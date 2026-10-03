const { WebSocketServer, WebSocket } = require('ws');
const { HttpsProxyAgent } = require('https-proxy-agent');
const { SocksProxyAgent } = require('socks-proxy-agent');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');

const IDLE_APP_WARN_MS = 45000;
const CONFIG_PATH = path.join(__dirname, 'proxies.json');

/** @type {{ maxPerProxy: number, proxies: string[] }} */
let config = { maxPerProxy: 2, proxies: [] };
/** @type {Map<string, number>} */
const used = new Map();
/** proxy -> timestamp until which it is skipped after hard fail */
const cooldownUntil = new Map();
const FAIL_COOLDOWN_MS = 60_000;

function loadConfig() {
    try {
        const raw = fs.readFileSync(CONFIG_PATH, 'utf8');
        const j = JSON.parse(raw);
        config.maxPerProxy = Math.max(1, Number(j.maxPerProxy) || 2);
        config.proxies = Array.isArray(j.proxies)
            ? j.proxies.map(String).map(s => s.trim()).filter(Boolean)
            : [];
        for (const p of config.proxies) {
            if (!used.has(p)) used.set(p, 0);
        }
        for (const key of [...used.keys()]) {
            if (!config.proxies.includes(key)) used.delete(key);
        }
        console.log(`[pool] loaded ${config.proxies.length} proxies, maxPerProxy=${config.maxPerProxy}`);
    } catch (e) {
        console.error('[pool] failed to read proxies.json:', e.message);
        config = { maxPerProxy: 2, proxies: [] };
    }
}

function acquireProxy() {
    const now = Date.now();
    let best = null;
    let bestUsed = Infinity;
    for (const p of config.proxies) {
        const until = cooldownUntil.get(p) || 0;
        if (until > now) continue; // recently failed (ConnectionRefused etc.)
        const n = used.get(p) || 0;
        if (n < config.maxPerProxy && n < bestUsed) {
            best = p;
            bestUsed = n;
        }
    }
    if (!best) return null;
    used.set(best, (used.get(best) || 0) + 1);
    return best;
}

function markProxyFailed(proxy, reason) {
    if (!proxy) return;
    cooldownUntil.set(proxy, Date.now() + FAIL_COOLDOWN_MS);
    console.log(`[pool] cooldown 60s ${maskProxy(proxy)} — ${String(reason).slice(0, 80)}`);
}

function releaseProxy(proxy) {
    if (!proxy) return;
    const n = (used.get(proxy) || 1) - 1;
    used.set(proxy, Math.max(0, n));
}

function poolStatus() {
    let free = 0;
    let total = config.proxies.length * config.maxPerProxy;
    for (const p of config.proxies) {
        free += Math.max(0, config.maxPerProxy - (used.get(p) || 0));
    }
    return { free, total, proxies: config.proxies.length, maxPerProxy: config.maxPerProxy };
}

loadConfig();
try {
    fs.watch(CONFIG_PATH, { persistent: false }, () => {
        console.log('[pool] proxies.json changed — reload');
        loadConfig();
    });
} catch (_) {}

const wss = new WebSocketServer({
    host: '127.0.0.1',
    port: 8787
});

function maskProxy(proxy) {
    if (!proxy) return 'direct';
    try {
        const u = new URL(proxy);
        if (u.username) u.username = '***';
        if (u.password) u.password = '***';
        return u.toString();
    } catch {
        return 'proxy';
    }
}

function logResponse(proxy, res) {
    const headers = res.headers || {};
    console.log(`[${proxy}] upstream HTTP ${res.statusCode}`);
    console.log(`[${proxy}] server: ${headers.server || '-'}`);
    console.log(`[${proxy}] cf-ray: ${headers['cf-ray'] || '-'}`);
    console.log(`[${proxy}] cf-mitigated: ${headers['cf-mitigated'] || '-'}`);
}

function ms(from) {
    return from == null ? null : Math.round(Date.now() - from);
}

function fmtDur(msVal) {
    if (msVal == null) return '-';
    if (msVal < 1000) return msVal + 'ms';
    if (msVal < 60000) return (msVal / 1000).toFixed(1) + 's';
    const m = Math.floor(msVal / 60000);
    const s = Math.round((msVal % 60000) / 1000);
    return m + 'm' + s + 's';
}

function codeHint(code) {
    const map = {
        1000: 'normal', 1001: 'going-away', 1005: 'no-status', 1006: 'abnormal-RST',
        4000: 'relay-mapped', 4001: 'bad-url', 4002: 'host-blocked', 4003: 'upstream-lost',
        4010: 'no-proxy-slot'
    };
    return map[code] || (code >= 3000 && code <= 4999 ? 'app' : 'other');
}

function diagnose({ code, openedAt, bytesIn, bytesOut, msgIn, msgOut, idleAppRX, idleAppTX, closeSource, t0 }) {
    const life = ms(t0);
    const upLife = openedAt ? ms(openedAt) : null;
    if (!openedAt) return 'NEVER_OPEN: proxy/handshake failed before WS open';
    if (closeSource && String(closeSource).startsWith('up-error:')) return 'UP_ERROR: ' + String(closeSource).slice(9);
    if (closeSource && String(closeSource).startsWith('fail:')) return 'FAIL: ' + String(closeSource).slice(5);
    if (upLife != null && upLife < 2500 && bytesIn < 50 && msgIn === 0) return 'REJECT_FAST: open then die, no app RX (token/IP/CF or proxy drop)';
    if (upLife != null && upLife < 5000 && msgIn === 0 && msgOut > 0) return 'REJECT_AFTER_TX: bot sent packets, server never answered (token/IP mismatch?)';
    if (code === 1000 && upLife != null && upLife < 8000 && bytesIn < 200) return 'SERVER_1000_FAST: clean close soon after open (often bad token / ban)';
    if (idleAppRX != null && idleAppRX >= IDLE_APP_WARN_MS && msgIn > 0) return `IDLE_RX: no app packets from server for ${fmtDur(idleAppRX)}`;
    if (idleAppTX != null && idleAppTX >= IDLE_APP_WARN_MS && msgOut > 0) return `IDLE_TX: bot sent no app packets for ${fmtDur(idleAppTX)}`;
    if (code === 1006) {
        if (idleAppRX != null && idleAppRX < 5000 && (msgIn > 0 || msgOut > 0)) return 'RST_ACTIVE: 1006 while traffic was recent (proxy/network cut)';
        if (msgIn === 0 && msgOut === 0) return 'RST_EMPTY: 1006 with zero app messages';
        return 'RST_1006: abnormal close without WS close frame';
    }
    if (code === 1000 && (msgIn > 10 || bytesIn > 1000)) return 'SERVER_1000: graceful close after gameplay';
    if (closeSource === 'client') return 'CLIENT_LEFT: Colean closed the socket first';
    if (closeSource === 'upstream') return 'UPSTREAM_CLOSED: game server or proxy closed first';
    return `UNKNOWN life=${fmtDur(life)} up=${fmtDur(upLife)} code=${code}`;
}

wss.on('connection', (client, req) => {
    const q = new URL(req.url, 'http://localhost').searchParams;
    const target = q.get('url');
    const cookie = q.get('cookie');
    // Client may omit proxy — server assigns from pool
    let proxy = q.get('proxy') || null;
    let fromPool = false;

    if (!proxy) {
        proxy = acquireProxy();
        fromPool = !!proxy;
        if (!proxy) {
            const st = poolStatus();
            console.log(`[pool] no free slot free=${st.free}/${st.total}`);
            client.close(4010, 'no free proxy');
            return;
        }
    }

    const tag = maskProxy(proxy);
    const t0 = Date.now();
    const st = poolStatus();
    console.log(`[${tag}] client connected t=0 pool=${fromPool ? 'yes' : 'client'} free=${st.free}/${st.total}`);

    const chromeCiphers = [
        'TLS_AES_256_GCM_SHA384', 'TLS_CHACHA20_POLY1305_SHA256', 'TLS_AES_128_GCM_SHA256',
        'ECDHE-ECDSA-AES128-GCM-SHA256', 'ECDHE-RSA-AES128-GCM-SHA256',
        'ECDHE-ECDSA-AES256-GCM-SHA384', 'ECDHE-RSA-AES256-GCM-SHA384',
        'ECDHE-ECDSA-CHACHA20-POLY1305', 'ECDHE-RSA-CHACHA20-POLY1305'
    ].join(':');

    let u;
    try {
        u = new URL(target);
    } catch {
        if (fromPool) releaseProxy(proxy);
        client.close(4001, 'bad url');
        return;
    }

    if (!/^wss?:$/i.test(u.protocol) || !/(^|\.)moomoo\.io$/i.test(u.hostname)) {
        if (fromPool) releaseProxy(proxy);
        client.close(4002, 'host not allowed');
        return;
    }

    console.log(`[${tag}] target: ${u.origin}${u.pathname}`);

    let agent;
    let pingInterval = null;
    let openedAt = null;
    let lastAppRX = null, lastAppTX = null, lastPongAt = null;
    let bytesIn = 0, bytesOut = 0, msgIn = 0, msgOut = 0, pongs = 0;
    let closeSource = null, closed = false, diagnosed = false;

    const release = () => {
        if (fromPool && proxy) {
            releaseProxy(proxy);
            fromPool = false;
            const s = poolStatus();
            console.log(`[${tag}] slot released free=${s.free}/${s.total}`);
        }
    };

    try {
        if (proxy) {
            if (/^socks/i.test(proxy)) {
                agent = new SocksProxyAgent(proxy);
            } else {
                agent = new HttpsProxyAgent(proxy, {
                    secureOptions: crypto.constants.SSL_OP_NO_TLSv1 | crypto.constants.SSL_OP_NO_TLSv1_1,
                    ciphers: chromeCiphers,
                    honorCipherOrder: true,
                    minVersion: 'TLSv1.2'
                });
            }
        }
    } catch (e) {
        console.log(`[${tag}] proxy agent error: ${e.message}`);
        release();
        client.close(4003, 'proxy agent error');
        return;
    }

    const origin = u.hostname.includes('sandbox')
        ? 'https://sandbox.moomoo.io'
        : 'https://moomoo.io';

    const up = new WebSocket(target, {
        agent,
        headers: {
            Origin: origin,
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36',
            'Accept-Language': 'ru-RU,ru;q=0.9,en-US;q=0.8,en;q=0.7',
            'Cache-Control': 'no-cache',
            Pragma: 'no-cache',
            Cookie: cookie || ''
        }
    });

    const pending = [];

    const snap = () => ({
        life: fmtDur(ms(t0)),
        up: openedAt ? fmtDur(ms(openedAt)) : 'never',
        idleAppRX: lastAppRX != null ? fmtDur(ms(lastAppRX)) : (openedAt ? 'no-app-RX' : '-'),
        idleAppTX: lastAppTX != null ? fmtDur(ms(lastAppTX)) : (openedAt ? 'no-app-TX' : '-'),
        lastPong: lastPongAt != null ? fmtDur(ms(lastPongAt)) : 'no-pong',
        in: bytesIn, out: bytesOut, msgIn, msgOut, pongs
    });

    const printDiag = (code, reasonText) => {
        if (diagnosed) return;
        diagnosed = true;
        const s = snap();
        const verdict = diagnose({
            code, openedAt, bytesIn, bytesOut, msgIn, msgOut,
            idleAppRX: lastAppRX != null ? ms(lastAppRX) : (openedAt ? ms(openedAt) : null),
            idleAppTX: lastAppTX != null ? ms(lastAppTX) : (openedAt ? ms(openedAt) : null),
            closeSource, t0
        });
        console.log(
            `[${tag}] CLOSE code=${code} (${codeHint(code)}) after=${s.life} up=${s.up} ` +
            `idleAppRX=${s.idleAppRX} idleAppTX=${s.idleAppTX} pong=${s.lastPong} ` +
            `msgIn=${s.msgIn} msgOut=${s.msgOut} in=${s.in}B out=${s.out}B pongs=${s.pongs} ` +
            `src=${closeSource || '?'} reason="${(reasonText || '').slice(0, 60)}"`
        );
        console.log(`[${tag}] DIAG: ${verdict}`);
    };

    const fail = why => {
        if (closed) return;
        closeSource = closeSource || ('fail:' + why);
        if (!openedAt && fromPool) markProxyFailed(proxy, why);
        printDiag(4003, why);
        if (client.readyState === WebSocket.OPEN) client.close(4003, String(why).slice(0, 100));
    };

    const handshakeTimeout = setTimeout(() => {
        if (up.readyState === WebSocket.CONNECTING) {
            console.log(`[${tag}] handshake TIMEOUT after=${ms(t0)}ms`);
            try { up.terminate(); } catch (_) {}
            fail('proxy handshake timeout');
        }
    }, 10000);

    client.on('message', (data, isBinary) => {
        lastAppTX = Date.now();
        msgOut += 1;
        bytesOut += data.length || data.byteLength || 0;
        if (up.readyState === WebSocket.OPEN) up.send(data, { binary: isBinary });
        else if (up.readyState === WebSocket.CONNECTING) pending.push([data, isBinary]);
    });

    up.on('open', () => {
        clearTimeout(handshakeTimeout);
        openedAt = Date.now();
        console.log(`[${tag}] upstream open after=${ms(t0)}ms`);
        pingInterval = setInterval(() => {
            if (up.readyState === WebSocket.OPEN) {
                try { up.ping(); } catch (_) {}
            } else {
                clearInterval(pingInterval);
                pingInterval = null;
            }
        }, 25000);
        for (const [data, isBinary] of pending) {
            if (up.readyState === WebSocket.OPEN) up.send(data, { binary: isBinary });
        }
        pending.length = 0;
    });

    up.on('message', (data, isBinary) => {
        lastAppRX = Date.now();
        msgIn += 1;
        bytesIn += data.length || data.byteLength || 0;
        if (client.readyState === WebSocket.OPEN) client.send(data, { binary: isBinary });
    });

    up.on('pong', () => { lastPongAt = Date.now(); pongs += 1; });

    up.on('unexpected-response', (request, res) => {
        logResponse(tag, res);
        let body = '';
        res.setEncoding('utf8');
        res.on('data', chunk => { if (body.length < 2000) body += chunk; });
        res.on('end', () => {
            if (body) console.log(`[${tag}] response body: ${body.slice(0, 2000)}`);
            fail(`upstream HTTP ${res.statusCode}`);
        });
    });

    up.on('error', error => {
        closeSource = closeSource || ('up-error:' + error.message);
        fail(`upstream error: ${error.message}`);
    });

    up.on('close', (code, reason) => {
        const text = reason?.toString() || '';
        if (!closeSource) closeSource = 'upstream';
        closed = true;
        clearTimeout(handshakeTimeout);
        if (pingInterval) { clearInterval(pingInterval); pingInterval = null; }
        printDiag(code, text);
        release();
        if (client.readyState === WebSocket.OPEN) {
            client.close(4003, (`Up ${code} after ${snap().up}`).slice(0, 100));
        }
    });

    client.on('error', error => {
        closeSource = closeSource || ('client-error:' + error.message);
        console.log(`[${tag}] CLIENT ERROR after=${ms(t0)}ms: ${error.message}`);
        closed = true;
        if (up.readyState === WebSocket.OPEN || up.readyState === WebSocket.CONNECTING) {
            try { up.terminate(); } catch (_) {}
        }
    });

    client.on('close', (code, reason) => {
        if (!closeSource) closeSource = 'client';
        closed = true;
        clearTimeout(handshakeTimeout);
        if (pingInterval) { clearInterval(pingInterval); pingInterval = null; }
        printDiag(code, (reason && reason.toString()) || '');
        release();
        if (up.readyState === WebSocket.OPEN || up.readyState === WebSocket.CONNECTING) {
            try { up.terminate(); } catch (_) {}
        }
    });
});


const http = require('http');
const statusServer = http.createServer((req, res) => {
    res.setHeader('Access-Control-Allow-Origin', '*');
    res.setHeader('Access-Control-Allow-Methods', 'GET, OPTIONS');
    if (req.method === 'OPTIONS') { res.writeHead(204); res.end(); return; }
    if (req.url === '/status' || req.url === '/') {
        const st = poolStatus();
        const now = Date.now();
        let onCooldown = 0;
        for (const pxy of config.proxies) {
            if ((cooldownUntil.get(pxy) || 0) > now) onCooldown++;
        }
        res.writeHead(200, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({
            ok: true,
            free: st.free,
            total: st.total,
            proxies: st.proxies,
            maxPerProxy: st.maxPerProxy,
            onCooldown
        }));
        return;
    }
    res.writeHead(404); res.end('not found');
});
statusServer.listen(8788, '127.0.0.1', () => {
    console.log('Status: http://127.0.0.1:8788/status');
});

console.log('Relay: ws://127.0.0.1:8787');
console.log('Proxy pool: proxies.json next to this file (client does NOT send passwords)');
console.log('Connect: ws://127.0.0.1:8787/?url=' + encodeURIComponent('wss://...moomoo.io/'));
const st = poolStatus();
console.log(`[pool] ready free=${st.free}/${st.total}`);