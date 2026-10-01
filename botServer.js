const { WebSocketServer, WebSocket } = require('ws');

const { HttpsProxyAgent } = require('https-proxy-agent');
const { SocksProxyAgent } = require('socks-proxy-agent');

const wss = new WebSocketServer({
    host: '127.0.0.1',
    port: 8787
});

const safeCode = code =>
    (code >= 3000 && code <= 4999) || code === 1000 ? code : 4000;

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
    console.log(`[${proxy}] location: ${headers.location || '-'}`);
    console.log(`[${proxy}] content-type: ${headers['content-type'] || '-'}`);
}

wss.on('connection', (client, req) => {
    const q = new URL(req.url, 'http://localhost').searchParams;

    const target = q.get('url');
    const proxy = q.get('proxy');

    const tag = maskProxy(proxy);

    let u;

    try {
        u = new URL(target);
    } catch {
        client.close(4001, 'bad url');
        return;
    }

    if (
        !/^wss?:$/i.test(u.protocol) ||
        !/(^|\.)moomoo\.io$/i.test(u.hostname)
    ) {
        client.close(4002, 'host not allowed');
        return;
    }

    console.log(`[${tag}] client connected`);
    console.log(`[${tag}] target: ${u.origin}${u.pathname}`);

    let agent;

    try {
        if (proxy) {
            if (/^socks/i.test(proxy)) {
                agent = new SocksProxyAgent(proxy);
            } else {
                agent = new HttpsProxyAgent(proxy);
            }
        }
    } catch (e) {
        console.log(`[${tag}] proxy agent error: ${e.message}`);
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

            "User-Agent":
                    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/153.0.0.0 Safari/537.36",

            "Accept-Language":
                "ru-RU,ru;q=0.9,en-US;q=0.8,en;q=0.7",

            "Cache-Control": "no-cache",

            Pragma: "no-cache"
        }
    });

    const pending = [];

    let closed = false;

    const fail = why => {
        if (closed) return;

        console.log(`[${tag}] ${why}`);

        if (client.readyState === WebSocket.OPEN) {
            client.close(
                4003,
                String(why).slice(0, 100)
            );
        }
    };

    client.on('message', (data, isBinary) => {
        if (up.readyState === WebSocket.OPEN) {
            up.send(data, { binary: isBinary });
        } else if (up.readyState === WebSocket.CONNECTING) {
            pending.push([data, isBinary]);
        }
    });

    up.on('open', () => {
        console.log(`[${tag}] upstream open`);

        for (const [data, isBinary] of pending) {
            if (up.readyState === WebSocket.OPEN) {
                up.send(data, { binary: isBinary });
            }
        }

        pending.length = 0;
    });

    up.on('message', (data, isBinary) => {
        if (client.readyState === WebSocket.OPEN) {
            client.send(data, { binary: isBinary });
        }
    });

    up.on('unexpected-response', (request, res) => {
        logResponse(tag, res);

        let body = '';

        res.setEncoding('utf8');

        res.on('data', chunk => {
            if (body.length < 2000) {
                body += chunk;
            }
        });

        res.on('end', () => {
            if (body) {
                console.log(
                    `[${tag}] response body: ${body.slice(0, 2000)}`
                );
            }

            fail(`upstream HTTP ${res.statusCode}`);
        });
    });

    up.on('error', error => {
        fail(`upstream error: ${error.message}`);
    });

    up.on('close', (code, reason) => {
        const text = reason?.toString() || '';
        console.log(`[${tag}] UPSTREAM CLOSE code=${code} reason="${text}"`);
        closed = true;
        if (client.readyState === WebSocket.OPEN) {
            client.close(safeCode(code), text.slice(0, 100));
        }
    });

    client.on('error', (error) => {
        console.log(`[${tag}] client error: ${error.message}`);
        closed = true;
        if (up.readyState === WebSocket.OPEN || up.readyState === WebSocket.CONNECTING) {
            try { up.close(); } catch (_) {}
        }
    });

    client.on('close', (code, reason) => {
        console.log(
            `[${tag}] CLIENT CLOSE code=${code} reason="${(reason && reason.toString()) || ''}"`
        );
        closed = true;
        if (up.readyState === WebSocket.OPEN || up.readyState === WebSocket.CONNECTING) {
            try { up.close(); } catch (_) {}
        }
    });
});

console.log('Relay: ws://127.0.0.1:8787');