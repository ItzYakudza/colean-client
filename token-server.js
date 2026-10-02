/**
 * Bridge: Colean → Theyka/Turnstile-Solver with the SAME SOCKS proxy as the bot.
 *
 * Theyka returns plain text "CAPTCHA_NOT_READY" while solving (not JSON).
 *
 *   set THEYKA_DIR=%USERPROFILE%\Turnstile-Solver
 *   node theyka-bridge.js
 *
 * Theyka must be running:
 *   python api_solver.py --proxy True --browser_type camoufox --thread 1
 */
const http = require('http');
const fs = require('fs');
const path = require('path');
const { URL } = require('url');

const PORT = 8790;
const HOST = '127.0.0.1';
const THEYKA = process.env.THEYKA_URL || 'http://127.0.0.1:5000';
const PAGE_URL = 'https://moomoo.io/';
const THEYKA_DIR = process.env.THEYKA_DIR || path.join(process.env.USERPROFILE || process.env.HOME || '.', 'Turnstile-Solver');
const PROXIES_FILE = path.join(THEYKA_DIR, 'proxies.txt');

let locked = Promise.resolve();

function sendJson(res, code, obj) {
    const body = JSON.stringify(obj);
    res.writeHead(code, {
        'Content-Type': 'application/json',
        'Access-Control-Allow-Origin': '*',
        'Access-Control-Allow-Methods': 'GET, OPTIONS',
        'Access-Control-Allow-Headers': '*'
    });
    res.end(body);
}

/** socks5://user:pass@host:port → socks5://host:port:user:pass */
function toTheykaProxyLine(proxyUrl) {
    const u = new URL(proxyUrl);
    const scheme = (u.protocol || 'socks5:').replace(':', '');
    const host = u.hostname;
    const port = u.port || (scheme.startsWith('socks') ? '1080' : '80');
    const user = decodeURIComponent(u.username || '');
    const pass = decodeURIComponent(u.password || '');
    if (user || pass) return `${scheme}://${host}:${port}:${user}:${pass}`;
    return `${scheme}://${host}:${port}`;
}

function sleep(ms) {
    return new Promise(r => setTimeout(r, ms));
}

async function fetchText(url) {
    const res = await fetch(url);
    const text = await res.text();
    return { status: res.status, text: text.trim() };
}

function parseTheykaBody(text) {
    if (!text) return { kind: 'empty' };
    // Plain-text statuses from Theyka
    if (/^CAPTCHA_NOT_READY$/i.test(text)) return { kind: 'pending' };
    if (/^CAPTCHA_FAIL/i.test(text)) return { kind: 'fail', error: text };
    if (/^ERROR/i.test(text)) return { kind: 'fail', error: text };
    // Raw token (long string starting with 0. or similar)
    if (text.length > 40 && !text.startsWith('{') && !/\s/.test(text)) {
        return { kind: 'token', token: text };
    }
    try {
        const j = JSON.parse(text);
        if (j.task_id || j.id) return { kind: 'task', taskId: j.task_id || j.id };
        if (j.value && String(j.value).length > 20) return { kind: 'token', token: String(j.value) };
        if (j.token && String(j.token).length > 20) return { kind: 'token', token: String(j.token) };
        if (j.error) return { kind: 'fail', error: String(j.error) };
        if (j.status && /not.?ready|pending|process/i.test(String(j.status))) return { kind: 'pending' };
        if (j.status && /fail|error/i.test(String(j.status))) return { kind: 'fail', error: JSON.stringify(j) };
        return { kind: 'unknown', raw: j };
    } catch {
        return { kind: 'unknown', raw: text };
    }
}

async function theykaSolve(sitekey, proxyUrl) {
    let release;
    const wait = new Promise(r => { release = r; });
    const prev = locked;
    locked = prev.then(() => wait);
    await prev;

    const line = toTheykaProxyLine(proxyUrl);
    let backup = null;
    try {
        if (fs.existsSync(PROXIES_FILE)) {
            backup = fs.readFileSync(PROXIES_FILE, 'utf8');
        }
        fs.mkdirSync(path.dirname(PROXIES_FILE), { recursive: true });
        fs.writeFileSync(PROXIES_FILE, line + '\n', 'utf8');
        console.log('[bridge] proxies.txt →', line.replace(/:([^:/\s]+)$/, ':***'));

        const createUrl = `${THEYKA}/turnstile?url=${encodeURIComponent(PAGE_URL)}&sitekey=${encodeURIComponent(sitekey)}`;
        const created = await fetchText(createUrl);
        const createdParsed = parseTheykaBody(created.text);
        let taskId = createdParsed.taskId;
        if (!taskId && createdParsed.kind === 'token') {
            // unlikely immediate solve
            return createdParsed.token;
        }
        if (!taskId) {
            // try JSON field extract from raw
            try {
                const j = JSON.parse(created.text);
                taskId = j.task_id || j.id;
            } catch (_) {}
        }
        if (!taskId) {
            throw new Error('Theyka create failed: ' + created.text.slice(0, 200));
        }
        console.log('[bridge] task', taskId);

        for (let i = 0; i < 90; i++) {
            await sleep(2000);
            const polled = await fetchText(`${THEYKA}/result?id=${encodeURIComponent(taskId)}`);
            const parsed = parseTheykaBody(polled.text);

            if (parsed.kind === 'token') {
                console.log('[bridge] OK len', parsed.token.length);
                return parsed.token;
            }
            if (parsed.kind === 'pending') {
                if (i % 5 === 0) console.log('[bridge] waiting… CAPTCHA_NOT_READY');
                continue;
            }
            if (parsed.kind === 'fail') {
                throw new Error('Theyka: ' + parsed.error);
            }
            if (i % 5 === 0) {
                console.log('[bridge] waiting…', polled.text.slice(0, 100));
            }
        }
        throw new Error('Theyka timeout waiting for token');
    } finally {
        try {
            if (backup !== null) fs.writeFileSync(PROXIES_FILE, backup, 'utf8');
        } catch (_) {}
        release();
    }
}

const server = http.createServer(async (req, res) => {
    if (req.method === 'OPTIONS') return sendJson(res, 204, {});
    let url;
    try {
        url = new URL(req.url, `http://${HOST}:${PORT}`);
    } catch {
        return sendJson(res, 400, { error: 'bad url' });
    }
    if (url.pathname === '/health') {
        return sendJson(res, 200, { ok: true, theyka: THEYKA, proxiesFile: PROXIES_FILE });
    }
    if (url.pathname !== '/token') {
        return sendJson(res, 404, { error: 'not found' });
    }
    const sitekey = url.searchParams.get('sitekey');
    const proxy = url.searchParams.get('proxy');
    if (!sitekey || !proxy) {
        return sendJson(res, 400, { error: 'sitekey and proxy required' });
    }
    try {
        const token = await theykaSolve(sitekey, proxy);
        sendJson(res, 200, { token });
    } catch (e) {
        console.error('[bridge] FAIL', e.message);
        sendJson(res, 500, { error: e.message || String(e) });
    }
});

server.listen(PORT, HOST, () => {
    console.log(`[theyka-bridge] http://${HOST}:${PORT}/token`);
    console.log(`[theyka-bridge] Theyka API: ${THEYKA}`);
    console.log(`[theyka-bridge] proxies.txt: ${PROXIES_FILE}`);
});