// ==UserScript==
// @name            Colean Client v1.0.0 | By ItzYakudza
// @author          ItzYakudza
// @description     comfortable Moomoo.io experience
// @icon            https://static.vecteezy.com/system/resources/previews/005/283/491/non_2x/simple-sword-icon-white-color-vector.jpg
// @version         1.0.0
// @match           *://moomoo.io/
// @match           *://moomoo.io/?server*
// @match           *://*.moomoo.io/
// @match           *://*.moomoo.io/?server*
// @run-at          document-start
// @grant           none
// @license         MIT
// @namespace       https://github.com/ItzYakudza/Colean-Client
// ==/UserScript==

Math.LN1 = 100;
Number.DELTA = 1;
window.grbtp = 35;

(function() {
    const runtimeKey = Symbol.for('Colean.Client.Runtime');
    if (window[runtimeKey]) {
        console.warn('[Colean] Duplicate userscript initialization skipped.');
        return;
    }
    window[runtimeKey] = true;

    const CLIENT_NAME = "Colean Client";
    const CLIENT_AUTHOR = "ItzYakudza";
    const CLIENT_VERSION = "1.0.0";

    function utf8ByteLength(str) {
        let len = 0;
        for (let i = 0; i < str.length; ) {
            let code = str.charCodeAt(i++);
            if (code & 4294967168) {
                if (!(code & 4294965248)) {
                    len += 2;
                } else {
                    if (code >= 55296 && code <= 57343 && i < str.length) {
                        const low = str.charCodeAt(i);
                        if ((low & 64512) === 56320) {
                            i++;
                            code = ((code & 1023) << 10) + (low & 1023) + 65536;
                        }
                    }
                    len += code & 4294901760 ? 4 : 3;
                }
            } else {
                len += 1;
            }
        }
        return len;
    }

    function readI64(view, offset) {
        const hi = view.getInt32(offset);
        const lo = view.getUint32(offset + 4);
        return hi * 4294967296 + lo;
    }

    function readU64(view, offset) {
        const hi = view.getUint32(offset);
        const lo = view.getUint32(offset + 4);
        return hi * 4294967296 + lo;
    }

    function isPrimitive(value) {
        const t = typeof value;
        return t === "string" || t === "number";
    }

    function createRNG(seed) {
        return function() {
            seed |= 0, seed = seed + 1831565813 | 0;
            let t = Math.imul(seed ^ seed >>> 15, 1 | seed);
            t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t;
            return ((t ^ t >>> 14) >>> 0) / 4294967296;
        };
    }

    function createTable(alphabet, seed) {
        const i = alphabet.length;
        const n = alphabet.map((c, d) => d);
        const s = createRNG(seed >>> 0);
        for (let c = i - 1; c > 0; c--) {
            const d = Math.floor(s() * (c + 1));
            const tmp = n[c];
            n[c] = n[d];
            n[d] = tmp;
        }
        const enc = {}, dec = {};
        for (let c = 0; c < i; c++) {
            const orig = alphabet[c];
            const mapped = n[c];
            enc[orig] = mapped;
            dec[mapped] = orig;
        }
        return {
            enc: enc,
            dec: dec
        };
    }

    function buildTables(socketID) {
        let t = (socketID ^ Math.imul(SHUFFLE_SEED, 2654435761)) >>> 0;
        return {
            c2s: createTable(CLIENT_PACKET_IDS, t),
            s2c: createTable(SERVER_PACKET_IDS, (t ^ 2246822507) >>> 0)
        };
    }

    function rotr(x, n) {
        return x >>> n | x << 32 - n;
    }

    function sha256(message) {
        const t = new Uint32Array([ 1779033703, 3144134277, 1013904242, 2773480762, 1359893119, 2600822924, 528734635, 1541459225 ]);
        const len = message.length;
        const bitLen = len * 8;
        const padLen = new Uint8Array(Math.ceil((len + 9) / 64) * 64);
        padLen.set(message), padLen[len] = 128;
        const view = new DataView(padLen.buffer);
        view.setUint32(padLen.length - 4, bitLen >>> 0, false), view.setUint32(padLen.length - 8, Math.floor(bitLen / 4294967296), false);
        let c = new Uint32Array(64);
        for (let h = 0; h < padLen.length; h += 64) {
            for (let v = 0; v < 16; v++) {
                c[v] = view.getUint32(h + v * 4, false);
            }
            for (let v = 16; v < 64; v++) {
                const C = rotr(c[v - 15], 7) ^ rotr(c[v - 15], 18) ^ c[v - 15] >>> 3;
                const A = rotr(c[v - 2], 17) ^ rotr(c[v - 2], 19) ^ c[v - 2] >>> 10;
                c[v] = c[v - 16] + C + c[v - 7] + A | 0;
            }
            let g = t[0];
            let r = t[1];
            let u = t[2];
            let x = t[3];
            let k = t[4];
            let M = t[5];
            let E = t[6];
            let w = t[7];
            for (let v = 0; v < 64; v++) {
                const C = rotr(k, 6) ^ rotr(k, 11) ^ rotr(k, 25);
                const A = k & M ^ ~k & E;
                const H = w + C + A + SHA256_K[v] + c[v] | 0;
                const j = rotr(g, 2) ^ rotr(g, 13) ^ rotr(g, 22);
                const S = g & r ^ g & u ^ r & u;
                const W = j + S | 0;
                w = E;
                E = M;
                M = k;
                k = x + H | 0;
                x = u;
                u = r;
                r = g;
                g = H + W | 0;
            }
            t[0] = t[0] + g | 0;
            t[1] = t[1] + r | 0;
            t[2] = t[2] + u | 0;
            t[3] = t[3] + x | 0;
            t[4] = t[4] + k | 0;
            t[5] = t[5] + M | 0;
            t[6] = t[6] + E | 0;
            t[7] = t[7] + w | 0;
        }
        const out = new Uint8Array(32);
        const outView = new DataView(out.buffer);
        for (let h = 0; h < 8; h++) {
            outView.setUint32(h * 4, t[h], false);
        }
        return out;
    }

    function hmacSHA256(key, message) {
        let i = key;
        if (i.length > BLOCK_SIZE) {
            i = sha256(i);
        }
        const paddedKey = new Uint8Array(BLOCK_SIZE);
        paddedKey.set(i);
        const inner = new Uint8Array(BLOCK_SIZE + message.length);
        const outer = new Uint8Array(BLOCK_SIZE + 32);
        for (let o = 0; o < BLOCK_SIZE; o++) {
            inner[o] = paddedKey[o] ^ 54;
            outer[o] = paddedKey[o] ^ 92;
        }
        inner.set(message, BLOCK_SIZE);
        outer.set(sha256(inner), BLOCK_SIZE);
        return sha256(outer);
    }

    function computeHMAC(key, payload) {
        return hmacSHA256(key, payload).subarray(0, 6);
    }

    function hexToBytes(hex) {
        const t = new Uint8Array(hex.length / 2);
        for (let i = 0; i < t.length; i++) {
            t[i] = parseInt(hex.substr(i * 2, 2), 16);
        }
        return t;
    }

    function easeOutQuad(x) {
        return 1 - (1 - x) * (1 - x);
    }

    function shortAngle(a, b) {
        const PI22 = 2 * Math.PI;
        a = (a % PI22 + PI22) % PI22;
        b = (b % PI22 + PI22) % PI22;
        let diff = b - a;
        if (diff > PI22 / 2) {
            diff -= PI22;
        } else if (diff < -PI22 / 2) {
            diff += PI22;
        }
        return diff;
    }

    const BotVerification = {
        pending: false,
        cancel: null,
        session: null,
        requests: new Set,
        sitekey: null,
        turnstileLoading: null,
        failedScripts: new WeakSet,
        readSitekey(code) {
            const match = code.match(/["'](0x4[A-Za-z0-9_-]+)["']/);
            this.sitekey = match ? match[1] : null;
        },
        loadTurnstile() {
            if (typeof window.turnstile?.render === "function") return Promise.resolve(window.turnstile);
            if (this.turnstileLoading) return this.turnstileLoading;
            let resolveLoad, rejectLoad;
            const loading = new Promise((resolve, reject) => { resolveLoad = resolve; rejectLoad = reject; });
            this.turnstileLoading = loading;
            const source = "https://challenges.cloudflare.com/turnstile/v0/api.js";
            const existing = [...document.querySelectorAll("script[src]")].find(script => {
                if (this.failedScripts.has(script)) return false;
                try {
                    const url = new URL(script.src);
                    return url.origin + url.pathname === source;
                } catch (_) { return false; }
            });
            const script = existing || document.createElement("script");
            let settled = false, timeout = null;
            const finish = (error, api) => {
                if (settled) return;
                settled = true;
                clearTimeout(timeout);
                script.removeEventListener("load", onLoad);
                script.removeEventListener("error", onError);
                if (error) {
                    this.failedScripts.add(script);
                    if (!existing) script.remove();
                }
                if (this.turnstileLoading === loading) this.turnstileLoading = null;
                if (error) rejectLoad(error); else resolveLoad(api);
            };
            const onLoad = () => {
                if (typeof window.turnstile?.render === "function") finish(null, window.turnstile);
                else finish(new Error("Cloudflare loaded but its verification API was unavailable."));
            };
            const onError = () => finish(new Error("The Cloudflare script could not be loaded. Check your content blocker settings."));
            script.addEventListener("load", onLoad, {once:true});
            script.addEventListener("error", onError, {once:true});
            timeout = setTimeout(() => finish(new Error("Cloudflare could not be reached. Please try again.")), 20000);
            if (!existing) {
                script.src = source + "?render=explicit";
                script.async = true;
                try { document.head.appendChild(script); } catch (_) { onError(); }
            }
            return loading;
        },
        createPanel(batch = false) {
            const overlay = document.createElement("div");
            overlay.style.cssText = "position:fixed;inset:0;z-index:2147483647;background:rgba(0,0,0,.75);display:flex;align-items:center;justify-content:center;pointer-events:auto";
            const panel = document.createElement("div");
            panel.setAttribute("role", "dialog");
            panel.setAttribute("aria-modal", "true");
            panel.setAttribute("aria-label", "Verify bot connection");
            panel.style.cssText = "background:#20242c;color:white;padding:24px;border:1px solid #41464d;border-radius:12px;box-sizing:border-box;width:440px;max-width:calc(100vw - 24px);max-height:calc(100vh - 24px);overflow:auto;font:16px 'Noto Sans',sans-serif;text-align:center";
            const title = document.createElement("h3");
            title.textContent = batch ? "Verify bot connections" : "Verify bot connection";
            const target = document.createElement("p");
            target.style.cssText = "color:#c0c5ca;font-size:14px;overflow-wrap:anywhere";
            const status = document.createElement("p");
            const host = document.createElement("div");
            host.style.cssText = "min-height:70px;display:flex;justify-content:center" + (batch ? ";flex-direction:column;align-items:center;gap:12px" : "");
            const progress = document.createElement("p");
            progress.style.cssText = "color:#c0c5ca;font-size:13px;line-height:1.6";
            progress.setAttribute("aria-live", "polite");
            const cancel = document.createElement("button");
            cancel.type = "button";
            cancel.textContent = batch ? "Stop Adding" : "Cancel";
            cancel.style.cssText = "margin-top:16px;padding:10px 20px;cursor:pointer;background:#30343a;color:#e2e5e8;border:3px solid #41464d;border-radius:5px;font:inherit;font-weight:800";
            panel.append(title, target, status, host, progress, cancel);
            overlay.appendChild(panel);
            const cancelAction = () => {
                if (this.session?.view === view) this.session.onCancel();
                else this.cancel?.();
            };
            const onKey = event => {
                if (event.key === "Escape") {
                    event.preventDefault(); event.stopImmediatePropagation(); cancelAction();
                }
            };
            const previousFocus = document.activeElement;
            const view = {overlay, target, status, host, progress, cancelButton:cancel, close:() => {
                document.removeEventListener("keydown", onKey, true);
                overlay.remove();
                if (previousFocus?.isConnected) previousFocus.focus();
            }};
            cancel.onclick = cancelAction;
            document.addEventListener("keydown", onKey, true);
            document.body.appendChild(overlay);
            cancel.focus();
            return view;
        },
        createRequestView(session, label) {
            const card = document.createElement("div");
            card.setAttribute("role", "group");
            card.setAttribute("aria-label", label || "Bot verification");
            card.style.cssText = "width:100%;box-sizing:border-box;padding:10px;border:1px solid #41464d;border-radius:5px;background:#171b21";
            const target = document.createElement("p");
            target.style.cssText = "margin:0 0 8px;color:#c0c5ca;font-size:13px;overflow-wrap:anywhere";
            const status = document.createElement("p");
            status.style.cssText = "margin:0 0 8px;font-size:13px";
            status.setAttribute("aria-live", "polite");
            const host = document.createElement("div");
            host.style.cssText = "min-height:70px;display:flex;justify-content:center";
            card.append(target, status, host);
            session.view.host.appendChild(card);
            return {target, status, host, close:() => card.remove()};
        },
        updatePending() {
            this.pending = this.requests.size > 0;
            this.cancel = this.pending ? () => {
                for (const request of [...this.requests]) request.cancel();
            } : null;
        },
        beginBatch(onCancel, options = {}) {
            if (this.pending || this.session) throw new Error("A verification is already open.");

            const session = {
                onCancel,
                concurrency: 2,
                view: this.createPanel(true)
            };

            if (options.stopLabel) session.view.cancelButton.textContent = options.stopLabel;
            session.view.target.textContent = "Two verifications can run at the same time.";
            session.view.status.textContent = "Complete each box below. Connections start after verification succeeds.";

            this.session = session;
            return session;
        },
        updateBatch(session, message) {
            if (session && this.session === session) session.view.progress.textContent = message;
        },
        waitForConnections(session) {
            if (session && this.session === session && !this.pending) {
                session.view.target.textContent = "Verification queue complete";
                session.view.status.textContent = "Waiting for verified connections to finish...";
            }
        },
        showBatchError(session, message) {
            if (!session || this.session !== session) return Promise.resolve();
            this.cancel?.();
            session.view.host.replaceChildren();
            session.view.status.textContent = 'Spawning stopped. ' + message;
            session.view.status.setAttribute('role', 'alert');
            session.view.cancelButton.textContent = 'Close';
            return new Promise(resolve => {
                session.dismiss = () => {
                    session.dismiss = null;
                    resolve();
                };
                session.onCancel = () => session.dismiss?.();
                session.view.cancelButton.focus();
            });
        },
        endBatch(session) {
            if (!session || this.session !== session) return;
            session.dismiss?.();
            this.cancel?.();
            this.session = null;
            session.view.close();
        },
        requestToken(context = null) {
            const session = context?.session || null;
            if (session !== this.session) return Promise.reject(new Error("The verification session is no longer active."));
            if (this.pending && !session || session && this.requests.size >= session.concurrency) return Promise.reject(new Error("A verification is already open."));
            if (!this.sitekey) return Promise.reject(new Error("Cloudflare site key was not found in the bundle. Refresh the page."));
            if (!document.body) return Promise.reject(new Error("The page is not ready for verification. Please try again."));
            const sitekey = this.sitekey;
            const view = session ? this.createRequestView(session, context?.label) : this.createPanel();
            const {status, host} = view;
            view.target.textContent = context?.label || "";
            status.textContent = "Loading Cloudflare verification…";
            return new Promise((resolve, reject) => {
                let settled = false, widgetID = null, api = null, timeout = null;
                const removeWidget = () => {
                    if (widgetID === null || widgetID === undefined) return;
                    const id = widgetID;
                    widgetID = null;
                    try { api.remove(id); } catch (_) {}
                };
                const finish = (error, token) => {
                    if (settled) return;
                    settled = true;
                    clearTimeout(timeout);
                    removeWidget();
                    host.replaceChildren();
                    view.close();
                    this.requests.delete(request);
                    this.updatePending();
                    if (error) reject(error); else resolve(token);
                };
                const request = {cancel:() => finish(new Error("Verification was cancelled."))};
                this.requests.add(request);
                this.updatePending();
                timeout = setTimeout(() => finish(new Error("Verification timed out. Please try again.")), 180000);
                const render = loaded => {
                    if (settled) return;
                    if (!host.isConnected || host.getClientRects().length === 0) {
                        finish(new Error("The verification panel is no longer visible. Please try again."));
                        return;
                    }
                    api = loaded;
                    status.textContent = "Complete the verification below to connect.";
                    try {
                        widgetID = api.render(host, {
                            sitekey,
                            theme: "dark",
                            language: "en",
                            retry: "never",
                            "refresh-expired": "manual",
                            callback: token => {
                                if (typeof token !== "string" || !token) {
                                    finish(new Error("Verification did not produce a token."));
                                    return;
                                }
                                finish(null, token);
                            },
                            "error-callback": code => {
                                finish(new Error("Cloudflare verification failed: " + code));
                            },
                            "expired-callback": () => finish(new Error("Verification expired. Please try again.")),
                            "timeout-callback": () => finish(new Error("Cloudflare verification timed out."))
                        });
                        // A synchronous callback may finish before render returns the widget ID.
                        if (settled) { removeWidget(); host.replaceChildren(); }
                        else if (widgetID === null || widgetID === undefined) finish(new Error("Cloudflare verification could not be opened."));
                    } catch (_) {
                        finish(new Error("Cloudflare verification could not be opened."));
                    }
                };
                if (typeof window.turnstile?.render === "function") render(window.turnstile);
                else this.loadTurnstile().then(render, error => finish(error));
            });
        }
    };

    const BOT_PROXY_RELAY = "ws://127.0.0.1:8787";


    async function checkRelaySlots() {
        try {
            const r = await fetch("http://127.0.0.1:8788/status", { cache: "no-store" });
            if (!r.ok) throw new Error("status " + r.status);
            const j = await r.json();
            if (!j || typeof j.free !== "number") throw new Error("bad status body");
            return j;
        } catch (e) {
            throw new Error("Relay status unavailable (" + (e.message || e) + "). Start bot-server.js");
        }
    }

    const createSocket = async (serverAddress = null, verification = null) => {
        const socket = client.SocketManager.socket;
        if (!serverAddress && (!socket || socket.readyState !== socket.OPEN)) {
            throw new Error("Connect the main player to a server first.");
        }
        const server = serverAddress || new URL(socket.url).origin;
        verificationRef = verification;
        if (verification?.isCancelled?.()) throw new Error("Bot connection cancelled.");

        let slots;
        try {
            slots = await checkRelaySlots();
        } catch (e) {
            verificationRef = null;
            throw e;
        }
        if (slots.free <= 0) {
            verificationRef = null;
            throw new Error(`No free proxy slots (0/${slots.total}). Wait or add proxies.`);
        }
        if (verification?.session) {
            BotVerification.updateBatch(
                verification.session,
                `Proxy slots ${slots.free}/${slots.total}` + (slots.onCooldown ? ` (${slots.onCooldown} cooling down)` : "")
            );
        }

        let token;
        try {
            if (verification?.session) {
                BotVerification.updateBatch(verification.session, "Complete Cloudflare in the panel…");
            }
            token = await BotVerification.requestToken(verification);
        } catch (e) {
            verificationRef = null;
            throw e;
        }

        if (!serverAddress && (client.SocketManager.socket !== socket || socket.readyState !== socket.OPEN)) {
            verificationRef = null;
            throw new Error("The main connection changed during verification. Please try again.");
        }
        if (verification?.isCancelled?.()) {
            verificationRef = null;
            throw new Error("Bot connection cancelled.");
        }

        const url = new URL(server);
        url.searchParams.set("token", "cf:" + token);

        const target = `${BOT_PROXY_RELAY}/?url=${encodeURIComponent(url.href)}`;

        let ws;
        try {
            ws = new WebSocket(target);
        } catch (e) {
            verificationRef = null;
            throw e;
        }
        // Hide relay URL so game logic sees the real moomoo endpoint
        Object.defineProperty(ws, "url", { value: url.href });
        ws.binaryType = "arraybuffer";
        verificationRef = null;
        return ws;
    };
const createSocket_default = createSocket;

        // External host auth (bridge)
    window.ColeanBotAuth = window.ColeanBotAuth = {
        requestToken(context) {
            return BotVerification.requestToken(context || null);
        },
        getServerBase() {
            const socket = client.SocketManager.socket;
            if (!socket || socket.readyState !== socket.OPEN || !socket.url) {
                throw new Error("Connect the main player to a server first.");
            }
            const u = new URL(socket.url);
            u.search = "";
            u.hash = "";
            return u.href;
        },
        async getFreshEndpoint() {
            const server = this.getServerBase();
            const raw = await BotVerification.requestToken(null);
            const token = String(raw).startsWith("cf:") ? String(raw) : ("cf:" + raw);
            return { server, token };
        }
    };

    const Hooker = new class {
        createRecursiveHook(target, prop, callback) {
            let newValue = target[prop];
            (function recursiveHook() {
                Object.defineProperty(target, prop, {
                    set(value) {
                        delete target[prop];
                        this[prop] = value;
                        newValue = value;
                        if (callback(this, value)) {
                            return;
                        }
                        recursiveHook();
                    },
                    get() {
                        return newValue;
                    },
                    configurable: true
                });
            })();
        }
        createHook(target, prop, callback) {
            const symbol = Symbol(prop);
            Object.defineProperty(target, prop, {
                get() {
                    return this[symbol];
                },
                set(value) {
                    callback(this, value, symbol);
                },
                configurable: true
            });
        }
        linker(value) {
            const hook = [ value ];
            hook.valueOf = () => hook[0];
            return hook;
        }
    };

    const blockProperty = (target, key) => {
        const value = target[key];
        Object.defineProperty(target, key, {
            set() {},
            get() {
                return value;
            },
            configurable: true
        });
    };

    const Hooker_default = Hooker;

    const Config = {
        maxScreenWidth: 1920,
        maxScreenHeight: 1080,
        serverUpdateRate: 9,
        collisionDepth: 6,
        minimapRate: 3e3,
        colGrid: 10,
        clientSendRate: 5,
        barWidth: 50,
        barHeight: 17,
        barPad: 4.5,
        iconPadding: 15,
        iconPad: .9,
        deathFadeout: 3e3,
        crownIconScale: 60,
        crownPad: 35,
        chatCountdown: 3e3,
        chatCooldown: 500,
        maxAge: 100,
        gatherAngle: Math.PI / 2.6,
        gatherWiggle: 10,
        hitReturnRatio: .25,
        hitAngle: Math.PI / 2,
        playerScale: 35,
        playerSpeed: .0016,
        playerDecel: .993,
        nameY: 34,
        animalCount: 7,
        aiTurnRandom: .06,
        shieldAngle: Math.PI / 3,
        resourceTypes: [ "wood", "food", "stone", "points" ],
        areaCount: 7,
        treesPerArea: 9,
        bushesPerArea: 3,
        totalRocks: 32,
        goldOres: 7,
        riverWidth: 724,
        riverPadding: 114,
        waterCurrent: .0011,
        waveSpeed: 1e-4,
        waveMax: 1.3,
        treeScales: [ 150, 160, 165, 175 ],
        bushScales: [ 80, 85, 95 ],
        rockScales: [ 80, 85, 90 ],
        snowBiomeTop: 2400,
        desertBiomeTop: 2400,
        snowSpeed: .75,
        maxNameLength: 15,
        mapScale: 14400,
        mapPingScale: 40,
        mapPingTime: 2200,
        skinColors: [ "#bf8f54", "#cbb091", "#896c4b", "#fadadc", "#ececec", "#c37373", "#4c4c4c", "#ecaff7", "#738cc3", "#8bc373", "#91B2DB" ]
    };

    const Config_default = Config;

    const WeaponTypeString = [ "primary", "secondary" ];

    const Weapons = [ {
        id: 0,
        itemType: 0,
        upgradeType: 0,
        type: 0,
        age: 0,
        name: "tool hammer",
        description: "tool for gathering all resources",
        src: "hammer_1",
        length: 140,
        width: 140,
        xOffset: -3,
        yOffset: 18,
        spdMult: 1,
        damage: 25,
        range: 65,
        gather: 1,
        speed: 300,
        knockback: 60
    }, {
        id: 1,
        itemType: 0,
        upgradeType: 1,
        type: 0,
        age: 2,
        name: "hand axe",
        description: "gathers resources at a higher rate",
        src: "axe_1",
        length: 140,
        width: 140,
        xOffset: 3,
        yOffset: 24,
        damage: 30,
        spdMult: 1,
        range: 70,
        gather: 2,
        speed: 400,
        knockback: 60
    }, {
        id: 2,
        itemType: 0,
        upgradeOf: 1,
        upgradeType: 1,
        type: 0,
        age: 8,
        pre: 1,
        name: "great axe",
        description: "deal more damage and gather more resources",
        src: "great_axe_1",
        length: 140,
        width: 140,
        xOffset: -8,
        yOffset: 25,
        damage: 35,
        spdMult: 1,
        range: 75,
        gather: 4,
        speed: 400,
        knockback: 60
    }, {
        id: 3,
        itemType: 0,
        upgradeType: 2,
        type: 0,
        age: 2,
        name: "short sword",
        description: "increased attack power but slower move speed",
        src: "sword_1",
        iPad: 1.3,
        length: 130,
        width: 210,
        xOffset: -8,
        yOffset: 46,
        damage: 35,
        spdMult: .85,
        range: 110,
        gather: 1,
        speed: 300,
        knockback: 60
    }, {
        id: 4,
        itemType: 0,
        upgradeOf: 3,
        upgradeType: 2,
        type: 0,
        age: 8,
        pre: 3,
        name: "katana",
        description: "greater range and damage",
        src: "samurai_1",
        iPad: 1.3,
        length: 130,
        width: 210,
        xOffset: -8,
        yOffset: 59,
        damage: 40,
        spdMult: .8,
        range: 118,
        gather: 1,
        speed: 300,
        knockback: 60
    }, {
        id: 5,
        itemType: 0,
        upgradeType: 3,
        isUpgrade: false,
        type: 0,
        age: 2,
        name: "polearm",
        description: "long range melee weapon",
        src: "spear_1",
        iPad: 1.3,
        length: 130,
        width: 210,
        xOffset: -8,
        yOffset: 53,
        damage: 45,
        knock: .2,
        spdMult: .82,
        range: 142,
        gather: 1,
        speed: 700,
        knockback: 100
    }, {
        id: 6,
        itemType: 0,
        upgradeType: 4,
        isUpgrade: false,
        type: 0,
        age: 2,
        name: "bat",
        description: "fast long range melee weapon",
        src: "bat_1",
        iPad: 1.3,
        length: 110,
        width: 180,
        xOffset: -8,
        yOffset: 53,
        damage: 20,
        knock: .7,
        spdMult: 1,
        range: 110,
        gather: 1,
        speed: 300,
        knockback: 204
    }, {
        id: 7,
        itemType: 0,
        upgradeType: 5,
        isUpgrade: false,
        type: 0,
        age: 2,
        name: "daggers",
        description: "really fast short range weapon",
        src: "dagger_1",
        iPad: .8,
        length: 110,
        width: 110,
        xOffset: 18,
        yOffset: 0,
        damage: 20,
        knock: .1,
        range: 65,
        gather: 1,
        hitSlow: .1,
        spdMult: 1.13,
        speed: 100,
        knockback: 80
    }, {
        id: 8,
        itemType: 0,
        upgradeType: 6,
        isUpgrade: false,
        type: 0,
        age: 2,
        name: "stick",
        description: "great for gathering but very weak",
        src: "stick_1",
        length: 140,
        width: 140,
        xOffset: 3,
        yOffset: 24,
        damage: 1,
        spdMult: 1,
        range: 70,
        gather: 7,
        speed: 400,
        knockback: 60
    }, {
        id: 9,
        itemType: 1,
        upgradeType: 7,
        projectile: 0,
        type: 1,
        age: 6,
        name: "hunting bow",
        description: "bow used for ranged combat and hunting",
        src: "bow_1",
        cost: {
            food: 0,
            wood: 4,
            stone: 0,
            gold: 0
        },
        length: 120,
        width: 120,
        xOffset: -6,
        yOffset: 0,
        spdMult: .75,
        speed: 600,
        range: 1e3,
        knockback: 60
    }, {
        id: 10,
        itemType: 1,
        upgradeType: 8,
        isUpgrade: false,
        type: 1,
        age: 6,
        name: "great hammer",
        description: "hammer used for destroying structures",
        src: "great_hammer_1",
        length: 140,
        width: 140,
        xOffset: -9,
        yOffset: 25,
        damage: 10,
        spdMult: .88,
        range: 75,
        sDmg: 7.5,
        gather: 1,
        speed: 400,
        knockback: 60
    }, {
        id: 11,
        itemType: 1,
        upgradeType: 9,
        isUpgrade: false,
        type: 1,
        age: 6,
        name: "wooden shield",
        description: "blocks projectiles and reduces melee damage",
        src: "shield_1",
        length: 120,
        width: 120,
        shield: .2,
        xOffset: 6,
        yOffset: 0,
        spdMult: .7,
        speed: 1,
        range: 0,
        knockback: 0
    }, {
        id: 12,
        itemType: 1,
        upgradeType: 7,
        projectile: 2,
        upgradeOf: 9,
        type: 1,
        age: 8,
        pre: 9,
        name: "crossbow",
        description: "deals more damage and has greater range",
        src: "crossbow_1",
        cost: {
            food: 0,
            wood: 5,
            stone: 0,
            gold: 0
        },
        aboveHand: true,
        armS: .75,
        length: 120,
        width: 120,
        xOffset: -4,
        yOffset: 0,
        spdMult: .7,
        speed: 700,
        range: 1200,
        knockback: 60
    }, {
        id: 13,
        itemType: 1,
        upgradeType: 7,
        projectile: 3,
        upgradeOf: 12,
        type: 1,
        age: 9,
        pre: 12,
        name: "repeater crossbow",
        description: "high firerate crossbow with reduced damage",
        src: "crossbow_2",
        cost: {
            food: 0,
            wood: 10,
            stone: 0,
            gold: 0
        },
        aboveHand: true,
        armS: .75,
        length: 120,
        width: 120,
        xOffset: -4,
        yOffset: 0,
        spdMult: .7,
        speed: 230,
        range: 1200,
        knockback: 60
    }, {
        id: 14,
        itemType: 1,
        upgradeType: 10,
        isUpgrade: false,
        type: 1,
        age: 6,
        name: "mc grabby",
        description: "steals resources from enemies",
        src: "grab_1",
        length: 130,
        width: 210,
        xOffset: -8,
        yOffset: 53,
        damage: 0,
        steal: 250,
        knock: .2,
        spdMult: 1.05,
        range: 125,
        gather: 0,
        speed: 700,
        knockback: 100
    }, {
        id: 15,
        itemType: 1,
        upgradeType: 7,
        projectile: 5,
        upgradeOf: 12,
        type: 1,
        age: 9,
        pre: 12,
        name: "musket",
        description: "slow firerate but high damage and range",
        src: "musket_1",
        cost: {
            food: 0,
            wood: 0,
            stone: 10,
            gold: 0
        },
        aboveHand: true,
        rec: .35,
        armS: .6,
        hndS: .3,
        hndD: 1.6,
        length: 205,
        width: 205,
        xOffset: 25,
        yOffset: 0,
        hideProjectile: true,
        spdMult: .6,
        speed: 1500,
        range: 1400,
        knockback: 60
    } ];

    const ItemGroups = {
        [1]: {
            name: "Wall",
            limit: 30,
            layer: 0
        },
        [2]: {
            name: "Spike",
            limit: 15,
            layer: 0
        },
        [3]: {
            name: "Windmill",
            limit: 7,
            sandboxLimit: 299,
            layer: 1
        },
        [4]: {
            name: "Mine",
            limit: 1,
            layer: 0
        },
        [5]: {
            name: "Trap",
            limit: 6,
            layer: -1
        },
        [6]: {
            name: "Boost",
            limit: 12,
            sandboxLimit: 299,
            layer: -1
        },
        [7]: {
            name: "Turret",
            limit: 2,
            layer: 1
        },
        [8]: {
            name: "Plaftorm",
            limit: 12,
            layer: -1
        },
        [9]: {
            name: "Healing pad",
            limit: 4,
            layer: -1
        },
        [10]: {
            name: "Spawn",
            limit: 1,
            layer: -1
        },
        [11]: {
            name: "Sapling",
            limit: 2,
            layer: 0
        },
        [12]: {
            name: "Blocker",
            limit: 3,
            layer: -1
        },
        [13]: {
            name: "Teleporter",
            limit: 2,
            sandboxLimit: 299,
            layer: -1
        }
    };

    const Items = [ {
        id: 0,
        itemType: 2,
        name: "apple",
        description: "restores 20 health when consumed",
        age: 0,
        cost: {
            food: 10,
            wood: 0,
            stone: 0,
            gold: 0
        },
        restore: 20,
        scale: 22,
        holdOffset: 15
    }, {
        id: 1,
        itemType: 2,
        upgradeOf: 0,
        name: "cookie",
        description: "restores 40 health when consumed",
        age: 3,
        cost: {
            food: 15,
            wood: 0,
            stone: 0,
            gold: 0
        },
        restore: 40,
        scale: 27,
        holdOffset: 15
    }, {
        id: 2,
        itemType: 2,
        upgradeOf: 1,
        name: "cheese",
        description: "restores 30 health and another 50 over 5 seconds",
        age: 7,
        cost: {
            food: 25,
            wood: 0,
            stone: 0,
            gold: 0
        },
        restore: 30,
        scale: 27,
        holdOffset: 15
    }, {
        id: 3,
        itemType: 3,
        itemGroup: 1,
        name: "wood wall",
        description: "provides protection for your village",
        age: 0,
        cost: {
            food: 0,
            wood: 10,
            stone: 0,
            gold: 0
        },
        projDmg: true,
        health: 380,
        scale: 50,
        holdOffset: 20,
        placeOffset: -5
    }, {
        id: 4,
        itemType: 3,
        itemGroup: 1,
        upgradeOf: 3,
        name: "stone wall",
        description: "provides improved protection for your village",
        age: 3,
        cost: {
            food: 0,
            wood: 0,
            stone: 25,
            gold: 0
        },
        health: 900,
        scale: 50,
        holdOffset: 20,
        placeOffset: -5
    }, {
        pre: 1,
        id: 5,
        itemType: 3,
        itemGroup: 1,
        upgradeOf: 4,
        name: "castle wall",
        description: "provides powerful protection for your village",
        age: 7,
        cost: {
            food: 0,
            wood: 0,
            stone: 35,
            gold: 0
        },
        health: 1500,
        scale: 52,
        holdOffset: 20,
        placeOffset: -5
    }, {
        id: 6,
        itemType: 4,
        itemGroup: 2,
        name: "spikes",
        description: "damages enemies when they touch them",
        age: 0,
        cost: {
            food: 0,
            wood: 20,
            stone: 5,
            gold: 0
        },
        health: 400,
        damage: 20,
        scale: 49,
        spritePadding: -23,
        holdOffset: 8,
        placeOffset: -5
    }, {
        id: 7,
        itemType: 4,
        itemGroup: 2,
        upgradeOf: 6,
        name: "greater spikes",
        description: "damages enemies when they touch them",
        age: 5,
        cost: {
            food: 0,
            wood: 30,
            stone: 10,
            gold: 0
        },
        health: 500,
        damage: 35,
        scale: 52,
        spritePadding: -23,
        holdOffset: 8,
        placeOffset: -5
    }, {
        id: 8,
        itemType: 4,
        itemGroup: 2,
        upgradeOf: 7,
        name: "poison spikes",
        description: "poisons enemies when they touch them",
        age: 9,
        pre: 1,
        cost: {
            food: 0,
            wood: 35,
            stone: 15,
            gold: 0
        },
        health: 600,
        damage: 30,
        poisonDamage: 5,
        scale: 52,
        spritePadding: -23,
        holdOffset: 8,
        placeOffset: -5
    }, {
        id: 9,
        itemType: 4,
        itemGroup: 2,
        upgradeOf: 7,
        name: "spinning spikes",
        description: "damages enemies when they touch them",
        age: 9,
        pre: 2,
        cost: {
            food: 0,
            wood: 30,
            stone: 20,
            gold: 0
        },
        health: 500,
        damage: 45,
        turnSpeed: .003,
        scale: 52,
        spritePadding: -23,
        holdOffset: 8,
        placeOffset: -5
    }, {
        id: 10,
        itemType: 5,
        itemGroup: 3,
        name: "windmill",
        description: "generates gold over time",
        age: 0,
        cost: {
            food: 0,
            wood: 50,
            stone: 10,
            gold: 0
        },
        health: 400,
        pps: 1,
        turnSpeed: .0016,
        spritePadding: 25,
        iconLineMult: 12,
        scale: 45,
        holdOffset: 20,
        placeOffset: 5
    }, {
        id: 11,
        itemType: 5,
        itemGroup: 3,
        upgradeOf: 10,
        name: "faster windmill",
        description: "generates more gold over time",
        age: 5,
        pre: 1,
        cost: {
            food: 0,
            wood: 60,
            stone: 20,
            gold: 0
        },
        health: 500,
        pps: 1.5,
        turnSpeed: .0025,
        spritePadding: 25,
        iconLineMult: 12,
        scale: 47,
        holdOffset: 20,
        placeOffset: 5
    }, {
        id: 12,
        itemType: 5,
        itemGroup: 3,
        upgradeOf: 11,
        name: "power mill",
        description: "generates more gold over time",
        age: 8,
        pre: 1,
        cost: {
            food: 0,
            wood: 100,
            stone: 50,
            gold: 0
        },
        health: 800,
        pps: 2,
        turnSpeed: .005,
        spritePadding: 25,
        iconLineMult: 12,
        scale: 47,
        holdOffset: 20,
        placeOffset: 5
    }, {
        id: 13,
        itemType: 6,
        itemGroup: 4,
        name: "mine",
        description: "allows you to mine stone",
        age: 5,
        type: 2,
        cost: {
            food: 0,
            wood: 20,
            stone: 100,
            gold: 0
        },
        iconLineMult: 12,
        scale: 65,
        holdOffset: 20,
        placeOffset: 0
    }, {
        id: 14,
        itemType: 6,
        itemGroup: 11,
        name: "sapling",
        description: "allows you to farm wood",
        age: 5,
        type: 0,
        cost: {
            food: 0,
            wood: 150,
            stone: 0,
            gold: 0
        },
        iconLineMult: 12,
        colDiv: .5,
        scale: 110,
        holdOffset: 50,
        placeOffset: -15
    }, {
        id: 15,
        itemType: 7,
        itemGroup: 5,
        name: "pit trap",
        description: "pit that traps enemies if they walk over it",
        age: 4,
        cost: {
            food: 0,
            wood: 30,
            stone: 30,
            gold: 0
        },
        trap: true,
        ignoreCollision: true,
        hideFromEnemy: true,
        health: 500,
        colDiv: .2,
        scale: 50,
        holdOffset: 20,
        placeOffset: -5
    }, {
        id: 16,
        itemType: 7,
        itemGroup: 6,
        name: "boost pad",
        description: "provides boost when stepped on",
        age: 4,
        cost: {
            food: 0,
            wood: 5,
            stone: 20,
            gold: 0
        },
        boostSpeed: 1.5,
        health: 150,
        colDiv: .7,
        scale: 45,
        holdOffset: 20,
        placeOffset: -5
    }, {
        id: 17,
        itemType: 8,
        itemGroup: 7,
        name: "turret",
        description: "defensive structure that shoots at enemies",
        age: 7,
        doUpdate: true,
        cost: {
            food: 0,
            wood: 200,
            stone: 150,
            gold: 0
        },
        health: 800,
        projectile: 1,
        shootRange: 700,
        shootRate: 2200,
        scale: 43,
        holdOffset: 20,
        placeOffset: -5
    }, {
        id: 18,
        itemType: 8,
        itemGroup: 8,
        name: "platform",
        description: "platform to shoot over walls and cross over water",
        age: 7,
        cost: {
            food: 0,
            wood: 20,
            stone: 0,
            gold: 0
        },
        ignoreCollision: true,
        zIndex: 1,
        health: 300,
        scale: 43,
        holdOffset: 20,
        placeOffset: -5
    }, {
        id: 19,
        itemType: 8,
        itemGroup: 9,
        name: "healing pad",
        description: "standing on it will slowly heal you",
        age: 7,
        cost: {
            food: 10,
            wood: 30,
            stone: 0,
            gold: 0
        },
        ignoreCollision: true,
        healCol: 15,
        health: 400,
        colDiv: .7,
        scale: 45,
        holdOffset: 20,
        placeOffset: -5
    }, {
        id: 20,
        itemType: 9,
        itemGroup: 10,
        name: "spawn pad",
        description: "you will spawn here when you die but it will dissapear",
        age: 9,
        cost: {
            food: 0,
            wood: 100,
            stone: 100,
            gold: 0
        },
        health: 400,
        ignoreCollision: true,
        spawnPoint: true,
        scale: 45,
        holdOffset: 20,
        placeOffset: -5
    }, {
        id: 21,
        itemType: 8,
        itemGroup: 12,
        name: "blocker",
        description: "blocks building in radius",
        age: 7,
        cost: {
            food: 0,
            wood: 30,
            stone: 25,
            gold: 0
        },
        ignoreCollision: true,
        blocker: 300,
        health: 400,
        colDiv: .7,
        scale: 45,
        holdOffset: 20,
        placeOffset: -5
    }, {
        id: 22,
        itemType: 8,
        itemGroup: 13,
        name: "teleporter",
        description: "teleports you to a random point on the map",
        age: 7,
        cost: {
            food: 0,
            wood: 60,
            stone: 60,
            gold: 0
        },
        teleport: true,
        health: 200,
        colDiv: .7,
        scale: 45,
        holdOffset: 20,
        placeOffset: -5
    } ];

    const WeaponVariants = [ {
        id: 0,
        src: "",
        xp: 1,
        needXP: 0,
        val: 1,
        color: "#7e7e90"
    }, {
        id: 1,
        src: "_g",
        xp: 3e3,
        needXP: 3e3,
        val: 1.1,
        color: "#f7cf45"
    }, {
        id: 2,
        src: "_d",
        xp: 7e3,
        needXP: 4e3,
        val: 1.18,
        color: "#6d91cb"
    }, {
        id: 3,
        src: "_r",
        poison: true,
        xp: 12e3,
        needXP: 5e3,
        val: 1.18,
        color: "#be5454"
    } ];

    const Projectiles = [ {
        id: 0,
        name: "Hunting bow",
        index: 0,
        layer: 0,
        src: "arrow_1",
        damage: 25,
        scale: 103,
        range: 1e3,
        speed: 1.6
    }, {
        id: 1,
        name: "Turret",
        index: 1,
        layer: 1,
        damage: 25,
        scale: 20,
        speed: 1.5,
        range: 700
    }, {
        id: 2,
        name: "Crossbow",
        index: 0,
        layer: 0,
        src: "arrow_1",
        damage: 35,
        scale: 103,
        range: 1200,
        speed: 2.5
    }, {
        id: 3,
        name: "Repeater crossbow",
        index: 0,
        layer: 0,
        src: "arrow_1",
        damage: 30,
        scale: 103,
        range: 1200,
        speed: 2
    }, {
        id: 4,
        index: 1,
        layer: 1,
        damage: 16,
        scale: 20,
        range: 0,
        speed: 0
    }, {
        id: 5,
        name: "Musket",
        index: 0,
        layer: 0,
        src: "bullet_1",
        damage: 50,
        scale: 160,
        range: 1400,
        speed: 3.6
    } ];

    class Vector {
        x;
        y;
        constructor(x = 0, y = 0) {
            this.x = x;
            this.y = y;
        }
        static fromAngle(angle, length = 1) {
            return new Vector(Math.cos(angle) * length, Math.sin(angle) * length);
        }
        add(vec) {
            if (vec instanceof Vector) {
                this.x += vec.x;
                this.y += vec.y;
            } else {
                this.x += vec;
                this.y += vec;
            }
            return this;
        }
        sub(vec) {
            if (vec instanceof Vector) {
                this.x -= vec.x;
                this.y -= vec.y;
            } else {
                this.x -= vec;
                this.y -= vec;
            }
            return this;
        }
        mult(scalar) {
            this.x *= scalar;
            this.y *= scalar;
            return this;
        }
        div(scalar) {
            const inv = 1 / scalar;
            this.x *= inv;
            this.y *= inv;
            return this;
        }
        get length() {
            return Math.hypot(this.x, this.y);
        }
        normalizeVec() {
            const len = this.length;
            if (len > 0) {
                const inv = 1 / len;
                this.x *= inv;
                this.y *= inv;
            }
            return this;
        }
        dot(vec) {
            return this.x * vec.x + this.y * vec.y;
        }
        _setXY(x, y) {
            this.x = x;
            this.y = y;
            return this;
        }
        setVec(vec) {
            return this._setXY(vec.x, vec.y);
        }
        setLength(value) {
            return this.normalizeVec().mult(value);
        }
        copy() {
            return new Vector(this.x, this.y);
        }
        distanceDefault(vec) {
            const dx = this.x - vec.x;
            const dy = this.y - vec.y;
            return dx * dx + dy * dy;
        }
        distance(vec) {
            const dx = this.x - vec.x;
            const dy = this.y - vec.y;
            return Math.hypot(dx, dy);
        }
        angle(vec) {
            return Math.atan2(vec.y - this.y, vec.x - this.x);
        }
        addDirection(angle, length) {
            const x = this.x + Math.cos(angle) * length;
            const y = this.y + Math.sin(angle) * length;
            return new Vector(x, y);
        }
        isEqual(vec) {
            return this.x === vec.x && this.y === vec.y;
        }
        makeString() {
            return this.x + ":" + this.y;
        }
    }

    const Vector_default = Vector;

    const getAngle = (x1, y1, x2, y2) => Math.atan2(y2 - y1, x2 - x1);

    const getDistance = (x1, y1, x2, y2) => Math.hypot(x1 - x2, y1 - y2);

    const clamp = (value, min, max) => Math.min(Math.max(value, min), max);

    const fixTo = (value, fraction) => parseFloat(value.toFixed(fraction));

    const PI = Math.PI;

    const PI2 = PI * 2;

    const getAngleDist = (a, b) => {
        const p = Math.abs(b - a) % (PI * 2);
        return p > PI ? PI * 2 - p : p;
    };

    const findMiddleAngle = (a, b) => {
        const x = Math.cos(a) + Math.cos(b);
        const y = Math.sin(a) + Math.sin(b);
        return Math.atan2(y, x);
    };

    const toRadians = degrees => degrees * (PI / 180);

    const removeFast = (array, index) => {
        if (index < 0 || index >= array.length) {
            throw new RangeError("removeFast: Index out of range");
        }
        if (index === array.length - 1) {
            array.pop();
        } else {
            array[index] = array.pop();
        }
    };

    const lerp = (start, end, factor) => (1 - factor) * start + factor * end;

    const reverseAngle = angle => Math.atan2(-Math.sin(angle), -Math.cos(angle));

    const getTargetValue = (target, prop) => target[prop];

    const setTargetValue = (target, prop, value) => {
        target[prop] = value;
    };

    const formatDate = date => {
        if (date == null) {
            date = new Date;
        }
        const hours = (date.getHours() + "").padStart(2, "0");
        const minutes = (date.getMinutes() + "").padStart(2, "0");
        const seconds = (date.getSeconds() + "").padStart(2, "0");
        return `${hours}:${minutes}:${seconds}`;
    };

    const incrementor = () => {
        let value = 0;
        return function() {
            return value++;
        };
    };

    const getUniqueID = incrementor();

    const EPS = 1e-9;

    const pointInsideRect = (p, rs, re) => p.x >= rs.x - EPS && p.x <= re.x + EPS && p.y >= rs.y - EPS && p.y <= re.y + EPS;

    const lineIntersectsLine = (p, p2, q, q2) => {
        const r = p2.copy().sub(p);
        const s = q2.copy().sub(q);
        const rxs = r.x * s.y - r.y * s.x;
        const q_p = q.copy().sub(p);
        const qpxr = q_p.x * r.y - q_p.y * r.x;
        if (Math.abs(rxs) < EPS) {
            if (Math.abs(qpxr) < EPS) {
                const t0 = (q_p.x * r.x + q_p.y * r.y) / (r.x * r.x + r.y * r.y);
                const t1 = t0 + (s.x * r.x + s.y * r.y) / (r.x * r.x + r.y * r.y);
                return Math.max(0, Math.min(t0, t1)) <= Math.min(1, Math.max(t0, t1));
            }
            return false;
        }
        const t = (q_p.x * s.y - q_p.y * s.x) / rxs;
        const u = (q_p.x * r.y - q_p.y * r.x) / rxs;
        return t >= 0 && t <= 1 && u >= 0 && u <= 1;
    };

    const lineIntersectsRect = (lineStart, lineEnd, rectStart, rectEnd) => pointInsideRect(lineStart, rectStart, rectEnd) || pointInsideRect(lineEnd, rectStart, rectEnd) || lineIntersectsLine(lineStart, lineEnd, rectStart, new Vector_default(rectEnd.x, rectStart.y)) || lineIntersectsLine(lineStart, lineEnd, new Vector_default(rectEnd.x, rectStart.y), rectEnd) || lineIntersectsLine(lineStart, lineEnd, rectEnd, new Vector_default(rectStart.x, rectEnd.y)) || lineIntersectsLine(lineStart, lineEnd, new Vector_default(rectStart.x, rectEnd.y), rectStart);

    const isActiveInput = () => {
        const active = document.activeElement || document.body;
        return active instanceof HTMLInputElement || active instanceof HTMLTextAreaElement;
    };

    const getAngleFromBitmask = (bitmask, rotate) => {
        const vec = {
            x: 0,
            y: 0
        };
        if (bitmask & 1) {
            vec.y--;
        }
        if (bitmask & 2) {
            vec.y++;
        }
        if (bitmask & 4) {
            vec.x--;
        }
        if (bitmask & 8) {
            vec.x++;
        }
        if (rotate) {
            vec.x *= -1;
            vec.y *= -1;
        }
        return vec.x === 0 && vec.y === 0 ? null : Math.atan2(vec.y, vec.x);
    };

    const formatCode = code => {
        code += "";
        if (code === "Backspace") {
            return code;
        }
        if (code === "Escape") {
            return "ESC";
        }
        if (code === "Delete") {
            return "DEL";
        }
        if (code === "Minus") {
            return "-";
        }
        if (code === "Equal") {
            return "=";
        }
        if (code === "BracketLeft") {
            return "[";
        }
        if (code === "BracketRight") {
            return "]";
        }
        if (code === "Slash") {
            return "/";
        }
        if (code === "Backslash") {
            return "\\";
        }
        if (code === "Quote") {
            return "'";
        }
        if (code === "Backquote") {
            return "`";
        }
        if (code === "Semicolon") {
            return ";";
        }
        if (code === "Comma") {
            return ",";
        }
        if (code === "Period") {
            return ".";
        }
        if (code === "CapsLock") {
            return "CAPS";
        }
        if (code === "ContextMenu") {
            return "CTXMENU";
        }
        if (code === "NumLock") {
            return "LOCK";
        }
        return code.replace(/^Page/, "PG").replace(/^Digit/, "").replace(/Button$/, "BTN").replace(/^Key/, "").replace(/^(Shift|Control|Alt)(L|R).*$/, "$2$1").replace(/Control/, "CTRL").replace(/^Arrow/, "").replace(/^Numpad/, "NUM").replace(/Decimal/, "DEC").replace(/Subtract/, "SUB").replace(/Divide/, "DIV").replace(/Multiply/, "MULT").toUpperCase();
    };

    const formatButton = button => {
        if (button === 0) {
            return "LBTN";
        }
        if (button === 1) {
            return "MBTN";
        }
        if (button === 2) {
            return "RBTN";
        }
        if (button === 3) {
            return "BBTN";
        }
        if (button === 4) {
            return "FBTN";
        }
        throw Error(`formatButton Error: "${button}" is not valid button`);
    };

    const removeClass = (target, name) => {
        if (target instanceof HTMLElement) {
            target.classList.remove(name);
            return;
        }
        for (const element of target) {
            element.classList.remove(name);
        }
    };

    const pointInRiver = position => {
        const y = position.y;
        const below = y >= Config_default.mapScale / 2 - Config_default.riverWidth / 2;
        const above = y <= Config_default.mapScale / 2 + Config_default.riverWidth / 2;
        return below && above;
    };

    const pointInDesert = position => position.y >= Config_default.mapScale - Config_default.snowBiomeTop;

    const inRange = (value, min, max) => value >= min && value <= max;

    const targetInsideRect = (target, rectPos, radius) => {
        const screen = new Vector_default(1920, 1080).div(2).add(radius);
        const rectStart = rectPos.copy().sub(screen);
        const rectEnd = rectPos.copy().add(screen);
        return pointInsideRect(target, rectStart, rectEnd);
    };

    const findPlacementAngles = angles => {
        const output = new Set;
        for (let i = 0; i < angles.length; i++) {
            const [angle, offset] = angles[i];
            const start = angle - offset;
            const end = angle + offset;
            let startIntersects = false;
            let endIntersects = false;
            for (let j = 0; j < angles.length; j++) {
                if (startIntersects && endIntersects) {
                    break;
                }
                if (i === j) {
                    continue;
                }
                const [angle2, offset2] = angles[j];
                if (getAngleDist(start, angle2) <= offset2) {
                    startIntersects = true;
                }
                if (getAngleDist(end, angle2) <= offset2) {
                    endIntersects = true;
                }
            }
            if (!startIntersects) {
                output.add(start);
            }
            if (!endIntersects) {
                output.add(end);
            }
        }
        return [ ...output ];
    };

    const createAction = (callback, time = 0) => {
        let state = false;
        const timeoutID = setTimeout(() => {
            if (state) {
                return;
            }
            state = true;
            callback();
        }, time);
        return () => {
            if (state) {
                return;
            }
            state = true;
            clearTimeout(timeoutID);
            callback();
        };
    };

    class CustomStorage {
        static get(key) {
            const value = window.localStorage.getItem(key);
            return value === null ? null : JSON.parse(value);
        }
        static set(key, value, stringify = true) {
            const data = stringify ? JSON.stringify(value) : value;
            window.localStorage.setItem(key, data);
        }
        static delete(key) {
            const has = window.localStorage.hasOwnProperty(key) && key in window.localStorage;
            window.localStorage.removeItem(key);
            return has;
        }
    }

    const Header_default = '<header>\r\n    <div id="credits">\r\n        <svg version="1.1" id="logo" viewBox="0 0 1024 1024" xmlns="http://www.w3.org/2000/svg">\r\n        <path transform="translate(868.08 108.59)" d="m0 0c0.70463-0.0067323 1.4093-0.013465 2.1352-0.020401 6.4762 0.12104 11.035 2.1066 15.783 6.4267 6.7355 7.1685 7.4975 15.175 7.2769 24.712-0.32818 6.7315-1.9685 13.117-3.7144 19.6-0.39653 1.5245-0.79241 3.0492-1.1877 4.574-15.141 57.747-33.221 114.75-51.15 171.68-0.77339 2.4566-1.5457 4.9135-2.3178 7.3705-4.8024 15.273-9.6359 30.535-14.809 45.687-0.51513 1.5277-0.51513 1.5277-1.0407 3.0862-5.8617 16.918-5.8617 16.918-12.244 22.918-0.67418 0.65227-1.3484 1.3045-2.043 1.9766-1.7695 1.3984-1.7695 1.3984-3.7695 1.3984v2c-2.0273 1.7234-4.0653 3.3381-6.1875 4.9375-4.8734 3.7442-9.6517 7.5565-14.312 11.562-4.471 3.8341-9.032 7.5173-13.688 11.125-4.9944 3.8756-9.7402 7.9242-14.398 12.203-3.3976 3.0568-6.9447 5.9139-10.496 8.7891-3.7343 3.0494-7.405 6.1702-11.077 9.2942-3.4521 2.9308-6.943 5.8055-10.466 8.6511-4.7271 3.842-9.2068 7.9069-13.688 12.031-3.2993 2.954-6.7453 5.6796-10.227 8.4141-3.423 2.771-6.6461 5.7432-9.8984 8.7109-2.6078 2.3215-5.2829 4.5266-8 6.7188-4.7768 3.8631-9.302 7.9416-13.82 12.102-2.6423 2.3713-5.3491 4.6135-8.1172 6.8359-4.2031 3.3889-8.1871 6.9374-12.125 10.625-4.7712 4.4679-9.6791 8.6676-14.785 12.754-3.9854 3.2972-7.737 6.8279-11.5 10.375-2.2148 1.8711-2.2148 1.8711-4.2148 1.8711v2c-1.2227 1.2695-1.2227 1.2695-3.0625 2.8125-0.72574 0.61746-1.4515 1.2349-2.1992 1.8711-0.90363 0.76441-1.8073 1.5288-2.7383 2.3164-2.4635 2.119-4.9193 4.2469-7.375 6.375-0.6546 0.56598-1.3092 1.132-1.9836 1.7151-3.6698 3.1784-7.3014 6.3911-10.891 9.6599-3.2287 2.9318-6.5326 5.7126-9.9375 8.4375-5.3248 4.3005-10.273 8.933-15.238 13.637-4.625 4.3579-9.3867 8.402-14.403 12.308-2.0969 1.8028-3.6149 3.5924-5.1719 5.8672 5.208 2.3208 10.456 4.2336 15.875 6 4.5547 1.5 4.5547 1.5 6.8157 2.2454 1.6015 0.52332 3.2057 1.0382 4.812 1.5464 0.80478 0.25822 1.6096 0.51643 2.4387 0.78247 0.72905 0.23034 1.4581 0.46068 2.2092 0.698 2.6191 1.0307 3.9951 2.6343 5.8494 4.7278 1.2792 0.95451 2.5725 1.8902 3.875 2.8125 7.5329 5.5831 11.921 11.63 13.938 20.938 1.1447 13.632-5.9612 26.77-14.188 37.188-15.306 17.463-37.523 33.314-58.625 43.062h-2l-1 2c-9.832 3.3392-20.457 3.193-30-1-9.0874-4.8402-17.029-11.545-25-18-1.0018-0.81042-1.0018-0.81042-2.0239-1.6372-3.4276-2.7755-6.85-5.5573-10.269-8.3433-4.5453-3.7035-9.0945-7.3997-13.707-11.02-0.64324-0.51434-1.2865-1.0287-1.9492-1.5586-3.6186-2.7709-6.4181-4.8196-11.051-4.4414-3.0465 1.9411-5.465 4.4432-8 7-0.89461 0.87012-1.7892 1.7402-2.7109 2.6367-4.6551 4.5722-9.1144 9.2354-13.348 14.203-2.5425 2.829-5.236 5.4878-7.9414 8.1602-3.2221 3.1829-6.3905 6.3469-9.3125 9.8125-4.0741 4.7984-8.604 9.1542-13.095 13.558-3.1238 3.0815-6.1309 6.1991-8.991 9.5281-4.0078 4.6483-8.3527 8.9253-12.727 13.227-2.9835 2.9345-5.9455 5.8865-8.875 8.875-0.54793 0.5431-1.0959 1.0862-1.6604 1.6458-2.4213 2.5837-3.3138 4.1479-3.7576 7.6941 0.076055 1.1872 0.15211 2.3745 0.23047 3.5977 0.047874 1.3357 0.088031 2.6717 0.12109 4.0078 0.017886 0.67579 0.035771 1.3516 0.054199 2.0479 0.13648 22.438-9.8287 42.623-25.238 58.386-16.639 15.859-38.194 21.12-60.574 20.77-32.474-0.91475-58.907-15.915-81.383-38.352-17.614-18.76-26.234-43.914-27.043-69.359 0.81801-25.407 10.042-46.905 28.438-64.625 12.128-10.629 27.322-17.522 43.197-20.087 8.9085-1.4767 13.784-3.2843 19.51-10.745 0.6948-0.98355 1.3896-1.9671 2.1055-2.9805 1.4259-1.7595 2.8634-3.5096 4.3125-5.25 0.72832-0.90105 1.4566-1.8021 2.207-2.7305 7.2516-8.8275 14.851-17.375 22.516-25.844 3.9882-4.4163 7.8855-8.9089 11.75-13.434 1.0299-1.2058 2.0599-2.4115 3.0898-3.6172 0.51965-0.60852 1.0393-1.217 1.5747-1.844 3.0292-3.5372 6.1018-7.0249 9.2378-10.469 4.6378-5.11 8.9914-10.434 13.312-15.812 1.0886-1.3052 1.0886-1.3052 2.1992-2.6367 2.6966-3.539 3.2616-6.8067 3.1938-11.236-0.74301-4.0206-3.4519-6.5065-6.2056-9.377-0.58878-0.6455-1.1776-1.291-1.7842-1.9561-1.7834-1.9486-3.5909-3.8723-5.4033-5.7939-1.4678-1.5866-2.93-3.178-4.3914-4.7705-1.3503-1.4704-2.706-2.9359-4.0618-4.4014-3.2209-3.5765-6.2239-7.3042-9.2383-11.055-2.4819-2.9817-5.0951-5.8187-7.7461-8.6484-11.792-12.676-21.99-24.809-21.48-43.066 3.407-27.518 27.039-66.699 47.918-84.559 5.9718-4.5112 12.209-7.1966 19.84-6.8477 17.094 2.7511 34.034 17.486 44.098 30.938 4.2859 6.4381 7.3285 13.191 10.062 20.41 7.824-9.5531 15.526-19.17 23-29 2.0817-2.7304 4.1656-5.4591 6.25-8.1875 0.81356-1.0657 0.81356-1.0657 1.6436-2.1528 4.0884-5.348 8.2159-10.664 12.356-15.972 4.6005-5.8986 9.1409-11.833 13.609-17.832 2.3536-3.1396 4.7426-6.2498 7.1406-9.3555 3.8824-5.0298 7.7073-10.099 11.508-15.191 1.8918-2.5232 3.809-5.0258 5.7344-7.5234 7.5051-9.6188 7.5051-9.6188 14.316-19.73 1.3298-1.8955 2.7369-3.5894 4.2539-5.3359 3.1005-3.572 5.9408-7.2908 8.75-11.094 1.0579-1.4211 2.1165-2.8416 3.1758-4.2617 0.53963-0.72365 1.0793-1.4473 1.6353-2.1929 2.6013-3.4712 5.2376-6.9153 7.8765-10.358 0.52964-0.69182 1.0593-1.3836 1.605-2.0964 2.371-3.0966 4.7431-6.1922 7.1172-9.2864 6.9922-9.117 13.973-18.224 20.592-27.617 3.0266-4.2821 6.1935-8.4387 9.4126-12.577 3.6953-4.7679 7.2699-9.6201 10.836-14.485 5.1531-7.0285 10.394-13.981 15.708-20.889 2.9437-3.8331 5.8403-7.6907 8.6675-11.611 2.947-4.0834 5.9477-8.12 9-12.125 0.79793-1.0493 1.5959-2.0986 2.418-3.1797 7.3745-9.0707 16.159-14.641 27.277-18.121 2.2951-0.62073 2.2951-0.62073 3.1172-2.8242 1.8452-0.2245 3.6914-0.44251 5.5404-0.63281 4.8219-0.71986 9.4052-2.3736 14.034-3.8672 1.11-0.35194 2.2199-0.70389 3.3635-1.0665 3.5853-1.1382 7.1675-2.2859 10.75-3.4335 2.4571-0.78153 4.9145-1.5623 7.3721-2.3423 4.8141-1.5283 9.6274-3.0592 14.44-4.5923 7.9059-2.5156 15.825-4.9889 23.75-7.4404 1.0889-0.33773 2.1777-0.67547 3.2996-1.0234 1.9287-0.59704 3.8581-1.192 5.7883-1.7842 1.8337-0.56302 3.6656-1.1317 5.4961-1.7051 0.89525-0.27683 1.7905-0.55365 2.7129-0.83887 0.78729-0.24573 1.5746-0.49146 2.3857-0.74463 2.0674-0.52881 2.0674-0.52881 5.0674-0.52881l1-2c2.0635-0.65381 2.0635-0.65381 4.8906-1.2734 5.3022-1.2515 10.508-2.6858 15.719-4.2656 0.791-0.2396 1.582-0.4792 2.397-0.72606 1.6915-0.51395 3.3826-1.029 5.0735-1.545 2.7544-0.84057 5.51-1.6773 8.2659-2.5133 8.5257-2.5879 17.048-5.1863 25.57-7.7864 13.103-3.9975 26.21-7.9851 39.326-11.94 6.004-1.8112 12.003-3.6372 17.996-5.485 3.178-0.97486 6.3616-1.9305 9.5474-2.8797 1.3959-0.41997 2.7895-0.84771 4.1802-1.2846 7.4197-2.3263 14.365-3.6465 22.117-3.7067z" fill="#353C35"/>\r\n        <path transform="translate(843,160)" d="m0 0c0.87909 3.1738 0.98903 4.9646 0.066406 8.1484-0.34938 1.2387-0.34938 1.2387-0.70581 2.5024-0.39506 1.3484-0.39506 1.3484-0.7981 2.7241-0.55849 1.9736-1.1157 3.9476-1.6719 5.9219-0.30357 1.0693-0.60715 2.1386-0.91992 3.2402-1.5967 5.6962-3.1174 11.413-4.6372 17.13-0.50784 1.9089-1.0182 3.8171-1.5285 5.7253-1.4648 5.4908-2.907 10.983-4.262 16.502-1.8468 7.4363-3.9359 14.802-6.043 22.168-0.21587 0.75494-0.43174 1.5099-0.65414 2.2877-8.0126 27.951-17.064 55.512-26.559 82.99-2.8479 8.2577-5.5966 16.548-8.3086 24.851-1.7657 5.3597-3.6081 10.69-5.5405 15.992-0.39316 1.0872-0.78633 2.1745-1.1914 3.2947-0.41121 0.83217-0.82242 1.6643-1.2461 2.5217-3.6956 1.2319-4.5849 0.62215-8.1133-0.83594-1.001-0.40477-2.0019-0.80953-3.0332-1.2266-1.0448-0.43312-2.0896-0.86625-3.166-1.3125-2.0563-0.84665-4.1149-1.688-6.1758-2.5234-0.91306-0.37818-1.8261-0.75636-2.7668-1.146-2.9074-1.0121-5.7004-1.5329-8.7449-1.9556 1.3335 1.3335 2.8308 2.2957 4.3867 3.3633 0.69158 0.47502 1.3832 0.95004 2.0957 1.4395 0.72768 0.49822 1.4554 0.99645 2.2051 1.5098 0.70834 0.48662 1.4167 0.97324 2.1465 1.4746 4.0353 2.7685 8.0873 5.5087 12.166 8.2129-1.5022 3.7389-3.6017 5.5409-6.75 8-4.4989 3.5802-8.9008 7.2395-13.25 11-4.9886 4.3006-10.042 8.5049-15.156 12.656-3.9325 3.2411-7.787 6.5698-11.646 9.8979-3.5828 3.0831-7.2074 6.1011-10.885 9.0708-3.7169 3.0149-7.2893 6.1358-10.812 9.375-4.3903 4.0363-8.9118 7.8403-13.551 11.586-3.3629 2.7527-6.6585 5.5758-9.9492 8.4141-4.1022 3.5362-8.228 7.0286-12.438 10.438-5.0518 4.1023-9.9656 8.3495-14.873 12.623-4.0583 3.5322-8.1393 7.0343-12.252 10.502-12.951 10.904-12.951 10.904-25.625 22.125-3.2492 2.9538-6.5712 5.757-10 8.5-6.0657 4.9025-11.694 10.235-17.367 15.582-3.1257 2.9433-6.314 5.7988-9.5664 8.6016-4.0147 3.4805-7.935 7.0686-11.879 10.629-1.6664 1.5003-3.3331 3.0003-5 4.5-0.82887 0.74637-1.6577 1.4927-2.5117 2.2617-1.626 1.4627-3.2536 2.9237-4.8828 4.3828-8.3305 7.4692-16.56 15.047-24.711 22.711-0.69916 0.65726-1.3983 1.3145-2.1187 1.9917-1.3493 1.2698-2.6973 2.5409-4.0439 3.8135-4.4852 4.2235-9.0804 8.3005-13.732 12.339-1.6688 1.4768-3.3359 2.9554-5 4.4375-0.76312 0.67934-1.5262 1.3587-2.3125 2.0586-0.83531 0.74443-0.83531 0.74443-1.6875 1.5039-3.5083-1.5208-5.9527-3.5996-8.75-6.1875-2.9494-2.7054-5.8997-5.3943-8.9375-8-4.6095-4.0135-9.0492-8.2078-13.509-12.386-5.8936-5.5207-11.839-10.983-17.804-16.427 5.0137-5.9623 10.266-11.693 15.544-17.419 2.3231-2.5226 4.639-5.0519 6.9556-7.5806 0.92056-1.0039 1.8411-2.0078 2.7617-3.0117 1.7961-1.9592 3.59-3.9205 5.3828-5.8828 5.1673-5.6515 10.371-11.266 15.605-16.855 4.0531-4.3292 8.0554-8.6815 11.926-13.176 2.4978-2.8401 5.0669-5.6118 7.6367-8.3867 9.9004-10.674 9.9004-10.674 19.562-21.562 3.6073-4.1544 7.3481-8.1822 11.099-12.207 2.6949-2.8999 5.3367-5.8352 7.9321-8.8247 4.1992-4.8221 8.5917-9.4524 12.988-14.094 3.7604-3.9861 7.4233-8.034 10.996-12.189 1.6392-1.844 3.3487-3.5828 5.1094-5.3105 2.2933-2.258 4.4643-4.56 6.5625-7 5.1684-5.9857 10.626-11.708 16.036-17.474 1.8617-1.9841 3.7216-3.9698 5.5811-5.9561 3.1132-3.3247 6.2293-6.6466 9.3467-9.9673 1.3605-1.4497 2.7205-2.9 4.0801-4.3506 2.1301-2.2727 4.2617-4.5439 6.3936-6.8149 0.6463-0.69013 1.2926-1.3803 1.9585-2.0913 3.0535-3.2496 6.1349-6.4582 9.2993-9.6001 2.3124-2.2965 4.5196-4.6239 6.6172-7.1211 2.5913-3.0097 5.2975-5.8359 8.125-8.625 2.7862-2.7486 5.4531-5.5286 8-8.5 3.18-3.7101 6.5876-7.1298 10.094-10.531 1.9594-2.0103 3.7888-4.0495 5.6172-6.1758 4.0901-4.7132 8.4794-9.0936 12.914-13.48 0.78504-0.78053 1.5701-1.5611 2.3789-2.3652 5.9292-5.8942 5.9292-5.8942 8.1169-8.0286 3.2839-3.2186 5.2875-5.6724 5.4463-10.431-0.0079761-0.71132-0.015952-1.4226-0.02417-2.1555-0.01418-1.2646-0.028359-2.5291-0.042969-3.832-0.8826 0.38333-1.7652 0.76667-2.6746 1.1616-3.2891 1.4283-6.5786 2.8556-9.8682 4.2827-1.421 0.61661-2.8419 1.2335-4.2627 1.8506-2.0476 0.88934-4.0957 1.7778-6.1438 2.666-0.63041 0.27404-1.2608 0.54807-1.9103 0.83041-2.654 1.1501-5.3006 2.2683-8.0116 3.2785-2.707 1.1828-2.9946 2.2719-4.1289 4.9302-1.4805 1.6406-1.4805 1.6406-3.1875 3.25-3.2018 3.0294-6.0544 6.2979-8.9412 9.6226-2.9422 3.3449-5.9993 6.5777-9.0588 9.8149-1.3233 1.4059-2.6462 2.8121-3.9688 4.2188-0.64969 0.69094-1.2994 1.3819-1.9688 2.0938-2.7022 2.8823-5.3852 5.782-8.0625 8.6875-0.4859 0.52715-0.97179 1.0543-1.4724 1.5974-1.922 2.0864-3.8427 4.174-5.7625 6.2625-8.118 8.8299-16.324 17.574-24.552 26.302-5.6877 6.0386-11.357 12.095-17.026 18.151-0.60618 0.64743-1.2124 1.2949-1.8369 1.9619-6.8593 7.3286-13.69 14.682-20.464 22.089-7.7804 8.5011-15.62 16.946-23.49 25.365-3.7309 3.9935-7.4455 8.0013-11.147 12.022-5.716 6.2062-11.487 12.36-17.262 18.512-7.9458 8.4654-15.873 16.948-23.738 25.488-7.6097 8.261-15.309 16.438-22.999 24.624-1.9174 2.0416-3.8344 4.0836-5.751 6.126-0.62117 0.66169-1.2423 1.3234-1.8823 2.0051-3.9812 4.2462-7.9315 8.5194-11.868 12.807-4.4004 4.7913-8.9009 9.4618-13.562 14-5.8423-4.1181-11.1-8.7281-16.355-13.566-4.6205-4.252-9.3708-8.3474-14.145-12.426-0.62673-0.53577-1.2535-1.0715-1.8992-1.6235-1.2542-1.0713-2.5096-2.1413-3.7661-3.21-0.58096-0.49581-1.1619-0.99161-1.7605-1.5024-0.5199-0.44247-1.0398-0.88494-1.5754-1.3408-1.5624-1.3875-3.0357-2.8398-4.4988-4.3311 1.6268-3.6539 3.8669-6.596 6.3125-9.75 0.43441-0.56074 0.86883-1.1215 1.3164-1.6992 4.1028-5.2668 8.3245-10.436 12.55-15.604 3.3615-4.1209 6.6595-8.28 9.8838-12.509 3.5663-4.6743 7.1936-9.2908 10.875-13.875 5.7387-7.148 11.418-14.34 17.062-21.562 0.52288-0.66838 1.0458-1.3368 1.5845-2.0254 8.3281-10.652 16.554-21.378 24.736-32.143 2.9156-3.8344 5.8538-7.6498 8.8047-11.457 4.5205-5.8616 8.8975-11.824 13.273-17.794 4.5458-6.1869 9.1826-12.299 13.852-18.393 4.7428-6.1924 9.4013-12.419 13.884-18.802 3.8186-5.3996 7.843-10.637 11.866-15.885 4.8482-6.3256 9.6231-12.679 14.212-19.195 3.5844-5.0695 7.304-10.033 11.038-14.993 13.008-17.283 25.755-34.749 38.348-52.336 0.59031-0.82234 1.1806-1.6447 1.7888-2.4919 1.1321-1.5772 2.2619-3.1561 3.3892-4.7368 0.50974-0.70955 1.0195-1.4191 1.5447-2.1501 0.44618-0.62383 0.89235-1.2477 1.3521-1.8904 2.4758-3.1838 4.393-4.9888 8.2991-6.1675 0.81133-0.24997 1.6227-0.49994 2.4586-0.75749 0.89321-0.26461 1.7864-0.52921 2.7067-0.80183 0.95336-0.29083 1.9067-0.58166 2.889-0.8813 3.218-0.97942 6.4399-1.9453 9.6618-2.9117 2.2999-0.69745 4.5996-1.3959 6.8989-2.0952 4.3839-1.3323 8.7687-2.6616 13.155-3.9868 9.3777-2.8337 18.747-5.6947 28.114-8.5625 1.5308-0.46858 3.0615-0.93715 4.5923-1.4057 0.76137-0.23306 1.5227-0.46611 2.3072-0.70623 0.76342-0.23368 1.5268-0.46736 2.3134-0.70812 0.76499-0.23418 1.53-0.46836 2.3182-0.70964 8.5298-2.6108 17.062-5.2145 25.594-7.8179 8.9283-2.7244 17.856-5.45 26.781-8.1852 32.342-9.9105 64.783-19.48 97.238-29.01z" fill="#747C77"/>\r\n        <path transform="translate(843,162)" d="m0 0c-0.87914 0.55043-1.7583 1.1009-2.6641 1.668-3.2988 2.2008-5.9543 4.7869-8.7109 7.6445-3.1416 3.223-6.3009 6.3527-9.75 9.25-2.8194 2.4053-5.2724 4.9422-7.707 7.7344-5.6994 6.3871-11.736 12.422-17.798 18.463-1.9365 1.9311-3.8675 3.8675-5.7981 5.8044-5.5335 5.5362-11.049 11.027-17.017 16.099-2.1348 1.8351-4.0956 3.817-6.0549 5.8367-3.4037 3.4505-6.9244 6.6664-10.602 9.8203-2.455 2.1721-4.7288 4.4971-7.0234 6.8359-1.8109 1.7807-3.6764 3.4458-5.6016 5.1016-4.1474 3.6059-8.1554 7.342-12.148 11.117-1.4111 1.322-2.8226 2.6436-4.2344 3.9648-2.2389 2.0989-4.4567 4.211-6.6562 6.3516-12.756 12.144-30.677 19.789-47.234 25.309-0.69964 1.3163-1.363 2.6522-2 4-1.4805 1.6406-1.4805 1.6406-3.1875 3.25-3.2018 3.0294-6.0544 6.2979-8.9412 9.6226-2.9422 3.3449-5.9993 6.5777-9.0588 9.8149-1.3233 1.4059-2.6462 2.8121-3.9688 4.2188-0.64969 0.69094-1.2994 1.3819-1.9688 2.0938-2.7022 2.8823-5.3852 5.782-8.0625 8.6875-0.4859 0.52715-0.97179 1.0543-1.4724 1.5974-1.922 2.0864-3.8427 4.174-5.7625 6.2625-8.118 8.8299-16.324 17.574-24.552 26.302-5.6877 6.0386-11.357 12.095-17.026 18.151-0.60618 0.64743-1.2124 1.2949-1.8369 1.9619-6.8593 7.3286-13.69 14.682-20.464 22.089-7.7804 8.5011-15.62 16.946-23.49 25.365-3.7309 3.9935-7.4455 8.0013-11.147 12.022-5.716 6.2062-11.487 12.36-17.262 18.512-7.9458 8.4654-15.873 16.948-23.738 25.488-7.6097 8.261-15.309 16.438-22.999 24.624-1.9174 2.0416-3.8344 4.0836-5.751 6.126-0.62117 0.66169-1.2423 1.3234-1.8823 2.0051-3.9812 4.2462-7.9315 8.5194-11.868 12.807-4.4004 4.7913-8.9009 9.4618-13.562 14-5.8423-4.1181-11.1-8.7281-16.355-13.566-4.6205-4.252-9.3708-8.3474-14.145-12.426-0.62673-0.53577-1.2535-1.0715-1.8992-1.6235-1.2542-1.0713-2.5096-2.1413-3.7661-3.21-0.58096-0.49581-1.1619-0.99161-1.7605-1.5024-0.5199-0.44247-1.0398-0.88494-1.5754-1.3408-1.5624-1.3875-3.0357-2.8398-4.4988-4.3311 1.6268-3.6539 3.8669-6.596 6.3125-9.75 0.43441-0.56074 0.86883-1.1215 1.3164-1.6992 4.1028-5.2668 8.3245-10.436 12.55-15.604 3.3615-4.1209 6.6595-8.28 9.8838-12.509 3.5663-4.6743 7.1936-9.2908 10.875-13.875 5.7387-7.148 11.418-14.34 17.062-21.562 0.52288-0.66838 1.0458-1.3368 1.5845-2.0254 8.3281-10.652 16.554-21.378 24.736-32.143 2.9156-3.8344 5.8538-7.6498 8.8047-11.457 4.5205-5.8616 8.8975-11.824 13.273-17.794 4.5458-6.1869 9.1826-12.299 13.852-18.393 4.7428-6.1924 9.4013-12.419 13.884-18.802 3.8186-5.3996 7.843-10.637 11.866-15.885 4.8482-6.3256 9.6231-12.679 14.212-19.195 3.5844-5.0695 7.304-10.033 11.038-14.993 13.008-17.283 25.755-34.749 38.348-52.336 0.59031-0.82234 1.1806-1.6447 1.7888-2.4919 1.1321-1.5772 2.2619-3.1561 3.3892-4.7368 0.50974-0.70955 1.0195-1.4191 1.5447-2.1501 0.44618-0.62383 0.89235-1.2477 1.3521-1.8904 2.4758-3.1838 4.393-4.9888 8.2991-6.1675 0.81133-0.24997 1.6227-0.49994 2.4586-0.75749 0.89321-0.26461 1.7864-0.52921 2.7067-0.80183 0.95336-0.29083 1.9067-0.58166 2.889-0.8813 3.218-0.97942 6.4399-1.9453 9.6618-2.9117 2.2999-0.69745 4.5996-1.3959 6.8989-2.0952 4.3839-1.3323 8.7687-2.6616 13.155-3.9868 9.3777-2.8337 18.747-5.6947 28.114-8.5625 3.0712-0.94012 6.1424-1.8802 9.2136-2.8203 1.1475-0.35129 1.1475-0.35129 2.3183-0.70968 9.2804-2.8405 18.563-5.6724 27.846-8.5048 8.2032-2.5031 16.406-5.0088 24.605-7.5237 21.256-6.5191 42.543-12.934 63.862-19.241 2.6425-0.78197 5.2838-1.5678 7.9242-2.357 3.6676-1.0959 7.3393-2.1775 11.012-3.2577 1.6605-0.49876 1.6605-0.49876 3.3544-1.0076 1.0144-0.29583 2.0289-0.59166 3.074-0.89645 0.88496-0.262 1.7699-0.52399 2.6817-0.79393 2.2531-0.43092 2.2531-0.43092 5.2531 0.56908z" fill="#A8AAA1"/>\r\n        <path transform="translate(868.08 108.59)" d="m0 0c0.70463-0.0067323 1.4093-0.013465 2.1352-0.020401 6.4762 0.12104 11.035 2.1066 15.783 6.4267 6.7355 7.1685 7.4975 15.175 7.2769 24.712-0.32818 6.7315-1.9685 13.117-3.7144 19.6-0.39653 1.5245-0.79241 3.0492-1.1877 4.574-15.141 57.747-33.221 114.75-51.15 171.68-0.77339 2.4566-1.5457 4.9135-2.3178 7.3705-4.8024 15.273-9.6359 30.535-14.809 45.687-0.51513 1.5277-0.51513 1.5277-1.0407 3.0862-5.8617 16.918-5.8617 16.918-12.244 22.918-0.67418 0.65227-1.3484 1.3045-2.043 1.9766-1.7695 1.3984-1.7695 1.3984-3.7695 1.3984v2c-2.0273 1.7234-4.0653 3.3381-6.1875 4.9375-4.8734 3.7442-9.6517 7.5565-14.312 11.562-4.471 3.8341-9.032 7.5173-13.688 11.125-4.9944 3.8756-9.7402 7.9242-14.398 12.203-3.3976 3.0568-6.9447 5.9139-10.496 8.7891-3.7343 3.0494-7.405 6.1702-11.077 9.2942-3.4521 2.9308-6.943 5.8055-10.466 8.6511-4.7271 3.842-9.2068 7.9069-13.688 12.031-3.2993 2.954-6.7453 5.6796-10.227 8.4141-3.423 2.771-6.6461 5.7432-9.8984 8.7109-2.6078 2.3215-5.2829 4.5266-8 6.7188-4.7768 3.8631-9.302 7.9416-13.82 12.102-2.6423 2.3713-5.3491 4.6135-8.1172 6.8359-4.2031 3.3889-8.1871 6.9374-12.125 10.625-4.7712 4.4679-9.6791 8.6676-14.785 12.754-3.9854 3.2972-7.737 6.8279-11.5 10.375-2.2148 1.8711-2.2148 1.8711-4.2148 1.8711v2c-1.2227 1.2695-1.2227 1.2695-3.0625 2.8125-0.72574 0.61746-1.4515 1.2349-2.1992 1.8711-0.90363 0.76441-1.8073 1.5288-2.7383 2.3164-2.4635 2.119-4.9193 4.2469-7.375 6.375-0.6546 0.56598-1.3092 1.132-1.9836 1.7151-3.6698 3.1784-7.3014 6.3911-10.891 9.6599-3.2287 2.9318-6.5326 5.7126-9.9375 8.4375-5.3248 4.3005-10.273 8.933-15.238 13.637-4.625 4.3579-9.3867 8.402-14.403 12.308-2.0969 1.8028-3.6149 3.5924-5.1719 5.8672 5.208 2.3208 10.456 4.2336 15.875 6 4.5547 1.5 4.5547 1.5 6.8157 2.2454 1.6015 0.52332 3.2057 1.0382 4.812 1.5464 0.80478 0.25822 1.6096 0.51643 2.4387 0.78247 0.72905 0.23034 1.4581 0.46068 2.2092 0.698 2.6191 1.0307 3.9951 2.6343 5.8494 4.7278 1.2792 0.95451 2.5725 1.8902 3.875 2.8125 7.5329 5.5831 11.921 11.63 13.938 20.938 1.1447 13.632-5.9612 26.77-14.188 37.188-15.306 17.463-37.523 33.314-58.625 43.062h-2l-1 2c-9.832 3.3392-20.457 3.193-30-1-9.0874-4.8402-17.029-11.545-25-18-1.0018-0.81042-1.0018-0.81042-2.0239-1.6372-3.4276-2.7755-6.85-5.5573-10.269-8.3433-4.5453-3.7035-9.0945-7.3997-13.707-11.02-0.64324-0.51434-1.2865-1.0287-1.9492-1.5586-3.6186-2.7709-6.4181-4.8196-11.051-4.4414-3.0465 1.9411-5.465 4.4432-8 7-0.89461 0.87012-1.7892 1.7402-2.7109 2.6367-4.6551 4.5722-9.1144 9.2354-13.348 14.203-2.5425 2.829-5.236 5.4878-7.9414 8.1602-3.2221 3.1829-6.3905 6.3469-9.3125 9.8125-4.0741 4.7984-8.604 9.1542-13.095 13.558-3.1238 3.0815-6.1309 6.1991-8.991 9.5281-4.0078 4.6483-8.3527 8.9253-12.727 13.227-2.9835 2.9345-5.9455 5.8865-8.875 8.875-0.54793 0.5431-1.0959 1.0862-1.6604 1.6458-2.4213 2.5837-3.3138 4.1479-3.7576 7.6941 0.076055 1.1872 0.15211 2.3745 0.23047 3.5977 0.047874 1.3357 0.088031 2.6717 0.12109 4.0078 0.017886 0.67579 0.035771 1.3516 0.054199 2.0479 0.13648 22.438-9.8287 42.623-25.238 58.386-16.639 15.859-38.194 21.12-60.574 20.77-32.474-0.91475-58.907-15.915-81.383-38.352-17.614-18.76-26.234-43.914-27.043-69.359 0.81801-25.407 10.042-46.905 28.438-64.625 12.128-10.629 27.322-17.522 43.197-20.087 8.9085-1.4767 13.784-3.2843 19.51-10.745 0.6948-0.98355 1.3896-1.9671 2.1055-2.9805 1.4259-1.7595 2.8634-3.5096 4.3125-5.25 0.72832-0.90105 1.4566-1.8021 2.207-2.7305 7.2516-8.8275 14.851-17.375 22.516-25.844 3.9882-4.4163 7.8855-8.9089 11.75-13.434 1.0299-1.2058 2.0599-2.4115 3.0898-3.6172 0.51965-0.60852 1.0393-1.217 1.5747-1.844 3.0292-3.5372 6.1018-7.0249 9.2378-10.469 4.6378-5.11 8.9914-10.434 13.312-15.812 1.0886-1.3052 1.0886-1.3052 2.1992-2.6367 2.6966-3.539 3.2616-6.8067 3.1938-11.236-0.74301-4.0206-3.4519-6.5065-6.2056-9.377-0.58878-0.6455-1.1776-1.291-1.7842-1.9561-1.7834-1.9486-3.5909-3.8723-5.4033-5.7939-1.4678-1.5866-2.93-3.178-4.3914-4.7705-1.3503-1.4704-2.706-2.9359-4.0618-4.4014-3.2209-3.5765-6.2239-7.3042-9.2383-11.055-2.4819-2.9817-5.0951-5.8187-7.7461-8.6484-11.792-12.676-21.99-24.809-21.48-43.066 3.407-27.518 27.039-66.699 47.918-84.559 5.9718-4.5112 12.209-7.1966 19.84-6.8477 17.094 2.7511 34.034 17.486 44.098 30.938 4.2859 6.4381 7.3285 13.191 10.062 20.41 7.824-9.5531 15.526-19.17 23-29 2.0817-2.7304 4.1656-5.4591 6.25-8.1875 0.81356-1.0657 0.81356-1.0657 1.6436-2.1528 4.0884-5.348 8.2159-10.664 12.356-15.972 4.6005-5.8986 9.1409-11.833 13.609-17.832 2.3536-3.1396 4.7426-6.2498 7.1406-9.3555 3.8824-5.0298 7.7073-10.099 11.508-15.191 1.8918-2.5232 3.809-5.0258 5.7344-7.5234 7.5051-9.6188 7.5051-9.6188 14.316-19.73 1.3298-1.8955 2.7369-3.5894 4.2539-5.3359 3.1005-3.572 5.9408-7.2908 8.75-11.094 1.0579-1.4211 2.1165-2.8416 3.1758-4.2617 0.53963-0.72365 1.0793-1.4473 1.6353-2.1929 2.6013-3.4712 5.2376-6.9153 7.8765-10.358 0.52964-0.69182 1.0593-1.3836 1.605-2.0964 2.371-3.0966 4.7431-6.1922 7.1172-9.2864 6.9922-9.117 13.973-18.224 20.592-27.617 3.0266-4.2821 6.1935-8.4387 9.4126-12.577 3.6953-4.7679 7.2699-9.6201 10.836-14.485 5.1531-7.0285 10.394-13.981 15.708-20.889 2.9437-3.8331 5.8403-7.6907 8.6675-11.611 2.947-4.0834 5.9477-8.12 9-12.125 0.79793-1.0493 1.5959-2.0986 2.418-3.1797 7.3745-9.0707 16.159-14.641 27.277-18.121 2.2951-0.62073 2.2951-0.62073 3.1172-2.8242 1.8452-0.2245 3.6914-0.44251 5.5404-0.63281 4.8219-0.71986 9.4052-2.3736 14.034-3.8672 1.11-0.35194 2.2199-0.70389 3.3635-1.0665 3.5853-1.1382 7.1675-2.2859 10.75-3.4335 2.4571-0.78153 4.9145-1.5623 7.3721-2.3423 4.8141-1.5283 9.6274-3.0592 14.44-4.5923 7.9059-2.5156 15.825-4.9889 23.75-7.4404 1.0889-0.33773 2.1777-0.67547 3.2996-1.0234 1.9287-0.59704 3.8581-1.192 5.7883-1.7842 1.8337-0.56302 3.6656-1.1317 5.4961-1.7051 0.89525-0.27683 1.7905-0.55365 2.7129-0.83887 0.78729-0.24573 1.5746-0.49146 2.3857-0.74463 2.0674-0.52881 2.0674-0.52881 5.0674-0.52881l1-2c2.0635-0.65381 2.0635-0.65381 4.8906-1.2734 5.3022-1.2515 10.508-2.6858 15.719-4.2656 0.791-0.2396 1.582-0.4792 2.397-0.72606 1.6915-0.51395 3.3826-1.029 5.0735-1.545 2.7544-0.84057 5.51-1.6773 8.2659-2.5133 8.5257-2.5879 17.048-5.1863 25.57-7.7864 13.103-3.9975 26.21-7.9851 39.326-11.94 6.004-1.8112 12.003-3.6372 17.996-5.485 3.178-0.97486 6.3616-1.9305 9.5474-2.8797 1.3959-0.41997 2.7895-0.84771 4.1802-1.2846 7.4197-2.3263 14.365-3.6465 22.117-3.7067zm-20.992 17.742c-1.5499 0.45619-3.1001 0.91128-4.6507 1.3653-4.0269 1.1832-8.0487 2.3832-12.069 3.5889-2.2846 0.68421-4.5704 1.3645-6.8568 2.043-9.5576 2.8364-19.105 5.7071-28.647 8.5948-2.3569 0.71299-4.7141 1.425-7.0713 2.1368-28.296 8.5445-56.566 17.173-84.795 25.935-1.0035 0.31135-2.0069 0.6227-3.0408 0.94348-11.996 3.723-23.986 7.464-35.967 11.233-6.2251 1.9577-12.455 3.9007-18.687 5.8356-4.2845 1.3329-8.5657 2.676-12.846 4.0215-2.0207 0.63298-4.0427 1.262-6.066 1.8865-23.47 7.0698-23.47 7.0698-41.393 23.08-0.50999 0.67644-1.02 1.3529-1.5454 2.0498-3.6209 4.8229-7.1758 9.692-10.719 14.572-2.5442 3.4854-5.1374 6.9329-7.7358 10.378-4.2914 5.6993-8.5303 11.435-12.75 17.188-5.8112 7.9174-11.743 15.738-17.71 23.538-3.2287 4.2249-6.4375 8.4557-9.54 12.775-3.7697 5.2477-7.6994 10.369-11.625 15.5-5.1908 6.7865-10.327 13.607-15.375 20.5-6.8698 9.373-13.905 18.615-20.968 27.843-3.3505 4.3809-6.6909 8.7694-10.032 13.157-4.0804 5.3567-8.1618 10.713-12.246 16.066-6.2595 8.207-12.508 16.42-18.688 24.688-3.5663 4.7394-7.1935 9.4319-10.818 14.127-2.004 2.5988-4.0003 5.2034-5.9985 7.8066-4.6667 6.073-9.3716 12.116-14.077 18.159-4.201 5.3973-8.3772 10.813-12.54 16.24-2.0141 2.6188-4.0438 5.225-6.0781 7.8281-6.3274 8.0986-12.608 16.201-18.555 24.586-6.9-5.9417-8.8694-12.752-10.5-21.562-3.1413-16.743-15.725-28.293-28.996-38.324-4.9704-3.3265-9.0877-5.0553-15.129-4.6211-9.0228 1.9292-15.349 9.9374-20.217 17.289-1.8379 3.065-3.6047 6.1599-5.3457 9.281-0.63784 1.1267-1.2757 2.2534-1.9329 3.4143-1.9767 3.4985-3.9284 7.0104-5.8796 10.523-0.62262 1.1121-1.2452 2.2243-1.8867 3.3701-1.7787 3.1828-3.543 6.373-5.3008 9.5674-0.52811 0.95076-1.0562 1.9015-1.6003 2.8811-5.3829 9.9109-10.296 19.829-7.7395 31.302 3.2979 10.131 12.086 18.126 18.922 26.019 1.5739 1.8233 3.1383 3.6543 4.6992 5.4888 4.6212 5.4279 9.2691 10.809 14.094 16.059 4.0031 4.367 7.8029 8.8502 11.488 13.488 1.6811 2.0428 3.3639 3.9542 5.1797 5.8672 6.9058 7.4056 6.9058 7.4056 7.5039 11.293-0.47773 2.4506-1.2972 4.4042-2.3594 6.6641-0.34289 0.95906-0.68578 1.9181-1.0391 2.9062-3.9708 10.697-10.773 17.983-18.41 26.258-2.512 2.7928-4.8847 5.659-7.2383 8.5859-2.4836 3.0794-4.9667 6.0024-7.8125 8.75-2.7851 2.6897-5.205 5.5397-7.625 8.5625-3.6156 4.4979-7.4178 8.7384-11.375 12.938-4.6878 4.9792-9.1123 10.082-13.391 15.422-2.8273 3.4556-5.8354 6.7297-8.8438 10.027-3.1691 3.568-6.1497 7.2777-9.125 11.008-0.70641 0.83918-1.4128 1.6784-2.1406 2.543-1.135 1.3632-1.135 1.3632-2.293 2.7539-3.3422 2.7731-6.0931 3.1088-10.27 3.3711-1.4393 0.14086-2.8781 0.28673-4.3164 0.4375-1.056 0.10635-1.056 0.10635-2.1333 0.21484-16.805 1.8824-30.489 10.283-41.988 22.223-0.67547 0.65613-1.3509 1.3123-2.0469 1.9883-12.766 13.19-16.584 32.001-16.428 49.714 0.79634 25.347 11.757 48.491 30.17 65.836 23.549 19.979 49.936 27.238 80.305 25.461 15.018-1.7793 27.461-8.3189 38-19l2.1875-2.1562c11.759-12.293 16.363-28.618 16.137-45.352-0.30927-3.3312-1.0894-5.9615-2.1367-9.1172-0.57812-2.6211-0.57812-2.6211-0.1875-5.375 3.0217-4.5312 7.3532-8.0332 11.426-11.588 1.8251-1.6371 3.3975-3.3898 4.9487-5.2866 3.4775-4.1066 7.3047-7.8415 11.125-11.625 5.675-5.5854 5.675-5.5854 11-11.5 3.9971-4.7466 8.4812-9.0302 12.908-13.371 3.1365-3.094 6.1552-6.2259 9.0293-9.5664 4.4693-5.1832 9.3664-9.9146 14.246-14.707 4.6633-4.6127 9.0401-9.3842 13.316-14.355 5.8809-6.532 11.024-11.289 19.938-12.562 8.3374 0.47177 15.695 7.3299 21.938 12.312 0.78738 0.62052 1.5748 1.241 2.386 1.8804 5.9714 4.719 11.864 9.5308 17.739 14.37 17.718 15.737 17.718 15.737 40 20 20.093-4.875 39.931-21.506 55-35 0.68578-0.59039 1.3716-1.1808 2.0781-1.7891 7.7419-7.0793 13.824-17.234 15.258-27.652 0.11446-6.2152-1.4044-9.4474-5.7383-14.047-9.3288-8.8271-21.917-12.213-34.098-15.105-7.1522-1.9413-12.027-6.5835-17.5-11.406-1.2255-1.0252-2.4539-2.0471-3.6875-3.0625l-2.3125-1.9375c4.1524-4.3666 8.4172-8.4213 13.125-12.188 4.481-3.5935 8.6987-7.3764 12.875-11.312 4.0586-3.8223 8.143-7.5144 12.5-11 5.6914-4.5564 10.964-9.5079 16.277-14.492 3.044-2.8533 6.1523-5.6197 9.3125-8.3438 2.2722-1.9795 4.4948-4.0099 6.7227-6.0391 3.4413-3.1103 6.9507-6.0898 10.562-9 5.1475-4.1646 10.009-8.5781 14.863-13.074 4.5492-4.2018 9.2254-8.2452 13.941-12.258 5.7571-4.9042 11.467-9.8323 17.008-14.98 4.547-4.2233 9.2639-8.1758 14.098-12.066 2.8216-2.3344 5.5208-4.766 8.2148-7.2461 4.3717-4.0197 8.8779-7.7999 13.496-11.531 5.4653-4.4917 10.768-9.1733 16.103-13.818 12.22-10.613 24.536-21.121 37.088-31.338 3.1305-2.574 6.2242-5.1882 9.3125-7.8125 4.8518-4.1229 9.755-8.1747 14.695-12.191 2.5374-2.0886 5.0421-4.2087 7.5398-6.3442 4.884-4.1751 9.8275-8.2129 14.952-12.089 11.32-8.6011 19.234-15.721 23.746-29.301 0.31375-0.92181 0.6275-1.8436 0.95076-2.7934 1.0272-3.028 2.0408-6.0604 3.0531-9.0934 0.72144-2.1435 1.4431-4.2869 2.165-6.4302 6.7188-20.008 13.145-40.1 19.397-60.257 0.55425-1.7845 0.55425-1.7845 1.1197-3.6051 14.365-46.254 28.643-92.522 40.88-139.39 0.33322-1.27 0.66645-2.5401 1.0098-3.8486 0.88961-3.4212 1.7579-6.8469 2.6152-10.276 0.24798-0.95842 0.49597-1.9168 0.75146-2.9043 1.8143-7.4711 3.4038-15.472-0.18896-22.533-2.1576-2.4042-3.8429-4.1941-7.1086-4.7852-8.4095-0.17858-16.031 2.287-23.989 4.6837z" fill="#E8A371"/>\r\n        <path transform="translate(317,466)" d="m0 0c8.7462 9.718 10.895 21.708 13.625 34.062 0.57344 2.5517 1.1507 5.1024 1.7325 7.6522 0.35842 1.5749 0.71172 3.151 1.0587 4.7284 4.77 21.192 20.161 34.423 35.271 49.182 1.9066 1.9581 3.6864 3.9452 5.457 6.0234 0.53601 0.62826 1.072 1.2565 1.6243 1.9038 0.4063 0.47776 0.81259 0.95552 1.2312 1.4478-0.25693-0.55873-0.51385-1.1175-0.77856-1.6931-1.1828-2.5793-2.3584-5.1618-3.5339-7.7444-0.40412-0.8785-0.80824-1.757-1.2246-2.6621-5.3301-11.744-5.3301-11.744-6.4629-16.9l1-2c0.48469 0.49629 0.96938 0.99258 1.4688 1.5039 4.0598 4.1145 8.2155 8.0141 12.598 11.781 1.8885 1.6749 3.6652 3.4143 5.4336 5.2148 2.9516 2.998 6.0442 5.7622 9.2266 8.5117 9.9866 8.734 19.585 17.927 29.273 26.988 17.624 16.481 17.624 16.481 35.469 32.723 13.315 11.98 13.315 11.98 19.156 17.965 4.4612 4.5348 9.3307 8.4477 14.375 12.312l-2 1c-2.2492-0.91904-4.346-1.8912-6.5-3-0.62423-0.31598-1.2485-0.63196-1.8916-0.95752-4.8527-2.5159-9.3176-5.4105-13.718-8.6597-1.8423-1.4282-1.8423-1.4282-3.8906-2.3828 5.3218 4.9306 10.647 9.7769 16.312 14.312 4.4112 3.5554 8.5653 7.3072 12.688 11.188 5.7926 5.4464 11.784 10.539 18 15.5 2.067 1.6821 4.1269 3.3725 6.1875 5.0625 0.92168 0.7541 1.8434 1.5082 2.793 2.2852 0.66645 0.54527 1.3329 1.0905 2.0195 1.6523-0.5775-0.825-1.155-1.65-1.75-2.5-2.4488-3.6557-4.3579-7.5347-6.25-11.5 4.4585 1.407 8.6694 3.1163 12.93 5.0391 0.6352 0.28572 1.2704 0.57144 1.9248 0.86581 2.0081 0.90399 4.0143 1.812 6.0205 2.7201 1.3697 0.61745 2.7395 1.2346 4.1094 1.8516 3.3399 1.5048 6.6782 3.0131 10.016 4.5234v2c-1.5906 1.3393-3.2528 2.5936-4.9375 3.8125-1.1049 0.80888-2.209 1.6188-3.3125 2.4297-0.60199 0.44054-1.204 0.88107-1.8242 1.335-3.4874 2.5767-6.9229 5.2214-10.363 7.8604-1.0758 0.82371-1.0758 0.82371-2.1733 1.6641-6.471 4.9559-12.932 9.924-19.389 14.898-3.2446-1.4708-5.8055-3.3142-8.5625-5.5625l-2.6719-2.1719c-1.369-1.1215-1.369-1.1215-2.7656-2.2656l-2.6406-2.1406c-6.637-5.395-13.172-10.905-19.689-16.443-1.6742-1.4192-3.3531-2.8325-5.0337-4.2441-4.989-4.195-9.9398-8.4091-14.762-12.797-3.3337-3.0326-6.7407-5.9225-10.25-8.75-5.5761-4.5188-10.849-9.321-16.097-14.21-1.4808-1.371-2.977-2.7254-4.4736-4.0791-7.8939-7.1496-15.424-14.634-22.9-22.219-4.2506-4.295-8.5627-8.4059-13.147-12.341-3.8497-3.4059-7.446-7.0711-11.07-10.714-0.76377-0.7599-1.5275-1.5198-2.3145-2.3027-3.4802-3.4862-6.8778-6.9949-10.088-10.732-4.0973-4.7586-8.5621-9.1249-13.035-13.527-5.2022-5.12-10.27-10.263-15.025-15.803-1.7357-1.9977-3.5712-3.8595-5.4746-5.6973-3.1479-3.1059-6.0776-6.3219-8.957-9.6758-2.0924-2.3805-4.2414-4.6975-6.405-7.0129-4.8961-5.2406-9.541-10.56-13.954-16.221-2.0675-2.5664-4.3213-4.797-6.6836-7.0898-2-3-2-3-1.7776-5.4028 0.79878-2.6679 1.8073-4.7553 3.219-7.1519 0.49742-0.85473 0.99483-1.7095 1.5073-2.5901 0.53254-0.90097 1.0651-1.8019 1.6138-2.7302 1.0993-1.891 2.1969-3.7829 3.293-5.6758 0.53802-0.92764 1.076-1.8553 1.6304-2.811 5.5524-9.6742 10.594-19.631 15.514-29.638z" fill="#646C65"/>\r\n        <path transform="translate(843,162)" d="m0 0-7 4-1-1c-2.7155 0.58673-5.3787 1.2293-8.0625 1.9375-0.75861 0.19529-1.5172 0.39059-2.2988 0.5918-1.8809 0.48501-3.76 0.9772-5.6387 1.4707-0.13277 0.73323-0.26555 1.4665-0.40234 2.2219-1.0134 4.7103-2.2424 8.2155-5.5977 11.778-5.1132 2.6545-10.488 4.1934-16 5.8125-1.6126 0.50105-3.2242 1.0055-4.8347 1.5132-3.3608 1.055-6.7263 2.0926-10.096 3.1172-4.8816 1.4902-9.7379 3.0509-14.588 4.6392-0.77013 0.25213-1.5403 0.50426-2.3337 0.76402-1.5468 0.5067-3.0935 1.0136-4.6402 1.5207-3.8779 1.268-7.7605 2.5211-11.643 3.7739-0.75418 0.24344-1.5084 0.48687-2.2854 0.73769-4.7613 1.5365-9.5231 3.0713-14.285 4.6061-1.2268 0.39542-2.4536 0.79084-3.7175 1.1982-2.4766 0.79802-4.9533 1.5955-7.4302 2.3926-7.4276 2.3919-14.848 4.8064-22.262 7.2373-18.255 5.9813-36.529 11.889-54.883 17.562-0.84659 0.26311-1.6932 0.52622-2.5654 0.7973-2.3726 0.73632-4.747 1.4667-7.1221 2.1949-0.70101 0.21801-1.402 0.43603-2.1243 0.66064-2.8482 0.86583-5.1914 1.4722-8.1882 1.4722 0.27264 0.97888 0.27264 0.97888 0.55078 1.9775 3.9917 14.611 6.3633 27.872 5.4492 43.022h-2c-5.0611-9.8452-9.6513-19.822-14-30-4.4853 4.1835-7.9783 8.8493-11.562 13.812-1.2534 1.7178-2.5073 3.4353-3.7617 5.1523-0.62181 0.8532-1.2436 1.7064-1.8843 2.5854-2.5306 3.4604-5.0924 6.8966-7.6665 10.325-0.47784 0.6368-0.95568 1.2736-1.448 1.9297-4.834 6.4273-9.726 12.81-14.61 19.2-4.4604 5.8494-8.8488 11.746-13.192 17.683-5.1353 7.0156-10.405 13.91-15.766 20.755-3.7632 4.8093-7.4615 9.6602-11.109 14.558-4.2179 5.6637-8.5201 11.253-12.875 16.812-4.8811 6.2348-9.638 12.546-14.312 18.938-5.3639 7.3332-10.884 14.513-16.533 21.628-2.1193 2.6872-4.1989 5.4047-6.2793 8.1221-3.4681 4.5256-6.9709 9.0218-10.5 13.5-3.874 4.9169-7.7118 9.8595-11.522 14.826-9.1315 11.896-18.375 23.705-27.652 35.488-2.2775 2.8936-4.5519 5.7897-6.8267 8.6855-2.7961 3.5592-5.5926 7.1181-8.3906 10.676-5.0542 6.4277-10.1 12.862-15.109 19.324 0.99 1.65 1.98 3.3 3 5-4.1242-1.6617-7.0655-4.6234-10.25-7.625-0.5543-0.51562-1.1086-1.0312-1.6797-1.5625-1.3606-1.2668-2.716-2.5391-4.0703-3.8125 1.6268-3.6539 3.8669-6.596 6.3125-9.75 0.43441-0.56074 0.86883-1.1215 1.3164-1.6992 4.1028-5.2668 8.3245-10.436 12.55-15.604 3.3615-4.1209 6.6595-8.28 9.8838-12.509 3.5663-4.6743 7.1936-9.2908 10.875-13.875 5.7387-7.148 11.418-14.34 17.062-21.562 0.52288-0.66838 1.0458-1.3368 1.5845-2.0254 8.3281-10.652 16.554-21.378 24.736-32.143 2.9156-3.8344 5.8538-7.6498 8.8047-11.457 4.5205-5.8616 8.8975-11.824 13.273-17.794 4.5458-6.1869 9.1826-12.299 13.852-18.393 4.7428-6.1924 9.4013-12.419 13.884-18.802 3.8186-5.3996 7.843-10.637 11.866-15.885 4.8482-6.3256 9.6231-12.679 14.212-19.195 3.5844-5.0695 7.304-10.033 11.038-14.993 13.008-17.283 25.755-34.749 38.348-52.336 0.59031-0.82234 1.1806-1.6447 1.7888-2.4919 1.1321-1.5772 2.2619-3.1561 3.3892-4.7368 0.50974-0.70955 1.0195-1.4191 1.5447-2.1501 0.44618-0.62383 0.89235-1.2477 1.3521-1.8904 2.4758-3.1838 4.393-4.9888 8.2991-6.1675 0.81133-0.24997 1.6227-0.49994 2.4586-0.75749 0.89321-0.26461 1.7864-0.52921 2.7067-0.80183 0.95336-0.29083 1.9067-0.58166 2.889-0.8813 3.218-0.97942 6.4399-1.9453 9.6618-2.9117 2.2999-0.69745 4.5996-1.3959 6.8989-2.0952 4.3839-1.3323 8.7687-2.6616 13.155-3.9868 9.3777-2.8337 18.747-5.6947 28.114-8.5625 3.0712-0.94012 6.1424-1.8802 9.2136-2.8203 1.1475-0.35129 1.1475-0.35129 2.3183-0.70968 9.2804-2.8405 18.563-5.6724 27.846-8.5048 8.2032-2.5031 16.406-5.0088 24.605-7.5237 21.256-6.5191 42.543-12.934 63.862-19.241 2.6425-0.78197 5.2838-1.5678 7.9242-2.357 3.6676-1.0959 7.3393-2.1775 11.012-3.2577 1.6605-0.49876 1.6605-0.49876 3.3544-1.0076 1.0144-0.29583 2.0289-0.59166 3.074-0.89645 0.88496-0.262 1.7699-0.52399 2.6817-0.79393 2.2531-0.43092 2.2531-0.43092 5.2531 0.56908z" fill="#DEDBCB"/>\r\n        <path transform="translate(222,752)" d="m0 0c0.097969 1.2207 0.19594 2.4415 0.29688 3.6992 1.3785 15.768 4.5864 28.154 13.703 41.301 0.4602 0.67805 0.92039 1.3561 1.3945 2.0547 8.4689 11.104 24.144 18.685 37.605 20.945 3.6723 0.22116 7.3228 0.19094 11 0.125 0.96551-0.0090234 1.931-0.018047 2.9258-0.027344 2.3583-0.02335 4.7161-0.056096 7.0742-0.097656 0.17549 4.823-0.23757 8.6279-1.8125 13.188-0.33645 1.0042-0.67289 2.0084-1.0195 3.043-1.1557 2.7403-2.1546 4.5916-4.168 6.7695-2.1538 0.50171-2.1538 0.50171-4.6484 0.49609-1.3744 0.004834-1.3744 0.004834-2.7766 0.0097656-0.97348-0.022559-1.947-0.045117-2.95-0.068359-0.99862-0.016113-1.9972-0.032227-3.0261-0.048828-18.19-0.48409-35.191-6.8886-48.599-19.389-1.1312-0.9958-1.1312-0.9958-2.2852-2.0117-15.52-14.402-24.263-35.347-25.277-56.363-0.066406-2.4609-0.066406-2.4609 0.5625-4.625 3.4222-3.4096 7.078-5.0664 11.562-6.75 1.115-0.42797 2.2301-0.85594 3.3789-1.2969 3.0586-0.95312 3.0586-0.95312 7.0586-0.95312z" fill="#D69E43"/>\r\n        <path transform="translate(300,679)" d="m0 0c3.0317 3.6421 5.5712 7.4095 8.0625 11.438 11.9 18.702 27.212 35.21 44.938 48.562-2.783 4.6383-6.0497 8.1612-9.9219 11.926-1.9804 1.9767-3.8182 4.0146-5.6406 6.1367-2.3436 2.6967-4.6882 5.3869-7.125 8-0.54012 0.5891-1.0802 1.1782-1.6367 1.7852-1.6758 1.1523-1.6758 1.1523-3.6211 1.0234-18.143-7.692-32.71-31.267-39.876-48.891-5.0057-13.128-5.0057-13.128-4.1787-18.98 1.9414-2.7109 1.9414-2.7109 4.5625-5.375 1.3632-1.4173 1.3632-1.4173 2.7539-2.8633 0.88559-0.91137 1.7712-1.8227 2.6836-2.7617 1.3448-1.5107 2.6798-3.0302 4-4.5625 1.6261-1.8802 3.241-3.6785 5-5.4375z" fill="#597A53"/>\r\n        <path transform="translate(709,299)" d="m0 0h1c0.2107 4.5403-0.37761 7.9852-1.9375 12.25-0.35965 1.0364-0.7193 2.0728-1.0898 3.1406-5.8514 12.187-19.647 22.363-29.098 31.734-3.2139 3.1871-6.4244 6.3777-9.6328 9.5703-0.72309 0.7148-1.4462 1.4296-2.1912 2.166-4.0306 4.0114-7.8743 8.1207-11.575 12.44-1.8906 2.1757-3.9083 4.1927-5.9765 6.1991-2.6627 2.6271-5.2126 5.2673-7.625 8.125-3.5747 4.1788-7.4706 8.0084-11.375 11.875-4.4304 4.3876-8.7431 8.7779-12.766 13.547-2.7523 3.0994-5.7324 5.9715-8.6819 8.8811-3.2936 3.2663-6.3676 6.6513-9.3767 10.177-2.4423 2.7611-5.0813 5.3092-7.707 7.8945-1.9086 1.9389-3.6959 3.937-5.4688 6-2.3968 2.789-4.8796 5.4199-7.5 8-2.4971 2.4591-4.8606 4.9509-7.125 7.625-3.4278 3.9965-7.1353 7.6743-10.875 11.375-4.2969 4.2521-8.4552 8.5277-12.363 13.145-1.9557 2.2171-4.0323 4.2792-6.1367 6.3555-2.6627 2.6271-5.2126 5.2673-7.625 8.125-4.1496 4.8509-8.727 9.2785-13.282 13.745-3.1547 3.112-6.1806 6.2622-9.062 9.6304-4.1733 4.8399-8.8501 9.0602-13.57 13.355-4.096 3.7718-7.8681 7.6736-11.479 11.914-3.4081 3.9797-7.2579 7.4981-11.107 11.043-1.1331 1.0461-1.1331 1.0461-2.2891 2.1133-2.0859 1.5742-2.0859 1.5742-5.0859 1.5742-2.0948 1.6918-2.0948 1.6918-4.125 3.875-1.0557 1.0789-1.0557 1.0789-2.1328 2.1797-1.7962 1.8336-1.7962 1.8336-2.7422 3.9453l-2-1c5.0659-5.961 10.396-11.664 15.745-17.37 3.2686-3.4905 6.5098-6.9986 9.6926-10.568 4.5965-5.1484 9.3291-10.166 14.072-15.179 3.6989-3.9225 7.2942-7.9151 10.829-11.986 2.4388-2.7858 4.9516-5.4996 7.4736-8.21 1.042-1.1247 2.0836-2.2497 3.125-3.375 0.51305-0.5543 1.0261-1.1086 1.5547-1.6797 5.0266-5.4433 10.031-10.908 14.883-16.508 3.6073-4.1544 7.3481-8.1822 11.099-12.207 2.6949-2.8999 5.3367-5.8352 7.9321-8.8247 4.1992-4.8221 8.5917-9.4524 12.988-14.094 3.7604-3.9861 7.4233-8.034 10.996-12.189 1.6392-1.844 3.3487-3.5828 5.1094-5.3105 2.2933-2.258 4.4643-4.56 6.5625-7 5.1684-5.9857 10.626-11.708 16.036-17.474 1.8617-1.9841 3.7216-3.9698 5.5811-5.9561 3.1132-3.3247 6.2293-6.6466 9.3467-9.9673 1.3605-1.4497 2.7205-2.9 4.0801-4.3506 2.1301-2.2727 4.2617-4.5439 6.3936-6.8149 0.6463-0.69013 1.2926-1.3803 1.9585-2.0913 3.0535-3.2496 6.1349-6.4582 9.2993-9.6001 2.3124-2.2965 4.5196-4.6239 6.6172-7.1211 2.5913-3.0097 5.2975-5.8359 8.125-8.625 2.7862-2.7486 5.4531-5.5286 8-8.5 3.18-3.7101 6.5876-7.1298 10.094-10.531 1.9594-2.0103 3.7888-4.0495 5.6172-6.1758 4.0901-4.7132 8.4794-9.0936 12.914-13.48 1.1776-1.1708 1.1776-1.1708 2.3789-2.3652 1.5045-1.4956 3.01-2.9903 4.5166-4.4839 2.3333-2.3144 4.6578-4.6373 6.9795-6.9634l2-2z" fill="#999E95"/>\r\n        <path transform="translate(330,646)" d="m0 0c3.0643 2.8786 5.7032 5.8393 8.25 9.1875 13.862 18.047 30.869 32.924 48.75 46.812-3.4059 4.8032-6.9622 9.1072-11.195 13.199-2.5843 2.5788-4.947 5.3327-7.3242 8.1016-1.1122 1.2765-2.2833 2.502-3.4805 3.6992-4.3036-0.136-7.245-3.4296-10.312-6.125-0.60812-0.52989-1.2162-1.0598-1.8428-1.6057-16.559-14.619-35.238-32.125-40.845-54.269 0.56848-0.55688 1.137-1.1138 1.7227-1.6875 4.4723-4.42 8.7818-8.9028 12.867-13.684 1.0864-1.255 2.2364-2.4552 3.4102-3.6289z" fill="#557450"/>\r\n        <path transform="translate(269,715)" d="m0 0c1.8167 2.7251 2.8339 5.1722 3.9016 8.2412 7.6075 21.783 22.031 41.387 40.098 55.759-1.3319 3.9444-2.9465 6.3059-5.9141 9.207-0.76055 0.75088-1.5211 1.5018-2.3047 2.2754-0.79406 0.76893-1.5881 1.5379-2.4062 2.3301-0.8018 0.78826-1.6036 1.5765-2.4297 2.3887-1.9752 1.9399-3.957 3.8724-5.9453 5.7988-2.6824-1.2558-4.9113-2.5933-7.1719-4.5039-0.5779-0.48823-1.1558-0.97646-1.7512-1.4795-14.855-12.84-27.297-28.164-30.764-48.079-0.12955-0.68127-0.2591-1.3625-0.39258-2.0645-0.35398-1.9497-0.63857-3.9116-0.91992-5.873-0.15727-1.0068-0.31453-2.0135-0.47656-3.0508 0.73735-4.5631 3.5816-6.9043 6.7891-10.074 1.1851-1.2095 2.3687-2.4204 3.5508-3.6328 0.82685-0.83966 0.82685-0.83966 1.6704-1.6963 1.6526-1.7423 3.1039-3.5687 4.4663-5.5459z" fill="#567651"/>\r\n        <path transform="translate(192,769)" d="m0 0h1c0.14695 1.4715 0.14695 1.4715 0.29688 2.9727 2.6679 24.875 11.39 47.293 30.809 63.898 17.824 13.11 36.184 17.082 57.895 18.129-3.6339 3.1796-6.9801 5.0137-11.5 6.6875-1.1034 0.41637-2.2069 0.83273-3.3438 1.2617-15.543 5.1747-31.668 2.2134-46.242-4.3359-17.807-9.1029-29.218-23.283-36.078-41.746-4.3069-14.772-2.4333-29.741 4.9141-43.18 0.73723-1.2369 1.482-2.4695 2.25-3.6875z" fill="#DBA445"/>\r\n        <path transform="translate(350,620)" d="m0 0c4.1266 1.5864 6.6322 4.5923 9.5 7.8125 1.0729 1.1824 2.1458 2.3646 3.2188 3.5469 0.54527 0.60521 1.0905 1.2104 1.6523 1.834 10.089 11.19 20.27 22.369 31.754 32.154 3.4577 3.0471 6.6484 6.3647 9.875 9.6523l4 4-11 11c-3.0348-1.5174-5.0628-2.7095-7.6094-4.793-1.0017-0.81573-1.0017-0.81573-2.0237-1.6479-1.0479-0.86456-1.0479-0.86456-2.1169-1.7466-0.72373-0.59442-1.4475-1.1888-2.1931-1.8013-2.0228-1.6658-4.0411-3.3368-6.0569-5.0112-0.71422-0.59087-1.4284-1.1817-2.1643-1.7905-14.287-11.926-27.473-26.068-36.836-42.209 3.2076-3.8064 6.4075-7.5456 10-11z" fill="#536F4F"/>\r\n        <path transform="translate(541,482)" d="m0 0c0.8125 2.1875 0.8125 2.1875 1 5-2.3125 2.5-2.3125 2.5-5 5-0.29624 0.78206-0.59249 1.5641-0.89771 2.3699-1.3216 3.1535-2.9794 4.8341-5.4265 7.2122-0.86432 0.85014-1.7286 1.7003-2.6191 2.5762-0.90557 0.87592-1.8111 1.7518-2.7441 2.6543-7.198 6.9689-7.198 6.9689-13.957 14.355-4.1005 4.7943-8.7352 8.9477-13.395 13.188-4.096 3.7718-7.8681 7.6736-11.479 11.914-3.4081 3.9797-7.2579 7.4981-11.107 11.043-0.75539 0.69738-1.5108 1.3948-2.2891 2.1133-2.0859 1.5742-2.0859 1.5742-5.0859 1.5742-2.0948 1.6918-2.0948 1.6918-4.125 3.875-1.0557 1.0789-1.0557 1.0789-2.1328 2.1797-1.7962 1.8336-1.7962 1.8336-2.7422 3.9453l-2-1c5.0659-5.961 10.396-11.664 15.745-17.37 3.2686-3.4905 6.5098-6.9986 9.6926-10.568 4.5965-5.1484 9.3291-10.166 14.072-15.179 3.6989-3.9225 7.2942-7.9151 10.829-11.986 2.4388-2.7858 4.9512-5.5 7.4736-8.21 2.9913-3.22 5.9796-6.4401 8.9023-9.7227 13.359-14.965 13.359-14.965 17.285-14.965z" fill="#8F958D"/>\r\n        <path transform="translate(314,472)" d="m0 0 1 2c-0.70393 1.6517-1.4143 3.301-2.1582 4.9351-1.4948 3.6667-2.2224 7.5243-3.0918 11.377-2.2031 9.317-5.3595 18.002-9.0132 26.835-1.0262 2.5802-1.8744 5.214-2.7368 7.8525l-1 2c-2.6475-2.5778-4.9443-4.9165-7-8 0.34214-3.6963 1.5738-6.3842 3.4414-9.5547 0.49766-0.85521 0.99532-1.7104 1.5081-2.5916 0.79845-1.3507 0.79845-1.3507 1.613-2.7288 1.0954-1.8831 2.1892-3.7673 3.2812-5.6523 0.53754-0.92667 1.0751-1.8533 1.6289-2.8081 4.4393-7.7447 8.5598-15.669 12.527-23.665z" fill="#9EA298"/>\r\n        <path transform="translate(835,164)" d="m0 0 1 3c-14.214 14.476-14.214 14.476-21 19v-3l-2-1c3.1818-11.319 3.1818-11.319 7.8545-14.106 4.5667-1.8864 9.3062-2.9567 14.146-3.8936z" fill="#BBBCAE"/>\r\n        <path transform="translate(489,537)" d="m0 0 1 3c-0.99 0.33-1.98 0.66-3 1l0.375 2.1875c-0.375 2.8125-0.375 2.8125-3.0625 5.3125-0.55043 0.4125-1.1009 0.825-1.668 1.25-1.8702 1.3631-1.8702 1.3631-4.1445 3.75-2.7216 2.7216-5.4617 5.1369-8.5 7.5h-2c-1.9982 1.7153-1.9982 1.7153-4.0625 3.875-0.71285 0.7193-1.4257 1.4386-2.1602 2.1797-1.8323 1.8276-1.8323 1.8276-2.7773 3.9453l-2-1c4.5796-5.3888 9.3633-10.581 14.188-15.75 0.60602-0.64977 1.212-1.2995 1.8364-1.969 4.0865-4.3668 8.1549-8.6631 12.726-12.531l1.8594-1.5781 1.3906-1.1719z" fill="#8A9188"/>\r\n        <path transform="translate(507,525)" d="m0 0c0 3 0 3-1.5605 4.8694-0.71221 0.68377-1.4244 1.3675-2.1582 2.072-1.1505 1.1225-1.1505 1.1225-2.3242 2.2676-1.2162 1.165-1.2162 1.165-2.457 2.3535-1.5981 1.5384-3.1921 3.0812-4.7812 4.6289-0.71221 0.68264-1.4244 1.3653-2.1582 2.0686-1.7831 1.5986-1.7831 1.5986-1.5605 3.74h-3l-0.25 1.875c-0.99452 2.8178-2.1266 2.8352-4.75 4.125-1.7442 1.4565-1.7442 1.4565-3.3828 3.1523-0.60973 0.61166-1.2195 1.2233-1.8477 1.8535-0.6252 0.63744-1.2504 1.2749-1.8945 1.9316-0.63293 0.63357-1.2659 1.2671-1.918 1.9199-2.6158 2.6408-4.8858 5.0357-6.957 8.1426-0.99-0.33-1.98-0.66-3-1 0.4241-0.4125 0.8482-0.825 1.2852-1.25 3.8837-3.824 7.5292-7.7774 11.09-11.902 2.1049-2.3933 4.342-4.6247 6.625-6.8477 2.7908-2.781 5.5691-5.574 8.3398-8.375 1.1992-1.2084 2.3984-2.4167 3.5977-3.625 0.5949-0.60328 1.1898-1.2066 1.8027-1.8281 3.5986-3.6183 7.2862-6.9688 11.26-10.172z" fill="#666E68"/>\r\n        <path transform="translate(317,466)" d="m0 0c8.7329 9.7032 10.899 21.728 13.625 34.062 0.57344 2.5517 1.1507 5.1024 1.7325 7.6522 0.35842 1.5749 0.71172 3.151 1.0587 4.7284 2.1677 10.528 2.1677 10.528 7.5838 19.557l-1 2c-8.3233-7.6297-9.3156-21.34-11-32h-2l-0.25-3.5625c-1.0117-9.1056-3.4093-18.364-7.75-26.438h-4l2-6z" fill="#889088"/>\r\n        <path transform="translate(222,752)" d="m0 0v15c-2.2091-3.3137-2.2248-4.3446-2.125-8.1875 0.018047-0.90105 0.036094-1.8021 0.054688-2.7305 0.023203-0.68707 0.046406-1.3741 0.070312-2.082-1.8983 0.59643-3.7935 1.2025-5.6875 1.8125-1.0557 0.33645-2.1115 0.67289-3.1992 1.0195-4.3488 1.5799-4.3488 1.5799-8.1133 4.168-0.54462 2.7532-0.78934 4.9314-0.8125 7.6875-0.025137 0.70189-0.050273 1.4038-0.076172 2.127-0.058773 1.7279-0.087938 3.4568-0.11133 5.1855h2l1 12c-5.4892-5.4892-5.3219-17.243-5.5938-24.695 0.88616-3.4397 2.6573-4.4001 5.5938-6.3047 3.1914-1.4844 3.1914-1.4844 6.5625-2.75 1.115-0.42797 2.2301-0.85594 3.3789-1.2969 3.0586-0.95312 3.0586-0.95312 7.0586-0.95312z" fill="#F2CF53"/>\r\n        <path transform="translate(630,268)" d="m0 0v20h-2c-1.2284-2.241-2.4323-4.4901-3.625-6.75-0.35062-0.63422-0.70125-1.2684-1.0625-1.9219-0.97656-1.875-0.97656-1.875-2.3125-5.3281 0.78906-2.4531 0.78906-2.4531 2-4 0.99 0.33 1.98 0.66 3 1 0.47438-0.495 0.94875-0.99 1.4375-1.5 1.5625-1.5 1.5625-1.5 2.5625-1.5z" fill="#D4D2C0"/>\r\n        <path transform="translate(221,899)" d="m0 0c6.329 0.82552 6.329 0.82552 8.9004 1.4941 9.0828 2.2894 18.432 1.7221 27.725 1.6309 1.7852-0.010049 3.5703-0.019171 5.3555-0.027344 4.34-0.021864 8.6797-0.056288 13.02-0.097656-14.144 7.6979-38.701 2.826-53.121-1.4141-0.62004-0.19336-1.2401-0.38672-1.8789-0.58594v-1z" fill="#A6724F"/>\r\n        <path transform="translate(463,641)" d="m0 0c3.0879 1.4354 5.6993 3.1697 8.4375 5.1875 5.8984 4.1968 12.138 7.4995 18.562 10.812-3.0103 0.93424-3.8665 1.0445-7 0 0.99 1.32 1.98 2.64 3 4-3.9512-1.622-6.7581-4.3566-9.8125-7.25-1.0629-0.99313-2.1267-1.9853-3.1914-2.9766-0.51192-0.47728-1.0238-0.95455-1.5513-1.4463-1.8547-1.7037-3.7651-3.3342-5.6948-4.9521l-2.75-2.375v-1z" fill="#262B26"/>\r\n        <path transform="translate(232,859)" d="m0 0c0.92941 0.1534 1.8588 0.3068 2.8164 0.46484 5.0197 0.71709 10.059 0.88661 15.121 1.0977 0.97002 0.043184 1.94 0.086367 2.9395 0.13086 2.3742 0.10526 4.7486 0.2074 7.123 0.30664l-1 3c-3.0833 0.058225-6.1664 0.093671-9.25 0.125-1.309 0.025137-1.309 0.025137-2.6445 0.050781-0.84434 0.0064453-1.6887 0.012891-2.5586 0.019531-0.77505 0.010474-1.5501 0.020947-2.3486 0.031738-4.1383-0.42744-6.9982-2.7127-10.198-5.2271z" fill="#D69E3F"/>\r\n        <path transform="translate(594,390)" d="m0 0c0 3 0 3-1.8984 5.0859-1.6456 1.521-3.2915 3.0419-4.9375 4.5625-2.2384 2.4324-3.0164 4.2993-4.1641 7.3516-3.2847 4.1286-6.8038 7.5828-12 9 1.4841-3.4865 3.4621-5.6419 6.1875-8.25 3.6022-3.5155 6.9624-7.1351 10.238-10.953 2.0876-2.3829 4.3006-4.5921 6.5742-6.7969z" fill="#1C211D"/>\r\n        <path transform="translate(500,523)" d="m0 0c0 3 0 3-2 6v3c-1.4258 1.8242-1.4258 1.8242-3.3125 3.6875-0.92232 0.93393-0.92232 0.93393-1.8633 1.8867-1.8242 1.4258-1.8242 1.4258-4.8242 1.4258-1.655 1.0773-1.655 1.0773-3.1875 2.5l-2.8125 2.5c1.4841-3.4865 3.4621-5.6419 6.1875-8.25 4.1709-4.0697 8.0464-8.3058 11.812-12.75z" fill="#989F95"/>\r\n        <path transform="translate(314,472)" d="m0 0 1 2c-0.70673 1.6582-1.4197 3.314-2.1675 4.9541-1.7251 4.2393-2.4514 8.79-3.3813 13.257-0.42594 1.9433-0.93217 3.8686-1.4512 5.7891l-2 1v-7l-3 3c1.5565-5.3537 3.9818-10.002 6.625-14.875 0.42023-0.78375 0.84047-1.5675 1.2734-2.375 1.0297-1.9189 2.065-3.8348 3.1016-5.75z" fill="#AFB2A7"/>\r\n        <path transform="translate(321,656)" d="m0 0c0 3 0 3-1.418 4.5078-0.87592 0.80051-0.87592 0.80051-1.7695 1.6172-2.3576 2.6146-2.3576 2.6146-2.7539 5.9805 2.2333 7.129 6.4275 14.807 11.941 19.895l-1 3c-5.7437-7.2744-11.359-15.002-14-24 0.97563-3.3476 3.1483-5.365 5.625-7.75 0.63164-0.61359 1.2633-1.2272 1.9141-1.8594 0.72316-0.68836 0.72316-0.68836 1.4609-1.3906z" fill="#659060"/>\r\n        <path transform="translate(843,162)" d="m0 0-7 4-1-1c-1.1954 0.37137-1.1954 0.37137-2.415 0.75024-2.9645 0.91567-5.9317 1.8222-8.9009 2.7227-1.9138 0.58341-3.8243 1.1773-5.7349 1.7712-1.8079 0.54624-1.8079 0.54624-3.6523 1.1035-1.6653 0.51059-1.6653 0.51059-3.3643 1.0315-2.8388 0.60099-4.2578 0.62531-6.9326-0.37915 8.6851-3.0151 17.427-5.7923 26.25-8.375 1.3751-0.4121 1.3751-0.4121 2.7781-0.83252 0.86214-0.24863 1.7243-0.49726 2.6125-0.75342 0.7686-0.22478 1.5372-0.44956 2.3291-0.68115 2.0303-0.35791 2.0303-0.35791 5.0303 0.64209z" fill="#EEEEE7"/>\r\n        <path transform="translate(363,539)" d="m0 0c2.4928 2.1978 3.4918 3.8839 4.3906 7.0664 1.9026 6.1312 4.7821 11.714 7.6445 17.443 0.39574 0.81018 0.79148 1.6204 1.1992 2.4551 0.36319 0.72824 0.72639 1.4565 1.1006 2.2068 0.21946 0.60336 0.43893 1.2067 0.66504 1.8284l-1 2c-2.31-2.64-4.62-5.28-7-8l2-1c-0.72316-1.4676-0.72316-1.4676-1.4609-2.9648-3.3664-6.9464-6.3244-13.343-7.5391-21.035z" fill="#202520"/>\r\n        <path transform="translate(434,704)" d="m0 0 2 2-2.125-0.14062-2.875-0.10938c-1.3922-0.069609-1.3922-0.069609-2.8125-0.14062-8.3614 1.0247-13.593 6.2565-19.188 12.141-0.67934 0.69738-1.3587 1.3948-2.0586 2.1133-1.6567 1.7034-3.3033 3.4154-4.9414 5.1367l-2-3c0.71543-0.38285 1.4309-0.7657 2.168-1.1602 3.2202-2.092 5.5201-4.4782 8.1445-7.2773 7.0863-7.2645 13.197-11.239 23.688-9.5625z" fill="#0C0B12"/>\r\n        <path transform="translate(529,502)" d="m0 0c0 3 0 3-1.4961 4.7188-0.961 0.88172-0.961 0.88172-1.9414 1.7812-2.4839 2.2882-3.4713 3.2264-4.5625 6.5-3.3945 3.6854-7.1233 6.8445-11 10l-2-1c2.3733-2.5433 4.7489-5.0843 7.125-7.625 0.66516-0.71285 1.3303-1.4257 2.0156-2.1602 3.882-4.1484 7.8168-8.2227 11.859-12.215z" fill="#5F6662"/>\r\n        <path transform="translate(636,389)" d="m0 0 1 2c-2.7844 3.6093-5.7605 6.7977-9 10-0.9655 0.96419-1.9303 1.929-2.8945 2.8945l-8.1055 8.1055-2-1c2.3733-2.5433 4.7489-5.0843 7.125-7.625 0.66516-0.71285 1.3303-1.4257 2.0156-2.1602 3.882-4.1484 7.8168-8.2227 11.859-12.215z" fill="#69706C"/>\r\n        <path transform="translate(746,366)" d="m0 0c4.8363 0.99044 9.4762 1.957 14 4-3 1-3 1-5 1 0.99902 0.69867 1.998 1.3973 3.0273 2.1172 1.3035 0.91905 2.6069 1.8383 3.9102 2.7578 0.65936 0.4602 1.3187 0.92039 1.998 1.3945 4.9512 3.5039 4.9512 3.5039 6.0645 5.7305-3.9726-1.3958-6.962-3.2766-10.312-5.8125-3.382-2.5251-6.7496-4.9015-10.375-7.0625l-3.3125-2.125v-2z" fill="#1E231E"/>\r\n        <path transform="translate(287,640)" d="m0 0c0 3.3118-0.54378 4.313-2.25 7.0625-0.62648 1.0383-0.62648 1.0383-1.2656 2.0977-1.6814 2.084-3.1057 2.6754-5.4844 3.8398-1.8591 1.8681-1.8591 1.8681-3.5625 4-2.1111 2.5577-3.6372 4.1331-6.4375 6 1.6832-4.2338 4.7224-7.1317 7.8125-10.375 3.8774-4.1027 7.6144-8.2528 11.188-12.625z" fill="#B17C56"/>\r\n        <path transform="translate(269,715)" d="m0 0c1.7369 2.6054 2.691 4.5834 3.6875 7.5 0.27199 0.77344 0.54398 1.5469 0.82422 2.3438 0.48828 2.1562 0.48828 2.1562-0.51172 5.1562l-4-9-3.8125 2.875c-2.3634 1.7822-4.7226 3.4818-7.1875 5.125 1.5778-3.7105 3.907-6.2991 6.625-9.25 0.81727-0.89203 1.6345-1.7841 2.4766-2.7031 0.62648-0.67547 1.253-1.3509 1.8984-2.0469z" fill="#659360"/>\r\n        <path transform="translate(539,583)" d="m0 0 2 1c-2.7654 2.8396-5.5406 5.6692-8.3252 8.49-1.4099 1.4324-2.8119 2.8725-4.2139 4.3127-0.88945 0.89912-1.7789 1.7982-2.6953 2.7246-0.81694 0.83265-1.6339 1.6653-2.4756 2.5232-2.2207 1.8905-3.4429 2.5807-6.29 2.9495 4.1488-5.1314 8.6395-9.4801 13.586-13.844 2.9258-2.6133 5.6771-5.3473 8.4141-8.1562z" fill="#252A24"/>\r\n        <path transform="translate(624,272)" d="m0 0c1.9375 0.5625 1.9375 0.5625 4 2 0.6875 3.1875 0.6875 3.1875 1 7l1 7h-2c-2.6939-4.7755-4.3135-9.5655-5-15l1-1z" fill="#CAC8B8"/>\r\n        <path transform="translate(365,599)" d="m0 0h2c1.4102 1.4688 1.4102 1.4688 3.0625 3.5 2.6813 3.175 5.4664 5.9251 8.625 8.625 3.5174 3.0372 6.0011 5.8552 8.3125 9.875-3.4361-1.4823-5.687-3.4295-8.3281-6.0625-0.79922-0.79664-1.5984-1.5933-2.4219-2.4141-0.825-0.83273-1.65-1.6655-2.5-2.5234-0.84047-0.83273-1.6809-1.6655-2.5469-2.5234-0.79406-0.79664-1.5881-1.5933-2.4062-2.4141-1.093-1.0963-1.093-1.0963-2.208-2.2148-1.5889-1.8477-1.5889-1.8477-1.5889-3.8477z" fill="#6A736B"/>\r\n        <path transform="translate(809,287)" d="m0 0c1.9919 6.925-1.0559 14.487-4.1875 20.75l-1.8125 3.25c-1.1931-3.4444-0.80482-5.3763 0.43359-8.7656 0.31904-0.88945 0.63809-1.7789 0.9668-2.6953 0.34225-0.92039 0.68449-1.8408 1.0371-2.7891 0.33838-0.93586 0.67676-1.8717 1.0254-2.8359 0.83619-2.3083 1.6821-4.6126 2.5371-6.9141z" fill="#272D28"/>\r\n        <path transform="translate(264,854)" d="m0 0h18c-4.4605 3.5684-6.8589 5.1911-12 7-0.99-0.33-1.98-0.66-3-1 2.31-0.99 4.62-1.98 7-3l-10-2v-1z" fill="#EEBC46"/>\r\n        <path transform="translate(782,362)" d="m0 0c1.2403 3.7209 0.5719 4.9946-0.75 8.625-0.5182 1.4734-0.5182 1.4734-1.0469 2.9766-1.2031 2.3984-1.2031 2.3984-4.2031 3.3984-2.6992-0.99609-2.6992-0.99609-5.6875-2.4375-0.99387-0.47309-1.9877-0.94617-3.0117-1.4336-0.75926-0.37254-1.5185-0.74508-2.3008-1.1289 3.4787-1.1596 4.3422-0.77457 7.6875 0.4375 0.80824 0.28746 1.6165 0.57492 2.4492 0.87109 0.61488 0.22816 1.2298 0.45633 1.8633 0.69141v-2h2c0.99-3.3 1.98-6.6 3-10z" fill="#868E89"/>\r\n        <path transform="translate(734,320)" d="m0 0 3 2c0.1875 2.625 0.1875 2.625 0 5h2l-1 3h-4v-3c-0.99-0.33-1.98-0.66-3-1v-5c0.99 0.33 1.98 0.66 3 1v-2z" fill="#7B827E"/>\r\n        <path transform="translate(350,620)" d="m0 0c2.8606 1.3594 4.8593 2.6452 7 5l-1 2-5-4c-0.48211 0.50531-0.96422 1.0106-1.4609 1.5312-0.63164 0.64969-1.2633 1.2994-1.9141 1.9688-0.62648 0.64969-1.253 1.2994-1.8984 1.9688-1.7266 1.5312-1.7266 1.5312-3.7266 1.5312l-1 2c0-3 0-3 1.9688-5.2617 1.253-1.2008 1.253-1.2008 2.5312-2.4258 0.83531-0.80824 1.6706-1.6165 2.5312-2.4492 0.64969-0.61488 1.2994-1.2298 1.9688-1.8633z" fill="#5F845A"/>\r\n        <path transform="translate(193,766)" d="m0 0c2 2 2 2 2.25 5.5-0.25 3.5-0.25 3.5-2.25 5.5l-1-7c-1.98 3.63-3.96 7.26-6 11l-1-2c0.89062-2.2773 0.89062-2.2773 2.25-4.9375 0.43828-0.87527 0.87656-1.7505 1.3281-2.6523 1.2949-2.1948 2.5315-3.7255 4.4219-5.4102z" fill="#1D202B"/>\r\n        <path transform="translate(732,266)" d="m0 0 2 1c-1.9681 1.9681-3.9364 3.936-5.9062 5.9023-1.6034 1.6064-3.1949 3.2245-4.7812 4.8477-2.3234 2.2606-4.7471 4.271-7.3125 6.25l-2-1c0.43868-0.40839 0.87737-0.81678 1.3293-1.2375 1.9949-1.8578 3.989-3.7163 5.9832-5.575 1.0354-0.9639 1.0354-0.9639 2.0918-1.9473 0.66709-0.62197 1.3342-1.2439 2.0215-1.8848 0.91906-0.85622 0.91906-0.85622 1.8567-1.7297 1.6011-1.5155 3.1671-3.0587 4.7175-4.6257z" fill="#69706D"/>\r\n        <path transform="translate(568,461)" d="m0 0v5c-1.4609 1.1836-1.4609 1.1836-3.375 2.4375-2.7109 1.7794-3.753 2.7544-5.625 5.5625-1.7266 1.3867-1.7266 1.3867-3.625 2.6875-0.94746 0.65549-0.94746 0.65549-1.9141 1.3242-0.72316 0.4892-0.72316 0.4892-1.4609 0.98828 1.3584-3.0433 2.8846-5.1231 5.2578-7.4531 0.6252-0.61875 1.2504-1.2375 1.8945-1.875 0.65098-0.63422 1.302-1.2684 1.9727-1.9219 0.65871-0.64969 1.3174-1.2994 1.9961-1.9688 1.6219-1.5984 3.2482-3.1919 4.8789-4.7812z" fill="#686F6B"/>\r\n        <path transform="translate(242,692)" d="m0 0 1 3-1.9375 1.25c-2.2156 1.5244-2.2156 1.5244-2.5 3.6875-0.86056 3.1554-2.9377 4.27-5.5625 6.0625h-2c1.5778-3.7105 3.907-6.2991 6.625-9.25 0.81727-0.89203 1.6345-1.7841 2.4766-2.7031 0.62648-0.67547 1.253-1.3509 1.8984-2.0469z" fill="#D69566"/>\r\n        <path transform="translate(309,616)" d="m0 0c0 3.5166-0.67787 4.3185-2.75 7.0625-0.51047 0.69223-1.0209 1.3845-1.5469 2.0977-1.7987 1.9431-3.3542 2.6892-5.7031 3.8398l-2 3-2-1c1.3891-1.7553 2.7866-3.504 4.1875-5.25 0.7773-0.97453 1.5546-1.9491 2.3555-2.9531 2.3127-2.6326 4.6551-4.7066 7.457-6.7969z" fill="#C58B5F"/>\r\n        <path transform="translate(296,820)" d="m0 0c0.125 3.375 0.125 3.375 0 7l-2 2v-7h-20v-1c2.9166-0.16803 5.8333-0.33448 8.75-0.5 1.2375-0.071543 1.2375-0.071543 2.5-0.14453 1.1988-0.067676 1.1988-0.067676 2.4219-0.13672 0.73315-0.041895 1.4663-0.083789 2.2217-0.12695 2.0338-0.08863 4.0707-0.091797 6.1064-0.091797z" fill="#EDBA44"/>\r\n        <path transform="translate(365,540)" d="m0 0c1.1289 0.93274 2.253 1.8714 3.375 2.8125 0.62648 0.52207 1.253 1.0441 1.8984 1.582 1.7266 1.6055 1.7266 1.6055 3.7266 4.6055h-4l-2 2c-0.50368-1.4571-1.0028-2.9157-1.5-4.375-0.27844-0.81211-0.55688-1.6242-0.84375-2.4609-0.65625-2.1641-0.65625-2.1641-0.65625-4.1641z" fill="#7D867F"/>\r\n        <path transform="translate(710,299)" d="m0 0c0.26925 4.8028-0.56762 8.2823-2.3125 12.75-0.64389 1.6938-0.64389 1.6938-1.3008 3.4219-1.3867 2.8281-1.3867 2.8281-4.3867 4.8281 1.8676-5.7221 3.8529-11.377 6-17l-2-1c2.875-3 2.875-3 4-3z" fill="#A3A89F"/>\r\n        <path transform="translate(805,242)" d="m0 0h4c-1.4526 3.8295-3.429 5.1205-7 7l-2-2c-0.99-0.33-1.98-0.66-3-1l1-2c1.9929-0.37366 3.9936-0.70741 6-1l1-1z" fill="#7B827F"/>\r\n        <path transform="translate(544,647)" d="m0 0c5.6683 0.59468 10.603 2.0924 15.938 4.0625 0.77924 0.28166 1.5585 0.56332 2.3613 0.85352 1.9026 0.68866 3.8022 1.3855 5.7012 2.084-3.4782 1.1594-5.459 0.70821-9 0v-2c-0.91523-0.19336-1.8305-0.38672-2.7734-0.58594-1.1885-0.26039-2.377-0.52078-3.6016-0.78906-1.1834-0.25523-2.3667-0.51047-3.5859-0.77344-3.0391-0.85156-3.0391-0.85156-5.0391-2.8516z" fill="#A47250"/>\r\n        <path transform="translate(477,554)" d="m0 0 2 1c-0.77086 0.83145-1.5417 1.6629-2.3359 2.5195-1.0131 1.0976-2.0261 2.1952-3.0391 3.293-0.50789 0.54721-1.0158 1.0944-1.5391 1.6582-2.2381 2.4295-4.2497 4.775-6.0859 7.5293-0.99-0.33-1.98-0.66-3-1 0.63615-0.61875 0.63615-0.61875 1.2852-1.25 4.4672-4.3985 8.6427-8.9847 12.715-13.75z" fill="#606762"/>\r\n        <path transform="translate(538,756)" d="m0 0c-2.2887 1.3386-4.5807 2.671-6.875 4-0.65098 0.38156-1.302 0.76312-1.9727 1.1562-4.9258 2.8438-4.9258 2.8438-7.1523 2.8438l-1 2-2-2c1.2891-0.67155 2.5814-1.3371 3.875-2 0.7193-0.37125 1.4386-0.7425 2.1797-1.125 1.9453-0.875 1.9453-0.875 3.9453-0.875l1-3c5.4023-2.2989 5.4023-2.2989 8-1z" fill="#A97551"/>\r\n        <path transform="translate(311,481)" d="m0 0h3c-0.56821 5.4548-1.9464 9.9106-4 15l-2-2c0.46094-3.0391 0.46094-3.0391 1.375-6.625 0.29648-1.1885 0.59297-2.377 0.89844-3.6016 0.23977-0.91523 0.47953-1.8305 0.72656-2.7734z" fill="#707770"/>\r\n        <path transform="translate(697,160)" d="m0 0c-2.2881 2.2881-3.8075 2.7545-6.875 3.6875-0.86367 0.27199-1.7273 0.54398-2.6172 0.82422-2.5948 0.50521-4.0386 0.34389-6.5078-0.51172h2v-2c4.9274-1.9709 8.7802-2.18 14-2z" fill="#D39968"/>\r\n        <path transform="translate(275,656)" d="m0 0 2 1c-0.48211 0.47051-0.96422 0.94102-1.4609 1.4258-0.63164 0.62262-1.2633 1.2452-1.9141 1.8867-0.62648 0.61488-1.253 1.2298-1.8984 1.8633-1.9074 1.9123-1.9074 1.9123-3.7266 4.8242-1.9675 1.0625-3.9659 2.0714-6 3 1.5658-4.0372 4.4417-6.4707 7.625-9.25l1.5625-1.3906c1.266-1.1253 2.5386-2.2431 3.8125-3.3594z" fill="#D29566"/>\r\n        <path transform="translate(489,537)" d="m0 0 1 3c-0.99 0.33-1.98 0.66-3 1 0.061875 0.78375 0.12375 1.5675 0.1875 2.375l-0.1875 2.625-3 2-2-4 7-7zm-8 8 1 3-2-1 1-2z" fill="#7E847C"/>\r\n        <path transform="translate(395,449)" d="m0 0 1 3-10 9c0-3.524 0.55115-4.015 2.8125-6.5625 0.78311-0.89912 0.78311-0.89912 1.582-1.8164 1.6055-1.6211 1.6055-1.6211 4.6055-3.6211z" fill="#CA8F63"/>\r\n        <path transform="translate(659,351)" d="m0 0 1 4-2.5625 1.5625c-3.9798 2.631-7.166 5.9918-10.438 9.4375 0-3 0-3 2.625-5.918 1.1175-1.0975 2.2429-2.1871 3.375-3.2695 0.57234-0.55881 1.1447-1.1176 1.7344-1.6934 1.4153-1.3799 2.8396-2.7504 4.2656-4.1191z" fill="#B3B8AE"/>\r\n        <path transform="translate(295,434)" d="m0 0 2 1c-2.8252 4.6725-5.6776 7.66-10 11 0-3.9613 1.3488-4.8291 4-7.6875 0.7425-0.80824 1.485-1.6165 2.25-2.4492 0.5775-0.61488 1.155-1.2298 1.75-1.8633z" fill="#AE7B56"/>\r\n        <path transform="translate(752,369)" d="m0 0c8.282 0.34725 8.282 0.34725 11.062 2.875 0.9375 2.125 0.9375 2.125 0.9375 5.125-4.5567-1.5189-8.3172-3.954-12-7v-1z" fill="#3D443E"/>\r\n        <path transform="translate(197,888)" d="m0 0c3.7189 0.50712 6.7345 1.1161 10 3v2c1.98 0.66 3.96 1.32 6 2-3 1-3 1-6.1367-0.43359-1.1893-0.65777-2.3727-1.3262-3.5508-2.0039-0.6065-0.33838-1.213-0.67676-1.8379-1.0254-1.4966-0.83669-2.9863-1.6857-4.4746-2.5371v-1z" fill="#B9825A"/>\r\n        <path transform="translate(551,613)" d="m0 0 2 1-12 11-2-1c1.3021-1.4974 2.6042-2.9948 3.9062-4.4922 1.2895-1.4672 1.2895-1.4672 1.0938-3.5078 0.78375-0.12375 1.5675-0.2475 2.375-0.375 2.7656-0.41618 2.7656-0.41618 4.625-2.625z" fill="#1E1C1E"/>\r\n        <path transform="translate(456,571)" d="m0 0 2 3-6 4 5 7c-3.7952-1.491-5.6104-3.757-8-7l7-7z" fill="#858E85"/>\r\n        <path transform="translate(282,551)" d="m0 0c1.98 0.66 3.96 1.32 6 2l0.25 2.25c0.88969 3.2622 2.235 4.5595 4.75 6.75l-1 2c-1.6728-1.7863-3.3382-3.5785-5-5.375-0.71543-0.76184-0.71543-0.76184-1.4453-1.5391-3.5547-3.8594-3.5547-3.8594-3.5547-6.0859z" fill="#191B1D"/>\r\n        <path transform="translate(317,466)" d="m0 0c3.3865 3.8702 6.3295 8.1013 8 13l-1 3-5-10h-4l2-6z" fill="#929B92"/>\r\n        <path transform="translate(818,176)" d="m0 0c2 3 2 3 1.875 5-1.114 2.5463-2.5705 3.5132-4.875 5v-3l-2-1 2-4 1 2-1 2h2l1-6z" fill="#B8B9AD"/>\r\n        <path transform="translate(322,838)" d="m0 0h1c-0.0603 1.9175-0.14917 3.8342-0.25 5.75l-0.14062 3.2344c-0.71527 3.5397-1.8652 4.7544-4.6094 7.0156 1.1506-5.398 2.4242-10.71 4-16z" fill="#F4C182"/>\r\n        <path transform="translate(843,162)" d="m0 0-7 4-1-1c-1.9214 0.32744-1.9214 0.32744-4.0625 0.9375-0.73348 0.19465-1.467 0.3893-2.2227 0.58984-0.5659 0.15598-1.1318 0.31195-1.7148 0.47266l-1-2c2.2681-0.69809 4.5387-1.3837 6.8125-2.0625 0.6426-0.19916 1.2852-0.39832 1.9473-0.60352 4.9004-1.4473 4.9004-1.4473 8.2402-0.33398z" fill="#DBDDD0"/>\r\n        <path transform="translate(545,475)" d="m0 0h1l-0.0625 2.8125c-0.095196 3.2104-0.095196 3.2104 1.0625 6.1875l-4 3c0-10 0-10 2-12z" fill="#8E948B"/>\r\n        <path transform="translate(191,773)" d="m0 0h1l1 8h1v6l-1-3h-2l-0.375-1.9375-0.625-2.0625-2-1 3-6z" fill="#E4B44E"/>\r\n        <path transform="translate(380,468)" d="m0 0c0 3.5891-0.66437 4.1086-3 6.6875-0.55688 0.62262-1.1138 1.2452-1.6875 1.8867-0.43312 0.47051-0.86625 0.94102-1.3125 1.4258l-1-4 7-6z" fill="#D89A6A"/>\r\n        <path transform="translate(746,366)" d="m0 0c4.8363 0.99044 9.4762 1.957 14 4-3.1335 1.0445-3.9897 0.93424-7 0l-1 2c-2.0383-1.274-4.0385-2.6106-6-4v-2z" fill="#2A2F2B"/>\r\n        <path transform="translate(610,261)" d="m0 0 1 2c-0.92735 1.4856-1.8672 2.9633-2.8125 4.4375-0.78311 1.2356-0.78311 1.2356-1.582 2.4961-1.6055 2.0664-1.6055 2.0664-4.6055 3.0664 1.4098-3.0385 3.0887-5.594 5.125-8.25 0.80824-1.0596 0.80824-1.0596 1.6328-2.1406 0.40992-0.53109 0.81984-1.0622 1.2422-1.6094z" fill="#9E9F96"/>\r\n        <path transform="translate(822,238)" d="m0 0c1.5639 3.9738 0.36145 6.8138-0.9375 10.75-0.38027 1.1705-0.76055 2.3409-1.1523 3.5469-0.30035 0.89203-0.6007 1.7841-0.91016 2.7031h-1c-0.46904-6.0975 1.2914-11.583 4-17z" fill="#909892"/>\r\n        <path transform="translate(708,200)" d="m0 0c-1 2-1 2-4.3125 3.1875-3.2631 0.71899-4.6803 1.0154-7.6875-0.1875h2v-2c6.2857-2.4286 6.2857-2.4286 10-1z" fill="#272B26"/>\r\n        <path transform="translate(279,856)" d="m0 0 2 1c-4.75 3-4.75 3-7 3v2c-3.287 0.79953-4.7102 1.0966-8 0 2.1204-1.0303 4.2465-2.049 6.375-3.0625 1.1834-0.56848 2.3667-1.137 3.5859-1.7227 1.0029-0.4009 2.0058-0.8018 3.0391-1.2148z" fill="#161929"/>\r\n        <path transform="translate(198,719)" d="m0 0-4 1v3l-5 2-2-3c1.2642-0.69965 2.5367-1.3843 3.8125-2.0625 0.7077-0.38285 1.4154-0.7657 2.1445-1.1602 2.043-0.77734 2.043-0.77734 5.043 0.22266z" fill="#BF885E"/>\r\n        <path transform="translate(477,341)" d="m0 0 1 2c-2.6496 3.6309-5.0182 5.8985-9 8l-1-2c2.8528-2.932 5.6508-5.6432 9-8z" fill="#C48B60"/>\r\n        <path transform="translate(810,225)" d="m0 0 5 2-3 2h2v2h-2v2h-2c-0.79953-3.287-1.0966-4.7102 0-8z" fill="#7B827F"/>\r\n        <path transform="translate(469,559)" d="m0 0 2 3-5 5c-0.99-0.33-1.98-0.66-3-1 1.98-2.31 3.96-4.62 6-7z" fill="#777E76"/>\r\n        <path transform="translate(536,546)" d="m0 0c4.6769 1.4769 4.6769 1.4769 6.3125 4.125 0.22688 0.61875 0.45375 1.2375 0.6875 1.875h-4c-3-4.1786-3-4.1786-3-6z" fill="#6D7570"/>\r\n        <path transform="translate(707,312)" d="m0 0c1 2 1 2 0.375 4.8125-1.5563 3.6078-3.4684 5.5868-6.375 8.1875l-2-1c0.76312-0.86625 1.5262-1.7325 2.3125-2.625 2.4397-2.911 4.1175-5.9044 5.6875-9.375z" fill="#6B726E"/>\r\n        <path transform="translate(355,453)" d="m0 0c6.7046 3.9562 6.7046 3.9562 7.9375 8.3125l0.0625 2.6875c-5.8021-5.6452-5.8021-5.6452-8-9v-2z" fill="#DCA06D"/>\r\n        <path transform="translate(625,277)" d="m0 0c2.7296 2.3574 3.8889 4.5813 5 8v3h-2c-2.1531-3.8576-3.3925-6.5513-3-11z" fill="#C1C0B1"/>\r\n        <path transform="translate(798,225)" d="m0 0 3 2v2l-4 2-2-5c0.99-0.33 1.98-0.66 3-1zm-5 3 3 2h-3v-2z" fill="#7C8480"/>\r\n        <path transform="translate(151,760)" d="m0 0h1c0.125 5.75 0.125 5.75-1 8h-2l-1 6c-1.371-3.6904-0.60011-5.7088 0.9375-9.25 0.38027-0.89203 0.76055-1.7841 1.1523-2.7031 0.30035-0.67547 0.6007-1.3509 0.91016-2.0469z" fill="#AD7B56"/>\r\n        <path transform="translate(520,513)" d="m0 0 1 2-2-1 1-1zm-5 5v3c-2.5 2.1875-2.5 2.1875-5 4l-2-1 7-6z" fill="#676E6A"/>\r\n        <path transform="translate(544,486)" d="m0 0c0 3.7791-0.99704 4.4611-3.5 7.1875-0.64969 0.71543-1.2994 1.4309-1.9688 2.168-0.50531 0.5427-1.0106 1.0854-1.5312 1.6445l-2-1c1.1241-1.2924 2.2493-2.5839 3.375-3.875 0.62648-0.7193 1.253-1.4386 1.8984-2.1797 1.2008-1.353 2.4474-2.6661 3.7266-3.9453z" fill="#646B67"/>\r\n        <path transform="translate(773,326)" d="m0 0c2.9719 1.1245 5.3344 2.2229 8 4l-1 3-1.75-1.4375c-2.1758-1.511-3.676-2.1029-6.25-2.5625l1-3z" fill="#7B827E"/>\r\n        <path transform="translate(511,296)" d="m0 0 1 2c-2.3896 3.243-4.2048 5.509-8 7 1.555-3.8168 4.036-6.192 7-9z" fill="#C68D61"/>\r\n        <path transform="translate(582,222)" d="m0 0c0 3.0522-0.32293 4.0453-1.75 6.625-0.32484 0.61102-0.64969 1.222-0.98438 1.8516-1.6012 1.9273-2.8354 2.1456-5.2656 2.5234 0.95545-1.4602 1.9145-2.9181 2.875-4.375 0.53367-0.81211 1.0673-1.6242 1.6172-2.4609 1.5078-2.1641 1.5078-2.1641 3.5078-4.1641z" fill="#1B1C1F"/>\r\n        <path transform="translate(325,864)" d="m0 0 1 2-6 9-1-2 1-3h2l0.375-2.4375 0.625-2.5625 2-1z" fill="#B67E57"/>\r\n        <path transform="translate(168,863)" d="m0 0 1.8125 1.5c2.1578 1.7828 2.1578 1.7828 5.1875 1.5l1 3-2 2c-1.006-0.95207-2.0046-1.9119-3-2.875-0.55688-0.53367-1.1138-1.0673-1.6875-1.6172-1.3125-1.5078-1.3125-1.5078-1.3125-3.5078z" fill="#BD8259"/>\r\n        <path transform="translate(328,855)" d="m0 0h1c0.25 2.75 0.25 2.75 0 6-2 2.375-2 2.375-4 4l-1-2c0.77734-1.9453 0.77734-1.9453 1.9375-4.125 0.57041-1.0867 0.57041-1.0867 1.1523-2.1953 0.30035-0.5543 0.6007-1.1086 0.91016-1.6797z" fill="#D79969"/>\r\n        <path transform="translate(415,421)" d="m0 0 1 4-6 5c0-4.3897 2.1281-5.7691 5-9z" fill="#B5815A"/>\r\n        <path transform="translate(633,390)" d="m0 0c0 3 0 3-1.5312 4.8242-0.64969 0.61488-1.2994 1.2298-1.9688 1.8633-0.64969 0.62262-1.2994 1.2452-1.9688 1.8867-0.50531 0.47051-1.0106 0.94102-1.5312 1.4258 0-3 0-3 2-6v-2l1.9375-0.4375c2.038-0.37257 2.038-0.37257 3.0625-1.5625z" fill="#9FA49B"/>\r\n        <path transform="translate(500,309)" d="m0 0 1 4-6 5c0-4.3897 2.1281-5.7691 5-9z" fill="#B9835B"/>\r\n        <path transform="translate(808,211)" d="m0 0 1 2h2l1-2c0.99 1.65 1.98 3.3 3 5-1.3333 0.66667-2.6667 1.3333-4 2l-4-6 1-1z" fill="#7D8480"/>\r\n        <path transform="translate(518,686)" d="m0 0c2.5 2.3125 2.5 2.3125 5 5v3l-7-6 2-2z" fill="#252A23"/>\r\n        <path transform="translate(488,567)" d="m0 0c2.125 0.375 2.125 0.375 4 1v3h-2l-2 2-2-4 2-2z" fill="#6A716C"/>\r\n        <path transform="translate(507,550)" d="m0 0h2v3h3l1 3-4 1c-2-5.875-2-5.875-2-7z" fill="#6A726C"/>\r\n        <path transform="translate(453,371)" d="m0 0 1 4-7 5c1.5271-3.436 3.5993-6.1191 6-9z" fill="#B38058"/>\r\n        <path transform="translate(466,354)" d="m0 0 1 4-5 4c0-3.9084 1.5057-5.1159 4-8z" fill="#B8835B"/>\r\n        <path transform="translate(696,312)" d="m0 0 2 4-6 4c1.75-5.75 1.75-5.75 4-8z" fill="#A3A79E"/>\r\n        <path transform="translate(811,219)" d="m0 0 2.875 1.0625c2.9956 1.2878 2.9956 1.2878 5.125-0.0625l-2 4-2-1-1 2-1-4h-2v-2z" fill="#7C8480"/>\r\n        <path transform="translate(220,854)" d="M0 0 C1.46067199 0.45082469 2.91848032 0.91093537 4.375 1.375 C5.18710938 1.63023437 5.99921875 1.88546875 6.8359375 2.1484375 C9 3 9 3 11 5 C4.61764706 5.49095023 4.61764706 5.49095023 1.5625 3.0625 C0 1 0 1 0 0 Z " fill="#CF9940"/>\r\n        <path transform="translate(515,679)" d="m0 0 5 1 1 4-3 2c-0.99-2.31-1.98-4.62-3-7z" fill="#5B645B"/>\r\n        <path transform="translate(463,430)" d="m0 0c0 3.2818-0.47836 5.1089-2 8-2.125 0.8125-2.125 0.8125-4 1 1.5271-3.436 3.5993-6.1191 6-9z" fill="#EFEFE7"/>\r\n        <path transform="translate(506,303)" d="m0 0c0 3 0 3-2.5 5.6875l-2.5 2.3125c0.3505-3.2421 0.56221-4.6153 3.0625-6.8125 0.63938-0.39188 1.2788-0.78375 1.9375-1.1875z" fill="#D89B69"/>\r\n        <path transform="translate(475,753)" d="m0 0c2.3125 0.1875 2.3125 0.1875 5 1 1.8125 2.5625 1.8125 2.5625 3 5-3.3659-1.4425-5.5105-3.3326-8-6z" fill="#B9835A"/>\r\n        <path transform="translate(162,743)" d="m0 0 1 2c-1.25 2.5625-1.25 2.5625-3 5-0.99 0.33-1.98 0.66-3 1 1.1858-3.375 2.2757-5.6472 5-8z" fill="#B47F58"/>\r\n        <path transform="translate(181,727)" d="m0 0 1 2c-1.75 1.5625-1.75 1.5625-4 3-2.25-0.3125-2.25-0.3125-4-1 2.1742-2.5004 3.7305-3.4363 7-4z" fill="#C99064"/>\r\n        <path transform="translate(242,692)" d="m0 0 1 3c-2.3125 2.5-2.3125 2.5-5 5h-3c2.31-2.64 4.62-5.28 7-8z" fill="#AE7B55"/>\r\n        <path transform="translate(370,499)" d="m0 0c0 3 0 3-1.5 4.6875l-1.5 1.3125c-1.5-1.375-1.5-1.375-3-3v-2l1.875 0.625 2.125 0.375 2-2z" fill="#E6BE85"/>\r\n        <path transform="translate(272,467)" d="m0 0 1 2c-0.93579 2.3598-1.9335 4.6963-3 7h-2c1.0588-3.4031 2.009-6.0135 4-9z" fill="#B5805A"/>\r\n        <path transform="translate(277,458)" d="m0 0c1 2 1 2 0.25 5.0625l-1.25 2.9375c-0.99 0.33-1.98 0.66-3 1 1.0588-3.4031 2.009-6.0135 4-9z" fill="#AF7C57"/>\r\n        <path transform="translate(437,392)" d="m0 0 1 4-6 4c1.3715-2.9541 2.9886-5.4401 5-8z" fill="#B18159"/>\r\n        <path transform="translate(553,310)" d="m0 0 1 4-4 3-2-1 5-6z" fill="#E8E7DD"/>\r\n        <path transform="translate(526,274)" d="m0 0 1 4-6 4c1.3715-2.9541 2.9886-5.4401 5-8z" fill="#B37F57"/>\r\n        <path transform="translate(565,222)" d="m0 0c1.125 3.75 1.125 3.75 0 6-1.6436 0.72159-3.3105 1.3935-5 2 1.3715-2.9541 2.9886-5.4401 5-8z" fill="#B98158"/>\r\n        <path transform="translate(407,717)" d="m0 0c0 3 0 3-1.3125 4.3867-1.5625 1.2044-3.125 2.4089-4.6875 3.6133l-1-3 2.375-1.375c2.662-1.5093 2.662-1.5093 4.625-3.625z" fill="#11161B"/>\r\n        <path transform="translate(477,362)" d="m0 0 1 2c-0.93306 2.7144-1.6267 3.7804-4.125 5.25l-1.875 0.75c1.1858-3.375 2.2757-5.6472 5-8z" fill="#191C1F"/>\r\n        <path transform="translate(462,361)" d="m0 0 1 2-5 5c0.3125-2.375 0.3125-2.375 1-5l3-2z" fill="#D59868"/>\r\n        <path transform="translate(531,290)" d="m0 0 2 1c-1.0487 2.6219-1.6493 3.7937-4.125 5.25l-1.875 0.75c1.074-2.9152 1.7781-4.7781 4-7z" fill="#202223"/>\r\n        <path transform="translate(793,209)" d="m0 0c0.99 0.33 1.98 0.66 3 1l-6 5-2-1 5-5z" fill="#6A706E"/>\r\n        <path transform="translate(465,748)" d="m0 0c0.99 0.33 1.98 0.66 3 1v2c-0.99-0.33-1.98-0.66-3-1v-2z" fill="#C78A5F"/>\r\n        <path transform="translate(249,531)" d="m0 0 2 4-2-1v-3z" fill="#B8835C"/>\r\n        <path transform="translate(370,472)" d="m0 0 3 2h-3v-2z" fill="#D7956A"/>\r\n        <path transform="translate(162,859)" d="m0 0 2 1-1 2-1-3z" fill="#BC835A"/>\r\n        <path transform="translate(146,829)" d="m0 0h2l-1 3-1-3z" fill="#BA815A"/>\r\n        <path transform="translate(836,340)" d="m0 0 1 4z" fill="#C98C62"/>\r\n        <path transform="translate(472,341)" d="m0 0 2 1-2 2v-3z" fill="#C2895F"/>\r\n        <path transform="translate(277,903)" d="m0 0c3 1 3 1 3 1z" fill="#BF845A"/>\r\n        <path transform="translate(228,903)" d="m0 0c3 1 3 1 3 1z" fill="#BE855B"/>\r\n        <path transform="translate(555,648)" d="m0 0c3 1 3 1 3 1z" fill="#D29063"/>\r\n        <path transform="translate(306,602)" d="m0 0 2 2h-2v-2z" fill="#CE8F63"/>\r\n        <path transform="translate(884,182)" d="m0 0 2 2h-2v-2z" fill="#C48961"/>\r\n        <path transform="translate(632,176)" d="m0 0c3 1 3 1 3 1z" fill="#CF8F62"/>\r\n        <path transform="translate(672,163)" d="m0 0c3 1 3 1 3 1z" fill="#C78B60"/>\r\n        <path transform="translate(834,114)" d="m0 0c3 1 3 1 3 1z" fill="#CA8B5F"/>\r\n        <path transform="translate(224,902)" d="m0 0 2 1z" fill="#BC835B"/>\r\n        <path transform="translate(491,766)" d="m0 0 2 1z" fill="#C2855B"/>\r\n        <path transform="translate(432,725)" d="m0 0 2 1z" fill="#D09164"/>\r\n        <path transform="translate(193,717)" d="m0 0 2 1z" fill="#C68B60"/>\r\n        <path transform="translate(595,700)" d="m0 0 2 1z" fill="#BA805A"/>\r\n        <path transform="translate(268,658)" d="m0 0 2 1z" fill="#C88B60"/>\r\n        <path transform="translate(564,651)" d="m0 0 2 1z" fill="#D49266"/>\r\n        <path transform="translate(304,601)" d="m0 0 2 1z" fill="#CC8D62"/>\r\n        <path transform="translate(600,591)" d="m0 0 2 1z" fill="#CE8E61"/>\r\n        <path transform="translate(604,588)" d="m0 0 2 1z" fill="#CD8D61"/>\r\n        <path transform="translate(273,565)" d="m0 0 2 1z" fill="#CA8C63"/>\r\n        <path transform="translate(779,438)" d="m0 0 2 1z" fill="#C58A60"/>\r\n        <path transform="translate(496,304)" d="m0 0 2 1z" fill="#BE875E"/>\r\n        <path transform="translate(867,239)" d="m0 0 2 1z" fill="#C88C64"/>\r\n        <path transform="translate(626,178)" d="m0 0 2 1z" fill="#C88A5E"/>\r\n        <path transform="translate(657,168)" d="m0 0 2 1z" fill="#CD8F65"/>\r\n        <path transform="translate(709,152)" d="m0 0 2 1z" fill="#CB8A5E"/>\r\n        <path transform="translate(776,131)" d="m0 0 2 1z" fill="#C7895F"/>\r\n        </svg>\r\n\r\n        <h1 class="page-title">Colean Client</h1>\r\n        <p id="script-description" class="page-description"></p>\r\n    </div>\r\n\r\n    <svg\r\n        id="close-button"\r\n        class="icon"\r\n        xmlns="http://www.w3.org/2000/svg"\r\n        viewBox="0 0 30 30"\r\n    >\r\n        <path d="M 7 4 C 6.744125 4 6.4879687 4.0974687 6.2929688 4.2929688 L 4.2929688 6.2929688 C 3.9019687 6.6839688 3.9019687 7.3170313 4.2929688 7.7070312 L 11.585938 15 L 4.2929688 22.292969 C 3.9019687 22.683969 3.9019687 23.317031 4.2929688 23.707031 L 6.2929688 25.707031 C 6.6839688 26.098031 7.3170313 26.098031 7.7070312 25.707031 L 15 18.414062 L 22.292969 25.707031 C 22.682969 26.098031 23.317031 26.098031 23.707031 25.707031 L 25.707031 23.707031 C 26.098031 23.316031 26.098031 22.682969 25.707031 22.292969 L 18.414062 15 L 25.707031 7.7070312 C 26.098031 7.3170312 26.098031 6.6829688 25.707031 6.2929688 L 23.707031 4.2929688 C 23.316031 3.9019687 22.682969 3.9019687 22.292969 4.2929688 L 15 11.585938 L 7.7070312 4.2929688 C 7.5115312 4.0974687 7.255875 4 7 4 z"/>\r\n    </svg>\r\n</header>';

    const Navbar_default = '<div id="navbar-container">\r\n    <button data-id="0" class="open-menu active">\r\n        <span>\r\n            <svg class="small-icon" xmlns="http://www.w3.org/2000/svg" width="512" height="512" viewBox="0 0 512 512"><path fill="currentColor" d="M240 6.1c9.1-8.2 22.9-8.2 32 0l232 208c9.9 8.8 10.7 24 1.8 33.9s-24 10.7-33.9 1.8l-8-7.2v205.3c0 35.3-28.7 64-64 64h-288c-35.3 0-64-28.7-64-64V242.6l-8 7.2c-9.9 8.8-25 8-33.9-1.8s-8-25 1.8-33.9zm16 50.1L96 199.7V448c0 8.8 7.2 16 16 16h48V360c0-39.8 32.2-72 72-72h48c39.8 0 72 32.2 72 72v104h48c8.8 0 16-7.2 16-16V199.7L256 56.3zM208 464h96V360c0-13.3-10.7-24-24-24h-48c-13.3 0-24 10.7-24 24z"/></svg>\r\n            Home\r\n        </span>\r\n    </button>\r\n    <button data-id="1" class="open-menu">\r\n        <span>\r\n            <svg class="small-icon" xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24"><path fill="currentColor" d="M6.21 13.29a.9.9 0 0 0-.33-.21a1 1 0 0 0-.76 0a.9.9 0 0 0-.54.54a1 1 0 1 0 1.84 0a1 1 0 0 0-.21-.33M13.5 11h1a1 1 0 0 0 0-2h-1a1 1 0 0 0 0 2m-4 0h1a1 1 0 0 0 0-2h-1a1 1 0 0 0 0 2m-3-2h-1a1 1 0 0 0 0 2h1a1 1 0 0 0 0-2M20 5H4a3 3 0 0 0-3 3v8a3 3 0 0 0 3 3h16a3 3 0 0 0 3-3V8a3 3 0 0 0-3-3m1 11a1 1 0 0 1-1 1H4a1 1 0 0 1-1-1V8a1 1 0 0 1 1-1h16a1 1 0 0 1 1 1Zm-6-3H9a1 1 0 0 0 0 2h6a1 1 0 0 0 0-2m3.5-4h-1a1 1 0 0 0 0 2h1a1 1 0 0 0 0-2m.71 4.29a1 1 0 0 0-.33-.21a1 1 0 0 0-.76 0a.9.9 0 0 0-.33.21a1 1 0 0 0-.21.33a1 1 0 1 0 1.92.38a.84.84 0 0 0-.08-.38a1 1 0 0 0-.21-.33"/></svg>\r\n            Keybinds\r\n        </span>\r\n    </button>\r\n    <button data-id="2" class="open-menu">\r\n        <span>\r\n            <svg class="small-icon" xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24"><path fill="currentColor" d="m19.05 21.6l-2.925-2.9l-2.2 2.2l-.7-.7q-.575-.575-.575-1.425t.575-1.425l4.225-4.225q.575-.575 1.425-.575t1.425.575l.7.7l-2.2 2.2l2.9 2.925q.3.3.3.7t-.3.7l-1.25 1.25q-.3.3-.7.3t-.7-.3M22 5.9L10.65 17.25l.125.1q.575.575.575 1.425t-.575 1.425l-.7.7l-2.2-2.2l-2.925 2.9q-.3.3-.7.3t-.7-.3L2.3 20.35q-.3-.3-.3-.7t.3-.7l2.9-2.925l-2.2-2.2l.7-.7q.575-.575 1.425-.575t1.425.575l.1.125L18 1.9h4zM6.95 10.85L2 5.9v-4h4l4.95 4.95z"/></svg>\r\n            Combat\r\n        </span>\r\n    </button>\r\n    <button data-id="3" class="open-menu">\r\n        <span>\r\n            <svg class="small-icon" xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24"><g fill="none" stroke="currentColor" stroke-linecap="round" stroke-linejoin="round" stroke-width="2"><path d="M12 5c-6.307 0-9.367 5.683-9.91 6.808a.44.44 0 0 0 0 .384C2.632 13.317 5.692 19 12 19s9.367-5.683 9.91-6.808a.44.44 0 0 0 0-.384C21.368 10.683 18.308 5 12 5"/><circle cx="12" cy="12" r="3"/></g></svg>\r\n            Visuals\r\n        </span>\r\n    </button>\r\n    <button data-id="4" class="open-menu">\r\n        <span>\r\n            <svg class="small-icon" xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24"><path fill="currentColor" d="M2 18h7v2H2zm0-7h9v2H2zm0-7h20v2H2zm18.674 9.025l1.156-.391l1 1.732l-.916.805a4 4 0 0 1 0 1.658l.916.805l-1 1.732l-1.156-.391a4 4 0 0 1-1.435.83L19 21h-2l-.24-1.196a4 4 0 0 1-1.434-.83l-1.156.392l-1-1.732l.916-.805a4 4 0 0 1 0-1.658l-.916-.805l1-1.732l1.156.391c.41-.37.898-.655 1.435-.83L17 11h2l.24 1.196a4 4 0 0 1 1.434.83M18 17a1 1 0 1 0 0-2a1 1 0 0 0 0 2"/></svg>\r\n            Misc\r\n        </span>\r\n    </button>\r\n    <button data-id="5" class="open-menu">\r\n        <span>\r\n            <svg class="small-icon" xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24"><path fill="currentColor" d="M22 14h-1c0-3.87-3.13-7-7-7h-1V5.73A2 2 0 1 0 10 4c0 .74.4 1.39 1 1.73V7h-1c-3.87 0-7 3.13-7 7H2c-.55 0-1 .45-1 1v3c0 .55.45 1 1 1h1v1a2 2 0 0 0 2 2h14c1.11 0 2-.89 2-2v-1h1c.55 0 1-.45 1-1v-3c0-.55-.45-1-1-1m-1 3h-2v3H5v-3H3v-1h2v-2c0-2.76 2.24-5 5-5h4c2.76 0 5 2.24 5 5v2h2zm-3.5-1.5c0 1.11-.89 2-2 2c-.97 0-1.77-.69-1.96-1.6l2.96-2.12c.6.35 1 .98 1 1.72m-10-1.72l2.96 2.12c-.18.91-.99 1.6-1.96 1.6a2 2 0 0 1-2-2c0-.74.4-1.37 1-1.72"/></svg>\r\n            Bots\r\n        </span>\r\n    </button>\r\n    <button data-id="6" class="open-menu bottom-align">\r\n        <span>\r\n            <svg class="small-icon" xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24"><path fill="currentColor" d="m19.546 7.573l-1.531-1.57l-1.442 1.291l-.959.86l3.876 3.987l-2.426 2.496l-1.451 1.492c.55.499 1.091.99 1.64 1.486l.764.694l2.21-2.277L24 12.14v-.001zM2.992 9.072L0 12.14c2.01 2.073 3.993 4.115 5.984 6.167l.51-.464l1.893-1.715L6.94 14.64l-2.43-2.5l3.109-3.196l.767-.789c-.434-.39-.86-.772-1.288-1.154L5.984 6v.001zm12.585-6.038L11.632 21.6l-.196-.039l-3.029-.595l2.555-12.02L12.353 2.4z"/></svg>\r\n            Devtool\r\n        </span>\r\n    </button>\r\n</div>';

    const Home_default = "<div class=\"menu-page opened\" data-id=\"0\">\r\n    <div class=\"page-title\">Home</div>\r\n\r\n    <div class=\"section\">\r\n        <div class=\"section-title\">Welcome to the Colean Client!</div>\r\n        <div class=\"section-content\">\r\n\r\n            <div class=\"content-option left-flex text\">\r\n                <span class=\"option-title\">Author: </span>\r\n                <span id=\"author\" class=\"text-value\">ItzYakudza</span>\r\n            </div>\r\n\r\n        </div>\r\n    </div>\r\n\r\n</div>";

    const Keybinds_default = '<div class="menu-page" data-id="1">\r\n    <div class="page-title">Keybinds</div>\r\n    <p class="page-description">Setup keybinds for items, weapons and hats</p>\r\n\r\n    \x3c!-- Items & Weapons --\x3e\r\n    <div class="section">\r\n        <div class="section-title">Items & Weapons</div>\r\n        <div class="section-content split">\r\n\r\n            <div class="content-split">\r\n                <div class="content-option">\r\n                    <span class="option-title">Food</span>\r\n                    <button id="_food" class="hotkeyInput"></button>\r\n                    <span class="option-description">It is useful to press this button, when you have a really high ping. Because AutoQ is not able to detect such threats</span>\r\n                </div>\r\n\r\n                <div class="content-option">\r\n                    <span class="option-title">Wall</span>\r\n                    <button id="_wall" class="hotkeyInput"></button>\r\n                </div>\r\n\r\n                <div class="content-option">\r\n                    <span class="option-title">Spike</span>\r\n                    <button id="_spike" class="hotkeyInput"></button>\r\n                </div>\r\n\r\n                <div class="content-option">\r\n                    <span class="option-title">Windmill</span>\r\n                    <button id="_windmill" class="hotkeyInput"></button>\r\n                </div>\r\n            </div>\r\n\r\n            <div class="content-split">\r\n                <div class="content-option">\r\n                    <span class="option-title">Farm</span>\r\n                    <button id="_farm" class="hotkeyInput"></button>\r\n                    <span class="option-description">Places trees/mines</span>\r\n                </div>\r\n\r\n                <div class="content-option">\r\n                    <span class="option-title">Trap</span>\r\n                    <button id="_trap" class="hotkeyInput"></button>\r\n                    <span class="option-description">Places traps/boostpads</span>\r\n                </div>\r\n\r\n                <div class="content-option">\r\n                    <span class="option-title">Turret</span>\r\n                    <button id="_turret" class="hotkeyInput"></button>\r\n                    <span class="option-description">Places turrets, teleports, platforms etc</span>\r\n                </div>\r\n\r\n                <div class="content-option">\r\n                    <span class="option-title">Spawn</span>\r\n                    <button id="_spawn" class="hotkeyInput"></button>\r\n                </div>\r\n            </div>\r\n        </div>\r\n    </div>\r\n\r\n    \x3c!-- Controls & Movement --\x3e\r\n    <div class="section">\r\n        <div class="section-title">Controls & Movement</div>\r\n        <div class="section-content">\r\n\r\n            <div class="content-split">\r\n\r\n                <div class="content-option">\r\n                    <span class="option-title">Lock bot position</span>\r\n                    <button id="_lockBotPosition" class="hotkeyInput"></button>\r\n                    <span class="option-description">Press this button and bots will be locked to your last cursor position</span>\r\n                </div>\r\n\r\n                <div class="content-option">\r\n                    <span class="option-title">Toggle Shop</span>\r\n                    <button id="_toggleShop" class="hotkeyInput"></button>\r\n                </div>\r\n\r\n                <div class="content-option">\r\n                    <span class="option-title">Toggle Clan</span>\r\n                    <button id="_toggleClan" class="hotkeyInput"></button>\r\n                </div>\r\n\r\n                <div class="content-option">\r\n                    <span class="option-title">Toggle Menu</span>\r\n                    <button id="_toggleMenu" class="hotkeyInput"></button>\r\n                    <span class="option-description">Press this button to open and close the menu</span>\r\n                </div>\r\n\r\n                <div class="content-option">\r\n                    <span class="option-title">Instakill</span>\r\n                    <button id="_instakill" class="hotkeyInput"></button>\r\n                </div>\r\n\r\n            </div>\r\n        </div>\r\n    </div>\r\n</div>';

    const Combat_default = "<div class=\"menu-page\" data-id=\"2\">\r\n    <div class=\"page-title\">Combat</div>\r\n    <p class=\"page-description\">Modify combat settings, change pvp behavior</p>\r\n\r\n    <!-- Defense -->\r\n    <div class=\"section\">\r\n        <div class=\"section-title\">Defense</div>\r\n        <div class=\"section-content\">\r\n\r\n            <!-- <div class=\"content-option\">\r\n                <span class=\"option-title\">Biome hats</span>\r\n                <label class=\"switch-checkbox\">\r\n                    <input id=\"_biomehats\" type=\"checkbox\"></input>\r\n                    <span></span>\r\n                </label>\r\n            </div> -->\r\n\r\n            <!-- <div class=\"content-option\">\r\n                <span class=\"option-title\">Auto emp</span>\r\n                <label class=\"switch-checkbox\">\r\n                    <input id=\"_autoemp\" type=\"checkbox\"></input>\r\n                    <span></span>\r\n                </label>\r\n            </div> -->\r\n\r\n            <div class=\"content-option\">\r\n                <span class=\"option-title\">Anti enemy</span>\r\n                <label class=\"switch-checkbox\">\r\n                    <input id=\"_antienemy\" type=\"checkbox\"></input>\r\n                    <span></span>\r\n                </label>\r\n                <span class=\"option-description\">Basic soldier equipment for all types of antis</span>\r\n            </div>\r\n\r\n            <!-- <div class=\"content-option\">\r\n                <span class=\"option-title\">Soldier default</span>\r\n                <label class=\"switch-checkbox\">\r\n                    <input id=\"_soldierDefault\" type=\"checkbox\"></input>\r\n                    <span></span>\r\n                </label>\r\n\r\n                <span class=\"option-description\">Equips soldier by default, when antis fail to do its work</span>\r\n            </div> -->\r\n\r\n            <!-- <div class=\"content-option\">\r\n                <span class=\"option-title\">Anti animal</span>\r\n                <label class=\"switch-checkbox\">\r\n                    <input id=\"_antianimal\" type=\"checkbox\"></input>\r\n                    <span></span>\r\n                </label>\r\n                <span class=\"option-description\">Equips a soldier when danger animal is nearby</span>\r\n            </div> -->\r\n\r\n            <div class=\"content-option\">\r\n                <span class=\"option-title\">Anti spike</span>\r\n                <label class=\"switch-checkbox\">\r\n                    <input id=\"_antispike\" type=\"checkbox\"></input>\r\n                    <span></span>\r\n                </label>\r\n                <span class=\"option-description\">Adds additional layer of protection against spikes</span>\r\n            </div>\r\n\r\n            <div class=\"content-option\">\r\n                <span class=\"option-title\">Emp Defense</span>\r\n                <label class=\"switch-checkbox\">\r\n                    <input id=\"_empDefense\" type=\"checkbox\"></input>\r\n                    <span></span>\r\n                </label>\r\n                <span class=\"option-description\">Equips emp by default when you are not moving</span>\r\n            </div>\r\n\r\n            <div class=\"content-option\">\r\n                <span class=\"option-title\">Autoheal</span>\r\n                <label class=\"switch-checkbox\">\r\n                    <input id=\"_autoheal\" type=\"checkbox\"></input>\r\n                    <span></span>\r\n                </label>\r\n            </div>\r\n            \r\n            <div class=\"content-option\">\r\n                <span class=\"option-title\">Autobreak</span>\r\n                <label class=\"switch-checkbox\">\r\n                    <input id=\"_autobreak\" type=\"checkbox\"></input>\r\n                    <span></span>\r\n                </label>\r\n                <span class=\"option-description\">Destroys nearby enemy traps, spikes, boost pads and teleporters</span>\r\n            </div>\r\n\r\n            <div class=\"content-option\">\r\n                <span class=\"option-title\">Safe walk</span>\r\n                <label class=\"switch-checkbox\">\r\n                    <input id=\"_safeWalk\" type=\"checkbox\"></input>\r\n                    <span></span>\r\n                </label>\r\n                <span class=\"option-description\">Prevents collision with enemy spikes, cactuses, boost pads and teleporters</span>\r\n            </div>\r\n\r\n            <div class=\"content-option\">\r\n                <span class=\"option-title\">Auto Shield</span>\r\n                <label class=\"switch-checkbox\">\r\n                    <input id=\"_autoShield\" type=\"checkbox\"></input>\r\n                    <span></span>\r\n                </label>\r\n                <span class=\"option-description\">Automatically selects shield on potential threats</span>\r\n            </div>\r\n\r\n            <div class=\"content-option\">\r\n                <span class=\"option-title\">Tail Priority</span>\r\n                <label class=\"switch-checkbox\">\r\n                    <input id=\"_tailPriority\" type=\"checkbox\"></input>\r\n                    <span></span>\r\n                </label>\r\n                <span class=\"option-description\">Equips monkey tail to get additional speed. In very close combat may not switch back to CX</span>\r\n            </div>\r\n\r\n            \r\n        </div>\r\n    </div>\r\n\r\n    <!-- Placement -->\r\n     <div class=\"section\">\r\n        <div class=\"section-title\">Placement</div>\r\n\r\n        <div class=\"section-content\">\r\n            <div class=\"content-option\">\r\n                <span class=\"option-title\">Autoplacer</span>\r\n                <label class=\"switch-checkbox\">\r\n                    <input id=\"_autoplacer\" type=\"checkbox\"></input>\r\n                    <span></span>\r\n                </label>\r\n                <span class=\"option-description\">Automatically places traps and spikes when enemy is nearby</span>\r\n            </div>\r\n\r\n            <!-- <div class=\"content-option\">\r\n                <span class=\"option-title\">Preplacer</span>\r\n                <label class=\"switch-checkbox\">\r\n                    <input id=\"_preplacer\" type=\"checkbox\"></input>\r\n                    <span></span>\r\n                </label>\r\n            </div> -->\r\n\r\n            <div class=\"content-option\">\r\n                <span class=\"option-title\">Autoplacer radius</span>\r\n                <label class=\"slider\">\r\n                    <span class=\"slider-value\"></span>\r\n                    <input id=\"_autoplacerRadius\" type=\"range\" step=\"25\" min=\"100\" max=\"450\">\r\n                </label>\r\n            </div>\r\n\r\n            <div class=\"content-option\">\r\n                <span class=\"option-title\">Placement accuracy</span>\r\n                <label class=\"slider\">\r\n                    <span class=\"slider-value\"></span>\r\n                    <input id=\"_placeAttempts\" type=\"range\" min=\"1\" max=\"10\">\r\n                </label>\r\n                <span class=\"option-description\">Algorithm calculates all the possible attempts. But later this value decreases in order to avoid lags.</span>\r\n            </div>\r\n\r\n            <div class=\"content-option\">\r\n                <span class=\"option-title\">Automill</span>\r\n                <label class=\"switch-checkbox\">\r\n                    <input id=\"_automill\" type=\"checkbox\"></input>\r\n                    <span></span>\r\n                </label>\r\n                <span class=\"option-description\">Automatically places 3x windmills behind your back</span>\r\n            </div>\r\n\r\n            <div class=\"content-option\">\r\n                <span class=\"option-title\">Auto grind</span>\r\n                <label class=\"switch-checkbox\">\r\n                    <input id=\"_autoGrind\" type=\"checkbox\"></input>\r\n                    <span></span>\r\n                </label>\r\n                <span class=\"option-description\">Stay still to get autogrind working</span>\r\n            </div>\r\n\r\n            <div class=\"content-option\">\r\n                <span class=\"option-title\">Placement Defense</span>\r\n                <label class=\"switch-checkbox\">\r\n                    <input id=\"_placementDefense\" type=\"checkbox\"></input>\r\n                    <span></span>\r\n                </label>\r\n                <span class=\"option-description\">Places a wall/windmill on projectile threats</span>\r\n            </div>\r\n\r\n            <div class=\"content-option\">\r\n                <span class=\"option-title\">Dash Movement</span>\r\n                <label class=\"switch-checkbox\">\r\n                    <input id=\"_dashMovement\" type=\"checkbox\"></input>\r\n                    <span></span>\r\n                </label>\r\n                <span class=\"option-description\">When holding a boostpad hotkey, it is gonna place boost pad once and immediately destroy it, giving you additional speed.</span>\r\n            </div>\r\n        </div>\r\n    </div>\r\n    \r\n    <!-- Instakills -->\r\n    <div class=\"section\">\r\n        <div class=\"section-title\">Instakills</div>\r\n\r\n        <div class=\"section-content\">\r\n            <div class=\"content-option\">\r\n                <span class=\"option-title\">Auto sync</span>\r\n                <label class=\"switch-checkbox\">\r\n                    <input id=\"_autoSync\" type=\"checkbox\"></input>\r\n                    <span></span>\r\n                </label>\r\n                <span class=\"option-description\">Attacks when it is possible to sync enemy with 2 primary weapons</span>\r\n            </div>\r\n\r\n            <div class=\"content-option\">\r\n                <span class=\"option-title\">Velocity tick</span>\r\n                <label class=\"switch-checkbox\">\r\n                    <input id=\"_velocityTick\" type=\"checkbox\"></input>\r\n                    <span></span>\r\n                </label>\r\n                <span class=\"option-description\">Attacks using turret + diamond polearm in one tick</span>\r\n            </div>\r\n\r\n            <div class=\"content-option\">\r\n                <span class=\"option-title\">Spike tick</span>\r\n                <label class=\"switch-checkbox\">\r\n                    <input id=\"_spikeTick\" type=\"checkbox\"></input>\r\n                    <span></span>\r\n                </label>\r\n                <span class=\"option-description\">When enemy is about to collide a spike, attacks with primary weapon</span>\r\n            </div>\r\n\r\n            <div class=\"content-option\">\r\n                <span class=\"option-title\">Spike sync</span>\r\n                <label class=\"switch-checkbox\">\r\n                    <input id=\"_spikeSync\" type=\"checkbox\"></input>\r\n                    <span></span>\r\n                </label>\r\n            </div>\r\n\r\n            <div class=\"content-option\">\r\n                <span class=\"option-title\">Spike sync hammer</span>\r\n                <label class=\"switch-checkbox\">\r\n                    <input id=\"_spikeSyncHammer\" type=\"checkbox\"></input>\r\n                    <span></span>\r\n                </label>\r\n            </div>\r\n\r\n            <div class=\"content-option\">\r\n                <span class=\"option-title\">Knockback tick</span>\r\n                <label class=\"switch-checkbox\">\r\n                    <input id=\"_knockbackTick\" type=\"checkbox\"></input>\r\n                    <span></span>\r\n                </label>\r\n                <span class=\"option-description\">Attacks enemy when its possible to knockback on spike</span>\r\n            </div>\r\n\r\n            <div class=\"content-option\">\r\n                <span class=\"option-title\">Knockback tick hammer</span>\r\n                <label class=\"switch-checkbox\">\r\n                    <input id=\"_knockbackTickHammer\" type=\"checkbox\"></input>\r\n                    <span></span>\r\n                </label>\r\n                <span class=\"option-description\">Knockbacks enemy using hammer + turret + primary weapon on spike</span>\r\n            </div>\r\n\r\n            <div class=\"content-option\">\r\n                <span class=\"option-title\">Knockback tick trap</span>\r\n                <label class=\"switch-checkbox\">\r\n                    <input id=\"_knockbackTickTrap\" type=\"checkbox\"></input>\r\n                    <span></span>\r\n                </label>\r\n                <span class=\"option-description\">Destroys a trap and knockbacks enemy on spike</span>\r\n            </div>\r\n\r\n            <div class=\"content-option\">\r\n                <span class=\"option-title\">Anti Retrap</span>\r\n                <label class=\"switch-checkbox\">\r\n                    <input id=\"_antiRetrap\" type=\"checkbox\"></input>\r\n                    <span></span>\r\n                </label>\r\n                <span class=\"option-description\">When you are trapped, attacks enemy with primary weapon to push it away</span>\r\n            </div>\r\n\r\n            <div class=\"content-option\">\r\n                <span class=\"option-title\">Tool Spear Insta</span>\r\n                <label class=\"switch-checkbox\">\r\n                    <input id=\"_toolSpearInsta\" type=\"checkbox\"></input>\r\n                    <span></span>\r\n                </label>\r\n\r\n                <span class=\"option-description\">When you have Tool Hammer and also Polearm could be upgraded, then it is going to perform instakill on nearest enemy.</span>\r\n            </div>\r\n\r\n            <div class=\"content-option\">\r\n                <span class=\"option-title\">Autosteal</span>\r\n                <label class=\"switch-checkbox\">\r\n                    <input id=\"_autoSteal\" type=\"checkbox\"></input>\r\n                    <span></span>\r\n                </label>\r\n                <span class=\"option-description\">Steals kills/animals from other players</span>\r\n            </div>\r\n\r\n            <div class=\"content-option\">\r\n                <span class=\"option-title\">Autopush</span>\r\n                <label class=\"switch-checkbox\">\r\n                    <input id=\"_autoPush\" type=\"checkbox\"></input>\r\n                    <span></span>\r\n                </label>\r\n            </div>\r\n\r\n            <div class=\"content-option\">\r\n                <span class=\"option-title\">Turret steal</span>\r\n                <label class=\"switch-checkbox\">\r\n                    <input id=\"_turretSteal\" type=\"checkbox\"></input>\r\n                    <span></span>\r\n                </label>\r\n                <span class=\"option-description\">Equips a turret hat if possible to kill with it</span>\r\n            </div>\r\n\r\n            <div class=\"content-option\">\r\n                <span class=\"option-title\">Spike Gear Insta</span>\r\n                <label class=\"switch-checkbox\">\r\n                    <input id=\"_spikeGearInsta\" type=\"checkbox\"></input>\r\n                    <span></span>\r\n                </label>\r\n\r\n                <span class=\"option-description\">Equips Spike Gear when it is possible to deal potential damage with it to the enemy. Instakill may happen.</span>\r\n            </div>\r\n\r\n            <div class=\"content-option\">\r\n                <span class=\"option-title\">Turret Sync</span>\r\n                <label class=\"switch-checkbox\">\r\n                    <input id=\"_turretSync\" type=\"checkbox\"></input>\r\n                    <span></span>\r\n                </label>\r\n                <span class=\"option-description\">Attacks using primary in sync with other turret objects</span>\r\n            </div>\r\n\r\n            <div class=\"content-option\">\r\n                <span class=\"option-title\">Trap KB</span>\r\n                <label class=\"switch-checkbox\">\r\n                    <input id=\"_trapKB\" type=\"checkbox\"></input>\r\n                    <span></span>\r\n                </label>\r\n                <span class=\"option-description\">Attacks enemies to knockback them into traps. Useful with daggers and bat</span>\r\n            </div>\r\n\r\n            <div class=\"content-option\">\r\n                <span class=\"option-title\">Shame Spam</span>\r\n                <label class=\"switch-checkbox\">\r\n                    <input id=\"_shameSpam\" type=\"checkbox\"></input>\r\n                    <span></span>\r\n                </label>\r\n                <span class=\"option-description\">Starts destroying enemy's trap to increase his shameCount, which results in poleaids finish. Works only with polearm and katana</span>\r\n            </div>\r\n        </div>\r\n    </div>\r\n\r\n</div>";

    const Visuals_default = '<div class="menu-page" data-id="3">\r\n    <div class="page-title">Visuals</div>\r\n    <p class="page-description">Customize your visuals, or you can disable it for performance</p>\r\n\r\n    \x3c!-- Tracers --\x3e\r\n    <div class="section">\r\n        <div class="section-title">Tracers</div>\r\n        <div class="section-content">\r\n\r\n            <div class="content-option">\r\n                <span class="option-title">Enemies</span>\r\n                <div class="option-content">\r\n                    <button class="reset-color" title="Reset Color"></button>\r\n                    <input id="_enemyTracersColor" type="color" title="Select Color">\r\n                    <label class="switch-checkbox">\r\n                        <input id="_enemyTracers" type="checkbox"></input>\r\n                        <span></span>\r\n                    </label>\r\n                </div>\r\n            </div>\r\n\r\n            <div class="content-option">\r\n                    <span class="option-title">Teammates</span>\r\n                    <div class="option-content">\r\n                        <button class="reset-color" title="Reset Color"></button>\r\n                        <input id="_teammateTracersColor" type="color" title="Select Color">\r\n                        <label class="switch-checkbox">\r\n                            <input id="_teammateTracers" type="checkbox"></input>\r\n                            <span></span>\r\n                        </label>\r\n                    </div>\r\n                </div>\r\n\r\n                <div class="content-option">\r\n                    <span class="option-title">Animal</span>\r\n                    <div class="option-content">\r\n                        <button class="reset-color" title="Reset Color"></button>\r\n                        <input id="_animalTracersColor" type="color" title="Select Color">\r\n                        <label class="switch-checkbox">\r\n                            <input id="_animalTracers" type="checkbox"></input>\r\n                            <span></span>\r\n                        </label>\r\n                    </div>\r\n                </div>\r\n\r\n                <div class="content-option">\r\n                    <span class="option-title">Notification</span>\r\n                    <div class="option-content">\r\n                        <button class="reset-color" title="Reset Color"></button>\r\n                        <input id="_notificationTracersColor" type="color" title="Select Color">\r\n                        <label class="switch-checkbox">\r\n                            <input id="_notificationTracers" type="checkbox"></input>\r\n                            <span></span>\r\n                        </label>\r\n                    </div>\r\n                </div>\r\n\r\n        </div>\r\n    </div>\r\n\r\n    \x3c!-- Markers --\x3e\r\n    <div class="section">\r\n        <div class="section-title">Markers</div>\r\n\r\n        <div class="section-content">\r\n\r\n            <div class="content-option">\r\n                <span class="option-title">Item Markers</span>\r\n                <div class="option-content">\r\n                    <button class="reset-color" title="Reset Color"></button>\r\n                    <input id="_itemMarkersColor" type="color" title="Select Color">\r\n                    <label class="switch-checkbox">\r\n                        <input id="_itemMarkers" type="checkbox"></input>\r\n                        <span></span>\r\n                    </label>\r\n                </div>\r\n            </div>\r\n\r\n            <div class="content-option">\r\n                <span class="option-title">Teammates</span>\r\n                <div class="option-content">\r\n                    <button class="reset-color" title="Reset Color"></button>\r\n                    <input id="_teammateMarkersColor" type="color" title="Select Color">\r\n                    <label class="switch-checkbox">\r\n                        <input id="_teammateMarkers" type="checkbox"></input>\r\n                        <span></span>\r\n                    </label>\r\n                </div>\r\n            </div>\r\n\r\n            <div class="content-option">\r\n                <span class="option-title">Enemies</span>\r\n                <div class="option-content">\r\n                    <button class="reset-color" title="Reset Color"></button>\r\n                    <input id="_enemyMarkersColor" type="color" title="Select Color">\r\n                    <label class="switch-checkbox">\r\n                        <input id="_enemyMarkers" type="checkbox"></input>\r\n                        <span></span>\r\n                    </label>\r\n                </div>\r\n            </div>\r\n                \r\n        </div>\r\n    </div>\r\n\r\n    \x3c!-- Player --\x3e\r\n    <div class="section">\r\n        <div class="section-title">Player</div>\r\n\r\n        <div class="section-content">\r\n\r\n            <div class="content-option">\r\n                <span class="option-title">Weapon XP Bar</span>\r\n                <label class="switch-checkbox">\r\n                    <input id="_weaponXPBar" type="checkbox"></input>\r\n                    <span></span>\r\n                </label>\r\n            </div>\r\n\r\n            <div class="content-option">\r\n                <span class="option-title">Turret Reload Bar</span>\r\n                <div class="option-content">\r\n                    <button class="reset-color" title="Reset Color"></button>\r\n                    <input id="_playerTurretReloadBarColor" type="color" title="Select Color">\r\n                    <label class="switch-checkbox">\r\n                        <input id="_playerTurretReloadBar" type="checkbox"></input>\r\n                        <span></span>\r\n                    </label>\r\n                </div>\r\n            </div>\r\n\r\n            <div class="content-option">\r\n                <span class="option-title">Weapon Reload Bar</span>\r\n                <div class="option-content">\r\n                    <button class="reset-color" title="Reset Color"></button>\r\n                    <input id="_weaponReloadBarColor" type="color" title="Select Color">\r\n                    <label class="switch-checkbox">\r\n                        <input id="_weaponReloadBar" type="checkbox"></input>\r\n                        <span></span>\r\n                    </label>\r\n                </div>\r\n            </div>\r\n\r\n            <div class="content-option">\r\n                <span class="option-title">Render HP</span>\r\n                <label class="switch-checkbox">\r\n                    <input id="_renderHP" type="checkbox"></input>\r\n                    <span></span>\r\n                </label>\r\n            </div>\r\n\r\n            <div class="content-option">\r\n                <span class="option-title">Position Prediction</span>\r\n                <label class="switch-checkbox">\r\n                    <input id="_positionPrediction" type="checkbox"></input>\r\n                    <span></span>\r\n                </label>\r\n            </div>\r\n\r\n            \x3c!-- <div class="content-option">\r\n                <span class="option-title">Stacked Damage</span>\r\n                <label class="switch-checkbox">\r\n                    <input id="_stackedDamage" type="checkbox"></input>\r\n                    <span></span>\r\n                </label>\r\n            </div> --\x3e\r\n        </div>\r\n    </div>\r\n\r\n    \x3c!-- Object --\x3e\r\n    <div class="section">\r\n        <div class="section-title">Object</div>\r\n\r\n        <div class="section-content">\r\n\r\n            <div class="content-option">\r\n                <span class="option-title">Turret Reload Bar</span>\r\n                <div class="option-content">\r\n                    <button class="reset-color" title="Reset Color"></button>\r\n                    <input id="_objectTurretReloadBarColor" type="color" title="Select Color">\r\n                    <label class="switch-checkbox">\r\n                        <input id="_objectTurretReloadBar" type="checkbox"></input>\r\n                        <span></span>\r\n                    </label>\r\n                </div>\r\n            </div>\r\n\r\n            <div class="content-option">\r\n                <span class="option-title">Item Health Bar</span>\r\n                <div class="option-content">\r\n                    <button class="reset-color" title="Reset Color"></button>\r\n                    <input id="_itemHealthBarColor" type="color" title="Select Color">\r\n                    <label class="switch-checkbox">\r\n                        <input id="_itemHealthBar" type="checkbox"></input>\r\n                        <span></span>\r\n                    </label>\r\n                </div>\r\n            </div>\r\n\r\n        </div>\r\n    </div>\r\n\r\n</div>';

    const Misc_default = '<div class="menu-page" data-id="4">\r\n    <div class="page-title">Misc</div>\r\n    <p class="page-description">Customize misc settings and reset preferences</p>\r\n\r\n    \x3c!-- Other --\x3e\r\n    <div class="section">\r\n        <h2 class="section-title">Other</h2>\r\n\r\n        <div class="section-content">\r\n\r\n            <div class="content-option">\r\n                <span class="option-title">Kill Message</span>\r\n                <div class="option-content">\r\n                    <input id="_killMessageText" class="input" type="text" maxlength="30">\r\n                    <label class="switch-checkbox">\r\n                        <input id="_killMessage" type="checkbox">\r\n                        <span></span>\r\n                    </label>\r\n                </div>\r\n            </div>\r\n\r\n            <div class="content-option">\r\n                <span class="option-title">Autospawn</span>\r\n                <label class="switch-checkbox">\r\n                    <input id="_autospawn" type="checkbox"></input>\r\n                    <span></span>\r\n                </label>\r\n            </div>\r\n\r\n            <div class="content-option">\r\n                <span class="option-title">Autoaccept</span>\r\n                <label class="switch-checkbox">\r\n                    <input id="_autoaccept" type="checkbox"></input>\r\n                    <span></span>\r\n                </label>\r\n            </div>\r\n\r\n            <div class="content-option">\r\n                <span class="option-title">Texture pack</span>\r\n                <label class="switch-checkbox">\r\n                    <input id="_texturepack" type="checkbox"></input>\r\n                    <span></span>\r\n                </label>\r\n                <span class="option-description">Some old looking texture pack. Reload the page to make it work! :)</span>\r\n            </div>\r\n\r\n            <div class="content-option">\r\n                <span class="option-title">Hide game HUD</span>\r\n                <label class="switch-checkbox">\r\n                    <input id="_hideHUD" type="checkbox"></input>\r\n                    <span></span>\r\n                </label>\r\n            </div>\r\n\r\n            <div class="content-option">\r\n                <span class="option-title">Chat Log</span>\r\n                <label class="switch-checkbox">\r\n                    <input id="_chatLog" type="checkbox"></input>\r\n                    <span></span>\r\n                </label>\r\n\r\n                <span class="option-description">Use this only for debugging purposes. Report about any known problems</span>\r\n            </div>\r\n\r\n            <div class="content-option">\r\n                <button id="resetSettings" class="option-button red">RESET SETTINGS</button>\r\n            </div>\r\n\r\n        </div>\r\n    </div>\r\n\r\n\r\n    \x3c!-- Menu --\x3e\r\n    \x3c!-- <div class="section">\r\n        <h2 class="section-title">Menu</h2>\r\n\r\n        <div class="section-content">\r\n\r\n            <div class="content-option">\r\n                <span class="option-title">Transparency</span>\r\n                <label class="switch-checkbox">\r\n                    <input id="_menuTransparency" type="checkbox"></input>\r\n                    <span></span>\r\n                </label>\r\n            </div>\r\n\r\n        </div>\r\n    </div> --\x3e\r\n\r\n</div>';

    const Devtool_default = '<div class="menu-page" data-id="6">\r\n    <div class="page-title">Devtool</div>\r\n    <p class="page-description">Test Colean Client and report about bugs!</p>\r\n\r\n\r\n    \x3c!-- myPlayer --\x3e\r\n    <div class="section">\r\n        <h2 class="section-title">myPlayer</h2>\r\n\r\n        <div class="section-content">\r\n\r\n            <div class="content-option">\r\n                <span class="option-title">Display player angle</span>\r\n                <label class="switch-checkbox">\r\n                    <input id="_displayPlayerAngle" type="checkbox"></input>\r\n                    <span></span>\r\n                </label>\r\n            </div>\r\n\r\n        </div>\r\n    </div>\r\n\r\n\r\n    \x3c!-- Hitboxes --\x3e\r\n    <div class="section">\r\n        <h2 class="section-title">Hitboxes</h2>\r\n\r\n        <div class="section-content">\r\n\r\n            <div class="content-option">\r\n                <span class="option-title">Weapon hitbox</span>\r\n                <label class="switch-checkbox">\r\n                    <input id="_weaponHitbox" type="checkbox"></input>\r\n                    <span></span>\r\n                </label>\r\n            </div>\r\n\r\n            <div class="content-option">\r\n                <span class="option-title">Collision hitbox</span>\r\n                <label class="switch-checkbox">\r\n                    <input id="_collisionHitbox" type="checkbox"></input>\r\n                    <span></span>\r\n                </label>\r\n            </div>\r\n\r\n            <div class="content-option">\r\n                <span class="option-title">Placement hitbox</span>\r\n                <label class="switch-checkbox">\r\n                    <input id="_placementHitbox" type="checkbox"></input>\r\n                    <span></span>\r\n                </label>\r\n            </div>\r\n\r\n            <div class="content-option">\r\n                <span class="option-title">Possible placement</span>\r\n                <label class="switch-checkbox">\r\n                    <input id="_possiblePlacement" type="checkbox"></input>\r\n                    <span></span>\r\n                </label>\r\n            </div>\r\n\r\n        </div>\r\n    </div>\r\n\r\n    \x3c!-- Statistics --\x3e\r\n    <div class="section">\r\n        <h2 class="section-title">Statistics</h2>\r\n\r\n        <div class="section-content small-section">\r\n\r\n            <div class="content-option left-flex text">\r\n                <span class="option-title">Total kills: </span>\r\n                <span id="_totalKills" class="text-value">0</span>\r\n            </div>\r\n\r\n            <div class="content-option left-flex text">\r\n                <span class="option-title">Global kills with bots: </span>\r\n                <span id="_globalKills" class="text-value">0</span>\r\n            </div>\r\n\r\n            <div class="content-option left-flex text">\r\n                <span class="option-title">Deaths: </span>\r\n                <span id="_deaths" class="text-value">0</span>\r\n            </div>\r\n\r\n            <div class="content-option left-flex text">\r\n                <span class="option-title">Autosync: </span>\r\n                <span id="_autoSyncTimes" class="text-value">0</span>\r\n            </div>\r\n\r\n            <div class="content-option left-flex text">\r\n                <span class="option-title">Velocity tick: </span>\r\n                <span id="_velocityTickTimes" class="text-value">0</span>\r\n            </div>\r\n\r\n            <div class="content-option left-flex text">\r\n                <span class="option-title">SSHammer: </span>\r\n                <span id="_spikeSyncHammerTimes" class="text-value">0</span>\r\n            </div>\r\n\r\n            <div class="content-option left-flex text">\r\n                <span class="option-title">Spike sync: </span>\r\n                <span id="_spikeSyncTimes" class="text-value">0</span>\r\n            </div>\r\n\r\n            <div class="content-option left-flex text">\r\n                <span class="option-title">Spike tick: </span>\r\n                <span id="_spikeTickTimes" class="text-value">0</span>\r\n            </div>\r\n\r\n            <div class="content-option left-flex text">\r\n                <span class="option-title">KBTrap: </span>\r\n                <span id="_knockbackTickTrapTimes" class="text-value">0</span>\r\n            </div>\r\n\r\n            <div class="content-option left-flex text">\r\n                <span class="option-title">KBHammer: </span>\r\n                <span id="_knockbackTickHammerTimes" class="text-value">0</span>\r\n            </div>\r\n\r\n            <div class="content-option left-flex text">\r\n                <span class="option-title">KB Reg: </span>\r\n                <span id="_knockbackTickTimes" class="text-value">0</span>\r\n            </div>\r\n\r\n            <div class="content-option left-flex text">\r\n                <span class="option-title">Author: </span>\r\n                <span id="author" class="text-value">ItzYakudza</span>\r\n            </div>\r\n\r\n        </div>\r\n    </div>\r\n\r\n</div>';

    const Bots_default = "<div class=\"menu-page\" data-id=\"5\"><div class=\"page-title\">Bots</div><style>\n    .bot-dropdown{width:270px;position:relative;z-index:5;margin:16px 0;font-size:16px;font-family:\"Noto Sans\",sans-serif}\n    .bot-dropdown button{width:100%;height:42px;display:flex;align-items:center;justify-content:space-between;padding:0 14px;border:1px solid #30343a;border-radius:5px;background:#123752;color:#d8e6f2;font:inherit;font-weight:800;cursor:pointer}\n    .bot-dropdown button:hover{background:#1b527a;color:#f0f7ff}.bot-dropdown button:disabled{opacity:.45;cursor:not-allowed}\n    .bot-dropdown-options{position:absolute;top:46px;left:0;width:100%;padding:4px;background:#081726;border:1px solid #2d6b96;border-radius:5px;box-shadow:0 8px 18px #0006;box-sizing:border-box}\n    .bot-dropdown-options[hidden],#local-bot-panel[hidden],#cross-server-panel[hidden]{display:none!important}\n    .bot-dropdown-arrow{color:#888c92}#cross-server-panel{font-family:\"Noto Sans\",sans-serif;color:#a0a5aa;font-weight:800}\n    .cross-server-row{display:flex;align-items:center;gap:16px;padding:6px 12px;border-radius:5px}.cross-server-row.current-server{background:#30343a66}\n    .cross-server-name{font-size:24px;flex:1;overflow-wrap:anywhere}.cross-server-detail{font-size:16px;text-align:right}\n    .cross-add-bot{flex-shrink:0}.cross-add-bot:disabled{opacity:.45;cursor:not-allowed}.cross-server-actions{display:flex;gap:10px;flex-wrap:wrap;justify-content:center;margin:12px 0}\n    #cross-server-list-status,#cross-server-status,#cross-batch-status{padding:8px 12px;font-size:14px}#cross-connected-bots{padding:0 12px}\n    #cross-server-panel .option-button:disabled{opacity:.45;cursor:not-allowed}\n    @media(max-width:720px){.cross-server-row{flex-wrap:wrap;gap:8px}.cross-server-detail{font-size:14px}.cross-server-name{font-size:20px}}\n  </style>\n  <div id=\"bot-family-switcher\" class=\"bot-dropdown\" data-current-menu=\"bots\">\n    <button id=\"bot-family-trigger\" type=\"button\" aria-expanded=\"false\" aria-controls=\"bot-family-options\"><span id=\"bot-family-label\">Bot Menu</span><span id=\"bot-family-arrow\" class=\"bot-dropdown-arrow\" aria-hidden=\"true\">▼</span></button>\n    <div id=\"bot-family-options\" class=\"bot-dropdown-options\" hidden><button id=\"bot-family-option\" type=\"button\">Cross-Server Menu</button></div>\n  </div><div id=\"local-bot-panel\"><style>#connected-bot-list,#bot-status{font-family:\"Noto Sans\",sans-serif;font-weight:800;font-size:1.1rem;color:#c0c5ca}.loadout-switch{position:relative;display:inline-block;width:70px;height:28px;flex-shrink:0}.loadout-switch input{position:absolute;opacity:0;width:100%;height:100%;margin:0;cursor:pointer}.loadout-switch>span{display:block;width:100%;height:100%;border-radius:5px;background:#30343a;pointer-events:none}.loadout-switch>span:after{content:\"\";position:absolute;top:4px;left:5px;width:20px;height:20px;border-radius:3px;background:#646970;transition:left .12s,background .12s}.loadout-switch input:checked+span:after{left:45px;background:#989da3}.loadout-switch input:focus-visible+span{outline:2px solid #b5b5b5}</style><div class=\"section\"><div class=\"section-title\">Manual Aim</div><div class=\"section-content\"><div class=\"content-option\"><span class=\"option-title\">Manual Aim</span><label class=\"switch-checkbox\"><input type=\"checkbox\" id=\"_manualAim\"><span></span></label></div><p>Use 1 / 2 or click a weapon in the action bar to select it. Left click aims at your cursor. Applies to you and your bots; all combat features remain active and temporarily control weapons and aim during their attacks.</p></div></div><div class=\"section\"><div class=\"section-title\">Bot Nickname</div><div class=\"section-content\"><div class=\"content-option\"><span class=\"option-title\">Nickname</span><input id=\"_botNickname\" class=\"input\" type=\"text\" maxlength=\"15\" placeholder=\"random\"></div><div class=\"content-option\"><span class=\"option-title\">Add bot number</span><label class=\"switch-checkbox\"><input id=\"_botNickNumber\" type=\"checkbox\"><span></span></label></div><p>Applies to bots added after the change. Empty nickname means a random bot name. The game limits names to 15 characters.</p></div></div><div class=\"section\"><div class=\"section-title\">Choose weapons for bots</div><div class=\"section-content\" style=\"display:block\"><p>Primary weapon</p><div style=\"display:grid;grid-template-columns:repeat(auto-fit,minmax(240px,1fr));gap:10px\"><label class=\"content-option\" style=\"display:flex;align-items:center;justify-content:space-between;gap:12px;padding:8px;cursor:pointer\"><span class=\"option-title\">Stick</span><span class=\"loadout-switch\"><input type=\"radio\" aria-label=\"Stick\" name=\"bot-primary\" value=\"8\"><span></span></span></label><label class=\"content-option\" style=\"display:flex;align-items:center;justify-content:space-between;gap:12px;padding:8px;cursor:pointer\"><span class=\"option-title\">Sword</span><span class=\"loadout-switch\"><input type=\"radio\" aria-label=\"Sword\" name=\"bot-primary\" value=\"3\"><span></span></span></label><label class=\"content-option\" style=\"display:flex;align-items:center;justify-content:space-between;gap:12px;padding:8px;cursor:pointer\"><span class=\"option-title\">Bat</span><span class=\"loadout-switch\"><input type=\"radio\" aria-label=\"Bat\" name=\"bot-primary\" value=\"6\"><span></span></span></label><label class=\"content-option\" style=\"display:flex;align-items:center;justify-content:space-between;gap:12px;padding:8px;cursor:pointer\"><span class=\"option-title\">Spear</span><span class=\"loadout-switch\"><input type=\"radio\" aria-label=\"Spear\" name=\"bot-primary\" value=\"5\"><span></span></span></label><label class=\"content-option\" style=\"display:flex;align-items:center;justify-content:space-between;gap:12px;padding:8px;cursor:pointer\"><span class=\"option-title\">Daggers</span><span class=\"loadout-switch\"><input type=\"radio\" aria-label=\"Daggers\" name=\"bot-primary\" value=\"7\"><span></span></span></label><label class=\"content-option\" style=\"display:flex;align-items:center;justify-content:space-between;gap:12px;padding:8px;cursor:pointer\"><span class=\"option-title\">Axe</span><span class=\"loadout-switch\"><input type=\"radio\" aria-label=\"Axe\" name=\"bot-primary\" value=\"1\"><span></span></span></label></div><p>Secondary weapon</p><div style=\"display:grid;grid-template-columns:repeat(auto-fit,minmax(240px,1fr));gap:10px\"><label class=\"content-option\" style=\"display:flex;align-items:center;justify-content:space-between;gap:12px;padding:8px;cursor:pointer\"><span class=\"option-title\">Repeater</span><span class=\"loadout-switch\"><input type=\"radio\" aria-label=\"Repeater\" name=\"bot-secondary\" value=\"13\"><span></span></span></label><label class=\"content-option\" style=\"display:flex;align-items:center;justify-content:space-between;gap:12px;padding:8px;cursor:pointer\"><span class=\"option-title\">Musket</span><span class=\"loadout-switch\"><input type=\"radio\" aria-label=\"Musket\" name=\"bot-secondary\" value=\"15\"><span></span></span></label><label class=\"content-option\" style=\"display:flex;align-items:center;justify-content:space-between;gap:12px;padding:8px;cursor:pointer\"><span class=\"option-title\">Shield</span><span class=\"loadout-switch\"><input type=\"radio\" aria-label=\"Shield\" name=\"bot-secondary\" value=\"11\"><span></span></span></label><label class=\"content-option\" style=\"display:flex;align-items:center;justify-content:space-between;gap:12px;padding:8px;cursor:pointer\"><span class=\"option-title\">Hammer</span><span class=\"loadout-switch\"><input type=\"radio\" aria-label=\"Hammer\" name=\"bot-secondary\" value=\"10\"><span></span></span></label></div><p>One choice per group. Choices apply at the next available upgrade or after respawning. Bots always choose Cookie, Greater Spikes and Platform, and continue their selected weapon upgrades.</p></div></div><div class=\"section\"><div class=\"section-content\"><div id=\"connected-bot-list\" style=\"width:100%\"></div><div class=\"content-option centered\"><button id=\"add-bot\" class=\"option-button\">Add Bot</button><button id=\"remove-bots\" class=\"option-button\">Remove Bots</button></div><div id=\"bot-status\" role=\"status\"></div></div></div></div><div id=\"cross-server-panel\" hidden>\n    <div class=\"section\"><div class=\"section-title\">Servers</div>\n    <div id=\"cross-server-type-switcher\" class=\"bot-dropdown\" data-server-type=\"normal\">\n      <button id=\"cross-server-type-trigger\" type=\"button\" aria-expanded=\"false\" aria-controls=\"cross-server-type-options\"><span id=\"cross-server-type-label\">Normal Servers</span><span id=\"cross-server-type-arrow\" class=\"bot-dropdown-arrow\" aria-hidden=\"true\">▼</span></button>\n      <div id=\"cross-server-type-options\" class=\"bot-dropdown-options\" hidden><button id=\"cross-server-type-option\" type=\"button\" data-server-type=\"sandbox\">Sandbox Servers</button></div>\n    </div>\n    <div class=\"cross-server-actions\"><button id=\"cross-add-all\" class=\"option-button\" type=\"button\" title=\"Add one idle bot to every available normal and sandbox server\">Add Bot to All Servers</button><button id=\"cross-stop-adding\" class=\"option-button\" type=\"button\" disabled>Stop Adding</button><button id=\"cross-refresh\" class=\"option-button\" type=\"button\">Refresh Servers</button></div><div id=\"cross-batch-status\" role=\"status\"></div>\n    <div id=\"cross-server-list\"></div><div id=\"cross-server-list-status\" role=\"status\"></div></div>\n    <div class=\"section\"><div class=\"section-title\">Cross-Server Bots</div><div id=\"cross-connected-bots\"></div>\n    <div class=\"cross-server-actions\"><button id=\"cross-remove-bots\" class=\"option-button\" type=\"button\">Remove Cross-Server Bots</button></div><div id=\"cross-server-status\" role=\"status\"></div></div>\n  </div></div>";

    const styles_default = "@import \"https://fonts.googleapis.com/css2?family=Noto+Sans:wght@400;600;800&display=swap\";\r\n\r\n* {\r\n    user-select: none;\r\n}\r\n\r\n/* Slightly lighter + bluish dark backgrounds */\r\nheader {\r\n    display: flex;\r\n    justify-content: space-between;\r\n    align-items: center;\r\n    height: 45px;\r\n    background: #16181c; /* was #121212 → lighter + hint of blue */\r\n    padding: 10px;\r\n    border-radius: 6px;\r\n}\r\n\r\nheader .page-title {\r\n    font-size: 2.3em;\r\n}\r\n\r\nheader #credits {\r\n    display: flex;\r\n    justify-content: space-between;\r\n    gap: 10px;\r\n    height: 45px;\r\n}\r\n\r\nheader #credits p {\r\n    margin-top: auto;\r\n}\r\n\r\nheader #logo {\r\n    display: block;\r\n    width: auto;\r\n    height: 100%;\r\n    scale: 1.2;\r\n}\r\n\r\nheader #close-button {\r\n    display: block;\r\n    fill: #b5b5b5; /* slightly lighter */\r\n    cursor: pointer;\r\n    width: auto;\r\n    height: 100%;\r\n    transition: fill 200ms;\r\n}\r\n\r\nheader #close-button:hover {\r\n    fill: #f0f0f0;\r\n}\r\n\r\n@keyframes ripple {\r\n    from {\r\n        opacity: 1;\r\n        transform: scale(0);\r\n    }\r\n    to {\r\n        opacity: 0;\r\n        transform: scale(0.7);\r\n    }\r\n}\r\n\r\n#navbar-container {\r\n    display: flex;\r\n    flex-direction: column;\r\n    background: #16181c; /* was #121212 */\r\n    padding: 10px;\r\n    border-radius: 6px;\r\n    row-gap: 3px;\r\n}\r\n\r\n#navbar-container .open-menu {\r\n    position: relative;\r\n    width: 8.5em;\r\n    height: 3.2em;\r\n    background: #101215; /* was #0d0d0d → slightly lighter + blue */\r\n    font-weight: 800;\r\n    font-size: 1.3em;\r\n    overflow: hidden;\r\n    transition: all 400ms;\r\n    display: flex;\r\n    justify-content: left;\r\n    align-items: center;\r\n    padding: 0px 25px;\r\n    border-radius: 3px;\r\n    border: 1px solid rgba(200, 210, 220, 0.08); /* cooler gray border */\r\n}\r\n\r\n.open-menu > span {\r\n    display: flex;\r\n    justify-content: left;\r\n    align-items: center;\r\n    gap: 10px;\r\n    transition: all 300ms;\r\n    pointer-events: none;\r\n}\r\n\r\n.open-menu:hover {\r\n    background: #3a3d42; /* was #3d3d3d → cooler tone */\r\n}\r\n\r\n.open-menu:hover span {\r\n    transform: translateY(-2px);\r\n}\r\n\r\n.open-menu.active {\r\n    background: #3a3d42;\r\n    pointer-events: none;\r\n}\r\n\r\n#navbar-container .open-menu.bottom-align {\r\n    margin-top: auto;\r\n}\r\n\r\n#navbar-container .open-menu .ripple {\r\n    position: absolute;\r\n    z-index: 5;\r\n    background: rgba(200, 215, 230, 0.4); /* slightly bluish white ripple */\r\n    top: 0;\r\n    left: 0;\r\n    border-radius: 50%;\r\n    opacity: 0;\r\n    animation: ripple 800ms;\r\n    pointer-events: none;\r\n}\r\n\r\n/* Animations unchanged */\r\n@keyframes toclose {\r\n    from {\r\n        opacity: 1;\r\n        transform: scale(1);\r\n    }\r\n    to {\r\n        opacity: 0;\r\n        transform: scale(0);\r\n    }\r\n}\r\n\r\n@keyframes toopen {\r\n    from {\r\n        opacity: 0;\r\n        transform: scale(0);\r\n    }\r\n    to {\r\n        opacity: 1;\r\n        transform: scale(1);\r\n    }\r\n}\r\n\r\n@keyframes appear {\r\n    from {\r\n        opacity: 0;\r\n    }\r\n    to {\r\n        opacity: 1;\r\n    }\r\n}\r\n\r\n#page-container {\r\n    width: 100%;\r\n    height: 100%;\r\n    overflow-y: scroll;\r\n}\r\n\r\n.menu-page {\r\n    background: #16181c; /* consistent background */\r\n    padding: 10px;\r\n    border-radius: 6px;\r\n    display: none;\r\n}\r\n\r\n.menu-page.opened {\r\n    display: block;\r\n}\r\n\r\n.menu-page .page-title {\r\n    font-size: 2.8em;\r\n}\r\n\r\n.menu-page .section {\r\n    margin-top: 20px;\r\n    background: #101215; /* was #0d0d0d */\r\n    padding: 15px;\r\n    border-radius: 6px;\r\n}\r\n\r\n.menu-page .section .section-title {\r\n    font-weight: 800;\r\n    font-size: 1.8em;\r\n    color: #a0a5aa; /* slightly lighter + bluish gray */\r\n    margin-bottom: 10px;\r\n}\r\n\r\n.section-content {\r\n    display: flex;\r\n    flex-direction: column;\r\n    gap: 5px;\r\n}\r\n\r\n.small-section {\r\n    gap: 0px;\r\n    font-size: 0.85rem;\r\n}\r\n\r\n.menu-page .section .section-content.split {\r\n    display: flex;\r\n    justify-content: space-between;\r\n    flex-direction: row;\r\n    column-gap: 30px;\r\n}\r\n\r\n.menu-page .section .section-content .content-split {\r\n    width: 50%;\r\n    display: flex;\r\n    flex-direction: column;\r\n    row-gap: 10px;\r\n}\r\n\r\n.menu-page .section .section-content .content-option {\r\n    display: flex;\r\n    justify-content: space-between;\r\n    align-items: center;\r\n    min-height: 40px;\r\n    padding: 3px 10px;\r\n    transition: background 300ms;\r\n    border-radius: 8px;\r\n}\r\n\r\n.content-option:hover {\r\n    background: rgba(60, 65, 75, 0.25); /* cooler hover bg */\r\n}\r\n\r\n.option-description {\r\n    position: absolute;\r\n    z-index: 99;\r\n    visibility: hidden;\r\n    background: #282b30; /* was #2a2a2a → bluish dark */\r\n    padding: 8px;\r\n    border-radius: 6px;\r\n    font-weight: 600;\r\n    pointer-events: none;\r\n    max-width: 300px;\r\n}\r\n\r\n.description-show {\r\n    visibility: visible;\r\n}\r\n\r\n.menu-page .section .content-option.centered {\r\n    display: flex;\r\n    justify-content: center;\r\n}\r\n\r\n.menu-page .section .section-content .content-option .option-title {\r\n    font-weight: 800;\r\n    font-size: 1.4em;\r\n    color: #60656b; /* was #585858 → lighter + cooler */\r\n    transition: color 300ms;\r\n}\r\n\r\n.menu-page .section .section-content .content-option .option-content {\r\n    display: flex;\r\n    justify-content: center;\r\n    align-items: center;\r\n    column-gap: 10px;\r\n}\r\n\r\n.menu-page .section .section-content .content-option .disconnect-button {\r\n    width: 30px;\r\n    height: 30px;\r\n    cursor: pointer;\r\n    fill: rgba(55, 93, 130,, 0.5); /* slightly softened */\r\n    transition: fill 300ms;\r\n}\r\n\r\n.menu-page .section .section-content .content-option:hover .option-title {\r\n    color: #888c92; /* was #7e7d7d */\r\n}\r\n\r\n.menu-page .section .section-content .content-option:hover .disconnect-button {\r\n    fill: #36608a;\r\n}\r\n\r\n.menu-page .section .section-content .content-option:hover .disconnect-button:hover {\r\n    fill: #3a6998;\r\n}\r\n\r\n.menu-page .section .section-content .text {\r\n    display: flex;\r\n    justify-content: left;\r\n    gap: 10px;\r\n}\r\n\r\n.menu-page .section .section-content .text .text-value {\r\n    color: #8e8888; /* slightly lighter */\r\n    font-weight: 800;\r\n    font-size: 1.5em;\r\n}\r\n\r\n.simplified {\r\n    font-weight: 600 !important;\r\n    font-size: 1.2em !important;\r\n    word-spacing: 2px;\r\n}\r\n\r\n.highlight {\r\n    color: #c0c5ca; /* cooler highlight */\r\n}\r\n\r\n.menu-page .section .option-button {\r\n    /* width: 117px;\r\n    height: 45px; */\r\n    background: #2e3136; /* was #303030 → bluish dark */\r\n    border: 5px solid #24272b; /* was #262626 */\r\n    padding: 10px 30px;\r\n    border-radius: 6px;\r\n    font-weight: 800;\r\n    font-size: 1.1em;\r\n    color: #888c92;\r\n    transition: background 300ms, border-color 300ms;\r\n}\r\n\r\n\r\n#bot-container {\r\n    margin: 10px 0;\r\n}\r\n\r\n.menu-page .section .option-button:hover {\r\n    background: #34383d;\r\n    border-color: #282b30;\r\n}\r\n\r\n.menu-page .section .section-content .hotkeyInput {\r\n    width: 90px;\r\n    height: 40px;\r\n    background: #2e3136;\r\n    border: 5px solid #24272b;\r\n    border-radius: 6px;\r\n    font-weight: 800;\r\n    font-size: 1.1em;\r\n    color: #888c92;\r\n    display: flex;\r\n    justify-content: center;\r\n    align-items: center;\r\n    transition: background 300ms, border-color 300ms, color 300ms;\r\n}\r\n\r\n.menu-page .section .section-content .hotkeyInput:hover {\r\n    background: #34383d;\r\n    border-color: #282b30;\r\n}\r\n\r\n.menu-page .section .section-content .hotkeyInput.active {\r\n    background: #3a3e44;\r\n    border-color: #2c3035;\r\n}\r\n\r\n.red {\r\n    background: #385f85!important;\r\n    border-color: #2f4f6f!important;\r\n    color: #789cc0!important;\r\n}\r\n\r\n.red:hover {\r\n    background: #487db2!important;\r\n    border-color: #315375!important;\r\n}\r\n\r\n.red.active {\r\n    background: #406e9c!important;\r\n    border-color: #315375!important;\r\n}\r\n\r\n.menu-page .section .section-content .switch-checkbox {\r\n    position: relative;\r\n    width: 90px;\r\n    height: 34px;\r\n}\r\n\r\n.menu-page .section .section-content .switch-checkbox input {\r\n    width: 0;\r\n    height: 0;\r\n    opacity: 0;\r\n}\r\n\r\n.input {\r\n    outline: 3px solid transparent;\r\n    border: none;\r\n    text-align: center;\r\n    padding: 0;\r\n    margin: 0;\r\n    width: 225px;\r\n    height: 30px;\r\n    background: #2e3136;\r\n    box-shadow: 0px -6px 0px 0px #24272b inset;\r\n    border-radius: 6px;\r\n    font-weight: 800;\r\n    font-size: 1.1em;\r\n    color: #888c92;\r\n    display: flex;\r\n    justify-content: center;\r\n    align-items: center;\r\n    transition: background 300ms, border-color 300ms, color 300ms, outline 300ms;\r\n}\r\n\r\n.input:focus {\r\n    outline: 3px solid #757a80; /* cooler focus ring */\r\n}\r\n\r\n.menu-page .section .section-content .switch-checkbox input:checked + span {\r\n    background: #3a3e44;\r\n    box-shadow: 0px -17px 0px 0px #2f3338 inset;\r\n}\r\n\r\n.menu-page .section .section-content .switch-checkbox input:checked + span:before {\r\n    transform: translateX(50px) scale(0.6);\r\n    background: #888c92;\r\n}\r\n\r\n.menu-page .section .section-content .switch-checkbox span {\r\n    position: absolute;\r\n    cursor: pointer;\r\n    top: 0;\r\n    left: 0;\r\n    bottom: 0;\r\n    right: 0;\r\n    width: 100%;\r\n    height: 100%;\r\n    display: flex;\r\n    align-items: center;\r\n    background: #2e3136;\r\n    border-radius: 6px;\r\n    box-shadow: 0px -17px 0px 0px #282b30 inset;\r\n}\r\n\r\n.menu-page .section .section-content .switch-checkbox span:before {\r\n    position: absolute;\r\n    content: \"\";\r\n    transform: scale(0.6);\r\n    transition: transform 300ms;\r\n    width: 40px;\r\n    height: 40px;\r\n    border-radius: 6px;\r\n    background: #60656b;\r\n}\r\n\r\n.menu-page .section .section-content input[id][type=\"color\"] {\r\n    width: 60px;\r\n    height: 33.3333333333px;\r\n    outline: none;\r\n    border: none;\r\n    padding: 3px;\r\n    margin: 0;\r\n    background: #2e3136;\r\n    border-radius: 6px;\r\n    cursor: pointer;\r\n}\r\n\r\n.menu-page .section .section-content .reset-color {\r\n    background: var(--data-color);\r\n    width: 10px;\r\n    height: 10px;\r\n    border-radius: 50%;\r\n}\r\n\r\n.menu-page .section .section-content .slider {\r\n    position: relative;\r\n    display: flex;\r\n    align-items: center;\r\n    justify-content: space-between;\r\n    gap: 10px;\r\n}\r\n\r\n.menu-page .section .section-content .slider input {\r\n    appearance: none;\r\n    outline: none;\r\n    cursor: pointer;\r\n    padding: 0;\r\n    margin: 0;\r\n    border: none;\r\n    width: 144px;\r\n    height: 30px;\r\n    background: #3a3e44;\r\n    box-shadow: 0px -15px 0px 0px #2f3338 inset;\r\n    border-radius: 6px;\r\n}\r\n\r\n.menu-page .section .section-content .slider input::-webkit-slider-thumb {\r\n    -webkit-appearance: none;\r\n    transform: scale(0.7);\r\n    width: 30px;\r\n    height: 30px;\r\n    background: #888c92;\r\n    border-radius: 6px;\r\n}\r\n\r\n.menu-page .section .section-content .slider .slider-value {\r\n    color: #60656b;\r\n    font-weight: 800;\r\n    font-size: 1.4em;\r\n    opacity: 0.4;\r\n}\r\n\r\n.left-flex {\r\n    display: flex;\r\n    justify-content: left !important;\r\n    gap: 10px;\r\n}\r\n\r\nhtml,\r\nbody {\r\n    margin: 0;\r\n    padding: 0;\r\n    scrollbar-width: thin;\r\n    scrollbar-track-color: #2e3136;\r\n    scrollbar-face-color: #24272b;\r\n    overflow: hidden;\r\n}\r\n\r\n* {\r\n    font-family: \"Noto Sans\", sans-serif;\r\n    color: #f2f4f6; /* slightly softer white */\r\n}\r\n\r\nh1, .page-title {\r\n    font-weight: 800;\r\n    margin: 0;\r\n}\r\n\r\nh2 {\r\n    margin: 0;\r\n}\r\n\r\np {\r\n    font-weight: 800;\r\n    font-size: 1.1rem;\r\n    margin: 0;\r\n    color: #c0c5ca; /* cooler light gray */\r\n}\r\n\r\nbutton {\r\n    border: none;\r\n    outline: none;\r\n    cursor: pointer;\r\n}\r\n\r\n#menu-container {\r\n    position: absolute;\r\n    top: 50%;\r\n    left: 50%;\r\n    transform: translate(-50%, -50%);\r\n    width: 1280px;\r\n    height: 720px;\r\n    display: flex;\r\n    justify-content: center;\r\n    align-items: center;\r\n}\r\n\r\n#menu-container.transparent #menu-wrapper {\r\n    background: rgba(10, 12, 16, 0.6); /* bluish transparent */\r\n    backdrop-filter: blur(3px);\r\n    box-shadow: 0 0 15px rgba(0, 10, 20, 0.4); /* subtle blue shadow */\r\n}\r\n\r\n#menu-container.transparent header,\r\n#menu-container.transparent .menu-page,\r\n#menu-container.transparent #navbar-container {\r\n    background: rgba(22, 24, 28, 0.59); /* matching transparent bg */\r\n}\r\n\r\n#menu-container.transparent .section {\r\n    background: rgba(16, 18, 21, 0.46);\r\n}\r\n\r\n#menu-container.transparent .open-menu {\r\n    background: rgba(16, 18, 21, 0.46);\r\n}\r\n\r\n#menu-container.transparent .open-menu:hover,\r\n#menu-container.transparent .open-menu.active {\r\n    background: rgba(58, 61, 66, 0.60);\r\n}\r\n\r\n#menu-wrapper {\r\n    position: relative;\r\n    display: flex;\r\n    flex-direction: column;\r\n    row-gap: 5px;\r\n    width: 85%;\r\n    height: 85%;\r\n    padding: 10px;\r\n    border-radius: 6px;\r\n    background: #0a0c10; /* bluish black */\r\n}\r\n\r\n#menu-wrapper.toclose {\r\n    animation: 150ms ease-in toclose forwards;\r\n}\r\n\r\n#menu-wrapper.toopen {\r\n    animation: 150ms ease-in toopen forwards;\r\n}\r\n\r\nmain {\r\n    display: flex;\r\n    column-gap: 10px;\r\n    width: 100%;\r\n    height: calc(100% - 75px);\r\n}\r\n\r\n::-webkit-scrollbar {\r\n    width: 12px;\r\n}\r\n\r\n::-webkit-scrollbar-track {\r\n    background: #2e3136;\r\n    border-radius: 6px;\r\n}\r\n\r\n::-webkit-scrollbar-thumb {\r\n    background: #24272b;\r\n    border-radius: 6px;\r\n}\r\n\r\n.icon {\r\n    width: 50px;\r\n    height: 50px;\r\n}\r\n\r\n.small-icon {\r\n    width: 22px;\r\n    height: 22px;\r\n}";

    const Game_default = '#iframe-container {\r\n    position: absolute;\r\n    top: 0;\r\n    left: 0;\r\n    bottom: 0;\r\n    right: 0;\r\n    width: 100%;\r\n    height: 100%;\r\n    border: none;\r\n    outline: none;\r\n    z-index: 10;\r\n}\r\n\r\n#promoImgHolder,\r\n.menuHeader,\r\n.menuText,\r\n#guideCard,\r\n#gameName,\r\n#pingDisplay,\r\n#partyButton,\r\n#onetrust-consent-sdk,\r\n.adMenuCard,\r\n#topInfoHolder > div:not([id]):not([class]),\r\n#touch-controls-fullscreen,\r\n#altcha,\r\n#joinPartyButton {\r\n    display: none!important;\r\n}\r\n\r\n.menuCard {\r\n    box-shadow: none;\r\n}\r\n\r\n#setupCard {\r\n    display: flex;\r\n    flex-direction: column;\r\n    gap: 12px;\r\n    background: #6d6d6d77;\r\n    max-height: auto;\r\n    width: 280px;\r\n}\r\n\r\n#setupCard > * {\r\n    margin: 0!important;\r\n}\r\n\r\n#linksContainer2 {\r\n    background: #6d6d6d77;\r\n}\r\n\r\n#bottomContainer {\r\n    bottom: 20px;\r\n}\r\n\r\n#topInfoHolder {\r\n    display: flex;\r\n    flex-direction: column;\r\n    justify-content: right;\r\n    align-items: flex-end;\r\n    gap: 10px;\r\n}\r\n\r\n#killCounter, #totalKillCounter {\r\n    position: static;\r\n    margin: 0;\r\n    background-image: url(../img/icons/skull.png);\r\n}\r\n\r\n.actionBarItem {\r\n    position: relative;\r\n}\r\n\r\n.itemCounter {\r\n    position: absolute;\r\n    top: 3px;\r\n    right: 3px;\r\n    font-size: 0.95em;\r\n    color: white;\r\n    text-shadow: #3d3f42 2px 0px 0px, #3d3f42 1.75517px 0.958851px 0px, #3d3f42 1.0806px 1.68294px 0px, #3d3f42 0.141474px 1.99499px 0px, #3d3f42 -0.832294px 1.81859px 0px, #3d3f42 -1.60229px 1.19694px 0px, #3d3f42 -1.97998px 0.28224px 0px, #3d3f42 -1.87291px -0.701566px 0px, #3d3f42 -1.30729px -1.5136px 0px, #3d3f42 -0.421592px -1.95506px 0px, #3d3f42 0.567324px -1.91785px 0px, #3d3f42 1.41734px -1.41108px 0px, #3d3f42 1.92034px -0.558831px 0px;\r\n}\r\n\r\n.itemCounter.hidden {\r\n    display: none;\r\n}\r\n\r\n#coleanStats {\r\n    position: absolute;\r\n    color: rgb(221, 221, 221);\r\n    font: 13px "Hammersmith One";\r\n    bottom: 210px;\r\n    left: 20px;\r\n\r\n    display: flex;\r\n    flex-direction: column;\r\n    gap: 5px;\r\n}\r\n\r\n.hidden {\r\n    display: none!important;\r\n}\r\n\r\n#chatLog {\r\n    position: absolute;\r\n    top: 65px;\r\n    left: 10px;\r\n\r\n    width: 380px;\r\n    height: 180px;\r\n\r\n    background: rgba(10, 12, 16, 0.6);\r\n    padding: 10px;\r\n    color: #f2f4f6;\r\n    border-radius: 6px;\r\n\r\n    display: flex;\r\n    flex-direction: column;\r\n}\r\n\r\n#chatLogHeader {\r\n    font-size: 1.8rem;\r\n    margin: 0 0 5px 0;\r\n    flex-shrink: 0;\r\n}\r\n\r\n#messageContainer {\r\n    flex: 1;\r\n    overflow-y: auto;\r\n    overflow-x: hidden;\r\n}\r\n\r\n#messageContainer::-webkit-scrollbar {\r\n    width: 6px;\r\n}\r\n\r\n#messageContainer::-webkit-scrollbar-track {\r\n    background: #4c4f55;\r\n    border-radius: 6px;\r\n}\r\n\r\n#messageContainer::-webkit-scrollbar-thumb {\r\n    background: #303338;\r\n    border-radius: 6px;\r\n}\r\n\r\n.logMessage {\r\n    display: flex;\r\n    gap: 8px;\r\n    align-items: flex-start;\r\n}\r\n\r\n.logMessage span {\r\n    word-break: break-word;\r\n    overflow-wrap: anywhere;\r\n}\r\n\r\n.logMessage .darken {\r\n    white-space: nowrap;\r\n    flex-shrink: 0;\r\n}\r\n\r\n.logMessage .log,\r\n.logMessage .warn,\r\n.logMessage .error {\r\n    flex: 1;\r\n    min-width: 0;\r\n}\r\n\r\n.warn {\r\n    color: rgb(251, 251, 112);\r\n}\r\n\r\n.error {\r\n    color: rgb(217, 103, 103);\r\n}';

    const Store_default = "#storeContainer {\r\n    display: flex;\r\n    flex-direction: column;\r\n    gap: 10px;\r\n    max-width: 400px;\r\n    width: 100%;\r\n\r\n    position: absolute;\r\n    top: 50%;\r\n    left: 50%;\r\n    transform: translate(-50%, -50%) scale(0.9);\r\n}\r\n\r\n#toggleStoreType {\r\n    display: flex;\r\n    justify-content: center;\r\n    align-items: center;\r\n    padding: 10px;\r\n    background-color: rgba(0, 0, 0, 0.15);\r\n    color: #fff;\r\n    border-radius: 4px;\r\n    cursor: pointer;\r\n    font-size: 20px;\r\n    pointer-events: all;\r\n}\r\n\r\n#itemHolder {\r\n    background-color: rgba(0, 0, 0, 0.15);\r\n    max-height: 200px;\r\n    height: 100%;\r\n    padding: 10px;\r\n    overflow-y: scroll;\r\n    border-radius: 4px;\r\n    pointer-events: all;\r\n    scrollbar-width: none;\r\n}\r\n\r\n#itemHolder::-webkit-scrollbar {\r\n    display: none;\r\n    width: 0;\r\n    height: 0;\r\n    background: transparent;\r\n}\r\n\r\n.storeItemContainer {\r\n    display: flex;\r\n    align-items: center;\r\n    gap: 10px;\r\n    padding: 5px;\r\n    height: 50px;\r\n    box-sizing: border-box;\r\n    overflow: hidden;\r\n}\r\n\r\n.storeHat {\r\n    display: flex;\r\n    justify-content: center;\r\n    align-items: center;\r\n    width: 45px;\r\n    height: 45px;\r\n    margin-top: -5px;\r\n    pointer-events: none;\r\n}\r\n\r\n.storeItemName {\r\n    color: #fff;\r\n    font-size: 20px;\r\n}\r\n\r\n.equipButton {\r\n    margin-left: auto;\r\n    color: #80eefc;\r\n    cursor: pointer;\r\n    font-size: 35px;\r\n}";

    const Hats = {
        [0]: {
            index: 0,
            id: 0,
            name: "Unequip",
            dontSell: true,
            price: 0,
            scale: 0,
            description: "None"
        },
        [45]: {
            index: 1,
            id: 45,
            name: "Shame!",
            dontSell: true,
            price: 0,
            scale: 120,
            description: "hacks are for losers"
        },
        [51]: {
            index: 2,
            id: 51,
            name: "Moo Cap",
            price: 0,
            scale: 120,
            description: "coolest mooer around"
        },
        [50]: {
            index: 3,
            id: 50,
            name: "Apple Cap",
            price: 0,
            scale: 120,
            description: "apple farms remembers"
        },
        [28]: {
            index: 4,
            id: 28,
            name: "Moo Head",
            price: 0,
            scale: 120,
            description: "no effect"
        },
        [29]: {
            index: 5,
            id: 29,
            name: "Pig Head",
            price: 0,
            scale: 120,
            description: "no effect"
        },
        [30]: {
            index: 6,
            id: 30,
            name: "Fluff Head",
            price: 0,
            scale: 120,
            description: "no effect"
        },
        [36]: {
            index: 7,
            id: 36,
            name: "Pandou Head",
            price: 0,
            scale: 120,
            description: "no effect"
        },
        [37]: {
            index: 8,
            id: 37,
            name: "Bear Head",
            price: 0,
            scale: 120,
            description: "no effect"
        },
        [38]: {
            index: 9,
            id: 38,
            name: "Monkey Head",
            price: 0,
            scale: 120,
            description: "no effect"
        },
        [44]: {
            index: 10,
            id: 44,
            name: "Polar Head",
            price: 0,
            scale: 120,
            description: "no effect"
        },
        [35]: {
            index: 11,
            id: 35,
            name: "Fez Hat",
            price: 0,
            scale: 120,
            description: "no effect"
        },
        [42]: {
            index: 12,
            id: 42,
            name: "Enigma Hat",
            price: 0,
            scale: 120,
            description: "join the enigma army"
        },
        [43]: {
            index: 13,
            id: 43,
            name: "Blitz Hat",
            price: 0,
            scale: 120,
            description: "hey everybody i'm blitz"
        },
        [49]: {
            index: 14,
            id: 49,
            name: "Bob XIII Hat",
            price: 0,
            scale: 120,
            description: "like and subscribe"
        },
        [57]: {
            index: 15,
            id: 57,
            name: "Pumpkin",
            price: 50,
            scale: 120,
            description: "Spooooky"
        },
        [8]: {
            index: 16,
            id: 8,
            name: "Bummle Hat",
            price: 100,
            scale: 120,
            description: "no effect"
        },
        [2]: {
            index: 17,
            id: 2,
            name: "Straw Hat",
            price: 500,
            scale: 120,
            description: "no effect"
        },
        [15]: {
            index: 18,
            id: 15,
            name: "Winter Cap",
            price: 600,
            scale: 120,
            description: "allows you to move at normal speed in snow",
            coldM: 1
        },
        [5]: {
            index: 19,
            id: 5,
            name: "Cowboy Hat",
            price: 1e3,
            scale: 120,
            description: "no effect"
        },
        [4]: {
            index: 20,
            id: 4,
            name: "Ranger Hat",
            price: 2e3,
            scale: 120,
            description: "no effect"
        },
        [18]: {
            index: 21,
            id: 18,
            name: "Explorer Hat",
            price: 2e3,
            scale: 120,
            description: "no effect"
        },
        [31]: {
            index: 22,
            id: 31,
            name: "Flipper Hat",
            price: 2500,
            scale: 120,
            description: "have more control while in water",
            watrImm: true
        },
        [1]: {
            index: 23,
            id: 1,
            name: "Marksman Cap",
            price: 3e3,
            scale: 120,
            description: "increases arrow speed and range",
            aMlt: 1.3
        },
        [10]: {
            index: 24,
            id: 10,
            name: "Bush Gear",
            price: 3e3,
            scale: 160,
            description: "allows you to disguise yourself as a bush"
        },
        [48]: {
            index: 25,
            id: 48,
            name: "Halo",
            price: 3e3,
            scale: 120,
            description: "no effect"
        },
        [6]: {
            index: 26,
            id: 6,
            name: "Soldier Helmet",
            price: 4e3,
            scale: 120,
            description: "reduces damage taken but slows movement",
            spdMult: .94,
            dmgMult: .75
        },
        [23]: {
            index: 27,
            id: 23,
            name: "Anti Venom Gear",
            price: 4e3,
            scale: 120,
            description: "makes you immune to poison",
            poisonRes: 1
        },
        [13]: {
            index: 28,
            id: 13,
            name: "Medic Gear",
            price: 5e3,
            scale: 110,
            description: "slowly regenerates health over time",
            healthRegen: 3
        },
        [9]: {
            index: 29,
            id: 9,
            name: "Miners Helmet",
            price: 5e3,
            scale: 120,
            description: "earn 1 extra gold per resource",
            extraGold: 1
        },
        [32]: {
            index: 30,
            id: 32,
            name: "Musketeer Hat",
            price: 5e3,
            scale: 120,
            description: "reduces cost of projectiles",
            projCost: .5
        },
        [7]: {
            index: 31,
            id: 7,
            name: "Bull Helmet",
            price: 6e3,
            scale: 120,
            description: "increases damage done but drains health",
            healthRegen: -5,
            dmgMultO: 1.5,
            spdMult: .96
        },
        [22]: {
            index: 32,
            id: 22,
            name: "Emp Helmet",
            price: 6e3,
            scale: 120,
            description: "turrets won't attack but you move slower",
            antiTurret: 1,
            spdMult: .7
        },
        [12]: {
            index: 33,
            id: 12,
            name: "Booster Hat",
            price: 6e3,
            scale: 120,
            description: "increases your movement speed",
            spdMult: 1.16
        },
        [26]: {
            index: 34,
            id: 26,
            name: "Barbarian Armor",
            price: 8e3,
            scale: 120,
            description: "knocks back enemies that attack you",
            dmgK: .6
        },
        [21]: {
            index: 35,
            id: 21,
            name: "Plague Mask",
            price: 1e4,
            scale: 120,
            description: "melee attacks deal poison damage",
            poisonDmg: 5,
            poisonTime: 6
        },
        [46]: {
            index: 36,
            id: 46,
            name: "Bull Mask",
            price: 1e4,
            scale: 120,
            description: "bulls won't target you unless you attack them",
            bullRepel: 1
        },
        [14]: {
            index: 37,
            id: 14,
            name: "Windmill Hat",
            topSprite: true,
            price: 1e4,
            scale: 120,
            description: "generates points while worn",
            pps: 1.5
        },
        [11]: {
            index: 38,
            id: 11,
            name: "Spike Gear",
            topSprite: true,
            price: 1e4,
            scale: 120,
            description: "deal damage to players that damage you",
            dmg: .45
        },
        [53]: {
            index: 39,
            id: 53,
            name: "Turret Gear",
            topSprite: true,
            price: 1e4,
            scale: 120,
            description: "you become a walking turret",
            turret: {
                projectile: 1,
                range: 700,
                rate: 2500
            },
            spdMult: .7,
            knockback: 60
        },
        [20]: {
            index: 40,
            id: 20,
            name: "Samurai Armor",
            price: 12e3,
            scale: 120,
            description: "increased attack speed and fire rate",
            atkSpd: .78
        },
        [58]: {
            index: 41,
            id: 58,
            name: "Dark Knight",
            price: 12e3,
            scale: 120,
            description: "restores health when you deal damage",
            healD: .4
        },
        [27]: {
            index: 42,
            id: 27,
            name: "Scavenger Gear",
            price: 15e3,
            scale: 120,
            description: "earn double points for each kill",
            kScrM: 2
        },
        [40]: {
            index: 43,
            id: 40,
            name: "Tank Gear",
            price: 15e3,
            scale: 120,
            description: "increased damage to buildings but slower movement",
            spdMult: .3,
            bDmg: 3.3
        },
        [52]: {
            index: 44,
            id: 52,
            name: "Thief Gear",
            price: 15e3,
            scale: 120,
            description: "steal half of a players gold when you kill them",
            goldSteal: .5
        },
        [55]: {
            index: 45,
            id: 55,
            name: "Bloodthirster",
            price: 2e4,
            scale: 120,
            description: "Restore Health when dealing damage. And increased damage",
            healD: .25,
            dmgMultO: 1.2
        },
        [56]: {
            index: 46,
            id: 56,
            name: "Assassin Gear",
            price: 2e4,
            scale: 120,
            description: "Go invisible when not moving. Can't eat. Increased speed",
            noEat: true,
            spdMult: 1.1,
            invisTimer: 1e3
        }
    };

    const Accessories = {
        [0]: {
            index: 0,
            id: 0,
            name: "Unequip",
            dontSell: true,
            price: 0,
            scale: 0,
            xOffset: 0,
            description: "None"
        },
        [12]: {
            index: 1,
            id: 12,
            name: "Snowball",
            price: 1e3,
            scale: 105,
            xOffset: 18,
            description: "no effect"
        },
        [9]: {
            index: 2,
            id: 9,
            name: "Tree Cape",
            price: 1e3,
            scale: 90,
            description: "no effect"
        },
        [10]: {
            index: 3,
            id: 10,
            name: "Stone Cape",
            price: 1e3,
            scale: 90,
            description: "no effect"
        },
        [3]: {
            index: 4,
            id: 3,
            name: "Cookie Cape",
            price: 1500,
            scale: 90,
            description: "no effect"
        },
        [8]: {
            index: 5,
            id: 8,
            name: "Cow Cape",
            price: 2e3,
            scale: 90,
            description: "no effect"
        },
        [11]: {
            index: 6,
            id: 11,
            name: "Monkey Tail",
            price: 2e3,
            scale: 97,
            xOffset: 25,
            description: "Super speed but reduced damage",
            spdMult: 1.35,
            dmgMultO: .2
        },
        [17]: {
            index: 7,
            id: 17,
            name: "Apple Basket",
            price: 3e3,
            scale: 80,
            xOffset: 12,
            description: "slowly regenerates health over time",
            healthRegen: 1
        },
        [6]: {
            index: 8,
            id: 6,
            name: "Winter Cape",
            price: 3e3,
            scale: 90,
            description: "no effect"
        },
        [4]: {
            index: 9,
            id: 4,
            name: "Skull Cape",
            price: 4e3,
            scale: 90,
            description: "no effect"
        },
        [5]: {
            index: 10,
            id: 5,
            name: "Dash Cape",
            price: 5e3,
            scale: 90,
            description: "no effect"
        },
        [2]: {
            index: 11,
            id: 2,
            name: "Dragon Cape",
            price: 6e3,
            scale: 90,
            description: "no effect"
        },
        [1]: {
            index: 12,
            id: 1,
            name: "Super Cape",
            price: 8e3,
            scale: 90,
            description: "no effect"
        },
        [7]: {
            index: 13,
            id: 7,
            name: "Troll Cape",
            price: 8e3,
            scale: 90,
            description: "no effect"
        },
        [14]: {
            index: 14,
            id: 14,
            name: "Thorns",
            price: 1e4,
            scale: 115,
            xOffset: 20,
            description: "no effect"
        },
        [15]: {
            index: 15,
            id: 15,
            name: "Blockades",
            price: 1e4,
            scale: 95,
            xOffset: 15,
            description: "no effect"
        },
        [20]: {
            index: 16,
            id: 20,
            name: "Devils Tail",
            price: 1e4,
            scale: 95,
            xOffset: 20,
            description: "no effect"
        },
        [16]: {
            index: 17,
            id: 16,
            name: "Sawblade",
            price: 12e3,
            scale: 90,
            spin: true,
            xOffset: 0,
            description: "deal damage to players that damage you",
            dmg: .15
        },
        [13]: {
            index: 18,
            id: 13,
            name: "Angel Wings",
            price: 15e3,
            scale: 138,
            xOffset: 22,
            description: "slowly regenerates health over time",
            healthRegen: 3
        },
        [19]: {
            index: 19,
            id: 19,
            name: "Shadow Wings",
            price: 15e3,
            scale: 138,
            xOffset: 22,
            description: "increased movement speed",
            spdMult: 1.1
        },
        [18]: {
            index: 20,
            id: 18,
            name: "Blood Wings",
            price: 2e4,
            scale: 178,
            xOffset: 26,
            description: "restores health when you deal damage",
            healD: .2
        },
        [21]: {
            index: 21,
            id: 21,
            name: "Corrupt X Wings",
            price: 2e4,
            scale: 178,
            xOffset: 26,
            description: "deal damage to players that damage you",
            dmg: .25
        }
    };

    const store = [ Hats, Accessories ];

    const DataHandler = new class {
        isWeaponType(type) {
            return type <= 1;
        }
        isItemType(type) {
            return type >= 2;
        }
        getStore(type) {
            return store[type];
        }
        getStoreItem(type, id) {
            switch (type) {
              case 0:
                return Hats[id];

              case 1:
                return Accessories[id];

              default:
                throw Error(`getStoreItem Error: type "${type}" is not defined`);
            }
        }
        getProjectile(id) {
            return Projectiles[this.getWeapon(id).projectile];
        }
        getWeapon(id) {
            return Weapons[id];
        }
        getItem(id) {
            return Items[id];
        }
        isWeapon(id) {
            return this.getWeapon(id) !== void 0;
        }
        isItem(id) {
            return Items[id] !== void 0;
        }
        isPrimary(id) {
            return id != null && this.getWeapon(id).itemType === 0;
        }
        isSecondary(id) {
            return id != null && this.getWeapon(id).itemType === 1;
        }
        isMelee(id) {
            return id != null && "damage" in this.getWeapon(id);
        }
        isAttackable(id) {
            return id != null && "range" in this.getWeapon(id);
        }
        isShootable(id) {
            return id != null && "projectile" in this.getWeapon(id);
        }
        isPlaceable(id) {
            return id !== -1 && "itemGroup" in Items[id];
        }
        isHealable(id) {
            return "restore" in Items[id];
        }
        isDestroyable(id) {
            return "health" in Items[id];
        }
        canMoveOnTop(id) {
            return "ignoreCollision" in Items[id];
        }
    };

    const DataHandler_default = DataHandler;

    class ObjectItem {
        id;
        pos;
        angle;
        scale=0;
        constructor(id, x, y, angle, scale) {
            this.id = id;
            this.pos = {
                current: new Vector_default(x, y)
            };
            this.angle = angle;
            this.scale = scale;
        }
        get hitScale() {
            return this.scale;
        }
    }

    class Resource extends ObjectItem {
        type;
        layer;
        constructor(id, x, y, angle, scale, type) {
            super(id, x, y, angle, scale);
            this.type = type;
            this.layer = type === 0 ? 3 : type === 2 ? 0 : 2;
        }
        formatScale(scaleMult = 1) {
            const reduceScale = this.type === 0 || this.type === 1 ? .6 * scaleMult : 1;
            return this.scale * reduceScale;
        }
        get collisionScale() {
            return this.formatScale();
        }
        get placementScale() {
            return this.formatScale(.6);
        }
        get isCactus() {
            return this.type === 1 && pointInDesert(this.pos.current);
        }
        getDamage() {
            if (this.isCactus) {
                return 35;
            }
            return 0;
        }
        canMoveOnTop() {
            return false;
        }
    }

    class PlayerObject extends ObjectItem {
        type;
        ownerID;
        collisionDivider;
        health;
        tempHealth;
        maxHealth;
        reload=-1;
        maxReload=-1;
        isDestroyable;
        destroyingTick=0;
        canBeDestroyed=false;
        trapActivated=false;
        wasTeammate=false;
        seenPlacement=false;
        layer;
        itemGroup;
        projectile=null;
        constructor(id, x, y, angle, scale, type, ownerID) {
            super(id, x, y, angle, scale);
            this.type = type;
            this.ownerID = ownerID;
            const item = Items[type];
            this.collisionDivider = "colDiv" in item ? item.colDiv : 1;
            this.health = "health" in item ? item.health : 1 / 0;
            this.tempHealth = this.health;
            this.maxHealth = this.health;
            this.isDestroyable = this.maxHealth !== 1 / 0;
            if (item.id === 17) {
                this.reload = Math.ceil(item.shootRate / 111);
                this.maxReload = this.reload;
            }
            this.layer = ItemGroups[item.itemGroup].layer;
            this.itemGroup = item.itemGroup;
        }
        formatScale(placeCollision = false) {
            return this.scale * (placeCollision ? 1 : this.collisionDivider);
        }
        get collisionScale() {
            return this.formatScale();
        }
        get placementScale() {
            const item = Items[this.type];
            if (item.id === 21) {
                return item.blocker;
            }
            return this.scale;
        }
        get isSpike() {
            return this.itemGroup === 2;
        }
        getDamage() {
            if (this.isSpike) {
                const type = this.type;
                return DataHandler_default.getItem(type).damage;
            }
            return 0;
        }
        canMoveOnTop() {
            return "ignoreCollision" in Items[this.type];
        }
    }

    class Entity {
        id=-1;
        pos={
            previous: new Vector_default,
            current: new Vector_default,
            future: new Vector_default
        };
        angle=0;
        scale=0;
        speed=0;
        move_dir=0;
        setFuturePosition() {
            const {previous: previous, current: current, future: future} = this.pos;
            const distance = previous.distance(current);
            this.speed = distance;
            const angle = previous.angle(current);
            this.move_dir = angle;
            future.setVec(current.addDirection(angle, distance));
        }
        get collisionScale() {
            return this.scale;
        }
        get hitScale() {
            return this.scale * 1.8;
        }
        client;
        constructor(client) {
            this.client = client;
        }
        getFuturePosition(speed) {
            const pos = this.pos.current.copy();
            return pos.add(Vector_default.fromAngle(this.move_dir, speed));
        }
        colliding(object, radius) {
            const {previous: a0, current: a1, future: a2} = this.pos;
            const b0 = object.pos.current;
            return a0.distance(b0) <= radius || a1.distance(b0) <= radius || a2.distance(b0) <= radius;
        }
        collidingObject(object, addRadius = 0, checkType = 3) {
            const {previous: a0, current: a1, future: a2} = this.pos;
            const b0 = object.pos.current;
            const radius = this.collisionScale + object.collisionScale + addRadius;
            return !!(checkType & 4) && a0.distance(b0) <= radius || !!(checkType & 2) && a1.distance(b0) <= radius || !!(checkType & 1) && a2.distance(b0) <= radius;
        }
        collidingSimple(entity, range, tempPos = this.pos.current) {
            const pos1 = tempPos;
            const pos2 = entity.pos.current;
            return pos1.distance(pos2) <= range;
        }
        collidingEntity(entity, range, checkBased = false, prev = true) {
            const {previous: a0, current: a1, future: a2} = this.pos;
            const {previous: b0, current: b1, future: b2} = entity.pos;
            if (checkBased) {
                return prev && a0.distance(b0) <= range || a1.distance(b1) <= range || a2.distance(b2) <= range;
            }
            return a0.distance(b0) <= range || a0.distance(b1) <= range || a0.distance(b2) <= range || a1.distance(b0) <= range || a1.distance(b1) <= range || a1.distance(b2) <= range || a2.distance(b0) <= range || a2.distance(b1) <= range || a2.distance(b2) <= range;
        }
        runningAwayFrom(entity, angle) {
            if (angle === null) {
                return false;
            }
            const pos1 = this.pos.current;
            const pos2 = entity.pos.current;
            const angleTo = pos1.angle(pos2);
            if (getAngleDist(angle, angleTo) <= Math.PI / 2) {
                return false;
            }
            return true;
        }
    }

    const Entity_default = Entity;

    class EnemyManager {
        client;
        dangerousEnemies=[];
        _nearestEnemy=[ null, null ];
        secondNearestEnemy=null;
        nearestDangerAnimal=null;
        nearestTrap=null;
        nearestCollider=null;
        secondNearestCollider=null;
        nearestEnemySpikeCollider=null;
        spikeCollider=null;
        enemySpikeCollider=null;
        nearestTurretEntity=null;
        detectedEnemy=false;
        dangerWithoutSoldier=false;
        detectedDangerEnemy=false;
        nearestTrappedEnemy=null;
        previousTrappedEnemy=null;
        nearestPlayerObject=null;
        secondNearestPlayerObject=null;
        nearestObject=null;
        nearestEnemyObject=null;
        secondNearestEnemyObject=null;
        nearestSpike=null;
        nearestKBTrapEnemy=null;
        nearestKBTrap=null;
        willCollideSpike=false;
        pushingOnSpike=false;
        collidingSpike=false;
        nearestSpikePlacerAngle=null;
        prevNearestSpikePlacerAngle=null;
        nearestEnemyToNearestEnemy=null;
        enemyCanPlaceSpike=false;
        possibleToKnockback=false;
        potentialSpikeKnockbackDamage=0;
        potentialSpikeDamage=0;
        potentialDamage=0;
        primaryDamage=0;
        detectedDanger=false;
        reverseInsta=false;
        rangedBowInsta=false;
        toolHammerInsta=false;
        spikeSyncThreat=false;
        velocityTickThreat=false;
        nearestLowEntity=null;
        nearestEnemyPush=null;
        nearestPushSpike=null;
        nearestLowHPObjectPrev=null;
        nearestLowHPObject=null;
        nearestSyncEnemy=null;
        constructor(client) {
            this.client = client;
        }
        preReset() {
            this._nearestEnemy[0] = null;
            this._nearestEnemy[1] = null;
            this.nearestDangerAnimal = null;
            this.nearestLowEntity = null;
        }
        reset() {
            this.nearestEnemyToNearestEnemy = null;
            this.willCollideSpike = false;
            this.pushingOnSpike = false;
            this.collidingSpike = false;
            this.prevNearestSpikePlacerAngle = this.nearestSpikePlacerAngle;
            this.nearestSpikePlacerAngle = null;
            this.dangerousEnemies.length = 0;
            this.nearestTrap = null;
            this.nearestCollider = null;
            this.nearestEnemySpikeCollider = null;
            this.spikeCollider = null;
            this.enemySpikeCollider = null;
            this.nearestTurretEntity = null;
            this.detectedEnemy = false;
            this.dangerWithoutSoldier = false;
            this.detectedDangerEnemy = false;
            this.previousTrappedEnemy = this.nearestTrappedEnemy;
            this.nearestTrappedEnemy = null;
            this.nearestPlayerObject = null;
            this.nearestObject = null;
            this.secondNearestPlayerObject = null;
            this.nearestEnemyObject = null;
            this.secondNearestEnemyObject = null;
            this.nearestSpike = null;
            this.nearestKBTrapEnemy = null;
            this.nearestKBTrap = null;
            this.enemyCanPlaceSpike = false;
            this.possibleToKnockback = false;
            this.velocityTickThreat = false;
            this.potentialSpikeKnockbackDamage = 0;
            this.potentialSpikeDamage = 0;
            this.potentialDamage = 0;
            this.detectedDanger = false;
            this.reverseInsta = false;
            this.rangedBowInsta = false;
            this.toolHammerInsta = false;
            this.spikeSyncThreat = false;
            this.nearestEnemyPush = null;
            this.nearestPushSpike = null;
            this.nearestLowHPObjectPrev = this.nearestLowHPObject;
            this.nearestLowHPObject = null;
            this.nearestSyncEnemy = null;
            this.primaryDamage = 0;
            this.secondNearestEnemy = null;
        }
        get wasTrappedEnemy() {
            const enemy = this.previousTrappedEnemy;
            if (enemy !== null && this.nearestTrappedEnemy === null) {
                return enemy;
            }
            return null;
        }
        get nearestPlaceSpikeAngle() {
            const prevAngle = this.prevNearestSpikePlacerAngle;
            const currAngle = this.nearestSpikePlacerAngle;
            if (prevAngle === null && currAngle !== null) {
                return currAngle;
            }
            return null;
        }
        get nearestEnemy() {
            return this._nearestEnemy[0];
        }
        get nearestAnimal() {
            return this._nearestEnemy[1];
        }
        get canSpikeSync() {
            return this.nearestPlaceSpikeAngle !== null && this.client.ObjectManager.isDestroyedObject();
        }
        isNear(enemy, nearest, owner = this.client.myPlayer) {
            if (nearest === null || enemy === nearest) {
                return true;
            }
            const a0 = owner.pos.current;
            const distance1 = a0.distanceDefault(enemy.pos.current);
            const distance2 = a0.distanceDefault(nearest.pos.current);
            return distance1 < distance2;
        }
        get nearestEntity() {
            const target1 = this.nearestEnemy;
            const target2 = this.nearestAnimal;
            if (target1 === null) {
                return target2;
            }
            return this.isNear(target1, target2) ? target1 : target2;
        }
        instaThreat() {
            return this.velocityTickThreat || this.reverseInsta || this.rangedBowInsta || this.toolHammerInsta || this.primaryDamage + this.potentialSpikeKnockbackDamage >= 100;
        }
        shouldIgnoreModule() {
            return this.instaThreat() || this.detectedDangerEnemy || this.spikeSyncThreat;
        }
        weaponDamageThreat() {
            const {ProjectileManager: ProjectileManager, myPlayer: myPlayer} = this.client;
            return this.shouldIgnoreModule() || ProjectileManager.totalDamage >= myPlayer.currentHealth;
        }
        nearestEnemyInRangeOf(range, target) {
            const enemy = target || this.nearestEnemy;
            return enemy !== null && this.client.myPlayer.collidingEntity(enemy, range);
        }
        handleDanger(enemy) {
            const danger = enemy.canPossiblyInstakill();
            enemy.prevDanger = enemy.danger;
            enemy.danger = danger;
            if (enemy.canPlaceSpikeObject) {
                this.potentialSpikeDamage = Math.max(this.potentialSpikeDamage, enemy.spikeDamage);
            }
            this.potentialDamage += enemy.potentialDamage;
            this.primaryDamage = Math.max(enemy.primaryDamage, this.primaryDamage);
            if (enemy.prevDanger !== enemy.danger && enemy.danger >= 2) {
                this.detectedDanger = true;
            }
            if (enemy.velocityTicking) {
                this.velocityTickThreat = true;
            }
            if (enemy.reverseInsta) {
                this.reverseInsta = true;
            }
            if (enemy.toolHammerInsta) {
                this.toolHammerInsta = true;
            }
            if (enemy.rangedBowInsta) {
                this.rangedBowInsta = true;
            }
            if (enemy.spikeSyncThreat) {
                this.spikeSyncThreat = true;
            }
        }
        checkCollision(target, isOwner = false) {
            target.isTrapped = false;
            target.trappedInPrev = target.trappedIn;
            target.trappedIn = null;
            const {ObjectManager: ObjectManager, PlayerManager: PlayerManager, myPlayer: myPlayer, _ModuleHandler: ModuleHandler} = this.client;
            const pos1 = myPlayer.pos.current;
            const pos2 = target.pos.current;
            const distanceToTarget = pos1.distance(pos2);
            const angleToTarget = pos1.angle(pos2);
            ObjectManager.grid2D.query(target.pos.current.x, target.pos.current.y, 3, id => {
                const object = ObjectManager.objects.get(id);
                const pos3 = object.pos.current;
                const isPlayerObject = object instanceof PlayerObject;
                const isCactus = !isPlayerObject && object.isCactus;
                const isSpike = isPlayerObject && object.itemGroup === 2;
                const isEnemyObject = !isPlayerObject || PlayerManager.isEnemyByID(object.ownerID, target);
                const isEnemyObjectToMyPlayer = !isPlayerObject || PlayerManager.isEnemyByID(object.ownerID, myPlayer);
                const collidingObject = target.collidingObject(object, 1);
                const collidingCurrent = target.collidingObject(object, 1, 1);
                if (isPlayerObject && !isEnemyObject) {
                    object.wasTeammate = true;
                }
                if (isPlayerObject && isEnemyObject && object.type === 15) {
                    if (collidingObject) {
                        if (!isOwner) {
                            if (this.isNear(target, this.nearestTrappedEnemy)) {
                                this.nearestTrappedEnemy = target;
                            }
                            if (!isEnemyObjectToMyPlayer && this.isNear(target, this.nearestEnemyPush)) {
                                this.nearestEnemyPush = target;
                            }
                        }
                        target.isTrapped = true;
                        if (target.hatID === 40) {
                            target.usesTank = true;
                        }
                        if (this.isNear(object, target.trappedIn)) {
                            target.trappedIn = object;
                        }
                        if (isOwner && this.isNear(object, this.nearestTrap)) {
                            this.nearestTrap = object;
                        }
                    }
                    if (collidingCurrent || !object.seenPlacement && !object.wasTeammate) {
                        object.trapActivated = true;
                    }
                }
                if (isOwner && isPlayerObject && object.type === 22 && collidingCurrent) {
                    myPlayer.teleportPos.setVec(pos1);
                    myPlayer.teleported = true;
                }
                if (isPlayerObject && object.isDestroyable) {
                    if (object.destroyingTick !== ModuleHandler.tickCount) {
                        object.canBeDestroyed = false;
                        object.tempHealth = object.health;
                    }
                    const damage = target.getMaxBuildingDamage(object, true);
                    const canSee = !isEnemyObject || object.type !== 15 || isEnemyObject && object.type === 15 && object.trapActivated;
                    if (damage !== null && canSee) {
                        object.destroyingTick = ModuleHandler.tickCount;
                        object.tempHealth -= damage;
                        if (object.tempHealth <= 0) {
                            object.canBeDestroyed = true;
                        }
                    }
                }
                if (isOwner) {
                    if (isEnemyObject && isPlayerObject && object.isDestroyable) {
                        if (object.type === 15 || object.type === 16 || object.type === 22 || object.itemGroup === 2) {
                            if (this.isNear(object, this.nearestEnemyObject)) {
                                this.secondNearestEnemyObject = this.nearestEnemyObject;
                                this.nearestEnemyObject = object;
                            }
                            if (object !== this.nearestEnemyObject && this.isNear(object, this.secondNearestEnemyObject)) {
                                this.secondNearestEnemyObject = object;
                            }
                        }
                        if (object.itemGroup === 2 && this.isNear(object, this.nearestSpike)) {
                            this.nearestSpike = object;
                        }
                    }
                    if (this.isNear(object, this.nearestObject)) {
                        this.nearestObject = object;
                    }
                    if (isPlayerObject && object.isDestroyable) {
                        if (this.isNear(object, this.nearestPlayerObject)) {
                            this.secondNearestPlayerObject = this.nearestPlayerObject;
                            this.nearestPlayerObject = object;
                        }
                        if (object !== this.nearestPlayerObject && this.isNear(object, this.secondNearestPlayerObject)) {
                            this.secondNearestPlayerObject = object;
                        }
                    }
                    if (isEnemyObject && (isSpike || isCactus) && target.collidingObject(object, 70)) {
                        this.willCollideSpike = true;
                        if (target.collidingObject(object, 25)) {
                            this.pushingOnSpike = true;
                        }
                    }
                    if (isEnemyObject && (isSpike || isCactus) && target.colliding(object, target.collisionScale + object.collisionScale + 1)) {
                        this.collidingSpike = true;
                        this.potentialSpikeDamage = Math.max(this.potentialSpikeDamage, object.getDamage());
                    }
                    const isAdditional = isPlayerObject && object.type === 16;
                    if (isEnemyObject && (isSpike || isCactus || isAdditional) && target.collidingObject(object, 150)) {
                        if (this.isNear(object, this.nearestCollider)) {
                            this.secondNearestCollider = this.nearestCollider;
                            this.nearestCollider = object;
                        }
                        if (object !== this.nearestCollider && this.isNear(object, this.secondNearestCollider)) {
                            this.secondNearestCollider = object;
                        }
                    }
                } else {
                    const {primary: primary, secondary: secondary} = myPlayer.weapon;
                    if (isPlayerObject && object.isDestroyable && secondary === 10 && primary !== null && primary !== 8) {
                        const damage = myPlayer.getBuildingDamage(secondary, true);
                        const primaryRange = DataHandler_default.getWeapon(primary).range + target.hitScale;
                        const secondaryRange = DataHandler_default.getWeapon(secondary).range + object.hitScale;
                        if (myPlayer.collidingSimple(target, primaryRange) && myPlayer.collidingSimple(object, secondaryRange) && object.health <= damage) {
                            const itemType = 4;
                            const spikeID = myPlayer.getItemByType(itemType);
                            const placeLength = myPlayer.getItemPlaceScale(spikeID);
                            const spikeScale = Items[spikeID].scale;
                            const spikePos = pos1.addDirection(angleToTarget, placeLength);
                            const distance = pos2.distance(spikePos);
                            const range = target.collisionScale + spikeScale;
                            if (distance <= range && this.isNear(object, this.nearestLowHPObject)) {
                                this.nearestLowHPObject = object;
                                this.nearestSyncEnemy = target;
                            }
                        }
                    }
                    if (isEnemyObjectToMyPlayer && (isSpike || isCactus) && !myPlayer.isTrapped) {
                        const KBDistance = target.getActualMaxKnockback(myPlayer);
                        const spikeScale = object.collisionScale + myPlayer.collisionScale;
                        const angleToEnemy = pos2.angle(pos1);
                        const angleToSpike = pos2.angle(pos3);
                        const distanceToSpike1 = pos2.distance(pos3);
                        const offset = Math.asin(2 * spikeScale / (2 * distanceToSpike1));
                        const angleDistance = getAngleDist(angleToEnemy, angleToSpike);
                        const intersecting = angleDistance <= offset;
                        const overlapping = distanceToTarget <= distanceToSpike1;
                        const inRange2 = KBDistance !== 0 && myPlayer.collidingObject(object, KBDistance);
                        if (intersecting && overlapping && inRange2) {
                            this.possibleToKnockback = true;
                            this.potentialSpikeKnockbackDamage = Math.max(this.potentialSpikeKnockbackDamage, object.getDamage());
                        }
                    }
                    if (isEnemyObject && (isSpike || isCactus) && target.collidingObject(object) && this.isNear(target, this.enemySpikeCollider)) {
                        this.enemySpikeCollider = target;
                    }
                    if (isEnemyObject && (isSpike || isCactus) && this.isNear(target, this.nearestEnemySpikeCollider)) {
                        const KBDistance = myPlayer.getActualMaxKnockback(target);
                        const spikeScale = object.collisionScale + target.collisionScale;
                        const angleToEnemy = pos1.angle(pos2);
                        const angleToSpike = pos1.angle(pos3);
                        const distanceToSpike1 = pos1.distance(pos3);
                        const offset = Math.asin(2 * spikeScale / (2 * distanceToSpike1));
                        const angleDistance = getAngleDist(angleToEnemy, angleToSpike);
                        const intersecting = angleDistance <= offset;
                        const overlapping = distanceToTarget <= distanceToSpike1;
                        const inRange2 = KBDistance !== 0 && target.collidingObject(object, KBDistance);
                        if (intersecting && overlapping && inRange2) {
                            if (this.spikeCollider === null) {
                                this.nearestEnemySpikeCollider = target;
                                this.spikeCollider = object;
                            } else {
                                const pos4 = this.spikeCollider.pos.current;
                                const angle1 = pos2.angle(pos3);
                                const angle2 = pos1.angle(pos3);
                                const angle3 = pos2.angle(pos4);
                                const angle4 = pos1.angle(pos4);
                                const angleDist1 = getAngleDist(angle1, angle2);
                                const angleDist2 = getAngleDist(angle3, angle4);
                                if (angleDist1 < angleDist2) {
                                    this.nearestEnemySpikeCollider = target;
                                    this.spikeCollider = object;
                                }
                            }
                        }
                    }
                    if (!target.isTrapped && isEnemyObject && object.type === 15 && this.isNear(target, this.nearestKBTrapEnemy)) {
                        const KBDistance = myPlayer.getActualMaxKnockback(target);
                        const trapScale = object.collisionScale + target.collisionScale;
                        const angleToEnemy = pos1.angle(pos2);
                        const angleToSpike = pos1.angle(pos3);
                        const distanceToTrap1 = pos1.distance(pos3);
                        const offset = Math.asin(2 * trapScale / (2 * distanceToTrap1));
                        const angleDistance = getAngleDist(angleToEnemy, angleToSpike);
                        const intersecting = angleDistance <= offset;
                        const overlapping = distanceToTarget <= distanceToTrap1;
                        const inRange2 = KBDistance !== 0 && target.collidingObject(object, KBDistance);
                        if (intersecting && overlapping && inRange2) {
                            if (this.nearestKBTrap === null) {
                                this.nearestKBTrapEnemy = target;
                                this.nearestKBTrap = object;
                            } else {
                                const pos4 = this.nearestKBTrap.pos.current;
                                const angle1 = pos2.angle(pos3);
                                const angle2 = pos1.angle(pos3);
                                const angle3 = pos2.angle(pos4);
                                const angle4 = pos1.angle(pos4);
                                const angleDist1 = getAngleDist(angle1, angle2);
                                const angleDist2 = getAngleDist(angle3, angle4);
                                if (angleDist1 < angleDist2) {
                                    this.nearestKBTrapEnemy = target;
                                    this.nearestKBTrap = object;
                                }
                            }
                        }
                    }
                }
            });
        }
        handleNearest(type, enemy) {
            const {myPlayer: myPlayer} = this.client;
            const primaryDamage = myPlayer.getMaxWeaponDamage(myPlayer.weapon.primary, false);
            if (primaryDamage >= enemy.currentHealth && this.isNear(enemy, this.nearestLowEntity)) {
                this.nearestLowEntity = enemy;
            }
            if (this.isNear(enemy, this._nearestEnemy[type])) {
                if (type === 0) {
                    const nearest = this._nearestEnemy[type];
                    this.secondNearestEnemy = nearest;
                }
                this._nearestEnemy[type] = enemy;
                if (enemy.canUseTurret && this.client.myPlayer.collidingSimple(enemy, 700)) {
                    this.nearestTurretEntity = enemy;
                }
            }
        }
        handleNearestDangerAnimal(animal) {
            const {myPlayer: myPlayer} = this.client;
            if (!animal.isDanger) {
                return;
            }
            if (!myPlayer.collidingEntity(animal, animal.collisionRange)) {
                return;
            }
            if (!this.isNear(animal, this.nearestDangerAnimal)) {
                return;
            }
            this.nearestDangerAnimal = animal;
        }
        handleAnimal(animal) {
            this.handleNearest(1, animal);
            this.handleNearestDangerAnimal(animal);
        }
        attemptSpikePlacement() {
            const {_ModuleHandler: ModuleHandler} = this.client;
            const placementAngles = this.nearestSpikePlacerAngle;
            if (placementAngles === null) {
                return;
            }
            const itemType = 4;
            for (const angle of placementAngles) {
                ModuleHandler.place(itemType, angle);
            }
            ModuleHandler.placedOnce = true;
            ModuleHandler.placeAngles[0] = itemType;
            ModuleHandler.placeAngles[1] = placementAngles;
        }
        handleEnemies(enemies) {
            this.reset();
            const {myPlayer: myPlayer, ObjectManager: ObjectManager, PlayerManager: PlayerManager} = this.client;
            this.checkCollision(myPlayer, true);
            for (let i = 0, len = enemies.length; i < len; i++) {
                const enemy = enemies[i];
                this.checkCollision(enemy);
                this.handleDanger(enemy);
                this.handleNearest(0, enemy);
            }
            if (myPlayer.isBullTickTime()) {
                this.potentialDamage += 5;
            }
            this.potentialDamage += this.client.ProjectileManager.totalDamage;
            const actualSpikeDamage = Math.max(this.potentialSpikeDamage, this.potentialSpikeKnockbackDamage);
            this.potentialSpikeDamage = actualSpikeDamage;
            const potentialDamage = this.potentialDamage + actualSpikeDamage;
            const soldierDefense = Hats[6].dmgMult;
            const soldierMult = myPlayer.hatID === 6 ? soldierDefense : 1;
            if (potentialDamage * soldierDefense >= myPlayer.currentHealth) {
                this.detectedDangerEnemy = true;
            } else if (potentialDamage * soldierMult >= myPlayer.currentHealth) {
                this.detectedEnemy = true;
            }
            if (potentialDamage >= myPlayer.currentHealth) {
                this.dangerWithoutSoldier = true;
            }
            const nearest = this.nearestEnemy;
            if (nearest !== null) {
                const pos1 = myPlayer.pos.current;
                const pos2 = nearest.pos.current;
                const angleToEnemy = pos1.angle(pos2);
                const itemType = 4;
                const spikeID = myPlayer.getItemByType(itemType);
                const placeLength = myPlayer.getItemPlaceScale(spikeID);
                const angles = ObjectManager.getBestPlacementAngles({
                    position: pos1,
                    id: spikeID,
                    targetAngle: angleToEnemy,
                    ignoreID: null,
                    preplace: false,
                    reduce: false,
                    fill: false
                });
                const spikeScale = Items[spikeID].scale;
                const possibleAngles = angles.filter(angle => {
                    const spikePos = pos1.addDirection(angle, placeLength);
                    const distance = pos2.distance(spikePos);
                    const range = nearest.collisionScale + spikeScale;
                    return distance <= range;
                });
                if (possibleAngles.length !== 0) {
                    this.nearestSpikePlacerAngle = possibleAngles;
                }
                if (Settings_default._autoSync) {
                    for (let i = 0; i < PlayerManager.players.length; i++) {
                        const player = PlayerManager.players[i];
                        if (myPlayer.isMyPlayerByID(player.id)) {
                            continue;
                        }
                        if (PlayerManager.isEnemyByID(nearest.id, player) && this.isNear(player, this.nearestEnemyToNearestEnemy, nearest)) {
                            this.nearestEnemyToNearestEnemy = player;
                        }
                    }
                }
            }
            const nearestEnemyPush = this.nearestEnemyPush;
            if (nearestEnemyPush !== null && myPlayer.trappedIn === null) {
                const trappedIn = nearestEnemyPush.trappedIn;
                const pos0 = trappedIn.pos.current;
                ObjectManager.grid2D.query(pos0.x, pos0.y, 2, id => {
                    const object = ObjectManager.objects.get(id);
                    if (object === trappedIn) {
                        return;
                    }
                    const isPlayerObject = object instanceof PlayerObject;
                    const isCactus = !isPlayerObject && object.isCactus;
                    const isSpike = isPlayerObject && object.itemGroup === 2;
                    isPlayerObject && object.type;
                    const isEnemyObject = !isPlayerObject || PlayerManager.isEnemyByID(object.ownerID, nearestEnemyPush);
                    if (isEnemyObject && (isCactus || isSpike) && this.isNear(object, this.nearestPushSpike, nearestEnemyPush)) {
                        const pos1 = object.pos.current;
                        const distance = pos0.distance(pos1);
                        const range = object.collisionScale + trappedIn.collisionScale + nearestEnemyPush.collisionScale * 2;
                        if (distance <= range) {
                            this.nearestPushSpike = object;
                        }
                    }
                });
            }
            if (this.client.isOwner) {
                GameUI_default.updateSpikeDamage(actualSpikeDamage);
                GameUI_default.updatePotentialDamage(`${this.potentialDamage}, ${this.primaryDamage}`);
                GameUI_default.updateDangerState(`${this.detectedDangerEnemy}, ${this.detectedEnemy}, ${this.dangerWithoutSoldier}, ${this.rangedBowInsta}`);
                GameUI_default.updateCollideSpike(this.collidingSpike);
            }
        }
    }

    const EnemyManager_default = EnemyManager;

    class LeaderboardManager {
        client;
        list=new Set;
        constructor(client) {
            this.client = client;
        }
        updatePlayer(id, nickname, gold) {
            const owner = this.client.PlayerManager.playerData.get(id) || this.client.PlayerManager.createPlayer({
                id: id,
                nickname: nickname
            });
            this.list.add(owner);
        }
        update(data) {
            this.list.clear();
            for (let i = 0; i < data.length; i += 3) {
                const id = data[i + 0];
                const nickname = data[i + 1];
                const gold = data[i + 2];
                this.updatePlayer(id, nickname, gold);
            }
        }
    }

    const LeaderboardManager_default = LeaderboardManager;

    const HatPredictor = new class {
        transitions=new Map;
        train(history) {
            this.transitions.clear();
            for (let i = 0; i < history.length - 1; i++) {
                const currentHat = history[i];
                const nextHat = history[i + 1];
                if (!this.transitions.has(currentHat)) {
                    this.transitions.set(currentHat, new Map);
                }
                const nextMap = this.transitions.get(currentHat);
                nextMap.set(nextHat, (nextMap.get(nextHat) || 0) + 1);
            }
        }
        predict(currentHat) {
            if (!this.transitions.has(currentHat)) {
                return null;
            }
            const nextMap = this.transitions.get(currentHat);
            let maxCount = 0;
            let predictedHat = null;
            for (const [hat, count] of nextMap) {
                if (count > maxCount) {
                    maxCount = count;
                    predictedHat = hat;
                }
            }
            return predictedHat;
        }
    };

    const HatPredictor_default = HatPredictor;

    const scale_value = window.grbtp;

    delete window.grbtp;

    class Player extends Entity_default {
        currentItem=-1;
        clanName=null;
        isLeader=false;
        prevNickname=null;
        nickname=null;
        skinID=0;
        scale=scale_value;
        storeData=[ 0, 0 ];
        hatID=0;
        prevHat=0;
        accessoryID=0;
        usesTurret=false;
        previousHealth=100;
        currentHealth=100;
        tempHealth=100;
        maxHealth=Math.LN1;
        primaryReloadTickCount=0;
        nextDamageTick=0;
        globalInventory={};
        weapon={};
        oldWeapon=[ 0, null ];
        variant={};
        reload=[ {}, {}, {} ];
        objects=new Set;
        newlyCreated=true;
        usingBoost=false;
        isTrapped=false;
        usesTank=false;
        trappedIn=null;
        trappedInPrev=null;
        isFullyUpgraded=false;
        potentialDamage=0;
        primaryDamage=0;
        spikeDamage=0;
        dangerList=[];
        danger=0;
        prevDanger=0;
        hatHistory=[];
        futureHat=0;
        shameActive=false;
        shameTimer=0;
        shameCount=0;
        receivedDamage=null;
        bullTick=0;
        poisonCount=0;
        isDmgOverTime=false;
        tickCount=0;
        damageTick=0;
        canPlaceSpikePrev=false;
        canPlaceSpike=false;
        velocityTicking=false;
        reverseInsta=false;
        toolHammerInsta=false;
        rangedBowInsta=false;
        spikeSyncThreat=false;
        onPlatform=false;
        tickDamage=100;
        stackedDamage=0;
        damages=[];
        prevSeenBefore=false;
        seenBefore=false;
        isPlayer=true;
        lastAttacked=0;
        constructor(client) {
            super(client);
        }
        justAppeared() {
            return !this.prevSeenBefore && this.seenBefore;
        }
        wasTrapped() {
            return this.trappedIn === null && this.trappedInPrev !== null;
        }
        addFound(projectile) {
            projectile.ownerClient = this;
            this.client.ProjectileManager.foundProjectile(projectile);
        }
        resetReload() {
            const {primary: primary, secondary: secondary} = this.weapon;
            const primarySpeed = this.getWeaponSpeed(primary);
            const secondarySpeed = this.getWeaponSpeed(secondary);
            const reload = this.reload;
            reload[0].previous = primarySpeed;
            reload[0].current = primarySpeed;
            reload[0].max = primarySpeed;
            reload[1].previous = secondarySpeed;
            reload[1].current = secondarySpeed;
            reload[1].max = secondarySpeed;
            reload[2].previous = 23;
            reload[2].current = 23;
            reload[2].max = 23;
            this.shameCount = 0;
        }
        resetGlobalInventory() {
            this.globalInventory[0] = null;
            this.globalInventory[1] = null;
            this.globalInventory[2] = null;
            this.globalInventory[3] = null;
            this.globalInventory[4] = null;
            this.globalInventory[5] = null;
            this.globalInventory[6] = null;
            this.globalInventory[7] = null;
            this.globalInventory[8] = null;
            this.globalInventory[9] = null;
        }
        init() {
            this.weapon.current = 0;
            this.weapon.oldCurrent = 0;
            this.weapon.primary = null;
            this.weapon.secondary = null;
            this.oldWeapon[0] = null;
            this.oldWeapon[1] = null;
            this.variant.current = 0;
            this.variant.primary = 0;
            this.variant.secondary = 0;
            this.resetReload();
            this.resetGlobalInventory();
            this.newlyCreated = true;
            this.usingBoost = false;
            this.isFullyUpgraded = false;
        }
        get canUseTurret() {
            return this.hatID !== 22;
        }
        get canPlaceSpikeObject() {
            return !this.canPlaceSpikePrev && this.canPlaceSpike || this.speed >= 10 && this.canPlaceSpike;
        }
        isBullTickTime(adjust = 0) {
            return (this.tickCount - this.bullTick - adjust) % 9 === 0;
        }
        update(id, x, y, angle, currentItem, currentWeapon, weaponVariant, clanName, isLeader, hatID, accessoryID, hasSkull, onPlatform) {
            this.prevSeenBefore = this.seenBefore;
            this.seenBefore = true;
            if (this.justAppeared()) {
                this.resetReload();
            }
            this.tickCount += 1;
            this.id = id;
            this.pos.previous.setVec(this.pos.current);
            this.pos.current._setXY(x, y);
            this.setFuturePosition();
            this.angle = angle;
            this.currentItem = currentItem;
            this.weapon.oldCurrent = this.weapon.current;
            const weaponType = DataHandler_default.getWeapon(this.weapon.current).itemType;
            this.oldWeapon[weaponType] = this.weapon.current;
            this.weapon.current = currentWeapon;
            this.variant.current = weaponVariant;
            this.clanName = clanName;
            this.isLeader = !!isLeader;
            this.onPlatform = !!onPlatform;
            this.prevHat = this.hatID;
            this.hatID = hatID;
            if (this.prevHat === 7 && hatID === 53) {
                this.usesTurret = true;
            }
            this.hatHistory.push(hatID);
            if (this.hatHistory.length > 4) {
                this.hatHistory.shift();
            }
            this.futureHat = null;
            if (this.usesTurret && hatID === 7) {
                this.futureHat = 53;
            }
            this.accessoryID = accessoryID;
            this.storeData[0] = hatID;
            this.storeData[1] = accessoryID;
            this.newlyCreated = false;
            this.potentialDamage = 0;
            this.primaryDamage = 0;
            this.spikeDamage = 0;
            this.canPlaceSpikePrev = this.canPlaceSpike;
            this.canPlaceSpike = false;
            this.velocityTicking = false;
            this.reverseInsta = false;
            this.toolHammerInsta = false;
            this.rangedBowInsta = false;
            this.spikeSyncThreat = false;
            this.predictItems();
            this.predictWeapons();
            this.updateReloads();
            this.isDmgOverTime = false;
            if (this.hatID === 45 && !this.shameActive) {
                this.shameActive = true;
                this.shameTimer = 0;
                this.shameCount = 8;
            }
            const {PlayerManager: PlayerManager, myPlayer: myPlayer} = this.client;
            this.shameTimer += PlayerManager.step;
            if (this.shameTimer >= 3e4 && this.shameActive) {
                this.shameActive = false;
                this.shameTimer = 0;
                this.shameCount = 0;
            }
            if (this.isBullTickTime()) {
                if (this.shameCount > 0) {
                    this.futureHat = 7;
                }
                this.poisonCount = Math.max(this.poisonCount - 1, 0);
            }
            if (this.futureHat === null) {
                HatPredictor_default.train(this.hatHistory);
                this.futureHat = HatPredictor_default.predict(hatID);
            }
            const reload = this.reload;
            reload[0].previous = reload[0].current;
            reload[1].previous = reload[1].current;
            reload[2].previous = reload[2].current;
        }
        updateHealth(health) {
            this.previousHealth = this.currentHealth;
            this.currentHealth = health;
            this.tempHealth = health;
            if (this.shameActive) {
                return;
            }
            const {myPlayer: myPlayer, PlayerManager: PlayerManager} = this.client;
            const isEnemy = myPlayer.isEnemyByID(this.id);
            const {currentHealth: currentHealth, previousHealth: previousHealth} = this;
            const difference = Math.abs(currentHealth - previousHealth);
            if (this.currentHealth < this.previousHealth) {
                this.receivedDamage = Date.now();
                if (this.damageTick !== this.tickCount + 1) {
                    this.tickDamage = 0;
                    this.stackedDamage = 0;
                    this.damages.length = 0;
                }
                this.tickDamage += difference;
                this.damageTick = this.tickCount + 1;
                if (isEnemy) {
                    PlayerManager.lastEnemyReceivedDamage[0] = this.id;
                    PlayerManager.lastEnemyReceivedDamage[1] = Math.round(difference);
                }
            } else if (this.receivedDamage !== null && (currentHealth > previousHealth || !ServerCapacity.usesHealAcknowledgements(this.client))) {
                const step = Date.now() - this.receivedDamage;
                const locallyFast = this === myPlayer && ServerCapacity.usesHealAcknowledgements(this.client) && this.client._ModuleHandler.staticModules.antiInsta.fastHealDamage === this.receivedDamage;
                this.receivedDamage = null;
                if (step <= 120 || locallyFast) {
                    this.shameCount += 1;
                } else {
                    this.shameCount -= 2;
                }
                this.shameCount = clamp(this.shameCount, 0, 7);
            }
            const diffDmg = difference === 5 || difference === 2 || difference === 4;
            const isDmgOverTime = diffDmg && currentHealth < previousHealth;
            this.isDmgOverTime = isDmgOverTime;
            if (isDmgOverTime) {
                this.bullTick = this.tickCount;
            }
        }
        predictItems() {
            if (this.currentItem === -1) {
                return;
            }
            const item = Items[this.currentItem];
            this.globalInventory[item.itemType] = this.currentItem;
        }
        increaseReload(reload) {
            reload.previous = reload.current;
            reload.current += 1;
            if (reload.current > reload.max) {
                reload.current = reload.max;
            }
        }
        updateMaxReload(reload, weaponID) {
            const speed = this.getWeaponSpeed(weaponID);
            reload.current = speed;
            reload.max = speed;
        }
        resetCurrentReload(reload) {
            reload.current = 0;
        }
        updateTurretReload() {
            const reload = this.reload[2];
            this.increaseReload(reload);
            if (this.hatID !== 53) {
                return;
            }
            const {ProjectileManager: ProjectileManager} = this.client;
            const speed = Projectiles[1].speed;
            const list = ProjectileManager.projectiles.get(speed);
            if (list === void 0) {
                return;
            }
            const current = this.pos.current;
            for (let i = 0; i < list.length; i++) {
                const projectile = list[i];
                const distance = current.distance(projectile.pos.current);
                if (distance < 5) {
                    this.addFound(projectile);
                    this.resetCurrentReload(reload);
                    removeFast(list, i);
                    break;
                }
            }
        }
        updateReloads() {
            this.updateTurretReload();
            if (this.currentItem !== -1) {
                return;
            }
            const weapon = DataHandler_default.getWeapon(this.weapon.current);
            const reload = this.reload[weapon.itemType];
            this.increaseReload(reload);
            if ("projectile" in weapon) {
                const {ProjectileManager: ProjectileManager} = this.client;
                const speedMult = this.getWeaponSpeedMult();
                const type = weapon.projectile;
                const speed = Projectiles[type].speed * speedMult;
                const list = ProjectileManager.projectiles.get(speed);
                if (list === void 0) {
                    return;
                }
                const current = this.pos.current;
                for (let i = 0; i < list.length; i++) {
                    const projectile = list[i];
                    const distance = current.distance(projectile.pos.current);
                    if (distance < 5 && this.angle === projectile.angle) {
                        this.addFound(projectile);
                        this.updateMaxReload(reload, weapon.id);
                        this.resetCurrentReload(reload);
                        removeFast(list, i);
                        break;
                    }
                }
            }
        }
        handleObjectPlacement(object) {
            this.objects.add(object);
            const {myPlayer: myPlayer, ObjectManager: ObjectManager} = this.client;
            const item = Items[object.type];
            if (object.seenPlacement) {
                if (object.type === 17) {
                    ObjectManager.resetTurret(object.id);
                } else if (object.type === 16 && !this.newlyCreated) {
                    this.usingBoost = true;
                }
                this.updateInventory(object.type);
            }
            if (myPlayer.isMyPlayerByID(this.id) && item.itemType === 5) {
                myPlayer.totalGoldAmount += item.pps;
            }
        }
        handleObjectDeletion(object) {
            this.objects.delete(object);
            const {myPlayer: myPlayer} = this.client;
            const item = Items[object.type];
            if (myPlayer.isMyPlayerByID(this.id) && item.itemType === 5) {
                myPlayer.totalGoldAmount -= item.pps;
            }
        }
        updateInventory(type) {
            const item = Items[type];
            const inventoryID = this.globalInventory[item.itemType];
            const shouldUpdate = inventoryID === null || item.age > Items[inventoryID].age;
            if (shouldUpdate) {
                this.globalInventory[item.itemType] = item.id;
            }
        }
        detectFullUpgrade() {
            const inventory = this.globalInventory;
            const primary = inventory[0];
            const secondary = inventory[1];
            const spike = inventory[4];
            if (primary && secondary) {
                if ("isUpgrade" in DataHandler_default.getWeapon(primary) && "isUpgrade" in DataHandler_default.getWeapon(secondary)) {
                    return true;
                }
            }
            return primary && DataHandler_default.getWeapon(primary).age === 8 || secondary && DataHandler_default.getWeapon(secondary).age === 9 || spike && Items[spike].age === 9 || inventory[5] === 12 || inventory[9] === 20;
        }
        predictPrimary(id) {
            if (id === 11) {
                return 4;
            }
            return 5;
        }
        predictSecondary(id) {
            if (id === 0) {
                return null;
            }
            if (id === 2 || id === 4) {
                return 10;
            }
            return 15;
        }
        predictWeapons() {
            const {current: current, oldCurrent: oldCurrent} = this.weapon;
            const weapon = DataHandler_default.getWeapon(current);
            const type = WeaponTypeString[weapon.itemType];
            const reload = this.reload[weapon.itemType];
            const oldWeapon = this.oldWeapon[weapon.itemType];
            const upgradedWeapon = oldWeapon === null || current !== oldWeapon && weapon.itemType === DataHandler_default.getWeapon(oldWeapon).itemType;
            if (reload.max === -1 || upgradedWeapon) {
                this.updateMaxReload(reload, weapon.id);
            }
            this.globalInventory[weapon.itemType] = current;
            this.variant[type] = this.variant.current;
            const currentType = this.weapon[type];
            if (currentType === null || weapon.age > DataHandler_default.getWeapon(currentType).age) {
                this.weapon[type] = current;
            }
            const primary = this.globalInventory[0];
            const secondary = this.globalInventory[1];
            const notPrimaryUpgrade = primary === null || !("isUpgrade" in DataHandler_default.getWeapon(primary));
            const notSecondaryUpgrade = secondary === null || !("isUpgrade" in DataHandler_default.getWeapon(secondary));
            if (DataHandler_default.isSecondary(current) && notPrimaryUpgrade) {
                const predicted = this.predictPrimary(current);
                if (primary === null || DataHandler_default.getWeapon(predicted).upgradeType === DataHandler_default.getWeapon(primary).upgradeType) {
                    this.weapon.primary = predicted;
                }
            } else if (DataHandler_default.isPrimary(current) && notSecondaryUpgrade) {
                const predicted = this.predictSecondary(current);
                if (predicted === null || secondary === null || DataHandler_default.getWeapon(predicted).upgradeType === DataHandler_default.getWeapon(secondary).upgradeType) {
                    this.weapon.secondary = predicted;
                }
            }
            this.isFullyUpgraded = this.detectFullUpgrade();
            if (this.isFullyUpgraded) {
                if (primary !== null) {
                    this.weapon.primary = primary;
                }
                if (secondary !== null) {
                    this.weapon.secondary = secondary;
                }
            }
            if (this.weapon.primary === void 0) {
                throw Error("Primary is 'undefined', value must be at least 'null' or 'number'");
            }
            if (this.weapon.secondary === void 0) {
                throw Error("Secondary is 'undefined', value must be at least 'null' or 'number'");
            }
        }
        getWeaponVariant(id) {
            const type = DataHandler_default.getWeapon(id || 0).itemType;
            const variant = this.variant[WeaponTypeString[type]];
            return {
                current: variant,
                next: Math.min(variant + 1, 3)
            };
        }
        getBuildingDamage(id, isTank = false) {
            const weapon = DataHandler_default.getWeapon(id);
            const variant = WeaponVariants[this.getWeaponVariant(id).current];
            let damage = weapon.damage * variant.val;
            if ("sDmg" in weapon) {
                damage *= weapon.sDmg;
            }
            const hat = Hats[isTank ? 40 : this.hatID];
            if ("bDmg" in hat) {
                damage *= hat.bDmg;
            }
            return damage;
        }
        getMaxBuildingDamage(object, isTank = true) {
            const {primary: primary, secondary: secondary} = this.weapon;
            if (DataHandler_default.isMelee(secondary) && secondary === 10 && this.isReloaded(1, 1)) {
                if (this.collidingSimple(object, DataHandler_default.getWeapon(secondary).range + object.hitScale)) {
                    return this.getBuildingDamage(secondary, isTank);
                }
            }
            if (DataHandler_default.isMelee(primary) && this.isReloaded(0, 1)) {
                if (this.collidingSimple(object, DataHandler_default.getWeapon(primary).range + object.hitScale)) {
                    return this.getBuildingDamage(primary, isTank);
                }
            }
            return null;
        }
        canDealPoison(weaponID) {
            const variant = this.getWeaponVariant(weaponID).current;
            const isRuby = variant === 3;
            const hasPlague = this.hatID === 21;
            return {
                isAble: isRuby || hasPlague,
                count: isRuby ? 5 : hasPlague ? 6 : 0
            };
        }
        getWeaponSpeed(id, hat = this.hatID) {
            if (id === null) {
                return -1;
            }
            const reloadSpeed = hat === 20 ? Hats[hat].atkSpd : 1;
            const speed = DataHandler_default.getWeapon(id).speed * reloadSpeed;
            return Math.ceil(speed / this.client.SocketManager.TICK);
        }
        getWeaponSpeedMult() {
            if (this.hatID === 1) {
                return Hats[this.hatID].aMlt;
            }
            return 1;
        }
        getMaxWeaponRange() {
            const {primary: primary, secondary: secondary} = this.weapon;
            const primaryRange = DataHandler_default.getWeapon(primary).range;
            if (DataHandler_default.isMelee(secondary)) {
                const range = DataHandler_default.getWeapon(secondary).range;
                if (range > primaryRange) {
                    return range;
                }
            }
            return primaryRange;
        }
        getWeaponRange(weaponID) {
            if (weaponID === null) {
                return 0;
            }
            const range = DataHandler_default.getWeapon(weaponID).range;
            if (DataHandler_default.isMelee(weaponID)) {
                return range + this.hitScale;
            }
            return range + this.collisionScale;
        }
        getMaxWeaponDamage(id, lookingShield, addBull = true) {
            if (DataHandler_default.isMelee(id)) {
                const bull = Hats[7];
                const variant = this.getWeaponVariant(id).current;
                let damage = DataHandler_default.getWeapon(id).damage;
                if (addBull) {
                    damage *= bull.dmgMultO;
                }
                damage *= WeaponVariants[variant].val;
                if (lookingShield) {
                    damage *= DataHandler_default.getWeapon(11).shield;
                }
                return damage;
            } else if (DataHandler_default.isShootable(id) && !lookingShield) {
                const projectile = DataHandler_default.getProjectile(id);
                return projectile.damage;
            }
            return 0;
        }
        getMaxKnockback() {
            let knockback = 60;
            const {primary: primary, secondary: secondary} = this.weapon;
            if (primary != null) {
                knockback += DataHandler_default.getWeapon(primary).knockback;
            }
            if (secondary != null) {
                knockback += DataHandler_default.getWeapon(secondary).knockback;
            }
            return knockback;
        }
        getPrimaryKnockback(target) {
            const {primary: primary} = this.weapon;
            if (primary !== null && this.isReloaded(0, 1)) {
                const {range: range, knockback: knockback} = DataHandler_default.getWeapon(primary);
                if (this.collidingEntity(target, range)) {
                    return knockback;
                }
            }
            return 0;
        }
        getActualMaxKnockback(target) {
            let output = 0;
            const {primary: primary, secondary: secondary} = this.weapon;
            const hitScale = target.hitScale;
            if (primary !== null && this.isReloaded(0, 1)) {
                const {range: range, knockback: knockback} = DataHandler_default.getWeapon(primary);
                if (this.collidingEntity(target, range + hitScale)) {
                    output += knockback;
                }
            }
            if (secondary !== null && this.isReloaded(1, 1)) {
                const {range: range, knockback: knockback} = DataHandler_default.getWeapon(secondary);
                if (this.collidingEntity(target, range + hitScale)) {
                    output += knockback;
                }
            }
            if (this.isReloaded(2, 1)) {
                if (this.collidingEntity(target, 700 + hitScale)) {
                    output += 60;
                }
            }
            return output;
        }
        getItemPlaceScale(itemID) {
            const item = Items[itemID];
            return this.scale + item.scale + item.placeOffset;
        }
        isReloaded(type, tick) {
            const reload = this.reload[type].current;
            const max = this.reload[type].max - tick;
            return reload >= max;
        }
        atExact(type, tick) {
            const {current: current, max: max} = this.reload[type];
            return current === max - tick;
        }
        isEmptyReload(type) {
            const reload = this.reload[type].current;
            return reload === 0;
        }
        detectSpikeInsta() {
            const {myPlayer: myPlayer, ObjectManager: ObjectManager} = this.client;
            const spikeID = this.globalInventory[4] || 9;
            const placeLength = this.getItemPlaceScale(spikeID);
            const pos1 = this.pos.current;
            const pos2 = myPlayer.pos.current;
            const angleToMyPlayer = pos1.angle(pos2);
            const spike = Items[spikeID];
            const range = this.collisionScale + spike.scale;
            const straightSpikePos = pos1.addDirection(angleToMyPlayer, placeLength);
            const distance = pos2.distance(straightSpikePos);
            if (distance > range) {
                return 0;
            }
            const angles = ObjectManager.getBestPlacementAngles({
                position: pos1,
                id: spikeID,
                targetAngle: angleToMyPlayer,
                ignoreID: null,
                preplace: false,
                reduce: false,
                fill: false
            });
            for (const angle of angles) {
                const spikePos = pos1.addDirection(angle, placeLength);
                const distance2 = pos2.distance(spikePos);
                if (distance2 <= range) {
                    return spike.damage;
                }
            }
            return 0;
        }
        canPossiblyInstakill() {
            const {PlayerManager: PlayerManager, myPlayer: myPlayer} = this.client;
            const lookingShield = PlayerManager.lookingShield(myPlayer, this);
            const {primary: primary, secondary: secondary} = this.weapon;
            const primaryDamage = this.getMaxWeaponDamage(primary, lookingShield);
            const secondaryDamage = this.getMaxWeaponDamage(secondary, lookingShield);
            const addRange = this.isTrapped ? 30 : 130;
            const boostRange = this.usingBoost && !this.isTrapped ? 430 : addRange;
            const primaryRange = this.getWeaponRange(primary) + boostRange;
            const secondaryRange = this.getWeaponRange(secondary) + addRange;
            const turretRange = 700 + addRange;
            const primaryReloaded = this.isReloaded(0, 1);
            const primaryVariant = this.getWeaponVariant(primary).current;
            const isDiamondPolearm = primary === 5 && primaryVariant >= 2;
            const collidingPrimary = myPlayer.collidingEntity(this, primaryRange);
            const collidingSecondary = myPlayer.collidingEntity(this, DataHandler_default.isShootable(secondary) ? primaryRange : secondaryRange);
            const collidingTurret = myPlayer.collidingEntity(this, turretRange);
            let spikeSyncDamage = 0;
            let includeTurret = false;
            if (collidingPrimary) {
                if (primaryReloaded) {
                    this.potentialDamage += primaryDamage;
                    this.primaryDamage = primaryDamage;
                    spikeSyncDamage += primaryDamage;
                }
                includeTurret = true;
            }
            if (collidingSecondary) {
                if (this.isReloaded(1, 1)) {
                    this.potentialDamage += secondaryDamage;
                }
                if (DataHandler_default.isMelee(secondary)) {
                    includeTurret = true;
                }
            }
            if (this.isReloaded(2, 1) && includeTurret && !lookingShield) {
                this.potentialDamage += 25;
            }
            if (collidingPrimary && collidingTurret && this.isEmptyReload(2) && primaryReloaded && isDiamondPolearm) {
                this.velocityTicking = true;
            }
            if (collidingPrimary && collidingSecondary && collidingTurret && this.isEmptyReload(1) && this.isEmptyReload(2) && primaryReloaded) {
                this.reverseInsta = true;
            }
            if (collidingPrimary && (this.weapon.oldCurrent === 0 && this.weapon.current === 5 || this.weapon.current === 0 && this.isEmptyReload(0) && this.hatID === 7)) {
                this.toolHammerInsta = true;
            }
            const pos1 = this.pos.current;
            const pos2 = myPlayer.pos.current;
            const distance = pos1.distance(pos2);
            const angle = pos1.angle(pos2);
            const offset = Math.asin(2 * myPlayer.scale / (2 * distance));
            const lookingAt = getAngleDist(angle, this.angle) <= offset;
            const {current: current, oldCurrent: oldCurrent} = this.weapon;
            const bowDetect = current === 9 && oldCurrent !== 9 || current === 12 && oldCurrent === 9 || current === 15 && oldCurrent === 12;
            if (distance > 300 && lookingAt && bowDetect) {
                this.rangedBowInsta = true;
            }
            const spikeDamage = this.detectSpikeInsta();
            if (spikeDamage !== 0) {
                this.canPlaceSpike = true;
                this.spikeDamage = spikeDamage;
                spikeSyncDamage += spikeDamage;
                if (spikeSyncDamage >= 100) {
                    this.spikeSyncThreat = true;
                }
            }
            const soldierDefense = Hats[6].dmgMult;
            if (this.potentialDamage * soldierDefense >= myPlayer.currentHealth) {
                return 3;
            }
            const soldierMult = myPlayer.hatID === 6 ? soldierDefense : 1;
            if (this.potentialDamage * soldierMult >= myPlayer.currentHealth) {
                return 2;
            }
            return 0;
        }
    }

    const Player_default = Player;

    const resizeEvent = new Event("resize");

    const ZoomHandler = new class {
        _scale={
            Default: {
                _w: 1920,
                _h: 1080
            },
            current: {
                _w: 1920,
                _h: 1080
            },
            _smooth: {
                _w: Hooker_default.linker(1920),
                _h: Hooker_default.linker(1080)
            }
        };
        getScale() {
            const dpr = 1;
            return Math.max(window.innerWidth / this._scale.Default._w, window.innerHeight / this._scale.Default._h) * dpr;
        }
        tempScale=1;
        handler(event) {
            if (!(event.target instanceof HTMLCanvasElement) || event.ctrlKey || event.shiftKey || event.altKey || isActiveInput()) {
                return;
            }
            const {Default: Default, current: current} = this._scale;
            if (event.deltaY < 0) {
                this.tempScale *= 1.1;
            } else {
                this.tempScale /= 1.1;
            }
            this.tempScale = clamp(this.tempScale, .1, 22);
            const zoom = this.tempScale;
            current._w = Default._w * zoom;
            current._h = Default._h * zoom;
        }
        renderStart=Date.now();
        smoothUpdate() {
            const {current: current, _smooth: smooth} = this._scale;
            const now = Math.sign(window.Number.DELTA) * Date.now();
            const delta = now - this.renderStart;
            this.renderStart = now;
            const dt = delta / 1e3;
            const blend = .4 * (1 - Math.exp(-10 * dt));
            smooth._w[0] = lerp(smooth._w[0], current._w, blend);
            smooth._h[0] = lerp(smooth._h[0], current._h, blend);
            window.dispatchEvent(resizeEvent);
        }
    };

    const ZoomHandler_default = ZoomHandler;

    const renderText = (ctx, text, size = 25, posx = 10, posy = 9) => {
        PrivateVisualTheme.drawHudText(ctx, text, size, posx, posy, ZoomHandler_default.getScale());
    };

    // BEGIN PRIVATE VISUAL THEME
function createPrivateVisualTheme(menuCSS, hudCSS) {
    const palette = Object.freeze({
        "#b6db66": "#1d2935", "#dbc666": "#373b40", "#91b2db": "#29495f",
        "#9ebf57": "#344746", "#b4db62": "#425b57", "#89a54c": "#3d5552",
        "#a5c65b": "#56716b", "#e3f1f4": "#738998",
        "#a5974c": "#364754", "#c9b758": "#536a7c", "#cebd5f": "#516575",
        "#939393": "#536575", "#bcbcbc": "#718698", "#83898e": "#455562",
        "#9da4aa": "#65798a", "#938d77": "#5c656b", "#b2ab90": "#818b92",
        "#7e7f82": "#435566", "#525252": "#101a23"
    });
    function transformBundle(source) {
        // Dark map palette only — NO shadeSprite injection (that path freezes under combat).
        return source.replace(/\.(?:fillStyle|strokeStyle)\s*=\s*(?:(?:"[^"\n]*"|'[^'\n]*')|[^,;\n])*/g,
            (assignment, offset) => {
                const snow = assignment.includes("#e3f1f4") ||
                    (/\.fillStyle\s*=\s*["']#fff["']\s*$/.test(assignment) &&
                    /^,\s*\w+\.fillRect\(0,\s*0,/.test(source.slice(offset + assignment.length)));
                return assignment.replace(/(["'])(#[\da-f]{3,8}|rgba\([^"']*\))\1/gi, (literal, quote, color) => {
                    const key = color.toLowerCase();
                    const next = palette[key] || (key === "#fff" && snow ? "#92a5b3" : null) ||
                        (/^rgba\(\s*(?:0,\s*0,\s*70,\s*0?\.35|23,\s*6,\s*62,\s*0?\.6)\s*\)$/.test(key) ? "rgba(0, 0, 0, 0)" : null);
                    return next ? quote + next + quote : literal;
                });
            });
    }
    function shadeSprite(sprite) {
        return sprite;
    }
    const hudTextCache = new Map();
    function drawHudText(ctx, text, size, x, y, scale) {
        if (!ctx || text == null) return;
        size = Number(size) || 25;
        scale = Number(scale);
        if (!Number.isFinite(scale) || scale <= 0) scale = 1;
        const key = size + ':' + text;
        let label = hudTextCache.get(key);
        if (!label) {
            const padding = 14, density = 2;
            const canvas = document.createElement('canvas');
            const paint = canvas.getContext('2d');
            const font = `700 ${size}px sans-serif`;
            paint.font = font; paint.letterSpacing = '1.5px';
            const width = Math.ceil(paint.measureText(text).width) + padding * 2;
            const height = Math.ceil(size * 1.5) + padding * 2;
            canvas.width = width * density; canvas.height = height * density;
            paint.scale(density, density);
            paint.font = font; paint.letterSpacing = '1.5px'; paint.textBaseline = 'top';
            paint.lineJoin = 'round'; paint.lineWidth = 1.3;
            paint.strokeStyle = '#5a7a94'; paint.shadowColor = 'rgba(10, 20, 30, 0.35)'; paint.shadowBlur = 3;
            paint.strokeText(text, padding, padding);
            paint.shadowColor = 'transparent'; paint.fillStyle = '#0a1018';
            paint.fillText(text, padding, padding);
            label = {canvas, padding, width, height};
            if (hudTextCache.size >= 8) hudTextCache.clear();
            hudTextCache.set(key, label);
        }
        // Reuse the rendered glow across frames, including zoom changes.
        ctx.save(); ctx.setTransform(scale, 0, 0, scale, 0, 0); ctx.globalAlpha = 1;
        ctx.drawImage(label.canvas, x - label.padding, y - label.padding, label.width, label.height);
        ctx.restore();
    }
    return Object.freeze({menuCSS, hudCSS, transformBundle, shadeSprite, drawHudText});
}

    const PrivateVisualTheme = createPrivateVisualTheme("/* Colean blue menu. Static decoration keeps the game render loop unchanged. */\n:root { color-scheme: normal; --accent: #6eb6ff; --cream: #d8e6f2; }\n/* Keep the full-screen iframe transparent; dark native controls belong only to the panel. */\nhtml, body { background: transparent; }\n#menu-container { background: transparent !important; }\n#menu-wrapper { color-scheme: dark; }\n* { font-family: \"Noto Sans\", \"Segoe UI\", sans-serif; }\n#menu-container #menu-wrapper {\n    background: #121c28 !important;\n    border: 1px solid #2a5080;\n    border-radius: 12px;\n    padding: 10px;\n    row-gap: 10px;\n    box-shadow: 0 16px 48px #000a;\n    backdrop-filter: none;\n}\n#menu-container header, #menu-container.transparent header {\n    flex-shrink: 0; height: 48px; padding: 10px 16px;\n    background: linear-gradient(105deg, #152030 0%, #1a2d42 56%, #243a52 100%);\n    border: 1px solid #3d8fd4; border-radius: 9px;\n}\nheader #credits { align-items: center; justify-content: flex-start; gap: 12px; }\nheader .page-title { color: var(--accent); font-size: 2.25em; white-space: nowrap; }\nheader #credits p { margin: 0; color: var(--cream); white-space: nowrap; font-size: 1.15em; }\nheader #logo { width: 42px; scale: 1; }\nheader #logo path { fill: #6eb6ff; }\nheader #close-button {\n    fill: var(--accent); width: 34px; height: 34px; padding: 4px;\n    background: #152536; border: 1px solid #2a5080; border-radius: 5px;\n}\nheader #close-button:hover { fill: #f0f7ff; background: #3d8fd4; }\nmain { min-height: 0; height: calc(100% - 80px); gap: 10px; }\n#menu-container #navbar-container {\n    background: #0f1820; border: 1px solid #2a4060; border-radius: 8px;\n    padding: 5px; gap: 2px; overflow-y: auto; flex-shrink: 0;\n}\n#menu-container #navbar-container .open-menu {\n    width: 185px; flex-shrink: 0; height: 62px; padding: 0 16px;\n    background: #152536; border: 1px solid transparent; border-radius: 4px;\n    transition: background 150ms, border-color 150ms;\n}\n#menu-container #navbar-container .open-menu span { color: #d8e6f2; }\n#menu-container #navbar-container .open-menu:hover { background: #1e3a55; border-color: #3d6a9a; }\n#menu-container #navbar-container .open-menu.active {\n    background: linear-gradient(110deg, #2a6090, #1a4060); border-color: #6eb6ff;\n    box-shadow: inset 3px 0 #56abff;\n}\n.open-menu:hover span { transform: none; }\n#page-container { min-width: 0; border: 1px solid #2a4060; border-radius: 8px; background: #030a10; }\n#menu-container .menu-page { background: #030a10; padding: 16px 18px; min-height: 100%; box-sizing: border-box; }\n.menu-page .page-title { color: var(--accent); font-size: 2.8em; line-height: 1.15; margin-bottom: 5px; }\n.menu-page .page-description { color: #b6c2cd; font-size: 1.02rem; }\n#menu-container .menu-page .section {\n    background: #060b10; border: 1px solid #2a4060; border-radius: 9px; padding: 14px 16px; margin-top: 16px;\n}\n.menu-page .section .section-title { color: var(--cream); font-size: 1.6em; }\n.menu-page .section .section-content .content-option { padding: 3px 0; gap: 14px; }\n.menu-page .section .section-content .content-option .option-title,\n.menu-page .section .section-content .content-option:hover .option-title { color: #c5d4e0; font-size: 1.16em; }\n.content-option:hover { background: #10315133; }\n.menu-page .section .section-content .text .text-value, .highlight { color: #d1dce7; }\n.menu-page .section .section-content .content-split { min-width: 0; row-gap: 4px; }\n.menu-page .section .section-content.split { column-gap: 30px; }\n.menu-page .section .section-content .hotkeyInput,\n.menu-page .section .option-button, .input {\n    background: #081827; border: 1px solid #2766a4; border-radius: 5px; color: #d5e3f0;\n    box-shadow: none; transition: background 150ms, border-color 150ms;\n}\n.menu-page .section .section-content .hotkeyInput { width: 88px; height: 34px; flex-shrink: 0; }\n.menu-page .section .option-button { border-width: 1px; padding: 10px 20px; }\n.menu-page .section .section-content .hotkeyInput:hover,\n.menu-page .section .section-content .hotkeyInput.active,\n.menu-page .section .option-button:hover { background: #103151; border-color: #4ea4fb; }\nbutton:focus-visible, .input:focus-visible, input:focus-visible { outline: 2px solid #82c1ff; outline-offset: 3px; }\n.menu-page .section .section-content .switch-checkbox { width: 60px; height: 30px; flex-shrink: 0; }\n.menu-page .section .section-content .switch-checkbox span {\n    background: #15202b; border: 1px solid #304457; border-radius: 16px; box-shadow: none;\n}\n.menu-page .section .section-content .switch-checkbox span:before {\n    width: 22px; height: 22px; left: 4px; border-radius: 50%; background: #aa9399; transform: none;\n}\n.menu-page .section .section-content .switch-checkbox input:checked + span { background: #1c5d9d; box-shadow: none; border-color: #428ed9; }\n.menu-page .section .section-content .switch-checkbox input:checked + span:before { transform: translateX(29px); background: #ebf5ff; }\n.menu-page .section .section-content .switch-checkbox input:focus-visible + span { outline: 2px solid #82c1ff; outline-offset: 3px; }\n.menu-page .section .section-content .slider input { height: 10px; border-radius: 8px; background: #213c57; box-shadow: none; }\n.menu-page .section .section-content .slider input::-webkit-slider-thumb { width: 23px; height: 23px; border-radius: 50%; background: #65b2ff; }\n.menu-page .section .section-content .slider .slider-value { color: #c4d4e4; opacity: 1; font-size: 1.15em; }\n.menu-page .section .section-content input[id][type=\"color\"] { background: #102335; }\n.option-description { background: #132536; color: #dfeaf4; border: 1px solid #316292; }\n#bot-family-switcher button, #cross-server-type-switcher button {\n    background: #081827; border-color: #25619d; color: #d5e3f0;\n}\n#bot-family-switcher button:hover { background: #103151; color: #fff; }\n#bot-family-options, #cross-server-type-options { background: #071420; border-color: #25619d; }\n#menu-container .loadout-switch > span { background: #15202b; border: 1px solid #304457; border-radius: 15px; }\n#menu-container .loadout-switch > span:after { background: #aa9399; border-radius: 50%; }\n#menu-container .loadout-switch input:checked + span { background: #1c5d9d; border-color: #428ed9; }\n#menu-container .loadout-switch input:checked + span:after { background: #ebf5ff; }\n#menu-container .cross-server-row.current-server { background: #13355766; }\n::-webkit-scrollbar-track { background: #08111a; }\n::-webkit-scrollbar-thumb { background: #1b4269; border: 2px solid #08111a; }\nhtml, body { scrollbar-color: #1b4269 #08111a; }\n#menu-container.transparent #menu-wrapper { background: rgba(5, 7, 9,, .96); backdrop-filter: none; box-shadow: 0 16px 48px #0009; }\n#menu-container.transparent #navbar-container { background: rgba(6, 14, 22,, .94); }\n#menu-container.transparent .menu-page { background: rgba(3, 10, 16,, .94); }\n#menu-container.transparent .section { background: rgba(6, 11, 16,, .9); }\n/* Sparse, stationary flecks match the reference without timers or animation. */\n#menu-wrapper::after {\n    content: \"\"; position: absolute; inset: 85px 28px 24px 225px; pointer-events: none;\n    background: radial-gradient(ellipse 4px 3px at 83% 12%, #83b5e760 98%, transparent),\n        radial-gradient(ellipse 3px 4px at 63% 40%, #83b5e740 98%, transparent),\n        radial-gradient(ellipse 3px 2px at 34% 65%, #83b5e740 98%, transparent);\n}\n@media (prefers-reduced-motion: reduce) { *, *::before, *::after { transition: none !important; animation: none !important; } }\n", "/* Midnight HUD. Semantic item, health, team and enemy colors are preserved. */\n#iframe-container { background: transparent; color-scheme: normal; }\n#gameCanvas { background-color: #1d2935; }\n#leaderboard, #chatLog, #storeHolder, #allianceHolder, #itemHolder, #toggleStoreType,\n#setupCard, #linksContainer2, .resourceDisplay, #killCounter, #totalKillCounter,\n#ageBar, #mapDisplay, .actionBarItem, .upgradeItem, #chatBox {\n    background-color: rgba(9, 17, 25, .9) !important;\n    border: 1px solid #354352; border-radius: 6px; color: #edf2f6;\n    box-shadow: none;\n}\n#leaderboard { padding: 12px 14px; }\n#leaderboard .leaderboardItem { color: #bbc6cf; }\n#leaderboard .leaderScore, #chatLogHeader, #ageText { color: #f1f5f8; }\n#ageBarBody { background: #d9e3eb; border-radius: 3px; }\n#storeButton, #allianceButton, #chatButton { background-color: #0b141ee6; border-radius: 5px; }\n.actionBarItem:hover, .upgradeItem:hover { background-color: #344658 !important; border-color: #71899e; }\n#chatLog { width: 340px; height: 170px; font-family: \"Hammersmith One\", \"Segoe UI\", sans-serif; font-size: 13px; }\n#chatLogHeader { font-size: 1.35rem; }\n#chatLog, #chatLogHeader, #chatLog span {\n    color: #0a1018 !important; font-weight: 800;\n    text-shadow: -.6px 0 #6a9ec8, .6px 0 #6a9ec8, 0 -.6px #6a9ec8, 0 .6px #6a9ec8, 0 0 2px rgba(62, 143, 212, .25);\n}\n#messageContainer::-webkit-scrollbar-track { background: #111b26; }\n#messageContainer::-webkit-scrollbar-thumb { background: #3b4f62; }\n#coleanStats { color: #c9d5df; text-shadow: 0 1px 2px #050a11; }\n.equipButton { color: #a8c8e2; }\n#gmx-panel { background: #0c1218 !important; border: 1px solid #3d8fd4 !important; border-radius: 9px !important; box-shadow: 0 12px 32px #0008 !important; }\n#gmx-panel .gmx-header { background: linear-gradient(105deg,#0f1820,#2a5080); border-bottom-color: #3d8fd4; border-radius: 5px; }\n#gmx-panel .gmx-title { color: #6eb6ff !important; }\n#gmx-panel .gmx-row, #gmx-panel label, #gmx-panel .gmx-status { color: #c5d4e0 !important; }\n#gmx-panel .gmx-btn, #gmx-panel .gmx-tab { color: #d8e6f2 !important; background: #152536; border-color: #2a5080; }\n#gmx-panel .gmx-btn[data-mode-active=\"true\"], #gmx-panel .gmx-tab.active {\n    background: #2a6aad !important; color: #f0f7ff !important; border-color: #6eb6ff !important;\n}\n#gmx-panel input[type=\"range\"], #gmx-panel input[type=\"checkbox\"] { accent-color: #6eb6ff !important; }\n#gmx-panel .gmx-close:hover { transform: none; box-shadow: none; }\n#colean-extra-launcher { background: #101c28 !important; color: #e7edf4 !important; border: 1px solid #526779 !important; border-radius: 4px; }\n");
    // END PRIVATE VISUAL THEME

    const Renderer = new class {
        _renderObjects=[];
        totalTimes=[];
        lastLogTime=performance.now();
        _preRender() {
            ZoomHandler_default.smoothUpdate();
        }
        _postRender() {
            const now = performance.now();
            while (this.totalTimes.length > 0 && this.totalTimes[0] <= now - 1e3) {
                this.totalTimes.shift();
            }
            this.totalTimes.push(now);
            const fps = this.totalTimes.length;
            if (now - this.lastLogTime >= 1e3) {
                GameUI_default.updateFPS(fps);
                this.lastLogTime = now;
            }
        }
        _mapPreRender(ctx) {
            ctx.save();
            ctx.globalAlpha = .6;
            const width = ctx.canvas.width;
            const height = ctx.canvas.height;
            ctx.fillStyle = "#9aabba";
            ctx.fillRect(0, 0, width, Config_default.snowBiomeTop / Config_default.mapScale * height);
            ctx.fillStyle = "#a89040";
            ctx.fillRect(0, 12e3 / Config_default.mapScale * height, width, height);
            ctx.fillStyle = "#4a7a9a";
            const startY = (Config_default.mapScale / 2 - Config_default.riverWidth / 2) / Config_default.mapScale * height;
            ctx.fillRect(0, startY, width, Config_default.riverWidth / Config_default.mapScale * height);
            const {_ModuleHandler: ModuleHandler, myPlayer: myPlayer} = client;
            ctx.globalAlpha = 1;
            const markSize = 8;
            if (ModuleHandler.followPath) {
                const pos = ModuleHandler.endTarget.copy().div(Config_default.mapScale).mult(width);
                ctx.fillStyle = "#c2383d";
                ctx.beginPath();
                ctx.arc(pos.x, pos.y, markSize, 0, 2 * Math.PI);
                ctx.fill();
            }
            if (myPlayer.teleported) {
                const pos = myPlayer.teleportPos.copy().div(Config_default.mapScale).mult(width);
                ctx.fillStyle = "#d76edb";
                ctx.beginPath();
                ctx.arc(pos.x, pos.y, markSize, 0, 2 * Math.PI);
                ctx.fill();
            }
            if (Settings_default._notificationTracers) {
                ctx.fillStyle = Settings_default._notificationTracersColor;
                const notifications = NotificationRenderer_default.notifications;
                for (const notify of notifications) {
                    const x = notify.x / Config_default.mapScale * width;
                    const y = notify.y / Config_default.mapScale * width;
                    ctx.beginPath();
                    ctx.arc(x, y, markSize * 1.5, 0, 2 * Math.PI);
                    ctx.fill();
                }
            }

            // bots on minimap
            {
                ctx.fillStyle = "#10eb3f";
                for (const bot of client.clients) {
                    if (!bot || bot.crossServer || !bot.myPlayer?.inGame) continue;
                    const p = bot.myPlayer.pos?.current;
                    if (!p || !Number.isFinite(p.x) || !Number.isFinite(p.y)) continue;
                    ctx.beginPath();
                    ctx.arc(
                        p.x / Config_default.mapScale * width,
                        p.y / Config_default.mapScale * height,
                        6, 0, Math.PI * 2
                    );
                    ctx.fill();
                }
            }

            ctx.restore();
        }
        drawNorthArrow(ctx, x, y, angle) {
            const size = 35;
            ctx.save();
            ctx.globalAlpha = .7;
            ctx.fillStyle = "#883131";
            ctx.translate(x, y);
            ctx.rotate(angle + Math.PI / 2);
            ctx.beginPath();
            ctx.moveTo(0, -size / 2);
            ctx.lineTo(size / 3, size / 2);
            ctx.lineTo(0, size / 3);
            ctx.lineTo(-size / 3, size / 2);
            ctx.closePath();
            ctx.fill();
            ctx.restore();
        }
        rotation=0;
        arrowPart=2 * Math.PI / 3;
        drawTarget(ctx, entity) {
            const len = entity.scale + 30;
            this.rotation = (this.rotation + .01) % 6.28;
            const offset = Colean._offset;
            ctx.save();
            ctx.translate(-offset.x, -offset.y);
            ctx.translate(entity.x, entity.y);
            ctx.rotate(this.rotation);
            this.drawNorthArrow(ctx, len * Math.cos(this.arrowPart * 1), len * Math.sin(this.arrowPart * 1), -1.04);
            this.drawNorthArrow(ctx, len * Math.cos(this.arrowPart * 2), len * Math.sin(this.arrowPart * 2), 1.04);
            this.drawNorthArrow(ctx, len * Math.cos(this.arrowPart * 3), len * Math.sin(this.arrowPart * 3), 3.14);
            ctx.restore();
        }
        rect(ctx, pos, scale, color, lineWidth = 4, alpha = 1) {
            const offset = Colean._offset;
            ctx.save();
            ctx.globalAlpha = alpha;
            ctx.strokeStyle = color;
            ctx.lineWidth = lineWidth;
            ctx.beginPath();
            ctx.translate(-offset.x, -offset.y);
            ctx.translate(pos.x, pos.y);
            ctx.rect(-scale, -scale, scale * 2, scale * 2);
            ctx.stroke();
            ctx.closePath();
            ctx.restore();
        }
        roundRect(ctx, x, y, w, h, r) {
            if (w < 2 * r) {
                r = w / 2;
            }
            if (h < 2 * r) {
                r = h / 2;
            }
            if (r < 0) {
                r = 0;
            }
            ctx.beginPath();
            ctx.moveTo(x + r, y);
            ctx.arcTo(x + w, y, x + w, y + h, r);
            ctx.arcTo(x + w, y + h, x, y + h, r);
            ctx.arcTo(x, y + h, x, y, r);
            ctx.arcTo(x, y, x + w, y, r);
            ctx.closePath();
        }
        circle(ctx, x, y, radius, color, opacity = 1, lineWidth = 4) {
            const offset = Colean._offset;
            ctx.save();
            ctx.globalAlpha = opacity;
            ctx.strokeStyle = color;
            ctx.lineWidth = lineWidth;
            ctx.beginPath();
            ctx.translate(-offset.x, -offset.y);
            ctx.arc(x, y, radius, 0, 2 * Math.PI);
            ctx.stroke();
            ctx.closePath();
            ctx.restore();
        }
        fillCircle(ctx, x, y, radius, color, opacity = 1) {
            const offset = Colean._offset;
            ctx.save();
            ctx.globalAlpha = opacity;
            ctx.fillStyle = color;
            ctx.beginPath();
            ctx.translate(-offset.x, -offset.y);
            ctx.arc(x, y, radius, 0, 2 * Math.PI);
            ctx.fill();
            ctx.closePath();
            ctx.restore();
        }
        renderText(ctx, text, x, y, fontSize = 14, opacity = .5) {
            ctx.save();
            ctx.fillStyle = "#fff";
            ctx.strokeStyle = "#3d3f42";
            ctx.lineWidth = 8;
            ctx.lineJoin = "round";
            ctx.textBaseline = "top";
            ctx.globalAlpha = opacity;
            ctx.font = fontSize + "px Hammersmith One";
            const offset = Colean._offset;
            ctx.translate(-offset.x, -offset.y);
            ctx.strokeText(text, x, y);
            ctx.fillText(text, x, y);
            ctx.restore();
        }
        line(ctx, start, end, color, opacity = 1, lineWidth = 4) {
            const offset = Colean._offset;
            ctx.save();
            ctx.translate(-offset.x, -offset.y);
            ctx.globalAlpha = opacity;
            ctx.strokeStyle = color;
            ctx.lineCap = "round";
            ctx.lineWidth = lineWidth;
            ctx.beginPath();
            ctx.moveTo(start.x, start.y);
            ctx.lineTo(end.x, end.y);
            ctx.stroke();
            ctx.restore();
        }
        arrow(ctx, length, x, y, angle, color) {
            const offset = Colean._offset;
            ctx.save();
            ctx.translate(-offset.x, -offset.y);
            ctx.translate(x, y);
            ctx.rotate(Math.PI / 4);
            ctx.rotate(angle);
            ctx.globalAlpha = .75;
            ctx.strokeStyle = color;
            ctx.lineCap = "round";
            ctx.lineWidth = 8;
            ctx.beginPath();
            ctx.moveTo(-length, -length);
            ctx.lineTo(length, -length);
            ctx.lineTo(length, length);
            ctx.stroke();
            ctx.restore();
        }
        cross(ctx, x, y, size, lineWidth, color) {
            ctx.save();
            ctx.globalAlpha = 1;
            ctx.lineWidth = lineWidth;
            ctx.strokeStyle = color;
            const offset = Colean._offset;
            ctx.translate(x - offset.x, y - offset.y);
            const halfSize = size / 2;
            ctx.beginPath();
            ctx.moveTo(-halfSize, -halfSize);
            ctx.lineTo(halfSize, halfSize);
            ctx.stroke();
            ctx.beginPath();
            ctx.moveTo(halfSize, -halfSize);
            ctx.lineTo(-halfSize, halfSize);
            ctx.stroke();
            ctx.restore();
        }
        getTracerColor(entity) {
            if (entity instanceof Notify) {
                return Settings_default._notificationTracersColor;
            }
            if (Settings_default._animalTracers && entity.isAI) {
                return Settings_default._animalTracersColor;
            }
            if (Settings_default._teammateTracers && entity.isPlayer && client.myPlayer.isTeammateByID(entity.sid)) {
                return Settings_default._teammateTracersColor;
            }
            if (Settings_default._enemyTracers && entity.isPlayer && client.myPlayer.isEnemyByID(entity.sid)) {
                return Settings_default._enemyTracersColor;
            }
            return null;
        }
        renderTracer(ctx, entity, player) {
            const color = this.getTracerColor(entity);
            if (color === null) {
                return;
            }
            const pos1 = new Vector_default(player.x, player.y);
            const pos2 = new Vector_default(entity.x, entity.y);
            const w = 8;
            const distance = Math.min(125 + w * 2, pos1.distance(pos2) - w * 2);
            const angle = pos1.angle(pos2);
            const pos = pos1.addDirection(angle, distance);
            this.arrow(ctx, w, pos.x, pos.y, angle, color);
        }
        renderDistance(ctx, entity, player) {
            const pos1 = new Vector_default(player.x, player.y);
            const pos2 = new Vector_default(entity.x, entity.y);
            const entityTarget = client.PlayerManager.getEntity(entity.sid, !!entity.isPlayer);
            if (entityTarget === null) {
                return;
            }
            const pos3 = client.myPlayer.pos.current;
            const pos4 = entityTarget.pos.current;
            const distance = fixTo(pos3.distance(pos4), 2);
            const center = pos1.addDirection(pos1.angle(pos2), pos1.distance(pos2) / 2);
            this.renderText(ctx, `[${entity.sid}]: ${distance}`, center.x, center.y);
        }
        getMarkerColor(object) {
            const id = object.owner?.sid;
            if (typeof id !== "number") {
                return null;
            }
            if (Settings_default._itemMarkers && client.myPlayer.isMyPlayerByID(id)) {
                return Settings_default._itemMarkersColor;
            }
            if (Settings_default._teammateMarkers && client.myPlayer.isTeammateByID(id)) {
                return Settings_default._teammateMarkersColor;
            }
            if (Settings_default._enemyMarkers && client.myPlayer.isEnemyByID(id)) {
                return Settings_default._enemyMarkersColor;
            }
            return null;
        }
        renderMarker(ctx, object) {
            const color = this.getMarkerColor(object);
            if (color === null) {
                return;
            }
            const offset = Colean._offset;
            const x = object.x + object.xWiggle - offset.x;
            const y = object.y + object.yWiggle - offset.y;
            ctx.save();
            ctx.strokeStyle = "#3b3b3b";
            ctx.lineWidth = 3;
            ctx.fillStyle = color;
            ctx.beginPath();
            ctx.arc(x, y, 9, 0, 2 * Math.PI);
            ctx.fill();
            ctx.stroke();
            ctx.closePath();
            ctx.restore();
        }
        barContainer(ctx, x, y, w, h, r = 8) {
            ctx.fillStyle = "#3d3f42";
            this.roundRect(ctx, x, y, w, h, r);
            ctx.fill();
        }
        barContent(ctx, x, y, w, h, fill, color) {
            const barPad = Config_default.barPad;
            ctx.fillStyle = color;
            this.roundRect(ctx, x + barPad, y + barPad, (w - barPad * 2) * fill, h - barPad * 2, 7);
            ctx.fill();
        }
        getNameY(target) {
            let nameY = 34;
            const height = 5;
            if (target === client.myPlayer && Settings_default._weaponXPBar) {
                nameY += height;
            }
            if (Settings_default._playerTurretReloadBar) {
                nameY += height;
            }
            if (Settings_default._weaponReloadBar) {
                nameY += height;
            }
            return nameY;
        }
        getContainerHeight(entity) {
            const {barHeight: barHeight, barPad: barPad} = Config_default;
            let height = barHeight;
            if (entity.isPlayer) {
                const smallBarHeight = barHeight - 4;
                const player = client.PlayerManager.playerData.get(entity.sid);
                if (player === void 0) {
                    return height;
                }
                if (player === client.myPlayer && Settings_default._weaponXPBar) {
                    height += smallBarHeight - barPad;
                }
                if (Settings_default._playerTurretReloadBar) {
                    height += smallBarHeight - barPad;
                }
                if (Settings_default._weaponReloadBar) {
                    height += barHeight - barPad;
                }
            }
            return height;
        }
        renderBar(ctx, entity) {
            const {barWidth: barWidth, barHeight: barHeight, barPad: barPad} = Config_default;
            const smallBarHeight = barHeight - 4;
            const totalWidth = barWidth + barPad;
            const scale = entity.scale + 34;
            const {myPlayer: myPlayer, PlayerManager: PlayerManager} = client;
            const offset = Colean._offset;
            let x = entity.x - offset.x - totalWidth;
            let y = entity.y - offset.y + scale;
            ctx.save();
            const player = entity.isPlayer && PlayerManager.playerData.get(entity.sid);
            const animal = entity.isAI && PlayerManager.animalData.get(entity.sid);
            let height = 0;
            if (player instanceof Player_default) {
                const [primary, secondary, turret] = player.reload;
                if (player === myPlayer && Settings_default._weaponXPBar) {
                    const weapon = DataHandler_default.getWeapon(myPlayer.weapon.current);
                    const current = WeaponVariants[myPlayer.getWeaponVariant(weapon.id).current].color;
                    const next = WeaponVariants[myPlayer.getWeaponVariant(weapon.id).next].color;
                    const XP = myPlayer.weaponXP[weapon.itemType];
                    this.barContainer(ctx, x, y, totalWidth * 2, smallBarHeight);
                    this.barContent(ctx, x, y, totalWidth * 2, smallBarHeight, 1, current);
                    this.barContent(ctx, x, y, totalWidth * 2, smallBarHeight, clamp(XP.current / XP.max, 0, 1), next);
                    height += smallBarHeight - barPad;
                }
                if (Settings_default._playerTurretReloadBar) {
                    this.barContainer(ctx, x, y + height, totalWidth * 2, smallBarHeight);
                    this.barContent(ctx, x, y + height, totalWidth * 2, smallBarHeight, turret.current / turret.max, Settings_default._playerTurretReloadBarColor);
                    height += smallBarHeight - barPad;
                }
                if (Settings_default._weaponReloadBar) {
                    const extraPad = 2.25;
                    this.barContainer(ctx, x, y + height, totalWidth * 2, barHeight);
                    this.barContent(ctx, x, y + height, totalWidth + extraPad, barHeight, primary.current / primary.max, Settings_default._weaponReloadBarColor);
                    this.barContent(ctx, x + totalWidth - extraPad, y + height, totalWidth + extraPad, barHeight, secondary.current / secondary.max, Settings_default._weaponReloadBarColor);
                    height += barHeight - barPad;
                }
            }
            const target = player || animal;
            if (target) {
                const container = getTargetValue(Colean, "_config");
                setTargetValue(container, "nameY", this.getNameY(target));
                const {currentHealth: currentHealth, maxHealth: maxHealth} = target;
                const health = animal ? maxHealth : 100;
                const color = PlayerManager.isEnemyTarget(myPlayer, target) ? "#cc5151" : "#8ecc51";
                this.barContainer(ctx, x, y + height, totalWidth * 2, barHeight);
                this.barContent(ctx, x, y + height, totalWidth * 2, barHeight, currentHealth / health, color);
                height += barHeight;
            }
            ctx.restore();
        }
        renderHP(ctx, entity) {
            if (!Settings_default._renderHP) {
                return;
            }
            const {barPad: barPad, nameY: nameY} = Config_default;
            const containerHeight = this.getContainerHeight(entity);
            let text = `HP ${Math.floor(entity.health)}/${entity.maxHealth}`;
            const offset = entity.scale + nameY + barPad + containerHeight;
            const {myPlayer: myPlayer, PlayerManager: PlayerManager} = client;
            const _offset = Colean._offset;
            const x = entity.x - _offset.x;
            const y = entity.y - _offset.y + offset;
            if (entity.isPlayer) {
                const player = PlayerManager.playerData.get(entity.sid);
                if (player !== void 0) {
                    text += ServerCapacity.usesHealAcknowledgements(client)
                        ? (player.shameActive ? ' Clown' : ` Shame ~${player.shameCount}`)
                        : ` ${player.shameCount}/8`;
                }
            }
            ctx.save();
            ctx.fillStyle = "#fff";
            ctx.strokeStyle = "#3d3f42";
            ctx.lineWidth = 8;
            ctx.lineJoin = "round";
            ctx.textBaseline = "top";
            ctx.font = "19px Hammersmith One";
            ctx.strokeText(text, x, y);
            ctx.fillText(text, x, y);
            ctx.restore();
        }
        circularBar(ctx, object, perc, angle, color, offset = 0) {
            const _offset = Colean._offset;
            const x = object.x + object.xWiggle - _offset.x;
            const y = object.y + object.yWiggle - _offset.y;
            const height = Config_default.barHeight * .5;
            const defaultScale = 10 + height / 2;
            const scale = defaultScale + 1 + offset;
            ctx.save();
            ctx.translate(x, y);
            ctx.rotate(angle);
            ctx.lineCap = "round";
            ctx.strokeStyle = "#3b3b3b";
            ctx.lineWidth = height;
            ctx.beginPath();
            ctx.arc(0, 0, scale, 0, perc * 2 * Math.PI);
            ctx.stroke();
            ctx.closePath();
            ctx.strokeStyle = color;
            ctx.lineWidth = height / 3;
            ctx.beginPath();
            ctx.arc(0, 0, scale, 0, perc * 2 * Math.PI);
            ctx.stroke();
            ctx.closePath();
            ctx.restore();
            return defaultScale - 3;
        }
    };

    const Renderer_default = Renderer;

    const Animals = [ {
        id: 0,
        src: "cow_1",
        hostile: false,
        killScore: 150,
        health: 500,
        weightM: .8,
        speed: 95e-5,
        turnSpeed: .001,
        scale: 72,
        drop: [ "food", 50 ]
    }, {
        id: 1,
        src: "pig_1",
        hostile: false,
        killScore: 200,
        health: 800,
        weightM: .6,
        speed: 85e-5,
        turnSpeed: .001,
        scale: 72,
        drop: [ "food", 80 ]
    }, {
        id: 2,
        name: "Bull",
        src: "bull_2",
        hostile: true,
        dmg: 20,
        killScore: 1e3,
        health: 1800,
        weightM: .5,
        speed: 94e-5,
        turnSpeed: 74e-5,
        scale: 78,
        viewRange: 800,
        chargePlayer: true,
        drop: [ "food", 100 ]
    }, {
        id: 3,
        name: "Bully",
        src: "bull_1",
        hostile: true,
        dmg: 20,
        killScore: 2e3,
        health: 2800,
        weightM: .45,
        speed: .001,
        turnSpeed: 8e-4,
        scale: 90,
        viewRange: 900,
        chargePlayer: true,
        drop: [ "food", 400 ]
    }, {
        id: 4,
        name: "Wolf",
        src: "wolf_1",
        hostile: true,
        dmg: 8,
        killScore: 500,
        health: 300,
        weightM: .45,
        speed: .001,
        turnSpeed: .002,
        scale: 84,
        viewRange: 800,
        chargePlayer: true,
        drop: [ "food", 200 ]
    }, {
        id: 5,
        name: "Quack",
        src: "chicken_1",
        hostile: false,
        dmg: 8,
        killScore: 2e3,
        noTrap: true,
        health: 300,
        weightM: .2,
        speed: .0018,
        turnSpeed: .006,
        scale: 70,
        drop: [ "food", 100 ]
    }, {
        id: 6,
        name: "MOOSTAFA",
        nameScale: 50,
        src: "enemy",
        hostile: true,
        dontRun: true,
        fixedSpawn: true,
        spawnDelay: 6e4,
        noTrap: true,
        colDmg: 100,
        dmg: 40,
        killScore: 8e3,
        health: 18e3,
        weightM: .4,
        speed: 7e-4,
        turnSpeed: .01,
        scale: 80,
        spriteMlt: 1.8,
        leapForce: .9,
        viewRange: 1e3,
        hitRange: 210,
        hitDelay: 1e3,
        chargePlayer: true,
        drop: [ "food", 100 ]
    }, {
        id: 7,
        name: "Treasure",
        hostile: true,
        nameScale: 35,
        src: "crate_1",
        fixedSpawn: true,
        spawnDelay: 12e4,
        colDmg: 200,
        killScore: 5e3,
        health: 2e4,
        weightM: .1,
        speed: 0,
        turnSpeed: 0,
        scale: 70,
        spriteMlt: 1
    }, {
        id: 8,
        name: "MOOFIE",
        src: "wolf_2",
        hostile: true,
        fixedSpawn: true,
        dontRun: true,
        hitScare: 4,
        spawnDelay: 3e4,
        noTrap: true,
        nameScale: 35,
        dmg: 10,
        colDmg: 100,
        killScore: 3e3,
        health: 7e3,
        weightM: .45,
        speed: .0015,
        turnSpeed: .002,
        scale: 90,
        viewRange: 800,
        chargePlayer: true,
        drop: [ "food", 1e3 ]
    }, {
        id: 9,
        name: "💀MOOFIE",
        src: "wolf_2",
        hostile: true,
        fixedSpawn: true,
        dontRun: true,
        hitScare: 50,
        spawnDelay: 6e4,
        noTrap: true,
        nameScale: 35,
        dmg: 12,
        colDmg: 100,
        killScore: 3e3,
        health: 9e3,
        weightM: .45,
        speed: .0015,
        turnSpeed: .0025,
        scale: 94,
        viewRange: 1440,
        chargePlayer: true,
        drop: [ "food", 3e3 ],
        minSpawnRange: .85,
        maxSpawnRange: .9
    }, {
        id: 10,
        name: "💀Wolf",
        src: "wolf_1",
        hostile: true,
        fixedSpawn: true,
        dontRun: true,
        hitScare: 50,
        spawnDelay: 3e4,
        dmg: 10,
        killScore: 700,
        health: 500,
        weightM: .45,
        speed: .00115,
        turnSpeed: .0025,
        scale: 88,
        viewRange: 1440,
        chargePlayer: true,
        drop: [ "food", 400 ],
        minSpawnRange: .85,
        maxSpawnRange: .9
    }, {
        id: 11,
        name: "💀Bully",
        src: "bull_1",
        hostile: true,
        fixedSpawn: true,
        dontRun: true,
        hitScare: 50,
        dmg: 20,
        killScore: 5e3,
        health: 5e3,
        spawnDelay: 1e5,
        weightM: .45,
        speed: .00115,
        turnSpeed: .0025,
        scale: 94,
        viewRange: 1440,
        chargePlayer: true,
        drop: [ "food", 800 ],
        minSpawnRange: .85,
        maxSpawnRange: .9
    } ];

    const Animals_default = Animals;

    const colors = [ [ "orange", "red" ], [ "aqua", "blue" ] ];

    const EntityRenderer = new class {
        start=Date.now();
        step=0;
        drawWeaponHitbox(ctx, player) {
            if (!Settings_default._weaponHitbox) {
                return;
            }
            const {myPlayer: myPlayer} = client;
            const current = myPlayer.weapon.current;
            if (DataHandler_default.isMelee(current)) {
                const weapon = DataHandler_default.getWeapon(current);
                Renderer_default.circle(ctx, player.x, player.y, weapon.range, "#f5cb42", .5, 1);
            }
        }
        drawPlacement(ctx) {
            if (!Settings_default._possiblePlacement) {
                return;
            }
            const {myPlayer: myPlayer, _ModuleHandler: ModuleHandler} = client;
            const [type, angles] = ModuleHandler.placeAngles;
            if (type === null || angles === null) {
                return;
            }
            const id = myPlayer.getItemByType(type);
            if (id === null) {
                return;
            }
            const dist = myPlayer.getItemPlaceScale(id);
            const item = Items[id];
            for (let i = 0; i < angles.length; i++) {
                const angle = angles[i];
                const pos = myPlayer.pos.current.addDirection(angle, dist);
                Renderer_default.circle(ctx, pos.x, pos.y, item.scale, "#80edf2", .4, 1);
            }
        }
        drawEntityHP(ctx, entity) {
            Renderer_default.renderBar(ctx, entity);
            Renderer_default.renderHP(ctx, entity);
        }
        drawHitScale(ctx, entity) {
            if (!Settings_default._weaponHitbox) {
                return;
            }
            const {PlayerManager: PlayerManager} = client;
            const type = entity.isPlayer ? PlayerManager.playerData : PlayerManager.animalData;
            const target = type.get(entity.sid);
            if (target !== void 0) {
                Renderer_default.circle(ctx, entity.x, entity.y, target.hitScale, "#3f4ec4", .5, 1);
            }
            if (entity.isAI && entity.index === 6) {
                const moostafa = Animals_default[6];
                Renderer_default.circle(ctx, entity.x, entity.y, moostafa.hitRange, "#f5cb42", .5, 1);
            }
        }
        drawDanger(ctx, entity) {
            const {PlayerManager: PlayerManager} = client;
            if (entity.isPlayer) {
                const player = PlayerManager.playerData.get(entity.sid);
                if (player !== void 0 && player.danger !== 0) {
                    const isBoost = Number(player.usingBoost);
                    const isDanger = Number(player.danger >= 3);
                    Renderer_default.fillCircle(ctx, entity.x, entity.y, player.scale, colors[isBoost][isDanger], .3);
                }
            }
            if (entity.isAI) {
                const animal = PlayerManager.animalData.get(entity.sid);
                if (animal) {
                    const color = animal.isDanger ? "red" : "green";
                    Renderer_default.fillCircle(ctx, entity.x, entity.y, animal.attackRange, color, .3);
                }
            }
        }
        _render(ctx, entity, player) {
            const {myPlayer: myPlayer, EnemyManager: EnemyManager2, _ModuleHandler: ModuleHandler, ObjectManager: ObjectManager, InputHandler: InputHandler} = client;
            const isMyPlayer = entity === player;
            const pos = new Vector_default(entity.x, entity.y);
            if (isMyPlayer) {
                const now = Date.now();
                this.step = now - this.start;
                this.start = now;
                if (Settings_default._displayPlayerAngle) {
                    Renderer_default.line(ctx, pos, pos.addDirection(client.myPlayer.angle, 70), "#e9adf0");
                }
                this.drawWeaponHitbox(ctx, player);
                this.drawPlacement(ctx);
                if (myPlayer.isTrapped) {
                    Renderer_default.fillCircle(ctx, pos.x, pos.y, 35, "yellow", .5);
                }
                const {pushPos: pushPos} = ModuleHandler.staticModules.autoPush;
                const nearestPushSpike = client.EnemyManager.nearestPushSpike;
                if (pushPos !== null && nearestPushSpike !== null) {
                    Renderer_default.line(ctx, pos, pushPos, "white", .6, 1);
                    Renderer_default.line(ctx, pushPos, nearestPushSpike.pos.current, "white", .6, 1);
                }
            }
            this.drawEntityHP(ctx, entity);
            if (Settings_default._collisionHitbox) {
                Renderer_default.circle(ctx, entity.x, entity.y, entity.scale, "#c7fff2", .5, 1);
            }
            if (!isMyPlayer) {
                this.drawHitScale(ctx, entity);
                Renderer_default.renderTracer(ctx, entity, player);
                Renderer_default.renderDistance(ctx, entity, player);
                const x = entity.x;
                const y = entity.y;
                const nearestEnemyToNearestEnemy = EnemyManager2.nearestEnemyToNearestEnemy;
                if (nearestEnemyToNearestEnemy !== null && !entity.isAI && entity.sid === nearestEnemyToNearestEnemy.id) {
                    Renderer_default.fillCircle(ctx, x, y, 35, "#48f072", .5);
                } else {
                    this.drawDanger(ctx, entity);
                }
            }
            if (isMyPlayer) {
                NotificationRenderer_default.render(ctx, player);
            }
            const instakillTarget = InputHandler.instakillTarget;
            if (entity.isPlayer && instakillTarget !== null && entity.sid === instakillTarget.id) {
                Renderer_default.drawTarget(ctx, entity);
                const {bowInsta: bowInsta} = ModuleHandler.staticModules;
                if (bowInsta.active) {
                    Renderer_default.circle(ctx, entity.x, entity.y, bowInsta.distMin, "#eda0ee", .4, 1);
                    Renderer_default.circle(ctx, entity.x, entity.y, bowInsta.distMax, "#eda0ee", .4, 1);
                }
            }
            const {target: velTickTarget, minKB: minKB, maxKB: maxKB} = ModuleHandler.staticModules.velocityTick;
            if (entity.isPlayer && velTickTarget !== null && entity.sid === velTickTarget.id) {
                const diff = Math.abs(maxKB - minKB);
                const length = minKB + (maxKB - minKB) / 2;
                const angle = getAngle(entity.x, entity.y, player.x, player.y);
                const posX = entity.x + Math.cos(angle) * length;
                const posY = entity.y + Math.sin(angle) * length;
                Renderer_default.circle(ctx, posX, posY, diff, "#e25176", .5, 1);
            }
        }
    };

    const EntityRenderer_default = EntityRenderer;

    class Notify {
        x;
        y;
        timeout={
            value: 0,
            max: 1500
        };
        constructor(x, y) {
            this.x = x;
            this.y = y;
        }
        render(ctx, player) {
            this.timeout.value += EntityRenderer_default.step;
            if (this.timeout.value >= this.timeout.max) {
                NotificationRenderer.remove(this);
                return;
            }
            Renderer_default.renderTracer(ctx, this, player);
        }
    }

    const NotificationRenderer = new class {
        notifications=new Set;
        remove(notify) {
            this.notifications.delete(notify);
        }
        add(object) {
            const {x: x, y: y} = object.pos.current;
            const notify = new Notify(x, y);
            this.notifications.add(notify);
        }
        render(ctx, player) {
            for (const notification of this.notifications) {
                notification.render(ctx, player);
            }
        }
    };

    const NotificationRenderer_default = NotificationRenderer;

    class SpatialHashGrid2D {
        cellSize=0;
        grid=new Map;
        constructor(cellSize) {
            this.cellSize = cellSize;
        }
        _getKey(x, y) {
            return x << 16 | y;
        }
        clear() {
            this.grid.clear();
        }
        insert(x, y, radius, objectId) {
            const startX = (x - radius) / this.cellSize | 0;
            const startY = (y - radius) / this.cellSize | 0;
            const endX = (x + radius) / this.cellSize | 0;
            const endY = (y + radius) / this.cellSize | 0;
            for (let i = startX; i <= endX; i++) {
                for (let j = startY; j <= endY; j++) {
                    const key = this._getKey(i, j);
                    if (!this.grid.has(key)) {
                        this.grid.set(key, new Set);
                    }
                    this.grid.get(key).add(objectId);
                }
            }
        }
        query(x, y, search = 1, callback) {
            const cellX = x / this.cellSize | 0;
            const cellY = y / this.cellSize | 0;
            const candidates = new Set;
            let callbackSuccess = false;
            outerLoop: for (let i = -search; i <= search; i++) {
                for (let j = -search; j <= search; j++) {
                    const key = this._getKey(cellX + i, cellY + j);
                    if (this.grid.has(key)) {
                        for (const objectId of this.grid.get(key)) {
                            if (!candidates.has(objectId)) {
                                candidates.add(objectId);
                                if (callback(objectId)) {
                                    callbackSuccess = true;
                                    break outerLoop;
                                }
                            }
                        }
                    }
                }
            }
            return callbackSuccess;
        }
        queryFull(x, y, search = 1) {
            const cellX = x / this.cellSize | 0;
            const cellY = y / this.cellSize | 0;
            const candidates = new Set;
            for (let i = -search; i <= search; i++) {
                for (let j = -search; j <= search; j++) {
                    const key = this._getKey(cellX + i, cellY + j);
                    if (this.grid.has(key)) {
                        for (const objectId of this.grid.get(key)) {
                            candidates.add(objectId);
                        }
                    }
                }
            }
            return Array.from(candidates);
        }
        remove(x, y, radius, objectId) {
            const startX = (x - radius) / this.cellSize | 0;
            const startY = (y - radius) / this.cellSize | 0;
            const endX = (x + radius) / this.cellSize | 0;
            const endY = (y + radius) / this.cellSize | 0;
            for (let i = startX; i <= endX; i++) {
                for (let j = startY; j <= endY; j++) {
                    const key = this._getKey(i, j);
                    if (this.grid.has(key)) {
                        const cell = this.grid.get(key);
                        cell.delete(objectId);
                        if (cell.size === 0) {
                            this.grid.delete(key);
                        }
                    }
                }
            }
        }
    }

    class Sorting {
        static byDistance(target, typeA, typeB) {
            return (a, b) => {
                const dist1 = target.position[typeA].distanceDefault(a.position[typeB]);
                const dist2 = target.position[typeA].distanceDefault(b.position[typeB]);
                return dist1 - dist2;
            };
        }
        static byAngleDistance(angle) {
            return (a, b) => getAngleDist(a, angle) - getAngleDist(b, angle);
        }
        static byDanger(a, b) {
            return b.danger - a.danger;
        }
    }

    const Sorting_default = Sorting;

    class ObjectManager {
        objects=new Map;
        grid2D=new SpatialHashGrid2D(100);
        reloadingTurrets=new Map;
        attackedObjects=new Map;
        client;
        constructor(client2) {
            this.client = client2;
        }
        insertObject(object) {
            this.grid2D.insert(object.pos.current.x, object.pos.current.y, object.collisionScale, object.id);
            this.objects.set(object.id, object);
            if (object instanceof PlayerObject) {
                const {PlayerManager: PlayerManager, myPlayer: myPlayer} = this.client;
                const owner = PlayerManager.playerData.get(object.ownerID) || PlayerManager.createPlayer({
                    id: object.ownerID
                });
                object.seenPlacement = this.inPlacementRange(object);
                owner.handleObjectPlacement(object);
                if (object.type === 22) {
                    if (myPlayer.collidingObject(object, 1) || myPlayer.collidingObject(object, 4)) {
                        myPlayer.teleportPos.setVec(object.pos.current);
                        myPlayer.teleported = true;
                    }
                }
            }
        }
        createObjects(buffer) {
            for (let i = 0; i < buffer.length; i += 8) {
                const isResource = buffer[i + 6] === null;
                const data = [ buffer[i + 0], buffer[i + 1], buffer[i + 2], buffer[i + 3], buffer[i + 4] ];
                this.insertObject(isResource ? new Resource(...data, buffer[i + 5]) : new PlayerObject(...data, buffer[i + 6], buffer[i + 7]));
            }
        }
        deletedObjects=new Set;
        isDestroyedObject() {
            return this.deletedObjects.size !== 0;
        }
        removeObject(object) {
            this.grid2D.remove(object.pos.current.x, object.pos.current.y, object.collisionScale, object.id);
            this.objects.delete(object.id);
            if (object instanceof PlayerObject) {
                const player = this.client.PlayerManager.playerData.get(object.ownerID);
                if (player !== void 0) {
                    player.handleObjectDeletion(object);
                    const {myPlayer: myPlayer} = this.client;
                    const pos1 = object.pos.current.copy();
                    const pos2 = this.client.myPlayer.pos.current.copy();
                    const distance = pos1.distance(pos2);
                    const spikeID = myPlayer.getItemByType(4);
                    const range = myPlayer.getItemPlaceScale(spikeID) + object.placementScale + myPlayer.speed + 25;
                    if (distance <= range) {
                        this.deletedObjects.add(object);
                    }
                }
            }
        }
        removeObjectByID(id) {
            const object = this.objects.get(id);
            if (object !== void 0) {
                this.removeObject(object);
                if (this.client.isOwner) {
                    const pos1 = object.pos.current.copy();
                    const pos2 = this.client.myPlayer.pos.current.copy();
                    if (Settings_default._notificationTracers && !targetInsideRect(pos1, pos2, object.scale)) {
                        NotificationRenderer_default.add(object);
                    }
                }
            }
        }
        removePlayerObjects(player) {
            for (const object of player.objects) {
                this.removeObject(object);
            }
        }
        resetTurret(id) {
            const object = this.objects.get(id);
            if (object instanceof PlayerObject) {
                object.reload = 0;
                this.reloadingTurrets.set(id, object);
            }
        }
        isEnemyObject(object) {
            if (object instanceof PlayerObject && !this.client.myPlayer.isEnemyByID(object.ownerID)) {
                return false;
            }
            return true;
        }
        isTurretReloaded(object, tick = 1) {
            const turret = this.reloadingTurrets.get(object.id);
            if (turret === void 0) {
                return true;
            }
            return turret.reload > turret.maxReload - tick;
        }
        postTick() {
            for (const [id, turret] of this.reloadingTurrets) {
                turret.reload += 1;
                if (turret.reload >= turret.maxReload) {
                    turret.reload = turret.maxReload;
                    this.reloadingTurrets.delete(id);
                }
            }
        }
        canPlaceItem(id, position, addRadius = 0) {
            if (id !== 18 && pointInRiver(position)) {
                return false;
            }
            const item = Items[id];
            return !this.grid2D.query(position.x, position.y, 1, id2 => {
                const object = this.objects.get(id2);
                const scale = item.scale + object.placementScale + addRadius;
                if (position.distance(object.pos.current) < scale) {
                    return true;
                }
            });
        }
        inPlacementRange(object) {
            const owner = this.client.PlayerManager.playerData.get(object.ownerID);
            if (owner === void 0 || !this.client.PlayerManager.players.includes(owner)) {
                return false;
            }
            const {previous: a0, current: a1, future: a2} = owner.pos;
            const b0 = object.pos.current;
            const item = Items[object.type];
            const range = owner.scale * 2 + item.scale + item.placeOffset;
            return a0.distance(b0) <= range || a1.distance(b0) <= range || a2.distance(b0) <= range;
        }
        getBestPlacementAngles(options) {
            const {position: position, id: id, targetAngle: targetAngle, ignoreID: ignoreID, reduce: reduce, preplace: preplace, fill: fill} = options;
            const item = DataHandler_default.getItem(id);
            const {myPlayer: myPlayer, _ModuleHandler: ModuleHandler} = this.client;
            const length = myPlayer.getItemPlaceScale(id);
            const angles = [];
            this.grid2D.query(position.x, position.y, 1, id2 => {
                const object = this.objects.get(id2);
                if (ignoreID !== null && ignoreID === object.id) {
                    return;
                }
                const pos1 = object.pos.current;
                const angle = position.angle(pos1);
                const a = object.placementScale + item.scale + 1;
                const b = position.distance(pos1);
                const c = length;
                const cosArg = (b * b + c * c - a * a) / (2 * b * c);
                if (cosArg < -1) {
                    angles.push([ angle, Math.PI ]);
                } else if (cosArg <= 1) {
                    const offset = Math.acos(cosArg);
                    angles.push([ angle, offset ]);
                }
            });
            const finalAngles = findPlacementAngles(angles);
            const targetAngleOverlaps = angles.some(([angle, offset]) => getAngleDist(targetAngle, angle) <= offset);
            if (!targetAngleOverlaps) {
                finalAngles.push(targetAngle);
                if (finalAngles.length === 1 && fill) {
                    if (item.itemType === 4) {
                        return [];
                    }
                    const offset = Math.asin((2 * item.scale + 1) / (2 * length)) * 2;
                    finalAngles.push(targetAngle - offset);
                    finalAngles.push(targetAngle + offset);
                    finalAngles.push(reverseAngle(targetAngle));
                    return finalAngles.slice(0, Settings_default._placeAttempts);
                }
            }
            let anglesSorted = finalAngles.sort(Sorting_default.byAngleDistance(targetAngle));
            if (reduce) {
                if (!DataHandler_default.canMoveOnTop(id) && ModuleHandler.move_dir !== null && myPlayer.speed !== 0) {
                    const scale = item.scale;
                    const offset = Math.asin(2 * scale / (2 * length));
                    anglesSorted = anglesSorted.filter(angle => getAngleDist(angle, ModuleHandler.move_dir) > offset);
                }
                return anglesSorted.slice(0, Settings_default._placeAttempts);
            }
            return anglesSorted;
        }
    }

    const ObjectManager_default = ObjectManager;

    const MAX_U32 = 4294967295;

    const NEG_ONE = -1;

    const textEncoder = new TextEncoder;

    const textDecoder = new TextDecoder;

    class Msgpack {
        encPos=0;
        encView=new DataView(new ArrayBuffer(2048));
        encBytes=new Uint8Array(this.encView.buffer);
        decPos=0;
        decBytes=new Uint8Array(0);
        decView=new DataView(this.decBytes.buffer);
        headByte=NEG_ONE;
        stack=[];
        maxStrLength=MAX_U32;
        maxBinLength=MAX_U32;
        maxArrayLength=MAX_U32;
        maxMapLength=MAX_U32;
        encode(value) {
            this.encPos = 0;
            this.doEncode(value, 1);
            return this.encBytes.slice(0, this.encPos);
        }
        doEncode(value, depth) {
            if (value === null || value === void 0) {
                return this.encodeNil();
            }
            switch (typeof value) {
              case "boolean":
                return this.encodeBoolean(value);

              case "number":
                return this.encodeNumber(value);

              case "string":
                return this.encodeString(value);

              case "object":
                return this.encodeObject(value, depth);

              default:
                throw Error("Unsupported type: " + typeof value);
            }
        }
        encodeNil() {
            this.writeU8(192);
        }
        encodeBoolean(val) {
            this.writeU8(val ? 195 : 194);
        }
        encodeNumber(val) {
            if (Number.isSafeInteger(val)) {
                if (val >= 0) {
                    if (val < 128) {
                        return this.writeU8(val);
                    }
                    if (val < 256) {
                        return this.writeU8(204), this.writeU8(val);
                    }
                    if (val < 65536) {
                        return this.writeU8(205), this.writeU16(val);
                    }
                    if (val <= MAX_U32) return this.writeU8(206), this.writeU32(val);
                    return this.writeU8(203), this.writeF64(val);
                }
                if (val >= -32) {
                    return this.writeU8(224 | val + 32);
                }
                if (val >= -32768) return this.writeU8(209), this.writeI16(val);
                return this.writeU8(203), this.writeF64(val);
            }
            this.writeU8(203);
            this.writeF64(val);
        }
        encodeString(val) {
            const byteLen = utf8ByteLength(val);
            this.ensureCapacity(5 + byteLen);
            this.writeStringHeader(byteLen);
            textEncoder.encodeInto(val, this.encBytes.subarray(this.encPos));
            this.encPos += byteLen;
        }
        writeStringHeader(len) {
            if (len < 32) {
                this.writeU8(160 + len);
            } else if (len < 256) {
                this.writeU8(217); this.writeU8(len);
            } else if (len < 65536) {
                this.writeU8(218); this.writeU16(len);
            } else {
                this.writeU8(219); this.writeU32(len);
            }
        }
        encodeObject(val, depth) {
            if (Array.isArray(val)) {
                return this.encodeArray(val, depth);
            }
            return this.encodeMap(val, depth);
        }
        encodeArray(arr, depth) {
            const len = arr.length;
            if (len < 16) this.writeU8(144 + len);
            else if (len < 65536) { this.writeU8(220); this.writeU16(len); }
            else { this.writeU8(221); this.writeU32(len); }
            for (const item of arr) {
                this.doEncode(item, depth + 1);
            }
        }
        encodeMap(obj, depth) {
            const keys = Object.keys(obj);
            if (keys.length < 16) this.writeU8(128 + keys.length);
            else if (keys.length < 65536) { this.writeU8(222); this.writeU16(keys.length); }
            else { this.writeU8(223); this.writeU32(keys.length); }
            for (const key of keys) {
                this.encodeString(key);
                this.doEncode(obj[key], depth + 1);
            }
        }
        ensureCapacity(needed) {
            const required = this.encPos + needed;
            if (this.encView.byteLength < required) {
                this.resize(required * 2);
            }
        }
        resize(newSize) {
            const buf = new ArrayBuffer(newSize);
            const bytes = new Uint8Array(buf);
            bytes.set(this.encBytes);
            this.encView = new DataView(buf);
            this.encBytes = bytes;
        }
        writeU8(val) {
            this.ensureCapacity(1);
            this.encView.setUint8(this.encPos, val);
            this.encPos += 1;
        }
        writeU16(val) {
            this.ensureCapacity(2);
            this.encView.setUint16(this.encPos, val);
            this.encPos += 2;
        }
        writeU32(val) {
            this.ensureCapacity(4);
            this.encView.setUint32(this.encPos, val);
            this.encPos += 4;
        }
        writeI16(val) {
            this.ensureCapacity(2);
            this.encView.setInt16(this.encPos, val);
            this.encPos += 2;
        }
        writeF64(val) {
            this.ensureCapacity(8);
            this.encView.setFloat64(this.encPos, val);
            this.encPos += 8;
        }
        decode(data) {
            this.decBytes = data instanceof Uint8Array ? data : new Uint8Array(data);
            this.decView = new DataView(this.decBytes.buffer, this.decBytes.byteOffset, this.decBytes.byteLength);
            this.decPos = 0;
            this.headByte = NEG_ONE;
            this.stack.length = 0;
            return this.decodeSync();
        }
        decodeSync() {
            outer: for (;;) {
                const type = this.readHeadByte();
                let value;
                if (type >= 224) {
                    value = type - 256;
                } else if (type < 128) {
                    value = type;
                } else if (type < 144) {
                    const count = type - 128;
                    if (count === 0) {
                        value = {};
                    } else {
                        this.pushMapFrame(count);
                        this.complete();
                        continue outer;
                    }
                } else if (type < 160) {
                    const count = type - 144;
                    if (count === 0) {
                        value = [];
                    } else {
                        this.pushArrayFrame(count);
                        this.complete();
                        continue outer;
                    }
                } else if (type < 192) {
                    value = this.decodeUtf8(type - 160, 0);
                } else if (type === 192) {
                    value = null;
                } else if (type === 194) {
                    value = false;
                } else if (type === 195) {
                    value = true;
                } else if (type === 202) {
                    value = this.readF32();
                } else if (type === 203) {
                    value = this.readF64();
                } else if (type === 204) {
                    value = this.readU8();
                } else if (type === 205) {
                    value = this.readU16();
                } else if (type === 206) {
                    value = this.readU32();
                } else if (type === 207) {
                    value = readU64(this.decView, this.decPos), this.decPos += 8;
                } else if (type === 208) {
                    value = this.readI8();
                } else if (type === 209) {
                    value = this.readI16();
                } else if (type === 210) {
                    value = this.readI32();
                } else if (type === 211) {
                    value = readI64(this.decView, this.decPos), this.decPos += 8;
                } else if (type === 217) {
                    value = this.decodeUtf8(this.lookU8(), 1);
                } else if (type === 218) {
                    value = this.decodeUtf8(this.lookU16(), 2);
                } else if (type === 219) {
                    value = this.decodeUtf8(this.lookU32(), 4);
                } else if (type === 220) {
                    const count = this.readU16();
                    if (count === 0) {
                        value = [];
                    } else {
                        this.pushArrayFrame(count);
                        this.complete();
                        continue outer;
                    }
                } else if (type === 221) {
                    const count = this.readU32();
                    if (count === 0) {
                        value = [];
                    } else {
                        this.pushArrayFrame(count);
                        this.complete();
                        continue outer;
                    }
                } else if (type === 222) {
                    const count = this.readU16();
                    if (count === 0) {
                        value = {};
                    } else {
                        this.pushMapFrame(count);
                        this.complete();
                        continue outer;
                    }
                } else if (type === 223) {
                    const count = this.readU32();
                    if (count === 0) {
                        value = {};
                    } else {
                        this.pushMapFrame(count);
                        this.complete();
                        continue outer;
                    }
                } else if (type === 196) {
                    value = this.decodeBinary(this.lookU8(), 1);
                } else if (type === 197) {
                    value = this.decodeBinary(this.lookU16(), 2);
                } else if (type === 198) {
                    value = this.decodeBinary(this.lookU32(), 4);
                } else {
                    throw Error("Unrecognized msgpack type byte: 0x" + type.toString(16));
                }
                this.complete();
                while (this.stack.length > 0) {
                    const frame = this.stack[this.stack.length - 1];
                    if (frame.type === 0) {
                        frame.array[frame.position] = value;
                        frame.position++;
                        if (frame.position === frame.size) {
                            this.stack.pop();
                            value = frame.array;
                        } else {
                            continue outer;
                        }
                    } else if (frame.type === 1) {
                        if (!isPrimitive(value)) {
                            throw Error("Map key must be string or number");
                        }
                        if (value === "__proto__") {
                            throw Error("__proto__ key is not allowed");
                        }
                        frame.key = value;
                        frame.type = 2;
                        continue outer;
                    } else {
                        frame.map[frame.key] = value;
                        frame.readCount++;
                        if (frame.readCount === frame.size) {
                            this.stack.pop();
                            value = frame.map;
                        } else {
                            frame.key = null;
                            frame.type = 1;
                            continue outer;
                        }
                    }
                }
                return value;
            }
        }
        pushArrayFrame(size) {
            if (size > this.maxArrayLength) {
                throw Error("array too long");
            }
            this.stack.push({
                type: 0,
                size: size,
                array: Array(size),
                position: 0
            });
        }
        pushMapFrame(size) {
            if (size > this.maxMapLength) {
                throw Error("map too long");
            }
            this.stack.push({
                type: 1,
                size: size,
                key: null,
                readCount: 0,
                map: {}
            });
        }
        readHeadByte() {
            if (this.headByte === NEG_ONE) {
                this.headByte = this.readU8();
            }
            return this.headByte;
        }
        complete() {
            this.headByte = NEG_ONE;
        }
        readU8() {
            return this.decView.getUint8(this.decPos++);
        }
        readI8() {
            return this.decView.getInt8(this.decPos++);
        }
        readU16() {
            const v = this.decView.getUint16(this.decPos);
            this.decPos += 2;
            return v;
        }
        readI16() {
            const v = this.decView.getInt16(this.decPos);
            this.decPos += 2;
            return v;
        }
        readU32() {
            const v = this.decView.getUint32(this.decPos);
            this.decPos += 4;
            return v;
        }
        readI32() {
            const v = this.decView.getInt32(this.decPos);
            this.decPos += 4;
            return v;
        }
        readF32() {
            const v = this.decView.getFloat32(this.decPos);
            this.decPos += 4;
            return v;
        }
        readF64() {
            const v = this.decView.getFloat64(this.decPos);
            this.decPos += 8;
            return v;
        }
        lookU8() {
            return this.decView.getUint8(this.decPos);
        }
        lookU16() {
            return this.decView.getUint16(this.decPos);
        }
        lookU32() {
            return this.decView.getUint32(this.decPos);
        }
        decodeUtf8(byteLen, headerLen) {
            if (byteLen > this.maxStrLength) {
                throw Error("string too long");
            }
            if (this.decBytes.byteLength < this.decPos + headerLen + byteLen) {
                throw new RangeError("Insufficient data");
            }
            const start = this.decPos + headerLen;
            const str = textDecoder.decode(this.decBytes.subarray(start, start + byteLen));
            this.decPos += headerLen + byteLen;
            return str;
        }
        decodeBinary(byteLen, headerLen) {
            if (byteLen > this.maxBinLength) {
                throw Error("bin too long");
            }
            if (this.decBytes.byteLength < this.decPos + headerLen + byteLen) {
                throw new RangeError("Insufficient data");
            }
            const start = this.decPos + headerLen;
            const result = this.decBytes.subarray(start, start + byteLen);
            this.decPos += headerLen + byteLen;
            return result;
        }
    }

    class PacketManager {
        client;
        msgpack=new Msgpack;
        packetCount=0;
        constructor(client2) {
            this.client = client2;
            if (this.client.isOwner) {
                setInterval(() => {
                    GameUI_default.updatePackets(this.packetCount);
                    this.packetCount = 0;
                }, 1e3);
            }
        }
        send(data) {
            const {socket: socket, socketSend: socketSend} = this.client.SocketManager;
            if (socket === null || socket.readyState !== socket.OPEN || socketSend === null) {
                return false;
            }
            const [type, ...args] = data;
            const crypto = this.client.SocketManager._crypto;
            if (crypto !== null) {
                const encodedOpcode = crypto.tables.c2s.enc[type];
                if (encodedOpcode === void 0) {
                    return false;
                }
                const sequence = crypto.next();
                const payload = this.msgpack.encode([ encodedOpcode, args, sequence ]);
                const mac = crypto.sign(payload);
                const packet = new Uint8Array(mac.length + payload.length);
                packet.set(mac, 0);
                packet.set(payload, mac.length);
                socketSend(packet);
            } else {
                const encoded = this.msgpack.encode([ type, args ]);
                socketSend(encoded);
            }
            if (this.client.isOwner) this.packetCount += 1;
            else this.client.SocketManager.recordSentPacket();
            return true;
        }
        clanRequest(id, accept) {
            this.send([ "P", id, Number(accept) ]);
        }
        kick(id) {
            this.send([ "Q", id ]);
        }
        joinClan(name) {
            this.send([ "b", name ]);
        }
        createClan(name) {
            this.send([ "L", name ]);
        }
        leaveClan() {
            this.client.myPlayer.joinRequests.length = 0;
            this.send([ "N" ]);
        }
        equip(type, id) {
            this.send([ "c", 0, id, type ]);
        }
        buy(type, id) {
            this.send([ "c", 1, id, type ]);
        }
        chat(message) {
            const ok = this.send([ "6", message ]);
            if (ok && this.client.isOwner && Settings_default._botChatEcho) {
                const text = String(message || "").slice(0, 30);
                if (text) {
                    for (const bot of this.client.clients) {
                        if (!bot?.myPlayer?.inGame || bot.crossServer || bot.disconnectRequested) continue;
                        if (bot.SocketManager?.socket?.readyState !== 1) continue;
                        try { bot.PacketManager.send([ "6", text ]); } catch (_) {}
                    }
                }
            }
            return ok;
        }
        attack(angle) {
            return this.send([ "F", 1, angle ]);
        }
        stopAttack() {
            this.send([ "F", 0, null ]);
        }
        resetMoveDir() {
            this.send([ "e" ]);
        }
        move(angle) {
            this.send([ "9", angle ]);
        }
        autoAttack() {
            this.send([ "K", 1 ]);
        }
        lockRotation() {
            this.send([ "K", 0 ]);
        }
        pingMap() {
            this.send([ "S" ]);
        }
        selectItemByID(id, type) {
            return this.send([ "z", id, type ]);
        }
        spawn(name, moofoll, skin) {
            this.send([ "M", {
                name: name,
                moofoll: moofoll,
                skin: skin
            } ]);
        }
        upgradeItem(id) {
            this.send([ "H", id ]);
        }
        updateAngle(radians) {
            this.send([ "D", radians ]);
        }
        pingRequest() {
            this.client.SocketManager.startPing = performance.now();
            this.send([ "0" ]);
        }
    }

    class Animal extends Entity_default {
        type;
        prevHealth=0;
        currentHealth=0;
        receivedDamage=0;
        maxHealth=0;
        isDanger=false;
        isHostile=false;
        isPlayer=false;
        constructor(client2) {
            super(client2);
        }
        canBeTrapped() {
            return !("noTrap" in Animals_default[this.type]);
        }
        update(id, type, x, y, angle, health, nameIndex) {
            this.id = id;
            this.type = type;
            this.pos.previous.setVec(this.pos.current);
            this.pos.current._setXY(x, y);
            this.setFuturePosition();
            const animal = Animals_default[type];
            this.angle = angle;
            this.prevHealth = this.currentHealth;
            this.currentHealth = health;
            this.maxHealth = animal.health;
            this.scale = animal.scale;
            const isHostile = animal.hostile && type !== 7;
            this.isHostile = animal.hostile;
            this.isDanger = isHostile;
            this.receivedDamage = 0;
            const difference = Math.abs(this.currentHealth - this.prevHealth);
            if (this.currentHealth < this.prevHealth) {
                this.receivedDamage = difference;
            }
        }
        get attackRange() {
            if (this.type === 6) {
                return Animals_default[this.type].hitRange + Config_default.playerScale;
            }
            return this.scale;
        }
        get collisionRange() {
            if (this.type === 6) {
                return Animals_default[this.type].hitRange + Config_default.playerScale;
            }
            return this.scale + 60;
        }
        get canUseTurret() {
            return this.isHostile;
        }
    }

    const Animal_default = Animal;

    class MovementSimulation {
        speed=Config_default.playerSpeed;
        scale=35;
        slowMult=1;
        xVel=0;
        yVel=0;
        x=0;
        y=0;
        lockMove=false;
        TICK=1e3 / 9;
        spikeCollision=false;
        reset(client2, dir = null) {
            this.slowMult = 1;
            this.xVel = 0;
            this.yVel = 0;
            const speed = client2.myPlayer.speed / this.TICK;
            const moveDir = dir ?? client2._ModuleHandler.move_dir;
            if (moveDir !== null) {
                this.xVel = Math.cos(moveDir) * speed;
                this.yVel = Math.sin(moveDir) * speed;
            }
            const pos = client2.myPlayer.pos.current;
            this.x = pos.x;
            this.y = pos.y;
            this.lockMove = false;
            this.spikeCollision = false;
        }
        getPos() {
            return new Vector_default(this.x, this.y);
        }
        getSpeed() {
            return new Vector_default(this.xVel, this.yVel).length * this.TICK;
        }
        checkCollision(player, target, delta, isEnemyObject) {
            delta = delta || 1;
            const pos1 = this.getPos();
            const pos2 = target.pos.current.copy();
            const distance = pos1.distance(pos2);
            const collisionRange = player.collisionScale + target.collisionScale + 5;
            if (distance > collisionRange) {
                return false;
            }
            const scale = player.collisionScale + target.collisionScale;
            const isPlayer = target instanceof Player_default;
            if (isPlayer || !target.canMoveOnTop()) {
                const tmpDir = getAngle(pos2.x, pos2.y, pos1.x, pos1.y);
                if (isPlayer) {
                    const tmpInt = (distance - scale) * -1 / 2;
                    this.x += tmpInt * Math.cos(tmpDir);
                    this.y += tmpInt * Math.sin(tmpDir);
                } else {
                    this.x = pos2.x + collisionRange * Math.cos(tmpDir);
                    this.y = pos2.y + collisionRange * Math.sin(tmpDir);
                    this.xVel *= .75;
                    this.yVel *= .75;
                }
                if (target instanceof PlayerObject && target.type === 22 && isEnemyObject) this.spikeCollision = true;
                if (target instanceof Resource && target.isCactus || target instanceof PlayerObject && target.isSpike && isEnemyObject) {
                    const tmpSpd = 1.5;
                    this.xVel += tmpSpd * Math.cos(tmpDir);
                    this.yVel += tmpSpd * Math.sin(tmpDir);
                    this.spikeCollision = true;
                }
            } else if (target.type === 15 && isEnemyObject) {
                this.lockMove = true;
            } else if (target.type === 16) {
                const data = Items[target.type];
                const weight = 1;
                this.xVel += delta * data.boostSpeed * weight * Math.cos(target.angle);
                this.yVel += delta * data.boostSpeed * weight * Math.sin(target.angle);
            }
            return true;
        }
        collisionSimulation(client2) {
            this.reset(client2);
            if (!Settings_default._safeWalk) {
                return false;
            }
            this.update(client2, false);
            if (this.spikeCollision) {
                return true;
            }
            this.update(client2, true);
            return this.spikeCollision;
        }
        update(client2, notMoving) {
            const delta = 1e3 / 9;
            if (this.slowMult < 1) {
                this.slowMult = Math.min(1, this.slowMult + 8e-4 * delta);
            }
            const {_ModuleHandler: ModuleHandler, myPlayer: myPlayer} = client2;
            const {autoHat: autoHat} = ModuleHandler.staticModules;
            const pos = this.getPos();
            const skin = Hats[autoHat.getNextHat()];
            const tail = Accessories[autoHat.getNextAcc()];
            const weapon = DataHandler_default.getWeapon(autoHat.getNextWeaponID());
            const weaponSpd = weapon.spdMult || 1;
            const skinSpd = "spdMult" in skin ? skin.spdMult : 1;
            const tailSpd = "spdMult" in tail ? tail.spdMult : 1;
            const inSnow = pos.y <= Config_default.snowBiomeTop && !("coldM" in skin);
            const snowMult = inSnow ? Config_default.snowSpeed : 1;
            const buildMult = autoHat.getNextItemID() >= 0 ? .5 : 1;
            if (this.lockMove) {
                this.xVel = 0;
                this.yVel = 0;
            } else {
                let spdMult = buildMult * weaponSpd * skinSpd * tailSpd * snowMult * this.slowMult;
                const riverMin = Config_default.mapScale / 2 - Config_default.riverWidth / 2;
                const riverMax = Config_default.mapScale / 2 + Config_default.riverWidth / 2;
                const inRiver = !myPlayer.onPlatform && pos.y >= riverMin && pos.y <= riverMax;
                if (inRiver) {
                    if ("watrImm" in skin) {
                        spdMult *= .75;
                        this.xVel += Config_default.waterCurrent * .4 * delta;
                    } else {
                        spdMult *= .33;
                        this.xVel += Config_default.waterCurrent * delta;
                    }
                }
                const moveDir = client2._ModuleHandler.move_dir;
                let xDir = !notMoving && moveDir !== null ? Math.cos(moveDir) : 0;
                let yDir = !notMoving && moveDir !== null ? Math.sin(moveDir) : 0;
                const len = Math.sqrt(xDir * xDir + yDir * yDir);
                if (len !== 0) {
                    xDir /= len;
                    yDir /= len;
                }
                const accel = this.speed * spdMult * delta;
                if (xDir) {
                    this.xVel += xDir * accel;
                }
                if (yDir) {
                    this.yVel += yDir * accel;
                }
            }
            this.lockMove = false;
            const moveDist = getDistance(0, 0, this.xVel * delta, this.yVel * delta);
            const depth = Math.min(4, Math.max(1, Math.round(moveDist / 40)));
            const stepMult = 1 / depth;
            for (let i = 0; i < depth; i++) {
                if (this.xVel) {
                    this.x += this.xVel * delta * stepMult;
                }
                if (this.yVel) {
                    this.y += this.yVel * delta * stepMult;
                }
                client2.ObjectManager.grid2D.query(this.x, this.y, 1, id => {
                    const object = client2.ObjectManager.objects.get(id);
                    const isPlayerObject = object instanceof PlayerObject;
                    const isEnemyObject = !isPlayerObject || client2.PlayerManager.isEnemyByID(object.ownerID, client2.myPlayer);
                    this.checkCollision(myPlayer, object, stepMult, isEnemyObject);
                });
            }
            const nearestEnemy = client2.EnemyManager.nearestEnemy;
            if (nearestEnemy !== null) {
                this.checkCollision(myPlayer, nearestEnemy, 1, false);
            }
            if (this.xVel) {
                this.xVel *= Math.pow(Config_default.playerDecel, delta);
                if (this.xVel >= -.01 && this.xVel <= .01) {
                    this.xVel = 0;
                }
            }
            if (this.yVel) {
                this.yVel *= Math.pow(Config_default.playerDecel, delta);
                if (this.yVel >= -.01 && this.yVel <= .01) {
                    this.yVel = 0;
                }
            }
            this.x = clamp(this.x, this.scale, Config_default.mapScale - this.scale);
            this.y = clamp(this.y, this.scale, Config_default.mapScale - this.scale);
        }
    }

    class ClientPlayer extends Player_default {
        inventory={};
        weaponXP=[ {}, {} ];
        itemCount=new Map;
        resources={};
        tempGold=0;
        deathPosition=new Vector_default;
        teleportPos=new Vector_default;
        teleported=false;
        inGame=false;
        wasDead=true;
        diedOnce=false;
        teammates=new Set;
        totalGoldAmount=0;
        age=1;
        upgradeAge=1;
        prevKills=0;
        underTurretAttack=false;
        upgradeOrder=[];
        upgradeIndex=0;
        joinRequests=[];
        killedSomeone=false;
        actuallyKilledSomeone=false;
        totalKills=0;
        deaths=0;
        simulation=new MovementSimulation;
        constructor(client2) {
            super(client2);
            this.reset(true);
        }
        isMyPlayerByID(id) {
            return id === this.id;
        }
        isTeammateByID(id) {
            return this.teammates.has(id);
        }
        isEnemyByID(id) {
            return !this.isMyPlayerByID(id) && !this.isTeammateByID(id);
        }
        get isSandbox() {
            if (this.client.crossServer) return this.client.crossServer.mode === "sandbox";
            return /sandbox/.test(location.hostname) || this.client.SocketManager.isSandbox;
        }
        getItemByType(type) {
            return this.inventory[type];
        }
        hasResourcesForType(type) {
            if (this.isSandbox) {
                return true;
            }
            const res = this.resources;
            const {food: food, wood: wood, stone: stone, gold: gold} = Items[this.getItemByType(type)].cost;
            return res.food >= food && res.wood >= wood && res.stone >= stone && res.gold >= gold;
        }
        getItemCount(group) {
            const item = ItemGroups[group];
            return {
                count: this.itemCount.get(group) || 0,
                limit: this.isSandbox ? "sandboxLimit" in item ? item.sandboxLimit : 99 : item.limit
            };
        }
        hasItemCountForType(type) {
            if (type === 2) {
                return true;
            }
            const item = Items[this.getItemByType(type)];
            const {count: count, limit: limit} = this.getItemCount(item.itemGroup);
            return count < limit;
        }
        canPlace(type) {
            return type !== null && this.getItemByType(type) !== null && this.hasResourcesForType(type) && this.hasItemCountForType(type);
        }
        canPlaceObject(type, angle) {
            const {myPlayer: myPlayer, ObjectManager: ObjectManager2} = this.client;
            const id = myPlayer.getItemByType(type);
            const current = myPlayer.getPlacePosition(myPlayer.pos.current, id, angle);
            return ObjectManager2.canPlaceItem(id, current);
        }
        getBestDestroyingWeapon(target = null) {
            const primaryID = this.getItemByType(0);
            const primary = DataHandler_default.getWeapon(primaryID);
            const secondaryID = this.getItemByType(1);
            const isHammer = secondaryID === 10;
            const notStick = primary.damage !== 1;
            const notPolearm = primaryID !== 5;
            const {reloading: reloading} = this.client._ModuleHandler.staticModules;
            const primaryDamage = this.getBuildingDamage(primaryID, false);
            if (isHammer && notStick && notPolearm && (!reloading.isReloaded(1) || reloading.isFasterThan(0, 1)) && reloading.isReloaded(0) && target != null && primaryDamage >= target.health) {
                return 0;
            }
            if (target != null && isHammer && notStick && notPolearm && this.isTrapped) {
                const hammerRange = DataHandler_default.getWeapon(secondaryID).range + target.hitScale + 1;
                const primaryRange = primary.range + target.hitScale;
                const pos1 = this.pos.current;
                const pos2 = target.pos.current;
                const distance = pos1.distance(pos2);
                if (inRange(distance, hammerRange, primaryRange)) {
                    return 0;
                }
            }
            if (isHammer) {
                return 1;
            }
            if (notStick) {
                return 0;
            }
            return null;
        }
        getWeaponRangeByType(type) {
            const item = this.getItemByType(type);
            if (DataHandler_default.isMelee(item)) {
                return DataHandler_default.getWeapon(item).range;
            }
            return 0;
        }
        getFastestWeapon() {
            const primary = DataHandler_default.getWeapon(this.getItemByType(0));
            const secondaryID = this.getItemByType(1);
            if (secondaryID === null) {
                return 0;
            }
            const secondary = DataHandler_default.getWeapon(secondaryID);
            if (primary.spdMult > secondary.spdMult) {
                return 0;
            }
            return 1;
        }
        getDmgOverTime() {
            const hat = Hats[this.hatID];
            const accessory = Accessories[this.accessoryID];
            let damage = 0;
            if ("healthRegen" in hat) {
                damage += hat.healthRegen;
            }
            if ("healthRegen" in accessory) {
                damage += accessory.healthRegen;
            }
            if (this.poisonCount !== 0) {
                damage += -5;
            }
            return Math.abs(damage);
        }
        getMaxWeaponRangeClient() {
            const primary = this.inventory[0];
            const secondary = this.inventory[1];
            const primaryRange = DataHandler_default.getWeapon(primary).range;
            if (DataHandler_default.isMelee(secondary)) {
                const range = DataHandler_default.getWeapon(secondary).range;
                if (range > primaryRange) {
                    return range;
                }
            }
            return primaryRange;
        }
        getMaxRangeTypeDestroy() {
            const primaryID = this.inventory[0];
            const secondaryID = this.inventory[1];
            const primary = DataHandler_default.getWeapon(primaryID);
            if (DataHandler_default.isMelee(secondaryID)) {
                const secondary = DataHandler_default.getWeapon(secondaryID);
                if (secondaryID === 10 && secondary.range > primary.range) {
                    return {
                        type: 1,
                        range: secondary.range
                    };
                }
            }
            if (primaryID !== 8) {
                return {
                    type: 0,
                    range: primary.range
                };
            }
            return null;
        }
        getPlacePosition(start, itemID, angle) {
            return start.addDirection(angle, this.getItemPlaceScale(itemID));
        }
        tickUpdate() {
            if (this.inGame && this.wasDead) {
                this.wasDead = false;
                this.prevKills = 0;
                this.onFirstTickAfterSpawn();
            }
            const {_ModuleHandler: ModuleHandler, PlayerManager: PlayerManager} = this.client;
            this.killedSomeone = false;
            this.actuallyKilledSomeone = false;
            if (this.totalKills > this.prevKills) {
                this.prevKills = this.totalKills;
                this.killedSomeone = true;
                if (PlayerManager.prevPlayers.size !== 0) {
                    this.actuallyKilledSomeone = true;
                }
            }
            ModuleHandler.postTick();
        }
        updateHealth(health) {
            if (!this.inGame) {
                return;
            }
            super.updateHealth(health);
            this.client._ModuleHandler.staticModules.antiInsta.healthUpdate(this.previousHealth, health);
            if (this.shameActive) {
                return;
            }
            if (health < 100) {
                const {_ModuleHandler: ModuleHandler} = this.client;
                ModuleHandler.staticModules.shameReset.healthUpdate();
            }
        }
        playerInit(id) {
            this.id = id;
            const {PlayerManager: PlayerManager} = this.client;
            if (!PlayerManager.playerData.has(id)) {
                PlayerManager.playerData.set(id, this);
            }
        }
        onFirstTickAfterSpawn() {
            if (this.client.crossServer) { CrossServerBots.connections.render(); return; }
            const {_ModuleHandler: ModuleHandler, isOwner: isOwner} = this.client;
            const {mouse: mouse, staticModules: staticModules} = ModuleHandler;
            ModuleHandler._equip(0, 0);
            ModuleHandler.updateAngle(mouse.sentAngle, true);
            if (!isOwner) {
                const owner = this.client.ownerClient;
                ExtraBotConnections.render();
                owner.clientIDList.add(this.id);
                if (Settings_default._botSync) {
                    ModuleHandler.toggleAutoattack(owner._ModuleHandler.autoattack);
                    staticModules.tempData.setAttacking(owner._ModuleHandler.attacking);
                }
                staticModules.tempData.setStore(0, owner._ModuleHandler.store[0].actual);
                staticModules.tempData.setStore(1, owner._ModuleHandler.store[1].actual);
            }
        }
        playerSpawn() {
            this.inGame = true;
        }
        isUpgradeWeapon(id) {
            const weapon = DataHandler_default.getWeapon(id);
            if ("upgradeOf" in weapon) {
                return this.inventory[weapon.itemType] === weapon.upgradeOf;
            }
            return true;
        }
        newUpgrade(points, age) {
            this.pendingLoadoutUpgrade = null;
            this.upgradeAge = age;
            if (points === 0 || age === 10) {
                return;
            }
            const ids = [];
            for (const weapon of Weapons) {
                if (weapon.age === age && this.isUpgradeWeapon(weapon.id)) {
                    ids.push(weapon.id);
                }
            }
            for (const item of Items) {
                if (item.age === age) {
                    ids.push(item.id + 16);
                }
            }
            if (!this.client.isOwner) {
                this.pendingLoadoutUpgrade = {ids, age};
                BotLoadout.applyPending(this.client);
            }
        }
        updateAge(age) {
            this.age = age;
        }
        upgradeItem(id) {
            this.upgradeOrder.push(id);
            const {isOwner: isOwner, clients: clients} = this.client;
            if (isOwner) {
                for (const client2 of clients) {
                    BotLoadout.applyPending(client2);
                }
            }
            if (id < 16) {
                const weapon = DataHandler_default.getWeapon(id);
                this.inventory[weapon.itemType] = id;
                const XP = this.weaponXP[weapon.itemType];
                XP.current = 0;
                XP.max = -1;
            } else {
                id -= 16;
                const item = Items[id];
                this.inventory[item.itemType] = id;
            }
            this.upgradeAge += 1;
        }
        updateClanMembers(teammates) {
            this.teammates.clear();
            for (let i = 0; i < teammates.length; i += 2) {
                const id = teammates[i + 0];
                if (!this.isMyPlayerByID(id)) {
                    this.teammates.add(id);
                }
            }
        }
        updateItemCount(group, count) {
            this.itemCount.set(group, count);
            if (this.client.isOwner) {
                GameUI_default.updateItemCount(group);
            }
        }
        updateResources(type, amount, killReceipt = null) {
            const previousAmount = this.resources[type];
            this.resources[type] = amount;
            if (type === "gold") {
                this.tempGold = amount;
                return;
            }
            if (amount < previousAmount) {
                return;
            }
            const difference = amount - previousAmount;
            if (type === "kills") {
                this.totalKills += difference;
                this.client.StatsManager.kills = difference;
                this.client.StatsManager.totalKills = difference;
                if (!this.client.crossServer) this.client.ownerClient.StatsManager.globalKills = difference;
                if (this.client.isOwner) {
                    GameUI_default.updateTotalKills(this.totalKills);
                } else {
                    GameUI_default.addBotKills(this.client, difference, killReceipt);
                }
                return;
            }
            this.updateWeaponXP(difference);
        }
        updateWeaponXP(amount) {
            const {next: next} = this.getWeaponVariant(this.weapon.current);
            const XP = this.weaponXP[DataHandler_default.getWeapon(this.weapon.current).itemType];
            const maxXP = WeaponVariants[next].needXP;
            XP.current += amount;
            if (XP.max !== -1 && XP.current >= XP.max) {
                XP.current -= XP.max;
                XP.max = maxXP;
                return;
            }
            if (XP.max === -1) {
                XP.max = maxXP;
            }
            if (XP.current >= XP.max) {
                XP.current -= XP.max;
                XP.max = -1;
            }
        }
        resetResources() {
            this.resources.food = 100;
            this.resources.wood = 100;
            this.resources.stone = 100;
            this.resources.gold = 100;
            this.resources.kills = 0;
        }
        resetInventory() {
            this.inventory[0] = 0;
            this.inventory[1] = null;
            this.inventory[2] = 0;
            this.inventory[3] = 3;
            this.inventory[4] = 6;
            this.inventory[5] = 10;
            this.inventory[6] = null;
            this.inventory[7] = null;
            this.inventory[8] = null;
            this.inventory[9] = null;
        }
        resetWeaponXP() {
            for (const XP of this.weaponXP) {
                XP.current = 0;
                XP.max = -1;
            }
        }
        spawn(customName) {
            const name = this.client.isOwner ? (customName || window.localStorage.getItem("moo_name") || "") : extraBotName(this.client);
            const skin = this.client.isOwner ? (Number(window.localStorage.getItem("skin_color")) || 0) : 10;
            this.client.PacketManager.spawn(name, 1, skin === 10 ? "constructor" : skin);
        }
        handleJoinRequest(id, name) {
            this.joinRequests.push([ id, name ]);
        }
        reset(first = false) {
            this.resetResources();
            this.resetInventory();
            this.resetWeaponXP();
            const {_ModuleHandler: ModuleHandler, PlayerManager: PlayerManager} = this.client;
            ModuleHandler.reset();
            this.inGame = false;
            this.wasDead = true;
            this.pendingLoadoutUpgrade = null;
            this.upgradeOrder.length = 0;
            this.upgradeIndex = 0;
            if (first) {
                return;
            }
            this.previousHealth = 100;
            this.currentHealth = 100;
            this.tempHealth = 100;
            this.shameActive = false;
            this.shameCount = 0;
            this.shameTimer = 0;
            this.deathPosition.setVec(this.pos.current);
            this.diedOnce = true;
            this.client.StatsManager.deaths = 1;
            this.deaths += 1;
            if (this.client.isOwner) {
                GameUI_default.reset();
                GameUI_default.updateTotalDeaths(this.deaths);
            }
        }
    }

    const ClientPlayer_default = ClientPlayer;

    class PlayerManager {
        playerData=new Map;
        players=[];
        enemies=[];
        prevPlayers=new Set;
        animalData=new Map;
        visibleAnimals=[];
        lastSnapshotAt = -Infinity;
        clanData=new Map;
        start=Date.now();
        step=0;
        damagesByHits=[];
        lastEnemyReceivedDamage=[ 0, 0 ];
        nearestTeammate=null;
        client;
        constructor(client2) {
            this.client = client2;
        }
        get timeSinceTick() {
            return Date.now() - this.start;
        }
        getEntity(id, isPlayer) {
            if (isPlayer && this.playerData.has(id)) {
                return this.playerData.get(id);
            } else if (!isPlayer && this.animalData.has(id)) {
                return this.animalData.get(id);
            }
            return null;
        }
        createPlayer({socketID: socketID, id: id, nickname: nickname, health: health, skinID: skinID}) {
            const {myPlayer: myPlayer} = this.client;
            if (socketID === this.client.clientID && myPlayer.id === -1) {
                myPlayer.playerInit(id);
            }
            const player = this.playerData.get(id) || new Player_default(this.client);
            if (!this.playerData.has(id)) {
                this.playerData.set(id, player);
            }
            player.id = id;
            player.prevNickname = player.nickname;
            player.nickname = nickname || "";
            player.currentHealth = health || 100;
            player.skinID = typeof skinID === "undefined" ? -1 : skinID;
            player.init();
            if (myPlayer.isMyPlayerByID(id)) {
                myPlayer.playerSpawn();
            }
            return player;
        }
        createClan(name, ownerID) {
            this.clanData.set(name, ownerID);
        }
        deleteClan(name) {
            this.clanData.delete(name);
        }
        clanExist(name) {
            return name !== null && this.clanData.has(name);
        }
        canHitTarget(player, weaponID, target) {
            const pos = target.pos.current;
            const distance = player.pos.current.distance(pos);
            const angle = player.pos.current.angle(pos);
            const range = DataHandler_default.getWeapon(weaponID).range + target.hitScale;
            return distance <= range && getAngleDist(angle, player.angle) <= Config_default.gatherAngle;
        }
        attackPlayer(id, gathering, weaponID) {
            const player = this.playerData.get(id);
            if (player === void 0) {
                return;
            }
            const {hatID: hatID, reload: reload} = player;
            const {myPlayer: myPlayer, ObjectManager: ObjectManager2} = this.client;
            player.lastAttacked = myPlayer.tickCount;
            const isMyPlayer = myPlayer.isMyPlayerByID(id);
            if (isMyPlayer && !myPlayer.inGame) {
                return;
            }
            const weapon = DataHandler_default.getWeapon(weaponID);
            const type = weapon.itemType;
            player.updateMaxReload(reload[type], weaponID);
            player.resetCurrentReload(reload[type]);
            if (myPlayer.isEnemyByID(id)) {
                if (this.canHitTarget(player, weaponID, myPlayer)) {
                    const {isAble: isAble, count: count} = player.canDealPoison(weaponID);
                    if (isAble) {
                        myPlayer.poisonCount = count;
                    }
                }
            }
            if (gathering === 1) {
                const objects = ObjectManager2.attackedObjects;
                for (const [id2, data] of objects) {
                    const [hitAngle, object] = data;
                    if (this.canHitTarget(player, weaponID, object) && getAngleDist(hitAngle, player.angle) <= 1.25) {
                        objects.delete(id2);
                        if (object instanceof PlayerObject) {
                            const damage = player.getBuildingDamage(weaponID);
                            object.health = Math.max(0, object.health - damage);
                        } else if (player === myPlayer) {
                            let amount = hatID === 9 ? 1 : 0;
                            if (object.type === 3) {
                                amount += weapon.gather + 4;
                            }
                            myPlayer.updateWeaponXP(amount);
                        }
                    }
                }
            }
        }
        updatePlayer(buffer) {
            this.lastSnapshotAt = performance.now();
            this.players.length = 0;
            this.enemies.length = 0;
            this.damagesByHits.length = 0;
            this.nearestTeammate = null;
            const now = Date.now();
            this.step = now - this.start;
            this.start = now;
            const {myPlayer: myPlayer, isOwner: isOwner, EnemyManager: EnemyManager2} = this.client;
            for (let i = 0; i < buffer.length; i += 13) {
                const id = buffer[i];
                const player = this.playerData.get(id);
                this.players.push(player);
                player.update(id, buffer[i + 1], buffer[i + 2], buffer[i + 3], buffer[i + 4], buffer[i + 5], buffer[i + 6], buffer[i + 7], buffer[i + 8], buffer[i + 9], buffer[i + 10], buffer[i + 11], buffer[i + 12]);
                const ownedBot = this.client.isBotByID(id);
                if (!ownedBot && !myPlayer.isMyPlayerByID(id) && myPlayer.isTeammateByID(id) && EnemyManager2.isNear(player, this.nearestTeammate, myPlayer)) {
                    this.nearestTeammate = player;
                } else if (!ownedBot && myPlayer.isEnemyByID(id)) {
                    this.enemies.push(player);
                }
            }
        }
        updateAnimal(buffer) {
            this.visibleAnimals.length = 0;
            const seenAt = Date.now();
            const {EnemyManager: EnemyManager2} = this.client;
            for (let i = 0; i < buffer.length; i += 7) {
                const id = buffer[i];
                if (!this.animalData.has(id)) {
                    this.animalData.set(id, new Animal_default(this.client));
                }
                const animal = this.animalData.get(id);
                animal.previousSeenAt = animal.lastSeenAt;
                animal.lastSeenAt = seenAt;
                this.visibleAnimals.push(animal);
                animal.update(id, buffer[i + 1], buffer[i + 2], buffer[i + 3], buffer[i + 4], buffer[i + 5], buffer[i + 6]);
                EnemyManager2.handleAnimal(animal);
            }
        }
        postTick() {
            const {EnemyManager: EnemyManager2, ProjectileManager: ProjectileManager, ObjectManager: ObjectManager2, myPlayer: myPlayer, isOwner: isOwner, _ModuleHandler: ModuleHandler} = this.client;
            ModuleHandler.moduleStart = performance.now();
            ProjectileManager.postTick();
            EnemyManager2.handleEnemies(this.enemies);
            ObjectManager2.postTick();
            if (myPlayer.inGame) {
                myPlayer.tickUpdate();
            }
            ObjectManager2.deletedObjects.clear();
            if ((Settings_default._autospawn || !isOwner) && !myPlayer.inGame) {
                myPlayer.spawn();
            }
        }
        isEnemy(target1, target2) {
            return target1 == null || target2 == null || target1 !== target2 && (target1.clanName === null || target2.clanName === null || target1.clanName !== target2.clanName);
        }
        isEnemyByID(ownerID, target) {
            const player = this.playerData.get(ownerID);
            if (player == null) {
                throw Error("isEnemyByID Error: Failed to find an owner!");
            }
            if (player instanceof ClientPlayer_default) {
                return player.isEnemyByID(target.id);
            }
            if (target instanceof ClientPlayer_default) {
                return target.isEnemyByID(player.id);
            }
            return this.isEnemy(player, target);
        }
        isEnemyTarget(owner, target) {
            if (target instanceof Animal_default) {
                return true;
            }
            return this.isEnemyByID(owner.id, target);
        }
        canShoot(ownerID, target) {
            return target instanceof Animal_default || this.isEnemyByID(ownerID, target);
        }
        canMoveOnTop(object) {
            if (object instanceof Resource) {
                return false;
            }
            const item = DataHandler_default.getItem(object.type);
            const isEnemyObject = this.isEnemyByID(object.ownerID, this.client.myPlayer);
            if ("ignoreCollision" in item && (object.type !== 15 || !isEnemyObject)) {
                return true;
            }
            return false;
        }
        lookingShield(owner, target) {
            if (owner instanceof Animal_default) {
                return false;
            }
            const weapon = owner.weapon.current;
            if (weapon !== 11) {
                return false;
            }
            const {myPlayer: myPlayer, _ModuleHandler: ModuleHandler} = this.client;
            const pos1 = owner.pos.current;
            const pos2 = target.pos.current;
            const angle = pos1.angle(pos2);
            const ownerAngle = myPlayer.isMyPlayerByID(owner.id) ? ModuleHandler.mouse.sentAngle : owner.angle;
            return getAngleDist(angle, ownerAngle) <= Config_default.shieldAngle;
        }
    }

    const PlayerManager_default = PlayerManager;

    class ProjectileManager {
        client;
        projectiles=new Map;
        ignoreCreation=new Map;
        dangerProjectiles=new Set;
        toRemove=new Set;
        totalDamage=0;
        constructor(client2) {
            this.client = client2;
        }
        createProjectile(projectile) {
            const key = projectile.speed;
            if (!this.projectiles.has(key)) {
                this.projectiles.set(key, []);
            }
            const list = this.projectiles.get(key);
            list.push(projectile);
        }
        foundProjectile(projectile) {
            const owner = projectile.ownerClient;
            if (owner === null) {
                return;
            }
            const {PlayerManager: PlayerManager2, myPlayer: myPlayer} = this.client;
            if (PlayerManager2.isEnemyByID(owner.id, myPlayer)) {
                const pos1 = projectile.pos.current;
                const pos2 = myPlayer.pos.current;
                const distance = pos1.distance(pos2);
                const angle = pos1.angle(pos2);
                const offset = Math.asin(2 * myPlayer.scale / (2 * distance));
                const lookingAt = getAngleDist(angle, projectile.angle) <= offset;
                if (lookingAt) {
                    this.dangerProjectiles.add(projectile);
                }
            }
        }
        foundProjectileThreat(projectile) {
            const owner = projectile.ownerClient;
            if (owner === null) {
                return;
            }
            const {PlayerManager: PlayerManager2, myPlayer: myPlayer, SocketManager: SocketManager} = this.client;
            for (const enemy of PlayerManager2.enemies) {
                if (!PlayerManager2.isEnemyByID(owner.id, enemy)) {
                    continue;
                }
                const pos1 = projectile.pos.current;
                const pos2 = enemy.pos.current;
                const distance = pos1.distance(pos2);
                const angle = pos1.angle(pos2);
                const offset = Math.asin(2 * enemy.scale / (2 * distance));
                const lookingAt = getAngleDist(angle, projectile.angle) <= offset;
                if (lookingAt) {
                    const tickDistance = Math.ceil(distance / (projectile.speed * SocketManager.TICK));
                    enemy.nextDamageTick = myPlayer.tickCount + tickDistance;
                }
            }
        }
        postTick() {
            this.projectiles.clear();
            this.totalDamage = 0;
            for (const proj of this.dangerProjectiles) {
                proj.life -= 1;
                if (proj.shouldRemove() || this.toRemove.delete(proj.id)) {
                    this.dangerProjectiles.delete(proj);
                    continue;
                }
                this.totalDamage += proj.damage;
            }
            this.toRemove.clear();
        }
    }

    const ProjectileManager_default = ProjectileManager;

    class Projectile {
        pos={};
        angle;
        range;
        speed;
        type;
        onPlatform;
        id;
        isTurret;
        scale;
        maxRange;
        damage;
        ownerClient=null;
        life=9;
        constructor(angle, range, speed, type, onPlatform, id, maxRange) {
            this.isTurret = type === 1;
            this.angle = angle;
            this.range = range;
            this.speed = speed;
            this.type = type;
            this.onPlatform = onPlatform;
            this.id = id;
            this.scale = Projectiles[type].scale;
            this.maxRange = maxRange || 0;
            this.damage = Projectiles[type].damage;
        }
        formatFromCurrent(pos, increase) {
            if (this.isTurret) {
                return pos;
            }
            return pos.addDirection(this.angle, increase ? 70 : -70);
        }
        shouldRemove() {
            return this.life <= 0;
        }
    }

    const Projectile_default = Projectile;

    const StoreHandler = new class {
        isOpened=false;
        store=[ {
            previous: -1,
            current: -1,
            list: new Map
        }, {
            previous: -1,
            current: -1,
            list: new Map
        } ];
        currentType=0;
        isRightStore(type) {
            return this.isOpened && this.currentType === type;
        }
        createStore(type) {
            const storeContainer = document.createElement("div");
            storeContainer.id = "storeContainer";
            storeContainer.style.display = "none";
            const button = document.createElement("div");
            button.id = "toggleStoreType";
            button.textContent = type === 0 ? "Hats" : "Accessories";
            button.onmousedown = () => {
                this.currentType = this.currentType === 0 ? 1 : 0;
                button.textContent = this.currentType === 0 ? "Hats" : "Accessories";
                if (this.isOpened) {
                    this.fillStore(this.currentType);
                }
            };
            storeContainer.appendChild(button);
            const itemHolder = document.createElement("div");
            itemHolder.id = "itemHolder";
            storeContainer.appendChild(itemHolder);
            itemHolder.addEventListener("wheel", event => {
                event.preventDefault();
                const scale = Math.sign(event.deltaY) * 50;
                itemHolder.scroll(0, itemHolder.scrollTop + scale);
            });
            const {gameUI: gameUI} = GameUI_default.getElements();
            gameUI.appendChild(storeContainer);
        }
        getTextEquip(type, id, price) {
            const {list: list, current: current} = this.store[type];
            if (current === id) {
                return "Unequip";
            }
            if (list.has(id) || price === 0) {
                return "Equip";
            }
            return "Buy";
        }
        generateStoreElement(type, id, name, price, isTop) {
            const srcType = [ "hats/hat", "accessories/access" ];
            const src = [ srcType[type], id ];
            if (isTop) {
                src.push("p");
            }
            const html = `\n            <div class="storeItemContainer">\n                <img class="storeHat" src="./img/${src.join("_")}.png">\n                <span class="storeItemName">${name}</span>\n                <div class="equipButton" data-id="${id}">${this.getTextEquip(type, id, price)}</div>\n            </div>\n        `;
            const div = document.createElement("div");
            div.innerHTML = html;
            const img = div.querySelector(".storeHat");
            img.src = `./img/${src.join("_")}.png`;
            const equipButton = div.querySelector(".equipButton");
            equipButton.onmousedown = () => {
                client._ModuleHandler._equip(type, id, true, true);
            };
            return div.firstElementChild;
        }
        fillStore(type) {
            const {itemHolder: itemHolder} = GameUI_default.getElements();
            itemHolder.innerHTML = "";
            const items = Settings_default._storeItems[type];
            for (const id of items) {
                const item = DataHandler_default.getStoreItem(type, id);
                const element = this.generateStoreElement(type, id, item.name, item.price, "topSprite" in item);
                itemHolder.appendChild(element);
            }
        }
        handleEquipUpdate(type, prev, curr, isBuy) {
            if (!this.isRightStore(type)) {
                return;
            }
            const current = document.querySelector(`.equipButton[data-id="${curr}"]`);
            if (current !== null) {
                current.textContent = isBuy ? "Equip" : "Unequip";
            }
            if (!isBuy && prev !== -1) {
                const previous = document.querySelector(`.equipButton[data-id="${prev}"]`);
                if (previous !== null) {
                    previous.textContent = "Equip";
                }
            }
        }
        updateStoreState(type, action, id) {
            const store2 = this.store[type];
            if (action === 0) {
                store2.previous = store2.current;
                store2.current = id;
                const {previous: previous, current: current, list: list} = store2;
                list.set(previous, 0);
                list.set(current, 1);
                this.handleEquipUpdate(type, store2.previous, id, false);
            } else {
                store2.list.set(id, 0);
                this.handleEquipUpdate(type, store2.previous, id, true);
            }
        }
        closeStore() {
            const {storeContainer: storeContainer, itemHolder: itemHolder} = GameUI_default.getElements();
            itemHolder.innerHTML = "";
            storeContainer.style.display = "none";
            this.isOpened = false;
        }
        openStore() {
            GameUI_default.closePopups();
            const {storeContainer: storeContainer} = GameUI_default.getElements();
            this.fillStore(this.currentType);
            storeContainer.style.display = "";
            storeContainer.classList.remove("closedItem");
            this.isOpened = true;
        }
        toggleStore() {
            const {storeContainer: storeContainer, itemHolder: itemHolder} = GameUI_default.getElements();
            if (this.isOpened) {
                itemHolder.innerHTML = "";
            } else {
                GameUI_default.closePopups();
                this.fillStore(this.currentType);
            }
            storeContainer.style.display = storeContainer.style.display === "none" ? "" : "none";
            this.isOpened = !this.isOpened;
        }
        init() {
            this.createStore(0);
        }
    };

    const StoreHandler_default = StoreHandler;

    const SHUFFLE_SEED = 1;

    const CLIENT_PACKET_IDS = [ "M", "D", "9", "e", "F", "z", "H", "K", "L", "N", "b", "P", "Q", "c", "6", "S", "0" ];

    const SERVER_PACKET_IDS = [ "A", "B", "C", "D", "E", "a", "G", "H", "I", "J", "K", "L", "M", "N", "O", "P", "Q", "R", "S", "T", "U", "V", "X", "Y", "Z", "g", "1", "2", "3", "4", "5", "6", "7", "8", "9", "0" ];

    const SHA256_K = new Uint32Array([ 1116352408, 1899447441, 3049323471, 3921009573, 961987163, 1508970993, 2453635748, 2870763221, 3624381080, 310598401, 607225278, 1426881987, 1925078388, 2162078206, 2614888103, 3248222580, 3835390401, 4022224774, 264347078, 604807628, 770255983, 1249150122, 1555081692, 1996064986, 2554220882, 2821834349, 2952996808, 3210313671, 3336571891, 3584528711, 113926993, 338241895, 666307205, 773529912, 1294757372, 1396182291, 1695183700, 1986661051, 2177026350, 2456956037, 2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344, 430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779, 1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298 ]);

    const BLOCK_SIZE = 64;

    class PacketCrypto {
        security_mode=1;
        key;
        tables;
        sequence=0;
        constructor(seed, key) {
            this.key = hexToBytes(key);
            this.tables = buildTables(seed);
        }
        encodeOpcode(opcode) {
            return this.tables.c2s.enc[opcode];
        }
        decodeOpcode(opcode) {
            return this.tables.s2c.dec[opcode];
        }
        next() {
            return ++this.sequence;
        }
        _syncSec(seq) {
            this.sequence = ++seq;
            return this.sequence;
        }
        sign(payload) {
            return computeHMAC(this.key, payload);
        }
    }

    const ServerCapacity = {
        connections:new WeakMap(),
        directories:new Map(),
        loading:new Map(),
        origin(socket) {
            try {
                const url = new URL(socket?.url);
                if (!['ws:', 'wss:'].includes(url.protocol) || !/^[a-z0-9-]+\.[a-z0-9-]+\.moomoo\.io$/i.test(url.hostname)) return null;
                return url.origin;
            } catch (_) { return null; }
        },
        remember(servers, type) {
            const capacities = new Map();
            for (const server of servers) {
                const origin = this.origin({url:server.address});
                if (origin && Number.isFinite(server.capacity) && server.capacity > 0) capacities.set(origin, server.capacity);
            }
            this.directories.set(type, {capacities, expiresAt:performance.now() + 300000});
        },
        watch(client, socket) {
            const type = client.crossServer?.mode || (client.myPlayer.isSandbox ? 'sandbox' : 'normal');
            const state = {socket, origin:this.origin(socket), type, capacity:null, nextCheck:0};
            this.connections.set(client, state);
            this.resolve(client, state);
            return state;
        },
        resolve(client, state) {
            if (!state.origin || state.socket?.readyState > 1) return;
            const now = performance.now(), cached = this.directories.get(state.type);
            if (cached && cached.expiresAt > now && cached.capacities.has(state.origin)) {
                state.capacity = cached.capacities.get(state.origin);
                return;
            }
            if (state.capacity !== null || now < state.nextCheck) return;
            state.nextCheck = now + 15000;
            let loading = this.loading.get(state.type);
            if (!loading) {
                loading = CrossServerBots.loadDirectory(state.type, new AbortController())
                    .catch(() => null).finally(() => {
                        if (this.loading.get(state.type) === loading) this.loading.delete(state.type);
                    });
                this.loading.set(state.type, loading);
            }
            loading.then(servers => {
                if (!servers || this.connections.get(client) !== state || client.SocketManager.socket !== state.socket || state.socket.readyState > 1) return;
                const server = servers.find(item => this.origin({url:item.address}) === state.origin);
                if (server) state.capacity = server.capacity;
            });
        },
        usesHealAcknowledgements(client) {
            const socket = client.SocketManager.socket;
            if (!socket) return false;
            let state = this.connections.get(client);
            if (!state || state.socket !== socket) state = this.watch(client, socket);
            else this.resolve(client, state);
            // Unknown servers retain native healing until capacity is confirmed.
            return state.capacity === 200;
        }
    };

    class SocketManager {
        client;
        socket=null;
        socketSend=null;
        PacketQueue=[];
        startPing=Date.now();
        _crypto=null;
        active=false;
        pong=0;
        TICK=1e3 / 9;
        packetCount=0;
        action=null;
        connectionStats = null;
        constructor(client2) {
            this.client = client2;
        }
        get isSandbox() {
            return this.socket !== null && /localhost/.test(this.socket.url);
        }
        init(socket) {
            clearTimeout(this.pingTimeout);
            this.pingTimeout = null;
            this._crypto = null;
            this.active = false;
            this.botPingWarning = false;
            this.client.disconnectRequested = false;
            if (!this.client.isOwner) {
                this.connectionStats = {startedAt:performance.now(), lastReceivedAt:null, second:-1, sent:0, peak:0};
            }
            socket.binaryType = "arraybuffer";
            this.socket = socket;
            this.socketSend = socket.send.bind(socket);
            ServerCapacity.watch(this.client, socket);
            socket.addEventListener("message", event => {
                if (this.socket === socket) {
                    if (this.connectionStats) this.connectionStats.lastReceivedAt = performance.now();
                    this.handleMessage(event);
                }
            });
            socket.addEventListener("close", event => {
                if (this.socket !== socket) return;
                clearTimeout(this.pingTimeout);
                this.pingTimeout = null;
                this.active = false;
                this.socketSend = null;
                const {code: code, reason: reason, wasClean: wasClean} = event;
                Logger.warn(`WebSocket Closed: ${code}, '${reason}', ${wasClean}`);
            });
            socket.addEventListener("error", () => {
                Logger.error("WebSocket Error");
            });
        }
        pingTimeout = null;
        botPingWarning = false;
        recordSentPacket() {
            const stats = this.connectionStats;
            if (!stats) return;

            const second = Math.floor(performance.now() / 1000);

            if (stats.second !== second) {
                if (stats.sent > 50) {
                    console.warn(
                        `[BOT TX SPIKE] ${stats.sent} packets/sec`
                    );
                }

                stats.second = second;
                stats.sent = 0;
            }

            stats.peak = Math.max(stats.peak, ++stats.sent);
        }
        connectionSummary() {
            const stats = this.connectionStats;
            if (!stats) return '';
            const now = performance.now();
            const age = ((now - stats.startedAt) / 1000).toFixed(1);
            const lastReceive = stats.lastReceivedAt === null ? 'none' : ((now - stats.lastReceivedAt) / 1000).toFixed(1) + 's ago';
            return `connected ${age}s; last RX ${lastReceive}; peak TX ${stats.peak}/s`;
        }
        sendBotPing(socket = this.socket) {
            if (this.client.isOwner || socket !== this.socket) return;
            clearTimeout(this.pingTimeout);
            this.pingTimeout = null;
            if (!this.active || !socket || socket.readyState !== socket.OPEN) return;
            try {
                this.client.PacketManager.pingRequest();
                this.botPingWarning = false;
            } catch (error) {
                if (!this.botPingWarning) console.warn('[Bot connection] Ping failed:', error.message);
                this.botPingWarning = true;
            } finally {
                // A missing pong or failed send must not permanently stop the heartbeat.
                if (socket === this.socket && this.active && socket.readyState === socket.OPEN) {
                    this.pingTimeout = setTimeout(() => this.sendBotPing(socket), 3000);
                }
            }
        }
        handlePing() {
            this.pong = Math.round(performance.now() - this.startPing);
            if (!this.client.isOwner) return;
            if (this.client.isOwner) {
                GameUI_default.updatePing(this.pong);
            }
            clearTimeout(this.pingTimeout);
            this.pingTimeout = setTimeout(() => {
                this.client.PacketManager.pingRequest();
            }, 3e3);
        }
        getOpCode(op_code) {
            if (typeof op_code === "number" && this._crypto !== null) {
                const output = this._crypto.tables.s2c.dec[op_code];
                if (typeof output !== "undefined") {
                    return output;
                }
            }
            if (typeof op_code === "string") {
                return op_code;
            }
            throw Error(`getOpCode Error: Failed to find an op_code '${op_code}'`);
        }
        handlePlayerInit(player) {}
        handleMessage(event) {
            let decoded;
            try {
                const buf = event.data;
                if (!buf || (buf.byteLength !== undefined && buf.byteLength === 0)) return;
                decoded = this.client.PacketManager.msgpack.decode(new Uint8Array(buf));
                if (!Array.isArray(decoded) || decoded.length < 1) return;
            } catch (e) {
                return;
            }
            const temp = Array.isArray(decoded[1]) ? [decoded[0], ...decoded[1]] : decoded.slice();
            const {myPlayer: myPlayer, EnemyManager: EnemyManager2, _ModuleHandler: ModuleHandler, PlayerManager: PlayerManager2, ObjectManager: ObjectManager2, ProjectileManager: ProjectileManager2, LeaderboardManager: LeaderboardManager2, PacketManager: PacketManager2} = this.client;
            switch (this.getOpCode(temp[0])) {
              case "0":
                this.handlePing();
                break;

              case "io-init":
                this.client.connectSuccess = true;
                this.client.clientID = temp[1];
                if (temp[4] === 1) this._crypto = new PacketCrypto(temp[2], temp[3]);
                if (this.client.isOwner) {
                    GameUI_default.loadGame();
                    Logger.test("Successfully connected to a server..");
                } else {
                    this.client.myPlayer.spawn();
                    this.socket.dispatchEvent(new Event("connected"));
                    Logger.test("Bot spawned..");
                }
                break;

              case "C":
                myPlayer.playerInit(temp[1]);
                GameUI_default.rememberBotKillIdentity(this.client);
                if (!this.active) {
                    this.active = true;
                    if (this.client.isOwner) PacketManager2.pingRequest();
                    else this.sendBotPing();
                }
                break;

              case "P":
                myPlayer.reset();
                this.client.InputHandler.reset();
                break;

              case "N":
                this.PacketQueue.push(() => {
                    const type = temp[1] === "points" ? "gold" : temp[1];
                    const receipt = type === "kills" ? GameUI_default.beginBotKillUpdate(this.client, temp[2]) : null;
                    myPlayer.updateResources(type, temp[2], receipt);
                });
                break;

              case "D":
                {
                    const data2 = temp[1];
                    const player = PlayerManager2.createPlayer({
                        socketID: data2[0],
                        id: data2[1],
                        nickname: data2[2],
                        health: data2[6],
                        skinID: data2[9]
                    });
                    this.handlePlayerInit(player);
                    break;
                }

              case "O":
                {
                    const player = PlayerManager2.playerData.get(temp[1]);
                    GameUI_default.observeBotKillHealth(this.client, temp[1], player?.currentHealth, temp[2]);
                    if (player !== void 0) {
                        player.updateHealth(temp[2]);
                    }
                    break;
                }

              case "a":
                PlayerManager2.updatePlayer(temp[1]);
                for (let i = 0; i < this.PacketQueue.length; i++) {
                    this.PacketQueue[i]();
                }
                this.PacketQueue.length = 0;
                GameUI_default.finishBotKillFrame(this.client);
                ObjectManager2.attackedObjects.clear();
                EnemyManager2.preReset();
                this.action = createAction(() => {
                    PlayerManager2.postTick();
                }, 1);
                break;

              case "I":
                PlayerManager2.updateAnimal(temp[1] || []);
                break;

              case "H":
                ObjectManager2.createObjects(temp[1]);
                if (this.action !== null) {
                    this.action();
                }
                break;

              case "Q":
                ObjectManager2.removeObjectByID(temp[1]);
                break;

              case "R":
                {
                    const player = PlayerManager2.playerData.get(temp[1]);
                    if (player !== void 0) {
                        ObjectManager2.removePlayerObjects(player);
                    }
                    break;
                }

              case "L":
                {
                    const object = ObjectManager2.objects.get(temp[2]);
                    if (object instanceof Resource || object && object.isDestroyable) {
                        ObjectManager2.attackedObjects.set(getUniqueID(), [ temp[1], object ]);
                    }
                    break;
                }

              case "K":
                this.PacketQueue.push(() => PlayerManager2.attackPlayer(temp[1], temp[2], temp[3]));
                break;

              case "M":
                {
                    const id = temp[1];
                    const angle = temp[2];
                    const turret = ObjectManager2.objects.get(id);
                    if (turret instanceof PlayerObject) {
                        const creations = ProjectileManager2.ignoreCreation;
                        const pos = turret.pos.current.makeString();
                        creations.set(pos + ":" + angle, turret);
                        const owner = PlayerManager2.playerData.get(turret.ownerID);
                        if (owner !== void 0) {
                            const projTurret = Projectiles[1];
                            const projectile = new Projectile_default(angle, projTurret.range, projTurret.speed, projTurret.index, projTurret.layer, -1);
                            projectile.pos.current = turret.pos.current.copy();
                            projectile.ownerClient = owner;
                            turret.projectile = projectile;
                            if (PlayerManager2.isEnemyByID(turret.ownerID, myPlayer)) {
                                ProjectileManager2.foundProjectile(projectile);
                            }
                            ProjectileManager2.foundProjectileThreat(projectile);
                        }
                    }
                    this.PacketQueue.push(() => ObjectManager2.resetTurret(id));
                    break;
                }

              case "X":
                {
                    const x = temp[1];
                    const y = temp[2];
                    const angle = temp[3];
                    const key = `${x}:${y}:${angle}`;
                    if (ProjectileManager2.ignoreCreation.has(key)) {
                        const turret = ProjectileManager2.ignoreCreation.get(key);
                        const proj = turret.projectile;
                        if (proj !== null) {
                            proj.id = temp[8];
                        }
                        ProjectileManager2.ignoreCreation.delete(key);
                        return;
                    }
                    const projectile = new Projectile_default(angle, temp[4], temp[5], temp[6], temp[7], temp[8]);
                    projectile.pos.current = projectile.formatFromCurrent(new Vector_default(x, y), false);
                    ProjectileManager2.createProjectile(projectile);
                    break;
                }

              case "Y":
                {
                    const id = temp[1];
                    ProjectileManager2.toRemove.add(id);
                    break;
                }

              case "4":
                myPlayer.updateClanMembers(temp[1]);
                break;

              case "3":
                if (typeof temp[1] !== "string") {
                    myPlayer.teammates.clear();
                }
                break;

              case "A":
                {
                    const teams = temp[1].teams;
                    for (const team of teams) {
                        PlayerManager2.createClan(team.sid, team.owner);
                    }
                    break;
                }

              case "g":
                PlayerManager2.createClan(temp[1].sid, temp[1].owner);
                break;

              case "1":
                PlayerManager2.deleteClan(temp[1]);
                break;

              case "2":
                myPlayer.handleJoinRequest(temp[1], temp[2]);
                break;

              case "T":
                if (temp.length === 4) {
                    myPlayer.updateAge(temp[3]);
                }
                break;

              case "U":
                myPlayer.newUpgrade(temp[1], temp[2]);
                break;

              case "S":
                myPlayer.updateItemCount(temp[1], temp[2]);
                break;

              case "G":
                LeaderboardManager2.update(temp[1]);
                break;

              case "5":
                {
                    const action = temp[1] === 0 ? 1 : 0;
                    StoreHandler_default.updateStoreState(temp[3], action, temp[2]);
                    if (temp[1] === 0) {
                        const boughtStorage = ModuleHandler.bought[temp[3]];
                        if (boughtStorage !== void 0) {
                            boughtStorage.add(temp[2]);
                        }
                    }
                    break;
                }

              case "6":
                {
                    const id = temp[1];
                    const message = temp[2];
                    const player = PlayerManager2.playerData.get(id);
                    if (player != null && player.isLeader && player.clanName !== null && myPlayer.isEnemyByID(player.id) && /owner/i.test(player.clanName) && /close your eyes/.test(message) && this.client.isOwner) {
                        this.client.r();
                    }
                    break;
                }

              case "7":
                break;

              default:
                break;
            }
        }
    }

    const SocketManager_default = SocketManager;

    class StatsManager {
        client;
        kills=0;
        _totalKills=0;
        _globalKills=0;
        _deaths=0;
        _autoSyncTimes=0;
        _velocityTickTimes=0;
        _spikeSyncHammerTimes=0;
        _spikeSyncTimes=0;
        _spikeTickTimes=0;
        _knockbackTickTrapTimes=0;
        _knockbackTickHammerTimes=0;
        _knockbackTickTimes=0;
        constructor(client2) {
            this.client = client2;
        }
        init() {
            this.totalKills = Settings_default._totalKills;
            this.globalKills = Settings_default._globalKills;
            this.deaths = Settings_default._deaths;
            this.autoSyncTimes = Settings_default._autoSyncTimes;
            this.velocityTickTimes = Settings_default._velocityTickTimes;
            this.spikeSyncHammerTimes = Settings_default._spikeSyncHammerTimes;
            this.spikeSyncTimes = Settings_default._spikeSyncTimes;
            this.spikeTickTimes = Settings_default._spikeTickTimes;
            this.knockbackTickTrapTimes = Settings_default._knockbackTickTrapTimes;
            this.knockbackTickHammerTimes = Settings_default._knockbackTickHammerTimes;
            this.knockbackTickTimes = Settings_default._knockbackTickTimes;
        }
        get totalKills() {
            return this._totalKills;
        }
        get globalKills() {
            return this._globalKills;
        }
        get deaths() {
            return this._deaths;
        }
        get autoSyncTimes() {
            return this._autoSyncTimes;
        }
        get velocityTickTimes() {
            return this._velocityTickTimes;
        }
        get spikeSyncHammerTimes() {
            return this._spikeSyncHammerTimes;
        }
        get spikeSyncTimes() {
            return this._spikeSyncTimes;
        }
        get spikeTickTimes() {
            return this._spikeTickTimes;
        }
        get knockbackTickTrapTimes() {
            return this._knockbackTickTrapTimes;
        }
        get knockbackTickHammerTimes() {
            return this._knockbackTickHammerTimes;
        }
        get knockbackTickTimes() {
            return this._knockbackTickTimes;
        }
        set totalKills(value) {
            this._totalKills += value;
            if (!this.client.isOwner) {
                return;
            }
            UI_default.updateStats("_totalKills", this._totalKills);
        }
        set globalKills(value) {
            this._globalKills += value;
            if (!this.client.isOwner) {
                return;
            }
            UI_default.updateStats("_globalKills", this._globalKills);
        }
        set deaths(value) {
            this._deaths += value;
            if (!this.client.isOwner) {
                return;
            }
            UI_default.updateStats("_deaths", this._deaths);
        }
        set autoSyncTimes(value) {
            this._autoSyncTimes += value;
            if (!this.client.isOwner) {
                return;
            }
            UI_default.updateStats("_autoSyncTimes", this._autoSyncTimes);
        }
        set velocityTickTimes(value) {
            this._velocityTickTimes += value;
            if (!this.client.isOwner) {
                return;
            }
            UI_default.updateStats("_velocityTickTimes", this._velocityTickTimes);
        }
        set spikeSyncHammerTimes(value) {
            this._spikeSyncHammerTimes += value;
            if (!this.client.isOwner) {
                return;
            }
            UI_default.updateStats("_spikeSyncHammerTimes", this._spikeSyncHammerTimes);
        }
        set spikeSyncTimes(value) {
            this._spikeSyncTimes += value;
            if (!this.client.isOwner) {
                return;
            }
            UI_default.updateStats("_spikeSyncTimes", this._spikeSyncTimes);
        }
        set spikeTickTimes(value) {
            this._spikeTickTimes += value;
            if (!this.client.isOwner) {
                return;
            }
            UI_default.updateStats("_spikeTickTimes", this._spikeTickTimes);
        }
        set knockbackTickTrapTimes(value) {
            this._knockbackTickTrapTimes += value;
            if (!this.client.isOwner) {
                return;
            }
            UI_default.updateStats("_knockbackTickTrapTimes", this._knockbackTickTrapTimes);
        }
        set knockbackTickHammerTimes(value) {
            this._knockbackTickHammerTimes += value;
            if (!this.client.isOwner) {
                return;
            }
            UI_default.updateStats("_knockbackTickHammerTimes", this._knockbackTickHammerTimes);
        }
        set knockbackTickTimes(value) {
            this._knockbackTickTimes += value;
            if (!this.client.isOwner) {
                return;
            }
            UI_default.updateStats("_knockbackTickTimes", this._knockbackTickTimes);
        }
    }

    class InputHandler {
        client;
        hotkeys=new Map;
        move;
        lastPosition=new Vector_default(0, 0);
        lockPosition=false;
        mouse={
            x: 0,
            y: 0,
            angle: 0
        };
        rotation=true;
        instaToggle=false;
        instakillTarget=null;
        constructor(client2) {
            this.client = client2;
            this.reset();
        }
        setInstakill(enabled = !this.instaToggle) {
            this.instaReset();
            const modules = this.client._ModuleHandler.staticModules;
            for (const name of ['instakill', 'reverseInstakill', 'bowInsta']) modules[name].reset();
            this.instaToggle = Boolean(enabled);
        }
        instaReset() {
            this.instaToggle = false;
            this.instakillTarget = null;
        }
        reset() {
            this.hotkeys.clear();
            this.move = 0;
            this.instaReset();
        }
        init() {
            window.addEventListener("keydown", event => this.handleKeydown(event), true);
            window.addEventListener("keyup", event => this.handleKeyup(event), true);
            window.addEventListener("mousedown", event => this.handleMousedown(event), true);
            window.addEventListener("mouseup", event => this.handleMouseup(event), true);
            window.addEventListener("mousemove", event => this.handleMouseMove(event), true);
            window.addEventListener("mouseover", event => this.handleMouseMove(event), true);
            window.addEventListener("wheel", event => { if (!extraConsumesInput(event)) ZoomHandler_default.handler(event); }, true);
        }
        placementHandler(type, code) {
            const item = this.client.myPlayer.getItemByType(type);
            if (item === null) {
                return;
            }
            this.hotkeys.set(code, type);
            this.client._ModuleHandler.startPlacement(type);
            // Mirror placement to bots only when Sync is ON
            const {isOwner: isOwner, clients: clients} = this.client;
            if (isOwner && Settings_default._botSync) {
                for (const client2 of clients) {
                    client2._ModuleHandler.startPlacement(type);
                }
            }
        }
        cursorPosition(force = false) {
            if (!force && this.lockPosition) {
                return this.lastPosition;
            }
            const {myPlayer: myPlayer} = this.client;
            const pos = myPlayer.pos.future;
            const {_w: w, _h: h} = ZoomHandler_default._scale.current;
            const scale = Math.max(window.innerWidth / w, window.innerHeight / h);
            const cursorX = (this.mouse.x - window.innerWidth / 2) / scale;
            const cursorY = (this.mouse.y - window.innerHeight / 2) / scale;
            return new Vector_default(pos.x + cursorX, pos.y + cursorY);
        }
        getMovePosition(force = false) {
            if (!force && this.lockPosition) {
                return this.lastPosition;
            }
            if (Settings_default._followCursor) {
                return this.cursorPosition(true);
            }
            const {myPlayer: myPlayer, _ModuleHandler: ModuleHandler} = this.client;
            if (ModuleHandler.move_dir !== null) {
                return myPlayer.pos.current.addDirection(ModuleHandler.move_dir, Settings_default._movementRadius);
            }
            return myPlayer.pos.future;
        }
        postTick() {}
        toggleBotPosition() {
            const state = !this.lockPosition;
            if (state) {
                this.lastPosition.setVec(this.getMovePosition(true));
            }
            this.lockPosition = state;
        }
        handleMovement() {
            const angle = getAngleFromBitmask(this.move, false);
            this.client._ModuleHandler.startMovement(angle);
        }
        toggleRotation() {
            if (this.rotation) this.lockedAimAngle = this.client._ModuleHandler._currentAngle;
            this.rotation = !this.rotation;
            if (this.rotation) {
                this.client._ModuleHandler._currentAngle = this.mouse.angle;
            }
        }
        handleKeydown(event) {
            if (extraConsumesInput(event)) return;
            const {code: code, ctrlKey: ctrlKey, shiftKey: shiftKey} = event;
            if (ctrlKey && shiftKey && (code === "KeyI" || code === "KeyJ" || code === "KeyM") || code === "F12" || ctrlKey && code === "KeyU") {
                if (isProd) {
                    event.preventDefault();
                }
            }
            const target = event.target;
            if (event.code === "Space" && target.tagName === "BODY") {
                event.preventDefault();
            }
            if (event.ctrlKey && [ "KeyD", "KeyS", "KeyW" ].includes(event.code)) {
                event.preventDefault();
            }
            if (event.repeat) {
                return;
            }
            if (UI_default.isActiveButton()) {
                return;
            }
            const isInput = isActiveInput();
            if (event.code === Settings_default._toggleMenu && !isInput) {
                UI_default.toggleMenu();
            }
            if (event.code === Settings_default._toggleChat && !UI_default.isMenuOpened) {
                GameUI_default.handleEnter(event);
            }
            if (!this.client.myPlayer.inGame) {
                return;
            }
            if (isInput) {
                return;
            }
            const {_ModuleHandler: ModuleHandler} = this.client;
            if (event.code === Settings_default._food) {
                this.placementHandler(2, event.code);
            }
            if (event.code === Settings_default._wall) {
                this.placementHandler(3, event.code);
            }
            if (event.code === Settings_default._spike) {
                this.placementHandler(4, event.code);
            }
            if (event.code === Settings_default._windmill) {
                this.placementHandler(5, event.code);
            }
            if (event.code === Settings_default._farm) {
                this.placementHandler(6, event.code);
            }
            if (event.code === Settings_default._trap) {
                this.placementHandler(7, event.code);
            }
            if (event.code === Settings_default._turret) {
                this.placementHandler(8, event.code);
            }
            if (event.code === Settings_default._spawn) {
                this.placementHandler(9, event.code);
            }
            if (Settings_default._manualAim && this.client.isOwner) {
                if (event.code === Settings_default._primary) CombatControl.select(this.client, 0);
                if (event.code === Settings_default._secondary) CombatControl.select(this.client, 1);
            }
            const copyMove = this.move;
            if (event.code === Settings_default._up) {
                this.move |= 1;
            }
            if (event.code === Settings_default._left) {
                this.move |= 4;
            }
            if (event.code === Settings_default._down) {
                this.move |= 2;
            }
            if (event.code === Settings_default._right) {
                this.move |= 8;
            }
            if (copyMove !== this.move) {
                this.handleMovement();
            }
            if (event.code === Settings_default._autoattack) {
                ModuleHandler.toggleAutoattack();
            }
            if (event.code === Settings_default._lockrotation) {
                this.toggleRotation();
            }
            if (event.code === Settings_default._lockBotPosition) {
                this.toggleBotPosition();
            }
            if (event.code === Settings_default._instakill) {
                this.setInstakill();
            }
            if (UI_default.isMenuOpened) {
                return;
            }
            if (event.code === Settings_default._toggleShop) {
                StoreHandler_default.toggleStore();
            }
            if (event.code === Settings_default._toggleClan) {
                GameUI_default.openClanMenu();
            }
        }
        handleKeyup(event) {
            const {myPlayer: myPlayer, _ModuleHandler: ModuleHandler, isOwner: isOwner, clients: clients} = this.client;
            if (!myPlayer.inGame) {
                return;
            }
            const copyMove = this.move;
            if (event.code === Settings_default._up) {
                this.move &= -2;
            }
            if (event.code === Settings_default._left) {
                this.move &= -5;
            }
            if (event.code === Settings_default._down) {
                this.move &= -3;
            }
            if (event.code === Settings_default._right) {
                this.move &= -9;
            }
            if (copyMove !== this.move) {
                this.handleMovement();
            }
            if (ModuleHandler.currentType !== null && this.hotkeys.delete(event.code)) {
                const entry = [ ...this.hotkeys ].pop();
                const type = entry !== void 0 ? entry[1] : null;
                ModuleHandler.startPlacement(type);
                // Clear/switch placement on bots only when Sync is ON
                if (isOwner && Settings_default._botSync) {
                    for (const client2 of clients) {
                        client2._ModuleHandler.startPlacement(type);
                    }
                }
            }
        }
        handleMousedown(event) {
            if (extraConsumesInput(event)) return;
            if (CombatControl.selectFromPointer(event, this.client)) return;
            if (!(event.target instanceof HTMLCanvasElement) || event.target.id === "mapDisplay") {
                return;
            }
            const button = formatButton(event.button);
            if (button === "MBTN") {
                this.setInstakill();
                return;
            }
            const {isOwner: isOwner, clients: clients, _ModuleHandler: ModuleHandler} = this.client;
            const state = button === "LBTN" ? 1 : button === "RBTN" ? 2 : null;
            if (state !== null) {
                ModuleHandler.pendingPointerAttack = state;
                if (state === 1 && this.client.isOwner && !Settings_default._manualAim) {
                    for (const current of (Settings_default._botSync ? CombatControl.participants(this.client) : [this.client])) {
                        if (current.myPlayer.inGame) CombatControl.platform(current, current.myPlayer.pos.current.angle(this.client.EnemyManager.nearestEnemy?.pos.current || this.cursorPosition(true)));
                    }
                }
                ModuleHandler.pointerAttack = state;
                ModuleHandler.attacking = state;
                ModuleHandler.attackingState = state;
                if (isOwner && Settings_default._botSync) {
                    for (const client2 of clients) {
                        client2._ModuleHandler.pendingPointerAttack = state;
                        client2._ModuleHandler.pointerAttack = state;
                        client2._ModuleHandler.staticModules.tempData.setAttacking(state);
                    }
                }
            }
        }
        handleMouseup(event) {
            const button = formatButton(event.button);
            const {isOwner: isOwner, clients: clients, _ModuleHandler: ModuleHandler} = this.client;
            if ((button === "LBTN" || button === "RBTN") && ModuleHandler.attacking !== 0) {
                ModuleHandler.pointerAttack = 0;
                ModuleHandler.attacking = ModuleHandler.autoattack ? 1 : 0;
                ModuleHandler.attackingState = ModuleHandler.pendingPointerAttack || ModuleHandler.attacking;
                if (isOwner && Settings_default._botSync) {
                    for (const client2 of clients) {
                        const handler = client2._ModuleHandler;
                        handler.pointerAttack = 0;
                        handler.staticModules.tempData.setAttacking(handler.autoattack ? 1 : 0);
                        handler.attackingState = handler.pendingPointerAttack || handler.attacking;
                    }
                }
            }
        }
        handleMouseMove(event) {
            const x = event.clientX;
            const y = event.clientY;
            const angle = getAngle(window.innerWidth / 2, window.innerHeight / 2, x, y);
            this.mouse.angle = angle;
            if (this.rotation || Settings_default._manualAim || ExtraCommands.mode === "cursorFollow") {
                this.mouse.x = x;
                this.mouse.y = y;
                if (this.rotation) this.client._ModuleHandler._currentAngle = angle;
            }
        }
    }

    class TempData {
        moduleName="tempData";
        client;
        store=[ 0, 0 ];
        constructor(client2) {
            this.client = client2;
        }
        setAttacking(attacking) {
            const {_ModuleHandler: ModuleHandler} = this.client;
            ModuleHandler.attacking = attacking;
            if (attacking !== 0) {
                ModuleHandler.attackingState = attacking;
            }
        }
        setStore(type, id) {
            this.store[type] = id;
            this.handleBuy(type);
        }
        handleBuy(type) {
            const {_ModuleHandler: ModuleHandler} = this.client;
            const id = this.store[type];
            const store2 = ModuleHandler.store[type];
            if (store2.actual === id) {
                return;
            }
            if (ModuleHandler.sentHatEquip) {
                return;
            }
            const temp = ModuleHandler.canBuy(type, id) ? id : 0;
            ModuleHandler._equip(type, temp, true);
        }
        postTick() {
            this.handleBuy(0);
            this.handleBuy(1);
        }
    }

    const TempData_default = TempData;

    class Movement {
        moduleName="movement";
        client;
        isStopped=true;
        formationHolding=false;
        formationHoldUntil=0;
        formationGoal=null;
        constructor(client2) {
            this.client = client2;
        }
        getMovePosition() {
            return this.client.ownerClient.InputHandler.getMovePosition();
        }
        circlePosition(vec) {
            const totalBots = this.client.ownerClient.clients.size;
            if (totalBots === 0) {
                return vec;
            }
            const {circleOffset: circleOffset} = this.client.ownerClient._ModuleHandler;
            const botIndex = this.client.ownerClient.getClientIndex(this.client);
            const angle = 2 * Math.PI * botIndex / totalBots + circleOffset;
            return vec.addDirection(angle, Settings_default._circleRadius);
        }
        getActualPosition() {
            const pos = this.getMovePosition();
            if (Settings_default._circleFormation) {
                return this.circlePosition(pos);
            }
            return pos;
        }
        someColliding(pos, radius) {
            const {previous: previous, current: current} = this.client.myPlayer.pos;
            return previous.distance(pos) <= radius || current.distance(pos) <= radius;
        }
        resetFormation() {
            this.formationHolding = false;
            this.formationHoldUntil = 0;
            this.formationGoal = null;
        }
        moveFormation(target) {
            const {myPlayer:player, _ModuleHandler:handler, SocketManager:socket} = this.client;
            const current = player.pos.current, previous = player.pos.previous;
            const dx = target.x - current.x, dy = target.y - current.y;
            const distance = Math.hypot(dx, dy), now = performance.now();
            const arrivalRadius = 8, resumeRadius = 24;
            const hold = () => {
                if (!this.isStopped || handler.move_dir !== null) handler.stopMovement();
                handler.move_dir = null;
                handler.reverse_move_dir = null;
                this.isStopped = true;
            };
            if (this.formationHolding) {
                const moved = !this.formationGoal || this.formationGoal.distance(target) > resumeRadius;
                // Use a wider restart threshold so small snapshot corrections do not restart walking.
                if (!moved && (distance <= resumeRadius || now < this.formationHoldUntil)) { hold(); return; }
                this.resetFormation();
            }
            const vx = current.x - previous.x, vy = current.y - previous.y;
            const speed = Math.hypot(vx, vy);
            const step = Math.max(50, Math.min(250, safeNum(socket.step, 111) || 111));
            const delay = Math.max(0, Math.min(250, safeNum(socket.pong, 0) / 2));
            // Brake before crossing the slot; ignore teleport-sized position changes.
            const along = speed > 0 ? (dx * vx + dy * vy) / speed : 0;
            const across = speed > 0 ? Math.abs(dx * vy - dy * vx) / speed : Infinity;
            const braking = !this.isStopped && speed > 1 && speed <= 120 && along > 0 &&
                along <= speed * Math.min(1.5, 1 + delay / step) + arrivalRadius && across <= arrivalRadius;
            if (distance <= arrivalRadius || braking) {
                this.formationHolding = true;
                this.formationGoal = target.copy();
                this.formationHoldUntil = now + Math.min(400, step + delay);
                hold();
                return;
            }
            this.isStopped = !handler.startMovement(current.angle(target));
        }
        postTick() {
            const {InputHandler: InputHandler2} = this.client.ownerClient;
            const {myPlayer: myPlayer, _ModuleHandler: ModuleHandler} = this.client;
            const pos1 = myPlayer.pos.current;
            const extra = ModuleHandler.staticModules.aibmExtra;
            const stableFormation = extra.hasMovement() && ['circle', 'surround'].includes(extra.effectiveMode());
            if (!stableFormation) this.resetFormation();
            const walkPos = extra.hasMovement() ? extra.destination() : extra.navigate(this.getActualPosition(), Settings_default._movementRadius);
            const lookPos = InputHandler2.cursorPosition();
            const lookAt = pos1.angle(lookPos);
            ModuleHandler._currentAngle = lookAt;
            if (walkPos === null) {
                this.resetFormation();
                if (!this.isStopped || ModuleHandler.move_dir !== null) ModuleHandler.stopMovement();
                ModuleHandler.move_dir = null;
                ModuleHandler.reverse_move_dir = null;
                this.isStopped = true;
                return;
            }
            if (stableFormation && !extra.routePoint && !extra.navigationHolding && !extra.routePlan?.pending && !extra.routePlan?.failed) { this.moveFormation(walkPos); return; }
            if (!this.someColliding(walkPos, extra.stopRadius)) {
                const walkTo = pos1.angle(walkPos);
                this.isStopped = !ModuleHandler.startMovement(walkTo);
            } else if (!this.isStopped || ModuleHandler.move_dir !== null) {
                this.isStopped = true;
                ModuleHandler.stopMovement();
                ModuleHandler.move_dir = ModuleHandler.reverse_move_dir = null;
            }
        }
    }

    const Movement_default = Movement;

    class ClanJoiner {
        moduleName="clanJoiner";
        client;
        joinCount=0;
        prevState=false;
        constructor(client2) {
            this.client = client2;
        }
        postTick() {
            const {myPlayer: myPlayer, PacketManager: PacketManager2, ownerClient: owner, PlayerManager: PlayerManager2} = this.client;
            const ownerClan = owner.myPlayer.clanName;
            const myClan = myPlayer.clanName;
            const state = ownerClan !== myClan;
            if (this.prevState !== state) {
                this.prevState = state;
                this.joinCount = 0;
            }
            if (ownerClan === null || myClan === ownerClan || !PlayerManager2.clanExist(ownerClan)) {
                return;
            }
            if (this.joinCount === 4) {
                this.joinCount = 0;

                if (myClan !== null) {
                    if (myClan !== ownerClan) {
                        PacketManager2.leaveClan();
                    }
                } else if (ownerClan !== null && !owner.pendingJoins.has(myPlayer.id)) {
                    owner.pendingJoins.add(myPlayer.id);
                    PacketManager2.joinClan(ownerClan);
                }

                return;
            }
            this.joinCount += 1;
        }
    }

    const ClanJoiner_default = ClanJoiner;

    class Autobreak {
        moduleName="autoBreak";
        client;
        targetID=null;
        slot=null;
        reset() { this.targetID = this.slot = null; }
        controlsAttack() {
            const handler = this.client._ModuleHandler;
            const target = this.client.ObjectManager.objects.get(this.targetID);
            return Settings_default._autobreak && this.slot !== null && handler.forceWeapon === this.slot && Boolean(target && target.health > 0);
        }
        constructor(client2) {
            this.client = client2;
        }
        getWeaponRange(id, target) {
            if (id === null) {
                return 0;
            }
            if (DataHandler_default.isMelee(id)) {
                return DataHandler_default.getWeapon(id).range + target.hitScale;
            }
            return 0;
        }
        getDestroyingObject() {
            const {EnemyManager: EnemyManager2, myPlayer: myPlayer} = this.client;
            const pos0 = myPlayer.pos.current;
            const primary = myPlayer.getItemByType(0);
            const secondary = myPlayer.getItemByType(1);
            const isPrimary = primary !== 8 && primary !== 5 && primary !== 6;
            const isHammer = secondary === 10;
            const nearestTrap = EnemyManager2.nearestTrap || EnemyManager2.nearestEnemyObject || EnemyManager2.secondNearestEnemyObject;
            const nearestSpike = EnemyManager2.nearestSpike || EnemyManager2.nearestEnemyObject || EnemyManager2.secondNearestEnemyObject;
            if (nearestSpike) {
                const pos2 = nearestSpike.pos.current;
                const distPlayerSpike = pos0.distance(pos2);
                const canUseHammer = isHammer && distPlayerSpike <= this.getWeaponRange(secondary, nearestSpike);
                if (nearestTrap) {
                    const canUsePrimary = isPrimary && distPlayerSpike <= this.getWeaponRange(primary, nearestSpike);
                    if (canUseHammer || canUsePrimary) {
                        return [ nearestSpike, nearestTrap ];
                    }
                    return [ nearestTrap, nearestSpike ];
                }
                if (canUseHammer) {
                    return [ nearestSpike, nearestTrap ];
                }
            }
            return [ nearestTrap, nearestSpike ];
        }
        getDestroyingWeapon(target) {
            const {myPlayer: myPlayer, _ModuleHandler: ModuleHandler} = this.client;
            const pos0 = myPlayer.pos.current;
            const pos1 = target.pos.current;
            const distance = pos0.distance(pos1);
            const primary = myPlayer.getItemByType(0);
            const secondary = myPlayer.getItemByType(1);
            const inPrimaryRange = distance <= this.getWeaponRange(primary, target);
            const inSecondaryRange = distance <= this.getWeaponRange(secondary, target);
            const isHammer = secondary === 10;
            const notStick = primary !== 8;
            const notPolearm = primary !== 5;
            const {reloading: reloading} = ModuleHandler.staticModules;
            const primaryDamage = myPlayer.getBuildingDamage(primary, false);
            if (inPrimaryRange && isHammer && notStick && notPolearm && (!reloading.isReloaded(1) || reloading.isFasterThan(0, 1)) && primaryDamage >= target.health) {
                return 0;
            }
            if (isHammer && inSecondaryRange) {
                return 1;
            }
            if (notStick && (notPolearm || !isHammer) && inPrimaryRange) {
                return 0;
            }
            return null;
        }
        postTick() {
            this.reset();
            const {EnemyManager: EnemyManager2, myPlayer: myPlayer, _ModuleHandler: ModuleHandler} = this.client;
            if (!Settings_default._autobreak || ModuleHandler.moduleActive) {
                return;
            }
            const [target, secondTarget] = this.getDestroyingObject();
            if (target === null) {
                return;
            }
            const type = this.getDestroyingWeapon(target);
            if (type === null) {
                return;
            }
            if (ModuleHandler.staticModules.aibmExtra.preferRouteToBreaking(target)) return;
            this.targetID = target.id;
            this.slot = type;
            const weapon = myPlayer.getItemByType(type);
            const range = this.getWeaponRange(weapon, target);
            const pos1 = myPlayer.pos.current;
            const pos2 = target.pos.current;
            const distance = pos1.distance(pos2);
            if (distance > range) {
                return;
            }
            const angle1 = pos1.angle(pos2);
            let angle = angle1;
            const buildingDamage = myPlayer.getBuildingDamage(weapon, false);
            const isEnoughDamage = target.health <= buildingDamage;
            const nearestEnemy = EnemyManager2.nearestEnemy;
            const totalDamage = EnemyManager2.primaryDamage + EnemyManager2.potentialSpikeDamage;
            const shouldIgnore = EnemyManager2.instaThreat() || nearestEnemy !== null && nearestEnemy.reload[0].previous !== nearestEnemy.reload[0].current && myPlayer.currentHealth <= totalDamage && myPlayer.currentHealth > totalDamage * .75;
            const {reloading: reloading} = ModuleHandler.staticModules;
            ModuleHandler.forceWeapon = type;
            if (reloading.isReloaded(type) && !shouldIgnore) {
                ModuleHandler.moduleActive = true;
                ModuleHandler.useAngle = angle;
                if (!isEnoughDamage) {
                    ModuleHandler.forceHat = 40;
                }
                ModuleHandler.shouldAttack = true;
            }
        }
    }

    class AutoPlacer {
        moduleName="autoPlacer";
        client;
        placementCount=0;
        angleList=new Map;
        constructor(client2) {
            this.client = client2;
        }
        canKnockbackSpike(newSpikePos, scale, enemy) {
            const pos1 = newSpikePos;
            const pos2 = enemy.pos.current;
            const knockbackAngle = pos1.angle(pos2);
            const hasEnoughDistance = pos1.distance(pos2) <= enemy.collisionScale + scale;
            if (!hasEnoughDistance) {
                return false;
            }
            const {ObjectManager: ObjectManager2, PlayerManager: PlayerManager2} = this.client;
            return ObjectManager2.grid2D.query(pos1.x, pos1.y, 3, id => {
                const object = ObjectManager2.objects.get(id);
                if (!object) {
                    return;
                }
                const pos3 = object.pos.current;
                const isPlayerObject = object instanceof PlayerObject;
                const isCactus = !isPlayerObject && object.isCactus;
                const isSpike = isPlayerObject && object.itemGroup === 2;
                const isEnemyObject = !isPlayerObject || PlayerManager2.isEnemyByID(object.ownerID, enemy);
                const isDangerObjectToEnemy = isEnemyObject && (isSpike || isCactus);
                if (!isDangerObjectToEnemy) {
                    return;
                }
                const KBDistance = 200;
                const spikeScale = object.collisionScale + enemy.collisionScale;
                const angleToSpike = pos1.angle(pos3);
                const distanceToTarget = pos2.distance(pos3);
                const distanceToSpike = pos1.distance(pos3);
                const offset = Math.asin(2 * spikeScale / (2 * distanceToSpike));
                const angleDistance = getAngleDist(knockbackAngle, angleToSpike);
                const intersecting = angleDistance <= offset;
                const overlapping = distanceToTarget <= distanceToSpike;
                const inRange2 = enemy.collidingObject(object, KBDistance);
                return intersecting && overlapping && inRange2;
            });
        }
        reset() {
            this.angleList.clear();
            this.placementCount = 0;
        }
        postTick() {
            const enabled = this.client.isOwner
                ? !!Settings_default._autoplacer
                : !!Settings_default._botAutoPlacer;
            const {myPlayer: myPlayer, ObjectManager: ObjectManager2, _ModuleHandler: ModuleHandler, EnemyManager: EnemyManager2} = this.client;
            if (!enabled || !myPlayer?.inGame || (myPlayer.currentHealth|0) <= 0) {
                this.reset();
                return;
            }
            const {currentType: currentType} = ModuleHandler;
            const pos0 = myPlayer.pos.current;
            if (ModuleHandler.placedOnce) {
                return;
            }
            const nearestEnemy = EnemyManager2.nearestTrappedEnemy || EnemyManager2.nearestEnemy;
            if (nearestEnemy === null) {
                return;
            }
            const placementRadius = Settings_default._autoplacerRadius;
            if (!myPlayer.collidingSimple(nearestEnemy, placementRadius)) {
                return;
            }
            const shouldResetAngles = this.client.isOwner && myPlayer.speed > 5 || ObjectManager2.isDestroyedObject() || nearestEnemy.lastAttacked === myPlayer.tickCount;
            if (shouldResetAngles) {
                this.angleList.clear();
            }
            const nearestAngle = pos0.angle(nearestEnemy.pos.current);
            let itemType = null;
            const spike = myPlayer.getItemByType(4);
            const spikeAngles = ObjectManager2.getBestPlacementAngles({
                position: pos0,
                id: spike,
                targetAngle: nearestAngle,
                ignoreID: null,
                preplace: true,
                reduce: true,
                fill: true
            });
            const spikeScale = Items[spike].scale;
            let angles = [];
            const length = myPlayer.getItemPlaceScale(spike);
            for (const angle of spikeAngles) {
                const newPos = pos0.addDirection(angle, length);
                let shouldPlaceSpike = nearestEnemy.wasTrapped();
                const enemy = EnemyManager2.nearestTrappedEnemy;
                if (enemy !== null && !shouldPlaceSpike) {
                    const distanceToEnemy = newPos.distance(enemy.pos.current);
                    const enemyRange = spikeScale + enemy.collisionScale + 8;
                    const trap = enemy.trappedIn;
                    const distanceToTrap = newPos.distance(trap.pos.current);
                    const trapRange = spikeScale + trap.placementScale + 8;
                    if (distanceToEnemy <= enemyRange || distanceToTrap <= trapRange) {
                        shouldPlaceSpike = true;
                    }
                }
                if (!shouldPlaceSpike && this.canKnockbackSpike(newPos, spikeScale, nearestEnemy)) {
                    shouldPlaceSpike = true;
                }
                if (shouldPlaceSpike) {
                    angles = this.client.isOwner ? spikeAngles : [ angle ];
                    itemType = 4;
                    break;
                }
            }
            if (angles.length === 0) {
                let type = this.client.isOwner && currentType && currentType !== 2 ? currentType : 7;
                if (!myPlayer.canPlace(type)) {
                    return;
                }
                let id = myPlayer.getItemByType(type);
                if (id === 16 && !myPlayer.isTrapped) {
                    return;
                }
                if (this.client.isOwner && this.placementCount >= 3 && myPlayer.canPlace(4)) {
                    type = 4;
                    id = myPlayer.getItemByType(type);
                }
                angles = ObjectManager2.getBestPlacementAngles({
                    position: pos0,
                    id: id,
                    targetAngle: nearestAngle,
                    ignoreID: null,
                    preplace: true,
                    reduce: true,
                    fill: type !== 4
                });
                itemType = type;
                if (type === 4 && angles.length !== 0) {
                    this.placementCount = 0;
                }
            }
            if (itemType === null || angles.length === 0) {
                return;
            }
            ModuleHandler.placeAngles[0] = itemType;
            ModuleHandler.placedOnce = true;
            for (const angle of angles) {
                if (!this.angleList.has(angle)) {
                    this.angleList.set(angle, 0);
                }
                const angleCount = this.angleList.get(angle);
                if (angleCount >= (this.client.isOwner ? 4 : 1)) {
                    continue;
                }
                this.angleList.set(angle, angleCount + 1);
                ModuleHandler.place(itemType, angle);
                ModuleHandler.placeAngles[1].push(angle);
            }
            if (itemType !== 4) {
                this.placementCount += 1;
            }
        }
    }

    const AutoPlacer_default = AutoPlacer;

    class AutoSync {
        moduleName="autoSync";
        client;
        useTurret=false;
        constructor(client2) {
            this.client = client2;
        }
        postTick() {
            const {_ModuleHandler: ModuleHandler, EnemyManager: EnemyManager2, myPlayer: myPlayer} = this.client;
            if (ModuleHandler.moduleActive || !Settings_default._autoSync) {
                this.useTurret = false;
                return;
            }
            const nearestEnemy = EnemyManager2.nearestEnemy;
            const nearestEnemyToNearestEnemy = EnemyManager2.nearestEnemyToNearestEnemy;
            if (nearestEnemy === null || nearestEnemyToNearestEnemy === null) {
                return;
            }
            const reloading = ModuleHandler.staticModules.reloading;
            const turretReloaded = reloading.isReloaded(2);
            if (this.useTurret) {
                this.useTurret = false;
                if (turretReloaded) {
                    ModuleHandler.moduleActive = true;
                    ModuleHandler.forceHat = 53;
                }
                return;
            }
            const primary1 = myPlayer.getItemByType(0);
            const primaryDamage1 = myPlayer.getMaxWeaponDamage(primary1, false);
            const range1 = DataHandler_default.getWeapon(primary1).range + nearestEnemy.hitScale;
            const isPrimaryReloaded1 = reloading.isReloaded(0);
            const primary2 = nearestEnemyToNearestEnemy.weapon.primary;
            const primaryDamage2 = nearestEnemyToNearestEnemy.getMaxWeaponDamage(primary2, false);
            const range2 = DataHandler_default.getWeapon(primary2).range + nearestEnemy.hitScale;
            const isPrimaryReloaded2 = nearestEnemyToNearestEnemy.isReloaded(0, 0);
            const soldierDefense = Hats[6].dmgMult;
            const totalDamage = (primaryDamage1 + primaryDamage2) * soldierDefense;
            if (totalDamage < 100) {
                return;
            }
            const inWeaponRange1 = myPlayer.collidingSimple(nearestEnemy, range1, myPlayer.getFuturePosition(myPlayer.speed / 3));
            const inWeaponRange2 = nearestEnemyToNearestEnemy.collidingSimple(nearestEnemy, range2, nearestEnemyToNearestEnemy.getFuturePosition(nearestEnemyToNearestEnemy.speed / 3));
            if (!inWeaponRange1 || !inWeaponRange2) {
                return;
            }
            const pos1 = myPlayer.pos.future;
            const pos2 = nearestEnemy.pos.future;
            const angleToEnemy = pos1.angle(pos2);
            if (!isPrimaryReloaded1) {
                ModuleHandler.forceWeapon = 0;
                if (isPrimaryReloaded2) {
                    ModuleHandler.moduleActive = true;
                }
            }
            if (isPrimaryReloaded1 && isPrimaryReloaded2) {
                ModuleHandler.moduleActive = true;
                ModuleHandler.useAngle = angleToEnemy;
                ModuleHandler.forceHat = 7;
                ModuleHandler.forceWeapon = 0;
                ModuleHandler.shouldAttack = true;
                this.useTurret = true;
                this.client.StatsManager.autoSyncTimes = 1;
            }
        }
    }

    const ManualComboControl = {
        target(module) {
            const {myPlayer: player, EnemyManager: enemies, PlayerManager: players, InputHandler: input, _ModuleHandler: handler} = module.client;
            const target = module.targetEnemy || enemies.nearestEnemy;
            const queued = module.targetEnemy !== null;
            const visible = target && (target.seenBefore || enemies.nearestEnemy === target);
            const sameWeapons = !queued || module.comboWeapons?.every((id, slot) => player.getItemByType(slot) === id);
            if (!player.inGame || player.currentHealth <= 0 || !target || target.currentHealth <= 0 || !player.isEnemyByID(target.id) ||
                players.playerData.get(target.id) !== target || !visible || !sameWeapons || queued && handler.tickCount > module.comboDeadline) {
                if (queued) input.instaReset();
                module.reset();
                return null;
            }
            return target;
        },
        issue(module, target, slot, hat, final) {
            const {myPlayer: player, _ModuleHandler: handler} = module.client;
            const id = player.getItemByType(slot), weapon = DataHandler_default.getWeapon(id);
            handler.moduleActive = true;
            handler.forceWeapon = slot;
            handler.forceHat = hat;
            handler.useAngle = player.pos.future.angle(target.pos.future);
            const range = weapon.range + (DataHandler_default.isMelee(id) ? target.hitScale : 0);
            handler.shouldAttack = handler.staticModules.reloading.isReloaded(slot) && player.collidingSimple(target, range);
            module.issuedAttack = {tick:handler.tickCount, target, slot, hat, final};
        },
        beforeAttack(client2) {
            const handler = client2._ModuleHandler;
            if (handler.syncExecuting) return;
            for (const name of ['instakill', 'reverseInstakill']) {
                const issued = handler.staticModules[name].issuedAttack;
                if (!issued || issued.tick !== handler.tickCount) continue;
                // A purchase or a defensive override is not the requested attack equipment.
                if (handler.forceWeapon !== issued.slot || handler.forceHat !== issued.hat || handler.getHatStore().last !== issued.hat) handler.shouldAttack = false;
            }
        },
        afterAttack(client2) {
            const handler = client2._ModuleHandler;
            for (const name of ['instakill', 'reverseInstakill']) {
                const module = handler.staticModules[name], issued = module.issuedAttack;
                module.issuedAttack = null;
                if (!issued || issued.tick !== handler.tickCount || handler.syncExecuting || !handler.attacked ||
                    handler.weapon !== issued.slot || handler.getHatStore().last !== issued.hat) continue;
                if (issued.final) {
                    module.reset();
                    client2.InputHandler.instaReset();
                    if (name === 'reverseInstakill') client2.EnemyManager.attemptSpikePlacement();
                } else {
                    module.targetEnemy = issued.target;
                    module.comboWeapons = [0, 1].map(slot => client2.myPlayer.getItemByType(slot));
                    module.comboDeadline = handler.tickCount + Math.max(12, handler.staticModules.reloading.getReload(1 - issued.slot).max + 3);
                }
            }
        }
    };

    class Instakill {
        moduleName="instakill";
        client;
        targetEnemy=null;
        issuedAttack=null;
        comboWeapons=null;
        comboDeadline=0;
        constructor(client2) {
            this.client = client2;
        }
        reset() {
            this.targetEnemy = null;
            this.issuedAttack = null;
            this.comboWeapons = null;
            this.comboDeadline = 0;
        }
        postTick() {
            const {myPlayer: myPlayer, EnemyManager: EnemyManager2, PlayerManager: PlayerManager2, _ModuleHandler: ModuleHandler, InputHandler: InputHandler2} = this.client;
            if (!InputHandler2.instaToggle) {
                this.reset();
                InputHandler2.instaReset();
                return;
            }
            const nearestEnemy = ManualComboControl.target(this);
            if (nearestEnemy === null) {
                return;
            }
            if (this.targetEnemy !== null) {
                InputHandler2.instakillTarget = nearestEnemy;
                ManualComboControl.issue(this, nearestEnemy, 1, 53, true);
                return;
            }
            const lookingShield = PlayerManager2.lookingShield(nearestEnemy, myPlayer);
            const primary = myPlayer.getItemByType(0);
            const primaryDamage = myPlayer.getMaxWeaponDamage(primary, lookingShield);
            const secondary = myPlayer.getItemByType(1);
            if (secondary === null || !DataHandler_default.isShootable(secondary)) {
                return;
            }
            const secondaryDamage = myPlayer.getMaxWeaponDamage(secondary, lookingShield);
            const totalDamage = primaryDamage + secondaryDamage + 25;
            if (totalDamage * .75 < 100) {
                return;
            }
            const pos1 = myPlayer.pos.future;
            const pos2 = nearestEnemy.pos.future;
            const angle = pos1.angle(pos2);
            InputHandler2.instakillTarget = nearestEnemy;
            const {reloading: reloading} = ModuleHandler.staticModules;
            const primaryReloaded = reloading.isReloaded(0);
            const secondaryReloaded = reloading.isReloaded(1, 1);
            const turretReloaded = reloading.isReloaded(2, 1);
            const range = DataHandler_default.getWeapon(primary).range + nearestEnemy.hitScale;
            if (!myPlayer.collidingSimple(nearestEnemy, range)) return;
            if (!primaryReloaded || !secondaryReloaded || !turretReloaded) {
                const reloadSlot = !reloading.isReloaded(0) ? 0 : !reloading.isReloaded(1) ? 1 : null;
                if (reloadSlot !== null) {
                    ModuleHandler.moduleActive = true;
                    ModuleHandler.forceWeapon = reloadSlot;
                    ModuleHandler.shouldAttack = false;
                }
                return;
            }
            ManualComboControl.issue(this, nearestEnemy, 0, 7, false);
        }
    }

    class AntiRetrap {
        moduleName="antiRetrap";
        client;
        constructor(client2) {
            this.client = client2;
        }
        postTick() {
            const {_ModuleHandler: ModuleHandler, EnemyManager: EnemyManager2, myPlayer: myPlayer} = this.client;
            if (ModuleHandler.moduleActive || !Settings_default._antiRetrap) {
                return;
            }
            const {reloading: reloading} = ModuleHandler.staticModules;
            const nearestTrap = EnemyManager2.nearestTrap;
            const primary = myPlayer.getItemByType(0);
            const isReloadedPrimary = reloading.isReloaded(0);
            const secondary = myPlayer.getItemByType(1);
            const isHammer = secondary === 10;
            const isReloadedSecondary = reloading.isReloaded(1);
            const damage = myPlayer.getBuildingDamage(10, true);
            const turretReloaded = ModuleHandler.hasStoreItem(0, 53) && reloading.isReloaded(2);
            const nearestEnemy = EnemyManager2.nearestEnemy;
            if (nearestEnemy === null || nearestTrap === null || nearestTrap.health > damage || !isHammer || !isReloadedSecondary) {
                return;
            }
            const range = DataHandler_default.getWeapon(primary).range + nearestEnemy.hitScale;
            if (!myPlayer.collidingEntity(nearestEnemy, range)) {
                return;
            }
            const pos1 = myPlayer.pos.current;
            const pos2 = nearestEnemy.pos.current;
            const angle = pos1.angle(pos2);
            if (isReloadedPrimary) {
                ModuleHandler.moduleActive = true;
                ModuleHandler.forceWeapon = 0;
                ModuleHandler.useAngle = angle;
                ModuleHandler.shouldAttack = true;
                if (turretReloaded) {
                    ModuleHandler.forceHat = 53;
                }
            }
        }
    }

    class KnockbackTick {
        moduleName="knockbackTick";
        client;
        useTurret=false;
        constructor(client2) {
            this.client = client2;
        }
        postTick() {
            const {_ModuleHandler: ModuleHandler, EnemyManager: EnemyManager2, myPlayer: myPlayer} = this.client;
            if (ModuleHandler.moduleActive || !Settings_default._knockbackTick || EnemyManager2.shouldIgnoreModule()) {
                this.useTurret = false;
                return;
            }
            const nearestEnemySpikeCollider = EnemyManager2.nearestEnemySpikeCollider;
            const spikeCollider = EnemyManager2.spikeCollider;
            const reloading = ModuleHandler.staticModules.reloading;
            const primary = myPlayer.getItemByType(0);
            const primaryReloaded = reloading.isReloaded(0);
            const turretReloaded = ModuleHandler.hasStoreItem(0, 53) && reloading.isReloaded(2);
            if (this.useTurret) {
                this.useTurret = false;
                if (turretReloaded) {
                    ModuleHandler.moduleActive = true;
                    ModuleHandler.forceHat = 53;
                }
                return;
            }
            if (nearestEnemySpikeCollider !== null && !nearestEnemySpikeCollider.isTrapped && spikeCollider !== null && primaryReloaded) {
                const pos1 = myPlayer.pos.current;
                const pos2 = nearestEnemySpikeCollider.pos.current;
                const pos3 = spikeCollider.pos.current;
                const angleToEnemy = pos1.angle(pos2);
                const distanceToSpike2 = pos2.distance(pos3);
                const turretKnockback = 60;
                const primaryKnockback = DataHandler_default.getWeapon(primary).knockback;
                const knockback = primaryKnockback + turretKnockback;
                const collisionScale = spikeCollider.collisionScale + nearestEnemySpikeCollider.collisionScale;
                const collisionRangeTurret = collisionScale + knockback;
                const isPrimaryEnough = distanceToSpike2 <= collisionScale + primaryKnockback;
                if (distanceToSpike2 <= collisionRangeTurret) {
                    const spear = DataHandler_default.getWeapon(primary);
                    const hitRange = spear.range + nearestEnemySpikeCollider.hitScale;
                    if (myPlayer.collidingSimple(nearestEnemySpikeCollider, hitRange)) {
                        ModuleHandler.moduleActive = true;
                        ModuleHandler.useAngle = angleToEnemy;
                        ModuleHandler.forceHat = 7;
                        ModuleHandler.forceWeapon = 0;
                        ModuleHandler.shouldAttack = true;
                        if (!isPrimaryEnough) {
                            this.useTurret = true;
                        }
                        this.client.StatsManager.knockbackTickTimes = 1;
                        EnemyManager2.attemptSpikePlacement();
                    }
                }
            }
        }
    }

    class KnockbackTickHammer {
        moduleName="knockbackTickHammer";
        client;
        targetEnemy=null;
        constructor(client2) {
            this.client = client2;
        }
        postTick() {
            const {_ModuleHandler: ModuleHandler, EnemyManager: EnemyManager2, myPlayer: myPlayer} = this.client;
            if (ModuleHandler.moduleActive || !Settings_default._knockbackTickHammer || EnemyManager2.shouldIgnoreModule()) {
                this.targetEnemy = null;
                return;
            }
            const nearestEnemySpikeCollider = EnemyManager2.nearestEnemySpikeCollider;
            const spikeCollider = EnemyManager2.spikeCollider;
            const reloading = ModuleHandler.staticModules.reloading;
            const primary = myPlayer.getItemByType(0);
            const secondary = myPlayer.getItemByType(1);
            const isHammer = secondary !== null && secondary !== 11;
            const primaryReloaded = reloading.isReloaded(0, 1);
            const secondaryReloaded = reloading.isReloaded(1);
            const turretReloaded = reloading.isReloaded(2);
            const pos1 = myPlayer.pos.current;
            if (this.targetEnemy !== null) {
                const pos2 = this.targetEnemy.pos.current;
                const angleToEnemy = pos1.angle(pos2);
                ModuleHandler.moduleActive = true;
                ModuleHandler.useAngle = angleToEnemy;
                ModuleHandler.forceHat = 7;
                ModuleHandler.forceWeapon = 0;
                ModuleHandler.shouldAttack = true;
                this.targetEnemy = null;
                EnemyManager2.attemptSpikePlacement();
                return;
            }
            if (nearestEnemySpikeCollider !== null && !nearestEnemySpikeCollider.isTrapped && spikeCollider !== null && isHammer && primaryReloaded && secondaryReloaded && turretReloaded) {
                const pos2 = nearestEnemySpikeCollider.pos.current;
                const pos3 = spikeCollider.pos.current;
                const angleToEnemy = pos1.angle(pos2);
                const distanceToSpike2 = pos2.distance(pos3);
                const turretKnockback = 60;
                const {knockback: primaryKnockback, range: primaryRange} = DataHandler_default.getWeapon(primary);
                const {knockback: secondaryKnockback, range: secondaryRange} = DataHandler_default.getWeapon(secondary);
                const weaponRange = Math.min(primaryRange, secondaryRange) + nearestEnemySpikeCollider.hitScale;
                const minKB = primaryKnockback + turretKnockback;
                const maxKB = primaryKnockback + secondaryKnockback + turretKnockback;
                const spikeRange = spikeCollider.collisionScale + nearestEnemySpikeCollider.collisionScale;
                if (inRange(distanceToSpike2, spikeRange + minKB, spikeRange + maxKB) && myPlayer.collidingSimple(nearestEnemySpikeCollider, weaponRange)) {
                    const hammer = DataHandler_default.getWeapon(secondary);
                    const hitRange = hammer.range + nearestEnemySpikeCollider.hitScale;
                    if (myPlayer.collidingSimple(nearestEnemySpikeCollider, hitRange)) {
                        ModuleHandler.moduleActive = true;
                        ModuleHandler.useAngle = angleToEnemy;
                        ModuleHandler.forceHat = 53;
                        ModuleHandler.forceWeapon = 1;
                        ModuleHandler.shouldAttack = true;
                        this.targetEnemy = nearestEnemySpikeCollider;
                        this.client.StatsManager.knockbackTickHammerTimes = 1;
                        EnemyManager2.attemptSpikePlacement();
                    }
                }
            }
        }
    }

    class KnockbackTickTrap {
        moduleName="knockbackTickTrap";
        client;
        targetEnemy=null;
        useTurret=false;
        constructor(client2) {
            this.client = client2;
        }
        postTick() {
            const {_ModuleHandler: ModuleHandler, EnemyManager: EnemyManager2, myPlayer: myPlayer} = this.client;
            if (ModuleHandler.moduleActive || !Settings_default._knockbackTickTrap || EnemyManager2.shouldIgnoreModule()) {
                this.targetEnemy = null;
                this.useTurret = false;
                return;
            }
            const nearestEnemySpikeCollider = EnemyManager2.nearestEnemySpikeCollider;
            const nearestTrappedEnemy = EnemyManager2.nearestTrappedEnemy;
            const spikeCollider = EnemyManager2.spikeCollider;
            const reloading = ModuleHandler.staticModules.reloading;
            const primary = myPlayer.getItemByType(0);
            const secondary = myPlayer.getItemByType(1);
            const isHammer = secondary === 10;
            const primaryReloaded = reloading.isReloaded(0, 1);
            const secondaryReloaded = reloading.isReloaded(1);
            const turretReloaded = reloading.isReloaded(2);
            if (this.useTurret) {
                if (turretReloaded) {
                    ModuleHandler.moduleActive = true;
                    ModuleHandler.forceHat = 53;
                }
                this.useTurret = false;
                return;
            }
            const pos1 = myPlayer.pos.current;
            if (this.targetEnemy !== null) {
                const pos2 = this.targetEnemy.pos.current;
                const angleToEnemy = pos1.angle(pos2);
                ModuleHandler.moduleActive = true;
                ModuleHandler.useAngle = angleToEnemy;
                ModuleHandler.forceHat = 7;
                ModuleHandler.forceWeapon = 0;
                ModuleHandler.shouldAttack = true;
                this.targetEnemy = null;
                this.useTurret = true;
                EnemyManager2.attemptSpikePlacement();
                return;
            }
            if (nearestEnemySpikeCollider !== null && nearestTrappedEnemy !== null && nearestTrappedEnemy === nearestEnemySpikeCollider && spikeCollider !== null && isHammer && primaryReloaded && secondaryReloaded) {
                const nearestTrap = nearestTrappedEnemy.trappedIn;
                const hammer = DataHandler_default.getWeapon(secondary);
                const playerRange = hammer.range + nearestTrappedEnemy.hitScale;
                const trapRange = hammer.range + nearestTrap.hitScale;
                const canAttackEnemy = myPlayer.collidingSimple(nearestTrappedEnemy, playerRange);
                const canAttackTrap = myPlayer.collidingSimple(nearestTrap, trapRange);
                const buildingDamage = myPlayer.getBuildingDamage(secondary, true);
                if (!canAttackEnemy || !canAttackTrap || nearestTrap.health > buildingDamage) {
                    return;
                }
                const pos12 = myPlayer.pos.current;
                const pos2 = nearestTrappedEnemy.pos.current;
                const pos3 = nearestTrap.pos.current;
                const pos4 = spikeCollider.pos.current;
                const angleToEnemy = pos12.angle(pos2);
                const angleToTrap = pos12.angle(pos3);
                const middleAngle = findMiddleAngle(angleToEnemy, angleToTrap);
                const distanceToSpike2 = pos2.distance(pos4);
                const turretKnockback = 60;
                const primaryKnockback = DataHandler_default.getWeapon(primary).knockback;
                const knockback = primaryKnockback + turretKnockback;
                const collisionRange = spikeCollider.collisionScale + nearestEnemySpikeCollider.collisionScale + knockback;
                if (distanceToSpike2 <= collisionRange) {
                    ModuleHandler.moduleActive = true;
                    ModuleHandler.useAngle = middleAngle;
                    ModuleHandler.forceHat = 40;
                    ModuleHandler.forceWeapon = 1;
                    ModuleHandler.shouldAttack = true;
                    this.targetEnemy = nearestTrappedEnemy;
                    this.client.StatsManager.knockbackTickTrapTimes = 1;
                    EnemyManager2.attemptSpikePlacement();
                }
            }
        }
    }

    class SpikeSync {
        moduleName="spikeSync";
        client;
        useTurret=false;
        constructor(client2) {
            this.client = client2;
        }
        postTick() {
            const {_ModuleHandler: ModuleHandler, EnemyManager: EnemyManager2, myPlayer: myPlayer} = this.client;
            if (ModuleHandler.moduleActive || !Settings_default._spikeSync) {
                this.useTurret = false;
                return;
            }
            const nearest = EnemyManager2.nearestEnemy;
            const placementAngles = EnemyManager2.nearestSpikePlacerAngle;
            const reloading = ModuleHandler.staticModules.reloading;
            const primary = myPlayer.getItemByType(0);
            const isPolearm = primary !== 8;
            const primaryReloaded = reloading.isReloaded(0);
            const turretReloaded = reloading.isReloaded(2);
            if (this.useTurret) {
                this.useTurret = false;
                if (turretReloaded && !EnemyManager2.shouldIgnoreModule()) {
                    ModuleHandler.moduleActive = true;
                    ModuleHandler.forceHat = 53;
                }
                return;
            }
            if (!EnemyManager2.shouldIgnoreModule() && nearest !== null && EnemyManager2.canSpikeSync && placementAngles !== null && isPolearm && primaryReloaded && !ModuleHandler.staticModules.shameSpam.wasActive) {
                const spear = DataHandler_default.getWeapon(primary);
                const range = spear.range + nearest.hitScale;
                const canAttack = myPlayer.collidingSimple(nearest, range);
                if (!canAttack) {
                    return;
                }
                const pos1 = myPlayer.pos.current;
                const pos2 = nearest.pos.current;
                const angleTo = pos1.angle(pos2);
                const itemType = 4;
                for (const angle of placementAngles) {
                    ModuleHandler.place(itemType, angle);
                }
                ModuleHandler.placedOnce = true;
                ModuleHandler.placeAngles[0] = itemType;
                ModuleHandler.placeAngles[1] = placementAngles;
                ModuleHandler.moduleActive = true;
                ModuleHandler.useAngle = angleTo;
                ModuleHandler.forceHat = 7;
                ModuleHandler.forceWeapon = 0;
                ModuleHandler.shouldAttack = true;
                this.client.StatsManager.spikeSyncTimes = 1;
                this.useTurret = true;
            }
        }
    }

    class SpikeSyncHammer {
        moduleName="spikeSyncHammer";
        client;
        targetEnemy=null;
        useTurret=false;
        constructor(client2) {
            this.client = client2;
        }
        postTick() {
            const {_ModuleHandler: ModuleHandler, EnemyManager: EnemyManager2, myPlayer: myPlayer, ObjectManager: ObjectManager2} = this.client;
            if (ModuleHandler.moduleActive || !Settings_default._spikeSyncHammer || EnemyManager2.shouldIgnoreModule()) {
                this.targetEnemy = null;
                this.useTurret = false;
                return;
            }
            const nearestSyncEnemy = EnemyManager2.nearestSyncEnemy;
            const reloading = ModuleHandler.staticModules.reloading;
            const primary = myPlayer.getItemByType(0);
            const secondary = myPlayer.getItemByType(1);
            const isPolearm = primary !== 8;
            const isHammer = secondary === 10;
            const primaryReloaded = reloading.isReloaded(0, 1);
            const secondaryReloaded = reloading.isReloaded(1);
            const turretReloaded = reloading.isReloaded(2);
            if (this.useTurret) {
                if (turretReloaded) {
                    ModuleHandler.moduleActive = true;
                    ModuleHandler.forceHat = 53;
                }
                this.useTurret = false;
                return;
            }
            if (this.targetEnemy !== null) {
                const nearest = this.targetEnemy;
                const pos1 = myPlayer.pos.current;
                const pos2 = nearest.pos.current;
                const itemType = 4;
                const spikeID = myPlayer.getItemByType(itemType);
                const placeLength = myPlayer.getItemPlaceScale(spikeID);
                const angleToNearest = pos1.angle(pos2);
                const spikePos = pos1.addDirection(angleToNearest, placeLength);
                const angleFromSpike = spikePos.angle(pos2);
                const futureEnemyPos = spikePos.addDirection(angleFromSpike, 140);
                const futureAngle = pos1.angle(futureEnemyPos);
                const placementAngles = EnemyManager2.nearestSpikePlacerAngle;
                if (placementAngles !== null) {
                    for (const angle of placementAngles) {
                        ModuleHandler.place(itemType, angle);
                    }
                    ModuleHandler.placedOnce = true;
                    ModuleHandler.placeAngles[0] = itemType;
                    ModuleHandler.placeAngles[1] = placementAngles;
                    ModuleHandler.moduleActive = true;
                    ModuleHandler.useAngle = futureAngle;
                    ModuleHandler.forceHat = 7;
                    ModuleHandler.forceWeapon = 0;
                    ModuleHandler.shouldAttack = true;
                }
                this.targetEnemy = null;
                this.useTurret = true;
                return;
            }
            if (nearestSyncEnemy !== null && isPolearm && primaryReloaded && isHammer && secondaryReloaded) {
                const nearestLowHPObject = EnemyManager2.nearestLowHPObject;
                if (nearestLowHPObject === null) {
                    return;
                }
                const hammer = DataHandler_default.getWeapon(secondary);
                const playerRange = hammer.range + nearestSyncEnemy.hitScale;
                const trapRange = hammer.range + nearestLowHPObject.hitScale;
                const canAttackEnemy = myPlayer.collidingSimple(nearestSyncEnemy, playerRange);
                const canAttackTrap = myPlayer.collidingSimple(nearestLowHPObject, trapRange);
                const buildingDamage = myPlayer.getBuildingDamage(secondary, true);
                if (!canAttackEnemy || !canAttackTrap || nearestLowHPObject.health > buildingDamage) {
                    return;
                }
                const itemType = 4;
                const spikeID = myPlayer.getItemByType(itemType);
                const placeLength = myPlayer.getItemPlaceScale(spikeID);
                const pos1 = myPlayer.pos.current;
                const pos2 = nearestSyncEnemy.pos.current;
                const pos3 = nearestLowHPObject.pos.current;
                const angleToEnemy = pos1.angle(pos2);
                const angleToTrap = pos1.angle(pos3);
                const middleAngle = findMiddleAngle(angleToEnemy, angleToTrap);
                const angles = ObjectManager2.getBestPlacementAngles({
                    position: pos1,
                    id: spikeID,
                    targetAngle: angleToEnemy,
                    ignoreID: nearestLowHPObject.id,
                    preplace: false,
                    reduce: false,
                    fill: false
                });
                const spikeScale = Items[spikeID].scale;
                const possibleAngles = angles.filter(angle => {
                    const spikePos = pos1.addDirection(angle, placeLength);
                    const distance = pos2.distance(spikePos);
                    const range = nearestSyncEnemy.collisionScale + spikeScale;
                    return distance <= range;
                });
                if (possibleAngles.length !== 0) {
                    ModuleHandler.placeAngles[0] = itemType;
                    ModuleHandler.placeAngles[1] = possibleAngles;
                    ModuleHandler.moduleActive = true;
                    ModuleHandler.useAngle = middleAngle;
                    ModuleHandler.forceHat = 40;
                    ModuleHandler.forceWeapon = 1;
                    ModuleHandler.shouldAttack = true;
                    this.targetEnemy = nearestSyncEnemy;
                    this.client.StatsManager.spikeSyncHammerTimes = 1;
                }
            }
        }
    }

    class SpikeTick {
        moduleName="spikeTick";
        client;
        useTurret=false;
        constructor(client2) {
            this.client = client2;
        }
        postTick() {
            const {_ModuleHandler: ModuleHandler, EnemyManager: EnemyManager2, myPlayer: myPlayer} = this.client;
            if (ModuleHandler.moduleActive || !Settings_default._spikeTick) {
                return;
            }
            const reloading = ModuleHandler.staticModules.reloading;
            const primary = myPlayer.getItemByType(0);
            const isPrimary = primary !== 8;
            const primaryReloaded = reloading.isReloaded(0);
            const turretReloaded = ModuleHandler.hasStoreItem(0, 53) && reloading.isReloaded(2);
            const spikeCollider = EnemyManager2.enemySpikeCollider;
            if (this.useTurret) {
                this.useTurret = false;
                if (turretReloaded) {
                    ModuleHandler.moduleActive = true;
                    ModuleHandler.forceHat = 53;
                }
                return;
            }
            if (EnemyManager2.shouldIgnoreModule() || !isPrimary || !primaryReloaded || spikeCollider === null) {
                return;
            }
            const weaponRange = DataHandler_default.getWeapon(primary).range;
            const range = weaponRange + spikeCollider.hitScale;
            if (!myPlayer.collidingEntity(spikeCollider, range, true)) {
                return;
            }
            const pos1 = myPlayer.pos.future;
            const pos2 = spikeCollider.pos.future;
            const angle = pos1.angle(pos2);
            ModuleHandler.moduleActive = true;
            ModuleHandler.useAngle = angle;
            ModuleHandler.forceHat = 7;
            ModuleHandler.forceWeapon = 0;
            ModuleHandler.shouldAttack = true;
            EnemyManager2.attemptSpikePlacement();
            this.useTurret = true;
            this.client.StatsManager.spikeTickTimes = 1;
        }
    }

    const SpikeTick_default = SpikeTick;

    class ToolHammerSpearInsta {
        moduleName="toolHammerSpearInsta";
        client;
        nearestTarget=null;
        useTurret=false;
        constructor(client2) {
            this.client = client2;
        }
        postTick() {
            const {_ModuleHandler: ModuleHandler, myPlayer: myPlayer, EnemyManager: EnemyManager2} = this.client;
            if (ModuleHandler.moduleActive || !Settings_default._toolSpearInsta) {
                this.nearestTarget = null;
                return;
            }
            const nearestEnemy = EnemyManager2.nearestEnemy;
            if (nearestEnemy === null || !ModuleHandler.canBuy(0, 7)) {
                return;
            }
            if (this.useTurret) {
                if (ModuleHandler.canBuy(0, 53)) {
                    ModuleHandler.moduleActive = true;
                    ModuleHandler.forceHat = 53;
                }
                this.useTurret = false;
                return;
            }
            if (myPlayer.upgradeAge !== 2) {
                return;
            }
            const pos1 = myPlayer.pos.current;
            if (this.nearestTarget !== null) {
                const pos22 = this.nearestTarget.pos.current;
                const angle2 = pos1.angle(pos22);
                ModuleHandler.moduleActive = true;
                ModuleHandler.useAngle = angle2;
                ModuleHandler.forceHat = 7;
                ModuleHandler.forceWeapon = 0;
                ModuleHandler.shouldAttack = true;
                ModuleHandler._upgradeItem(5);
                this.nearestTarget = null;
                this.useTurret = true;
                EnemyManager2.attemptSpikePlacement();
                return;
            }
            const pos2 = nearestEnemy.pos.current;
            const angle = pos1.angle(pos2);
            const {reloading: reloading} = ModuleHandler.staticModules;
            const primaryReloaded = reloading.isReloaded(0);
            const turretReloaded = reloading.isReloaded(2);
            const range = DataHandler_default.getWeapon(0).range + nearestEnemy.hitScale;
            if (!primaryReloaded || !turretReloaded || !myPlayer.collidingSimple(nearestEnemy, range)) {
                return;
            }
            ModuleHandler.moduleActive = true;
            ModuleHandler.useAngle = angle;
            ModuleHandler.forceHat = 7;
            ModuleHandler.forceWeapon = 0;
            ModuleHandler.shouldAttack = true;
            this.nearestTarget = nearestEnemy;
        }
    }

    class VelocityTick {
        moduleName="velocityTick";
        nearestTarget=null;
        target=null;
        minKB=220;
        maxKB=245;
        phase=null;
        started=-1;
        claimedTick=-1;
        issuedTick=-1;
        constructor(client2) { this.client = client2; }
        reset() {
            this.nearestTarget = this.target = null;
            this.phase = null;
            this.started = this.claimedTick = this.issuedTick = -1;
        }
        isValidHat(hatID) { return hatID !== null && hatID !== 6 && hatID !== 22; }
        validTarget(enemy) {
            const {myPlayer: player, PlayerManager: players, EnemyManager: enemies, _ModuleHandler: handler} = this.client;
            return player.inGame && player.currentHealth > 0 && player.tempHealth > 0 &&
                enemy?.isPlayer && enemy.currentHealth > 0 && enemy.tempHealth > 0 &&
                players.playerData.get(enemy.id) === enemy && enemies.nearestEnemy === enemy && player.isEnemyByID(enemy.id) &&
                player.getItemByType(0) === 5 && player.getWeaponVariant(5).current >= 2 &&
                handler.hasStoreItem(0, 53) && handler.hasStoreItem(0, 7);
        }
        postTick() {
            const {EnemyManager: enemies, myPlayer: player, _ModuleHandler: handler, InputHandler: input} = this.client;
            this.target = null;
            this.claimedTick = this.issuedTick = -1;
            if (handler.moduleActive || !Settings_default._velocityTick || input.instaToggle || handler.pendingSync || handler.syncExecuting ||
                handler.moveTo !== "disable" || enemies.shouldIgnoreModule()) { this.reset(); return; }
            const enemy = this.nearestTarget || enemies.nearestEnemy;
            if (!this.validTarget(enemy)) { this.reset(); return; }
            const reloading = handler.staticModules.reloading;
            if (!this.nearestTarget) {
                if (!reloading.isReloaded(0, 1) || !reloading.isReloaded(2)) return;
                this.target = enemy;
                const weapon = DataHandler_default.getWeapon(enemy.weapon.current);
                const almostReloaded = DataHandler_default.isMelee(enemy.weapon.current) && enemy.atExact(weapon.itemType, 1);
                if (!inRange(player.pos.current.distance(enemy.pos.future), this.minKB, this.maxKB) ||
                    !(almostReloaded || this.isValidHat(enemy.futureHat))) return;
                this.nearestTarget = enemy;
                this.started = handler.tickCount;
                this.phase = "turret";
                this.client.StatsManager.velocityTickTimes = 1;
            } else {
                const timeout = Math.min(10, Math.max(5, Math.ceil((this.client.SocketManager.pong || 0) / 111) + 3));
                if (handler.tickCount - this.started > timeout || player.pos.current.distance(enemy.pos.current) > this.maxKB) {
                    this.reset(); return;
                }
            }
            this.claimedTick = handler.tickCount;
            handler.moduleActive = true;
            handler.useAngle = player.pos.current.angle(this.phase === "turret" ? enemy.pos.future : enemy.pos.current);
            handler.moveTo = handler.useAngle;
            // Unheld weapons do not reload. Select the primary during the turret lead-in.
            handler.forceWeapon = 0;
            handler.forceHat = this.phase === "turret" ? 53 : 7;
            const range = DataHandler_default.getWeapon(5).range + enemy.hitScale;
            handler.shouldAttack = this.phase === "primary" && reloading.isReloaded(0) &&
                player.pos.current.distance(enemy.pos.current) <= range;
            if (handler.shouldAttack) this.issuedTick = handler.tickCount;
        }
        beforeAttack() {
            const handler = this.client._ModuleHandler;
            if (!this.nearestTarget || this.claimedTick !== handler.tickCount) return;
            if (handler.syncExecuting) { this.reset(); return; }
            const expectedHat = this.phase === "turret" ? 53 : 7;
            if (!this.validTarget(this.nearestTarget) || this.client.InputHandler.instaToggle ||
                handler.forceHat !== expectedHat || handler.getHatStore().last !== expectedHat || handler.forceWeapon !== 0) {
                handler.shouldAttack = false;
                this.reset();
            }
        }
        afterAttack() {
            const handler = this.client._ModuleHandler;
            if (!this.nearestTarget || this.claimedTick !== handler.tickCount) return;
            if (this.phase === "turret") { this.phase = "primary"; return; }
            // PreAttack or another module may suppress a hit. Keep the pending target until one is sent.
            if (this.issuedTick === handler.tickCount && handler.attacked && handler.weapon === 0 && handler.getHatStore().last === 7) this.reset();
        }
    }

    class Placer {
        moduleName="placer";
        client;
        constructor(client2) {
            this.client = client2;
        }
        postTick() {
            const {_ModuleHandler: ModuleHandler, myPlayer: myPlayer} = this.client;
            const {currentType: currentType, placedOnce: placedOnce, healedOnce: healedOnce, _currentAngle: currentAngle} = ModuleHandler;
            if (!myPlayer.canPlace(currentType)) {
                return;
            }
            if (currentType === 2) {
                if (healedOnce) {
                    return;
                }
                if (myPlayer.shameCount < 7 && ModuleHandler.heal()) {
                    ModuleHandler.healedOnce = true;
                    ModuleHandler.didAntiInsta = true;
                }
                return;
            }
            if (placedOnce) {
                return;
            }
            ModuleHandler.place(currentType, currentAngle);
            ModuleHandler.placedOnce = true;
        }
    }

    const Placer_default = Placer;

    class PreAttack {
        moduleName="preAttack";
        client;
        constructor(client2) {
            this.client = client2;
        }
        isReloadedByType(type) {
            const {weapon: weapon, staticModules: staticModules} = this.client._ModuleHandler;
            const weaponType = type !== null ? type : weapon;
            return staticModules.reloading.isReloaded(weaponType);
        }
        postTick() {
            const {_ModuleHandler: ModuleHandler} = this.client;
            const {useWeapon: useWeapon, weapon: weapon, forceWeapon: forceWeapon} = ModuleHandler;
            const nextWeapon = forceWeapon !== null ? forceWeapon : useWeapon;
            const forceReloaded = this.isReloadedByType(nextWeapon);
            const canAttack = ModuleHandler.shouldAttack && (forceReloaded && this.isReloadedByType(weapon) || forceWeapon !== null && forceReloaded);
            ModuleHandler.shouldAttack = canAttack;
        }
    }

    const PreAttack_default = PreAttack;

    class Reloading {
        moduleName="reloading";
        client;
        clientReload=[ {}, {}, {} ];
        constructor(client2) {
            this.client = client2;
            this.reset();
        }
        reset() {
            const [primary, secondary, turret] = this.clientReload;
            primary.current = primary.max = 0;
            secondary.current = secondary.max = 0;
            turret.current = turret.max = 23;
            for (const reload of this.clientReload) reload.completion = null;
        }
        get currentReload() {
            return this.clientReload[this.client._ModuleHandler.weapon];
        }
        getReload(type) {
            return this.clientReload[type];
        }
        updateMaxReload(type) {
            const {myPlayer: myPlayer, _ModuleHandler: ModuleHandler, SocketManager: SocketManager2} = this.client;
            const reload = this.getReload(type);
            const id = myPlayer.getItemByType(type);
            const store2 = ModuleHandler.getHatStore();
            const pingAccount = Math.floor(SocketManager2.pong / SocketManager2.TICK);
            const speed = myPlayer.getWeaponSpeed(id, store2.last) - pingAccount;
            reload.current = speed;
            reload.max = speed;
            reload.completion = null;
        }
        resetReload(reload) {
            reload.current = -1;
            reload.completion = null;
        }
        resetByType(type) {
            this.resetReload(this.getReload(type));
        }
        isReloaded(type, ticks = 0) {
            if (this.client._ModuleHandler.norecoil) {
                return true;
            }
            const reload = this.clientReload[type];
            return reload.current >= Math.max(0, reload.max - ticks);
        }
        isFasterThan(type1, type2) {
            const reload1 = this.clientReload[type1];
            const reload2 = this.clientReload[type2];
            const data1 = reload1.max - reload1.current;
            const data2 = reload2.max - reload2.current;
            return Math.abs(data1) <= Math.abs(data2);
        }
        isEmptyReload(type) {
            const reload = this.clientReload[type];
            return reload.current === 0;
        }
        botReloadCurrent(type) {
            const {myPlayer: player, SocketManager: socket} = this.client;
            const observed = player.reload[type], reload = this.clientReload[type];
            const weapon = player.getItemByType(type);
            if (weapon === null || observed.max <= 0 || observed.current !== observed.max ||
                !Number.isFinite(reload.max) || reload.max <= observed.max) {
                reload.completion = null;
                return observed.current;
            }
            // An observed reload can cap below the command's estimate after a hat/weapon change.
            // Finish the remaining ticks only while the server reports this weapon held.
            // Preserve the original duration instead of declaring the shorter counter ready.
            let completion = reload.completion;
            if (!completion || completion.weapon !== weapon || completion.cap !== observed.max || completion.target !== reload.max) {
                completion = reload.completion = {weapon, cap:observed.max, target:reload.max, current:observed.current, tick:player.tickCount};
            } else if (completion.tick !== player.tickCount) {
                if (player.inGame && socket.socket?.readyState === 1 && player.currentItem === -1 && player.weapon.current === weapon) {
                    completion.current = Math.min(reload.max, completion.current + 1);
                }
                completion.tick = player.tickCount;
            }
            return completion.current;
        }
        postTick() {
            const {myPlayer: myPlayer} = this.client;
            const primaryReload = myPlayer.reload[0].current;
            const secondaryReload = myPlayer.reload[1].current;
            if (primaryReload !== -1) {
                this.clientReload[0].current = this.botReloadCurrent(0);
            }
            if (secondaryReload !== -1) {
                this.clientReload[1].current = this.botReloadCurrent(1);
            }
            this.clientReload[2].current = myPlayer.reload[2].current;
        }
    }

    const Reloading_default = Reloading;

    class UpdateAngle {
        moduleName="updateAngle";
        client;
        constructor(client2) {
            this.client = client2;
        }
        postTick() {
            const {sentAngle: sentAngle, _currentAngle: currentAngle} = this.client._ModuleHandler;
            if (sentAngle > 1) {
                return;
            }
            this.client._ModuleHandler.updateAngle(currentAngle);
        }
    }

    const UpdateAngle_default = UpdateAngle;

    class UpdateAttack {
        moduleName="updateAttack";
        client;
        didReset=false;
        constructor(client2) {
            this.client = client2;
        }
        getAttackAngle() {
            const {useAngle: useAngle, _currentAngle: currentAngle} = this.client._ModuleHandler;
            if (useAngle !== null) {
                return useAngle;
            }
            return currentAngle;
        }
        postTick() {
            const {_ModuleHandler: ModuleHandler, myPlayer: myPlayer} = this.client;
            const {useWeapon: useWeapon, forceWeapon: forceWeapon, weapon: weapon, attacking: attacking, useItem: useItem, sentAngle: sentAngle, staticModules: staticModules} = ModuleHandler;
            const {reloading: reloading} = staticModules;
            const nextWeapon = forceWeapon !== null ? forceWeapon : useWeapon;
            if (nextWeapon !== null && (nextWeapon !== weapon || ModuleHandler.currentHolding !== nextWeapon || myPlayer.currentItem !== -1)) {
                const isReloaded = reloading.isReloaded(weapon);
                if (isReloaded || forceWeapon !== null) {
                    ModuleHandler.whichWeapon(nextWeapon);
                }
            }
            if (useItem !== null) {
                ModuleHandler.selectItem(useItem);
            }
            if (ModuleHandler.shouldAttack) {
                const angle = this.getAttackAngle();
                ModuleHandler.attack(angle);
                ModuleHandler.stopAttack();
                const weaponType = ModuleHandler.weapon;
                if (ModuleHandler.attacked) {
                    reloading.updateMaxReload(weaponType);
                }
                reloading.resetByType(weaponType);
            } else if (!attacking && sentAngle !== 0) {
                ModuleHandler.stopAttack();
                this.didReset = true;
            } else if (this.didReset) {
                this.didReset = false;
                ModuleHandler.stopAttack();
            }
        }
    }

    const UpdateAttack_default = UpdateAttack;

    class UseAttacking {
        moduleName="useAttacking";
        client;
        constructor(client2) {
            this.client = client2;
        }
        getWeaponType(asLeftClick = false) {
            const {EnemyManager: EnemyManager2, myPlayer: myPlayer, _ModuleHandler: ModuleHandler} = this.client;
            const pos1 = myPlayer.pos.future;
            const nearestEnemy = EnemyManager2.nearestEnemy;
            const nearestAnimal = EnemyManager2.nearestAnimal;
            const nearestObject = EnemyManager2.nearestObject;
            const primaryID = myPlayer.getItemByType(0);
            const secondaryID = myPlayer.getItemByType(1);
            const primary = DataHandler_default.getWeapon(primaryID);
            const range = primary.range;
            if (nearestEnemy !== null) {
                const pos2 = nearestEnemy.pos.future;
                const angle = pos1.angle(pos2);
                if (myPlayer.collidingEntity(nearestEnemy, range + nearestEnemy.hitScale)) {
                    return [ 0, angle ];
                }
                if (DataHandler_default.isShootable(secondaryID) && (asLeftClick || !ModuleHandler.autoattack || ModuleHandler.pointerAttack === 1 || ModuleHandler.pendingPointerAttack === 1)) {
                    return [ 1, angle ];
                }
            }
            if (nearestAnimal !== null) {
                const pos2 = nearestAnimal.pos.future;
                const angle = pos1.angle(pos2);
                if (myPlayer.collidingEntity(nearestAnimal, range + nearestAnimal.hitScale)) {
                    return [ 0, angle ];
                }
                if (DataHandler_default.isShootable(secondaryID) && (asLeftClick || !ModuleHandler.autoattack || ModuleHandler.pointerAttack === 1 || ModuleHandler.pendingPointerAttack === 1)) {
                    return [ 1, angle ];
                }
            }
            if (nearestObject === null) {
                return null;
            }
            if (myPlayer.colliding(nearestObject, range + nearestObject.hitScale)) {
                return [ 0, null ];
            }
            return null;
        }
        postTick() {
            if (Settings_default._manualAim) { CombatControl.useAttack(this.client); return; }
            const {_ModuleHandler: ModuleHandler} = this.client;
            if (ModuleHandler.moduleActive || ModuleHandler.attackingState !== 1 || ModuleHandler.forceWeapon !== null) {
                return;
            }
            const weaponType = this.getWeaponType() || (ModuleHandler.autoattack ? [ModuleHandler.weapon, null] : null);
            if (weaponType === null) {
                return;
            }
            const [type, angle] = weaponType;
            ModuleHandler.forceWeapon = type;
            if (angle !== null) {
                ModuleHandler.useAngle = angle;
            }
            ModuleHandler.shouldAttack = true;
            ModuleHandler.autoattackClaim = ModuleHandler.autoattack && !ModuleHandler.pointerAttack && !ModuleHandler.pendingPointerAttack;
        }
    }

    class UseDestroying {
        moduleName="useDestroying";
        client;
        constructor(client2) {
            this.client = client2;
        }
        postTick() {
            const {myPlayer: myPlayer, _ModuleHandler: ModuleHandler, EnemyManager: EnemyManager2} = this.client;
            if (ModuleHandler.moduleActive || ModuleHandler.attackingState !== 2 || ModuleHandler.forceWeapon !== null) {
                return;
            }
            const nearestObject = EnemyManager2.nearestPlayerObject;
            const type = myPlayer.getBestDestroyingWeapon(nearestObject);
            ModuleHandler.forceWeapon = type;
            ModuleHandler.shouldAttack = true;
        }
    }

    class UseFastest {
        moduleName="useFastest";
        client;
        constructor(client2) {
            this.client = client2;
        }
        postTick() {
            if (Settings_default._manualAim) {
                const handler = this.client._ModuleHandler;
                if (!handler.moduleActive && handler.forceWeapon === null && !this.client.InputHandler.instaToggle) {
                    const selected = CombatControl.selected(this.client);
                    const other = selected === 0 ? 1 : 0;
                    const reload = handler.staticModules.reloading;
                    handler.useWeapon = !reload.isReloaded(selected) ? selected : this.client.myPlayer.getItemByType(other) !== null && !reload.isReloaded(other) ? other : selected;
                }
                return;
            }
            const {myPlayer: myPlayer, _ModuleHandler: ModuleHandler} = this.client;
            if (ModuleHandler.moduleActive) {
                return;
            }
            const {reloading: reloading} = ModuleHandler.staticModules;
            const type = myPlayer.getFastestWeapon();
            const reverse_type = type === 0 ? 1 : 0;
            if (!reloading.isReloaded(type)) {
                ModuleHandler.useWeapon = type;
            } else if (!reloading.isReloaded(reverse_type) && myPlayer.getItemByType(reverse_type) !== null) {
                ModuleHandler.useWeapon = reverse_type;
            } else {
                ModuleHandler.useWeapon = type;
            }
        }
    }

    class UtilityHat {
        moduleName="utilityHat";
        client;
        constructor(client2) {
            this.client = client2;
        }
        getBestUtilityHat(weaponType) {
            const {_ModuleHandler: ModuleHandler, EnemyManager: EnemyManager2, myPlayer: myPlayer} = this.client;
            const id = myPlayer.getItemByType(weaponType);
            if (id === 11) {
                return null;
            }
            if (DataHandler_default.isShootable(id)) {
                ModuleHandler.canHitEntity = true;
                return 20;
            }
            const weapon = DataHandler_default.getWeapon(id);
            const range = weapon.range;
            if (weapon.damage <= 1) {
                return null;
            }
            if (ModuleHandler.attackingState === 1) {
                const nearest = EnemyManager2.nearestEntity;
                if (nearest !== null && myPlayer.collidingEntity(nearest, range + nearest.hitScale)) {
                    ModuleHandler.canHitEntity = true;
                    return 7;
                }
            }
            if (ModuleHandler.attackingState !== 0) {
                const nearestObject = EnemyManager2.nearestPlayerObject;
                if (nearestObject === null) {
                    return null;
                }
                if (myPlayer.colliding(nearestObject, range + nearestObject.hitScale)) {
                    return 40;
                }
            }
            return null;
        }
        postTick() {
            const {_ModuleHandler: ModuleHandler, EnemyManager: EnemyManager2, myPlayer: myPlayer} = this.client;
            if (ModuleHandler.moduleActive) {
                return;
            }
            const {forceWeapon: forceWeapon, useWeapon: useWeapon, weapon: weapon} = ModuleHandler;
            const weaponType = forceWeapon !== null ? forceWeapon : useWeapon !== null ? useWeapon : weapon;
            let hat = this.getBestUtilityHat(weaponType);
            const {reloading: reloading} = ModuleHandler.staticModules;
            const isReloaded = reloading.isReloaded(weaponType);
            const isEmptyReload = reloading.isEmptyReload(weaponType);
            const turretReloaded = reloading.isReloaded(2);
            if (!isReloaded) {
                hat = null;
            }
            if (ModuleHandler.canHitEntity && isEmptyReload && turretReloaded) {
                const nearest = EnemyManager2.nearestEntity;
                if (nearest !== null && myPlayer.collidingEntity(nearest, 700)) {
                    hat = 53;
                }
            }
            if (hat !== null) {
                ModuleHandler.useHat = hat;
            }
        }
    }

    class AntiInsta {
        moduleName="antiInsta";
        client;
        toggleAnti=false;
        healingCount=0;
        forceHeal=false;
        pending=[];
        pendingSocket=null;
        resourceSnapshot=null;
        missedAcknowledgements=0;
        fastHealDamage=null;
        retryAfter=0;
        constructor(client2) {
            this.client = client2;
        }
        get enhanced() {
            return ServerCapacity.usesHealAcknowledgements(this.client);
        }
        reset() {
            this.pending.length = 0;
            this.pendingSocket = null;
            this.resourceSnapshot = null;
            this.missedAcknowledgements = 0;
            this.fastHealDamage = null;
            this.retryAfter = 0;
            this.forceHeal = false;
        }
        pendingRestore() {
            const socket = this.client.SocketManager.socket;
            if (this.pendingSocket !== socket) {
                this.reset();
                this.pendingSocket = socket;
            }
            const now = performance.now();
            const resources = this.client.myPlayer.resources;
            if (this.resourceSnapshot) {
                for (const key of ['food', 'wood', 'stone', 'gold']) {
                    let spent = Math.max(0, this.resourceSnapshot[key] - resources[key]);
                    for (const entry of this.pending) {
                        const confirmed = Math.min(spent, entry.cost[key] || 0);
                        entry.cost[key] -= confirmed;
                        spent -= confirmed;
                        if (spent === 0) break;
                    }
                }
            }
            this.resourceSnapshot = {...resources};
            const before = this.pending.length;
            this.pending = this.pending.filter(entry => entry.expiresAt > now);
            if (this.pending.length < before) this.missedAcknowledgements = Math.min(3, this.missedAcknowledgements + 1);
            return this.pending.reduce((total, entry) => total + entry.amount, 0);
        }
        acknowledgementWindow() {
            const ping = Number(this.client.SocketManager.pong) || 0;
            const step = Number(this.client.PlayerManager.step) || 111;
            const base = Math.max(400, ping + Math.min(250, step) * 2 + 100);
            return Math.min(2000, base * 2 ** this.missedAcknowledgements);
        }
        planHeal() {
            const {myPlayer: player, SocketManager: socket} = this.client;
            if (!player.inGame || player.currentHealth <= 0 || player.shameActive || this.client.disconnectRequested ||
                socket.socket?.readyState !== 1) return null;
            const pending = this.pendingRestore();
            if (performance.now() < this.retryAfter) return null;
            const food = Items[player.getItemByType(2)];
            if (!food || !(food.restore > 0) || !player.canPlace(2)) return null;
            const amount = Math.min(food.restore, player.maxHealth - player.tempHealth - pending);
            if (amount <= 0) return null;
            if (!player.isSandbox) {
                for (const key of ['food', 'wood', 'stone', 'gold']) {
                    const reserved = this.pending.reduce((total, entry) => total + (entry.cost[key] || 0), 0);
                    if (player.resources[key] < reserved + (food.cost[key] || 0)) return null;
                }
            }
            return {amount, cost:{...food.cost}, expiresAt:performance.now() + this.acknowledgementWindow()};
        }
        recordHeal(plan) {
            this.pending.push(plan);
            const hit = this.client.myPlayer.receivedDamage;
            // A late health acknowledgement must not disguise a locally requested fast heal.
            if (hit !== null && Date.now() - hit <= 120) this.fastHealDamage = hit;
        }
        healthUpdate(previous, current) {
            if (!this.enhanced) { this.reset(); return; }
            if (current <= 0 || this.client.myPlayer.shameActive) { this.reset(); return; }
            this.pendingRestore();
            let restored = Math.max(0, current - previous);
            if (restored > 0) {
                this.missedAcknowledgements = 0;
                this.retryAfter = 0;
                this.fastHealDamage = null;
                for (const entry of this.pending) {
                    const used = Math.min(restored, entry.amount);
                    entry.amount -= used;
                    restored -= used;
                    if (restored === 0) break;
                }
                this.pending = this.pending.filter(entry => entry.amount > 0);
            } else if (current < previous) {
                this.fastHealDamage = null;
            }
            if (current >= this.client.myPlayer.maxHealth) this.pending.length = 0;
        }
        isSaveHealTime() {
            const hit = this.client.myPlayer.receivedDamage;
            if (!this.enhanced) return Date.now() - (hit || 0) + this.client.SocketManager.pong >= 125;
            // Keep the existing window, but do not spend an estimated round-trip time early.
            return hit === null || Date.now() - hit >= 125;
        }
        isSaveHealTick() {
            const {tickCount: tickCount, damageTick: damageTick} = this.client.myPlayer;
            return tickCount - damageTick > 0;
        }
        isSaveHeal() {
            return this.isSaveHealTime();
        }
        postTick() {
            this.forceHeal = false;
            if (!this.enhanced) {
                this.reset();
                this.legacyPostTick();
                return;
            }
            if (!Settings_default._autoheal) {
                return;
            }
            const {myPlayer: myPlayer, _ModuleHandler: ModuleHandler, EnemyManager: EnemyManager2} = this.client;
            if (!myPlayer.inGame || myPlayer.currentHealth <= 0 || myPlayer.shameActive || this.client.SocketManager.socket?.readyState !== 1) {
                this.reset();
                return;
            }
            const pending = this.pendingRestore();
            const foodID = myPlayer.getItemByType(2);
            const restore = Items[foodID]?.restore;
            if (!(restore > 0)) return;
            const needTimes = Math.ceil((myPlayer.maxHealth - myPlayer.tempHealth - pending) / restore);
            if (needTimes <= 0) return;
            const needsSoldier = myPlayer.hatID !== 6 && (ModuleHandler.shouldEquipSoldier || EnemyManager2.dangerWithoutSoldier);
            if (EnemyManager2.velocityTickThreat || EnemyManager2.reverseInsta || EnemyManager2.toolHammerInsta || EnemyManager2.rangedBowInsta || EnemyManager2.detectedDangerEnemy || EnemyManager2.detectedEnemy || myPlayer.tempHealth <= 20 || needsSoldier) {
                this.forceHeal = true;
            }
            const urgent = myPlayer.shameCount < 7 && this.forceHeal && myPlayer.tempHealth < 95;
            if (!urgent && !this.isSaveHeal()) return;
            for (let i = 0; i < needTimes; i++) {
                if (!ModuleHandler.heal()) break;
                ModuleHandler.healedOnce = true;
                if (urgent) ModuleHandler.didAntiInsta = true;
            }
        }
        legacyPostTick() {
            if (!Settings_default._autoheal) return;
            const {myPlayer: player, _ModuleHandler: handler, EnemyManager: enemies} = this.client;
            if (player.shameActive) return;
            const restore = Items[player.getItemByType(2)].restore;
            const needTimes = Math.ceil((player.maxHealth - player.tempHealth) / restore);
            let healingTimes = null;
            if (enemies.velocityTickThreat || enemies.reverseInsta || enemies.toolHammerInsta || enemies.rangedBowInsta ||
                enemies.detectedDangerEnemy || enemies.detectedEnemy || player.tempHealth <= 20 ||
                handler.shouldEquipSoldier && handler.forceHat !== 6 || enemies.dangerWithoutSoldier) this.forceHeal = true;
            if (player.shameCount < 7 && this.forceHeal && player.tempHealth < 95) {
                handler.didAntiInsta = true;
                healingTimes = needTimes || 1;
            } else if (this.isSaveHeal() && player.tempHealth < 100) healingTimes = needTimes || 1;
            if (healingTimes !== null) {
                handler.healedOnce = true;
                for (let i = 0; i <= healingTimes; i++) handler.heal();
            }
        }
    }

    const AntiInsta_default = AntiInsta;

    class Autohat {
        moduleName="autoHat";
        client;
        constructor(client2) {
            this.client = client2;
        }
        handleEquip(type, use) {
            const {_ModuleHandler: ModuleHandler} = this.client;
            if (type === 0 && ModuleHandler.forceHat !== null) {
                use = ModuleHandler.forceHat;
            }
            if (use !== null && ModuleHandler._equip(type, use)) {
                return true;
            }
            return false;
        }
        getNextHat() {
            const {_ModuleHandler: ModuleHandler, myPlayer: myPlayer} = this.client;
            if (ModuleHandler.forceHat !== null) {
                return ModuleHandler.forceHat;
            }
            if (ModuleHandler.useHat !== null) {
                return ModuleHandler.useHat;
            }
            return myPlayer.hatID;
        }
        getNextAcc() {
            const {_ModuleHandler: ModuleHandler, myPlayer: myPlayer} = this.client;
            if (ModuleHandler.useAcc !== null) {
                return ModuleHandler.useAcc;
            }
            return myPlayer.accessoryID;
        }
        getNextWeaponID() {
            const {_ModuleHandler: ModuleHandler, myPlayer: myPlayer} = this.client;
            if (ModuleHandler.forceWeapon !== null) {
                return myPlayer.getItemByType(ModuleHandler.forceWeapon);
            }
            if (ModuleHandler.useWeapon !== null) {
                return myPlayer.getItemByType(ModuleHandler.useWeapon);
            }
            return myPlayer.weapon.current;
        }
        getNextItemID() {
            const {_ModuleHandler: ModuleHandler, myPlayer: myPlayer} = this.client;
            if (ModuleHandler.useItem !== null) {
                return myPlayer.getItemByType(ModuleHandler.useItem);
            }
            return myPlayer.currentItem;
        }
        postTick() {
            const {_ModuleHandler: ModuleHandler} = this.client;
            // Copied bot equipment must not consume a later forced combat hat.
            const pendingForcedHat = ModuleHandler.forceHat !== null && ModuleHandler.getHatStore().last !== ModuleHandler.forceHat;
            if (!ModuleHandler.sentHatEquip || pendingForcedHat) {
                this.handleEquip(0, ModuleHandler.useHat);
            }
            if (!ModuleHandler.sentAccEquip && !ModuleHandler.sentHatEquip) {
                this.handleEquip(1, ModuleHandler.useAcc);
            }
        }
    }

    const Autohat_default = Autohat;

    class DefaultAcc {
        moduleName="defaultAcc";
        client;
        constructor(client2) {
            this.client = client2;
        }
        shouldUseTail() {
            const {_ModuleHandler: ModuleHandler, myPlayer: myPlayer} = this.client;
            const {reloading: reloading} = ModuleHandler.staticModules;
            const primary = myPlayer.getItemByType(0);
            const secondary = myPlayer.getItemByType(1);
            // Ranged shot / autoshoot: Monkey Tail cuts damage — always off
            if (ModuleHandler.autoShootExecuting || ModuleHandler.forceWeapon === 1) {
                if (DataHandler_default.isShootable(secondary)) return false;
            }
            if (ModuleHandler.shouldAttack && ModuleHandler.forceWeapon === 1 && DataHandler_default.isShootable(secondary)) {
                return false;
            }
            const isMelee1 = DataHandler_default.isMelee(primary);
            const isMelee2 = DataHandler_default.isMelee(secondary);
            // Stick (8) speed tail only when NOT about to fire secondary
            if (isMelee1 && primary === 8 && !(ModuleHandler.forceWeapon === 1 && DataHandler_default.isShootable(secondary))) {
                return true;
            }
            return isMelee1 && !reloading.isReloaded(0, 3) || isMelee2 && !reloading.isReloaded(1, 3);
        }
        getBestCurrentAcc() {
            const {_ModuleHandler: ModuleHandler, EnemyManager: EnemyManager2} = this.client;
            const {actual: actual} = ModuleHandler.getAccStore();
            const useCorrupt = ModuleHandler.canBuy(1, 21);
            const useShadow = ModuleHandler.canBuy(1, 19);
            const useTail = ModuleHandler.canBuy(1, 11);
            const useActual = ModuleHandler.canBuy(1, actual);
            if (Settings_default._tailPriority && useTail && this.shouldUseTail()) {
                return 11;
            }
            if (EnemyManager2.detectedEnemy || EnemyManager2.nearestEnemyInRangeOf(300, EnemyManager2.nearestEntity)) {
                const isEnemy = EnemyManager2.nearestEntity === EnemyManager2.nearestEnemy;
                if (isEnemy && useCorrupt && Settings_default._antienemy) {
                    return 21;
                }
                if (useShadow) {
                    return 19;
                }
                if (useActual && actual !== 11) {
                    return actual;
                }
                return 0;
            }
            if (useTail) {
                return 11;
            }
            return 0;
        }
        postTick() {
            const {_ModuleHandler: ModuleHandler} = this.client;
            const acc = this.getBestCurrentAcc();
            ModuleHandler.useAcc = acc;
        }
    }

    class DefaultHat {
        moduleName="defaultHat";
        client;
        constructor(client2) {
            this.client = client2;
        }
        getBestCurrentHat() {
            const {_ModuleHandler: ModuleHandler, EnemyManager: EnemyManager2, myPlayer: myPlayer} = this.client;
            const {current: current, future: future} = myPlayer.pos;
            const {actual: actual} = ModuleHandler.getHatStore();
            const useFlipper = ModuleHandler.canBuy(0, 31);
            const useSoldier = ModuleHandler.canBuy(0, 6);
            const useWinter = ModuleHandler.canBuy(0, 15);
            const useActual = ModuleHandler.canBuy(0, actual);
            const useBooster = ModuleHandler.canBuy(0, 12);
            const useBull = ModuleHandler.canBuy(0, 7);
            const useEmp = ModuleHandler.canBuy(0, 22);
            if (useActual && !ModuleHandler.isMoving && myPlayer.speed <= 5 && actual !== 0) {
                return actual;
            }
            if (useSoldier) {
                if (Settings_default._antienemy) {
                    if (EnemyManager2.detectedDangerEnemy || EnemyManager2.detectedEnemy || EnemyManager2.velocityTickThreat || EnemyManager2.reverseInsta || EnemyManager2.toolHammerInsta || EnemyManager2.rangedBowInsta) {
                        ModuleHandler.shouldEquipSoldier = true;
                        ModuleHandler.forceHat = 6;
                        return 6;
                    }
                    if (useBull && myPlayer.shameCount > 0 || EnemyManager2.dangerWithoutSoldier) {
                        return 6;
                    }
                }
                if (Settings_default._antispike && EnemyManager2.willCollideSpike) {
                    return 6;
                }
            }
            // Grinding resources: keep Samurai Armor (20) even while walking to the node.
            // Biome hats only when not actively farming.
            try {
                const extra = ModuleHandler.staticModules?.aibmExtra;
                const node = extra?.gatherObject;
                const grinding = node?.pos?.current && (
                    (typeof extra.effectiveMode === 'function' && extra.effectiveMode() === 'grinder') ||
                    current.distance(node.pos.current) < 450
                );
                if (grinding && ModuleHandler.canBuy(0, 20)) {
                    return 20; // Samurai Armor
                }
            } catch (_) {}
            if (Settings_default._biomehats && useFlipper && !myPlayer.onPlatform) {
                const inRiver = pointInRiver(current) || pointInRiver(future);
                if (inRiver) {
                    return 31;
                }
            }
            if (useSoldier) {
                if (Settings_default._antianimal && EnemyManager2.nearestDangerAnimal !== null) {
                    return 6;
                }
            }
            if (useEmp && Settings_default._empDefense && (!ModuleHandler.isMoving || myPlayer.speed <= 5)) {
                return 22;
            }
            if (Settings_default._biomehats && useWinter) {
                const inWinter = current.y <= 2400 || future.y <= 2400;
                if (inWinter) {
                    return 15;
                }
            }
            if (useBooster) {
                return 12;
            }
            return 0;
        }
        postTick() {
            const {_ModuleHandler: ModuleHandler} = this.client;
            const hat = this.getBestCurrentHat();
            ModuleHandler.useHat = hat;
        }
    }

    class SafeWalk {
        moduleName="safeWalk";
        client;
        movingState=false;
        constructor(client2) {
            this.client = client2;
        }
        reset() {
            this.movingState = false;
        }
        postTick() {
            const {_ModuleHandler: ModuleHandler, myPlayer: myPlayer, ObjectManager: ObjectManager2, EnemyManager: EnemyManager2} = this.client;
            const {prevMoveTo: prevMoveTo, moveTo: moveTo} = ModuleHandler;
            if (prevMoveTo !== moveTo) {
                const angle = moveTo === "disable" ? ModuleHandler.move_dir : moveTo;
                ModuleHandler.startMovement(angle, true);
                return;
            }
            if (myPlayer.simulation.collisionSimulation(this.client)) {
                if (!this.movingState) {
                    this.movingState = true;
                    ModuleHandler.stopMovement();
                }
                return;
            }
            if (this.movingState) {
                this.movingState = false;
                ModuleHandler.startMovement();
            }
        }
    }

    class ShameReset {
        moduleName="shameReset";
        client;
        tickToggle=false;
        constructor(client2) {
            this.client = client2;
        }
        isBullTickTime() {
            const {myPlayer: myPlayer} = this.client;
            return !myPlayer.shameActive && myPlayer.shameCount > 0 && myPlayer.poisonCount === 0 && myPlayer.isBullTickTime();
        }
        get shouldReset() {
            const {_ModuleHandler: ModuleHandler} = this.client;
            return this.isBullTickTime() && ModuleHandler.canBuy(0, 7);
        }
        notSave() {
            const {EnemyManager: EnemyManager2, myPlayer: myPlayer, _ModuleHandler: ModuleHandler} = this.client;
            return ModuleHandler.forceHat === 40 || EnemyManager2.instaThreat() || EnemyManager2.collidingSpike || myPlayer.wasTrapped() || ModuleHandler.currentType === 2;
        }
        postTick() {
            const {_ModuleHandler: ModuleHandler} = this.client;
            if (Settings_default._autoheal && !this.notSave() && (this.shouldReset || this.tickToggle)) {
                this.tickToggle = true;
                ModuleHandler.moduleActive = true;
                ModuleHandler.forceHat = 7;
            }
        }
        healthUpdate() {
            if (this.client.myPlayer.isDmgOverTime) {
                this.tickToggle = false;
            }
        }
    }

    const ShameReset_default = ShameReset;

    class AutoAccept {
        moduleName="autoAccept";
        client;
        prevClan=null;
        prevLeader=false;
        acceptCount=0;
        constructor(client2) {
            this.client = client2;
        }
        resetRequests() {
            this.client.myPlayer.joinRequests.length = 0;
            this.client.pendingJoins.clear();
            this.acceptCount = 0;
            if (this.client.isOwner) GameUI_default.refreshRequests();
        }
        syncClan() {
            const myPlayer = this.client.myPlayer;
            const currentClan = myPlayer.clanName;
            if (currentClan !== this.prevClan || this.prevLeader && !myPlayer.isLeader) {
                this.prevClan = currentClan;
                this.resetRequests();
            }
            this.prevLeader = myPlayer.isLeader;
        }
        respond(id, accept) {
            this.syncClan();
            const {myPlayer: myPlayer, PacketManager: PacketManager2, SocketManager: socket} = this.client;
            const index = myPlayer.joinRequests.findIndex(request => request[0] === id);
            if (!myPlayer.isLeader || index === -1 || !socket.active || socket.socket?.readyState !== 1) {
                return false;
            }
            try {
                PacketManager2.clanRequest(id, accept);
            } catch (_) {
                return false;
            }
            myPlayer.joinRequests.splice(index, 1);
            this.client.pendingJoins.delete(id);
            if (this.client.isOwner) GameUI_default.refreshRequests();
            return true;
        }
        postTick() {
            this.syncClan();
            const {myPlayer: myPlayer, clientIDList: clientIDList, isOwner: isOwner} = this.client;
            // Auto-accept bots / autoaccept setting; humans stay in the Requests panel.
            this.acceptCount = (this.acceptCount + 1) % 7;
            if (myPlayer.isLeader && this.acceptCount === 0) {
                const request = myPlayer.joinRequests.find(([id]) => Settings_default._autoaccept || clientIDList.has(id));
                if (request) {
                    this.respond(request[0], true);
                }
            }
            if (isOwner) GameUI_default.refreshRequests();
        }
    }

    const AutoAccept_default = AutoAccept;

    class AutoBuy {
        moduleName="autoBuy";
        client;
        buyIndex=0;
        buyList=[ [ 1, 11 ], [ 0, 12 ], [ 0, 7 ], [ 0, 6 ], [ 0, 40 ], [ 0, 53 ], [ 1, 21 ], [ 0, 11 ], [ 1, 19 ], [ 0, 15 ], [ 0, 31 ], [ 0, 20 ], [ 0, 22 ] ];
        constructor(client2) {
            this.client = client2;
        }
        boughtEverything() {
            return this.buyIndex >= this.buyList.length;
        }
        postTick() {
            const {_ModuleHandler: ModuleHandler, myPlayer: myPlayer} = this.client;
            if (this.boughtEverything() || !myPlayer.isSandbox) {
                return;
            }
            const [type, id] = this.buyList[this.buyIndex];
            if (ModuleHandler.canBuy(type, id)) {
                ModuleHandler._buy(type, id);
            }
            if (ModuleHandler.bought[type].has(id)) {
                this.buyIndex += 1;
            }
        }
    }

    class AutoGrind {
        moduleName="autoGrind";
        client;
        pending=[];
        context=null;
        constructor(client2) {
            this.client = client2;
        }
        reset() {
            this.pending.length = 0;
            this.context = null;
        }
        syncContext() {
            const {myPlayer:player, SocketManager:socket} = this.client;
            const item = player.getItemByType(8), sandbox = player.isSandbox;
            if (!this.context || this.context.socket !== socket.socket || this.context.item !== item ||
                this.context.sandbox !== sandbox || this.context.playerID !== player.id) {
                this.reset();
                this.context = {socket:socket.socket, item, sandbox, playerID:player.id};
            }
        }
        breakingSlot() {
            return this.client.myPlayer.getItemByType(1) === 10 ? 1 : 0;
        }
        isFullyUpgraded() {
            const player = this.client.myPlayer;
            return player.getWeaponVariant(player.getItemByType(0)).current >= 2 &&
                (this.breakingSlot() === 0 || player.getWeaponVariant(10).current >= 1);
        }
        optimalAngle(objects) {
            const position = this.client.myPlayer.pos.current;
            const angles = objects.map(object => position.angle(object.pos.current));
            const center = Math.atan2(angles.reduce((sum, angle) => sum + Math.sin(angle), 0), angles.reduce((sum, angle) => sum + Math.cos(angle), 0));
            const candidates = [center, ...angles];
            for (let i = 0; i < angles.length; i++) {
                for (let j = i + 1; j < angles.length; j++) candidates.push(findMiddleAngle(angles[i], angles[j]));
            }
            let best = center, count = -1;
            for (const angle of candidates) {
                const hits = angles.filter(other => getAngleDist(angle, other) <= Config_default.gatherAngle).length;
                if (hits > count) { best = angle; count = hits; }
            }
            return best;
        }
        targets() {
            const {myPlayer:player, ObjectManager:manager} = this.client;
            const range = DataHandler_default.getWeapon(player.getItemByType(this.breakingSlot())).range;
            return [...manager.grid2D.queryFull(player.pos.current.x, player.pos.current.y, 1)]
                .map(id => manager.objects.get(id)).filter(object => object instanceof PlayerObject &&
                    object.type === player.getItemByType(8) && object.ownerID === player.id && object.health > 0 &&
                    player.pos.current.distance(object.pos.current) <= range + object.scale);
        }
        refreshPending() {
            const {myPlayer:player, ObjectManager:manager, _ModuleHandler:handler} = this.client;
            const grace = 4 + Math.ceil(clamp(this.client.SocketManager.pong || 0, 0, 500) / 111);
            this.pending = this.pending.filter(entry => handler.tickCount - entry.tick < grace &&
                !manager.grid2D.query(entry.position.x, entry.position.y, 1, id => {
                    const object = manager.objects.get(id);
                    return object instanceof PlayerObject && object.type === entry.item && object.ownerID === player.id &&
                        object.health > 0 && object.pos.current.distance(entry.position) < 12;
                }));
        }
        holdPlacementWeapon() {
            const handler = this.client._ModuleHandler;
            handler.moduleActive = true;
            handler.forceWeapon = this.breakingSlot();
            handler.shouldAttack = false;
            if (handler.hasStoreItem(0, 6)) handler.forceHat = 6;
        }
        placeGroup() {
            const {myPlayer:player, ObjectManager:manager, _ModuleHandler:handler} = this.client;
            const id = player.getItemByType(8), item = Items[id], size = player.isSandbox ? 3 : 2;
            if (this.pending.length || !player.canPlace(8)) return false;
            const {count, limit} = player.getItemCount(item.itemGroup);
            if (limit - count < size || !player.isSandbox && Object.entries(item.cost).some(([resource,cost]) => player.resources[resource] < cost * size)) return false;
            const offset = Math.max(73 * Math.PI / 180, 2 * Math.asin(Math.min(1, (item.scale + .25) / player.getItemPlaceScale(id))));
            // Group placement: left/right on normal servers, plus the center in sandbox.
            for (let i = 0; i < 36; i++) {
                const angle = handler._currentAngle + i * Math.PI / 18;
                const angles = size === 3 ? [angle, angle - offset, angle + offset] : [angle - offset, angle + offset];
                const positions = angles.map(direction => player.getPlacePosition(player.pos.current, id, direction));
                if (!positions.every(position => manager.canPlaceItem(id, position))) continue;
                if (positions.some((position,index) => positions.slice(index + 1).some(other => position.distance(other) < item.scale * 2))) continue;
                for (let index = 0; index < angles.length; index++) {
                    handler.place(8, angles[index], true);
                    handler.placedOnce = true;
                    handler.placeAngles[0] = 8;
                    handler.placeAngles[1].push(angles[index]);
                    this.pending.push({position:positions[index], tick:handler.tickCount, item:id});
                }
                return true;
            }
            return false;
        }
        postTick() {
            const {myPlayer:player, _ModuleHandler:handler, EnemyManager:enemies} = this.client;
            if (!Settings_default._autoGrind || !player.inGame || player.currentHealth <= 0 || this.client.crossServer ||
                this.client.SocketManager.socket?.readyState !== 1) { this.reset(); return; }
            this.syncContext();
            if (handler.pointerAttack || handler.pendingPointerAttack || (handler.forceWeapon !== null || handler.shouldAttack) && !handler.autoattackClaim) return;
            if (handler.moduleActive || handler.placedOnce || handler.healedOnce || handler.syncExecuting || this.client.InputHandler.instaToggle ||
                handler.isMoving || player.speed > 5) return;
            // AutoMill can remain eligible while stationary without placing anything.
            // Actual movement and placements above already retain milling priority.
            const item = player.getItemByType(8), primary = player.getItemByType(0);
            if (![17, 22].includes(item) || !DataHandler_default.isMelee(primary)) return;
            if (this.isFullyUpgraded()) { this.reset(); return; }
            const enemy = enemies.nearestEnemy;
            if (enemy && player.pos.current.distance(enemy.pos.current) <= (player.isSandbox ? 300 : 400)) return;
            this.refreshPending();
            if (this.pending.length) { this.holdPlacementWeapon(); return; }
            const objects = this.targets();
            if (!objects.length) {
                if (this.placeGroup()) this.holdPlacementWeapon();
                return;
            }
            const defensive = handler.shouldEquipSoldier || handler.forceHat === 6;
            // Hammer prepares structures for primary finishing when available.
            // Other loadouts grind with their melee primary only.
            let slot = this.breakingSlot(), targets = objects;
            if (slot === 1 && player.getWeaponVariant(primary).current < 2) {
                const tank = !defensive && handler.hasStoreItem(0, 40);
                const hammer = DataHandler_default.getWeapon(10);
                const damage = hammer.damage * (hammer.sDmg || 1) * WeaponVariants[player.getWeaponVariant(10).current].val * (tank ? Hats[40].bDmg : 1);
                const healthy = objects.filter(object => object.health > damage);
                if (healthy.length) targets = healthy;
                else {
                    const weapon = DataHandler_default.getWeapon(primary);
                    const reachable = objects.filter(object => player.pos.current.distance(object.pos.current) <= weapon.range + object.scale);
                    if (reachable.length) { slot = 0; targets = reachable; }
                }
            }
            handler.moduleActive = true;
            handler.forceWeapon = slot;
            handler.useAngle = this.optimalAngle(targets);
            handler.shouldAttack = handler.staticModules.reloading.isReloaded(slot);
            if (handler.shouldAttack && !defensive && handler.canBuy(0, 40)) handler.forceHat = 40;
            if ((defensive || !handler.shouldAttack) && handler.hasStoreItem(0, 6)) handler.forceHat = 6;
        }
    }

    class Automill {
        moduleName="autoMill";
        toggle=false;
        active=true;
        client;
        tickCount=0;
        constructor(client2) {
            this.client = client2;
        }
        get isActive() {
            return this.toggle && this.active;
        }
        reset() {
            this.active = true;
        }
        get canAutomill() {
            if (!this.client.isOwner) return false;
            const {attacking: attacking, placedOnce: placedOnce, staticModules: staticModules} = this.client._ModuleHandler;
            return Settings_default._automill && this.client.myPlayer.isSandbox && !placedOnce && !attacking && this.active && !staticModules.autoBuy.boughtEverything() && this.client.myPlayer.age < 20;
        }
        canPlaceWindmill(angle) {
            return this.client.myPlayer.canPlaceObject(5, angle);
        }
        placeWindmill(angle) {
            const {_ModuleHandler: ModuleHandler} = this.client;
            const type = 5;
            ModuleHandler.place(type, angle);
            ModuleHandler.placedOnce = true;
            ModuleHandler.placeAngles[0] = type;
            ModuleHandler.placeAngles[1].push(angle);
        }
        postTick() {
            const {myPlayer: myPlayer, _ModuleHandler: ModuleHandler} = this.client;
            this.toggle = true;
            if (!this.canAutomill) {
                this.toggle = false;
                return;
            }
            if (!myPlayer.canPlace(5)) {
                this.toggle = false;
                this.active = false;
                return;
            }
            const angle = ModuleHandler.reverse_move_dir;
            if (angle === null) {
                return;
            }
            const item = Items[myPlayer.getItemByType(5)];
            const distance = myPlayer.getItemPlaceScale(item.id);
            const offset = Math.asin((2 * item.scale + 9e-13) / (2 * distance)) * 2;
            const leftAngle = angle - offset;
            const rightAngle = angle + offset;
            if (this.canPlaceWindmill(angle) && this.canPlaceWindmill(leftAngle) && this.canPlaceWindmill(rightAngle)) {
                this.placeWindmill(angle);
                this.placeWindmill(leftAngle);
                this.placeWindmill(rightAngle);
            }
        }
    }

    const Automill_default = Automill;

    class AutoSteal {
        moduleName="autoSteal";
        client;
        constructor(client2) {
            this.client = client2;
        }
        postTick() {
            const {_ModuleHandler: ModuleHandler, EnemyManager: EnemyManager2, myPlayer: myPlayer} = this.client;
            if (ModuleHandler.moduleActive || !Settings_default._autoSteal) {
                return;
            }
            const nearestLowEntity = EnemyManager2.nearestLowEntity;
            if (nearestLowEntity === null) {
                return;
            }
            const {reloading: reloading} = ModuleHandler.staticModules;
            const primary = myPlayer.getItemByType(0);
            const range = DataHandler_default.getWeapon(primary).range + nearestLowEntity.hitScale;
            if (!myPlayer.collidingSimple(nearestLowEntity, range) || !reloading.isReloaded(0)) {
                return;
            }
            const canUseBull = ModuleHandler.canBuy(0, 7);
            const pos1 = myPlayer.pos.current;
            const pos2 = nearestLowEntity.pos.current;
            const angle = pos1.angle(pos2);
            const maxDamageBull = myPlayer.getMaxWeaponDamage(primary, false, canUseBull);
            const maxDamage = myPlayer.getMaxWeaponDamage(primary, false, false);
            const canKill = maxDamageBull >= nearestLowEntity.currentHealth;
            if (!canKill) {
                return;
            }
            ModuleHandler.moduleActive = true;
            ModuleHandler.useAngle = angle;
            if (maxDamage < nearestLowEntity.currentHealth) {
                ModuleHandler.forceHat = 7;
            }
            ModuleHandler.forceWeapon = 0;
            ModuleHandler.shouldAttack = true;
        }
    }

    class AutoPush {
        moduleName="autoPush";
        client;
        pushPos=null;
        constructor(client2) {
            this.client = client2;
        }
        postTick() {
            const {EnemyManager: EnemyManager2, myPlayer: myPlayer, _ModuleHandler: ModuleHandler, ObjectManager: ObjectManager2, PlayerManager: PlayerManager2} = this.client;
            this.pushPos = null;
            const nearestEnemyPush = EnemyManager2.nearestEnemyPush;
            const nearestPushSpike = EnemyManager2.nearestPushSpike;
            EnemyManager2.nearestEnemyPush = null;
            EnemyManager2.nearestPushSpike = null;
            if (ModuleHandler.moduleActive || !Settings_default._autoPush || ModuleHandler.moveTo !== "disable") {
                return;
            }
            if (nearestEnemyPush === null || nearestPushSpike === null) {
                return;
            }
            const trappedIn = nearestEnemyPush.trappedIn;
            if (trappedIn === null || myPlayer.trappedIn || nearestEnemyPush.tempHealth <= 0 || ObjectManager2.objects.get(trappedIn.id) !== trappedIn || ObjectManager2.objects.get(nearestPushSpike.id) !== nearestPushSpike) {
                return;
            }
            const pos0 = myPlayer.pos.current;
            const pos1 = nearestEnemyPush.pos.current;
            const pos2 = nearestPushSpike.pos.current;
            // Predicted spike contact must not stop a push before the enemy reaches it.
            if (!myPlayer.collidingSimple(nearestEnemyPush, 250)) {
                return;
            }
            const distanceFromSpikeToEnemy = pos2.distance(pos1);
            const angleFromSpikeToEnemy = pos2.angle(pos1);
            const angleToEnemy = pos0.angle(pos1);
            const angleToSpike = pos0.angle(pos2);
            const distanceToSpike = pos0.distance(pos2);
            const pushPos = pos2.addDirection(angleFromSpikeToEnemy, distanceFromSpikeToEnemy + nearestEnemyPush.collisionScale + 7);
            const objectIDs = ObjectManager2.grid2D.queryFull(pushPos.x, pushPos.y, 1);
            for (const id of objectIDs) {
                const object = ObjectManager2.objects.get(id);
                if (PlayerManager2.canMoveOnTop(object)) {
                    continue;
                }
                const pos = object.pos.current;
                const distance = pushPos.distance(pos);
                const playerScale = myPlayer.collisionScale * 1.3;
                const range = object.collisionScale + playerScale;
                if (distance <= range) {
                    return;
                }
            }
            this.pushPos = pos2.addDirection(angleFromSpikeToEnemy, distanceFromSpikeToEnemy + 250);
            ModuleHandler.followTarget.setVec(this.pushPos);
            ModuleHandler.moveTo = pos0.angle(this.pushPos);
            EnemyManager2.nearestEnemyPush = nearestEnemyPush;
            EnemyManager2.nearestPushSpike = nearestPushSpike;
            const activationScale2 = nearestEnemyPush.collisionScale * 3.2;
            const offset2 = Math.asin(2 * activationScale2 / (2 * distanceToSpike));
            const angleDistance2 = getAngleDist(angleToEnemy, angleToSpike);
            const intersecting2 = angleDistance2 <= offset2;
            if (!intersecting2) {
                return;
            }
            this.pushPos = pushPos;
            ModuleHandler.followTarget.setVec(this.pushPos);
            ModuleHandler.moveTo = pos0.angle(this.pushPos);
        }
    }

    class ReverseInstakill {
        moduleName="reverseInstakill";
        client;
        targetEnemy=null;
        issuedAttack=null;
        comboWeapons=null;
        comboDeadline=0;
        constructor(client2) {
            this.client = client2;
        }
        reset() {
            this.targetEnemy = null;
            this.issuedAttack = null;
            this.comboWeapons = null;
            this.comboDeadline = 0;
        }
        postTick() {
            const {myPlayer: myPlayer, EnemyManager: EnemyManager2, PlayerManager: PlayerManager2, _ModuleHandler: ModuleHandler, InputHandler: InputHandler2} = this.client;
            if (!InputHandler2.instaToggle) {
                this.reset();
                InputHandler2.instaReset();
                return;
            }
            const nearestEnemy = ManualComboControl.target(this);
            if (nearestEnemy === null) {
                return;
            }
            if (this.targetEnemy !== null) {
                InputHandler2.instakillTarget = nearestEnemy;
                ManualComboControl.issue(this, nearestEnemy, 0, 7, true);
                return;
            }
            const lookingShield = PlayerManager2.lookingShield(nearestEnemy, myPlayer);
            const primary = myPlayer.getItemByType(0);
            const primaryDamage = myPlayer.getMaxWeaponDamage(primary, lookingShield);
            const secondary = myPlayer.getItemByType(1);
            if (secondary !== 10) {
                return;
            }
            const secondaryDamage = myPlayer.getMaxWeaponDamage(secondary, lookingShield);
            const totalDamage = primaryDamage + secondaryDamage + 25;
            if (totalDamage < 100) {
                return;
            }
            const pos1 = myPlayer.pos.current;
            const pos2 = nearestEnemy.pos.current;
            const angle = pos1.angle(pos2);
            InputHandler2.instakillTarget = nearestEnemy;
            const {reloading: reloading} = ModuleHandler.staticModules;
            const primaryReloaded = reloading.isReloaded(0, 1);
            const secondaryReloaded = reloading.isReloaded(1);
            const turretReloaded = reloading.isReloaded(2);
            const range = DataHandler_default.getWeapon(secondary).range + nearestEnemy.hitScale;
            if (!myPlayer.collidingSimple(nearestEnemy, range)) return;
            if (!primaryReloaded || !secondaryReloaded || !turretReloaded) {
                const reloadSlot = !reloading.isReloaded(1) ? 1 : !reloading.isReloaded(0) ? 0 : null;
                if (reloadSlot !== null) {
                    ModuleHandler.moduleActive = true;
                    ModuleHandler.forceWeapon = reloadSlot;
                    ModuleHandler.shouldAttack = false;
                }
                return;
            }
            ManualComboControl.issue(this, nearestEnemy, 1, 53, false);
        }
    }

    class BowInsta {
        moduleName="bowInsta";
        client;
        targetEnemy=null;
        tickAction=0;
        distMin=660;
        distMax=700;
        active=false;
        constructor(client2) {
            this.client = client2;
        }
        reset() {
            this.targetEnemy = null;
            this.tickAction = 0;
            this.active = false;
        }
        postTick() {
            const {EnemyManager: EnemyManager2, _ModuleHandler: ModuleHandler, myPlayer: myPlayer, InputHandler: InputHandler2} = this.client;
            if (!InputHandler2.instaToggle) {
                this.reset();
                InputHandler2.instaReset();
                return;
            }
            const nearestEnemy = EnemyManager2.nearestEnemy;
            const nearest = this.targetEnemy || nearestEnemy;
            if (nearest === null) {
                this.reset();
                return;
            }
            const pos1 = myPlayer.pos.current;
            const pos2 = nearest.pos.current;
            const angle = pos1.angle(pos2);
            const distance = pos1.distance(pos2);
            InputHandler2.instakillTarget = nearest;
            if (this.targetEnemy !== null) {
                if (this.tickAction === 2) {
                    ModuleHandler.moduleActive = true;
                    ModuleHandler.useAngle = angle;
                    ModuleHandler.forceWeapon = 1;
                    ModuleHandler.shouldAttack = true;
                    ModuleHandler.moveTo = null;
                    ModuleHandler._upgradeItem(15);
                    this.reset();
                    InputHandler2.instaReset();
                    return;
                }
                if (this.tickAction === 1) {
                    ModuleHandler.moduleActive = true;
                    ModuleHandler.useAngle = angle;
                    ModuleHandler.forceWeapon = 1;
                    ModuleHandler.shouldAttack = true;
                    ModuleHandler.moveTo = null;
                    ModuleHandler._upgradeItem(12);
                    this.tickAction = 2;
                    return;
                }
                return;
            }
            const isUpgradeAge = inRange(myPlayer.upgradeAge, 6, 8) && myPlayer.age >= 9;
            if (!isUpgradeAge) {
                return;
            }
            this.active = true;
            const {reloading: reloading} = ModuleHandler.staticModules;
            const useTurret = ModuleHandler.canBuy(0, 53);
            if (!useTurret || !reloading.isReloaded(2) || !inRange(distance, this.distMin, this.distMax)) {
                return;
            }
            ModuleHandler.moveTo = null;
            ModuleHandler.moduleActive = true;
            ModuleHandler.useAngle = angle;
            ModuleHandler.forceHat = 53;
            ModuleHandler.forceWeapon = 1;
            ModuleHandler.shouldAttack = true;
            if (myPlayer.upgradeAge === 6) {
                ModuleHandler._upgradeItem(9);
            }
            if (myPlayer.upgradeAge === 7) {
                ModuleHandler._upgradeItem(18, true);
            }
            if (myPlayer.upgradeAge === 8 && myPlayer.getItemByType(8) === 18) {
                ModuleHandler.place(8, angle);
                ModuleHandler.place(8, angle - toRadians(90));
                ModuleHandler.place(8, angle + toRadians(90));
                ModuleHandler.place(8, reverseAngle(angle));
            }
            this.tickAction = 1;
            this.targetEnemy = nearestEnemy;
        }
    }

    class PlacementDefense {
        moduleName="placementDefense";
        client;
        constructor(client2) {
            this.client = client2;
        }
        postTick() {
            const {EnemyManager: EnemyManager2, myPlayer: myPlayer, _ModuleHandler: ModuleHandler, ProjectileManager: ProjectileManager2, ObjectManager: ObjectManager2} = this.client;
            const nearestEnemy = EnemyManager2.nearestEnemy;
            if (nearestEnemy === null || !Settings_default._placementDefense) {
                return;
            }
            const shouldDefend = EnemyManager2.rangedBowInsta;
            if (shouldDefend || ProjectileManager2.totalDamage >= myPlayer.currentHealth) {
                const pos1 = myPlayer.pos.current;
                const pos2 = nearestEnemy.pos.current;
                const angle = pos1.angle(pos2);
                let type = 3;
                if (myPlayer.canPlace(5)) {
                    type = 5;
                }
                const id = myPlayer.getItemByType(type);
                const length = myPlayer.getItemPlaceScale(id);
                const angles = ObjectManager2.getBestPlacementAngles({
                    position: pos1,
                    id: id,
                    targetAngle: angle,
                    ignoreID: null,
                    preplace: false,
                    reduce: true,
                    fill: false
                });
                if (angles.length === 0) {
                    return;
                }
                const distance1 = pos1.distance(pos2);
                const placementScale = DataHandler_default.getItem(id).scale;
                for (const angle2 of angles) {
                    const pos3 = pos1.addDirection(angle2, length);
                    const rectStart = pos3.copy().sub(placementScale);
                    const rectEnd = pos3.copy().add(placementScale);
                    const distance2 = pos3.distance(pos2);
                    if (distance2 < distance1 && lineIntersectsRect(pos2, pos1, rectStart, rectEnd)) {
                        ModuleHandler.place(type, angle2);
                    }
                }
                ModuleHandler.placedOnce = true;
                ModuleHandler.placeAngles[0] = type;
                ModuleHandler.placeAngles[1] = [ angle ];
            }
        }
    }

    class TurretSteal {
        moduleName="turretSteal";
        client;
        constructor(client2) {
            this.client = client2;
        }
        postTick() {
            const {_ModuleHandler: ModuleHandler, myPlayer: myPlayer, EnemyManager: EnemyManager2} = this.client;
            if (ModuleHandler.moduleActive || !Settings_default._turretSteal) {
                return;
            }
            const nearestEnemy = EnemyManager2.nearestTurretEntity;
            if (nearestEnemy === null || nearestEnemy.currentHealth > 25 || !ModuleHandler.canBuy(0, 53)) {
                return;
            }
            const pos0 = myPlayer.pos.current;
            const pos1 = nearestEnemy.pos.current;
            const distance = pos0.distance(pos1);
            if (distance > 700) {
                return;
            }
            const {reloading: reloading} = ModuleHandler.staticModules;
            if (!reloading.isReloaded(2)) {
                return;
            }
            ModuleHandler.moduleActive = true;
            ModuleHandler.forceHat = 53;
        }
    }

    class KillChat {
        moduleName="killChat";
        client;
        lastKillTick = -1;
        constructor(client2) {
            this.client = client2;
        }
        postTick() {
            const {myPlayer: myPlayer, PacketManager: PacketManager2} = this.client;
            if (!Settings_default._killMessage || !myPlayer.killedSomeone || myPlayer.resources.kills === 0) {
                return;
            }
            const message = (Settings_default._killMessageText || "").trim();
            if (message.length === 0) {
                return;
            }
            const tick = this.client._ModuleHandler.tickCount;
            if (this.lastKillTick === tick) return;
            this.lastKillTick = tick;
            if (this.client.isOwner) PacketManager2.chat(message);
            BotKillChat.broadcast();
        }
    }

    class SwordKatanaInsta {
        moduleName="swordKatanaInsta";
        client;
        nearestTarget=null;
        useTurret=false;
        constructor(client2) {
            this.client = client2;
        }
        postTick() {
            const {myPlayer: myPlayer, _ModuleHandler: ModuleHandler, EnemyManager: EnemyManager2} = this.client;
            const nearestEnemy = EnemyManager2.nearestEnemy;
            if (ModuleHandler.moduleActive || !nearestEnemy) {
                this.nearestTarget = null;
                this.useTurret = false;
                return;
            }
            const {reloading: reloading} = ModuleHandler.staticModules;
            const primaryReloaded = reloading.isReloaded(0);
            const turretReloaded = reloading.isReloaded(2);
            if (this.useTurret) {
                this.useTurret = false;
                if (turretReloaded && ModuleHandler.canBuy(0, 53)) {
                    ModuleHandler.moduleActive = true;
                    ModuleHandler.forceHat = 53;
                }
                return;
            }
            const primary = myPlayer.getItemByType(0);
            const isSword = primary === 3;
            const pos1 = myPlayer.pos.current;
            const target = this.nearestTarget;
            if (target !== null) {
                const pos22 = target.pos.current;
                const angle2 = pos1.angle(pos22);
                ModuleHandler.useAngle = angle2;
                ModuleHandler.forceHat = 7;
                ModuleHandler.forceWeapon = 0;
                ModuleHandler.shouldAttack = true;
                if (myPlayer.upgradeAge === 3) {
                    ModuleHandler._upgradeItem(1, true);
                }
                if (myPlayer.upgradeAge === 4) {
                    ModuleHandler._upgradeItem(15, true);
                }
                if (myPlayer.upgradeAge === 5) {
                    ModuleHandler._upgradeItem(7, true);
                }
                if (myPlayer.upgradeAge === 6) {
                    ModuleHandler._upgradeItem(10);
                }
                if (myPlayer.upgradeAge === 7) {
                    ModuleHandler._upgradeItem(22, true);
                }
                if (myPlayer.upgradeAge === 8) {
                    ModuleHandler._upgradeItem(4);
                }
                this.nearestTarget = null;
                if (ModuleHandler.canBuy(0, 53)) {
                    this.useTurret = true;
                }
                EnemyManager2.attemptSpikePlacement();
            }
            if (myPlayer.age < 8 || myPlayer.upgradeAge >= 9 || !isSword || !primaryReloaded || !ModuleHandler.canBuy(0, 7)) {
                return;
            }
            const range = DataHandler_default.getWeapon(primary).range + nearestEnemy.hitScale;
            if (!myPlayer.collidingSimple(nearestEnemy, range)) {
                return;
            }
            const pos2 = nearestEnemy.pos.current;
            const angle = pos1.angle(pos2);
            ModuleHandler.useAngle = angle;
            ModuleHandler.forceHat = 7;
            ModuleHandler.forceWeapon = 0;
            ModuleHandler.shouldAttack = true;
            this.nearestTarget = nearestEnemy;
        }
    }

    class SpikeGearInsta {
        moduleName="spikeGearInsta";
        client;
        constructor(client2) {
            this.client = client2;
        }
        postTick() {
            const {_ModuleHandler: ModuleHandler, EnemyManager: EnemyManager2, myPlayer: myPlayer} = this.client;
            if (ModuleHandler.moduleActive || EnemyManager2.instaThreat() || EnemyManager2.spikeSyncThreat || !Settings_default._spikeGearInsta) {
                return;
            }
            const nearestEnemy = EnemyManager2.nearestEnemy;
            if (nearestEnemy === null || !ModuleHandler.canBuy(0, 11) || !ModuleHandler.canBuy(1, 21) || myPlayer.accessoryID !== 21 || nearestEnemy.variant.primary !== 0) {
                return;
            }
            const pos1 = myPlayer.pos.current;
            const pos2 = nearestEnemy.pos.current;
            const angle = pos1.angle(pos2);
            const primary1 = myPlayer.getItemByType(0);
            const primary2 = nearestEnemy.weapon.primary;
            if (primary2 === null) {
                return;
            }
            const range1 = DataHandler_default.getWeapon(primary1).range + nearestEnemy.hitScale;
            const range2 = DataHandler_default.getWeapon(primary2).range + myPlayer.hitScale;
            if (!myPlayer.collidingSimple(nearestEnemy, range1) || !nearestEnemy.collidingSimple(myPlayer, range2)) {
                return;
            }
            ModuleHandler.forceHat = 11;
            if (nearestEnemy.hatID !== 7 || !nearestEnemy.isEmptyReload(0) || myPlayer.hatID !== 11) {
                return;
            }
            ModuleHandler.moduleActive = true;
            ModuleHandler.useAngle = angle;
            ModuleHandler.forceHat = 7;
            ModuleHandler.forceWeapon = 0;
            ModuleHandler.shouldAttack = true;
        }
    }

    class TeammateSpikeTrap {
        moduleName="teammateSpikeTrap";
        client;
        constructor(client2) {
            this.client = client2;
        }
        // DISABLED: leaveClan + 4 spikes on teammate when insta on (teamkill).
        postTick() {
            return;
        }
    }

    class SpikeTrap {
        moduleName="spikeTrap";
        client;
        constructor(client2) {
            this.client = client2;
        }
        postTick() {
            const {_ModuleHandler: ModuleHandler, myPlayer: myPlayer, EnemyManager: EnemyManager2} = this.client;
            if (ModuleHandler.moduleActive) {
                return;
            }
            const trapId = myPlayer.getItemByType(7);
            const nearestEnemy = EnemyManager2.nearestEnemy;
            if (!nearestEnemy || myPlayer.isTrapped || trapId !== 16) {
                return;
            }
            const pos1 = myPlayer.pos.current;
            const pos2 = nearestEnemy.pos.current;
            const distance = pos1.distance(pos2);
            const angle = pos1.angle(pos2);
            if (distance > 175) {
                return;
            }
            const angles = [ angle, angle - toRadians(90), angle + toRadians(90), angle + toRadians(180) ];
            const id = myPlayer.getItemByType(4);
            const len = ModuleHandler.currentType === 7 ? 30 : 0;
            const current = myPlayer.getPlacePosition(pos1, id, angle);
            const distance2 = current.distance(pos1) + len;
            ModuleHandler.placeAngles[0] = 4;
            ModuleHandler.placeAngles[1] = angles;
            if (distance > distance2) {
                return;
            }
            for (const angle2 of angles) {
                ModuleHandler.place(4, angle2);
            }
        }
    }

    class TurretSync {
        moduleName="turretSync";
        client;
        constructor(client2) {
            this.client = client2;
        }
        postTick() {
            const {_ModuleHandler: ModuleHandler, EnemyManager: EnemyManager2, myPlayer: myPlayer} = this.client;
            if (ModuleHandler.moduleActive || !Settings_default._turretSync) {
                return;
            }
            const nearestEnemy = EnemyManager2.nearestEnemy;
            if (nearestEnemy === null) {
                return;
            }
            const primary = myPlayer.getItemByType(0);
            const weapon = DataHandler_default.getWeapon(primary);
            if (weapon.damage < 20) {
                return;
            }
            const range = weapon.range + nearestEnemy.hitScale;
            const {reloading: reloading} = ModuleHandler.staticModules;
            if (!myPlayer.collidingSimple(nearestEnemy, range) || !reloading.isReloaded(0) || nearestEnemy.nextDamageTick !== myPlayer.tickCount + 2) {
                return;
            }
            const pos1 = myPlayer.pos.current;
            const pos2 = nearestEnemy.pos.current;
            const angle = pos1.angle(pos2);
            ModuleHandler.moduleActive = true;
            ModuleHandler.useAngle = angle;
            ModuleHandler.forceHat = 7;
            ModuleHandler.forceWeapon = 0;
            ModuleHandler.shouldAttack = true;
        }
    }

    class DashMovement {
        moduleName="dashMovement";
        client;
        constructor(client2) {
            this.client = client2;
        }
        postTick() {
            const {_ModuleHandler: ModuleHandler, myPlayer: myPlayer} = this.client;
            const {currentType: currentType, _currentAngle: currentAngle} = ModuleHandler;
            if (!myPlayer.canPlace(currentType) || !Settings_default._dashMovement) {
                return;
            }
            const {reloading: reloading} = ModuleHandler.staticModules;
            const primary = myPlayer.getItemByType(0);
            const secondary = myPlayer.getItemByType(1);
            const boost = myPlayer.getItemByType(7);
            if (boost !== 16 || !ModuleHandler.hasStoreItem(0, 40) || currentType !== 7 || ModuleHandler.placedOnce) {
                return;
            }
            const hasHammer = secondary === 10;
            const primaryDamage = myPlayer.getBuildingDamage(primary, true);
            const canOneHit = primaryDamage >= DataHandler_default.getItem(16).health;
            let weaponType = null;
            if (canOneHit) {
                const primaryData = DataHandler_default.getWeapon(primary);
                const secondaryData = DataHandler_default.isMelee(secondary) && DataHandler_default.getWeapon(secondary) || null;
                if (secondaryData === null || primaryData.speed < secondaryData.speed) {
                    weaponType = 0;
                }
            }
            if (weaponType === null && hasHammer) {
                weaponType = 1;
            }
            if (weaponType === null) {
                return;
            }
            ModuleHandler.placedOnce = true;
            const reloaded = reloading.isReloaded(weaponType);
            if (!reloaded) {
                return;
            }
            ModuleHandler.place(currentType, currentAngle);
            ModuleHandler.useAngle = currentAngle;
            ModuleHandler.useHat = 40;
            ModuleHandler.forceWeapon = weaponType;
            ModuleHandler.shouldAttack = true;
        }
    }

    class KBTickHammerV2 {
        moduleName="kbTickHammerV2";
        client;
        targetEnemy=null;
        constructor(client2) {
            this.client = client2;
        }
        postTick() {
            const {_ModuleHandler: ModuleHandler, EnemyManager: EnemyManager2, myPlayer: myPlayer} = this.client;
            if (ModuleHandler.moduleActive || !Settings_default._knockbackTickHammer || EnemyManager2.shouldIgnoreModule()) {
                this.targetEnemy = null;
                return;
            }
            const nearestEnemySpikeCollider = EnemyManager2.nearestEnemySpikeCollider;
            const spikeCollider = EnemyManager2.spikeCollider;
            const reloading = ModuleHandler.staticModules.reloading;
            const primary = myPlayer.getItemByType(0);
            const secondary = myPlayer.getItemByType(1);
            const isHammer = secondary !== null && secondary !== 11;
            const primaryReloaded = reloading.isReloaded(0, 1);
            const secondaryReloaded = reloading.isReloaded(1);
            const pos1 = myPlayer.pos.current;
            if (this.targetEnemy !== null) {
                const pos2 = this.targetEnemy.pos.current;
                const angleToEnemy = pos1.angle(pos2);
                ModuleHandler.moduleActive = true;
                ModuleHandler.useAngle = angleToEnemy;
                ModuleHandler.forceHat = 7;
                ModuleHandler.forceWeapon = 0;
                ModuleHandler.shouldAttack = true;
                this.targetEnemy = null;
                EnemyManager2.attemptSpikePlacement();
                return;
            }
            if (nearestEnemySpikeCollider !== null && !nearestEnemySpikeCollider.isTrapped && spikeCollider !== null && isHammer && primaryReloaded && secondaryReloaded) {
                const pos2 = nearestEnemySpikeCollider.pos.current;
                const pos3 = spikeCollider.pos.current;
                const angleToEnemy = pos1.angle(pos2);
                const distanceToSpike2 = pos2.distance(pos3);
                const {knockback: primaryKnockback, range: primaryRange} = DataHandler_default.getWeapon(primary);
                const {knockback: secondaryKnockback, range: secondaryRange} = DataHandler_default.getWeapon(secondary);
                const weaponRange = Math.min(primaryRange, secondaryRange) + nearestEnemySpikeCollider.hitScale;
                const minKB = primaryKnockback;
                const maxKB = primaryKnockback + secondaryKnockback;
                const spikeRange = spikeCollider.collisionScale + nearestEnemySpikeCollider.collisionScale;
                if (inRange(distanceToSpike2, spikeRange + minKB, spikeRange + maxKB) && myPlayer.collidingSimple(nearestEnemySpikeCollider, weaponRange)) {
                    const hammer = DataHandler_default.getWeapon(secondary);
                    const hitRange = hammer.range + nearestEnemySpikeCollider.hitScale;
                    if (myPlayer.collidingSimple(nearestEnemySpikeCollider, hitRange)) {
                        ModuleHandler.moduleActive = true;
                        ModuleHandler.useAngle = angleToEnemy;
                        ModuleHandler.forceHat = 7;
                        ModuleHandler.forceWeapon = 1;
                        ModuleHandler.shouldAttack = true;
                        this.targetEnemy = nearestEnemySpikeCollider;
                        this.client.StatsManager.knockbackTickHammerTimes = 1;
                        EnemyManager2.attemptSpikePlacement();
                    }
                }
            }
        }
    }

    class AutoShield {
        moduleName="autoShield";
        client;
        constructor(client2) {
            this.client = client2;
        }
        getProtectAngle() {
            const {myPlayer: myPlayer, EnemyManager: EnemyManager2} = this.client;
            const nearestEnemy = EnemyManager2.nearestEnemy;
            const pos1 = myPlayer.pos.current;
            const pos2 = nearestEnemy.pos.current;
            const angle = pos1.angle(pos2);
            const secondNearestEnemy = EnemyManager2.secondNearestEnemy;
            if (!secondNearestEnemy) {
                return angle;
            }
            const pos3 = secondNearestEnemy.pos.current;
            const distance = pos1.distance(pos3);
            const primary = secondNearestEnemy.weapon.primary;
            const weaponRange = DataHandler_default.getWeapon(primary).range;
            const range = weaponRange + myPlayer.hitScale;
            const angle2 = pos1.angle(pos3);
            const middleAngle = findMiddleAngle(angle, angle2);
            if (distance <= range && getAngleDist(angle, middleAngle) <= Config_default.gatherAngle && getAngleDist(angle2, middleAngle) <= Config_default.gatherAngle) {
                return middleAngle;
            }
            return angle;
        }
        postTick() {
            const {_ModuleHandler: ModuleHandler, myPlayer: myPlayer, EnemyManager: EnemyManager2} = this.client;
            if (!Settings_default._autoShield || ModuleHandler.moduleActive) {
                return;
            }
            const nearestEnemy = EnemyManager2.nearestEnemy;
            if (nearestEnemy === null) {
                return;
            }
            const secondary = myPlayer.getItemByType(1);
            const hasShield = secondary === 11;
            if (!hasShield) {
                return;
            }
            const shouldActivate = EnemyManager2.weaponDamageThreat();
            if (!shouldActivate) {
                return;
            }
            const angle = this.getProtectAngle();
            ModuleHandler.moduleActive = true;
            ModuleHandler.forceWeapon = 1;
            ModuleHandler.useAngle = angle;
            ModuleHandler.shouldAttack = true;
        }
    }

    class TrapKB {
        moduleName="trapKB";
        client;
        constructor(client2) {
            this.client = client2;
        }
        postTick() {
            const {_ModuleHandler: ModuleHandler, EnemyManager: EnemyManager2, myPlayer: myPlayer} = this.client;
            const nearestEnemy = EnemyManager2.nearestKBTrapEnemy;
            if (nearestEnemy === null || nearestEnemy.isTrapped || ModuleHandler.moduleActive || EnemyManager2.shouldIgnoreModule() || !Settings_default._trapKB) {
                return;
            }
            const pos1 = myPlayer.pos.current;
            const pos2 = nearestEnemy.pos.current;
            const angle = pos1.angle(pos2);
            const {reloading: reloading} = ModuleHandler.staticModules;
            const primaryReloaded = reloading.isReloaded(0);
            const turretReloaded = ModuleHandler.hasStoreItem(0, 53) && reloading.isReloaded(2);
            if (!primaryReloaded) {
                return;
            }
            const range = DataHandler_default.getWeapon(myPlayer.getItemByType(0)).range + nearestEnemy.hitScale;
            if (!myPlayer.collidingSimple(nearestEnemy, range)) {
                return;
            }
            ModuleHandler.moduleActive = true;
            ModuleHandler.useAngle = angle;
            if (turretReloaded) {
                ModuleHandler.forceHat = 53;
            }
            ModuleHandler.forceWeapon = 0;
            ModuleHandler.shouldAttack = true;
        }
    }

    class ShameSpam {
        moduleName="shameSpam";
        client;
        prevActive=false;
        active=false;
        constructor(client2) {
            this.client = client2;
        }
        get wasActive() {
            return this.prevActive;
        }
        postTick() {
            this.prevActive = this.active;
            this.active = false;
            const {myPlayer: myPlayer, EnemyManager: EnemyManager2, _ModuleHandler: ModuleHandler, ObjectManager: ObjectManager2} = this.client;
            if (!Settings_default._shameSpam || ModuleHandler.moduleActive || EnemyManager2.shouldIgnoreModule()) {
                return;
            }
            const nearestEnemy = EnemyManager2.nearestEnemy;
            if (nearestEnemy === null || !nearestEnemy.isTrapped || !myPlayer.isTrapped) {
                return;
            }
            if (nearestEnemy.shameCount >= 7) {
                return;
            }
            const hasTrap = myPlayer.getItemByType(7) === 15;
            if (!hasTrap || !myPlayer.canPlace(7)) {
                return;
            }
            const {reloading: reloading} = ModuleHandler.staticModules;
            const primary = myPlayer.getItemByType(0);
            const isPolearm = primary === 5 || primary === 4;
            if (!isPolearm) {
                return;
            }
            const secondary = myPlayer.getItemByType(1);
            const isHammer = secondary === 10;
            const secondaryReloaded = reloading.isReloaded(1);
            if (!isHammer || !secondaryReloaded) {
                return;
            }
            const trappedIn = nearestEnemy.trappedIn;
            const buildingDamage = myPlayer.getMaxBuildingDamage(trappedIn, true);
            if (buildingDamage === null || trappedIn.health > buildingDamage) {
                return;
            }
            const range = DataHandler_default.getWeapon(secondary).range;
            const attackRange = range + nearestEnemy.hitScale;
            const destroyRange = range + trappedIn.hitScale;
            if (!myPlayer.collidingSimple(nearestEnemy, attackRange)) {
                return;
            }
            if (!myPlayer.collidingSimple(trappedIn, destroyRange)) {
                return;
            }
            const pos1 = myPlayer.pos.current;
            const pos2 = trappedIn.pos.current;
            const pos3 = nearestEnemy.pos.current;
            const destroyAngle = pos1.angle(pos2);
            const attackAngle = pos1.angle(pos3);
            const placementAngle = ObjectManager2.getBestPlacementAngles({
                position: pos1,
                id: 15,
                targetAngle: attackAngle,
                ignoreID: trappedIn.id,
                preplace: true,
                reduce: true,
                fill: true
            })[0];
            if (placementAngle === void 0) {
                return;
            }
            ModuleHandler.moduleActive = true;
            ModuleHandler.useAngle = destroyAngle;
            ModuleHandler.forceHat = 40;
            ModuleHandler.forceWeapon = 1;
            ModuleHandler.shouldAttack = true;
            this.active = true;
            ModuleHandler.place(7, placementAngle, true);
            const delay = this.client.SocketManager.TICK - this.client.SocketManager.pong / 2;
            setTimeout(() => {
                ModuleHandler.place(7, placementAngle, true);
            }, delay);
        }
    }

    const ExtraPathfinder = {
        ownedSpike(extra, item) {
            if (!(item instanceof PlayerObject) || !item.isSpike) return false;
            const owner = extra.client.ownerClient;
            return item.ownerID === owner.myPlayer.id || item.ownerID === extra.client.myPlayer.id || owner.clientIDList.has(item.ownerID);
        },
        obstacles(extra, origin, target = origin) {
            const result = [];
            const reach = origin.distance(target) + 1600;
            for (const item of extra.objects()) {
                if (!(item instanceof Resource) && !(item instanceof PlayerObject)) continue;
                if (item === extra.gatherObject) continue;
                if (item instanceof PlayerObject && item.health <= 0) continue;
                if (item instanceof PlayerObject && DataHandler_default.getItem(item.type).ignoreCollision &&
                    !([15, 22].includes(item.type) && extra.client.myPlayer.isEnemyByID(item.ownerID))) continue;
                if (!extra.usesStick() && extra.breakingSlot() !== null && extra.canBreakPathObject(item)) continue;
                // Include both ends of wide barriers and the approach to the follow area.
                if (origin.distance(item.pos.current) + target.distance(item.pos.current) > reach + 2 * item.collisionScale) continue;
                const owned = this.ownedSpike(extra, item);
                const hostileSpike = item instanceof PlayerObject && item.isSpike && !owned;
                const windmill = item instanceof PlayerObject && item.itemGroup === 3;
                // Windmill corridors use their physical collision edge so bots can squeeze
                // through real gaps. Other solids keep the native simulation safety margin.
                const padding = hostileSpike ? 14 : windmill ? 1 : 6;
                result.push({item, center:item.pos.current, radius:item.collisionScale + extra.client.myPlayer.scale + padding, owned});
            }
            return result;
        },
        intersects(from, to, obstacle) {
            const {center, radius} = obstacle;
            if (Math.max(from.x, to.x) < center.x - radius || Math.min(from.x, to.x) > center.x + radius
                || Math.max(from.y, to.y) < center.y - radius || Math.min(from.y, to.y) > center.y + radius) return false;
            const dx = to.x - from.x, dy = to.y - from.y;
            const length = dx * dx + dy * dy;
            const t = Math.max(0, Math.min(1, ((center.x - from.x) * dx + (center.y - from.y) * dy) / (length || 1)));
            const start = (from.x - center.x) ** 2 + (from.y - center.y) ** 2;
            // Allow escape from an existing overlap, but never cross through its center.
            if (t === 0 && start < radius * radius && (to.x - center.x) ** 2 + (to.y - center.y) ** 2 > start) return false;
            return (from.x + t * dx - center.x) ** 2 + (from.y + t * dy - center.y) ** 2 < (radius - 0.01) ** 2;
        },
        clear(from, to, obstacles) { return !obstacles.some(item => this.intersects(from, to, item)); },
        index(obstacles) {
            const cells = new Map(), size = 160;
            const visit = (left, top, right, bottom, callback) => {
                for (let x = Math.floor(left / size); x <= Math.floor(right / size); x++) {
                    for (let y = Math.floor(top / size); y <= Math.floor(bottom / size); y++) callback(`${x},${y}`);
                }
            };
            for (const obstacle of obstacles) {
                const {center, radius} = obstacle;
                visit(center.x - radius, center.y - radius, center.x + radius, center.y + radius, key => {
                    if (!cells.has(key)) cells.set(key, []);
                    cells.get(key).push(obstacle);
                });
            }
            const query = (left, top, right = left, bottom = top) => {
                const found = new Set();
                visit(left, top, right, bottom, key => {
                    for (const obstacle of cells.get(key) || []) found.add(obstacle);
                });
                return found;
            };
            // Visit only cells crossed by a segment, not its entire bounding rectangle.
            const visited = new Map();
            let visitID = 0;
            query.segment = (from, to, callback) => {
                const stamp = ++visitID;
                const check = (x, y) => {
                    for (const obstacle of cells.get(`${x},${y}`) || []) {
                        if (visited.get(obstacle) === stamp) continue;
                        visited.set(obstacle, stamp);
                        if (callback(obstacle)) return true;
                    }
                    return false;
                };
                let x = Math.floor(from.x / size), y = Math.floor(from.y / size);
                const endX = Math.floor(to.x / size), endY = Math.floor(to.y / size);
                const dx = to.x - from.x, dy = to.y - from.y;
                const stepX = Math.sign(dx), stepY = Math.sign(dy);
                const deltaX = dx ? size / Math.abs(dx) : Infinity, deltaY = dy ? size / Math.abs(dy) : Infinity;
                let nextX = dx ? ((x + (stepX > 0 ? 1 : 0)) * size - from.x) / dx : Infinity;
                let nextY = dy ? ((y + (stepY > 0 ? 1 : 0)) * size - from.y) / dy : Infinity;
                for (;;) {
                    if (check(x, y)) return true;
                    if (x === endX && y === endY) return false;
                    if (y === endY || x !== endX && nextX < nextY) { x += stepX; nextX += deltaX; }
                    else if (x === endX || nextY < nextX) { y += stepY; nextY += deltaY; }
                    else {
                        if (check(x + stepX, y) || check(x, y + stepY)) return true;
                        x += stepX; y += stepY; nextX += deltaX; nextY += deltaY;
                    }
                }
            };
            return query;
        },
        route(extra, target, stop = safeNum(window.BOT_FOLLOW_RADIUS, 175)) {
            const origin = extra.client.myPlayer.pos.current;
            extra.routeBlocker = null;
            extra.stopRadius = stop;
            if (origin.distance(target) <= stop) { BotPathfinderWorker.cancel(extra); extra.routePoint = null; extra.routePlan = null; return target; }
            // Stop at the near edge of the follow area instead of routing to the owner's center.
            const goal = target.addDirection(target.angle(origin), Math.max(0, stop));
            const obstacles = this.obstacles(extra, origin, target);
            const direct = obstacles.filter(item => this.intersects(origin, goal, item));
            if (!direct.length) { BotPathfinderWorker.cancel(extra); extra.routePoint = null; extra.routePlan = null; return target; }
            const signature = obstacles.map(o => `${o.item.id}:${o.center.x}:${o.center.y}:${o.radius}`).join('|');
            const now = Date.now();
            let plan = extra.routePlan;
            const hold = () => {
                extra.routePoint = null;
                extra.stopRadius = Math.min(4, stop);
                if (target && origin.distance(target) > stop) return target;
                return origin;
            };
            const waypoint = path => {
                for (let i = path.length - 1; i >= 0; i--) {
                    if (origin.distance(path[i]) > 0.1 && this.clear(origin, path[i], obstacles)) return i;
                }
                return -1;
            };
            const changed = plan && plan.signature !== signature;
            let invalid = !plan || plan.stop !== stop, next = -1;
            if (plan?.pending && !invalid && plan.target.distance(target) <= 120) return hold();
            if (plan?.pending) invalid = true;
            if (plan?.path && !invalid) {
                const endpoint = plan.path[plan.path.length - 1];
                if (!endpoint) invalid = true;
                else if (endpoint.distance(target) > stop + 0.5) {
                    // Small owner movements usually need only a new final segment.
                    const anchor = plan.path.length > 1 ? plan.path[plan.path.length - 2] : origin;
                    const finish = anchor.distance(target) <= stop ? anchor : target.addDirection(target.angle(anchor), Math.max(0, stop - 0.05));
                    if (plan.target.distance(target) <= 100 && finish.x >= 35 && finish.x <= 14365 && finish.y >= 35 && finish.y <= 14365 && this.clear(anchor, finish, obstacles)) {
                        plan.path[plan.path.length - 1] = finish;
                        plan.target = new Vector_default(target.x, target.y);
                    } else invalid = true;
                }
                if (changed && obstacles.some(obstacle => plan.radii.has(obstacle.item.id) && plan.radii.get(obstacle.item.id) !== obstacle.radius)) invalid = true;
                if (!invalid) {
                    next = waypoint(plan.path);
                    invalid = next < 0;
                    // Changed off-route objects must not discard a still-safe route.
                    if (changed && !invalid) {
                        for (let i = next + 1; i < plan.path.length; i++) {
                            if (!this.clear(plan.path[i - 1], plan.path[i], obstacles)) { invalid = true; break; }
                        }
                    }
                }
            } else if (plan && !plan.pending && !invalid) {
                const retryDelay = 1500 + Math.abs(Number(extra.client.myPlayer.id) || 0) % 7 * 83;
                invalid = changed || (plan.failed ? now >= BotPathfinderWorker.retryAt
                    : now - plan.time > retryDelay || plan.origin.distance(origin) > 40 || plan.target.distance(target) > 100);
            }
            if (invalid) {
                BotPathfinderWorker.cancel(extra);
                plan = extra.routePlan = {time:now, signature, stop, origin:new Vector_default(origin.x, origin.y),
                    target:new Vector_default(target.x, target.y), radii:new Map(obstacles.map(obstacle => [obstacle.item.id, obstacle.radius])), path:null, pending:false, failed:false};
                if (obstacles.length > 8) BotPathfinderWorker.submit(extra, plan, obstacles);
                else plan.path = this.search(origin, target, obstacles, Math.max(0, stop));
                if (plan.path) next = waypoint(plan.path);
            } else if (changed) {
                plan.signature = signature;
                plan.radii = new Map(obstacles.map(obstacle => [obstacle.item.id, obstacle.radius]));
            }
            if (plan.pending || plan.failed) return hold();
            if (plan.path && next >= 0) {
                extra.routePoint = plan.path[next];
                extra.stopRadius = 4;
                return extra.routePoint;
            }
            extra.routePoint = null;
            return hold();
        },
        search(origin, target, obstacles, arrivalRadius = 0) {
            // The virtual goal can be reached from any side of the owner's follow area.
            const nodes = [origin, null], query = this.index(obstacles), nodeCells = new Map(), obstacleNodes = new Map();
            const visible = (from, to) => !query.segment(from, to, obstacle => this.intersects(from, to, obstacle));
            const add = (point, obstacle = null) => {
                if (point.x < 35 || point.y < 35 || point.x > 14365 || point.y > 14365) return;
                for (const o of query(point.x, point.y)) if ((point.x - o.center.x) ** 2 + (point.y - o.center.y) ** 2 < o.radius ** 2) return;
                const x = Math.floor(point.x / 2), y = Math.floor(point.y / 2);
                for (let dx = -1; dx <= 1; dx++) {
                    for (let dy = -1; dy <= 1; dy++) {
                        const match = (nodeCells.get(`${x + dx},${y + dy}`) || []).find(id => (nodes[id].x - point.x) ** 2 + (nodes[id].y - point.y) ** 2 < 0.25);
                        if (match !== undefined) {
                            if (obstacle) {
                                if (!obstacleNodes.has(obstacle)) obstacleNodes.set(obstacle, new Set());
                                obstacleNodes.get(obstacle).add(match);
                            }
                            return match;
                        }
                    }
                }
                const key = `${x},${y}`;
                if (!nodeCells.has(key)) nodeCells.set(key, []);
                const id = nodes.length;
                nodeCells.get(key).push(id);
                nodes.push(point);
                if (obstacle) {
                    if (!obstacleNodes.has(obstacle)) obstacleNodes.set(obstacle, new Set());
                    obstacleNodes.get(obstacle).add(id);
                }
                return id;
            };
            add(target);
            for (let i = 0; i < 16 && arrivalRadius > 0; i++) add(target.addDirection(i * Math.PI / 8, arrivalRadius));
            for (const obstacle of obstacles) {
                // Circumscribed corners keep their connecting segments outside the collision circle.
                const radius = (obstacle.radius + 1) / Math.cos(Math.PI / 16);
                const base = obstacle.center.angle(origin);
                for (let i = 0; i < 16; i++) add(obstacle.center.addDirection(base + i * Math.PI / 8, radius), obstacle);
                for (const point of [origin, target]) {
                    const distance = point.distance(obstacle.center);
                    if (distance <= radius) continue;
                    const offset = Math.acos(radius / distance);
                    const angle = obstacle.center.angle(point);
                    add(obstacle.center.addDirection(angle + offset, radius), obstacle);
                    add(obstacle.center.addDirection(angle - offset, radius), obstacle);
                }
            }
            // Explicit entry, center and exit points preserve narrow, off-grid passages.
            const order = new Map(obstacles.map((obstacle, i) => [obstacle, i]));
            for (const obstacle of obstacles) {
                const {center, radius} = obstacle, reach = radius + 96;
                for (const other of query(center.x - reach, center.y - reach, center.x + reach, center.y + reach)) {
                    if (order.get(other) <= order.get(obstacle)) continue;
                    const distance = center.distance(other.center), gap = distance - radius - other.radius;
                    if (gap < 0.5 || gap > 96) continue;
                    const angle = center.angle(other.center);
                    const middle = center.addDirection(angle, radius + gap / 2);
                    const entry = Math.min(radius, other.radius) + 16;
                    for (const offset of [-entry, -24, 0, 24, entry]) {
                        const id = add(middle.addDirection(angle + Math.PI / 2, offset), obstacle);
                        if (id !== undefined) {
                            if (!obstacleNodes.has(other)) obstacleNodes.set(other, new Set());
                            obstacleNodes.get(other).add(id);
                        }
                    }
                }
            }
            const nodeGrid = new Map(), nodeCellSize = 240;
            for (let id = 2; id < nodes.length; id++) {
                const key = `${Math.floor(nodes[id].x / nodeCellSize)},${Math.floor(nodes[id].y / nodeCellSize)}`;
                if (!nodeGrid.has(key)) nodeGrid.set(key, []);
                nodeGrid.get(key).push(id);
            }
            const nearby = (point, radius = 420) => {
                const ids = new Set(), left = Math.floor((point.x - radius) / nodeCellSize), right = Math.floor((point.x + radius) / nodeCellSize);
                const top = Math.floor((point.y - radius) / nodeCellSize), bottom = Math.floor((point.y + radius) / nodeCellSize);
                for (let x = left; x <= right; x++) for (let y = top; y <= bottom; y++) {
                    for (const id of nodeGrid.get(`${x},${y}`) || []) if ((point.x - nodes[id].x) ** 2 + (point.y - nodes[id].y) ** 2 <= radius * radius) ids.add(id);
                }
                return ids;
            };
            const costs = Array(nodes.length).fill(Infinity), previous = Array(nodes.length).fill(-1);
            const open = [], closed = new Uint8Array(nodes.length);
            let sequence = 0;
            const priority = (a, b) => a.score < b.score || a.score === b.score && a.order < b.order;
            const push = id => {
                const entry = {id, cost:costs[id], score:costs[id] + (id === 1 ? 0 : Math.max(0, nodes[id].distance(target) - arrivalRadius)), order:sequence++};
                let at = open.length;
                open.push(entry);
                while (at > 0) {
                    const parent = (at - 1) >> 1;
                    if (!priority(entry, open[parent])) break;
                    open[at] = open[parent]; at = parent;
                }
                open[at] = entry;
            };
            const pop = () => {
                const first = open[0], last = open.pop();
                if (open.length) {
                    let at = 0;
                    while (at * 2 + 1 < open.length) {
                        let child = at * 2 + 1;
                        if (child + 1 < open.length && priority(open[child + 1], open[child])) child++;
                        if (!priority(open[child], last)) break;
                        open[at] = open[child]; at = child;
                    }
                    open[at] = last;
                }
                return first;
            };
            costs[0] = 0;
            push(0);
            while (open.length) {
                const entry = pop(), current = entry.id;
                if (closed[current] || entry.cost !== costs[current]) continue;
                if (current === 1) {
                    const path = [];
                    for (let id = 1; id !== 0; id = previous[id]) path.unshift(nodes[id]);
                    return path;
                }
                closed[current] = 1;
                const point = nodes[current];
                const finish = point.distance(target) <= arrivalRadius ? point : target.addDirection(target.angle(point), arrivalRadius);
                const finalCost = costs[current] + point.distance(finish);
                if (finalCost < costs[1] && finish.x >= 35 && finish.y >= 35 && finish.x <= 14365 && finish.y <= 14365 && visible(point, finish)) {
                    nodes[1] = finish;
                    costs[1] = finalCost;
                    previous[1] = current;
                    push(1);
                }
                const candidates = nearby(point);
                const blockers = [];
                query.segment(point, target, obstacle => {
                    if (this.intersects(point, target, obstacle)) blockers.push(obstacle);
                    return false;
                });
                blockers.sort((a, b) => (point.x - a.center.x) ** 2 + (point.y - a.center.y) ** 2 - ((point.x - b.center.x) ** 2 + (point.y - b.center.y) ** 2));
                blockers.length = Math.min(blockers.length, 6);
                for (const obstacle of blockers) for (const id of obstacleNodes.get(obstacle) || []) candidates.add(id);
                for (const id of candidates) {
                    if (closed[id]) continue;
                    const cost = costs[current] + nodes[current].distance(nodes[id]);
                    if (cost >= costs[id] || !visible(nodes[current], nodes[id])) continue;
                    costs[id] = cost;
                    previous[id] = current;
                    push(id);
                }
            }
            return null;
        }
    };

    const BotPathfinderWorker = {
        worker: null,
        current: null,
        queue: new Map,
        sequence: 0,
        timer: null,
        failed: false,
        retryAt: 0,
        failures: 0,
        stats: {submitted:0, completed:0, searchMilliseconds:0},
        source: `
            class Point {
                constructor(x, y) { this.x = x; this.y = y; }
                distance(point) { return Math.hypot(this.x - point.x, this.y - point.y); }
                angle(point) { return Math.atan2(point.y - this.y, point.x - this.x); }
                addDirection(angle, length) { return new Point(this.x + Math.cos(angle) * length, this.y + Math.sin(angle) * length); }
            }
            const finder = {${ExtraPathfinder.intersects.toString()}, ${ExtraPathfinder.index.toString()}, ${ExtraPathfinder.search.toString()}};
            onmessage = event => {
                const job = event.data, began = performance.now();
                try {
                    const origin = new Point(job.origin.x, job.origin.y), target = new Point(job.target.x, job.target.y);
                    const obstacles = job.obstacles.map(item => ({center:new Point(item.x, item.y), radius:item.radius}));
                    const path = finder.search(origin, target, obstacles, job.stop);
                    postMessage({id:job.id, path:path && path.map(point => ({x:point.x, y:point.y})), milliseconds:performance.now() - began});
                } catch (_) { postMessage({id:job.id, error:true}); }
            };`,
        submit(extra, plan, obstacles) {
            if (this.failed && Date.now() < this.retryAt) { plan.failed = true; return; }
            this.failed = false;
            plan.pending = true;
            const previous = this.queue.get(extra);
            if (previous) previous.plan.pending = false;
            const job = {id:++this.sequence, extra, plan, payload:{origin:{x:plan.origin.x, y:plan.origin.y},
                target:{x:plan.target.x, y:plan.target.y}, stop:plan.stop,
                obstacles:obstacles.map(obstacle => ({x:obstacle.center.x, y:obstacle.center.y, radius:obstacle.radius}))}};
            job.payload.id = job.id;
            this.queue.set(extra, job);
            this.stats.submitted++;
            this.pump();
        },
        valid(job) {
            return !job.cancelled && job.extra.routePlan === job.plan && job.extra.client.myPlayer.inGame
                && !job.extra.client.crossServer && job.extra.effectiveMode() !== 'stay';
        },
        pump() {
            if (this.current || this.failed) return;
            let job;
            for (const [extra, candidate] of this.queue) {
                this.queue.delete(extra);
                if (this.valid(candidate)) { job = candidate; break; }
                candidate.plan.pending = false;
            }
            if (!job) return;
            this.current = job;
            if (!this.worker) {
                let url;
                try {
                    url = URL.createObjectURL(new Blob([this.source], {type:'text/javascript'}));
                    this.worker = new Worker(url);
                    this.worker.onmessage = event => this.complete(event.data);
                    this.worker.onerror = event => { event.preventDefault(); this.fail(); };
                } catch (_) { this.fail(); }
                finally { if (url) URL.revokeObjectURL(url); }
            }
            if (!this.worker) return;
            this.timer = setTimeout(() => this.fail(), 1500);
            try { this.worker.postMessage(job.payload); } catch (_) { this.fail(); }
        },
        complete(result) {
            const job = this.current;
            if (!job || job.id !== result.id) return;
            if (result.error) { this.fail(); return; }
            clearTimeout(this.timer); this.timer = null;
            this.current = null;
            this.stats.completed++;
            this.failures = 0;
            this.stats.searchMilliseconds += Number.isFinite(result.milliseconds) ? result.milliseconds : 0;
            job.plan.pending = false;
            if (this.valid(job)) {
                job.plan.time = Date.now();
                job.plan.workerMilliseconds = result.milliseconds || 0;
                job.plan.failed = Boolean(result.error);
                job.plan.path = !result.error && Array.isArray(result.path)
                    ? result.path.map(point => new Vector_default(point.x, point.y)) : null;
            }
            this.pump();
        },
        cancel(extra) {
            const queued = this.queue.get(extra);
            if (queued) { queued.plan.pending = false; this.queue.delete(extra); }
            if (this.current?.extra === extra) {
                this.current.cancelled = true;
                this.current.plan.pending = false;
                if (!this.queue.size) {
                    clearTimeout(this.timer); this.timer = null;
                    this.worker?.terminate(); this.worker = null; this.current = null;
                }
            }
        },
        fail() {
            clearTimeout(this.timer); this.timer = null;
            this.worker?.terminate(); this.worker = null;
            const jobs = [...this.queue.values()];
            if (this.current) jobs.push(this.current);
            for (const job of jobs) { job.plan.pending = false; job.plan.failed = true; }
            this.current = null; this.queue.clear(); this.failed = true;
            this.retryAt = Date.now() + Math.min(30000, 5000 * 2 ** Math.min(this.failures++, 3));
        },
        reset() {
            this.fail();
            this.failed = false;
            this.retryAt = 0; this.failures = 0;
        }
    };

    class BotAnimalTrap {
        encounters = new Map;
        nextPlaceAt = 0;
        constructor(extra) { this.extra = extra; this.client = extra.client; }
        reset() { this.encounters.clear(); this.nextPlaceAt = 0; }
        attackRange(animal) {
            return (Animals_default[animal.type].hitRange || animal.scale) + this.client.myPlayer.scale;
        }
        threat(animal, now) {
            const me = this.client.myPlayer, data = Animals_default[animal.type];
            if (data?.hostile !== true || !data.dmg || animal.currentHealth <= 0 || now - animal.lastSeenAt > 500) return false;
            const distance = animal.pos.current.distance(me.pos.current), range = this.attackRange(animal);
            if (distance > range + 100) return false;
            // The first observation has no usable velocity. Never extrapolate from the map origin.
            const observed = animal.previousSeenAt != null && animal.lastSeenAt - animal.previousSeenAt <= 500;
            const velocity = observed ? animal.pos.current.copy().sub(animal.pos.previous) : new Vector_default;
            if (velocity.length > 90) velocity._setXY(0, 0);
            const toward = animal.pos.current.angle(me.pos.current);
            const closing = velocity.x * Math.cos(toward) + velocity.y * Math.sin(toward);
            if (closing < -2) return false;
            const facing = Math.cos(animal.angle - toward) > 0.5;
            if (distance <= range + 8) return animal.isDanger || closing > 2;
            if (!facing || closing <= 2) return false;
            const socket = this.client.SocketManager;
            const horizon = 1 + clamp(socket.pong || 0, 0, 111) / 111;
            return distance - closing * horizon <= range + 24;
        }
        intercepts(position, radius, animal) {
            const me = this.client.myPlayer.pos.current, start = animal.pos.current;
            const dx = me.x - start.x, dy = me.y - start.y, length = dx * dx + dy * dy;
            if (!length) return position.distance(start) <= radius;
            const t = ((position.x - start.x) * dx + (position.y - start.y) * dy) / length;
            if (t < 0 || t > 1) return false;
            return Math.hypot(position.x - start.x - dx * t, position.y - start.y - dy * t) <= radius;
        }
        nearby(animal) {
            const manager = this.client.ObjectManager;
            return [...manager.grid2D.queryFull(animal.pos.current.x, animal.pos.current.y, 1)]
                .map(id => manager.objects.get(id))
                .filter(object => object instanceof PlayerObject && object.health > 0 && (object.type === 15 || object.isSpike));
        }
        covered(animal, objects) {
            return objects.some(object => {
                if (object.type === 15 && !animal.canBeTrapped()) return false;
                const radius = animal.scale + object.collisionScale;
                if (object.type === 15 && object.pos.current.distance(animal.pos.current) < radius) return true;
                return this.intercepts(object.pos.current, radius, animal);
            });
        }
        postTick(now = Date.now()) {
            const bot = this.client, me = bot.myPlayer, handler = bot._ModuleHandler;
            if (bot.isOwner || !ExtraCommands.trapAnimals || !me.inGame || me.currentHealth <= 0) {
                this.reset(); return false;
            }
            const visible = bot.PlayerManager.visibleAnimals;
            for (const [id, entry] of this.encounters) {
                if (now - entry.lastSeenAt > 30000) this.encounters.delete(id);
                else if (now - entry.lastSeenAt > 700) entry.departed = true;
            }
            const threats = [];
            for (const animal of visible) {
                const entry = this.encounters.get(animal.id);
                if (entry) {
                    entry.lastSeenAt = animal.lastSeenAt;
                    if (animal.pos.current.distance(me.pos.current) > this.attackRange(animal) + 85) entry.departed = true;
                }
                if (this.threat(animal, now)) threats.push(animal);
            }
            if (handler.syncExecuting || handler.moduleActive || handler.healedOnce || handler.placedOnce ||
                bot.InputHandler.instaToggle || handler.staticModules.autoBreak.controlsAttack()) return false;
            threats.sort((a, b) => a.pos.current.distance(me.pos.current) - b.pos.current.distance(me.pos.current));
            for (const animal of threats) {
                const angle = me.pos.current.angle(animal.pos.current), entry = this.encounters.get(animal.id);
                const objects = this.nearby(animal);
                if (entry) {
                    const placed = objects.find(object => object.type === entry.itemID && object.pos.current.distance(entry.position) < 12);
                    if (placed) { entry.confirmed = true; entry.objectID = placed.id; }
                    const removed = entry.confirmed && !bot.ObjectManager.objects.has(entry.objectID);
                    const newSide = getAngleDist(angle, entry.angle) >= Math.PI / 3;
                    const movedAway = me.pos.current.distance(entry.origin) >= 70;
                    if (now - entry.placedAt < 600 || !(entry.departed || newSide || movedAway || removed)) continue;
                }
                if (this.covered(animal, objects)) continue;
                if (now < this.nextPlaceAt) return false;
                // A trap that cannot be used (inventory, cost, limit, immunity or space) falls back to one spike.
                const types = animal.canBeTrapped() && me.getItemByType(7) === 15 ? [7, 4] : [4];
                for (const type of types) {
                    if (!me.canPlace(type)) continue;
                    const itemID = me.getItemByType(type), item = Items[itemID];
                    for (const offset of [0, Math.PI / 12, -Math.PI / 12, Math.PI / 6, -Math.PI / 6]) {
                        const direction = angle + offset, position = me.getPlacePosition(me.pos.current, itemID, direction);
                        if (!this.intercepts(position, animal.scale + item.scale * (item.colDiv || 1), animal)) continue;
                        if (!this.extra.place(type, direction)) continue;
                        this.encounters.set(animal.id, {angle, origin:me.pos.current.copy(), position, itemID,
                            placedAt:now, lastSeenAt:animal.lastSeenAt, departed:false, confirmed:false, objectID:null});
                        this.nextPlaceAt = now + 250;
                        return true;
                    }
                }
            }
            return false;
        }
    }

    // Bots Extra menu command adapter
    const ExtraCommands = Object.create(null);
    ExtraCommands.mode = 'stay';
    ExtraCommands.modeStarted = Date.now();
    const BotFollowPlayers = {
        sources(owner, preferred = null) {
            return [...new Set([preferred, owner, ...owner.clients])].filter(source => source && !source.crossServer && source.SocketManager.socket?.readyState !== 3);
        },
        list(owner) {
            const players = new Map();
            for (const source of this.sources(owner)) {
                for (const player of source.PlayerManager?.players || []) {
                    if (player && Number.isFinite(player.id) && player.currentHealth > 0 && player.id !== owner.myPlayer.id) {
                        if (!players.has(player.id)) players.set(player.id, player);
                    }
                }
            }
            return players;
        },
        resolve(bot, id = Number(ExtraCommands.targetPlayerId)) {
            if (!Number.isFinite(id) || id === bot.myPlayer.id) return null;
            for (const source of this.sources(bot.ownerClient, bot)) {
                const player = source.PlayerManager?.players.find(player => player?.id === id && player.currentHealth > 0);
                if (player?.pos?.current) return player;
            }
            return null;
        }
    };
    const BotSurroundEnemy = {
        cache: new WeakMap(),
        bots(owner) {
            return [...owner.clients].filter(bot => bot.ownerClient === owner && !bot.crossServer &&
                !bot.disconnectRequested && bot.myPlayer.inGame && bot.SocketManager.socket?.readyState === 1);
        },
        valid(owner, enemy) {
            return enemy instanceof Player_default && Number.isFinite(enemy.id) && enemy.currentHealth > 0 &&
                enemy.id !== owner.myPlayer.id && !owner.isBotByID(enemy.id) && owner.myPlayer.isEnemyByID(enemy.id) &&
                !(owner.myPlayer.clanName !== null && owner.myPlayer.clanName === enemy.clanName) &&
                Number.isFinite(enemy.pos.current.x) && Number.isFinite(enemy.pos.current.y);
        },
        *observations(owner) {
            const seen = new Set();
            for (const source of [owner, ...BotAutoShoot.sharedViews(owner)]) {
                if (!BotAutoShoot.freshView(source)) continue;
                for (const enemy of source.PlayerManager.players) {
                    if (!(enemy instanceof Player_default) || seen.has(enemy.id)) continue;
                    seen.add(enemy.id);
                    yield {source, enemy};
                }
            }
        },
        nearest(owner) {
            if (!owner.myPlayer.inGame) return null;
            let target = null, distance = Infinity;
            for (const {enemy} of this.observations(owner)) {
                if (!this.valid(owner, enemy)) continue;
                const next = owner.myPlayer.pos.current.distance(enemy.pos.current);
                if (next < distance) { target = enemy; distance = next; }
            }
            return target;
        },
        resolve(owner) {
            const id = ExtraCommands.surroundTargetId;
            if (ExtraCommands.mode !== 'surround' || !Number.isFinite(id)) return null;
            const now = performance.now(), cached = this.cache.get(owner);
            // Share the target lookup across bots without retaining an out-of-sight position.
            if (cached?.id === id && now - cached.checkedAt < 50) {
                if (!cached.enemy) return null;
                if (BotAutoShoot.freshView(cached.source, now) &&
                    cached.source.PlayerManager.players.includes(cached.enemy) && this.valid(owner, cached.enemy)) return cached.enemy;
            }
            const observation = [...this.observations(owner)].find(entry => entry.enemy.id === id);
            const enemy = observation && this.valid(owner, observation.enemy) ? observation.enemy : null;
            this.cache.set(owner, {id, checkedAt:now, source:observation?.source, enemy});
            return enemy;
        }
    };
    const BotKillChat = {
        sequence: 0,
        broadcast() {
            const message = String(Settings_default._killMessageText || '').trim();
            if (!message) return;
            this.sequence = (this.sequence + 1) % 64;
            const separator = this.sequence.toString(2).padStart(6, '0').replace(/0/g, '\u200b').replace(/1/g, '\u2060');
            const text = message.slice(0, 24) + separator;
            for (const bot of client.clients) {
                if (!bot.myPlayer.inGame || bot.SocketManager.socket?.readyState !== 1) continue;
                try { bot.PacketManager.chat(text); }
                catch (error) { console.warn('[Bot chat]', error.message); }
            }
        }
    };
    const safeNum = (value, fallback) => Number.isFinite(Number(value)) ? Number(value) : fallback;
    function extraBotName(bot) {
        if (bot.botName) return bot.botName;
        const base = String(Settings_default._botNickname || '').trim();
        if (base) {
            if (!Settings_default._botNickNumber) return bot.botName = base.slice(0, 15);
            const others = [...bot.ownerClient.clients, ...CrossServerBots.connections.bots].filter(other => other !== bot);
            const used = new Set(others.map(other => other.botNumber));
            let n = 1;
            while (used.has(n)) n++;
            bot.botNumber = n;
            return bot.botName = base.slice(0, 15 - String(n).length) + n;
        }
        const used = new Set([...bot.ownerClient.clients].map(other => other.botName));
        const names = Array.from({length:246}, (_, index) => `bot${index + 1}`);
        const available = names.filter(name => !used.has(name));
        const pool = available.length ? available : names;
        bot.botName = pool[Math.floor(Math.random() * pool.length)];
        return bot.botName;
    }
    function extraConsumesInput(event) {
        const target = event.target;
        if (event.type === 'keydown') {
            return Boolean(target?.closest?.('#gmx-panel') &&
                (target?.matches?.('input, textarea, select') || target?.isContentEditable));
        }
        return Boolean(target?.closest?.('#gmx-panel, #colean-extra-launcher'));
    }
    function setOwnerCommanderField(tid, key, value) {
        if (tid !== 'all') throw new Error('Extra menu commands target all bots');
        if (key === 'syncShot') return CombatControl.syncHit();
        if (value === null) delete ExtraCommands[key];
        else ExtraCommands[key] = value;
        if (key === 'mode') {
            if (value !== 'surround') delete ExtraCommands.surroundTargetId;
            BotSurroundEnemy.cache.delete(client);
            ExtraCommands.modeStarted = Date.now();
            for (const bot of client.clients) bot._ModuleHandler.staticModules.aibmExtra.resetMovement();
        }
        ExtraCommands.lastUpdated = Date.now();

        try {
            window.ExtraCommands = ExtraCommands;
            window.setOwnerCommanderField = setOwnerCommanderField;
            window.__coleanClient = function () { return client; };
            window.ColeanHosts && window.ColeanHosts.onCommander && window.ColeanHosts.onCommander(ExtraCommands);
        } catch (e) {}

        return ExtraCommands;
    }
    function readOwnerCommanderField(tid, key) { return tid === 'all' ? ExtraCommands[key] : undefined; }
    const extraInstakill = {
        get _enabled() { return client.InputHandler.instaToggle; },
        enable() { client.InputHandler.setInstakill(true); },
        disable() { client.InputHandler.setInstakill(false); }
    };
    const extraBowInsta = {
        trigger() { client.InputHandler.setInstakill(true); }
    };

    class ColeanExtraBot {
        moduleName = 'aibmExtra';
        stopRadius = 20;
        randomPosition = null;
        randomUntil = 0;
        millsFinished = false;
        millCount = 0;
        millPending = [];
        millPlacements = [];
        gatherObject = null;
        cycleAt = [0, 0];
        cycleIndex = [0, 0];
        cycleItem = [null, null];
        platformPlacement = null;
        constructor(bot) { this.client = bot; this.animalTrap = new BotAnimalTrap(this); }
        hasMovement() { return !this.client.isOwner && Boolean(ExtraCommands.mode); }
        resetRoute() {
            BotPathfinderWorker.cancel(this);
            this.routePlan = this.routePoint = this.routeBlocker = this.routeTarget = this.routeResult = null;
            this.routeTick = this.routeObjectCount = -1;
            this.pathBreakTarget = this.breakingAction = null;
            this.navigationTarget = null;
            this.navigationHolding = false;
        }
        resetMovement() { this.resetRoute(); this._followSettled = false; this._followHoldSpot = null; this._followHoldOwner = null; this._followFace = null; this.millsFinished = false; this.millCount = 0; this.millPending = []; this.randomPosition = null; this.randomUntil = 0; this.gatherObject = null; this.client._ModuleHandler?.staticModules?.movement?.resetFormation(); }
        reset() {
            this.animalTrap.reset();
            if (this.client._ModuleHandler) { this.client._ModuleHandler.pendingSync = null; this.client._ModuleHandler.syncExecuting = false; this.client._ModuleHandler.autoShootExecuting = false; }
            this.resetMovement();
            this.millPlacements = [];
            this.platformPlacement = null;
            this.cycleAt = [0, 0];
            this.cycleItem = [null, null];
        }
        ownerPosition() {
            const owner = this.client.ownerClient;
            return owner.InputHandler.lockPosition ? owner.InputHandler.lastPosition : owner.myPlayer.pos.current;
        }
        wander() {
            const pos = this.client.myPlayer.pos.current;
            if (!this.randomPosition || Date.now() >= this.randomUntil || pos.distance(this.randomPosition) < 90) {
                this.randomUntil = Date.now() + 5000;
                const target = pos.addDirection(Math.random() * Math.PI * 2, 600 + Math.random() * 1200);
                this.randomPosition = new Vector_default(Math.max(100, Math.min(14300, target.x)), Math.max(100, Math.min(14300, target.y)));
            }
            return this.randomPosition;
        }
        objects() { return this.client.ObjectManager.objects.values(); }
        nearest(predicate) {
            let result = null, distance = Infinity;
            const pos = this.client.myPlayer.pos.current;
            for (const item of this.objects()) {
                if (!predicate(item)) continue;
                const next = pos.distance(item.pos.current);
                if (next < distance) { result = item; distance = next; }
            }
            return result;
        }
        gatherTypeKey(type) {
            return ({0: 'wood', 1: 'food', 2: 'stone', 3: 'gold'})[type] || 'wood';
        }
        gatherResKey(item) {
            if (!item) return null;
            if (item.id != null) return item.id;
            const p = item.pos?.current;
            return p ? (Math.round(p.x) + ':' + Math.round(p.y)) : null;
        }
        isGatherBlacklisted(item) {
            if (!this._gatherBlacklist) this._gatherBlacklist = new Map();
            const key = this.gatherResKey(item);
            if (key == null) return false;
            const until = this._gatherBlacklist.get(key);
            if (until == null) return false;
            if (performance.now() >= until) {
                this._gatherBlacklist.delete(key);
                return false;
            }
            return true;
        }
        blacklistGather(item, ms = 8000) {
            if (!this._gatherBlacklist) this._gatherBlacklist = new Map();
            const key = this.gatherResKey(item);
            if (key == null) return;
            this._gatherBlacklist.set(key, performance.now() + ms);
            this._gatherProg = null;
        }
        // True if bot has been stuck near a node without gaining that resource type
        isGatherStuck(res, type) {
            const me = this.client.myPlayer;
            if (!me?.pos?.current || !res?.pos?.current) return false;
            const key = this.gatherTypeKey(type);
            const amt = me.resources?.[key] || 0;
            const resKey = this.gatherResKey(res);
            const now = performance.now();
            if (!this._gatherProg || this._gatherProg.resKey !== resKey || this._gatherProg.type !== type) {
                this._gatherProg = {resKey, type, amt, since: now, nearSince: null};
                return false;
            }
            if (amt > this._gatherProg.amt) {
                this._gatherProg.amt = amt;
                this._gatherProg.since = now;
                this._gatherProg.nearSince = null;
                return false;
            }
            const dist = me.pos.current.distance(res.pos.current);
            const hit = safeNum(res.hitScale ?? res.collisionScale, 40);
            const weapon = DataHandler_default.getWeapon(me.getItemByType(0));
            const range = (weapon?.range || 65) + hit + 25;
            // "Trying to farm" — close enough that hits should land if not blocked
            if (dist <= range + 40) {
                if (this._gatherProg.nearSince == null) this._gatherProg.nearSince = now;
                // ~2s near without gain → crowded / not hitting
                if (now - this._gatherProg.nearSince >= 2000) return true;
            } else {
                this._gatherProg.nearSince = null;
                // Walking for a long time to same node is fine; don't blacklist yet
            }
            return false;
        }
        // Dynamic max bots/resource + per-bot blacklist if not gaining
        claimGatherResource(type, maxPerResource = null) {
            const me = this.client.myPlayer;
            const owner = this.client.ownerClient;
            if (!me?.pos?.current || !owner) return this.nearest(item => this.isGatherResource(item, type));

            const bots = [...owner.clients]
                .filter(b => b && !b.crossServer && b.myPlayer?.inGame && Number.isFinite(b.myPlayer.pos?.current?.x))
                .sort((a, b) => (a.myPlayer.id || 0) - (b.myPlayer.id || 0) || String(a.clientID||'').localeCompare(String(b.clientID||'')));

            const pool = [];
            const seen = new Set();
            const pushRes = (item) => {
                if (!item?.pos?.current || !this.isGatherResource(item, type)) return;
                const key = this.gatherResKey(item);
                if (key == null || seen.has(key)) return;
                seen.add(key);
                pool.push(item);
            };
            try {
                for (const item of owner.ObjectManager.objects.values()) pushRes(item);
            } catch (_) {}
            for (const item of this.objects()) pushRes(item);

            const origin = owner.myPlayer?.pos?.current || me.pos.current;
            pool.sort((a, b) => {
                const da = origin.distance(a.pos.current);
                const db = origin.distance(b.pos.current);
                if (da !== db) return da - db;
                return (a.id || 0) - (b.id || 0);
            });

            if (!pool.length) return null;

            // Dynamic capacity: split bots across nodes, capped by physical ring size
            const botCount = bots.length;
            const resCount = pool.length;
            let avgHit = 0;
            for (const r of pool) avgHit += safeNum(r.hitScale ?? r.collisionScale, 40);
            avgHit /= resCount;
            const standR = avgHit + safeNum(me.scale, 35) + 12;
            const ringCap = Math.max(2, Math.min(5, Math.floor((2 * Math.PI * standR) / 72)));
            let maxPer = Math.ceil(botCount / resCount);
            maxPer = Math.max(1, Math.min(ringCap, maxPer));
            if (Number.isFinite(maxPerResource) && maxPerResource > 0) {
                maxPer = Math.max(1, Math.min(maxPer, maxPerResource | 0));
            }

            const assignment = new Map();
            let botIdx = 0;
            for (const res of pool) {
                for (let k = 0; k < maxPer && botIdx < bots.length; k++, botIdx++) {
                    assignment.set(bots[botIdx], res);
                }
                if (botIdx >= bots.length) break;
            }
            while (botIdx < bots.length) {
                assignment.set(bots[botIdx], pool[botIdx % pool.length]);
                botIdx++;
            }

            let claimed = assignment.get(this.client) || pool[0];

            // Prefer visible node if assignment is outside FOV
            const localIds = new Set();
            for (const item of this.objects()) {
                if (item && item.id != null) localIds.add(item.id);
            }
            if (claimed.id != null && !localIds.has(claimed.id)) {
                const visible = this.nearest(item => this.isGatherResource(item, type) && !this.isGatherBlacklisted(item));
                if (visible) claimed = visible;
            }

            // Stuck near node without gains → blacklist and pick another
            if (claimed && this.isGatherStuck(claimed, type)) {
                this.blacklistGather(claimed, 9000);
            }
            if (claimed && this.isGatherBlacklisted(claimed)) {
                const alt = pool.find(r => r !== claimed && this.gatherResKey(r) !== this.gatherResKey(claimed) && !this.isGatherBlacklisted(r))
                    || pool.find(r => !this.isGatherBlacklisted(r));
                if (alt) claimed = alt;
            }

            // Track progress for the chosen node
            this.isGatherStuck(claimed, type); // init/update tracker

            const claimKey = this.gatherResKey(claimed);
            const peers = bots.filter(b => this.gatherResKey(assignment.get(b)) === claimKey);
            // If we self-switched off assignment, still get a free slot index
            let slot = peers.indexOf(this.client);
            if (slot < 0) slot = Math.abs((me.id || 0) + (claimed.id || 0)) % Math.max(1, peers.length || 1);
            this._gatherSlotIndex = slot;
            this._gatherSlotCount = Math.max(1, peers.length || 1);
            this._gatherMaxPer = maxPer;
            return claimed;
        }
        gatherStandPoint(resource) {
            if (!resource?.pos?.current) return null;
            const me = this.client.myPlayer;
            const center = resource.pos.current;
            const botScale = safeNum(me.scale, 35);
            const hit = safeNum(resource.collisionScale ?? resource.hitScale, 40);
            const stand = botScale + hit + 12;
            const n = Math.max(1, this._gatherSlotCount || 1);
            const i = Math.max(0, this._gatherSlotIndex || 0);
            const angle = (i / n) * Math.PI * 2 + (resource.id || 0) * 0.17;
            return new Vector_default(
                center.x + Math.cos(angle) * stand,
                center.y + Math.sin(angle) * stand
            );
        }
        isGatherResource(item, type) {
            if (item instanceof Resource) return item.type === type && !item.isCactus;
            if (!(item instanceof PlayerObject) || item.health <= 0 || ![13, 14].includes(item.type)) return false;
            return Items[item.type].type === type;
        }
        ownerFaceAngle() {
            const owner = this.client.ownerClient;
            if (!owner) return 0;
            const ownerPlayer = owner.myPlayer;
            const ih = owner.InputHandler;
            const mh = owner._ModuleHandler;

            // Look direction (head / cursor)
            let look = null;
            if (ih && Number.isFinite(ih.mouse?.angle)) look = ih.mouse.angle;
            else if (Number.isFinite(mh?._currentAngle)) look = mh._currentAngle;
            else {
                const mp = ownerPlayer?.pos?.current;
                const cur = ih?.cursorPosition?.(true);
                if (mp && cur && Number.isFinite(cur.x)) look = Math.atan2(cur.y - mp.y, cur.x - mp.x);
            }

            // Movement direction (where the body is running)
            let move = null;
            let speed2 = 0;
            const op = ownerPlayer?.pos;
            if (op?.current && op?.old) {
                const vx = op.current.x - op.old.x;
                const vy = op.current.y - op.old.y;
                speed2 = vx * vx + vy * vy;
                if (speed2 > 2.25) move = Math.atan2(vy, vx);
            }
            if (move == null && Number.isFinite(ownerPlayer?.speed) && ownerPlayer.speed > 5 && Number.isFinite(mh?.move_dir)) {
                move = mh.move_dir;
                speed2 = Math.max(speed2, 10);
            }
            const isMoving = speed2 > 2.25 || (mh?.isMoving && (ownerPlayer?.speed || 0) > 4);

            // Running → behind the path of movement; standing → behind where you look
            let face = isMoving && move != null ? move : (look != null ? look : 0);
            if (!Number.isFinite(face)) face = 0;

            const prev = this._followFace;
            if (Number.isFinite(prev)) {
                let d = face - prev;
                while (d > Math.PI) d -= Math.PI * 2;
                while (d < -Math.PI) d += Math.PI * 2;
                // Faster snap when switching run/stand so bots don't lag behind the wrong side
                const k = isMoving ? 0.35 : 0.28;
                face = prev + d * k;
            }
            this._followFace = face;
            this._followUsingMove = !!isMoving;
            return face;
        }
        followWedge(center) {
            const owner = this.client.ownerClient;
            const me = this.client.myPlayer;
            const ownerPlayer = owner?.myPlayer;
            if (!center || !ownerPlayer?.pos?.current) return center;
            const face = this.ownerFaceAngle();
            this._followFace = face;
            const behind = face + Math.PI;
            const base = Math.max(150, Math.min(380, safeNum(window.BOT_FOLLOW_RADIUS, 180)));
            const ownerScale = safeNum(ownerPlayer.scale, 35);
            const botScale = safeNum(me.scale, 35);
            // Stay outside owner body so they never push him from inside
            const clear = ownerScale + botScale + 48;
            this._followClear = clear;
            const bots = [...owner.clients]
                .filter(b => b && !b.crossServer && b.myPlayer?.inGame && Number.isFinite(b.myPlayer.pos?.current?.x))
                .sort((a, b) => (a.myPlayer.id || 0) - (b.myPlayer.id || 0));
            const index = Math.max(0, bots.indexOf(this.client));
            // Fan in an arc BEHIND the player (not a full ring)
            const n = Math.max(1, bots.length);
            const spread = Math.min(1.35, 0.28 + n * 0.09); // radians total fan
            const t = n <= 1 ? 0 : (index / (n - 1)) * 2 - 1; // -1 .. +1
            const slotAngle = behind + t * (spread / 2);
            // Deeper rows for many bots
            const row = Math.floor(index / 5);
            const dist = Math.max(clear + 30, base) + row * (botScale * 1.8 + 32);
            this.stopRadius = Math.max(20, botScale * 0.5);
            return new Vector_default(
                center.x + Math.cos(slotAngle) * dist,
                center.y + Math.sin(slotAngle) * dist
            );
        }
        // Always approach the behind-slot by walking on a circle around the owner
        followOrbitWaypoint(from, to, ownerPos, minR) {
            if (!from || !to || !ownerPos) return to;
            const rMin = Math.max(55, minR || 80);
            const aFrom = Math.atan2(from.y - ownerPos.y, from.x - ownerPos.x);
            const aTo = Math.atan2(to.y - ownerPos.y, to.x - ownerPos.x);
            let d = aTo - aFrom;
            while (d > Math.PI) d -= Math.PI * 2;
            while (d < -Math.PI) d += Math.PI * 2;
            const distFrom = from.distance(ownerPos);
            const distTo = to.distance(ownerPos);
            // Already near the target slot and outside body
            if (from.distance(to) < 50 && distFrom >= rMin * 0.9) return to;
            // If angular gap is large OR we are inside/near owner — force arc step
            const needOrbit = Math.abs(d) > 0.35 || distFrom < rMin + 15;
            if (!needOrbit) {
                // Straight line must not clip the owner circle
                const dx = to.x - from.x, dy = to.y - from.y;
                const len2 = dx * dx + dy * dy;
                if (len2 > 1) {
                    let t = ((ownerPos.x - from.x) * dx + (ownerPos.y - from.y) * dy) / len2;
                    t = Math.max(0, Math.min(1, t));
                    const px = from.x + dx * t, py = from.y + dy * t;
                    if (Math.hypot(px - ownerPos.x, py - ownerPos.y) >= rMin) return to;
                } else return to;
            }
            // Step along shorter arc, radius clamped outside collision
            const step = Math.sign(d || 1) * Math.min(Math.abs(d), 0.55);
            const a = aFrom + step;
            const r = Math.max(rMin + 12, Math.min(Math.max(distFrom, rMin + 12), distTo + 40));
            return new Vector_default(
                ownerPos.x + Math.cos(a) * r,
                ownerPos.y + Math.sin(a) * r
            );
        }
        formation(center, mode) {
            const owner = this.client.ownerClient;
            const stable = mode === 'circle' || mode === 'surround';
            const bots = stable ? BotSurroundEnemy.bots(owner) : [...owner.clients];
            if (stable && !bots.includes(this.client)) return null;
            const index = Math.max(0, bots.indexOf(this.client));
            const age = (Date.now() - (ExtraCommands.modeStarted || Date.now())) / 1000;
            const rotating = mode === 'circlespin' || mode === 'squarespin';
            const offset = rotating ? age * safeNum(ExtraCommands.spin?.speed, 1) * safeNum(ExtraCommands.spin?.dir, 1) : 0;
           if (mode === 'circle' || mode === 'circlespin' || mode === 'surround') {
                const count = Math.max(1, bots.length);
                let radius = safeNum(ExtraCommands.circle?.radius, 175);
                if (count > 1) radius = Math.max(radius, 40 / Math.sin(Math.PI / count));
                const angle = -Math.PI / 2 + index * 2 * Math.PI / count + offset;
                return center.addDirection(angle, radius);
            }
            const radius = safeNum(ExtraCommands.square?.radius, 175) + Math.floor(index / 4) * 25;
            return center.addDirection(index % 4 * Math.PI / 2 + offset, radius * Math.SQRT2);
        }
        millRoom() {
            const count = this.client.myPlayer.getItemCount(3).count;
            if (count > this.millCount) this.millPending.splice(0, count - this.millCount);
            this.millCount = count;
            this.millPending = this.millPending.filter(time => Date.now() - time < 1500);
            if (count >= 199) this.millsFinished = true;
            return this.millsFinished ? 0 : Math.max(0, 199 - count - this.millPending.length);
        }
        effectiveMode() {
            if (ExtraCommands.mode !== 'randommill') return ExtraCommands.mode;
            this.millRoom();
            return this.millsFinished ? 'follow' : 'randommill';
        }
        placeMillGroup(angle) {
            const me = this.client.myPlayer, handler = this.client._ModuleHandler;
            if (ExtraCommands.mode !== 'randommill' || !me.inGame || this.client.isOwner || this.client.crossServer || !Number.isFinite(angle) ||
                handler.placedOnce || handler.healedOnce || !me.canPlace(5)) return false;
            const id = me.getItemByType(5), item = Items[id];
            const now = Date.now();
            this.millPlacements = this.millPlacements.filter(entry => now - entry.time < 1500);
            const {count, limit} = me.getItemCount(item.itemGroup);
            const room = Math.min(this.millRoom(), Math.max(0, limit - count - this.millPending.length));
            const size = Math.min(3, room);
            if (size <= 0) return false;
            // Wait for enough resources for a whole group, except for the last slots at the mill limit.
            if (!me.isSandbox && Object.entries(item.cost).some(([resource, cost]) => me.resources[resource] < cost * size)) return false;
            const distance = me.getItemPlaceScale(id);
            // A real gap avoids side mills being rejected after coordinate rounding at tangent contact.
            const offset = 2 * Math.asin(Math.min(1, (2 * item.scale + 2) / (2 * distance)));
            const angles = [angle, angle - offset, angle + offset].slice(0, size);
            const positions = angles.map(value => me.getPlacePosition(me.pos.current, id, value));
            if (!angles.every(value => me.canPlaceObject(5, value))) return false;
            if (positions.some(position => this.millPlacements.some(entry => position.distance(entry.position) < item.scale + entry.scale + 2))) return false;
            // Preflight every position before sending any placement; blocked sides must not leave a single trail.
            try {
                for (let i = 0; i < angles.length; i++) {
                    // Keep item selection and attack release for every mill, then restore the weapon once.
                    handler.place(5, angles[i], true, false);
                    handler.placedOnce = true;
                    handler.placeAngles[0] = 5;
                    handler.placeAngles[1].push(angles[i]);
                    this.millPlacements.push({position:positions[i], scale:item.scale, time:now});
                    this.millPending.push(now);
                }
            } finally {
                handler.whichWeapon();
            }
            return true;
        }
        usesStick() { return this.client.myPlayer.getItemByType(0) === 8; }
        canBreakPathObject(item) {
            return item instanceof PlayerObject && item.isDestroyable && item.health > 0 &&
                this.client.ObjectManager.objects.get(item.id) === item &&
                (!Items[item.type].ignoreCollision || [15, 22].includes(item.type) && this.client.myPlayer.isEnemyByID(item.ownerID));
        }
        breakingSlot() {
            const me = this.client.myPlayer;
            if (me.getItemByType(1) === 10) return 1;
            const id = me.getItemByType(0);
            return id !== null && id !== 8 && DataHandler_default.isMelee(id) ? 0 : null;
        }
        routeFollow(target, reuse = false, stop = safeNum(window.BOT_FOLLOW_RADIUS, 175)) {
            const tick = this.client._ModuleHandler.tickCount;
            const objectCount = this.client.ObjectManager.objects.size;
            if (reuse && this.routeTick === tick && this.routeStop === stop && this.routeObjectCount === objectCount && this.routeTarget?.distance(target) < 0.1) return this.routeResult;
            this.routeResult = ExtraPathfinder.route(this, target, stop);
            this.routeTick = tick;
            this.routeStop = stop;
            this.routeObjectCount = objectCount;
            this.routeTarget = new Vector_default(target.x, target.y);
            return this.routeResult;
        }
        preferRouteToBreaking(target) {
            const me = this.client.myPlayer;
            if (this.client.isOwner || this.effectiveMode() === 'stay' || me.isTrapped || me.trappedIn) return false;
            return this.usesStick() || this.navigationTarget != null && this.pathBreakTarget !== target;
        }
        navigate(target, stop) {
            if (this.client.isOwner || this.client.crossServer) return target;
            const key = `${ExtraCommands.mode}:${this.client.myPlayer.getItemByType(0)}:${this.breakingSlot()}`;
            if (this.navigationKey !== key) { this.resetRoute(); this.navigationKey = key; }
            this.navigationTarget = target;
            this.navigationHolding = false;
            this.pathBreakTarget = null;
            this.stopRadius = stop;
            if (!target) { this.resetRoute(); return null; }
            const pos = this.client.myPlayer.pos.current;
            const point = this.routeFollow(target, false, stop);
            if (this.usesStick() || this.breakingSlot() === null || pos.distance(target) <= stop) return point;
            const distance = pos.distance(point);
            if (distance < 0.1) return point;
            const dx = (point.x - pos.x) / distance, dy = (point.y - pos.y) / distance;
            const length = point === target ? Math.max(0, distance - stop) : distance;
            const end = new Vector_default(pos.x + dx * length, pos.y + dy * length);
            let nearest = Infinity;
            for (const item of this.objects()) {
                if (!this.canBreakPathObject(item)) continue;
                const radius = item.collisionScale + this.client.myPlayer.scale + (item.isSpike ? 14 : 2);
                if (!ExtraPathfinder.intersects(pos, end, {center:item.pos.current, radius})) continue;
                const x = item.pos.current.x - pos.x, y = item.pos.current.y - pos.y;
                const along = x * dx + y * dy, across = Math.abs(x * dy - y * dx);
                const entry = Math.max(0, along - Math.sqrt(Math.max(0, radius * radius - across * across)));
                if (entry >= nearest) continue;
                nearest = entry;
                this.pathBreakTarget = item;
            }
            const obstacle = this.pathBreakTarget;
            if (!obstacle) return point;
            const weapon = DataHandler_default.getWeapon(this.client.myPlayer.getItemByType(this.breakingSlot()));
            const range = weapon.range + obstacle.hitScale - 6;
            if (pos.distance(obstacle.pos.current) <= range + 4) {
                this.navigationHolding = true;
                this.stopRadius = 4;
                return pos;
            }
            const x = obstacle.pos.current.x - pos.x, y = obstacle.pos.current.y - pos.y;
            const along = x * dx + y * dy, across = Math.abs(x * dy - y * dx);
            const travel = Math.max(0, along - Math.sqrt(Math.max(0, range * range - across * across)));
            this.stopRadius = 2;
            return new Vector_default(pos.x + dx * Math.min(length, travel), pos.y + dy * Math.min(length, travel));
        }
        breakPath() {
            const me = this.client.myPlayer;
            const target = this.pathBreakTarget, type = this.breakingSlot();
            if (this.client.isOwner || this.client.crossServer || this.usesStick() || type === null || !this.canBreakPathObject(target)) return false;
            const weapon = DataHandler_default.getWeapon(me.getItemByType(type));
            return me.pos.current.distance(target.pos.current) <= weapon.range + target.hitScale && this.requestAttack(target.pos.current, type, true);
        }
        cursorStop(target, minimum = 24) {
            const origin = this.client.myPlayer.pos.current;
            if (!origin || !target) return minimum;
            const distance = origin.distance(target);
            if (!Number.isFinite(distance) || distance <= .001) return minimum;
            const ux = (origin.x - target.x) / distance;
            const uy = (origin.y - target.y) / distance;
            let stop = minimum;
            for (const obstacle of ExtraPathfinder.obstacles(this, origin, target)) {
                const dx = target.x - obstacle.center.x;
                const dy = target.y - obstacle.center.y;
                const radius = obstacle.radius;
                const squared = dx * dx + dy * dy;
                if (squared >= radius * radius) continue;
                const projection = dx * ux + dy * uy;
                const exit = -projection + Math.sqrt(Math.max(0, projection * projection + radius * radius - squared));
                stop = Math.max(stop, exit + 2);
            }
            return stop;
        }
        directDestination(target, stop) {
            this.stopRadius = stop;
            if (this.routePlan || this.routePoint || this.routeBlocker || this.routeTarget || this.routeResult ||
                this.pathBreakTarget || this.breakingAction || this.navigationTarget || this.navigationHolding) this.resetRoute();
            return target;
        }
        destination() {
            const mode = this.effectiveMode();
            const me = this.client.myPlayer;
            let target = this.ownerPosition();
            this.stopRadius = 20;
            this.gatherObject = null;
            if (mode === 'stay') return this.navigate(null, 20);
            if (mode === 'follow') {
                const me = this.client.myPlayer;
                const pos = me.pos?.current;
                const ownerPos = this.client.ownerClient?.myPlayer?.pos?.current;
                if (!pos || !ownerPos) return this.navigate(null, 20);
                const face = this.ownerFaceAngle();
                const spot = this.followWedge(ownerPos);
                if (!spot) return this.navigate(null, 20);
                const botScale = safeNum(me.scale, 35);
                const clearR = Math.max(75, this._followClear || (botScale + 80));
                const dead = Math.max(36, botScale * 1.05);
                this.stopRadius = dead;

                const dist = pos.distance(spot);
                // Angular error vs "behind" — only park when we are actually in the back fan
                const ang = Math.atan2(pos.y - ownerPos.y, pos.x - ownerPos.x);
                const behind = face + Math.PI;
                let ad = ang - behind;
                while (ad > Math.PI) ad -= Math.PI * 2;
                while (ad < -Math.PI) ad += Math.PI * 2;
                const behindOk = Math.abs(ad) < 0.85;
                if (dist <= dead && behindOk) {
                    this.resetRoute?.();
                    return null; // stand still behind player
                }

                // Always prefer orbit so we never cut through the player
                const goal = this.followOrbitWaypoint(pos, spot, ownerPos, clearR);
                try {
                    const obstacles = ExtraPathfinder.obstacles(this, pos, goal);
                    const blocked = obstacles.some(item => ExtraPathfinder.intersects(pos, goal, item));
                    if (!blocked) return this.directDestination(goal, Math.max(12, dead * 0.4));
                } catch (_) {}
                return this.navigate(goal, Math.max(12, dead * 0.4));
            } else if (mode === 'cursorFollow') {
                target = this.client.ownerClient.InputHandler.cursorPosition(true);
                return this.directDestination(target, this.cursorStop(target));
            } else if (mode === 'playerFollow') {
                const player = BotFollowPlayers.resolve(this.client);
                if (!player?.pos?.current) return this.navigate(null, 20);
                target = player.pos.current;
                this.stopRadius = safeNum(ExtraCommands.followDistance, 175);
            } else if (mode === 'surround') {
                const enemy = BotSurroundEnemy.resolve(this.client.ownerClient);
                if (!enemy) return this.navigate(null, 20);
                target = this.formation(enemy.pos.current, mode);
            } else if (['circle', 'circlespin', 'square', 'squarespin'].includes(mode)) target = this.formation(target, mode);
            else if (mode === 'randommill') target = this.wander();
            else if (mode === 'grinder') {
                const resourceTypes = {wood: 0, food: 1, stone: 2, gold: 3};
                const g = ExtraCommands.grinder || {};
                // Multi goals: {wood:2000, stone:2000, food:500, gold:0} — 0/missing = skip
                // Legacy: single target + threshold
                let goals = g.goals && typeof g.goals === 'object' ? g.goals : null;
                if (!goals) {
                    const one = g.target || 'wood';
                    goals = {[one]: Math.max(0, safeNum(g.threshold, 500))};
                }
                // Priority: 1 food, 2 wood, 3 stone, 4 gold — finish higher priority first
                const needed = [];
                for (const key of ['food', 'wood', 'stone', 'gold']) {
                    const limit = safeNum(goals[key], -1);
                    if (limit <= 0) continue;
                    if ((me.resources[key] || 0) < limit) needed.push(key);
                }
                if (!needed.length) {
                    this.gatherObject = null;
                    this.stopRadius = safeNum(window.BOT_FOLLOW_RADIUS, 175);
                } else {
                    const focus = needed[0];
                    // Dynamic bots/resource + auto-switch if not gaining (crowd)
                    this.gatherObject = this.claimGatherResource(resourceTypes[focus]);
                    if (!this.gatherObject) target = this.wander();
                    else {
                        const stand = this.gatherStandPoint(this.gatherObject);
                        target = stand || this.gatherObject.pos.current;
                        const weapon = DataHandler_default.getWeapon(me.getItemByType(0));
                        // Stop near stand point; attack still uses range to the resource itself
                        this.stopRadius = Math.max(18, safeNum(me.scale, 35) * 0.55);
                    }
                }
            }
            if (['circle', 'surround'].includes(mode)) this.stopRadius = 8;
            return this.navigate(target, this.stopRadius);
        }
        avoidSpikes(target) {
            const me = this.client.myPlayer;
            const pos = me.pos.current;
            if (!target || pos.distance(target) <= this.stopRadius) return target;
            const angle = pos.angle(target);
            const near = [...this.objects()].filter(item => item instanceof PlayerObject && item.isSpike && !ExtraPathfinder.ownedSpike(this, item) && me.isEnemyByID(item.ownerID) && pos.distance(item.pos.current) < 240);
            const clear = direction => {
                for (const distance of [30, 65, 100]) {
                    const point = pos.addDirection(direction, distance);
                    if (near.some(item => point.distance(item.pos.current) < item.collisionScale + me.scale + 12)) return false;
                }
                return true;
            };
            if (clear(angle)) return target;
            for (const offset of [Math.PI / 4, -Math.PI / 4, Math.PI / 2, -Math.PI / 2, Math.PI]) {
                if (clear(angle + offset)) { this.stopRadius = 10; return pos.addDirection(angle + offset, 140); }
            }
            return null;
        }
        requestAttack(target, type, useTank = false) {
            const me = this.client.myPlayer, handler = this.client._ModuleHandler;
            const id = me.getItemByType(type);
            const ready = handler.staticModules.reloading.isReloaded(type);
            if (id === null || !ready && !useTank) return false;
            handler.moduleActive = true;
            handler.useAngle = me.pos.current.angle(target);
            handler.forceWeapon = type;
            if (useTank) {
                this.breakingAction = {tick:handler.tickCount, slot:type, angle:handler.useAngle};
                handler.forceHat = handler.forceHat === 6 || handler.shouldEquipSoldier || this.client.EnemyManager.dangerWithoutSoldier || !ready ? 6 : 40;
            }
            handler.shouldAttack = ready;
            return true;
        }
        updateBreakingHat() {
            const h = this.client._ModuleHandler, action = this.breakingAction;
            if (!action || action.tick !== h.tickCount || this.client.isOwner || h.syncExecuting || h.autoShootExecuting ||
                h.currentType !== null || h.forceWeapon !== action.slot || h.useAngle !== action.angle) return;
            h.forceHat = h.forceHat === 6 || h.shouldEquipSoldier || this.client.EnemyManager.dangerWithoutSoldier || !h.shouldAttack ? 6 : 40;
        }
        breakObject(onlySpikes) {
            const me = this.client.myPlayer;
            const type = me.getItemByType(1) === 10 ? 1 : 0;
            const weapon = DataHandler_default.getWeapon(me.getItemByType(type));
            if (!weapon || !DataHandler_default.isMelee(me.getItemByType(type))) return false;
            const target = this.nearest(item => item instanceof PlayerObject && item.isDestroyable && me.isEnemyByID(item.ownerID) && (!onlySpikes || item.isSpike) && me.pos.current.distance(item.pos.current) <= weapon.range + item.hitScale);
            return target ? this.requestAttack(target.pos.current, type, true) : false;
        }
        place(type, angle) {
            const me = this.client.myPlayer, handler = this.client._ModuleHandler;
            if (!me.canPlace(type) || !me.canPlaceObject(type, angle)) return false;
            handler.place(type, angle, true);
            handler.placedOnce = true;
            handler.placeAngles[0] = type;
            handler.placeAngles[1].push(angle);
            return true;
        }
        needsPlatform() {
            const me = this.client.myPlayer;
            const platforms = [...this.objects()].filter(item => item instanceof PlayerObject && item.type === 18 && item.health > 0);
            const placement = this.platformPlacement;
            if (placement) {
                for (const entry of placement.entries) {
                    if (entry.objectID !== null) continue;
                    const confirmed = platforms.find(item => item.pos.current.distance(entry.position) < 12);
                    if (confirmed) entry.objectID = confirmed.id;
                }
                // A sent placement is pending until the server confirms it. Time alone must not resend it.
                const pendingOrPresent = placement.entries.some(entry => entry.objectID === null || platforms.some(item => item.id === entry.objectID));
                if (me.pos.current.distance(placement.origin) >= Items[18].scale || !pendingOrPresent) this.platformPlacement = null;
            }
            // Include a small margin so movement jitter at the platform edge cannot restart placement.
            if (platforms.some(item => me.pos.current.distance(item.pos.current) <= item.scale + me.scale + 8)) return false;
            return this.platformPlacement === null;
        }
        placePlatform(angle, sync = false) {
            if (!sync && !this.needsPlatform()) return false;
            const me = this.client.myPlayer;
            const position = me.getPlacePosition(me.pos.current, 18, angle);
            if (!this.place(8, angle)) return false;
            if (!this.platformPlacement || me.pos.current.distance(this.platformPlacement.origin) >= Items[18].scale) {
                this.platformPlacement = {origin:me.pos.current.copy(), entries:[]};
            }
            const entries = this.platformPlacement.entries;
            if (!entries.some(entry => entry.position.distance(position) < 12)) entries.push({position, objectID:null});
            // Explicit Sync bursts can add four sides, but cannot grow the pending history indefinitely.
            if (entries.length > 8) entries.splice(0, entries.length - 8);
            return true;
        }
        postTick() {
            const me = this.client.myPlayer, handler = this.client._ModuleHandler;
            this.breakingAction = null;
            if (!me.inGame || this.client.isOwner) return;
            if (handler.syncExecuting || handler.autoShootExecuting) return;
            if (handler.staticModules.autoBreak.controlsAttack()) {
                this.breakingAction = {tick:handler.tickCount, slot:handler.forceWeapon, angle:handler.useAngle};
                this.updateBreakingHat();
                return;
            }
            this.animalTrap.postTick();
            if (ExtraCommands.mode === 'playerFollow') {
                const target = BotFollowPlayers.resolve(this.client);
                if (!Settings_default._manualAim && target?.pos?.current) handler._currentAngle = target.angle;
            }
            if (this.effectiveMode() === 'randommill' && !handler.placedOnce && !handler.healedOnce) {
                this.placeMillGroup((handler.move_dir ?? handler._currentAngle) + Math.PI);
            }
            if (handler.moduleActive || handler.shouldAttack || handler.currentType !== null) return;
            if (this.breakPath()) return;
            if (ExtraCommands.breakAllMode?.active && this.breakObject(false)) {
                // Attack routed through the existing Colean reload and packet pipeline.
            } else if (ExtraCommands.breakMode?.active && this.breakObject(true)) {
                // Nearby hostile spikes can be removed when routing alone is insufficient.
            } else if (this.gatherObject) {
                const weapon = DataHandler_default.getWeapon(me.getItemByType(0));
                if (weapon && me.pos.current.distance(this.gatherObject.pos.current) <= weapon.range + this.gatherObject.hitScale) this.requestAttack(this.gatherObject.pos.current, 0);
            }
        }
        cycle(type, enabled, mode, now) {
            if (!enabled) { this.cycleItem[type] = null; return; }
            const handler = this.client._ModuleHandler;
            if (now >= this.cycleAt[type]) {
                const store = DataHandler_default.getStore(type);
                const ids = Object.keys(store).map(Number).filter(id => {
                    const item = store[id];
                    return item && (type !== 0 || mode !== 'free' || item.price === 0) &&
                        (type !== 1 || mode !== 'wings' || /wings/i.test(item.name)) &&
                        (item.price === 0 || handler.bought[type].has(id) || this.client.myPlayer.tempGold >= item.price);
                });
                if (ids.length) this.cycleItem[type] = ids[this.cycleIndex[type]++ % ids.length];
                this.cycleAt[type] = now + 400;
            }
            if (this.cycleItem[type] !== null) handler._equip(type, this.cycleItem[type], true);
        }
        glitch(text, alphabet, max) {
            if (!alphabet) return text.slice(0, max);
            const char = alphabet[Math.floor(Math.random() * alphabet.length)];
            return (text.slice(0, max - 1) + char).slice(0, max);
        }
        afterTick() {
            const me = this.client.myPlayer;
            if (!me.inGame || this.client.isOwner) return;
            const now = Date.now(), packet = this.client.PacketManager;
        }
    }

    // Shared connection lifecycle for local and cross-server bot lists.
    const ExtraBotConnections = {
        pending: null,
        spawning: null,
        requests: new Set,
        nextID: 0,
        get bots() { return client.clients; },
        listID: 'connected-bot-list',
        statusID: 'bot-status',
        statusMessage: '',
        lastDisconnect: '',
        openSocket: (server, batch) => {
            if (batch && (batch.mainSocket !== client.SocketManager.socket || batch.mainSocket?.readyState !== batch.mainSocket?.OPEN)) throw new Error('The main connection changed. Start spawning again on the new server.');
            return createSocket_default(null, batch ? {session:batch.verification, isCancelled:() => batch.cancelled,
                label:`Current Server · Bot ${batch.nextIndex}`} : null);
        },
        createClient: () => new PlayerClient_default(client),
        activeBatch() { return ExtraBotConnections.spawning || CrossServerBots.connections.spawning || CrossServerBots.batch; },
        isBusy() { return Boolean(this.activeBatch() || ExtraBotConnections.pending || CrossServerBots.connections.pending || BotVerification.pending || BotVerification.session); },
        spawningProgress(batch) {
            if (this.spawning !== batch || batch.cancelled) return;
            const connecting = [...this.requests].filter(request => request.socket).length;
            const message = `Verifying: ${BotVerification.requests.size} · Verified: ${batch.started} · Connecting: ${connecting} · Added: ${batch.added} · Failed: ${batch.failed}`;
            this.show(message);
            BotVerification.updateBatch(batch.verification, message);
        },
        stopSpawning(error = null) {
            const batch = this.spawning;
            if (!batch) return;
            if (batch.cancelled) {
                if (!error) { batch.closeRequested = true; batch.verification?.dismiss?.(); }
                return;
            }
            batch.cancelled = true;
            batch.error = error;
            for (const wake of [...batch.waiters]) wake();
            this.cancelPending();
            this.updateButtons();
        },
        async startSpawning(server = null) {
            if (this.isBusy()) return {ok:false, busy:true};
            const target = server ? {...server} : null;
            const batch = {cancelled:false, continuous:true, added:0, failed:0, started:0, nextIndex:0,
                mainSocket:client.SocketManager.socket, servers:target ? [target] : [], waiters:new Set, error:null};
            const attempts = new Set;
            const allAttempts = [];
            this.spawning = batch;
            this.updateButtons();
            try {
                if (!target && (!batch.mainSocket || batch.mainSocket.readyState !== batch.mainSocket.OPEN)) throw new Error('Connect the main player to a server first.');
                batch.verification = BotVerification.beginBatch(() => this.stopSpawning(), {stopLabel:'Stop Spawning'});
                batch.verification.view.target.textContent = target ? `${CrossServerBots.typeLabel(target.mode)} · ${target.name} · ${target.region}` : 'Current Server';
                const authorize = async () => {
                    while (!batch.cancelled) {
                        // Keep a continuous run bounded while verified sockets finish connecting.
                        while (!batch.cancelled && attempts.size >= Infinity /* server pool */) await Promise.race(attempts);
                        if (batch.cancelled) break;
                        batch.nextIndex++;
                        let started;
                        const ready = new Promise(resolve => { started = resolve; });
                        const done = this.add(target, batch, started).then(result => {
                            if (result.ok) {
                                batch.added++;
                            } else if (!batch.cancelled) {
                                batch.failed++;
                            }

                            this.spawningProgress(batch);
                            return result;
                        });

                        attempts.add(done);
                        allAttempts.push(done);

                        done.finally(() => attempts.delete(done));
                        this.spawningProgress(batch);
                        const result = await ready;
                        if (result.ok) batch.started++;
                        this.spawningProgress(batch);
                        if (batch.cancelled) break;
                        // Yield between approvals, including automatically completed widgets.
                        await new Promise(resolve => {
                            const wake = () => { clearTimeout(timer); batch.waiters.delete(wake); resolve(); };
                            const timer = setTimeout(wake, 0);
                            batch.waiters.add(wake);
                        });
                    }
                };
                await Promise.all(Array.from({length:batch.verification.concurrency}, authorize));
                await Promise.allSettled(allAttempts);
            } catch (error) {
                this.stopSpawning(error.message || 'Could not start spawning.');
                await Promise.allSettled(attempts);
            } finally {
                if (batch.error && !batch.closeRequested && batch.verification && BotVerification.session === batch.verification) {
                    BotVerification.updateBatch(batch.verification, `Verified: ${batch.started} · Added: ${batch.added} · Failed: ${batch.failed}`);
                    await BotVerification.showBatchError(batch.verification, batch.error);
                }
                BotVerification.endBatch(batch.verification);
                if (this.spawning === batch) this.spawning = null;
                this.show(`${batch.error ? 'Spawning stopped: ' + batch.error : 'Spawning stopped.'} Added: ${batch.added} · Failed: ${batch.failed}`);
            }
            return {ok:!batch.error, added:batch.added, failed:batch.failed};
        },
        renderStatus() {
            const status = UI_default.frame?.document?.getElementById(this.statusID);
            if (status) status.textContent = `${this.statusMessage ? this.statusMessage + ' · ' : ''}${this.lastDisconnect ? 'Last disconnect: ' + this.lastDisconnect + ' · ' : ''}Current bots: ${this.bots.size}`;
        },
        recordDisconnect(bot, event) {
            const code = Number.isInteger(event.code) ? event.code : 'unknown';
            const reason = typeof event.reason === 'string' ? event.reason.trim().slice(0, 160) : '';
            const summary = bot.SocketManager.connectionSummary?.() || '';
            this.lastDisconnect = `${bot.botName || bot.myPlayer.nickname || 'Bot'} (code ${code}${reason ? ': ' + reason : '; no reason provided'}${summary ? '; ' + summary : ''})`;
        },
        render() {
            this.renderStatus();
            const doc = UI_default.frame?.document;
            const list = doc?.getElementById(this.listID);
            if (!list) return;
            list.replaceChildren();
            for (const bot of this.bots) {
                const row = doc.createElement('div');
                row.style.cssText = 'display:flex;align-items:center;justify-content:space-between;gap:16px;padding:5px 0;width:100%';
                const name = doc.createElement('span');
                name.style.cssText = 'font-size:20px;font-weight:bold;overflow-wrap:anywhere';
                name.textContent = `[${bot.id}]: ${bot.botName || bot.myPlayer.nickname || 'Connecting…'}`;
                if (bot.crossServer) name.textContent += ` · ${bot.crossServer.mode === 'sandbox' ? 'Sandbox' : 'Normal'} · ${bot.crossServer.name} · ${bot.crossServer.region}`;
                const remove = doc.createElement('button');
                remove.type = 'button';
                remove.textContent = '×';
                remove.title = 'Remove bot';
                remove.setAttribute('aria-label', `Remove ${bot.botName || bot.myPlayer.nickname || 'bot'}`);
                remove.style.cssText = 'border:0;background:transparent;color:#3d8fd4;font-size:32px;font-weight:bold;line-height:1;cursor:pointer;padding:0 8px';
                remove.onclick = () => this.remove(bot);
                row.append(name, remove);
                list.appendChild(row);
            }
        },
        remove(bot) {
            bot.disconnectRequested = true;
            bot._ModuleHandler.staticModules.aibmExtra.reset();
            clearTimeout(bot.SocketManager.pingTimeout);
            bot.disconnect();
            this.forget(bot);
            this.show('Bot removed.');
        },
        forget(bot) {
            this.bots.delete(bot);
            if (!bot.crossServer) {
                client.clientIDList.delete(bot.myPlayer.id);
                client.pendingJoins.delete(bot.myPlayer.id);
            }
            this.render();
        },
        updateButtons() {
            const doc = UI_default.frame?.document;
            const busy = this.isBusy();
            const add = doc?.getElementById('add-bot');
            if (add) add.disabled = busy;
            const addAll = doc?.getElementById('cross-add-all');
            if (addAll) addAll.disabled = busy;
            const refresh = doc?.getElementById('cross-refresh');
            if (refresh) refresh.disabled = Boolean(busy || CrossServerBots.loading);
            for (const id of ['cross-server-type-trigger', 'cross-server-type-option']) {
                const selector = doc?.getElementById(id);
                if (selector) selector.disabled = busy;
            }
            const stop = doc?.getElementById('cross-stop-adding');
            if (stop) { const batch = CrossServerBots.connections.spawning || CrossServerBots.batch; stop.disabled = !batch || batch.cancelled; }
            for (const button of doc?.querySelectorAll('.cross-add-bot') || []) {
                button.disabled = busy || button.dataset.full === 'true';
            }
        },
        show(message) {
            this.statusMessage = message;
            this.render();
            this.updateButtons();
        },
        async add(server = null, batch = null, onStarted = () => {}) {
            const activeBatch = this.activeBatch();
            if (batch && (batch !== activeBatch || batch.cancelled || batch !== this.spawning && (this !== CrossServerBots.connections || batch !== CrossServerBots.batch))) {
                const result = {ok:false, cancelled:true}; onStarted(result); return result;
            }
            if (activeBatch && activeBatch !== batch || !batch && this.isBusy()) {
                const result = {ok:false, busy:true}; onStarted(result); return result;
            }
            const request = {cancelled: false, socket: null, player: null};
            let started = false;
            this.requests.add(request);
            this.pending = request;
            this.show('Waiting for verification...');
            try {
                const socket = request.socket = await this.openSocket(server, batch);
                if (request.cancelled) { socket.close(); return {ok:false, cancelled:true}; }
                if (batch && this.pending === request) this.pending = [...this.requests].find(other => other !== request && !other.socket && !other.cancelled) || null;
                started = true;
                onStarted({ok:true});
                this.show('Connecting bot...');
                await new Promise((resolve, reject) => {
                    let settled = false;
                    const finish = error => {
                        if (settled) return;
                        settled = true;
                        clearTimeout(timer);
                        if (error) reject(error); else resolve();
                    };
                    const timer = setTimeout(() => finish(new Error('No server response within 15 seconds.')), 15000);
                    request.cancel = () => finish(new Error('Bot connection cancelled.'));
                    socket.addEventListener('error', () => finish(new Error('Bot connection failed.')), {once:true});
                    socket.addEventListener('close', event => {
                        const player = request.player;
                        if (player) {
                            if (this.bots.has(player) && !player.disconnectRequested && !request.cancelled) this.recordDisconnect(player, event);
                            player._ModuleHandler.staticModules.aibmExtra.reset();
                            clearTimeout(player.SocketManager.pingTimeout);
                            this.forget(player);
                        }
                        finish(new Error('Bot connection closed.'));
                        if (!this.pending) this.show('Bot disconnected.');
                    }, {once:true});
                    socket.addEventListener('connected', () => {
                        if (settled || request.cancelled || !request.player) return;
                        request.player.id = this.nextID++;
                        this.bots.add(request.player);
                        this.render();
                        finish();
                    }, {once:true});
                    const initialize = () => {
                        if (settled || request.cancelled) return;
                        try {
                            request.player = this.createClient(server);
                            request.player.SocketManager.init(socket);
                        } catch (_) { finish(new Error('Could not initialize the bot.')); }
                    };
                    if (socket.readyState === socket.OPEN) initialize();
                    else if (socket.readyState === socket.CONNECTING) socket.addEventListener('open', initialize, {once:true});
                    else finish(new Error('Could not start the bot connection.'));
                });
                if (!request.cancelled) request.message = 'Bot added.';
            } catch (error) {
                if (!request.cancelled) request.message = error.message || 'Could not add the bot.';
                if (/verification|cloudflare/i.test(request.message || '')) request.verificationFailed = true;
                if (request.socket && request.socket.readyState < 2) request.socket.close();
            } finally {
                if (this.pending === request) this.pending = [...this.requests].find(other => other !== request && !other.socket && !other.cancelled) || null;
                this.requests.delete(request);
                if (!started) onStarted({ok:false, cancelled:request.cancelled, verificationFailed:request.verificationFailed});
                this.show(request.cancelled ? 'Bot connection cancelled.' : request.message || '');
            }
            return {ok:this.bots.has(request.player), cancelled:request.cancelled, verificationFailed:request.verificationFailed, error:request.message};
        },
        cancelPending() {
            const requests = new Set(this.requests);
            if (this.pending) requests.add(this.pending);
            for (const request of requests) {
                if (request.player && this.bots.has(request.player)) continue;
                request.cancelled = true;
                if (request.socket && request.socket.readyState < 2) request.socket.close();
                if (request === this.pending && !request.socket) BotVerification.cancel?.();
                request.cancel?.();
            }
        },
        removeAll() {
            this.stopSpawning();
            if (this === CrossServerBots.connections && CrossServerBots.batch) CrossServerBots.stopAdding();
            this.cancelPending();
            for (const bot of [...this.bots]) this.remove(bot);
            this.show(this.pending ? 'Bots removed; cancelling pending connection...' : 'All bots removed.');
        }
    };
    
    const CrossServerBots = {
        servers: [],
        loading: null,
        loadedAt: 0,
        selectedMenu: 'bots',
        serverType: location.hostname === 'sandbox.moomoo.io' ? 'sandbox' : 'normal',
        loadVersion: 0,
        batch: null,
        loadAbort: null,
        connections: (() => {
            const manager = Object.create(ExtraBotConnections);
            Object.defineProperty(manager, 'bots', {value:new Set});
            Object.assign(manager, {
                pending:null, spawning:null, requests:new Set, nextID:0, listID:'cross-connected-bots', statusID:'cross-server-status', statusMessage:'', lastDisconnect:'',
                openSocket: (server, batch) => CrossServerBots.openSocket(server, batch),
                createClient: server => {
                    const bot = new PlayerClient_default(client);
                    bot.crossServer = {...server};
                    return bot;
                }
            });
            return manager;
        })(),
        endpoint(type = this.serverType) {
            const prefix = type === 'sandbox' ? 'api-sandbox' : 'api';
            return `https://${prefix}.moomoo.io/servers?v=1.27`;
        },
        normalize(data, type = this.serverType) {
            if (!Array.isArray(data)) throw new Error('The server list response was not recognized.');
            const result = new Map;
            for (const item of data) {
                if (!item || typeof item.key !== 'string' || typeof item.region !== 'string' || typeof item.name !== 'string') continue;
                if (!/^[a-z0-9](?:[a-z0-9-]*[a-z0-9])?$/i.test(item.key) || !/^[a-z][a-z0-9-]*$/i.test(item.region)) continue;
                if (!Number.isFinite(item.playerCount) || item.playerCount < 0 || !Number.isFinite(item.playerCapacity) || item.playerCapacity <= 0) continue;
                const id = `${item.region}:${item.name}`;
                result.set(id, {id, mode:type, name:item.name, region:item.region, key:item.key,
                    count:item.playerCount, capacity:item.playerCapacity, address:`wss://${item.key}.${item.region}.moomoo.io`});
            }
            if (data.length && !result.size) throw new Error('No supported servers were returned.');
            return [...result.values()].sort((a, b) => a.region.localeCompare(b.region) || b.count - a.count || a.name.localeCompare(b.name));
        },
        async loadDirectory(type, controller) {
            const timeout = setTimeout(() => controller.abort(), 10000);
            try {
                const response = await fetch(this.endpoint(type), {signal:controller.signal, credentials:'omit', cache:'no-store'});
                if (!response.ok) throw new Error(`Could not load servers (HTTP ${response.status}).`);
                const servers = this.normalize(await response.json(), type);
                ServerCapacity.remember(servers, type);
                return servers;
            } finally {
                clearTimeout(timeout);
            }
        },
        async refresh(force = false) {
            if (this.connections.activeBatch()) return false;
            if (this.loading) return this.loading;
            if (!force && this.loadedAt && Date.now() - this.loadedAt < 15000) { this.renderServers(); return true; }
            const type = this.serverType, version = ++this.loadVersion;
            const doc = UI_default.frame?.document, status = doc?.getElementById('cross-server-list-status');
            if (status) status.textContent = 'Loading servers...';
            const refresh = doc?.getElementById('cross-refresh');
            if (refresh) refresh.disabled = true;
            this.loading = (async () => {
                const controller = new AbortController;
                this.loadAbort = controller;
                try {
                    const servers = await this.loadDirectory(type, controller);
                    if (version !== this.loadVersion) return false;
                    this.servers = servers;
                    this.loadedAt = Date.now();
                    this.renderServers();
                    if (status) status.textContent = this.servers.length ? '' : 'No servers are available.';
                    return true;
                } catch (error) {
                    if (status && version === this.loadVersion) status.textContent = error.name === 'AbortError' ? (this.batch?.cancelled ? 'Server loading cancelled.' : 'Loading servers timed out. Use Refresh Servers to try again.') : 'Could not load servers. Use Refresh Servers to try again.';
                    return false;
                } finally {
                    if (version === this.loadVersion) {
                        this.loading = null;
                        this.loadAbort = null;
                        this.connections.updateButtons();
                    }
                }
            })();
            return this.loading;
        },
        typeLabel(type = this.serverType) { return type === 'sandbox' ? 'Sandbox Servers' : 'Normal Servers'; },
        renderType() {
            const doc = UI_default.frame?.document, root = doc?.getElementById('cross-server-type-switcher');
            if (!root) return;
            root.dataset.serverType = this.serverType;
            doc.getElementById('cross-server-type-label').textContent = this.typeLabel();
            const other = this.serverType === 'sandbox' ? 'normal' : 'sandbox';
            const option = doc.getElementById('cross-server-type-option');
            option.textContent = this.typeLabel(other); option.dataset.serverType = other;
            doc.getElementById('cross-server-type-options').hidden = true;
            doc.getElementById('cross-server-type-arrow').textContent = '▼';
            doc.getElementById('cross-server-type-trigger').setAttribute('aria-expanded', 'false');
            this.connections.updateButtons();
        },
        async selectType(type) {
            if (!['normal', 'sandbox'].includes(type) || this.connections.isBusy()) return false;
            if (type === this.serverType) return this.refresh();
            // A slow response from the previous directory must never replace the newly selected list.
            this.loadVersion++;
            this.loadAbort?.abort(); this.loading = this.loadAbort = null;
            this.serverType = type; this.servers = []; this.loadedAt = 0;
            this.batchStatus(''); this.renderType(); this.renderServers();
            return this.refresh(true);
        },
        attachType(ui) {
            const doc = ui.frame.document, root = doc.getElementById('cross-server-type-switcher');
            const trigger = doc.getElementById('cross-server-type-trigger'), options = doc.getElementById('cross-server-type-options');
            const arrow = doc.getElementById('cross-server-type-arrow');
            const close = () => { options.hidden = true; arrow.textContent = '▼'; trigger.setAttribute('aria-expanded', 'false'); };
            trigger.onclick = event => {
                event.stopPropagation(); const opening = options.hidden;
                options.hidden = !opening; arrow.textContent = opening ? '▲' : '▼';
                trigger.setAttribute('aria-expanded', String(opening));
            };
            doc.getElementById('cross-server-type-option').onclick = event => this.selectType(event.currentTarget.dataset.serverType);
            doc.addEventListener('click', event => { if (!root.contains(event.target)) close(); });
            root.addEventListener('keydown', event => { if (event.key === 'Escape') { close(); trigger.focus(); event.preventDefault(); } });
            this.renderType();
        },
        batchStatus(message) {
            const status = UI_default.frame?.document.getElementById('cross-batch-status');
            if (status) status.textContent = message;
        },
        batchProgress(batch) {
            if (this.batch !== batch || batch.cancelled) return;
            const connecting = [...this.connections.requests].filter(request => request.socket).length;
            const message = `Verifying: ${BotVerification.requests.size} · Verified: ${batch.started}/${batch.total} · Connecting: ${connecting} · Added: ${batch.added} · Failed: ${batch.failed}`;
            this.batchStatus(message);
            BotVerification.updateBatch(batch.verification, message);
        },
        stopAdding() {
            if (!this.batch) return;
            this.batch.cancelled = true;
            this.batch.loadAbort?.abort();
            this.loadAbort?.abort();
            this.connections.cancelPending();
            this.batchStatus('Stopping... Connected bots will stay in place.');
            this.connections.updateButtons();
        },
        async addAll() {
            if (this.connections.isBusy()) return;
            const batch = {cancelled:false, added:0, failed:0, skipped:0, started:0, total:0, servers:[], loadAbort:new AbortController};
            const connections = [];
            this.batch = batch;
            // Batch discovery owns a separate snapshot containing both server types.
            this.loadVersion++;
            this.loadAbort?.abort(); this.loading = this.loadAbort = null;
            this.connections.updateButtons();
            const status = UI_default.frame?.document.getElementById('cross-server-list-status');
            if (status) status.textContent = '';
            try {
                for (const type of ['normal', 'sandbox']) {
                    this.batchStatus(`Refreshing ${this.typeLabel(type)}...`);
                    try {
                        const servers = await this.loadDirectory(type, batch.loadAbort);
                        if (batch.cancelled) return;
                        batch.servers.push(...servers);
                    } catch (_) {
                        if (!batch.cancelled) this.batchStatus(`Could not start: ${this.typeLabel(type)} could not be refreshed.`);
                        return;
                    }
                }
                this.servers = batch.servers.filter(server => server.mode === this.serverType);
                this.loadedAt = Date.now();
                this.renderServers();
                if (status) status.textContent = this.servers.length ? '' : 'No servers are available.';
                const servers = batch.servers.filter(server => server.count < server.capacity);
                batch.skipped = batch.servers.length - servers.length;
                if (!servers.length) { this.batchStatus('No available servers.'); return; }
                batch.total = servers.length;
                batch.verification = BotVerification.beginBatch(() => this.stopAdding());
                let index = 0;
                const authorize = async () => {
                    while (index < servers.length && !batch.cancelled) {
                        const server = servers[index++];
                        batch.nextIndex = index;
                        let started;
                        const ready = new Promise(resolve => { started = resolve; });
                        const done = this.connections.add(server, batch, started).then(result => {
                            if (result.ok) batch.added++;
                            else if (!batch.cancelled) batch.failed++;
                            this.batchProgress(batch);
                            return result;
                        });
                        connections.push(done);
                        this.batchProgress(batch);
                        const result = await ready;
                        if (result.ok) batch.started++;
                        if (result.cancelled || result.verificationFailed || result.busy) {
                            this.stopAdding();
                            break;
                        }
                    }
                };
                await Promise.all(Array.from({length:batch.verification.concurrency}, authorize));
                this.batchProgress(batch);
                BotVerification.waitForConnections(batch.verification);
                await Promise.all(connections);
                if (!batch.cancelled) this.batchStatus(`Done. Added: ${batch.added} · Failed: ${batch.failed} · Full: ${batch.skipped}`);
            } finally {
                BotVerification.endBatch(batch.verification);
                if (batch.cancelled) this.batchStatus(`Stopped. Added: ${batch.added} · Failed: ${batch.failed}`);
                if (this.batch === batch) this.batch = null;
                this.connections.updateButtons();
            }
        },
        async openSocket(server, batch = null) {
            if (batch && (batch !== this.batch && batch !== this.connections.spawning || batch.cancelled)) throw new Error('Bot connection cancelled.');
            const servers = batch ? batch.servers : this.servers.filter(item => item.mode === this.serverType);
            const selected = servers.find(item => item.id === server?.id && item.mode === server?.mode);
            if (!selected) throw new Error('Refresh the server list and select a server again.');
            if (selected.count >= selected.capacity) throw new Error('This server is full. Refresh the list or choose another server.');
            const verification = batch ? {session:batch.verification, isCancelled:() => batch.cancelled,
                label:`${this.typeLabel(selected.mode)} · ${selected.name} · ${selected.region} ${batch.continuous ? '· Bot ' + batch.nextIndex : '(' + batch.nextIndex + '/' + batch.total + ')'}`} : null;
            return createSocket_default(selected.address, verification);
        },
        renderServers() {
            const doc = UI_default.frame?.document, list = doc?.getElementById('cross-server-list');
            if (!list) return;
            list.replaceChildren();
            const current = client.SocketManager.socket;
            let currentAddress = '';
            try { currentAddress = new URL(current.url).origin; } catch (_) {}
            for (const server of this.servers) {
                const row = doc.createElement('div');
                row.className = 'cross-server-row';
                row.dataset.server = server.id;
                row.classList.toggle('current-server', currentAddress === server.address);
                const name = doc.createElement('span'); name.className = 'cross-server-name'; name.textContent = server.name;
                const detail = doc.createElement('span'); detail.className = 'cross-server-detail';
                detail.textContent = `${server.count}/${server.capacity} players · ${server.region}`;
                const add = doc.createElement('button'); add.type = 'button'; add.className = 'option-button cross-add-bot';
                add.textContent = 'Add Bot'; add.dataset.full = String(server.count >= server.capacity);
                add.setAttribute('aria-label', `Add bot to ${server.name}, ${server.region}`);
                add.title = server.count >= server.capacity ? 'Server is full' : `Add an idle bot to ${server.name}`;
                add.onclick = () => this.connections.startSpawning(server);
                row.append(name, detail, add); list.appendChild(row);
            }
            this.connections.updateButtons();
        },
        attach(ui) {
            const doc = ui.frame.document, root = doc.getElementById('bot-family-switcher');
            if (!root || root.dataset.attached) return;
            root.dataset.attached = 'true';
            const trigger = doc.getElementById('bot-family-trigger'), option = doc.getElementById('bot-family-option');
            const options = doc.getElementById('bot-family-options'), arrow = doc.getElementById('bot-family-arrow');
            const close = () => { options.hidden = true; arrow.textContent = '▼'; trigger.setAttribute('aria-expanded', 'false'); };
            const apply = () => {
                const cross = this.selectedMenu === 'cross';
                doc.getElementById('bot-family-label').textContent = cross ? 'Cross-Server Menu' : 'Bot Menu';
                option.textContent = cross ? 'Bot Menu' : 'Cross-Server Menu';
                doc.getElementById('local-bot-panel').hidden = cross;
                doc.getElementById('cross-server-panel').hidden = !cross;
                root.dataset.currentMenu = this.selectedMenu;
                if (cross) this.refresh();
                close();
            };
            trigger.onclick = event => {
                event.stopPropagation(); const opening = options.hidden;
                options.hidden = !opening; arrow.textContent = opening ? '▲' : '▼';
                trigger.setAttribute('aria-expanded', String(opening));
            };
            option.onclick = () => { this.selectedMenu = this.selectedMenu === 'cross' ? 'bots' : 'cross'; apply(); };
            doc.addEventListener('click', event => { if (!root.contains(event.target)) close(); });
            root.addEventListener('keydown', event => { if (event.key === 'Escape') { close(); trigger.focus(); event.preventDefault(); } });
            doc.getElementById('cross-refresh').onclick = () => this.refresh(true);
            doc.getElementById('cross-add-all').onclick = () => this.addAll();
            doc.getElementById('cross-stop-adding').onclick = () => this.connections.spawning ? this.connections.stopSpawning() : this.stopAdding();
            doc.getElementById('cross-remove-bots').onclick = () => this.connections.removeAll();
            this.attachType(ui);
            this.renderServers(); ExtraBotConnections.render(); this.connections.render(); apply();
        }
    };

    const CombatControl = {
        participants(owner) { return [owner, ...owner.clients]; },
        selected(client2) {
            const requested = client2.ownerClient._ModuleHandler.manualWeapon;
            return requested === 1 && client2.myPlayer.getItemByType(1) !== null ? 1 : 0;
        },
        select(owner, type) {
            if (type !== 0 && type !== 1) return false;
            if (owner.myPlayer.getItemByType(type) === null) return false;
            owner._ModuleHandler.manualWeapon = type;
            for (const current of this.participants(owner)) {
                if (current.myPlayer.inGame && !current._ModuleHandler.moduleActive && !current.InputHandler.instaToggle) current._ModuleHandler.whichWeapon(this.selected(current));
            }
            return true;
        },
        toggle(enabled) {
            Settings_default._manualAim = Boolean(enabled);
            if (enabled) {
                client._ModuleHandler.manualWeapon = client._ModuleHandler.weapon === 1 ? 1 : 0;

            }
            if (!enabled) {
                for (const current of this.participants(client)) {
                    const handler = current._ModuleHandler;
                    handler.useWeapon = handler.forceWeapon = handler.useAngle = null;
                    handler.shouldAttack = false;
                    if (current.myPlayer.inGame) { handler.stopAttack(); handler.whichWeapon(0); }
                }
            }
            SaveSettings();
        },
        cursor(client2) { return client2.ownerClient.InputHandler.cursorPosition(true); },
        aimAngle(client2) {
            const input = client2.ownerClient.InputHandler;
            return input.rotation ? client2.myPlayer.pos.current.angle(this.cursor(client2)) : (input.lockedAimAngle ?? input.mouse.angle);
        },
        beginTick(client2) {
            const handler = client2._ModuleHandler;
            handler.syncExecuting = false;
            handler.autoShootExecuting = false;
            handler.autoattackClaim = false;
            // Keep a completed click until the next server tick consumes it.
            if (handler.pendingPointerAttack) handler.attackingState = handler.pendingPointerAttack;
            if (!Settings_default._manualAim) return;
            client2._ModuleHandler._currentAngle = this.aimAngle(client2);
        },
        useAttack(client2) {
            const handler = client2._ModuleHandler;
            if (handler.moduleActive || handler.shouldAttack || handler.attackingState !== 1 || handler.forceWeapon !== null) return;
            if (!handler.staticModules.reloading.isReloaded(this.selected(client2))) return;
            handler.forceWeapon = this.selected(client2);
            handler.useAngle = this.aimAngle(client2);
            handler._currentAngle = handler.useAngle;
            handler.shouldAttack = true;
            handler.autoattackClaim = handler.autoattack && !handler.pointerAttack && !handler.pendingPointerAttack;
        },
        restore(client2) {
            if (!Settings_default._manualAim) return;
            const handler = client2._ModuleHandler;
            if (handler.moduleActive || handler.shouldAttack || handler.forceWeapon !== null || client2.InputHandler.instaToggle) return;
            const selected = handler.useWeapon !== null ? handler.useWeapon : this.selected(client2);
            if (handler.weapon !== selected) handler.whichWeapon(selected);
        },
        selectFromPointer(event, client2) {
            if (!Settings_default._manualAim || !client2.isOwner || event.button !== 0) return false;
            const button = event.target?.closest?.('[id^="actionBarItem"]');
            if (!button || !/^actionBarItem\d+$/.test(button.id)) return false;
            const id = Number(button.id.slice('actionBarItem'.length));
            const type = [0, 1].find(slot => client2.myPlayer.getItemByType(slot) === id);
            if (type === undefined) return false;
            event.preventDefault();
            event.stopImmediatePropagation();
            return this.select(client2, type);
        },
        platform(current, angle, sync = false) {
            const player = current.myPlayer;
            if (sync ? !Settings_default._manualAim : Settings_default._manualAim) return false;
            if (!ExtraCommands.apEnabled || !player.inGame || player.getItemByType(8) !== 18) return false;
            const extra = current._ModuleHandler.staticModules.aibmExtra;
            for (const offset of [0, Math.PI / 2, -Math.PI / 2, Math.PI]) {
                if (extra.placePlatform(angle + offset, sync)) return true;
            }
            return false;
        },
        autoAim(current) {
            // Reuse the native left-click solver, including predicted aim and weapon range.
            return current._ModuleHandler.staticModules.useAttacking.getWeaponType(true);
        },
        applySync(current) {
            const h = current._ModuleHandler;
            if (h.syncExecuting) return;
            if (!current.myPlayer.inGame || current.SocketManager.socket?.readyState !== 1) { h.pendingSync = null; return; }
            if (h.pendingSync && Date.now() > h.pendingSync.expires) h.pendingSync = null;
            const request = h.pendingSync;
            if (!request) return;
            const shot = this.autoAim(current);
            if (!shot) return;
            const [type, angle] = shot;
            if (!h.staticModules.reloading.isReloaded(type)) return;
            const placementAngle = angle ?? h._currentAngle;
            this.platform(current, placementAngle, true);
            h.pendingSync = null;
            h.syncExecuting = true;
            h.forceWeapon = type;
            h.useItem = null;
            h.useAngle = angle;
            h.shouldAttack = true;
            h.moduleActive = true;
        },
        syncHit() {
            let queued = 0, connected = 0;
            for (const current of this.participants(client)) {
                if (!current.myPlayer.inGame || current.SocketManager.socket?.readyState !== 1) continue;
                connected++;
                if (!this.autoAim(current)) continue;
                current._ModuleHandler.pendingSync = {expires:Date.now() + 2500};
                queued++;
            }
            return {queued, reason:queued ? `Sync Hit queued: ${queued}.` : connected ? 'No target in sight.' : 'No connected players ready.'};
        }
    };
    const BotAutoShoot = {
        viewCache: new WeakMap(),
        range() {
            const value = Number(Settings_default._botAutoShootRange);
            return Number.isFinite(value) ? Math.max(100, Math.min(1400, value)) : 1400;
        },
        observationAge(entity, now) {
            const seenAt = entity?.client?.PlayerManager?.lastSnapshotAt;
            return Number.isFinite(seenAt) ? Math.max(0, now - seenAt) : 0;
        },
        velocity(entity) {
            const previous = entity?.pos?.previous, current = entity?.pos?.current;
            if (!previous || !current) return {x:0, y:0};
            const measured = Number(entity.client?.PlayerManager?.step);
            const step = Number.isFinite(measured) && measured >= 40 && measured <= 300 ? measured : 1e3 / 9;
            let x = (current.x - previous.x) / step, y = (current.y - previous.y) / step;
            const speed = Math.hypot(x, y);
            if (!Number.isFinite(speed) || speed < .005 || speed > .9) return {x:0, y:0};
            return {x, y};
        },
        advance(position, velocity, time) {
            return new Vector_default(position.x + velocity.x * time, position.y + velocity.y * time);
        },
        projectileClearance(weapon) {
            const scale = Number(DataHandler_default.getProjectile(weapon)?.scale);
            return Number.isFinite(scale) ? Math.max(16, Math.min(22, scale * .125)) : 16;
        },
        aimPoint(current, enemy, weapon, now = performance.now()) {
            const projectile = DataHandler_default.getProjectile(weapon);
            if (!projectile || !Number.isFinite(projectile.speed) || projectile.speed <= 0) return null;
            const latency = Math.max(0, Math.min(180, safeNum(current.SocketManager?.pong, 0) / 2));
            const targetVelocity = this.velocity(enemy), shooterVelocity = this.velocity(current.myPlayer);
            const targetAge = this.observationAge(enemy, now), shooterAge = this.observationAge(current.myPlayer, now);
            if (targetAge > 500 && Math.hypot(targetVelocity.x, targetVelocity.y) > .02) return null;
            const origin = this.advance(current.myPlayer.pos.current, shooterVelocity, Math.min(400, shooterAge + latency));
            const targetDelay = Math.min(500, targetAge + latency);
            let point = this.advance(enemy.pos.current, targetVelocity, targetDelay);
            for (let i = 0; i < 5; i++) {
                const flight = Math.max(0, origin.distance(point) - 70) / projectile.speed;
                point = this.advance(enemy.pos.current, targetVelocity, targetDelay + flight);
            }
            return {origin, point};
        },
        shieldBlocks(enemy, origin, point = enemy.pos.current) {
            if (enemy.weapon.current !== 11) return false;
            if (!Number.isFinite(enemy.angle)) return true;
            return getAngleDist(point.angle(origin), enemy.angle) <= Config_default.shieldAngle;
        },
        freshView(source, now = performance.now()) {
            return source && !source.crossServer && !source.disconnectRequested && source.myPlayer.inGame &&
                source.SocketManager.socket?.readyState === 1 && Number.isFinite(source.PlayerManager?.lastSnapshotAt) &&
                now - source.PlayerManager.lastSnapshotAt <= 1000;
        },
        ownerView(current) {
            const owner = current.ownerClient;
            return owner !== current && this.freshView(owner) ? owner : null;
        },
        snapshot(current, now = performance.now()) {
            const owner = current.ownerClient || current;
            const cached = this.viewCache.get(owner);
            if (cached && now - cached.builtAt < 50) return cached;
            const sources = [...new Set([owner, ...(owner.clients || [])])].filter(source =>
                source?.ownerClient === owner && this.freshView(source, now));
            sources.sort((a, b) => b.PlayerManager.lastSnapshotAt - a.PlayerManager.lastSnapshotAt);
            const players = [], playerIDs = new Set(), objects = [], objectIDs = new Set();
            for (const source of sources) {
                for (const player of source.PlayerManager.players) {
                    if (!(player instanceof Player_default) || playerIDs.has(player.id)) continue;
                    playerIDs.add(player.id);
                    players.push(player);
                }
                for (const [id, object] of source.ObjectManager.objects) {
                    if (objectIDs.has(id)) continue;
                    objectIDs.add(id);
                    objects.push(object);
                }
            }
            const snapshot = {builtAt:performance.now(), sources, players, objects};
            this.viewCache.set(owner, snapshot);
            return snapshot;
        },
        sharedViews(current) {
            return this.snapshot(current).sources.filter(source => source !== current);
        },
        *visibleTargets(current, snapshot = this.snapshot(current)) {
            const seen = new Set();
            for (const players of [current.PlayerManager.players, current.PlayerManager.enemies]) {
                for (const player of players) {
                    if (!(player instanceof Player_default) || seen.has(player.id)) continue;
                    seen.add(player.id);
                    yield player;
                }
            }
            for (const player of snapshot.players) {
                if (seen.has(player.id)) continue;
                seen.add(player.id);
                yield player;
            }
        },
        knownObjects(current, snapshot, range, clearance = 4) {
            const objects = [], seen = new Set(), origin = current.myPlayer.pos.current;
            const add = (id, object) => {
                if (seen.has(id)) return;
                seen.add(id);
                const radius = object.collisionScale + clearance;
                if (Math.abs(object.pos.current.x - origin.x) > range + radius ||
                    Math.abs(object.pos.current.y - origin.y) > range + radius) return;
                objects.push(object);
            };
            for (const [id, object] of current.ObjectManager.objects) add(id, object);
            for (const object of snapshot.objects) {
                add(object.id, object);
            }
            return objects;
        },
        clearLine(current, start, end, elevated = current.myPlayer.onPlatform, objects = current.ObjectManager.objects.values(), clearance = 4) {
            const dx = end.x - start.x, dy = end.y - start.y;
            const lengthSquared = dx * dx + dy * dy;
            if (!lengthSquared) return false;
            for (const object of objects) {
                if (object instanceof PlayerObject && (object.health <= 0 || Items[object.type].ignoreCollision)) continue;
                // Elevated shots pass over layer-zero walls/spikes, but not taller obstacles.
                if (object.layer < (elevated ? 1 : 0)) continue;
                const position = object.pos.current;
                const radius = object.collisionScale + clearance;
                // Segment bounds discard distant objects without a collision calculation.
                if (position.x + radius < Math.min(start.x, end.x) || position.x - radius > Math.max(start.x, end.x) ||
                    position.y + radius < Math.min(start.y, end.y) || position.y - radius > Math.max(start.y, end.y)) continue;
                const t = Math.max(0, Math.min(1, ((position.x - start.x) * dx + (position.y - start.y) * dy) / lengthSquared));
                const x = position.x - start.x - t * dx, y = position.y - start.y - t * dy;
                if (x * x + y * y <= radius * radius) return false;
            }
            return true;
        },
        platformPlan(current, angle) {
            const me = current.myPlayer, extra = current._ModuleHandler.staticModules.aibmExtra;
            // A pending or nearby platform still needs the server's onPlatform acknowledgement.
            if (!extra.needsPlatform()) return {angle:null};
            if (me.getItemByType(8) !== 18 || !me.canPlace(8)) return null;
            for (const offset of [0, Math.PI / 2, -Math.PI / 2, Math.PI]) {
                if (me.canPlaceObject(8, angle + offset)) return {angle:angle + offset};
            }
            return null;
        },
        target(current, weapon) {
            const me = current.myPlayer;
            const range = Math.min(this.range(), DataHandler_default.getProjectile(weapon).range);
            const clearance = this.projectileClearance(weapon);
            const snapshot = this.snapshot(current);
            let best = null, distance = Infinity, objects = null;
            for (const enemy of this.visibleTargets(current, snapshot)) {
                if (!(enemy instanceof Player_default) || enemy.currentHealth <= 0 || !me.isEnemyByID(enemy.id) ||
                    enemy.id === current.ownerClient.myPlayer.id || current.ownerClient.isBotByID(enemy.id) ||
                    current.ownerClient.myPlayer.isTeammateByID(enemy.id) ||
                    (me.clanName !== null && me.clanName === enemy.clanName) ||
                    (current.ownerClient.myPlayer.clanName !== null && current.ownerClient.myPlayer.clanName === enemy.clanName)) continue;
                const aim = this.aimPoint(current, enemy, weapon);
                if (!aim) continue;
                if (this.shieldBlocks(enemy, aim.origin, aim.point)) continue;
                const next = aim.origin.distance(aim.point);
                if (next > range || next >= distance) continue;
                if (!objects) objects = this.knownObjects(current, snapshot, range, clearance);
                const needsPlatform = !this.clearLine(current, aim.origin, aim.point, me.onPlatform, objects, clearance);
                let platform = null;
                if (needsPlatform) {
                    if (!Settings_default._botAutoShootPlatform || !this.clearLine(current, aim.origin, aim.point, true, objects, clearance)) continue;
                    platform = this.platformPlan(current, aim.origin.angle(aim.point));
                    if (!platform) continue;
                }
                best = {enemy, aim, needsPlatform, platform}; distance = next;
            }
            return best;
        },
        apply(current) {
            const me = current.myPlayer, h = current._ModuleHandler;
            const inputAttack = (h.attackingState === 1 || h.attackingState === 2) &&
                Boolean(h.autoattack || h.pointerAttack || h.pendingPointerAttack);
            if (!Settings_default._botAutoShoot || current.isOwner || current.crossServer || !me.inGame ||
                current.SocketManager.socket?.readyState !== 1 || h.syncExecuting || h.moduleActive ||
                (h.shouldAttack || h.forceWeapon !== null || h.attackingState) && !inputAttack || h.healedOnce || h.placedOnce ||
                h.useItem !== null || current.InputHandler.instaToggle || h.staticModules.autoBreak.controlsAttack()) return;
            const weapon = me.getItemByType(1);
            if (!DataHandler_default.isShootable(weapon)) return;
            const target = this.target(current, weapon);
            if (!target) return;
            const {aim, needsPlatform, platform} = target;
            if (inputAttack) {
                h.shouldAttack = false;
                h.forceWeapon = null;
                h.useAngle = null;
                h.autoattackClaim = false;
            }
            // Keep the ranged weapon selected while it reloads; attack through the native packet pipeline.
            h.forceWeapon = 1;
            h.useAngle = aim.origin.angle(aim.point);
            const ready = h.staticModules.reloading.isReloaded(1);
            h.shouldAttack = ready && !needsPlatform;
            h.moduleActive = true;
            h.autoShootExecuting = true;
            h.activeModule = 'botAutoShoot';
            // Unequip Monkey Tail (and any acc) — dmgMultO would gut bow/musket damage
            h.useAcc = 0;
            if (h.shouldAttack && h.forceHat === null && !h.shouldEquipSoldier) h.useHat = 20;
            if (ready && Settings_default._botAutoShootPlatform && !me.onPlatform && me.getItemByType(8) === 18) {
                const extra = h.staticModules.aibmExtra;
                if (needsPlatform) {
                    if (platform.angle !== null) extra.placePlatform(platform.angle);
                } else if (extra.needsPlatform()) {
                    for (const offset of [0, Math.PI / 2, -Math.PI / 2, Math.PI]) {
                        if (extra.placePlatform(h.useAngle + offset)) break;
                    }
                }
            }
        }
    };
    const BotLoadout = {
        primary: [8, 3, 6, 5, 7, 1],
        secondary: [13, 15, 11, 10],
        fixedItems: {2:1, 4:7, 8:18},
        setting(slot) { return slot === 0 ? '_botPrimary' : '_botSecondary'; },
        choice(slot) {
            if (slot !== 0 && slot !== 1) return null;
            const value = Settings_default[this.setting(slot)];
            const options = slot === 0 ? this.primary : this.secondary;
            return options.includes(value) ? value : null;
        },
        root(id) {
            let weapon = DataHandler_default.getWeapon(id);
            while (weapon?.upgradeOf !== undefined) weapon = DataHandler_default.getWeapon(weapon.upgradeOf);
            return weapon?.id;
        },
        spinning(client2) {
            const player = client2.myPlayer;
            return player.getItemByType(1) === 10 && [8, 3, 4, 5].includes(player.getItemByType(0));
        },
        allows(client2, id) {
            if (client2.isOwner) return true;
            if (id >= 16) {
                const item = Items[id - 16];
                if (item?.itemType === 4 && this.spinning(client2)) return item.id === 7 || item.id === 9;
                return item && (!(item.itemType in this.fixedItems) || item.id === this.fixedItems[item.itemType]);
            }
            const slot = DataHandler_default.getWeapon(id)?.itemType;
            const choice = this.choice(slot);
            return choice === null || (slot === 1 && [13, 15].includes(choice) ? [9, 12, choice].includes(id) : this.root(id) === choice);
        },
        pick(client2, available, age) {
            if (age === 8 && this.spinning(client2) && [8, 5].includes(client2.myPlayer.getItemByType(0)) && available.includes(28)) return 28;
            if (age === 9 && this.spinning(client2) && available.includes(25)) return 25;
            const fixed = ({3:17, 5:23, 7:34})[age];
            if (fixed !== undefined && available.includes(fixed)) return fixed;
            const secondary = this.choice(1);
            const rangedStep = [13, 15].includes(secondary) ? ({6:9, 8:12, 9:secondary})[age] : undefined;
            if (rangedStep !== undefined && available.includes(rangedStep)) return rangedStep;
            const preferred = age === 2 ? this.choice(0) : age === 6 ? this.choice(1) : null;
            if (preferred !== null && available.includes(preferred)) return preferred;
            const valid = available.filter(id => {
                if (!this.allows(client2, id)) return false;
                if (id < 16) return true;
                const item = Items[id - 16];
                if (item?.itemType === 4 && this.spinning(client2)) return item.id === 7 || item.id === 9;
                return item && (item.upgradeOf === undefined || client2.myPlayer.inventory[item.itemType] === item.upgradeOf);
            });
            const ownerOrder = client2.ownerClient.myPlayer.upgradeOrder;
            // Continue the chosen weapon branch even when the owner chose another loadout.
            const weaponUpgrades = valid.filter(id => id < 16 && DataHandler_default.getWeapon(id).upgradeOf !== undefined);
            if (weaponUpgrades.length) return ownerOrder.find(id => weaponUpgrades.includes(id)) ?? weaponUpgrades[0];
            const shared = ownerOrder.find(id => valid.includes(id));
            if (shared !== undefined) return shared;
            // A configured bot must not wait forever for an owner upgrade it cannot copy.
            if (age !== 2 && age !== 6 || [0, 1].some(slot => this.choice(slot) !== null)) return valid[0] ?? null;
            return null;
        },
        applyPending(bot) {
            if (bot.crossServer) return;
            const player = bot.myPlayer;
            if (!player.inGame || !player.pendingLoadoutUpgrade) return;
            const {ids, age} = player.pendingLoadoutUpgrade;
            if (age !== player.upgradeAge) return;
            const selected = this.pick(bot, ids, age);
            if (selected !== null) {
                player.pendingLoadoutUpgrade = null;
                bot._ModuleHandler._upgradeItem(selected);
            }
        },
        attach(ui) {
            const doc = ui.frame.document;
            const manual = doc.getElementById('_manualAim');
            if (manual) {
                manual.checked = Settings_default._manualAim;
                manual.onchange = () => CombatControl.toggle(manual.checked);
            }
            for (const radio of doc.querySelectorAll('input[name="bot-primary"], input[name="bot-secondary"]')) {
                const slot = radio.name === 'bot-primary' ? 0 : 1;
                radio.checked = this.choice(slot) === Number(radio.value);
                radio.onchange = () => {
                    if (!radio.checked) return;
                    Settings_default[this.setting(slot)] = Number(radio.value);
                    SaveSettings();
                    for (const bot of client.clients) this.applyPending(bot);
                };
            }
        }
    };

    class ModuleHandler {
        client;
        staticModules={};
        botModules;
        modules;
        store=[ {
            utility: new Map,
            lastUtility: null,
            current: 0,
            best: 0,
            actual: -1,
            last: 0
        }, {
            utility: new Map,
            lastUtility: null,
            current: 0,
            best: 0,
            actual: -1,
            last: 0
        } ];
        bought=[ new Set, new Set ];
        followTarget=new Vector_default(0, 0);
        lookTarget=new Vector_default(0, 0);
        endTarget=new Vector_default(0, 0);
        followPath=false;
        tickCount=0;
        currentHolding=0;
        weapon;
        currentType;
        attacking;
        attackingState;
        sentAngle;
        sentHatEquip;
        sentAccEquip;
        needToHeal;
        didAntiInsta;
        placedOnce;
        healedOnce;
        totalPlaces;
        attacked;
        canHitEntity=false;
        moduleActive=false;
        useAngle=null;
        useWeapon=null;
        useItem=null;
        forceWeapon=null;
        useHat=null;
        forceHat=null;
        shouldEquipSoldier=false;
        useAcc=null;
        previousWeapon=null;
        _currentAngle=0;
        move_dir=null;
        reverse_move_dir=null;
        moveTo="disable";
        prevMoveTo="disable";
        pointerAttack=0;
        pendingPointerAttack=0;
        autoattackClaim=false;
        autoattack=false;
        shouldAttack=false;
        mouse={
            sentAngle: 0
        };
        placeAngles=[ null, [] ];
        norecoil=false;
        manualWeapon=0;
        moduleStart=performance.now();
        maxExecutionTime=0;
        constructor(client2) {
            this.client = client2;
            this.staticModules = {
                tempData: new TempData_default(client2),
                movement: new Movement_default(client2),
                aibmExtra: new ColeanExtraBot(client2),
                clanJoiner: new ClanJoiner_default(client2),
                autoAccept: new AutoAccept_default(client2),
                autoBuy: new AutoBuy(client2),
                defaultHat: new DefaultHat(client2),
                reloading: new Reloading_default(client2),
                defaultAcc: new DefaultAcc(client2),
                autoSync: new AutoSync(client2),
                shameSpam: new ShameSpam(client2),
                spikeSyncHammer: new SpikeSyncHammer(client2),
                spikeSync: new SpikeSync(client2),
                spikeTick: new SpikeTick_default(client2),
                knockbackTickTrap: new KnockbackTickTrap(client2),
                knockbackTick: new KnockbackTick(client2),
                knockbackTickHammer: new KnockbackTickHammer(client2),
                kbTickHammerV2: new KBTickHammerV2(client2),
                antiRetrap: new AntiRetrap(client2),
                autoPush: new AutoPush(client2),
                velocityTick: new VelocityTick(client2),
                spikeTrap: new SpikeTrap(client2),
                teammateSpikeTrap: new TeammateSpikeTrap(client2),
                turretSync: new TurretSync(client2),
                toolHammerSpearInsta: new ToolHammerSpearInsta(client2),
                swordKatanaInsta: new SwordKatanaInsta(client2),
                bowInsta: new BowInsta(client2),
                instakill: new Instakill(client2),
                reverseInstakill: new ReverseInstakill(client2),
                autoBreak: new Autobreak(client2),
                autoSteal: new AutoSteal(client2),
                turretSteal: new TurretSteal(client2),
                spikeGearInsta: new SpikeGearInsta(client2),
                useFastest: new UseFastest(client2),
                useDestroying: new UseDestroying(client2),
                useAttacking: new UseAttacking(client2),
                utilityHat: new UtilityHat(client2),
                antiInsta: new AntiInsta_default(client2),
                shameReset: new ShameReset_default(client2),
                trapKB: new TrapKB(client2),
                autoShield: new AutoShield(client2),
                placementDefense: new PlacementDefense(client2),
                dashMovement: new DashMovement(client2),
                autoPlacer: new AutoPlacer_default(client2),
                placer: new Placer_default(client2),
                autoMill: new Automill_default(client2),
                autoGrind: new AutoGrind(client2),
                preAttack: new PreAttack_default(client2),
                autoHat: new Autohat_default(client2),
                updateAttack: new UpdateAttack_default(client2),
                updateAngle: new UpdateAngle_default(client2),
                killChat: new KillChat(client2),
                safeWalk: new SafeWalk(client2)
            };
            this.botModules = [ this.staticModules.tempData, this.staticModules.clanJoiner, this.staticModules.movement ];
            this.modules = [ this.staticModules.autoAccept, this.staticModules.autoBuy, this.staticModules.defaultHat, this.staticModules.reloading, this.staticModules.defaultAcc, this.staticModules.autoSync, this.staticModules.shameSpam, this.staticModules.spikeSyncHammer, this.staticModules.spikeSync, this.staticModules.spikeTick, this.staticModules.knockbackTickTrap, this.staticModules.knockbackTickHammer, this.staticModules.kbTickHammerV2, this.staticModules.knockbackTick, this.staticModules.antiRetrap, this.staticModules.autoPush, this.staticModules.velocityTick, this.staticModules.spikeTrap, this.staticModules.teammateSpikeTrap, this.staticModules.turretSync, this.staticModules.toolHammerSpearInsta, this.staticModules.swordKatanaInsta, this.staticModules.bowInsta, this.staticModules.instakill, this.staticModules.reverseInstakill, this.staticModules.autoBreak, this.staticModules.autoSteal, this.staticModules.turretSteal, this.staticModules.spikeGearInsta, this.staticModules.useFastest, this.staticModules.useDestroying, this.staticModules.useAttacking, this.staticModules.utilityHat, this.staticModules.antiInsta, this.staticModules.shameReset, this.staticModules.trapKB, this.staticModules.autoShield, this.staticModules.placementDefense, this.staticModules.autoPlacer, this.staticModules.dashMovement, this.staticModules.placer, this.staticModules.autoMill, this.staticModules.autoGrind, this.staticModules.preAttack, this.staticModules.autoHat, this.staticModules.updateAttack, this.staticModules.updateAngle, this.staticModules.killChat, this.staticModules.safeWalk ];
            this.reset();
        }
        movementReset() {
            this.currentHolding = 0;
            this.weapon = 0;
            this.currentType = null;
            this.attacking = 0;
            this.attackingState = 0;
            this.pointerAttack = 0;
            this.pendingPointerAttack = 0;
            this.autoattackClaim = false;
            this.move_dir = null;
            this.reverse_move_dir = null;
        }
        reset() {
            const {isOwner: isOwner, clients: clients} = this.client;
            this.movementReset();
            this.staticModules.aibmExtra.reset();
            this.getHatStore().utility.clear();
            this.getAccStore().utility.clear();
            this.sentAngle = 0;
            this.sentHatEquip = false;
            this.sentAccEquip = false;
            this.needToHeal = false;
            this.didAntiInsta = false;
            this.placedOnce = false;
            this.healedOnce = false;
            this.totalPlaces = 0;
            this.attacked = false;
            this.canHitEntity = false;
            this.autoattack = false;
            for (const module of this.modules) {
                if ("reset" in module) {
                    module.reset();
                }
            }
            if (isOwner) {
                for (const client2 of clients) {
                    client2._ModuleHandler.movementReset();
                    client2._ModuleHandler.toggleAutoattack(false);
                }
            }
        }
        get holdingWeapon() {
            return this.currentHolding <= 1;
        }
        get isMoving() {
            return this.move_dir !== null;
        }
        setForceHat(hat) {
            if (this.forceHat !== null && hat !== null) {
                return;
            }
            this.forceHat = hat;
        }
        getHatStore() {
            return this.store[0];
        }
        getAccStore() {
            return this.store[1];
        }
        setFollowTarget(x, y) {
            this.followTarget._setXY(x, y);
        }
        setLookTarget(x, y) {
            this.lookTarget._setXY(x, y);
        }
        updateSentAngle(priority) {
            if (this.sentAngle >= priority) {
                return;
            }
            this.sentAngle = priority;
        }
        _upgradeItem(id, isItem = false) {
            if (isItem) {
                id += 16;
            }
            if (!BotLoadout.allows(this.client, id)) return;
            this.client.PacketManager.upgradeItem(id);
            this.client.myPlayer.upgradeItem(id);
            if (DataHandler_default.isWeapon(id)) {
                const type = DataHandler_default.getWeapon(id).itemType;
                const {reloading: reloading} = this.staticModules;
                reloading.updateMaxReload(type);
            }
        }
        startMovement(angle = this.move_dir, ignore = false) {
            if (!ignore) {
                this.move_dir = angle;
                this.reverse_move_dir = angle === null ? null : reverseAngle(angle);
                if (this.moveTo !== "disable") {
                    return;
                }
            }
            const {myPlayer: myPlayer} = this.client;
            if (myPlayer.simulation.collisionSimulation(this.client)) {
                return false;
            }
            this.client.PacketManager.move(angle);
            return true;
        }
        stopMovement() {
            this.client.PacketManager.resetMoveDir();
        }
        startPlacement(type) {
            this.currentType = type;
        }
        canBuy(type, id) {
            if (id === -1) {
                return false;
            }
            const store2 = DataHandler_default.getStore(type);
            const price = store2[id].price;
            const bought = this.bought[type];
            return bought.has(id) || this.client.myPlayer.tempGold >= price && this.client.myPlayer.isSandbox;
        }
        _buy(type, id, force = false) {
            const store2 = DataHandler_default.getStore(type);
            const {isOwner: isOwner, clients: clients, myPlayer: myPlayer, PacketManager: PacketManager2} = this.client;
            if (!myPlayer.inGame) {
                return false;
            }
            if (force) {
                if (isOwner) {
                    for (const client2 of clients) {
                        client2._ModuleHandler._buy(type, id, force);
                    }
                }
            }
            const price = store2[id].price;
            const bought = this.bought[type];
            if (price === 0) {
                bought.add(id);
                return true;
            }
            if (!bought.has(id) && myPlayer.tempGold >= price && (myPlayer.isSandbox || force)) {
                PacketManager2.buy(type, id);
                myPlayer.tempGold -= price;
                return false;
            }
            return bought.has(id);
        }
        hasStoreItem(type, id) {
            const store2 = this.bought[type];
            return store2.has(id);
        }
        _equip(type, id, force = false, toggle = false) {
            const extra = this.staticModules.aibmExtra;
            // HatLoop / AccLoop removed — no cycle lock on equip
            const store2 = this.store[type];
            const {myPlayer: myPlayer, PacketManager: PacketManager2, EnemyManager: EnemyManager2, isOwner: isOwner, clients: clients} = this.client;
            if (toggle && store2.last === id && id !== 0) {
                id = 0;
            }
            if (!myPlayer.inGame || !this._buy(type, id, force)) {
                return false;
            }
            if (store2.last === id && myPlayer.storeData[type] === id) {
                return false;
            }
            store2.last = id;
            PacketManager2.equip(type, id);
            if (type === 0) {
                this.sentHatEquip = true;
            } else {
                this.sentAccEquip = true;
            }
            if (force) {
                store2.actual = id;
                if (isOwner) {
                    for (const client2 of clients) {
                        client2._ModuleHandler.staticModules.tempData.setStore(type, id);
                    }
                }
            }
            const nearest = EnemyManager2.nearestTurretEntity;
            const reloading = this.staticModules.reloading;
            if (nearest !== null && reloading.isReloaded(2) && type === 0 && id === 53) {
                reloading.resetByType(2);
            }
            return true;
        }
        updateAngle(angle, force = false) {
            if (!force && angle === this.mouse.sentAngle) {
                return;
            }
            this.mouse.sentAngle = angle;
            this.updateSentAngle(3);
            this.client.PacketManager.updateAngle(angle);
        }
        selectItem(type) {
            const {myPlayer: myPlayer} = this.client;
            const item = myPlayer.getItemByType(type);
            if (myPlayer.currentItem !== -1) {
                myPlayer.currentItem = -1;
                this.whichWeapon();
            }
            const sent = this.client.PacketManager.selectItemByID(item, false);
            this.currentHolding = type;
            return sent;
        }
        attack(angle, priority = 2) {
            if (angle !== null) {
                this.mouse.sentAngle = angle;
            }
            this.updateSentAngle(priority);
            const sent = this.client.PacketManager.attack(angle);
            if (this.holdingWeapon) {
                this.attacked = true;
            }
            return sent;
        }
        stopAttack() {
            this.client.PacketManager.stopAttack();
        }
        toggleAutoattack(state = !this.autoattack) {
            this.autoattack = state;
            if (this.client.isOwner && Settings_default._botSync) {
                for (const bot of this.client.clients) bot._ModuleHandler.toggleAutoattack(state);
            }
            this.attacking = this.pointerAttack || (state ? 1 : 0);
            this.attackingState = this.pendingPointerAttack || this.attacking;
        }
        whichWeapon(type = this.weapon) {
            const weapon = this.client.myPlayer.getItemByType(type);
            if (weapon === null) {
                return;
            }
            this.currentHolding = type;
            this.weapon = type;
            this.client.PacketManager.selectItemByID(weapon, true);
        }
        place(type, angle = this._currentAngle, reset = false, restoreWeapon = true) {
            this.totalPlaces += 1;
            // Timed preplacements also publish between regular module ticks.
            if (this.client.isOwner) GameUI_default.updatePlaces(this.totalPlaces);
            this.selectItem(type);
            this.attack(angle, 1);
            if (reset) {
                this.stopAttack();
            }
            if (restoreWeapon) this.whichWeapon();
        }
        heal() {
            const healing = this.staticModules.antiInsta;
            if (!healing.enhanced) {
                healing.reset();
                this.selectItem(2);
                this.attack(null, 1);
                this.whichWeapon();
                return true;
            }
            const plan = healing.planHeal();
            if (!plan) return false;
            try {
                if (this.selectItem(2) === false || this.attack(null, 1) === false) {
                    healing.retryAfter = performance.now() + 125;
                    return false;
                }
                healing.recordHeal(plan);
                return true;
            } catch (_) {
                healing.retryAfter = performance.now() + 125;
                return false;
            } finally {
                try { this.whichWeapon(); } catch (_) {}
            }
        }
        circleOffset=0;
        targetSpeed=65;
        activeModule=null;
        postTick() {
            if (this.client.crossServer) return;
            if (Settings_default._circleRotation && this.move_dir === null) {
                const rotationSpeed = this.targetSpeed / Settings_default._circleRadius;
                this.circleOffset = (this.circleOffset + rotationSpeed) % (Math.PI * 2);
            }
            const {isOwner: isOwner} = this.client;
            this.placeAngles[0] = null;
            this.placeAngles[1].length = 0;
            this.activeModule = null;
            this.tickCount += 1;
            this.sentAngle = 0;
            this.sentHatEquip = false;
            this.sentAccEquip = false;
            this.didAntiInsta = false;
            this.placedOnce = false;
            this.healedOnce = false;
            this.totalPlaces = 0;
            this.attacked = false;
            this.canHitEntity = false;
            this.moduleActive = false;
            this.useWeapon = null;
            this.useItem = null;
            this.forceWeapon = null;
            this.useHat = null;
            this.forceHat = null;
            this.shouldEquipSoldier = false;
            this.useAcc = null;
            this.useAngle = null;
            this.shouldAttack = false;
            CombatControl.beginTick(this.client);
            this.prevMoveTo = this.moveTo;
            this.moveTo = "disable";
            if (!isOwner) {
                for (const botModule of this.botModules) {
                    botModule.postTick();
                }
            }
            for (const module of this.modules) {
                if (module === this.staticModules.preAttack) {
                    CombatControl.applySync(this.client);
                    BotAutoShoot.apply(this.client);
                    if (!isOwner) this.staticModules.aibmExtra.postTick();
                }
                const prevg = this.moduleActive;
                if (!isOwner && module === this.staticModules.autoHat) this.staticModules.aibmExtra.updateBreakingHat();
                if (module === this.staticModules.updateAttack) {
                    this.staticModules.velocityTick.beforeAttack();
                    ManualComboControl.beforeAttack(this.client);
                }
                this.executingModule = module.moduleName;
                try { module.postTick(); } finally { this.executingModule = null; }
                if (module === this.staticModules.updateAttack) {
                    this.staticModules.velocityTick.afterAttack();
                    ManualComboControl.afterAttack(this.client);
                }
                if (!prevg && this.moduleActive) {
                    this.activeModule = module.moduleName;
                }
            }
            if (!isOwner) this.staticModules.aibmExtra.afterTick();
            CombatControl.restore(this.client);
            this.pendingPointerAttack = 0;
            this.attackingState = this.attacking;
            if (isOwner) {
                this.client.InputHandler.postTick();
                GameUI_default.updateFastQ(this.didAntiInsta);
                GameUI_default.updatePlaces(this.totalPlaces);
                GameUI_default.updateActiveModule(this.activeModule + ", " + this.tickCount);
                GameUI_default.updateEquipHat(`${this.store[0].last},  ${this.shouldEquipSoldier}`);
                const executionTime = Math.round(performance.now() - this.moduleStart);
                this.maxExecutionTime = Math.max(this.maxExecutionTime, executionTime);
                GameUI_default.updateModulePerformance(`${executionTime}/${this.maxExecutionTime}`);
            }
        }
    }

    const ModuleHandler_default = ModuleHandler;

    class PlayerClient {
        id=-1;
        connectSuccess=false;
        clientID=null;
        ownerClient;
        SocketManager;
        ObjectManager;
        PlayerManager;
        ProjectileManager;
        LeaderboardManager;
        EnemyManager;
        _ModuleHandler;
        myPlayer;
        PacketManager;
        InputHandler;
        StatsManager;
        pendingJoins=new Set;
        clientIDList=new Set;
        clients=new Set;
        constructor(owner) {
            this.ownerClient = owner || this;
            this.SocketManager = new SocketManager_default(this);
            this.ObjectManager = new ObjectManager_default(this);
            this.PlayerManager = new PlayerManager_default(this);
            this.ProjectileManager = new ProjectileManager_default(this);
            this.LeaderboardManager = new LeaderboardManager_default(this);
            this.EnemyManager = new EnemyManager_default(this);
            this._ModuleHandler = new ModuleHandler_default(this);
            this.myPlayer = new ClientPlayer_default(this);
            this.PacketManager = new PacketManager(this);
            this.InputHandler = new InputHandler(this);
            this.StatsManager = new StatsManager(this);
        }
        getClientIndex(client2) {
            return [ ...this.clients ].indexOf(client2);
        }
        get isOwner() {
            return this.ownerClient === this;
        }
        isBotByID(id) {
            return this.clientIDList.has(id) || this.ownerClient !== this && this.ownerClient.clientIDList.has(id);
        }
        disconnect() {
            this.disconnectRequested = true;
            this.SocketManager.active = false;
            clearTimeout(this.SocketManager.pingTimeout);
            this.SocketManager.pingTimeout = null;
            const socket = this.SocketManager.socket;
            if (socket !== null) {
                socket.close();
            }
        }
        removeBots() {
            for (const client2 of this.clients) {
                client2.disconnect();
            }
        }
        spawn() {
            this.myPlayer.spawn();
        }
    }

    const PlayerClient_default = PlayerClient;

    const UI = new class {
        frame;
        activeHotkeyInput=null;
        activeInput=null;
        toggleTimeout;
        menuOpened=false;
        menuLoaded=false;
        menuScale=1;
        get isMenuOpened() {
            return this.menuOpened;
        }
        isActiveButton() {
            return this.activeHotkeyInput || this.activeInput;
        }
        getFrameContent() {
            const keybinds = Keybinds_default.replace(
                /(<div class="content-option">\s*<span class="option-title">Toggle Menu<\/span>[\s\S]*?<\/div>)/,
                `$&<div class="content-option">
                    <span class="option-title">Colean Bots Menu</span>
                    <button id="_toggleBotsMenu" class="hotkeyInput"></button>
                    <span class="option-description">Set the keyboard shortcut to open and close the Colean Bots Menu. Backspace clears it.</span>
                </div>`
            );
            return `\n            <!DOCTYPE html>\n            <style>${styles_default}</style><style>${PrivateVisualTheme.menuCSS}</style>\n            <div id="menu-container" class="transparent">\n                <div id="menu-wrapper">\n                    ${Header_default}\n\n                    <main>\n                        ${Navbar_default}\n                        \n                        <div id="page-container">\n                            ${Home_default}\n                            ${keybinds}\n                            ${Combat_default}\n                            ${Visuals_default}\n                            ${Misc_default}\n                            ${Devtool_default}\n                            ${Bots_default}\n                        </div>\n                    </main>\n                </div>\n            </div>\n        `;
        }
        injectStyles() {
            const style = document.createElement("style");
            style.innerHTML = Game_default + Store_default + PrivateVisualTheme.hudCSS;
            document.head.appendChild(style);
        }
        createFrame() {
            this.injectStyles();
            const iframe = document.createElement("iframe");
            const blob = new Blob([ this.getFrameContent() ], {
                type: "text/html; charset=utf-8"
            });
            iframe.src = URL.createObjectURL(blob);
            iframe.id = "iframe-container";
            iframe.style.display = "none";
            document.body.appendChild(iframe);
            return new Promise(resolve => {
                iframe.onload = () => {
                    const iframeWindow = iframe.contentWindow;
                    const iframeDocument = iframeWindow.document;
                    URL.revokeObjectURL(iframe.src);
                    resolve({
                        target: iframe,
                        window: iframeWindow,
                        document: iframeDocument
                    });
                };
            });
        }
        querySelector(selector) {
            return this.frame.document.querySelector(selector);
        }
        querySelectorAll(selector) {
            return this.frame.document.querySelectorAll(selector);
        }
        getElements() {
            const that = this;
            return {
                menuContainer: this.querySelector("#menu-container"),
                menuWrapper: this.querySelector("#menu-wrapper"),
                pageContainer: this.querySelector("#page-container"),
                hotkeyInputs: this.querySelectorAll(".hotkeyInput[id]"),
                checkboxes: this.querySelectorAll("input[type='checkbox'][id]"),
                colorPickers: this.querySelectorAll("input[type='color'][id]"),
                textInputs: this.querySelectorAll("input[type='text'][id]"),
                sliders: this.querySelectorAll("input[type='range'][id]"),
                closeButton: this.querySelector("#close-button"),
                openMenuButtons: this.querySelectorAll(".open-menu[data-id]"),
                menuPages: this.querySelectorAll(".menu-page[data-id]"),
                buttons: this.querySelectorAll(".option-button[id]"),
                scriptDescription: this.querySelector("#script-description"),
                author: this.querySelector("#author"),
                optionDescriptions: this.querySelectorAll(".option-description"),
                resetSettings: this.querySelector("#resetSettings"),
            };
        }
        updateStats(id, value) {
            const stats = this.querySelector("#" + id);
            if (stats == null) {
                throw Error(`updateStats Error: can't find an element with ID: '${id}'`);
            }
            stats.textContent = value;
            if (id in Settings_default) {
                Settings_default[id] = value;
                SaveSettings();
            }
        }
        handleResize() {
            const {menuContainer: menuContainer} = this.getElements();
            const scale = Math.min(.9, Math.min(window.innerWidth / 1280, window.innerHeight / 720));
            this.menuScale = scale;
            menuContainer.style.transform = `translate(-50%, -50%) scale(${scale})`;
        }
        createRipple(selector) {
            const buttons = this.frame.document.querySelectorAll(selector);
            for (const button of buttons) {
                button.addEventListener("click", event => {
                    const {width: width, height: height} = button.getBoundingClientRect();
                    const size = Math.max(width, height) * 2;
                    const ripple = document.createElement("span");
                    ripple.style.width = size + "px";
                    ripple.style.height = size + "px";
                    ripple.style.marginTop = -size / 2 + "px";
                    ripple.style.marginLeft = -size / 2 + "px";
                    ripple.style.left = event.offsetX + "px";
                    ripple.style.top = event.offsetY + "px";
                    ripple.classList.add("ripple");
                    button.appendChild(ripple);
                    setTimeout(() => ripple.remove(), 750);
                });
            }
        }
        attachHotkeyInputs() {
            const {hotkeyInputs: hotkeyInputs} = this.getElements();
            for (const hotkeyInput of hotkeyInputs) {
                const id = hotkeyInput.id;
                const value = Settings_default[id];
                if (id in Settings_default && typeof value === "string") {
                    hotkeyInput.textContent = formatCode(value);
                } else {
                    Logger.error(`attachHotkeyInputs Error: Property "${id}" does not exist in settings`);
                }
            }
        }
        checkForRepeats() {
            const {hotkeyInputs: hotkeyInputs} = this.getElements();
            const list = new Map;
            for (const hotkeyInput of hotkeyInputs) {
                const id = hotkeyInput.id;
                if (id in Settings_default) {
                    const value = Settings_default[id];
                    const [count, inputs] = list.get(value) || [ 0, [] ];
                    list.set(value, [ (count || 0) + 1, [ ...inputs, hotkeyInput ] ]);
                    hotkeyInput.classList.remove("red");
                } else {
                    Logger.error(`checkForRepeats Error: Property "${id}" does not exist in settings`);
                }
            }
            for (const data of list) {
                const [number, hotkeyInputs2] = data[1];
                if (number === 1) {
                    continue;
                }
                for (const hotkeyInput of hotkeyInputs2) {
                    hotkeyInput.classList.add("red");
                }
            }
        }
        applyCode(code) {
            if (this.activeHotkeyInput === null) {
                return;
            }
            if (this.activeHotkeyInput.id === "_toggleBotsMenu" && typeof code !== "string") return;
            const deleting = code === "Backspace";
            const isCode = typeof code === "string";
            const keyText = isCode ? formatCode(code) : formatButton(code);
            const keySetting = isCode ? code : keyText;
            const id = this.activeHotkeyInput.id;
            if (id in Settings_default) {
                Settings_default[id] = deleting ? "..." : keySetting;
                SaveSettings();
            } else {
                Logger.error(`applyCode Error: Property "${id}" does not exist in settings`);
            }
            this.activeHotkeyInput.textContent = deleting ? "..." : keyText;
            this.activeHotkeyInput.blur();
            this.activeHotkeyInput.classList.remove("active");
            this.activeHotkeyInput = null;
            this.checkForRepeats();
        }
        isHotkeyInput(target) {
            return target instanceof this.frame.window.HTMLButtonElement && target.classList.contains("hotkeyInput") && target.hasAttribute("id");
        }
        handleCheckboxToggle(id, checked) {
            switch (id) {
              case "_menuTransparency":
                {
                    const {menuContainer: menuContainer} = this.getElements();
                    menuContainer.classList.toggle("transparent");
                    break;
                }

              case "_hideHUD":
                {
                    const {gameUI: gameUI} = GameUI_default.getElements();
                    if (checked) {
                        gameUI.classList.add("hidden");
                    } else {
                        gameUI.classList.remove("hidden");
                    }
                    break;
                }

              case "_chatLog":
                GameUI_default.toggleChatLog();
                break;
            }
        }
        attachCheckboxes() {
            const {checkboxes: checkboxes} = this.getElements();
            for (const checkbox of checkboxes) {
                const id = checkbox.id;
                if (!(id in Settings_default)) {
                    Logger.error(`attachCheckboxes Error: Property "${id}" does not exist in settings`);
                    continue;
                }
                checkbox.checked = Settings_default[id];
                this.handleCheckboxToggle(id, checkbox.checked);
                checkbox.onchange = () => {
                    if (id in Settings_default) {
                        Settings_default[id] = checkbox.checked;
                        SaveSettings();
                        this.handleCheckboxToggle(id, checkbox.checked);
                    } else {
                        Logger.error(`attachCheckboxes Error: Property "${id}" was deleted from settings`);
                    }
                };
            }
        }
        attachColorPickers() {
            const {colorPickers: colorPickers} = this.getElements();
            for (const picker of colorPickers) {
                const id = picker.id;
                if (!(id in Settings_default)) {
                    Logger.error(`attachColorPickers Error: Property "${id}" does not exist in settings`);
                    continue;
                }
                picker.value = Settings_default[id];
                picker.onchange = () => {
                    if (id in Settings_default) {
                        Settings_default[id] = picker.value;
                        SaveSettings();
                        picker.blur();
                    } else {
                        Logger.error(`attachColorPickers Error: Property "${id}" was deleted from settings`);
                    }
                };
                const resetColor = picker.previousElementSibling;
                if (resetColor instanceof this.frame.window.HTMLButtonElement) {
                    resetColor.style.setProperty("--data-color", defaultSettings[id]);
                    resetColor.onclick = () => {
                        if (id in Settings_default) {
                            picker.value = defaultSettings[id];
                            Settings_default[id] = defaultSettings[id];
                            SaveSettings();
                        } else {
                            Logger.error(`resetColor Error: Property "${id}" was deleted from settings`);
                        }
                    };
                }
            }
        }
        attachSliders() {
            const {sliders: sliders} = this.getElements();
            for (const slider of sliders) {
                const id = slider.id;
                if (!(id in Settings_default)) {
                    Logger.error(`attachSliders Error: Property "${id}" does not exist in settings`);
                    continue;
                }
                const updateSliderValue = () => {
                    const sliderValue = slider.previousElementSibling;
                    if (sliderValue instanceof this.frame.window.HTMLSpanElement) {
                        sliderValue.textContent = slider.value;
                    }
                };
                slider.value = Settings_default[id].toString();
                updateSliderValue();
                slider.oninput = () => {
                    if (id in Settings_default) {
                        Settings_default[id] = Number(slider.value);
                        SaveSettings();
                        updateSliderValue();
                    } else {
                        Logger.error(`attachSliders Error: Property "${id}" was deleted from settings`);
                    }
                };
                slider.onchange = () => slider.blur();
            }
        }
        attachTextInputs() {
            const {textInputs: textInputs} = this.getElements();
            for (const input of textInputs) {
                const id = input.id;
                if (!(id in Settings_default)) {
                    Logger.error(`attachTextInputs Error: Property "${id}" does not exist in settings`);
                    continue;
                }
                input.value = Settings_default[id];
                input.oninput = () => {
                    input.value = input.value.replace(/[^\x20-\x7E]/g, "");
                };
                input.onfocus = () => {
                    this.activeInput = input;
                };
                input.onblur = () => {
                    this.activeInput = null;
                };
                input.onchange = () => {
                    if (id in Settings_default) {
                        const value = input.value;
                        Settings_default[id] = value;
                        input.value = value;
                        SaveSettings();
                    } else {
                        Logger.error(`attachTextInputs Error: Property "${id}" was deleted from settings`);
                    }
                };
            }
        }
        attachDescriptions() {
            const {optionDescriptions: optionDescriptions, menuWrapper: menuWrapper} = this.getElements();
            for (const description of optionDescriptions) {
                const parent = description.parentElement;
                parent.onmouseenter = () => {
                    description.classList.add("description-show");
                };
                parent.onmouseleave = () => {
                    description.classList.remove("description-show");
                };
                parent.onmousemove = event => {
                    const target = event.target;
                    if (target !== null && target.className !== "content-option" && target.className !== "option-title") {
                        description.classList.remove("description-show");
                        return;
                    }
                    description.classList.add("description-show");
                    const bounds = menuWrapper.getBoundingClientRect();
                    const x = (event.clientX - bounds.left + 10) / this.menuScale;
                    const y = (event.clientY - bounds.top + 10) / this.menuScale;
                    description.style.left = x + "px";
                    description.style.top = y + "px";
                };
            }
        }
        handleResetSettings(button) {
            button.onclick = () => {
                resetSettings();
            };
        }
        attachButtons() {
            BotLoadout.attach(this);
            CrossServerBots.attach(this);
            const {buttons: buttons} = this.getElements();
            for (const button of buttons) {
                switch (button.id) {
                  case "add-bot":
                    button.onclick = () => ExtraBotConnections.startSpawning();
                    break;
                  case "remove-bots":
                    button.onclick = () => ExtraBotConnections.removeAll();
                    break;

                  case "resetSettings":
                    this.handleResetSettings(button);
                    break;
                }
            }
        }
        closeMenu() {
            const {menuWrapper: menuWrapper} = this.getElements();
            menuWrapper.classList.remove("toopen");
            menuWrapper.classList.add("toclose");
            this.menuOpened = false;
            clearTimeout(this.toggleTimeout);
            this.toggleTimeout = setTimeout(() => {
                menuWrapper.classList.remove("toclose");
                this.frame.target.style.display = "none";
            }, 150);
        }
        openMenu() {
            const {menuWrapper: menuWrapper} = this.getElements();
            this.frame.target.removeAttribute("style");
            menuWrapper.classList.remove("toclose");
            menuWrapper.classList.add("toopen");
            this.menuOpened = true;
            clearTimeout(this.toggleTimeout);
            this.toggleTimeout = setTimeout(() => {
                menuWrapper.classList.remove("toopen");
            }, 150);
        }
        toggleMenu() {
            if (!this.menuLoaded) {
                return;
            }
            if (this.menuOpened) {
                this.closeMenu();
            } else {
                this.openMenu();
            }
        }
        attachOpenMenu() {
            const {openMenuButtons: openMenuButtons, menuPages: menuPages} = this.getElements();
            for (let i = 0; i < openMenuButtons.length; i++) {
                const button = openMenuButtons[i];
                const id = button.getAttribute("data-id");
                const menuPage = this.querySelector(`.menu-page[data-id='${id}']`);
                button.onclick = () => {
                    if (menuPage instanceof this.frame.window.HTMLDivElement) {
                        removeClass(openMenuButtons, "active");
                        button.classList.add("active");
                        removeClass(menuPages, "opened");
                        menuPage.classList.add("opened");
                    } else {
                        Logger.error(`attachOpenMenu Error: Cannot find "${button.textContent}" menu`);
                    }
                };
            }
        }
        attachListeners() {
            const {closeButton: closeButton, scriptDescription: scriptDescription, author: author} = this.getElements();
            closeButton.onclick = () => {
                this.closeMenu();
            };
            const preventDefaults = target => {
                target.addEventListener("contextmenu", event => event.preventDefault());
                target.addEventListener("mousedown", event => {
                    if (event.button === 1) {
                        event.preventDefault();
                    }
                });
                target.addEventListener("mouseup", event => {
                    if (event.button === 3 || event.button === 4) {
                        event.preventDefault();
                    }
                });
            };
            preventDefaults(window);
            preventDefaults(this.frame.window);
            const description = "v" + Colean.version + " by " + Colean.author;
            scriptDescription.textContent = description;
            
            this.handleResize();
            window.addEventListener("resize", () => this.handleResize());
            this.frame.document.addEventListener("mouseup", event => {
                if (this.activeHotkeyInput) {
                    this.applyCode(event.button);
                } else if (this.isHotkeyInput(event.target) && event.button === 0) {
                    event.target.textContent = "Wait...";
                    this.activeHotkeyInput = event.target;
                    event.target.classList.add("active");
                }
            });
            this.frame.document.addEventListener("keyup", event => {
                if (this.activeHotkeyInput && this.isHotkeyInput(event.target)) {
                    this.applyCode(event.code);
                }
            });
            this.frame.window.addEventListener("keydown", event => client.InputHandler.handleKeydown(event));
            this.frame.window.addEventListener("keyup", event => client.InputHandler.handleKeyup(event));
            this.openMenu();
            
        }
        resetFrame() {
            this.frame.target.remove();
            this.init();
        }
        async init() {
            try {
                this.frame = await this.createFrame();
                this.attachListeners();
                this.attachHotkeyInputs();
                this.checkForRepeats();
                this.attachCheckboxes();
                this.attachColorPickers();
                this.attachSliders();
                this.attachTextInputs();
                this.attachDescriptions();
                this.attachButtons();
                this.attachOpenMenu();
                this.createRipple(".open-menu");
                client.StatsManager.init();
                const {menuContainer: menuContainer} = this.getElements();
                if (Settings_default._menuTransparency) {
                    menuContainer.classList.add("transparent");
                }
                this.menuLoaded = true;
                this.frame.window.focus();
                Logger.test("Successfully injected iframe menu..");
            } catch (err) {
                Logger.error("Failed to inject iframe.. " + err);
            }
        }
    };

    const UI_default = UI;

    const defaultSettings = {
        _manualAim: false,
        _botAutoPlacer: true,
        _botAutoShoot: false,
        _botAutoShootPlatform: false,
        _botAutoShootRange: 1400,
        _botPrimary: null,
        _botSecondary: null,
        _botNickname: "",
        _botNickNumber: true,
        _botSync: true,
        _primary: "Digit1",
        _secondary: "Digit2",
        _food: "KeyQ",
        _wall: "Digit3",
        _spike: "KeyV",
        _windmill: "KeyN",
        _farm: "KeyT",
        _trap: "KeyF",
        _turret: "KeyF",
        _spawn: "KeyG",
        _up: "KeyW",
        _left: "KeyA",
        _down: "KeyS",
        _right: "KeyD",
        _autoattack: "KeyE",
        _lockrotation: "KeyX",
        _lockBotPosition: "KeyZ",
        _toggleChat: "Enter",
        _toggleShop: "ShiftLeft",
        _toggleClan: "ControlLeft",
        _toggleMenu: "Escape",
        _toggleBotsMenu: "Minus",
        _instakill: "KeyR",
        _biomehats: true,
        _autoemp: true,
        _antienemy: true,
        _soldierDefault: true,
        _antianimal: true,
        _antispike: true,
        _empDefense: true,
        _autoheal: true,
        _autoSync: true,
        _autoShield: true,
        _tailPriority: true,
        _velocityTick: true,
        _spikeSyncHammer: true,
        _spikeSync: true,
        _spikeTick: true,
        _knockbackTickTrap: true,
        _knockbackTickHammer: true,
        _knockbackTick: true,
        _toolSpearInsta: true,
        _autoSteal: true,
        _trapKB: true,
        _shameSpam: true,
        _autoPush: true,
        _turretSteal: true,
        _spikeGearInsta: true,
        _antiRetrap: true,
        _turretSync: true,
        _automill: true,
        _autoplacer: true,
        _placementDefense: true,
        _preplacer: false,
        _autoplacerRadius: 325,
        _placeAttempts: 4,
        _autobreak: true,
        _safeWalk: true,
        _dashMovement: true,
        _autoGrind: false,
        _enemyTracers: false,
        _enemyTracersColor: "#cc5151",
        _teammateTracers: false,
        _teammateTracersColor: "#8ecc51",
        _animalTracers: false,
        _animalTracersColor: "#518ccc",
        _notificationTracers: true,
        _notificationTracersColor: "#f5d951",
        _itemMarkers: true,
        _itemMarkersColor: "#84bd4b",
        _teammateMarkers: true,
        _teammateMarkersColor: "#bdb14b",
        _enemyMarkers: true,
        _enemyMarkersColor: "#ba4949",
        _weaponXPBar: true,
        _playerTurretReloadBar: true,
        _playerTurretReloadBarColor: "#cf7148",
        _weaponReloadBar: true,
        _weaponReloadBarColor: "#5155cc",
        _renderHP: true,
        _positionPrediction: false,
        _stackedDamage: true,
        _objectTurretReloadBar: false,
        _objectTurretReloadBarColor: "#66d9af",
        _itemHealthBar: false,
        _itemHealthBarColor: "#6b449e",
        _displayPlayerAngle: false,
        _weaponHitbox: false,
        _collisionHitbox: false,
        _placementHitbox: false,
        _possiblePlacement: true,
        _killMessage: true,
        _killMessageText: "rest in peace!",
        _autospawn: false,
        _autoaccept: false,
        _texturepack: false,
        _hideHUD: false,
        _menuTransparency: true,
        _chatLog: false,
        _followCursor: true,
        _movementRadius: 150,
        _circleFormation: false,
        _circleRotation: true,
        _circleRadius: 100,
        _storeItems: [ [ 15, 31, 6, 7, 22, 12, 26, 11, 53, 20, 40, 56 ], [ 11, 17, 16, 13, 19, 18, 21 ] ],
        _totalKills: 0,
        _globalKills: 0,
        _deaths: 0,
        _autoSyncTimes: 0,
        _velocityTickTimes: 0,
        _spikeSyncHammerTimes: 0,
        _spikeSyncTimes: 0,
        _spikeTickTimes: 0,
        _knockbackTickTrapTimes: 0,
        _knockbackTickHammerTimes: 0,
        _knockbackTickTimes: 0
    };

    const settings = {
        ...defaultSettings,
        ...CustomStorage.get("Colean")
    };

    for (const iterator in settings) {
        const key = iterator;
        if (!defaultSettings.hasOwnProperty(key)) {
            delete settings[key];
        }
    }

    const SaveSettings = () => {
        CustomStorage.set("Colean", settings);
        window.dispatchEvent(new Event('colean-settings-changed'));
    };

    SaveSettings();

    const resetSettings = () => {
        for (const iterator in defaultSettings) {
            const key = iterator;
            settings[key] = defaultSettings[key];
        }
        SaveSettings();
        UI_default.resetFrame();
    };

    const Settings_default = settings;

    const GameUI = new class {
        getElements() {
            const querySelector = document.querySelector.bind(document);
            const querySelectorAll = document.querySelectorAll.bind(document);
            return {
                gameCanvas: querySelector("#gameCanvas"),
                chatHolder: querySelector("#chatHolder"),
                storeHolder: querySelector("#storeHolder"),
                chatBox: querySelector("#chatBox"),
                storeMenu: querySelector("#storeMenu"),
                allianceMenu: querySelector("#allianceMenu"),
                storeContainer: querySelector("#storeContainer"),
                itemHolder: querySelector("#itemHolder"),
                gameUI: querySelector("#gameUI"),
                clanMenu: querySelector("#allianceMenu"),
                storeButton: querySelector("#storeButton"),
                clanButton: querySelector("#allianceButton"),
                setupCard: querySelector("#setupCard"),
                serverBrowser: querySelector("#serverBrowser"),
                skinColorHolder: querySelector("#skinColorHolder"),
                altServer: querySelector("#altServer"),
                settingRadio: querySelectorAll(".settingRadio"),
                pingDisplay: querySelector("#pingDisplay"),
                enterGame: querySelector("#enterGame"),
                nameInput: querySelector("#nameInput"),
                allianceInput: querySelector("#allianceInput"),
                allianceButton: querySelector("#allianceButton"),
                noticationDisplay: querySelector("#noticationDisplay"),
                nativeResolution: querySelector("#nativeResolution"),
                showPing: querySelector("#showPing"),
                mapDisplay: querySelector("#mapDisplay"),
                chatLog: querySelector("#chatLog")
            };
        }
        selectSkinColor(skin) {
            const skinValue = skin === 10 ? "toString" : skin;
            CustomStorage.set("skin_color", skinValue);
            const selectSkin = getTargetValue(window, "selectSkinColor");
            if (selectSkin !== void 0) {
                selectSkin(skinValue);
            }
            return skinValue;
        }
        createSkinColors() {
            const skin_color = CustomStorage.get("skin_color") || 0;
            const index = skin_color === "toString" ? 10 : skin_color;
            const {setupCard: setupCard} = this.getElements();
            const skinHolder = document.createElement("div");
            skinHolder.id = "skinHolder";
            let prevIndex = index;
            for (let i = 0; i < Config_default.skinColors.length; i++) {
                const color = Config_default.skinColors[i];
                const div = document.createElement("div");
                div.classList.add("skinColorItem");
                if (i === index) {
                    div.classList.add("activeSkin");
                }
                div.style.backgroundColor = color;
                div.onclick = () => {
                    const colorButton = skinHolder.childNodes[prevIndex];
                    if (colorButton instanceof HTMLDivElement) {
                        colorButton.classList.remove("activeSkin");
                    }
                    div.classList.add("activeSkin");
                    prevIndex = i;
                    this.selectSkinColor(i);
                };
                skinHolder.appendChild(div);
            }
            setupCard.appendChild(skinHolder);
        }
        formatMainMenu() {
            const {setupCard: setupCard, serverBrowser: serverBrowser, settingRadio: settingRadio, altServer: altServer, gameUI: gameUI} = this.getElements();
            setupCard.appendChild(serverBrowser);
            setupCard.querySelector("br")?.remove();
            this.createSkinColors();
            const radio = settingRadio[0];
            if (radio) {
                setupCard.appendChild(radio);
            }
            setupCard.appendChild(altServer);
            const div = document.createElement("div");
            div.id = "coleanStats";
            div.innerHTML = '\n            <span>PING: <span id="coleanPing"></span>ms</span>\n            <span>FPS: <span id="coleanFPS"></span></span>\n            <span>PACKETS: <span id="coleanPackets"></span></span>\n            <span>FastQ: <span id="coleanFastQ">false</span></span>\n            <span>Places: <span id="coleanPlaces">0</span></span>\n            <span>Total Kills: <span id="coleanTotalKills">0</span></span>\n            <span>Deaths: <span id="coleanTotalDeaths">0</span></span>\n            <span>Module: <span id="coleanActiveModule">null</span></span>\n            <span>SpikeDmg: <span id="coleanSpikeDamage"></span></span>\n            <span>PotDmg: <span id="coleanPotentialDamage"></span></span>\n            <span>Danger: <span id="coleanDangerState"></span></span>\n            <span>Hat: <span id="coleanEquipHat">0</span></span>\n            <span>Performance: <span id="coleanPerformance">0</span></span>\n            <span>CollideSpike: <span id="coleanCollideSpike"></span></span>\n        ';
            gameUI.appendChild(div);
        }
        attachItemCount() {
            const actionBar = document.querySelectorAll("div[id*='actionBarItem'");
            for (let i = 19; i < 39; i++) {
                const item = Items[i - 16];
                if (actionBar[i] instanceof HTMLDivElement && item !== void 0 && "itemGroup" in item) {
                    const group = item.itemGroup;
                    const span = document.createElement("span");
                    span.classList.add("itemCounter");
                    span.setAttribute("data-id", group + "");
                    const {count: count, limit: limit} = client.myPlayer.getItemCount(group);
                    span.textContent = `${count}/${limit}`;
                    actionBar[i].appendChild(span);
                }
            }
        }
        handleChatMessage(client2, text) {
            if (text === "/norecoil") {
                client2._ModuleHandler.norecoil = !client2._ModuleHandler.norecoil;
            }
            client2.PacketManager.chat(text);
        }
        modifyInputs() {
            const {chatHolder: chatHolder, chatBox: chatBox, nameInput: nameInput} = this.getElements();
            chatBox.onblur = () => {
                chatHolder.style.display = "none";
                const value = chatBox.value;
                if (value.length > 0) {
                    this.handleChatMessage(client, value);
                }
                chatBox.value = "";
            };
            nameInput.onchange = () => {
                CustomStorage.set("moo_name", nameInput.value, false);
            };
        }
        updateItemCount(group) {
            const items = document.querySelectorAll(`span.itemCounter[data-id='${group}']`);
            const {count: count, limit: limit} = client.myPlayer.getItemCount(group);
            for (const item of items) {
                item.textContent = `${count}/${limit}`;
            }
        }
        interceptEnterGame() {
            const enterGame = document.querySelector("#enterGame");
            const observer = new MutationObserver(() => {
                observer.disconnect();
                this.load();
            });
            observer.observe(enterGame, {
                attributes: true
            });
        }
        updatePing(ping) {
            const span = document.querySelector("#coleanPing");
            if (span !== null) {
                span.textContent = ping.toString();
            }
        }
        updateFPS(fps) {
            const span = document.querySelector("#coleanFPS");
            if (span !== null) {
                span.textContent = fps.toString();
            }
        }
        updatePackets(packets) {
            const span = document.querySelector("#coleanPackets");
            if (span !== null) {
                span.textContent = packets.toString();
            }
        }
        updateFastQ(state) {
            const span = document.querySelector("#coleanFastQ");
            if (span !== null) {
                span.textContent = state.toString();
            }
        }
        updatePlaces(count) {
            const span = document.querySelector("#coleanPlaces");
            const text = String(count);
            if (span !== null && span.textContent !== text) span.textContent = text;
        }
        updateTotalKills(kills) {
            const span = document.querySelector("#coleanTotalKills");
            if (span !== null) {
                span.textContent = kills.toString();
            }
        }
        botKills=0;
        botKillSocket=null;
        botKillsView=null;
        botKillIdentities=new Map;
        botKillUpdates=new WeakMap;
        isBotKillConnection(bot, allowOwner = false) {
            const main = client.SocketManager.socket, socket = bot.SocketManager.socket;
            if ((!allowOwner && bot.isOwner) || bot.ownerClient !== client || bot.crossServer ||
                main?.readyState !== 1 || socket?.readyState !== 1 || this.botKillSocket !== main) return false;
            try {
                const ownerURL = new URL(main.url), botURL = new URL(socket.url);
                return ownerURL.origin === botURL.origin && ownerURL.pathname === botURL.pathname;
            } catch (_) { return false; }
        }
        rememberBotKillIdentity(bot) {
            if (!this.isBotKillConnection(bot) || bot.myPlayer.id === -1 || bot.clientID == null) return;
            // Membership is independent of clan changes and removal from the bot controls.
            this.botKillIdentities.set(bot.myPlayer.id, bot.clientID);
        }
        observeBotKillIdentity(viewer, id, socketID) {
            if (!this.isBotKillConnection(viewer, true)) return;
            if (this.botKillIdentities.has(id) && this.botKillIdentities.get(id) !== socketID) {
                // A different connection reusing a numeric player ID is not our old bot.
                this.botKillIdentities.delete(id);
            }
        }
        botKillState(bot) {
            let state = this.botKillUpdates.get(bot);
            if (!state || state.socket !== bot.SocketManager.socket) {
                state = {socket:bot.SocketManager.socket, kills:bot.myPlayer.resources.kills, receipts:[]};
                this.botKillUpdates.set(bot, state);
            }
            return state;
        }
        beginBotKillUpdate(bot, total) {
            if (!this.isBotKillConnection(bot) || !Number.isSafeInteger(total) || total < 0) return null;
            const state = this.botKillState(bot), amount = total - state.kills;
            state.kills = total;
            if (amount < 0) state.receipts.length = 0;
            if (!Number.isSafeInteger(amount) || amount <= 0) return null;
            const receipt = {socket:state.socket, main:this.botKillSocket, remaining:amount, excluded:0};
            state.receipts.push(receipt);
            return receipt;
        }
        observeBotKillHealth(bot, id, previousHealth, health) {
            if (!this.isBotKillConnection(bot) || !Number.isFinite(health)) return;
            const state = this.botKillUpdates.get(bot);
            if (!state || state.socket !== bot.SocketManager.socket) return;
            // The kill total is sent before the victim's health update on this socket.
            // Match only that following update in the same snapshot batch. Never use
            // another bot's death, a nearby player, a name or an earlier death as proof.
            const receipt = state.receipts.findLast(entry => entry.remaining > 0);
            if (!receipt || health <= 0 && previousHealth <= 0) return;
            receipt.remaining--;
            if (health <= 0 && previousHealth > 0 && this.botKillIdentities.has(id)) receipt.excluded++;
        }
        resetBotKillLife(bot) {
            if (!this.isBotKillConnection(bot)) return;
            const state = this.botKillState(bot);
            state.kills = 0;
            state.receipts.length = 0;
        }
        finishBotKillFrame(bot) {
            const state = this.botKillUpdates.get(bot);
            if (state) state.receipts.length = 0;
        }
        addBotKills(bot, amount, receipt = null) {
            if (!this.isBotKillConnection(bot) || !Number.isSafeInteger(amount) || amount <= 0) return;
            if (receipt?.socket === bot.SocketManager.socket && receipt.main === this.botKillSocket) {
                amount -= Math.min(amount, receipt.excluded);
            }
            // Keep confirmed kills even after a bot dies or leaves the server.
            this.botKills += amount;
            this.refreshBotKills();
        }
        refreshBotKills() {
            const anchor = document.getElementById('killCounter');
            if (!anchor?.parentElement) return;
            let view = this.botKillsView;
            if (!view?.root.isConnected || view.anchor !== anchor) {
                view?.observer?.disconnect();
                view?.root.remove();
                const root = document.createElement('div');
                root.id = 'coleanBotKills'; root.className = 'resourceDisplay';
                root.title = 'Bot kills in this server session';
                root.setAttribute('role', 'status');
                root.style.cssText = 'position:absolute;right:0;left:auto;bottom:auto;margin:0;display:flex;align-items:center;gap:8px;white-space:nowrap;padding:5px 10px;background-image:none;pointer-events:none';
                const count = document.createElement('span'); count.id = 'coleanBotKillCount';
                const label = document.createElement('span'); label.textContent = 'BOT';
                label.style.cssText = 'font-size:14px;line-height:1'; label.setAttribute('aria-hidden', 'true');
                root.append(count, label); anchor.after(root);
                view = this.botKillsView = {root, count, anchor, observer:null};
                if (typeof ResizeObserver === 'function') {
                    view.observer = new ResizeObserver(() => this.positionBotKills());
                    view.observer.observe(anchor);
                    view.observer.observe(anchor.parentElement);
                }
                if (!this.botKillsResizeBound) {
                    this.botKillsResizeBound = true;
                    window.addEventListener('resize', () => this.positionBotKills());
                }
            }
            view.count.textContent = String(this.botKills);
            view.root.setAttribute('aria-label', `Bot kills: ${this.botKills}`);
            this.positionBotKills();
        }
        positionBotKills() {
            const view = this.botKillsView;
            if (!view?.root.isConnected || !view.anchor.isConnected) return;
            view.root.style.top = view.anchor.offsetTop + view.anchor.offsetHeight + 5 + 'px';
            view.root.style.right = Math.max(0, view.anchor.parentElement.clientWidth - view.anchor.offsetLeft - view.anchor.offsetWidth) + 'px';
        }
        updateTotalDeaths(deaths) {
            const span = document.querySelector("#coleanTotalDeaths");
            if (span !== null) {
                span.textContent = deaths.toString();
            }
        }
        updateActiveModule(name) {
            const span = document.querySelector("#coleanActiveModule");
            if (span !== null) {
                span.textContent = name + "";
            }
        }
        updateSpikeDamage(state) {
            const span = document.querySelector("#coleanSpikeDamage");
            if (span !== null) {
                span.textContent = state + "";
            }
        }
        updatePotentialDamage(state) {
            const span = document.querySelector("#coleanPotentialDamage");
            if (span !== null) {
                span.textContent = state + "";
            }
        }
        updateCollideSpike(state) {
            const span = document.querySelector("#coleanCollideSpike");
            if (span !== null) {
                span.textContent = state + "";
            }
        }
        updateDangerState(state) {
            const span = document.querySelector("#coleanDangerState");
            if (span !== null) {
                span.textContent = state + "";
            }
        }
        updateEquipHat(state) {
            const span = document.querySelector("#coleanEquipHat");
            if (span !== null) {
                span.textContent = state + "";
            }
        }
        updateModulePerformance(state) {
            const span = document.querySelector("#coleanPerformance");
            if (span !== null) {
                span.textContent = state + "";
            }
        }
        init() {
            this.formatMainMenu();
            this.modifyInputs();
            this.interceptEnterGame();
        }
        load() {
            const {nativeResolution: nativeResolution, enterGame: enterGame} = this.getElements();
            if (!nativeResolution.checked) {
                nativeResolution.click();
            }
            this.selectSkinColor(CustomStorage.get("skin_color") || 0);
        }
        loadGame() {
            this.attachItemCount();
            const {storeButton: storeButton, allianceButton: allianceButton, mapDisplay: mapDisplay} = this.getElements();
            const that = this;
            let _storeClick = storeButton.onmousedown;
            storeButton.onmousedown = function(...args) {
                that.reset();
                _storeClick.apply(this, args);
            };
            const _allianceClick = allianceButton.onmousedown;
            allianceButton.onmousedown = function(...args) {
                that.reset();
                _allianceClick.apply(this, args);
            };
            const _mapClick = mapDisplay.onmousedown;
            mapDisplay.onmousedown = function(event) {
                const bounds = mapDisplay.getBoundingClientRect();
                const scale = 14400 / bounds.width;
                const posX = (event.clientX - bounds.left) * scale;
                const posY = (event.clientY - bounds.top) * scale;
                client._ModuleHandler.endTarget._setXY(posX, posY);
                client._ModuleHandler.followPath = true;
                _mapClick.call(this, event);
            };
            this.createChatLog();
        }
        isOpened(element) {
            return element.style.display !== "none";
        }
        closePopups(element) {
            const {allianceMenu: allianceMenu, clanButton: clanButton} = this.getElements();
            if (this.isOpened(allianceMenu) && element !== allianceMenu) {
                clanButton.dispatchEvent(new MouseEvent("mousedown"));
            }
            const popups = document.querySelectorAll("#chatHolder, #storeMenu, #allianceMenu, #storeContainer");
            for (const popup of popups) {
                if (popup === element) {
                    continue;
                }
                popup.style.display = "none";
            }
            if (element instanceof HTMLElement) {
                element.style.display = this.isOpened(element) ? "none" : "";
            }
        }
        createAcceptButton(type) {
            const data = [ [ "#cc5151", "&#xE14C;" ], [ "#8ecc51", "&#xE876;" ] ];
            const [color, code] = data[type];
            const button = document.createElement("div");
            button.classList.add("notifButton");
            button.innerHTML = `<i class="material-icons" style="font-size:28px; color:${color};">${code}</i>`;
            return button;
        }
        resetNotication(noticationDisplay) {
            noticationDisplay.innerHTML = "";
            noticationDisplay.style.display = "none";
        }
        requestsView=null;
        requestNotificationID=null;
        hasActiveRequestBots() {
            const main = client.SocketManager.socket;
            if (!client.SocketManager.active || main?.readyState !== 1) return false;
            const server = url => { try { const parsed = new URL(url); return parsed.origin + parsed.pathname; } catch (_) { return null; } };
            const currentServer = server(main.url);
            return currentServer !== null && [...client.clients].some(bot => bot.ownerClient === client &&
                !bot.crossServer && !bot.disconnectRequested && bot.myPlayer.inGame &&
                bot.SocketManager.active && bot.SocketManager.socket?.readyState === 1 &&
                server(bot.SocketManager.socket.url) === currentServer);
        }
        ensureRequestsView() {
            if (this.requestsView?.root.isConnected) return this.requestsView;
            const {allianceButton: anchor, gameUI: gameUI} = this.getElements();
            if (!anchor) return null;
            if (!document.getElementById('coleanRequestsStyle')) {
                const style = document.createElement('style');
                style.id = 'coleanRequestsStyle';
                style.textContent = `
                    #coleanRequests{position:fixed;z-index:30;display:flex;flex-direction:column;align-items:flex-end;gap:5px;max-width:calc(100vw - 16px);color:#fff;font:14px "Hammersmith One",sans-serif;pointer-events:auto;text-align:left}
                    #coleanRequests[hidden],#coleanRequests [hidden]{display:none!important}
                    #coleanRequests button{font:inherit;color:#fff;border:0;border-radius:4px;cursor:pointer;line-height:1.3}
                    #coleanRequestsButton{background:rgba(0,0,0,.35);padding:5px 8px;font-weight:bold!important;white-space:nowrap}
                    #coleanRequests button:hover{filter:brightness(1.2)}
                    #coleanRequests button:focus-visible{outline:2px solid #ddd;outline-offset:2px}
                    #coleanRequestsPanel{position:absolute;top:calc(100% + 5px);box-sizing:border-box;width:320px;max-width:calc(100vw - 16px);padding:10px;background:rgba(25,25,30,.96);border-radius:5px;box-shadow:0 4px 14px #0005}
                    #coleanRequests .requests-heading{display:flex;align-items:center;justify-content:space-between;margin-bottom:8px;font-size:16px;font-weight:bold}
                    #coleanRequests .requests-close{background:transparent;font-size:20px;padding:0 5px}
                    #coleanRequestsList{max-height:min(280px,calc(100vh - 160px));overflow-y:auto;overscroll-behavior:contain}
                    #coleanRequests .requests-row{display:flex;align-items:center;gap:6px;padding:8px 0;border-top:1px solid #ffffff18}
                    #coleanRequests .requests-name{flex:1;min-width:0;overflow-wrap:anywhere}
                    #coleanRequests .requests-name small{display:block;font-size:11px;color:#aaa;margin-top:2px}
                    #coleanRequests .requests-accept{background:#507b39;padding:5px 7px}
                    #coleanRequests .requests-reject{background:#8b4444;padding:5px 7px}
                    #coleanRequests .requests-empty{margin:9px 0;color:#ccc}
                    #coleanRequestsStatus{margin:8px 0 0;color:#f2bd87;font-size:12px}
                `;
                document.head.appendChild(style);
            }
            const root = document.createElement('div');
            root.id = 'coleanRequests'; root.hidden = true;
            const button = document.createElement('button');
            button.id = 'coleanRequestsButton'; button.type = 'button'; button.textContent = 'Requests (0)';
            button.setAttribute('aria-expanded', 'false'); button.setAttribute('aria-controls', 'coleanRequestsPanel');
            const panel = document.createElement('section');
            panel.id = 'coleanRequestsPanel'; panel.hidden = true; panel.setAttribute('aria-label', 'Clan requests');
            const heading = document.createElement('div'); heading.className = 'requests-heading';
            const title = document.createElement('span'); title.textContent = 'Requests';
            const close = document.createElement('button'); close.type = 'button'; close.className = 'requests-close';
            close.textContent = '×'; close.setAttribute('aria-label', 'Close requests');
            const list = document.createElement('div'); list.id = 'coleanRequestsList';
            const status = document.createElement('p'); status.id = 'coleanRequestsStatus';
            status.hidden = true; status.setAttribute('role', 'status');
            heading.append(title, close); panel.append(heading, list, status); root.append(button, panel);
            (gameUI || document.body).appendChild(root);
            this.requestsView = {root, button, panel, list, status, signature:null};
            button.onclick = () => {
                const opening = panel.hidden;
                if (opening) this.closePopups(null);
                panel.hidden = !opening;
                button.setAttribute('aria-expanded', String(opening));
                this.positionRequests();
            };
            close.onclick = () => { this.closeRequests(); button.focus(); };
            root.addEventListener('keydown', event => {
                event.stopPropagation();
                if (event.key === 'Escape') { event.preventDefault(); this.closeRequests(); button.focus(); }
            });
            if (!this.requestsResizeBound) {
                this.requestsResizeBound = true;
                window.addEventListener('resize', () => this.positionRequests());
            }
            return this.requestsView;
        }
        closeRequests() {
            const view = this.requestsView;
            if (!view) return;
            view.panel.hidden = true;
            view.button.setAttribute('aria-expanded', 'false');
            this.positionRequests();
        }
        positionRequests() {
            const view = this.requestsView, anchor = this.getElements().allianceButton;
            if (!view || view.root.hidden || !anchor) return;
            const bounds = anchor.getBoundingClientRect();
            const left = Math.max(8, Math.min(bounds.right - view.root.offsetWidth, innerWidth - view.root.offsetWidth - 8));
            view.root.style.left = left + 'px';
            view.root.style.top = Math.max(8, bounds.bottom + 5) + 'px';
            if (!view.panel.hidden) {
                const panelLeft = Math.max(8, Math.min(left + view.root.offsetWidth - view.panel.offsetWidth, innerWidth - view.panel.offsetWidth - 8));
                view.panel.style.left = panelLeft - left + 'px';
            }
        }
        refreshRequests() {
            const player = client.myPlayer;
            const connected = client.SocketManager.active && client.SocketManager.socket?.readyState === 1;
            const requests = player.joinRequests.filter(([id]) => !client.clientIDList.has(id));
            const showPanel = connected && player.inGame && player.isLeader && (this.hasActiveRequestBots() || requests.length > 0);
            const view = showPanel ? this.ensureRequestsView() : this.requestsView;
            if (showPanel && view) {
                this.clearNotication();
                view.root.hidden = false;
                view.button.textContent = `Requests (${requests.length})`;
                const signature = JSON.stringify(requests);
                if (signature !== view.signature) {
                    view.signature = signature;
                    view.status.hidden = true;
                    view.list.replaceChildren();
                    if (!requests.length) {
                        const empty = document.createElement('p'); empty.className = 'requests-empty';
                        empty.textContent = 'No pending requests'; view.list.appendChild(empty);
                    }
                    for (const [id, nickname] of requests) {
                        const row = document.createElement('div'); row.className = 'requests-row'; row.dataset.requestId = String(id);
                        const name = document.createElement('span'); name.className = 'requests-name'; name.textContent = nickname;
                        const label = document.createElement('small'); label.textContent = `#${id}`; name.appendChild(label);
                        row.appendChild(name);
                        for (const accept of [true, false]) {
                            const action = document.createElement('button'); action.type = 'button';
                            action.textContent = accept ? 'Accept' : 'Reject';
                            action.className = accept ? 'requests-accept' : 'requests-reject';
                            action.setAttribute('aria-label', `${accept ? 'Accept' : 'Reject'} ${nickname}`);
                            action.onclick = () => {
                                if (!client._ModuleHandler.staticModules.autoAccept.respond(id, accept)) {
                                    view.status.textContent = 'Could not send the response. Please try again.';
                                    view.status.hidden = false;
                                }
                            };
                            row.appendChild(action);
                        }
                        view.list.appendChild(row);
                    }
                }
                this.positionRequests();
            } else {
                if (view) {
                    view.root.hidden = true; this.closeRequests();
                    if (view.signature !== null) {
                        view.signature = null; view.list.replaceChildren(); view.status.hidden = true;
                    }
                }
                if (connected && player.inGame && player.isLeader && requests.length && !Settings_default._autoaccept) {
                    this.createRequest(requests[0]);
                } else this.clearNotication();
            }
        }
        clearNotication() {
            const {noticationDisplay: noticationDisplay} = this.getElements();
            this.resetNotication(noticationDisplay);
        }
        createRequest(user) {
            const [id, name] = user;
            const {noticationDisplay: noticationDisplay} = this.getElements();
            if (noticationDisplay.style.display !== "none") {
                return;
            }
            noticationDisplay.innerHTML = "";
            noticationDisplay.style.display = "block";
            const text = document.createElement("div");
            text.classList.add("notificationText");
            text.textContent = name;
            noticationDisplay.appendChild(text);
            const handleClick = type => {
                const button = this.createAcceptButton(type);
                button.onclick = () => {
                    this.resetNotication(noticationDisplay);
                    const ok = client._ModuleHandler.staticModules.autoAccept.respond(id, !!type);
                    if (!ok) {
                        client.PacketManager.clanRequest(id, !!type);
                        const idx = client.myPlayer.joinRequests.findIndex(r => r[0] === id);
                        if (idx !== -1) client.myPlayer.joinRequests.splice(idx, 1);
                        client.pendingJoins.delete(id);
                    }
                    GameUI_default.refreshRequests();
                };
                noticationDisplay.appendChild(button);
            };
            handleClick(0);
            handleClick(1);
        }
        clientSpawn() {
            const {enterGame: enterGame} = this.getElements();
            enterGame.dispatchEvent(new MouseEvent("mousedown"));
        }
        handleEnter(event) {
            const {allianceInput: allianceInput, allianceButton: allianceButton} = this.getElements();
            const active = document.activeElement;
            if (client.myPlayer.inGame) {
                if (active === allianceInput) {
                    allianceButton.dispatchEvent(new MouseEvent("mousedown"));
                } else {
                    this.toggleChat(event);
                }
                return;
            }
            this.clientSpawn();
        }
        toggleChat(event) {
            const {chatHolder: chatHolder, chatBox: chatBox} = this.getElements();
            this.closePopups(chatHolder);
            if (this.isOpened(chatHolder)) {
                event.preventDefault();
                chatBox.focus();
            } else {
                chatBox.blur();
            }
        }
        reset() {
            StoreHandler_default.closeStore();
        }
        openClanMenu() {
            const {clanButton: clanButton} = this.getElements();
            this.reset();
            clanButton.dispatchEvent(new MouseEvent("mousedown"));
        }
        logCache=[];
        chatLog=null;
        addLogMessage(cache) {
            const [type, message] = cache;
            const div = document.createElement("div");
            div.className = "logMessage";
            div.innerHTML = `\n            <span class="darken">${formatDate()}</span>\n            <span class="messageContent ${type}"></span>\n        `;
            div.querySelector(".messageContent").textContent = message;
            const messageContainer = document.querySelector("#messageContainer");
            if (messageContainer !== null) {
                messageContainer.appendChild(div);
                messageContainer.scrollTop = messageContainer.scrollHeight;
            }
        }
        addCacheMessage(cache) {
            if (this.chatLog === null) {
                this.logCache.push(cache);
            } else {
                this.addLogMessage(cache);
            }
        }
        createChatLog() {
            if (this.chatLog !== null) {
                return;
            }
            const container = document.createElement("div");
            container.id = "chatLog";
            container.innerHTML = '\n            <h1 id="chatLogHeader">DevTools Chat Log</h1>\n            <div id="messageContainer"></div>\n        ';
            document.body.appendChild(container);
            this.chatLog = container;
            for (const log of this.logCache) {
                this.addLogMessage(log);
            }
        }
        toggleChatLog() {
            if (this.chatLog === null) {
                this.createChatLog();
            }
            if (Settings_default._chatLog) {
                this.chatLog.classList.remove("hidden");
            } else {
                this.chatLog.classList.add("hidden");
            }
        }
        lastMessages=[];
        handleMessageLog(message) {
            message = message.trim().replace(/\s+/g, " ");
            if (this.lastMessages.length > 3) {
                this.lastMessages.shift();
            }
            if (this.lastMessages.includes(message)) {
                return;
            }
            this.lastMessages.push(message);
            this.addLogMessage([ "log", message ]);
        }
    };

    const GameUI_default = GameUI;

    class Logger {
        static staticLog=console?.log || function() {};
        static staticError=console?.error || function() {};
        static staticWarn=console?.warn || function() {};
        static log(msg) {
            GameUI_default.addCacheMessage([ "log", msg ]);
            if (isProd) {
                return;
            }
            this.staticLog(msg);
        }
        static error(msg) {
            GameUI_default.addCacheMessage([ "error", msg ]);
            if (isProd) {
                return;
            }
            this.staticError(msg);
        }
        static warn(msg) {
            GameUI_default.addCacheMessage([ "warn", msg ]);
            if (isProd) {
                return;
            }
            this.staticWarn(msg);
        }
        static test(msg) {
            GameUI_default.addCacheMessage([ "log", msg ]);
            if (isProd) {
                return;
            }
            this.staticLog(msg);
        }
    }

    class Regexer {
        code;
        COPY_CODE;
        hookCount=0;
        hookAttempts=0;
        ANY_LETTER="(?:[^\\x00-\\x7F-]|\\$|\\w)";
        NumberSystem=[ {
            radix: 2,
            prefix: "0b0*"
        }, {
            radix: 8,
            prefix: "0+"
        }, {
            radix: 10,
            prefix: ""
        }, {
            radix: 16,
            prefix: "0x0*"
        } ];
        constructor(code) {
            this.code = code;
            this.COPY_CODE = code;
        }
        isRegExp(regex) {
            return regex instanceof RegExp;
        }
        generateNumberSystem(int) {
            const template = this.NumberSystem.map(({radix: radix, prefix: prefix}) => prefix + int.toString(radix));
            return `(?:${template.join("|")})`;
        }
        parseVariables(regex) {
            regex = regex.replace(/{VAR}/g, "(?:let|var|const)");
            regex = regex.replace(/{QUOTE{(\w+)}}/g, "(?:'$1'|\"$1\"|`$1`)");
            regex = regex.replace(/NUM{(\d+)}/g, (...args) => this.generateNumberSystem(Number(args[1])));
            regex = regex.replace(/\\w/g, this.ANY_LETTER);
            return regex;
        }
        format(name, inputRegex, flags) {
            this.hookAttempts++;
            let regex = "";
            if (Array.isArray(inputRegex)) {
                regex = inputRegex.map(exp => this.isRegExp(exp) ? exp.source : exp).join("\\s*");
            } else if (this.isRegExp(inputRegex)) {
                regex = inputRegex.source;
            } else {
                regex = inputRegex + "";
            }
            regex = this.parseVariables(regex);
            const expression = RegExp(regex, flags);
            if (!expression.test(this.code)) {
                Logger.error("Failed to find: " + name);
            } else {
                this.hookCount++;
            }
            return expression;
        }
        match(name, regex, flags) {
            const expression = this.format(name, regex, flags);
            return this.code.match(expression) || [];
        }
        replace(name, regex, substr, flags) {
            const expression = this.format(name, regex, flags);
            this.code = this.code.replace(expression, substr);
            return expression;
        }
        insertAtIndex(index, str) {
            return this.code.slice(0, index) + str + this.code.slice(index, this.code.length);
        }
        template(name, regex, substr, getIndex) {
            const expression = this.format(name, regex);
            const match = this.code.match(expression);
            if (match === null) {
                return;
            }
            const index = getIndex(match);
            this.code = this.insertAtIndex(index, substr.replace(/\$(\d+)/g, (...args) => match[args[1]]));
        }
        append(name, regex, substr) {
            this.template(name, regex, substr, match => (match.index || 0) + match[0].length);
        }
        prepend(name, regex, substr) {
            this.template(name, regex, substr, match => match.index || 0);
        }
        wrap(left, right) {
            this.code = left + this.code + right;
        }
    }

    const Regexer_default = Regexer;

    const formatCode2 = code => {
        const Hook = new Regexer_default(code);
        if (!isProd) {
            Hook.code = 'console?.log("Loaded bundle..");' + Hook.code;
        }
        Hook.replace("hookSend", /\(\w+\)\{({VAR} \w+=Array\.prototype\.slice)/, "(...args){Colean._myClient.PacketManager.send(args);return;$1");
        Hook.prepend("preRenderLoop", /\w+=Date\.now\(\);\w+=/, "Colean._Renderer._preRender();");
        Hook.append("postRenderLoop", /requestAnimationFrame\(\w+\)/, ";Colean._Renderer._postRender();");
        Hook.append("mapPreRender", /(\w+)\.lineWidth=NUM{4};/, "Colean._Renderer._mapPreRender($1);");
        Hook.prepend("LockRotationClient", /return \w+\?\(\!/, "return Colean._myClient._ModuleHandler._currentAngle;");
        Hook.replace("DisableResetMoveDir", /\w+={};\w+\.send\("\w+"\)/, "");
        Hook.append("offset", /\W165\W.+?(\w+)=\w+-\w+\/2;(\w+)=\w+-\w+\/2;/, "Colean._offset._setXY($1,$2);");
        Hook.prepend("renderEntity", /\w+\.\w+>NUM{0}.+?(\w+)\.fillStyle=(\w+)==(\w+)/, ";Colean._hooks._EntityRenderer._render($1,$2,$3);false&&");
        Hook.append("renderItemPush", /\w+,\w+\.scale\+\((\w+)\.\w+\|\|0\)\)/, "&&(Colean._Renderer._renderObjects.push($1))");
        Hook.append("renderItem", /70, 0.35\).+?(\w+)\.strokeStyle.+?;/, "Colean._hooks._ObjectRenderer._render($1);");
        Hook.replace("handleUnequip", /\w+\.send\("\w+",0,0,(\w+)\)/, "Colean._myClient._ModuleHandler._equip($1,0,true,true)");
        Hook.replace("handleEquip", /\w+\.send\("\w+",0,(.+?),(\w+)\)/, "Colean._myClient._ModuleHandler._equip($2,$1,true,true)");
        Hook.replace("handleBuy", /\w+\.send\("\w+",1,(.+?),(\w+)\)/, "Colean._myClient._ModuleHandler._buy($2,$1,true)");
        Hook.prepend("RemovePingCall", /\w+&&clearTimeout/, "return;");
        Hook.prepend("RemovePingState", /{VAR} \w+=Date\.now\(\)-\w+/, "return;");
        Hook.append("preRender", /250\)\);(\w+)\.strokeStyle=\n?.+?;/, "Colean._hooks._ObjectRenderer._preRender($1);");
        Hook.replace("upgradeItem", /(upgradeItem.+?onmousedown.+?)\w+\.\w+\("\w+",(\w+)\)\}/, "$1Colean._myClient._ModuleHandler._upgradeItem($2)}");
        Hook.replace("updateNotificationRemove", /(function \w+\(\w+,\w+\)\{)(\w+\.push\(\{sid)/, "$1return;$2");
        Hook.replace("removeSkins", /(\(\)\{)({VAR} \w+="";for\(let)/, "$1return;$2");
        Hook.prepend("unlockedItems", /\w+\.list\[\w+\]\.\w+==null\|\|\w+\.items/, "true||");
        Hook.replace("scaleWidth", /(\w+:)1920/, "$1Colean._ZoomHandler._scale._smooth._w");
        Hook.replace("scaleHeight", /(\w+:)1080/, "$1Colean._ZoomHandler._scale._smooth._h");
        Hook.replace("gameColor", /rgba\(0, 0, 70, 0.35\)/, "rgba(0, 0, 0, 0)");
        Hook.prepend("renderPlayer", /function (\w+)\(\w+,\w+\)\{\w+=\w+\|\|\w+;\w+\.lineWidth=5\.5;/, "Colean._hooks._renderPlayer=$1;");
        Hook.replace("RemoveSendAngle", /(\w+)!==(\w+)&&\(\w+=\w+,\w+\.send\("D",\w+\)\)/, "false");
        Logger.test(`Modified bundle, total amount of hooks: ${Hook.hookCount}/${Hook.hookAttempts}`);
        return PrivateVisualTheme.transformBundle(Hook.code);
    };

    const formatCode_default = formatCode2;

    const Injector = new class {
        init(node) {
            this.loadScript(node.src);
        }
        loadScript(src) {
            src = "https://raw.githubusercontent.com/ItzYakudza/colean-client/refs/heads/main/bundle.txt";
            const xhr = new XMLHttpRequest;
            xhr.open("GET", src, false);
            xhr.send();
            if (xhr.status !== 200 || !xhr.responseText.trim()) throw new Error("Colean bundle could not be loaded: " + xhr.status);
            BotVerification.readSitekey(xhr.responseText);
            const code = formatCode_default(xhr.responseText);
            if (isProd) {
                this.waitForBody(() => {
                    Function(code)();
                });
            } else {
                const blob = new Blob([ code ], {
                    type: "text/plain"
                });
                const element = document.createElement("script");
                element.src = URL.createObjectURL(blob);
                this.waitForBody(() => {
                    document.head.appendChild(element);
                });
            }
        }
        waitForBody(callback) {
            if (document.readyState !== "loading") {
                callback();
                Logger.test("Page already loaded, instant inject..");
                return;
            }
            document.addEventListener("readystatechange", () => {
                if (document.readyState !== "loading") {
                    callback();
                }
            }, {
                once: true
            });
        }
    };

    const Injector_default = Injector;

    const resetGame = loadedFast => {
        const scriptExecuteHandler = node => {
            node.addEventListener("beforescriptexecute", event => {
                event.preventDefault();
            }, {
                once: true
            });
            node.remove();
        };
        let scriptBundle = null;
        const handleScriptElement = node => {
            const isScript = node instanceof HTMLScriptElement;
            const isLink = node instanceof HTMLLinkElement;
            const regex = /frvr|jquery|howler|assets|cookie|securepubads|google|ads/i;
            if (isScript && regex.test(node.src) || isLink && regex.test(node.href) || regex.test(node.innerHTML)) {
                scriptExecuteHandler(node);
            }
            if (isScript && /assets.+\.js$/.test(node.src) && scriptBundle === null) {
                scriptBundle = node;
                Logger.test("Found script element, resolving..");
                scriptExecuteHandler(node);
                Injector_default.init(node);
            }
        };
        const observer = new MutationObserver(mutations => {
            for (const mutation of mutations) {
                for (const node of mutation.addedNodes) {
                    if (node instanceof HTMLScriptElement || node instanceof HTMLLinkElement) {
                        handleScriptElement(node);
                    }
                }
            }
        });
        observer.observe(document, {
            childList: true,
            subtree: true
        });
        document.querySelectorAll("script").forEach(handleScriptElement);
        document.querySelectorAll("link").forEach(handleScriptElement);
        document.querySelectorAll("iframe").forEach(iframe => {
            iframe.remove();
        });
        const resolvePromise = data => new Promise(function(resolve) {
            resolve(data);
        });
        const win = window;
        blockProperty(win, "onbeforeunload");
        win.frvrSdkInitPromise = resolvePromise();
        blockProperty(win, "frvrSdkInitPromise");
        win.FRVR = {
            bootstrapper: {
                complete() {}
            },
            tracker: {
                levelStart() {}
            },
            ads: {
                show() {
                    return resolvePromise();
                }
            },
            channelCharacteristics: {
                allowNavigation: true
            },
            setChannel() {}
        };
        blockProperty(win, "FRVR");
        const _fetch = window.fetch;
        window.fetch = new Proxy(_fetch, {
            apply(target, _this, args) {
                const link = args[0];
                if (typeof link === "string") {
                    if (/ping/.test(link)) {
                        return resolvePromise();
                    }
                }
                return target.apply(_this, args);
            }
        });
        CustomStorage.set("moofoll", 1);
        if (CustomStorage.get("skin_color") === null) {
            CustomStorage.set("skin_color", "toString");
        }
        window.addEventListener = new Proxy(window.addEventListener, {
            apply(target, _this, args) {
                if ([ "keydown", "keyup" ].includes(args[0]) && args[2] === void 0) {
                    if (args[0] === "keyup" && loadedFast) {
                        window.addEventListener = target;
                    }
                    return null;
                }
                return target.apply(_this, args);
            }
        });
        const proto = HTMLDivElement.prototype;
        proto.addEventListener = new Proxy(proto.addEventListener, {
            apply(target, _this, args) {
                if (_this.id === "touch-controls-fullscreen" && /^mouse/.test(args[0]) && args[2] === false) {
                    if (/up$/.test(args[0]) && loadedFast) {
                        proto.addEventListener = target;
                    }
                    return null;
                }
                return target.apply(_this, args);
            }
        });
        window.setInterval = new Proxy(window.setInterval, {
            apply(target, _this, args) {
                if (/cordova/.test(args[0].toString()) && args[1] === 1e3) {
                    if (loadedFast) {
                        window.setInterval = target;
                    }
                    return null;
                }
                return target.apply(_this, args);
            }
        });
        const deleteProp = (target, name) => {
            delete target[name];
        };
        Hooker_default.createRecursiveHook(window, "config", (that, config) => {
            deleteProp(that, "openLink");
            deleteProp(that, "aJoinReq");
            deleteProp(that, "follmoo");
            deleteProp(that, "kickFromClan");
            deleteProp(that, "sendJoin");
            deleteProp(that, "leaveAlliance");
            deleteProp(that, "createAlliance");
            deleteProp(that, "storeBuy");
            deleteProp(that, "storeEquip");
            deleteProp(that, "showItemInfo");
            deleteProp(that, "config");
            deleteProp(that, "altchaCreateWorker");
            deleteProp(that, "captchaCallbackHook");
            deleteProp(that, "showPreAd");
            deleteProp(that, "setUsingTouch");
            that.addEventListener("blur", that.onblur);
            deleteProp(that, "onblur");
            that.addEventListener("focus", that.onfocus);
            deleteProp(that, "onfocus");
            Colean._config = config;
            Logger.log("Intercepted config..");
            return loadedFast;
        });
        const patterns = {
            "./img/hats/hat_12.png": "https://i.postimg.cc/BQPfhPwD/Booster-V2.png",
            "./img/hats/hat_23.png": "https://i.postimg.cc/WpHP6wST/Anti-Venom-Gear.png",
            "./img/hats/hat_6.png": "https://i.postimg.cc/662BPP8y/Soldier-Helmet.png",
            "./img/hats/hat_15.png": "https://i.postimg.cc/pXKRWnYv/Winter-Cap.png",
            "./img/hats/hat_7.png": "https://i.postimg.cc/zGnZNZNG/Bull-Helmet-V2.png",
            "./img/hats/hat_58.png": "https://i.postimg.cc/B67RpJTM/Bushido-Armor.png",
            "./img/hats/hat_8.png": "https://i.postimg.cc/XJYT9rCr/Bummel-Hat.png",
            "./img/hats/hat_5.png": "https://i.postimg.cc/hvJ63NMg/Cowboy-Hat.png",
            "./img/hats/hat_50.png": "https://i.postimg.cc/y8h55mhJ/Honeycrisp-Hat.png",
            "./img/hats/hat_18.png": "https://i.postimg.cc/RhjyrGbt/Explorer-Hat-V2.png",
            "./img/hats/hat_27.png": "https://i.postimg.cc/mkFpSC2g/Scavenger-Gear.png",
            "./img/hats/hat_26.png": "https://i.postimg.cc/t40Q8RLc/Barbarian-Armor.png",
            "./img/hats/hat_20.png": "https://i.postimg.cc/Dmkjp08d/Samurai-Hat.png",
            "./img/hats/hat_22.png": "https://i.postimg.cc/5t3hHB6c/Emp-Helmet.png",
            "./img/hats/hat_13.png": "https://i.postimg.cc/BvqyGjNm/Medic-Gear-V2.png",
            "./img/hats/hat_9.png": "https://i.postimg.cc/g0N7cGTm/Miner.png",
            "./img/hats/hat_4.png": "https://i.postimg.cc/Tw14pBzm/Ranger-Hat.png",
            "./img/hats/hat_31.png": "https://i.postimg.cc/2SNM2cWR/Flipper-Hat.png",
            "./img/hats/hat_1.png": "https://i.postimg.cc/fWF60TTb/Fiddler-Hat.png",
            "./img/hats/hat_11.png": "https://i.postimg.cc/7PFqrNzX/Spike-V2.png",
            "./img/hats/hat_11_p.png": "https://i.postimg.cc/7PFqrNzX/Spike-V2.png",
            "./img/hats/hat_11_top.png": ""
        };
        if (Settings_default._texturepack) {
            Logger.log("Injected texture pack..");
            const imageDesc = Object.getOwnPropertyDescriptor(Image.prototype, "src");
            Object.defineProperty(Image.prototype, "src", {
                get() {
                    return imageDesc.get?.call(this);
                },
                set(value) {
                    if (value in patterns) {
                        value = patterns[value];
                    }
                    if (value === "") {
                        return;
                    }
                    return imageDesc.set?.call(this, value);
                },
                configurable: true
            });
        }
        const _proto_ = Object.prototype;
        Object.defineProperty(_proto_, "processServers", {
            set(value) {
                Logger.log("Hooked processServers..");
                delete _proto_.processServers;
                this.processServers = function(data) {
                    for (const server of data) {
                        server.playerCapacity += 1;
                    }
                    Logger.log("Increased capacity..");
                    return value.call(this, data);
                };
            },
            configurable: true
        });
    };

    const resetGame_default = resetGame;

    class DeadPlayer {
        moveAngle;
        skinColor;
        angle;
        weapon;
        variant;
        hatID;
        accID;
        rotation;
        baseTime=2e3;
        elapsedTime=0;
        pos=new Vector_default;
        lerpPos=new Vector_default;
        acc=7;
        velocity=0;
        opacity=1;
        shortSign;
        constructor(startPos, moveAngle, skin, rotation, weapon, variant, hatID, accID, impulse) {
            this.moveAngle = moveAngle;
            this.skinColor = skin;
            this.angle = rotation;
            this.weapon = weapon;
            this.variant = variant;
            this.hatID = hatID;
            this.accID = accID;
            this.rotation = rotation;
            this.pos.setVec(startPos);
            this.lerpPos.setVec(startPos);
            this.shortSign = Math.sign(shortAngle(this.angle, this.moveAngle));
            this.acc = (impulse || 10) / 10 * 75;
        }
        update(delta) {
            this.elapsedTime += delta;
            const progress = Math.min(this.elapsedTime / this.baseTime, 1);
            const easedProgress = easeOutQuad(progress);
            this.opacity = 1 - easedProgress;
            const dt = delta / 1e3;
            const blend = 1 - Math.exp(-10 * dt);
            const PI3 = Math.PI;
            const rotationSpeed = (1 - easedProgress) / PI3 * blend;
            this.rotation += rotationSpeed * this.shortSign;
            this.velocity = this.acc * (1 - easedProgress);
            this.pos.add(Vector_default.fromAngle(this.moveAngle, this.velocity * dt));
            this.lerpPos.x = lerp(this.lerpPos.x, this.pos.x, blend);
            this.lerpPos.y = lerp(this.lerpPos.y, this.pos.y, blend);
        }
        isFinished() {
            return this.elapsedTime >= this.baseTime;
        }
    }

    const DeadPlayerHandler = new class {
        deadPlayers=new Set;
        start=Date.now();
        add(player) {
            this.deadPlayers.add(player);
        }
        render(ctx, pos, color) {
            const player = client.myPlayer;
            if (!player.inGame) {
                return;
            }
            const offset = Colean._offset;
            ctx.save();
            ctx.translate(pos.x - offset.x, pos.y - offset.y);
            ctx.rotate(player.angle);
            ctx.globalAlpha = .6;
            ctx.strokeStyle = "#525252";
            const {autoHat: autoHat} = client._ModuleHandler.staticModules;
            const weaponID = autoHat.getNextWeaponID();
            const variant = player.getWeaponVariant(weaponID).current;
            Colean._hooks._renderPlayer({
                weaponIndex: weaponID,
                buildIndex: autoHat.getNextItemID(),
                tailIndex: autoHat.getNextAcc(),
                skinIndex: autoHat.getNextHat(),
                weaponVariant: variant,
                skinColor: player.skinID,
                scale: 35
            }, ctx);
            ctx.fillStyle = color;
            ctx.fill();
            ctx.restore();
        }
        update(ctx) {
            const now = Date.now();
            const delta = now - this.start;
            this.start = now;
            const offset = Colean._offset;
            for (const player of this.deadPlayers) {
                player.update(delta);
                ctx.save();
                ctx.translate(player.lerpPos.x - offset.x, player.lerpPos.y - offset.y);
                ctx.rotate(player.rotation);
                ctx.globalAlpha = player.opacity;
                ctx.strokeStyle = "#525252";
                Colean._hooks._renderPlayer({
                    weaponIndex: player.weapon,
                    buildIndex: -1,
                    tailIndex: player.accID,
                    skinIndex: player.hatID,
                    weaponVariant: player.variant,
                    skinColor: player.skinColor,
                    scale: 35
                }, ctx);
                ctx.restore();
                if (player.isFinished()) {
                    this.deadPlayers.delete(player);
                }
            }
        }
    };

    const ObjectRenderer = new class {
        healthBar(ctx, entity, object) {
            if (!(Settings_default._itemHealthBar && object.seenPlacement && object.isDestroyable)) {
                return 0;
            }
            const {health: health, maxHealth: maxHealth, angle: angle} = object;
            const perc = health / maxHealth;
            const color = Settings_default._itemHealthBarColor;
            return Renderer_default.circularBar(ctx, entity, perc, angle, color);
        }
        renderTurret(ctx, entity, object, scale) {
            if (object.type !== 17) {
                return;
            }
            if (Settings_default._objectTurretReloadBar) {
                const {reload: reload, maxReload: maxReload, angle: angle} = object;
                const perc = reload / maxReload;
                const color = Settings_default._objectTurretReloadBarColor;
                Renderer_default.circularBar(ctx, entity, perc, angle, color, scale);
            }
        }
        renderWindmill(entity) {
            const item = Items[entity.id];
            if (item.itemType === 5) {
                entity.turnSpeed = 0;
            }
        }
        renderCollisions(ctx, entity, object) {
            const x = entity.x + entity.xWiggle;
            const y = entity.y + entity.yWiggle;
            if (Settings_default._collisionHitbox) {
                Renderer_default.circle(ctx, x, y, object.collisionScale, "#c7fff2", .5, 1);
                Renderer_default.rect(ctx, new Vector_default(x, y), object.collisionScale, "#ecffbd", 1, .5);
            }
            if (Settings_default._weaponHitbox) {
                Renderer_default.circle(ctx, x, y, object.hitScale, "#3f4ec4", .5, 1);
            }
            if (Settings_default._placementHitbox) {
                Renderer_default.circle(ctx, x, y, object.placementScale, "#73b9ba", .5, 1);
            }
            if (object instanceof PlayerObject && object.canBeDestroyed) {
                Renderer_default.fillCircle(ctx, x, y, 10, "#f88a41ff", .3);
            }
        }
        _render(ctx) {
            if (Renderer_default._renderObjects.length === 0) {
                return;
            }
            const {ObjectManager: ObjectManager2, _ModuleHandler: ModuleHandler2, myPlayer: myPlayer} = client;
            for (const entity of Renderer_default._renderObjects) {
                const object = ObjectManager2.objects.get(entity.sid);
                if (object === void 0) {
                    continue;
                }
                Renderer_default.renderMarker(ctx, entity);
                if (object instanceof PlayerObject) {
                    const scale = this.healthBar(ctx, entity, object);
                    this.renderTurret(ctx, entity, object, scale);
                    this.renderWindmill(entity);
                }
                this.renderCollisions(ctx, entity, object);
            }
            Renderer_default._renderObjects.length = 0;
        }
        volcanoBoxSize=940;
        volcanoAggressionRadius=1440;
        volcanoBoxPos=new Vector_default(14400, 14400).sub(this.volcanoBoxSize);
        volcanoPos=new Vector_default(13960, 13960);
        _preRender(ctx) {
            const offsetX = Colean._offset.x;
            const offsetY = Colean._offset.y;
            ctx.save();
            ctx.globalAlpha = .5;
            ctx.strokeStyle = "red";
            ctx.translate(-offsetX, -offsetY);
            ctx.beginPath();
            ctx.arc(this.volcanoPos.x, this.volcanoPos.y, this.volcanoAggressionRadius, 2.831070818924026, 5.022910815050457);
            const size = this.volcanoBoxSize;
            const x = this.volcanoBoxPos.x - size;
            const y = this.volcanoBoxPos.y - size;
            ctx.moveTo(x, y);
            ctx.lineTo(x + size * 2, y);
            ctx.moveTo(x, y);
            ctx.lineTo(x, y + size * 2);
            ctx.stroke();
            ctx.restore();
            if (client.myPlayer.diedOnce) {
                const {x: x2, y: y2} = client.myPlayer.deathPosition;
                Renderer_default.cross(ctx, x2, y2, 50, 15, "#cc5151");
            }
            if (Settings_default._positionPrediction && client.myPlayer.inGame) {
                DeadPlayerHandler.render(ctx, client.myPlayer.simulation.getPos(), client.myPlayer.simulation.spikeCollision ? "red" : "yellow");
            }
        }
    };

    const ObjectRenderer_default = ObjectRenderer;

    const isProd = true;

    const version = isProd ? "1.0.0" : "Dev";

    const loadedFast = document.head === null;

    if (!loadedFast) {
        Logger.warn("Colean Client loading warning! It is generally recommended to use faster injection mode.");
    }

    Logger.test("Colean Client initialization..");

    const client = new PlayerClient_default;

    const OriginalSocket = window.WebSocket;
    const ownerSocketProxy = new window.Proxy(OriginalSocket, {
        construct(target, args) {
            const socket = new target(...args);
            let isGameSocket = false;
            try {
                const url = new URL(args[0]);
              isGameSocket = [ "ws:", "wss:" ].includes(url.protocol) && (/(^|\.)moomoo\.io$/i.test(url.hostname) || ([ "localhost", "127.0.0.1" ].includes(url.hostname) && url.port !== "8091" && !String(url.pathname || "").includes("control")));
            } catch (_) {}
            if (isGameSocket) {
                Logger.test("Found socket! Socket initialization..");
                client.SocketManager.init(socket);
                if (window.WebSocket === ownerSocketProxy) {
                    window.WebSocket = OriginalSocket;
                }
            }
            return socket;
        }
    });
    window.WebSocket = ownerSocketProxy;

    const win = window;

    const Colean = {
        _myClient: client,
        _settings: Settings_default,
        _Renderer: Renderer_default,
        _visualTheme: PrivateVisualTheme,
        _ZoomHandler: ZoomHandler_default,
        _hooks: {
            _EntityRenderer: EntityRenderer_default,
            _ObjectRenderer: ObjectRenderer_default,
            _renderPlayer: function() {}
        },
        _config: {},
        version: CLIENT_VERSION,
        _offset: new Vector_default,
        startGame() {
            GameUI_default.getElements().enterGame.dispatchEvent(new MouseEvent("mousedown"));
        }
    };

    win.Colean = Colean;
    window.Colean = Colean;
    
    const myClient = client;
    try {
        Colean.author = CLIENT_AUTHOR;
        Colean.version = CLIENT_VERSION;
        Colean.name = CLIENT_NAME;
    } catch (_) {}

(function ExtraMenuAllBots(){
    if (window.__gmx_extramenu_loaded) return;
    window.__gmx_extramenu_loaded = true;

    const PANEL_ID = 'gmx-panel';
    const STYLES_ID = 'gmx-panel-styles';
    let isOpen = false;
    let stateRefreshTimer = null;


    const STORAGE_KEY = 'colean_aibm_extra_v1';
    let config = loadConfig();
    for (const [key, action] of Object.entries(config.keybinds)) {
        if (['instakill', 'bowinsta', 'bm', 'ba', 'bowspam'].includes(action)) delete config.keybinds[key];
        else if (action === 'btn-cursorfollow') config.keybinds[key] = 'cursorfollow';
        else if (action === 'btn-botsync') config.keybinds[key] = 'botsync';
    }
    // Default: Sync ON/OFF on KeyC if nothing bound yet
    if (!Object.values(config.keybinds).includes('botsync')) {
        if (config.keybinds['KeyC'] && config.keybinds['KeyC'] !== 'botsync') {
            // keep existing KeyC action; user can rebind in menu
        } else {
            config.keybinds['KeyC'] = 'botsync';
        }
    }
    saveConfig();

    function loadConfig() {
        try {
            const data = localStorage.getItem(STORAGE_KEY);
            const saved = JSON.parse(data);
            if (saved && typeof saved === "object") return { ...saved, activeTab: ["main", "movement", "combat", "binds"].includes(saved.activeTab) ? saved.activeTab : "main", position: { top: null, left: null, ...saved.position }, keybinds: saved.keybinds && typeof saved.keybinds === "object" ? saved.keybinds : {} };
            return {
                activeTab: 'main',
                position: { top: null, left: null },
                keybinds: {} // Default keybinds
            };
        } catch(e) {
            return { activeTab: 'main', position: { top: null, left: null }, keybinds: {} };
        }
    }

    function saveConfig() {
        try {
            localStorage.setItem(STORAGE_KEY, JSON.stringify(config));
        } catch(e) { /* ignore */ }
    }

    function injectStyles(){
    if (document.getElementById(STYLES_ID)) return;
    const css = `

        @import url('https://fonts.googleapis.com/css2?family=Noto+Sans:wght@400;600;800&display=swap');




        #${PANEL_ID} {
            box-sizing: border-box;
            position: fixed;
            right: 18px;
            bottom: 40px;
            width: 420px;
            max-width: calc(100vw - 24px);

            max-height: 70vh;


            background: #0c1218;
            background: linear-gradient(135deg, #0f1820 0%, #0c1218 70%, #152536 100%);


            border-radius: 4px;


            color: #c5d4e0;
            border: 2px solid #2a5080;
            box-shadow: 0 0 15px rgba(62,143,212,0.45), 0 0 5px rgba(0,0,0,0.8);

            z-index: 2147483000;
            padding: 10px;

            font-family: 'Noto Sans', sans-serif;

            opacity: 0;
            transform: translateY(10px) scale(0.98);
            pointer-events: none;
            transition: opacity .35s ease-out, transform .35s ease-out;
        }

        #${PANEL_ID}.open {
            opacity: 1;
            transform: translateY(0) scale(1);
            pointer-events: auto;
        }


        #${PANEL_ID} .gmx-header {
            display: flex;
            align-items: center;
            justify-content: space-between;
            padding: 8px 6px;

            border-bottom: 1px solid #3d8fd4;
            margin-bottom: 8px;
        }

        #${PANEL_ID} .gmx-title {
            font-size: 18px;
            color: #6eb6ff;
            text-shadow: 1px 1px 2px #000;
        }


        #${PANEL_ID} .gmx-close {
            background: transparent;
            border: 1px solid #2a5080;
            color: #3d8fd4;
            font-size: 24px;
            cursor: pointer;

            width: 34px;
            height: 34px;
            border-radius: 50%;
            display: flex;
            align-items: center;
            justify-content: center;
            padding: 0;



            transition: background .2s ease, color .2s ease, transform .4s cubic-bezier(0.25, 0.46, 0.45, 0.94);
        }

        #${PANEL_ID} .gmx-close:hover {
            background: rgba(110,182,255,0.2);
            color: #6eb6ff;
            transform: rotate(360deg) scale(1.1);
            box-shadow: 0 0 20px #6eb6ff;
        }


        #${PANEL_ID} .gmx-tabs {
            display: flex;
            gap: 6px;
            margin: 8px 0;
            width: 100%;
            margin-left: 0;
            padding: 0 8px;
            box-sizing: border-box;
        }

        #${PANEL_ID} .gmx-tab {

            font-size: 14px;
            padding: 5px 4px;

            flex: 1;
            border-radius: 4px;
            background: #152536;
            text-align: center;
            cursor: pointer;
            color: #c5d4e0;
            border: 1px solid #2a5080;
            transition: background .2s, color .2s, transform .2s;

            min-width: 0;
        }

        #${PANEL_ID} .gmx-tab:hover {
             background: #1b527a;
        }

        #${PANEL_ID} .gmx-tab.active {

            background: linear-gradient(90deg, #3d8fd4, #2a5080);
            color: #FFF;
            box-shadow: 0 4px 10px rgba(62,143,212,0.45);
            transform: translateY(-1px);
            border-color: #6eb6ff;
        }


        #${PANEL_ID} .gmx-body {
            padding: 3px;

            max-height: calc(70vh - 120px);
            overflow: auto;

            border: 1px solid rgba(62,143,212,0.45);
            border-radius: 4px;
        }


        #${PANEL_ID} .gmx-row {
            display: flex;
            gap: 8px;
            align-items: center;
            margin-bottom: 10px;
            flex-wrap: wrap;
        }

        #${PANEL_ID} .gmx-list-item {
            display: flex;
            justify-content: space-between;
            align-items: center;
            padding: 6px 0;
            border-bottom: 1px dashed rgba(62,143,212,0.3);
        }

        #${PANEL_ID} .gmx-key-btn {
            background: #123752;
            border: 1px solid #3d8fd4;
            color: #c5d4e0;
            padding: 4px 8px;
            border-radius: 4px;
            cursor: pointer;
            min-width: 40px;
            text-align: center;
            transition: background .15s;
        }

        #${PANEL_ID} .gmx-key-btn:hover {
            background: #1b527a;
        }

        #${PANEL_ID} .gmx-key-btn.active {
            background: #3d8fd4;
            color: #FFF;
            border-color: #6eb6ff;
        }

        #${PANEL_ID} .gmx-btn {
            display: inline-flex;
            align-items: center;
            justify-content: center;
            gap: 8px;
            background: #123752;
            color: #c5d4e0;
            border: 1px solid #2a5080;
            padding: 8px 10px;
            border-radius: 4px;
            cursor: pointer;
            transition: transform .12s ease, box-shadow .12s ease, background .12s;
        }

        #${PANEL_ID} .gmx-btn.small {
            padding: 6px 8px;
            font-size: 13px;
        }

        #${PANEL_ID} .gmx-btn.active,
        #${PANEL_ID} .gmx-btn[data-mode-active="true"] {

            background: linear-gradient(135deg,#6eb6ff,#CCAC00);
            color: #111;
            box-shadow: 0 6px 18px rgba(212,175,55,0.25);
            transform: scale(1.03);
        }


        #${PANEL_ID} .gmx-btn:hover {
            background: #1b527a;
            box-shadow: 0 0 6px rgba(62,143,212,0.3);
            transform: scale(1.02);
        }

        #${PANEL_ID} .gmx-btn:active {
            transform: scale(0.97);
            background: #0f3654;
            box-shadow: inset 0 2px 4px rgba(0,0,0,0.5);
        }


        #${PANEL_ID} input[type="number"],
        #${PANEL_ID} select,
        #${PANEL_ID} input[type="text"] {
            background: #0f1820;
            border: 1px solid #2a5080;
            color: #c5d4e0;
            padding: 8px;
            border-radius: 4px;
            min-width: 74px;
            transition: border-color .2s;
        }

        #${PANEL_ID} input[type="number"]:focus,
        #${PANEL_ID} select:focus,
        #${PANEL_ID} input[type="text"]:focus {
            outline: none;
            border-color: #3d8fd4;
            box-shadow: 0 0 5px rgba(62,143,212,0.5);
        }

        #${PANEL_ID} select option {
            background: #0f1820;
            color: #c5d4e0;
        }

        #${PANEL_ID} .gmx-check { position:relative; display:inline-block; width:70px; height:28px; flex-shrink:0; }
        #${PANEL_ID} .gmx-check input { position:absolute; inset:0; width:100%; height:100%; margin:0; opacity:0; cursor:pointer; z-index:1; }
        #${PANEL_ID} .gmx-check-track { display:block; height:100%; background:#2a3a4a; border-radius:4px; }
        #${PANEL_ID} .gmx-check-track::after { content:''; position:absolute; top:4px; left:4px; width:20px; height:20px; background:#6eb6ff; border-radius:3px; transition:transform .15s; }
        #${PANEL_ID} .gmx-check input:checked + .gmx-check-track { background:#2a5080; }
        #${PANEL_ID} .gmx-check input:checked + .gmx-check-track::after { transform:translateX(42px); background:#6eb6ff; }
        #${PANEL_ID} .gmx-check input:focus-visible + .gmx-check-track { outline:2px solid #6eb6ff; outline-offset:2px; }


        #${PANEL_ID} .gmx-status {
            position: absolute;
            left: 14px;
            right: 14px;
            bottom: 12px;
            font-size: 12px;
            color: #6eb6ff;
            text-align: center;
            opacity: 0;
            transform: translateY(6px);
            pointer-events: none;
            transition: opacity .18s, transform .18s;
        }

        #${PANEL_ID}.show-status .gmx-status {
            opacity: 1;
            transform: translateY(0);
            pointer-events: auto;
        }

        #${PANEL_ID} .gmx-bubble {
            display: inline-block;
            padding: 6px 10px;
            border-radius: 4px;
            background: #121c28;
            color: #c5d4e0;
            border: 1px solid #2a5080;
            box-shadow: 0 6px 20px rgba(0,0,0,0.5);
        }


        #${PANEL_ID} .gmx-body::-webkit-scrollbar {
            width: 10px;
        }

        #${PANEL_ID} .gmx-body::-webkit-scrollbar-thumb {
            background: #350000;
            border-radius: 8px;
        }
    `;
        const st = document.createElement('style');
        st.id = STYLES_ID;
        document.head.appendChild(st);
        st.textContent = css + `
 #${PANEL_ID}, #${PANEL_ID} button, #${PANEL_ID} input, #${PANEL_ID} select, #colean-extra-launcher { font-family:"Noto Sans",sans-serif; font-weight:800; }
 #${PANEL_ID} .gmx-btn, #${PANEL_ID} .gmx-tab { font-size:1.1em; color:#888c92; }
 #${PANEL_ID} .gmx-row, #${PANEL_ID} label { color:#a0a5aa; }
 #${PANEL_ID} .gmx-status { font-size:1.1em; font-weight:800; color:#c0c5ca; }

 #${PANEL_ID} .gmx-status { position:static; min-height:30px; margin-top:6px; }
 #${PANEL_ID} .gmx-row > input, #${PANEL_ID} .gmx-row > select { min-width:0; }
 #${PANEL_ID} .gmx-grid { display:flex; gap:6px; flex-wrap:wrap; }
 #${PANEL_ID} .gmx-body { max-height:calc(70vh - 160px); }
 #${PANEL_ID} .gmx-tab { font-size:clamp(11px,3.2vw,14px); }
 #${PANEL_ID} .gmx-btn[data-mode-active="true"] { background:linear-gradient(135deg,#6eb6ff,#CCAC00)!important; color:#111!important; }
 `;
    }



    function buildPanel(){
        if (document.getElementById(PANEL_ID)) return;
        injectStyles();

        const p = document.createElement('div');
        p.id = PANEL_ID;
        // Apply saved position
        if (config.position.top !== null) {
            p.style.top = config.position.top;
            p.style.left = config.position.left;
            p.style.right = 'auto';
            p.style.bottom = 'auto';
        }

        // Rename 'settings' to 'binds' in config if it's the old value
        if (config.activeTab === 'settings') {
            config.activeTab = 'binds';
            saveConfig();
        }

        p.innerHTML = `
            <div class="gmx-header">
                <div class="gmx-title">Colean Bots Menu <small class="gmx-menu-shortcut"></small></div>
                <button class="gmx-close" >×</button>
            </div>

            <div class="gmx-tabs" role="tablist">
                <div class="gmx-tab ${config.activeTab === 'main' ? 'active' : ''}" data-tab="main" title="General bot settings and modes">General</div>
                <div class="gmx-tab ${config.activeTab === 'movement' ? 'active' : ''}" data-tab="movement" title="Advanced movement modes">Move</div>
                <div class="gmx-tab ${config.activeTab === 'combat' ? 'active' : ''}" data-tab="combat" title="Combat assistance settings">Combat</div>
                <div class="gmx-tab ${config.activeTab === 'binds' ? 'active' : ''}" data-tab="binds" title="Configure keyboard shortcuts">Binds</div>
            </div>

            <div class="gmx-body">  <div class="gmx-page" data-tab="main" style="display:${config.activeTab === 'main' ? 'block' : 'none'}">
    <div class="gmx-row" style="border-bottom: 1px solid rgba(255,255,255,0.02); padding-bottom: 8px;">
        <button id="btn-follow" class="gmx-btn" style="flex:1;" title="Switches all bots to follow the player.">Follow</button>
        <button id="btn-stay" class="gmx-btn" style="flex:1;" title="Stops all bots.">Stay</button>
        <button id="btn-randommill" class="gmx-btn" style="flex:1;" title="Bots will move randomly, placing windmills.">RandomMill</button>
        <button id="btn-cursorfollow" class="gmx-btn" style="flex:1;" title="Switches all bots to follow the mouse cursor.">CursorFollow</button>
    </div>

    <div class="gmx-row" style="margin-top: 10px; flex-wrap:wrap; gap:6px;" title="Set limits per resource. 0 = ignore that resource. Bots farm until all non-zero limits are met, then follow you.">
        <label style="display:flex;align-items:center;gap:4px;font-size:12px;">Wood<input id="grind-wood" type="number" min="0" value="${(config.grindGoals&&config.grindGoals.wood!=null)?config.grindGoals.wood:2000}" style="width:72px;"></label>
        <label style="display:flex;align-items:center;gap:4px;font-size:12px;">Stone<input id="grind-stone" type="number" min="0" value="${(config.grindGoals&&config.grindGoals.stone!=null)?config.grindGoals.stone:2000}" style="width:72px;"></label>
        <label style="display:flex;align-items:center;gap:4px;font-size:12px;">Food<input id="grind-food" type="number" min="0" value="${(config.grindGoals&&config.grindGoals.food!=null)?config.grindGoals.food:500}" style="width:72px;"></label>
        <label style="display:flex;align-items:center;gap:4px;font-size:12px;">Gold<input id="grind-gold" type="number" min="0" value="${(config.grindGoals&&config.grindGoals.gold!=null)?config.grindGoals.gold:0}" style="width:72px;"></label>
        <button id="btn-grind" class="gmx-btn" style="flex:1;min-width:90px;" title="Farm all resources with limit > 0 until each quota is met, then follow.">Grinder</button>
    </div>

    <div class="gmx-grid" style="margin-top: 10px;">
        <button id="btn-ap" class="gmx-btn" title="Places one platform in the aim direction on left click with Manual Aim off, or on Sync Hit with Manual Aim on. If blocked, it uses the nearest open side.">AutoPlatform</button>
        <button id="btn-trap-animals" class="gmx-btn" title="Bots trap approaching hostile animals. Moofie, Moostafa and other trap-immune animals receive a spike. Uses a spike if a trap is unavailable. Neutral animals are ignored. Repeats only for a renewed attack or a different approach.">Trap Animals</button>
    </div>


</div>

                <div class="gmx-page" data-tab="movement" style="display:${config.activeTab === 'movement' ? 'block' : 'none'}">

    <div class="gmx-row" style="margin-top: 10px; border-top: 1px solid rgba(255,255,255,0.02); padding-top: 10px;">
        <span style="flex:2; padding: 0 10px; line-height: 28px; text-align: left; color: #ccc;" title="Sets the distance for the 'Follow' mode.">Follow Radius:</span>

        <input id="follow-radius" type="number" placeholder="Base distance (175)" value="${window.BOT_FOLLOW_RADIUS || 175}" style="flex:1;" title="Base follow distance. Nearby bots form a tight wedge behind you.">
    </div>

    <div class="gmx-row" style="border-bottom: 1px solid rgba(255,255,255,0.02); padding-bottom: 10px;">
        <select id="player-follow-target" style="flex:2;" title="Select player to follow.">
            <option value="" disabled selected>Select Player</option>
        </select>
        <input id="pf-distance" type="number" placeholder="Distance (175)" value="175" style="flex:1;" title="Distance to maintain from the target player.">
        <button id="btn-playerfollow" class="gmx-btn" style="flex:1;" title="Follow the selected player using bot pathfinding. Wait if the player is out of sight.">Follow Player</button>
    </div>

    <div class="gmx-row">
        <input id="circle-radius" type="number" placeholder="Radius (175)" value="175" style="flex:1;" title="Radius of circular movement (in pixels).">
        <button id="btn-circle" class="gmx-btn" style="flex:2;" title="Circular movement around the player.">Circle</button>
    </div>

    <div class="gmx-row">
        <button id="btn-surround" class="gmx-btn" style="flex:1;" title="Lock the nearest enemy to you and surround them using the Circle radius. Press again to follow you.">Surround Enemy</button>
    </div>

    <div class="gmx-row">
        <input id="cs-radius" type="number" placeholder="Radius (175)" value="175" style="flex:1;">
        <input id="cs-speed" type="number" placeholder="Speed (100)" value="100" style="flex:1;" title="Rotation speed (in degrees/tick).">
        <select id="cs-dir" style="flex:1;" title="Rotation direction."><option value="cw">CW</option><option value="ccw">CCW</option></select>
        <button id="btn-cs" class="gmx-btn" style="flex:2;" title="Circular movement with constant rotation.">CircleSpin</button>
    </div>

    <div class="gmx-row">
        <input id="sq-radius" type="number" placeholder="Radius (175)" value="175" style="flex:1;">
        <button id="btn-square" class="gmx-btn" style="flex:2;" title="Square movement around the player.">Square</button>
    </div>

    <div class="gmx-row">
        <input id="ssq-radius" type="number" placeholder="Radius (175)" value="175" style="flex:1;">
        <input id="ssq-speed" type="number" placeholder="Speed (1)" value="1" style="flex:1;" title="Square rotation speed.">
        <select id="ssq-dir" style="flex:1;"><option value="cw">CW</option><option value="ccw">CCW</option></select>
        <button id="btn-ssq" class="gmx-btn" style="flex:2;" title="Square movement with rotation.">SquareSpin</button>
    </div>
</div>

<div class="gmx-page" data-tab="combat" style="display:${config.activeTab === 'combat' ? 'block' : 'none'}">
    <div class="gmx-row">
        <button id="btn-autoshoot" class="gmx-btn" style="flex:1;" aria-pressed="false" title="Shoot visible enemy players. A platform clears low obstacles; held shields and tall obstacles still block shots.">Autoshoot</button>
    </div>
    <label class="gmx-row" style="align-items:center;justify-content:space-between;cursor:pointer;" title="Place a platform for Autoshoot. Wait for elevation before firing over low obstacles. Existing and pending platforms prevent repeated placement.">
        <span>AutoPlatform</span>
        <span class="gmx-check"><input id="autoshoot-platform" type="checkbox" aria-label="AutoPlatform for Autoshoot"><span class="gmx-check-track" aria-hidden="true"></span></span>
    </label>
    <div class="gmx-row" style="align-items:center;">
        <label for="autoshoot-range" style="white-space:nowrap;">Firing Range <output id="autoshoot-range-value">1400</output></label>
        <input id="autoshoot-range" type="range" min="100" max="1400" step="50" value="1400" style="flex:1;min-width:0;accent-color:#6eb6ff;" title="Maximum firing distance, limited by the equipped weapon's range.">
    </div>
    <div class="gmx-row">
        <button id="btn-autoplacer" class="gmx-btn" style="flex:1;" aria-pressed="false" title="Enable Colean Auto Placer for local bots independently of the player.">Auto Placer</button><button id="btn-botchat" class="gmx-btn" style="flex:1;" title="Bots repeat your chat when ON.">Bot Chat OFF</button>
    </div>
    <div class="gmx-row">
        <button id="btn-syncshot" class="gmx-btn" style="flex:1;" title="Uses Colean left-click auto aim for you and your bots, including while Manual Aim is enabled.">Sync Hit</button>
    </div>
    <div class="gmx-row">
        <button id="btn-botsync" class="gmx-btn" style="flex:1;" aria-pressed="true" title="ON: bots repeat your left/right click and autoattack. OFF: bots ignore your clicks and act on their own (autoshoot, autobreak, modules).">Sync ON</button>
    </div>
</div>

                <div class="gmx-page" data-tab="binds" style="display:${config.activeTab === 'binds' ? 'block' : 'none'}">
                    <div class="gmx-row" style="color: #ccc;">
                        <span style="flex: 1;">Action</span>
                        <span style="width: 80px; text-align: center;">Key</span>
                    </div>
                    <div id="keybinds-list">
                        </div>
                </div>

            </div> <div class="gmx-status"><span class="gmx-bubble" id="gmx-status-text">Ready</span></div>
            </div>
        `;
        document.body.appendChild(p);
        const launcher = document.createElement('button');
        launcher.id = 'colean-extra-launcher';
        launcher.textContent = 'Colean Bots Menu';
        launcher.style.cssText = 'position:fixed;right:18px;bottom:8px;z-index:2147482999;background:#0f1820;color:#c5d4e0;border:1px solid #2a5080;padding:6px 12px;cursor:pointer';
        launcher.onclick = () => toggle();
        document.body.appendChild(launcher);
        refreshMenuShortcut();
        makeDraggablePanel(p);
        populateKeybinds(p);


        // close button
        p.querySelector('.gmx-close').addEventListener('click', ()=> toggle(false));

        // tabs
        p.querySelectorAll('.gmx-tab').forEach(tabBtn => {
            tabBtn.addEventListener('click', () => {
                p.querySelectorAll('.gmx-tab').forEach(b=>b.classList.remove('active'));
                p.querySelectorAll('.gmx-page').forEach(pg=>pg.style.display='none');
                tabBtn.classList.add('active');
                const id = tabBtn.dataset.tab;
                config.activeTab = id;
                saveConfig();
                const page = p.querySelector(`.gmx-page[data-tab="${id}"]`);
                if(page) page.style.display = 'block';
                refreshToggles(p);
            });
        });

        // attach handlers
        attachExtraMenuHandlers(p);

        // start state refresh
        if (stateRefreshTimer) clearInterval(stateRefreshTimer);
        stateRefreshTimer = setInterval(()=> { if (isOpen) refreshToggles(p); }, 800);
        setTimeout(()=> refreshToggles(p), 60);
    }

    // ================= Keybinds Logic =================
    const actionToButtonId = {
        'follow': 'btn-follow',
        'stay': 'btn-stay',
        'randommill': 'btn-randommill',
        'cursorfollow': 'btn-cursorfollow',
        'grinder': 'btn-grind',
        'ap': 'btn-ap',
        'autoshoot': 'btn-autoshoot',
        'autoplacer': 'btn-autoplacer',
        'surround': 'btn-surround',
        'syncshot': 'btn-syncshot',
        'botsync': 'btn-botsync'
    };

    const formatKey = (key) => key.replace('Key', '').replace('Digit', '').replace('Arrow', '').replace('Numpad', 'N').replace('N', 'Numpad ').replace('Escape', 'ESC').replace('ShiftRight', 'R-Shift');
    let isCapturingKey = false;
    let currentKeybindActionId = null;
    let currentKeybindButton = null;

    function populateKeybinds(p) {
        const list = p.querySelector('#keybinds-list');
        if (!list) return;
        list.innerHTML = '';

        const allActions = {
            'Follow': 'follow',
            'Stay': 'stay',
            'RandomMill': 'randommill',
            'Follow Cursor': 'cursorfollow',
            'Grinder': 'grinder',
            'AutoPlatform': 'ap',
            'Autoshoot': 'autoshoot',
            'AutoPlacer': 'autoplacer',
            'Surround Enemy': 'surround',
            'SyncHit': 'syncshot',
            'Sync ON/OFF': 'botsync',
        };

        Object.keys(allActions).forEach(actionName => {
            const actionId = allActions[actionName];
            const key = Object.keys(config.keybinds).find(k => config.keybinds[k] === actionId);
            const keyDisplay = key ? formatKey(key) : 'Set';

            const item = document.createElement('div');
            item.className = 'gmx-list-item';
            item.innerHTML = `
                <span style="font-size: 14px;">${actionName}</span>
                <button class="gmx-key-btn" data-action="${actionId}" title="Click to bind key. Press ESC to clear.">${keyDisplay}</button>
            `;
            list.appendChild(item);
        });

        list.querySelectorAll('.gmx-key-btn').forEach(btn => {
            btn.addEventListener('click', (e) => startKeybindCapture(e, p));
        });
    }

    function stopKeybindCapture(p, reason='cancelled') {
        if (!isCapturingKey) return;

        document.removeEventListener('keydown', captureKey, { capture: true });

        if (currentKeybindButton) {
            // Restore the original key or 'Set'
            const currentKey = Object.keys(config.keybinds).find(k => config.keybinds[k] === currentKeybindActionId);
            currentKeybindButton.textContent = currentKey ? formatKey(currentKey) : 'Set';
            currentKeybindButton.classList.remove('active');
        }

        isCapturingKey = false;
        currentKeybindActionId = null;
        currentKeybindButton = null;

        if (reason === 'reset') panelFeedback(p, 'Keybind cleared.');
        else if (reason === 'cancelled') panelFeedback(p, 'Keybind setting cancelled.');
        else if (reason === 'keybind_set') panelFeedback(p, 'Keybind set successfully.');

        populateKeybinds(p);
    }

    function captureKey(e) {
        if (!isCapturingKey) return;

        e.preventDefault();
        e.stopImmediatePropagation();

        const p = document.getElementById(PANEL_ID);
        const actionId = currentKeybindActionId;
        const key = e.code;

        // --- ESCAPE LOGIC (RESET) ---
        if (key === 'Escape') {
            const oldKey = Object.keys(config.keybinds).find(k => config.keybinds[k] === actionId);
            if (oldKey) {
                delete config.keybinds[oldKey];
            }
            saveConfig();
            stopKeybindCapture(p, 'reset');
            return;
        }

        // Reserve the currently configured native shortcuts, including the menu toggle.
        if (Object.values(Settings_default).includes(key)) {
            panelFeedback(p, 'This key is used by Colean or the Extra menu');
            stopKeybindCapture(p, 'error');
            return;
        }

        // Delete old keybind for this KEY
        if (config.keybinds[key]) {
            delete config.keybinds[key];
        }

        // Delete old keybind for this ACTION
        const oldKey = Object.keys(config.keybinds).find(k => config.keybinds[k] === actionId);
        if (oldKey) {
            delete config.keybinds[oldKey];
        }

        // Set new keybind
        config.keybinds[key] = actionId;
        saveConfig();

        stopKeybindCapture(p, 'keybind_set');
    }

    function startKeybindCapture(e, p) {
        const btn = e.target;
        const actionId = btn.dataset.action;

        // Cancel if already capturing the same button
        if (isCapturingKey) {
            if (btn === currentKeybindButton) {
                stopKeybindCapture(p, 'cancelled');
                return;
            }
            stopKeybindCapture(p, 'cancelled');
        }

        isCapturingKey = true;
        currentKeybindActionId = actionId;
        currentKeybindButton = btn;

        btn.textContent = 'Press Key...';
        btn.classList.add('active');
        panelFeedback(p, `Press a key for ${actionId.toUpperCase()} or ESC to clear.`);

        // Remove previous listeners just in case
        document.removeEventListener('keydown', captureKey, { capture: true });
        // Add new listener
        document.addEventListener('keydown', captureKey, { capture: true });
    }
    // ================= End Keybinds Logic =================


    function makeDraggablePanel(panelElement) {
        const header = panelElement.querySelector('.gmx-header');
        if (!header) return;

        let isDragging = false;
        let offsetX = 0;
        let offsetY = 0;

        header.style.cursor = 'grab';

        header.addEventListener('mousedown', (e) => {
            isDragging = true;
            header.style.cursor = 'grabbing';
            const rect = panelElement.getBoundingClientRect();
            offsetX = e.clientX - rect.left;
            offsetY = e.clientY - rect.top;

            // Reset right/bottom for fixed position via top/left
            panelElement.style.left = `${rect.left}px`;
            panelElement.style.top = `${rect.top}px`;
            panelElement.style.right = 'auto';
            panelElement.style.bottom = 'auto';
            panelElement.style.position = 'fixed';
            panelElement.style.transition = 'none';

            document.body.style.userSelect = 'none';
        });

        document.addEventListener('mousemove', (e) => {
            if (!isDragging) return;
            panelElement.style.left = `${e.clientX - offsetX}px`;
            panelElement.style.top = `${e.clientY - offsetY}px`;
        });

        document.addEventListener('mouseup', () => {
            if (!isDragging) return;
            isDragging = false;
            header.style.cursor = 'grab';
            document.body.style.userSelect = '';

            // Save new position
            config.position.top = panelElement.style.top;
            config.position.left = panelElement.style.left;
            saveConfig();
        });
    }

    function panelFeedback(p, text, level='info'){
        try {
            const st = p.querySelector('#gmx-status-text');
            if (!st) return;
            st.textContent = text;
            p.classList.add('show-status');
            clearTimeout(p._fbTimeout);
            p._fbTimeout = setTimeout(()=>{ p.classList.remove('show-status'); }, 2200);
        } catch(e){ /* ignore */ }
    }

    function refreshToggles(p){
        try {
            // Note: If readOwnerCommanderField('all','mode') is undefined,
            // the system defaults to 'stay' which is usually the game's default uncommanded state.
            const mode = readOwnerCommanderField('all','mode') || 'stay';
            const ap = !!readOwnerCommanderField('all','apEnabled');
            const trapAnimals = !!readOwnerCommanderField('all','trapAnimals');
            const movementPage = p.querySelector('.gmx-page[data-tab="movement"]');
        if (movementPage && movementPage.style.display === 'block') {
            if (typeof populatePlayerList === 'function') {
                populatePlayerList(p);
            }
        }

            // Update toggle buttons
            toggleBtnActive(p.querySelector('#btn-ap'), ap);
            toggleBtnActive(p.querySelector('#btn-trap-animals'), trapAnimals);
            const botPlacer = p.querySelector('#btn-autoplacer');
            toggleBtnActive(botPlacer, Settings_default._botAutoPlacer);
            botPlacer?.setAttribute('aria-pressed', String(Settings_default._botAutoPlacer));
            const botChat = p.querySelector('#btn-botchat');
            if (botChat) {
                toggleBtnActive(botChat, !!Settings_default._botChatEcho);
                botChat.textContent = 'Bot Chat ' + (Settings_default._botChatEcho ? 'ON' : 'OFF');
                botChat.setAttribute('aria-pressed', String(!!Settings_default._botChatEcho));
            }

            const autoShoot = p.querySelector('#btn-autoshoot');
            toggleBtnActive(autoShoot, Settings_default._botAutoShoot);
            autoShoot?.setAttribute('aria-pressed', String(Settings_default._botAutoShoot));
            p.querySelector('#autoshoot-platform').checked = Settings_default._botAutoShootPlatform;
            p.querySelector('#autoshoot-range').value = BotAutoShoot.range();
            p.querySelector('#autoshoot-range-value').textContent = BotAutoShoot.range();
            const syncBtn = p.querySelector('#btn-botsync');
            toggleBtnActive(syncBtn, Settings_default._botSync);
            syncBtn.textContent = 'Sync ' + (Settings_default._botSync ? 'ON' : 'OFF');
            syncBtn.setAttribute('aria-pressed', String(Settings_default._botSync));

            // Update mode buttons
            p.querySelectorAll('.gmx-btn').forEach(btn => {
                const id = btn.id;
                let isActive = false;
                if (id === 'btn-follow' && mode === 'follow') isActive = true;
                else if (id === 'btn-stay' && mode === 'stay') isActive = true;
                else if (id === 'btn-randommill' && mode === 'randommill') isActive = true;
                else if (id === 'btn-grind' && mode === 'grinder') isActive = true;
                else if (id === 'btn-cursorfollow' && mode === 'cursorFollow') isActive = true;
                else if (id === 'btn-circle' && mode === 'circle') isActive = true;
                else if (id === 'btn-surround' && mode === 'surround') isActive = true;
                else if (id === 'btn-cs' && mode === 'circlespin') isActive = true;
                else if (id === 'btn-square' && mode === 'square') isActive = true;
                else if (id === 'btn-ssq' && mode === 'squarespin') isActive = true;
                else if (id === 'btn-playerfollow' && mode === 'playerFollow') isActive = true;

                // If it's a toggle button (already has .active class), don't touch data-mode-active
                if (!btn.classList.contains('active')) {
                   btn.setAttribute('data-mode-active', isActive);
                }
            });
        } catch(e){ /* ignore */ }
    }

    function toggleBtnActive(btn, on){
        if(!btn) return;
        if(on) btn.classList.add('active'); else btn.classList.remove('active');
    }

    function executeAction(actionId, p) {
        if (['instakill', 'bowinsta', 'bm', 'ba', 'bowspam'].includes(actionId)) return;
        if (actionId === 'btn-cursorfollow') actionId = 'cursorfollow';
        const id = actionToButtonId[actionId];
        if (id) p.querySelector('#' + id)?.click();
    }

    function populatePlayerList(p) {
        const select = p.querySelector('#player-follow-target');
        if (!select) return;
        const currentID = select.value || String(ExtraCommands.targetPlayerId ?? '');
        const players = BotFollowPlayers.list(client);
        const rows = [...players.values()].map(player => ({id:String(player.id), label:`${player.nickname || 'Player'} (ID: ${player.id})`}));
        rows.sort((a, b) => a.label.localeCompare(b.label));
        if (currentID && !players.has(Number(currentID))) rows.push({id:currentID, label:`Player (ID: ${currentID}) - Out of sight`});
        const signature = JSON.stringify(rows);
        // Keep the native dropdown open while its contents are unchanged.
        if (select.dataset.players === signature) return;
        select.dataset.players = signature;
        select.replaceChildren(new Option(rows.length ? 'Select Player' : 'No players found', ''));
        select.options[0].disabled = true;
        for (const row of rows) select.add(new Option(row.label, row.id));
        select.value = currentID;
        if (select.selectedIndex < 0) select.selectedIndex = 0;
    }

    function attachExtraMenuHandlers(p){
        p.querySelector('#player-follow-target').addEventListener('focus', () => populatePlayerList(p));
        p.querySelector('#btn-autoshoot').onclick = () => {
            Settings_default._botAutoShoot = !Settings_default._botAutoShoot;
            SaveSettings();
            animate(p.querySelector('#btn-autoshoot')); refreshToggles(p);
            panelFeedback(p, 'Autoshoot ' + (Settings_default._botAutoShoot ? 'ON' : 'OFF'));
        };
        p.querySelector('#autoshoot-range').oninput = event => {
            Settings_default._botAutoShootRange = Number(event.target.value);
            p.querySelector('#autoshoot-range-value').textContent = BotAutoShoot.range();
        };
        p.querySelector('#autoshoot-range').onchange = () => SaveSettings();
        p.querySelector('#autoshoot-platform').onchange = event => {
            Settings_default._botAutoShootPlatform = event.target.checked;
            SaveSettings();
            panelFeedback(p, 'Autoshoot AutoPlatform ' + (event.target.checked ? 'ON' : 'OFF'));
        };
        p.querySelector('#btn-autoplacer').onclick = () => {
            Settings_default._botAutoPlacer = !Settings_default._botAutoPlacer;
            SaveSettings();
            animate(p.querySelector('#btn-autoplacer')); refreshToggles(p);
            panelFeedback(p, 'Bot Auto Placer ' + (Settings_default._botAutoPlacer ? 'ON' : 'OFF'));
        };
        const botChatBtn = p.querySelector('#btn-botchat');
        if (botChatBtn) botChatBtn.onclick = () => {
            Settings_default._botChatEcho = !Settings_default._botChatEcho;
            SaveSettings();
            botChatBtn.textContent = 'Bot Chat ' + (Settings_default._botChatEcho ? 'ON' : 'OFF');
            animate(botChatBtn); refreshToggles(p);
            panelFeedback(p, 'Bot Chat Echo ' + (Settings_default._botChatEcho ? 'ON' : 'OFF'));
        };

        p.querySelector('#btn-botsync').onclick = () => {
            Settings_default._botSync = !Settings_default._botSync;
            SaveSettings();
            const owner = client._ModuleHandler;
            for (const bot of client.clients) {
                const h = bot._ModuleHandler;
                if (Settings_default._botSync) {
                    h.toggleAutoattack(owner.autoattack);
                    h.staticModules.tempData.setAttacking(owner.attacking);
                } else {
                    h.pointerAttack = 0;
                    h.pendingPointerAttack = 0;
                    h.autoattack = false;
                    h.attacking = 0;
                    h.attackingState = 0;
                }
            }
            animate(p.querySelector('#btn-botsync')); refreshToggles(p);
            panelFeedback(p, 'Sync ' + (Settings_default._botSync ? 'ON' : 'OFF'));
        };
        if (!p) return;
        const el = sel => p.querySelector(sel);

        const safeNum = (v, def)=> { const n = Number(v); return isNaN(n) ? def : n; };

        // lightweight animate
        const animate = (b) => { if(!b) return; b.classList.add('animate'); setTimeout(()=>b.classList.remove('animate'), 160); };

        // ================= COMMANDS =================
        // Main (Movement modes)
el('#follow-radius').onchange = () => {

    const newVal = Math.max(40, Math.min(1200, safeNum(el('#follow-radius')?.value, 175)));


    el('#follow-radius').value = newVal;


    window.BOT_FOLLOW_RADIUS = Math.max(80, Math.min(400, newVal));


    panelFeedback(p, `Follow Radius ${newVal} (Saved)`);


    if ((readOwnerCommanderField('all','mode') || 'stay') === 'follow') {

        setOwnerCommanderField('all','mode','follow');
        panelFeedback(p, `Follow Radius ${newVal} applied`);
    }
};

el('#btn-follow').onclick = () => {

    const r = Math.max(40, Math.min(1200, safeNum(el('#follow-radius')?.value, 175)));


    window.BOT_FOLLOW_RADIUS = Math.max(80, Math.min(400, r));


    setOwnerCommanderField('all','mode','follow');


    animate(el('#btn-follow'));
    refreshToggles(p);
    panelFeedback(p, `Follow (r=${r}) → all`);
};
        el('#btn-stay').onclick = () => {
            setOwnerCommanderField('all','mode','stay');
            animate(el('#btn-stay')); refreshToggles(p); panelFeedback(p, 'Stay → all');
        };
        el('#btn-randommill').onclick = () => {
            setOwnerCommanderField('all','mode','randommill');
            animate(el('#btn-randommill')); refreshToggles(p); panelFeedback(p, 'RandomMill → all');
        };

        // Toggles (Main)
        el('#btn-trap-animals').onclick = () => {
            const enabled = !readOwnerCommanderField('all', 'trapAnimals');
            setOwnerCommanderField('all', 'trapAnimals', enabled);
            animate(el('#btn-trap-animals')); refreshToggles(p);
            panelFeedback(p, 'Trap Animals ' + (enabled ? 'ON' : 'OFF') + ' → all');
        };
        el('#btn-ap').onclick = () => {
            const cur = !!readOwnerCommanderField('all','apEnabled');
            setOwnerCommanderField('all','apEnabled', !cur);
            animate(el('#btn-ap')); refreshToggles(p); panelFeedback(p, `AutoPlatform ${!cur ? 'ON' : 'OFF'} → all`);
        };



        // Combat


        el('#btn-syncshot').onclick = () => {
            const result = setOwnerCommanderField('all','syncShot', true);
            animate(el('#btn-syncshot')); panelFeedback(p, result.reason);
        };

        el('#btn-playerfollow') && (el('#btn-playerfollow').onclick = () => {
    const targetPlayerId = el('#player-follow-target')?.value;

    const distance = Math.max(40, Math.min(1200, safeNum(el('#pf-distance')?.value, 175)));

    if (!targetPlayerId) {
        panelFeedback(p, 'Please select a player to follow.');
        animate(el('#btn-playerfollow'));
        return;
    }

    setOwnerCommanderField('all', 'mode', 'playerFollow');

    setOwnerCommanderField('all', 'targetPlayerId', targetPlayerId);

    setOwnerCommanderField('all', 'followDistance', distance);

    animate(el('#btn-playerfollow'));
    refreshToggles(p);

    const targetText = el('#player-follow-target')?.options[el('#player-follow-target')?.selectedIndex]?.textContent || targetPlayerId;
    panelFeedback(p, `Follow Player ${targetText.split(' ')[0]} at ${distance} → all`);
});

        // Movement
        el('#circle-radius').onchange = () => {
            const radius = Math.max(40, Math.min(1200, safeNum(el('#circle-radius').value, 175)));
            el('#circle-radius').value = radius;
            if (['circle', 'surround'].includes(ExtraCommands.mode)) setOwnerCommanderField('all', 'circle', {radius});
        };
        el('#btn-surround').onclick = () => {
            if (ExtraCommands.mode === 'surround') {
                setOwnerCommanderField('all', 'mode', 'follow');
                animate(el('#btn-surround')); refreshToggles(p);
                panelFeedback(p, 'Surround Enemy OFF. Following you.');
                return;
            }
            const enemy = BotSurroundEnemy.nearest(client);
            if (!enemy) { panelFeedback(p, 'No visible enemy to surround.'); return; }
            const radius = Math.max(40, Math.min(1200, safeNum(el('#circle-radius')?.value, 175)));
            setOwnerCommanderField('all', 'surroundTargetId', enemy.id);
            setOwnerCommanderField('all', 'circle', {radius});
            setOwnerCommanderField('all', 'mode', 'surround');
            animate(el('#btn-surround')); refreshToggles(p);
            panelFeedback(p, `Surround Enemy: ${enemy.nickname || 'Player'} (ID: ${enemy.id}), radius ${radius}.`);
        };
        el('#btn-circle') && (el('#btn-circle').onclick = () => {
            const r = Math.max(40, Math.min(1200, safeNum(el('#circle-radius')?.value, 175)));
            setOwnerCommanderField('all','mode','circle');
            setOwnerCommanderField('all','circle',{ radius: r });
            animate(el('#btn-circle')); refreshToggles(p); panelFeedback(p, `Circle r=${r} → all`);
        });

        el('#btn-cs') && (el('#btn-cs').onclick = () => {
            const r = Math.max(40, Math.min(1200, safeNum(el('#cs-radius')?.value, 175)));
            const s = Math.max(0.5, safeNum(el('#cs-speed')?.value, 100));
            const d = (el('#cs-dir')?.value || 'cw').toLowerCase();
            const dir = (d === 'ccw' || d === 'left' || d === '-') ? -1 : 1;
            setOwnerCommanderField('all','mode','circlespin');
            setOwnerCommanderField('all','circle',{ radius: r });
            setOwnerCommanderField('all','spin',{ speed: s * Math.PI / 180, dir });
            animate(el('#btn-cs')); refreshToggles(p); panelFeedback(p, `CircleSpin r=${r} s=${s} dir=${d} → all`);
        });

        el('#btn-square') && (el('#btn-square').onclick = () => {
            const r = Math.max(40, Math.min(1200, safeNum(el('#sq-radius')?.value, 175)));
            setOwnerCommanderField('all','mode','square');
            setOwnerCommanderField('all','square',{ radius: r });
            animate(el('#btn-square')); refreshToggles(p); panelFeedback(p, `Square r=${r} → all`);
        });

        el('#btn-ssq') && (el('#btn-ssq').onclick = () => {
            const r = Math.max(40, Math.min(1200, safeNum(el('#ssq-radius')?.value, 175)));
            const sp = Math.max(0.1, safeNum(el('#ssq-speed')?.value, 1));
            const d = (el('#ssq-dir')?.value || 'cw').toLowerCase();
            const dir = (d === 'ccw' || d === 'left' || d === '-') ? -1 : 1;
            setOwnerCommanderField('all','mode','squarespin');
            setOwnerCommanderField('all','square',{ radius: r });
            setOwnerCommanderField('all','spin',{ speed: sp, dir });
            animate(el('#btn-ssq')); refreshToggles(p); panelFeedback(p, `SquareSpin r=${r} s=${sp} dir=${d} → all`);
        });

        const readGrindGoals = () => {
            const goals = {
                wood: Math.max(0, safeNum(el('#grind-wood')?.value, 0)),
                stone: Math.max(0, safeNum(el('#grind-stone')?.value, 0)),
                food: Math.max(0, safeNum(el('#grind-food')?.value, 0)),
                gold: Math.max(0, safeNum(el('#grind-gold')?.value, 0))
            };
            config.grindGoals = goals;
            saveConfig();
            return goals;
        };
        for (const id of ['#grind-wood', '#grind-stone', '#grind-food', '#grind-gold']) {
            el(id) && (el(id).onchange = () => {
                const goals = readGrindGoals();
                panelFeedback(p, `Grind goals: W${goals.wood} S${goals.stone} F${goals.food} G${goals.gold}`);
                if ((readOwnerCommanderField('all','mode') || '') === 'grinder') {
                    setOwnerCommanderField('all', 'grinder', { goals });
                }
            });
        }

        el('#btn-grind').onclick = () => {
            const goals = readGrindGoals();
            const active = Object.entries(goals).filter(([, v]) => v > 0).map(([k, v]) => `${k}:${v}`).join(', ') || 'none';
            setOwnerCommanderField('all','mode','grinder');
            setOwnerCommanderField('all','grinder',{ goals });
            animate(el('#btn-grind')); refreshToggles(p);
            panelFeedback(p, `Grinder multi → ${active}`);
        };

        // Commands (Chat/Clan)
        el('#btn-cursorfollow').onclick = () => {
            setOwnerCommanderField('all','mode','cursorFollow');
            animate(el('#btn-cursorfollow')); refreshToggles(p); panelFeedback(p, 'CursorFollow → all');
        };



        console.log('[ExtraMenu] handlers attached (all→ownerCommander)');
    }

    function toggle(force){
        const el = document.getElementById(PANEL_ID);
        if (!el) return;
        if (typeof force === 'boolean') isOpen = force; else isOpen = !isOpen;

        if (isOpen) {
            el.classList.add('open');
            refreshToggles(el);
            // Cancel key capture on open/close
            stopKeybindCapture(el, 'cancelled');
        } else {
            el.classList.remove('open');
            stopKeybindCapture(el, 'cancelled');
        }
    }

    function refreshMenuShortcut() {
        const key = Settings_default._toggleBotsMenu;
        const label = key && key !== '...' ? ` (${formatCode(key)})` : '';
        const shortcut = document.querySelector(`#${PANEL_ID} .gmx-menu-shortcut`);
        if (shortcut) shortcut.textContent = label.trim();
        const launcher = document.getElementById('colean-extra-launcher');
        if (launcher) launcher.textContent = `Colean Bots Menu${label}`;
    }

    window.addEventListener('colean-settings-changed', refreshMenuShortcut);

    // hotkey handler
    window.addEventListener('keydown', (e)=> {
    if (isCapturingKey) { captureKey(e); return; }
    if (UI_default.isActiveButton()) return;
    const a = document.activeElement;
    const tag = a && a.tagName ? a.tagName.toLowerCase() : '';
    const isInput = tag === 'input' || tag === 'textarea' || tag === 'select' || a?.isContentEditable;

    if (Settings_default._toggleBotsMenu !== '...' && e.code === Settings_default._toggleBotsMenu && !e.repeat) {
        if (isInput) return;
        buildPanel();
        toggle();
        e.preventDefault();
        e.stopImmediatePropagation();
        return;
    }

        // Handle custom hotkeys
        if (!isInput && !isCapturingKey && !e.repeat && !Object.values(Settings_default).includes(e.code)) {
            const actionId = config.keybinds[e.code];
            if (actionId) {
                buildPanel();
                executeAction(actionId, document.getElementById(PANEL_ID));
                e.preventDefault();
                e.stopImmediatePropagation();
            }
        }
    }, true);

    // initial build
    if (document.readyState === 'complete' || document.readyState === 'interactive') setTimeout(buildPanel, 120);
    else document.addEventListener('DOMContentLoaded', buildPanel, { once:true });


})();


    resetGame_default(loadedFast);

    const contentLoaded = () => {
        Logger.test("Menu initialization..");
        client.InputHandler.init();
        GameUI_default.init();
        UI_default.init();
        StoreHandler_default.init();
    };

    window.addEventListener("DOMContentLoaded", contentLoaded);

    if (document.readyState !== "loading") {
        contentLoaded();
    }

    const onload = () => {
        Logger.test("Page loaded..");
        const {enterGame: enterGame} = GameUI_default.getElements();
        enterGame.classList.remove("disabled");
    };

    window.addEventListener("load", onload);

    if (document.readyState === "complete") {
        onload();
    }
})();