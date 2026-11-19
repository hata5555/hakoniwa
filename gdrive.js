/* gdrive.js — GitHub版で使う保存の仕組み（claude.ai の中では何もしない）
   ・データ：この端末（IndexedDB）にすぐ保存 → Google Drive の data.json に同期する
     （キャラ1人・メモ1件…のように1件ずつ「新しい方が勝つ」でまとめるので、iPhoneとiPadで別々に書いても混ざる）
   ・画像・PDF：原本を Drive に置いて、アプリが決めたフォルダへ自動で仕分ける。ほかの場所で使う分はショートカット
   ・読める写し：キャラのタブごとなどに .txt を自動で書き出す
   ・バックアップ：data.json の写しを毎日1つ、14日分残す */
(() => {
'use strict';
if (window.claude) return;                                  /* claude.ai の中 */
if (!/^https?:$/.test(location.protocol) || location.origin === 'null') return;
if (/(^|\.)(claude\.ai|claudeusercontent\.com|anthropic\.com)$/.test(location.hostname)) return;

const CFG = Object.assign({
  clientId: '',
  rootName: '創作の設定置き場',
  apiBase: 'https://www.googleapis.com',
  gisSrc: 'https://accounts.google.com/gsi/client',
  scope: 'https://www.googleapis.com/auth/drive.file'
}, window.GDRIVE_CONFIG || {});

const LOCAL_COLS = new Set(['thumbs', 'views', 'viewparts']);   /* 表示用の小さい写し：端末の中だけ（原本から作り直せる） */
const FOLDER = 'application/vnd.google-apps.folder';
const SHORTCUT = 'application/vnd.google-apps.shortcut';
const GRACE = 3 * 864e5;              /* どこからも使われなくなってから、ゴミ箱に入れるまで */
const FILE_FORMAT = 1;                /* data.json の書き方の版 */
const CACHE_CAP = 300 * 1048576;      /* 端末に置いておく原本の写しの上限 */
const TOMB_KEEP = 90 * 864e5;         /* 消した印を残しておく期間 */

/* ---------- 小物 ---------- */
const sleep = ms => new Promise(r => setTimeout(r, ms));
const cloneJ = o => o === undefined ? undefined : JSON.parse(JSON.stringify(o));
const colOf = p => p.slice(0, p.lastIndexOf('/'));
const topCol = p => p.split('/')[0];
const idOf = p => p.slice(p.lastIndexOf('/') + 1);
const pad = n => String(n).padStart(2, '0');
const today = () => { const d = new Date(); return `${d.getFullYear()}-${pad(d.getMonth() + 1)}-${pad(d.getDate())}`; };
function rid(n){ const cs = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789'; const a = new Uint8Array(n); crypto.getRandomValues(a); let s = ''; for (const b of a) s += cs[b % cs.length]; return s; }
function hstr(s){ let a = 0x811c9dc5, b = 0x01000193 ^ s.length; for (let i = 0; i < s.length; i++) { const c = s.charCodeAt(i); a = Math.imul(a ^ c, 16777619); b = Math.imul(b ^ c, 2246822507); } return (a >>> 0).toString(36) + (b >>> 0).toString(36); }
const qs = s => "'" + String(s).replace(/\\/g, '\\\\').replace(/'/g, "\\'") + "'";
function safeName(s){ const t = String(s == null ? '' : s).replace(/[\/\\]/g, '／').replace(/[\u0000-\u001f]/g, ' ').trim().slice(0, 100); return t || '名前なし'; }
const EXT = {'image/jpeg': '.jpg', 'image/png': '.png', 'image/webp': '.webp', 'image/gif': '.gif', 'image/heic': '.heic', 'application/pdf': '.pdf', 'text/plain': '.txt'};
const extOf = (mime, given) => given != null ? given : (EXT[String(mime || '').split(';')[0]] || '');
const dirKey = chain => chain.map(s => s.key).join('/');

/* ---------- IndexedDB ---------- */
let idbP = null;
function idb(){
  return idbP || (idbP = new Promise((res, rej) => {
    const r = indexedDB.open('settei-drive', 1);
    r.onupgradeneeded = () => { const d = r.result; for (const s of ['docs', 'cache', 'blobs', 'kv']) if (!d.objectStoreNames.contains(s)) d.createObjectStore(s); };
    r.onsuccess = () => res(r.result); r.onerror = () => rej(r.error);
  }));
}
const reqP = r => new Promise((res, rej) => { r.onsuccess = () => res(r.result); r.onerror = () => rej(r.error); });
const txDone = t => new Promise((res, rej) => { t.oncomplete = () => res(); t.onerror = () => rej(t.error); t.onabort = () => rej(t.error || new Error('abort')); });
async function idbGet(store, key){ const d = await idb(); return reqP(d.transaction(store).objectStore(store).get(key)); }
async function idbPut(store, key, val){ const d = await idb(); const t = d.transaction(store, 'readwrite'); t.objectStore(store).put(val, key); return txDone(t); }
async function idbDel(store, key){ const d = await idb(); const t = d.transaction(store, 'readwrite'); t.objectStore(store).delete(key); return txDone(t); }
async function idbAll(store){
  const d = await idb(); const out = [];
  await new Promise((res, rej) => { const r = d.transaction(store).objectStore(store).openCursor(); r.onsuccess = () => { const c = r.result; if (!c) return res(); out.push([c.key, c.value]); c.continue(); }; r.onerror = () => rej(r.error); });
  return out;
}
const quotaErr = e => { const x = new Error('この端末の保存領域がいっぱい'); x.code = 'quota_exceeded'; x.cause = e; return x; };

/* ---------- 端末の中の状態 ---------- */
let KV = {};
let kvT = 0;
function saveKV(){ clearTimeout(kvT); kvT = setTimeout(() => idbPut('kv', 'state', KV).catch(() => {}), 150); }
const DOCS = new Map();                 /* path → {v, t, d?, u?}   u = まだDriveに送ってない */
let lastStamp = 0;
const stamp = () => (lastStamp = Math.max(Date.now(), lastStamp + 1));
const persistQ = new Set(); let persistT = 0;
function persist(p){ persistQ.add(p); clearTimeout(persistT); persistT = setTimeout(flushPersist, 120); }
async function flushPersist(){
  clearTimeout(persistT); if (!persistQ.size) return;
  const ps = [...persistQ]; persistQ.clear();
  try { const d = await idb(); const t = d.transaction('docs', 'readwrite'); const s = t.objectStore('docs'); for (const p of ps) { const e = DOCS.get(p); if (e) s.put(e, p); else s.delete(p); } await txDone(t); }
  catch(e){ ps.forEach(p => persistQ.add(p)); toastErr('この端末に保存できなかった（容量がいっぱいかも）'); }
}
async function loadLocal(){
  try { KV = (await idbGet('kv', 'state')) || {}; } catch(e){ KV = {}; }
  if (!KV.deviceId) { KV.deviceId = rid(12); saveKV(); }
  for (const [p, e] of await idbAll('docs')) { DOCS.set(p, e); if (e.t > lastStamp) lastStamp = e.t; }
  for (const [id, rec] of await idbAll('blobs')) if (rec && rec.pending) PENDING.add(id);
}

/* ---------- アプリから見える db（Firestore っぽい形） ---------- */
const listeners = new Set();
function snapDoc(path, e){ const live = !!e && !e.d; const v = live ? e.v : undefined; return {id: idOf(path), exists: live, data: () => cloneJ(v), metadata: {fromCache: false, hasPendingWrites: false}}; }
function querySnap(col, changes){
  const docs = [...DOCS.keys()].filter(p => colOf(p) === col && !DOCS.get(p).d).sort().map(p => snapDoc(p, DOCS.get(p)));
  return {docs, size: docs.length, empty: !docs.length, docChanges: () => changes, metadata: {fromCache: false, hasPendingWrites: false}};
}
/* changes: Map path → {type, old} */
function emit(changes){
  if (!changes.size) return;
  const byCol = new Map();
  for (const [p, ch] of changes) { const c = colOf(p); if (!byCol.has(c)) byCol.set(c, []); byCol.get(c).push({type: ch.type, doc: ch.type === 'removed' ? snapDoc(p, {v: ch.old, t: 0}) : snapDoc(p, DOCS.get(p)), oldIndex: -1, newIndex: -1}); }
  setTimeout(() => {
    for (const l of [...listeners]) {
      if (l.kind === 'col' && byCol.has(l.col)) { try { l.next(querySnap(l.col, byCol.get(l.col))); } catch(e){ console.error(e); } }
      if (l.kind === 'doc' && changes.has(l.path)) { try { l.next(snapDoc(l.path, DOCS.get(l.path))); } catch(e){ console.error(e); } }
    }
  }, 0);
}
function writeLocal(path, v, internal){
  const prev = DOCS.get(path);
  DOCS.set(path, {v: cloneJ(v), t: stamp(), u: 1}); persist(path);
  if (!internal) emit(new Map([[path, {type: prev && !prev.d ? 'modified' : 'added'}]]));
  onLocalChange(path);
}
function deleteLocal(path, internal){
  const prev = DOCS.get(path); if (!prev || prev.d) return;
  DOCS.set(path, {t: stamp(), d: 1, u: 1}); persist(path);
  if (!internal) emit(new Map([[path, {type: 'removed', old: prev.v}]]));
  onLocalChange(path);
}
const docOf = p => { const e = DOCS.get(p); return e && !e.d ? e.v : null; };
const docRef = path => ({
  id: idOf(path), path,
  async get(){
    if (LOCAL_COLS.has(topCol(path))) { const v = await idbGet('cache', path); return snapDoc(path, v === undefined ? null : {v, t: 0}); }
    return snapDoc(path, DOCS.get(path));
  },
  async set(data){
    if (LOCAL_COLS.has(topCol(path))) { try { await idbPut('cache', path, cloneJ(data)); } catch(e){ throw quotaErr(e); } return; }
    writeLocal(path, data);
  },
  async update(data){ const cur = docOf(path); if (!cur) throw {code: 'not_found'}; writeLocal(path, Object.assign(cloneJ(cur), cloneJ(data))); },
  async delete(){
    if (LOCAL_COLS.has(topCol(path))) { await idbDel('cache', path).catch(() => {}); return; }
    deleteLocal(path);
  },
  onSnapshot(next){ const l = {kind: 'doc', path, next}; listeners.add(l); setTimeout(() => next(snapDoc(path, DOCS.get(path))), 0); return () => listeners.delete(l); },
  collection: sub => colRef(path + '/' + sub)
});
const colRef = col => ({
  path: col,
  doc: id => docRef(col + '/' + (id || rid(20))),
  onSnapshot(next){
    const l = {kind: 'col', col, next}; listeners.add(l);
    setTimeout(() => next(querySnap(col, [...DOCS.keys()].filter(p => colOf(p) === col && !DOCS.get(p).d).sort().map(p => ({type: 'added', doc: snapDoc(p, DOCS.get(p)), oldIndex: -1, newIndex: 0})))), 0);
    return () => listeners.delete(l);
  },
  async get(){ return querySnap(col, []); }
});

/* ---------- 状態の知らせ（アプリの右上の表示に使う） ---------- */
const ST = {mode: 'init', err: '', busy: false};
function setState(mode, err){
  if (mode) ST.mode = mode;
  if (err !== undefined) ST.err = err;
  const detail = {mode: ST.mode, err: ST.err, busy: !!(syncing || reconciling || pumping), pending: PENDING.size, lastSync: KV.lastSync || 0, email: KV.account || KV.email || '', connected: tokenValid(), rootId: KV.rootId || ''};
  try { window.dispatchEvent(new CustomEvent('gdrive-state', {detail})); } catch(e){}
}
function toastErr(msg){ try { window.dispatchEvent(new CustomEvent('gdrive-toast', {detail: msg})); } catch(e){} }

/* ---------- Google ログイン ---------- */
const AUTH = {token: null, exp: 0, acct: '', acctTok: ''};
const tokenValid = () => !!AUTH.token && Date.now() < AUTH.exp - 60000;
function loadToken(){ try { const o = JSON.parse(localStorage.getItem('gd_tok') || 'null'); if (o && o.exp > Date.now() + 60000) { AUTH.token = o.t; AUTH.exp = o.exp; if (o.a) { AUTH.acct = o.a; AUTH.acctTok = o.t; } } } catch(e){} }
function saveToken(){ try { if (AUTH.token) localStorage.setItem('gd_tok', JSON.stringify({t: AUTH.token, exp: AUTH.exp, a: AUTH.acctTok === AUTH.token ? AUTH.acct : ''})); else localStorage.removeItem('gd_tok'); } catch(e){} }
let gisP = null;
function loadGis(){
  if (window.google && google.accounts && google.accounts.oauth2) return Promise.resolve();
  return gisP || (gisP = new Promise((res, rej) => {
    const s = document.createElement('script'); s.src = CFG.gisSrc; s.async = true;
    s.onload = () => res(); s.onerror = () => { gisP = null; rej(new Error('Googleのログイン部品を読み込めなかった')); };
    document.head.appendChild(s);
  }));
}
let tokenClient = null;
/* ボタンを押した流れの中で呼ぶ（ポップアップが止められないように） */
function connect(){
  return new Promise((res, rej) => {
    if (!CFG.clientId) { rej(new Error('config.js にクライアントIDが入ってない')); return; }
    const go = () => {
      try {
        tokenClient = google.accounts.oauth2.initTokenClient({
          client_id: CFG.clientId, scope: CFG.scope, prompt: '', login_hint: KV.email || undefined,
          callback: r => {
            if (r && r.access_token) { AUTH.token = r.access_token; AUTH.exp = Date.now() + (Number(r.expires_in) || 3600) * 1000; saveToken(); setState(); res(true); after(); }
            else rej(new Error((r && (r.error_description || r.error)) || 'ログインできなかった'));
          },
          error_callback: e => rej(new Error(e && e.type === 'popup_closed' ? 'ログインの画面が閉じられた' : (e && (e.message || e.type)) || 'ログインできなかった'))
        });
        tokenClient.requestAccessToken();
      } catch(e){ rej(e); }
    };
    if (window.google && google.accounts && google.accounts.oauth2) go();
    else loadGis().then(go, rej);
  });
  function after(){ sync(); pumpUploads(); scheduleReconcile(4000); }
}
async function fetchAbout(){
  const r = await api('GET', 'about', {query: {fields: 'user(displayName,emailAddress),storageQuota(limit,usage)'}});
  const em = (r.user && r.user.emailAddress) || '';
  AUTH.acct = em; AUTH.acctTok = AUTH.token; saveToken();
  KV.name = (r.user && r.user.displayName) || ''; KV.quota = r.storageQuota || null; saveKV(); setState();
  return em;
}
/* この端末のデータが、今ログインしているアカウントのものか確かめる。
   ちがうアカウントのDriveに、前の人のデータを送ってしまわないため */
let acctP = null;
function ensureAccount(){
  if (AUTH.acct && AUTH.acctTok === AUTH.token) return Promise.resolve(checkAcct());
  return acctP || (acctP = fetchAbout().then(() => checkAcct()).finally(() => { acctP = null; }));
}
function checkAcct(){
  const em = AUTH.acct;
  if (!em) { const e = new Error('アカウントを確かめられなかった'); e.code = 'net'; throw e; }
  if (!KV.account) { KV.account = em; KV.email = em; saveKV(); return; }
  if (KV.account === em) { if (KV.email !== em) { KV.email = em; saveKV(); } return; }
  const e = new Error('別のGoogleアカウントでログインしてる'); e.code = 'account'; e.email = em; throw e;
}
let switchShown = false;
function switchPrompt(em){
  if (switchShown) return; switchShown = true;
  try { if (typeof flushAll === 'function') flushAll(); } catch(e){}   /* アプリの中で保存待ちの分も数える */
  const unsent = [...DOCS.values()].filter(e => e.u).length + PENDING.size;
  const el = document.createElement('div'); el.id = 'gdSwitch';
  el.innerHTML = `<style>
    #gdSwitch{position:fixed;inset:0;z-index:99999;display:flex;align-items:center;justify-content:center;padding:20px;background:rgba(0,0,0,.5);font-family:-apple-system,BlinkMacSystemFont,"Hiragino Sans","Noto Sans JP",sans-serif}
    #gdSwitch .bx{max-width:380px;width:100%;background:#fffdf8;color:#2a241c;border-radius:18px;padding:20px}
    @media (prefers-color-scheme:dark){#gdSwitch .bx{background:#2a2622;color:#efe7da}}
    #gdSwitch h2{font-size:17px;margin:0 0 10px}
    #gdSwitch p{font-size:14px;line-height:1.7;margin:0 0 10px}
    #gdSwitch .w{color:#b33}
    #gdSwitch button{display:block;width:100%;font:inherit;font-size:15px;font-weight:700;padding:12px;border-radius:12px;border:1px solid #d8cdbb;background:transparent;color:inherit;margin-top:8px}
    #gdSwitch button.p{background:#7a2e2e;color:#fff;border-color:#7a2e2e}
  </style><div class="bx"><h2>別のGoogleアカウントでログインした</h2>
    <p>この端末には <b></b> のデータが入ってる。<br>今ログインしたのは <b></b>。</p>
    ${unsent ? `<p class="w">${KV.account} でまだDriveに送れてない変更が ${unsent}件ある。切り替えると、その分は消える。先に元のアカウントでつなぎ直して送るのがおすすめ。</p>` : ''}
    <button data-x="keep">元のアカウントのままにする</button>
    <button class="p" data-x="switch">今のアカウントに切り替える</button>
    <p style="font-size:12px;opacity:.7;margin-top:10px">切り替えると、この端末の中身を入れ替えて、今のアカウントのDriveから読み込み直す。元のアカウントのDriveのデータはそのまま残る。</p></div>`;
  const bs = el.querySelectorAll('b'); bs[0].textContent = KV.account; bs[1].textContent = em;
  el.addEventListener('click', async ev => {
    const x = ev.target.closest('[data-x]'); if (!x) return;
    if (x.dataset.x === 'keep') { el.remove(); switchShown = false; signOut(); toastErr('ログアウトした。' + KV.account + ' でつなぎ直してね'); return; }
    x.disabled = true; x.textContent = '切り替えてる…';
    await wipeLocal(); location.reload();
  });
  document.body.appendChild(el);
}
async function wipeLocal(){
  const keep = KV.deviceId;
  try { const d = await idb(); const t = d.transaction(['docs', 'cache', 'blobs', 'kv'], 'readwrite'); for (const st of ['docs', 'cache', 'blobs', 'kv']) t.objectStore(st).clear(); t.objectStore('kv').put({deviceId: keep}, 'state'); await txDone(t); } catch(e){}
  clearTimeout(kvT); clearTimeout(persistT); persistQ.clear(); KV = {deviceId: keep}; DOCS.clear(); PENDING.clear();
}
function signOut(){
  try { if (AUTH.token && window.google && google.accounts && google.accounts.oauth2) google.accounts.oauth2.revoke(AUTH.token, () => {}); } catch(e){}
  AUTH.token = null; AUTH.exp = 0; saveToken(); setState('auth');
}

/* ---------- Drive の API ---------- */
function authErr(){ const e = new Error('Googleにつなぎ直してね'); e.code = 'auth'; return e; }
async function api(method, path, opt = {}){
  const url = new URL((opt.upload ? CFG.apiBase + '/upload/drive/v3/' : CFG.apiBase + '/drive/v3/') + path);
  for (const [k, v] of Object.entries(opt.query || {})) if (v != null && v !== '') url.searchParams.set(k, v);
  for (let k = 0; ; k++) {
    if (!tokenValid()) { setState('auth'); throw authErr(); }
    let r;
    try { r = await fetch(url, {method, headers: Object.assign({Authorization: 'Bearer ' + AUTH.token}, opt.headers || {}), body: opt.body}); }
    catch(e){ if (k < 3 && navigator.onLine) { await sleep(800 * (k + 1)); continue; } const x = new Error('ネットにつながらない'); x.code = 'net'; throw x; }
    if (r.status === 401) { AUTH.token = null; saveToken(); setState('auth'); throw authErr(); }
    if (!r.ok) {
      const txt = await r.text().catch(() => '');
      if ((r.status === 429 || r.status >= 500 || (r.status === 403 && /rateLimit|userRateLimit/i.test(txt))) && k < 4) { await sleep(1000 * 2 ** k + Math.random() * 400); continue; }
      const e = new Error('Drive ' + r.status + ' ' + txt.slice(0, 160)); e.status = r.status;
      if (r.status === 403 && /storageQuota/i.test(txt)) e.code = 'quota';
      throw e;
    }
    if (opt.raw) return r;
    if (r.status === 204) return null;
    const t = await r.text(); return t ? JSON.parse(t) : null;
  }
}
const J = {'Content-Type': 'application/json; charset=UTF-8'};
const FIELDS = 'id,name,mimeType,parents,version,trashed,appProperties';
async function listFiles(q){
  const out = []; let pt = null;
  do { const r = await api('GET', 'files', {query: {q, fields: 'nextPageToken,files(' + FIELDS + ')', pageSize: 1000, pageToken: pt, spaces: 'drive'}}); out.push(...(r.files || [])); pt = r.nextPageToken; } while (pt);
  return out;
}
const byProp = async (k, v, parent) => (await listFiles(`${parent ? qs(parent) + ' in parents and ' : ''}appProperties has { key='${k}' and value=${qs(v)} } and trashed=false`))[0] || null;
const createMeta = meta => api('POST', 'files', {query: {fields: FIELDS}, headers: J, body: JSON.stringify(meta)});
const patchMeta = (id, meta, q) => api('PATCH', 'files/' + id, {query: Object.assign({fields: FIELDS}, q || {}), headers: J, body: JSON.stringify(meta || {})});
const trash = id => patchMeta(id, {trashed: true});
async function uploadNew(blob, meta){
  if (blob.size > 4.5e6) return uploadResumable(blob, meta);
  const b = 'gd' + rid(16), mime = meta.mimeType || blob.type || 'application/octet-stream';
  const body = new Blob([`--${b}\r\nContent-Type: application/json; charset=UTF-8\r\n\r\n${JSON.stringify(meta)}\r\n--${b}\r\nContent-Type: ${mime}\r\n\r\n`, blob, `\r\n--${b}--`]);
  return api('POST', 'files', {upload: true, query: {uploadType: 'multipart', fields: FIELDS}, headers: {'Content-Type': 'multipart/related; boundary=' + b}, body});
}
async function uploadResumable(blob, meta){
  const mime = meta.mimeType || blob.type || 'application/octet-stream';
  const r = await api('POST', 'files', {upload: true, raw: true, query: {uploadType: 'resumable', fields: FIELDS}, headers: Object.assign({'X-Upload-Content-Type': mime}, J), body: JSON.stringify(meta)});
  const loc = r.headers.get('Location') || r.headers.get('location'); if (!loc) throw new Error('アップロードの場所がもらえなかった');
  for (let k = 0; ; k++) {
    try { const r2 = await fetch(loc, {method: 'PUT', headers: {'Content-Type': mime}, body: blob}); if (r2.ok) return r2.json(); if (r2.status < 500 || k >= 3) throw new Error('Drive ' + r2.status); }
    catch(e){ if (k >= 3) throw e; }
    await sleep(1500 * (k + 1));
  }
}
const putContent = (id, blob, mime) => api('PATCH', 'files/' + id, {upload: true, query: {uploadType: 'media', fields: FIELDS}, headers: {'Content-Type': mime || blob.type || 'application/octet-stream'}, body: blob});
async function moveFile(id, folder, name){
  const cur = await api('GET', 'files/' + id, {query: {fields: 'parents,name,trashed'}});
  const ps = cur.parents || [];
  const meta = name != null ? {name} : {}; if (cur.trashed) meta.trashed = false;
  return patchMeta(id, meta, {addParents: ps.includes(folder) ? null : folder, removeParents: ps.filter(x => x !== folder).join(',') || null});
}

/* ---------- Drive の置き場所の準備 ---------- */
let rootP = null;
function ensureRoot(){
  if (KV.rootId && KV.dataDirId && KV.bkDirId && KV.inboxId) return Promise.resolve();
  return rootP || (rootP = ensureRootNow().finally(() => { rootP = null; }));
}
async function ensureRootNow(){
  let root = await byProp('sk', 'root');
  if (!root) root = await createMeta({name: CFG.rootName, mimeType: FOLDER, appProperties: {sk: 'root'}});
  KV.rootId = root.id;
  const sub = async (sk, name, parent) => (await byProp('sk', sk)) || createMeta({name, mimeType: FOLDER, parents: [parent], appProperties: {sk}});
  KV.dataDirId = (await sub('datadir', 'データ（さわらない）', KV.rootId)).id;
  KV.bkDirId = (await sub('backup', 'バックアップ', KV.dataDirId)).id;
  KV.inboxId = (await sub('inbox', '_整理待ち', KV.rootId)).id;
  const df = await byProp('sk', 'data'); KV.dataId = df ? df.id : null; KV.dataVer = null;
  saveKV();
}

/* ---------- 同期 ---------- */
let syncing = null, syncAgain = false, syncT = 0;
function scheduleSync(ms = 2500){ clearTimeout(syncT); syncT = setTimeout(() => sync(), ms); }
function sync(){
  if (syncing) { syncAgain = true; return syncing; }
  syncing = (async () => {
    try { await syncOnce(); }
    catch(e){ onErr(e); }
    finally { syncing = null; setState(); if (syncAgain) { syncAgain = false; scheduleSync(400); } }
  })();
  setState();
  return syncing;
}
function onErr(e){
  if (e && e.code === 'account') { setState('account', e.email + ' でログインしてる'); switchPrompt(e.email); return; }
  if (e && e.code === 'auth') { setState('auth', ''); return; }
  if (e && e.code === 'net') { setState('offline', ''); return; }
  if (e && e.code === 'quota') { setState('error', 'Google Driveの容量がいっぱい'); toastErr('Google Driveの容量がいっぱいで、送れなかった'); return; }
  console.warn('[gdrive]', e); setState('error', String((e && e.message) || e).slice(0, 120));
}
async function syncOnce(){
  if (!navigator.onLine) { setState('offline', ''); return; }
  if (!tokenValid()) { setState('auth', ''); return; }
  await ensureAccount();
  await ensureRoot();
  /* 1. Drive の方が新しければ取ってきて混ぜる */
  if (!KV.dataId) { const df = await byProp('sk', 'data'); if (df) { KV.dataId = df.id; KV.dataVer = null; } }
  if (KV.dataId) {
    let m = null;
    try { m = await api('GET', 'files/' + KV.dataId, {query: {fields: 'id,version,trashed'}}); }
    catch(e){ if (e.status === 404) { KV.dataId = null; KV.dataVer = null; } else throw e; }
    if (m && m.trashed) { KV.dataId = null; KV.dataVer = null; }
    else if (m && String(m.version) !== String(KV.dataVer)) {
      const r = await api('GET', 'files/' + KV.dataId, {query: {alt: 'media'}, raw: true});
      let remote = null; try { remote = JSON.parse(await r.text()); } catch(e){ remote = null; }
      if (remote && remote.format > FILE_FORMAT) { setState('newer', 'アプリが古い。ページを読み込み直してね'); return; }
      if (remote && remote.docs) merge(remote);
      KV.dataVer = String(m.version);
    }
  }
  KV.pulledOnce = true;
  /* 2. まだ送ってない変更があれば送る */
  const need = !KV.dataId || [...DOCS.values()].some(e => e.u);
  if (need) {
    const snapT = lastStamp; const body = buildRemote();
    const blob = new Blob([JSON.stringify(body)], {type: 'application/json'});
    const r = KV.dataId ? await putContent(KV.dataId, blob, 'application/json')
      : await uploadNew(blob, {name: 'data.json', mimeType: 'application/json', parents: [KV.dataDirId], appProperties: {sk: 'data'}});
    KV.dataId = r.id; KV.dataVer = String(r.version);
    for (const [p, e] of DOCS) if (e.u && e.t <= snapT) { delete e.u; persist(p); }
    await dailyBackup().catch(e => console.warn('[gdrive] backup', e));
  }
  KV.lastSync = Date.now(); saveKV(); setState('ok', '');
  if (PENDING.size) pumpUploads();
  if (!KV.reconciledOnce) scheduleReconcile(3000);
}
function merge(remote){
  const rd = remote.docs || {}; const changes = new Map(); let assets = false;
  for (const p of Object.keys(rd)) {
    const re = rd[p], le = DOCS.get(p);
    if (!re || typeof re.t !== 'number') continue;
    if (!le || re.t > le.t) {
      const was = !!le && !le.d, now = !re.d;
      DOCS.set(p, re.d ? {t: re.t, d: 1} : {v: re.v, t: re.t}); persist(p);
      if (re.t > lastStamp) lastStamp = re.t;
      if (p.startsWith('_files/')) assets = true;
      if (!p.startsWith('_') && (was || now)) changes.set(p, {type: !now ? 'removed' : was ? 'modified' : 'added', old: le && le.v});
    } else if (le.t > re.t && !le.u) { le.u = 1; persist(p); }
  }
  for (const [p, le] of DOCS) if (!(p in rd) && !le.u) { le.u = 1; persist(p); }
  emit(changes);
  if (changes.size) scheduleReconcile(6000);
  if (assets) try { window.dispatchEvent(new CustomEvent('gdrive-assets')); } catch(e){}
}
function buildRemote(){
  const docs = {}; const now = Date.now();
  for (const [p, e] of [...DOCS]) {
    if (e.d && !e.u && now - e.t > TOMB_KEEP) { DOCS.delete(p); persist(p); continue; }
    docs[p] = e.d ? {t: e.t, d: 1} : {t: e.t, v: e.v};
  }
  return {app: 'settei-okiba', format: FILE_FORMAT, dataFormat: typeof DATA_FORMAT !== 'undefined' ? DATA_FORMAT : null, savedAt: new Date().toISOString(), by: KV.deviceId, docs};
}
async function dailyBackup(){
  const day = today(); if (KV.bkDay === day || !KV.dataId) return;
  await api('POST', `files/${KV.dataId}/copy`, {query: {fields: 'id'}, headers: J, body: JSON.stringify({name: `データ_${day}.json`, parents: [KV.bkDirId], appProperties: {sk: 'bk'}})});
  KV.bkDay = day; saveKV();
  const bks = (await listFiles(`${qs(KV.bkDirId)} in parents and trashed=false`)).filter(f => /^データ_\d{4}-\d{2}-\d{2}\.json$/.test(f.name)).sort((a, b) => b.name.localeCompare(a.name));
  for (const f of bks.slice(14)) await trash(f.id).catch(() => {});
}

/* ---------- 画像・PDF ---------- */
const PENDING = new Set();          /* まだ Drive に送ってない原本 */
const OBJ = new Map();              /* assetId → この端末で見るためのURL */
const objUrl = (id, blob) => { let u = OBJ.get(id); if (!u) { u = URL.createObjectURL(blob); OBJ.set(id, u); } return u; };
const fileDoc = id => docOf('_files/' + id);
async function storeBlob(id, blob, type, pending){
  try { await idbPut('blobs', id, {blob, type: type || blob.type || '', pending: !!pending, at: Date.now(), size: blob.size}); }
  catch(e){ throw quotaErr(e); }
  if (pending) PENDING.add(id);
}
async function addAsset(id, blob, type){
  const mime = type || blob.type || 'application/octet-stream';
  await storeBlob(id, blob, mime, true);
  writeLocal('_files/' + id, {mime, size: blob.size, at: Date.now(), dev: KV.deviceId}, true);
  setState(); pumpUploads();
  return {id, url: objUrl(id, blob), sizeBytes: blob.size, contentType: mime};
}
let pumpP = null, pumpAgain = false, pumping = false;
function pumpUploads(){
  if (pumpP) { pumpAgain = true; return pumpP; }
  if (!tokenValid() || !navigator.onLine || !PENDING.size) return Promise.resolve();
  pumpP = pumpNow().finally(() => { pumpP = null; if (pumpAgain) { pumpAgain = false; if (PENDING.size) pumpUploads(); } });
  return pumpP;
}
async function pumpNow(){
  pumping = true; setState(); let n = 0;
  try {
    await ensureAccount();
    await ensureRoot();
    for (let round = 0; round < 50 && PENDING.size; round++) {
    const before = PENDING.size;
    for (const id of [...PENDING]) {
      const rec = await idbGet('blobs', id);
      const f = fileDoc(id);
      if (!rec || !f) { PENDING.delete(id); if (rec) await idbDel('blobs', id); continue; }
      if (!f.f) {
        const meta = {name: id + extOf(rec.type), mimeType: rec.type || 'application/octet-stream', parents: [KV.inboxId], appProperties: {aid: id}};
        const ex = await byProp('aid', id);          /* 前に送りかけて記録だけ残ってない場合 */
        const r = ex || await uploadNew(rec.blob, meta);
        writeLocal('_files/' + id, Object.assign({}, fileDoc(id), {f: r.id}), true); n++;
      }
      rec.pending = false; await idbPut('blobs', id, rec); PENDING.delete(id); setState();
    }
    if (PENDING.size >= before) break;
    }
  } catch(e){ onErr(e); }
  finally { pumping = false; setState(); }
  if (n) { scheduleSync(800); scheduleReconcile(5000); }
}
let dlActive = 0; const dlWait = [];
const RES = new Map();
function resolveAsset(id){
  if (OBJ.has(id)) return Promise.resolve(OBJ.get(id));
  if (RES.has(id)) return RES.get(id);
  const p = (async () => {
    const rec = await idbGet('blobs', id).catch(() => null);
    if (rec && rec.blob) { if (!rec.pending) { rec.at = Date.now(); idbPut('blobs', id, rec).catch(() => {}); } return objUrl(id, rec.blob); }
    const f = fileDoc(id); if (!f || !f.f || !tokenValid() || !navigator.onLine) return null;
    if (dlActive >= 3) await new Promise(r => dlWait.push(r));
    dlActive++;
    try {
      const r = await api('GET', 'files/' + f.f, {query: {alt: 'media'}, raw: true});
      let b = await r.blob(); if (!b.type && f.mime) b = new Blob([b], {type: f.mime});
      await storeBlob(id, b, f.mime, false).catch(() => {});
      trimCache();
      return objUrl(id, b);
    } catch(e){ return null; }
    finally { dlActive--; const nx = dlWait.shift(); if (nx) nx(); }
  })();
  RES.set(id, p); p.finally(() => RES.delete(id));
  return p;
}
let trimAt = 0;
async function trimCache(){
  if (Date.now() - trimAt < 60000) return; trimAt = Date.now();
  try {
    const all = (await idbAll('blobs')).filter(([, r]) => r && !r.pending).sort((a, b) => (a[1].at || 0) - (b[1].at || 0));
    let total = all.reduce((s, [, r]) => s + (r.size || 0), 0);
    for (const [id, r] of all) { if (total <= CACHE_CAP) break; await idbDel('blobs', id); total -= r.size || 0; const u = OBJ.get(id); if (u) { URL.revokeObjectURL(u); OBJ.delete(id); } }
  } catch(e){}
}

/* ---------- 仕分け：原本をフォルダへ。ほかの場所にはショートカット ---------- */
let recT = 0, reconciling = false, recP = null;
function scheduleReconcile(ms = 10000){ clearTimeout(recT); recT = setTimeout(reconcile, ms); }
function reconcile(){
  if (recP) { scheduleReconcile(3000); return recP; }
  recP = reconcileNow().finally(() => { recP = null; });
  return recP;
}
async function reconcileNow(){
  const H = window.__setteiDrive;
  if (!H || !KV.pulledOnce || !tokenValid() || !navigator.onLine) { if (H && KV.pulledOnce && tokenValid()) scheduleReconcile(5000); return; }
  if (pumpP) await pumpP.catch(() => {});
  reconciling = true; setState();
  try {
    await ensureAccount();
    await ensureRoot();
    const dirs = new Map();
    await reconcileFiles(H, dirs);
    await reconcileTexts(H, dirs);
    KV.reconciledOnce = true; saveKV();
  } catch(e){ onErr(e); }
  finally { reconciling = false; setState(); }
}
const VERIFIED = new Set();
async function ensureDir(chain, cache){
  const full = dirKey(chain);
  if (cache.has(full)) return cache.get(full);
  let parent = KV.rootId, key = '';
  for (const seg of chain) {
    key = key ? key + '/' + seg.key : seg.key;
    if (cache.has(key)) { parent = cache.get(key); continue; }
    const name = safeName(seg.name), hk = hstr(key), dp = '_dir/' + hk;
    let d = docOf(dp), id = null;
    if (d && d.id) {
      id = d.id;
      if (!VERIFIED.has(id)) {
        try { const m = await api('GET', 'files/' + id, {query: {fields: 'id,trashed'}}); if (m.trashed) id = null; else VERIFIED.add(id); }
        catch(e){ if (e.status === 404) id = null; else throw e; }
      }
    }
    if (id && d) {
      if (d.name !== name || d.parent !== parent) {
        try { await patchMeta(id, {name}, d.parent !== parent ? {addParents: parent, removeParents: d.parent} : null); writeLocal(dp, {id, name, parent, key}, true); }
        catch(e){ if (e.status === 404) id = null; else throw e; }
      }
    }
    if (!id) {
      const ex = await byProp('dk', hk, parent);      /* ほかの端末が作ったばかりのフォルダ */
      const f = ex || await createMeta({name, mimeType: FOLDER, parents: [parent], appProperties: {dk: hk}});
      id = f.id; writeLocal(dp, {id, name, parent, key}, true);
    }
    cache.set(key, id); parent = id;
  }
  return parent;
}
async function reconcileFiles(H, dirs){
  const isAsset = id => !!fileDoc(id);
  let layout = [];
  try { layout = H.layout(isAsset) || []; } catch(e){ console.warn('[gdrive] layout', e); return; }
  const occ = new Map();
  for (const e of layout) { if (!e || !isAsset(e.id) || !Array.isArray(e.dir)) continue; if (!occ.has(e.id)) occ.set(e.id, []); occ.get(e.id).push(e); }
  for (const [p, ent] of [...DOCS]) {
    if (!p.startsWith('_files/') || ent.d || !ent.v.f) continue;
    const id = p.slice(7), f = ent.v, sp = '_drv/' + id;
    const st = Object.assign({sc: {}}, cloneJ(docOf(sp)) || {}); let changed = false;
    const list = occ.get(id) || [];
    if (!list.length) {
      if (!st.gone) { st.gone = Date.now(); changed = true; }
      else if (!st.tr && Date.now() - st.gone > GRACE) {
        try { await trash(f.f); } catch(e){ if (e.status !== 404) throw e; }
        for (const s of Object.values(st.sc)) await trash(s.id).catch(() => {});
        st.sc = {}; st.tr = 1; changed = true;
      }
      if (changed) writeLocal(sp, st, true);
      continue;
    }
    if (st.gone || st.tr) { if (st.tr) { try { await patchMeta(f.f, {trashed: false}); } catch(e){ if (e.status !== 404) throw e; } } delete st.gone; delete st.tr; changed = true; }
    const strong = list.filter(x => !x.weak);
    const cands = strong.length ? strong : list.slice(0, 1);
    const owner = cands.find(x => dirKey(x.dir) === st.k) || cands[0];
    const folder = await ensureDir(owner.dir, dirs);
    const name = safeName(owner.name) + extOf(f.mime, owner.ext);
    if (st.p !== folder || st.n !== name) {
      try { await moveFile(f.f, folder, name); } catch(e){ if (e.status === 404) { continue; } throw e; }
      st.p = folder; st.n = name; changed = true;
    }
    if (st.k !== dirKey(owner.dir)) { st.k = dirKey(owner.dir); changed = true; }
    const want = new Map();
    for (const x of strong) { if (x === owner) continue; const fd = await ensureDir(x.dir, dirs); if (fd !== folder && !want.has(fd)) want.set(fd, safeName(x.name) + extOf(f.mime, x.ext)); }
    for (const [fd, nm] of want) {
      const cur = st.sc[fd];
      if (cur && cur.n === nm) continue;
      if (cur) { try { await patchMeta(cur.id, {name: nm}); st.sc[fd] = {id: cur.id, n: nm}; changed = true; continue; } catch(e){ if (e.status !== 404) throw e; } }
      const ex = (await listFiles(`${qs(fd)} in parents and appProperties has { key='sc' and value=${qs(id)} } and trashed=false`))[0];
      const s = ex || await createMeta({name: nm, mimeType: SHORTCUT, parents: [fd], shortcutDetails: {targetId: f.f}, appProperties: {sc: id}});
      st.sc[fd] = {id: s.id, n: nm}; changed = true;
    }
    for (const fd of Object.keys(st.sc)) if (!want.has(fd)) { await trash(st.sc[fd].id).catch(() => {}); delete st.sc[fd]; changed = true; }
    if (changed) writeLocal(sp, st, true);
  }
}
async function reconcileTexts(H, dirs){
  if (typeof H.texts !== 'function') return;
  const nameOf = id => { const s = docOf('_drv/' + id); return (s && s.n) || null; };
  let items = [];
  try { items = H.texts(nameOf) || []; } catch(e){ console.warn('[gdrive] texts', e); return; }
  const seen = new Set();
  for (const it of items) {
    if (!it || !Array.isArray(it.dir) || !it.name) continue;
    const key = hstr(dirKey(it.dir) + '//' + it.name); seen.add(key);
    const text = '﻿' + String(it.text || ''); const h = hstr(text);
    const tp = '_txt/' + key, st = docOf(tp);
    const folder = await ensureDir(it.dir, dirs);
    const name = safeName(String(it.name).replace(/\.txt$/i, '')) + '.txt';
    if (st && st.f && st.h === h && st.p === folder && st.n === name) continue;
    const blob = new Blob([text], {type: 'text/plain'});
    let fid = st && st.f;
    if (fid) {
      try { if (st.h !== h) await putContent(fid, blob, 'text/plain; charset=UTF-8'); if (st.p !== folder || st.n !== name) await moveFile(fid, folder, name); }
      catch(e){ if (e.status === 404) fid = null; else throw e; }
    }
    if (!fid) {
      const ex = await byProp('tk', key, folder);
      if (ex) { fid = ex.id; await putContent(fid, blob, 'text/plain; charset=UTF-8'); if (ex.name !== name) await patchMeta(fid, {name}); }
      else fid = (await uploadNew(blob, {name, mimeType: 'text/plain', parents: [folder], appProperties: {tk: key}})).id;
    }
    writeLocal(tp, {f: fid, h, p: folder, n: name}, true);
  }
  for (const [p, e] of [...DOCS]) if (p.startsWith('_txt/') && !e.d && !seen.has(p.slice(5))) { await trash(e.v.f).catch(() => {}); deleteLocal(p, true); }
}

/* ---------- 変更のきっかけ ---------- */
function onLocalChange(path){
  scheduleSync(2500);
  if (!path.startsWith('_')) scheduleReconcile(10000);
}
document.addEventListener('visibilitychange', () => {
  if (document.visibilityState === 'hidden') { flushPersist(); if (DOCS.size && [...DOCS.values()].some(e => e.u)) sync(); }
  else sync();
});
window.addEventListener('pagehide', () => { flushPersist(); });
window.addEventListener('online', () => { sync(); pumpUploads(); });
window.addEventListener('offline', () => setState('offline'));
setInterval(() => { if (document.visibilityState === 'visible' && KV.pulledOnce) sync(); }, 60000);

/* ---------- 最初の画面（この端末で初めて開いたとき） ---------- */
function gate(){
  return new Promise(resolve => {
    const el = document.createElement('div'); el.id = 'gdGate';
    el.innerHTML = `<style>
      #gdGate{position:fixed;inset:0;z-index:99999;display:flex;align-items:center;justify-content:center;padding:24px;background:#f4ede2;color:#2a241c;font-family:-apple-system,BlinkMacSystemFont,"Hiragino Sans","Noto Sans JP",sans-serif}
      @media (prefers-color-scheme:dark){#gdGate{background:#1c1a17;color:#efe7da}}
      #gdGate .bx{max-width:360px;width:100%;text-align:center}
      #gdGate h1{font-size:22px;margin:0 0 10px;font-family:"Hiragino Mincho ProN","Noto Serif JP",serif}
      #gdGate p{font-size:14px;line-height:1.7;opacity:.8;margin:0 0 22px}
      #gdGate button{font:inherit;font-size:16px;font-weight:700;padding:13px 22px;border-radius:999px;border:0;background:#7a2e2e;color:#fff;width:100%}
      #gdGate button:disabled{opacity:.5}
      #gdGate .er{color:#b33;font-size:13px;margin-top:14px;min-height:1em;white-space:pre-wrap}
    </style><div class="bx"><h1>創作の設定置き場</h1><p>データと画像は、自分のGoogle Driveに入るよ。<br>まずGoogleにログインしてね。</p><button id="gdGo">Googleでログイン</button><div class="er" id="gdEr"></div></div>`;
    const mount = () => document.body.appendChild(el);
    if (document.body) mount(); else document.addEventListener('DOMContentLoaded', mount);
    const er = m => { const x = el.querySelector('#gdEr'); if (x) x.textContent = m || ''; };
    const finish = async () => {
      const btn = el.querySelector('#gdGo'); if (btn) { btn.disabled = true; btn.textContent = 'Driveを確かめてる…'; }
      try {
        await sync();
        if (!KV.pulledOnce) throw Object.assign(new Error(ST.mode === 'offline' ? 'ネットにつながってないみたい' : ST.err || 'Driveにつながらなかった。もう一度押してね'), {code: ST.mode === 'offline' ? 'net' : ''});
        saveKV(); el.remove(); resolve();
      } catch(e){ if (btn) { btn.disabled = false; btn.textContent = 'Googleでログイン'; } if (ST.mode !== 'account') er(e.code === 'net' ? 'ネットにつながってないみたい' : String(e.message || e)); }
    };
    el.addEventListener('click', ev => {
      if (!ev.target.closest('#gdGo')) return;
      er('');
      if (tokenValid()) { finish(); return; }
      connect().then(finish, e => er(String(e.message || e)));
    });
    if (!CFG.clientId) setTimeout(() => er('config.js にGoogleのクライアントIDが入ってない。手順書の「Google側の設定」を見てね'), 0);
    else if (tokenValid()) setTimeout(finish, 0);
  });
}

/* ---------- アプリへの入口 ---------- */
const downloads = {
  async save({filename, data}){
    const blob = data instanceof Blob ? data : new Blob([data], {type: /\.json$/i.test(filename) ? 'application/json' : /\.zip$/i.test(filename) ? 'application/zip' : 'text/plain;charset=utf-8'});
    const a = document.createElement('a'); a.href = URL.createObjectURL(blob); a.download = filename || 'file'; a.style.display = 'none';
    document.body.appendChild(a); a.click(); setTimeout(() => { URL.revokeObjectURL(a.href); a.remove(); }, 8000);
    return {status: 'saved'};
  }
};
const assets = {
  upload: (blob, opts) => addAsset(rid(32), blob, opts && opts.type),
  attach: async (id, blob, type) => { if (fileDoc(id)) return {id}; return addAsset(id, blob, type); },
  async list(){ const out = []; for (const [p, e] of DOCS) if (p.startsWith('_files/') && !e.d) { const id = p.slice(7); out.push({id, url: OBJ.get(id) || null, contentType: e.v.mime, sizeBytes: e.v.size}); } return {assets: out, usage: {}}; },
  async delete(){},
  has: id => !!fileDoc(id),
  resolve: id => resolveAsset(id),
  link: id => { const f = fileDoc(id); return f && f.f ? `https://drive.google.com/file/d/${f.f}/view` : null; }
};
const user = {isOwner: async () => true, canEdit: async () => true, can: async () => true, id: async () => 'me', me: async () => ({id: 'me', name: KV.name || '', isOwner: true, canEdit: true})};
const db = {doc: docRef, collection: colRef};

const READY = (async () => {
  try { await loadLocal(); } catch(e){ console.warn('[gdrive] local', e); }
  loadToken(); loadGis().catch(() => {});
  if (!KV.pulledOnce) await gate();
  else setTimeout(() => { if (tokenValid()) { sync(); pumpUploads(); scheduleReconcile(8000); } else setState('auth'); }, 200);
})();

window.__gdrive = {
  get state(){ return {mode: ST.mode, err: ST.err, pending: PENDING.size, lastSync: KV.lastSync || 0, email: KV.account || KV.email || '', connected: tokenValid(), rootId: KV.rootId || '', quota: KV.quota || null}; },
  connect, signOut,
  syncNow: () => { if (!tokenValid()) return Promise.resolve(); return sync().then(() => { pumpUploads(); scheduleReconcile(500); }); },
  folderUrl: () => KV.rootId ? 'https://drive.google.com/drive/folders/' + KV.rootId : 'https://drive.google.com/',
  ping: () => setState(),
  _debug: {DOCS, KV: () => KV, reconcile, sync, pumpUploads, PENDING, flushPersist}
};
window.claude = {use: async name => { await READY; return ({db, user, assets, downloads})[name] || null; }};
})();
