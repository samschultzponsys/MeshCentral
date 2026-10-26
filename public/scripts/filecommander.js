/**
* @description File Commander - a dual pane file manager for the Files tab.
*
* Each pane shows either the remote device (over the existing files tunnel) or a folder on this
* computer (File System Access API, Chromium based browsers). Files are copied or moved between
* the panes with F5/F6, drag and drop or the context menu. Folders are copied recursively.
*
* The page owns the files tunnel. It forwards the messages it receives to processData(),
* processBinary() and processBinaryString(), and calls onConnect()/onDisconnect() when the
* tunnel state changes. Requests sent from here use reqid/id values starting with "fc" so the
* page can tell them apart from its own.
*/

var FileCommander = (function () {
    'use strict';

    var localSupported = (typeof window.showDirectoryPicker == 'function') && (window.isSecureContext == true);
    var uploadWindow = 64; // Upload blocks sent but not yet acknowledged by the agent
    var downloadWindow = 64; // Download blocks the agent may send before the next ack
    var maxEditSize = 5 * 1024 * 1024;

    function esc(s) { return String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;').replace(/'/g, '&#39;'); }

    function sizeStr(n) {
        if ((n == null) || isNaN(n)) return '';
        if (n < 1024) return n + ' B';
        var u = ['KB', 'MB', 'GB', 'TB', 'PB'], i = -1;
        do { n /= 1024; i++; } while ((n >= 1024) && (i < u.length - 1));
        return n.toFixed((n < 10) ? 2 : ((n < 100) ? 1 : 0)) + ' ' + u[i];
    }

    function fileType(item) {
        if (item.kind == 'drive') { return (item.dt == 'REMOVABLE') ? 'Removable Disk' : ((item.dt == 'CDROM') ? 'CD Drive' : ((item.dt == 'NETWORK') ? 'Network Drive' : 'Local Disk')); }
        if (item.kind == 'dir') return 'File Folder';
        var i = item.name.lastIndexOf('.');
        if ((i <= 0) || (i == item.name.length - 1)) return 'File';
        return item.name.substring(i + 1).toUpperCase() + ' File';
    }

    function cancelError() { var e = new Error('Canceled'); e.canceled = true; return e; }

    // Small IndexedDB key/value store, used to remember local folders between visits.
    function idbOpen() {
        return new Promise(function (resolve, reject) {
            var r = indexedDB.open('meshcentral-filecommander', 1);
            r.onupgradeneeded = function () { r.result.createObjectStore('kv'); };
            r.onsuccess = function () { resolve(r.result); };
            r.onerror = function () { reject(r.error); };
        });
    }
    function idbGet(key) {
        return idbOpen().then(function (db) {
            return new Promise(function (resolve) {
                var r = db.transaction('kv', 'readonly').objectStore('kv').get(key);
                r.onsuccess = function () { resolve(r.result); };
                r.onerror = function () { resolve(null); };
            });
        }).catch(function () { return null; });
    }
    function idbSet(key, value) {
        return idbOpen().then(function (db) {
            return new Promise(function (resolve) {
                var t = db.transaction('kv', 'readwrite');
                t.objectStore('kv').put(value, key);
                t.oncomplete = function () { resolve(true); };
                t.onerror = function () { resolve(false); };
            });
        }).catch(function () { return false; });
    }

    function storeGet(key, def) { try { var v = localStorage.getItem(key); return (v == null) ? def : JSON.parse(v); } catch (ex) { return def; } }
    function storeSet(key, value) { try { localStorage.setItem(key, JSON.stringify(value)); } catch (ex) { } }

    // host: {
    //   root: element to render in,
    //   send(obj), sendBinary(Uint8Array), isConnected(), isWindows(), isSftp(), nodeId(), nodeName(),
    //   chunkSize(), formatDate(Date), downloadUrl(path, name) (optional), onActiveChanged(active) (optional)
    // }
    function create(host) {
        var obj = { active: false };
        var root = host.root;
        var panes = [];
        var activeIdx = 1;
        var reqSeq = 0;
        var pending = {};        // ls reqid -> { resolve, reject, timer }
        var upload = null;       // Running upload
        var download = null;     // Running download
        var job = null;          // Running copy/move job
        var remoteDrives = null; // Root listing of a Windows device
        var recentLocal = [];    // Recently used local folder handles
        var menuEl = null, modalEl = null;
        var dragSource = null;

        //
        // Remote primitives
        //

        function nextId(p) { return 'fc' + p + (++reqSeq); }
        function connected() { return host.isConnected() == true; }
        function rSend(cmd) { if (connected()) { host.send(cmd); } }
        function caseless() { return host.isWindows(); }

        function rPath(segs) {
            if (host.isWindows()) { return (segs.length == 0) ? '' : (segs.join('/') + ((segs.length == 1) ? '/' : '')); }
            return '/' + segs.join('/');
        }
        function rPathNoSlash(segs) { return host.isWindows() ? segs.join('/') : ('/' + segs.join('/')); }
        function rDisplay(segs) {
            if (host.isWindows()) { return (segs.length == 0) ? 'Computer' : (segs.join('\\') + ((segs.length == 1) ? '\\' : '')); }
            return '/' + segs.join('/');
        }
        function rParse(s) { return String(s).replace(/\\/g, '/').split('/').filter(function (x) { return (x != '') && (x != '.'); }); }

        function rList(path) {
            return new Promise(function (resolve, reject) {
                if (!connected()) { reject(new Error('Not connected')); return; }
                var reqid = nextId('l');
                pending[reqid] = { resolve: resolve, reject: reject, timer: setTimeout(function () { delete pending[reqid]; reject(new Error('The device did not answer')); }, 120000) };
                host.send({ action: 'ls', reqid: reqid, path: path });
            });
        }

        function remoteItem(f) {
            var d = null;
            if (f.d != null) { d = (typeof f.d == 'number') ? (f.d * 1000) : Date.parse(f.d); if (isNaN(d)) { d = null; } }
            return { name: f.n, kind: (f.t == 1) ? 'drive' : ((f.t == 2) ? 'dir' : 'file'), size: (f.t == 3) ? (f.s || 0) : ((f.t == 1) ? f.s : null), free: f.f, dt: f.dt, date: d };
        }

        function rUpload(dirPath, name, blob, onProgress) {
            return new Promise(function (resolve, reject) {
                if (!connected()) { reject(new Error('Not connected')); return; }
                upload = { reqid: nextId('u'), blob: blob, size: blob.size, ptr: 0, inflight: 0, reading: false, doneSent: false, resolve: resolve, reject: reject, onProgress: onProgress };
                host.send({ action: 'upload', reqid: upload.reqid, path: dirPath, name: name, size: blob.size });
            });
        }

        function uploadPump() {
            var u = upload;
            if ((u == null) || u.reading) return;
            if (u.ptr >= u.size) {
                if ((u.inflight == 0) && !u.doneSent) { u.doneSent = true; rSend({ action: 'uploaddone', reqid: u.reqid }); }
                return;
            }
            if (u.inflight >= uploadWindow) return;
            var end = Math.min(u.size, u.ptr + host.chunkSize());
            u.reading = true;
            u.blob.slice(u.ptr, end).arrayBuffer().then(function (buf) {
                u.reading = false;
                if (upload !== u) return;
                var d = new Uint8Array(buf);
                if ((d.length > 0) && ((d[0] == 0) || (d[0] == 123))) { var x = new Uint8Array(d.length + 1); x.set(d, 1); d = x; } // Leading zero marks the block as data, not JSON
                host.sendBinary(d);
                u.inflight++;
                u.ptr = end;
                if (u.onProgress) { u.onProgress(u.ptr, u.size); }
                uploadPump();
            }, function (err) {
                u.reading = false;
                if (upload !== u) return;
                upload = null;
                rSend({ action: 'uploadcancel', reqid: u.reqid });
                u.reject(err);
            });
        }

        function uploadMessage(m) {
            var u = upload;
            if ((u == null) || (u.reqid != m.reqid)) return;
            switch (m.action) {
                case 'uploadstart': { uploadPump(); break; }
                case 'uploadack': { if (u.inflight > 0) { u.inflight--; } uploadPump(); break; }
                case 'uploaddone': { upload = null; u.resolve(); break; }
                case 'uploaderror': { upload = null; u.reject(new Error('Unable to write the file on the device')); break; }
                case 'uploadcancel': { upload = null; u.reject(cancelError()); break; }
            }
        }

        function uploadCancel() {
            var u = upload;
            if (u == null) return;
            upload = null;
            rSend({ action: 'uploadcancel', reqid: u.reqid });
            u.reject(cancelError());
        }

        // sink: { write(Uint8Array) -> Promise, close() -> Promise, abort() }
        function rDownload(path, size, sink, onProgress) {
            return new Promise(function (resolve, reject) {
                if (!connected()) { reject(new Error('Not connected')); return; }
                download = { id: nextId('d'), state: 0, got: 0, size: size, sink: sink, chain: Promise.resolve(), resolve: resolve, reject: reject, onProgress: onProgress };
                host.send({ action: 'download', sub: 'start', id: download.id, path: path });
            });
        }

        function downloadFail(d, err) {
            if (download === d) { download = null; rSend({ action: 'download', sub: 'stop', id: d.id }); }
            if (d.failed) return;
            d.failed = true;
            try { d.sink.abort(); } catch (ex) { }
            d.reject(err);
        }

        function downloadMessage(m) {
            var d = download;
            if ((d == null) || (d.id != m.id)) return;
            if (m.sub == 'start') { d.state = 1; rSend({ action: 'download', sub: 'startack', id: d.id, ack: downloadWindow, bs: host.chunkSize() }); }
            else if (m.sub == 'cancel') { download = null; downloadFail(d, new Error('Unable to read the file on the device')); }
        }

        function downloadBlock(data) {
            var d = download;
            if ((d == null) || (d.state != 1) || (data.length < 4) || (data[0] != 1)) return false;
            var payload = data.slice(4), last = ((data[3] & 1) != 0);
            d.got += payload.length;
            if (payload.length > 0) { d.chain = d.chain.then(function () { if (!d.failed) { return d.sink.write(payload); } }); }
            d.chain = d.chain.catch(function (err) { downloadFail(d, err); });
            if (d.onProgress) { d.onProgress(d.got, d.size); }
            if (last) {
                download = null;
                d.chain.then(function () { if (!d.failed) { return d.sink.close().then(d.resolve); } }).catch(function (err) { downloadFail(d, err); });
            } else {
                rSend({ action: 'download', sub: 'ack', id: d.id });
            }
            return true;
        }

        function downloadCancel() { var d = download; if (d != null) { downloadFail(d, cancelError()); } }

        function memorySink() {
            var chunks = [], size = 0;
            return {
                write: function (b) { size += b.length; if (size > maxEditSize) { return Promise.reject(new Error('File is too large')); } chunks.push(b); return Promise.resolve(); },
                close: function () { return Promise.resolve(); },
                abort: function () { chunks = []; },
                blob: function () { return new Blob(chunks); }
            };
        }

        function localSink(dirHandle, name) {
            return dirHandle.getFileHandle(name, { create: true }).then(function (fh) { return fh.createWritable(); }).then(function (w) {
                return { write: function (b) { return w.write(b); }, close: function () { return w.close(); }, abort: function () { try { w.abort(); } catch (ex) { } } };
            });
        }

        //
        // Local helpers
        //

        async function localEntries(dirHandle) {
            var list = [], files = [];
            for await (var h of dirHandle.values()) {
                if (h.kind == 'directory') { list.push({ name: h.name, kind: 'dir', size: null, date: null, handle: h }); }
                else { var it = { name: h.name, kind: 'file', size: null, date: null, handle: h }; list.push(it); files.push(it); }
            }
            for (var i = 0; i < files.length; i += 64) {
                await Promise.all(files.slice(i, i + 64).map(function (it) {
                    return it.handle.getFile().then(function (f) { it.size = f.size; it.date = f.lastModified; }, function () { });
                }));
            }
            return list;
        }

        async function ensurePermission(handle) {
            var opts = { mode: 'readwrite' };
            if ((await handle.queryPermission(opts)) == 'granted') return true;
            return (await handle.requestPermission(opts)) == 'granted';
        }

        //
        // Panes
        //

        function newPane(idx) {
            return { idx: idx, type: 'remote', segs: [], stack: [], items: [], rows: [], sortKey: 'name', sortDir: 1, marked: {}, cursor: 0, anchor: 0, loadSeq: 0, loading: false, message: null, el: {} };
        }

        function other(p) { return panes[1 - p.idx]; }
        function activePane() { return panes[activeIdx]; }

        function paneLabel(p) {
            if (p.type == 'remote') return rDisplay(p.segs);
            if (p.stack.length == 0) return '';
            return p.stack.map(function (h) { return h.name; }).join('\\') + '\\';
        }

        function sortItems(p) {
            var dir = p.sortDir, key = p.sortKey;
            function byName(a, b) { return a.name.localeCompare(b.name, undefined, { numeric: true, sensitivity: 'base' }); }
            var cmp = byName;
            if (key == 'size') { cmp = function (a, b) { return ((a.size || 0) - (b.size || 0)) || byName(a, b); }; }
            else if (key == 'date') { cmp = function (a, b) { return ((a.date || 0) - (b.date || 0)) || byName(a, b); }; }
            else if (key == 'type') { cmp = function (a, b) { return fileType(a).localeCompare(fileType(b)) || byName(a, b); }; }
            var rank = { drive: 0, dir: 1, file: 2 };
            var list = p.items.slice().sort(function (a, b) { return (rank[a.kind] - rank[b.kind]) || (cmp(a, b) * dir); });
            p.rows = (atRoot(p) ? [] : [{ up: true, name: '..', kind: 'up' }]).concat(list);
        }

        function atRoot(p) { return (p.type == 'remote') ? (p.segs.length == 0) : (p.stack.length <= 1); }

        function saveState() {
            storeSet('fcTypes', [panes[0].type, panes[1].type]);
            storeSet('fcSort', [[panes[0].sortKey, panes[0].sortDir], [panes[1].sortKey, panes[1].sortDir]]);
            if (host.nodeId()) {
                var paths = storeGet('fcPaths', []).filter(function (x) { return x.n != host.nodeId(); });
                paths.push({ n: host.nodeId(), p: [panes[0].segs, panes[1].segs] });
                while (paths.length > 40) { paths.shift(); }
                storeSet('fcPaths', paths);
            }
        }

        async function loadRemote(p, segs, keepMarks, focusName) {
            if (p.type != 'remote') return false;
            if (!connected()) { p.items = []; p.rows = []; p.message = 'Not connected. Use the Connect button above.'; renderPane(p); return false; }
            var seq = ++p.loadSeq;
            p.loading = true; renderStatus(p);
            var dir;
            try { dir = await rList(rPath(segs)); } catch (ex) { if (seq == p.loadSeq) { p.loading = false; flash(p, ex.message); renderStatus(p); } return false; }
            if ((seq != p.loadSeq) || (p.type != 'remote')) return false;
            p.loading = false;
            if (dir == null) {
                flash(p, 'Unable to open ' + rDisplay(segs));
                if ((p.rows.length == 0) && (segs.length > 0)) { return loadRemote(p, segs.slice(0, -1)); }
                renderStatus(p);
                return false;
            }
            var samePath = (rPath(segs) == rPath(p.segs));
            var prevName = (p.rows[p.cursor] != null) ? p.rows[p.cursor].name : null;
            p.segs = segs;
            p.items = dir.map(remoteItem);
            p.message = null;
            if (segs.length == 0 && host.isWindows()) { remoteDrives = p.items.filter(function (x) { return x.kind == 'drive'; }); renderDrives(panes[0]); renderDrives(panes[1]); }
            finishLoad(p, (samePath && keepMarks), focusName || (samePath ? prevName : null));
            saveState();
            return true;
        }

        async function loadLocal(p, stack, keepMarks, focusName) {
            if (p.type != 'local') return false;
            if (stack.length == 0) { p.stack = []; p.items = []; p.rows = []; p.message = null; renderPane(p); return false; }
            var seq = ++p.loadSeq;
            p.loading = true; renderStatus(p);
            var items;
            try { items = await localEntries(stack[stack.length - 1]); } catch (ex) { if (seq == p.loadSeq) { p.loading = false; flash(p, ex.message); renderStatus(p); } return false; }
            if ((seq != p.loadSeq) || (p.type != 'local')) return false;
            p.loading = false;
            var samePath = (stack.length == p.stack.length) && (stack[stack.length - 1] === p.stack[p.stack.length - 1]);
            var prevName = (p.rows[p.cursor] != null) ? p.rows[p.cursor].name : null;
            p.stack = stack;
            p.items = items;
            p.message = null;
            finishLoad(p, (samePath && keepMarks), focusName || (samePath ? prevName : null));
            return true;
        }

        function finishLoad(p, keepMarks, focusName) {
            if (!keepMarks) { p.marked = {}; }
            else { var names = {}; p.items.forEach(function (x) { names[x.name] = 1; }); for (var n in p.marked) { if (!names[n]) { delete p.marked[n]; } } }
            sortItems(p);
            p.cursor = 0;
            if (focusName != null) { for (var i = 0; i < p.rows.length; i++) { if (p.rows[i].name == focusName) { p.cursor = i; break; } } }
            p.anchor = p.cursor;
            renderPane(p);
        }

        function refresh(p, focusName) {
            if (p.type == 'remote') { return loadRemote(p, p.segs, true, focusName); }
            return loadLocal(p, p.stack, true, focusName);
        }

        function refreshAll() { return Promise.all([refresh(panes[0]), refresh(panes[1])]); }

        function openRow(p, row) {
            if (row == null) return;
            if (row.up) { goUp(p); return; }
            if ((row.kind == 'dir') || (row.kind == 'drive')) {
                if (p.type == 'remote') { loadRemote(p, p.segs.concat([row.name])); }
                else { loadLocal(p, p.stack.concat([row.handle])); }
                return;
            }
            if (p.type == 'remote') { downloadToBrowser(p, [row]); }
        }

        function goUp(p) {
            if (atRoot(p)) return;
            if (p.type == 'remote') { var name = p.segs[p.segs.length - 1]; loadRemote(p, p.segs.slice(0, -1), false, name); }
            else { var h = p.stack[p.stack.length - 1]; loadLocal(p, p.stack.slice(0, -1), false, h.name); }
        }

        function goRoot(p) {
            if (p.type == 'remote') { loadRemote(p, []); }
            else if (p.stack.length > 0) { loadLocal(p, p.stack.slice(0, 1)); }
        }

        function gotoPath(p, text) {
            if (p.type == 'remote') { loadRemote(p, rParse(text)); return; }
            // Local panes can only move inside the chosen folder
            var parts = rParse(text), stack = p.stack.slice(0, 1);
            if ((stack.length == 0) || (parts.length == 0) || (parts[0] != stack[0].name)) { flash(p, 'Local paths must start with ' + (stack.length ? stack[0].name : 'a chosen folder')); renderPath(p); return; }
            (async function () {
                var s = stack.slice();
                for (var i = 1; i < parts.length; i++) {
                    try { s.push(await s[s.length - 1].getDirectoryHandle(parts[i])); } catch (ex) { flash(p, 'Folder not found: ' + parts[i]); break; }
                }
                loadLocal(p, s);
            })();
        }

        async function chooseLocalFolder(p, handle) {
            try {
                if (handle == null) { handle = await window.showDirectoryPicker({ mode: 'readwrite', id: 'meshcommander' + p.idx }); }
                else if (!(await ensurePermission(handle))) { flash(p, 'Permission to the folder was denied'); return; }
            } catch (ex) { if (ex && (ex.name != 'AbortError')) { flash(p, ex.message); } return; }
            var list = [handle];
            for (var i = 0; i < recentLocal.length && list.length < 8; i++) {
                var same = false;
                try { same = await recentLocal[i].isSameEntry(handle); } catch (ex) { }
                if (!same) { list.push(recentLocal[i]); }
            }
            recentLocal = list;
            idbSet('recent', recentLocal);
            renderDrives(panes[0]); renderDrives(panes[1]);
            loadLocal(p, [handle]);
        }

        function setPaneType(p, type) {
            if ((type == 'local') && !localSupported) { type = 'remote'; }
            p.type = type; p.items = []; p.rows = []; p.marked = {}; p.cursor = 0; p.message = null; p.loadSeq++;
            renderPane(p);
            renderDrives(p);
            saveState();
            if (type == 'remote') { loadRemote(p, p.segs || []); }
            else if (p.stack.length > 0) { loadLocal(p, p.stack); }
        }

        //
        // Selection
        //

        function selectedRows(p) {
            var r = p.rows.filter(function (x) { return !x.up && p.marked[x.name]; });
            if ((r.length == 0) && (p.rows[p.cursor] != null) && !p.rows[p.cursor].up) { r = [p.rows[p.cursor]]; }
            return r;
        }

        function setCursor(p, i, extend) {
            if (p.rows.length == 0) return;
            i = Math.max(0, Math.min(p.rows.length - 1, i));
            p.cursor = i;
            if (extend) {
                p.marked = {};
                var a = Math.min(p.anchor, i), b = Math.max(p.anchor, i);
                for (var j = a; j <= b; j++) { if (!p.rows[j].up) { p.marked[p.rows[j].name] = 1; } }
            } else {
                p.anchor = i;
            }
            renderMarks(p);
            scrollToCursor(p);
        }

        function toggleMark(p, i) {
            var row = p.rows[i];
            if ((row == null) || row.up) return;
            if (p.marked[row.name]) { delete p.marked[row.name]; } else { p.marked[row.name] = 1; }
        }

        function setActive(idx) {
            activeIdx = idx;
            for (var i = 0; i < 2; i++) { panes[i].el.pane.classList.toggle('fc-active', i == idx); }
            renderButtons();
        }

        //
        // Rendering
        //

        function h(tag, cls, html) { var e = document.createElement(tag); if (cls) { e.className = cls; } if (html != null) { e.innerHTML = html; } return e; }

        function build() {
            root.innerHTML = '';
            root.classList.add('fc-root');
            var panesEl = h('div', 'fc-panes');
            for (var i = 0; i < 2; i++) {
                var p = panes[i], e = p.el;
                e.pane = h('div', 'fc-pane');
                e.head = h('div', 'fc-head');
                e.src = h('select', 'fc-src');
                e.src.title = 'Show the remote device or a folder on this computer';
                e.drives = h('select', 'fc-drives');
                e.drives.title = 'Drives and folders';
                e.up = h('button', 'fc-btn', '&#x2191;'); e.up.title = 'Parent folder (Backspace)';
                e.rootBtn = h('button', 'fc-btn', '\\'); e.rootBtn.title = 'Root';
                e.refresh = h('button', 'fc-btn', '&#x21bb;'); e.refresh.title = 'Refresh (Ctrl+R)';
                e.head.append(e.src, e.drives, e.up, e.rootBtn, e.refresh);
                e.path = h('input', 'fc-path'); e.path.type = 'text'; e.path.spellcheck = false; e.path.title = 'Type a path and press Enter';
                e.scroll = h('div', 'fc-scroll'); e.scroll.tabIndex = 0;
                e.table = h('table', 'fc-table');
                e.table.innerHTML = '<colgroup><col><col class=fc-c-size><col class=fc-c-type><col class=fc-c-date></colgroup><thead><tr><th data-k=name>Name</th><th data-k=size class=fc-r>Size</th><th data-k=type>Type</th><th data-k=date>Modified</th></tr></thead><tbody></tbody>';
                e.tbody = e.table.tBodies[0];
                e.empty = h('div', 'fc-empty');
                e.scroll.append(e.table, e.empty);
                e.status = h('div', 'fc-status');
                e.pane.append(e.head, e.path, e.scroll, e.status);
                if (i == 0) { panesEl.append(e.pane, h('div', 'fc-split')); } else { panesEl.append(e.pane); }
                wirePane(p);
            }
            root.append(panesEl);
            obj.keysEl = h('div', 'fc-keys');
            root.append(obj.keysEl);
            obj.jobEl = h('div', 'fc-job');
            obj.jobEl.style.display = 'none';
            root.append(obj.jobEl);
            wireSplitter(panesEl);
            renderButtons();
        }

        function renderSrc(p) {
            var e = p.el, name = host.nodeName() || 'Remote device';
            e.src.innerHTML = '<option value=remote>' + esc(name) + '</option>' + '<option value=local' + (localSupported ? '' : ' disabled') + '>This computer</option>';
            e.src.value = p.type;
        }

        function renderDrives(p) {
            var e = p.el, x = '';
            if (p.type == 'remote') {
                if (host.isWindows()) {
                    x += '<option value=":root">Computer</option>';
                    (remoteDrives || []).forEach(function (d) { x += '<option value="' + esc(d.name) + '">' + esc(d.name) + ' ' + esc(fileType(d)) + '</option>'; });
                    e.drives.innerHTML = x;
                    e.drives.value = (p.segs.length == 0) ? ':root' : p.segs[0];
                    if (e.drives.selectedIndex < 0) { e.drives.value = ':root'; }
                } else {
                    e.drives.innerHTML = '<option value=":root">/</option>';
                }
                e.drives.style.display = host.isWindows() ? '' : 'none';
            } else {
                recentLocal.forEach(function (hd, i) { x += '<option value="' + i + '">' + esc(hd.name) + '</option>'; });
                x += '<option value=":pick">Choose folder...</option>';
                e.drives.innerHTML = x;
                var cur = -1;
                if (p.stack.length > 0) { for (var i = 0; i < recentLocal.length; i++) { if (recentLocal[i] === p.stack[0]) { cur = i; } } }
                e.drives.value = (cur >= 0) ? String(cur) : ':pick';
                e.drives.style.display = '';
            }
        }

        function renderPath(p) { p.el.path.value = paneLabel(p); }

        function rowHtml(p, row, i) {
            var cls = 'fc-row';
            if (p.marked[row.name] && !row.up) { cls += ' fc-marked'; }
            if (i == p.cursor) { cls += ' fc-cursor'; }
            if (row.up) { return '<tr class="' + cls + '" data-i=' + i + '><td class=fc-name><span class="fc-icon fileIcon2"></span>..</td><td class=fc-r></td><td>Up</td><td></td></tr>'; }
            var icon = (row.kind == 'drive') ? ((row.dt == 'REMOVABLE') ? 5 : ((row.dt == 'CDROM') ? 6 : 1)) : ((row.kind == 'dir') ? 2 : 3);
            var size = (row.kind == 'file') ? sizeStr(row.size) : ((row.kind == 'drive') && row.size ? (sizeStr(row.free) + ' free') : '');
            var date = (row.date != null) ? esc(host.formatDate(new Date(row.date))) : '';
            return '<tr class="' + cls + '" data-i=' + i + ' draggable=true><td class=fc-name title="' + esc(row.name) + '"><span class="fc-icon fileIcon' + icon + '"></span>' + esc(row.name) + '</td><td class=fc-r>' + esc(size) + '</td><td>' + esc(fileType(row)) + '</td><td>' + date + '</td></tr>';
        }

        function renderRows(p) {
            var x = [];
            for (var i = 0; i < p.rows.length; i++) { x.push(rowHtml(p, p.rows[i], i)); }
            p.el.tbody.innerHTML = x.join('');
            var ths = p.el.table.tHead.rows[0].cells;
            for (var j = 0; j < ths.length; j++) {
                var k = ths[j].getAttribute('data-k');
                ths[j].classList.toggle('fc-sorted', k == p.sortKey);
                ths[j].setAttribute('data-dir', (k == p.sortKey) ? (p.sortDir > 0 ? 'asc' : 'desc') : '');
            }
            renderStatus(p);
            if (p.idx == activeIdx) { renderButtons(); }
        }

        // Update selection and cursor without rebuilding the rows, so double clicks land on the same element
        function renderMarks(p) {
            var trs = p.el.tbody.rows;
            for (var i = 0; i < trs.length; i++) {
                var row = p.rows[i];
                trs[i].classList.toggle('fc-marked', !!(row && !row.up && p.marked[row.name]));
                trs[i].classList.toggle('fc-cursor', i == p.cursor);
            }
            renderStatus(p);
            if (p.idx == activeIdx) { renderButtons(); }
        }

        function renderPane(p) {
            renderSrc(p);
            renderDrives(p);
            renderPath(p);
            var e = p.el, msg = '';
            if (p.message) { msg = esc(p.message); }
            else if ((p.type == 'local') && (p.stack.length == 0)) {
                if (!localSupported) { msg = 'This browser cannot open folders on this computer. Use Chrome or Edge, or drag files from your desktop onto the device pane.'; }
                else {
                    msg = '<button class="fc-btn fc-primary fc-pick">Choose a folder on this computer</button>';
                    if (recentLocal.length > 0) { msg += '<div class=fc-recent>Recent: ' + recentLocal.map(function (hd, i) { return '<button class="fc-btn fc-reopen" data-i=' + i + '>' + esc(hd.name) + '</button>'; }).join(' ') + '</div>'; }
                    msg += '<div class=fc-hint>The folder stays on this computer. Files are copied to and from the device through this browser.</div>';
                }
            }
            e.empty.innerHTML = msg;
            e.empty.style.display = msg ? '' : 'none';
            e.table.style.display = msg ? 'none' : '';
            var pick = e.empty.querySelector('.fc-pick');
            if (pick) { pick.onclick = function () { chooseLocalFolder(p); }; }
            Array.prototype.forEach.call(e.empty.querySelectorAll('.fc-reopen'), function (b) { b.onclick = function () { chooseLocalFolder(p, recentLocal[parseInt(b.getAttribute('data-i'))]); }; });
            e.path.disabled = (p.type == 'local') && (p.stack.length == 0);
            renderRows(p);
            fit();
        }

        function renderStatus(p) {
            var dirs = 0, filesCount = 0, bytes = 0, sel = 0, selBytes = 0;
            p.items.forEach(function (x) {
                if (x.kind == 'file') { filesCount++; bytes += x.size || 0; } else { dirs++; }
                if (p.marked[x.name]) { sel++; if (x.kind == 'file') { selBytes += x.size || 0; } }
            });
            var s = '';
            if (p.loading) { s = 'Loading...'; }
            else if (p.items.length > 0) {
                s = dirs + ' folder' + (dirs == 1 ? '' : 's') + ', ' + filesCount + ' file' + (filesCount == 1 ? '' : 's') + ' (' + sizeStr(bytes) + ')';
                if (sel > 0) { s = sel + ' selected (' + sizeStr(selBytes) + ') of ' + s; }
                if ((p.type == 'remote') && host.isWindows() && (p.segs.length > 0) && remoteDrives) {
                    var d = remoteDrives.filter(function (x) { return x.name == p.segs[0]; })[0];
                    if (d && d.size) { s += ' — ' + sizeStr(d.free) + ' free of ' + sizeStr(d.size); }
                }
            }
            if (p.flash) { s = p.flash + (s ? ' — ' + s : ''); }
            p.el.status.textContent = s;
            p.el.status.classList.toggle('fc-error', !!p.flash && !p.flashInfo);
        }

        function flash(p, msg, info) {
            p.flash = msg;
            p.flashInfo = !!info;
            renderStatus(p);
            clearTimeout(p.flashTimer);
            p.flashTimer = setTimeout(function () { p.flash = null; renderStatus(p); }, 6000);
        }

        function scrollToCursor(p) {
            var tr = p.el.tbody.rows[p.cursor];
            if (tr == null) return;
            var sc = p.el.scroll, head = p.el.table.tHead.offsetHeight;
            if (tr.offsetTop - head < sc.scrollTop) { sc.scrollTop = tr.offsetTop - head; }
            else if (tr.offsetTop + tr.offsetHeight > sc.scrollTop + sc.clientHeight) { sc.scrollTop = tr.offsetTop + tr.offsetHeight - sc.clientHeight; }
        }

        var keyDefs = [
            { k: 'F2', t: 'Rename', f: function () { renameCmd(); }, en: function (p) { return selectedRows(p).length == 1; } },
            { k: 'F3', t: 'Download', f: function () { downloadToBrowser(activePane()); }, en: function (p) { return (p.type == 'remote') && selectedRows(p).some(function (x) { return x.kind == 'file'; }); } },
            { k: 'F4', t: 'Edit', f: function () { editCmd(); }, en: function (p) { var s = selectedRows(p); return (s.length == 1) && (s[0].kind == 'file'); } },
            { k: 'F5', t: 'Copy', f: function () { copyCmd(false); }, en: function (p) { return canTransfer(p); } },
            { k: 'F6', t: 'Move', f: function () { copyCmd(true); }, en: function (p) { return canTransfer(p); } },
            { k: 'F7', t: 'New Folder', f: function () { mkdirCmd(); }, en: function (p) { return canWrite(p); } },
            { k: 'F8', t: 'Delete', f: function () { deleteCmd(); }, en: function (p) { return canWrite(p) && selectedRows(p).length > 0; } },
            { k: 'S-F4', t: 'New File', f: function () { mkfileCmd(); }, en: function (p) { return canWrite(p); } },
            { k: '', t: 'Upload', f: function () { uploadPickCmd(); }, en: function (p) { return (p.type == 'remote') && canWrite(p); } },
            { k: '', t: 'Zip', f: function () { zipCmd(); }, en: function (p) { return (p.type == 'remote') && !host.isSftp() && canWrite(p) && selectedRows(p).length > 0; } },
            { k: '', t: 'Unzip', f: function () { unzipCmd(); }, en: function (p) { var s = selectedRows(p); return (p.type == 'remote') && !host.isSftp() && (s.length == 1) && /\.zip$/i.test(s[0].name); } },
            { k: 'C-R', t: 'Refresh', f: function () { refreshAll(); }, en: function () { return true; } }
        ];

        function canWrite(p) {
            if (p.type == 'local') return (p.stack.length > 0);
            return connected() && (!host.isWindows() || (p.segs.length > 0)); // The Windows root only lists drives
        }
        function canTransfer(p) {
            var o = other(p);
            if (selectedRows(p).length == 0 || !canWrite(o)) return false;
            if ((p.type == 'remote') && (o.type == 'remote') && host.isSftp()) return false;
            return true;
        }

        function renderButtons() {
            if (!obj.keysEl || panes.length < 2) return;
            var p = activePane(), x = '';
            keyDefs.forEach(function (d, i) {
                var label = d.t;
                if ((d.t == 'Copy') || (d.t == 'Move')) { label += ' ' + ((p.idx == 0) ? '→' : '←'); }
                x += '<button class=fc-key data-i=' + i + (d.en(p) ? '' : ' disabled') + '>' + (d.k ? '<b>' + esc(d.k.replace('S-', 'Shift+').replace('C-', 'Ctrl+')) + '</b> ' : '') + esc(label) + '</button>';
            });
            obj.keysEl.innerHTML = x;
        }

        //
        // Events
        //

        function rowIndex(ev) { var tr = ev.target.closest('tr.fc-row'); return tr ? parseInt(tr.getAttribute('data-i')) : -1; }

        function wirePane(p) {
            var e = p.el;
            e.pane.addEventListener('mousedown', function () { if (activeIdx != p.idx) { setActive(p.idx); } });
            e.src.onchange = function () { setPaneType(p, e.src.value); };
            e.drives.onchange = function () {
                var v = e.drives.value;
                if (p.type == 'remote') { loadRemote(p, (v == ':root') ? [] : [v]); }
                else if (v == ':pick') { chooseLocalFolder(p); }
                else { chooseLocalFolder(p, recentLocal[parseInt(v)]); }
            };
            e.up.onclick = function () { goUp(p); };
            e.rootBtn.onclick = function () { goRoot(p); };
            e.refresh.onclick = function () { refresh(p); };
            e.path.onkeydown = function (ev) {
                if (ev.key == 'Enter') { ev.preventDefault(); gotoPath(p, e.path.value); e.scroll.focus(); }
                else if (ev.key == 'Escape') { renderPath(p); e.scroll.focus(); }
                ev.stopPropagation();
            };
            e.table.tHead.onclick = function (ev) {
                var th = ev.target.closest('th'); if (!th) return;
                var k = th.getAttribute('data-k');
                if (p.sortKey == k) { p.sortDir = -p.sortDir; } else { p.sortKey = k; p.sortDir = 1; }
                var name = (p.rows[p.cursor] || {}).name;
                sortItems(p);
                p.cursor = Math.max(0, p.rows.findIndex(function (r) { return r.name == name; }));
                renderRows(p);
                saveState();
            };
            e.tbody.addEventListener('mousedown', function (ev) {
                var i = rowIndex(ev); if (i < 0) return;
                setActive(p.idx);
                if (ev.button == 2) { if (!p.rows[i].up && !p.marked[p.rows[i].name]) { p.marked = {}; p.marked[p.rows[i].name] = 1; } p.cursor = i; renderMarks(p); return; }
                if (ev.shiftKey) { setCursor(p, i, true); }
                else if (ev.ctrlKey || ev.metaKey) { toggleMark(p, i); p.anchor = i; p.cursor = i; renderMarks(p); }
                else if (!p.marked[(p.rows[i] || {}).name]) { p.marked = {}; toggleMark(p, i); setCursor(p, i); }
                else { p.cursor = i; p.anchor = i; renderMarks(p); }
            });
            e.tbody.addEventListener('click', function (ev) {
                // A plain click on a row that was already part of a multi selection narrows the selection to it
                var i = rowIndex(ev); if ((i < 0) || ev.shiftKey || ev.ctrlKey || ev.metaKey) return;
                if (p.marked[(p.rows[i] || {}).name] && Object.keys(p.marked).length > 1 && !p.dragged) { p.marked = {}; toggleMark(p, i); renderMarks(p); }
                p.dragged = false;
            });
            e.tbody.addEventListener('dblclick', function (ev) { var i = rowIndex(ev); if (i >= 0) { openRow(p, p.rows[i]); } });
            e.scroll.addEventListener('contextmenu', function (ev) { ev.preventDefault(); setActive(p.idx); showMenu(p, ev.clientX, ev.clientY); });
            e.scroll.addEventListener('keydown', function (ev) { onKey(p, ev); });
            e.scroll.addEventListener('focus', function () { if (activeIdx != p.idx) { setActive(p.idx); } });

            // Drag rows to the other pane
            e.tbody.addEventListener('dragstart', function (ev) {
                var i = rowIndex(ev); if ((i < 0) || p.rows[i].up) { ev.preventDefault(); return; }
                if (!p.marked[p.rows[i].name]) { p.marked = {}; p.marked[p.rows[i].name] = 1; renderMarks(p); }
                p.dragged = true;
                dragSource = p;
                ev.dataTransfer.effectAllowed = 'copyMove';
                ev.dataTransfer.setData('text/plain', selectedRows(p).map(function (r) { return r.name; }).join('\n'));
            });
            e.tbody.addEventListener('dragend', function () { dragSource = null; });
            e.pane.addEventListener('dragover', function (ev) {
                if ((dragSource === p) || !canWrite(p)) return;
                if ((dragSource == null) && !(ev.dataTransfer && Array.prototype.indexOf.call(ev.dataTransfer.types, 'Files') >= 0)) return;
                ev.preventDefault(); ev.stopPropagation();
                ev.dataTransfer.dropEffect = (dragSource && ev.shiftKey) ? 'move' : 'copy';
                e.pane.classList.add('fc-drop');
            });
            e.pane.addEventListener('dragleave', function (ev) { if (!e.pane.contains(ev.relatedTarget)) { e.pane.classList.remove('fc-drop'); } });
            e.pane.addEventListener('drop', function (ev) {
                e.pane.classList.remove('fc-drop');
                if ((dragSource === p) || !canWrite(p)) return;
                ev.preventDefault(); ev.stopPropagation();
                if (dragSource != null) { var src = dragSource; dragSource = null; setActive(src.idx); copyCmd(ev.shiftKey); return; }
                dropFromDesktop(p, ev.dataTransfer);
            });
        }

        function wireSplitter(panesEl) {
            var split = panesEl.querySelector('.fc-split');
            var ratio = storeGet('fcSplit', 0.5);
            function apply() { panes[0].el.pane.style.flexBasis = (ratio * 100) + '%'; panes[1].el.pane.style.flexBasis = ((1 - ratio) * 100) + '%'; }
            apply();
            split.addEventListener('mousedown', function (ev) {
                ev.preventDefault();
                var r = panesEl.getBoundingClientRect();
                function move(e2) { ratio = Math.max(0.15, Math.min(0.85, (e2.clientX - r.left) / r.width)); apply(); }
                function up() { document.removeEventListener('mousemove', move); document.removeEventListener('mouseup', up); storeSet('fcSplit', ratio); }
                document.addEventListener('mousemove', move);
                document.addEventListener('mouseup', up);
            });
            split.addEventListener('dblclick', function () { ratio = 0.5; apply(); storeSet('fcSplit', ratio); });
        }

        function onKey(p, ev) {
            if (modalEl) return;
            var page = Math.max(1, Math.floor(p.el.scroll.clientHeight / 22) - 1), handled = true, k = ev.key;
            if (k == 'ArrowDown') { setCursor(p, p.cursor + 1, ev.shiftKey); }
            else if (k == 'ArrowUp') { setCursor(p, p.cursor - 1, ev.shiftKey); }
            else if (k == 'PageDown') { setCursor(p, p.cursor + page, ev.shiftKey); }
            else if (k == 'PageUp') { setCursor(p, p.cursor - page, ev.shiftKey); }
            else if (k == 'Home') { setCursor(p, 0, ev.shiftKey); }
            else if (k == 'End') { setCursor(p, p.rows.length - 1, ev.shiftKey); }
            else if (k == 'Enter') { openRow(p, p.rows[p.cursor]); }
            else if (k == 'Backspace') { goUp(p); }
            else if (k == 'Tab') { setActive(1 - p.idx); panes[activeIdx].el.scroll.focus(); }
            else if ((k == ' ') || (k == 'Insert')) { toggleMark(p, p.cursor); setCursor(p, p.cursor + 1); }
            else if ((k == 'a' || k == 'A') && (ev.ctrlKey || ev.metaKey)) { p.marked = {}; p.rows.forEach(function (r) { if (!r.up) { p.marked[r.name] = 1; } }); renderMarks(p); }
            else if ((k == 'r' || k == 'R') && (ev.ctrlKey || ev.metaKey)) { refresh(p); }
            else if (k == 'Escape') { p.marked = {}; renderMarks(p); }
            else if (k == 'F2') { renameCmd(); }
            else if (k == 'F3') { downloadToBrowser(p); }
            else if ((k == 'F4') && ev.shiftKey) { mkfileCmd(); }
            else if (k == 'F4') { editCmd(); }
            else if (k == 'F5') { copyCmd(false); }
            else if (k == 'F6') { copyCmd(true); }
            else if (k == 'F7') { mkdirCmd(); }
            else if ((k == 'F8') || (k == 'Delete')) { deleteCmd(); }
            else { handled = false; }
            if (handled) { ev.preventDefault(); ev.stopPropagation(); }
        }

        //
        // Context menu and dialogs
        //

        function closeMenu() { if (menuEl) { menuEl.remove(); menuEl = null; } }

        function showMenu(p, x, y) {
            closeMenu();
            var items = [];
            var row = p.rows[p.cursor], sel = selectedRows(p);
            if (row && (row.up || row.kind != 'file')) { items.push(['Open', function () { openRow(p, row); }]); }
            keyDefs.forEach(function (d) { if ((d.t != 'Refresh') && d.en(p)) { items.push([d.t + (((d.t == 'Copy') || (d.t == 'Move')) ? (p.idx == 0 ? ' →' : ' ←') : ''), d.f]); } });
            if ((p.type == 'remote') && !host.isSftp() && (sel.length == 1) && host.openOnDevice) {
                items.push(['Open on device desktop', async function () {
                    if ((await modal('Open', 'Open <b>' + esc(sel[0].name) + '</b> on the desktop of the remote device?', [['Open', true, true], ['Cancel', false]])) !== true) return;
                    var path = rPathNoSlash(p.segs.concat([sel[0].name]));
                    host.openOnDevice(host.isWindows() ? path.replace(/\//g, '\\') : path, sel[0].kind != 'file');
                }]);
            }
            if (sel.length > 0) { items.push(['Copy path', function () { copyPaths(p, sel); }]); }
            items.push(['Select all', function () { p.marked = {}; p.rows.forEach(function (r) { if (!r.up) { p.marked[r.name] = 1; } }); renderMarks(p); }]);
            items.push(['Refresh', function () { refresh(p); }]);
            menuEl = h('div', 'fc-menu');
            items.forEach(function (it) { var b = h('div', 'fc-menu-item'); b.textContent = it[0]; b.onclick = function () { closeMenu(); it[1](); }; menuEl.append(b); });
            root.append(menuEl);
            var r = root.getBoundingClientRect();
            var left = Math.min(x - r.left, r.width - menuEl.offsetWidth - 4), top = Math.min(y - r.top, r.height - menuEl.offsetHeight - 4);
            menuEl.style.left = Math.max(0, left) + 'px';
            menuEl.style.top = Math.max(0, top) + 'px';
        }

        function copyPaths(p, sel) {
            var base = (p.type == 'remote') ? rDisplay(p.segs) : paneLabel(p);
            var sep = ((p.type == 'remote') && !host.isWindows()) ? '/' : '\\';
            if (!base.endsWith(sep)) { base += sep; }
            var text = sel.map(function (r) { return base + r.name; }).join('\r\n');
            try { navigator.clipboard.writeText(text); flash(p, 'Path copied', true); } catch (ex) { }
        }

        // buttons: [[label, value, primary]], body: html. Resolves with the value of the button,
        // or { value, text } when an input is shown.
        function modal(title, body, buttons, input) {
            return new Promise(function (resolve) {
                closeMenu();
                if (modalEl) { modalEl.remove(); }
                modalEl = h('div', 'fc-modal-bg');
                var box = h('div', 'fc-modal');
                box.append(h('div', 'fc-modal-title', esc(title)));
                var content = h('div', 'fc-modal-body', body || '');
                box.append(content);
                var inp = null;
                if (input) {
                    inp = h(input.multiline ? 'textarea' : 'input', input.multiline ? 'fc-editor' : 'fc-input');
                    if (!input.multiline) { inp.type = 'text'; }
                    inp.spellcheck = false;
                    inp.value = input.value || '';
                    content.append(inp);
                }
                var bar = h('div', 'fc-modal-buttons');
                function done(v) {
                    if (modalEl == null) return;
                    modalEl.remove(); modalEl = null;
                    var p = activePane(); if (p) { p.el.scroll.focus(); }
                    resolve(inp ? { value: v, text: inp.value } : v);
                }
                buttons.forEach(function (b) { var x = h('button', 'fc-btn' + (b[2] ? ' fc-primary' : '')); x.textContent = b[0]; x.onclick = function () { done(b[1]); }; bar.append(x); });
                box.append(bar);
                modalEl.append(box);
                modalEl.addEventListener('keydown', function (ev) {
                    ev.stopPropagation();
                    if (ev.key == 'Escape') { ev.preventDefault(); done(null); }
                    else if ((ev.key == 'Enter') && !(input && input.multiline)) { ev.preventDefault(); var pr = buttons.filter(function (b) { return b[2]; })[0]; done(pr ? pr[1] : null); }
                    else if ((ev.key == 's') && (ev.ctrlKey || ev.metaKey) && input && input.multiline) { ev.preventDefault(); done('save'); }
                });
                root.append(modalEl);
                if (inp) {
                    inp.focus();
                    if (!input.multiline) { var dot = inp.value.lastIndexOf('.'); inp.setSelectionRange(0, (input.selectStem && dot > 0) ? dot : inp.value.length); }
                } else { var f = bar.querySelector('.fc-primary') || bar.firstChild; if (f) { f.focus(); } }
            });
        }

        function alertBox(title, msg) { return modal(title, esc(msg), [['OK', true, true]]); }

        function validName(n) { return (n != null) && (n.trim() != '') && !/[\\\/:*?"<>|]/.test(n) && (n != '.') && (n != '..'); }

        //
        // Commands
        //

        function busyCheck() {
            if (job || upload || download) { alertBox('File Commander', 'Wait for the current transfer to finish.'); return true; }
            return false;
        }

        async function mkdirCmd() {
            var p = activePane();
            if (!canWrite(p) || busyCheck()) return;
            var r = await modal('New Folder', 'Folder name', [['Create', 'ok', true], ['Cancel', null]], { value: 'New Folder' });
            if ((r.value != 'ok') || !validName(r.text)) { if (r.value == 'ok') { flash(p, 'Invalid name'); } return; }
            try {
                if (p.type == 'remote') { rSend({ action: 'mkdir', reqid: 1, path: joinRemote(p.segs, r.text) }); }
                else { await p.stack[p.stack.length - 1].getDirectoryHandle(r.text, { create: true }); }
            } catch (ex) { flash(p, ex.message); }
            refresh(p, r.text);
        }

        async function mkfileCmd() {
            var p = activePane();
            if (!canWrite(p) || busyCheck()) return;
            var r = await modal('New File', 'File name', [['Create', 'ok', true], ['Cancel', null]], { value: 'New File.txt', selectStem: true });
            if ((r.value != 'ok') || !validName(r.text)) { if (r.value == 'ok') { flash(p, 'Invalid name'); } return; }
            try {
                if (p.type == 'remote') { rSend({ action: 'mkfile', reqid: 1, path: joinRemote(p.segs, r.text) }); }
                else { await p.stack[p.stack.length - 1].getFileHandle(r.text, { create: true }); }
            } catch (ex) { flash(p, ex.message); }
            refresh(p, r.text);
        }

        async function renameCmd() {
            var p = activePane(), sel = selectedRows(p);
            if ((sel.length != 1) || (sel[0].kind == 'drive') || busyCheck()) return;
            var item = sel[0];
            var r = await modal('Rename', 'New name for ' + esc(item.name), [['Rename', 'ok', true], ['Cancel', null]], { value: item.name, selectStem: (item.kind == 'file') });
            if ((r.value != 'ok') || (r.text == item.name)) return;
            if (!validName(r.text)) { flash(p, 'Invalid name'); return; }
            try {
                if (p.type == 'remote') { rSend({ action: 'rename', reqid: 1, path: rPath(p.segs), oldname: item.name, newname: r.text }); }
                else if (typeof item.handle.move == 'function') { await item.handle.move(r.text); }
                else { throw new Error('This browser cannot rename local files'); }
                p.marked = {};
            } catch (ex) { flash(p, ex.message); }
            refresh(p, r.text);
        }

        async function deleteCmd() {
            var p = activePane(), sel = selectedRows(p).filter(function (x) { return x.kind != 'drive'; });
            if ((sel.length == 0) || !canWrite(p) || busyCheck()) return;
            var dirs = sel.filter(function (x) { return x.kind == 'dir'; }).length;
            var msg = (sel.length == 1) ? ('Delete <b>' + esc(sel[0].name) + '</b>' + (dirs ? ' and everything in it' : '') + '?') : ('Delete ' + sel.length + ' items' + (dirs ? ', including ' + dirs + ' folder' + (dirs > 1 ? 's' : '') + ' and everything in them' : '') + '?');
            msg += '<div class=fc-where>' + esc(paneLabel(p)) + '</div>';
            if ((await modal('Delete', msg, [['Delete', true, true], ['Cancel', false]])) !== true) return;
            try {
                if (p.type == 'remote') { rSend({ action: 'rm', reqid: 1, path: rPath(p.segs), delfiles: sel.map(function (x) { return x.name; }), rec: true }); }
                else { var dir = p.stack[p.stack.length - 1]; for (var i = 0; i < sel.length; i++) { await dir.removeEntry(sel[i].name, { recursive: true }); } }
                p.marked = {};
            } catch (ex) { flash(p, ex.message); }
            refresh(p);
            var o = other(p);
            if ((o.type == p.type) && (paneLabel(o).indexOf(paneLabel(p)) == 0)) { refresh(o); }
        }

        async function zipCmd() {
            var p = activePane(), sel = selectedRows(p);
            if ((p.type != 'remote') || (sel.length == 0) || busyCheck()) return;
            var def = ((sel.length == 1) ? sel[0].name.replace(/\.[^.]*$/, '') : (p.segs[p.segs.length - 1] || 'archive').replace(':', '')) + '.zip';
            var r = await modal('Zip', 'Archive name', [['Zip', 'ok', true], ['Cancel', null]], { value: def, selectStem: true });
            if ((r.value != 'ok') || !validName(r.text)) return;
            var out = r.text.toLowerCase().endsWith('.zip') ? r.text : (r.text + '.zip');
            rSend({ action: 'zip', path: rPathNoSlash(p.segs), files: sel.map(function (x) { return x.name; }), output: out });
        }

        async function unzipCmd() {
            var p = activePane(), sel = selectedRows(p);
            if ((p.type != 'remote') || (sel.length != 1) || busyCheck()) return;
            var sep = host.isWindows() ? '\\' : '/';
            var base = rDisplay(p.segs); if (!base.endsWith(sep)) { base += sep; }
            var r = await modal('Unzip', 'Extract to folder', [['Unzip', 'ok', true], ['Cancel', null]], { value: base + sel[0].name.replace(/\.zip$/i, '') + sep });
            if ((r.value != 'ok') || (r.text.trim() == '')) return;
            rSend({ action: 'unzip', input: base + sel[0].name, dest: r.text });
        }

        function joinRemote(segs, name) { return rPathNoSlash(segs.concat([name])); }

        function downloadToBrowser(p, rows) {
            if (!p || (p.type != 'remote')) return;
            rows = (rows || selectedRows(p)).filter(function (x) { return x.kind == 'file'; });
            if (rows.length == 0) return;
            var segs = p.segs.slice(), tunnel = [];
            rows.forEach(function (row) {
                var url = host.downloadUrl ? host.downloadUrl(joinRemote(segs, row.name), row.name) : null;
                if (url) { host.downloadFile(url, row.name); } else { tunnel.push(row); }
            });
            if ((tunnel.length == 0) || busyCheck()) return;
            // No direct link (SFTP or a local device), pull the files through the tunnel
            runJob('Downloading', async function (j) {
                for (var i = 0; i < tunnel.length; i++) {
                    var row = tunnel[i], chunks = [];
                    if (j.canceled) throw cancelError();
                    j.current = row.name; j.curBytes = 0; j.curSize = row.size; renderJob();
                    var sink = { write: function (b) { chunks.push(b); return Promise.resolve(); }, close: function () { return Promise.resolve(); }, abort: function () { chunks = []; } };
                    await rDownload(joinRemote(segs, row.name), row.size, sink, function (got) { j.curBytes = got; renderJob(); });
                    if (typeof saveAs == 'function') { saveAs(new Blob(chunks), row.name); }
                    j.files++; j.bytes += row.size || 0;
                }
            });
        }

        async function uploadPickCmd() {
            var p = activePane();
            if ((p.type != 'remote') || !canWrite(p) || busyCheck()) return;
            var inp = document.createElement('input');
            inp.type = 'file'; inp.multiple = true;
            inp.onchange = function () { if (inp.files.length > 0) { startCopy(Array.prototype.map.call(inp.files, fileSource), p, false, 'Upload'); } };
            inp.click();
        }

        async function editCmd() {
            var p = activePane(), sel = selectedRows(p);
            if ((sel.length != 1) || (sel[0].kind != 'file') || busyCheck()) return;
            var row = sel[0];
            if ((row.size || 0) > maxEditSize) { alertBox('Edit', 'Only files smaller than ' + sizeStr(maxEditSize) + ' can be edited.'); return; }
            var bytes;
            try {
                if (p.type == 'remote') {
                    var sink = memorySink();
                    flash(p, 'Loading ' + row.name + '...', true);
                    await rDownload(joinRemote(p.segs, row.name), row.size, sink);
                    bytes = new Uint8Array(await sink.blob().arrayBuffer());
                } else {
                    bytes = new Uint8Array(await (await row.handle.getFile()).arrayBuffer());
                }
            } catch (ex) { flash(p, ex.message); return; }
            var text = new TextDecoder('utf-8').decode(bytes);
            var crlf = (text.match(/\r\n/g) || []).length, lf = (text.match(/\n/g) || []).length - crlf;
            var r = await modal('Edit - ' + row.name, '<div class=fc-where>' + esc(paneLabel(p)) + '</div>', [['Save', 'save', false], ['Close', null]], { multiline: true, value: text });
            if (r.value != 'save') return;
            var out = r.text;
            if (crlf > lf) { out = out.replace(/\r?\n/g, '\r\n'); }
            var blob = new Blob([new TextEncoder().encode(out)]);
            try {
                if (p.type == 'remote') { await rUpload(rPath(p.segs), row.name, blob); }
                else { var w = await row.handle.createWritable(); await w.write(blob); await w.close(); }
                flash(p, 'Saved ' + row.name, true);
            } catch (ex) { flash(p, 'Save failed: ' + ex.message); }
            refresh(p, row.name);
        }

        //
        // Copy / move engine
        //

        // A source item: { name, kind: 'file'|'dir', size, remote: { segs }, getFile(), children(), remove() }
        function remoteSource(segs, item) {
            return {
                name: item.name, kind: (item.kind == 'file') ? 'file' : 'dir', size: item.size, remote: { segs: segs },
                children: function () {
                    var s = segs.concat([item.name]);
                    return rList(rPath(s)).then(function (dir) { if (dir == null) { throw new Error('Unable to open ' + rDisplay(s)); } return dir.map(function (f) { return remoteSource(s, remoteItem(f)); }); });
                },
                remove: function () { rSend({ action: 'rm', reqid: 1, path: rPath(segs), delfiles: [item.name], rec: true }); return Promise.resolve(); }
            };
        }

        function handleSource(handle, parent, size) {
            return {
                name: handle.name, kind: (handle.kind == 'directory') ? 'dir' : 'file', size: size,
                getFile: function () { return handle.getFile(); },
                children: async function () { var r = []; for await (var c of handle.values()) { r.push(handleSource(c, handle)); } return r; },
                remove: function () { if (parent == null) { throw new Error('Unable to remove ' + handle.name); } return parent.removeEntry(handle.name, { recursive: true }); }
            };
        }

        function fileSource(file) {
            return { name: file.name, kind: 'file', size: file.size, getFile: function () { return Promise.resolve(file); }, remove: function () { return Promise.resolve(); } };
        }

        function entrySource(entry) {
            if (entry.isFile) { return { name: entry.name, kind: 'file', size: null, getFile: function () { return new Promise(function (res, rej) { entry.file(res, rej); }); }, remove: function () { return Promise.resolve(); } }; }
            return {
                name: entry.name, kind: 'dir',
                children: function () {
                    return new Promise(function (resolve, reject) {
                        var reader = entry.createReader(), all = [];
                        (function next() { reader.readEntries(function (list) { if (list.length == 0) { resolve(all.map(entrySource)); } else { all = all.concat(list); next(); } }, reject); })();
                    });
                },
                remove: function () { return Promise.resolve(); }
            };
        }

        // A destination: { remote: { segs } | local: dirHandle, names(), mkdir(name), writeFile(name, src, onProgress, move) }
        function remoteDest(segs) {
            return {
                remote: { segs: segs }, label: rDisplay(segs),
                names: function () { return rList(rPath(segs)).then(function (dir) { return (dir || []).map(function (f) { return f.n; }); }); },
                mkdir: function (name) { rSend({ action: 'mkdir', reqid: 1, path: joinRemote(segs, name) }); return Promise.resolve(remoteDest(segs.concat([name]))); },
                writeFile: async function (name, src, onProgress, move) {
                    if (src.remote) {
                        rSend({ action: move ? 'move' : 'copy', reqid: 1, scpath: rPath(src.remote.segs), dspath: rPath(segs), names: [name] });
                        return true; // The device copied or moved it on its own
                    }
                    var file = await src.getFile();
                    await rUpload(rPath(segs), name, file, onProgress);
                    return false;
                }
            };
        }

        function localDest(dir) {
            return {
                local: dir, label: dir.name,
                names: async function () { var r = []; for await (var k of dir.keys()) { r.push(k); } return r; },
                mkdir: async function (name) { return localDest(await dir.getDirectoryHandle(name, { create: true })); },
                writeFile: async function (name, src, onProgress) {
                    if (src.remote) {
                        var sink = await localSink(dir, name);
                        await rDownload(joinRemote(src.remote.segs, name), src.size, sink, onProgress);
                        return false;
                    }
                    var file = await src.getFile();
                    var fh = await dir.getFileHandle(name, { create: true });
                    var w = await fh.createWritable();
                    try { await w.write(file); await w.close(); } catch (ex) { try { await w.abort(); } catch (e2) { } throw ex; }
                    if (onProgress) { onProgress(file.size, file.size); }
                    return false;
                }
            };
        }

        function destFor(p) { return (p.type == 'remote') ? remoteDest(p.segs.slice()) : localDest(p.stack[p.stack.length - 1]); }

        function sourcesFor(p, rows) {
            if (p.type == 'remote') { var segs = p.segs.slice(); return rows.map(function (r) { return remoteSource(segs, r); }); }
            var parent = p.stack[p.stack.length - 1];
            return rows.map(function (r) { return handleSource(r.handle, parent, r.size); });
        }

        async function copyCmd(move) {
            var p = activePane(), o = other(p);
            var rows = selectedRows(p).filter(function (x) { return x.kind != 'drive'; });
            if ((rows.length == 0) || !canTransfer(p) || busyCheck()) return;
            if ((p.type == o.type) && (paneLabel(p) == paneLabel(o)) && ((p.type == 'remote') || (p.stack[p.stack.length - 1] === o.stack[o.stack.length - 1]))) { alertBox(move ? 'Move' : 'Copy', 'The source and destination folders are the same.'); return; }
            if ((p.type == 'remote') && (o.type == 'remote')) {
                var dst = rPath(o.segs).toLowerCase();
                for (var i = 0; i < rows.length; i++) {
                    if ((rows[i].kind == 'dir') && ((dst + '/').indexOf(rPath(p.segs.concat([rows[i].name])).toLowerCase() + '/') == 0)) { alertBox(move ? 'Move' : 'Copy', 'A folder cannot be copied into itself.'); return; }
                }
            }
            var verb = move ? 'Move' : 'Copy';
            var what = (rows.length == 1) ? ('<b>' + esc(rows[0].name) + '</b>') : (rows.length + ' items');
            var msg = verb + ' ' + what + ' to<div class=fc-where>' + esc(o.type == 'remote' ? (host.nodeName() + ': ' + paneLabel(o)) : ('This computer: ' + paneLabel(o))) + '</div>';
            if ((await modal(verb, msg, [[verb, true, true], ['Cancel', false]])) !== true) return;
            startCopy(sourcesFor(p, rows), o, move, verb, p);
        }

        async function dropFromDesktop(p, dt) {
            if (busyCheck()) return;
            var sources = [], items = dt.items ? Array.prototype.slice.call(dt.items) : [];
            var handles = items.filter(function (it) { return it.kind == 'file'; });
            if ((handles.length > 0) && (typeof handles[0].getAsFileSystemHandle == 'function')) {
                var hs = await Promise.all(handles.map(function (it) { return it.getAsFileSystemHandle(); }));
                hs.forEach(function (hd) { if (hd) { sources.push(handleSource(hd, null)); } });
            } else if ((handles.length > 0) && (typeof handles[0].webkitGetAsEntry == 'function')) {
                handles.forEach(function (it) { var en = it.webkitGetAsEntry(); if (en) { sources.push(entrySource(en)); } });
            } else {
                Array.prototype.forEach.call(dt.files || [], function (f) { sources.push(fileSource(f)); });
            }
            if (sources.length == 0) return;
            startCopy(sources, p, false, 'Upload');
        }

        function startCopy(sources, destPane, move, verb, srcPane) {
            var dest = destFor(destPane);
            runJob(move ? 'Moving' : (verb == 'Upload' ? 'Uploading' : 'Copying'), async function (j) {
                j.policy = null;
                j.caseless = (destPane.type == 'remote') ? caseless() : true;
                await copyInto(j, sources, dest, move);
            }, function () {
                refresh(destPane);
                if (srcPane && move) { srcPane.marked = {}; refresh(srcPane); }
            });
        }

        async function copyInto(j, sources, dest, move) {
            var existing = null;
            async function exists(name) {
                if (existing == null) { try { existing = (await dest.names()).map(function (n) { return j.caseless ? n.toLowerCase() : n; }); } catch (ex) { existing = []; } }
                return existing.indexOf(j.caseless ? name.toLowerCase() : name) >= 0;
            }
            for (var i = 0; i < sources.length; i++) {
                var s = sources[i];
                if (j.canceled) throw cancelError();
                if (s.kind == 'dir') {
                    var errorsBefore = j.errors.length + j.skipped;
                    try {
                        var sub = await dest.mkdir(s.name);
                        await copyInto(j, await s.children(), sub, move);
                        if (move && (j.errors.length + j.skipped == errorsBefore)) { await s.remove(); }
                    } catch (ex) { if (ex.canceled) throw ex; j.errors.push(s.name + ': ' + ex.message); }
                    continue;
                }
                if ((j.policy != 'overwrite') && (await exists(s.name))) {
                    var choice = j.policy;
                    if (choice == null) {
                        choice = await modal('File exists', '<b>' + esc(s.name) + '</b> already exists in<div class=fc-where>' + esc(dest.label) + '</div>', [['Overwrite', 'o1', true], ['Overwrite all', 'overwrite'], ['Skip', 's1'], ['Skip all', 'skip'], ['Cancel', null]]);
                        if (choice == null) { j.canceled = true; throw cancelError(); }
                        if ((choice == 'overwrite') || (choice == 'skip')) { j.policy = choice; }
                    }
                    if ((choice == 'skip') || (choice == 's1')) { j.skipped++; continue; }
                }
                j.current = s.name; j.curBytes = 0; j.curSize = s.size; renderJob();
                try {
                    var moved = await dest.writeFile(s.name, s, function (got, total) { j.curBytes = got; j.curSize = total; renderJob(); }, move);
                    j.files++;
                    j.bytes += (s.size != null) ? s.size : (j.curSize || 0);
                    if (move && !moved) { await s.remove(); }
                } catch (ex) { if (ex.canceled || j.canceled) throw cancelError(); j.errors.push(s.name + ': ' + ex.message); }
            }
        }

        function runJob(title, fn, after) {
            job = { title: title, files: 0, bytes: 0, skipped: 0, errors: [], current: null, curBytes: 0, curSize: 0, canceled: false };
            var j = job;
            renderJob();
            fn(j).then(function () { return null; }, function (ex) { return ex; }).then(function (ex) {
                job = null;
                if (ex && !ex.canceled) { j.errors.push(ex.message); }
                renderJob(j, ex && ex.canceled);
                if (after) { after(); }
                renderButtons();
            });
        }

        function renderJob(done, canceled) {
            var el = obj.jobEl, j = job || done;
            if (!el) return;
            if (j == null) { el.style.display = 'none'; return; }
            el.style.display = '';
            clearTimeout(obj.jobTimer);
            if (job) {
                var pct = (j.curSize > 0) ? Math.floor(j.curBytes * 100 / j.curSize) : 0;
                el.innerHTML = '<div class=fc-job-text>' + esc(j.title) + ' <b>' + esc(j.current || '') + '</b> ' + (j.curSize > 0 ? pct + '% of ' + sizeStr(j.curSize) : '') + ' &mdash; ' + j.files + ' done' + (j.skipped ? ', ' + j.skipped + ' skipped' : '') + (j.errors.length ? ', ' + j.errors.length + ' failed' : '') + '</div><progress max=100 value=' + pct + '></progress><button class="fc-btn fc-cancel">Cancel</button>';
                el.querySelector('.fc-cancel').onclick = function () { j.canceled = true; uploadCancel(); downloadCancel(); };
            } else {
                var s = (canceled ? 'Canceled' : 'Done') + ': ' + j.files + ' file' + (j.files == 1 ? '' : 's') + ' (' + sizeStr(j.bytes) + ')' + (j.skipped ? ', ' + j.skipped + ' skipped' : '') + (j.errors.length ? ', ' + j.errors.length + ' failed' : '');
                el.innerHTML = '<div class=fc-job-text' + (j.errors.length ? ' style=color:var(--fc-err)' : '') + '>' + esc(s) + '</div>' + (j.errors.length ? '<button class="fc-btn fc-details">Details</button>' : '') + '<button class="fc-btn fc-close">Close</button>';
                el.querySelector('.fc-close').onclick = function () { el.style.display = 'none'; };
                var det = el.querySelector('.fc-details');
                if (det) { det.onclick = function () { modal('Errors', '<div class=fc-errlist>' + j.errors.map(esc).join('<br>') + '</div>', [['OK', true, true]]); }; }
                if (j.errors.length == 0) { obj.jobTimer = setTimeout(function () { if (!job) { el.style.display = 'none'; } }, 6000); }
            }
        }

        //
        // Public API
        //

        obj.processData = function (data) {
            if (data == null) return false;
            if (data.action == 'refresh') { if (obj.active) { refreshAll(); } return false; }
            if ((typeof data.reqid == 'string') && (data.reqid.indexOf('fc') == 0)) {
                if ((typeof data.action == 'string') && (data.action.indexOf('upload') == 0)) { uploadMessage(data); return true; }
                var pr = pending[data.reqid];
                if (pr) { delete pending[data.reqid]; clearTimeout(pr.timer); pr.resolve(data.dir == null ? null : data.dir); }
                return true;
            }
            if ((data.action == 'download') && (typeof data.id == 'string') && (data.id.indexOf('fc') == 0)) { downloadMessage(data); return true; }
            return false;
        };

        obj.processBinary = function (data) { return downloadBlock(data); };

        obj.processBinaryString = function (str) {
            if ((download == null) || (download.state != 1)) return false;
            var b = new Uint8Array(str.length);
            for (var i = 0; i < str.length; i++) { b[i] = str.charCodeAt(i) & 0xFF; }
            return downloadBlock(b);
        };

        obj.onConnect = function () {
            remoteDrives = null;
            var saved = null;
            storeGet('fcPaths', []).forEach(function (x) { if (x.n == host.nodeId()) { saved = x.p; } });
            panes.forEach(function (p, i) {
                p.segs = (saved && Array.isArray(saved[i])) ? saved[i] : [];
                if (p.type != 'remote') return;
                p.items = []; p.rows = []; p.marked = {}; p.message = null;
                renderPane(p);
                if (obj.active) { loadRemote(p, p.segs); } // Otherwise loaded when the commander is shown
            });
            if (obj.active && host.isWindows() && !panes.some(function (p) { return (p.type == 'remote') && (p.segs.length == 0); })) {
                rList('').then(function (dir) { if (dir) { remoteDrives = dir.map(remoteItem).filter(function (x) { return x.kind == 'drive'; }); renderDrives(panes[0]); renderDrives(panes[1]); } }, function () { });
            }
            renderButtons();
        };

        obj.onDisconnect = function () {
            for (var k in pending) { clearTimeout(pending[k].timer); pending[k].reject(new Error('Disconnected')); }
            pending = {};
            if (job) { job.canceled = true; }
            uploadCancel(); downloadCancel();
            panes.forEach(function (p) { if (p.type == 'remote') { p.loadSeq++; p.loading = false; p.items = []; p.rows = []; p.marked = {}; p.message = 'Not connected. Use the Connect button above.'; renderPane(p); } });
            closeMenu();
            renderButtons();
        };

        obj.setActive = function (active) {
            obj.active = !!active;
            storeSet('fcActive', obj.active);
            root.style.display = obj.active ? '' : 'none';
            if (host.onActiveChanged) { host.onActiveChanged(obj.active); }
            if (obj.active) {
                fit();
                panes.forEach(function (p) {
                    if ((p.type == 'remote') && connected() && (p.items.length == 0)) { loadRemote(p, p.segs); }
                    else { renderPane(p); }
                });
                setActive(activeIdx);
                panes[activeIdx].el.scroll.focus();
            }
        };

        obj.toggle = function () { obj.setActive(!obj.active); };
        obj.isBusy = function () { return (job != null) || (upload != null) || (download != null); };

        // Keep the commander filling the space down to the bottom of the window
        // Themes such as Stylish UI clip the page column and pin a footer over the bottom of the window.
        function fit() {
            if (!obj.active || (root.offsetParent == null)) return;
            var rect = root.getBoundingClientRect(), bottom = window.innerHeight;
            for (var e = root.parentElement; e && (e != document.body); e = e.parentElement) {
                if (getComputedStyle(e).overflowY != 'visible') { bottom = Math.min(bottom, e.getBoundingClientRect().bottom); }
            }
            var x = rect.left + (rect.width / 2), y = bottom - 2, cover = document.elementFromPoint(x, y);
            for (var c = cover; c && !root.contains(c) && (c != document.body); c = c.parentElement) {
                var pos = getComputedStyle(c).position;
                if ((pos == 'fixed') || (pos == 'sticky')) { bottom = Math.min(bottom, c.getBoundingClientRect().top); break; }
            }
            root.style.height = Math.max(240, Math.floor(bottom - rect.top) - 4) + 'px';
        }
        obj.fit = fit;

        // Setup
        var types = storeGet('fcTypes', [localSupported ? 'local' : 'remote', 'remote']);
        var sorts = storeGet('fcSort', null);
        for (var i = 0; i < 2; i++) {
            panes.push(newPane(i));
            panes[i].type = ((types[i] == 'local') && localSupported) ? 'local' : 'remote';
            if (sorts && sorts[i]) { panes[i].sortKey = sorts[i][0]; panes[i].sortDir = sorts[i][1]; }
        }
        build();
        panes.forEach(renderPane);
        setActive(1);
        root.style.display = 'none';
        window.addEventListener('resize', fit);
        if (typeof ResizeObserver == 'function') { new ResizeObserver(fit).observe(document.body); }
        document.addEventListener('mousedown', function (ev) { if (menuEl && !menuEl.contains(ev.target)) { closeMenu(); } });
        obj.keysEl.addEventListener('click', function (ev) { var b = ev.target.closest('.fc-key'); if (b) { keyDefs[parseInt(b.getAttribute('data-i'))].f(); } });
        if (localSupported) {
            idbGet('recent').then(function (list) {
                if (Array.isArray(list)) { recentLocal = list; panes.forEach(function (p) { if (p.type == 'local') { renderPane(p); } }); }
            });
        }
        if (storeGet('fcActive', false)) { setTimeout(function () { obj.setActive(true); }, 0); }
        return obj;
    }

    return { create: create, localSupported: localSupported };
})();
