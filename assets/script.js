(() => {
  // ---------- config ----------
  const GAP_MS = 100;           // longer gaps (pen out of range / idle) don't count as intervals
  const LOW01_WINDOW = 10000;   // ms, 0.1% low always uses this
  const GRAPH_MAX_MS = 20;      // interval at the top of the interval graph (fixed)
  const BIN_MS = 0.1;           // histogram bin width
  const NICE_X = [4, 5, 6, 8, 10, 12, 15, 20, 30, 50, 100];
  const NICE_Y = [5, 10, 20, 25, 40, 50, 80, 100];
  const CAP = 65536;            // ring buffer size
  const C = { line: '#382e33', soft: '#ad9ea5', pink: '#ff66ab', yellow: '#ffdd55', blue: '#66ccff', ink: '#ffffff',
              pinkFill: 'rgba(255,102,171,0.18)', blueFill: 'rgba(102,204,255,0.18)' };
  const FONT = '400 11px "Exo 2", system-ui, sans-serif';

  const $ = id => document.getElementById(id);
  const app = $('app');
  const els = { name: $('name'), score: $('score'), rsd: $('rsd'), jit: $('jit'), maxint: $('maxint'), samples: $('samples'),
                repLabel: $('repLabel'), big: $('big'), lows: $('lows'), hint: $('hint'), btn: $('connect'), disconnectBtn: $('disconnect') };

  const state = { win: 2000, view: 'split', layout: null };
  try { const w = +localStorage.getItem('rrt:win'); if (w >= 500 && w <= 5000) state.win = Math.round(w / 100) * 100; } catch (_) {}

  // ---------- sample store ----------
  const rT = new Float64Array(CAP), rD = new Float32Array(CAP);
  const rX = new Float32Array(CAP), rY = new Float32Array(CAP), rP = new Float32Array(CAP);
  const rTX = new Float32Array(CAP), rTY = new Float32Array(CAP);
  let head = 0, count = 0, lastT = null, meanDt = 0, held = false, histState = null, histX = 10;

  // crosshair trail: recent raw (x, y, t) samples, newest last, used to paint the
  // full-screen position overlay. Pruned by age in drawCrosshair().
  const crossTrail = [];
  // fallback trail from browser pointer events (CSS pixels), used only for the
  // crosshair overlay when the tablet's HID reports don't expose a usable X/Y
  // field to WebHID — never used for any of the rate/jitter statistics.
  const mouseTrail = [];
  // running observed bounds for X/Y, used as a fallback when the HID descriptor's
  // logical min/max is missing or degenerate (min === max, or absent entirely)
  let obsXMin = Infinity, obsXMax = -Infinity, obsYMin = Infinity, obsYMax = -Infinity;

  function clearData() {
    head = 0; count = 0; lastT = null; meanDt = 0; held = false; histState = null; histX = 10;
    crossTrail.length = 0;
    obsXMin = Infinity; obsXMax = -Infinity; obsYMin = Infinity; obsYMax = -Infinity;
    showPlaceholders();
  }

  let tsShift = null;
  function norm(ts) {
    if (tsShift === null) tsShift = ts > 1e11 ? (performance.timeOrigin || 0) : 0;
    return ts - tsShift;
  }

  function addSample(t, x, y, p, tx, ty) {
    let dt = NaN;
    if (lastT !== null) {
      const d = t - lastT;
      if (d <= 0) return;
      if (d <= GAP_MS) dt = d;
    }
    lastT = t;
    const i = head;
    rT[i] = t; rD[i] = dt; rX[i] = x; rY[i] = y; rP[i] = p; rTX[i] = tx; rTY[i] = ty;
    head = (head + 1) % CAP; if (count < CAP) count++;
    if (x === x && y === y) {
      crossTrail.push({ x, y, t });
      if (x < obsXMin) obsXMin = x; if (x > obsXMax) obsXMax = x;
      if (y < obsYMin) obsYMin = y; if (y > obsYMax) obsYMax = y;
    }
    if (rec.active) recordRow(t, dt, x, y, p, tx, ty);
  }

  // ---------- HID report parsing (X, Y, pressure, tilt) ----------
  // Digitizer usage page 0x0D: 0x30 tip pressure, 0x3D/0x3E x/y tilt. Generic Desktop 0x01: 0x30 X, 0x31 Y.
  const WANTED = { '1:48': 'X', '1:49': 'Y', '13:48': 'P', '13:61': 'TX', '13:62': 'TY' };

  function mkLayout(list) {
    let bit = 0; const lay = { bits: 0, X: null, Y: null, P: null, TX: null, TY: null };
    for (const { item, page } of list) {
      const size = item.reportSize | 0, cnt = item.reportCount | 0;
      if (!item.isConstant && size > 0) {
        const hasList = item.usages && item.usages.length > 0;
        if (item.isRange || hasList) {
          for (let i = 0; i < cnt; i++) {
            const u = item.isRange ? item.usageMinimum + Math.min(i, item.usageMaximum - item.usageMinimum)
                                   : item.usages[Math.min(i, item.usages.length - 1)];
            const up = u > 0xFFFF ? ((u >>> 16) & 0xFFFF) : page, id = u & 0xFFFF;
            const key = WANTED[up + ':' + id];
            if (key && !lay[key]) {
              lay[key] = { off: bit + i * size, size, signed: item.logicalMinimum < 0,
                           min: item.logicalMinimum, max: item.logicalMaximum,
                           pmin: item.physicalMinimum, pmax: item.physicalMaximum,
                           unit: item.unit, exp: item.unitExponent };
            }
          }
        }
      }
      bit += size * cnt;
    }
    lay.bits = bit;
    return lay;
  }

  function buildLayouts(dev) {
    const out = new Map();
    try {
      // Two candidate readings of the descriptor tree; the right one is picked by matching real report length.
      const A = new Map(), B = new Map();
      const add = (map, col, rep) => {
        const id = rep.reportId || 0;
        if (!map.has(id)) map.set(id, []);
        for (const item of (rep.items || [])) map.get(id).push({ item, page: col.usagePage });
      };
      (function walk(cols, top) {
        for (const c of cols) {
          for (const r of (c.inputReports || [])) { add(A, c, r); if (top) add(B, c, r); }
          walk(c.children || [], false);
        }
      })(dev.collections || [], true);
      for (const id of A.keys()) out.set(id, { cands: [mkLayout(A.get(id)), mkLayout(B.get(id) || [])], chosen: undefined });
    } catch (_) {}
    return out;
  }

  function readField(dv, f) {
    const off = f.off, size = f.size;
    let v;
    if ((off & 7) === 0 && size === 16 && (off >> 3) + 2 <= dv.byteLength) v = dv.getUint16(off >> 3, true);
    else if ((off & 7) === 0 && size === 8 && (off >> 3) < dv.byteLength) v = dv.getUint8(off >> 3);
    else {
      v = 0;
      for (let i = 0; i < size; i++) {
        const idx = off + i, byte = idx >> 3;
        if (byte >= dv.byteLength) return NaN;
        v += ((dv.getUint8(byte) >> (idx & 7)) & 1) * Math.pow(2, i);
      }
    }
    if (f.signed && v >= Math.pow(2, size - 1)) v -= Math.pow(2, size);
    return v;
  }

  // ---------- connection: WebHID ----------
  let hidDevice = null, statusMsg = '', layouts = new Map(), primaryId = null;
  const hasHID = 'hid' in navigator;
  const reportCounts = new Map();

  function onInputReport(e) {
    const id = e.reportId;
    const c = (reportCounts.get(id) || 0) + 1;
    reportCounts.set(id, c);
    if (primaryId === null) primaryId = id;
    else if (id !== primaryId && c > 1.5 * (reportCounts.get(primaryId) || 0)) { primaryId = id; lastT = null; }
    if (id !== primaryId) return;

    let x = NaN, y = NaN, p = NaN, tx = NaN, ty = NaN;
    const entry = layouts.get(id);
    if (entry) {
      if (entry.chosen === undefined) {
        const len = e.data.byteLength;
        entry.chosen = entry.cands.find(l => Math.ceil(l.bits / 8) === len) || false;
      }
      const L = entry.chosen;
      if (L) {
        state.layout = L;
        const dv = e.data;
        if (L.X) x = readField(dv, L.X);
        if (L.Y) y = readField(dv, L.Y);
        if (L.P) p = readField(dv, L.P);
        if (L.TX) tx = readField(dv, L.TX);
        if (L.TY) ty = readField(dv, L.TY);
      }
    }
    addSample(norm(e.timeStamp), x, y, p, tx, ty);
  }
  setInterval(() => { for (const [k, v] of reportCounts) reportCounts.set(k, v * 0.5); }, 5000);

  function deviceName(d) {
    return d.productName || ('HID device ' + d.vendorId.toString(16).padStart(4, '0') + ':' + d.productId.toString(16).padStart(4, '0'));
  }

  async function unpairAllDevices(exceptDevice = null) {
    if (!hasHID) return;
    try {
      const devices = await navigator.hid.getDevices();
      for (const dev of devices) {
        if (exceptDevice && dev === exceptDevice) continue;
        try {
          dev.removeEventListener('inputreport', onInputReport);
          if (dev.opened) await dev.close();
          if ('forget' in dev) await dev.forget();
        } catch (_) {}
      }
    } catch (_) {}
  }

  async function connect(dev) {
    // Unpair/close all existing devices except the newly chosen device
    await unpairAllDevices(dev);

    try {
      if (!dev.opened) await dev.open();
    } catch (err) {
      statusMsg = 'Could not open ' + deviceName(dev) + '. A tablet driver or another app may be using it. Close it and try again.';
      return;
    }
    dev.removeEventListener('inputreport', onInputReport);
    dev.addEventListener('inputreport', onInputReport);
    hidDevice = dev; statusMsg = '';
    layouts = buildLayouts(dev); state.layout = null;
    reportCounts.clear(); primaryId = null;
    clearData();
    els.name.textContent = deviceName(dev);
    els.btn.textContent = 'Change Tablet';
    els.btn.classList.remove('connect-btn');
    els.disconnectBtn.hidden = false;
    try { localStorage.setItem('rrt:dev', dev.vendorId + ':' + dev.productId); } catch (_) {}
  }

  function resetConnectionUI() {
    hidDevice = null; state.layout = null;
    els.name.textContent = 'No tablet connected';
    els.btn.textContent = 'Connect Tablet';
    els.btn.classList.add('connect-btn');
    els.disconnectBtn.hidden = true;
    try { localStorage.removeItem('rrt:dev'); } catch (_) {}
    clearData();
  }

  els.btn.addEventListener('click', async () => {
    if (!hasHID) { statusMsg = 'This browser has no WebHID support. Use Chrome, Edge or Opera.'; return; }
    try {
      const picked = await navigator.hid.requestDevice({ filters: [] });
      if (picked.length) await connect(picked[0]);
    } catch (err) {
      statusMsg = (err && err.name === 'SecurityError')
        ? 'This page is not allowed to use WebHID here. Open it in its own browser tab.'
        : 'Could not connect: ' + ((err && err.message) || 'unknown error');
    }
  });

  els.disconnectBtn.addEventListener('click', async () => {
    await unpairAllDevices();
    statusMsg = 'Tablet disconnected and unpaired.';
    resetConnectionUI();
  });

  if (hasHID) {
    navigator.hid.addEventListener('disconnect', e => {
      if (e.device === hidDevice) {
        statusMsg = 'Tablet disconnected.';
        resetConnectionUI();
      }
    });
    (async () => {
      try {
        const saved = localStorage.getItem('rrt:dev');
        if (!saved) return;
        const dev = (await navigator.hid.getDevices()).find(d => (d.vendorId + ':' + d.productId) === saved);
        if (dev) await connect(dev);
      } catch (_) {}
    })();
  }

  window.addEventListener('contextmenu', e => e.preventDefault());

  // crosshair-only fallback: track real pointer position from browser events.
  // Some tablets move the OS cursor and drive apps like osu!/OpenTabletDriver
  // fine at the driver level, but don't expose a decodable X/Y usage to WebHID —
  // in that case the crosshair overlay falls back to this instead of going dark.
  // This never feeds the ring buffers or any statistic, only drawCrosshair().
  window.addEventListener('pointermove', e => {
    mouseTrail.push({ x: e.clientX, y: e.clientY, t: performance.now() });
    if (mouseTrail.length > 1000) mouseTrail.splice(0, mouseTrail.length - 1000);
  }, { passive: true });

  function pressRange() {
    if (hidDevice) { const P = state.layout && state.layout.P; return (P && P.max > P.min) ? P : null; }
    return null;
  }

  // full X/Y range for the currently connected device, used to map a raw sample
  // onto the tablet's active area (and from there, onto the screen). Prefers the
  // HID descriptor's logical min/max; falls back to the observed min/max seen so
  // far when the descriptor's range is missing or degenerate (common on some
  // tablets whose firmware reports min === max or omits the field entirely).
  function crossRange() {
    if (!hidDevice) return null;
    const L = state.layout, fx = L && L.X, fy = L && L.Y;
    if (fx && fy && fx.max > fx.min && fy.max > fy.min) {
      return { xMin: fx.min, xMax: fx.max, yMin: fy.min, yMax: fy.max, source: 'descriptor' };
    }
    if (obsXMax > obsXMin && obsYMax > obsYMin) {
      return { xMin: obsXMin, xMax: obsXMax, yMin: obsYMin, yMax: obsYMax, source: 'observed' };
    }
    return null;
  }

  // ---------- rolling stats ----------
  const tmpW = new Float32Array(CAP), tmp10 = new Float32Array(CAP);

  function showPlaceholders() {
    els.big.textContent = '--hz'; els.lows.textContent = '1% low: --, 0.1% low: --';
    els.score.textContent = '--'; els.rsd.textContent = '--'; els.jit.textContent = '--';
    els.maxint.textContent = '--'; els.samples.textContent = '--';
  }
  function pct(sorted, n, p) { return sorted[Math.min(n - 1, Math.max(0, Math.ceil(p * n) - 1))]; }

  function updateStats() {
    const now = performance.now(), W = state.win;
    let nW = 0, n10 = 0, sum = 0, sum2 = 0, sumR = 0, sumR2 = 0, max = 0;
    for (let k = 0; k < count; k++) {
      const idx = (head - 1 - k + CAP) % CAP;
      const age = now - rT[idx];
      if (age > LOW01_WINDOW) break;
      const dt = rD[idx];
      if (dt !== dt) continue; // NaN: first report after a gap
      tmp10[n10++] = dt;
      if (age <= W) {
        tmpW[nW++] = dt;
        sum += dt; sum2 += dt * dt;
        const r = 1000 / dt; sumR += r; sumR2 += r * r;
        if (dt > max) max = dt;
      }
    }

    if (nW >= 10) { // otherwise keep showing the last values
      held = true;
      meanDt = sum / nW;
      const avg = 1000 / meanDt;
      const sdDt = Math.sqrt(Math.max(0, sum2 / nW - meanDt * meanDt));
      const meanR = sumR / nW;
      const sdR = Math.sqrt(Math.max(0, sumR2 / nW - meanR * meanR));
      const sW = tmpW.subarray(0, nW).sort();
      const low1 = 1000 / pct(sW, nW, 0.99);
      const s10 = tmp10.subarray(0, n10).sort();
      const low01 = 1000 / pct(s10, n10, 0.999);

      els.big.textContent = Math.round(avg) + 'hz';
      els.lows.textContent = '1% low: ' + Math.round(low1) + 'hz, 0.1% low: ' + Math.round(low01) + 'hz';
      els.rsd.textContent = sdR.toFixed(1) + ' hz';
      els.jit.textContent = sdDt.toFixed(2) + ' ms';
      els.maxint.textContent = max.toFixed(1) + ' ms';
      els.samples.textContent = nW.toLocaleString();

      const steady = Math.max(0, 1 - 4 * (sdDt / meanDt));
      const r1 = Math.min(1, low1 / avg), r01 = Math.min(1, low01 / avg);
      els.score.textContent = Math.round(100 * (0.5 * steady + 0.25 * r1 + 0.25 * r01));

      // histogram of the window, x-range picked from the data with hysteresis so it doesn't jump around
      const need = Math.max(2 * sW[nW >> 1], 1.3 * pct(sW, nW, 0.99));
      const target = NICE_X.find(v => v >= need) || 100;
      if (target > histX) histX = target; else if (target < histX * 0.5) histX = target;
      const nb = Math.round(histX / BIN_MS), bins = new Uint16Array(nb);
      let over = 0;
      for (let i = 0; i < nW; i++) {
        const v = sW[i];
        if (v >= histX) { over++; bins[nb - 1]++; }
        else bins[Math.min(nb - 1, Math.floor(v / BIN_MS))]++;
      }
      histState = { bins, nb, xmax: histX, n: nW, mean: meanDt, over };
    }

    let hint;
    if (statusMsg) hint = statusMsg;
    else if (hidDevice) hint = held ? '' : 'Move your pen over the tablet.';
    else if (!hasHID) hint = 'This browser has no WebHID support. Please use Chrome, Edge, or Opera.';
    else hint = 'Please click "Connect Tablet" to select your device via WebHID.';
    if (els.hint.textContent !== hint) els.hint.textContent = hint;

    // pressure pane note
    const note = $('pressNote');
    let pn = '';
    if (state.view === 'pressure') {
      const pr = pressRange();
      if (!count) pn = 'Waiting for pen data.';
      else if (!pr || rP[(head - 1 + CAP) % CAP] !== rP[(head - 1 + CAP) % CAP]) pn = 'This tablet\u2019s reports don\u2019t expose a standard pressure field.';
    }
    note.hidden = !pn; if (note.textContent !== pn) note.textContent = pn;
  }

  // ---------- window slider ----------
  const win = $('win'), winOut = $('winOut');
  function applyWindow() {
    win.value = state.win;
    winOut.textContent = (state.win / 1000).toFixed(1) + ' s';
    els.repLabel.textContent = 'Reports (' + (state.win / 1000).toFixed(1) + ' s)';
  }
  win.addEventListener('input', () => {
    state.win = +win.value; applyWindow(); updateStats();
    try { localStorage.setItem('rrt:win', String(state.win)); } catch (_) {}
  });
  applyWindow();

  // ---------- tabs ----------
  const tabs = Array.from(document.querySelectorAll('.tab'));
  function setView(v) {
    state.view = v; app.dataset.view = v;
    app.toggleAttribute('data-full', v === 'graph' || v === 'hist');
    for (const t of tabs) { const on = t.dataset.view === v; t.setAttribute('aria-selected', on); t.tabIndex = on ? 0 : -1; }
    try { localStorage.setItem('rrt:view', v); } catch (_) {}
    updateStats();
  }
  tabs.forEach((t, i) => {
    t.addEventListener('click', () => setView(t.dataset.view));
    t.addEventListener('keydown', e => {
      if (e.key === 'ArrowRight' || e.key === 'ArrowLeft') {
        const n = tabs[(i + (e.key === 'ArrowRight' ? 1 : tabs.length - 1)) % tabs.length];
        n.focus(); setView(n.dataset.view); e.preventDefault();
      }
    });
  });
  { let v = 'split'; try { v = localStorage.getItem('rrt:view') || 'split'; } catch (_) {} setView(tabs.some(t => t.dataset.view === v) ? v : 'split'); }

  // ---------- recording / export ----------
  const rec = { active: false, done: false, dur: 10000, t0: 0, rows: [], startedISO: '' };
  const expBtn = $('expBtn'), pop = $('pop'), recStart = $('recStart'), recDl = $('recDl'),
        recNote = $('recNote'), recTrack = $('recTrack'), recFill = $('recFill'), recSec = $('recSec');
  const IDLE_NOTE = 'Captures timestamp, dt, X, Y, pressure and tilt, then gives you a JSON file. Fields your tablet doesn\u2019t report are null.';

  function recordRow(t, dt, x, y, p, tx, ty) {
    const rel = t - rec.t0;
    if (rel < 0) return;
    if (rel > rec.dur) { finishRec(); return; }
    rec.rows.push([rel, dt, x, y, p, tx, ty]);
  }
  function startRec() {
    const s = Math.max(1, Math.min(300, Math.round(+recSec.value || 10)));
    recSec.value = s;
    rec.rows = []; rec.dur = s * 1000; rec.t0 = performance.now(); rec.startedISO = new Date().toISOString();
    rec.active = true; rec.done = false;
    renderRec();
  }
  function finishRec() { if (!rec.active) return; rec.active = false; rec.done = true; renderRec(); }
  function cancelRec() { rec.active = false; rec.done = false; rec.rows = []; renderRec(); }

  function renderRec() {
    const now = performance.now();
    if (rec.active && now - rec.t0 >= rec.dur) { rec.active = false; rec.done = true; }
    if (rec.active) {
      const el = Math.min(rec.dur, now - rec.t0);
      expBtn.textContent = '\u25CF Recording ' + ((rec.dur - el) / 1000).toFixed(1) + ' s';
      recFill.style.width = (el / rec.dur * 100) + '%';
      recTrack.hidden = false; recDl.hidden = true;
      recStart.textContent = 'Cancel';
      recNote.textContent = 'Recording ' + (el / 1000).toFixed(1) + ' / ' + (rec.dur / 1000) + ' s, ' + rec.rows.length.toLocaleString() + ' reports so far.';
    } else if (rec.done) {
      expBtn.textContent = rec.rows.length ? 'Export \u00B7 ready' : 'Export';
      recTrack.hidden = true; recStart.textContent = 'Record again';
      recDl.hidden = rec.rows.length === 0;
      recNote.textContent = rec.rows.length
        ? 'Recorded ' + rec.rows.length.toLocaleString() + ' reports over ' + (rec.dur / 1000) + ' s.'
        : 'No reports arrived during the recording. Is the pen moving over the tablet?';
    } else {
      expBtn.textContent = 'Export'; recTrack.hidden = true; recDl.hidden = true;
      recStart.textContent = 'Start recording'; if (recNote.textContent !== IDLE_NOTE) recNote.textContent = IDLE_NOTE;
    }
  }

  const nn = v => (v !== v || v === undefined) ? null : v;
  const r3 = v => (v !== v) ? null : Math.round(v * 1000) / 1000;
  function fieldMeta(f) {
    return f ? { logicalMin: f.min, logicalMax: f.max, physicalMin: f.pmin, physicalMax: f.pmax, unit: f.unit, unitExponent: f.exp } : null;
  }
  function buildJSON() {
    const L = state.layout;
    const meta = {
      format: 'tablet-report-recording', version: 1,
      source: hidDevice ? 'webhid' : 'browser-pointer-events',
      device: hidDevice ? { name: deviceName(hidDevice), vendorId: hidDevice.vendorId, productId: hidDevice.productId, reportId: primaryId } : null,
      startedAt: rec.startedISO, durationMs: rec.dur, reports: rec.rows.length,
      columns: ['timestamp', 'dt', 'x', 'y', 'pressure', 'tilt'],
      units: {
        timestamp: 'ms since recording started',
        dt: 'ms since previous report, null for the first report or after a gap over ' + GAP_MS + ' ms',
        x: hidDevice ? 'raw device units' : 'CSS pixels', y: hidDevice ? 'raw device units' : 'CSS pixels',
        pressure: hidDevice ? 'raw device units' : '0 to 1',
        tilt: '[tiltX, tiltY] as reported, or null'
      },
      ranges: hidDevice
        ? { x: fieldMeta(L && L.X), y: fieldMeta(L && L.Y), pressure: fieldMeta(L && L.P), tiltX: fieldMeta(L && L.TX), tiltY: fieldMeta(L && L.TY) }
        : { pressure: { logicalMin: 0, logicalMax: 1 }, tilt: 'degrees' }
    };
    const head = JSON.stringify(meta, null, 2);
    const rows = rec.rows.map(r => JSON.stringify([
      r3(r[0]), r3(r[1]), nn(r[2]), nn(r[3]), nn(r[4]),
      (r[5] !== r[5] && r[6] !== r[6]) ? null : [nn(r[5]), nn(r[6])]
    ]));
    return head.slice(0, -2) + ',\n  "rows": [\n    ' + rows.join(',\n    ') + '\n  ]\n}\n';
  }

  async function saveFile(filename, text) {
    let dl = null;
    try { if (window.claude && window.claude.use) dl = await window.claude.use('downloads'); } catch (_) {}
    if (dl) {
      try { await dl.save({ filename, data: text }); }
      catch (err) { if (!err || err.code !== 'declined') recNote.textContent = 'The download could not be saved here (' + ((err && err.code) || 'error') + ').'; }
      return;
    }
    const url = URL.createObjectURL(new Blob([text], { type: 'application/json' }));
    const a = document.createElement('a');
    a.href = url; a.download = filename; document.body.appendChild(a); a.click(); a.remove();
    setTimeout(() => URL.revokeObjectURL(url), 2000);
  }

  expBtn.addEventListener('click', () => {
    const open = pop.hidden; pop.hidden = !open; expBtn.setAttribute('aria-expanded', String(open));
  });
  document.addEventListener('pointerdown', e => {
    if (!pop.hidden && !pop.contains(e.target) && !expBtn.contains(e.target)) { pop.hidden = true; expBtn.setAttribute('aria-expanded', 'false'); }
  });
  document.addEventListener('keydown', e => { if (e.key === 'Escape' && !pop.hidden) { pop.hidden = true; expBtn.setAttribute('aria-expanded', 'false'); expBtn.focus(); } });
  recStart.addEventListener('click', () => { rec.active ? cancelRec() : startRec(); });
  recDl.addEventListener('click', () => {
    const name = (hidDevice ? deviceName(hidDevice) : 'pointer').toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/^-|-$/g, '') || 'tablet';
    saveFile('report-rate-' + name + '-' + rec.startedISO.replace(/[:.]/g, '-').slice(0, 19) + '.json', buildJSON());
  });
  renderRec();

  setInterval(() => { updateStats(); renderRec(); }, 100);

  // ---------- charts ----------
  function mkCanvas(cid, pid) {
    const canvas = $(cid), pane = $(pid);
    const o = { canvas, ctx: canvas.getContext('2d'), W: 0, H: 0 };
    new ResizeObserver(() => {
      const dpr = window.devicePixelRatio || 1;
      o.W = pane.clientWidth; o.H = pane.clientHeight;
      canvas.width = Math.round(o.W * dpr); canvas.height = Math.round(o.H * dpr);
      o.ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    }).observe(pane);
    return o;
  }
  const cv = { graph: mkCanvas('cGraph', 'paneGraph'), hist: mkCanvas('cHist', 'paneHist'), press: mkCanvas('cPress', 'panePress'),
               cross: mkCanvas('cCross', 'app') };
  const PAD = { t: 30, b: 24, l: 48, r: 14 };

  function frameGrid(o, title, rows, fmt) { // rows: number of grid divisions; fmt(i) -> label for row i (0 = bottom)
    const { ctx, W, H } = o, pw = W - PAD.l - PAD.r, ph = H - PAD.t - PAD.b;
    ctx.clearRect(0, 0, W, H);
    ctx.font = FONT; ctx.fillStyle = C.soft; ctx.textAlign = 'left'; ctx.textBaseline = 'alphabetic';
    ctx.fillText(title, PAD.l, 18);
    ctx.textAlign = 'right'; ctx.textBaseline = 'middle';
    for (let i = 0; i <= rows; i++) {
      const y = Math.round(PAD.t + ph - i / rows * ph) + .5;
      ctx.strokeStyle = C.line; ctx.lineWidth = 1;
      ctx.beginPath(); ctx.moveTo(PAD.l, y); ctx.lineTo(W - PAD.r, y); ctx.stroke();
      ctx.fillStyle = C.soft; ctx.fillText(fmt(i), PAD.l - 8, y);
    }
    ctx.textBaseline = 'alphabetic';
    return { pw, ph };
  }

  // draws a time series as a line with the area beneath it filled; skip(idx) -> true to break the line
  function timeSeries(o, k, now, valueAt, yOf, base, color, fill, isBreak) {
    const { ctx, W, H } = o, pw = W - PAD.l - PAD.r, win = state.win;
    const xOf = t => PAD.l + (1 - (now - t) / win) * pw;
    const line = new Path2D(), area = new Path2D();
    let inSeg = false, prevT = -Infinity, lastX = 0;
    const close = () => { area.lineTo(lastX, base); area.closePath(); inSeg = false; };
    for (let i = k - 1; i >= 0; i--) {
      const idx = (head - 1 - i + CAP) % CAP, t = rT[idx], v = valueAt(idx);
      if (v !== v) { if (inSeg) close(); continue; }
      const x = xOf(t), y = yOf(v);
      if (!inSeg || t - prevT > GAP_MS) {
        if (inSeg) close();
        line.moveTo(x, y); area.moveTo(x, base); area.lineTo(x, y); inSeg = true;
      } else { line.lineTo(x, y); area.lineTo(x, y); }
      prevT = t; lastX = x;
    }
    if (inSeg) close();
    ctx.save();
    ctx.beginPath(); ctx.rect(PAD.l, 0, pw, H); ctx.clip();
    ctx.fillStyle = fill; ctx.fill(area);
    ctx.strokeStyle = color; ctx.lineWidth = 1.4; ctx.lineJoin = 'round'; ctx.stroke(line);
    ctx.restore();
    return xOf;
  }

  function windowCount(now) {
    let k = 0;
    while (k < count && now - rT[(head - 1 - k + CAP) % CAP] <= state.win + 100) k++;
    return k;
  }

  function xLabels(o) {
    const { ctx, W, H } = o;
    ctx.font = FONT; ctx.fillStyle = C.soft; ctx.textBaseline = 'alphabetic';
    ctx.textAlign = 'left'; ctx.fillText((state.win / 1000).toFixed(1) + ' s ago', PAD.l, H - 6);
    ctx.textAlign = 'right'; ctx.fillText('now', W - PAD.r, H - 6);
  }

  function drawGraph() {
    const o = cv.graph; if (!o.W || !o.H) return;
    const now = performance.now(), ctx = o.ctx;
    const { ph } = frameGrid(o, 'Report interval', 4, i => (i * GRAPH_MAX_MS / 4) + ' ms');
    xLabels(o);
    const yOf = dt => PAD.t + ph - Math.min(dt, GRAPH_MAX_MS) / GRAPH_MAX_MS * ph;
    const k = windowCount(now);
    let xOf = null;
    if (k >= 2) {
      xOf = timeSeries(o, k, now, idx => rD[idx], yOf, PAD.t + ph, C.pink, C.pinkFill);
      if (meanDt > 0) {
        const lim = meanDt * 1.75, pw = o.W - PAD.l - PAD.r;
        ctx.save(); ctx.beginPath(); ctx.rect(PAD.l, 0, pw, o.H); ctx.clip();
        ctx.fillStyle = C.yellow;
        for (let i = k - 1; i >= 0; i--) {
          const idx = (head - 1 - i + CAP) % CAP, d = rD[idx];
          if (d > lim) { ctx.beginPath(); ctx.arc(xOf(rT[idx]), yOf(d), 2.3, 0, 6.2832); ctx.fill(); }
        }
        ctx.restore();
      }
    }
    if (meanDt > 0) {
      const y = Math.round(yOf(meanDt)) + .5;
      ctx.save(); ctx.setLineDash([4, 5]); ctx.strokeStyle = C.ink; ctx.globalAlpha = .35; ctx.lineWidth = 1;
      ctx.beginPath(); ctx.moveTo(PAD.l, y); ctx.lineTo(o.W - PAD.r, y); ctx.stroke(); ctx.restore();
      ctx.fillStyle = C.soft; ctx.textAlign = 'right'; ctx.textBaseline = 'alphabetic';
      ctx.fillText('avg ' + meanDt.toFixed(1) + ' ms', o.W - PAD.r, y - 6);
    }
  }

  function drawPress() {
    const o = cv.press; if (!o.W || !o.H) return;
    const now = performance.now(), ctx = o.ctx;
    const { ph } = frameGrid(o, 'Pressure', 4, i => (i * 25) + '%');
    xLabels(o);
    const pr = pressRange(); if (!pr) return;
    const span = pr.max - pr.min;
    const norm01 = v => Math.min(1, Math.max(0, (v - pr.min) / span));
    const yOf = v => PAD.t + ph - norm01(v) * ph;
    const k = windowCount(now);
    if (k >= 2) timeSeries(o, k, now, idx => rP[idx], yOf, PAD.t + ph, C.blue, C.blueFill);
  }

  function drawHist() {
    const o = cv.hist; if (!o.W || !o.H) return;
    const h = histState, ctx = o.ctx;
    const maxPct = h ? Math.max(...h.bins) / h.n * 100 : 0;
    const ymax = NICE_Y.find(v => v >= maxPct * 1.08) || 100;
    const { pw, ph } = frameGrid(o, 'Interval distribution', 4, i => (i * ymax / 4).toFixed(ymax % 4 ? 1 : 0).replace(/\.0$/, '') + '%');
    ctx.font = FONT;
    if (!h) { ctx.fillStyle = C.soft; ctx.textAlign = 'center'; ctx.fillText('Waiting for data', PAD.l + pw / 2, PAD.t + ph / 2); return; }

    // bars
    const bw = pw / h.nb, gap = bw > 4 ? 1 : 0;
    for (let i = 0; i < h.nb; i++) {
      const c = h.bins[i]; if (!c) continue;
      const bh = Math.max(1, (c / h.n * 100) / ymax * ph);
      ctx.fillStyle = (i === h.nb - 1 && h.over > 0) ? C.yellow : C.pink;
      ctx.fillRect(PAD.l + i * bw, PAD.t + ph - bh, Math.max(1, bw - gap), bh);
    }
    // x axis ticks
    const step = [0.5, 1, 2, 5, 10, 20].find(s => h.xmax / s <= 10) || 20;
    ctx.fillStyle = C.soft; ctx.textBaseline = 'alphabetic';
    for (let v = 0; v <= h.xmax + 1e-9; v += step) {
      const x = PAD.l + v / h.xmax * pw;
      ctx.textAlign = v === 0 ? 'left' : (v >= h.xmax - 1e-9 ? 'right' : 'center');
      ctx.fillText(v + (v === 0 || v >= h.xmax - 1e-9 ? ' ms' : ''), x, o.H - 6);
    }
    // mean marker
    if (h.mean > 0 && h.mean < h.xmax) {
      const x = Math.round(PAD.l + h.mean / h.xmax * pw) + .5;
      ctx.save(); ctx.setLineDash([4, 5]); ctx.strokeStyle = C.ink; ctx.globalAlpha = .4; ctx.lineWidth = 1;
      ctx.beginPath(); ctx.moveTo(x, PAD.t); ctx.lineTo(x, PAD.t + ph); ctx.stroke(); ctx.restore();
      ctx.fillStyle = C.soft; ctx.textAlign = x > o.W - 90 ? 'right' : 'left';
      ctx.fillText('avg ' + h.mean.toFixed(2) + ' ms', x + (x > o.W - 90 ? -6 : 6), PAD.t + 12);
    }
    if (h.over > 0) {
      ctx.fillStyle = C.yellow; ctx.textAlign = 'right';
      ctx.fillText(h.over + ' at \u2265 ' + h.xmax + ' ms', o.W - PAD.r, 18);
    }
  }

  // crosshair overlay: one marker per incoming sample, mapped from the tablet's
  // active area onto the full screen, painted above everything but the stats panel.
  const CROSS_MAX_AGE = 300; // ms a marker stays visible before fully fading
  const CROSS_ARM = 5, CROSS_GAP = 0, CROSS_BUCKETS = 1;
  function drawCrosshair() {
    const o = cv.cross; if (!o.W || !o.H) return;
    const ctx = o.ctx, W = o.W, H = o.H;
    ctx.clearRect(0, 0, W, H);
    const now = performance.now();
    while (crossTrail.length && now - crossTrail[0].t > CROSS_MAX_AGE) crossTrail.shift();
    while (mouseTrail.length && now - mouseTrail[0].t > CROSS_MAX_AGE) mouseTrail.shift();

    // prefer real HID position data; fall back to browser pointer events only
    // when the tablet's reports don't decode to a usable X/Y field
    const R = crossRange();
    let trail, toScreen;
    if (R && crossTrail.length) {
      const spanX = R.xMax - R.xMin, spanY = R.yMax - R.yMin;
      trail = crossTrail;
      toScreen = e => {
        const nx = Math.min(1, Math.max(0, (e.x - R.xMin) / spanX));
        const ny = Math.min(1, Math.max(0, (e.y - R.yMin) / spanY));
        return [nx * W, ny * H];
      };
    } else if (mouseTrail.length) {
      const rect = o.canvas.getBoundingClientRect();
      trail = mouseTrail;
      toScreen = e => [e.x - rect.left, e.y - rect.top];
    } else {
      return;
    }
    const arm = (p, cx, cy) => {
      p.moveTo(cx - CROSS_ARM, cy); p.lineTo(cx - CROSS_GAP, cy);
      p.moveTo(cx + CROSS_GAP, cy); p.lineTo(cx + CROSS_ARM, cy);
      p.moveTo(cx, cy - CROSS_ARM); p.lineTo(cx, cy - CROSS_GAP);
      p.moveTo(cx, cy + CROSS_GAP); p.lineTo(cx, cy + CROSS_ARM);
    };
    // bucket the trail by age so we only issue a handful of stroke() calls
    // instead of one per sample, however dense the report stream is
    const paths = Array.from({ length: CROSS_BUCKETS }, () => new Path2D());
    for (let i = 0; i < trail.length - 1; i++) {
      const e = trail[i], frac = 1 - (now - e.t) / CROSS_MAX_AGE;
      if (frac <= 0) continue;
      const bi = Math.min(CROSS_BUCKETS - 1, Math.floor(frac * CROSS_BUCKETS));
      const [cx, cy] = toScreen(e);
      arm(paths[bi], cx, cy);
    }
    ctx.lineCap = 'round'; ctx.lineWidth = 1.5; ctx.strokeStyle = C.pink;
    for (let b = 0; b < CROSS_BUCKETS; b++) {
      ctx.globalAlpha = Math.pow((b + 1) / CROSS_BUCKETS, 1.6) * 0.55;
      ctx.stroke(paths[b]);
    }
    // the newest sample gets its own full-opacity marker with a small ring
    const last = trail[trail.length - 1];
    const [cx, cy] = toScreen(last);
    ctx.globalAlpha = 1; ctx.lineWidth = 1.8; ctx.strokeStyle = C.ink;
    const cur = new Path2D(); arm(cur, cx, cy); ctx.stroke(cur);
    ctx.strokeStyle = C.pink; ctx.lineWidth = 1.4;
    ctx.beginPath(); ctx.arc(cx, cy, 3.5, 0, 6.2832); ctx.stroke();
    ctx.globalAlpha = 1;
  }

  (function loop() {
    const v = state.view;
    if (v === 'split' || v === 'graph') drawGraph();
    if (v === 'split' || v === 'hist') drawHist();
    if (v === 'pressure') drawPress();
    drawCrosshair();
    requestAnimationFrame(loop);
  })();
})();
