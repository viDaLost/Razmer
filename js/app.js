/* Раскладка пола — интерфейс. Ядро расчёта в js/engine.js (RazmerEngine). */
(() => {
'use strict';
const E = window.RazmerEngine;
const { DEG, clamp, mod, num, mm, f1, fm2, dist, plural, hash01, area, perim, inPoly, segDist, bboxOf, centroid, centroidMany, onLine,
  CATS, catById, TONES, PATTERNS, patDef, BORDER_PATTERNS, TEMPLATES, rectWalls, defaultPat, newRoom, newId, defaultState, migrateState,
  roomGeom, wallsFromCorners, innerAngles, unitV, inwardOf, arcRadius, arcLength, sagittaFromRadius, computeGeo, unitKeys, buildUnit, computeUnit,
  plankPts, plankOutline, mainPart, cutSpec, genBond, genHerring, genChevron, genBasket, planRemnant, randShifts, clipBy } = E;

/* ================= helpers ================= */
const $ = (s, r = document) => r.querySelector(s);
const $$ = (s, r = document) => Array.from(r.querySelectorAll(s));
const esc = s => String(s).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
const lsGet = k => { try { return localStorage.getItem(k); } catch (e) { return null; } };
const lsSet = (k, v) => { try { localStorage.setItem(k, v); return true; } catch (e) { return false; } };
const capUse = name => { try { return (window.claude && typeof window.claude.use === 'function') ? window.claude.use(name).catch(() => null) : Promise.resolve(null); } catch (e) { return Promise.resolve(null); } };
const deep = o => JSON.parse(JSON.stringify(o));
const rgb = c => 'rgb(' + c[0] + ',' + c[1] + ',' + c[2] + ')';
const mix = (a, b, t) => a.map((x, i) => Math.round(x * (1 - t) + b[i] * t));
const hashStr = s => { let h = 7; for (let i = 0; i < s.length; i++) h = Math.imul(h ^ s.charCodeAt(i), 2654435761); return h >>> 0; };
const ICON = {
  split: '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><path d="M4 12h16M12 7v10"/></svg>',
  del: '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><path d="M6 6l12 12M18 6L6 18"/></svg>',
  plus: '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><path d="M12 5v14M5 12h14"/></svg>',
};

const KEY_DRAFT = 'raskladka.draft.v1', KEY_PROJ = 'raskladka.projects.v1', KEY_MATS = 'raskladka.mats.v1', KEY_UI = 'raskladka.ui.v2';
let S = defaultState();
const UI = { tab: 'plan', mode: 'view', style: 'wood', labels: true, room: 'r1', target: 'floor', matTarget: 'main', catView: 'eng', sel: null, hl: null, step: 10, variants: null, help: true, mapH: null, addRoom: false, delArm: null, wallFocus: -1 };
let MODEL = null;

/* ================= расчёт ================= */
let GEO_FOR_ANALYZE = null;
function computeAll() {
  const geo = computeGeo(S); GEO_FOR_ANALYZE = geo;
  const units = [];
  for (const key of unitKeys(S, geo)) { const u = buildUnit(key, S, geo); if (u) units.push(computeUnit(u, false, analyzeUnit)); }
  const byKey = {}; units.forEach(r => { byKey[r.unit.key] = r; });
  const mats = new Map();
  for (const r of units) {
    if (r.err || !r.stats) continue; const M = r.unit.mat;
    const m = mats.get(M.key) || { M, boards: 0, full: 0, cut: 0, area: 0, names: [] };
    m.boards += r.stats.boards; m.full += r.stats.nFull; m.cut += r.stats.nCut; m.area += r.stats.layA; m.names.push(r.unit.name); mats.set(M.key, m);
  }
  return { geo, units, byKey, mats: [...mats.values()] };
}
function woodRGB(tone, idx, kind) {
  const base = (TONES[tone] || TONES.oak).c, h = hash01(idx * 2654435761 + 7);
  const f = 0.9 + h * 0.16 - (kind === 'B' ? 0.05 : 0);
  return base.map(c => clamp(Math.round(c * f), 0, 255));
}
function pathOf(poly) { const p = new Path2D(); poly.forEach((q, k) => k ? p.lineTo(q[0], q[1]) : p.moveTo(q[0], q[1])); p.closePath(); return p; }
function analyzeUnit(res) {
  const u = res.unit, M = u.mat, P = u.P, pd = patDef(P.type), thr = num(P.minEdge, 25), geo = GEO_FOR_ANALYZE, seed = hashStr(u.key) % 9973;
  const tapeRGB = [242, 183, 5], groups = new Map(), seams = new Path2D();
  let nFull = 0, nCut = 0, nBad = 0, minT = Infinity, nA = 0, nB = 0, layA = 0;
  res.pieces.forEach((p, idx) => {
    const F = p.F;
    p.rawW = p.raw.map(F.toW); p.w = p.parts.map(poly => poly.map(F.toW));
    p.path = pathOf(p.rawW); seams.addPath(p.path);
    if (p.kind === 'A') nA++; else if (p.kind === 'B') nB++;
    const base = woodRGB(M.tone, idx + seed, p.kind);
    if (p.full) { nFull++; p.col = rgb(base); return; }
    nCut++; p.bad = p.thick < thr; if (p.bad) nBad++; if (p.thick < minT) minT = p.thick;
    p.col = rgb(mix(base, tapeRGB, 0.42));
    p.spec = cutSpec(p);
    const g = groups.get(p.spec.key) || { key: p.spec.key, kind: p.kind, lines: p.spec.lines, idx: [], ext: p.spec.ext };
    g.idx.push(idx); groups.set(p.spec.key, g); p.gk = p.spec.key;
    const mp = mainPart(p), lb = bboxOf(mp);
    if (pd.group === 'bond') { const lu = lb.u1 - lb.u0, lv = lb.v1 - lb.v0; p.lab = (lu < M.L - 0.5 && lv < M.W - 0.5) ? mm(lu) + '×' + mm(lv) : lu < M.L - 0.5 ? mm(lu) : mm(lv); }
    else p.lab = mm(p.spec.ext);
    p.cen = centroid(mp.map(F.toW));
  });
  res.seams = seams;
  res.groups = [...groups.values()].sort((a, b) => b.idx.length - a.idx.length || b.ext - a.ext);
  res.clip = new Path2D();
  for (const part of u.parts) for (const r of part.regions) { let poly = r.poly; if (area(poly) < 0) poly = poly.slice().reverse(); res.clip.addPath(pathOf(poly)); layA += Math.abs(area(poly)); }
  for (const part of u.parts) for (const s of part.subtract) for (const r of part.regions) layA -= Math.abs(area(clipBy(r.poly, s)));
  // ряды
  res.rows = null;
  if (pd.group === 'bond' && u.kind !== 'border') {
    const map = new Map();
    res.pieces.forEach((p, idx) => {
      if (p.part !== 0) return;
      let v0 = Infinity, v1 = -Infinity; for (const q of p.parts) { const b = bboxOf(q); v0 = Math.min(v0, b.v0); v1 = Math.max(v1, b.v1); }
      const b = bboxOf(mainPart(p)); let r = map.get(p.row);
      if (!r) { r = { k: p.row, v0: Infinity, v1: -Infinity, items: [] }; map.set(p.row, r); }
      r.v0 = Math.min(r.v0, v0); r.v1 = Math.max(r.v1, v1);
      let len = 0; for (const q of p.parts) { const bq = bboxOf(q); len += bq.u1 - bq.u0; }
      r.items.push({ u0: b.u0, len: p.parts.length > 1 ? len : b.u1 - b.u0, full: p.full, idx, src: p.src, bad: p.bad });
    });
    res.rows = [...map.values()].sort((a, b) => a.k - b.k);
    res.rows.forEach(r => { r.items.sort((a, b) => a.u0 - b.u0); r.width = r.v1 - r.v0; });
  }
  // расход
  let boards;
  if (res.plans.length) boards = res.plans.reduce((s, p) => s + p.boards, 0);
  else {
    boards = 0; const byKind = {};
    for (const p of res.pieces) { if (p.full) { boards++; continue; } (byKind[p.kind] = byKind[p.kind] || []).push(Math.min(p.spec.ext, M.L)); }
    for (const k in byKind) {
      const list = byKind[k].sort((a, b) => b - a), bins = [];
      for (const len of list) { let placed = false; for (let i = 0; i < bins.length; i++) if (bins[i] >= len) { bins[i] -= len + M.kerf; placed = true; break; } if (!placed) bins.push(M.L - len - M.kerf); }
      boards += bins.length;
    }
  }
  res.walls = wallStats(res, geo);
  res.guides = unitGuides(res, geo);
  res.start = null;
  if (res.rows && res.rows.length && res.rows[0].items.length) {
    const F = u.parts[0].frame, r0 = res.rows[0], it = r0.items[0];
    res.start = { p: F.toW([it.u0, r0.v0]), du: F.vecW([1, 0]), dv: F.vecW([0, 1]) };
  }
  res.stats = { nFull, nCut, nBad, minT, nA, nB, boards, layA, needA: boards * M.L * M.W, waste: Math.max(0, 1 - layA / Math.max(1, boards * M.L * M.W)) };
}
function wallStats(res, geo) {
  const u = res.unit, sets = [];
  for (const rid of u.roomIds) {
    const G = geo[rid]; if (!G || G.err) continue;
    if (u.kind === 'border') sets.push({ rid, poly: G.lay, g: G.g, label: 'стена' });
    else if (u.kind === 'floor' || u.kind === 'room') sets.push({ rid, poly: G.center, g: G.g, label: G.inner ? 'рамка у стены' : 'стена' });
  }
  const out = [];
  for (const set of sets) {
    const n = set.g.n, Lp = set.poly.length, walls = [];
    for (let i = 0; i < n; i++) {
      const s = set.g.wIdx[i], e = i + 1 < n ? set.g.wIdx[i + 1] : Lp, segs = [];
      for (let k = s; k < e; k++) segs.push([set.poly[k % Lp], set.poly[(k + 1) % Lp]]);
      walls.push({ rid: set.rid, i, label: set.label, segs, count: 0, minD: Infinity, maxD: 0, minT: Infinity, len: dist(set.g.corners[i], set.g.corners[(i + 1) % n]), arc: Math.abs(set.g.arcs[i]) >= 0.5 });
    }
    for (const p of res.pieces) {
      if (p.full) continue;
      const F = p.F, o = p.fr.o, fx = p.fr.x, fy = p.fr.y;
      const outl = plankOutline(p.fr).map(q => F.toW([o[0] + q[0] * fx[0] + q[1] * fy[0], o[1] + q[0] * fx[1] + q[1] * fy[1]]));
      for (const w of walls) {
        let hit = false;
        for (const part of p.w) {
          for (let k = 0, m = part.length; k < m && !hit; k++) {
            const a = part[k], b = part[(k + 1) % m]; if (dist(a, b) < 0.5) continue;
            let fac = false; for (let j = 0; j < 4; j++) if (onLine(a, b, outl[j], outl[(j + 1) % 4], 0.6)) { fac = true; break; }
            if (fac) continue;
            for (const [s0, s1] of w.segs) {
              if (!onLine(a, b, s0, s1, 0.6)) continue;
              const dx = s1[0] - s0[0], dy = s1[1] - s0[1], l = Math.hypot(dx, dy) || 1;
              const t1 = ((a[0] - s0[0]) * dx + (a[1] - s0[1]) * dy) / l, t2 = ((b[0] - s0[0]) * dx + (b[1] - s0[1]) * dy) / l;
              if (Math.max(t1, t2) > -0.5 && Math.min(t1, t2) < l + 0.5) { hit = true; break; }
            }
          }
          if (hit) break;
        }
        if (!hit) continue;
        let depth = 0;
        for (const part of p.w) for (const q of part) { let dmin = Infinity; for (const [s0, s1] of w.segs) dmin = Math.min(dmin, segDist(q[0], q[1], s0, s1)); depth = Math.max(depth, dmin); }
        w.count++; w.minD = Math.min(w.minD, depth); w.maxD = Math.max(w.maxD, depth); w.minT = Math.min(w.minT, p.thick);
      }
    }
    out.push(...walls);
  }
  return out;
}
function unitGuides(res, geo) {
  const u = res.unit; if (u.kind === 'border') return [];
  const F = u.parts[0].frame, M = u.mat, pd = patDef(u.P.type), G = geo[u.refRoom];
  const polys = u.kind === 'ins' ? [u.ins.region] : [G.center];
  const L = polys.map(p => p.map(F.toL)), cen = centroidMany(L), lines = [];
  if (pd.group === 'herring') { const per = Math.SQRT2 * (M.L + M.g); lines.push({ axis: 'v', c: Math.round(cen[1] / per) * per, name: 'ось ёлочки' }); }
  else if (pd.group === 'chevron') { const Sv = (M.L + M.g) * Math.sin(clamp(num(u.P.chevAngle, 45), 15, 75) * DEG); lines.push({ axis: 'v', c: Math.round(cen[1] / Sv) * Sv, name: 'линия вершин' }); }
  else if (pd.group === 'basket') { const B = M.L + M.g; lines.push({ axis: 'u', c: Math.round(cen[0] / B) * B, name: 'разметка' }, { axis: 'v', c: Math.round(cen[1] / B) * B, name: 'разметка' }); }
  else if (pd.id === 'grid') { const Lp = M.L + M.g, Wp = M.W + M.g; lines.push({ axis: 'u', c: Math.round(cen[0] / Lp) * Lp, name: 'шов' }, { axis: 'v', c: Math.round(cen[1] / Wp) * Wp, name: 'шов' }); }
  else if (res.rows && res.rows.length) { const r0 = res.rows.find(r => r.width > M.W * 0.5) || res.rows[0]; lines.push({ axis: 'v', c: r0.v1 + M.g / 2, name: 'край ' + (res.rows.indexOf(r0) + 1) + '-го ряда' }); }
  // расстояния до параллельных прямых стен опорной комнаты
  const g = G.g, C = g.corners.map(F.toL);
  for (const ln of lines) {
    let lo = null, hi = null;
    for (let i = 0; i < g.n; i++) {
      if (Math.abs(g.arcs[i]) >= 0.5) continue;
      const p = C[i], q = C[(i + 1) % g.n], d = [q[0] - p[0], q[1] - p[1]], l = Math.hypot(d[0], d[1]); if (l < 1) continue;
      const par = ln.axis === 'v' ? Math.abs(d[1]) / l < 0.01 : Math.abs(d[0]) / l < 0.01; if (!par) continue;
      const pos = ln.axis === 'v' ? (p[1] + q[1]) / 2 : (p[0] + q[0]) / 2, dd = Math.abs(pos - ln.c);
      if (pos < ln.c) { if (!lo || dd < lo.dist) lo = { wall: i, dist: dd }; } else { if (!hi || dd < hi.dist) hi = { wall: i, dist: dd }; }
    }
    ln.lo = lo; ln.hi = hi; ln.room = u.refRoom;
  }
  return lines;
}

/* ================= цвета и рендер ================= */
let COL = {};
function readColors() {
  const cs = getComputedStyle(document.documentElement), g = n => cs.getPropertyValue(n).trim();
  COL = { canvas: g('--canvas'), grid: g('--grid'), wall: g('--wall'), gap: g('--gapzone'), schA: g('--sch-a'), schB: g('--sch-b'), seam: g('--seam'), chalk: g('--chalk'), onChalk: g('--on-chalk'), tape: g('--tape'), tapeSoft: g('--tape-soft'), bad: g('--bad'), badSoft: g('--bad-soft'), ink: g('--ink'), muted: g('--muted'), panel: g('--panel'), mono: g('--font-mono') || 'monospace', body: g('--font-body') || 'sans-serif' };
}
const view = { s: 0.1, cx: 0, cy: 0, fitted: false };
const cv = $('#plan'); let CW = 300, CH = 300, DPR = 1;
const room = id => S.rooms.find(r => r.id === id);
const curRoom = () => room(UI.room) || S.rooms[0];
const roomName = id => (room(id) || {}).name || '';

function render(ctx, W, H, vw, opt) {
  const k = opt.k || 1;
  ctx.setTransform(k, 0, 0, k, 0, 0);
  ctx.fillStyle = COL.canvas; ctx.fillRect(0, 0, W, H);
  const s = vw.s, tx = W / 2 - vw.cx * s, ty = H / 2 - vw.cy * s, X = x => x * s + tx, Y = y => y * s + ty;
  const steps = [100, 250, 500, 1000, 2000, 5000]; const st = steps.find(v => v * s >= 28) || 5000;
  ctx.strokeStyle = COL.grid; ctx.lineWidth = 1; ctx.beginPath();
  const x0 = Math.floor((-tx / s) / st) * st, y0 = Math.floor((-ty / s) / st) * st;
  for (let x = x0; X(x) < W; x += st) { const px = Math.round(X(x)) + 0.5; ctx.moveTo(px, 0); ctx.lineTo(px, H); }
  for (let y = y0; Y(y) < H; y += st) { const py = Math.round(Y(y)) + 0.5; ctx.moveTo(0, py); ctx.lineTo(W, py); }
  ctx.stroke();
  if (!MODEL) return;
  const geo = MODEL.geo, sch = opt.style === 'scheme', live = opt.live;
  ctx.save(); ctx.transform(s, 0, 0, s, tx, ty);
  for (const r of S.rooms) { const G = geo[r.id]; if (G && G.g && !G.err) { ctx.fillStyle = COL.gap; ctx.fill(pathOf(G.g.poly)); } }
  for (const res of MODEL.units) {
    if (res.err || !res.clip) continue;
    ctx.save(); ctx.clip(res.clip);
    for (const p of res.pieces) { ctx.fillStyle = sch ? (p.full ? (p.kind === 'B' ? COL.schB : COL.schA) : (p.bad ? COL.badSoft : COL.tape)) : (p.bad ? COL.badSoft : p.col); ctx.fill(p.path); }
    if (live && UI.hl && UI.hl.key === res.unit.key) { ctx.fillStyle = 'rgba(29,107,214,.45)'; for (const p of res.pieces) if (p.gk === UI.hl.gk) ctx.fill(p.path); }
    ctx.lineWidth = clamp(s * 1.6, 0.35, 1.1) / s; ctx.strokeStyle = COL.seam; ctx.stroke(res.seams);
    ctx.restore();
  }
  // выбранная планка
  const selP = live ? selectedPiece() : null;
  if (selP) { ctx.lineWidth = 3 / s; ctx.strokeStyle = COL.chalk; for (const part of selP.p.w) ctx.stroke(pathOf(part)); }
  // рамка и вставки: тонкий контур
  ctx.lineWidth = 1.2 / s; ctx.strokeStyle = COL.wall; ctx.setLineDash([6 / s, 4 / s]);
  for (const r of S.rooms) { const G = geo[r.id]; if (!G || G.err) continue; if (G.inner) ctx.stroke(pathOf(G.inner)); for (const x of G.inserts) ctx.stroke(pathOf(x.rect)); }
  ctx.setLineDash([]);
  // стены с проёмами
  ctx.lineCap = 'round'; ctx.lineJoin = 'round';
  for (const r of S.rooms) {
    const G = geo[r.id]; if (!G || !G.g) continue;
    const sel = r.id === UI.room && S.rooms.length > 1;
    ctx.strokeStyle = G.err ? COL.bad : COL.wall; ctx.lineWidth = (sel ? 4 : 3.2) / s;
    if (G.err) ctx.setLineDash([8 / s, 6 / s]);
    const g = G.g, Lp = g.poly.length;
    for (let i = 0; i < g.n; i++) {
      const sIdx = g.wIdx[i], eIdx = i + 1 < g.n ? g.wIdx[i + 1] : Lp, pts = [];
      for (let kk = sIdx; kk <= eIdx; kk++) pts.push(g.poly[kk % Lp]);
      const doors = G.doors.filter(d => d.wall === i);
      if (!doors.length) { ctx.beginPath(); pts.forEach((q, j) => j ? ctx.lineTo(q[0], q[1]) : ctx.moveTo(q[0], q[1])); ctx.stroke(); continue; }
      const P = g.corners[i], c = dist(P, g.corners[(i + 1) % g.n]), u = doors[0].u;
      const cuts = doors.map(d => [d.t0, d.t1]).sort((a, b) => a[0] - b[0]); let t = 0;
      ctx.beginPath();
      for (const [a, b] of cuts) { if (a > t) { ctx.moveTo(P[0] + u[0] * t, P[1] + u[1] * t); ctx.lineTo(P[0] + u[0] * a, P[1] + u[1] * a); } t = Math.max(t, b); }
      if (t < c) { ctx.moveTo(P[0] + u[0] * t, P[1] + u[1] * t); ctx.lineTo(P[0] + u[0] * c, P[1] + u[1] * c); }
      ctx.stroke();
      ctx.save(); ctx.lineWidth = 1.5 / s; const T = Math.max(0, num(S.set.wallT, 120));
      for (const d of doors) for (const tt of [d.t0, d.t1]) { const B = [P[0] + u[0] * tt, P[1] + u[1] * tt]; ctx.beginPath(); ctx.moveTo(B[0], B[1]); ctx.lineTo(B[0] + d.n[0] * T, B[1] + d.n[1] * T); ctx.stroke(); }
      ctx.restore();
    }
    ctx.setLineDash([]);
  }
  ctx.restore();
  // подписи подрезок
  if (opt.labels) {
    ctx.font = '600 11px ' + COL.mono; ctx.textAlign = 'center'; ctx.textBaseline = 'middle'; ctx.lineJoin = 'round';
    const placed = [], free = (x0, y0, x1, y1) => { for (const q of placed) if (x0 < q[2] && x1 > q[0] && y0 < q[3] && y1 > q[1]) return false; placed.push([x0, y0, x1, y1]); return true; };
    for (const res of MODEL.units) {
      if (res.err) continue;
      for (const p of res.pieces) {
        if (p.full || !p.lab || !p.cen) continue;
        const b = bboxOf(p.w.length === 1 ? p.w[0] : p.w.flat()), sw = (b.u1 - b.u0) * s, sh = (b.v1 - b.v0) * s, tw = ctx.measureText(p.lab).width + 4;
        if (Math.min(sw, sh) < 13 || Math.max(sw, sh) < tw) continue;
        const cx = X(p.cen[0]), cy = Y(p.cen[1]), rot = sh > sw && sw < tw, hw = (rot ? 7 : tw / 2), hh = (rot ? tw / 2 : 7);
        if (!free(cx - hw, cy - hh, cx + hw, cy + hh)) continue;
        ctx.save(); ctx.translate(cx, cy); if (rot) ctx.rotate(-Math.PI / 2);
        ctx.lineWidth = 3; ctx.strokeStyle = 'rgba(255,255,255,.85)'; ctx.strokeText(p.lab, 0, 0.5);
        ctx.fillStyle = p.bad ? '#a32616' : '#3b2a00'; ctx.fillText(p.lab, 0, 0.5); ctx.restore();
      }
    }
  }
  // направляющие выбранного участка
  const tres = MODEL.byKey[UI.target];
  if (tres && !tres.err && tres.guides && tres.guides.length) {
    const F = tres.unit.parts[0].frame, big = 1e5;
    ctx.save(); ctx.setTransform(k, 0, 0, k, 0, 0); ctx.transform(s, 0, 0, s, tx, ty); ctx.clip(tres.clip);
    ctx.setLineDash([9 / s, 6 / s]); ctx.lineWidth = 2 / s; ctx.strokeStyle = COL.chalk;
    for (const gl of tres.guides) { const a = F.toW(gl.axis === 'v' ? [-big, gl.c] : [gl.c, -big]), b = F.toW(gl.axis === 'v' ? [big, gl.c] : [gl.c, big]); ctx.beginPath(); ctx.moveTo(a[0], a[1]); ctx.lineTo(b[0], b[1]); ctx.stroke(); }
    ctx.restore(); ctx.setLineDash([]);
    if (opt.labels) for (const gl of tres.guides) {
      const parts = []; if (gl.lo) parts.push(mm(gl.lo.dist) + ' от ст. ' + (gl.lo.wall + 1)); if (gl.hi) parts.push(mm(gl.hi.dist) + ' от ст. ' + (gl.hi.wall + 1));
      const L = (tres.unit.kind === 'ins' ? [tres.unit.ins.region] : [MODEL.geo[tres.unit.refRoom].center]).map(p => p.map(F.toL));
      const bb = bboxOf(L.flat()), P = gl.axis === 'v' ? [(bb.u0 + bb.u1) / 2, gl.c] : [gl.c, (bb.v0 + bb.v1) / 2], w = F.toW(P);
      const roomW = (gl.axis === 'v' ? bb.u1 - bb.u0 : bb.v1 - bb.v0) * s * 0.9;
      let txt = gl.name + (parts.length ? ': ' + parts.join(' · ') : ''); ctx.font = '600 11px ' + COL.body;
      if (ctx.measureText(txt).width + 14 > roomW) txt = [gl.lo, gl.hi].filter(Boolean).map(x => mm(x.dist)).join(' · ') || gl.name;
      if (ctx.measureText(txt).width + 14 <= Math.max(roomW, 60)) pillText(ctx, txt, X(w[0]), Y(w[1]), COL.chalk, COL.onChalk, 'center');
    }
  }
  if (tres && tres.start && live) {
    const p = tres.start.p, px = X(p[0]), py = Y(p[1]), du = tres.start.du, dv = tres.start.dv, L = 30;
    ctx.strokeStyle = COL.chalk; ctx.fillStyle = COL.chalk; ctx.lineWidth = 3;
    ctx.beginPath(); ctx.moveTo(px + du[0] * L, py + du[1] * L); ctx.lineTo(px, py); ctx.lineTo(px + dv[0] * L * 0.7, py + dv[1] * L * 0.7); ctx.stroke();
    arrowHead(ctx, px + du[0] * L, py + du[1] * L, du); ctx.beginPath(); ctx.arc(px, py, 5, 0, Math.PI * 2); ctx.fill();
    pillText(ctx, 'СТАРТ', px + du[0] * 10 + dv[0] * 20, py + du[1] * 10 + dv[1] * 20, COL.chalk, COL.onChalk, 'left');
  }
  // подписи стен выбранной комнаты
  const R = curRoom(), RG = R && geo[R.id];
  if (RG && RG.g && opt.labels !== false) {
    const g = RG.g, sgn = g.sgn;
    ctx.font = '600 11px ' + COL.mono; ctx.textBaseline = 'middle';
    for (let i = 0; i < g.n; i++) {
      const P = g.corners[i], Q = g.corners[(i + 1) % g.n], c = dist(P, Q); if (c * s < 30) continue;
      const u = unitV(P, Q), n = sgn > 0 ? [u[1], -u[0]] : [-u[1], u[0]];
      let M = [(P[0] + Q[0]) / 2, (P[1] + Q[1]) / 2];
      if (Math.abs(g.arcs[i]) >= 0.5) M = [M[0] + n[0] * g.arcs[i], M[1] + n[1] * g.arcs[i]];
      const mx = X(M[0]) + n[0] * 17, my = Y(M[1]) + n[1] * 17;
      const txt = (Math.abs(g.arcs[i]) >= 0.5 ? '⌒ ' : '') + mm(c), tw = ctx.measureText(txt).width;
      const auto = g.autoClosed && i === g.n - 1;
      ctx.fillStyle = auto ? COL.muted : COL.chalk; ctx.beginPath(); ctx.arc(mx - tw / 2 - 11, my, 9, 0, Math.PI * 2); ctx.fill();
      ctx.fillStyle = COL.onChalk; ctx.textAlign = 'center'; ctx.fillText(String(i + 1), mx - tw / 2 - 11, my + 0.5);
      ctx.textAlign = 'left'; ctx.lineWidth = 3; ctx.strokeStyle = COL.canvas; ctx.strokeText(txt, mx - tw / 2, my + 0.5); ctx.fillStyle = COL.ink; ctx.fillText(txt, mx - tw / 2, my + 0.5);
    }
  }
  // названия комнат в режимах «Стены» и «Комнаты»
  if (live && (UI.mode === 'rooms' || UI.mode === 'walls')) {
    for (const r of S.rooms) { const G = geo[r.id]; if (!G || !G.g) continue; const c = centroid(G.g.poly); pillText(ctx, r.name + (G.err ? ' — ошибка' : ' · ' + fm2(Math.abs(area(G.g.poly))) + ' м²'), X(c[0]), Y(c[1]), r.id === UI.room ? COL.chalk : COL.ink, r.id === UI.room ? COL.onChalk : COL.panel, 'center'); }
  }
  // ручки
  if (live && UI.mode === 'walls' && RG && RG.g) {
    const g = RG.g;
    for (let i = 0; i < g.n; i++) {
      const h = midHandle(g, i), hx = X(h[0]), hy = Y(h[1]);
      ctx.beginPath(); ctx.moveTo(hx, hy - 7); ctx.lineTo(hx + 7, hy); ctx.lineTo(hx, hy + 7); ctx.lineTo(hx - 7, hy); ctx.closePath();
      ctx.fillStyle = COL.panel; ctx.fill(); ctx.lineWidth = 2; ctx.strokeStyle = COL.tape; ctx.stroke();
    }
    for (const q of g.corners) { ctx.beginPath(); ctx.arc(X(q[0]), Y(q[1]), 8, 0, Math.PI * 2); ctx.fillStyle = COL.panel; ctx.fill(); ctx.lineWidth = 2.5; ctx.strokeStyle = COL.chalk; ctx.stroke(); }
  }
  // линейка
  const want = 90 / s, nice = [100, 200, 500, 1000, 2000, 5000, 10000].find(v => v >= want * 0.6) || 10000, px = nice * s, bx = W - px - 14, by = H - 12;
  ctx.strokeStyle = COL.ink; ctx.lineWidth = 2; ctx.beginPath(); ctx.moveTo(bx, by - 5); ctx.lineTo(bx, by); ctx.lineTo(bx + px, by); ctx.lineTo(bx + px, by - 5); ctx.stroke();
  ctx.fillStyle = COL.ink; ctx.font = '600 11px ' + COL.mono; ctx.textAlign = 'center'; ctx.textBaseline = 'bottom';
  ctx.fillText(nice >= 1000 ? (nice / 1000) + ' м' : nice + ' мм', bx + px / 2, by - 4);
}
function midHandle(g, i) { const P = g.corners[i], Q = g.corners[(i + 1) % g.n], u = unitV(P, Q), n = g.sgn > 0 ? [u[1], -u[0]] : [-u[1], u[0]], h = g.arcs[i] || 0; return [(P[0] + Q[0]) / 2 + n[0] * h, (P[1] + Q[1]) / 2 + n[1] * h]; }
function arrowHead(ctx, x, y, d) { const a = Math.atan2(d[1], d[0]); ctx.beginPath(); ctx.moveTo(x + Math.cos(a) * 8, y + Math.sin(a) * 8); ctx.lineTo(x + Math.cos(a + 2.5) * 8, y + Math.sin(a + 2.5) * 8); ctx.lineTo(x + Math.cos(a - 2.5) * 8, y + Math.sin(a - 2.5) * 8); ctx.closePath(); ctx.fill(); }
function pillText(ctx, text, x, y, bg, fg, align) {
  ctx.font = '600 11px ' + COL.body; const w = ctx.measureText(text).width + 14, h = 20, bx = align === 'left' ? x : x - w / 2;
  ctx.fillStyle = bg; ctx.beginPath(); const r = 10; ctx.moveTo(bx + r, y - h / 2); ctx.arcTo(bx + w, y - h / 2, bx + w, y + h / 2, r); ctx.arcTo(bx + w, y + h / 2, bx, y + h / 2, r); ctx.arcTo(bx, y + h / 2, bx, y - h / 2, r); ctx.arcTo(bx, y - h / 2, bx + w, y - h / 2, r); ctx.closePath(); ctx.fill();
  ctx.fillStyle = fg; ctx.textAlign = 'left'; ctx.textBaseline = 'middle'; ctx.fillText(text, bx + 7, y + 0.5);
}

function resizeCanvas() {
  const r = cv.getBoundingClientRect(); DPR = window.devicePixelRatio || 1;
  CW = Math.max(50, r.width); CH = Math.max(50, r.height);
  cv.width = Math.round(CW * DPR); cv.height = Math.round(CH * DPR);
  if (!view.fitted) fitView(); draw();
}
function floorBBox() { const pts = []; for (const r of S.rooms) { const G = MODEL && MODEL.geo[r.id]; const g = G && G.g ? G.g : roomGeom(r); pts.push(...g.poly); } return pts.length ? bboxOf(pts) : null; }
function fitView() {
  const b = floorBBox(); if (!b) return;
  const m = CW < 560 ? 48 : 56, w = Math.max(1, b.u1 - b.u0), h = Math.max(1, b.v1 - b.v0);
  view.s = Math.min((CW - 2 * m) / w, (CH - 2 * m) / h); view.cx = (b.u0 + b.u1) / 2; view.cy = (b.v0 + b.v1) / 2; view.fitted = true;
}
let drawQueued = false;
function draw() { if (drawQueued) return; drawQueued = true; requestAnimationFrame(() => { drawQueued = false; render(cv.getContext('2d'), CW, CH, view, { k: DPR, style: UI.style, labels: UI.labels, live: true }); }); }

/* ================= пересчёт и сохранение черновика ================= */
let computeQueued = false, panelTimer = 0, saveTimer = 0;
function recompute() { MODEL = computeAll(); fixTargets(); draw(); renderStatus(); renderPieceInfo(); }
function invalidate(opts) {
  opts = opts || {};
  if (!computeQueued) { computeQueued = true; requestAnimationFrame(() => { computeQueued = false; recompute(); }); }
  clearTimeout(panelTimer); panelTimer = setTimeout(() => { refreshLight(); if (UI.tab === 'res') renderResults(); }, opts.fast ? 0 : 220);
  clearTimeout(saveTimer); saveTimer = setTimeout(() => lsSet(KEY_DRAFT, JSON.stringify(S)), 600);
}
function refreshLight() { renderRoomList(); renderRoomKV(); renderClosure(); renderWallHints(); }

/* ================= участки: что настраиваем ================= */
function unitName(key) {
  const r = MODEL && MODEL.byKey[key]; if (r) return r.unit.name;
  if (key === 'floor') return 'Общий рисунок';
  const [k, rid, iid] = key.split(':'), rr = room(rid); if (!rr) return key;
  if (k === 'room') return rr.name + ': свой рисунок'; if (k === 'border') return rr.name + ': рамка';
  return rr.name + ': вставка ' + ((rr.inserts || []).findIndex(x => x.id === iid) + 1);
}
function availTargets() { const geo = MODEL ? MODEL.geo : computeGeo(S); return unitKeys(S, geo); }
function fixTargets() {
  if (!room(UI.room)) UI.room = S.rooms[0] && S.rooms[0].id;
  const keys = availTargets();
  if (!keys.includes(UI.target)) UI.target = keys[0] || 'floor';
  const mk = matKeys(); if (!mk.includes(UI.matTarget)) UI.matTarget = 'main';
}
function patOf(key) {
  if (key === 'floor') return S.floorPat;
  const [k, rid, iid] = key.split(':'), r = room(rid); if (!r) return S.floorPat;
  if (k === 'room') return r.pat; if (k === 'border') return r.border.pat;
  const ins = (r.inserts || []).find(x => x.id === iid); return ins ? ins.pat : S.floorPat;
}
const curP = () => patOf(UI.target);
const targetKind = key => key === 'floor' ? 'floor' : key.split(':')[0];
function matKeys() {
  const out = ['main'];
  for (const r of S.rooms) { if (r.own) out.push('room:' + r.id); if (r.border && r.border.on) out.push('border:' + r.id); for (const x of r.inserts || []) out.push('ins:' + r.id + ':' + x.id); }
  return out;
}
function matHolder(key) {
  if (key === 'main') return null; const [k, rid, iid] = key.split(':'), r = room(rid); if (!r) return null;
  if (k === 'room') return r; if (k === 'border') return r.border; return (r.inserts || []).find(x => x.id === iid) || null;
}
function curMat(createOwn) {
  if (UI.matTarget === 'main') return S.mat; const h = matHolder(UI.matTarget); if (!h) return S.mat;
  if (!h.mat && createOwn) h.mat = deep(S.mat);
  return h.mat || S.mat;
}
function matForKey(key) { if (key === 'floor') return S.mat; const h = matHolder(key); return (h && h.mat) || S.mat; }
function matKeyName(key) { if (key === 'main') return 'Основное'; const [k, rid, iid] = key.split(':'), r = room(rid); if (!r) return key; if (k === 'room') return r.name; if (k === 'border') return 'Рамка: ' + r.name; return 'Вставка ' + ((r.inserts || []).findIndex(x => x.id === iid) + 1) + ': ' + r.name; }

/* ================= строка состояния и сообщения ================= */
let msgTimer = 0;
function say(text, kind, sticky) { const el = $('#msg'); el.textContent = text; el.className = 'msg' + (kind ? ' ' + kind : ''); clearTimeout(msgTimer); if (!sticky) msgTimer = setTimeout(modeHint, clamp(3000 + text.length * 50, 4000, 12000)); }
const MODE_HINT = {
  view: 'Нажмите на доску — покажу, как её пилить. Карту двигайте пальцем, масштаб — двумя.',
  pattern: 'Тяните рисунок пальцем или жмите стрелки — подрезки пересчитываются сразу.',
  walls: 'Кружки — углы, ромбы — середины стен. Потяните ромб, и стена станет дугой.',
  rooms: 'Тяните комнату пальцем — у соседней стены она прилипнет.',
};
function modeHint() { const el = $('#msg'); el.className = 'msg'; el.textContent = MODE_HINT[UI.mode] || ''; }
function renderStatus() {
  const el = $('#status'); if (!MODEL) { el.innerHTML = ''; return; }
  const errs = S.rooms.filter(r => MODEL.geo[r.id] && MODEL.geo[r.id].err);
  const res = MODEL.byKey[UI.target], parts = [];
  if (errs.length) parts.push('<span class="pill bad">Ошибка: ' + esc(errs.map(r => r.name).join(', ')) + '</span>');
  const ov = overlaps(); if (ov) parts.push('<span class="pill bad">Наложились: ' + esc(ov) + '</span>');
  if (res) {
    parts.push('<span class="pill info">' + esc(res.unit.name) + '</span>');
    if (res.err) parts.push('<span class="pill bad">' + esc(res.err) + '</span>');
    else {
      const s = res.stats;
      parts.push('<span class="pill">Целых ' + s.nFull + '</span>', '<span class="pill warn">Подрезок ' + s.nCut + '</span>');
      if (s.nCut) parts.push('<span class="pill ' + (s.nBad ? 'bad' : 'ok') + '">' + (s.nBad ? 'Узких ' + s.nBad + ' · мин. ' + mm(s.minT) + ' мм' : 'Мин. кусок ' + mm(s.minT) + ' мм') + '</span>');
      parts.push('<span class="pill">Нужно ' + s.boards + ' шт</span>');
    }
  }
  el.innerHTML = parts.join('');
}

function overlaps() {
  const ok = S.rooms.map(r => [r, MODEL.geo[r.id]]).filter(([, G]) => G && G.g && !G.err);
  for (let i = 0; i < ok.length; i++) for (let j = i + 1; j < ok.length; j++) {
    const A = ok[i][1].lay, B = ok[j][1].lay, ba = bboxOf(A), bb = bboxOf(B);
    if (ba.u1 <= bb.u0 + 1 || bb.u1 <= ba.u0 + 1 || ba.v1 <= bb.v0 + 1 || bb.v1 <= ba.v0 + 1) continue;
    const inside = (P, Q) => P.some(q => inPoly(q[0], q[1], Q) && E.minEdgeDist(q[0], q[1], Q) > 1) || inPoly(...centroid(P), Q);
    if (inside(A, B) || inside(B, A)) return ok[i][0].name + ' и ' + ok[j][0].name;
  }
  return '';
}

/* ================= карточка подрезки (в панели) ================= */
function selectedPiece() {
  if (!UI.sel || !MODEL) return null; const res = MODEL.byKey[UI.sel.key]; if (!res || res.err) return null;
  const idx = res.pieces.findIndex(p => p.id === UI.sel.id); return idx < 0 ? null : { res, p: res.pieces[idx], idx };
}
function renderPieceInfo() {
  const el = $('#pieceInfo'), sp = selectedPiece();
  if (!sp) { el.hidden = true; return; }
  const { res, p } = sp, u = res.unit, spec = p.spec || cutSpec(p), grp = p.gk ? res.groups.find(g => g.key === p.gk) : null;
  const kindName = p.kind === 'A' ? (patDef(u.P.type).group === 'basket' ? 'вдоль' : 'тип A (левая)') : p.kind === 'B' ? (patDef(u.P.type).group === 'basket' ? 'поперёк' : 'тип B (правая)') : '';
  let rowInfo = ''; if (res.rows) { const ri = res.rows.findIndex(x => x.k === p.row); if (ri >= 0) rowInfo = 'ряд ' + (ri + 1) + ' из ' + res.rows.length; }
  const src = p.src === 'pool' ? 'из обрезка' : p.src === 'new' ? 'от новой планки' : '';
  el.innerHTML = '<header><b>' + (p.full ? 'Целая планка' : 'Подрезка') + (kindName ? ' <span class="tag">' + kindName + '</span>' : '') + '</b>' +
    '<button class="icon" type="button" data-act="piece-close" aria-label="Закрыть">' + ICON.del + '</button></header>' +
    '<canvas id="pieceCv"></canvas><ul>' + spec.lines.map(l => '<li>' + esc(l) + '</li>').join('') + '</ul>' +
    '<div class="meta">' + [esc(u.name), rowInfo, src, (!p.full ? 'самое узкое место ≈ ' + mm(p.thick) + ' мм' : ''), grp && grp.idx.length > 1 ? 'таких же: ' + grp.idx.length + ' шт' : ''].filter(Boolean).join(' · ') + '</div>' +
    (grp && grp.idx.length > 1 ? '<button class="btn small" type="button" data-act="piece-hl">' + (UI.hl && UI.hl.gk === p.gk ? 'Снять подсветку' : 'Показать все такие на плане') + '</button>' : '');
  el.hidden = false;
  drawPlank($('#pieceCv'), p, u.mat);
}
function drawPlank(c, p, M) {
  const dpr = window.devicePixelRatio || 1, w = c.clientWidth || 300, h = c.clientHeight || 112; c.width = w * dpr; c.height = h * dpr;
  const ctx = c.getContext('2d'); ctx.setTransform(dpr, 0, 0, dpr, 0, 0); ctx.clearRect(0, 0, w, h);
  const fr = p.fr, out = plankOutline(fr), partsP = p.parts.map(q => plankPts(p, q)), b = bboxOf(out.concat(...partsP));
  const pad = 24, s = Math.min((w - 2 * pad) / (b.u1 - b.u0), (h - 2 * pad) / (b.v1 - b.v0));
  const ox = (w - (b.u1 - b.u0) * s) / 2 - b.u0 * s, oy = (h - (b.v1 - b.v0) * s) / 2 - b.v0 * s, P = q => [q[0] * s + ox, q[1] * s + oy];
  const poly = arr => { ctx.beginPath(); arr.forEach((q, i) => { const r = P(q); i ? ctx.lineTo(r[0], r[1]) : ctx.moveTo(r[0], r[1]); }); ctx.closePath(); };
  ctx.setLineDash([4, 4]); ctx.strokeStyle = COL.muted; ctx.lineWidth = 1; poly(out); ctx.stroke(); ctx.setLineDash([]);
  for (const pts of partsP) {
    ctx.fillStyle = p.full ? p.col : rgb(mix((TONES[M.tone] || TONES.oak).c, [242, 183, 5], 0.35)); poly(pts); ctx.fill();
    ctx.strokeStyle = COL.wall; ctx.lineWidth = 1.2; poly(pts); ctx.stroke();
    ctx.strokeStyle = COL.bad; ctx.lineWidth = 2.5;
    for (let i = 0, n = pts.length; i < n; i++) {
      const a = pts[i], q = pts[(i + 1) % n]; let fac = false;
      for (let k = 0; k < 4; k++) if (onLine(a, q, out[k], out[(k + 1) % 4], 0.6)) { fac = true; break; }
      if (fac || dist(a, q) < 1) continue;
      const A = P(a), B = P(q); ctx.beginPath(); ctx.moveTo(A[0], A[1]); ctx.lineTo(B[0], B[1]); ctx.stroke();
    }
  }
  const pts = plankPts(p, mainPart(p));
  ctx.font = '600 11px ' + COL.mono; ctx.fillStyle = COL.ink; ctx.textAlign = 'center';
  const edgeExt = y0 => { let lo = Infinity, hi = -Infinity; for (let i = 0, n = pts.length; i < n; i++) { const a = pts[i], q = pts[(i + 1) % n]; if (Math.abs(a[1] - y0) < 0.6 && Math.abs(q[1] - y0) < 0.6) { lo = Math.min(lo, a[0], q[0]); hi = Math.max(hi, a[0], q[0]); } } return hi > lo + 0.5 ? [lo, hi] : null; };
  const e0 = edgeExt(0), e1 = edgeExt(fr.W);
  if (e0) { const A = P([e0[0], 0]), B = P([e0[1], 0]); ctx.textBaseline = 'bottom'; ctx.fillText(mm(e0[1] - e0[0]), (A[0] + B[0]) / 2, Math.min(A[1], B[1]) - 4); }
  if (e1) { const A = P([e1[0], fr.W]), B = P([e1[1], fr.W]); ctx.textBaseline = 'top'; ctx.fillText(mm(e1[1] - e1[0]), (A[0] + B[0]) / 2, Math.max(A[1], B[1]) + 4); }
  const yb = bboxOf(pts); if (yb.v1 - yb.v0 < fr.W - 0.6) { const A = P([yb.u1, yb.v0]), B = P([yb.u1, yb.v1]); ctx.textAlign = 'left'; ctx.textBaseline = 'middle'; ctx.fillText(mm(yb.v1 - yb.v0), Math.max(A[0], B[0]) + 5, (A[1] + B[1]) / 2); }
}

/* ================= работа с картой ================= */
const ptrs = new Map(); let gest = null;
const s2w = (x, y) => [(x - CW / 2) / view.s + view.cx, (y - CH / 2) / view.s + view.cy];
const w2s = (x, y) => [(x - view.cx) * view.s + CW / 2, (y - view.cy) * view.s + CH / 2];
function roomAt(w) { for (let i = S.rooms.length - 1; i >= 0; i--) { const G = MODEL && MODEL.geo[S.rooms[i].id]; if (G && G.g && inPoly(w[0], w[1], G.g.poly)) return S.rooms[i].id; } return null; }
function startGesture() {
  const pts = [...ptrs.values()];
  if (pts.length >= 2) { const a = pts[0], b = pts[1], mx = (a.x + b.x) / 2, my = (a.y + b.y) / 2; gest = { type: 'pinch', d0: Math.hypot(a.x - b.x, a.y - b.y) || 1, s0: view.s, w: s2w(mx, my), moved: true }; return; }
  const p = pts[0], R = curRoom(), RG = R && MODEL && MODEL.geo[R.id];
  gest = { type: 'pan', sx: p.x, sy: p.y, moved: false, cx: view.cx, cy: view.cy };
  if (UI.mode === 'pattern') {
    const res = MODEL && MODEL.byKey[UI.target];
    if (res && !res.err) { const P = curP(), F = res.unit.parts[0].frame; Object.assign(gest, { type: 'pattern', P, F, offA: num(P.offA), offB: num(P.offB), kind: res.unit.kind }); }
  } else if (UI.mode === 'walls' && RG && RG.g) {
    const g = RG.g; let best = 24, hit = null;
    g.corners.forEach((q, i) => { const sc = w2s(q[0], q[1]), d = Math.hypot(sc[0] - p.x, sc[1] - p.y); if (d < best) { best = d; hit = { type: 'corner', i }; } });
    for (let i = 0; i < g.n; i++) { const h = midHandle(g, i), sc = w2s(h[0], h[1]), d = Math.hypot(sc[0] - p.x, sc[1] - p.y); if (d < best) { best = d; hit = { type: 'bend', i }; } }
    if (hit) Object.assign(gest, hit, { rid: R.id, g });
  } else if (UI.mode === 'rooms') {
    const rid = roomAt(s2w(p.x, p.y));
    if (rid) {
      if (rid !== UI.room) { UI.room = rid; renderPlanTab(); }
      const r = room(rid), others = [];
      for (const o of S.rooms) if (o.id !== rid) { const G = MODEL.geo[o.id]; if (G && G.g) others.push(...G.g.corners); }
      Object.assign(gest, { type: 'room', rid, x0: num(r.x0), y0: num(r.y0), mine: MODEL.geo[rid].g.corners.map(q => q.slice()), others });
    }
  }
}
cv.addEventListener('pointerdown', e => { cv.setPointerCapture(e.pointerId); const r = cv.getBoundingClientRect(); ptrs.set(e.pointerId, { x: e.clientX - r.left, y: e.clientY - r.top }); startGesture(); });
cv.addEventListener('pointermove', e => {
  if (!ptrs.has(e.pointerId) || !gest) return;
  const r = cv.getBoundingClientRect(); ptrs.set(e.pointerId, { x: e.clientX - r.left, y: e.clientY - r.top });
  if (gest.type === 'pinch') {
    const pts = [...ptrs.values()]; if (pts.length < 2) return;
    const a = pts[0], b = pts[1], d = Math.hypot(a.x - b.x, a.y - b.y), mx = (a.x + b.x) / 2, my = (a.y + b.y) / 2;
    view.s = clamp(gest.s0 * d / gest.d0, 0.005, 20); view.cx = gest.w[0] - (mx - CW / 2) / view.s; view.cy = gest.w[1] - (my - CH / 2) / view.s; draw(); return;
  }
  const p = ptrs.get(e.pointerId), dx = p.x - gest.sx, dy = p.y - gest.sy;
  if (!gest.moved && Math.hypot(dx, dy) < 5) return;
  gest.moved = true;
  const wx = dx / view.s, wy = dy / view.s;
  if (gest.type === 'pan') { view.cx = gest.cx - wx; view.cy = gest.cy - wy; draw(); }
  else if (gest.type === 'pattern') {
    const F = gest.F;
    gest.P.offA = Math.round(gest.offA + wx * F.e1[0] + wy * F.e1[1]);
    if (gest.kind !== 'border') gest.P.offB = Math.round(gest.offB + wx * F.e2[0] + wy * F.e2[1]);
    syncPatInputs(); clearVariantMark(); invalidate();
  } else if (gest.type === 'corner') {
    const w = s2w(p.x, p.y), g = gest.g, pts = g.corners.map(q => q.slice()), n = pts.length, i = gest.i, snap = 10 / view.s;
    let x = Math.round(w[0] / 5) * 5, y = Math.round(w[1] / 5) * 5;
    for (const nb of [pts[(i - 1 + n) % n], pts[(i + 1) % n]]) { if (Math.abs(x - nb[0]) < snap) x = nb[0]; if (Math.abs(y - nb[1]) < snap) y = nb[1]; }
    pts[i] = [x, y]; Object.assign(room(gest.rid), wallsFromCorners(pts, g.arcs)); invalidate();
  } else if (gest.type === 'bend') {
    const w = s2w(p.x, p.y), g = gest.g, i = gest.i, P = g.corners[i], Q = g.corners[(i + 1) % g.n], u = unitV(P, Q), n = g.sgn > 0 ? [u[1], -u[0]] : [-u[1], u[0]];
    let h = (w[0] - (P[0] + Q[0]) / 2) * n[0] + (w[1] - (P[1] + Q[1]) / 2) * n[1]; h = Math.round(h / 10) * 10; if (Math.abs(h) < 40) h = 0;
    h = clamp(h, -dist(P, Q) * 0.49, dist(P, Q));
    const r = room(gest.rid);
    if (i >= r.walls.length) Object.assign(r, wallsFromCorners(g.corners, g.arcs));
    r.walls[i].arc = h; say('Стена ' + (i + 1) + (h ? ': прогиб ' + mm(Math.abs(h)) + ' мм ' + (h > 0 ? 'наружу' : 'внутрь') + ', радиус ≈ ' + mm(arcRadius(dist(P, Q), h)) + ' мм' : ': прямая'), null, true); invalidate();
  } else if (gest.type === 'room') {
    let ddx = wx, ddy = wy; const T = Math.max(0, num(S.set.wallT, 120)), th = 14 / view.s;
    let bx = null, by = null;
    for (const c of gest.mine) for (const o of gest.others) for (const kk of [0, T, -T]) {
      const sx = o[0] + kk - (c[0] + wx), sy = o[1] + kk - (c[1] + wy);
      if (Math.abs(sx) < th && (bx === null || Math.abs(sx) < Math.abs(bx))) bx = sx;
      if (Math.abs(sy) < th && (by === null || Math.abs(sy) < Math.abs(by))) by = sy;
    }
    if (bx !== null) ddx += bx; else ddx = Math.round(ddx / 10) * 10;
    if (by !== null) ddy += by; else ddy = Math.round(ddy / 10) * 10;
    const r = room(gest.rid); r.x0 = Math.round(gest.x0 + ddx); r.y0 = Math.round(gest.y0 + ddy); invalidate();
  }
});
function endPointer(e) {
  if (!ptrs.has(e.pointerId)) return;
  const g = gest, wasTap = g && !g.moved && g.type !== 'pinch' && ptrs.size === 1;
  ptrs.delete(e.pointerId);
  if (wasTap) selectAt(g.sx, g.sy);
  if (ptrs.size) startGesture(); else gest = null;
  if (g && g.moved && ['corner', 'bend', 'room'].includes(g.type)) { renderPlanTab(); invalidate({ fast: true }); }
  if (g && g.moved && g.type === 'pattern') invalidate({ fast: true });
}
cv.addEventListener('pointerup', endPointer);
cv.addEventListener('pointercancel', endPointer);
cv.addEventListener('wheel', e => {
  e.preventDefault(); const r = cv.getBoundingClientRect(), mx = e.clientX - r.left, my = e.clientY - r.top, w = s2w(mx, my);
  view.s = clamp(view.s * Math.exp(-e.deltaY * (e.ctrlKey ? 0.01 : 0.0015)), 0.005, 20);
  view.cx = w[0] - (mx - CW / 2) / view.s; view.cy = w[1] - (my - CH / 2) / view.s; draw();
}, { passive: false });
function selectAt(x, y) {
  if (!MODEL) return; const w = s2w(x, y);
  const rid = roomAt(w);
  if (rid && rid !== UI.room) { UI.room = rid; renderPlanTab(); if (UI.tab === 'pat') renderPatTab(); }
  let found = null;
  for (let ui = MODEL.units.length - 1; ui >= 0 && !found; ui--) {
    const res = MODEL.units[ui]; if (res.err) continue;
    for (const p of res.pieces) { for (const part of p.w) { const b = bboxOf(part); if (w[0] < b.u0 || w[0] > b.u1 || w[1] < b.v0 || w[1] > b.v1) continue; if (inPoly(w[0], w[1], part)) { found = { key: res.unit.key, id: p.id }; break; } } if (found) break; }
  }
  UI.sel = found && !(UI.sel && UI.sel.key === found.key && UI.sel.id === found.id) ? found : null;
  renderPieceInfo(); draw();
}

/* ================= панель: вкладки и поля ================= */
function setTab(t) {
  UI.tab = t;
  $$('.tab').forEach(b => b.setAttribute('aria-selected', String(b.dataset.tab === t)));
  $$('.tabbody').forEach(b => { b.hidden = b.dataset.body !== t; });
  if (t === 'plan') renderPlanTab(); if (t === 'mat') renderMatTab(); if (t === 'pat') renderPatTab(); if (t === 'res') renderResults();
  $('#panel').scrollTop = 0; saveUI();
}
$$('.tab').forEach(b => b.addEventListener('click', () => setTab(b.dataset.tab)));
function getK(path) { return path.split('.').reduce((o, k) => o == null ? o : o[k], S); }
function setK(path, val) { const ks = path.split('.'); let o = S; for (let i = 0; i < ks.length - 1; i++) o = o[ks[i]]; o[ks[ks.length - 1]] = val; }
const fmtIn = v => v === undefined || v === null ? '' : typeof v === 'number' ? String(Math.round(v * 100) / 100).replace('.', ',') : v;
function setIn(el, v) { if (el === document.activeElement) return; if (el.type === 'checkbox') el.checked = !!v; else el.value = fmtIn(v); }
function syncInputs() {
  $$('[data-k]').forEach(el => setIn(el, getK(el.dataset.k)));
  const m = curMat(false); $$('[data-mk]').forEach(el => setIn(el, m[el.dataset.mk]));
  syncPatInputs();
  setIn($('#projName'), S.name || '');
}
function syncPatInputs() { const P = curP(); $$('[data-pk]').forEach(el => setIn(el, P[el.dataset.pk])); }
function readIn(t) { if (t.type === 'checkbox') return t.checked; if ('num' in t.dataset) { if (String(t.value).trim() === '') return undefined; const v = num(t.value, NaN); return Number.isFinite(v) ? v : undefined; } return t.value; }
document.addEventListener('input', e => {
  const t = e.target; if (!(t instanceof HTMLElement) || !t.closest('.app')) return;
  if (t.id === 'projName') { S.name = t.value; invalidate(); return; }
  if (t.id === 'matUseMain') return;
  if (t.dataset.k) { const v = readIn(t); if (v === undefined) return; setK(t.dataset.k, v); invalidate(); return; }
  if (t.dataset.mk) { const v = readIn(t); if (v === undefined) return; const m = curMat(true); m[t.dataset.mk] = v; m.item = null; const tk = UI.matTarget === 'main' ? 'floor' : UI.matTarget; if (t.dataset.mk === 'shape' && v === 'chevron' && targetKind(tk) !== 'border') setPatternType(patOf(tk), 'chevron'); renderSizes(); invalidate(); return; }
  if (t.dataset.pk) { const v = readIn(t); if (v === undefined) return; const P = curP(); P[t.dataset.pk] = v; clearVariantMark(); if (['refRoom', 'refWall'].includes(t.dataset.pk)) { renderRefSelects(); recomputeNow(); centerTarget(UI.target, true); } if (t.dataset.pk === 'chevAngle') renderPatList(); invalidate(); return; }
  if (t.dataset.rk) { const r = curRoom(); const v = t.dataset.rk === 'name' ? t.value : readIn(t); if (v === undefined) return; r[t.dataset.rk] = v; invalidate(); return; }
  if (t.dataset.w !== undefined) { onWallInput(t); return; }
  if (t.dataset.d !== undefined) { const d = curRoom().doors[+t.dataset.d]; if (!d) return; const v = readIn(t); if (v === undefined) return; d[t.dataset.df] = t.dataset.df === 'wall' ? (v | 0) : v; invalidate(); return; }
  if (t.dataset.ins !== undefined) { const ins = curRoom().inserts[+t.dataset.ins]; if (!ins) return; const v = readIn(t); if (v === undefined) return; ins[t.dataset.f] = v; invalidate(); return; }
  if (t.dataset.bf) { const B = curRoom().border, v = readIn(t); if (v === undefined) return; B[t.dataset.bf] = v; invalidate(); return; }
});
function recomputeNow() { MODEL = computeAll(); fixTargets(); }

/* ================= 1. План: комнаты и стены ================= */
function roomSize(g) { const b = bboxOf(g.poly); return mm(b.u1 - b.u0) + '×' + mm(b.v1 - b.v0); }
function renderRoomList() {
  const el = $('#roomList'); if (!el) return;
  let total = 0;
  el.innerHTML = S.rooms.map(r => {
    const G = MODEL && MODEL.geo[r.id], ok = G && G.g && !G.err, a = ok ? Math.abs(area(G.g.poly)) : 0; total += a;
    const badge = G && G.err ? '<span class="badge err">ошибка</span>' : r.own ? '<span class="badge own">свой рисунок</span>' : '<span class="badge">' + (S.rooms.length > 1 ? 'сквозной' : 'рисунок') + '</span>';
    return '<button class="rcard" type="button" data-act="room-select" data-room="' + r.id + '" aria-pressed="' + (r.id === UI.room) + '"><b>' + esc(r.name) + '</b>' + badge + '<small>' + (ok ? fm2(a) + ' м² · ' + roomSize(G.g) + ' мм' : esc(G ? G.err : '')) + '</small></button>';
  }).join('');
  $('#floorSum').textContent = S.rooms.length + ' ' + plural(S.rooms.length, 'комната', 'комнаты', 'комнат') + ' · ' + fm2(total) + ' м²';
}
function renderTplChips() { $('#tplNew').innerHTML = TEMPLATES.filter(t => t.id !== 'rect').map(t => '<button class="chip" type="button" data-act="room-add-tpl" data-tpl="' + t.id + '">' + esc(t.name) + '</button>').join(''); }
function renderPlanTab() { renderRoomList(); renderRoomEditor(); $('#helpBox').hidden = !UI.help; $('#addRoomBox').hidden = !UI.addRoom; }
const innerOf = turn => 180 - turn;
function wallCard(r, i, g) {
  const w = r.walls[i], arc = num(w.arc), isArc = Math.abs(arc) >= 0.5, c = num(w.len);
  return '<div class="wcard' + (i === UI.wallFocus ? ' sel' : '') + '" data-wi="' + i + '">' +
    '<div class="whead"><span class="wn">' + (i + 1) + '</span><b>Стена ' + (i + 1) + '</b>' +
    '<div class="seg mini" role="group" aria-label="Форма стены ' + (i + 1) + '"><button type="button" data-act="wall-shape" data-w="' + i + '" data-v="straight" aria-pressed="' + !isArc + '">Прямая</button><button type="button" data-act="wall-shape" data-w="' + i + '" data-v="arc" aria-pressed="' + isArc + '">Дуга</button></div>' +
    '<button class="icon" type="button" data-act="wall-split" data-w="' + i + '" title="Разделить стену пополам (добавить угол)" aria-label="Разделить стену ' + (i + 1) + '"' + (isArc ? ' disabled' : '') + '>' + ICON.split + '</button>' +
    '<button class="icon" type="button" data-act="wall-del" data-w="' + i + '" title="Удалить стену" aria-label="Удалить стену ' + (i + 1) + '"' + (r.walls.length <= 2 ? ' disabled' : '') + '>' + ICON.del + '</button></div>' +
    '<div class="wrow"><label class="fld"><span>' + (isArc ? 'Длина по хорде' : 'Длина') + '</span><span class="inp"><input id="w' + i + 'len" data-w="' + i + '" data-wf="len" inputmode="decimal" value="' + mm(c) + '"><i>мм</i></span></label>' +
    (isArc ? '<label class="fld"><span>Прогиб дуги</span><span class="inp"><input id="w' + i + 'arc" data-w="' + i + '" data-wf="arc" inputmode="decimal" value="' + mm(Math.abs(arc)) + '"><i>мм</i></span></label>' +
      '<label class="fld"><span>или радиус</span><span class="inp"><input id="w' + i + 'rad" data-w="' + i + '" data-wf="rad" inputmode="decimal" value="' + mm(arcRadius(c, arc)) + '"><i>мм</i></span></label>' : '') + '</div>' +
    (isArc ? '<div class="wrow"><div class="seg mini" role="group" aria-label="Куда выгнута стена"><button type="button" data-act="wall-side" data-w="' + i + '" data-v="out" aria-pressed="' + (arc > 0) + '">Наружу</button><button type="button" data-act="wall-side" data-w="' + i + '" data-v="in" aria-pressed="' + (arc < 0) + '">Внутрь</button></div><span class="hint" id="w' + i + 'hint">длина по дуге ≈ ' + mm(arcLength(c, arc)) + ' мм</span></div>' : '') +
    '</div>';
}
function cornerRow(r, i) {
  const ang = innerOf(num(r.walls[i].turn)), v = Math.round(ang * 10) / 10;
  const chips = [[90, 'обычный'], [270, 'выступ'], [135, ''], [180, 'прямо']].map(([a, t]) => '<button class="chip" type="button" data-act="corner-set" data-w="' + i + '" data-v="' + a + '" aria-pressed="' + (Math.abs(v - a) < 0.05) + '" title="' + (t || a + '°') + '">' + a + '°' + (t ? ' ' + t : '') + '</button>').join('');
  return '<div class="corner">Угол между стенами ' + i + ' и ' + (i + 1) + ': ' + chips + '<span class="inp"><input id="c' + i + 'ang" data-w="' + i + '" data-wf="ang" inputmode="decimal" value="' + f1(v) + '" aria-label="Угол между стенами ' + i + ' и ' + (i + 1) + '"><i>°</i></span></div>';
}
function renderRoomEditor() {
  const el = $('#roomEditor'), r = curRoom(); if (!r) { el.innerHTML = ''; return; }
  const G = MODEL && MODEL.geo[r.id], g = G && G.g ? G.g : roomGeom(r);
  const walls = r.walls.map((w, i) => (i > 0 ? cornerRow(r, i) : '') + wallCard(r, i, g)).join('');
  const straight = []; for (let i = 0; i < g.n; i++) if (Math.abs(g.arcs[i]) < 0.5) straight.push(i);
  const doors = (r.doors || []).map((d, j) => '<div class="drow"><label class="fld"><span>Стена</span><span class="inp"><select id="d' + j + 'wall" data-d="' + j + '" data-df="wall" data-num>' + straight.map(i => '<option value="' + i + '"' + (i === d.wall ? ' selected' : '') + '>' + (i + 1) + '</option>').join('') + '</select></span></label>' +
    '<label class="fld"><span>От угла</span><span class="inp"><input id="d' + j + 'pos" data-d="' + j + '" data-df="pos" data-num inputmode="decimal" value="' + mm(d.pos) + '"><i>мм</i></span></label>' +
    '<label class="fld"><span>Ширина</span><span class="inp"><input id="d' + j + 'w" data-d="' + j + '" data-df="width" data-num inputmode="decimal" value="' + mm(d.width) + '"><i>мм</i></span></label>' +
    '<button class="icon" type="button" data-act="door-del" data-d="' + j + '" aria-label="Удалить проём ' + (j + 1) + '">' + ICON.del + '</button></div>').join('');
  el.innerHTML =
    '<div class="sec"><h3>Комната «' + esc(r.name) + '»</h3><label class="fld"><span>Название</span><span class="inp"><input class="txt" id="rName" data-rk="name" value="' + esc(r.name) + '" maxlength="40"></span></label>' +
    '<div class="row-btns"><button class="btn small" type="button" data-act="room-dup">Копия</button><button class="btn small" type="button" data-act="room-rot">Повернуть 90°</button>' +
    (S.rooms.length > 1 ? '<button class="btn small danger" type="button" data-act="room-del">' + (UI.delArm === 'room:' + r.id ? 'Точно удалить?' : 'Удалить') + '</button>' : '') + '</div>' +
    (G && G.err ? '<p class="note bad">' + esc(G.err) + '</p>' : '') + '</div>' +
    '<div class="sec"><h3>Форма <small>заменит стены комнаты</small></h3><div class="grid2"><label class="fld"><span>Длина</span><span class="inp"><input id="rL" inputmode="decimal" value="' + mm(Math.max(...[0, 2].map(i => num((r.walls[i] || {}).len)))) + '"><i>мм</i></span></label>' +
    '<label class="fld"><span>Ширина</span><span class="inp"><input id="rW" inputmode="decimal" value="' + mm(Math.max(...[1, 3].map(i => num((r.walls[i] || {}).len)))) + '"><i>мм</i></span></label></div>' +
    '<button class="btn" type="button" data-act="room-rect">Сделать прямоугольником</button>' +
    '<div class="chips">' + TEMPLATES.filter(t => t.id !== 'rect').map(t => '<button class="chip" type="button" data-act="room-tpl" data-tpl="' + t.id + '">' + esc(t.name) + '</button>').join('') + '</div></div>' +
    '<div class="sec"><h3>Стены <small>по часовой стрелке</small></h3><p class="note">Идите вдоль стен по часовой стрелке и вписывайте длины. Между стенами — угол комнаты: 90° обычный, 270° — выступ внутрь комнаты. Стену можно сделать дугой: впишите прогиб или радиус.</p>' +
    '<div class="walls" id="walls">' + walls + '</div>' +
    '<button class="btn" type="button" data-act="wall-add">' + ICON.plus + 'Добавить стену</button><p class="note" id="closureNote"></p></div>' +
    '<div class="sec"><h3>Проёмы <small>рисунок идёт в соседнюю комнату</small></h3>' + (doors || '<p class="note">Проёмов нет. Добавьте проём, если пол без порога продолжается в соседнюю комнату.</p>') +
    '<button class="btn" type="button" data-act="door-add">' + ICON.plus + 'Добавить проём</button>' +
    '<p class="note">Соседняя комната должна стоять вплотную через стену ' + mm(num(S.set.wallT, 120)) + ' мм — подвиньте её на карте в режиме «Комнаты».</p></div>' +
    '<div class="sec"><h3>Рисунок в этой комнате</h3><div class="seg" role="group" aria-label="Рисунок в комнате"><button type="button" data-act="own-set" data-v="0" aria-pressed="' + !r.own + '">Общий, сквозной</button><button type="button" data-act="own-set" data-v="1" aria-pressed="' + !!r.own + '">Свой</button></div>' +
    '<p class="note">' + (r.own ? 'У комнаты свой рисунок и своё положение. Настройте его на шаге 3, покрытие — на шаге 2.' : 'Рисунок продолжается из соседних комнат без сдвига — как при укладке без порогов.') + '</p></div>' +
    '<div class="sec"><h3>Положение на плане</h3><div class="grid2"><label class="fld"><span>X первого угла</span><span class="inp"><input id="rX" data-rk="x0" data-num inputmode="decimal" value="' + mm(r.x0) + '"><i>мм</i></span></label>' +
    '<label class="fld"><span>Y первого угла</span><span class="inp"><input id="rY" data-rk="y0" data-num inputmode="decimal" value="' + mm(r.y0) + '"><i>мм</i></span></label></div></div>' +
    '<div class="sec"><h3>Итог по комнате</h3><dl class="kv" id="roomKV"></dl></div>';
  renderClosure(); renderRoomKV();
}
function renderClosure() {
  const el = $('#closureNote'), r = curRoom(); if (!el || !r) return;
  const g = roomGeom(r);
  if (g.autoClosed) {
    const a = g.corners[g.n - 1], b = g.corners[0];
    el.className = 'note warn';
    el.innerHTML = 'Стены не сходятся на <b>' + mm(g.closure) + ' мм</b>. Карта замыкает комнату серой стеной ' + g.n + ' длиной ' + mm(dist(a, b)) + ' мм. Проверьте размеры или <button class="btn small" type="button" data-act="close-auto">добавьте её как стену</button>';
  } else { el.className = 'note'; el.textContent = 'Комната замкнута: ' + g.n + ' ' + plural(g.n, 'стена', 'стены', 'стен') + '. Последний угол получился ' + f1(innerAngles(g)[0]) + '°.'; }
}
function renderWallHints() {
  const r = curRoom(); if (!r) return;
  r.walls.forEach((w, i) => { const h = $('#w' + i + 'hint'); if (h) h.textContent = 'длина по дуге ≈ ' + mm(arcLength(num(w.len), num(w.arc))) + ' мм'; const rad = $('#w' + i + 'rad'); if (rad && rad !== document.activeElement && Math.abs(num(w.arc)) >= 0.5) rad.value = mm(arcRadius(num(w.len), num(w.arc))); const ar = $('#w' + i + 'arc'); if (ar && ar !== document.activeElement && Math.abs(num(w.arc)) >= 0.5) ar.value = mm(Math.abs(num(w.arc))); });
}
function renderRoomKV() {
  const el = $('#roomKV'), r = curRoom(); if (!el || !r) return;
  const G = MODEL && MODEL.geo[r.id]; if (!G || !G.g || G.err) { el.innerHTML = '<dt>Площадь</dt><dd>—</dd>'; return; }
  const g = G.g, ang = innerAngles(g), odd = ang.map((a, i) => ({ a, i })).filter(x => Math.abs(x.a - 90) > 0.4 && Math.abs(x.a - 270) > 0.4);
  el.innerHTML = '<dt>Площадь пола</dt><dd>' + fm2(Math.abs(area(g.poly))) + ' м²</dd><dt>Периметр</dt><dd>' + f1(perim(g.poly) / 1000) + ' м</dd><dt>Габарит</dt><dd>' + roomSize(g) + ' мм</dd>' +
    '<dt>Под укладку (без зазора)</dt><dd>' + fm2(Math.abs(area(G.lay))) + ' м²</dd><dt>Углы не 90°</dt><dd>' + (odd.length ? odd.map(x => (x.i + 1) + ': ' + f1(x.a) + '°').join(', ') : 'нет') + '</dd>';
}
function onWallInput(t) {
  const r = curRoom(), i = +t.dataset.w, w = r.walls[i]; if (!w) return;
  const v = num(t.value, NaN); if (!Number.isFinite(v)) return;
  const f = t.dataset.wf;
  if (f === 'len') { if (v <= 0) return; w.len = v; }
  else if (f === 'ang') { w.turn = 180 - v; $$('[data-act="corner-set"][data-w="' + i + '"]').forEach(b => b.setAttribute('aria-pressed', String(Math.abs(num(b.dataset.v) - v) < 0.05))); }
  else if (f === 'arc') { const sg = num(w.arc) < 0 ? -1 : 1; w.arc = sg * Math.max(1, Math.abs(v)); }
  else if (f === 'rad') { const h = sagittaFromRadius(num(w.len), v); if (!Number.isFinite(h)) { say('Радиус меньше половины хорды (' + mm(num(w.len) / 2) + ' мм) — так дугу не построить.', 'bad'); return; } const sg = num(w.arc) < 0 ? -1 : 1; w.arc = sg * Math.max(1, h); }
  renderClosure(); renderWallHints(); invalidate();
}
function placeNewRoom() { const b = floorBBox(); return b ? [Math.round(b.u1 + 1000), Math.round(b.v0)] : [0, 0]; }

/* ================= действия (клики) ================= */
const ACT = {
  'help-close': () => { UI.help = false; $('#helpBox').hidden = true; saveUI(); },
  'room-select': b => { UI.room = b.dataset.room; UI.delArm = null; UI.wallFocus = -1; renderPlanTab(); draw(); saveUI(); },
  'room-add-open': () => { UI.addRoom = !UI.addRoom; $('#addRoomBox').hidden = !UI.addRoom; },
  'room-add-rect': () => { const L = num($('#newL').value), W = num($('#newW').value); if (!(L >= 300 && W >= 300)) { say('Впишите длину и ширину новой комнаты в миллиметрах.', 'bad'); return; } addRoom(rectWalls(L, W), 'Комната ' + (S.rooms.length + 1)); },
  'room-add-tpl': b => { const t = TEMPLATES.find(x => x.id === b.dataset.tpl); if (t) addRoom(t.make(), t.name); },
  'room-dup': () => { const r = curRoom(), c = deep(r), b = floorBBox(), rb = bboxOf(roomGeom(r).poly); c.id = newId('r'); c.name = r.name + ' (копия)'; c.x0 = Math.round((b ? b.u1 : rb.u1) + 1000 + (num(r.x0) - rb.u0)); c.y0 = Math.round(num(r.y0) + ((b ? b.v0 : rb.v0) - rb.v0)); c.doors = []; S.rooms.push(c); UI.room = c.id; view.fitted = false; afterRooms('Копия добавлена справа.'); fitView(); draw(); },
  'room-rot': () => { const r = curRoom(); r.a0 = mod(num(r.a0) + 90, 360); afterRooms('Комната повёрнута на 90°.'); },
  'room-del': () => { const r = curRoom(); if (UI.delArm !== 'room:' + r.id) { UI.delArm = 'room:' + r.id; renderRoomEditor(); return; } S.rooms = S.rooms.filter(x => x.id !== r.id); UI.delArm = null; UI.room = S.rooms[0].id; afterRooms('Комната удалена.'); },
  'room-rect': () => { const L = num($('#rL').value), W = num($('#rW').value); if (!(L >= 300 && W >= 300)) { say('Впишите длину и ширину в миллиметрах.', 'bad'); return; } const r = curRoom(); r.walls = rectWalls(L, W); r.doors = (r.doors || []).filter(d => d.wall < 4); afterRooms(); },
  'room-tpl': b => { const t = TEMPLATES.find(x => x.id === b.dataset.tpl); if (!t) return; const r = curRoom(); r.walls = t.make(); r.doors = []; afterRooms('Форма «' + t.name + '»: поправьте длины стен под свою комнату.'); },
  'wall-shape': b => { const r = curRoom(), w = r.walls[+b.dataset.w]; if (!w) return; if (b.dataset.v === 'arc') { if (Math.abs(num(w.arc)) < 0.5) w.arc = Math.round(num(w.len) * 0.12 / 10) * 10 || 100; r.doors = (r.doors || []).filter(d => d.wall !== +b.dataset.w); } else w.arc = 0; UI.wallFocus = +b.dataset.w; renderRoomEditor(); invalidate({ fast: true }); },
  'wall-side': b => { const w = curRoom().walls[+b.dataset.w]; if (!w) return; w.arc = (b.dataset.v === 'in' ? -1 : 1) * Math.abs(num(w.arc)); renderRoomEditor(); invalidate({ fast: true }); },
  'wall-split': b => { const r = curRoom(), i = +b.dataset.w, w = r.walls[i]; if (!w || Math.abs(num(w.arc)) >= 0.5) return; r.walls.splice(i, 1, { len: num(w.len) / 2, turn: w.turn, arc: 0 }, { len: num(w.len) / 2, turn: 0, arc: 0 }); r.doors = (r.doors || []).map(d => d.wall > i ? Object.assign(d, { wall: d.wall + 1 }) : d); UI.wallFocus = i + 1; renderRoomEditor(); invalidate({ fast: true }); say('Стена разделена. Впишите новые длины и угол между частями.'); },
  'wall-del': b => { const r = curRoom(), i = +b.dataset.w; if (r.walls.length <= 2) return; r.walls.splice(i, 1); if (i === 0 && r.walls[0]) r.walls[0].turn = 0; r.doors = (r.doors || []).filter(d => d.wall !== i).map(d => d.wall > i ? Object.assign(d, { wall: d.wall - 1 }) : d); renderRoomEditor(); invalidate({ fast: true }); },
  'wall-add': () => { const r = curRoom(); r.walls.push({ len: 1000, turn: 90, arc: 0 }); UI.wallFocus = r.walls.length - 1; renderRoomEditor(); invalidate({ fast: true }); const el = $('#w' + (r.walls.length - 1) + 'len'); if (el) { el.focus(); el.select(); } },
  'corner-set': b => { const r = curRoom(), w = r.walls[+b.dataset.w]; if (!w) return; w.turn = 180 - num(b.dataset.v); renderRoomEditor(); invalidate({ fast: true }); },
  'close-auto': () => { const r = curRoom(), g = roomGeom(r); Object.assign(r, wallsFromCorners(g.corners, g.arcs)); renderRoomEditor(); invalidate({ fast: true }); },
  'door-add': () => { const r = curRoom(), g = roomGeom(r); let wi = -1, best = 0; for (let i = 0; i < g.n; i++) { const c = dist(g.corners[i], g.corners[(i + 1) % g.n]); if (Math.abs(g.arcs[i]) < 0.5 && c > best && c > 1000) { best = c; wi = i; } } if (wi < 0) { say('Нужна прямая стена длиннее метра.', 'bad'); return; } r.doors = r.doors || []; r.doors.push({ id: newId('d'), wall: wi, pos: Math.round((best - 900) / 2), width: 900 }); renderRoomEditor(); invalidate({ fast: true }); say('Проём добавлен на стену ' + (wi + 1) + '. Поставьте соседнюю комнату вплотную — рисунок пройдёт через проём.'); },
  'door-del': b => { curRoom().doors.splice(+b.dataset.d, 1); renderRoomEditor(); invalidate({ fast: true }); },
  'own-set': b => { const r = curRoom(); r.own = b.dataset.v === '1'; if (r.own) { r.pat = Object.assign(deep(S.floorPat), { refRoom: r.id, refWall: 0 }); UI.target = 'room:' + r.id; } afterRooms(r.own ? 'У комнаты «' + r.name + '» теперь свой рисунок — настройте его на шаге 3.' : 'Комната снова в общем рисунке.'); if (r.own) { recomputeNow(); centerTarget(UI.target, true); invalidate({ fast: true }); } },
  // покрытие
  'mat-target': b => { UI.matTarget = b.dataset.key; const m = curMat(false); if (m && m.cat) UI.catView = m.cat; renderMatTab(); },
  'cat': b => { UI.catView = b.dataset.cat; renderCats(); renderSizes(); },
  'item': b => { const cat = catById(UI.catView), it = allItems(cat).find(x => x.id === b.dataset.item); if (it) applyItem(cat, it); },
  'tone': b => { const m = curMat(true); m.tone = b.dataset.tone; renderTones(); invalidate(); if (UI.tab === 'pat') renderPatList(); },
  'save-custom': () => saveCustom(),
  // рисунок
  'pat-target': b => { UI.target = b.dataset.key; UI.variants = null; renderPatTab(); renderStatus(); draw(); },
  'pat': b => { const P = curP(); setPatternType(P, b.dataset.pat); clearVariants(); recomputeNow(); centerTarget(UI.target, true); renderPatTab(); invalidate({ fast: true }); },
  'dir': b => { const P = curP(); P.dir = b.dataset.v; clearVariants(); recomputeNow(); centerTarget(UI.target, true); syncPatternUI(); invalidate({ fast: true }); },
  'center': () => { recomputeNow(); centerTarget(UI.target, false); clearVariants(); invalidate({ fast: true }); },
  'corner0': () => { const P = curP(); P.offA = 0; P.offB = 0; syncPatInputs(); clearVariants(); invalidate({ fast: true }); },
  'optimize': () => optimize(),
  'variant': b => { const v = UI.variants && UI.variants.list[+b.dataset.i]; if (!v) return; const P = curP(); P.offA = v.offA; P.offB = v.offB; UI.variants.cur = +b.dataset.i; syncPatInputs(); renderVariants(); invalidate({ fast: true }); },
  'flipV': () => { const P = curP(); P.flipV = !P.flipV; clearVariants(); invalidate({ fast: true }); },
  'flipU': () => { const P = curP(); P.flipU = !P.flipU; clearVariants(); invalidate({ fast: true }); },
  'shuffle': () => { const P = curP(); P.seed = (num(P.seed, 1) | 0) + 1; invalidate({ fast: true }); },
  'border-toggle': () => { const r = curRoom(); r.border.on = !r.border.on; if (r.border.on) UI.target = 'border:' + r.id; afterRooms(r.border.on ? 'Рамка включена. Ниже выберите рисунок рамки, центр настраивается отдельно.' : 'Рамка выключена.'); },
  'border-type': b => { const r = curRoom(); r.border.pat.type = b.dataset.v; renderComposite(); invalidate({ fast: true }); },
  'border-tone': b => { const r = curRoom(); if (!r.border.mat) r.border.mat = deep(S.mat); r.border.mat.tone = b.dataset.tone; renderComposite(); invalidate({ fast: true }); },
  'ins-add': () => { const r = curRoom(), G = MODEL.geo[r.id]; if (!G || G.err) return; const b = bboxOf(G.center); const ins = { id: newId('i'), w: Math.round((b.u1 - b.u0) * 0.55 / 10) * 10, h: Math.round((b.v1 - b.v0) * 0.55 / 10) * 10, dx: 0, dy: 0, rot: 0, pat: defaultPat('basket'), mat: null }; r.inserts = r.inserts || []; r.inserts.push(ins); UI.target = 'ins:' + r.id + ':' + ins.id; recomputeNow(); centerTarget(UI.target, true); renderPatTab(); invalidate({ fast: true }); say('Вставка добавлена в центр комнаты. Задайте её размер и рисунок.'); },
  'ins-del': b => { const r = curRoom(); r.inserts.splice(+b.dataset.ins, 1); afterRooms('Вставка удалена.'); },
  'ins-rot': b => { const ins = curRoom().inserts[+b.dataset.ins]; if (!ins) return; ins.rot = num(b.dataset.v); renderComposite(); invalidate({ fast: true }); },
  'ins-edit': b => { UI.target = b.dataset.key; renderPatTab(); renderStatus(); draw(); },
  // расчёт
  'res-target': b => { UI.target = b.dataset.key; renderResults(); renderStatus(); draw(); },
  'grp': b => { const key = b.dataset.key, gk = b.dataset.gk; UI.hl = UI.hl && UI.hl.gk === gk && UI.hl.key === key ? null : { key, gk }; $$('.grp').forEach(x => x.setAttribute('aria-pressed', String(!!UI.hl && x.dataset.gk === UI.hl.gk && x.dataset.key === UI.hl.key))); draw(); },
  'export-img': () => exportImage(), 'export-copy': () => copyReport(), 'export-file': () => exportProject(),
  'piece-close': () => { UI.sel = null; UI.hl = null; renderPieceInfo(); draw(); },
  'piece-hl': () => { const sp = selectedPiece(); if (!sp) return; UI.hl = UI.hl && UI.hl.gk === sp.p.gk ? null : { key: sp.res.unit.key, gk: sp.p.gk }; renderPieceInfo(); draw(); },
};
$('.app').addEventListener('click', e => { const b = e.target.closest('[data-act]'); if (!b || b.disabled) return; const f = ACT[b.dataset.act]; if (f) f(b); });
document.addEventListener('focusin', e => { const c = e.target.closest && e.target.closest('.wcard'); if (c) { const i = +c.dataset.wi; if (i !== UI.wallFocus) { UI.wallFocus = i; $$('.wcard').forEach(x => x.classList.toggle('sel', +x.dataset.wi === i)); } } });
function addRoom(walls, name) {
  const [x, y] = placeNewRoom(), r = newRoom(name, walls, x, y); S.rooms.push(r); UI.room = r.id; UI.addRoom = false;
  view.fitted = false; afterRooms('Комната «' + name + '» добавлена справа. Подвиньте её к соседней в режиме «Комнаты» и добавьте проём.'); recomputeNow(); fitView(); draw();
}
function afterRooms(msg) { recomputeNow(); renderPlanTab(); if (UI.tab === 'pat') renderPatTab(); if (UI.tab === 'mat') renderMatTab(); invalidate({ fast: true }); if (msg) say(msg); }

/* ================= 2. Покрытие ================= */
function allItems(cat) { return cat.id === 'custom' ? Store.mats.map(m => Object.assign({}, m, { id: 'c:' + m.id })) : cat.items.map((it, i) => Object.assign({}, it, { id: cat.id + ':' + i })); }
function renderMatTab() {
  const keys = matKeys();
  $('#matTargets').innerHTML = keys.map(k => '<button class="chip" type="button" data-act="mat-target" data-key="' + k + '" aria-pressed="' + (k === UI.matTarget) + '">' + esc(matKeyName(k)) + '</button>').join('');
  const h = UI.matTarget === 'main' ? null : matHolder(UI.matTarget), useMain = !!h && !h.mat;
  $('#matUseMainFld').hidden = UI.matTarget === 'main'; $('#matUseMain').checked = useMain;
  $('#matEditor').hidden = useMain;
  $('#matTargetNote').textContent = UI.matTarget === 'main' ? (keys.length > 1 ? 'Основное покрытие — для общего рисунка. Рамку, вставки и комнаты со своим рисунком можно сделать из другого покрытия.' : 'Покрытие для всего этажа.') : useMain ? 'Используется основное покрытие. Снимите галочку, чтобы выбрать другое.' : 'Своё покрытие для «' + matKeyName(UI.matTarget) + '».';
  renderCats(); renderSizes(); renderTones(); syncInputs();
}
$('#matUseMain').addEventListener('change', e => { const h = matHolder(UI.matTarget); if (!h) return; h.mat = e.target.checked ? null : deep(S.mat); renderMatTab(); invalidate({ fast: true }); });
function renderCats() { $('#catChips').innerHTML = CATS.map(c => '<button class="chip" type="button" data-act="cat" data-cat="' + c.id + '" aria-pressed="' + (UI.catView === c.id) + '">' + esc(c.name) + '</button>').join(''); }
function renderSizes() {
  const cat = catById(UI.catView), items = allItems(cat), m = curMat(false);
  $('#sizesTitle').textContent = cat.name + ' — размеры';
  $('#sizesNote').textContent = cat.id === 'custom' ? (items.length ? 'Ваши сохранённые размеры.' : 'Здесь появятся ваши размеры. Впишите длину и ширину ниже и нажмите «В свои размеры».') : 'Типовые размеры. Если у вашей планки другие — впишите их ниже, расчёт обновится сразу.';
  $('#sizeList').innerHTML = items.map(it => {
    const sel = m.item === it.id || (!m.item && m.cat === cat.id && Math.abs(num(m.L) - it.L) < 0.5 && Math.abs(num(m.W) - it.W) < 0.5 && (m.shape || 'plank') === (it.shape || 'plank'));
    return '<button class="size" type="button" data-act="item" data-item="' + it.id + '" aria-pressed="' + sel + '"><b>' + mm(it.L) + '×' + mm(it.W) + '</b><span>' + esc([it.name, it.note, it.T ? it.T + ' мм' : ''].filter(Boolean).join(' · ')) + '</span></button>';
  }).join('');
}
function renderTones() { const m = curMat(false); $('#tones').innerHTML = Object.entries(TONES).map(([k, t]) => '<button class="tone" type="button" data-act="tone" data-tone="' + k + '" title="' + t.n + '" aria-label="' + t.n + '" aria-pressed="' + ((m.tone || 'oak') === k) + '" style="background:' + rgb(t.c) + '"></button>').join(''); }
function applyItem(cat, it) {
  const m = curMat(true);
  Object.assign(m, { cat: cat.id, item: it.id, L: it.L, W: it.W, T: it.T || '', shape: it.shape || 'plank', joint: it.joint !== undefined ? it.joint : (cat.joint || 0), tone: it.tone || cat.tone });
  const tk = UI.matTarget === 'main' ? 'floor' : UI.matTarget;
  if (UI.matTarget === 'main') { S.set.gap = cat.gap; S.set.kerf = cat.kerf; }
  if (targetKind(tk) !== 'border') {
    const P = patOf(tk), pid = it.shape === 'chevron' ? 'chevron' : (it.pat || cat.pat);
    setPatternType(P, pid);
    P.minPiece = Math.min(cat.minPiece, Math.round(it.L * 0.35 / 10) * 10 || cat.minPiece); P.minStag = Math.min(cat.minStag, Math.round(it.L * 0.3 / 10) * 10 || cat.minStag);
    if (it.angle) P.chevAngle = it.angle;
    if (UI.matTarget === 'main') for (const r of S.rooms) if (r.own && !r.mat) setPatternType(r.pat, pid);
    recomputeNow(); if (availTargets().includes(tk)) centerTarget(tk, true);
  }
  syncInputs(); renderSizes(); renderTones(); invalidate({ fast: true });
  say('Выбрано: ' + cat.name.toLowerCase() + ' ' + mm(it.L) + '×' + mm(it.W) + ' мм' + (targetKind(tk) !== 'border' ? ', рисунок «' + patDef(patOf(tk).type).name + '»' : '') + '.');
}
async function saveCustom() {
  const m = curMat(false), L = num(m.L), W = num(m.W); if (!(L >= 20 && W >= 20)) { say('Сначала впишите длину и ширину планки.', 'bad'); return; }
  const name = $('#customName').value.trim() || (catById(m.cat).name + ' ' + mm(L) + '×' + mm(W));
  const it = { id: Date.now().toString(36), name, L, W, T: num(m.T) || '', shape: m.shape, joint: num(m.joint), tone: m.tone };
  await Store.saveMats([...Store.mats, it]); $('#customName').value = ''; UI.catView = 'custom'; m.cat = 'custom'; m.item = 'c:' + it.id; renderCats(); renderSizes(); say('Размер «' + name + '» сохранён в «Свои размеры».', 'ok');
}

/* ================= 3. Рисунок ================= */
function setPatternType(P, id) {
  const old = patDef(P.type), nw = patDef(id); P.type = id;
  if (old.group !== nw.group || P.minEdge === undefined) { P.minEdge = nw.group === 'bond' ? 50 : 25; P.keepCenter = nw.group === 'herring' || nw.group === 'chevron'; }
}
function renderPatTab() {
  fixTargets();
  const keys = availTargets();
  $('#patTargets').innerHTML = keys.map(k => '<button class="chip" type="button" data-act="pat-target" data-key="' + k + '" aria-pressed="' + (k === UI.target) + '">' + esc(unitName(k)) + '</button>').join('');
  const kind = targetKind(UI.target), res = MODEL && MODEL.byKey[UI.target];
  $('#patTargetNote').textContent = kind === 'floor' ? (res && res.unit.roomIds.length > 1 ? 'Один рисунок на комнаты: ' + res.unit.roomIds.map(roomName).join(', ') + '. Он идёт через проёмы без сдвига.' : 'Рисунок комнаты.') : kind === 'border' ? 'Рамка вдоль стен: ряды идут параллельно каждой стене, в углах — рез на ус 45°.' : kind === 'ins' ? 'Вставка в центре комнаты со своим рисунком.' : 'Отдельный рисунок комнаты, не связан с соседними.';
  renderComposite(); renderPatList(); renderRefSelects(); syncPatternUI(); renderVariants(); syncPatInputs();
}
function renderComposite() {
  const r = curRoom(), box = $('#compBox'); if (!r) { box.innerHTML = ''; return; }
  $('#compRoom').textContent = r.name;
  const B = r.border, bm = B.mat || S.mat, G = MODEL && MODEL.geo[r.id];
  let h = '<div class="comp"><header><h4>Рамка вдоль стен</h4><button class="btn small' + (B.on ? ' primary' : '') + '" type="button" data-act="border-toggle" aria-pressed="' + B.on + '">' + (B.on ? 'Включена' : 'Включить') + '</button></header>';
  if (B.on) {
    h += '<div class="grid2"><label class="fld"><span>Рядов в рамке</span><span class="inp"><input id="bRows" data-bf="rows" data-num inputmode="numeric" value="' + (B.rows | 0) + '"><i>шт</i></span></label><div class="fld"><span>Ширина рамки</span><b style="font:600 15px var(--font-mono);padding:8px 0">' + (G && G.bw ? mm(G.bw) + ' мм' : '—') + '</b></div></div>' +
      '<div class="chips">' + BORDER_PATTERNS.map(id => '<button class="chip" type="button" data-act="border-type" data-v="' + id + '" aria-pressed="' + (B.pat.type === id) + '">' + esc(patDef(id).name) + '</button>').join('') + '</div>' +
      '<div class="tones" aria-label="Цвет рамки">' + Object.entries(TONES).map(([k, t]) => '<button class="tone" type="button" data-act="border-tone" data-tone="' + k + '" title="' + t.n + '" aria-label="Рамка: ' + t.n + '" aria-pressed="' + ((bm.tone || 'oak') === k) + '" style="background:' + rgb(t.c) + '"></button>').join('') + '</div>' +
      (G && G.borderErr ? '<p class="note bad">' + esc(G.borderErr) + '</p>' : '<p class="note">Планка рамки ' + mm(num(bm.L)) + '×' + mm(num(bm.W)) + ' мм. Другую планку для рамки выберите на шаге 2.</p>');
  } else h += '<p class="note">Например, центр квадратами, а по краям — палуба вразбежку. Рамка ложится вдоль всех стен комнаты.</p>';
  h += '</div><div class="comp"><header><h4>Вставки в центре</h4><button class="btn small" type="button" data-act="ins-add">' + ICON.plus + 'Добавить</button></header>';
  (r.inserts || []).forEach((ins, j) => {
    const key = 'ins:' + r.id + ':' + ins.id;
    h += '<div style="display:grid;gap:8px;padding-top:8px;border-top:1px dashed var(--line)"><div class="whead"><b>Вставка ' + (j + 1) + ' · ' + esc(patDef(ins.pat.type).name) + '</b><button class="btn small" type="button" data-act="ins-edit" data-key="' + key + '"' + (UI.target === key ? ' disabled' : '') + '>' + (UI.target === key ? 'Настраиваем' : 'Рисунок') + '</button><button class="icon" type="button" data-act="ins-del" data-ins="' + j + '" aria-label="Удалить вставку ' + (j + 1) + '">' + ICON.del + '</button></div>' +
      '<div class="grid2"><label class="fld"><span>Длина</span><span class="inp"><input id="i' + j + 'w" data-ins="' + j + '" data-f="w" data-num inputmode="decimal" value="' + mm(ins.w) + '"><i>мм</i></span></label><label class="fld"><span>Ширина</span><span class="inp"><input id="i' + j + 'h" data-ins="' + j + '" data-f="h" data-num inputmode="decimal" value="' + mm(ins.h) + '"><i>мм</i></span></label>' +
      '<label class="fld"><span>Сдвиг вдоль стены 1</span><span class="inp"><input id="i' + j + 'dx" data-ins="' + j + '" data-f="dx" data-num inputmode="decimal" value="' + mm(ins.dx) + '"><i>мм</i></span></label><label class="fld"><span>Сдвиг от стены 1</span><span class="inp"><input id="i' + j + 'dy" data-ins="' + j + '" data-f="dy" data-num inputmode="decimal" value="' + mm(ins.dy) + '"><i>мм</i></span></label></div>' +
      '<div class="seg mini" role="group" aria-label="Поворот вставки"><button type="button" data-act="ins-rot" data-ins="' + j + '" data-v="0" aria-pressed="' + (num(ins.rot) === 0) + '">Прямо</button><button type="button" data-act="ins-rot" data-ins="' + j + '" data-v="45" aria-pressed="' + (num(ins.rot) === 45) + '">Ромбом 45°</button></div></div>';
  });
  if (!(r.inserts || []).length) h += '<p class="note">Прямоугольник со своим рисунком: «ковёр» из квадратов или ёлочки посреди палубы.</p>';
  box.innerHTML = h + '</div>';
}
function renderPatList() {
  const el = $('#patList'), kind = targetKind(UI.target), list = kind === 'border' ? PATTERNS.filter(p => BORDER_PATTERNS.includes(p.id)) : PATTERNS, P = curP();
  el.innerHTML = list.map(p => '<button class="pat" type="button" data-act="pat" data-pat="' + p.id + '" aria-pressed="' + (p.id === P.type) + '"><canvas></canvas><b>' + esc(p.name) + '</b><span>' + esc(p.sub || '') + '</span></button>').join('');
  const M = E.unitMat(matForKey(UI.target), S);
  $$('.pat', el).forEach(b => drawPreview($('canvas', b), b.dataset.pat, M, P));
}
function drawPreview(c, pid, M, Pt) {
  const pd = patDef(pid), dpr = window.devicePixelRatio || 1, w = c.clientWidth || 100, h = c.clientHeight || 56;
  c.width = w * dpr; c.height = h * dpr; const ctx = c.getContext('2d'); ctx.setTransform(dpr, 0, 0, dpr, 0, 0); ctx.clearRect(0, 0, w, h);
  let L = M.L, W = M.W, g = M.g; if (!(L >= 20 && W >= 20) || L < W) { L = 1200; W = 200; g = 0; }
  const span = pd.group === 'bond' ? 1.45 * L : pd.group === 'basket' ? 2.3 * L : 2.6 * L, s = Math.max(w / span, 4 / W), bw = w / s, bh = h / s;
  const box = [[0, 0], [bw, 0], [bw, bh], [0, bh]], bb = { u0: 0, v0: 0, u1: bw, v1: bh }, Mx = { L, W, g, kerf: 3 };
  let raw = [];
  try {
    if (pd.group === 'herring' && pd.n * (W + g) >= L + g) raw = [];
    else if (pd.id === 'remnant') raw = planRemnant([box], [], bb, Mx, { minPiece: Math.min(num(Pt.minPiece, 300), L * 0.3), minStag: Math.min(num(Pt.minStag, 300), L * 0.3) }).raw;
    else if (pd.id === 'random') raw = genBond(bb, L, W, g, randShifts(-2, Math.ceil(bh / W) + 2, L + g, L * 0.25, 3));
    else if (pd.group === 'bond') raw = genBond(bb, L, W, g, k => mod(k * pd.frac * (L + g), L + g));
    else if (pd.group === 'herring') raw = genHerring(bb, L, W, g, pd.n);
    else if (pd.group === 'chevron') raw = genChevron(bb, L, W, g, clamp(num(Pt.chevAngle, 45), 15, 75));
    else raw = genBasket(bb, L, W, g);
  } catch (e) { raw = []; }
  raw.forEach((p, i) => { const poly = clipBy(box, p.poly); if (poly.length < 3) return; ctx.beginPath(); poly.forEach((q, k) => k ? ctx.lineTo(q[0] * s, q[1] * s) : ctx.moveTo(q[0] * s, q[1] * s)); ctx.closePath(); ctx.fillStyle = rgb(woodRGB(M.tone, i, p.kind)); ctx.fill(); ctx.lineWidth = 0.7; ctx.strokeStyle = 'rgba(40,28,18,.55)'; ctx.stroke(); });
  if (!raw.length) { ctx.fillStyle = COL.muted; ctx.font = '500 11px ' + COL.body; ctx.textAlign = 'center'; ctx.textBaseline = 'middle'; ctx.fillText('не подходит к размеру', w / 2, h / 2); }
}
function renderRefSelects() {
  const P = curP(), kind = targetKind(UI.target);
  const rr = kind === 'floor' ? S.rooms.filter(r => !r.own) : [room(UI.target.split(':')[1])].filter(Boolean);
  $('#refRoomFld').hidden = kind !== 'floor' || rr.length < 2;
  $('#refRoom').innerHTML = rr.map(r => '<option value="' + r.id + '"' + (r.id === P.refRoom ? ' selected' : '') + '>' + esc(r.name) + '</option>').join('');
  const refR = kind === 'floor' ? (rr.find(r => r.id === P.refRoom) || rr[0]) : rr[0];
  const g = refR ? roomGeom(refR) : null;
  $('#refWall').innerHTML = g ? g.corners.map((p, i) => '<option value="' + i + '"' + (i === (num(P.refWall) | 0) ? ' selected' : '') + '>Стена ' + (i + 1) + ' · ' + mm(dist(p, g.corners[(i + 1) % g.n])) + ' мм</option>').join('') : '';
}
function syncPatternUI() {
  const P = curP(), pd = patDef(P.type), grp = pd.group, kind = targetKind(UI.target);
  $$('#dirSeg button').forEach(b => b.setAttribute('aria-pressed', String(b.dataset.v === P.dir)));
  $('#dirSec').hidden = kind === 'border';
  $('#refFlds').hidden = kind === 'ins';
  $('#customAngleFld').hidden = P.dir !== 'custom';
  $('#chevFld').hidden = grp !== 'chevron';
  $$('[data-show]').forEach(el => { const k = el.dataset.show; el.hidden = !(k === grp || k === pd.id); });
  $('#keepCenterFld').hidden = !(grp === 'herring' || grp === 'chevron') || kind === 'border';
  $('#offBFld').hidden = kind === 'border';
  $('#btnCenter').hidden = kind === 'border';
  $('#flipBtns').hidden = kind === 'border';
  const segTxt = grp === 'bond' || grp === 'basket' ? ['Вдоль', 'Поперёк', '45°', 'Свой угол'] : ['Ось вдоль', 'Ось поперёк', '45°', 'Свой угол'];
  $$('#dirSeg button').forEach((b, i) => { b.textContent = segTxt[i]; });
  $('#dirTitle').textContent = 'Направление · ' + (grp === 'herring' ? 'ось ёлочки' : grp === 'chevron' ? 'линия вершин' : grp === 'basket' ? 'квадраты' : 'доски');
  $('#dirNote').textContent = kind === 'ins' ? 'Направление считается от сторон вставки.' : grp === 'herring' ? 'Ось ёлочки параллельна опорной стене, планки идут к стенам под 45°. «45°» поворачивает ось — тогда планки параллельны стенам.' : grp === 'chevron' ? 'Вершины французской ёлочки идут по линии вдоль опорной стены. Обычно её ведут вдоль длинной стороны или по свету из окна.' : 'Доски кладут вдоль света из окна или вдоль длинной стены.';
  $('#btnFlipV').textContent = grp === 'bond' ? 'Первый ряд — у другой стены' : 'Отразить ⇅';
  $('#btnFlipU').textContent = grp === 'bond' ? 'Ряд начинать с другого конца' : 'Отразить ⇄';
  $('#offBLabel').textContent = kind === 'ins' ? 'Сдвиг поперёк' : grp === 'herring' ? 'Ось: сдвиг от стены' : grp === 'chevron' ? 'Вершины: сдвиг от стены' : 'Сдвиг от опорной стены';
  $('#offALabel').textContent = kind === 'border' ? 'Сдвиг стыков вдоль стен' : kind === 'ins' ? 'Сдвиг вдоль' : 'Сдвиг вдоль стены';
  const M = E.unitMat(matForKey(UI.target), S), pn = $('#patNote'); let note = '';
  if (grp === 'chevron' && M.shape !== 'chevron') note = 'Для французской ёлочки нужны планки со скошенными торцами (левые и правые). Прямоугольные придётся подрезать по торцам под ' + num(P.chevAngle, 45) + '°.';
  else if (grp !== 'chevron' && M.shape === 'chevron') note = 'Выбраны планки со скошенными торцами — они для французской ёлочки.';
  else if (grp === 'basket' && Math.abs(Math.round((M.L + M.g) / (M.W + M.g)) * (M.W + M.g) - (M.L + M.g)) > 1.5) note = 'Для квадратов длина должна делиться на ширину без остатка (280×70 = 4 планки). Сейчас ' + mm(M.L) + '/' + mm(M.W) + ' ≈ ' + f1(M.L / M.W) + ' — будут щели или нахлёст.';
  else if (grp === 'herring') note = 'Для ёлочки нужны левые (A) и правые (B) планки поровну.';
  pn.hidden = !note; pn.textContent = note; pn.className = 'note' + (note && !note.startsWith('Для ёлочки') ? ' warn' : '');
  $('#nudgeTarget').textContent = unitName(UI.target).toLowerCase();
  $$('.pad button').forEach(b => { const [, dy] = b.dataset.nudge.split(',').map(Number); b.disabled = kind === 'border' && dy !== 0; });
}
function clearVariants() { UI.variants = null; renderVariants(); }
function clearVariantMark() { if (UI.variants) { UI.variants.cur = -1; renderVariants(); } }
function renderVariants() {
  const el = $('#variants'); if (!el) return; const V = UI.variants;
  if (!V || V.key !== UI.target || !V.list.length) { el.innerHTML = ''; return; }
  el.innerHTML = '<p class="note">Лучшие положения. Нажмите, чтобы примерить на карте:</p>' + V.list.map((v, i) => '<button class="var" type="button" data-act="variant" data-i="' + i + '" aria-pressed="' + (V.cur === i) + '"><span class="vn">' + (i + 1) + '</span><span>' + (v.bad ? '<b style="color:var(--bad)">узких ' + v.bad + '</b>' : '<b>без узких</b>') + ' · мин. кусок ' + mm(v.minT) + ' мм · подрезок ' + v.cuts + '<br><small>сдвиг ' + (targetKind(V.key) === 'border' ? 'вдоль ' + mm(v.offA) : mm(v.offB) + ' / ' + mm(v.offA)) + ' мм</small></span></button>').join('');
}

/* сдвиг и центрирование */
function shiftP(F, P, du, dv) { const w = F.vecW([du, dv]); P.offA = Math.round(num(P.offA) + w[0] * F.e1[0] + w[1] * F.e1[1]); P.offB = Math.round(num(P.offB) + w[0] * F.e2[0] + w[1] * F.e2[1]); }
function balanceShift(a, b, P, sym) { const span = b - a, rem = mod(span, P); const w0 = rem < 1 || P - rem < 1 ? P : rem < P / 2 ? (rem + P) / 2 : sym ? rem / 2 : P; return mod(a + w0, P); }
function centerTarget(key, quiet) {
  const geo = MODEL ? MODEL.geo : computeGeo(S), u = buildUnit(key, S, geo); if (!u || u.kind === 'border') return;
  const P = u.P, M = u.mat, pd = patDef(P.type), F = u.parts[0].frame;
  const polys = (u.kind === 'ins' ? [u.ins.region] : [geo[u.refRoom].center]).map(p => p.map(F.toL)), b = bboxOf(polys.flat()), c = centroidMany(polys);
  let du = 0, dv = 0;
  if (pd.group === 'herring') { const per = Math.SQRT2 * (M.L + M.g), pu = Math.SQRT2 * pd.n * (M.W + M.g); dv = c[1] - Math.round(c[1] / per) * per; du = c[0] - Math.round(c[0] / pu) * pu; }
  else if (pd.group === 'chevron') { const Sv = (M.L + M.g) * Math.sin(clamp(num(P.chevAngle, 45), 15, 75) * DEG); dv = c[1] - Math.round(c[1] / Sv) * Sv; }
  else if (pd.group === 'basket') { const B = M.L + M.g; du = balanceShift(b.u0, b.u1, B, true); dv = balanceShift(b.v0, b.v1, B, true); }
  else { dv = balanceShift(b.v0, b.v1, M.W + M.g, pd.id === 'grid' || u.kind === 'ins'); if (pd.id === 'grid' || u.kind === 'ins') du = balanceShift(b.u0, b.u1, M.L + M.g, true); }
  shiftP(F, P, du, dv); syncPatInputs();
  if (!quiet) say(pd.group === 'herring' || pd.group === 'chevron' ? 'Ось поставлена по центру — подрезки у противоположных стен одинаковые.' : pd.group === 'bond' && pd.id !== 'grid' ? 'Первый ряд целый, если последний выходит не уже половины доски. Иначе крайние ряды поровну.' : 'Рисунок по центру: подрезки у противоположных стен одинаковые.', 'ok');
}
let optimizing = false;
async function optimize() {
  if (optimizing || !MODEL) return; const btn = $('#btnOptimize'), key = UI.target, geo = MODEL.geo;
  const u0 = buildUnit(key, S, geo); if (!u0) return;
  const base = computeUnit(u0, true); if (base.err) { say(base.err, 'bad'); return; }
  optimizing = true; btn.disabled = true;
  const P = u0.P, pd = patDef(P.type), M = u0.mat, F = u0.parts[0].frame, kind = u0.kind;
  const keep = !!P.keepCenter && (pd.group === 'herring' || pd.group === 'chevron') && kind !== 'border';
  let pu, pv;
  if (pd.group === 'bond') { pu = M.L + M.g; pv = M.W + M.g; }
  else if (pd.group === 'herring') { pu = Math.SQRT2 * pd.n * (M.W + M.g); pv = Math.SQRT2 * (M.L + M.g); }
  else if (pd.group === 'chevron') { const a = clamp(num(P.chevAngle, 45), 15, 75) * DEG; pu = (M.W + M.g) / Math.sin(a); pv = 2 * (M.L + M.g) * Math.sin(a); }
  else { pu = pv = 2 * (M.L + M.g); }
  const onlyV = pd.id === 'remnant' && kind !== 'border', onlyU = keep || kind === 'border';
  const N2 = clamp(Math.round(Math.sqrt(600000 / Math.max(50, base.pieces.length))), 12, 26);
  const Nu = onlyV ? 1 : onlyU ? 40 : N2, Nv = kind === 'border' ? 1 : onlyU ? 2 : onlyV ? 40 : N2;
  const A0 = num(P.offA), B0 = num(P.offB), seen = [];
  const at = (du, dv) => { if (kind === 'border') return [A0 + du, 0]; const w = F.vecW([du, dv]); return [A0 + w[0] * F.e1[0] + w[1] * F.e1[1], B0 + w[0] * F.e2[0] + w[1] * F.e2[1]]; };
  const evalAt = (du, dv) => { const o = at(du, dv); P.offA = o[0]; P.offB = o[1]; const r = computeUnit(buildUnit(key, S, geo), true); const v = { s: r.err ? Infinity : r.score, du, dv, bad: r.bad, minT: r.minT, cuts: r.cuts, offA: Math.round(o[0]), offB: Math.round(o[1]) }; seen.push(v); return v; };
  const starts = 6, levels = 3, total = Nu * Nv + starts * levels * 24; let cnt = 0;
  const tick = async () => { if (++cnt % 6 === 0) { btn.textContent = 'Подбираю… ' + Math.min(99, Math.round(cnt / total * 100)) + '%'; await new Promise(r => setTimeout(r, 0)); } };
  const coarse = [evalAt(0, 0)];
  for (let i = 0; i < Nu; i++) for (let j = 0; j < Nv; j++) { if (!i && !j) continue; coarse.push(evalAt(i / Nu * pu, j / Nv * pv)); await tick(); }
  coarse.sort((x, y) => x.s - y.s);
  for (const c0 of coarse.slice(0, starts)) {
    let cur = c0, hu = onlyV ? 0 : pu / Nu / 2, hv = onlyU ? 0 : pv / Nv / 2;
    for (let lv = 0; lv < levels; lv++) {
      let nb = cur;
      for (const i of hu ? [-2, -1, 0, 1, 2] : [0]) for (const j of hv ? [-2, -1, 0, 1, 2] : [0]) { if (!i && !j) continue; const v = evalAt(cur.du + i * hu / 2, cur.dv + j * hv / 2); if (v.s < nb.s - 1e-6) nb = v; await tick(); }
      cur = nb; hu /= 2; hv /= 2;
    }
  }
  // устойчивые варианты: проверяем после округления до миллиметра и берём разные по положению
  seen.sort((x, y) => x.s - y.s);
  const list = [], minSep = Math.min(pu, pv) * 0.12;
  for (const v of seen) {
    if (list.length >= 5) break;
    if (list.some(x => Math.hypot(x.offA - v.offA, x.offB - v.offB) < minSep)) continue;
    P.offA = v.offA; P.offB = v.offB; const r = computeUnit(buildUnit(key, S, geo), true); if (r.err) continue;
    list.push({ offA: v.offA, offB: v.offB, s: r.score, bad: r.bad, minT: r.minT, cuts: r.cuts });
  }
  list.sort((x, y) => x.s - y.s);
  const best = list[0] || { offA: A0, offB: B0 };
  P.offA = best.offA; P.offB = best.offB;
  UI.variants = { key, list, cur: 0 };
  btn.textContent = 'Подобрать варианты'; btn.disabled = false; optimizing = false;
  syncPatInputs(); renderVariants(); recompute(); invalidate({ fast: true });
  const st = MODEL.byKey[key] && MODEL.byKey[key].stats;
  if (st && st.nBad) say('Вариант 1 применён: узких подрезок ' + st.nBad + '.' + (keep ? ' Снимите галочку «Только симметричные варианты» — без неё вариантов больше.' : ' Можно уменьшить порог в «Правилах» или сменить направление.'), 'bad');
  else say('Вариант 1 применён: узких подрезок нет, самый маленький кусок ' + (st ? mm(st.minT) : '—') + ' мм. Ниже — другие варианты.', 'ok');
}
/* стрелки под картой */
$('#nudge').addEventListener('click', e => {
  const b = e.target.closest('button'); if (!b || b.disabled) return;
  if ('stepCycle' in b.dataset) { UI.step = UI.step === 1 ? 10 : UI.step === 10 ? 50 : 1; syncStep(); saveUI(); return; }
  if (!b.dataset.nudge || !MODEL) return;
  const res = MODEL.byKey[UI.target]; if (!res || res.err) return;
  const [sx, sy] = b.dataset.nudge.split(',').map(Number), F = res.unit.parts[0].frame, P = curP(), d = UI.step;
  if (res.unit.kind === 'border') P.offA = Math.round(num(P.offA) + sx * d);
  else { const wx = sx * d, wy = sy * d; P.offA = Math.round(num(P.offA) + wx * F.e1[0] + wy * F.e1[1]); P.offB = Math.round(num(P.offB) + wx * F.e2[0] + wy * F.e2[1]); }
  syncPatInputs(); clearVariantMark(); invalidate();
});
function syncStep() { $('#stepBtn').textContent = 'шаг ' + UI.step + ' мм'; }

/* ================= 4. Расчёт ================= */
const wallRef = (rid, i, multi) => 'стены ' + (i + 1) + (multi ? ' (' + roomName(rid) + ')' : '');
function unitSteps(res) {
  const u = res.unit, st = res.stats, M = u.mat, pd = patDef(u.P.type), gap = num(S.set.gap), steps = [], multi = u.roomIds.length > 1 || S.rooms.length > 1;
  const gtxt = gl => { const p = []; if (gl.lo) p.push('<b>' + mm(gl.lo.dist) + ' мм</b> от ' + wallRef(gl.room, gl.lo.wall, multi)); if (gl.hi) p.push('<b>' + mm(gl.hi.dist) + ' мм</b> от ' + wallRef(gl.room, gl.hi.wall, multi)); return p.join(' и '); };
  if (u.kind === 'border') {
    const G = MODEL.geo[u.roomIds[0]];
    steps.push('Рамка: <b>' + (u.P && room(u.roomIds[0]).border.rows) + ' ' + plural(room(u.roomIds[0]).border.rows | 0, 'ряд', 'ряда', 'рядов') + '</b> по ' + mm(M.W) + ' мм вдоль всех стен, общая ширина <b>' + mm(G.bw) + ' мм</b>. В углах планки режутся на ус (45°).');
    steps.push('Отбейте линию рамки: <b>' + mm(G.bw + gap) + ' мм</b> от стен (' + mm(gap) + ' мм зазор + рамка). Обычно центр кладут с запасом, по этой линии подрезают его и затем кладут рамку.');
    steps.push('Рисунок рамки: «' + pd.name + '». Ряды идут от стены к центру.');
  } else if (u.kind === 'ins') {
    const ins = u.ins, g = MODEL.geo[u.refRoom].g, d1 = lineDist(ins.C, g, 0), d2w = perpWall(g, 0), d2 = d2w >= 0 ? lineDist(ins.C, g, d2w) : null;
    steps.push('Вставка ' + mm(num(ins.ins.w)) + '×' + mm(num(ins.ins.h)) + ' мм' + (num(ins.ins.rot) ? ', повёрнута на ' + num(ins.ins.rot) + '°' : '') + '. Центр — в <b>' + mm(d1) + ' мм</b> от стены 1' + (d2 !== null ? ' и <b>' + mm(d2) + ' мм</b> от стены ' + (d2w + 1) : '') + '.');
    steps.push('Отбейте контур вставки, уложите её первой, затем основной рисунок вокруг с подрезкой по контуру.');
  } else {
    if (gap > 0) steps.push('Поставьте клинья: зазор <b>' + mm(gap) + ' мм</b> от стен (его закроет плинтус).');
    if (u.kind === 'floor' && u.roomIds.length > 1) steps.push('Рисунок общий для комнат: ' + u.roomIds.map(roomName).join(', ') + '. Через проёмы ведите его без сдвига, порог не нужен.');
  }
  if (pd.group === 'bond' && res.rows && res.rows.length && u.kind !== 'border') {
    const rows = res.rows, first = rows[0], last = rows[rows.length - 1], thr = num(u.P.minEdge, 50);
    steps.push('Всего <b>' + rows.length + ' ' + plural(rows.length, 'ряд', 'ряда', 'рядов') + '</b>. Начало — угол с отметкой «СТАРТ» на плане.');
    steps.push('Первый ряд: ширина <b>' + mm(first.width) + ' мм</b>' + (first.width < M.W - 0.5 ? ' — распустите доски вдоль, отпилите ' + mm(M.W - first.width) + ' мм (со стороны стены обычно срезают гребень).' : ' — доски целые по ширине.'));
    if (rows.length > 1) steps.push('Последний ряд: ширина <b>' + mm(last.width) + ' мм</b>' + (last.width < thr ? '. <b style="color:var(--bad)">Это узко</b> — нажмите «По центру» или «Подобрать варианты» на шаге 3.' : '.'));
    if (pd.id === 'remnant') steps.push('Каждый следующий ряд начинайте обрезком от конца предыдущего — длины кусков по рядам ниже. Стыки соседних рядов не ближе <b>' + mm(num(u.P.minStag)) + ' мм</b>, куски не короче <b>' + mm(num(u.P.minPiece)) + ' мм</b>.');
    else if (pd.frac > 0) steps.push('Смещение стыков в соседних рядах: <b>' + mm(pd.frac * (M.L + M.g)) + ' мм</b>.');
    else if (pd.id === 'random') steps.push('Разбег стыков случайный, но не меньше <b>' + mm(num(u.P.minStag)) + ' мм</b>.');
    for (const gl of res.guides || []) if (gl.lo || gl.hi) steps.push((pd.id === 'grid' ? 'Разметочная линия по шву: ' : 'Для клеевой укладки отбейте линию по ' + gl.name + ': ') + gtxt(gl) + '.');
  } else if (pd.group === 'herring' && u.kind !== 'border') {
    const gl = res.guides[0], Wc = pd.n * (M.W + M.g), Lc = M.L + M.g;
    steps.push('Отбейте шнуром ось ёлочки (синий пунктир): ' + (gl && (gl.lo || gl.hi) ? gtxt(gl) : 'по центру') + '. Расстояния — до самой стены.');
    steps.push('Начинайте от оси: первая «ёлка» по линии, дальше в обе стороны. Шаг вдоль оси — <b>' + mm(Math.SQRT2 * Wc) + ' мм</b> на пару ' + (pd.n > 1 ? 'блоков' : 'планок') + ', соседние ёлки — через <b>' + mm(Math.SQRT2 * Lc) + ' мм</b>.');
    steps.push('Нужны левые и правые планки: A — <b>' + st.nA + '</b>, B — <b>' + st.nB + '</b> шт (с подрезками).');
  } else if (pd.group === 'chevron' && u.kind !== 'border') {
    const gl = res.guides[0], a = clamp(num(u.P.chevAngle, 45), 15, 75) * DEG;
    steps.push('Отбейте линию вершин (синий пунктир): ' + (gl && (gl.lo || gl.hi) ? gtxt(gl) : 'по центру') + '. По ней сходятся торцы планок.');
    steps.push('Вершины вдоль линии — через <b>' + mm((M.W + M.g) / Math.sin(a)) + ' мм</b>, следующие линии вершин — через <b>' + mm((M.L + M.g) * Math.sin(a)) + ' мм</b>.');
    steps.push('Планки A — <b>' + st.nA + '</b>, B — <b>' + st.nB + '</b> шт (с подрезками).');
  } else if (pd.group === 'basket') {
    for (const gl of res.guides || []) if (gl.lo || gl.hi) steps.push('Разметочная линия по краю квадратов: ' + gtxt(gl) + '.');
    const n = Math.max(1, Math.round((M.L + M.g) / (M.W + M.g)));
    steps.push('Квадрат — ' + n + ' ' + plural(n, 'планка', 'планки', 'планок') + ' по ' + mm(M.L) + ' мм, соседние квадраты повёрнуты на 90°.');
  }
  const worst = (res.walls || []).filter(w => w.count && w.minT < num(u.P.minEdge, 25));
  if (worst.length) steps.push('<b style="color:var(--bad)">Узкие подрезки</b> у ' + worst.map(w => (w.label === 'стена' ? 'стены ' : 'рамки у стены ') + (w.i + 1) + (multi ? ' (' + roomName(w.rid) + ')' : '')).join(', ') + '. Сдвиньте рисунок или нажмите «Подобрать варианты».');
  else if (st.nCut) steps.push('Узких подрезок нет: самый маленький кусок ' + mm(st.minT) + ' мм.');
  return steps;
}
function lineDist(p, g, i) { const a = g.corners[i], b = g.corners[(i + 1) % g.n], dx = b[0] - a[0], dy = b[1] - a[1], l = Math.hypot(dx, dy) || 1; return Math.abs((p[0] - a[0]) * dy - (p[1] - a[1]) * dx) / l; }
function perpWall(g, i) { const d0 = unitV(g.corners[i], g.corners[(i + 1) % g.n]); for (let k = 1; k < g.n; k++) { const j = (i + k) % g.n; if (Math.abs(g.arcs[j]) >= 0.5) continue; const d = unitV(g.corners[j], g.corners[(j + 1) % g.n]); if (Math.abs(d0[0] * d[0] + d0[1] * d[1]) < 0.02) return j; } return -1; }
function renderResults() {
  const el = $('#results'); if (!MODEL) return;
  const errs = S.rooms.filter(r => MODEL.geo[r.id].err), reserve = Math.max(0, num(S.set.reserve));
  let roomsA = 0, layA = 0; for (const r of S.rooms) { const G = MODEL.geo[r.id]; if (G.err) continue; roomsA += Math.abs(area(G.g.poly)); layA += Math.abs(area(G.lay)); }
  let h = '<div class="sec"><h3>Итог по этажу <small>' + S.rooms.length + ' ' + plural(S.rooms.length, 'комната', 'комнаты', 'комнат') + '</small></h3>' +
    (errs.length ? '<p class="note bad">Не построены: ' + errs.map(r => esc(r.name) + ' — ' + esc(MODEL.geo[r.id].err)).join('; ') + '</p>' : '') +
    '<div class="tiles"><div class="tile"><b>' + fm2(roomsA) + ' м²</b><span>площадь комнат</span></div><div class="tile"><b>' + fm2(layA) + ' м²</b><span>под укладку, без зазора</span></div></div></div>';
  h += '<div class="sec"><h3>Сколько покупать</h3><div class="tblwrap"><table class="tbl"><thead><tr><th>Покрытие</th><th>По плану</th><th>С запасом ' + f1(reserve) + '%</th></tr></thead><tbody>';
  for (const m of MODEL.mats) {
    const M = m.M, br = Math.ceil(m.boards * (1 + reserve / 100)), isMain = M.key === E.unitMat(S.mat, S).key;
    let packs = '';
    if (isMain && num(S.set.perPack) > 0) packs = ' · ' + Math.ceil(br / num(S.set.perPack)) + ' уп.';
    else if (isMain && num(S.set.packM2) > 0) packs = ' · ' + Math.ceil(br * M.L * M.W / 1e6 / num(S.set.packM2) - 1e-9) + ' уп.';
    h += '<tr><td>' + esc(catById(M.cat).name) + ' ' + mm(M.L) + '×' + mm(M.W) + '<br><small class="hint">' + esc(m.names.join(', ')) + '</small></td><td class="n">' + m.boards + ' шт<br><small class="hint">' + fm2(m.boards * M.L * M.W) + ' м²</small></td><td class="n"><b>' + br + ' шт</b>' + packs + '<br><small class="hint">' + fm2(br * M.L * M.W) + ' м²</small></td></tr>';
  }
  h += '</tbody></table></div><p class="note">Обрезки длиннее нужного куска засчитаны повторно, в «палубе по остаткам» — по рядам.' + (num(S.set.perPack) || num(S.set.packM2) ? '' : ' Впишите, сколько штук или м² в пачке (шаг 2), — посчитаем упаковки.') + '</p></div>';
  const keys = MODEL.units.map(r => r.unit.key);
  const res = MODEL.byKey[UI.target] || MODEL.units[0];
  h += '<div class="sec"><h3>Как укладывать</h3>' + (keys.length > 1 ? '<div class="chips">' + keys.map(k => '<button class="chip" type="button" data-act="res-target" data-key="' + k + '" aria-pressed="' + (res && k === res.unit.key) + '">' + esc(unitName(k)) + '</button>').join('') + '</div>' : '');
  if (!res) { el.innerHTML = h + '<p class="note">Нет участков для укладки.</p></div>'; return; }
  if (res.err) { el.innerHTML = h + '<p class="note bad">' + esc(res.err) + '</p></div>'; return; }
  const st = res.stats;
  h += '<div class="tiles"><div class="tile"><b>' + st.nFull + '</b><span>целых</span></div><div class="tile"><b>' + st.nCut + '</b><span>подрезок' + (st.nBad ? ', узких ' + st.nBad : '') + '</span></div></div>';
  h += '<ol class="steps">' + unitSteps(res).map(s => '<li><span>' + s + '</span></li>').join('') + '</ol></div>';
  if (res.walls && res.walls.length) {
    const thr = num(res.unit.P.minEdge, 25), multi = S.rooms.length > 1;
    h += '<div class="sec"><h3>Что приходит к стенам</h3><div class="tblwrap"><table class="tbl"><thead><tr><th>Стена</th><th>Подрезок</th><th>Глубина куска</th><th>Самый узкий</th></tr></thead><tbody>';
    for (const w of res.walls) {
      const name = (w.label === 'стена' ? '' : 'рамка ') + (w.i + 1) + (multi ? ' ' + roomName(w.rid) : '') + ' · ' + (w.arc ? '⌒' : '') + mm(w.len);
      if (!w.count) { h += '<tr><td class="n">' + esc(name) + '</td><td class="n">0</td><td colspan="2">целые планки</td></tr>'; continue; }
      const bad = w.minT < thr;
      h += '<tr class="' + (bad ? 'bad' : '') + '"><td class="n">' + esc(name) + '</td><td class="n">' + w.count + '</td><td class="n">' + (Math.abs(w.maxD - w.minD) < 1 ? mm(w.minD) : mm(w.minD) + '–' + mm(w.maxD)) + ' мм</td><td class="n">' + mm(w.minT) + ' мм' + (bad ? ' ⚠' : '') + '</td></tr>';
    }
    h += '</tbody></table></div><p class="note">Глубина — насколько кусок заходит от края укладки. «Самый узкий» — ширина самого тонкого куска у этой стены.</p></div>';
  }
  if (res.rows && res.rows.length) {
    const M = res.unit.mat;
    h += '<div class="sec"><h3>Ряды <small>от старта, мм</small></h3><div class="rows">';
    res.rows.forEach((row, ri) => {
      const chips = []; let run = 0; const flush = () => { if (run) { chips.push('<span class="pc">' + mm(M.L) + (run > 1 ? ' × ' + run : '') + '</span>'); run = 0; } };
      row.items.forEach(it => { if (it.full) { run++; return; } flush(); chips.push('<span class="pc ' + (it.bad ? 'bad' : 'cut') + '">' + mm(it.len) + (it.src === 'pool' ? '<sup>обр.</sup>' : '') + '</span>'); });
      flush();
      const cutW = row.width < M.W - 0.5;
      h += '<div class="rowl"><div class="rh">Ряд ' + (ri + 1) + '<small class="' + (cutW ? 'cutw' : '') + '">' + (cutW ? 'шир. ' + mm(row.width) : 'целый') + '</small></div><div class="pcs">' + chips.join('') + '</div></div>';
    });
    h += '</div><p class="note"><span class="pc cut">742</span> — подрезанный кусок, <sup>обр.</sup> — из обрезка прошлых рядов.</p></div>';
  }
  if (res.groups.length && (!res.rows || patDef(res.unit.P.type).group !== 'bond')) {
    const list = res.groups.slice(0, 40), key = res.unit.key;
    h += '<div class="sec"><h3>Подрезки <small>одинаковые можно напилить пачкой</small></h3><div class="groups">' +
      list.map(g => '<button class="grp" type="button" data-act="grp" data-key="' + key + '" data-gk="' + esc(g.key) + '" aria-pressed="' + (!!UI.hl && UI.hl.key === key && UI.hl.gk === g.key) + '"><span class="cnt">×' + g.idx.length + '</span><span class="tx">' + (g.kind === 'A' || g.kind === 'B' ? '<small>планка ' + g.kind + '</small>' : '') + g.lines.map(esc).join('<br>') + '</span></button>').join('') + '</div>' +
      (res.groups.length > list.length ? '<p class="note">Ещё ' + (res.groups.length - list.length) + ' разных подрезок — смотрите на карте.</p>' : '') + '<p class="note">Нажмите на строку — такие куски подсветятся на плане.</p></div>';
  }
  h += '<div class="sec"><h3>Обозначения</h3><div class="legend"><span><i style="background:' + rgb((TONES[res.unit.mat.tone] || TONES.oak).c) + '"></i>целая</span><span><i style="background:' + COL.tape + '"></i>подрезка</span><span><i style="background:' + COL.badSoft + ';border-color:' + COL.bad + '"></i>узкая подрезка</span><span><i style="background:' + COL.chalk + ';height:3px"></i>линия разметки</span><span><i style="background:' + COL.gap + '"></i>зазор у стен</span></div></div>';
  h += '<div class="sec"><h3>Сохранить и отправить</h3><div class="row-btns"><button class="btn" type="button" data-act="export-img">Картинка плана</button><button class="btn" type="button" data-act="export-copy">Скопировать расчёт</button><button class="btn" type="button" data-act="export-file">Файл проекта</button></div></div>';
  el.innerHTML = h;
}
function reportText() {
  if (!MODEL) return '';
  const strip = s => s.replace(/<[^>]+>/g, ''), lines = [S.name || 'Раскладка'], reserve = Math.max(0, num(S.set.reserve));
  for (const r of S.rooms) { const G = MODEL.geo[r.id]; if (G.err) { lines.push(r.name + ': ' + G.err); continue; } lines.push(r.name + ': ' + fm2(Math.abs(area(G.g.poly))) + ' м², стены ' + G.g.corners.map((p, i) => (i + 1) + ') ' + (Math.abs(G.g.arcs[i]) >= 0.5 ? 'дуга ' : '') + mm(dist(p, G.g.corners[(i + 1) % G.g.n]))).join(', ') + ' мм'); }
  lines.push('', 'Покупать:');
  for (const m of MODEL.mats) lines.push('— ' + catById(m.M.cat).name + ' ' + mm(m.M.L) + '×' + mm(m.M.W) + ': ' + m.boards + ' шт, с запасом ' + f1(reserve) + '% — ' + Math.ceil(m.boards * (1 + reserve / 100)) + ' шт');
  for (const res of MODEL.units) {
    lines.push('', '== ' + res.unit.name + ' — ' + patDef(res.unit.P.type).name + ' ==');
    if (res.err) { lines.push(res.err); continue; }
    unitSteps(res).forEach((s, i) => lines.push((i + 1) + '. ' + strip(s)));
    if (res.rows) res.rows.forEach((row, i) => lines.push('Ряд ' + (i + 1) + (row.width < res.unit.mat.W - 0.5 ? ' (шир. ' + mm(row.width) + ')' : '') + ': ' + row.items.map(it => (it.full ? '' : '✂') + mm(it.len)).join(' | ')));
    else res.groups.forEach(g => lines.push('×' + g.idx.length + (g.kind !== 'R' ? ' [' + g.kind + ']' : '') + ' ' + g.lines.join('; ')));
  }
  return lines.join('\n');
}
async function copyReport() {
  const t = reportText();
  try { await navigator.clipboard.writeText(t); say('Расчёт скопирован — вставьте в мессенджер или заметки.', 'ok'); }
  catch (e) { openModal('<header><h2>Расчёт</h2><button class="icon" data-close type="button" aria-label="Закрыть">' + ICON.del + '</button></header><p class="note">Выделите текст и скопируйте.</p><textarea class="code" id="copyArea" readonly>' + esc(t) + '</textarea>'); const ta = $('#copyArea'); ta.focus(); ta.select(); }
}

/* ================= экспорт ================= */
const fileSafe = s => (String(s || 'raskladka').replace(/[\\/:*?"<>|]+/g, ' ').trim().slice(0, 60) || 'raskladka');
async function saveFile(name, data, mime) {
  const dl = await capUse('downloads');
  if (dl) { try { await dl.save({ filename: name, data }); return 'saved'; } catch (e) { if (e && e.code === 'declined') return 'declined'; } }
  let top = false; try { top = window.top === window.self; } catch (e) { top = false; }
  if (top && !window.claude) {
    try { const blob = data instanceof Blob ? data : new Blob([data], { type: mime }); const url = URL.createObjectURL(blob); const a = document.createElement('a'); a.href = url; a.download = name; document.body.appendChild(a); a.click(); a.remove(); setTimeout(() => URL.revokeObjectURL(url), 5000); return 'saved'; } catch (e) { /* ниже — окно */ }
  }
  return 'fallback';
}
async function exportImage() {
  if (!MODEL) return; const b = floorBBox(); if (!b) return;
  const K = 2, W = 1000, head = 92, foot = 40, pad = 56, s = (W - 2 * pad) / Math.max(1, b.u1 - b.u0), H = Math.round(head + foot + 2 * pad + (b.v1 - b.v0) * s);
  const c = document.createElement('canvas'); c.width = W * K; c.height = H * K; const ctx = c.getContext('2d');
  render(ctx, W, H, { s, cx: (b.u0 + b.u1) / 2, cy: (b.v0 + b.v1) / 2 - (head - foot) / 2 / s }, { k: K, style: UI.style, labels: true, live: false });
  ctx.setTransform(K, 0, 0, K, 0, 0); ctx.fillStyle = COL.panel; ctx.fillRect(0, 0, W, head - 16);
  ctx.fillStyle = COL.ink; ctx.textAlign = 'left'; ctx.textBaseline = 'alphabetic'; ctx.font = '700 20px ' + COL.body; ctx.fillText(S.name || 'Раскладка', 24, 32);
  ctx.font = '500 13px ' + COL.body; ctx.fillStyle = COL.muted;
  ctx.fillText(MODEL.units.filter(r => !r.err).map(r => r.unit.name + ' — ' + patDef(r.unit.P.type).name + ' ' + mm(r.unit.mat.L) + '×' + mm(r.unit.mat.W)).join(' · ').slice(0, 150), 24, 54);
  ctx.fillText(MODEL.mats.map(m => mm(m.M.L) + '×' + mm(m.M.W) + ': ' + m.boards + ' шт').join(' · ') + ' · зазор ' + mm(num(S.set.gap)) + ' мм', 24, 72);
  ctx.font = '500 11px ' + COL.body; ctx.fillText('Жёлтым — подрезки, красным — узкие куски, синим — линия разметки. Размеры в мм.', 24, H - 14);
  const blob = await new Promise(res => c.toBlob(res, 'image/png'));
  const r = blob ? await saveFile(fileSafe(S.name) + '.png', blob, 'image/png') : 'fallback';
  if (r === 'saved') { say('Картинка сохранена.', 'ok'); return; } if (r === 'declined') return;
  openModal('<header><h2>Картинка плана</h2><button class="icon" data-close type="button" aria-label="Закрыть">' + ICON.del + '</button></header><p class="note">Нажмите и удерживайте картинку (на компьютере — правая кнопка мыши), чтобы сохранить или отправить.</p><img alt="План раскладки" src="' + c.toDataURL('image/png') + '">');
}
function projData() { return { app: 'raskladka', v: 2, name: S.name, mat: S.mat, set: S.set, rooms: S.rooms, floorPat: S.floorPat }; }
async function exportProject() {
  const json = JSON.stringify(projData(), null, 1), r = await saveFile(fileSafe(S.name) + '.json', json, 'application/json');
  if (r === 'saved') { say('Файл проекта сохранён. Открыть: «Проекты» → «Открыть файл».', 'ok'); return; } if (r === 'declined') return;
  openModal('<header><h2>Файл проекта</h2><button class="icon" data-close type="button" aria-label="Закрыть">' + ICON.del + '</button></header><p class="note">Скопируйте текст и сохраните. Загрузить обратно: «Проекты» → «Вставить текст».</p><textarea class="code" id="copyArea" readonly>' + esc(json) + '</textarea>');
  $('#copyArea').select();
}

/* ================= хранилище проектов ================= */
const Store = {
  db: null, uid: null, cloud: [], mats: [],
  localList() { try { return JSON.parse(lsGet(KEY_PROJ) || '[]') || []; } catch (e) { return []; } },
  setLocal(list) { return lsSet(KEY_PROJ, JSON.stringify(list)); },
  col() { return this.db.collection('data/users/' + this.uid); },
  list() { return [...this.cloud.map(p => Object.assign({ where: 'cloud' }, p)), ...this.localList().map(p => Object.assign({ where: 'local' }, p))].sort((a, b) => (b.updated || 0) - (a.updated || 0)); },
  async save(p) {
    if (this.db) { try { await this.col().doc(p.id).set({ name: p.name, updated: p.updated, data: JSON.stringify(p.data) }); this.setLocal(this.localList().filter(x => x.id !== p.id)); return 'cloud'; } catch (e) { this.db = null; } }
    const l = this.localList().filter(x => x.id !== p.id); l.push(p); return this.setLocal(l) ? 'local' : 'fail';
  },
  async remove(p) { if (p.where === 'cloud' && this.db) { try { await this.col().doc(p.id).delete(); } catch (e) { say('Не удалось удалить: нет связи с аккаунтом.', 'bad'); } } else this.setLocal(this.localList().filter(x => x.id !== p.id)); },
  loadMats() { try { this.mats = JSON.parse(lsGet(KEY_MATS) || '[]') || []; } catch (e) { this.mats = []; } },
  async saveMats(list) { this.mats = list; lsSet(KEY_MATS, JSON.stringify(list)); if (this.db) { try { await this.col().doc('mats').set({ items: JSON.stringify(list) }); } catch (e) { /* остаются в браузере */ } } },
  async init() {
    this.loadMats();
    const [db, user] = await Promise.all([capUse('db'), capUse('user')]); if (!db || !user) return;
    let id = null; try { id = await user.id(); } catch (e) { id = null; } if (!id) return;
    this.db = db; this.uid = id;
    try {
      this.col().onSnapshot(snap => {
        this.cloud = snap.docs.filter(d => d.id.startsWith('p_')).map(d => { const x = d.data() || {}; let data = null; try { data = JSON.parse(x.data || 'null'); } catch (e) { data = null; } return { id: d.id, name: x.name || 'Без названия', updated: x.updated || 0, data }; }).filter(p => p.data);
        const md = snap.docs.find(d => d.id === 'mats');
        if (md) { try { const cm = JSON.parse((md.data() || {}).items || '[]'), ids = new Set(cm.map(m => m.id)); this.mats = cm.concat(this.mats.filter(m => !ids.has(m.id))); lsSet(KEY_MATS, JSON.stringify(this.mats)); if (UI.catView === 'custom' && UI.tab === 'mat') renderSizes(); } catch (e) { /* пропускаем */ } }
        if (!$('#modal').hidden && $('#modal').dataset.kind === 'projects') openProjects();
      }, () => { this.db = null; });
    } catch (e) { this.db = null; }
  },
};
const pidNew = () => 'p_' + Date.now().toString(36) + Math.random().toString(36).slice(2, 7);
async function saveProject(asNew) {
  if (asNew || !S.pid) S.pid = pidNew();
  const where = await Store.save({ id: S.pid, name: S.name || 'Без названия', updated: Date.now(), data: projData() });
  lsSet(KEY_DRAFT, JSON.stringify(S));
  say(where === 'cloud' ? 'Проект сохранён в вашем аккаунте — откроется и на другом устройстве.' : where === 'local' ? 'Проект сохранён в этом браузере.' : 'Не удалось сохранить: память браузера недоступна. Сохраните файл проекта.', where === 'fail' ? 'bad' : 'ok');
  if (!$('#modal').hidden && $('#modal').dataset.kind === 'projects') openProjects();
}
function loadProject(data, pid) {
  S = migrateState(data); S.pid = pid || null;
  UI.sel = null; UI.hl = null; UI.variants = null; UI.room = S.rooms[0].id; UI.target = 'floor'; UI.matTarget = 'main'; UI.catView = S.mat.cat || 'laminate';
  view.fitted = false; recomputeNow(); fitView(); syncAll(); invalidate({ fast: true });
}
function openProjects() {
  const list = Store.list();
  const rows = list.map(p => {
    let a = ''; try { const st = migrateState(p.data); let tot = 0; for (const r of st.rooms) { const g = roomGeom(r); if (g.poly.length >= 3) tot += Math.abs(area(g.poly)); } a = fm2(tot) + ' м²'; } catch (e) { a = ''; }
    const d = p.updated ? new Date(p.updated).toLocaleDateString('ru-RU', { day: 'numeric', month: 'short' }) : '';
    return '<div class="pitem"><div style="min-width:0"><b>' + esc(p.name) + '</b><small>' + [a, d, p.where === 'cloud' ? 'в аккаунте' : 'в этом браузере'].filter(Boolean).join(' · ') + '</small></div><div class="acts"><button class="btn small" data-open="' + p.id + '" type="button">Открыть</button><button class="btn small danger" data-del="' + p.id + '" type="button">' + (UI.delArm === p.id ? 'Точно?' : 'Удалить') + '</button></div></div>';
  }).join('');
  openModal('<header><h2>Проекты</h2><button class="icon" data-close type="button" aria-label="Закрыть">' + ICON.del + '</button></header>' +
    '<p class="note">' + (Store.db ? 'Проекты хранятся в вашем аккаунте и видны только вам.' : 'Проекты хранятся в этом браузере. Чтобы перенести на другое устройство, сохраните файл проекта.') + '</p>' +
    '<div class="row-btns"><button class="btn primary" data-pact="save" type="button">Сохранить текущий</button><button class="btn" data-pact="saveas" type="button">Сохранить как новый</button><button class="btn" data-pact="new" type="button">Новый проект</button></div>' +
    '<div class="plist">' + (rows || '<p class="note">Сохранённых проектов пока нет.</p>') + '</div>' +
    '<div class="row-btns"><label class="btn" for="fileIn">Открыть файл</label><input type="file" id="fileIn" accept=".json,application/json" hidden><button class="btn" data-pact="paste" type="button">Вставить текст</button><button class="btn" data-pact="export" type="button">Файл текущего</button></div>', 'projects');
  $('#fileIn').addEventListener('change', e => { const f = e.target.files && e.target.files[0]; if (!f) return; const rd = new FileReader(); rd.onload = () => importText(String(rd.result)); rd.readAsText(f); });
}
function importText(t) {
  try { const d = JSON.parse(t); if (!d || !(d.rooms || d.room)) throw new Error('bad'); loadProject(d, null); closeModal(); say('Проект «' + (d.name || 'без названия') + '» открыт.', 'ok'); }
  catch (e) { say('Это не файл проекта раскладки. Проверьте текст.', 'bad'); }
}
$('#modal').addEventListener('click', async e => {
  if (e.target === $('#modal') || e.target.closest('[data-close]')) { closeModal(); return; }
  const o = e.target.closest('[data-open]'); if (o) { const p = Store.list().find(x => x.id === o.dataset.open); if (p) { loadProject(p.data, p.id); closeModal(); say('Открыт проект «' + p.name + '».', 'ok'); } return; }
  const d = e.target.closest('[data-del]');
  if (d) { if (UI.delArm === d.dataset.del) { const p = Store.list().find(x => x.id === d.dataset.del); UI.delArm = null; if (p) { await Store.remove(p); if (S.pid === p.id) S.pid = null; say('Проект удалён.'); } } else UI.delArm = d.dataset.del; openProjects(); return; }
  const a = e.target.closest('[data-pact]'); if (!a) return;
  const act = a.dataset.pact;
  if (act === 'save') saveProject(false); else if (act === 'saveas') saveProject(true);
  else if (act === 'new') { const st = defaultState(); st.name = 'Новый этаж'; st.rooms = [Object.assign(newRoom('Комната 1', rectWalls(4200, 3600)), { id: 'r1' })]; st.floorPat = Object.assign(defaultPat('remnant'), { refRoom: 'r1' }); st.mat = { cat: 'laminate', item: 'laminate:0', L: 1380, W: 193, T: 8, shape: 'plank', joint: 0, tone: 'oak' }; loadProject(st, null); closeModal(); setTab('plan'); say('Новый проект: впишите размеры комнаты.'); }
  else if (act === 'export') exportProject();
  else if (act === 'paste') openModal('<header><h2>Вставить проект</h2><button class="icon" data-close type="button" aria-label="Закрыть">' + ICON.del + '</button></header><textarea class="code" id="pasteArea" placeholder="Вставьте сюда текст файла проекта"></textarea><button class="btn primary" data-pact="doPaste" type="button">Открыть</button>');
  else if (act === 'doPaste') importText($('#pasteArea').value);
});
function openModal(html, kind) { const m = $('#modal'); $('#modalBox').innerHTML = html; m.dataset.kind = kind || ''; m.hidden = false; }
function closeModal() { $('#modal').hidden = true; $('#modal').dataset.kind = ''; UI.delArm = null; }
document.addEventListener('keydown', e => { if (e.key === 'Escape' && !$('#modal').hidden) closeModal(); });

/* ================= верх, режимы, разделитель ================= */
$('#btnProjects').addEventListener('click', openProjects);
$('#btnSave').addEventListener('click', () => saveProject(false));
$$('[data-mode]').forEach(b => b.addEventListener('click', () => { UI.mode = b.dataset.mode; syncToolbar(); modeHint(); draw(); saveUI(); }));
$('#btnFit').addEventListener('click', () => { fitView(); draw(); });
$('#btnLabels').addEventListener('click', () => { UI.labels = !UI.labels; syncToolbar(); draw(); saveUI(); });
$('#btnStyle').addEventListener('click', () => { UI.style = UI.style === 'scheme' ? 'wood' : 'scheme'; syncToolbar(); draw(); saveUI(); });
$('#btnImage').addEventListener('click', exportImage);
function syncToolbar() {
  $$('[data-mode]').forEach(b => b.setAttribute('aria-pressed', String(b.dataset.mode === UI.mode)));
  $('#btnLabels').setAttribute('aria-pressed', String(UI.labels)); $('#btnStyle').setAttribute('aria-pressed', String(UI.style === 'scheme'));
  cv.className = 'm-' + UI.mode; $('#nudge').hidden = UI.mode !== 'pattern'; syncStep();
  if (UI.mode === 'pattern') $('#nudgeTarget').textContent = unitName(UI.target).toLowerCase();
}
const work = $('#work'), mapcol = $('#mapcol'), splitter = $('#splitter');
const isNarrow = () => window.matchMedia('(max-width:900px)').matches;
function setMapH(h) { const total = work.clientHeight; if (!total) return; h = clamp(h, 170, Math.max(170, total - 150)); UI.mapH = h / total; work.style.setProperty('--mapH', Math.round(h) + 'px'); }
function applyMapH() { if (!isNarrow()) return; setMapH((UI.mapH || 0.52) * work.clientHeight); }
let spl = null;
splitter.addEventListener('pointerdown', e => { spl = { y: e.clientY, h: mapcol.getBoundingClientRect().height }; splitter.setPointerCapture(e.pointerId); });
splitter.addEventListener('pointermove', e => { if (spl) setMapH(spl.h + (e.clientY - spl.y)); });
const splEnd = () => { if (spl) { spl = null; saveUI(); } };
splitter.addEventListener('pointerup', splEnd); splitter.addEventListener('pointercancel', splEnd);
splitter.addEventListener('keydown', e => { if (e.key === 'ArrowUp' || e.key === 'ArrowDown') { e.preventDefault(); setMapH(mapcol.getBoundingClientRect().height + (e.key === 'ArrowDown' ? 30 : -30)); saveUI(); } });
splitter.addEventListener('dblclick', () => { setMapH(UI.mapH > 0.6 ? 0.52 * work.clientHeight : 0.74 * work.clientHeight); saveUI(); });
function saveUI() { lsSet(KEY_UI, JSON.stringify({ tab: UI.tab, mode: UI.mode, style: UI.style, labels: UI.labels, step: UI.step, help: UI.help, mapH: UI.mapH, room: UI.room })); }
function loadUI() { try { const u = JSON.parse(lsGet(KEY_UI) || 'null'); if (u) Object.assign(UI, { tab: u.tab || 'plan', mode: u.mode || 'view', style: u.style || 'wood', labels: u.labels !== false, step: u.step || 10, help: u.help !== false, mapH: u.mapH || null, room: u.room || UI.room }); } catch (e) { /* по умолчанию */ } }
function syncAll() { syncInputs(); renderPlanTab(); syncToolbar(); renderTplChips(); if (UI.tab === 'mat') renderMatTab(); if (UI.tab === 'pat') renderPatTab(); if (UI.tab === 'res') renderResults(); renderStatus(); renderPieceInfo(); }
function measureTabs() { const t = $('#tabs'); if (t) document.documentElement.style.setProperty('--tabsH', t.offsetHeight + 'px'); }

/* ================= старт ================= */
function start() {
  readColors(); loadUI();
  const draft = lsGet(KEY_DRAFT);
  if (draft) { try { S = migrateState(JSON.parse(draft)); } catch (e) { S = defaultState(); } }
  else { S = defaultState(); }
  UI.catView = S.mat.cat || 'eng';
  recomputeNow();
  setTab(UI.tab); syncAll(); modeHint();
  new ResizeObserver(() => { applyMapH(); resizeCanvas(); measureTabs(); }).observe(work);
  new ResizeObserver(() => resizeCanvas()).observe(cv);
  applyMapH(); resizeCanvas(); measureTabs();
  const mq = window.matchMedia('(prefers-color-scheme: dark)'), retheme = () => { readColors(); draw(); if (UI.tab === 'pat') renderPatList(); };
  if (mq.addEventListener) mq.addEventListener('change', retheme);
  new MutationObserver(retheme).observe(document.documentElement, { attributes: true, attributeFilter: ['data-theme'] });
  if (document.fonts && document.fonts.ready) document.fonts.ready.then(() => { readColors(); draw(); });
  Store.init();
  try { if ('serviceWorker' in navigator && location.protocol === 'https:' && window.top === window.self && !window.claude) navigator.serviceWorker.register('sw.js').catch(() => {}); } catch (e) { /* без офлайна */ }
}
start();
})();
