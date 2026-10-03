/* Проверки ядра раскладки: рисунок покрывает пол без щелей и нахлёстов. Запуск: node scripts/engine-test.cjs */
const E = require('../js/engine.js');
let fails = 0, total = 0;
const ok = (cond, label, extra) => { total++; if (!cond) { fails++; console.log('FAIL', label, extra || ''); } };
const areaPieces = res => res.pieces.reduce((s, p) => s + p.area, 0);
const regionArea = u => u.parts.reduce((s, part) => s + part.regions.reduce((t, r) => t + Math.abs(E.area(r.poly)), 0), 0);

function checkState(label, S, tolRel) {
  const geo = E.computeGeo(S);
  for (const r of S.rooms) ok(!geo[r.id].err, label + ' room ' + r.name, geo[r.id].err);
  const keys = E.unitKeys(S, geo);
  let covered = 0, expect = 0;
  for (const key of keys) {
    const u = E.buildUnit(key, S, geo); if (!u) continue;
    const res = E.computeUnit(u, true);
    ok(!res.err, label + ' ' + key, res.err);
    if (res.err) continue;
    const ra = regionArea(u), sub = u.parts.reduce((s, part) => s + part.subtract.reduce((t, rc) => t + part.regions.reduce((q, rg) => q + Math.abs(E.area(E.clipBy(rg.poly, rc))), 0), 0), 0);
    const pa = areaPieces(res), rel = (pa - (ra - sub)) / ra;
    ok(Math.abs(rel) < tolRel, label + ' ' + key + ' area', 'rel=' + rel.toExponential(2));
    covered += pa;
  }
  // весь пол: сумма всех участков = площадь укладки комнат + проёмы
  for (const r of S.rooms) { const G = geo[r.id]; if (G.err) continue; expect += Math.abs(E.area(G.lay)); for (const d of G.doors) expect += Math.abs(E.area(d.poly)); }
  const rel = (covered - expect) / expect;
  ok(Math.abs(rel) < tolRel, label + ' whole floor', 'rel=' + rel.toExponential(2));
  return { geo, keys };
}

const base = E.defaultState();
base.set.gap = 0; // без допуска на зазор: проверяем точное покрытие
for (const pt of E.PATTERNS) {
  for (const dir of ['along', 'diag', 'custom']) {
    const S = JSON.parse(JSON.stringify(base));
    const m = pt.group === 'basket' ? [280, 70] : pt.group === 'bond' ? [1380, 193] : [600, 120];
    S.mat.L = m[0]; S.mat.W = m[1];
    Object.assign(S.floorPat, E.defaultPat(pt.id), { refRoom: 'r1', dir, angle: 17, offA: 37, offB: 91, minPiece: 300, minStag: 300 });
    checkState('2 rooms ' + pt.id + ' ' + dir, S, 2e-4);
  }
}
// комнаты сложной формы, включая дуги
for (const t of E.TEMPLATES) {
  for (const pid of ['remnant', 'bond3', 'herring1', 'chevron', 'basket']) {
    const S = JSON.parse(JSON.stringify(base));
    S.rooms = [Object.assign(E.newRoom(t.name, t.make()), { id: 'r1' })];
    const m = pid === 'basket' ? [280, 70] : pid === 'remnant' || pid === 'bond3' ? [1380, 193] : [600, 120];
    S.mat.L = m[0]; S.mat.W = m[1];
    Object.assign(S.floorPat, E.defaultPat(pid), { refRoom: 'r1', offA: 13, offB: 29 });
    checkState(t.id + ' ' + pid, S, 2e-4);
  }
}
// рамка вдоль стен + вставка + свой рисунок
for (const t of ['rect', 'L', 'arcwall', 'bevel']) {
  const S = JSON.parse(JSON.stringify(base));
  const tpl = E.TEMPLATES.find(x => x.id === t);
  S.rooms = [Object.assign(E.newRoom('A', tpl.make()), { id: 'r1' })];
  S.mat.L = 420; S.mat.W = 70;
  Object.assign(S.floorPat, E.defaultPat('basket'), { refRoom: 'r1' });
  S.rooms[0].border.on = true; S.rooms[0].border.rows = 3; S.rooms[0].border.pat.type = 'remnant';
  S.rooms[0].border.mat = { L: 1380, W: 193, shape: 'plank', joint: 0, tone: 'walnut' };
  S.rooms[0].inserts.push({ id: 'i1', w: 1200, h: 900, dx: 150, dy: -100, rot: 0, pat: E.defaultPat('herring1'), mat: { L: 600, W: 120, shape: 'plank', joint: 0, tone: 'oak' } });
  checkState('composite ' + t, S, 3e-4);
  S.rooms[0].own = true; S.rooms[0].pat = E.defaultPat('chevron'); S.rooms[0].mat = { L: 600, W: 120, shape: 'chevron', joint: 0 };
  checkState('composite own ' + t, S, 3e-4);
}
// сквозной рисунок: планка, проходящая через проём, считается одной
{
  const S = JSON.parse(JSON.stringify(base));
  S.mat.L = 1380; S.mat.W = 193; Object.assign(S.floorPat, E.defaultPat('bond2'), { refRoom: 'r1', dir: 'along' });
  S.rooms[0].doors[0].width = 1500;
  const geo = E.computeGeo(S), u = E.buildUnit('floor', S, geo), res = E.computeUnit(u, true);
  const multi = res.pieces.filter(p => p.parts.length > 1).length;
  ok(multi > 0, 'door continuity: pieces span rooms', multi);
}
// старое сохранение (одна комната) открывается
{
  const old = { name: 'Старый', room: { x0: 0, y0: 0, a0: 0, walls: [{ len: 4000, turn: 0 }, { len: 3000, turn: 90 }, { len: 4000, turn: 90 }, { len: 3000, turn: 90 }] }, mat: { L: 1380, W: 193 }, set: { gap: 10, tone: 'oak' }, pat: { type: 'bond2' } };
  const S = E.migrateState(old);
  ok(S.v === 2 && S.rooms.length === 1 && S.floorPat.type === 'bond2' && S.mat.tone === 'oak', 'migrate v1');
}
console.log('checks', total, 'failed', fails);
process.exit(fails ? 1 : 0);
