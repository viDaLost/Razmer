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
// ниши (наружу) и выступы (внутрь), в том числе в углах
{
  const mk = niches => { const r = Object.assign(E.newRoom('N', E.rectWalls(4000, 3000)), { id: 'r1' }); r.niches = niches; return r; };
  const A0 = 4000 * 3000;
  const cases = [
    ['niche mid', [{ id: 'n1', kind: 'niche', wall: 0, pos: 1000, width: 1200, depth: 150 }], A0 + 1200 * 150],
    ['niche corner', [{ id: 'n1', kind: 'niche', wall: 2, pos: 0, width: 900, depth: 600 }], A0 + 900 * 600],
    ['niche no floor', [{ id: 'n1', kind: 'niche', wall: 1, pos: 500, width: 1500, depth: 600, floor: false }], A0],
    ['box mid', [{ id: 'n1', kind: 'box', wall: 3, pos: 800, width: 400, depth: 300 }], A0 - 400 * 300],
    ['box start corner', [{ id: 'n1', kind: 'box', wall: 0, pos: 0, width: 400, depth: 300 }], A0 - 400 * 300],
    ['box end corner', [{ id: 'n1', kind: 'box', wall: 1, pos: 2600, width: 400, depth: 350 }], A0 - 400 * 350],
    ['boxes two corners', [{ id: 'n1', kind: 'box', wall: 0, pos: 3600, width: 400, depth: 300 }, { id: 'n2', kind: 'box', wall: 2, pos: 0, width: 500, depth: 250 }, { id: 'n3', kind: 'niche', wall: 3, pos: 1000, width: 1000, depth: 120 }], A0 - 400 * 300 - 500 * 250 + 1000 * 120],
  ];
  for (const [label, niches, expA] of cases) {
    const room = mk(niches), g = E.roomGeom(room);
    ok(Math.abs(Math.abs(E.area(g.poly)) - expA) < 1, 'geom ' + label, Math.abs(E.area(g.poly)) + ' vs ' + expA);
    for (const pid of ['remnant', 'herring1', 'chevron', 'basket']) {
      const S = JSON.parse(JSON.stringify(base)); S.set.gap = 10; S.rooms = [room];
      const m = pid === 'basket' ? [280, 70] : pid === 'remnant' ? [1380, 193] : [600, 120]; S.mat.L = m[0]; S.mat.W = m[1];
      Object.assign(S.floorPat, E.defaultPat(pid), { refRoom: 'r1', offA: 11, offB: 23 });
      checkState('niche ' + label + ' ' + pid, S, 3e-4);
    }
    // рамка вдоль стен с нишами и выступами
    const S = JSON.parse(JSON.stringify(base)); S.set.gap = 10; S.rooms = [mk(niches)];
    S.mat.L = 600; S.mat.W = 120; Object.assign(S.floorPat, E.defaultPat('herring1'), { refRoom: 'r1' });
    S.rooms[0].border.on = true; S.rooms[0].border.rows = 2; S.rooms[0].border.pat.type = 'bond2'; S.rooms[0].border.mat = { L: 1380, W: 193, shape: 'plank', joint: 0 };
    const { geo } = checkState('niche+border ' + label, S, 5e-4);
    ok(!geo.r1.borderErr, 'niche+border fits ' + label, geo.r1.borderErr);
  }
  // направление рисунка от стены с выступом в углу не сбивается
  const r = mk([{ id: 'n1', kind: 'box', wall: 0, pos: 0, width: 400, depth: 300 }]), S = JSON.parse(JSON.stringify(base)); S.rooms = [r];
  const geo = E.computeGeo(S), F = E.frameFor(geo.r1, Object.assign(E.defaultPat('bond2'), { refWall: 0 }));
  ok(Math.abs(F.eu[1]) < 1e-9 && Math.abs(F.A[0]) < 1e-6 && Math.abs(F.A[1]) < 1e-6, 'corner box keeps frame', JSON.stringify([F.eu, F.A]));
}
// стыки комнат: стена одной комнаты против стены другой через перегородку
{
  const S = E.defaultState(); let geo = E.computeGeo(S), adj = E.adjacency(S, geo);
  ok(adj.length === 2 && adj.some(a => a.a === 'r1' && a.i === 1 && Math.abs(a.o1 - a.o0 - 3850) < 1), 'adjacency default', JSON.stringify(adj));
  S.rooms[1].walls = E.rectWalls(3600, 2000); S.rooms[1].y0 = 1000; geo = E.computeGeo(S); adj = E.adjacency(S, geo);
  const a = adj.find(x => x.a === 'r1');
  ok(a && Math.abs(a.o0 - 1000) < 1 && Math.abs(a.o1 - 3000) < 1, 'adjacency partial', JSON.stringify(a));
  S.rooms[1].x0 = 5600; geo = E.computeGeo(S); ok(E.adjacency(S, geo).length === 0, 'adjacency apart');
  // комната, обойдённая в другую сторону, тоже находится
  S.rooms[1] = Object.assign(S.rooms[1], { x0: 5320, y0: 3850, a0: 0, walls: [{ len: 3600, turn: 0 }, { len: 3850, turn: -90 }, { len: 3600, turn: -90 }, { len: 3850, turn: -90 }] });
  geo = E.computeGeo(S); ok(!geo.r2.err && E.adjacency(S, geo).length === 2, 'adjacency ccw room', JSON.stringify(E.adjacency(S, geo).map(x => [x.a, x.i, x.o0, x.o1])));
}
// старые проекты без ниш открываются, ниши сохраняются
{
  const S = E.migrateState({ v: 2, rooms: [{ id: 'a', walls: E.rectWalls(3000, 3000), niches: [{ kind: 'box', wall: 1, pos: 100, width: 300, depth: 200 }], doors: [{ wall: 0, pos: 100, width: 900, auto: true, to: 'b', full: true }] }], noDoor: ['a|b'] });
  ok(S.rooms[0].niches.length === 1 && S.rooms[0].niches[0].kind === 'box' && S.rooms[0].doors[0].auto && S.rooms[0].doors[0].full && S.noDoor[0] === 'a|b', 'migrate niches/doors');
}
console.log('checks', total, 'failed', fails);
process.exit(fails ? 1 : 0);
