/* Проверка, что все файлы, на которые ссылается сайт, существуют. Запуск: node scripts/check-site.cjs */
const fs = require('fs');
const path = require('path');
const root = path.join(__dirname, '..');
let fails = 0;
const must = f => { if (!fs.existsSync(path.join(root, f))) { console.log('Нет файла:', f); fails++; } };
const html = fs.readFileSync(path.join(root, 'index.html'), 'utf8');
for (const m of html.matchAll(/(?:src|href)="([^"#:]+)"/g)) must(m[1]);
const manifest = JSON.parse(fs.readFileSync(path.join(root, 'manifest.webmanifest'), 'utf8'));
for (const icon of manifest.icons) must(icon.src);
const sw = fs.readFileSync(path.join(root, 'sw.js'), 'utf8');
for (const m of sw.match(/const SHELL = \[([^\]]+)\]/)[1].matchAll(/'([^']+)'/g)) if (m[1] !== './') must(m[1]);
if (!/<title>[^<]+<\/title>/.test(html)) { console.log('Нет <title>'); fails++; }
console.log(fails ? 'Ошибок: ' + fails : 'Все файлы на месте');
process.exit(fails ? 1 : 0);
