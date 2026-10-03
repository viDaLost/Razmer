/* Платформа: Telegram Mini App и ярлык на экране телефона.
   Библиотеку Telegram грузим только когда страницу открыл Telegram (в адресе есть tgWebApp…),
   поэтому в обычном браузере и без интернета ничего лишнего не загружается. */
(function (root) {
'use strict';
const ua = navigator.userAgent || '';
const P = {
  inTG: false,
  tg: null,
  ios: /iP(hone|ad|od)/.test(ua) || (navigator.platform === 'MacIntel' && navigator.maxTouchPoints > 1),
  android: /Android/i.test(ua),
  standalone: navigator.standalone === true || (root.matchMedia && root.matchMedia('(display-mode: standalone)').matches),
  ready: null,
};
const hint = /tgWebApp/i.test(location.hash) || /tgWebApp/i.test(location.search) || !!root.TelegramWebviewProxy;
function setup() {
  const tg = root.Telegram && root.Telegram.WebApp; if (!tg) return;
  P.tg = tg;
  P.inTG = !!(tg.initData || (tg.platform && tg.platform !== 'unknown'));
  if (!P.inTG) return;
  document.documentElement.classList.add('tg');
  try { tg.ready(); } catch (e) { /* старый клиент */ }
  try { tg.expand(); } catch (e) { /* старый клиент */ }
  // свайп вниз закрывает мини-приложение — мешает двигать карту пальцем
  try { if (P.version('7.7')) tg.disableVerticalSwipes(); } catch (e) { /* старый клиент */ }
}
P.version = v => { try { return !!(P.tg && P.tg.isVersionAtLeast && P.tg.isVersionAtLeast(v)); } catch (e) { return false; } };
P.ready = new Promise(resolve => {
  if (root.Telegram && root.Telegram.WebApp) { setup(); resolve(P); return; }
  if (!hint) { resolve(P); return; }
  const s = document.createElement('script');
  s.src = 'https://telegram.org/js/telegram-web-app.js';
  s.onload = () => { setup(); resolve(P); };
  s.onerror = () => resolve(P);
  document.head.appendChild(s);
  setTimeout(() => resolve(P), 5000);
});
/* лёгкая вибрация в Telegram: select — щелчок при прилипании, ok/warn — итог действия */
P.haptic = kind => {
  try {
    if (!P.inTG || !P.version('6.1')) return; const h = P.tg.HapticFeedback; if (!h) return;
    if (kind === 'select') h.selectionChanged(); else if (kind === 'ok') h.notificationOccurred('success'); else if (kind === 'warn') h.notificationOccurred('warning'); else h.impactOccurred(kind || 'light');
  } catch (e) { /* без вибрации */ }
};
root.RazmerPlatform = P;
})(window);
