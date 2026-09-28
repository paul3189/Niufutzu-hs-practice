/* ══════════════════════════════════════════════════════════════
   g11a-ch01 三角函數・分級練習本　題目產生器
   ─────────────────────────────────────────────────────────────
   每個產生器：function (rng) → { q, a, h, p }
     q：題目（HTML，可含 KaTeX $…$）　a：答案　h：一行提示
     p：產生這題用的參數（給 Node／sympy 獨立驗算用）
   所有答案都用「精確算術」（分數、根式、π 的有理倍）算出。
   角度一律用「弧度 = k·π/12」或「度 = 15° 的倍數」這類可精確求值的角。
   同時可在瀏覽器（window.PGEN）與 Node（module.exports）使用。
   ══════════════════════════════════════════════════════════════ */
(function (root, factory) {
  if (typeof module === 'object' && module.exports) module.exports = factory();
  else root.PGEN = factory();
}(typeof self !== 'undefined' ? self : this, function () {
  'use strict';

  /* ────────── 亂數 ────────── */
  function makeRng(seed) {
    var s = (seed === undefined) ? (Date.now() % 2147483647) : (seed % 2147483647);
    if (s <= 0) s += 2147483646;
    var r = function () { s = (s * 16807) % 2147483647; return (s - 1) / 2147483646; };
    r.int = function (lo, hi) { return lo + Math.floor(r() * (hi - lo + 1)); };
    r.pick = function (arr) { return arr[Math.floor(r() * arr.length)]; };
    r.sign = function () { return r() < 0.5 ? -1 : 1; };
    r.shuffle = function (arr) { var a = arr.slice(); for (var i = a.length - 1; i > 0; i--) { var j = Math.floor(r() * (i + 1)), t = a[i]; a[i] = a[j]; a[j] = t; } return a; };
    return r;
  }

  /* ────────── 整數／分數／根式 ────────── */
  function gcd(a, b) { a = Math.abs(a); b = Math.abs(b); while (b) { var t = a % b; a = b; b = t; } return a; }
  function simpSqrt(n) { var c = 1, r = n; for (var k = 2; k * k <= r; k++) { while (r % (k * k) === 0) { r /= k * k; c *= k; } } return { c: c, r: r }; }
  function F(n, d) { if (d === undefined) d = 1; if (d < 0) { n = -n; d = -d; } var g = gcd(n, d) || 1; return { n: n / g, d: d / g }; }
  var Fr = {
    add: function (x, y) { return F(x.n * y.d + y.n * x.d, x.d * y.d); },
    sub: function (x, y) { return F(x.n * y.d - y.n * x.d, x.d * y.d); },
    mul: function (x, y) { return F(x.n * y.n, x.d * y.d); },
    div: function (x, y) { return F(x.n * y.d, x.d * y.n); },
    neg: function (x) { return F(-x.n, x.d); },
    eq: function (x, y) { return x.n * y.d === y.n * x.d; },
    toNum: function (x) { return x.n / x.d; },
    tex: function (x, big) {
      if (x.d === 1) return String(x.n);
      var f = big === false ? '\\frac' : '\\dfrac';
      return (x.n < 0 ? '-' : '') + f + '{' + Math.abs(x.n) + '}{' + x.d + '}';
    }
  };
  function sqrtTex(n) { var s = simpSqrt(n); if (s.r === 1) return String(s.c); return (s.c === 1 ? '' : s.c) + '\\sqrt{' + s.r + '}'; }
  /* 「c·√r / d」型的精確值（r=1 就是分數）→ LaTeX；sign 隨 c */
  function surdOver(c, r, d) {
    if (c === 0) return '0';
    var s = simpSqrt(r); c *= s.c; r = s.r;
    var g = gcd(Math.abs(c), d); c /= g; d /= g;
    var num = (r === 1) ? String(Math.abs(c)) : ((Math.abs(c) === 1 ? '' : Math.abs(c)) + '\\sqrt{' + r + '}');
    var body = d === 1 ? num : '\\dfrac{' + num + '}{' + d + '}';
    return (c < 0 ? '-' : '') + body;
  }
  /* (a + b√r)/d */
  function surdFracTex(a, b, r, d) {
    var g = gcd(gcd(Math.abs(a), Math.abs(b)), Math.abs(d)) || 1; a /= g; b /= g; d /= g;
    if (d < 0) { a = -a; b = -b; d = -d; }
    var out = '';
    if (a !== 0) out += String(a);
    if (b !== 0) { var bb = Math.abs(b) === 1 ? '' : String(Math.abs(b)); out += (b < 0 ? '-' : (a !== 0 ? '+' : '')) + bb + '\\sqrt{' + r + '}'; }
    if (!out) out = '0';
    return d === 1 ? out : '\\dfrac{' + out + '}{' + d + '}';
  }
  function T(s) { return '$' + s + '$'; }
  function signed(b) { return b >= 0 ? '+' + b : '-' + (-b); }

  /* ────────── 角：k·π/12 的精確表示 ────────── */
  /* piTex(k, d)：k·π/d 化簡後的 LaTeX，如 5π/6、-π/4、2π、0 */
  function piTex(k, d) {
    if (k === 0) return '0';
    var g = gcd(Math.abs(k), d); k /= g; d /= g;
    var sgn = k < 0 ? '-' : ''; k = Math.abs(k);
    var num = (k === 1 ? '' : k) + '\\pi';
    return sgn + (d === 1 ? num : '\\dfrac{' + num + '}{' + d + '}');
  }
  function degTex(deg) { return deg + '^\\circ'; }
  function piToDegTex(k, d) { var f = F(k, d); return (f.d === 1 ? '' : '\\dfrac{') + (Math.abs(f.n) === 1 ? (f.n < 0 ? '-' : '') : f.n + '\\times') + '180^\\circ' + (f.d === 1 ? '' : '}{' + f.d + '}'); }   /* kπ/d 代 π=180°（k、d 先約分，才跟題幹一致） */
  /* 象限（角以度計）：回傳 1..4，或 0 表示在軸上 */
  function quadrant(deg) { var a = ((deg % 360) + 360) % 360; if (a % 90 === 0) return 0; return Math.floor(a / 90) + 1; }
  var QN = ['軸上', '一', '二', '三', '四'];

  /* 特殊角精確值：deg 是 15 的倍數但只保證 30/45 的倍數有「短」值；回傳 {c, r, d} 表 c√r/d，tan 可能為 null（不存在） */
  function tv(deg) {
    var a = ((deg % 360) + 360) % 360, ref = a % 180; if (ref > 90) ref = 180 - ref;
    var base = { 0: [0, 1, 1], 30: [1, 1, 2], 45: [1, 2, 2], 60: [1, 3, 2], 90: [1, 1, 1] };
    var bs = base[ref], bc = base[90 - ref];
    var sinv = { c: bs[0], r: bs[1], d: bs[2] }, cosv = { c: bc[0], r: bc[1], d: bc[2] };
    if (a > 180) sinv.c = -sinv.c;
    if (a > 90 && a < 270) cosv.c = -cosv.c;
    var tanv;
    if (ref === 90) tanv = null;
    else { var tb = { 0: [0, 1, 1], 30: [1, 3, 3], 45: [1, 1, 1], 60: [1, 3, 1] }[ref]; tanv = { c: tb[0], r: tb[1], d: tb[2] }; if ((a > 90 && a < 180) || (a > 270 && a < 360)) tanv.c = -tanv.c; }
    return { sin: sinv, cos: cosv, tan: tanv };
  }
  function vTex(v) { return surdOver(v.c, v.r, v.d); }
  function vNum(v) { return v.c * Math.sqrt(v.r) / v.d; }

  /* 畢氏三元組 (a, b, c)：sin=a/c, cos=b/c */
  var TRIPLES = [[3, 4, 5], [4, 3, 5], [5, 12, 13], [12, 5, 13], [8, 15, 17], [15, 8, 17], [7, 24, 25], [24, 7, 25], [20, 21, 29], [21, 20, 29], [9, 40, 41]];
  function fracTex(n, d) { return Fr.tex(F(n, d)); }
  function coefPi(x) { return x.d === 1 && Math.abs(x.n) === 1 ? (x.n < 0 ? '-' : '') + '\\pi' : Fr.tex(x) + '\\pi'; }   /* 分數 × π：係數 1 不寫成 1π */
  function negP(s) { return s.charAt(0) === '-' ? '\\left(' + s + '\\right)' : s; }                                       /* 負數放進算式要加括號 */
  function sgnPi(k) { return (k < 0 ? '-' : '+') + piTex(Math.abs(k), 12); }                                              /* ±kπ/12（帶正負號接在式子後面） */

  /* 誘導公式表：[名稱 LaTeX 的產生器, sin 結果, cos 結果, tan 結果]；結果用 {f: 'sin'|'cos'|'tan', s: ±1} */
  var REDUCE = [
    { arg: function (th) { return '\\pi-' + th; }, k: 180, m: -1, sin: ['sin', 1], cos: ['cos', -1], tan: ['tan', -1] },
    { arg: function (th) { return '\\pi+' + th; }, k: 180, m: 1, sin: ['sin', -1], cos: ['cos', -1], tan: ['tan', 1] },
    { arg: function (th) { return '-' + th; }, k: 0, m: -1, sin: ['sin', -1], cos: ['cos', 1], tan: ['tan', -1] },
    { arg: function (th) { return '2\\pi-' + th; }, k: 360, m: -1, sin: ['sin', -1], cos: ['cos', 1], tan: ['tan', -1] },
    { arg: function (th) { return '\\dfrac{\\pi}{2}-' + th; }, k: 90, m: -1, sin: ['cos', 1], cos: ['sin', 1], tan: ['cot', 1] },
    { arg: function (th) { return '\\dfrac{\\pi}{2}+' + th; }, k: 90, m: 1, sin: ['cos', 1], cos: ['sin', -1], tan: ['cot', -1] },
    { arg: function (th) { return '\\dfrac{3\\pi}{2}-' + th; }, k: 270, m: -1, sin: ['cos', -1], cos: ['sin', -1], tan: ['cot', 1] },
    { arg: function (th) { return '\\dfrac{3\\pi}{2}+' + th; }, k: 270, m: 1, sin: ['cos', -1], cos: ['sin', 1], tan: ['cot', -1] }
  ];

  /* ══════════════════════════════════════════════════════════
     L1　基礎（25 型；2026-09-28 依段考頻率補 4 型）
     ══════════════════════════════════════════════════════════ */
  var L1 = {};

  /* 1-1 弧度、扇形、定義 */
  L1.degToRad = function (r) {
    var base = r.pick([30, 45, 60, 90, 120, 135, 150, 210, 225, 240, 270, 300, 315, 330]);
    var deg = base + 360 * r.pick([0, 0, 0, 1, -1]);
    if (r() < 0.35) deg = -deg;
    var f = F(deg, 180);
    return { q: '將 ' + T(degTex(deg)) + ' 化為弧度。', a: T(piTex(f.n, f.d)), h: '乘以 $\\dfrac{\\pi}{180}$：$' + deg + '^\\circ=\\dfrac{' + deg + '\\pi}{180}$，分子分母同除以 $' + gcd(Math.abs(deg), 180) + '$。', p: { deg: deg } };
  };
  L1.radToDeg = function (r) {
    var d = r.pick([3, 4, 6, 6, 12]), k = r.int(1, 3 * d) * r.sign(), guard = 0;
    while ((k * 180 / d) % 90 === 0 && guard++ < 50) k = r.int(1, 3 * d) * r.sign();
    var deg = k * 180 / d, qd = quadrant(deg);
    return { q: '將 ' + T(piTex(k, d)) + ' 化為度數，並判斷它是第幾象限角。', a: T(degTex(deg)) + '，' + (qd ? '第' + QN[qd] + '象限角' : '終邊在坐標軸上'), h: '$\\pi=180^\\circ$：$' + piTex(k, d) + '=' + piToDegTex(k, d) + '$；判象限先加減 $360^\\circ$，化到 $[0^\\circ,360^\\circ)$ 是 $' + (((deg % 360) + 360) % 360) + '^\\circ$。', p: { k: k, d: d, deg: deg, quad: qd } };
  };
  L1.arcArea = function (r) {
    var rad = r.int(2, 12), k = r.pick([1, 2, 3, 4, 5]), d = r.pick([2, 3, 4, 6]);
    if (k >= 2 * d) k -= 3;                                            /* 圓心角要 <2π 才是扇形（原本會出 2π、5π/2） */
    var arc = F(rad * k, d), area = F(rad * rad * k, 2 * d);
    return { q: '一扇形半徑為 ' + T(rad) + '，圓心角為 ' + T(piTex(k, d)) + '，求弧長與面積。', a: '弧長 ' + T(coefPi(arc)) + '，面積 ' + T(coefPi(area)), h: '$s=r\\theta=' + rad + '\\times' + piTex(k, d) + '$、$A=\\dfrac12r^2\\theta=\\dfrac12\\times' + rad + '^2\\times' + piTex(k, d) + '$（$\\theta$ 一定用弧度，$\\pi$ 留著不要換）。', p: { r: rad, k: k, d: d } };
  };
  L1.sectorFromArc = function (r) {
    var rad = r.int(2, 10), th = r.pick([1, 2, 3, 4]);
    var arc = rad * th, area = F(rad * arc, 2);
    return { q: '一扇形半徑為 ' + T(rad) + '、弧長為 ' + T(arc) + '，求圓心角（弧度）與面積。', a: '圓心角 ' + T(th) + '，面積 ' + T(Fr.tex(area)), h: '$\\theta=\\dfrac sr=\\dfrac{' + arc + '}{' + rad + '}$；面積直接用 $\\dfrac12rs=\\dfrac12\\times' + rad + '\\times' + arc + '$，不必先算 $\\theta$。', p: { r: rad, arc: arc, th: th } };
  };
  L1.signQuad = function (r) {
    var v = r.pick([1, 2, 3, 4, 5, 6]), fn = r.pick(['sin', 'cos', 'tan']);
    var val = { sin: Math.sin(v), cos: Math.cos(v), tan: Math.tan(v) }[fn];
    var qd = v < Math.PI / 2 ? 1 : v < Math.PI ? 2 : v < 3 * Math.PI / 2 ? 3 : 4;
    return { q: '判斷 ' + T('\\' + fn + ' ' + v) + ' 的正負（' + v + ' 為弧度）。', a: (val > 0 ? '正' : '負') + '（' + v + ' 弧度在第' + QN[qd] + '象限）', h: '$\\dfrac{\\pi}{2}\\approx1.57$、$\\pi\\approx3.14$、$\\dfrac{3\\pi}{2}\\approx4.71$、$2\\pi\\approx6.28$：$' + v + '$ 弧度 $\\approx' + Math.round(v * 57.3) + '^\\circ$，在第' + QN[qd] + '象限，看 $\\' + fn + '$ 在那個象限的正負。', p: { v: v, fn: fn, sign: val > 0 ? 1 : -1 } };
  };
  L1.specialValue = function (r) {
    var fn = r.pick(['sin', 'cos', 'tan']), d = r.pick([3, 4, 6]), k = r.int(1, 4 * d);
    while (k % d === 0 || (fn === 'tan' && (k * 180 / d) % 180 === 90)) k = r.int(1, 4 * d);
    var deg = k * 180 / d, v = tv(deg)[fn];
    return { q: '求 ' + T('\\' + fn + piTex(k, d)) + ' 的值。', a: T(vTex(v)), h: '$' + piTex(k, d) + '=' + deg + '^\\circ$，減掉 $360^\\circ$ 的倍數得 $' + (((deg % 360) + 360) % 360) + '^\\circ$' + (quadrant(deg) ? '（第' + QN[quadrant(deg)] + '象限），參考角 $' + (function (a) { a %= 180; return a > 90 ? 180 - a : a; })(((deg % 360) + 360) % 360) + '^\\circ$，再依象限定正負。' : '，終邊在坐標軸上，直接看單位圓上的點。'), p: { fn: fn, k: k, d: d, deg: deg } };
  };
  L1.pointDef = function (r) {
    var t = r.pick(TRIPLES), sx = r.sign(), sy = r.sign(), x = sx * t[1], y = sy * t[0], c = t[2];
    return { q: '已知角 ' + T('\\theta') + ' 的終邊通過點 ' + T('P(' + x + ',' + y + ')') + '，求 ' + T('\\sin\\theta,\\ \\cos\\theta,\\ \\tan\\theta') + '。',
      a: T('\\sin\\theta=' + fracTex(y, c) + ',\\ \\cos\\theta=' + fracTex(x, c) + ',\\ \\tan\\theta=' + fracTex(y, x)),
      h: '$r=\\sqrt{(' + x + ')^2+(' + y + ')^2}=' + c + '$，$\\sin\\theta=\\dfrac yr$、$\\cos\\theta=\\dfrac xr$、$\\tan\\theta=\\dfrac yx$，$x=' + x + '$、$y=' + y + '$ 帶正負號代進去。', p: { x: x, y: y, r: c } };
  };
  L1.fromSinQuad = function (r) {
    var t = r.pick(TRIPLES), qd = r.pick([1, 2, 3, 4]);
    var give = r.pick(['sin', 'cos']);
    var s = (qd <= 2 ? 1 : -1) * t[0], c = (qd === 1 || qd === 4 ? 1 : -1) * t[1], R = t[2];
    var ask = give === 'sin' ? ['cos', 'tan'] : ['sin', 'tan'];
    var vals = { sin: fracTex(s, R), cos: fracTex(c, R), tan: fracTex(s, c) };
    return { q: '已知 ' + T('\\' + give + '\\theta=' + vals[give]) + '，且 ' + T('\\theta') + ' 為第' + QN[qd] + '象限角，求 ' + T('\\' + ask[0] + '\\theta') + ' 與 ' + T('\\' + ask[1] + '\\theta') + '。',
      a: T('\\' + ask[0] + '\\theta=' + vals[ask[0]] + ',\\ \\' + ask[1] + '\\theta=' + vals[ask[1]]),
      h: '$\\sin^2\\theta+\\cos^2\\theta=1$ ⟹ $|\\' + ask[0] + '\\theta|=\\sqrt{1-\\left(' + fracTex(give === 'sin' ? Math.abs(s) : Math.abs(c), R) + '\\right)^2}=' + fracTex(give === 'sin' ? Math.abs(c) : Math.abs(s), R) + '$（$' + t[0] + '$-$' + t[1] + '$-$' + t[2] + '$ 三元組），第' + QN[qd] + '象限決定正負，$\\tan$ 用兩者相除。', p: { give: give, s: s, c: c, R: R, quad: qd } };
  };
  L1.coterminal = function (r) {
    var mode = r.pick(['deg', 'rad']);
    if (mode === 'deg') {
      var base = r.pick([30, 45, 60, 120, 135, 150, 210, 225, 240, 300, 315, 330]), deg = base + 360 * r.pick([1, 2, -1, -2, 3]);
      return { q: '求與 ' + T(degTex(deg)) + ' 同界的最小正角，並判斷象限。', a: T(degTex(base)) + '，第' + QN[quadrant(base)] + '象限', h: '$' + deg + '^\\circ' + ((deg - base) > 0 ? '-' : '+') + Math.abs((deg - base) / 360) + '\\times360^\\circ$，落到 $[0^\\circ,360^\\circ)$ 就是同界的最小正角，再看象限。', p: { mode: mode, deg: deg, base: base } };
    }
    var d = r.pick([3, 4, 6]), k0 = r.int(1, 2 * d - 1); while ((k0 * 180 / d) % 90 === 0) k0 = r.int(1, 2 * d - 1);   /* π/2、3π/2 也在軸上，沒有象限 */
    var k = k0 + 2 * d * r.pick([1, 2, -1, -2]);
    return { q: '求與 ' + T(piTex(k, d)) + ' 同界的最小正角，並判斷象限。', a: T(piTex(k0, d)) + '，第' + QN[quadrant(k0 * 180 / d)] + '象限', h: '$2\\pi=\\dfrac{' + (2 * d) + '\\pi}{' + d + '}$：$' + piTex(k, d) + ((k - k0) > 0 ? '-' : '+') + Math.abs((k - k0) / (2 * d)) + '\\times2\\pi$，落到 $[0,2\\pi)$ 就是答案，再看象限。', p: { mode: mode, k: k, d: d, k0: k0 } };
  };
  L1.reduceFormula = function (r) {
    var rule = r.pick(REDUCE), fn = r.pick(['sin', 'cos', 'tan']);
    if (fn === 'tan' && rule.k % 180 === 90) fn = r.pick(['sin', 'cos']);   /* 避免 cot */
    var res = rule[fn];
    var ans = (res[1] < 0 ? '-' : '') + '\\' + res[0] + '\\theta';
    return { q: '化簡 ' + T('\\' + fn + '\\left(' + rule.arg('\\theta') + '\\right)') + '。', a: T(ans), h: '「奇變偶不變，符號看象限」：$' + rule.arg('\\theta') + '$ 裡的 $' + (rule.k === 0 ? '0' : piTex(rule.k / 15, 12)) + '$ 是 $\\dfrac{\\pi}{2}$ 的' + (rule.k % 180 === 90 ? '奇數倍 ⟹ $\\sin$、$\\cos$ 互換' : '偶數倍 ⟹ 函數名不變') + '；把 $\\theta$ 當銳角，$' + rule.arg('\\theta') + '$ 落在第' + QN[quadrant(rule.k + rule.m * 30)] + '象限，看 $\\' + fn + '$ 在那裡的正負。', p: { fn: fn, k: rule.k, m: rule.m, resf: res[0], ress: res[1] } };
  };

  /* 1-2 和差角、倍角、半角 */
  L1.sumExact = function (r) {
    var fn = r.pick(['sin', 'cos', 'tan']), deg = r.pick([15, 75, 105, 165, 195, 255, 285, 345]);
    var v = exact15(deg)[fn];
    var split = deg === 15 ? [45, -30] : deg % 90 === 15 ? [deg - 45, 45] : [deg - 30, 30];      /* 15° 用 45°−30°（原本拆成 −30°+45°） */
    return { q: '求 ' + T('\\' + fn + degTex(deg)) + ' 的精確值。', a: T(v), h: '拆成 ' + T(degTex(split[0]) + (split[1] > 0 ? '+' : '-') + degTex(Math.abs(split[1]))) + ' 再用' + (split[1] > 0 ? '和' : '差') + '角公式。', p: { fn: fn, deg: deg } };
  };
  /* 15° 倍數的精確值（用 45°±30° 展開）：回傳 LaTeX */
  function exact15(deg) {
    var a = ((deg % 360) + 360) % 360;
    var s = Math.sin(a * Math.PI / 180), c = Math.cos(a * Math.PI / 180);
    /* sin,cos ∈ {±(√6±√2)/4}；tan ∈ {±(2±√3)} */
    function sc(val) {
      var cands = [[1, 1, '\\dfrac{\\sqrt6+\\sqrt2}{4}'], [-1, -1, '-\\dfrac{\\sqrt6+\\sqrt2}{4}'], [1, -1, '\\dfrac{\\sqrt6-\\sqrt2}{4}'], [-1, 1, '\\dfrac{\\sqrt2-\\sqrt6}{4}']];
      for (var i = 0; i < cands.length; i++) { var v = (cands[i][0] * Math.sqrt(6) + cands[i][1] * Math.sqrt(2)) / 4; if (Math.abs(v - val) < 1e-9) return cands[i][2]; }
      return '?';
    }
    function tn(val) {
      var cands = [[2, 1, '2+\\sqrt3'], [2, -1, '2-\\sqrt3'], [-2, -1, '-2-\\sqrt3'], [-2, 1, '-2+\\sqrt3']];
      for (var i = 0; i < cands.length; i++) { var v = cands[i][0] + cands[i][1] * Math.sqrt(3); if (Math.abs(v - val) < 1e-9) return cands[i][2]; }
      return '?';
    }
    return { sin: sc(s), cos: sc(c), tan: tn(s / c) };
  }
  L1.cosDiffQuad = function (r) {
    var t1 = r.pick(TRIPLES), t2 = r.pick(TRIPLES), q1 = r.pick([1, 2, 3, 4]), q2 = r.pick([1, 2, 3, 4]);
    var s1 = (q1 <= 2 ? 1 : -1) * t1[0], c1 = (q1 === 1 || q1 === 4 ? 1 : -1) * t1[1], R1 = t1[2];
    var s2 = (q2 <= 2 ? 1 : -1) * t2[0], c2 = (q2 === 1 || q2 === 4 ? 1 : -1) * t2[1], R2 = t2[2];
    var which = r.pick(['sin+', 'cos-', 'cos+', 'sin-']);
    var num = { 'sin+': s1 * c2 + c1 * s2, 'sin-': s1 * c2 - c1 * s2, 'cos+': c1 * c2 - s1 * s2, 'cos-': c1 * c2 + s1 * s2 }[which];
    var expr = '\\' + which.slice(0, 3) + '(\\alpha' + which.slice(3) + '\\beta)';
    return { q: '已知 ' + T('\\sin\\alpha=' + fracTex(s1, R1)) + '（' + T('\\alpha') + ' 為第' + QN[q1] + '象限角）、' + T('\\cos\\beta=' + fracTex(c2, R2)) + '（' + T('\\beta') + ' 為第' + QN[q2] + '象限角），求 ' + T(expr) + '。',
      a: T(expr + '=' + fracTex(num, R1 * R2)), h: '先補齊：$|\\cos\\alpha|=' + fracTex(Math.abs(c1), R1) + '$（第' + QN[q1] + '象限定號）、$|\\sin\\beta|=' + fracTex(Math.abs(s2), R2) + '$（第' + QN[q2] + '象限定號），再套 $' + expr + '$ 的展開式。', p: { s1: s1, c1: c1, R1: R1, s2: s2, c2: c2, R2: R2, q1: q1, q2: q2, which: which, num: num } };
  };
  L1.tanSum = function (r) {
    var p1 = F(r.int(1, 5) * r.sign(), r.pick([1, 1, 2, 3])), p2 = F(r.int(1, 5) * r.sign(), r.pick([1, 1, 2, 3]));
    var sgn = r.sign();
    var den = Fr.sub(F(1), Fr.mul(F(sgn), Fr.mul(p1, p2))), guard = 0;
    while (den.n === 0 && guard++ < 20) { p2 = F(r.int(1, 5) * r.sign(), r.pick([1, 2, 3])); den = Fr.sub(F(1), Fr.mul(F(sgn), Fr.mul(p1, p2))); }
    var num = sgn > 0 ? Fr.add(p1, p2) : Fr.sub(p1, p2);
    var val = Fr.div(num, den);
    var expr = '\\tan(\\alpha' + (sgn > 0 ? '+' : '-') + '\\beta)';
    return { q: '已知 ' + T('\\tan\\alpha=' + Fr.tex(p1)) + '、' + T('\\tan\\beta=' + Fr.tex(p2)) + '，求 ' + T(expr) + '。', a: T(expr + '=' + Fr.tex(val)), h: '$\\tan(\\alpha\\pm\\beta)=\\dfrac{\\tan\\alpha\\pm\\tan\\beta}{1\\mp\\tan\\alpha\\tan\\beta}$（分母正負號相反）：代入 $\\dfrac{' + Fr.tex(p1, false) + (sgn > 0 ? '+' : '-') + '\\left(' + Fr.tex(p2, false) + '\\right)}{1' + (sgn > 0 ? '-' : '+') + '\\left(' + Fr.tex(p1, false) + '\\right)\\left(' + Fr.tex(p2, false) + '\\right)}$，上下同乘分母的最小公倍數。', p: { p1: [p1.n, p1.d], p2: [p2.n, p2.d], sgn: sgn, val: [val.n, val.d] } };
  };
  L1.doubleFromSin = function (r) {
    var t = r.pick(TRIPLES), qd = r.pick([1, 2, 3, 4]), give = r.pick(['sin', 'cos']);
    var s = (qd <= 2 ? 1 : -1) * t[0], c = (qd === 1 || qd === 4 ? 1 : -1) * t[1], R = t[2];
    var s2 = F(2 * s * c, R * R), c2 = F(c * c - s * s, R * R);
    return { q: '已知 ' + T('\\' + give + '\\theta=' + fracTex(give === 'sin' ? s : c, R)) + '，' + T('\\theta') + ' 為第' + QN[qd] + '象限角，求 ' + T('\\sin2\\theta') + ' 與 ' + T('\\cos2\\theta') + '。',
      a: T('\\sin2\\theta=' + Fr.tex(s2) + ',\\ \\cos2\\theta=' + Fr.tex(c2)), h: '先由畢氏補另一個：$|\\' + (give === 'sin' ? 'cos' : 'sin') + '\\theta|=' + fracTex(give === 'sin' ? Math.abs(c) : Math.abs(s), R) + '$，第' + QN[qd] + '象限定號；再 $\\sin2\\theta=2\\sin\\theta\\cos\\theta$、$\\cos2\\theta=\\cos^2\\theta-\\sin^2\\theta$。', p: { give: give, s: s, c: c, R: R, quad: qd } };
  };
  /* 半角：cosθ 取讓 (1±cosθ)/2 是完全平方的值 */
  var HALF = [[7, 25, 4, 5, 3, 5], [-7, 25, 3, 5, 4, 5], [1, 8, 3, 4, null, null], [-1, 8, null, null, 3, 4], [-31, 49, 3, 7, null, null], [31, 49, null, null, 3, 7], [17, 25, null, null, 2, 5], [-17, 25, 2, 5, null, null]];
  /* 每列：[cosθ 分子, 分母, cos(θ/2) 分子, 分母, sin(θ/2) 分子, 分母]（null = 不是有理數，不出這一問） */
  L1.halfFromCos = function (r) {
    var row = r.pick(HALF), askCos = row[2] !== null && (row[4] === null || r() < 0.5);
    var qd = r.pick([1, 2, 3, 4]); var cosv = row[0] / row[1];
    if ((cosv > 0) !== (qd === 1 || qd === 4)) qd = cosv > 0 ? r.pick([1, 4]) : r.pick([2, 3]);
    /* θ 在第 qd 象限（取 0<θ<2π），θ/2 的範圍 */
    var lo = (qd - 1) * 90, hi = qd * 90;   /* θ 的度數範圍 */
    var hlo = lo / 2, hhi = hi / 2;         /* θ/2 的範圍：(0,45),(45,90),(90,135),(135,180) */
    var sgn = askCos ? (hhi <= 90 ? 1 : -1) : 1;   /* sin(θ/2) 在 (0,180) 恆正；cos(θ/2) 在 (90,180) 為負 */
    var num = askCos ? row[2] : row[4], den = askCos ? row[3] : row[5];
    var fnName = askCos ? '\\cos' : '\\sin';
    return { q: '已知 ' + T('\\cos\\theta=' + fracTex(row[0], row[1])) + '，且 ' + T(piTex(lo / 180 * 12, 12) + '\\lt\\theta\\lt' + piTex(hi / 180 * 12, 12)) + '，求 ' + T(fnName + '\\dfrac{\\theta}{2}') + '。',
      a: T(fnName + '\\dfrac{\\theta}{2}=' + fracTex(sgn * num, den)), h: '半角公式 $' + (askCos ? '\\cos^2\\dfrac{\\theta}{2}=\\dfrac{1+\\cos\\theta}{2}=\\dfrac{1+' + negP(fracTex(row[0], row[1])) + '}{2}' : '\\sin^2\\dfrac{\\theta}{2}=\\dfrac{1-\\cos\\theta}{2}=\\dfrac{1-' + negP(fracTex(row[0], row[1])) + '}{2}') + '$；這裡 $' + piTex(lo / 30, 12) + '\\lt\\dfrac{\\theta}{2}\\lt' + piTex(hi / 30, 12) + '$（第' + QN[quadrant(lo / 2 + 1)] + '象限），決定開根號後的正負。', p: { cosn: row[0], cosd: row[1], quad: qd, askCos: askCos, num: sgn * num, den: den } };
  };

  /* 1-3 圖形與疊合 */
  L1.ampPeriod = function (r) {
    var a = r.int(1, 5) * r.sign(), b = r.pick([1, 2, 3, 4, 0.5]), cK = r.pick([0, 1, -1, 2, -2, 3]), d = r.int(-3, 3), fn = r.pick(['sin', 'cos']);
    var bT = b === 0.5 ? '\\dfrac{x}{2}' : (b === 1 ? 'x' : b + 'x');
    var inner = bT + (cK === 0 ? '' : (cK > 0 ? '+' : '-') + piTex(Math.abs(cK), 6));
    var per = b === 0.5 ? '4\\pi' : (b === 1 ? '2\\pi' : b === 2 ? '\\pi' : b === 4 ? '\\dfrac{\\pi}{2}' : '\\dfrac{2\\pi}{' + b + '}');
    var expr = (a === 1 ? '' : a === -1 ? '-' : a) + '\\' + fn + '\\left(' + inner + '\\right)' + (d === 0 ? '' : signed(d));
    return { q: '寫出 ' + T('y=' + expr) + ' 的振幅、週期、最大值與最小值。', a: '振幅 ' + T(Math.abs(a)) + '，週期 ' + T(per) + '，最大值 ' + T(d + Math.abs(a)) + '，最小值 ' + T(d - Math.abs(a)),
      h: '振幅 $=|a|=' + Math.abs(a) + '$、週期 $=\\dfrac{2\\pi}{|b|}$（這裡 $b=' + (b === 0.5 ? '\\dfrac12' : b) + '$）、最大最小 $=d\\pm|a|=' + d + '\\pm' + Math.abs(a) + '$；括號裡的相位不影響這四個量。', p: { a: a, b: b, cK: cK, d: d } };
  };
  L1.shiftFunc = function (r) {
    var fn = r.pick(['sin', 'cos']), hk = r.pick([1, 2, 3, 4, 6]), hs = r.sign(), vs = r.int(1, 3) * r.sign();
    var hor = hs > 0 ? '右' : '左', ver = vs > 0 ? '上' : '下';
    var ans = '\\' + fn + '\\left(x' + (hs > 0 ? '-' : '+') + piTex(1, hk) + '\\right)' + signed(vs);
    return { q: '將 ' + T('y=\\' + fn + ' x') + ' 的圖形向' + hor + '平移 ' + T(piTex(1, hk)) + '，再向' + ver + '平移 ' + T(Math.abs(vs)) + '，求所得圖形的方程式。', a: T('y=' + ans), h: '向' + hor + '平移 $' + piTex(1, hk) + '$ ⟹ 把 $x$ 換成 $x' + (hs > 0 ? '-' : '+') + piTex(1, hk) + '$（右減左加）；向' + ver + '平移 $' + Math.abs(vs) + '$ ⟹ 整個函數 $' + (vs > 0 ? '+' : '-') + Math.abs(vs) + '$，加在外面。', p: { fn: fn, hk: hk, hs: hs, vs: vs } };
  };
  /* a sin x + b cos x 的疊合：只用有精確 θ 的組合 */
  var COMB = [[1, 1, 2, 1, 4], [1, -1, 2, -1, 4], [-1, 1, 2, 3, 4], [1, 3, 4, 1, 3], [3, 1, 4, 1, 6], [3, -1, 4, -1, 6], [1, -3, 4, -1, 3], [-1, 3, 4, 2, 3], [-3, 1, 4, 5, 6]];
  /* 每列 [a, b（b=3 代表 √3）, r²(對 a,b 的實際值), θ 分子, θ 分母]：a sin x + b cos x = √(r²) sin(x + θ) */
  /* 疊合係數的排版：coef ∈ {±1, ±3(=±√3)}，倍數 m；first=true 是最前面的項（不印 +） */
  function combTerm(coef, m, first) {
    var neg = coef < 0, isS3 = Math.abs(coef) === 3;
    var mag = isS3 ? ((m === 1 ? '' : m) + '\\sqrt3') : (m === 1 ? '' : String(m));
    return (neg ? '-' : (first ? '' : '+')) + mag;
  }
  L1.combineStd = function (r) {
    var row = r.pick(COMB), m = r.pick([1, 1, 2, 3]);
    var a = row[0] * m, b = row[1] * m, RT = sqrtTex(row[2] * m * m);
    var aT = combTerm(row[0], m, true) + '\\sin x', bT = combTerm(row[1], m, false) + '\\cos x';
    return { q: '將 ' + T('y=' + aT + bT) + ' 化成 ' + T('r\\sin(x+\\theta)') + ' 的形式（' + T('r\\gt0') + '、' + T('-\\pi\\lt\\theta\\le\\pi') + '）。',
      a: T('y=' + RT + '\\sin\\left(x' + (row[3] < 0 ? '-' : '+') + piTex(Math.abs(row[3]), row[4]) + '\\right)'),
      h: '$a=' + combTerm(row[0], m, true) + '$、$b=' + combTerm(row[1], m, true) + '$，$r=\\sqrt{a^2+b^2}=' + RT + '$；$\\cos\\theta=\\dfrac ar$、$\\sin\\theta=\\dfrac br$，兩個符號一起決定 $\\theta$ 的象限（是 $\\dfrac{\\pi}{6}$、$\\dfrac{\\pi}{4}$、$\\dfrac{\\pi}{3}$ 家族的角）。',
      p: { aIsSqrt3: Math.abs(row[0]) === 3, aSign: row[0] < 0 ? -1 : 1, bIsSqrt3: Math.abs(row[1]) === 3, bSign: row[1] < 0 ? -1 : 1, m: m, R2: row[2] * m * m, thn: row[3], thd: row[4] } };
  };
  L1.maxMin = function (r) {
    var t = r.pick(TRIPLES), a = t[0] * r.sign(), b = t[1] * r.sign(), d = r.int(-4, 6), R = t[2];
    var expr = (a === 1 ? '' : a === -1 ? '-' : a) + '\\sin x' + (b === 1 ? '+' : b === -1 ? '-' : signed(b)) + '\\cos x' + (d === 0 ? '' : signed(d));
    return { q: '求 ' + T('f(x)=' + expr) + ' 的最大值與最小值。', a: '最大值 ' + T(d + R) + '，最小值 ' + T(d - R), h: '疊合後振幅 $=\\sqrt{a^2+b^2}$，這裡 $a=' + a + '$、$b=' + b + '$（$' + t[0] + '$-$' + t[1] + '$-$' + t[2] + '$ 三元組）；最大最小 $=' + d + '\\pm$ 振幅。', p: { a: a, b: b, d: d, R: R } };
  };
  L1.basicEq = function (r) {
    var fn = r.pick(['sin', 'cos', 'tan']);
    var pool = fn === 'tan' ? [[1, 1, 1], [-1, 1, 1], [1, 3, 1], [-1, 3, 1], [1, 3, 3], [-1, 3, 3], [0, 1, 1]] : [[1, 1, 2], [-1, 1, 2], [1, 2, 2], [-1, 2, 2], [1, 3, 2], [-1, 3, 2], [0, 1, 1], [1, 1, 1], [-1, 1, 1]];
    var v = r.pick(pool), val = { c: v[0], r: v[1], d: v[2] }, target = vNum(val);
    var sols = [];
    for (var k = 0; k < 24; k++) { var deg = k * 15; if (deg % 30 !== 0 && deg % 45 !== 0) continue; var w = tv(deg)[fn]; if (w && Math.abs(vNum(w) - target) < 1e-9) sols.push(k); }
    var solT = sols.map(function (k) { return piTex(k, 12); }).join(',\\ ');
    return { q: '解 ' + T('\\' + fn + ' x=' + vTex(val)) + '，' + T('0\\le x\\lt2\\pi') + '。', a: T('x=' + solT), h: (sols.length ? '第一個解 $x=' + piTex(sols[0], 12) + '$' + (sols.length > 1 ? '，另一個用對稱性（$\\pi-x$、$\\pi+x$ 或 $2\\pi-x$）補上' : '，這個值在 $[0,2\\pi)$ 只有一解') + '；$\\' + fn + '$ 值為' + (v[0] < 0 ? '負 ⟹ 終邊在' + (fn === 'sin' ? '三、四' : fn === 'cos' ? '二、三' : '二、四') + '象限' : v[0] > 0 ? '正 ⟹ 終邊在' + (fn === 'sin' ? '一、二' : fn === 'cos' ? '一、四' : '一、三') + '象限' : '零 ⟹ 終邊在坐標軸上') + '。' : '無解'), p: { fn: fn, c: v[0], r: v[1], d: v[2], ks: sols } };
  };
  L1.periodOf = function (r) {
    var b = r.pick([1, 2, 3, 4, 0.5]), kind = r.pick(['sin', 'cos', 'tan', 'abssin', 'sin2']);
    var bT = b === 0.5 ? '\\dfrac{x}{2}' : (b === 1 ? 'x' : b + 'x');
    var expr = { sin: '\\sin ' + bT, cos: '\\cos ' + bT, tan: '\\tan ' + bT, abssin: '\\left|\\sin ' + bT + '\\right|', sin2: '\\sin^2 ' + bT }[kind];
    var P = (kind === 'sin' || kind === 'cos') ? F(2, 1) : F(1, 1);      /* 以 π 為單位，再除以 b */
    P = Fr.div(P, F(b === 0.5 ? 1 : b, b === 0.5 ? 2 : 1));
    return { q: '求 ' + T('y=' + expr) + ' 的最小正週期。', a: T(P.n === 1 && P.d === 1 ? '\\pi' : Fr.tex(P) + '\\pi'), h: '這裡 $b=' + (b === 0.5 ? '\\dfrac12' : b) + '$：' + { sin: '$\\sin$ 的週期 $\\dfrac{2\\pi}{|b|}$', cos: '$\\cos$ 的週期 $\\dfrac{2\\pi}{|b|}$', tan: '$\\tan$ 本身的週期就是 $\\pi$，所以是 $\\dfrac{\\pi}{|b|}$', abssin: '加絕對值把負半波翻上來，週期減半成 $\\dfrac{\\pi}{|b|}$', sin2: '平方後 $\\sin^2u=\\dfrac{1-\\cos2u}{2}$，週期減半成 $\\dfrac{\\pi}{|b|}$' }[kind] + '。', p: { b: b, kind: kind, P: [P.n, P.d] } };
  };

  /* ══════════ 2026-09-28 擴充（依段考卷出現頻率補題型）：L1 4 型 ══════════ */
  function nonSpecDeg(r, lo, hi) { var d; do { d = r.int(lo, hi); } while (d % 15 === 0); return d; }   /* 不是 15° 倍數的整數度 */
  function dg(x) { return x + '^\\circ'; }

  /* 1-2 和差角公式逆用：看出是哪一條公式的展開式，合回一個角 */
  L1.sumReverse = function (r) {
    var fn = r.pick(['sin', 'sin', 'cos', 'cos', 'tan']), op = r.pick(['+', '-']), sw = r.int(0, 1);
    var Td = r.pick(fn === 'tan' ? [30, 45, 60, 120, 135, 150] : [30, 45, 60, 90, 120, 135, 150]);
    var B = op === '+' ? nonSpecDeg(r, 5, Math.min(85, Td - 5)) : nonSpecDeg(r, 5, Math.min(85, 175 - Td));
    var A = op === '+' ? Td - B : Td + B, sA = '\\sin' + dg(A), cA = '\\cos' + dg(A), sB = '\\sin' + dg(B), cB = '\\cos' + dg(B), expr;
    if (fn === 'sin') expr = sw ? cB + sA + op + sB + cA : sA + cB + op + cA + sB;
    else if (fn === 'cos') expr = op === '+' ? cA + cB + '-' + sA + sB : (sw ? sA + sB + '+' + cA + cB : cA + cB + '+' + sA + sB);
    else expr = '\\dfrac{\\tan' + dg(A) + op + '\\tan' + dg(B) + '}{1' + (op === '+' ? '-' : '+') + '\\tan' + dg(A) + '\\tan' + dg(B) + '}';
    var v = tv(Td)[fn], one = '\\' + fn + '(' + dg(A) + op + dg(B) + ')';
    return { q: '求 ' + T(expr) + ' 的值。', a: T(vTex(v)),
      h: '這是 $\\' + fn + '(\\alpha' + op + '\\beta)$ 的展開式（$\\alpha=' + dg(A) + '$、$\\beta=' + dg(B) + '$），合回一個角：$' + one + '=\\' + fn + dg(Td) + '$，再查特殊角的值。',
      p: { fn: fn, op: op, A: A, B: B, Td: Td, sw: sw } };
  };

  /* 1-2 倍角公式逆用：2 sinθcosθ、cos²θ−sin²θ、1−2sin²θ、2cos²θ−1、2tanθ/(1−tan²θ)、cos⁴θ−sin⁴θ 合成 2θ */
  var DBL_K = [2, 10, 14, 22, 3, 9, 15, 21];          /* θ = k·7.5°：前四個是 π/12 家族（2θ 是 30° 的倍數），後四個是 π/8 家族（2θ 是 45° 的倍數） */
  L1.doubleReverse = function (r) {
    var k = r.pick(DBL_K), form = r.int(0, 6), rad = k % 2 === 1 || r() < 0.5;
    var th = rad ? piTex(k, 24) : dg(7.5 * k), two = rad ? piTex(2 * k, 24) : dg(15 * k);
    var S = function (f, pw) { return '\\' + f + (pw ? '^' + pw : '') + (rad ? th : ' ' + th); };
    var expr = [ '2' + S('sin') + S('cos'), S('sin') + S('cos'), S('cos', 2) + '-' + S('sin', 2), '1-2' + S('sin', 2), '2' + S('cos', 2) + '-1',
      '\\dfrac{2' + S('tan') + '}{1-' + S('tan', 2) + '}', S('cos', 4) + '-' + S('sin', 4)][form];
    var f2 = form <= 1 ? 'sin' : form === 5 ? 'tan' : 'cos', v = tv(15 * k)[f2];
    var ans = form === 1 ? surdOver(v.c, v.r, 2 * v.d) : vTex(v);
    return { q: '求 ' + T(expr) + ' 的值。', a: T(ans),
      h: '把式子看成 $2\\theta$ 的倍角公式（$\\theta=' + th + '$）：原式 $=' + (form === 1 ? '\\dfrac12' : '') + '\\' + f2 + '\\left(2\\times' + th + '\\right)=' + (form === 1 ? '\\dfrac12' : '') + '\\' + f2 + (rad ? two : ' ' + two) + '$。' + (form === 6 ? '$\\cos^4\\theta-\\sin^4\\theta$ 先用平方差分解。' : ''),
      p: { k: k, form: form, rad: rad } };
  };

  /* 1-3 對稱軸與對稱中心：y=a sin(bx+c)+d、a cos(bx+c)+d */
  function kStepTex(st) {                         /* kπ·st（st 為分數）→ LaTeX */
    if (st.d === 1) return (st.n === 1 ? '' : st.n) + 'k\\pi';
    return '\\dfrac{' + (st.n === 1 ? '' : st.n) + 'k\\pi}{' + st.d + '}';
  }
  function modFr(x, st) {                          /* x 化到 [0, st) */
    var q = Math.floor((x.n * st.d) / (x.d * st.n));
    return Fr.sub(x, Fr.mul(F(q), st));
  }
  L1.symAxis = function (r) {
    var fn = r.pick(['sin', 'cos']), bF = r.pick([F(1), F(2), F(3), F(1, 2)]), cK = r.pick([2, 3, 4, 6, 8, 9, 10, -2, -3, -4, -6, -8]);
    var a = r.int(1, 4) * r.sign(), d = r.pick([0, 0, 1, -1, 2, -2]), t = r.int(0, 3), isAxis = t % 2 === 0;
    var bT = bF.d === 2 ? '\\dfrac{x}{2}' : (bF.n === 1 ? 'x' : bF.n + 'x');
    var inner = bT + (cK > 0 ? '+' : '-') + piTex(Math.abs(cK), 12);
    var expr = (a === 1 ? '' : a === -1 ? '-' : a) + '\\' + fn + '\\left(' + inner + '\\right)' + (d === 0 ? '' : signed(d));
    var u0 = ((fn === 'sin') === isAxis) ? 6 : 0;  /* 括號＝u0·π/12＋kπ */
    var st = Fr.div(F(1), bF), raw = Fr.div(F(u0 - cK, 12), bF), x0 = modFr(raw, st);
    var gen = (x0.n === 0 ? '' : piTex(x0.n, x0.d) + '+') + kStepTex(st), sp = x0.n === 0 ? st : x0;
    var kind = isAxis ? '對稱軸' : '對稱中心', a1, q;
    if (t === 0) { q = '寫出 ' + T('y=' + expr) + ' 圖形的所有對稱軸（用整數 ' + T('k') + ' 表示）。'; a1 = T('x=' + gen) + '（' + T('k') + ' 為整數）'; }
    else if (t === 1) { q = '寫出 ' + T('y=' + expr) + ' 圖形的所有對稱中心（用整數 ' + T('k') + ' 表示）。'; a1 = T('\\left(' + gen + ',' + d + '\\right)') + '（' + T('k') + ' 為整數）'; }
    else if (t === 2) { q = T('y=' + expr) + ' 圖形的對稱軸中，' + T('x') + ' 坐標是最小正數的是哪一條？'; a1 = T('x=' + piTex(sp.n, sp.d)); }
    else { q = T('y=' + expr) + ' 圖形的對稱中心中，' + T('x') + ' 坐標是最小正數的是哪一點？'; a1 = T('\\left(' + piTex(sp.n, sp.d) + ',' + d + '\\right)'); }
    var cond = u0 === 6 ? '\\dfrac{\\pi}{2}+k\\pi' : 'k\\pi';
    return { q: q, a: a1,
      h: '$\\' + fn + '$ 型的' + kind + (isAxis ? '通過最高點、最低點' : '在中線 $y=' + d + '$ 上') + '：令括號 $' + inner + '=' + cond + '$，解出 $x$；相鄰兩條' + (isAxis ? '對稱軸' : '對稱中心') + '相隔半個週期 $' + piTex(st.n, st.d) + '$。',
      p: { fn: fn, b: [bF.n, bF.d], cK: cK, a: a, d: d, t: t, x0: [x0.n, x0.d], st: [st.n, st.d] } };
  };

  /* 1-3 三角函數值的大小比較（弧度 1～6） */
  function cmpMap(fn, v) {                         /* 把角搬到函數單調的區間：回傳 [搬過去的角(數值), 說明 HTML] */
    var P = Math.PI, keep = function (rg) { return '$' + v + '$ 本身就在 ' + rg + ' 內'; };
    var mv = function (eq, w, ap) { return '$' + eq + '$，$' + w + '\\approx' + ap.toFixed(2) + '$'; };
    if (fn === 'sin') {
      if (v < P / 2) return [v, keep('$\\left[-\\dfrac{\\pi}{2},\\dfrac{\\pi}{2}\\right]$')];
      if (v < 1.5 * P) return [P - v, mv('\\sin' + v + '=\\sin(\\pi-' + v + ')', '\\pi-' + v, 3.14 - v)];
      return [v - 2 * P, mv('\\sin' + v + '=\\sin(' + v + '-2\\pi)', v + '-2\\pi', v - 6.28)];
    }
    if (fn === 'cos') {
      if (v < P) return [v, keep('$[0,\\pi]$')];
      return [2 * P - v, mv('\\cos' + v + '=\\cos(2\\pi-' + v + ')', '2\\pi-' + v, 6.28 - v)];
    }
    if (v < P / 2) return [v, keep('$\\left(-\\dfrac{\\pi}{2},\\dfrac{\\pi}{2}\\right)$')];
    if (v < 1.5 * P) return [v - P, mv('\\tan' + v + '=\\tan(' + v + '-\\pi)', v + '-\\pi', v - 3.14)];
    return [v - 2 * P, mv('\\tan' + v + '=\\tan(' + v + '-2\\pi)', v + '-2\\pi', v - 6.28)];
  }
  L1.trigCompare = function (r) {
    var fn = r.pick(['sin', 'cos', 'tan']), vs = r.shuffle([1, 2, 3, 4, 5, 6]).slice(0, 3), nm = ['a', 'b', 'c'];
    var val = { sin: Math.sin, cos: Math.cos, tan: Math.tan }[fn];
    var ord = [0, 1, 2].sort(function (i, j) { return val(vs[j]) - val(vs[i]); });
    var ans = nm[ord[0]] + '\\gt ' + nm[ord[1]] + '\\gt ' + nm[ord[2]];
    var where = { sin: '$\\left[-\\dfrac{\\pi}{2},\\dfrac{\\pi}{2}\\right]$（$\\sin$ 在這裡遞增）', cos: '$[0,\\pi]$（$\\cos$ 在這裡遞減）', tan: '$\\left(-\\dfrac{\\pi}{2},\\dfrac{\\pi}{2}\\right)$（$\\tan$ 在這裡遞增）' }[fn];
    return { q: '設 ' + T('a=\\' + fn + vs[0]) + '、' + T('b=\\' + fn + vs[1]) + '、' + T('c=\\' + fn + vs[2]) + '（角的單位為弧度），比較 ' + T('a,b,c') + ' 的大小。', a: T(ans),
      h: '$\\pi\\approx3.14$。用誘導公式把 $' + vs.join('$、$') + '$ 都搬到 ' + where + '，再比較搬過去的角。',
      p: { fn: fn, vs: vs, ord: ord } };
  };

  /* ══════════════════════════════════════════════════════════
     L1 解題步驟（s：每步一段 HTML）與第一層提示（h1：只講「這是哪一型、第一步做什麼」，不帶數字）
     由 p 重算，所以與題目、答案一定一致；答案由頁面另行附在步驟後。
     ══════════════════════════════════════════════════════════ */
  function absT(n) { return n < 0 ? '(' + n + ')' : String(n); }
  function refDeg(deg) { var a = ((deg % 360) + 360) % 360, r = a % 180; return r > 90 ? 180 - r : r; }
  function quadTxt(deg) { var q = quadrant(deg); return q ? '第' + QN[q] + '象限' : '終邊在坐標軸上'; }
  var L1_H1 = {
    degToRad: '這是「度換弧度」：抓住 $180^\\circ=\\pi$，度數乘上一個固定的比例就好。',
    radToDeg: '這是「弧度換度」：把 $\\pi$ 直接當成 $180^\\circ$ 代進去；判象限前先把角化到一圈以內。',
    arcArea: '這是「扇形的弧長與面積」：兩條公式都只用半徑與圓心角，圓心角要用弧度。',
    sectorFromArc: '這是「由弧長反推」：弧長公式倒過來用就得到圓心角；面積用「半徑乘弧長的一半」最快。',
    signQuad: '這是「弧度值判正負」：先估這個弧度是幾度、落在哪一象限，再看該象限的正負。',
    specialValue: '這是「特殊角求值」：先把角化到一圈以內，找參考角，再依象限定正負。',
    pointDef: '這是「終邊過一點求三角函數」：先算原點到該點的距離 $r$，三個函數都是坐標除以 $r$ 或彼此相除。',
    fromSinQuad: '這是「已知一個函數值求其他」：用 $\\sin^2\\theta+\\cos^2\\theta=1$ 補另一個，正負由象限決定。',
    coterminal: '這是「同界角」：加減整圈（$360^\\circ$ 或 $2\\pi$）直到落在一圈以內。',
    reduceFormula: '這是「誘導公式」：口訣「奇變偶不變、符號看象限」，先看括號裡是 $\\dfrac{\\pi}{2}$ 的幾倍。',
    sumExact: '這是「$15^\\circ$ 倍數的精確值」：把角拆成兩個特殊角的和或差，再用和差角公式。',
    cosDiffQuad: '這是「和差角求值」：先用畢氏補齊缺的函數值（正負看象限），再套公式。',
    tanSum: '這是「$\\tan$ 的和差角」：直接套公式，注意分母是 $1$ 減（或加）兩個 $\\tan$ 的乘積。',
    doubleFromSin: '這是「倍角求值」：先補另一個函數值，再套 $\\sin2\\theta$、$\\cos2\\theta$ 的公式。',
    halfFromCos: '這是「半角求值」：套半角公式後要開根號，正負看的是 $\\dfrac{\\theta}{2}$ 的象限，不是 $\\theta$ 的。',
    ampPeriod: '這是「讀四個參數」：$y=a\\sin(bx+c)+d$ 的振幅看 $a$、週期看 $b$、上下界看 $d\\pm|a|$。',
    shiftFunc: '這是「平移寫方程式」：左右平移動 $x$（右減左加），上下平移直接加減在最外面。',
    combineStd: '這是「正餘弦疊合」：$r$ 是兩係數的平方和開根號，$\\theta$ 由兩係數的正負與比值決定。',
    maxMin: '這是「$a\\sin x+b\\cos x$ 的最值」：疊合後振幅是 $\\sqrt{a^2+b^2}$，最大最小就是常數加減振幅。',
    basicEq: '這是「基本三角方程式」：先找一個參考解，再用單位圓的對稱性補上另一個。',
    periodOf: '這是「最小正週期」：先看是 $\\sin$、$\\cos$ 還是 $\\tan$，再看有沒有絕對值或平方讓週期減半。'
  };
  var L1_SOL = {};
  L1_SOL.degToRad = function (p) {
    var f = F(p.deg, 180), g = gcd(Math.abs(p.deg), 180);
    return ['$180^\\circ=\\pi$ ⟹ $1^\\circ=\\dfrac{\\pi}{180}$。', '$' + p.deg + '^\\circ=' + p.deg + '\\times\\dfrac{\\pi}{180}=\\dfrac{' + p.deg + '\\pi}{180}$。', '分子分母同除以 $' + g + '$：$\\dfrac{' + p.deg + '\\pi}{180}=' + piTex(f.n, f.d) + '$。'];
  };
  L1_SOL.radToDeg = function (p) {
    var red = ((p.deg % 360) + 360) % 360, n = (p.deg - red) / 360;
    return ['$\\pi=180^\\circ$ ⟹ $' + piTex(p.k, p.d) + '=' + piToDegTex(p.k, p.d) + '=' + p.deg + '^\\circ$。',
      (n === 0 ? '$' + p.deg + '^\\circ$ 已在 $[0^\\circ,360^\\circ)$ 內' : '$' + p.deg + '^\\circ' + (n > 0 ? '-' : '+') + Math.abs(n) + '\\times360^\\circ=' + red + '^\\circ$') + '，' + quadTxt(red) + '。'];
  };
  L1_SOL.arcArea = function (p) {
    var arc = F(p.r * p.k, p.d), area = F(p.r * p.r * p.k, 2 * p.d);
    return ['弧長 $s=r\\theta=' + p.r + '\\times' + piTex(p.k, p.d) + '=' + coefPi(arc) + '$。', '面積 $A=\\dfrac12r^2\\theta=\\dfrac12\\times' + p.r + '^2\\times' + piTex(p.k, p.d) + '=' + coefPi(area) + '$。'];
  };
  L1_SOL.sectorFromArc = function (p) {
    return ['$s=r\\theta$ ⟹ $\\theta=\\dfrac sr=\\dfrac{' + p.arc + '}{' + p.r + '}=' + p.th + '$（弧度）。', '面積 $A=\\dfrac12rs=\\dfrac12\\times' + p.r + '\\times' + p.arc + '=' + Fr.tex(F(p.r * p.arc, 2)) + '$。'];
  };
  L1_SOL.signQuad = function (p) {
    var qd = p.v < Math.PI / 2 ? 1 : p.v < Math.PI ? 2 : p.v < 3 * Math.PI / 2 ? 3 : 4;
    var rng = ['', '$0\\lt' + p.v + '\\lt\\dfrac{\\pi}{2}\\approx1.57$', '$\\dfrac{\\pi}{2}\\approx1.57\\lt' + p.v + '\\lt\\pi\\approx3.14$', '$\\pi\\approx3.14\\lt' + p.v + '\\lt\\dfrac{3\\pi}{2}\\approx4.71$', '$\\dfrac{3\\pi}{2}\\approx4.71\\lt' + p.v + '\\lt2\\pi\\approx6.28$'][qd];
    var signs = { 1: '全正', 2: '只有 $\\sin$ 為正', 3: '只有 $\\tan$ 為正', 4: '只有 $\\cos$ 為正' }[qd];
    return ['$' + p.v + '$ 弧度 $\\approx' + Math.round(p.v * 57.3) + '^\\circ$：' + rng + '，在第' + QN[qd] + '象限。', '第' + QN[qd] + '象限' + signs + '，所以 $\\' + p.fn + ' ' + p.v + '$ 為' + (p.sign > 0 ? '正' : '負') + '。'];
  };
  L1_SOL.specialValue = function (p) {
    var red = ((p.deg % 360) + 360) % 360, n = (p.deg - red) / 360, ref = refDeg(red), v = tv(p.deg)[p.fn], q = quadrant(red);
    var st = ['$' + piTex(p.k, p.d) + '=' + p.deg + '^\\circ$' + (n ? '，減掉 $' + n + '\\times360^\\circ$ 得 $' + red + '^\\circ$' : '') + '，' + quadTxt(red) + '。'];
    if (q) st.push('參考角 $' + ref + '^\\circ$：$\\' + p.fn + ref + '^\\circ=' + vTex(tv(ref)[p.fn]) + '$；第' + QN[q] + '象限的 $\\' + p.fn + '$ 為' + (v.c < 0 ? '負' : '正') + '，故 $\\' + p.fn + piTex(p.k, p.d) + '=' + vTex(v) + '$。');
    else st.push('終邊在坐標軸上，直接看單位圓上的點：$\\' + p.fn + red + '^\\circ=' + vTex(v) + '$。');
    return st;
  };
  L1_SOL.pointDef = function (p) {
    return ['$r=\\sqrt{x^2+y^2}=\\sqrt{' + absT(p.x) + '^2+' + absT(p.y) + '^2}=\\sqrt{' + (p.x * p.x + p.y * p.y) + '}=' + p.r + '$。', '$\\sin\\theta=\\dfrac yr=' + fracTex(p.y, p.r) + '$、$\\cos\\theta=\\dfrac xr=' + fracTex(p.x, p.r) + '$、$\\tan\\theta=\\dfrac yx=' + fracTex(p.y, p.x) + '$（正負號跟著坐標走）。'];
  };
  L1_SOL.fromSinQuad = function (p) {
    var given = p.give === 'sin' ? p.s : p.c, other = p.give === 'sin' ? 'cos' : 'sin', ov = p.give === 'sin' ? p.c : p.s;
    return ['$\\sin^2\\theta+\\cos^2\\theta=1$ ⟹ $\\' + other + '^2\\theta=1-\\left(' + fracTex(given, p.R) + '\\right)^2=\\dfrac{' + (p.R * p.R - given * given) + '}{' + (p.R * p.R) + '}$ ⟹ $|\\' + other + '\\theta|=' + fracTex(Math.abs(ov), p.R) + '$。',
      '$\\theta$ 在第' + QN[p.quad] + '象限，$\\' + other + '$ 為' + (ov > 0 ? '正' : '負') + '：$\\' + other + '\\theta=' + fracTex(ov, p.R) + '$。',
      '$\\tan\\theta=\\dfrac{\\sin\\theta}{\\cos\\theta}=' + fracTex(p.s, p.R) + '\\div' + negP(fracTex(p.c, p.R)) + '=' + fracTex(p.s, p.c) + '$。'];
  };
  L1_SOL.coterminal = function (p) {
    if (p.mode === 'deg') { var n = (p.deg - p.base) / 360; return ['$' + p.deg + '^\\circ' + (n > 0 ? '-' : '+') + Math.abs(n) + '\\times360^\\circ=' + p.base + '^\\circ$，落在 $[0^\\circ,360^\\circ)$ 內。', '$' + p.base + '^\\circ$ 在' + quadTxt(p.base) + '。']; }
    var m = (p.k - p.k0) / (2 * p.d);
    return ['$2\\pi=\\dfrac{' + 2 * p.d + '\\pi}{' + p.d + '}$：$' + piTex(p.k, p.d) + (m > 0 ? '-' : '+') + Math.abs(m) + '\\times2\\pi=' + piTex(p.k0, p.d) + '$，落在 $[0,2\\pi)$ 內。', '$' + piTex(p.k0, p.d) + '=' + (p.k0 * 180 / p.d) + '^\\circ$，在' + quadTxt(p.k0 * 180 / p.d) + '。'];
  };
  L1_SOL.reduceFormula = function (p) {
    var arg = { 180: p.m < 0 ? '\\pi-\\theta' : '\\pi+\\theta', 0: '-\\theta', 360: '2\\pi-\\theta', 90: p.m < 0 ? '\\dfrac{\\pi}{2}-\\theta' : '\\dfrac{\\pi}{2}+\\theta', 270: p.m < 0 ? '\\dfrac{3\\pi}{2}-\\theta' : '\\dfrac{3\\pi}{2}+\\theta' }[p.k];
    var odd = p.k % 180 === 90, q = quadrant(p.k + p.m * 30);
    return ['$' + arg + '$ 裡的 $' + (p.k === 0 ? '0' : piTex(p.k / 15, 12)) + '$ 是 $\\dfrac{\\pi}{2}$ 的' + (odd ? '奇數倍 ⟹ 函數名互換（$\\sin\\leftrightarrow\\cos$）' : '偶數倍 ⟹ 函數名不變') + '。',
      '把 $\\theta$ 當銳角，$' + arg + '$ 落在第' + QN[q] + '象限，$\\' + p.fn + '$ 在那裡為' + (p.ress < 0 ? '負' : '正') + '。',
      '所以 $\\' + p.fn + '\\left(' + arg + '\\right)=' + (p.ress < 0 ? '-' : '') + '\\' + p.resf + '\\theta$。'];
  };
  L1_SOL.sumExact = function (p) {
    var sp = p.deg === 15 ? [45, -30] : p.deg % 90 === 15 ? [p.deg - 45, 45] : [p.deg - 30, 30], A = sp[0], B = Math.abs(sp[1]), e = exact15(p.deg)[p.fn];
    var pm = sp[1] < 0 ? '-' : '+', mp = sp[1] < 0 ? '+' : '-';           /* 差角：sin、tan 分子用 −，cos、tan 分母用 + */
    var tA = tv(A), tB = tv(B), st, V = function (v) { return negP(vTex(v)); };
    if (p.fn === 'sin') st = '\\sin' + A + '^\\circ\\cos' + B + '^\\circ' + pm + '\\cos' + A + '^\\circ\\sin' + B + '^\\circ=' + V(tA.sin) + '\\cdot' + V(tB.cos) + pm + V(tA.cos) + '\\cdot' + V(tB.sin);
    else if (p.fn === 'cos') st = '\\cos' + A + '^\\circ\\cos' + B + '^\\circ' + mp + '\\sin' + A + '^\\circ\\sin' + B + '^\\circ=' + V(tA.cos) + '\\cdot' + V(tB.cos) + mp + V(tA.sin) + '\\cdot' + V(tB.sin);
    else st = '\\dfrac{\\tan' + A + '^\\circ' + pm + '\\tan' + B + '^\\circ}{1' + mp + '\\tan' + A + '^\\circ\\tan' + B + '^\\circ}=\\dfrac{' + V(tA.tan) + pm + V(tB.tan) + '}{1' + mp + V(tA.tan) + '\\cdot' + V(tB.tan) + '}';
    return ['$' + p.deg + '^\\circ=' + A + '^\\circ' + pm + B + '^\\circ$，兩個都是特殊角。', '$\\' + p.fn + p.deg + '^\\circ=' + st + '$。', '化簡' + (p.fn === 'tan' ? '（分母有根號就有理化）' : '') + '得 $' + e + '$。'];
  };
  L1_SOL.cosDiffQuad = function (p) {
    var w = p.which, f = w.slice(0, 3), sg = w.slice(3);
    var expr = '\\' + f + '(\\alpha' + sg + '\\beta)';
    var formula = f === 'sin' ? '\\sin\\alpha\\cos\\beta' + sg + '\\cos\\alpha\\sin\\beta' : '\\cos\\alpha\\cos\\beta' + (sg === '+' ? '-' : '+') + '\\sin\\alpha\\sin\\beta';
    var P = function (n, d) { return '\\left(' + fracTex(n, d) + '\\right)'; };
    var sub = f === 'sin' ? P(p.s1, p.R1) + P(p.c2, p.R2) + sg + P(p.c1, p.R1) + P(p.s2, p.R2) : P(p.c1, p.R1) + P(p.c2, p.R2) + (sg === '+' ? '-' : '+') + P(p.s1, p.R1) + P(p.s2, p.R2);
    return ['補 $\\cos\\alpha$：$|\\cos\\alpha|=\\sqrt{1-\\left(' + fracTex(p.s1, p.R1) + '\\right)^2}=' + fracTex(Math.abs(p.c1), p.R1) + '$，$\\alpha$ 在第' + QN[p.q1] + '象限 ⟹ $\\cos\\alpha=' + fracTex(p.c1, p.R1) + '$。',
      '補 $\\sin\\beta$：$|\\sin\\beta|=\\sqrt{1-\\left(' + fracTex(p.c2, p.R2) + '\\right)^2}=' + fracTex(Math.abs(p.s2), p.R2) + '$，$\\beta$ 在第' + QN[p.q2] + '象限 ⟹ $\\sin\\beta=' + fracTex(p.s2, p.R2) + '$。',
      '$' + expr + '=' + formula + '=' + sub + '=' + fracTex(p.num, p.R1 * p.R2) + '$。'];
  };
  L1_SOL.tanSum = function (p) {
    var t1 = F(p.p1[0], p.p1[1]), t2 = F(p.p2[0], p.p2[1]), sg = p.sgn, num = sg > 0 ? Fr.add(t1, t2) : Fr.sub(t1, t2), den = Fr.sub(F(1), Fr.mul(F(sg), Fr.mul(t1, t2)));
    return ['$\\tan(\\alpha' + (sg > 0 ? '+' : '-') + '\\beta)=\\dfrac{\\tan\\alpha' + (sg > 0 ? '+' : '-') + '\\tan\\beta}{1' + (sg > 0 ? '-' : '+') + '\\tan\\alpha\\tan\\beta}$。',
      '分子 $=' + Fr.tex(t1, false) + (sg > 0 ? '+' : '-') + '\\left(' + Fr.tex(t2, false) + '\\right)=' + Fr.tex(num, false) + '$，分母 $=1' + (sg > 0 ? '-' : '+') + '\\left(' + Fr.tex(t1, false) + '\\right)\\left(' + Fr.tex(t2, false) + '\\right)=' + Fr.tex(den, false) + '$。',
      '相除：$' + Fr.tex(num, false) + '\\div' + negP(Fr.tex(den, false)) + '=' + Fr.tex(F(p.val[0], p.val[1])) + '$。'];
  };
  L1_SOL.doubleFromSin = function (p) {
    var other = p.give === 'sin' ? 'cos' : 'sin', ov = p.give === 'sin' ? p.c : p.s, gv = p.give === 'sin' ? p.s : p.c;
    return ['補另一個：$|\\' + other + '\\theta|=\\sqrt{1-\\left(' + fracTex(gv, p.R) + '\\right)^2}=' + fracTex(Math.abs(ov), p.R) + '$，第' + QN[p.quad] + '象限 ⟹ $\\' + other + '\\theta=' + fracTex(ov, p.R) + '$。',
      '$\\sin2\\theta=2\\sin\\theta\\cos\\theta=2\\cdot' + negP(fracTex(p.s, p.R)) + '\\cdot' + negP(fracTex(p.c, p.R)) + '=' + Fr.tex(F(2 * p.s * p.c, p.R * p.R)) + '$。',
      '$\\cos2\\theta=\\cos^2\\theta-\\sin^2\\theta=\\dfrac{' + (p.c * p.c) + '}{' + (p.R * p.R) + '}-\\dfrac{' + (p.s * p.s) + '}{' + (p.R * p.R) + '}=' + Fr.tex(F(p.c * p.c - p.s * p.s, p.R * p.R)) + '$。'];
  };
  L1_SOL.halfFromCos = function (p) {
    var lo = (p.quad - 1) * 90, hi = p.quad * 90, fn = p.askCos ? '\\cos' : '\\sin', pm = p.askCos ? '+' : '-';
    var inner = Fr.div(p.askCos ? Fr.add(F(1), F(p.cosn, p.cosd)) : Fr.sub(F(1), F(p.cosn, p.cosd)), F(2));
    return ['半角公式：$' + fn + '^2\\dfrac{\\theta}{2}=\\dfrac{1' + pm + '\\cos\\theta}{2}=\\dfrac{1' + pm + '\\left(' + fracTex(p.cosn, p.cosd) + '\\right)}{2}=' + Fr.tex(inner) + '$。',
      '$' + piTex(lo / 15, 12) + '\\lt\\theta\\lt' + piTex(hi / 15, 12) + '$ ⟹ $' + piTex(lo / 30, 12) + '\\lt\\dfrac{\\theta}{2}\\lt' + piTex(hi / 30, 12) + '$，在第' + QN[quadrant(lo / 2 + 1)] + '象限，$' + fn + '$ 為' + (p.num < 0 ? '負' : '正') + '。',
      '開根號並取正負：$' + fn + '\\dfrac{\\theta}{2}=' + fracTex(p.num, p.den) + '$。'];
  };
  L1_SOL.ampPeriod = function (p) {
    var per = p.b === 0.5 ? '4\\pi' : p.b === 1 ? '2\\pi' : p.b === 2 ? '\\pi' : p.b === 4 ? '\\dfrac{2\\pi}{4}=\\dfrac{\\pi}{2}' : '\\dfrac{2\\pi}{' + p.b + '}';
    return ['$y=a\\sin(bx+c)+d$ 型：$a=' + p.a + '$、$b=' + (p.b === 0.5 ? '\\dfrac12' : p.b) + '$、$d=' + p.d + '$（括號裡的相位不影響這四個量）。',
      '振幅 $=|a|=' + Math.abs(p.a) + '$；週期 $=\\dfrac{2\\pi}{|b|}=' + per + '$。',
      '$\\sin$ 的值在 $-1$ 到 $1$ 之間 ⟹ 最大值 $=d+|a|=' + p.d + '+' + Math.abs(p.a) + '=' + (p.d + Math.abs(p.a)) + '$，最小值 $=d-|a|=' + (p.d - Math.abs(p.a)) + '$。'];
  };
  L1_SOL.shiftFunc = function (p) {
    var hor = p.hs > 0 ? '右' : '左', ver = p.vs > 0 ? '上' : '下';
    return ['向' + hor + '平移 $' + piTex(1, p.hk) + '$：把 $x$ 換成 $x' + (p.hs > 0 ? '-' : '+') + piTex(1, p.hk) + '$（右減左加），得 $y=\\' + p.fn + '\\left(x' + (p.hs > 0 ? '-' : '+') + piTex(1, p.hk) + '\\right)$。',
      '向' + ver + '平移 $' + Math.abs(p.vs) + '$：整個函數 $' + (p.vs > 0 ? '+' : '-') + Math.abs(p.vs) + '$，得 $y=\\' + p.fn + '\\left(x' + (p.hs > 0 ? '-' : '+') + piTex(1, p.hk) + '\\right)' + signed(p.vs) + '$。'];
  };
  L1_SOL.combineStd = function (p) {
    var aT = combTerm(p.aSign * (p.aIsSqrt3 ? 3 : 1), p.m, true), bT = combTerm(p.bSign * (p.bIsSqrt3 ? 3 : 1), p.m, true), RT = sqrtTex(p.R2);
    var a2 = p.m * p.m * (p.aIsSqrt3 ? 3 : 1), b2 = p.m * p.m * (p.bIsSqrt3 ? 3 : 1);
    return ['$a=' + aT + '$、$b=' + bT + '$，$r=\\sqrt{a^2+b^2}=\\sqrt{' + a2 + '+' + b2 + '}=' + RT + '$。',
      '$\\cos\\theta=\\dfrac ar=\\dfrac{' + aT + '}{' + RT + '}$、$\\sin\\theta=\\dfrac br=\\dfrac{' + bT + '}{' + RT + '}$，兩個符號決定 $\\theta$ 的象限：$\\cos\\theta$ 為' + (p.aSign > 0 ? '正' : '負') + '、$\\sin\\theta$ 為' + (p.bSign > 0 ? '正' : '負') + '。',
      '在 $-\\pi\\lt\\theta\\le\\pi$ 內符合的角是 $\\theta=' + (p.thn < 0 ? '-' : '') + piTex(Math.abs(p.thn), p.thd) + '$，故 $y=' + RT + '\\sin\\left(x' + (p.thn < 0 ? '-' : '+') + piTex(Math.abs(p.thn), p.thd) + '\\right)$。'];
  };
  L1_SOL.maxMin = function (p) {
    return ['$a\\sin x+b\\cos x$ 的部分疊合成 $\\sqrt{a^2+b^2}\\,\\sin(x+\\theta)$，振幅 $=\\sqrt{' + absT(p.a) + '^2+' + absT(p.b) + '^2}=\\sqrt{' + (p.a * p.a + p.b * p.b) + '}=' + p.R + '$。',
      '$\\sin(x+\\theta)$ 在 $-1$ 到 $1$ 之間 ⟹ $f(x)$ 在 $' + p.d + '-' + p.R + '$ 到 $' + p.d + '+' + p.R + '$ 之間。', '最大值 $' + (p.d + p.R) + '$，最小值 $' + (p.d - p.R) + '$。'];
  };
  L1_SOL.basicEq = function (p) {
    var val = { c: p.c, r: p.r, d: p.d }, vT = vTex(val), ks = p.ks;
    if (!ks.length) return ['$\\' + p.fn + ' x=' + vT + '$ 無解。'];
    var st = ['$\\' + p.fn + '$ 值為 $' + vT + '$' + (p.c === 0 ? '' : '，絕對值 $' + vTex({ c: Math.abs(p.c), r: p.r, d: p.d }) + '$ 對應的參考角是 $' + refDeg(ks[0] * 15) + '^\\circ=' + piTex(refDeg(ks[0] * 15) / 15, 12) + '$') + '。',
      '值為' + (p.c < 0 ? '負' : p.c > 0 ? '正' : '零') + ' ⟹ ' + (function () { var qs = [], axis = false; ks.forEach(function (k) { var q = quadrant(k * 15); if (!q) axis = true; else if (qs.indexOf(QN[q]) < 0) qs.push(QN[q]); }); return (qs.length ? '終邊在第' + qs.join('、') + '象限' : '') + (axis ? (qs.length ? '（另有落在坐標軸上的解）' : '終邊在坐標軸上') : ''); })() + '，在 $[0,2\\pi)$ 內' + (ks.length > 1 ? '有 ' + ks.length + ' 個解' : '只有 1 個解') + '。'];
    st.push('$x=' + ks.map(function (k) { return piTex(k, 12); }).join(',\\ ') + '$。');
    return st;
  };
  L1_SOL.periodOf = function (p) {
    var bT = p.b === 0.5 ? '\\dfrac12' : String(p.b), P = F(p.P[0], p.P[1]), PT = P.n === P.d ? '\\pi' : Fr.tex(P) + '\\pi';
    var why = { sin: '$\\sin u$ 的週期是 $2\\pi$', cos: '$\\cos u$ 的週期是 $2\\pi$', tan: '$\\tan u$ 的週期是 $\\pi$', abssin: '$|\\sin u|$ 把負半波翻上來，週期由 $2\\pi$ 減半成 $\\pi$', sin2: '$\\sin^2u=\\dfrac{1-\\cos2u}{2}$，週期由 $2\\pi$ 減半成 $\\pi$' }[p.kind];
    var base = (p.kind === 'sin' || p.kind === 'cos') ? '2\\pi' : '\\pi';
    if (p.b === 1) return [why + '。', '這裡 $u=x$（$b=1$），週期不必再除：答案就是 $' + PT + '$。'];
    return [why + '。', '$u=' + bT + 'x$，$x$ 的週期是 $u$ 的週期除以 $|b|$：$\\dfrac{' + base + '}{' + bT + '}=' + PT + '$。'];
  };

  /* ── 2026-09-28 擴充：新 L1 四型的第一層提示與解題步驟 ── */
  L1_H1.sumReverse = '這是「和差角公式倒過來用」：先認出是 $\\sin(\\alpha\\pm\\beta)$、$\\cos(\\alpha\\pm\\beta)$ 還是 $\\tan(\\alpha\\pm\\beta)$ 的展開式，再合回一個角。';
  L1_H1.doubleReverse = '這是「倍角公式倒過來用」：式子裡同一個角出現兩次（或平方），把它合成兩倍角的一個函數。';
  L1_H1.symAxis = '這是「對稱軸、對稱中心」：對稱軸通過最高點、最低點，對稱中心在中線上；令括號等於那些位置的角，解出 $x$。';
  L1_H1.trigCompare = '這是「大小比較」：用誘導公式把每個角搬到同一段函數單調的區間，再比較搬過去的角。';

  L1_SOL.sumReverse = function (p) {
    var A = dg(p.A), B = dg(p.B), op = p.op, v = vTex(tv(p.Td)[p.fn]);
    var fm = { sin: '\\sin(\\alpha' + op + '\\beta)=\\sin\\alpha\\cos\\beta' + op + '\\cos\\alpha\\sin\\beta',
      cos: '\\cos(\\alpha' + op + '\\beta)=\\cos\\alpha\\cos\\beta' + (op === '+' ? '-' : '+') + '\\sin\\alpha\\sin\\beta',
      tan: '\\tan(\\alpha' + op + '\\beta)=\\dfrac{\\tan\\alpha' + op + '\\tan\\beta}{1' + (op === '+' ? '-' : '+') + '\\tan\\alpha\\tan\\beta}' }[p.fn];
    return ['對照公式 $' + fm + '$' + (p.sw ? '（乘法可以交換順序，' + (p.fn === 'sin' ? '兩項也' : '加法也') + '可以交換）' : '') + '，題目正是 $\\alpha=' + A + '$、$\\beta=' + B + '$ 的展開式。',
      '合回一個角：原式 $=\\' + p.fn + '(' + A + op + B + ')=\\' + p.fn + dg(p.Td) + '$。',
      '$\\' + p.fn + dg(p.Td) + '=' + v + '$。'];
  };

  L1_SOL.doubleReverse = function (p) {
    var rad = p.rad, th = rad ? piTex(p.k, 24) : dg(7.5 * p.k), two = rad ? piTex(2 * p.k, 24) : dg(15 * p.k);
    var f2 = p.form <= 1 ? 'sin' : p.form === 5 ? 'tan' : 'cos', v = tv(15 * p.k)[f2], half = p.form === 1;
    var id = ['2\\sin\\theta\\cos\\theta=\\sin2\\theta', '\\sin\\theta\\cos\\theta=\\dfrac12\\sin2\\theta', '\\cos^2\\theta-\\sin^2\\theta=\\cos2\\theta', '1-2\\sin^2\\theta=\\cos2\\theta', '2\\cos^2\\theta-1=\\cos2\\theta',
      '\\dfrac{2\\tan\\theta}{1-\\tan^2\\theta}=\\tan2\\theta', '\\cos^4\\theta-\\sin^4\\theta=(\\cos^2\\theta+\\sin^2\\theta)(\\cos^2\\theta-\\sin^2\\theta)=\\cos^2\\theta-\\sin^2\\theta=\\cos2\\theta'][p.form];
    var st = ['倍角公式倒過來看：$' + id + '$，這裡 $\\theta=' + th + '$。',
      '原式 $=' + (half ? '\\dfrac12' : '') + '\\' + f2 + '\\left(2\\times' + th + '\\right)=' + (half ? '\\dfrac12' : '') + '\\' + f2 + (rad ? two : ' ' + two) + '$。'];
    if (half) st.push('$\\sin' + (rad ? two : ' ' + two) + '=' + vTex(v) + '$，所以原式 $=\\dfrac12\\times' + negP(vTex(v)) + '=' + surdOver(v.c, v.r, 2 * v.d) + '$。');
    else st.push('$\\' + f2 + (rad ? two : ' ' + two) + '=' + vTex(v) + '$。');
    return st;
  };

  L1_SOL.symAxis = function (p) {
    var bF = F(p.b[0], p.b[1]), bT = bF.d === 2 ? '\\dfrac{x}{2}' : (bF.n === 1 ? 'x' : bF.n + 'x'), isAxis = p.t % 2 === 0;
    var inner = bT + (p.cK > 0 ? '+' : '-') + piTex(Math.abs(p.cK), 12);
    var u0 = ((p.fn === 'sin') === isAxis) ? 6 : 0, cond = u0 === 6 ? '\\dfrac{\\pi}{2}+k\\pi' : 'k\\pi';
    var st = F(p.st[0], p.st[1]), x0 = F(p.x0[0], p.x0[1]), raw = Fr.div(F(u0 - p.cK, 12), bF);
    var gen = (x0.n === 0 ? '' : piTex(x0.n, x0.d) + '+') + kStepTex(st), rawT = (raw.n === 0 ? '' : piTex(raw.n, raw.d) + '+') + kStepTex(st);
    var sp = x0.n === 0 ? st : x0;
    var why = isAxis ? '對稱軸通過最高點、最低點，那裡 $\\' + p.fn + '$ 的值是 $\\pm1$' : '對稱中心在中線 $y=' + p.d + '$ 上，那裡 $\\' + p.fn + '$ 的值是 $0$';
    var out = [why + '：令 $' + inner + '=' + cond + '$（$k$ 為整數）。',
      '移項再除以 $' + (bF.d === 2 ? '\\dfrac12' : bF.n) + '$：$x=' + rawT + '$' + (Fr.eq(raw, x0) ? '' : '，常數項調到 $0$ 與半週期 $' + piTex(st.n, st.d) + '$ 之間：$x=' + gen + '$') + '。'];
    if (p.t === 0) out.push('所有對稱軸：$x=' + gen + '$，$k$ 為整數。');
    else if (p.t === 1) out.push('所有對稱中心：$\\left(' + gen + ',' + p.d + '\\right)$，$k$ 為整數。');
    else if (p.t === 2) out.push('取 $k$ 讓 $x$ 是最小的正數：$x=' + piTex(sp.n, sp.d) + '$。');
    else out.push('取 $k$ 讓 $x$ 是最小的正數，對稱中心是 $\\left(' + piTex(sp.n, sp.d) + ',' + p.d + '\\right)$。');
    return out;
  };

  L1_SOL.trigCompare = function (p) {
    var nm = ['a', 'b', 'c'], m = p.vs.map(function (v) { return cmpMap(p.fn, v); });
    var where = { sin: '$\\left[-\\dfrac{\\pi}{2},\\dfrac{\\pi}{2}\\right]$，$\\sin$ 在這裡遞增', cos: '$[0,\\pi]$，$\\cos$ 在這裡遞減', tan: '$\\left(-\\dfrac{\\pi}{2},\\dfrac{\\pi}{2}\\right)$，$\\tan$ 在這裡遞增' }[p.fn];
    var st = ['$\\pi\\approx3.14$。目標區間是 ' + where + '。'];
    st.push(m.map(function (x, i) { return '$' + nm[i] + '$：' + x[1]; }).join('；') + '。');
    var byW = [0, 1, 2].sort(function (i, j) { return m[j][0] - m[i][0]; });
    var wOrd = byW.map(function (i) { return nm[i]; });
    st.push('搬過去的角由大到小是 $' + wOrd.join('$、$') + '$ 的；' + (p.fn === 'cos' ? '$\\cos$ 遞減，角越大值越小，順序反過來' : '函數遞增，角越大值越大，順序不變') + '：$' + nm[p.ord[0]] + '\\gt ' + nm[p.ord[1]] + '\\gt ' + nm[p.ord[2]] + '$。');
    return st;
  };

  var META_L1 = [['degToRad', '度 → 弧度'], ['radToDeg', '弧度 → 度・判象限'], ['arcArea', '弧長與扇形面積'], ['sectorFromArc', '由弧長反推圓心角'], ['signQuad', '弧度值的正負判斷'], ['specialValue', '特殊角的函數值'], ['pointDef', '終邊過一點求三角函數'], ['fromSinQuad', '已知一個函數值求另兩個'], ['coterminal', '同界角與象限'], ['reduceFormula', '誘導公式化簡'],
    ['sumExact', '15° 倍數的精確值'], ['cosDiffQuad', '和差角公式求值'], ['tanSum', 'tan 的和差角'], ['sumReverse', '和差角公式逆用'], ['doubleFromSin', '二倍角求值'], ['doubleReverse', '倍角公式逆用'], ['halfFromCos', '半角求值'],
    ['ampPeriod', '振幅・週期・最大最小'], ['shiftFunc', '平移後的方程式'], ['combineStd', '正餘弦疊合（標準組合）'], ['maxMin', 'a sin x + b cos x 的最值'], ['basicEq', '基本三角方程式'], ['periodOf', '最小正週期'], ['symAxis', '對稱軸與對稱中心'], ['trigCompare', '三角函數值比大小']];

  /* ══════════════════════════════════════════════════════════
     L2　中等（22 型；2026-09-28 依段考頻率補 6 型）
     ══════════════════════════════════════════════════════════ */
  var L2 = {};

  L2.sectorSys = function (r) {
    var r1 = r.int(2, 6), r2 = r.int(r1 + 1, 9);
    var P = 2 * (r1 + r2), S = r1 * r2;
    var th1 = F(2 * r2, r1), th2 = F(2 * r1, r2);
    var bad1 = Fr.toNum(th1) >= 2 * Math.PI;                           /* 圓心角 ≥2π 就不是扇形：r=r1 那組要捨去（th2=2r1/r2<2 一定合法） */
    var pair2 = '\\left(' + r2 + ',' + Fr.tex(th2) + '\\right)';
    return { q: '一扇形的周長為 ' + T(P) + '、面積為 ' + T(S) + '，求其半徑與圓心角（弧度）。',
      a: bad1 ? T('(r,\\theta)=' + pair2) + '（另一根 ' + T('r=' + r1) + ' 時 ' + T('\\theta=' + Fr.tex(th1) + '\\gt2\\pi') + '，不是扇形，不合）'
              : T('(r,\\theta)=\\left(' + r1 + ',' + Fr.tex(th1) + '\\right)') + ' 或 ' + T(pair2),
      h: '設弧長 $s$：$2r+s=' + P + '$、$\\dfrac12rs=' + S + '$，消去 $s$ 得 $r$ 的二次方程；兩個根都要檢查圓心角 $\\theta=\\dfrac sr$ 有沒有小於 $2\\pi$。', p: { P: P, S: S, r1: r1, r2: r2, valid1: !bad1 } };
  };
  L2.sectorMax = function (r) {
    var kind = r.pick(['perim', 'perim', 'perimFrac', 'area', 'areaP']);
    if (kind === 'perim' || kind === 'perimFrac') {
      var L = kind === 'perim' ? 4 * r.int(3, 10) : r.pick([10, 14, 18, 22, 26, 30, 6]);
      var rr = F(L, 4), A = F(L * L, 16);
      var ask = r.pick(['both', 'area', 'r']);
      var q = '用長 ' + T(L) + ' 的鐵絲圍成一個扇形，圓心角為 ' + T('\\theta') + ' 弧度。' + (ask === 'both' ? '當 ' + T('\\theta') + ' 為何時面積最大？最大面積為何？' : ask === 'area' ? '求此扇形面積的最大值。' : '面積最大時，半徑為何？');
      var a = ask === 'both' ? T('\\theta=2') + '（此時 ' + T('r=' + Fr.tex(rr)) + '），最大面積 ' + T(Fr.tex(A)) : ask === 'area' ? '最大面積 ' + T(Fr.tex(A)) + '（' + T('\\theta=2') + '）' : T('r=' + Fr.tex(rr)) + '（' + T('\\theta=2') + '）';
      return { q: q, a: a, h: '$2r+r\\theta=' + L + '$ ⟹ 弧長 $s=' + L + '-2r$，面積 $=\\dfrac12rs=\\dfrac12r(' + L + '-2r)$ 是 $r$ 的二次函數，頂點在 $r=\\dfrac{' + L + '}{4}$，此時 $s=2r$、$\\theta=2$。', p: { kind: kind, L: L, ask: ask, r: [rr.n, rr.d], A: [A.n, A.d] } };
    }
    var k = r.int(2, 9), S = k * k;                                  /* 面積固定 S=k²：周長最小 4k，r=k，θ=2 */
    if (kind === 'area') return { q: '若一扇形的面積固定為 ' + T(S) + '，求其周長的最小值，並求此時的圓心角（弧度）。', a: '周長最小 ' + T(4 * k) + '，此時 ' + T('r=' + k) + '、' + T('\\theta=2'), h: '周長 $=2r+\\dfrac{2S}{r}=2r+\\dfrac{' + 2 * S + '}{r}\\ge2\\sqrt{2r\\cdot\\dfrac{' + 2 * S + '}{r}}$（算幾不等式），等號在 $2r=\\dfrac{' + 2 * S + '}{r}$ 即 $r=' + k + '$。', p: { kind: kind, S: S, k: k } };
    return { q: '一扇形的面積為 ' + T(S) + '，當它的周長最小時，求此扇形的弧長。', a: '弧長 ' + T(2 * k) + '（周長最小 ' + T(4 * k) + '，' + T('r=' + k) + '）', h: '周長 $=2r+s$ 而 $\\dfrac12rs=' + S + '$ ⟹ $s=\\dfrac{' + 2 * S + '}{r}$，算幾不等式 $2r+\\dfrac{' + 2 * S + '}{r}\\ge' + 4 * k + '$，等號時 $2r=s$。', p: { kind: kind, S: S, k: k } };
  };
  L2.coneShortest = function (r) {
    var rr = r.int(1, 3), mult = r.pick([6, 4, 3]), l = rr * mult;          /* 展開角 2π·rr/l = π/3, π/2, 2π/3 */
    var dd = r.pick([l / 2, l / 3, l / 4, 2 * l / 3].filter(function (v) { return Number.isInteger(v) && v < l; }));
    var cosA = { 6: 0.5, 4: 0, 3: -0.5 }[mult];
    var d2 = l * l + dd * dd - 2 * l * dd * cosA;
    return { q: '一直圓錐的底面半徑為 ' + T(rr) + '、母線長為 ' + T(l) + '。' + T('C') + ' 為底面圓周上一點，' + T('D') + ' 在母線 ' + T('\\overline{AC}') + ' 上（' + T('A') + ' 為頂點）且 ' + T('\\overline{AD}=' + dd) + '。一隻螞蟻從 ' + T('C') + ' 沿錐面繞一周爬到 ' + T('D') + '，求最短路徑長。',
      a: T(sqrtTex(d2)), h: '側面展開是扇形：半徑 $=$ 母線，圓心角 $=\\dfrac{2\\pi r}{l}=' + piTex(2 * rr * 12 / l, 12) + '$；最短路徑是展開圖上的線段，用餘弦定理。', p: { rr: rr, l: l, dd: dd, d2: d2 } };
  };
  /* sinθ+cosθ=k：真實 (s,c) 從三元組取，θ 的範圍要能決定 s-c 的正負 */
  L2.sumProd = function (r) {
    var t = r.pick(TRIPLES), R = t[2];
    var pool = [];   /* [s, c, 範圍文字(π/4 單位), s-c 的正負由範圍決定] */
    pool.push([t[0], t[1], t[0] > t[1] ? [1, 2] : [0, 1]]);      /* 第一象限 */
    pool.push([t[0], -t[1], [2, 4]]);                                /* 第二象限 */
    pool.push([-t[0], -t[1], Math.abs(t[0]) < Math.abs(t[1]) ? [4, 5] : [5, 6]]);   /* 第三象限 */
    pool.push([-t[0], t[1], [6, 8]]);                                /* 第四象限 */
    var pk = r.pick(pool), s = pk[0], c = pk[1], rg = pk[2];
    var k = F(s + c, R), sc = F(s * c, R * R), smc = F(s - c, R), cube = Fr.mul(F(s * s * s + c * c * c, R * R * R), F(1));
    return { q: '已知 ' + T('\\sin\\theta+\\cos\\theta=' + Fr.tex(k)) + '，且 ' + T(piTex(rg[0], 4) + '\\lt\\theta\\lt' + piTex(rg[1], 4)) + '。求 (1) ' + T('\\sin\\theta\\cos\\theta') + '　(2) ' + T('\\sin\\theta-\\cos\\theta') + '　(3) ' + T('\\sin^3\\theta+\\cos^3\\theta') + '。',
      a: '(1) ' + T(Fr.tex(sc)) + '　(2) ' + T(Fr.tex(smc)) + '　(3) ' + T(Fr.tex(cube)),
      h: '平方：$1+2\\sin\\theta\\cos\\theta=k^2$；$(\\sin\\theta-\\cos\\theta)^2=1-2\\sin\\theta\\cos\\theta$，正負由 $\\theta$ 的範圍決定；立方和用 $(s+c)^3-3sc(s+c)$。', p: { s: s, c: c, R: R, rg: rg } };
  };
  L2.quadRootCos2 = function (r) {
    var sv = r.pick([[1, 3], [-1, 3], [2, 3], [-2, 3], [1, 2], [-1, 2], [3, 4], [-3, 4], [1, 4], [-1, 4], [2, 5], [-2, 5], [3, 5], [-3, 5], [4, 5], [-4, 5]]);
    var p = sv[0], q = sv[1], u = r.pick([2, -2, 3, -3, 4, -4, 5]);
    /* (q x - p)(x - u) = q x² - (qu + p) x + p u */
    var B = -(q * u + p), C = p * u;
    var poly = q + 'x^2' + (B === 0 ? '' : (B > 0 ? '+' : '-') + (Math.abs(B) === 1 ? '' : Math.abs(B)) + 'x') + (C === 0 ? '' : signed(C));
    var cos2 = Fr.sub(F(1), F(2 * p * p, q * q));
    var fn = r.pick(['sin', 'cos']);
    var ans = fn === 'sin' ? cos2 : Fr.sub(F(2 * p * p, q * q), F(1));   /* cosθ 為根時 cos2θ=2cos²θ-1 */
    return { q: '若 ' + T('\\' + fn + '\\theta') + ' 為方程式 ' + T(poly + '=0') + ' 的一根，求 ' + T('\\cos2\\theta') + '。', a: T('\\cos2\\theta=' + Fr.tex(ans)),
      h: '先解方程式，只有 $|$根$|\\le1$ 的那個能當 $' + '\\' + fn + '\\theta$；再用 $\\cos2\\theta=1-2\\sin^2\\theta=2\\cos^2\\theta-1$。', p: { fn: fn, p: p, q: q, u: u, ans: [ans.n, ans.d] } };
  };
  L2.tanQuad = function (r) {
    var b = r.pick([-7, -5, -3, -2, 2, 3, 4, 5, 6]), mode = r.pick(['fwd', 'inv']);
    if (mode === 'fwd') {
      var a = r.int(1, 9) * r.sign(), g1 = 0;
      while (a * a - 4 * b <= 0 && g1++ < 60) a = r.int(1, 9) * r.sign();   /* 判別式要 >0：tanα、tanβ 必須是實數 */
      if (a * a - 4 * b <= 0) b = -Math.abs(b);
      var val = F(a, 1 - b);
      return { q: '若 ' + T('\\tan\\alpha') + '、' + T('\\tan\\beta') + ' 為方程式 ' + T('x^2' + (a > 0 ? '-' : '+') + (Math.abs(a) === 1 ? '' : Math.abs(a)) + 'x' + signed(b) + '=0') + ' 的兩根，求 ' + T('\\tan(\\alpha+\\beta)') + '。',
        a: T('\\tan(\\alpha+\\beta)=' + Fr.tex(val)), h: '根與係數：$\\tan\\alpha+\\tan\\beta=$ 兩根和、$\\tan\\alpha\\tan\\beta=$ 兩根積，代入 $\\dfrac{\\text{和}}{1-\\text{積}}$。', p: { mode: mode, a: a, b: b, val: [val.n, val.d] } };
    }
    var tv_ = F(r.int(1, 5) * r.sign(), r.pick([1, 2, 3])), aF = Fr.mul(tv_, F(1 - b)), g2 = 0;
    while (aF.n * aF.n - 4 * b * aF.d * aF.d <= 0 && g2++ < 60) { tv_ = F(r.int(1, 5) * r.sign(), r.pick([1, 2, 3])); aF = Fr.mul(tv_, F(1 - b)); }   /* 判別式 a²−4b 要 >0 */
    if (aF.n * aF.n - 4 * b * aF.d * aF.d <= 0) { b = -Math.abs(b); aF = Fr.mul(tv_, F(1 - b)); }
    return { q: '若 ' + T('x^2-ax' + signed(b) + '=0') + ' 的兩根為 ' + T('\\tan\\alpha') + '、' + T('\\tan\\beta') + '，且 ' + T('\\tan(\\alpha+\\beta)=' + Fr.tex(tv_)) + '，求 ' + T('a') + '。',
      a: T('a=' + Fr.tex(aF)), h: '$\\tan(\\alpha+\\beta)=\\dfrac{a}{1-b}$，解 $a$。', p: { mode: mode, b: b, t: [tv_.n, tv_.d], a: [aF.n, aF.d] } };
  };
  L2.systemSquare = function (r) {
    var guard = 0;
    while (guard++ < 80) {
      var p = r.int(1, 5), m = r.int(-(p + 1), p + 1), n = r.int(-(p + 1), p + 1), form = r.pick(['A+B', 'A+B', 'A-B', 'A+B-']);
      if (m === 0 && n === 0) continue;
      var S2 = m * m + n * n, rho = Math.sqrt(S2);
      if (Math.abs(rho - p) > 1 - 1e-9 || rho + p < 1 + 1e-9) continue;            /* 要真的有解且不相切：半徑 p 的圓與單位圓交於兩點 */
      var num = S2 - 1 - p * p, c = form === 'A+B-' ? F(-num, 2 * p) : F(num, 2 * p);
      if (Math.abs(Fr.toNum(c)) > 1) continue;
      var pT = p === 1 ? '' : String(p);
      var eq = form === 'A+B' ? '\\cos A+' + pT + '\\cos B=' + m + '\\\\ \\sin A-' + pT + '\\sin B=' + n
             : form === 'A-B' ? '\\cos A+' + pT + '\\cos B=' + m + '\\\\ \\sin A+' + pT + '\\sin B=' + n
             : '\\cos A-' + pT + '\\cos B=' + m + '\\\\ \\sin A+' + pT + '\\sin B=' + n;
      var ask = form === 'A-B' ? '\\cos(A-B)' : '\\cos(A+B)';
      return { q: '已知 ' + T('\\begin{cases}' + eq + '\\end{cases}') + '，求 ' + T(ask) + '。',
        a: T(ask + '=' + Fr.tex(c)), h: '兩式平方相加：$\\cos^2A+\\sin^2A=1$、$' + (p === 1 ? '' : p * p) + '(\\cos^2B+\\sin^2B)=' + p * p + '$，交叉項合成 $' + (form === 'A+B-' ? '-' : '') + 2 * p + ask + '$：$' + (m * m + n * n) + '=1+' + p * p + (form === 'A+B-' ? '-' : '+') + 2 * p + ask + '$。', p: { p: p, m: m, n: n, form: form, c: [c.n, c.d] } };
    }
    return L2.systemSquare(makeRng(r.int(1, 1e6)));
  };
  L2.halfFromCos2x = function (r) {
    var t = r.pick(TRIPLES), qd = r.pick([1, 2, 3, 4]), s = (qd <= 2 ? 1 : -1) * t[0], R = t[2];
    var cos2 = Fr.sub(F(1), F(2 * s * s, R * R));
    var lo = (qd - 1) * 6, hi = qd * 6;   /* π/12 單位 */
    var val2 = F(R - s, R);               /* (sin(x/2)-cos(x/2))² = 1 - sin x */
    var sgn = qd === 1 ? -1 : 1;
    var ansT = (sgn < 0 ? '-' : '') + surdOver(1, val2.n * val2.d, val2.d);
    return { q: '已知 ' + T('\\cos2x=' + Fr.tex(cos2)) + '，且 ' + T(piTex(lo, 12) + '\\lt x\\lt' + piTex(hi, 12)) + '，求 ' + T('\\sin\\dfrac{x}{2}-\\cos\\dfrac{x}{2}') + ' 之值。',
      a: T(ansT), h: '先由 $\\cos2x=1-2\\sin^2x$ 求 $\\sin x$（正負看 $x$ 的象限）；再用 $\\left(\\sin\\frac x2-\\cos\\frac x2\\right)^2=1-\\sin x$，正負看 $\\dfrac x2$ 的範圍。', p: { s: s, R: R, quad: qd, sgn: sgn, val2: [val2.n, val2.d] } };
  };
  L2.paramFit = function (r) {
    var a = r.int(1, 4), bF = r.pick([F(1, 2), F(1), F(2), F(3)]), d = r.int(-3, 3);
    var cF = r.pick([F(1, 6), F(1, 3), F(1, 2), F(2, 3), F(5, 6), F(1, 4), F(3, 4)]);
    var xmax = Fr.div(Fr.sub(F(1, 2), cF), bF);
    if (xmax.n <= 0) xmax = Fr.add(xmax, Fr.div(F(2), bF));
    var xmin = Fr.add(xmax, Fr.div(F(1), bF));
    function xT(fr) { return piTex(fr.n, fr.d); }
    return { q: '函數 ' + T('y=a\\sin(bx+c)+d') + '（' + T('a\\gt0,\\ b\\gt0,\\ 0\\lt c\\lt\\pi') + '）的圖形中，' + T('\\left(' + xT(xmax) + ',' + (d + a) + '\\right)') + ' 是最高點，' + T('\\left(' + xT(xmin) + ',' + (d - a) + '\\right)') + ' 是與它相鄰的最低點，求 ' + T('(a,b,c,d)') + '。',
      a: T('(a,b,c,d)=\\left(' + a + ',' + Fr.tex(bF) + ',' + piTex(cF.n, cF.d) + ',' + d + '\\right)'),
      h: '$a=\\dfrac{\\text{最高}-\\text{最低}}{2}$、$d=\\dfrac{\\text{最高}+\\text{最低}}{2}$；相鄰最高最低點的水平距離是半個週期；最後把最高點代入 $bx+c=\\dfrac{\\pi}{2}+2k\\pi$ 定 $c$。', p: { a: a, b: [bF.n, bF.d], c: [cF.n, cF.d], d: d, xmax: [xmax.n, xmax.d], xmin: [xmin.n, xmin.d] } };
  };
  L2.transformOrder = function (r) {
    var kF = r.pick([F(2), F(3), F(1, 2), F(4)]), sF = r.pick([F(1, 6), F(1, 3), F(1, 2), F(2, 3), F(1, 4), F(3, 4), F(5, 6)]);
    var fn = r.pick(['sin', 'cos']), tF = Fr.div(sF, kF);
    var kT = Fr.tex(kF);
    return { q: '將 ' + T('y=\\' + fn + ' x') + ' 的圖形以 ' + T('y') + ' 軸為基準水平伸縮為原來的 ' + T(kT) + ' 倍，再向右平移 ' + T(piTex(sF.n, sF.d)) + '，得到圖形 ' + T('\\Gamma') + '。若改成「先向右平移 ' + T('t') + '，再水平伸縮為原來的 ' + T(kT) + ' 倍」也能得到 ' + T('\\Gamma') + '，求 ' + T('t') + '。',
      a: T('t=' + piTex(tF.n, tF.d)), h: '伸縮 $k$ 倍再右移 $s$：$y=\\' + fn + '\\dfrac{x-s}{k}$；先右移 $t$ 再伸縮：$y=\\' + fn + '\\left(\\dfrac xk-t\\right)$。比較得 $t=\\dfrac sk$。', p: { fn: fn, k: [kF.n, kF.d], s: [sF.n, sF.d], t: [tF.n, tF.d] } };
  };
  L2.periodJudge = function (r) {
    var b = r.pick([1, 2, 3, 4]), kind = r.pick(['abstan', 'sincos2', 'absabs', 'prod', 'cos2', 'sum3']);
    var bT = b === 1 ? 'x' : b + 'x', b3T = (3 * b) + 'x', b2T = (2 * b) + 'x';
    var expr = { abstan: '|\\tan ' + bT + '|', sincos2: '\\sin ' + bT + '+\\cos ' + b2T, absabs: '|\\sin ' + bT + '|+|\\cos ' + bT + '|', prod: '\\sin ' + bT + '\\cos ' + bT, cos2: '\\cos^2 ' + bT, sum3: '\\sin ' + bT + '+\\sin ' + b3T }[kind];
    var P = { abstan: F(1, b), sincos2: F(2, b), absabs: F(1, 2 * b), prod: F(1, b), cos2: F(1, b), sum3: F(2, b) }[kind];
    var hint = { abstan: '$\\tan$ 加絕對值週期不變（$\\tan$ 本身已是半個「正弦週期」）。', sincos2: '兩項週期取最小公倍數（最小公倍數一定是週期，但未必最小；這一型代值檢驗後沒有更小的）。', absabs: '$|\\sin|+|\\cos|$ 把 $x$ 換成 $x+\\dfrac{\\pi}{2b}$ 會互換，週期是 $\\dfrac{\\pi}{2b}$。', prod: '$\\sin\\cos=\\dfrac12\\sin(2\\cdot)$，倍角後週期減半。', cos2: '降冪：$\\cos^2=\\dfrac{1+\\cos(2\\cdot)}{2}$。', sum3: '兩項週期 $\\dfrac{2\\pi}{b}$ 與 $\\dfrac{2\\pi}{3b}$，取最小公倍數（最小公倍數一定是週期，但未必最小；這一型代值檢驗後沒有更小的）。' }[kind];
    return { q: '求 ' + T('y=' + expr) + ' 的最小正週期。', a: T(P.n === 1 && P.d === 1 ? '\\pi' : Fr.tex(P) + '\\pi'), h: hint, p: { b: b, kind: kind, P: [P.n, P.d] } };
  };
  /* 解的個數：c + k sin x = x，用細掃描數變號；避開幾乎相切的參數 */
  function countRoots(c, k) {
    var lo = c - k - 1, hi = c + k + 1, n = 60000, prev = null, cnt = 0, minAbsAtExt = 9;
    var fprev2 = null, fprev = null;
    for (var i = 0; i <= n; i++) {
      var x = lo + (hi - lo) * i / n, f = c + k * Math.sin(x) - x;
      if (prev !== null && ((prev < 0 && f > 0) || (prev > 0 && f < 0))) cnt++;
      if (f === 0) cnt++;
      if (fprev2 !== null && ((fprev > fprev2 && fprev > f) || (fprev < fprev2 && fprev < f))) minAbsAtExt = Math.min(minAbsAtExt, Math.abs(fprev));
      fprev2 = fprev; fprev = f; prev = f;
    }
    return { cnt: cnt, safe: minAbsAtExt > 0.08 };
  }
  L2.rootCount = function (r) {
    var c, k, res, tries = 0;
    do { c = r.pick([0, 1, 2, 3, -1, -2, 4]); k = r.int(3, 12); res = countRoots(c, k); } while (!res.safe && tries++ < 40);
    var lhs = (c === 0 ? '' : c + '+') + k + '\\sin x';
    return { q: '方程式 ' + T(lhs + '=x') + ' 有幾個實數解？', a: T(res.cnt) + ' 個', h: '化成 $\\sin x=\\dfrac{x' + (c === 0 ? '' : signed(-c)) + '}{' + k + '}$，畫 $y=\\sin x$ 與一條斜率 $\\dfrac1{' + k + '}$ 的直線，直線只在 $|y|\\le1$ 的範圍內有效，數交點。', p: { c: c, k: k, cnt: res.cnt } };
  };
  /* 三角不等式：由兩個根（−1、−½、0、½、1）動態生成 fn 的二次式，解集合以 π/12 為單位掃出來 */
  var ROOTS = [[-1, 1], [-1, 2], [0, 1], [1, 2], [1, 1]];   /* [分子, 分母] */
  function fnValK(fn, k) {                                    /* fn(kπ/12)：回傳 {num:分數或null, val:浮點} */
    var deg = k * 15;
    if (deg % 30 !== 0 && deg % 45 !== 0) return { fr: null, val: { sin: Math.sin, cos: Math.cos }[fn](deg * Math.PI / 180) };
    var v = tv(deg)[fn], val = vNum(v);
    if (v.r === 1) return { fr: F(v.c, v.d), val: val };
    return { fr: null, val: val };
  }
  function setTex(iv, pts) {
    var parts = iv.map(function (v) {
      var lo = piTex(v[0], 12), hi = v[1] === 24 ? '2\\pi' : piTex(v[1], 12);
      return lo + (v[2] ? '\\le ' : '\\lt ') + 'x' + (v[3] ? '\\le ' : '\\lt ') + hi;
    });
    pts.forEach(function (k) { parts.push('x=' + piTex(k, 12)); });
    return parts.join('\\ \\text{或}\\ ');
  }
  L2.trigIneq = function (r) {
    var guard = 0;
    while (guard++ < 60) {
      var fn = r.pick(['sin', 'cos']), i1 = r.int(0, 4), i2 = r.int(0, 4); if (i1 === i2) continue; if (i1 > i2) { var tmp = i1; i1 = i2; i2 = tmp; }
      var r1 = ROOTS[i1], r2 = ROOTS[i2], s = r.sign(), op = r.pick(['<', '<=', '>', '>=']);
      /* Q(f) = s·(d1 f − n1)(d2 f − n2) = A f² + B f + C */
      var A = s * r1[1] * r2[1], B = -s * (r1[1] * r2[0] + r2[1] * r1[0]), C = s * r1[0] * r2[0];
      var form = r.pick(['same', 'same', 'mixed']);
      var cmp = function (val) { return op === '<' ? val < 0 : op === '<=' ? val <= 0 : op === '>' ? val > 0 : val >= 0; };
      var Q = function (fr, val) { return fr ? Fr.add(Fr.add(Fr.mul(F(A), Fr.mul(fr, fr)), Fr.mul(F(B), fr)), F(C)) : null; };
      var onGrid = [], onMid = [];
      for (var k = 0; k < 24; k++) {
        var g = fnValK(fn, k), qv = Q(g.fr, g.val);
        onGrid.push(cmp(qv ? Fr.toNum(qv) : A * g.val * g.val + B * g.val + C));
        var mv = { sin: Math.sin, cos: Math.cos }[fn]((k + 0.5) * Math.PI / 12);
        onMid.push(cmp(A * mv * mv + B * mv + C));
      }
      /* 掃成區間：段 k 為 (k, k+1)，端點 k */
      var iv = [], pts = [], k0 = 0;
      while (k0 < 24) {
        if (onMid[k0]) {
          var k1 = k0 + 1; while (k1 < 24 && onMid[k1] && onGrid[k1]) k1++;     /* 內部有不成立的孤立點（如 sin x=1）就在那裡切開 */
          iv.push([k0, k1, onGrid[k0] ? 1 : 0, (k1 < 24 && onGrid[k1]) ? 1 : 0]);
          k0 = k1;
        } else { if (onGrid[k0] && !(k0 > 0 && onMid[k0 - 1])) pts.push(k0); k0++; }
      }
      if (iv.length && iv[iv.length - 1][1] === 24 && iv[0][0] === 0 && onGrid[0]) { /* 跨 0 的區間：0 是端點，已含在第一段 */ }
      if (!iv.length && !pts.length) continue;
      if (iv.length === 1 && iv[0][0] === 0 && iv[0][1] === 24 && !pts.length) continue;   /* 恆成立，太無聊 */
      /* 題目文字 */
      var f2 = '\\' + fn + '^2x', f1 = '\\' + fn + ' x', g1 = '\\' + (fn === 'sin' ? 'cos' : 'sin') + '^2x';
      var terms, rhs = 0;
      if (form === 'same') terms = [[A, f2], [B, f1], [C, '']];
      else { terms = [[-A, g1], [B, f1]]; rhs = -(A + C); }
      var lead = terms[0][0] < 0 ? -1 : 1, opT = op;
      if (lead < 0) { terms = terms.map(function (x) { return [-x[0], x[1]]; }); rhs = -rhs; opT = { '<': '>', '<=': '>=', '>': '<', '>=': '<=' }[op]; }
      var lhs = '', first = true;
      terms.forEach(function (x) { if (x[0] === 0) return; var n = x[0]; var mag = x[1] === '' ? String(Math.abs(n)) : ((Math.abs(n) === 1 ? '' : Math.abs(n)) + x[1]); lhs += (n < 0 ? '-' : (first ? '' : '+')) + mag; first = false; });
      var opTex = { '<': '\\lt', '<=': '\\le', '>': '\\gt', '>=': '\\ge' }[opT];
      return { q: '設 ' + T('0\\le x\\lt2\\pi') + '，解不等式 ' + T(lhs + opTex + rhs) + '。', a: T(setTex(iv, pts)),
        h: (form === 'mixed' ? '先用 $\\sin^2x+\\cos^2x=1$ 把 $' + g1 + '$ 換成 $1-' + f2 + '$，' : '') + '化成 $' + f1 + '$ 的二次式後因式分解：根是 $' + fracTex(r1[0], r1[1]) + '$ 與 $' + fracTex(r2[0], r2[1]) + '$；先解出「$' + f1 + '$ 的範圍」，再對照單位圓翻成 $x$ 的範圍（根為 $\\pm1$ 時會出現孤立解）。',
        p: { fn: fn, A: A, B: B, C: C, op: op, form: form, iv: iv, pts: pts } };
    }
    return L2.trigIneq(makeRng(r.int(1, 1e6)));
  };
  L2.combineInterval = function (r) {
    var row = r.pick(COMB), unit = row[4] === 4 ? 3 : 2;      /* π/12 的倍數：π/4 或 π/6 */
    var lo = unit * r.int(0, 4), len = unit * r.int(2, 5), hi = lo + len;
    var m = r.pick([1, 2]), R2 = row[2] * m * m;
    var thK = row[3] * 12 / row[4];                              /* θ 以 π/12 為單位 */
    var aT = combTerm(row[0], m, true) + '\\sin x', bT = combTerm(row[1], m, false) + '\\cos x';
    /* f = √R2 · sin(x+θ)；在 [lo,hi] 上：候選點 = 端點 + 內部使 x+θ ≡ 6 或 18 (mod 24) 的點 */
    var cands = [lo, hi];
    for (var k = lo; k <= hi; k++) { var u = ((k + thK) % 24 + 24) % 24; if (u === 6 || u === 18) cands.push(k); }
    var best = null, worst = null, bestKs = [], worstKs = [];            /* 等高（例如兩端點一樣高）時，達到最值的 x 要全列 */
    cands.forEach(function (k) {
      var sv = tv((k + thK) * 15).sin, val = vNum(sv);
      if (best === null || val > best.val + 1e-12) { best = { k: k, val: val, sv: sv }; bestKs = [k]; } else if (Math.abs(val - best.val) <= 1e-12 && bestKs.indexOf(k) < 0) bestKs.push(k);
      if (worst === null || val < worst.val - 1e-12) { worst = { k: k, val: val, sv: sv }; worstKs = [k]; } else if (Math.abs(val - worst.val) <= 1e-12 && worstKs.indexOf(k) < 0) worstKs.push(k);
    });
    bestKs.sort(function (x, y) { return x - y; }); worstKs.sort(function (x, y) { return x - y; });
    function xsT(ks) { return 'x=' + ks.map(function (k) { return piTex(k, 12); }).join('\\ \\text{或}\\ '); }
    function fT(sv) { return surdOver(sv.c, R2 * sv.r, sv.d); }
    return { q: '設 ' + T(piTex(lo, 12) + '\\le x\\le' + (hi === 24 ? '2\\pi' : piTex(hi, 12))) + '，求 ' + T('f(x)=' + aT + bT) + ' 的最大值與最小值，並指出對應的 ' + T('x') + '。',
      a: '最大值 ' + T(fT(best.sv)) + '（' + T(xsT(bestKs)) + '），最小值 ' + T(fT(worst.sv)) + '（' + T(xsT(worstKs)) + '）',
      h: '先疊合成 $' + sqrtTex(R2) + '\\sin(x+\\theta)$，再看 $x+\\theta$ 在給定區間跑過哪一段，最大最小可能在端點或在 $\\dfrac{\\pi}{2}$、$\\dfrac{3\\pi}{2}$ 處。',
      p: { aIsSqrt3: Math.abs(row[0]) === 3, aSign: row[0] < 0 ? -1 : 1, bIsSqrt3: Math.abs(row[1]) === 3, bSign: row[1] < 0 ? -1 : 1, m: m, lo: lo, hi: hi, R2: R2, thK: thK, bestK: best.k, worstK: worst.k, bestKs: bestKs, worstKs: worstKs } };
  };
  L2.squareSub = function (r) {
    var sgn = r.sign(), k = r.pick([-4, -3, -2, -1, 1, 2, 3, 4]), mm = r.int(-3, 3);
    var tT = '(\\sin x' + (sgn > 0 ? '+' : '-') + '\\cos x)';
    var expr = tT + '^2' + (k === 1 ? '+' : k === -1 ? '-' : signed(k)) + tT + (mm === 0 ? '' : signed(mm));
    /* g(t)=t²+kt+m, t∈[-√2,√2] */
    var gEnd = function (s) { return { a: 2 + mm, b: k * s }; };      /* 值 = (2+m) + k s √2 → a + b√2 */
    var lo = gEnd(-1), hi = gEnd(1);
    var vertexIn = Math.abs(k) / 2 < Math.SQRT2;
    var minT, maxT;
    if (vertexIn) { var mv = F(4 * mm - k * k, 4); minT = Fr.tex(mv); }
    else { minT = surdFracTex(k < 0 ? hi.a : lo.a, k < 0 ? hi.b : lo.b, 2, 1); }
    maxT = surdFracTex(k > 0 ? hi.a : lo.a, k > 0 ? hi.b : lo.b, 2, 1);
    return { q: '求 ' + T('f(x)=' + expr) + ' 的最大值與最小值。', a: '最大值 ' + T(maxT) + '，最小值 ' + T(minT),
      h: '令 $t=\\sin x' + (sgn > 0 ? '+' : '-') + '\\cos x=\\sqrt2\\sin\\left(x' + (sgn > 0 ? '+' : '-') + '\\dfrac{\\pi}{4}\\right)$，$-\\sqrt2\\le t\\le\\sqrt2$，化成 $t$ 的二次函數在閉區間上求極值。', p: { sgn: sgn, k: k, m: mm, vertexIn: vertexIn } };
  };
  L2.eqSumCount = function (r) {
    var b = r.pick([2, 3, 4, 5, 6]), fn = r.pick(['sin', 'cos']), kpos = r.sign() > 0;
    var cnt = 2 * b, sumK = fn === 'sin' ? (kpos ? 2 * b - 1 : 2 * b + 1) : 2 * b;
    return { q: '設 ' + T('0\\lt x\\lt2\\pi') + '，' + T(kpos ? '0\\lt k\\lt1' : '-1\\lt k\\lt0') + '，求方程式 ' + T('\\' + fn + ' ' + b + 'x=k') + ' 的實數解個數，以及所有實數解的總和。',
      a: T(cnt) + ' 個，總和 ' + T(sumK + '\\pi'), h: '令 $u=' + b + 'x\\in(0,' + (2 * b) + '\\pi)$，每個週期有兩解且對稱於 $\\dfrac{\\pi}{2}$（或 $\\dfrac{3\\pi}{2}$、$\\pi$）配對相加，最後除以 $' + b + '$。', p: { b: b, fn: fn, kpos: kpos, cnt: cnt, sumK: sumK } };
  };

  /* ══════════ 2026-09-28 擴充（依段考卷出現頻率補題型）：L2 6 型 ══════════ */
  /* 1-1 弓形面積：扇形減三角形（優弧那一塊：圓減劣弓形） */
  L2.segmentArea = function (r) {
    var rad = r.int(2, 10), give = r.pick(['angle', 'angle', 'chord']), which = r.pick(['minor', 'minor', 'major']);
    var K = give === 'chord' ? r.pick([4, 6, 8]) : r.pick([2, 3, 4, 6, 8, 9, 10]);        /* 圓心角 = Kπ/12 */
    var sec = F(rad * rad * K, 24), sv = tv(15 * K).sin, tri = surdOver(rad * rad * sv.c, sv.r, 2 * sv.d);
    var ans = which === 'minor' ? coefPi(sec) + '-' + tri : coefPi(Fr.sub(F(rad * rad), sec)) + '+' + tri;
    var arcW = which === 'minor' ? '劣弧' : '優弧';
    var q = give === 'angle' ? '半徑為 ' + T(rad) + ' 的圓中，一弦所對的圓心角為 ' + T(piTex(K, 12)) + '，求此弦與' + arcW + '所圍成的弓形面積。'
      : '半徑為 ' + T(rad) + ' 的圓中，有一條長為 ' + T(sqrtTex(rad * rad * { 4: 1, 6: 2, 8: 3 }[K])) + ' 的弦，求此弦與' + arcW + '所圍成的弓形面積。';
    var h = (give === 'chord' ? '先求圓心角：弦長 $=2r\\sin\\dfrac{\\theta}{2}$，得 $\\theta=' + piTex(K, 12) + '$。' : '') +
      '劣弓形 $=$ 扇形 $-$ 三角形 $=\\dfrac12r^2\\theta-\\dfrac12r^2\\sin\\theta=\\dfrac12\\times' + rad + '^2\\times' + piTex(K, 12) + '-\\dfrac12\\times' + rad + '^2\\times' + vTex(sv) + '$' +
      (which === 'major' ? '；優弧那一塊是整個圓 $' + coefPi(F(rad * rad)) + '$ 減去劣弓形。' : '。');
    return { q: q, a: T(ans), h: h, p: { r: rad, K: K, give: give, which: which } };
  };

  /* 1-2 角的拆分：α=(α+β)−β、α=(α−β)+β */
  L2.angleSplit = function (r) {
    var g = 0, form, ask, gF, bF, t1, t2, cg, sg, R1, sb, cb, R2, ca, sa;
    do {
      form = r.pick(['sum', 'sum', 'diff']); ask = r.pick(['cos', 'sin']); bF = r.pick(['sin', 'cos']);
      gF = form === 'sum' ? 'cos' : r.pick(['sin', 'cos']);
      t1 = r.pick(TRIPLES); t2 = r.pick(TRIPLES);
      sg = t1[0]; cg = (form === 'sum' ? r.sign() : 1) * t1[1]; R1 = t1[2]; sb = t2[0]; cb = t2[1]; R2 = t2[2];
      ca = form === 'sum' ? cg * cb + sg * sb : cg * cb - sg * sb;          /* cos((α+β)−β)、cos((α−β)+β) */
      sa = form === 'sum' ? sg * cb - cg * sb : sg * cb + cg * sb;
    } while (!(ca > 0 && sa > 0) && g++ < 200);
    if (!(ca > 0 && sa > 0)) return L2.angleSplit(makeRng(r.int(1, 1e6)));
    var gam = form === 'sum' ? '\\alpha+\\beta' : '\\alpha-\\beta';
    var givenG = '\\' + gF + '(' + gam + ')=' + fracTex(gF === 'cos' ? cg : sg, R1), givenB = '\\' + bF + '\\beta=' + fracTex(bF === 'sin' ? sb : cb, R2);
    var rng = form === 'sum' ? T('0\\lt\\alpha\\lt\\dfrac{\\pi}{2}') + '、' + T('0\\lt\\beta\\lt\\dfrac{\\pi}{2}') : T('0\\lt\\beta\\lt\\alpha\\lt\\dfrac{\\pi}{2}');
    var val = ask === 'cos' ? ca : sa;
    return { q: '已知 ' + rng + '，' + T(givenG) + '、' + T(givenB) + '，求 ' + T('\\' + ask + '\\alpha') + '。', a: T('\\' + ask + '\\alpha=' + fracTex(val, R1 * R2)),
      h: '把 $\\alpha$ 看成 $' + (form === 'sum' ? '(\\alpha+\\beta)-\\beta' : '(\\alpha-\\beta)+\\beta') + '$。先補齊：$' + gam + '$ 在 ' + (form === 'sum' ? '$(0,\\pi)$ 內，$\\sin(\\alpha+\\beta)$ 一定是正的' : '$\\left(0,\\dfrac{\\pi}{2}\\right)$ 內，正弦、餘弦都是正的') + '；$\\beta$ 是銳角。再用' + (form === 'sum' ? '差' : '和') + '角公式。',
      p: { form: form, ask: ask, gF: gF, bF: bF, sg: sg, cg: cg, R1: R1, sb: sb, cb: cb, R2: R2, val: [val, R1 * R2] } };
  };

  /* 1-2 三角形中求 cos C（或 sin C）：C=π−(A+B)；給 sin 的角要檢查能不能是鈍角 */
  L2.triCosC = function (r) {
    for (var g = 0; g < 300; g++) {
      var tA = r.pick(TRIPLES), tB = r.pick(TRIPLES), oA = r() < 0.3, oB = !oA && r() < 0.25;
      var RA = tA[2], RB = tB[2], sA = tA[0], cA = (oA ? -1 : 1) * tA[1], sB = tB[0], cB = (oB ? -1 : 1) * tB[1];
      var A = Math.atan2(sA, cA), Bn = Math.atan2(sB, cB);
      if (A + Bn > Math.PI - 0.05) continue;
      var gA = r.pick(['sin', 'sin', 'cos']), gB = r.pick(['sin', 'cos', 'cos']);
      var candA = gA === 'cos' ? [A] : [A, Math.PI - A], candB = gB === 'cos' ? [Bn] : [Bn, Math.PI - Bn], ok = 0;
      candA.forEach(function (x) { candB.forEach(function (y) { if (x + y < Math.PI - 1e-9) ok++; }); });
      if (ok !== 1) continue;
      var ask = r.pick(['cos', 'cos', 'sin']);
      var num = ask === 'cos' ? sA * sB - cA * cB : sA * cB + cA * sB;
      if (num === 0) continue;
      var tipA = gA === 'sin' ? '$A$ 若是鈍角，$\\cos A=' + fracTex(-Math.abs(cA), RA) + '$' : '';
      return { q: '在 ' + T('\\triangle ABC') + ' 中，' + T('\\' + gA + ' A=' + fracTex(gA === 'sin' ? sA : cA, RA)) + '、' + T('\\' + gB + ' B=' + fracTex(gB === 'sin' ? sB : cB, RB)) + '，求 ' + T('\\' + ask + ' C') + '。',
        a: T('\\' + ask + ' C=' + fracTex(num, RA * RB)),
        h: '$C=\\pi-(A+B)$ ⟹ ' + (ask === 'cos' ? '$\\cos C=-\\cos(A+B)=\\sin A\\sin B-\\cos A\\cos B$' : '$\\sin C=\\sin(A+B)=\\sin A\\cos B+\\cos A\\sin B$') + '。給 $\\sin$ 的角要討論銳角、鈍角：' + (tipA ? tipA + '，' : '') + '兩角加起來不能超過 $\\pi$，不合的要捨去。',
        p: { gA: gA, gB: gB, sA: sA, cA: cA, RA: RA, sB: sB, cB: cB, RB: RB, ask: ask, val: [num, RA * RB] } };
    }
    return L2.triCosC(makeRng(r.int(1, 1e6)));
  };

  /* 1-2 三倍角（進階：課綱沒列，段考常考） */
  L2.tripleEval = function (r) {
    var t = r.int(0, 2);
    if (t < 2) {
      var dd = r.int(2, 7), nn = r.int(1, dd - 1); while (gcd(nn, dd) !== 1) nn = r.int(1, dd - 1);
      var x = F(r.sign() * nn, dd), x3 = Fr.mul(Fr.mul(x, x), x);
      var val = t === 0 ? Fr.sub(Fr.mul(F(3), x), Fr.mul(F(4), x3)) : Fr.sub(Fr.mul(F(4), x3), Fr.mul(F(3), x));
      var fn = t === 0 ? 'sin' : 'cos';
      return { q: '已知 ' + T('\\' + fn + '\\theta=' + Fr.tex(x)) + '，求 ' + T('\\' + fn + '3\\theta') + '。', a: T('\\' + fn + '3\\theta=' + Fr.tex(val)),
        h: t === 0 ? '$\\sin3\\theta=3\\sin\\theta-4\\sin^3\\theta=3\\times' + negP(Fr.tex(x)) + '-4\\times\\left(' + Fr.tex(x) + '\\right)^3$，不用知道 $\\theta$ 在哪一象限。'
          : '$\\cos3\\theta=4\\cos^3\\theta-3\\cos\\theta=4\\times\\left(' + Fr.tex(x) + '\\right)^3-3\\times' + negP(Fr.tex(x)) + '$，不用知道 $\\theta$ 在哪一象限。',
        p: { t: t, x: [x.n, x.d], val: [val.n, val.d] } };
    }
    var fn2 = r.pick(['sin', 'cos']), m = r.pick([1, 2]), th = r.pick([10, 20, 40, 50, 70, 80, 100, 110, 130, 140, 160, 170]);
    var S1 = '\\' + fn2 + dg(th), S3 = '\\' + fn2 + '^3 ' + dg(th);
    var expr = fn2 === 'sin' ? (3 * m) + S1 + '-' + (4 * m) + S3 : (4 * m) + S3 + '-' + (3 * m) + S1;
    var v = tv(3 * th)[fn2];
    return { q: '求 ' + T(expr) + ' 的值。', a: T(surdOver(m * v.c, v.r, v.d)),
      h: (fn2 === 'sin' ? '$3\\sin\\theta-4\\sin^3\\theta=\\sin3\\theta$' : '$4\\cos^3\\theta-3\\cos\\theta=\\cos3\\theta$') + '（三倍角公式倒過來用），' + (m === 2 ? '先提出 $2$，' : '') + '$\\theta=' + dg(th) + '$，$3\\theta=' + dg(3 * th) + '$ 是特殊角。',
      p: { t: t, fn: fn2, m: m, th: th } };
  };

  /* 1-3 二次型值域：cos²x＋p sin x＋q、sin²x＋p cos x＋q、cos2x＋p sin x＋q，令 t＝sin x 或 cos x */
  L2.quadTrigRange = function (r) {
    var form = r.int(0, 2), p = r.pick([-4, -3, -2, -1, 1, 2, 3, 4]), q = r.int(-3, 3), dom = r.pick([0, 0, 1]);
    var tv_ = form === 1 ? 'cos' : 'sin', other = form === 1 ? 'sin' : 'cos';
    var Aa = form === 2 ? 2 : 1, C = F(1 + q);                              /* g(t) = −Aa t² + p t + (1+q) */
    var lo = dom ? F(0) : F(-1), hi = F(1);
    var g = function (t) { return Fr.add(Fr.add(Fr.mul(F(-Aa), Fr.mul(t, t)), Fr.mul(F(p), t)), C); };
    var tv0 = F(p, 2 * Aa), inside = Fr.toNum(tv0) >= Fr.toNum(lo) && Fr.toNum(tv0) <= Fr.toNum(hi);
    var gl = g(lo), gh = g(hi), M = inside ? g(tv0) : (Fr.toNum(gl) > Fr.toNum(gh) ? gl : gh), mn = Fr.toNum(gl) < Fr.toNum(gh) ? gl : gh;
    var pT = (p === 1 ? '+' : p === -1 ? '-' : signed(p)) + '\\' + tv_ + ' x';
    var expr = (form === 2 ? '\\cos2x' : '\\' + other + '^2x') + pT + (q === 0 ? '' : signed(q));
    var domT = dom ? (tv_ === 'sin' ? '0\\le x\\le\\pi' : '-\\dfrac{\\pi}{2}\\le x\\le\\dfrac{\\pi}{2}') : '';
    return { q: (dom ? '設 ' + T(domT) + '，求 ' : '求 ') + T('f(x)=' + expr) + ' 的最大值與最小值。', a: '最大值 ' + T(Fr.tex(M)) + '，最小值 ' + T(Fr.tex(mn)),
      h: '令 $t=\\' + tv_ + ' x$，' + (dom ? '在 $' + domT + '$ 時 $' + Fr.tex(lo) + '\\le t\\le1$' : '$-1\\le t\\le1$') + '；' + (form === 2 ? '$\\cos2x=1-2\\sin^2x=1-2t^2$' : '$\\' + other + '^2x=1-t^2$') + '，$f=' + (Aa === 2 ? '-2' : '-') + 't^2' + (p === 1 ? '+' : p === -1 ? '-' : signed(p)) + 't' + (1 + q === 0 ? '' : signed(1 + q)) + '$，頂點在 $t=' + Fr.tex(tv0) + '$，' + (inside ? '在範圍內' : '不在範圍內') + '；最大最小要看頂點與兩端。',
      p: { form: form, p: p, q: q, dom: dom, M: [M.n, M.d], m: [mn.n, mn.d] } };
  };

  /* 1-3 二次型三角方程式：化成 sin x（或 cos x）的一元二次方程，因式分解，範圍外的根不合 */
  var QROOT_IN = [[-1, 1], [-1, 2], [0, 1], [1, 2], [1, 1]], QROOT_OUT = [[2, 1], [-2, 1], [3, 2], [-3, 2], [3, 1], [-3, 1]];
  L2.quadTrigEq = function (r) {
    var fn = r.pick(['sin', 'cos']), form = r.pick(['same', 'mixed', 'mixed', 'double']), i1 = r.int(0, 4), r1 = QROOT_IN[i1], r2, sgn = r.sign();
    if (r() < 0.5) r2 = r.pick(QROOT_OUT); else { var i2 = r.int(0, 4); while (i2 === i1) i2 = r.int(0, 4); r2 = QROOT_IN[i2]; }
    var A = sgn * r1[1] * r2[1], B = -sgn * (r1[1] * r2[0] + r2[1] * r1[0]), C = sgn * r1[0] * r2[0];   /* A t² + B t + C = 0 */
    var og = fn === 'sin' ? 'cos' : 'sin', terms;
    if (form === 'same') terms = [[A, '\\' + fn + '^2x'], [B, '\\' + fn + ' x'], [C, '']];
    else if (form === 'mixed') terms = [[-A, '\\' + og + '^2x'], [B, '\\' + fn + ' x'], [A + C, '']];
    else if (fn === 'sin') terms = [[-A, '\\cos2x'], [2 * B, '\\sin x'], [A + 2 * C, '']];
    else terms = [[A, '\\cos2x'], [2 * B, '\\cos x'], [A + 2 * C, '']];
    var gg = 0; terms.forEach(function (x) { gg = gcd(gg, x[0]); });
    var lead = terms.filter(function (x) { return x[0] !== 0; })[0][0] < 0 ? -1 : 1;
    terms = terms.map(function (x) { return [lead * x[0] / gg, x[1]]; });
    var lhs = '', first = true;
    terms.forEach(function (x) { if (x[0] === 0) return; var n = x[0], mag = x[1] === '' ? String(Math.abs(n)) : ((Math.abs(n) === 1 ? '' : Math.abs(n)) + x[1]); lhs += (n < 0 ? '-' : (first ? '' : '+')) + mag; first = false; });
    var roots = [r1, r2].filter(function (x) { return Math.abs(x[0]) <= x[1]; }), ks = [];
    roots.forEach(function (x) { for (var k = 0; k < 24; k += 2) { var v = vNum(tv(k * 15)[fn]); if (Math.abs(v - x[0] / x[1]) < 1e-9 && ks.indexOf(k) < 0) ks.push(k); } });
    ks.sort(function (a, b) { return a - b; });
    var rt = function (x) { return fracTex(x[0], x[1]); };
    return { q: '解方程式 ' + T(lhs + '=0') + '，' + T('0\\le x\\lt2\\pi') + '。', a: T('x=' + ks.map(function (k) { return piTex(k, 12); }).join(',\\ ')),
      h: (form === 'mixed' ? '先用 $\\sin^2x+\\cos^2x=1$ 把 $\\' + og + '^2x$ 換成 $1-\\' + fn + '^2x$，' : form === 'double' ? '先用 $\\cos2x=' + (fn === 'sin' ? '1-2\\sin^2x' : '2\\cos^2x-1') + '$ 換掉 $\\cos2x$，' : '') + '整理成 $\\' + fn + ' x$ 的二次方程，因式分解得 $\\' + fn + ' x=' + rt(r1) + '$ 或 $' + rt(r2) + '$' + (Math.abs(r2[0]) > r2[1] ? '（$' + rt(r2) + '$ 超出 $[-1,1]$，不合）' : '') + '，再在 $[0,2\\pi)$ 內找角。',
      p: { fn: fn, form: form, r1: r1, r2: r2, ks: ks } };
  };

  var META_L2 = [['sectorSys', '周長與面積反求扇形'], ['sectorMax', '定周長扇形面積最大'], ['coneShortest', '圓錐側面最短路徑'], ['segmentArea', '弓形面積'], ['sumProd', 'sinθ+cosθ=k 的連鎖求值'], ['quadRootCos2', '方程式的根 → cos2θ'], ['tanQuad', '根與係數 × tan 和角'], ['systemSquare', '平方相加求 cos(A+B)'], ['angleSplit', '角的拆分：α=(α+β)−β'], ['triCosC', '三角形中由 A、B 求 C'], ['halfFromCos2x', 'cos2x → 半角組合'], ['tripleEval', '三倍角（進階）'], ['paramFit', '由最高最低點反求 (a,b,c,d)'], ['transformOrder', '伸縮與平移的順序'], ['periodJudge', '合成函數的週期'], ['rootCount', '方程式 c+k sin x=x 的解數'], ['trigIneq', '三角不等式（含孤立解）'], ['quadTrigEq', '二次型三角方程式'], ['combineInterval', '疊合後的區間最值'], ['squareSub', 'sin x±cos x 的二次代換'], ['quadTrigRange', 'cos²x＋p sin x 型的最值'], ['eqSumCount', 'sin bx=k 的解數與總和']];

  /* ══════════════════════════════════════════════════════════
     L3　中上（18 型）：每型對應固定題 L3-1～L3-18 的「類似題」
     角一律是 π/12 的倍數（K 單位），值由 tv() 精確給出。
     ══════════════════════════════════════════════════════════ */
  var L3 = {};
  var SQ3 = Math.sqrt(3), SQ2 = Math.SQRT2;
  /* 有理數 rat + c√r/d → LaTeX（r 化簡後為 1 就併入有理數） */
  function mixTex(rat, c, r, d) {
    var s = simpSqrt(r); c = c * s.c; r = s.r;
    if (c === 0) return Fr.tex(rat);
    if (r === 1) return Fr.tex(Fr.add(rat, F(c, d)));
    var D = rat.d * d / gcd(rat.d, d), a = rat.n * (D / rat.d), b = c * (D / d);
    return surdFracTex(a, b, r, D);
  }
  /* 係數排版：n 為整數，isS3 表示 n√3；first 是不是最前面的項 */
  function coefTex(n, isS3, first) {
    var neg = n < 0, m = Math.abs(n);
    var mag = isS3 ? ((m === 1 ? '' : m) + '\\sqrt3') : (m === 1 ? '' : String(m));
    return (neg ? '-' : (first ? '' : '+')) + mag;
  }
  /* 依 (a 是否√3, a 正負, b 是否√3, b 正負) 找 COMB 列：a sin u + b cos u = √r² sin(u+θ) */
  function combRow(aS3, aSg, bS3, bSg) {
    for (var i = 0; i < COMB.length; i++) {
      var row = COMB[i];
      if ((Math.abs(row[0]) === 3) === aS3 && (row[0] < 0 ? -1 : 1) === aSg && (Math.abs(row[1]) === 3) === bS3 && (row[1] < 0 ? -1 : 1) === bSg) return row;
    }
    return null;
  }
  /* √R2·sin(u) 在 u = scale·x + thK（K 單位）、x ∈ [lo,hi] 上的最大／最小（候選：端點＋內部 u ≡ 6, 18） */
  function extremaOn(R2, thK, lo, hi, scale) {
    /* x 以 π/24 為單位（x24）回傳，u 以 π/12 為單位；內部極值點 u ≡ 6, 18 (mod 24) 在 scale=2 時 x 可能是 π/24 的奇數倍 */
    var uLo = scale * lo + thK, uHi = scale * hi + thK, cands = [{ x24: 2 * lo, u: uLo }, { x24: 2 * hi, u: uHi }];
    for (var u = uLo + 1; u < uHi; u++) { var um = ((u % 24) + 24) % 24; if (um === 6 || um === 18) cands.push({ x24: Math.round(2 * (u - thK) / scale), u: u }); }
    var best = null, worst = null, bestXs = [], worstXs = [];            /* 等高時，達到最值的 x 要全列 */
    cands.forEach(function (c) {
      var sv = tv(c.u * 15).sin, val = vNum(sv);
      if (best === null || val > best.val + 1e-12) { best = { x24: c.x24, val: val, sv: sv }; bestXs = [c.x24]; } else if (Math.abs(val - best.val) <= 1e-12 && bestXs.indexOf(c.x24) < 0) bestXs.push(c.x24);
      if (worst === null || val < worst.val - 1e-12) { worst = { x24: c.x24, val: val, sv: sv }; worstXs = [c.x24]; } else if (Math.abs(val - worst.val) <= 1e-12 && worstXs.indexOf(c.x24) < 0) worstXs.push(c.x24);
    });
    bestXs.sort(function (x, y) { return x - y; }); worstXs.sort(function (x, y) { return x - y; });
    function tex(sv) { var s = simpSqrt(R2 * sv.r); return { c: sv.c * s.c, r: s.r, d: sv.d }; }
    return { maxX24: best.x24, minX24: worst.x24, maxXs: bestXs, minXs: worstXs, max: tex(best.sv), min: tex(worst.sv), flat: Math.abs(best.val - worst.val) < 1e-12 };
  }
  function kTex(k) { return k === 24 ? '2\\pi' : k === -24 ? '-2\\pi' : piTex(k, 12); }
  function k24Tex(k) { return k === 48 ? '2\\pi' : k === -48 ? '-2\\pi' : piTex(k, 24); }
  function xs24Tex(ks) { return 'x=' + ks.map(k24Tex).join('\\ \\text{或}\\ '); }
  function surd3(o) { return surdOver(o.c, o.r, o.d); }

  /* L3-1　弧度值估大小（多選） */
  var BND = [['0', 0, '\\dfrac12', 0.5], ['\\dfrac12', 0.5, '\\dfrac{\\sqrt3}{2}', SQ3 / 2], ['\\dfrac{\\sqrt3}{2}', SQ3 / 2, '1', 1], ['-\\dfrac12', -0.5, '0', 0], ['-\\dfrac{\\sqrt3}{2}', -SQ3 / 2, '-\\dfrac12', -0.5], ['-1', -1, '-\\dfrac{\\sqrt3}{2}', -SQ3 / 2], ['\\dfrac{\\sqrt2}{2}', SQ2 / 2, '1', 1], ['-1', -1, '-\\dfrac{\\sqrt2}{2}', -SQ2 / 2], ['0', 0, '\\dfrac{\\sqrt2}{2}', SQ2 / 2], ['-\\dfrac{\\sqrt2}{2}', -SQ2 / 2, '0', 0]];
  var BNDT = [['0', 0, '\\dfrac{1}{\\sqrt3}', 1 / SQ3], ['\\dfrac{1}{\\sqrt3}', 1 / SQ3, '1', 1], ['1', 1, '\\sqrt3', SQ3], ['-1', -1, '0', 0], ['-\\sqrt3', -SQ3, '-1', -1], ['0', 0, '1', 1]];
  function argVal(arg) { return arg.kind === 'rad' ? arg.v : arg.kind === 'pideg' ? Math.PI * Math.PI / 180 : Math.PI * Math.PI; }
  function argTex(arg) { return arg.kind === 'rad' ? String(arg.v) : arg.kind === 'pideg' ? '(\\pi^\\circ)' : '(\\pi^2)'; }
  L3.radEstimate = function (r) {
    var items = [], ans = [], guard = 0;
    while (items.length < 5 && guard++ < 200) {
      var fn = r.pick(['sin', 'cos', 'cos', 'sin', 'tan']);
      var arg = r.pick([{ kind: 'rad', v: r.int(1, 6) }, { kind: 'rad', v: r.int(1, 6) }, { kind: 'rad', v: r.int(1, 6) }, { kind: 'pideg' }, { kind: 'pisq' }]);
      var val = { sin: Math.sin, cos: Math.cos, tan: Math.tan }[fn](argVal(arg));
      var rows = fn === 'tan' ? BNDT : BND;
      var okRows = rows.filter(function (b) { return Math.abs(val - b[1]) > 0.04 && Math.abs(val - b[3]) > 0.04; });
      var trues = okRows.filter(function (b) { return b[1] < val && val < b[3]; });
      var falses = okRows.filter(function (b) { return !(b[1] < val && val < b[3]); });
      var wantTrue = r() < 0.5, row = wantTrue && trues.length ? r.pick(trues) : (falses.length ? r.pick(falses) : null);
      if (!row) continue;
      var dup = items.some(function (it) { return it.fn === fn && it.arg.kind === arg.kind && it.arg.v === arg.v; });
      if (dup) continue;
      var truth = row[1] < val && val < row[3];
      items.push({ fn: fn, arg: arg, lo: row[0], hi: row[2], loV: row[1], hiV: row[3], t: truth });
    }
    if (items.length < 5) return L3.radEstimate(makeRng(r.int(1, 1e6)));
    var nT = items.filter(function (i) { return i.t; }).length;
    if (nT === 0 || nT === 5) return L3.radEstimate(makeRng(r.int(1, 1e6)));
    var q = '選出正確的選項：<br>' + items.map(function (it, i) { if (it.t) ans.push(i + 1); return '(' + (i + 1) + ') ' + T(it.lo + '\\lt\\' + it.fn + ' ' + argTex(it.arg) + '\\lt' + it.hi); }).join('　');
    return { q: q, a: '(' + ans.join(')(') + ')', h: '$1$ 弧度 $\\approx57.3^\\circ$：' + items.map(function (it) { return it.arg.kind === 'rad' ? '$' + it.arg.v + '\\approx' + Math.round(it.arg.v * 57.3) + '^\\circ$' : it.arg.kind === 'pideg' ? '$\\pi^\\circ\\approx3.1^\\circ$' : '$\\pi^2\\approx9.87$，減 $2\\pi$ 後約 $3.59$'; }).filter(function (s, i, a) { return a.indexOf(s) === i; }).join('、') + '，換成度數再定位。', p: { items: items.map(function (it) { return { fn: it.fn, arg: it.arg, lo: it.loV, hi: it.hiV, t: it.t }; }), ans: ans } };
  };

  /* L3-2　最高點到最低點的水平距離 → 半週期的奇數倍（多選） */
  L3.periodFromHighLow = function (r) {
    var dd = r.pick([2, 3, 4, 6]), dn = r.int(1, 2 * dd + 1); while (gcd(dn, dd) !== 1 && dn % dd === 0) dn = r.int(1, 2 * dd + 1);
    var D = F(dn, dd);                                     /* 水平距離（π 單位） */
    var x1 = F(r.int(-4, 4), r.pick([1, 2, 4])), x2 = r() < 0.5 ? Fr.add(x1, D) : Fr.sub(x1, D);
    var odds = [1, 3, 5, 7, 9, 11], evens = [2, 4, 6, 8, 10];
    var nT = r.int(2, 3), picks = r.shuffle(odds).slice(0, nT).concat(r.shuffle(evens).slice(0, 5 - nT));
    picks = r.shuffle(picks);
    var opts = picks.map(function (j) { return Fr.div(Fr.mul(F(2), D), F(j)); });
    var ans = [];
    var q = '已知 ' + T('A\\left(' + piTex(x1.n, x1.d) + ',1\\right)') + '、' + T('B\\left(' + piTex(x2.n, x2.d) + ',-1\\right)') + ' 為 ' + T('y=\\sin(ax+b)') + ' 圖形上兩點。下列何者可能是此函數的週期？<br>' +
      opts.map(function (o, i) { if (picks[i] % 2 === 1) ans.push(i + 1); return '(' + (i + 1) + ') ' + T(piTex(o.n, o.d)); }).join('　');
    return { q: q, a: '(' + ans.join(')(') + ')', h: '$A$ 是最高點、$B$ 是最低點，水平距離 $' + piTex(D.n, D.d) + '$ 必須是「半週期的奇數倍」：$' + piTex(D.n, D.d) + '=(2k+1)\\cdot\\dfrac T2$，逐一檢查每個選項的 $2k+1$ 是不是奇數。', p: { x1: [x1.n, x1.d], x2: [x2.n, x2.d], opts: opts.map(function (o) { return [o.n, o.d]; }), ans: ans } };
  };

  /* L3-3　平移後重合 → 相位差是 π 的整數倍 */
  L3.tanShiftCoincide = function (r) {
    var k1 = r.pick([2, 3, 4, 6, 8, 9, 10]), k2 = r.pick([2, 3, 4, 6, 8, 9, 10]); while (k2 === k1) k2 = r.pick([2, 3, 4, 6, 8, 9, 10]);
    var m = r.pick([2, 3, 4, 6]), dir = r.pick(['右', '左']);
    /* 右移 s：k1 − k·s·12/π… 以 K 單位：φ1 − k·(12/m) = φ2 + 12n  ⟹ k = m(φ1−φ2−12n)/12 */
    var d = (dir === '右' ? 1 : -1) * (k1 - k2), best = null;
    for (var n = -3; n <= 3; n++) { var kk = F(m * (d - 12 * n), 12); if (kk.n > 0 && (best === null || Fr.toNum(kk) < Fr.toNum(best))) best = kk; }
    return { q: T('k\\gt0') + '，將 ' + T('y=\\tan\\left(kx+' + piTex(k1, 12) + '\\right)') + ' 的圖形向' + dir + '平移 ' + T(piTex(1, m)) + ' 後與 ' + T('y=\\tan\\left(kx+' + piTex(k2, 12) + '\\right)') + ' 的圖形重合，求 ' + T('k') + ' 的最小值。',
      a: T('k=' + Fr.tex(best)), h: '向' + dir + '移 $' + piTex(1, m) + '$ 是把 $x$ 換成 $x' + (dir === '右' ? '-' : '+') + piTex(1, m) + '$；兩個 $\\tan$ 重合 ⟺ 括號內只差 $n\\pi$：$' + piTex(k1, 12) + (dir === '右' ? '-' : '+') + '\\dfrac{k\\pi}{' + m + '}=' + piTex(k2, 12) + '+n\\pi$，取讓 $k\\gt0$ 的最小者。', p: { k1: k1, k2: k2, m: m, dir: dir, ans: [best.n, best.d] } };
  };

  /* L3-4　sin bx = k 在 (0, Lπ) 的解數與總和 */
  L3.rootSumSin = function (r) {
    var b = r.int(2, 10), L = r.pick([1, 2, 3, 4, 5]), kpos = r() < 0.6, fn = r.pick(['sin', 'sin', 'cos']), M = b * L, cnt = 0, sumU = F(0);
    if (fn === 'cos') {
      if (M % 2) return L3.rootSumSin(makeRng(r.int(1, 1e6)));       /* cos 的兩解對稱於 2jπ+2π，要整數個週期 */
      for (var j3 = 0; 2 * j3 + 2 <= M; j3++) { cnt += 2; sumU = Fr.add(sumU, F(2 + 4 * j3)); }
    } else if (kpos) { for (var j = 0; 2 * j + 1 <= M; j++) { cnt += 2; sumU = Fr.add(sumU, F(1 + 4 * j)); } }
    else { for (var j2 = 0; 2 * j2 + 2 <= M; j2++) { cnt += 2; sumU = Fr.add(sumU, F(3 + 4 * j2)); } }
    if (cnt === 0) return L3.rootSumSin(makeRng(r.int(1, 1e6)));
    var sumX = Fr.div(sumU, F(b));
    var hint = fn === 'cos' ? '令 $u=' + b + 'x\\in(0,' + M + '\\pi)$；$\\cos u=k$ 的兩解在每個週期 $(2j\\pi,2j\\pi+2\\pi)$ 內對稱於 $2j\\pi+\\pi$（$u_0$ 與 $2\\pi-u_0$），每對相加 $=2\\pi+4j\\pi$，最後除以 $' + b + '$。'
      : '令 $u=' + b + 'x\\in(0,' + M + '\\pi)$；$k' + (kpos ? '\\gt0' : '\\lt0') + '$ 時兩解落在每個週期的' + (kpos ? '前' : '後') + '半段 $(' + (kpos ? '2j\\pi,2j\\pi+\\pi' : '2j\\pi+\\pi,2j\\pi+2\\pi') + ')$，對稱於 $' + (kpos ? '\\dfrac{\\pi}{2}' : '\\dfrac{3\\pi}{2}') + '+2j\\pi$，每對相加 $=' + (kpos ? '\\pi+4j\\pi' : '3\\pi+4j\\pi') + '$，最後除以 $' + b + '$。';
    return { q: '設 ' + T('0\\lt x\\lt' + (L === 1 ? '\\pi' : L + '\\pi')) + '，' + T(kpos ? '0\\lt k\\lt1' : '-1\\lt k\\lt0') + '，求方程式 ' + T('\\' + fn + b + 'x=k') + ' 的實數解個數，以及所有實數解的總和。',
      a: T(cnt) + ' 個，總和 ' + T(piTex(sumX.n, sumX.d)), h: hint, p: { b: b, L: L, kpos: kpos, fn: fn, cnt: cnt, sum: [sumX.n, sumX.d] } };
  };

  /* L3-5　絕對值／平方／乘積的週期相加 */
  var PERT = [
    { e: function (b) { return '|\\sin ' + b + '|+|\\cos ' + b + '|'; }, P: [1, 2], id: 'abs+abs' },
    { e: function (b) { return '|\\sin ' + b + '|-|\\cos ' + b + '|'; }, P: [1, 1], id: 'abs-abs' },
    { e: function (b) { return '|\\sin ' + b + '\\cos ' + b + '|'; }, P: [1, 2], id: 'absprod' },
    { e: function (b) { return '|\\sin ' + b + '|+\\cos ' + b; }, P: [2, 1], id: 'abs+cos' },
    { e: function (b) { return '\\sin^2 ' + b; }, P: [1, 1], id: 'sin2' },
    { e: function (b) { return '|\\tan ' + b + '|'; }, P: [1, 1], id: 'abstan' },
    { e: function (b) { return '|\\sin ' + b + '|'; }, P: [1, 1], id: 'abssin' },
    { e: function (b) { return '\\sin ' + b + '+|\\sin ' + b + '|'; }, P: [2, 1], id: 'sin+abs' },
    { e: function (b) { return '\\sin ' + b + '\\cos ' + b; }, P: [1, 1], id: 'prod' },
    { e: function (b) { return '|\\sin ' + b + '+\\cos ' + b + '|'; }, P: [1, 1], id: 'abssum' },
    { e: function (b) { return '\\cos^2 ' + b + '-\\sin^2 ' + b; }, P: [1, 1], id: 'cos2' }
  ];
  L3.absPeriodSum = function (r) {
    var i1 = r.int(0, PERT.length - 1), i2 = r.int(0, PERT.length - 1); while (i2 === i1) i2 = r.int(0, PERT.length - 1);
    var b1 = r.pick([1, 1, 2, 3]), b2 = r.pick([1, 1, 2, 3]);
    function bT(b) { return b === 1 ? 'x' : b + 'x'; }
    var P1 = Fr.div(F(PERT[i1].P[0], PERT[i1].P[1]), F(b1)), P2 = Fr.div(F(PERT[i2].P[0], PERT[i2].P[1]), F(b2)), S = Fr.add(P1, P2);
    return { q: '設 ' + T('f(x)=' + PERT[i1].e(bT(b1))) + '、' + T('g(x)=' + PERT[i2].e(bT(b2))) + ' 的最小正週期分別為 ' + T('p') + '、' + T('q') + '，求 ' + T('p+q') + '。',
      a: T('p+q=' + piTex(S.n, S.d)) + '（' + T('p=' + piTex(P1.n, P1.d)) + '、' + T('q=' + piTex(P2.n, P2.d)) + '）',
      h: '把 $x$ 換成 $x+\\dfrac{\\pi}{2b}$ 試「$|\\sin|$ 與 $|\\cos|$ 互換」；絕對值把負半波翻上來、平方降冪成 $2bx$、乘積用倍角；先各自找出 $p$、$q$ 再相加。', p: { t1: PERT[i1].id, b1: b1, t2: PERT[i2].id, b2: b2, P1: [P1.n, P1.d], P2: [P2.n, P2.d], sum: [S.n, S.d] } };
  };

  /* L3-6　tan 與一個坐標的正負 → 定象限，再判斷五個敘述（多選） */
  L3.quadTanPoint = function (r) {
    var pq = r.pick([[2, 1], [3, 1], [1, 2], [1, 3], [3, 2], [2, 3], [4, 3], [3, 4]]), tsg = r.sign();
    var coord = r.pick(['x', 'y']), csg = r.sign();
    /* tanθ = tsg·pq[0]/pq[1]；由 coord 的正負決定象限 */
    var quad = coord === 'y' ? (csg > 0 ? (tsg > 0 ? 1 : 2) : (tsg > 0 ? 3 : 4)) : (csg > 0 ? (tsg > 0 ? 1 : 4) : (tsg > 0 ? 3 : 2));
    var xs = (quad === 1 || quad === 4) ? 1 : -1, ys = (quad <= 2) ? 1 : -1;
    var R = Math.hypot(pq[0], pq[1]), s = ys * pq[0] / R, c = xs * pq[1] / R, th = Math.atan2(s, c);
    var q2 = quadrant(((th * 2 * 180 / Math.PI) % 360 + 360) % 360);
    var pool = [
      { id: 'sgtc', tex: '\\sin\\theta\\gt\\cos\\theta', v: s > c },
      { id: 'same2', txt: '標準位置角 $\\theta$ 與 $2\\theta$ 的終邊在同一象限', v: q2 === quad },
      { id: 'cos2neg', tex: '\\cos2\\theta\\lt0', v: c * c - s * s < 0 },
      { id: 'sinhalf', tex: '\\sin\\dfrac{\\theta}{2}\\gt0', v: false, fixed: true },
      { id: 'halfsin', tex: '\\dfrac12\\sin\\theta\\lt\\tan\\dfrac{\\theta}{2}', v: s / 2 < s / (1 + c) },
      { id: 'sin2pos', tex: '\\sin2\\theta\\gt0', v: 2 * s * c > 0 },
      { id: 'tan2neg', tex: '\\tan2\\theta\\lt0', v: (2 * s * c) / (c * c - s * s) < 0 },
      { id: 'sumpos', tex: '\\sin\\theta+\\cos\\theta\\gt0', v: s + c > 0 },
      { id: 'absgt', tex: '|\\sin\\theta|\\gt|\\cos\\theta|', v: Math.abs(s) > Math.abs(c) }
    ];
    var chosen = r.shuffle(pool).slice(0, 5), ans = [];
    var nT = chosen.filter(function (o) { return o.v; }).length;
    if (nT === 0 || nT === 5) return L3.quadTanPoint(makeRng(r.int(1, 1e6)));
    var q = '廣義角 ' + T('\\theta') + ' 的頂點為原點、始邊為 ' + T('x') + ' 軸正向，' + T('\\tan\\theta=' + fracTex(tsg * pq[0], pq[1])) + '，且終邊上一點 ' + T('P') + ' 的 ' + T(coord) + ' 坐標為 ' + T(csg > 0 ? r.pick([1, 2, 3]) : -r.pick([1, 2, 3])) + '。選出正確的選項：<br>' +
      chosen.map(function (o, i) { if (o.v) ans.push(i + 1); return '(' + (i + 1) + ') ' + (o.tex ? T(o.tex) : o.txt); }).join('　');
    return { q: q, a: '(' + ans.join(')(') + ')', h: '$\\tan\\theta' + (tsg > 0 ? '\\gt0' : '\\lt0') + '$ 且 $' + coord + (csg > 0 ? '\\gt0' : '\\lt0') + '$ ⟹ 第' + QN[quad] + '象限，取 $P(' + (xs * pq[1]) + ',' + (ys * pq[0]) + ')$、$r=' + sqrtTex(pq[0] * pq[0] + pq[1] * pq[1]) + '$ 逐項算；$\\dfrac{\\theta}{2}$ 的象限因 $\\theta$ 可加減 $2\\pi$ 而不確定，$\\tan\\dfrac{\\theta}{2}=\\dfrac{\\sin\\theta}{1+\\cos\\theta}$ 則是確定的。', p: { p: pq[0], q: pq[1], tsg: tsg, coord: coord, csg: csg, quad: quad, ids: chosen.map(function (o) { return o.id; }), ans: ans } };
  };

  /* 齊次二次式的排版：p cos²x + q sin x cos x + r sin²x（q 可為 √3 型） */
  function homogTex(pc, qn, qS3, rs) {
    var parts = [], first = true;
    if (pc !== 0) { parts.push(coefTex(pc, false, first) + '\\cos^2x'); first = false; }
    if (qn !== 0) { parts.push(coefTex(qn, qS3, first) + '\\sin x\\cos x'); first = false; }
    if (rs !== 0) { parts.push(coefTex(rs, false, first) + '\\sin^2x'); first = false; }
    return parts.join('');
  }
  /* L3-7　齊次式方程 → 降冪成 2x、疊合、在 (0,π) 解 */
  var SINV = { 2: [2, 10], '-2': [14, 22], 4: [6], '-4': [18], 0: [0, 12], 3: [3, 9], '-3': [15, 21] };   /* v 代碼 → sin u = v 的 u（K 單位，[0,24)）；2=½, 4=1, 3=√2/2 */
  var VTEX = { 2: '\\dfrac12', '-2': '-\\dfrac12', 4: '1', '-4': '-1', 0: '0', 3: '\\dfrac{\\sqrt2}{2}', '-3': '-\\dfrac{\\sqrt2}{2}' };
  L3.homogEq = function (r) {
    var rows = COMB.filter(function (row) { return Math.abs(row[1]) === 1; }), row = r.pick(rows), m = r.pick([1, 1, 2]);
    var aS3 = Math.abs(row[0]) === 3, aSg = row[0] < 0 ? -1 : 1, bSg = row[1] < 0 ? -1 : 1;
    var A = aSg * m, B = bSg * m;                                       /* A sin2x（A 可帶√3）+ B cos2x */
    var rs = r.int(-2, 2), pc = rs + 2 * B, qn = 2 * A;                 /* p−r = 2B, q = 2A */
    var R2 = row[2] * m * m, thK = row[3] * 12 / row[4];
    var vcode = R2 === 2 * m * m ? r.pick([3, -3]) : r.pick([2, -2, 4, -4, 0]);
    var Cv = { 2: m, '-2': -m, 4: 2 * m, '-4': -2 * m, 0: 0, 3: m, '-3': -m }[vcode];     /* C = √R2·v */
    var d = Cv + (pc + rs) / 2;
    var sols = [];
    SINV[vcode].forEach(function (u0) { for (var n = -1; n <= 1; n++) { var u = u0 + 24 * n; if (u > thK && u < thK + 24) sols.push(u - thK); } });
    sols.sort(function (x, y) { return x - y; });
    if (!sols.length) return L3.homogEq(makeRng(r.int(1, 1e6)));
    var solT = sols.map(function (u) { return piTex(u, 24); }).join(',\\ ');
    return { q: '設 ' + T('0\\lt x\\lt\\pi') + '，解方程式 ' + T(homogTex(pc, qn, aS3, rs) + '=' + d) + '。', a: T('x=' + solT),
      h: '$\\cos^2x=\\dfrac{1+\\cos2x}{2}$、$\\sin^2x=\\dfrac{1-\\cos2x}{2}$、$2\\sin x\\cos x=\\sin2x$ 全部降冪，整理成 $' + coefTex(A, aS3, true) + '\\sin2x' + coefTex(B, false, false) + '\\cos2x=' + Cv + '$，疊合成 $' + sqrtTex(R2) + '\\sin\\left(2x' + sgnPi(thK) + '\\right)=' + Cv + '$，注意 $2x' + sgnPi(thK) + '$ 的範圍是開區間。',
      p: { aS3: aS3, A: A, B: B, pc: pc, qn: qn, rs: rs, d: d, R2: R2, thK: thK, vcode: vcode, sols: sols } };
  };

  /* L3-8　分式相減／相加 → 通分，分子疊合、分母倍角 */
  var FRP = [{ a: [1, true], b: [1, false], R2: 4, phi: 30 }, { a: [1, false], b: [1, true], R2: 4, phi: 60 }, { a: [1, false], b: [1, false], R2: 2, phi: 45 }];
  L3.fracSubCombine = function (r) {
    var pr = r.pick(FRP), m = r.pick([1, 2, 3, 4]), form = r.pick(['-', '+']), swap = r() < 0.4, guard = 0, alpha, val, cand;
    var av = (pr.a[1] ? SQ3 : 1), bv = (pr.b[1] ? SQ3 : 1), R = Math.sqrt(pr.R2);
    var alphas = form === '-' ? [(270 - pr.phi) / 3, (90 - pr.phi) / 3] : [(90 + pr.phi) / 3, (270 + pr.phi) / 3, (450 - pr.phi) / 3];
    alphas = alphas.filter(function (a) { return a > 0 && a < 180 && a % 15 !== 0; });
    while (guard++ < 10) {
      alpha = r.pick(alphas);
      var s = Math.sin(alpha * Math.PI / 180), c = Math.cos(alpha * Math.PI / 180);
      val = m * av / s + (form === '-' ? -1 : 1) * m * bv / c;
      if (swap) val = -val;                                          /* 寫成 b/cos ∓ a/sin：整體變號（'+' 時不變號） */
      if (swap && form === '+') val = -val;
      cand = null;
      [1, -1, 2, -2, 4, -4].forEach(function (k) { if (Math.abs(val - k * m * R) < 1e-9) cand = k; });
      if (cand !== null) break;
    }
    if (cand === null) return L3.fracSubCombine(makeRng(r.int(1, 1e6)));
    var af = F(alpha, 180), aT = piTex(af.n, af.d), angT = '\\frac{' + (af.n === 1 ? '' : af.n) + '\\pi}{' + af.d + '}';
    var ans = surdOver(cand * m, pr.R2, 1);
    var numT = function (mm, s3) { return s3 ? ((mm === 1 ? '' : mm) + '\\sqrt3') : String(mm); };
    var cT = function (mm, s3) { var s = numT(mm, s3); return s === '1' ? '' : s; };                   /* 當係數用：1 不寫 */
    var tA = '\\dfrac{' + numT(m, pr.a[1]) + '}{\\sin' + angT + '}', tB = '\\dfrac{' + numT(m, pr.b[1]) + '}{\\cos' + angT + '}';
    var qT = swap ? tB + form + tA : tA + form + tB;
    return { q: '求 ' + T(qT) + ' 之值。',
      a: T(ans), h: '$' + aT + '=' + alpha + '^\\circ$，通分後分子 $' + (swap && form === '-' ? cT(m, pr.b[1]) + '\\sin' + alpha + '^\\circ-' + cT(m, pr.a[1]) + '\\cos' + alpha + '^\\circ' : cT(m, pr.a[1]) + '\\cos' + alpha + '^\\circ' + (form === '-' ? '-' : '+') + cT(m, pr.b[1]) + '\\sin' + alpha + '^\\circ') + '$ 可以疊合成 $' + sqrtTex(pr.R2 * m * m) + '\\cos(' + alpha + '^\\circ' + (form === '-' ? '+' : '-') + pr.phi + '^\\circ)$（差一個正負號）；分母 $\\sin' + alpha + '^\\circ\\cos' + alpha + '^\\circ=\\dfrac12\\sin' + (2 * alpha) + '^\\circ$，兩個角互補或互餘。', p: { aS3: pr.a[1], bS3: pr.b[1], m: m, form: form, swap: swap, alpha: alpha, R2: pr.R2, k: cand } };
  };

  /* L3-9　cos(θ/2)−sin(θ/2) 已知 → 平方得 sinθ；頂角 = 180°−2θ */
  L3.halfDiffIsos = function (r) {
    var pq = r.pick([[2, 3], [1, 2], [3, 4], [1, 4], [3, 5], [4, 5], [5, 13], [1, 3], [2, 5], [1, 5], [2, 7], [3, 7], [5, 7], [1, 6], [5, 6], [3, 8], [5, 8], [7, 9], [4, 9], [2, 9], [3, 10], [7, 10], [4, 7], [12, 13], [8, 17], [15, 17]]), p = pq[0], q = pq[1];
    var ask = r.pick(['tan', 'tan', 'sin', 'cos']);
    var given = surdOver(1, (q - p) * q, q);                            /* √((q−p)/q) */
    var ans;
    if (ask === 'tan') { var den = q * q - 2 * p * p; ans = { c: -2 * p * (den < 0 ? -1 : 1), r: q * q - p * p, d: Math.abs(den) }; }
    else if (ask === 'sin') ans = { c: 2 * p, r: q * q - p * p, d: q * q };
    else ans = { c: 2 * p * p - q * q, r: 1, d: q * q };
    return { q: '等腰三角形的底角為 ' + T('\\theta') + '、頂角為 ' + T('\\varphi') + '，且 ' + T('\\cos\\dfrac{\\theta}{2}-\\sin\\dfrac{\\theta}{2}=' + given) + '，求 ' + T('\\' + ask + '\\varphi') + '。',
      a: T('\\' + ask + '\\varphi=' + surd3(ans)), h: '平方：$1-\\sin\\theta=' + Fr.tex(F(q - p, q)) + '$ ⟹ $\\sin\\theta=' + Fr.tex(F(p, q)) + '$；底角是銳角，$\\cos\\theta=' + surdOver(1, q * q - p * p, q) + '$；$\\varphi=180^\\circ-2\\theta$ ⟹ $\\sin\\varphi=\\sin2\\theta$、$\\cos\\varphi=-\\cos2\\theta$、$\\tan\\varphi=-\\tan2\\theta$。', p: { p: p, q: q, ask: ask, ans: [ans.c, ans.r, ans.d] } };
  };

  /* 依 θ 的單位要求挑區間：unit=3（π/4 型）或 2（π/6 型）；scale=2 時 lo,hi 任意整數也行（u=2k 為偶數） */
  function pickInterval(r, unit, scale) {
    var step = scale === 2 ? (unit === 3 ? 3 : 1) : unit;
    var lo = step * r.int(-4, 4), len = step * r.int(2, 5); if (scale === 2 && step === 1) len = r.int(3, 8);
    return [lo, lo + len];
  }
  /* L3-10　sin x cos x 與 sin²x／cos²x 混合 → 降冪、疊合、區間最值 */
  L3.sinCosMixRange = function (r) {
    var rows = COMB.filter(function (row) { return Math.abs(row[1]) === 1; }), row = r.pick(rows), m = r.pick([1, 1, 2]);
    var aS3 = Math.abs(row[0]) === 3, A = (row[0] < 0 ? -1 : 1) * m, B = (row[1] < 0 ? -1 : 1) * m;
    var shape = r.pick(['pr', 'r', 'p']), rs = shape === 'pr' ? -B : shape === 'r' ? -2 * B : 0, pc = rs + 2 * B, qn = 2 * A;
    var K = F(pc + rs, 2), R2 = row[2] * m * m, thK = row[3] * 12 / row[4];
    var iv = pickInterval(r, row[4] === 4 ? 3 : 2, 2), lo = iv[0], hi = iv[1];
    var ex = extremaOn(R2, thK, lo, hi, 2);
    if (ex.flat) return L3.sinCosMixRange(makeRng(r.int(1, 1e6)));
    return { q: '設 ' + T(kTex(lo) + '\\le x\\le' + kTex(hi)) + '，求 ' + T('f(x)=' + homogTex(pc, qn, aS3, rs)) + ' 的最大值與最小值。',
      a: '最大值 ' + T(mixTex(K, ex.max.c, ex.max.r, ex.max.d)) + '（' + T(xs24Tex(ex.maxXs)) + '），最小值 ' + T(mixTex(K, ex.min.c, ex.min.r, ex.min.d)) + '（' + T(xs24Tex(ex.minXs)) + '）',
      h: '降冪：$f(x)=' + coefTex(A, aS3, true) + '\\sin2x' + coefTex(B, false, false) + '\\cos2x' + (K.n === 0 ? '' : (K.n > 0 ? '+' : '') + Fr.tex(K)) + '=' + sqrtTex(R2) + '\\sin\\left(2x' + sgnPi(thK) + '\\right)' + (K.n === 0 ? '' : (K.n > 0 ? '+' : '') + Fr.tex(K)) + '$，再看 $2x' + sgnPi(thK) + '$ 跑過 $\\left[' + kTex(2 * lo + thK) + ',' + kTex(2 * hi + thK) + '\\right]$ 的哪一段。',
      p: { aS3: aS3, A: A, B: B, pc: pc, qn: qn, rs: rs, lo: lo, hi: hi, R2: R2, thK: thK, K: [K.n, K.d], maxX24: ex.maxX24, minX24: ex.minX24, maxXs: ex.maxXs, minXs: ex.minXs, max: [ex.max.c, ex.max.r, ex.max.d], min: [ex.min.c, ex.min.r, ex.min.d] } };
  };

  /* L3-11　先展開再疊合，區間最值 */
  L3.expandCombineRange = function (r) {
    var fam = r.pick([1, 2, 3, 4]), m = r.pick([1, 1, 2]), sA = r.sign(), form = r.pick(['cos', 'sin']);
    /* 展開 A·trig(x+φ1) 得 a1 sin x + b1 cos x，記為 {n, s3} */
    var A, phiK, a1, b1, trig = 'sin';
    if (fam === 1) { A = 2 * m * sA; phiK = 2; a1 = { n: m * sA, s3: true }; b1 = { n: m * sA, s3: false }; }
    else if (fam === 2) { A = 2 * m * sA; phiK = 4; a1 = { n: m * sA, s3: false }; b1 = { n: m * sA, s3: true }; }
    else if (fam === 3) { A = m * sA; phiK = 3; a1 = { n: m * sA, s3: false }; b1 = { n: m * sA, s3: false }; }     /* A 實際是 m√2 */
    else { trig = 'cos'; A = 2 * m * sA; phiK = 4; a1 = { n: -m * sA, s3: true }; b1 = { n: m * sA, s3: false }; }
    /* 加上 B·form x：讓對應的係數反號 */
    var Bn, Bs3, a, b;
    if (form === 'cos') { Bn = -2 * b1.n; Bs3 = b1.s3; a = a1; b = { n: -b1.n, s3: b1.s3 }; }
    else { Bn = -2 * a1.n; Bs3 = a1.s3; a = { n: -a1.n, s3: a1.s3 }; b = b1; }
    var row = combRow(a.s3, a.n < 0 ? -1 : 1, b.s3, b.n < 0 ? -1 : 1);
    if (!row) return L3.expandCombineRange(makeRng(r.int(1, 1e6)));
    var R2 = row[2] * m * m, thK = row[3] * 12 / row[4];
    var iv = pickInterval(r, row[4] === 4 ? 3 : 2, 1), lo = iv[0], hi = iv[1];
    var ex = extremaOn(R2, thK, lo, hi, 1);
    if (ex.flat) return L3.expandCombineRange(makeRng(r.int(1, 1e6)));
    var AT = fam === 3 ? ((Math.abs(A) === 1 ? '' : Math.abs(A)) + '\\sqrt2') : String(Math.abs(A));
    var fT = (A < 0 ? '-' : '') + AT + '\\' + trig + '\\left(x+' + piTex(phiK, 12) + '\\right)' + coefTex(Bn, Bs3, false) + '\\' + form + ' x';
    return { q: '設 ' + T('f(x)=' + fT) + '，' + T(kTex(lo) + '\\le x\\le' + kTex(hi)) + '。若 ' + T('f(x)') + ' 的最大值為 ' + T('M') + '、最小值為 ' + T('N') + '，求 ' + T('(M,N)') + '。',
      a: T('(M,N)=\\left(' + surd3(ex.max) + ',' + surd3(ex.min) + '\\right)') + '（' + T(xs24Tex(ex.maxXs)) + ' 取最大、' + T(xs24Tex(ex.minXs)) + ' 取最小）',
      h: '先把 $' + AT + '\\' + trig + '\\left(x+' + piTex(phiK, 12) + '\\right)$ 用和角展開，合併後 $f(x)=' + coefTex(a.n, a.s3, true) + '\\sin x' + coefTex(b.n, b.s3, false) + '\\cos x=' + sqrtTex(R2) + '\\sin\\left(x' + (thK < 0 ? '-' : '+') + piTex(Math.abs(thK), 12) + '\\right)$，再看 $x' + (thK < 0 ? '-' : '+') + piTex(Math.abs(thK), 12) + '$ 跑過 $\\left[' + kTex(lo + thK) + ',' + kTex(hi + thK) + '\\right]$ 的哪一段。',
      p: { fam: fam, m: m, sA: sA, form: form, Bn: Bn, Bs3: Bs3, lo: lo, hi: hi, R2: R2, thK: thK, maxX24: ex.maxX24, minX24: ex.minX24, maxXs: ex.maxXs, minXs: ex.minXs, max: [ex.max.c, ex.max.r, ex.max.d], min: [ex.min.c, ex.min.r, ex.min.d] } };
  };

  /* L3-12　tanA、tanB 是兩根 ＋ 第三角已知 → tan(A+B) = −tanC */
  L3.tanRootsTriangle = function (r) {
    var guard = 0;
    while (guard++ < 60) {
      var p = r.pick([-3, -2, -1, 1, 2, 3]), q = r.int(-3, 3), rr = r.pick([-3, -2, -1, 1, 2, 3]), s = r.int(-2, 2), C = r.pick([45, 135]), t = C === 45 ? 1 : -1;
      if (p === t * rr) continue;
      var a = F(t * (s - 1) - q, p - t * rr);
      var av = Fr.toNum(a), S = p * av + q, P = rr * av + s, disc = S * S - 4 * P;
      if (disc <= 1e-9) continue;
      if (Math.abs(P) < 1e-9) continue;                                /* 兩根之積 0 ⟹ 有一個 tan=0，角是 0°，三角形退化 */
      var x1 = (S - Math.sqrt(disc)) / 2, x2 = (S + Math.sqrt(disc)) / 2;
      var A1 = Math.atan(x1) * 180 / Math.PI, A2 = Math.atan(x2) * 180 / Math.PI; if (A1 < 0) A1 += 180; if (A2 < 0) A2 += 180;
      if (Math.abs(A1 + A2 + C - 180) > 1e-6) continue;
      var pT = (Math.abs(p) === 1 ? '' : Math.abs(p)) + 'a', qT = q === 0 ? '' : (p > 0 ? signed(q) : signed(-q));
      var cT = (Math.abs(rr) === 1 ? '' : Math.abs(rr)) + 'a' + (s === 0 ? '' : (rr > 0 ? signed(s) : signed(-s)));
      var polyT = 'x^2' + (p > 0 ? '-' : '+') + (q === 0 ? pT : '(' + pT + qT + ')') + 'x' + (rr > 0 ? '+' : '-') + (s === 0 ? cT : '(' + cT + ')') + '=0';
      return { q: '在 ' + T('\\triangle ABC') + ' 中，' + T('\\tan A') + '、' + T('\\tan B') + ' 為 ' + T(polyT) + ' 的兩根，且 ' + T('\\angle C=' + C + '^\\circ') + '，求 ' + T('a') + '。',
        a: T('a=' + Fr.tex(a)), h: '$A+B=180^\\circ-C$ ⟹ $\\tan(A+B)=-\\tan C=' + (-t) + '$；根與係數：$\\tan A+\\tan B=' + pT + qT + '$、$\\tan A\\tan B=' + (Math.abs(rr) === 1 ? (rr < 0 ? '-' : '') : rr) + 'a' + (s === 0 ? '' : signed(s)) + '$，代入 $\\dfrac{\\text{和}}{1-\\text{積}}=' + (-t) + '$ 解一次方程。', p: { p: p, q: q, r: rr, s: s, C: C, ans: [a.n, a.d] } };
    }
    return L3.tanRootsTriangle(makeRng(r.int(1, 1e6)));
  };

  /* L3-13　兩式平方相加，交叉項是 sin(α+β) 或 cos(α−β) */
  var VALS = [{ t: '1', c: 1, r: 1, d: 1 }, { t: '\\sqrt2', c: 1, r: 2, d: 1 }, { t: '\\sqrt3', c: 1, r: 3, d: 1 }, { t: '\\dfrac12', c: 1, r: 1, d: 2 }, { t: '\\dfrac32', c: 3, r: 1, d: 2 }, { t: '\\dfrac{\\sqrt3}{2}', c: 1, r: 3, d: 2 }, { t: '\\dfrac{\\sqrt2}{2}', c: 1, r: 2, d: 2 }, { t: '0', c: 0, r: 1, d: 1 }, { t: '\\dfrac{\\sqrt6}{2}', c: 1, r: 6, d: 2 }, { t: '\\dfrac{\\sqrt5}{2}', c: 1, r: 5, d: 2 }, { t: '-1', c: -1, r: 1, d: 1 }, { t: '-\\dfrac12', c: -1, r: 1, d: 2 }, { t: '-\\sqrt2', c: -1, r: 2, d: 1 }];
  L3.crossSquareSum = function (r) {
    var guard = 0;
    while (guard++ < 50) {
      var vm = r.pick(VALS), vn = r.pick(VALS);
      var m2 = F(vm.c * vm.c * vm.r, vm.d * vm.d), n2 = F(vn.c * vn.c * vn.r, vn.d * vn.d), tot = Fr.add(m2, n2);
      if (tot.n < 0 || Fr.toNum(tot) > 4 || tot.d !== 1) continue;
      var kind = r.pick(['ab+', 'ab-', 'ab+']), ask;
      var base = kind === 'ab-' ? Fr.div(Fr.sub(F(2), tot), F(2)) : Fr.div(Fr.sub(tot, F(2)), F(2));   /* sin(α+β) 或 cos(α−β)／cos(α+β) */
      var eqs, target, ansF;
      if (kind === 'ab+') { eqs = '\\cos\\alpha+\\sin\\beta=' + vm.t + '\\\\ \\sin\\alpha+\\cos\\beta=' + vn.t; ask = r.pick(['\\sin(\\alpha+\\beta)', '\\cos(2\\alpha+2\\beta)']); }
      else if (kind === 'ab-') { eqs = '\\sin\\alpha+\\sin\\beta=' + vm.t + '\\\\ \\cos\\alpha-\\cos\\beta=' + vn.t; ask = r.pick(['\\cos(\\alpha+\\beta)', '\\cos(2\\alpha+2\\beta)']); }
      else { kind = 'diff'; eqs = '\\cos\\alpha+\\cos\\beta=' + vm.t + '\\\\ \\sin\\alpha+\\sin\\beta=' + vn.t; ask = r.pick(['\\cos(\\alpha-\\beta)', '\\cos(2\\alpha-2\\beta)']); }
      var dbl = ask.indexOf('2') >= 0;
      ansF = dbl ? (ask.indexOf('+2') >= 0 && kind === 'ab+' ? Fr.sub(F(1), Fr.mul(F(2), Fr.mul(base, base))) : Fr.sub(Fr.mul(F(2), Fr.mul(base, base)), F(1))) : base;
      return { q: '若 ' + T('\\begin{cases}' + eqs + '\\end{cases}') + '，求 ' + T(ask) + '。', a: T(ask + '=' + Fr.tex(ansF)),
        h: '兩式平方相加：$\\sin^2+\\cos^2$ 各收成 $1$，交叉項恰是 $2' + (kind === 'ab+' ? '\\sin(\\alpha+\\beta)' : kind === 'ab-' ? '\\cdot(-\\cos(\\alpha+\\beta))' : '\\cos(\\alpha-\\beta)') + '$：$2+2\\cdot(\\ldots)=' + Fr.tex(tot) + '$' + (dbl ? '；再用 $\\cos2u=1-2\\sin^2u=2\\cos^2u-1$。' : '。'), p: { kind: kind, m: [vm.c, vm.r, vm.d], n: [vn.c, vn.r, vn.d], ask: ask, base: [base.n, base.d], ans: [ansF.n, ansF.d] } };
    }
    return L3.crossSquareSum(makeRng(r.int(1, 1e6)));
  };

  /* L3-14　大角度的誘導公式：先減 2π 的倍數 */
  L3.reduceBigAngle = function (r) {
    var kk = r.pick([7, 9, 11, 13, 15, 17, 19, 21, 23, 25]) * r.pick([1, 1, -1]), fn = r.pick(['sin', 'cos']), sg = r.sign();
    var pq = r.pick([[1, 3], [1, 2], [2, 1], [3, 1], [2, 3], [3, 2], [3, 4], [4, 3]]), tsg = r.sign();
    var rng = r.pick([[1, 3], [2, 4], [0, 2], [-1, 1]]);              /* θ 的範圍（π/2 單位） */
    var quads = { '1,3': tsg > 0 ? 3 : 2, '2,4': tsg > 0 ? 3 : 4, '0,2': tsg > 0 ? 1 : 2, '-1,1': tsg > 0 ? 1 : 4 };
    var quad = quads[rng.join(',')];
    var xs = (quad === 1 || quad === 4) ? 1 : -1, ys = quad <= 2 ? 1 : -1;
    var kmod = ((kk % 4) + 4) % 4, res;                               /* fn(kπ/2 + sg·θ) */
    var sinN = ys * pq[0], cosN = xs * pq[1], rr = pq[0] * pq[0] + pq[1] * pq[1];
    /* 化簡：k 偶數 → 同名；奇數 → 互換；符號用一個「θ 當第一象限」的代表角數值判 */
    var th0 = 0.3, big = kk * Math.PI / 2 + sg * th0, v0 = { sin: Math.sin, cos: Math.cos }[fn](big);
    var useSin = (kmod % 2 === 0) ? (fn === 'sin') : (fn === 'cos');
    var ref = useSin ? Math.sin(th0) : Math.cos(th0), sign = Math.abs(v0 - ref) < 1e-9 ? 1 : -1;
    var numer = sign * (useSin ? sinN : cosN);
    var ans = surdOver(numer, rr, rr);
    var rT = function (k) { return k === 0 ? '0' : piTex(k, 2); };
    return { q: '設 ' + T(rT(rng[0]) + '\\lt\\theta\\lt' + rT(rng[1])) + '，' + T('\\tan\\theta=' + fracTex(tsg * pq[0], pq[1])) + '，求 ' + T('\\' + fn + '\\left(' + piTex(kk, 2) + (sg > 0 ? '+' : '-') + '\\theta\\right)') + '。',
      a: T(ans), h: '$' + piTex(kk, 2) + '=' + piTex(kk - (kmod === 3 ? 3 : kmod), 2).replace(/^0$/, '0') + '+' + (kmod === 0 ? '0' : piTex(kmod, 2)) + '$，先丟掉 $2\\pi$ 的倍數，剩 $\\' + fn + '\\left(' + (kmod === 0 ? '' : piTex(kmod, 2) + (sg > 0 ? '+' : '-')) + (kmod === 0 && sg < 0 ? '-' : '') + '\\theta\\right)=' + (sign < 0 ? '-' : '') + (useSin ? '\\sin' : '\\cos') + '\\theta$；再由 $\\tan\\theta' + (tsg > 0 ? '\\gt0' : '\\lt0') + '$ 與範圍定第' + QN[quad] + '象限，$r=' + sqrtTex(rr) + '$。', p: { k: kk, fn: fn, sg: sg, p: pq[0], q: pq[1], tsg: tsg, rng: rng, quad: quad, ans: ans } };
  };

  /* L3-15　週期模型（潮汐）：代入兩個已知時刻解 a、b，再代目標時刻 */
  L3.tideModel = function (r) {
    var TT = r.pick([12, 24]), phiK = r.pick([0, 2, 4, 6]), a = r.pick([2, 4, 6, 8]), b = r.int(a + 2, 16);
    var NICE = { 0: 1, 4: 0.5, 8: -0.5, 12: -1, 16: -0.5, 20: 0.5, 6: 0, 18: 0 };
    var times = [];
    for (var x = 0; x <= 23; x++) { var u = (x * 12 / TT + phiK); if (u !== Math.floor(u)) continue; u = ((u % 24) + 24) % 24; if (u in NICE) times.push({ x: x, c: NICE[u] }); }
    var pick = r.shuffle(times).slice(0, 3), guard = 0;
    while ((pick.length < 3 || pick[0].c === pick[1].c) && guard++ < 20) pick = r.shuffle(times).slice(0, 3);
    if (pick.length < 3 || pick[0].c === pick[1].c) return L3.tideModel(makeRng(r.int(1, 1e6)));
    pick.sort(function (u, v) { return u.x - v.x; });
    var known = r.shuffle(pick), t1 = known[0], t2 = known[1], t3 = known[2];
    if (t1.c === t2.c) { var tmp = t2; t2 = t3; t3 = tmp; }
    var d = function (t) { return a * t.c + b; };
    var hh = function (x) { return (x < 10 ? '0' : '') + x + '{:}00'; };
    var argT = '\\dfrac{' + (TT === 12 ? '' : '') + 'x}{' + TT + '}\\pi' + (phiK === 0 ? '' : '+' + piTex(phiK, 12));
    return { q: '某海灣的水深 ' + T('d(x)=a\\cos\\left(' + argT + '\\right)+b') + '（' + T('x') + ' 為時刻，單位：時，' + T('a\\gt0') + '）。若當日 ' + T(hh(t1.x)) + ' 水深 ' + T(d(t1)) + ' 公尺、' + T(hh(t2.x)) + ' 水深 ' + T(d(t2)) + ' 公尺，則當日 ' + T(hh(t3.x)) + ' 的水深為多少公尺？',
      a: T(d(t3)) + ' 公尺（' + T('a=' + a + ',\\ b=' + b) + '）', h: '把 $x=' + t1.x + ',' + t2.x + ',' + t3.x + '$ 代進括號，分別是 $' + [t1, t2, t3].map(function (t) { return piTex(((t.x * 12 / TT + phiK) % 24 + 24) % 24, 12); }).join('$、$') + '$，都是特殊角；兩個已知時刻給 $a\\cos(\\cdot)+b$ 的兩條一次方程，解出 $a,b$ 再代第三個時刻。', p: { T: TT, phiK: phiK, a: a, b: b, x1: t1.x, d1: d(t1), x2: t2.x, d2: d(t2), x3: t3.x, d3: d(t3) } };
  };

  /* ══════════ 2026-09-28 擴充：L3-16～L3-18 的類似題 ══════════ */
  /* L3-16　α+β=π/4（或 3π/4）：tan 和角公式交叉相乘，(1±tanα)(1±tanβ)=2 */
  L3.tanPairProd = function (r) {
    var t = r.int(0, 4), q, a, h, p;
    if (t <= 1) {
      var K = (t === 0 ? 3 : 9) + 12 * r.pick([0, 1, -1, 2]), sg = t === 0 ? '+' : '-';
      q = '若 ' + T('\\alpha+\\beta=' + piTex(K, 12)) + '（' + T('\\tan\\alpha') + '、' + T('\\tan\\beta') + ' 都有意義），求 ' + T('(1' + sg + '\\tan\\alpha)(1' + sg + '\\tan\\beta)') + ' 的值。';
      a = T('2');
      h = '$\\tan(\\alpha+\\beta)=\\tan\\left(' + piTex(K, 12) + '\\right)='+ (t === 0 ? '1' : '-1') + '$，把 $\\dfrac{\\tan\\alpha+\\tan\\beta}{1-\\tan\\alpha\\tan\\beta}=' + (t === 0 ? '1' : '-1') + '$ 交叉相乘得 $\\tan\\alpha+\\tan\\beta=' + (t === 0 ? '1-' : '-1+') + '\\tan\\alpha\\tan\\beta$，再把 $(1' + sg + '\\tan\\alpha)(1' + sg + '\\tan\\beta)$ 乘開代進去。';
      p = { t: t, K: K };
    } else if (t <= 3) {
      var S = t === 2 ? r.pick([45, 225]) : r.pick([135, 315]), A, B;
      do { A = S === 45 ? r.int(1, 44) : S === 225 ? r.int(46, 89) : S === 135 ? r.int(1, 89) : r.int(181, 224); B = S - A; } while (A === B || A % 90 === 0 || B % 90 === 0 || (A % 15 === 0 && B % 15 === 0));
      var ex = t === 2 ? '\\tan' + dg(A) + '+\\tan' + dg(B) + '+\\tan' + dg(A) + '\\tan' + dg(B) : '\\tan' + dg(A) + '+\\tan' + dg(B) + '-\\tan' + dg(A) + '\\tan' + dg(B);
      q = '求 ' + T(ex) + ' 的值。'; a = T(t === 2 ? '1' : '-1');
      h = '$' + dg(A) + '+' + dg(B) + '=' + dg(S) + '$，$\\tan' + dg(S) + '=' + (t === 2 ? '1' : '-1') + '$：由 $\\tan(' + dg(A) + '+' + dg(B) + ')$ 的公式交叉相乘，得 $\\tan' + dg(A) + '+\\tan' + dg(B) + '=' + (t === 2 ? '1-' : '-1+') + '\\tan' + dg(A) + '\\tan' + dg(B) + '$，代進去。';
      p = { t: t, A: A, B: B, S: S };
    } else {
      var sd = r.pick([1, 1, 1, 3, 5, 9]), m = sd === 1 ? r.int(1, 20) : sd, cnt = (45 - 2 * m) / sd + 1, n = cnt / 2, terms = [];   /* 角 m, m+sd, …, 45−m：頭尾配對和都是 45° */
      for (var j = 0; j < cnt; j++) terms.push('(1+\\tan' + dg(m + j * sd) + ')');
      q = '求 ' + T(cnt > 4 ? terms.slice(0, 3).join('') + '\\cdots' + terms[cnt - 1] : terms.join('')) + ' 的值。';
      a = T('2^{' + n + '}');
      h = '頭尾配對：$' + dg(m) + '+' + dg(45 - m) + '=45^\\circ$、$' + dg(m + sd) + '+' + dg(45 - m - sd) + '=45^\\circ$、…，角的和是 $45^\\circ$ 的兩個因式相乘等於 $2$；從 $' + dg(m) + '$ 到 $' + dg(45 - m) + '$' + (sd > 1 ? '（每次加 $' + dg(sd) + '$）' : '') + '共 $' + cnt + '$ 個因式，配成 $' + n + '$ 對。';
      p = { t: t, m: m, sd: sd, n: n };
    }
    return { q: q, a: a, h: h, p: p };
  };

  /* L3-17　a sin x + b cos x 疊合後判斷五個敘述（多選） */
  function valCoef(coef, m) { var s3 = Math.abs(coef) === 3; return (coef < 0 ? '-' : '') + (s3 ? (m === 1 ? '' : m) + '\\sqrt3' : String(m)); }
  L3.combineProps = function (r) {
    var row = r.pick(COMB), m = r.pick([1, 1, 2]), R2 = row[2] * m * m, RT = sqrtTex(R2), thK = row[3] * 12 / row[4], R = Math.sqrt(R2);
    var aV = (Math.abs(row[0]) === 3 ? SQ3 : 1) * (row[0] < 0 ? -1 : 1) * m, bV = (Math.abs(row[1]) === 3 ? SQ3 : 1) * (row[1] < 0 ? -1 : 1) * m;
    var f = function (x) { return aV * Math.sin(x) + bV * Math.cos(x); };
    var expr = combTerm(row[0], m, true) + '\\sin x' + combTerm(row[1], m, false) + '\\cos x';
    var pickX = function (base) { var c = [], k; for (k = -2; k <= 3; k++) { var x = base + 12 * k; if (x > -12 && x < 24 && x !== 0) c.push(x); } return r.pick(c); };
    var kinds = r.shuffle(['per', 'max', 'axis', 'ctr', 'solv', 'mono', 'yint']).slice(0, 5), items = [], ans = [];
    kinds.forEach(function (kd) {
      var tr = r() < 0.5, txt, v, x, cc;
      if (kd === 'per') { txt = '圖形的週期為 ' + T(tr ? '2\\pi' : '\\pi'); v = tr; }
      else if (kd === 'max') { txt = T('f(x)') + ' 的最大值為 ' + T(tr ? RT : String(R2)); v = tr; }
      else if (kd === 'axis') { x = pickX(tr ? 6 - thK : -thK); txt = '圖形對稱於直線 ' + T('x=' + piTex(x, 12)); v = tr; }
      else if (kd === 'ctr') { x = pickX(tr ? -thK : 6 - thK); txt = '圖形對稱於點 ' + T('\\left(' + piTex(x, 12) + ',0\\right)'); v = tr; }
      else if (kd === 'solv') { do { cc = r.int(1, 5) * r.sign(); } while (Math.abs(Math.abs(cc) - R) < 0.2); txt = '方程式 ' + T('f(x)=' + cc) + ' 有實數解'; v = Math.abs(cc) <= R; }
      else if (kd === 'mono') {
        var lo = r.int(-6, 18) * 2, len = r.pick([4, 6]), inc = r() < 0.5, allI = true, allD = true;
        for (var i = 1; i < 60; i++) { var u = (lo + len * i / 60 + thK) * Math.PI / 12, dcos = Math.cos(u); if (dcos < 1e-12) allI = false; if (dcos > -1e-12) allD = false; }
        txt = '在 ' + T(piTex(lo, 12) + '\\lt x\\lt' + piTex(lo + len, 12)) + ' 時，' + T('f(x)') + ' 遞' + (inc ? '增' : '減'); v = inc ? allI : allD;
      } else { var yv = tr ? valCoef(row[1], m) : (row[0] === row[1] ? RT : valCoef(row[0], m)); txt = '圖形與 ' + T('y') + ' 軸的交點為 ' + T('\\left(0,' + yv + '\\right)'); v = tr; }
      items.push({ k: kd, txt: txt, v: v });
    });
    var nT = items.filter(function (o) { return o.v; }).length;
    if (nT === 0 || nT === 5) return L3.combineProps(makeRng(r.int(1, 1e6)));
    var q = '設 ' + T('f(x)=' + expr) + '，選出正確的選項：<br>' + items.map(function (o, i) { if (o.v) ans.push(i + 1); return '(' + (i + 1) + ') ' + o.txt; }).join('　');
    var thT = (row[3] < 0 ? '-' : '+') + piTex(Math.abs(row[3]), row[4]);
    return { q: q, a: '(' + ans.join(')(') + ')',
      h: '先疊合：$f(x)=' + RT + '\\sin\\left(x' + thT + '\\right)$。週期 $2\\pi$、最大值 $' + RT + '$；對稱軸令 $x' + thT + '=\\dfrac{\\pi}{2}+k\\pi$，對稱中心令 $x' + thT + '=k\\pi$；$f(x)=c$ 有解 ⟺ $|c|\\le' + RT + '$；遞增看 $x' + thT + '$ 是否整段落在 $\\left[-\\dfrac{\\pi}{2}+2k\\pi,\\dfrac{\\pi}{2}+2k\\pi\\right]$ 內；$y$ 軸交點是 $f(0)$。',
      p: { row: row, m: m, kinds: kinds, ans: ans } };
  };

  /* L3-18　k sin²x + B cos x = D：化成 cos x 的二次方程，由 cos x 的值判斷根落在哪個區間（多選） */
  var QC_IN = [[1, 3], [2, 3], [1, 4], [3, 4], [1, 5], [2, 5], [3, 5], [4, 5], [1, 6], [5, 6]], QC_OUT = [[3, 2], [4, 3], [5, 4], [5, 3], [2, 1], [7, 4]];
  L3.quadCosRoots = function (r) {
    var c1, c2, g = 0, B;
    do {
      c1 = r.pick(QC_IN).slice(); c1[0] *= r.sign();
      c2 = (r() < 0.4 ? r.pick(QC_OUT) : r.pick(QC_IN)).slice(); c2[0] *= r.sign();
      B = c1[1] * c2[0] + c2[1] * c1[0];
    } while ((B === 0 || c1[0] * c2[1] === c2[0] * c1[1]) && g++ < 50);
    var k = c1[1] * c2[1], D = k + c1[0] * c2[0], gg = gcd(gcd(k, Math.abs(B)), Math.abs(D)) || 1;
    k /= gg; B /= gg; D /= gg;
    var eq = (k === 1 ? '' : k) + '\\sin^2x' + (B > 0 ? '+' : '-') + (Math.abs(B) === 1 ? '' : Math.abs(B)) + '\\cos x=' + D;
    var IV = [[0, 4], [4, 6], [6, 8], [8, 12]], BD = [[0.5, 1], [0, 0.5], [-0.5, 0], [-1, -0.5]], ans = [];
    [c1, c2].forEach(function (c) { var v = c[0] / c[1]; BD.forEach(function (b, i) { if (v > b[0] && v < b[1] && ans.indexOf(i + 1) < 0) ans.push(i + 1); }); });
    ans.sort(); if (!ans.length) ans = [5];
    var opts = IV.map(function (iv, i) { return '(' + (i + 1) + ') ' + T('\\left(' + piTex(iv[0], 12) + ',' + piTex(iv[1], 12) + '\\right)'); }).join('　') + '　(5) 以上皆非';
    var quad = (k === 1 ? '' : k) + '\\cos^2x' + (B > 0 ? '-' : '+') + (Math.abs(B) === 1 ? '' : Math.abs(B)) + '\\cos x' + (D - k === 0 ? '' : signed(D - k)) + '=0';
    var out = [c1, c2].filter(function (c) { return Math.abs(c[0]) > c[1]; });
    return { q: '方程式 ' + T(eq) + ' 在下列哪些區間有實根？<br>' + opts, a: '(' + ans.join(')(') + ')',
      h: '$\\sin^2x=1-\\cos^2x$ 代入，整理成 $' + quad + '$，因式分解得 $\\cos x=' + fracTex(c1[0], c1[1]) + '$ 或 $' + fracTex(c2[0], c2[1]) + '$' + (out.length ? '（$' + fracTex(out[0][0], out[0][1]) + '$ 超出 $[-1,1]$，不合）' : '') + '。$x$ 在 $(0,\\pi)$ 時 $\\cos x$ 遞減，四個區間的端點依序對應 $\\cos x=1,\\ \\dfrac12,\\ 0,\\ -\\dfrac12,\\ -1$。',
      p: { c1: c1, c2: c2, k: k, B: B, D: D, ans: ans } };
  };

  var META_L3 = [['radEstimate', '弧度值估大小（多選）'], ['periodFromHighLow', '最高最低點的水平距離 → 週期'], ['tanShiftCoincide', 'tan 平移後重合'], ['rootSumSin', 'sin bx=k 在 (0,Lπ) 的解數與總和'], ['absPeriodSum', '絕對值／平方的週期相加'], ['quadTanPoint', 'tan 與坐標正負定象限（多選）'], ['homogEq', '齊次式方程：降冪、疊合'], ['fracSubCombine', '分式通分後疊合'], ['halfDiffIsos', 'cos(θ/2)−sin(θ/2) 已知的等腰三角形'], ['sinCosMixRange', 'sin x cos x 與平方混合的區間最值'], ['expandCombineRange', '先展開再疊合的區間最值'], ['tanRootsTriangle', '兩根為 tanA、tanB 的三角形'], ['crossSquareSum', '兩式平方相加'], ['reduceBigAngle', '大角度的誘導公式'], ['tideModel', '週期模型（潮汐）'], ['tanPairProd', '和為 π/4：(1+tanα)(1+tanβ)'], ['combineProps', '疊合後的性質（多選）'], ['quadCosRoots', 'cos x 二次方程的根在哪個區間（多選）']];
  /* 固定題 L3-n 對應的類似題型 */
  var L3_FIX = { 'L3-1': 'radEstimate', 'L3-2': 'periodFromHighLow', 'L3-3': 'tanShiftCoincide', 'L3-4': 'rootSumSin', 'L3-5': 'absPeriodSum', 'L3-6': 'quadTanPoint', 'L3-7': 'homogEq', 'L3-8': 'fracSubCombine', 'L3-9': 'halfDiffIsos', 'L3-10': 'sinCosMixRange', 'L3-11': 'expandCombineRange', 'L3-12': 'tanRootsTriangle', 'L3-13': 'crossSquareSum', 'L3-14': 'reduceBigAngle', 'L3-15': 'tideModel', 'L3-16': 'tanPairProd', 'L3-17': 'combineProps', 'L3-18': 'quadCosRoots' };

  /* ══════════════════════════════════════════════════════════
     L0　章首先備診斷（5 型）：國中幾何、高一下三角比、高一上二次函數
     ══════════════════════════════════════════════════════════ */
  var L0 = {};
  L0.pythag = function (r) {
    var t = r.pick(TRIPLES), m = r.pick([1, 1, 2, 3]), a = t[0] * m, b = t[1] * m, c = t[2] * m, ask = r.pick(['c', 'c', 'leg']);
    if (ask === 'c') return { q: '直角三角形的兩股長為 ' + T(a) + ' 與 ' + T(b) + '，求斜邊長。', a: T(c), h: '畢氏定理：斜邊$^2=$ 兩股平方和 $=' + a + '^2+' + b + '^2$。', p: { a: a, b: b, c: c, ask: ask } };
    return { q: '直角三角形的斜邊長為 ' + T(c) + '、一股長為 ' + T(a) + '，求另一股長。', a: T(b), h: '畢氏定理：另一股 $=\\sqrt{' + c + '^2-' + a + '^2}$。', p: { a: a, b: b, c: c, ask: ask } };
  };
  L0.rightTriRatio = function (r) {
    var t = r.pick(TRIPLES), fn = r.pick(['sin', 'cos', 'tan']);
    var a = t[0], b = t[1], c = t[2], val = fn === 'sin' ? F(a, c) : fn === 'cos' ? F(b, c) : F(a, b);
    return { q: '直角 ' + T('\\triangle ABC') + ' 中 ' + T('\\angle C=90^\\circ') + '，' + T('\\overline{BC}=' + a) + '、' + T('\\overline{AC}=' + b) + '、' + T('\\overline{AB}=' + c) + '，求 ' + T('\\' + fn + ' A') + '。', a: T('\\' + fn + ' A=' + Fr.tex(val)), h: '$\\angle A$ 的對邊是 $\\overline{BC}$、鄰邊是 $\\overline{AC}$、斜邊 $\\overline{AB}$：$\\sin=\\dfrac{\\text{對}}{\\text{斜}}$、$\\cos=\\dfrac{\\text{鄰}}{\\text{斜}}$、$\\tan=\\dfrac{\\text{對}}{\\text{鄰}}$。', p: { a: a, b: b, c: c, fn: fn, val: [val.n, val.d] } };
  };
  L0.quadMax = function (r) {
    var s = r.sign(), h = r.int(-4, 4), k = r.int(-6, 6), B = -2 * s * h, C = s * h * h + k;
    var poly = (s < 0 ? '-' : '') + 'x^2' + (B === 0 ? '' : (B > 0 ? '+' : '-') + (Math.abs(B) === 1 ? '' : Math.abs(B)) + 'x') + (C === 0 ? '' : signed(C));
    return { q: '求二次函數 ' + T('y=' + poly) + ' 的' + (s > 0 ? '最小值' : '最大值') + '，並求此時的 ' + T('x') + '。', a: (s > 0 ? '最小值 ' : '最大值 ') + T(k) + '（' + T('x=' + h) + '）', h: '配方：$y=' + (s < 0 ? '-' : '') + '(x' + (h === 0 ? '' : signed(-h)) + ')^2' + (k === 0 ? '' : signed(k)) + '$，頂點 $(' + h + ',' + k + ')$。', p: { s: s, h: h, k: k } };
  };
  L0.circleMeasure = function (r) {
    var rad = r.int(2, 12), deg = r.pick([30, 45, 60, 90, 120, 135, 150, 180, 240, 270]);
    var arc = F(2 * rad * deg, 360), area = F(rad * rad * deg, 360);
    return { q: '半徑 ' + T(rad) + ' 的圓中，圓心角 ' + T(degTex(deg)) + ' 所對的弧長與扇形面積各為何？（以 ' + T('\\pi') + ' 表示）', a: '弧長 ' + T(coefPi(arc)) + '，面積 ' + T(coefPi(area)), h: '弧長 $=2\\pi r\\times\\dfrac{' + deg + '}{360}$，面積 $=\\pi r^2\\times\\dfrac{' + deg + '}{360}$。', p: { r: rad, deg: deg } };
  };
  L0.specialTri = function (r) {
    var kind = r.pick(['306090', '454590']), m = r.int(1, 6);
    if (kind === '454590') {
      var give = r.pick(['leg', 'hyp']);
      if (give === 'leg') return { q: '等腰直角三角形的一股長為 ' + T(m) + '，求斜邊長。', a: T(sqrtTex(2 * m * m)), h: '$45^\\circ$-$45^\\circ$-$90^\\circ$ 三邊比 $1:1:\\sqrt2$。', p: { kind: kind, m: m, give: give } };
      return { q: '等腰直角三角形的斜邊長為 ' + T(2 * m) + '，求一股長。', a: T(sqrtTex(2 * m * m)), h: '斜邊 $=$ 股 $\\times\\sqrt2$ ⟹ 股 $=\\dfrac{' + 2 * m + '}{\\sqrt2}=' + sqrtTex(2 * m * m) + '$。', p: { kind: kind, m: m, give: give } };
    }
    var give2 = r.pick(['short', 'hyp', 'long']);
    if (give2 === 'short') return { q: '直角三角形的一銳角為 ' + T('30^\\circ') + '，其對邊長 ' + T(m) + '，求斜邊與另一股。', a: '斜邊 ' + T(2 * m) + '，另一股 ' + T(sqrtTex(3 * m * m)), h: '$30^\\circ$-$60^\\circ$-$90^\\circ$ 三邊比 $1:\\sqrt3:2$，$30^\\circ$ 對最短邊。', p: { kind: kind, m: m, give: give2 } };
    if (give2 === 'hyp') return { q: '直角三角形的一銳角為 ' + T('30^\\circ') + '，斜邊長 ' + T(2 * m) + '，求兩股。', a: T(m) + ' 與 ' + T(sqrtTex(3 * m * m)), h: '斜邊是最短邊的 $2$ 倍：最短邊 $' + m + '$，另一股 $' + sqrtTex(3 * m * m) + '$。', p: { kind: kind, m: m, give: give2 } };
    return { q: '直角三角形的一銳角為 ' + T('60^\\circ') + '，其對邊長 ' + T(sqrtTex(3 * m * m)) + '，求斜邊與另一股。', a: '斜邊 ' + T(2 * m) + '，另一股 ' + T(m), h: '$60^\\circ$ 對的是 $\\sqrt3$ 那一邊：$' + sqrtTex(3 * m * m) + '\\div\\sqrt3=' + m + '$ 是最短邊。', p: { kind: kind, m: m, give: give2 } };
  };
  var META_L0 = [['pythag', '畢氏定理'], ['rightTriRatio', '直角三角形的三角比'], ['quadMax', '二次函數配方求極值'], ['circleMeasure', '圓的弧長與扇形面積（度數）'], ['specialTri', '30°-60°-90° 與 45°-45°-90°']];
  /* 先備題型 → 該去哪裡複習 */
  var PREREQ = { pythag: { txt: '畢氏定理（國中）', link: null }, rightTriRatio: { txt: '直角三角形的三角比（高一下第四章 三角比）', link: '../g10b-ch04/practice.html#L1' }, quadMax: { txt: '二次函數配方求極值（高一上第三章 多項式）', link: '../g10a-ch03/practice.html#L1' }, circleMeasure: { txt: '圓的弧長與扇形面積（國中，用度數）', link: null }, specialTri: { txt: '特殊直角三角形的邊長比（國中）', link: null } };

  /* ══════════════════════════════════════════════════════════
     對照題：同一型抽兩題，只差一個關鍵特徵（f 由 p 算出；keep 的欄位要相同）
     ══════════════════════════════════════════════════════════ */
  var CONTRAST = {
    'L1.degToRad': { f: function (p) { return p.deg < 0; }, why: '負角化弧度：負號照搬，其他步驟一模一樣。' },
    'L1.radToDeg': { f: function (p) { return p.quad; }, why: '同樣都把 $\\pi$ 當 $180^\\circ$；象限由「化到一圈內」的角決定，不是看分母。' },
    'L1.arcArea': { f: function (p) { return p.k / p.d > 1; }, why: '圓心角超過 $\\pi$ 也一樣套 $s=r\\theta$、$A=\\frac12r^2\\theta$，弧度不用換成度。' },
    'L1.signQuad': { f: function (p) { return p.fn; }, why: '同一個弧度值，不同函數的正負由象限口訣「一全正、二正弦、三正切、四餘弦」決定。' },
    'L1.specialValue': { f: function (p) { return p.fn; }, why: '同一個角：參考角相同，但 $\\sin$、$\\cos$、$\\tan$ 各自的正負不同。' },
    'L1.pointDef': { f: function (p) { return (p.x < 0 ? 'L' : 'R') + (p.y < 0 ? 'D' : 'U'); }, why: '點換到別的象限：$r$ 不變，只有正負號跟著坐標變。' },
    'L1.fromSinQuad': { f: function (p) { return p.quad; }, keep: ['give'], why: '同一個已知值、不同象限：補出來的值大小一樣，只有正負不同。' },
    'L1.coterminal': { f: function (p) { return p.mode; }, why: '度與弧度只是單位不同，做法都是加減整圈。' },
    'L1.reduceFormula': { f: function (p) { return p.k % 180 === 90; }, why: '$\\pi$ 的整數倍函數名不變、$\\frac{\\pi}{2}$ 的奇數倍 $\\sin$、$\\cos$ 互換，兩種情形只差在這裡；正負一律看象限。' },
    'L1.sumExact': { f: function (p) { return p.fn; }, why: '同一個角拆法相同，三個函數各套各的和差角公式。' },
    'L1.cosDiffQuad': { f: function (p) { return p.which; }, why: '和角與差角、$\\sin$ 與 $\\cos$：只差公式中間那個正負號，補值的步驟完全一樣。' },
    'L1.tanSum': { f: function (p) { return p.sgn; }, why: '和與差：分子的號與分母的號同時反過來。' },
    'L1.doubleFromSin': { f: function (p) { return p.give; }, why: '給 $\\sin$ 或給 $\\cos$：補齊另一個的步驟相同，倍角公式不變。' },
    'L1.halfFromCos': { f: function (p) { return p.quad; }, keep: ['askCos'], why: '$\\cos\\theta$ 一樣但 $\\theta$ 的範圍不同 ⟹ $\\frac{\\theta}{2}$ 落在不同象限，開根號後的正負就不同。' },
    'L1.ampPeriod': { f: function (p) { return p.b; }, why: '只有 $b$ 不同：振幅與上下界不變，週期變成 $\\frac{2\\pi}{|b|}$。' },
    'L1.shiftFunc': { f: function (p) { return p.hs; }, why: '左移與右移：括號內的正負號相反（右減左加）。' },
    'L1.combineStd': { f: function (p) { return p.aSign * 10 + p.bSign; }, why: '係數的正負決定 $\\theta$ 的象限，$r$ 完全不變。' },
    'L1.maxMin': { f: function (p) { return p.d; }, why: '常數 $d$ 只是把整個圖上下搬，振幅 $\\sqrt{a^2+b^2}$ 不變。' },
    'L1.basicEq': { f: function (p) { return p.fn; }, why: '同一個值，$\\sin$ 用 $\\pi-x$ 找第二解、$\\cos$ 用 $2\\pi-x$，因為兩者的對稱軸不同。' },
    'L1.periodOf': { f: function (p) { return p.kind; }, why: '$\\sin$、$\\cos$ 取絕對值或平方，週期減半；$\\tan$ 本身週期就是 $\\pi$，取絕對值或平方都不變。' },
    'L2.sectorMax': { f: function (p) { return p.kind === 'perim' || p.kind === 'perimFrac' ? 'P' : 'A'; }, why: '周長固定求面積最大用二次函數頂點；面積固定求周長最小用算幾不等式，兩題答案都是 $\\theta=2$。' },
    'L2.sumProd': { f: function (p) { return p.rg.join(','); }, why: '$\\sin\\theta+\\cos\\theta$ 的值一樣，只有 $\\theta$ 的範圍不同：平方後的結果相同，差的正負由範圍決定。' },
    'L2.quadRootCos2': { f: function (p) { return p.fn; }, why: '根是 $\\sin\\theta$ 用 $1-2\\sin^2\\theta$，根是 $\\cos\\theta$ 用 $2\\cos^2\\theta-1$。' },
    'L2.tanQuad': { f: function (p) { return p.mode; }, why: '正向是代根與係數求 $\\tan(\\alpha+\\beta)$，反向是由 $\\tan(\\alpha+\\beta)$ 反解係數，同一條公式。' },
    'L2.systemSquare': { f: function (p) { return p.form; }, why: '兩式的正負號配置不同，平方相加後交叉項是 $\\cos(A+B)$ 還是 $\\cos(A-B)$、帶正號還是負號。' },
    'L2.halfFromCos2x': { f: function (p) { return p.quad; }, why: '$\\cos2x$ 相同、$x$ 的象限不同：$\\sin x$ 的正負與 $\\frac x2$ 的象限跟著變。' },
    'L2.periodJudge': { f: function (p) { return p.kind; }, why: '不同的合成方式（絕對值、平方、乘積、相加）各有各的週期規則。' },
    'L2.rootCount': { f: function (p) { return p.c; }, why: '只有常數 $c$ 不同：直線平移，與正弦曲線的交點數就變了。' },
    'L2.trigIneq': { f: function (p) { return p.op; }, why: '同一個二次式，不等號方向或含不含等號不同，解集合就在區間內外、端點開閉之間變化。' },
    'L2.squareSub': { f: function (p) { return p.sgn; }, why: '$\\sin x+\\cos x$ 與 $\\sin x-\\cos x$ 換元後範圍都是 $[-\\sqrt2,\\sqrt2]$，二次函數一樣。' },
    'L2.eqSumCount': { f: function (p) { return p.kpos; }, why: '$k$ 的正負決定兩解落在每個週期的前半段還是後半段，總和的公式跟著變。' },
    'L3.tanShiftCoincide': { f: function (p) { return p.dir; }, why: '左移與右移只差 $x$ 換成 $x+s$ 或 $x-s$，其餘推導相同。' },
    'L3.rootSumSin': { f: function (p) { return p.fn + p.kpos; }, why: '$\\sin$ 與 $\\cos$ 的兩解對稱中心不同（$\\frac{\\pi}{2}+2j\\pi$ 對 $2j\\pi+\\pi$），$k$ 的正負決定落在哪半段。' },
    'L3.quadTanPoint': { f: function (p) { return p.coord; }, why: '給 $x$ 坐標或給 $y$ 坐標的正負，配合 $\\tan$ 的正負決定象限的方式不同。' },
    'L3.fracSubCombine': { f: function (p) { return p.form; }, why: '相加或相減，通分後分子的疊合角度不同。' },
    'L3.halfDiffIsos': { f: function (p) { return p.ask; }, why: '同樣先平方得 $\\sin\\theta$，問 $\\tan\\varphi$、$\\sin\\varphi$、$\\cos\\varphi$ 各用不同的倍角公式。' },
    'L3.expandCombineRange': { f: function (p) { return p.form; }, why: '加 $B\\cos x$ 或加 $B\\sin x$，展開後抵銷的是不同的項。' },
    'L3.tanRootsTriangle': { f: function (p) { return p.C; }, why: '$C=45^\\circ$ 與 $135^\\circ$ 只差 $\\tan C$ 的正負，$\\tan(A+B)=-\\tan C$ 的推導相同。' },
    'L3.crossSquareSum': { f: function (p) { return p.kind; }, why: '兩式的組合方式不同，平方相加的交叉項是 $\\sin(\\alpha+\\beta)$、$\\cos(\\alpha+\\beta)$ 還是 $\\cos(\\alpha-\\beta)$。' },
    'L3.reduceBigAngle': { f: function (p) { return p.sg; }, why: '$+\\theta$ 與 $-\\theta$：化簡後差在正負與函數名，象限判斷相同。' }
  };
  /* 2026-09-28 擴充題型的對照題 */
  CONTRAST['L1.sumReverse'] = { f: function (p) { return p.op; }, keep: ['fn'], why: '同一個函數，展開式中間的正負號決定是和角還是差角；$\\cos$ 的號與角的和差相反：$\\cos\\alpha\\cos\\beta-\\sin\\alpha\\sin\\beta$ 是 $\\cos(\\alpha+\\beta)$。' };
  CONTRAST['L1.doubleReverse'] = { f: function (p) { return p.form; }, why: '$2\\sin\\theta\\cos\\theta$ 合成 $\\sin2\\theta$，少了係數 $2$ 就要再乘 $\\dfrac12$；$\\cos^2\\theta-\\sin^2\\theta$、$1-2\\sin^2\\theta$、$2\\cos^2\\theta-1$ 三種寫法都是 $\\cos2\\theta$。' };
  CONTRAST['L1.symAxis'] = { f: function (p) { return p.t % 2; }, keep: ['fn'], why: '同一個函數：$\\sin$ 型的對稱軸令括號 $=\\dfrac{\\pi}{2}+k\\pi$、對稱中心令括號 $=k\\pi$；$\\cos$ 型剛好相反。對稱中心的 $y$ 坐標是中線 $d$，不一定是 $0$。' };
  CONTRAST['L1.trigCompare'] = { f: function (p) { return p.fn; }, why: '$\\sin$、$\\tan$ 在搬過去的區間遞增，角越大值越大；$\\cos$ 在 $[0,\\pi]$ 遞減，角越大值越小，順序要反過來。' };
  CONTRAST['L2.segmentArea'] = { f: function (p) { return p.which; }, why: '劣弓形是扇形減三角形；優弧那一塊是整個圓減劣弓形，三角形的面積變成加回去。' };
  CONTRAST['L2.angleSplit'] = { f: function (p) { return p.form; }, why: '$\\alpha=(\\alpha+\\beta)-\\beta$ 用差角公式、$\\alpha=(\\alpha-\\beta)+\\beta$ 用和角公式；補齊函數值時，$\\alpha+\\beta$ 可能是鈍角，要看給的 $\\cos$ 的正負。' };
  CONTRAST['L2.triCosC'] = { f: function (p) { return p.gA; }, why: '給 $\\cos A$ 時角唯一；給 $\\sin A$ 時 $A$ 可能是銳角也可能是鈍角，要用「$A+B\\lt\\pi$」把不合的那個刪掉。' };
  CONTRAST['L2.quadTrigRange'] = { f: function (p) { return p.dom; }, keep: ['form'], why: '同一個二次式，$x$ 的範圍變了，$t$ 的範圍就跟著變（例如 $0\\le x\\le\\pi$ 時 $\\sin x$ 只在 $[0,1]$），最大最小值要重新看頂點與端點。' };
  CONTRAST['L2.quadTrigEq'] = { f: function (p) { return p.form; }, keep: ['fn'], why: '三種寫法（同一函數、混 $\\sin^2$ 與 $\\cos^2$、混 $\\cos2x$）都先換成同一個函數的二次方程，換完之後解法一模一樣。' };
  CONTRAST['L2.tripleEval'] = { f: function (p) { return p.t; }, why: '$\\sin3\\theta=3\\sin\\theta-4\\sin^3\\theta$、$\\cos3\\theta=4\\cos^3\\theta-3\\cos\\theta$：兩條的次方項係數都是 $4$，正負號位置相反。' };
  CONTRAST['L3.tanPairProd'] = { f: function (p) { return p.t; }, why: '和是 $\\dfrac{\\pi}{4}$ 型（$\\tan=1$）配 $(1+\\tan\\alpha)(1+\\tan\\beta)$，和是 $\\dfrac{3\\pi}{4}$ 型（$\\tan=-1$）配 $(1-\\tan\\alpha)(1-\\tan\\beta)$，乘開後都等於 $2$。' };
  CONTRAST['L3.quadCosRoots'] = { f: function (p) { return p.ans.join(''); }, why: '兩個根的 $\\cos$ 值換了，落在哪個區間就跟著換；先確認根在 $[-1,1]$ 內，再和 $1,\\ \\dfrac12,\\ 0,\\ -\\dfrac12,\\ -1$ 比大小。' };

  function contrastPair(tier, key, seedA, maxTry) {
    var c = CONTRAST[tier + '.' + key]; if (!c) return null;
    var A = wrapItem(tier, key, seedA), fA = c.f(A.p), keep = c.keep || [];
    for (var n = 1; n < (maxTry || 600); n++) {
      var s = (seedA * 7919 + n * 104729) % 900000 + 1;                    /* 連號種子的 LCG 首值幾乎相同，要跳著取 */
      var B = wrapItem(tier, key, s);
      if (c.f(B.p) === fA) continue;
      var ok = true; keep.forEach(function (k) { if (JSON.stringify(B.p[k]) !== JSON.stringify(A.p[k])) ok = false; });
      if (!ok || B.q === A.q) continue;
      return { A: A, B: B, seedB: s, why: c.why };
    }
    return null;
  }
  function wrapItem(tier, key, seed) { return ({ L0: L0, L1: L1, L2: L2, L3: L3 })[tier][key](makeRng(seed)); }

  var META = { L0: META_L0, L1: META_L1, L2: META_L2, L3: META_L3 };

  /* ── HTML 安全：$…$ 裡的 < > 改成 \lt \gt ── */
  function escMath(s) {
    return String(s).replace(/\$([^$]*)\$/g, function (m, inner) { return '$' + inner.replace(/</g, '\\lt ').replace(/>/g, '\\gt ') + '$'; });
  }
  function wrapAll(group, solMap, h1Map) {
    Object.keys(group).forEach(function (k) {
      var f = group[k];
      group[k] = function (r) {
        var o = f(r); o.q = escMath(o.q); o.a = escMath(o.a); o.h = escMath(o.h);
        if (solMap && solMap[k]) o.s = solMap[k](o.p, o).map(escMath);
        if (h1Map && h1Map[k]) o.h1 = escMath(h1Map[k]);
        return o;
      };
    });
  }
  wrapAll(L0); wrapAll(L1, L1_SOL, L1_H1); wrapAll(L2); wrapAll(L3);

  return { makeRng: makeRng, L0: L0, L1: L1, L2: L2, L3: L3, L3_FIX: L3_FIX, META: META, PREREQ: PREREQ, CONTRAST: CONTRAST, contrastPair: contrastPair, _util: { F: F, Fr: Fr, tv: tv, piTex: piTex, exact15: exact15, countRoots: countRoots } };
}));
