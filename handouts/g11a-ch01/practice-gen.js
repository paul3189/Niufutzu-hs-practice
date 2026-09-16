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
     L1　基礎（21 型）
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
    return { q: '將 ' + T(piTex(k, d)) + ' 化為度數，並判斷它是第幾象限角。', a: T(degTex(deg)) + '，' + (qd ? '第' + QN[qd] + '象限角' : '終邊在坐標軸上'), h: '$\\pi=180^\\circ$：$' + piTex(k, d) + '=\\dfrac{' + k + '\\times180^\\circ}{' + d + '}$；判象限先加減 $360^\\circ$，化到 $[0^\\circ,360^\\circ)$ 是 $' + (((deg % 360) + 360) % 360) + '^\\circ$。', p: { k: k, d: d, deg: deg, quad: qd } };
  };
  L1.arcArea = function (r) {
    var rad = r.int(2, 12), k = r.pick([1, 2, 3, 4, 5]), d = r.pick([2, 3, 4, 6]);
    var arc = F(rad * k, d), area = F(rad * rad * k, 2 * d);
    return { q: '一扇形半徑為 ' + T(rad) + '，圓心角為 ' + T(piTex(k, d)) + '，求弧長與面積。', a: '弧長 ' + T(Fr.tex(arc) + '\\pi') + '，面積 ' + T(Fr.tex(area) + '\\pi'), h: '$s=r\\theta=' + rad + '\\times' + piTex(k, d) + '$、$A=\\dfrac12r^2\\theta=\\dfrac12\\times' + rad + '^2\\times' + piTex(k, d) + '$（$\\theta$ 一定用弧度，$\\pi$ 留著不要換）。', p: { r: rad, k: k, d: d } };
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
    return { q: '求 ' + T('\\' + fn + '\\dfrac{' + k + '\\pi}{' + d + '}') + ' 的值。', a: T(vTex(v)), h: '$\\dfrac{' + k + '\\pi}{' + d + '}=' + deg + '^\\circ$，減掉 $360^\\circ$ 的倍數得 $' + (((deg % 360) + 360) % 360) + '^\\circ$' + (quadrant(deg) ? '（第' + QN[quadrant(deg)] + '象限），參考角 $' + (function (a) { a %= 180; return a > 90 ? 180 - a : a; })(((deg % 360) + 360) % 360) + '^\\circ$，再依象限定正負。' : '，終邊在坐標軸上，直接看單位圓上的點。'), p: { fn: fn, k: k, d: d, deg: deg } };
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
    var d = r.pick([3, 4, 6]), k0 = r.int(1, 2 * d - 1); while (k0 % d === 0) k0 = r.int(1, 2 * d - 1);
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
    var split = deg % 90 === 15 ? [deg - 45, 45] : [deg - 30, 30];
    return { q: '求 ' + T('\\' + fn + degTex(deg)) + ' 的精確值。', a: T(v), h: '拆成 ' + T(degTex(split[0]) + (split[1] > 0 ? '+' : '-') + degTex(Math.abs(split[1]))) + ' 再用和角公式。', p: { fn: fn, deg: deg } };
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
      a: T(fnName + '\\dfrac{\\theta}{2}=' + fracTex(sgn * num, den)), h: '半角公式 $' + (askCos ? '\\cos^2\\dfrac{\\theta}{2}=\\dfrac{1+\\cos\\theta}{2}=\\dfrac{1+' + fracTex(row[0], row[1]) + '}{2}' : '\\sin^2\\dfrac{\\theta}{2}=\\dfrac{1-\\cos\\theta}{2}=\\dfrac{1-' + fracTex(row[0], row[1]) + '}{2}') + '$；這裡 $' + piTex(lo / 30, 12) + '\\lt\\dfrac{\\theta}{2}\\lt' + piTex(hi / 30, 12) + '$（第' + QN[quadrant(lo / 2 + 1)] + '象限），決定開根號後的正負。', p: { cosn: row[0], cosd: row[1], quad: qd, askCos: askCos, num: sgn * num, den: den } };
  };

  /* 1-3 圖形與疊合 */
  L1.ampPeriod = function (r) {
    var a = r.int(1, 5) * r.sign(), b = r.pick([1, 2, 3, 4, 0.5]), cK = r.pick([0, 1, -1, 2, -2, 3]), d = r.int(-3, 3), fn = r.pick(['sin', 'cos']);
    var bT = b === 0.5 ? '\\dfrac{x}{2}' : (b === 1 ? 'x' : b + 'x');
    var inner = bT + (cK === 0 ? '' : (cK > 0 ? '+' : '-') + piTex(Math.abs(cK), 6));
    var per = b === 0.5 ? '4\\pi' : (b === 1 ? '2\\pi' : b === 2 ? '\\pi' : '\\dfrac{2\\pi}{' + b + '}');
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

  /* ══════════════════════════════════════════════════════════
     L1 解題步驟（s：每步一段 HTML）與第一層提示（h1：只講「這是哪一型、第一步做什麼」，不帶數字）
     由 p 重算，所以與題目、答案一定一致；答案由頁面另行附在步驟後。
     ══════════════════════════════════════════════════════════ */
  function absT(n) { return n < 0 ? '(' + n + ')' : String(n); }
  function refDeg(deg) { var a = ((deg % 360) + 360) % 360, r = a % 180; return r > 90 ? 180 - r : r; }
  function quadTxt(deg) { var q = quadrant(deg); return q ? '第' + QN[q] + '象限' : '終邊在坐標軸上'; }
  var L1_H1 = {
    degToRad: '這是「度換弧度」：只要記住 $180^\\circ=\\pi$，度數乘上一個固定的比例就好。',
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
    return ['$\\pi=180^\\circ$ ⟹ $' + piTex(p.k, p.d) + '=\\dfrac{' + p.k + '\\times180^\\circ}{' + p.d + '}=' + p.deg + '^\\circ$。',
      (n === 0 ? '$' + p.deg + '^\\circ$ 已在 $[0^\\circ,360^\\circ)$ 內' : '$' + p.deg + '^\\circ' + (n > 0 ? '-' : '+') + Math.abs(n) + '\\times360^\\circ=' + red + '^\\circ$') + '，' + quadTxt(red) + '。'];
  };
  L1_SOL.arcArea = function (p) {
    var arc = F(p.r * p.k, p.d), area = F(p.r * p.r * p.k, 2 * p.d);
    return ['弧長 $s=r\\theta=' + p.r + '\\times' + piTex(p.k, p.d) + '=' + Fr.tex(arc) + '\\pi$。', '面積 $A=\\dfrac12r^2\\theta=\\dfrac12\\times' + p.r + '^2\\times' + piTex(p.k, p.d) + '=' + Fr.tex(area) + '\\pi$。'];
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
    var st = ['$\\dfrac{' + p.k + '\\pi}{' + p.d + '}=' + p.deg + '^\\circ$' + (n ? '，減掉 $' + n + '\\times360^\\circ$ 得 $' + red + '^\\circ$' : '') + '，' + quadTxt(red) + '。'];
    if (q) st.push('參考角 $' + ref + '^\\circ$：$\\' + p.fn + ref + '^\\circ=' + vTex(tv(ref)[p.fn]) + '$；第' + QN[q] + '象限的 $\\' + p.fn + '$ 為' + (v.c < 0 ? '負' : '正') + '，故 $\\' + p.fn + '\\dfrac{' + p.k + '\\pi}{' + p.d + '}=' + vTex(v) + '$。');
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
      '$\\tan\\theta=\\dfrac{\\sin\\theta}{\\cos\\theta}=' + fracTex(p.s, p.R) + '\\div' + fracTex(p.c, p.R) + '=' + fracTex(p.s, p.c) + '$。'];
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
    var sp = p.deg % 90 === 15 ? [p.deg - 45, 45] : [p.deg - 30, 30], A = sp[0], B = sp[1], e = exact15(p.deg)[p.fn];
    var tA = tv(A), tB = tv(B), st;
    if (p.fn === 'sin') st = '\\sin' + A + '^\\circ\\cos' + B + '^\\circ+\\cos' + A + '^\\circ\\sin' + B + '^\\circ=' + vTex(tA.sin) + '\\cdot' + vTex(tB.cos) + '+' + vTex(tA.cos) + '\\cdot' + vTex(tB.sin);
    else if (p.fn === 'cos') st = '\\cos' + A + '^\\circ\\cos' + B + '^\\circ-\\sin' + A + '^\\circ\\sin' + B + '^\\circ=' + vTex(tA.cos) + '\\cdot' + vTex(tB.cos) + '-' + vTex(tA.sin) + '\\cdot' + vTex(tB.sin);
    else st = '\\dfrac{\\tan' + A + '^\\circ+\\tan' + B + '^\\circ}{1-\\tan' + A + '^\\circ\\tan' + B + '^\\circ}=\\dfrac{' + vTex(tA.tan) + '+' + vTex(tB.tan) + '}{1-' + vTex(tA.tan) + '\\cdot' + vTex(tB.tan) + '}';
    return ['$' + p.deg + '^\\circ=' + A + '^\\circ+' + B + '^\\circ$，兩個都是特殊角。', '$\\' + p.fn + p.deg + '^\\circ=' + st + '$。', '化簡' + (p.fn === 'tan' ? '（分母有根號就有理化）' : '') + '得 $' + e + '$。'];
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
      '相除：$' + Fr.tex(num, false) + '\\div' + Fr.tex(den, false) + '=' + Fr.tex(F(p.val[0], p.val[1])) + '$。'];
  };
  L1_SOL.doubleFromSin = function (p) {
    var other = p.give === 'sin' ? 'cos' : 'sin', ov = p.give === 'sin' ? p.c : p.s, gv = p.give === 'sin' ? p.s : p.c;
    return ['補另一個：$|\\' + other + '\\theta|=\\sqrt{1-\\left(' + fracTex(gv, p.R) + '\\right)^2}=' + fracTex(Math.abs(ov), p.R) + '$，第' + QN[p.quad] + '象限 ⟹ $\\' + other + '\\theta=' + fracTex(ov, p.R) + '$。',
      '$\\sin2\\theta=2\\sin\\theta\\cos\\theta=2\\cdot' + fracTex(p.s, p.R) + '\\cdot\\left(' + fracTex(p.c, p.R) + '\\right)=' + Fr.tex(F(2 * p.s * p.c, p.R * p.R)) + '$。',
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
    var per = p.b === 0.5 ? '4\\pi' : p.b === 1 ? '2\\pi' : p.b === 2 ? '\\pi' : '\\dfrac{2\\pi}{' + p.b + '}';
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
    return [why + '。', '$u=' + (p.b === 1 ? 'x' : bT + 'x') + '$，$x$ 的週期是 $u$ 的週期除以 $|b|$：$\\dfrac{' + base + '}{' + bT + '}=' + PT + '$。'];
  };

  var META_L1 = [['degToRad', '度 → 弧度'], ['radToDeg', '弧度 → 度・判象限'], ['arcArea', '弧長與扇形面積'], ['sectorFromArc', '由弧長反推圓心角'], ['signQuad', '弧度值的正負判斷'], ['specialValue', '特殊角的函數值'], ['pointDef', '終邊過一點求三角函數'], ['fromSinQuad', '已知一個函數值求另兩個'], ['coterminal', '同界角與象限'], ['reduceFormula', '誘導公式化簡'],
    ['sumExact', '15° 倍數的精確值'], ['cosDiffQuad', '和差角公式求值'], ['tanSum', 'tan 的和差角'], ['doubleFromSin', '二倍角求值'], ['halfFromCos', '半角求值'],
    ['ampPeriod', '振幅・週期・最大最小'], ['shiftFunc', '平移後的方程式'], ['combineStd', '正餘弦疊合（標準組合）'], ['maxMin', 'a sin x + b cos x 的最值'], ['basicEq', '基本三角方程式'], ['periodOf', '最小正週期']];

  /* ══════════════════════════════════════════════════════════
     L2　中等（16 型）
     ══════════════════════════════════════════════════════════ */
  var L2 = {};

  L2.sectorSys = function (r) {
    var r1 = r.int(2, 6), r2 = r.int(r1 + 1, 9);
    var P = 2 * (r1 + r2), S = r1 * r2;
    var th1 = F(2 * r2, r1), th2 = F(2 * r1, r2);
    return { q: '一扇形的周長為 ' + T(P) + '、面積為 ' + T(S) + '，求其半徑與圓心角（弧度）。',
      a: T('(r,\\theta)=\\left(' + r1 + ',' + Fr.tex(th1) + '\\right)') + ' 或 ' + T('\\left(' + r2 + ',' + Fr.tex(th2) + '\\right)'),
      h: '設弧長 $s$：$2r+s=P$、$\\dfrac12rs=S$，消去 $s$ 得 $r$ 的二次方程，兩個根通常都合法。', p: { P: P, S: S, r1: r1, r2: r2 } };
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
      var a = r.int(1, 9) * r.sign(), val = F(a, 1 - b);
      return { q: '若 ' + T('\\tan\\alpha') + '、' + T('\\tan\\beta') + ' 為方程式 ' + T('x^2' + (a > 0 ? '-' : '+') + (Math.abs(a) === 1 ? '' : Math.abs(a)) + 'x' + signed(b) + '=0') + ' 的兩根，求 ' + T('\\tan(\\alpha+\\beta)') + '。',
        a: T('\\tan(\\alpha+\\beta)=' + Fr.tex(val)), h: '根與係數：$\\tan\\alpha+\\tan\\beta=$ 兩根和、$\\tan\\alpha\\tan\\beta=$ 兩根積，代入 $\\dfrac{\\text{和}}{1-\\text{積}}$。', p: { mode: mode, a: a, b: b, val: [val.n, val.d] } };
    }
    var tv_ = F(r.int(1, 5) * r.sign(), r.pick([1, 2, 3])), aF = Fr.mul(tv_, F(1 - b));
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
    var hint = { abstan: '$\\tan$ 加絕對值週期不變（$\\tan$ 本身已是半個「正弦週期」）。', sincos2: '兩項週期取最小公倍數。', absabs: '$|\\sin|+|\\cos|$ 把 $x$ 換成 $x+\\dfrac{\\pi}{2b}$ 會互換，週期是 $\\dfrac{\\pi}{2b}$。', prod: '$\\sin\\cos=\\dfrac12\\sin(2\\cdot)$，倍角後週期減半。', cos2: '降冪：$\\cos^2=\\dfrac{1+\\cos(2\\cdot)}{2}$。', sum3: '兩項週期 $\\dfrac{2\\pi}{b}$ 與 $\\dfrac{2\\pi}{3b}$，取最小公倍數。' }[kind];
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
    return { q: '方程式 ' + T(lhs + '=x') + ' 有幾個實數解？', a: T(res.cnt) + ' 個', h: '化成 $\\sin x=\\dfrac{x-' + c + '}{' + k + '}$，畫 $y=\\sin x$ 與一條斜率 $\\dfrac1{' + k + '}$ 的直線，直線只在 $|y|\\le1$ 的範圍內有效，數交點。', p: { c: c, k: k, cnt: res.cnt } };
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
    var best = null, worst = null;
    cands.forEach(function (k) {
      var sv = tv((k + thK) * 15).sin, val = vNum(sv);
      if (best === null || val > best.val + 1e-12) best = { k: k, val: val, sv: sv };
      if (worst === null || val < worst.val - 1e-12) worst = { k: k, val: val, sv: sv };
    });
    function fT(sv) { return surdOver(sv.c, R2 * sv.r, sv.d); }
    return { q: '設 ' + T(piTex(lo, 12) + '\\le x\\le' + (hi === 24 ? '2\\pi' : piTex(hi, 12))) + '，求 ' + T('f(x)=' + aT + bT) + ' 的最大值與最小值，並指出對應的 ' + T('x') + '。',
      a: '最大值 ' + T(fT(best.sv)) + '（' + T('x=' + piTex(best.k, 12)) + '），最小值 ' + T(fT(worst.sv)) + '（' + T('x=' + piTex(worst.k, 12)) + '）',
      h: '先疊合成 $' + sqrtTex(R2) + '\\sin(x+\\theta)$，再看 $x+\\theta$ 在給定區間跑過哪一段，最大最小可能在端點或在 $\\dfrac{\\pi}{2}$、$\\dfrac{3\\pi}{2}$ 處。',
      p: { aIsSqrt3: Math.abs(row[0]) === 3, aSign: row[0] < 0 ? -1 : 1, bIsSqrt3: Math.abs(row[1]) === 3, bSign: row[1] < 0 ? -1 : 1, m: m, lo: lo, hi: hi, R2: R2, thK: thK, bestK: best.k, worstK: worst.k } };
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

  var META_L2 = [['sectorSys', '周長與面積反求扇形'], ['sectorMax', '定周長扇形面積最大'], ['coneShortest', '圓錐側面最短路徑'], ['sumProd', 'sinθ+cosθ=k 的連鎖求值'], ['quadRootCos2', '方程式的根 → cos2θ'], ['tanQuad', '根與係數 × tan 和角'], ['systemSquare', '平方相加求 cos(A+B)'], ['halfFromCos2x', 'cos2x → 半角組合'], ['paramFit', '由最高最低點反求 (a,b,c,d)'], ['transformOrder', '伸縮與平移的順序'], ['periodJudge', '合成函數的週期'], ['rootCount', '方程式 c+k sin x=x 的解數'], ['trigIneq', '三角不等式（含孤立解）'], ['combineInterval', '疊合後的區間最值'], ['squareSub', 'sin x±cos x 的二次代換'], ['eqSumCount', 'sin bx=k 的解數與總和']];

  /* ══════════════════════════════════════════════════════════
     L3　中上（15 型）：每型對應固定題 L3-1～L3-15 的「類似題」
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
    var best = null, worst = null;
    cands.forEach(function (c) {
      var sv = tv(c.u * 15).sin, val = vNum(sv);
      if (best === null || val > best.val + 1e-12) best = { x24: c.x24, val: val, sv: sv };
      if (worst === null || val < worst.val - 1e-12) worst = { x24: c.x24, val: val, sv: sv };
    });
    function tex(sv) { var s = simpSqrt(R2 * sv.r); return { c: sv.c * s.c, r: s.r, d: sv.d }; }
    return { maxX24: best.x24, minX24: worst.x24, max: tex(best.sv), min: tex(worst.sv), flat: Math.abs(best.val - worst.val) < 1e-12 };
  }
  function kTex(k) { return k === 24 ? '2\\pi' : k === -24 ? '-2\\pi' : piTex(k, 12); }
  function k24Tex(k) { return k === 48 ? '2\\pi' : k === -48 ? '-2\\pi' : piTex(k, 24); }
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
      h: '把 $x$ 換成 $x+\\dfrac{\\pi}{2b}$ 試「$|\\sin|$ 與 $|\\cos|$ 互換」；絕對值把負半波翻上來、平方降冪成 $2bx$、乘積用倍角——先各自找出 $p$、$q$ 再相加。', p: { t1: PERT[i1].id, b1: b1, t2: PERT[i2].id, b2: b2, P1: [P1.n, P1.d], P2: [P2.n, P2.d], sum: [S.n, S.d] } };
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
    return { q: q, a: '(' + ans.join(')(') + ')', h: '$\\tan\\theta' + (tsg > 0 ? '\\gt0' : '\\lt0') + '$ 且 $' + coord + (csg > 0 ? '\\gt0' : '\\lt0') + '$ ⟹ 第' + QN[quad] + '象限，取 $P(' + (xs * pq[1]) + ',' + (ys * pq[0]) + ')$、$r=\\sqrt{' + (pq[0] * pq[0] + pq[1] * pq[1]) + '}$ 逐項算；$\\dfrac{\\theta}{2}$ 的象限因 $\\theta$ 可加減 $2\\pi$ 而不確定，$\\tan\\dfrac{\\theta}{2}=\\dfrac{\\sin\\theta}{1+\\cos\\theta}$ 則是確定的。', p: { p: pq[0], q: pq[1], tsg: tsg, coord: coord, csg: csg, quad: quad, ids: chosen.map(function (o) { return o.id; }), ans: ans } };
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
      h: '$\\cos^2x=\\dfrac{1+\\cos2x}{2}$、$\\sin^2x=\\dfrac{1-\\cos2x}{2}$、$2\\sin x\\cos x=\\sin2x$ 全部降冪，整理成 $' + coefTex(A, aS3, true) + '\\sin2x' + coefTex(B, false, false) + '\\cos2x=' + Cv + '$，疊合成 $' + sqrtTex(R2) + '\\sin\\left(2x+' + piTex(thK, 12) + '\\right)=' + Cv + '$，注意 $2x+' + piTex(thK, 12) + '$ 的範圍是開區間。',
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
    var tA = '\\dfrac{' + numT(m, pr.a[1]) + '}{\\sin' + angT + '}', tB = '\\dfrac{' + numT(m, pr.b[1]) + '}{\\cos' + angT + '}';
    var qT = swap ? tB + form + tA : tA + form + tB;
    return { q: '求 ' + T(qT) + ' 之值。',
      a: T(ans), h: '$' + aT + '=' + alpha + '^\\circ$，通分後分子 $' + (swap && form === '-' ? numT(m, pr.b[1]) + '\\sin' + alpha + '^\\circ-' + numT(m, pr.a[1]) + '\\cos' + alpha + '^\\circ' : numT(m, pr.a[1]) + '\\cos' + alpha + '^\\circ' + (form === '-' ? '-' : '+') + numT(m, pr.b[1]) + '\\sin' + alpha + '^\\circ') + '$ 可以疊合成 $' + sqrtTex(pr.R2 * m * m) + '\\cos(' + alpha + '^\\circ' + (form === '-' ? '+' : '-') + pr.phi + '^\\circ)$（差一個正負號）；分母 $\\sin' + alpha + '^\\circ\\cos' + alpha + '^\\circ=\\dfrac12\\sin' + (2 * alpha) + '^\\circ$，兩個角互補或互餘。', p: { aS3: pr.a[1], bS3: pr.b[1], m: m, form: form, swap: swap, alpha: alpha, R2: pr.R2, k: cand } };
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
      a: '最大值 ' + T(mixTex(K, ex.max.c, ex.max.r, ex.max.d)) + '（' + T('x=' + k24Tex(ex.maxX24)) + '），最小值 ' + T(mixTex(K, ex.min.c, ex.min.r, ex.min.d)) + '（' + T('x=' + k24Tex(ex.minX24)) + '）',
      h: '降冪：$f(x)=' + coefTex(A, aS3, true) + '\\sin2x' + coefTex(B, false, false) + '\\cos2x' + (K.n === 0 ? '' : (K.n > 0 ? '+' : '') + Fr.tex(K)) + '=' + sqrtTex(R2) + '\\sin\\left(2x+' + piTex(thK, 12) + '\\right)' + (K.n === 0 ? '' : (K.n > 0 ? '+' : '') + Fr.tex(K)) + '$，再看 $2x+' + piTex(thK, 12) + '$ 跑過 $\\left[' + kTex(2 * lo + thK) + ',' + kTex(2 * hi + thK) + '\\right]$ 的哪一段。',
      p: { aS3: aS3, A: A, B: B, pc: pc, qn: qn, rs: rs, lo: lo, hi: hi, R2: R2, thK: thK, K: [K.n, K.d], maxX24: ex.maxX24, minX24: ex.minX24, max: [ex.max.c, ex.max.r, ex.max.d], min: [ex.min.c, ex.min.r, ex.min.d] } };
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
      a: T('(M,N)=\\left(' + surd3(ex.max) + ',' + surd3(ex.min) + '\\right)') + '（' + T('x=' + k24Tex(ex.maxX24)) + ' 取最大、' + T('x=' + k24Tex(ex.minX24)) + ' 取最小）',
      h: '先把 $' + AT + '\\' + trig + '\\left(x+' + piTex(phiK, 12) + '\\right)$ 用和角展開，合併後 $f(x)=' + coefTex(a.n, a.s3, true) + '\\sin x' + coefTex(b.n, b.s3, false) + '\\cos x=' + sqrtTex(R2) + '\\sin\\left(x' + (thK < 0 ? '-' : '+') + piTex(Math.abs(thK), 12) + '\\right)$，再看 $x' + (thK < 0 ? '-' : '+') + piTex(Math.abs(thK), 12) + '$ 跑過 $\\left[' + kTex(lo + thK) + ',' + kTex(hi + thK) + '\\right]$ 的哪一段。',
      p: { fam: fam, m: m, sA: sA, form: form, Bn: Bn, Bs3: Bs3, lo: lo, hi: hi, R2: R2, thK: thK, maxX24: ex.maxX24, minX24: ex.minX24, max: [ex.max.c, ex.max.r, ex.max.d], min: [ex.min.c, ex.min.r, ex.min.d] } };
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
      var x1 = (S - Math.sqrt(disc)) / 2, x2 = (S + Math.sqrt(disc)) / 2;
      var A1 = Math.atan(x1) * 180 / Math.PI, A2 = Math.atan(x2) * 180 / Math.PI; if (A1 < 0) A1 += 180; if (A2 < 0) A2 += 180;
      if (Math.abs(A1 + A2 + C - 180) > 1e-6) continue;
      var pT = (Math.abs(p) === 1 ? '' : Math.abs(p)) + 'a', qT = q === 0 ? '' : (p > 0 ? signed(q) : signed(-q));
      var cT = (Math.abs(rr) === 1 ? '' : Math.abs(rr)) + 'a' + (s === 0 ? '' : (rr > 0 ? signed(s) : signed(-s)));
      var polyT = 'x^2' + (p > 0 ? '-' : '+') + '(' + pT + qT + ')x' + (rr > 0 ? '+' : '-') + (s === 0 ? cT : '(' + cT + ')') + '=0';
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
      a: T(ans), h: '$' + piTex(kk, 2) + '=' + piTex(kk - (kmod === 3 ? 3 : kmod), 2).replace(/^0$/, '0') + '+' + (kmod === 0 ? '0' : piTex(kmod, 2)) + '$，先丟掉 $2\\pi$ 的倍數，剩 $\\' + fn + '\\left(' + (kmod === 0 ? '' : piTex(kmod, 2) + (sg > 0 ? '+' : '-')) + (kmod === 0 && sg < 0 ? '-' : '') + '\\theta\\right)=' + (sign < 0 ? '-' : '') + (useSin ? '\\sin' : '\\cos') + '\\theta$；再由 $\\tan\\theta' + (tsg > 0 ? '\\gt0' : '\\lt0') + '$ 與範圍定第' + QN[quad] + '象限，$r=\\sqrt{' + rr + '}$。', p: { k: kk, fn: fn, sg: sg, p: pq[0], q: pq[1], tsg: tsg, rng: rng, quad: quad, ans: ans } };
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

  var META_L3 = [['radEstimate', '弧度值估大小（多選）'], ['periodFromHighLow', '最高最低點的水平距離 → 週期'], ['tanShiftCoincide', 'tan 平移後重合'], ['rootSumSin', 'sin bx=k 在 (0,Lπ) 的解數與總和'], ['absPeriodSum', '絕對值／平方的週期相加'], ['quadTanPoint', 'tan 與坐標正負定象限（多選）'], ['homogEq', '齊次式方程：降冪、疊合'], ['fracSubCombine', '分式通分後疊合'], ['halfDiffIsos', 'cos(θ/2)−sin(θ/2) 已知的等腰三角形'], ['sinCosMixRange', 'sin x cos x 與平方混合的區間最值'], ['expandCombineRange', '先展開再疊合的區間最值'], ['tanRootsTriangle', '兩根為 tanA、tanB 的三角形'], ['crossSquareSum', '兩式平方相加'], ['reduceBigAngle', '大角度的誘導公式'], ['tideModel', '週期模型（潮汐）']];
  /* 固定題 L3-n 對應的類似題型 */
  var L3_FIX = { 'L3-1': 'radEstimate', 'L3-2': 'periodFromHighLow', 'L3-3': 'tanShiftCoincide', 'L3-4': 'rootSumSin', 'L3-5': 'absPeriodSum', 'L3-6': 'quadTanPoint', 'L3-7': 'homogEq', 'L3-8': 'fracSubCombine', 'L3-9': 'halfDiffIsos', 'L3-10': 'sinCosMixRange', 'L3-11': 'expandCombineRange', 'L3-12': 'tanRootsTriangle', 'L3-13': 'crossSquareSum', 'L3-14': 'reduceBigAngle', 'L3-15': 'tideModel' };

  var META = { L1: META_L1, L2: META_L2, L3: META_L3 };

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
  wrapAll(L1, L1_SOL, L1_H1); wrapAll(L2); wrapAll(L3);

  return { makeRng: makeRng, L1: L1, L2: L2, L3: L3, L3_FIX: L3_FIX, META: META, _util: { F: F, Fr: Fr, tv: tv, piTex: piTex, exact15: exact15, countRoots: countRoots } };
}));
