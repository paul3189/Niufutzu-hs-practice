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
     L1　基礎（20 型）
     ══════════════════════════════════════════════════════════ */
  var L1 = {};

  /* 1-1 弧度、扇形、定義 */
  L1.degToRad = function (r) {
    var base = r.pick([30, 45, 60, 90, 120, 135, 150, 210, 225, 240, 270, 300, 315, 330]);
    var deg = base + 360 * r.pick([0, 0, 0, 1, -1]);
    if (r() < 0.35) deg = -deg;
    var f = F(deg, 180);
    return { q: '將 ' + T(degTex(deg)) + ' 化為弧度。', a: T(piTex(f.n, f.d)), h: '乘以 $\\dfrac{\\pi}{180}$，再約分。', p: { deg: deg } };
  };
  L1.radToDeg = function (r) {
    var d = r.pick([3, 4, 6, 6, 12]), k = r.int(1, 3 * d) * r.sign(), guard = 0;
    while ((k * 180 / d) % 90 === 0 && guard++ < 50) k = r.int(1, 3 * d) * r.sign();
    var deg = k * 180 / d, qd = quadrant(deg);
    return { q: '將 ' + T(piTex(k, d)) + ' 化為度數，並判斷它是第幾象限角。', a: T(degTex(deg)) + '，' + (qd ? '第' + QN[qd] + '象限角' : '終邊在坐標軸上'), h: '$\\pi$ 就是 $180^\\circ$；判象限先加減 $360^\\circ$ 化到 $[0^\\circ,360^\\circ)$。', p: { k: k, d: d, deg: deg, quad: qd } };
  };
  L1.arcArea = function (r) {
    var rad = r.int(2, 12), k = r.pick([1, 2, 3, 4, 5]), d = r.pick([2, 3, 4, 6]);
    var arc = F(rad * k, d), area = F(rad * rad * k, 2 * d);
    return { q: '一扇形半徑為 ' + T(rad) + '，圓心角為 ' + T(piTex(k, d)) + '，求弧長與面積。', a: '弧長 ' + T(Fr.tex(arc) + '\\pi') + '，面積 ' + T(Fr.tex(area) + '\\pi'), h: '$s=r\\theta$、$A=\\dfrac12r^2\\theta$，$\\theta$ 一定要用弧度。', p: { r: rad, k: k, d: d } };
  };
  L1.sectorFromArc = function (r) {
    var rad = r.int(2, 10), th = r.pick([1, 2, 3, 4]);
    var arc = rad * th, area = F(rad * arc, 2);
    return { q: '一扇形半徑為 ' + T(rad) + '、弧長為 ' + T(arc) + '，求圓心角（弧度）與面積。', a: '圓心角 ' + T(th) + '，面積 ' + T(Fr.tex(area)), h: '$\\theta=\\dfrac{s}{r}$；面積也可以直接用 $\\dfrac12rs$。', p: { r: rad, arc: arc, th: th } };
  };
  L1.signQuad = function (r) {
    var v = r.pick([1, 2, 3, 4, 5, 6]), fn = r.pick(['sin', 'cos', 'tan']);
    var val = { sin: Math.sin(v), cos: Math.cos(v), tan: Math.tan(v) }[fn];
    var qd = v < Math.PI / 2 ? 1 : v < Math.PI ? 2 : v < 3 * Math.PI / 2 ? 3 : 4;
    return { q: '判斷 ' + T('\\' + fn + ' ' + v) + ' 的正負（' + v + ' 為弧度）。', a: (val > 0 ? '正' : '負') + '（' + v + ' 弧度在第' + QN[qd] + '象限）', h: '$\\dfrac{\\pi}{2}\\approx1.57$、$\\pi\\approx3.14$、$\\dfrac{3\\pi}{2}\\approx4.71$、$2\\pi\\approx6.28$，先看角落在哪一段。', p: { v: v, fn: fn, sign: val > 0 ? 1 : -1 } };
  };
  L1.specialValue = function (r) {
    var fn = r.pick(['sin', 'cos', 'tan']), d = r.pick([3, 4, 6]), k = r.int(1, 4 * d);
    while (k % d === 0 || (fn === 'tan' && (k * 180 / d) % 180 === 90)) k = r.int(1, 4 * d);
    var deg = k * 180 / d, v = tv(deg)[fn];
    return { q: '求 ' + T('\\' + fn + '\\dfrac{' + k + '\\pi}{' + d + '}') + ' 的值。', a: T(vTex(v)), h: '先減掉 $2\\pi$ 的倍數，找參考角，再依象限定正負。', p: { fn: fn, k: k, d: d, deg: deg } };
  };
  L1.pointDef = function (r) {
    var t = r.pick(TRIPLES), sx = r.sign(), sy = r.sign(), x = sx * t[1], y = sy * t[0], c = t[2];
    return { q: '已知角 ' + T('\\theta') + ' 的終邊通過點 ' + T('P(' + x + ',' + y + ')') + '，求 ' + T('\\sin\\theta,\\ \\cos\\theta,\\ \\tan\\theta') + '。',
      a: T('\\sin\\theta=' + fracTex(y, c) + ',\\ \\cos\\theta=' + fracTex(x, c) + ',\\ \\tan\\theta=' + fracTex(y, x)),
      h: '$r=\\sqrt{x^2+y^2}$，$\\sin=\\dfrac yr$、$\\cos=\\dfrac xr$、$\\tan=\\dfrac yx$。', p: { x: x, y: y, r: c } };
  };
  L1.fromSinQuad = function (r) {
    var t = r.pick(TRIPLES), qd = r.pick([1, 2, 3, 4]);
    var give = r.pick(['sin', 'cos']);
    var s = (qd <= 2 ? 1 : -1) * t[0], c = (qd === 1 || qd === 4 ? 1 : -1) * t[1], R = t[2];
    var ask = give === 'sin' ? ['cos', 'tan'] : ['sin', 'tan'];
    var vals = { sin: fracTex(s, R), cos: fracTex(c, R), tan: fracTex(s, c) };
    return { q: '已知 ' + T('\\' + give + '\\theta=' + vals[give]) + '，且 ' + T('\\theta') + ' 為第' + QN[qd] + '象限角，求 ' + T('\\' + ask[0] + '\\theta') + ' 與 ' + T('\\' + ask[1] + '\\theta') + '。',
      a: T('\\' + ask[0] + '\\theta=' + vals[ask[0]] + ',\\ \\' + ask[1] + '\\theta=' + vals[ask[1]]),
      h: '$\\sin^2\\theta+\\cos^2\\theta=1$ 算出大小，象限決定正負。', p: { give: give, s: s, c: c, R: R, quad: qd } };
  };
  L1.coterminal = function (r) {
    var mode = r.pick(['deg', 'rad']);
    if (mode === 'deg') {
      var base = r.pick([30, 45, 60, 120, 135, 150, 210, 225, 240, 300, 315, 330]), deg = base + 360 * r.pick([1, 2, -1, -2, 3]);
      return { q: '求與 ' + T(degTex(deg)) + ' 同界的最小正角，並判斷象限。', a: T(degTex(base)) + '，第' + QN[quadrant(base)] + '象限', h: '加減 $360^\\circ$ 的整數倍。', p: { mode: mode, deg: deg, base: base } };
    }
    var d = r.pick([3, 4, 6]), k0 = r.int(1, 2 * d - 1); while (k0 % d === 0) k0 = r.int(1, 2 * d - 1);
    var k = k0 + 2 * d * r.pick([1, 2, -1, -2]);
    return { q: '求與 ' + T(piTex(k, d)) + ' 同界的最小正角，並判斷象限。', a: T(piTex(k0, d)) + '，第' + QN[quadrant(k0 * 180 / d)] + '象限', h: '加減 $2\\pi$ 的整數倍，也就是加減 $\\dfrac{' + (2 * d) + '\\pi}{' + d + '}$。', p: { mode: mode, k: k, d: d, k0: k0 } };
  };
  L1.reduceFormula = function (r) {
    var rule = r.pick(REDUCE), fn = r.pick(['sin', 'cos', 'tan']);
    if (fn === 'tan' && rule.k % 180 === 90) fn = r.pick(['sin', 'cos']);   /* 避免 cot */
    var res = rule[fn];
    var ans = (res[1] < 0 ? '-' : '') + '\\' + res[0] + '\\theta';
    return { q: '化簡 ' + T('\\' + fn + '\\left(' + rule.arg('\\theta') + '\\right)') + '。', a: T(ans), h: '「奇變偶不變，符號看象限」：把 $\\theta$ 當銳角，先看新角落在哪一象限。', p: { fn: fn, k: rule.k, m: rule.m, resf: res[0], ress: res[1] } };
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
      a: T(expr + '=' + fracTex(num, R1 * R2)), h: '先把 $\\cos\\alpha$、$\\sin\\beta$ 補齊（畢氏＋象限），再套公式。', p: { s1: s1, c1: c1, R1: R1, s2: s2, c2: c2, R2: R2, which: which, num: num } };
  };
  L1.tanSum = function (r) {
    var p1 = F(r.int(1, 5) * r.sign(), r.pick([1, 1, 2, 3])), p2 = F(r.int(1, 5) * r.sign(), r.pick([1, 1, 2, 3]));
    var sgn = r.sign();
    var den = Fr.sub(F(1), Fr.mul(F(sgn), Fr.mul(p1, p2))), guard = 0;
    while (den.n === 0 && guard++ < 20) { p2 = F(r.int(1, 5) * r.sign(), r.pick([1, 2, 3])); den = Fr.sub(F(1), Fr.mul(F(sgn), Fr.mul(p1, p2))); }
    var num = sgn > 0 ? Fr.add(p1, p2) : Fr.sub(p1, p2);
    var val = Fr.div(num, den);
    var expr = '\\tan(\\alpha' + (sgn > 0 ? '+' : '-') + '\\beta)';
    return { q: '已知 ' + T('\\tan\\alpha=' + Fr.tex(p1)) + '、' + T('\\tan\\beta=' + Fr.tex(p2)) + '，求 ' + T(expr) + '。', a: T(expr + '=' + Fr.tex(val)), h: '$\\tan(\\alpha\\pm\\beta)=\\dfrac{\\tan\\alpha\\pm\\tan\\beta}{1\\mp\\tan\\alpha\\tan\\beta}$，注意分母的正負號相反。', p: { p1: [p1.n, p1.d], p2: [p2.n, p2.d], sgn: sgn, val: [val.n, val.d] } };
  };
  L1.doubleFromSin = function (r) {
    var t = r.pick(TRIPLES), qd = r.pick([1, 2, 3, 4]), give = r.pick(['sin', 'cos']);
    var s = (qd <= 2 ? 1 : -1) * t[0], c = (qd === 1 || qd === 4 ? 1 : -1) * t[1], R = t[2];
    var s2 = F(2 * s * c, R * R), c2 = F(c * c - s * s, R * R);
    return { q: '已知 ' + T('\\' + give + '\\theta=' + fracTex(give === 'sin' ? s : c, R)) + '，' + T('\\theta') + ' 為第' + QN[qd] + '象限角，求 ' + T('\\sin2\\theta') + ' 與 ' + T('\\cos2\\theta') + '。',
      a: T('\\sin2\\theta=' + Fr.tex(s2) + ',\\ \\cos2\\theta=' + Fr.tex(c2)), h: '$\\sin2\\theta=2\\sin\\theta\\cos\\theta$、$\\cos2\\theta=\\cos^2\\theta-\\sin^2\\theta$，先補另一個函數值。', p: { give: give, s: s, c: c, R: R, quad: qd } };
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
      a: T(fnName + '\\dfrac{\\theta}{2}=' + fracTex(sgn * num, den)), h: '半角公式 $\\cos^2\\dfrac{\\theta}{2}=\\dfrac{1+\\cos\\theta}{2}$、$\\sin^2\\dfrac{\\theta}{2}=\\dfrac{1-\\cos\\theta}{2}$；正負號看 $\\dfrac{\\theta}{2}$ 落在哪一象限。', p: { cosn: row[0], cosd: row[1], quad: qd, askCos: askCos, num: sgn * num, den: den } };
  };

  /* 1-3 圖形與疊合 */
  L1.ampPeriod = function (r) {
    var a = r.int(1, 5) * r.sign(), b = r.pick([1, 2, 3, 4, 0.5]), cK = r.pick([0, 1, -1, 2, -2, 3]), d = r.int(-3, 3), fn = r.pick(['sin', 'cos']);
    var bT = b === 0.5 ? '\\dfrac{x}{2}' : (b === 1 ? 'x' : b + 'x');
    var inner = bT + (cK === 0 ? '' : (cK > 0 ? '+' : '-') + piTex(Math.abs(cK), 6));
    var per = b === 0.5 ? '4\\pi' : (b === 1 ? '2\\pi' : b === 2 ? '\\pi' : '\\dfrac{2\\pi}{' + b + '}');
    var expr = (a === 1 ? '' : a === -1 ? '-' : a) + '\\' + fn + '\\left(' + inner + '\\right)' + (d === 0 ? '' : signed(d));
    return { q: '寫出 ' + T('y=' + expr) + ' 的振幅、週期、最大值與最小值。', a: '振幅 ' + T(Math.abs(a)) + '，週期 ' + T(per) + '，最大值 ' + T(d + Math.abs(a)) + '，最小值 ' + T(d - Math.abs(a)),
      h: '振幅 $=|a|$、週期 $=\\dfrac{2\\pi}{|b|}$、最大最小 $=d\\pm|a|$；相位 $c$ 不影響這四個量。', p: { a: a, b: b, cK: cK, d: d } };
  };
  L1.shiftFunc = function (r) {
    var fn = r.pick(['sin', 'cos']), hk = r.pick([1, 2, 3, 4, 6]), hs = r.sign(), vs = r.int(1, 3) * r.sign();
    var hor = hs > 0 ? '右' : '左', ver = vs > 0 ? '上' : '下';
    var ans = '\\' + fn + '\\left(x' + (hs > 0 ? '-' : '+') + piTex(1, hk) + '\\right)' + signed(vs);
    return { q: '將 ' + T('y=\\' + fn + ' x') + ' 的圖形向' + hor + '平移 ' + T(piTex(1, hk)) + '，再向' + ver + '平移 ' + T(Math.abs(vs)) + '，求所得圖形的方程式。', a: T('y=' + ans), h: '向右平移 $k$ 是把 $x$ 換成 $x-k$（右減左加）；上下平移直接加減在外面。', p: { fn: fn, hk: hk, hs: hs, vs: vs } };
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
      h: '$r=\\sqrt{a^2+b^2}$，$\\cos\\theta=\\dfrac ar$、$\\sin\\theta=\\dfrac br$，兩個符號一起決定 $\\theta$ 的象限。',
      p: { aIsSqrt3: Math.abs(row[0]) === 3, aSign: row[0] < 0 ? -1 : 1, bIsSqrt3: Math.abs(row[1]) === 3, bSign: row[1] < 0 ? -1 : 1, m: m, R2: row[2] * m * m, thn: row[3], thd: row[4] } };
  };
  L1.maxMin = function (r) {
    var t = r.pick(TRIPLES), a = t[0] * r.sign(), b = t[1] * r.sign(), d = r.int(-4, 6), R = t[2];
    var expr = (a === 1 ? '' : a === -1 ? '-' : a) + '\\sin x' + (b === 1 ? '+' : b === -1 ? '-' : signed(b)) + '\\cos x' + (d === 0 ? '' : signed(d));
    return { q: '求 ' + T('f(x)=' + expr) + ' 的最大值與最小值。', a: '最大值 ' + T(d + R) + '，最小值 ' + T(d - R), h: '疊合後振幅 $=\\sqrt{a^2+b^2}$，最大最小就是 $d\\pm\\sqrt{a^2+b^2}$。', p: { a: a, b: b, d: d, R: R } };
  };
  L1.basicEq = function (r) {
    var fn = r.pick(['sin', 'cos', 'tan']);
    var pool = fn === 'tan' ? [[1, 1, 1], [-1, 1, 1], [1, 3, 1], [-1, 3, 1], [1, 3, 3], [-1, 3, 3], [0, 1, 1]] : [[1, 1, 2], [-1, 1, 2], [1, 2, 2], [-1, 2, 2], [1, 3, 2], [-1, 3, 2], [0, 1, 1], [1, 1, 1], [-1, 1, 1]];
    var v = r.pick(pool), val = { c: v[0], r: v[1], d: v[2] }, target = vNum(val);
    var sols = [];
    for (var k = 0; k < 24; k++) { var deg = k * 15; if (deg % 30 !== 0 && deg % 45 !== 0) continue; var w = tv(deg)[fn]; if (w && Math.abs(vNum(w) - target) < 1e-9) sols.push(k); }
    var solT = sols.map(function (k) { return piTex(k, 12); }).join(',\\ ');
    return { q: '解 ' + T('\\' + fn + ' x=' + vTex(val)) + '，' + T('0\\le x\\lt2\\pi') + '。', a: T('x=' + solT), h: '先找第一象限（或 $x=0$）的參考解，再用對稱性補上其他象限。', p: { fn: fn, c: v[0], r: v[1], d: v[2], ks: sols } };
  };
  L1.periodOf = function (r) {
    var b = r.pick([1, 2, 3, 4, 0.5]), kind = r.pick(['sin', 'cos', 'tan', 'abssin', 'sin2']);
    var bT = b === 0.5 ? '\\dfrac{x}{2}' : (b === 1 ? 'x' : b + 'x');
    var expr = { sin: '\\sin ' + bT, cos: '\\cos ' + bT, tan: '\\tan ' + bT, abssin: '\\left|\\sin ' + bT + '\\right|', sin2: '\\sin^2 ' + bT }[kind];
    var P = (kind === 'sin' || kind === 'cos') ? F(2, 1) : F(1, 1);      /* 以 π 為單位，再除以 b */
    P = Fr.div(P, F(b === 0.5 ? 1 : b, b === 0.5 ? 2 : 1));
    return { q: '求 ' + T('y=' + expr) + ' 的最小正週期。', a: T(P.n === 1 && P.d === 1 ? '\\pi' : Fr.tex(P) + '\\pi'), h: '$\\sin,\\cos$ 的週期 $\\dfrac{2\\pi}{|b|}$；$\\tan$、加絕對值、平方後都減半成 $\\dfrac{\\pi}{|b|}$。', p: { b: b, kind: kind, P: [P.n, P.d] } };
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
    var L = 4 * r.int(3, 10);
    return { q: '用長 ' + T(L) + ' 的鐵絲圍成一個扇形，圓心角為 ' + T('\\theta') + ' 弧度。當 ' + T('\\theta') + ' 為何時面積最大？最大面積為何？',
      a: T('\\theta=2') + '（此時 ' + T('r=' + (L / 4)) + '），最大面積 ' + T(L * L / 16), h: '$2r+r\\theta=L$ ⟹ 面積 $=\\dfrac12r(L-2r)$，是 $r$ 的二次函數，頂點在 $r=\\dfrac L4$。', p: { L: L } };
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
  var SYS = [[3, 2, 3, [1, 2]], [3, 3, 2, [1, 2]], [2, 1, 2, [0, 1]], [2, 2, 1, [0, 1]], [1, 1, 1, [0, 1]], [3, 1, 3, [0, 1]], [3, 3, 1, [0, 1]], [4, 1, 4, [0, 1]], [4, 4, 1, [0, 1]], [5, 2, 4, [-3, 5]], [5, 4, 2, [-3, 5]], [3, 2, 2, [-1, 3]]];
  L2.systemSquare = function (r) {
    var row = r.pick(SYS), p = row[0], m = row[1], n = row[2], c = F(row[3][0], row[3][1]);
    var pT = p === 1 ? '' : String(p);
    return { q: '已知 ' + T('\\begin{cases}\\cos A+' + pT + '\\cos B=' + m + '\\\\ \\sin A-' + pT + '\\sin B=' + n + '\\end{cases}') + '，求 ' + T('\\cos(A+B)') + '。',
      a: T('\\cos(A+B)=' + Fr.tex(c)), h: '兩式平方相加，$\\cos^2+\\sin^2$ 收成 $1$ 與 $p^2$，交叉項恰好是 $2p\\cos(A+B)$。', p: { p: p, m: m, n: n, c: [c.n, c.d] } };
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
  /* 三角不等式模板：解集合以 π/12 為單位 [lo, hi, 含lo, 含hi]，另有孤立點 */
  var INEQ = [
    { e: '2\\sin^2x+\\sin x-1\\le0', iv: [[0, 2, 1, 1], [10, 24, 1, 0]], pts: [], key: 'sin<=1/2' },
    { e: '2\\sin^2x-\\sin x-1\\ge0', iv: [[14, 22, 1, 1]], pts: [6], key: 'sin<=-1/2 or sin=1' },
    { e: '2\\cos^2x-\\cos x-1\\lt0', iv: [[0, 8, 0, 0], [16, 24, 0, 0]], pts: [], key: '-1/2<cos<1' },
    { e: '2\\cos^2x+\\cos x-1\\gt0', iv: [[0, 4, 1, 0], [20, 24, 0, 0]], pts: [], key: 'cos>1/2' },
    { e: '2\\cos^2x-3\\cos x+1\\le0', iv: [[0, 4, 1, 1], [20, 24, 1, 0]], pts: [], key: '1/2<=cos<=1' },
    { e: '2\\sin^2x-3\\sin x+1\\gt0', iv: [[0, 2, 1, 0], [10, 24, 0, 0]], pts: [], key: 'sin<1/2' },
    { e: '2\\sin^2x+3\\sin x+1\\ge0', iv: [[0, 14, 1, 1], [22, 24, 1, 0]], pts: [18], key: 'sin>=-1/2 or sin=-1' },
    { e: '2\\cos^2x+3\\cos x+1\\lt0', iv: [[8, 12, 0, 0], [12, 16, 0, 0]], pts: [], key: '-1<cos<-1/2' },
    { e: '2\\cos^2x-\\sin x\\le1', iv: [[2, 10, 1, 1]], pts: [18], key: 'sin>=1/2 or sin=-1' },
    { e: '2\\sin^2x+3\\cos x-3\\gt0', iv: [[0, 4, 0, 0], [20, 24, 0, 0]], pts: [], key: '1/2<cos<1' },
    { e: '2\\sin^2x-\\cos x-1\\ge0', iv: [[4, 20, 1, 1]], pts: [], key: '-1<=cos<=1/2' },
    { e: '2\\cos^2x+\\sin x-2\\lt0', iv: [[0, 2, 0, 0], [10, 24, 0, 0]], pts: [], key: 'sin<1/2 and sin!=0? no: (2s-1)(s)>0' }
  ];
  /* 最後一列：2cos²x+sinx-2<0 ⟺ 2-2s²+s-2<0 ⟺ s(2s-1)>0 ⟺ s<0 或 s>1/2 ⟹ (π/6,5π/6)∪(π,2π) */
  INEQ[11] = { e: '2\\cos^2x+\\sin x-2\\lt0', iv: [[2, 10, 0, 0], [12, 24, 0, 0]], pts: [], key: 'sin<0 or sin>1/2' };
  function setTex(iv, pts) {
    var parts = iv.map(function (v) {
      var lo = piTex(v[0], 12), hi = v[1] === 24 ? '2\\pi' : piTex(v[1], 12);
      return lo + (v[2] ? '\\le ' : '\\lt ') + 'x' + (v[3] ? '\\le ' : '\\lt ') + hi;
    });
    pts.forEach(function (k) { parts.push('x=' + piTex(k, 12)); });
    return parts.join('\\ \\text{或}\\ ');
  }
  L2.trigIneq = function (r) {
    var idx = r.int(0, INEQ.length - 1), tpl = INEQ[idx];
    return { q: '設 ' + T('0\\le x\\lt2\\pi') + '，解不等式 ' + T(tpl.e) + '。', a: T(setTex(tpl.iv, tpl.pts)), h: '用 $\\sin^2+\\cos^2=1$ 化成單一函數的二次式，因式分解後，先解「值的範圍」，再對照單位圓翻成 $x$ 的範圍；根為 $\\pm1$ 時會出現孤立解。', p: { idx: idx, iv: tpl.iv, pts: tpl.pts } };
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

  var META = { L1: META_L1, L2: META_L2 };

  /* ── HTML 安全：$…$ 裡的 < > 改成 \lt \gt ── */
  function escMath(s) {
    return String(s).replace(/\$([^$]*)\$/g, function (m, inner) { return '$' + inner.replace(/</g, '\\lt ').replace(/>/g, '\\gt ') + '$'; });
  }
  function wrapAll(group) {
    Object.keys(group).forEach(function (k) {
      var f = group[k];
      group[k] = function (r) { var o = f(r); o.q = escMath(o.q); o.a = escMath(o.a); o.h = escMath(o.h); return o; };
    });
  }
  wrapAll(L1); wrapAll(L2);

  return { makeRng: makeRng, L1: L1, L2: L2, META: META, _util: { F: F, Fr: Fr, tv: tv, piTex: piTex, exact15: exact15, countRoots: countRoots } };
}));
