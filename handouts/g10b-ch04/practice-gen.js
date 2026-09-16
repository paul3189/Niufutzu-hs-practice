/* ══════════════════════════════════════════════════════════════
   g10b-ch04 三角比・分級練習本　題目產生器
   ─────────────────────────────────────────────────────────────
   每個產生器：function (rng) → { q, a, h, p }
     q：題目（HTML，可含 KaTeX $…$）   a：答案（HTML）
     h：一行提示                         p：參數與結構化答案（給 verify_gen10b4.py 用 Fraction／sympy 獨立重算）
   答案一律精確：分數用 F()、根式用 S()（c√r/d）；角度一律用「度」，只用 30°／45° 的倍數當特殊角。
   同時可在瀏覽器（window.PGEN）與 Node（module.exports）使用。
   ══════════════════════════════════════════════════════════════ */
(function (root, factory) {
  if (typeof module === 'object' && module.exports) module.exports = factory();
  else root.PGEN = factory();
}(typeof self !== 'undefined' ? self : this, function () {
  'use strict';

  function makeRng(seed) {
    var s = (seed === undefined) ? (Date.now() % 2147483647) : (seed % 2147483647);
    if (s <= 0) s += 2147483646;
    var r = function () { s = (s * 16807) % 2147483647; return (s - 1) / 2147483646; };
    r.int = function (lo, hi) { return lo + Math.floor(r() * (hi - lo + 1)); };
    r.nz = function (lo, hi) { var v; do { v = r.int(lo, hi); } while (v === 0); return v; };
    r.pick = function (arr) { return arr[Math.floor(r() * arr.length)]; };
    r.sign = function () { return r() < 0.5 ? -1 : 1; };
    r.shuffle = function (arr) { var a = arr.slice(); for (var i = a.length - 1; i > 0; i--) { var j = Math.floor(r() * (i + 1)), t = a[i]; a[i] = a[j]; a[j] = t; } return a; };
    return r;
  }
  function gcd(a, b) { a = Math.abs(a); b = Math.abs(b); while (b) { var t = a % b; a = b; b = t; } return a; }
  function F(n, d) { if (d === undefined) d = 1; if (d < 0) { n = -n; d = -d; } var g = gcd(n, d) || 1; return { n: n / g, d: d / g }; }
  var Fr = {
    add: function (x, y) { return F(x.n * y.d + y.n * x.d, x.d * y.d); },
    sub: function (x, y) { return F(x.n * y.d - y.n * x.d, x.d * y.d); },
    mul: function (x, y) { return F(x.n * y.n, x.d * y.d); },
    div: function (x, y) { return F(x.n * y.d, x.d * y.n); },
    eq: function (x, y) { return x.n * y.d === y.n * x.d; },
    lt: function (x, y) { return x.n * y.d < y.n * x.d; },
    toNum: function (x) { return x.n / x.d; },
    tex: function (x, small) {
      if (x.d === 1) return String(x.n);
      var f = small ? '\\frac' : '\\dfrac';
      return (x.n < 0 ? '-' : '') + f + '{' + Math.abs(x.n) + '}{' + x.d + '}';
    }
  };
  function fr2(f) { return [f.n, f.d]; }
  function T(s) { return '$' + s + '$'; }
  function simpSqrt(n) { var c = 1, r = n; for (var p = 2; p * p <= r; p++) { while (r % (p * p) === 0) { r /= p * p; c *= p; } } return [c, r]; }
  function sqrtTex(n) { if (n === 0) return '0'; var s = simpSqrt(n); if (s[1] === 1) return String(s[0]); return (s[0] === 1 ? '' : s[0]) + '\\sqrt{' + s[1] + '}'; }
  /* ── 根式數 S：c√r/d（r 無平方因數、c/d 已約分） ── */
  function S(c, r, d) {
    if (d === undefined) d = 1;
    if (c === 0) return { c: 0, r: 1, d: 1 };
    if (d < 0) { c = -c; d = -d; }
    var s = simpSqrt(r); c *= s[0]; r = s[1];
    var g = gcd(Math.abs(c), d); return { c: c / g, r: r, d: d / g };
  }
  function sTex(v, small) {
    if (v.c === 0) return '0';
    var num = v.r === 1 ? String(Math.abs(v.c)) : ((Math.abs(v.c) === 1 ? '' : Math.abs(v.c)) + '\\sqrt{' + v.r + '}');
    var body = v.d === 1 ? num : (small ? '\\frac' : '\\dfrac') + '{' + num + '}{' + v.d + '}';
    return (v.c < 0 ? '-' : '') + body;
  }
  function sNum(v) { return v.c * Math.sqrt(v.r) / v.d; }
  function sArr(v) { return [v.c, v.r, v.d]; }
  function sMul(a, b) { return S(a.c * b.c, a.r * b.r, a.d * b.d); }
  function sDiv(a, b) { return S(a.c * b.d, a.r * b.r, a.d * b.c * b.r); }   // a/b = c1 d2 √(r1 r2)/(d1 c2 r2)
  function sMulF(a, f) { return S(a.c * f.n, a.r, a.d * f.d); }
  function sFromF(f) { return S(f.n, 1, f.d); }
  function sqrtF(f) { return S(1, f.n * f.d, f.d); }                          // √(n/d) = √(nd)/d
  function sIsRat(v) { return v.r === 1; }
  function sToF(v) { return F(v.c, v.d); }
  /* 「有理數 ＋ 根式」型答案：rat + surd */
  function twoTex(rat, surd) {
    if (surd.c === 0) return Fr.tex(rat);
    if (rat.n === 0) return sTex(surd);
    var st = sTex(surd); return Fr.tex(rat) + (surd.c < 0 ? st : '+' + st);
  }
  /* 精確特殊角值：只收 30°、45° 的倍數 */
  function tv(deg) {
    var a = ((deg % 360) + 360) % 360, ref = a % 180; if (ref > 90) ref = 180 - ref;
    var base = { 0: [0, 1, 1], 30: [1, 1, 2], 45: [1, 2, 2], 60: [1, 3, 2], 90: [1, 1, 1] };
    var bs = base[ref], bc = base[90 - ref];
    var sinv = S(bs[0], bs[1], bs[2]), cosv = S(bc[0], bc[1], bc[2]);
    if (a > 180) sinv = S(-sinv.c, sinv.r, sinv.d);
    if (a > 90 && a < 270) cosv = S(-cosv.c, cosv.r, cosv.d);
    var tanv = null;
    if (ref !== 90) {
      var tb = { 0: [0, 1, 1], 30: [1, 3, 3], 45: [1, 1, 1], 60: [1, 3, 1] }[ref]; tanv = S(tb[0], tb[1], tb[2]);
      if ((a > 90 && a < 180) || (a > 270 && a < 360)) tanv = S(-tanv.c, tanv.r, tanv.d);
    }
    return { sin: sinv, cos: cosv, tan: tanv };
  }
  var FN = { sin: '\\sin', cos: '\\cos', tan: '\\tan' };
  function degTex(k) { return k + '°'; }
  /* 畢氏三元組 (a, b, c)：a²+b²=c² */
  var TRIPLES = [[3, 4, 5], [4, 3, 5], [5, 12, 13], [12, 5, 13], [8, 15, 17], [15, 8, 17], [7, 24, 25], [24, 7, 25], [20, 21, 29], [21, 20, 29], [9, 40, 41], [6, 8, 10], [8, 6, 10], [9, 12, 15], [12, 9, 15]];
  function tri(r) { return r.pick(TRIPLES); }
  function shapeOf(a, b, c) { var m = Math.max(a, b, c), s = a * a + b * b + c * c - m * m; return m * m > s ? 'obtuse' : (m * m === s ? 'right' : 'acute'); }
  var SHAPE = { obtuse: '鈍角三角形', right: '直角三角形', acute: '銳角三角形' };
  function cosLaw(b, c, a) { return F(b * b + c * c - a * a, 2 * b * c); }          // 對邊 a 的角
  function heron2(a, b, c) { var s2 = a + b + c; return F(s2 * (s2 - 2 * a) * (s2 - 2 * b) * (s2 - 2 * c), 16); }   // K²
  function validTri(a, b, c) { return a + b > c && b + c > a && c + a > b; }
  function ov(x) { return '\\overline{' + x + '}'; }
  var ABC = '$\\triangle ABC$';

  /* ═══════════════════════ L1 ═══════════════════════ */
  var L1 = {};

  /* ── 1-1 三角比的定義 ── */
  L1.triDef = function (r) {
    var t = tri(r), a = t[0], b = t[1], c = t[2], kind = r.int(0, 1);
    var given = kind === 0 ? ov('BC') + '=' + a + '、' + ov('AC') + '=' + b : ov('AB') + '=' + c + '、' + ov('BC') + '=' + a;
    return { q: '直角三角形 $ABC$ 中 $\\angle C=90°$，' + T(given) + '。求 ' + T('\\sin A') + '、' + T('\\cos A') + '、' + T('\\tan A') + '。',
             a: T('\\sin A=' + Fr.tex(F(a, c))) + '、' + T('\\cos A=' + Fr.tex(F(b, c))) + '、' + T('\\tan A=' + Fr.tex(F(a, b))),
             h: '先用畢氏定理補齊第三邊（' + (kind === 0 ? T(ov('AB') + '=' + c) : T(ov('AC') + '=' + b)) + '）；$\\angle A$ 的對邊是 $\\overline{BC}$、鄰邊是 $\\overline{AC}$：$\\sin=\\dfrac{\\text{對}}{\\text{斜}}$、$\\cos=\\dfrac{\\text{鄰}}{\\text{斜}}$、$\\tan=\\dfrac{\\text{對}}{\\text{鄰}}$。',
             p: { kind: kind, a: a, b: b, c: c, ans: { sinA: fr2(F(a, c)), cosA: fr2(F(b, c)), tanA: fr2(F(a, b)) } } };
  };
  /* ── 1-1 特殊角求值 ── */
  L1.specialEval = function (r) {
    var angs = [30, 45, 60], fns = ['sin', 'cos', 'tan'], terms, val, tries = 0;
    do {
      terms = []; var parts = [];
      for (var i = 0; i < 2; i++) {
        var f1 = r.pick(fns), a1 = r.pick(angs), f2 = r.pick(fns), a2 = r.pick(angs), sq = r.int(0, 2) === 0;
        if (sq) { var v = tv(a1)[f1]; terms.push({ f1: f1, a1: a1, sq: true, sign: i === 0 ? 1 : r.sign() }); parts.push(sMul(v, v)); }
        else { terms.push({ f1: f1, a1: a1, f2: f2, a2: a2, sq: false, sign: i === 0 ? 1 : r.sign() }); parts.push(sMul(tv(a1)[f1], tv(a2)[f2])); }
      }
      val = null;
      var p0 = sMulF(parts[0], F(terms[0].sign)), p1 = sMulF(parts[1], F(terms[1].sign));
      if (p0.c === 0 || p1.c === 0 || p0.r === p1.r) val = S(p0.c * p1.d + p1.c * p0.d, p0.c === 0 ? p1.r : p0.r, p0.d * p1.d);
      tries++;
    } while ((val === null || (terms[0].sq && terms[1].sq)) && tries < 200);
    var tex = terms.map(function (t, i) {
      var s = t.sq ? FN[t.f1] + '^2' + t.a1 + '°' : FN[t.f1] + t.a1 + '°\\cdot' + FN[t.f2] + t.a2 + '°';
      return (i === 0 ? '' : (t.sign < 0 ? '-' : '+')) + s;
    }).join('');
    return { q: '求 ' + T(tex) + ' 的值。',
             a: T(sTex(val)),
             h: '把 $30°$、$45°$、$60°$ 的值畫出來（$1:\\sqrt3:2$ 與 $1:1:\\sqrt2$ 的直角三角形），逐項代入再相加；同類根式才能合併。',
             p: { terms: terms, ans: sArr(val) } };
  };
  /* ── 1-1 同角關係：已知一個求另外兩個 ── */
  L1.sinToCos = function (r) {
    var t = tri(r), a = t[0], b = t[1], c = t[2], kind = r.int(0, 2);
    var given = kind === 0 ? '\\sin\\theta=' + Fr.tex(F(a, c)) : kind === 1 ? '\\cos\\theta=' + Fr.tex(F(b, c)) : '\\tan\\theta=' + Fr.tex(F(a, b));
    var ask = kind === 0 ? T('\\cos\\theta') + ' 與 ' + T('\\tan\\theta') : kind === 1 ? T('\\sin\\theta') + ' 與 ' + T('\\tan\\theta') : T('\\sin\\theta') + ' 與 ' + T('\\cos\\theta');
    var ans = kind === 0 ? T('\\cos\\theta=' + Fr.tex(F(b, c))) + '、' + T('\\tan\\theta=' + Fr.tex(F(a, b))) : kind === 1 ? T('\\sin\\theta=' + Fr.tex(F(a, c))) + '、' + T('\\tan\\theta=' + Fr.tex(F(a, b))) : T('\\sin\\theta=' + Fr.tex(F(a, c))) + '、' + T('\\cos\\theta=' + Fr.tex(F(b, c)));
    return { q: '設 $\\theta$ 為銳角，且 ' + T(given) + '。求 ' + ask + '。',
             a: ans,
             h: '畫一個直角三角形把已知的比值標上去（' + (kind === 2 ? '對邊 $' + a + '$、鄰邊 $' + b + '$' : kind === 0 ? '對邊 $' + a + '$、斜邊 $' + c + '$' : '鄰邊 $' + b + '$、斜邊 $' + c + '$') + '），畢氏定理補第三邊，三個比值就全出來了。',
             p: { kind: kind, a: a, b: b, c: c, ans: { sin: fr2(F(a, c)), cos: fr2(F(b, c)), tan: fr2(F(a, b)) } } };
  };
  /* ── 1-1 對稱式：sinθ±cosθ 與 sinθcosθ ── */
  L1.sumProdAcute = function (r) {
    var t = tri(r), a = t[0], b = t[1], c = t[2], kind = r.int(0, 1);
    var sum = F(a + b, c), prod = F(a * b, c * c), diff = F(Math.abs(a - b), c);
    if (kind === 0)
      return { q: '設 $\\theta$ 為銳角且 ' + T('\\sin\\theta+\\cos\\theta=' + Fr.tex(sum)) + '。求 ' + T('\\sin\\theta\\cos\\theta') + ' 與 ' + T('|\\sin\\theta-\\cos\\theta|') + '。',
               a: T('\\sin\\theta\\cos\\theta=' + Fr.tex(prod)) + '、' + T('|\\sin\\theta-\\cos\\theta|=' + Fr.tex(diff)),
               h: '兩邊平方：$1+2\\sin\\theta\\cos\\theta=(\\sin\\theta+\\cos\\theta)^2$；再用 $(\\sin\\theta-\\cos\\theta)^2=1-2\\sin\\theta\\cos\\theta$ 開根號。',
               p: { kind: 0, sum: fr2(sum), ans: { prod: fr2(prod), diff: fr2(diff) } } };
    var big = Math.max(a, b), small = Math.min(a, b), d2 = F(big - small, c);
    return { q: '設 $\\theta$ 為銳角且 ' + T('\\sin\\theta-\\cos\\theta=' + Fr.tex(d2)) + '。求 ' + T('\\sin\\theta\\cos\\theta') + ' 與 ' + T('\\sin\\theta+\\cos\\theta') + '。',
             a: T('\\sin\\theta\\cos\\theta=' + Fr.tex(prod)) + '、' + T('\\sin\\theta+\\cos\\theta=' + Fr.tex(sum)),
             h: '兩邊平方：$1-2\\sin\\theta\\cos\\theta=(\\sin\\theta-\\cos\\theta)^2$；銳角時 $\\sin\\theta$、$\\cos\\theta$ 都是正的，所以 $\\sin\\theta+\\cos\\theta$ 取正根。',
             p: { kind: 1, diff: fr2(d2), ans: { prod: fr2(prod), sum: fr2(sum) } } };
  };
  /* ── 1-1 餘角關係：整串求和／求積 ── */
  L1.coAngleSum = function (r) {
    var kind = r.int(0, 2), d = r.pick([1, 2, 3, 5, 6, 9, 10, 15]), m = 90 / d - 1;
    if (kind === 2) {
      var dd = r.pick([1, 3, 5, 9, 15]), mm = 90 / dd - 1;
      return { q: '求 ' + T('\\tan' + dd + '°\\cdot\\tan' + (2 * dd) + '°\\cdot\\tan' + (3 * dd) + '°\\cdots\\tan' + (mm * dd) + '°') + ' 的值。',
               a: T('1'),
               h: '$\\tan\\theta\\cdot\\tan(90°-\\theta)=1$：頭尾配對，每一對乘積都是 $1$，中間落單的是 $\\tan45°=1$。',
               p: { kind: 2, d: dd, ans: 1 } };
    }
    var fn = kind === 0 ? 'sin' : 'cos';
    var tex = FN[fn] + '^2' + d + '°+' + FN[fn] + '^2' + (2 * d) + '°+' + FN[fn] + '^2' + (3 * d) + '°+\\cdots+' + FN[fn] + '^2' + (m * d) + '°';
    return { q: '求 ' + T(tex) + ' 的值（角度從 $' + d + '°$ 到 $' + (m * d) + '°$，每次加 $' + d + '°$，共 $' + m + '$ 項）。',
             a: T(Fr.tex(F(m, 2))),
             h: '$\\sin^2\\theta+\\sin^2(90°-\\theta)=\\sin^2\\theta+\\cos^2\\theta=1$：頭尾配對每對得 $1$；若項數是奇數，中間的 $45°$ 那一項貢獻 $\\dfrac12$。答案恰為「項數 $\\div2$」。',
             p: { kind: kind, d: d, fn: fn, ans: fr2(F(m, 2)) } };
  };
  /* ── 1-1 仰角測高：一次測量 ── */
  L1.elevOne = function (r) {
    var th = r.pick([30, 45, 60]), kind = r.int(0, 1), d = r.pick([10, 12, 15, 18, 20, 24, 30, 36, 40, 45, 50, 60]);
    if (kind === 0) {
      var h = sMulF(tv(th).tan, F(d));
      return { q: '小明站在距離塔底 ' + T(String(d)) + ' 公尺處，測得塔頂的仰角為 ' + T(th + '°') + '。求塔高。',
               a: T(sTex(h)) + ' 公尺',
               h: '已知鄰邊（水平距離）求對邊（高）用 $\\tan$：高 $=' + d + '\\tan' + th + '°$。',
               p: { kind: 0, d: d, th: th, ans: sArr(h) } };
    }
    var dist = sDiv(S(d, 1, 1), tv(th).tan);
    return { q: '從地面某點測得塔頂的仰角為 ' + T(th + '°') + '，已知塔高 ' + T(String(d)) + ' 公尺。求該點到塔底的距離。',
             a: T(sTex(dist)) + ' 公尺',
             h: '已知對邊（高）求鄰邊（水平距離）用 $\\tan$ 除回去：距離 $=\\dfrac{' + d + '}{\\tan' + th + '°}$。',
             p: { kind: 1, d: d, th: th, ans: sArr(dist) } };
  };
  /* ── 1-1 仰角測高：兩次測量 ── */
  L1.elevTwo = function (r) {
    var pair = r.pick([[30, 45], [30, 60], [45, 60]]), w = r.pick([10, 20, 30, 40, 50, 60, 100]);
    /* h = w/(cotθ1 − cotθ2)：(30,45) → w(√3+1)/2；(30,60) → w√3/2；(45,60) → w(3+√3)/2 */
    var rat, surd;
    if (pair[0] === 30 && pair[1] === 45) { rat = F(w, 2); surd = S(w, 3, 2); }
    else if (pair[0] === 30 && pair[1] === 60) { rat = F(0); surd = S(w, 3, 2); }
    else { rat = F(3 * w, 2); surd = S(w, 3, 2); }
    return { q: '在地面上甲點測得山頂的仰角為 ' + T(pair[0] + '°') + '，朝山的方向前進 ' + T(String(w)) + ' 公尺到乙點，測得仰角為 ' + T(pair[1] + '°') + '（山腳、甲、乙共線）。求山高。',
             a: T(twoTex(rat, surd)) + ' 公尺',
             h: '設山高 $h$：甲到山腳 $=\\dfrac{h}{\\tan' + pair[0] + '°}$、乙到山腳 $=\\dfrac{h}{\\tan' + pair[1] + '°}$，兩者相差 $' + w + '$，解 $h$（分母有根號要有理化）。',
             p: { th1: pair[0], th2: pair[1], w: w, ans: { rat: fr2(rat), surd: sArr(surd) } } };
  };

  /* ── 2-1 同界角與象限 ── */
  L1.coterminal = function (r) {
    var th; do { th = r.int(-1500, 1500); } while (th % 90 === 0);
    var pos = ((th % 360) + 360) % 360, neg = pos - 360, quad = Math.floor(pos / 90) + 1;
    return { q: '求 ' + T(th + '°') + ' 的最小正同界角與最大負同界角，並判斷它是第幾象限角。',
             a: '最小正同界角 ' + T(pos + '°') + '、最大負同界角 ' + T(neg + '°') + '，第' + ['一', '二', '三', '四'][quad - 1] + '象限角',
             h: '加減 $360°$ 的整數倍直到落在 $0°\\sim360°$；最大負同界角 $=$ 最小正同界角 $-360°$。',
             p: { th: th, ans: { pos: pos, neg: neg, quad: quad } } };
  };
  /* ── 2-1 終邊上一點求三角比 ── */
  L1.pointTrig = function (r) {
    var kind = r.int(0, 3), x, y, rr, sn, cs, tn;
    if (kind === 0) { var k = r.int(1, 5) * r.pick([1, 2]), sx = r.sign(), sy = r.sign(); x = sx * k; y = sy * k; sn = S(sy, 2, 2); cs = S(sx, 2, 2); tn = S(sx * sy, 1, 1); }
    else { var t = tri(r), m = r.pick([1, 1, 2]); x = r.sign() * t[0] * m; y = r.sign() * t[1] * m; rr = t[2] * m; sn = S(y, 1, rr); cs = S(x, 1, rr); tn = S(y, 1, x); }
    return { q: '標準位置角 $\\theta$ 的終邊過點 ' + T('P(' + x + ',' + y + ')') + '。求 ' + T('\\sin\\theta') + '、' + T('\\cos\\theta') + '、' + T('\\tan\\theta') + '。',
             a: T('\\sin\\theta=' + sTex(sn)) + '、' + T('\\cos\\theta=' + sTex(cs)) + '、' + T('\\tan\\theta=' + sTex(tn)),
             h: '$r=\\sqrt{x^2+y^2}$（永遠取正），$\\sin\\theta=\\dfrac yr$、$\\cos\\theta=\\dfrac xr$、$\\tan\\theta=\\dfrac yx$；正負號由 $x$、$y$ 決定。',
             p: { x: x, y: y, ans: { sin: sArr(sn), cos: sArr(cs), tan: sArr(tn) } } };
  };
  /* ── 2-1 象限判定與符號 ── */
  L1.quadFind = function (r) {
    var kind = r.int(0, 1);
    if (kind === 0) {
      var quad = r.int(1, 4), sgn = { 1: [1, 1, 1], 2: [1, -1, -1], 3: [-1, -1, 1], 4: [-1, 1, -1] }[quad];
      var pair = r.pick([[0, 1], [0, 2], [1, 2]]), names = ['\\sin\\theta', '\\cos\\theta', '\\tan\\theta'];
      var cond = names[pair[0]] + (sgn[pair[0]] > 0 ? '>0' : '<0') + '\\ \\text{且}\\ ' + names[pair[1]] + (sgn[pair[1]] > 0 ? '>0' : '<0');
      return { q: '若 ' + T(cond) + '，判斷 $\\theta$ 是第幾象限角。',
               a: '第' + ['一', '二', '三', '四'][quad - 1] + '象限角',
               h: '口訣「一全正、二正弦、三正切、四餘弦」：兩個條件各刷掉一半，交集只剩一個象限。',
               p: { kind: 0, pair: pair, signs: [sgn[pair[0]], sgn[pair[1]]], ans: quad } };
    }
    var t = tri(r), a = t[0], b = t[1], c = t[2], q2 = r.int(2, 4), sg = { 2: [1, -1], 3: [-1, -1], 4: [-1, 1] }[q2];
    var sn = F(sg[0] * a, c), cs = F(sg[1] * b, c), tn = F(sg[0] * sg[1] * a, b), which = r.int(0, 2);
    var given = which === 0 ? '\\sin\\theta=' + Fr.tex(sn) : which === 1 ? '\\cos\\theta=' + Fr.tex(cs) : '\\tan\\theta=' + Fr.tex(tn);
    var ask = which === 0 ? T('\\cos\\theta') + ' 與 ' + T('\\tan\\theta') : which === 1 ? T('\\sin\\theta') + ' 與 ' + T('\\tan\\theta') : T('\\sin\\theta') + ' 與 ' + T('\\cos\\theta');
    var ans = which === 0 ? T('\\cos\\theta=' + Fr.tex(cs)) + '、' + T('\\tan\\theta=' + Fr.tex(tn)) : which === 1 ? T('\\sin\\theta=' + Fr.tex(sn)) + '、' + T('\\tan\\theta=' + Fr.tex(tn)) : T('\\sin\\theta=' + Fr.tex(sn)) + '、' + T('\\cos\\theta=' + Fr.tex(cs));
    return { q: '已知 $\\theta$ 為第' + ['', '', '二', '三', '四'][q2] + '象限角，且 ' + T(given) + '。求 ' + ask + '。',
             a: ans,
             h: '取終邊上一點：先不管正負用 $' + a + ',' + b + ',' + c + '$ 這組畢氏數，再依象限決定 $x$、$y$ 的正負（$r$ 永遠為正）。',
             p: { kind: 1, quad: q2, which: which, a: a, b: b, c: c, ans: { sin: fr2(sn), cos: fr2(cs), tan: fr2(tn) } } };
  };
  /* ── 2-1 廣義角特殊值 ── */
  L1.reduceEval = function (r) {
    var fns = ['sin', 'cos', 'tan'], terms, val, tries = 0;
    var pool = [120, 135, 150, 180, 210, 225, 240, 270, 300, 315, 330, 360, 390, 420, 450, 480, 510, 540, 570, 600, 630, 660, 690, 720, -30, -45, -60, -90, -120, -135, -150, -180, -210, -225, -240, -270, -300, -315, -330];
    do {
      terms = []; var parts = [], ok = true;
      for (var i = 0; i < 2; i++) {
        var f1 = r.pick(fns), a1 = r.pick(pool), f2 = r.pick(fns), a2 = r.pick(pool);
        var v1 = tv(a1)[f1], v2 = tv(a2)[f2];
        if (!v1 || !v2) { ok = false; break; }
        terms.push({ f1: f1, a1: a1, f2: f2, a2: a2, sign: i === 0 ? 1 : r.sign() }); parts.push(sMulF(sMul(v1, v2), F(terms[i].sign)));
      }
      val = null;
      if (ok) { var p0 = parts[0], p1 = parts[1]; if (p0.c === 0 || p1.c === 0 || p0.r === p1.r) val = S(p0.c * p1.d + p1.c * p0.d, p0.c === 0 ? p1.r : p0.r, p0.d * p1.d); }
      tries++;
    } while (val === null && tries < 300);
    var atex = function (k) { return k < 0 ? '(' + k + '°)' : k + '°'; };
    var tex = terms.map(function (t, i) { return (i === 0 ? '' : (t.sign < 0 ? '-' : '+')) + FN[t.f1] + atex(t.a1) + '\\cdot' + FN[t.f2] + atex(t.a2); }).join('');
    return { q: '求 ' + T(tex) + ' 的值。',
             a: T(sTex(val)),
             h: '每個角先化到 $0°\\sim360°$（同界角），畫出終邊在哪個象限決定正負，再用參考角（終邊與 $x$ 軸的夾角）查特殊值。',
             p: { terms: terms, ans: sArr(val) } };
  };
  /* ── 2-2 極坐標與直角坐標互換 ── */
  L1.polarConv = function (r) {
    var kind = r.int(0, 1);
    if (kind === 0) {
      var rr = r.int(2, 8) * r.pick([1, 1, 2]), th = r.pick([30, 45, 60, 120, 135, 150, 210, 225, 240, 300, 315, 330]);
      var x = sMulF(tv(th).cos, F(rr)), y = sMulF(tv(th).sin, F(rr));
      return { q: '將極坐標 ' + T('[' + rr + ',' + th + '°]') + ' 化為直角坐標。',
               a: T('(' + sTex(x) + ',\\ ' + sTex(y) + ')'),
               h: '$x=r\\cos\\theta$、$y=r\\sin\\theta$；先判斷 $' + th + '°$ 在第幾象限決定正負，再用參考角查值。',
               p: { kind: 0, r: rr, th: th, ans: { x: sArr(x), y: sArr(y) } } };
    }
    var m = r.int(1, 5), pat = r.pick([[[1, 1, 1], [1, 3, 1], 60], [[1, 3, 1], [1, 1, 1], 30], [[1, 1, 1], [1, 1, 1], 45], [[0, 1, 1], [1, 1, 1], 90], [[1, 1, 1], [0, 1, 1], 0]]);
    var q = r.int(1, 4), sx = (q === 1 || q === 4) ? 1 : -1, sy = (q === 1 || q === 2) ? 1 : -1;
    var ref = pat[2], ang = q === 1 ? ref : q === 2 ? 180 - ref : q === 3 ? 180 + ref : 360 - ref;
    if (ref === 90) { sx = 1; ang = sy > 0 ? 90 : 270; } if (ref === 0) { sy = 1; ang = sx > 0 ? 0 : 180; }
    var X = S(sx * pat[0][0] * m, pat[0][1], 1), Y = S(sy * pat[1][0] * m, pat[1][1], 1), rad = ref === 45 ? m * Math.SQRT2 : 2 * m;
    var rTex = ref === 45 ? sTex(S(m, 2, 1)) : String(ref === 90 || ref === 0 ? m : 2 * m), rS = ref === 45 ? S(m, 2, 1) : S(ref === 90 || ref === 0 ? m : 2 * m, 1, 1);
    return { q: '將直角坐標 ' + T('(' + sTex(X) + ',\\ ' + sTex(Y) + ')') + ' 化為極坐標 ' + T('[r,\\theta]') + '（' + T('r>0') + '，' + T('0°\\le\\theta<360°') + '）。',
             a: T('[' + rTex + ',\\ ' + ang + '°]'),
             h: '$r=\\sqrt{x^2+y^2}$；由 $x$、$y$ 的正負先鎖定象限，再由 $\\tan$ 的絕對值（$\\dfrac{\\sqrt3}{3}$、$1$、$\\sqrt3$）找出參考角 $30°$、$45°$、$60°$。',
             p: { kind: 1, x: sArr(X), y: sArr(Y), ans: { r: sArr(rS), th: ang } } };
  };
  /* ── 2-2 極坐標下的距離與面積 ── */
  L1.polarDist = function (r) {
    var r1 = r.int(2, 9), r2 = r.int(2, 9), gap = r.pick([60, 90, 120]), th1 = r.int(0, 11) * 15, th2 = (th1 + gap) % 360;
    if (r.int(0, 1)) { var tmp = th1; th1 = th2; th2 = tmp; }
    var d2 = r1 * r1 + r2 * r2 - 2 * r1 * r2 * (gap === 60 ? 0.5 : gap === 90 ? 0 : -0.5), area = sMulF(tv(gap).sin, F(r1 * r2, 2));
    return { q: '設 $O$ 為極點，' + T('A[' + r1 + ',' + th1 + '°]') + '、' + T('B[' + r2 + ',' + th2 + '°]') + '。求 ' + T('\\angle AOB') + '、' + T(ov('AB')) + ' 與 ' + T('\\triangle OAB') + ' 的面積。',
             a: T('\\angle AOB=' + gap + '°') + '、' + T(ov('AB') + '=' + sqrtTex(d2)) + '、面積 ' + T('=' + sTex(area)),
             h: '夾角 $=$ 兩個極角的差（超過 $180°$ 就用 $360°$ 減）；$\\overline{AB}$ 用餘弦定理、面積用 $\\dfrac12r_1r_2\\sin\\angle AOB$——極坐標把「兩邊夾角」直接送給你。',
             p: { r1: r1, th1: th1, r2: r2, th2: th2, ans: { gap: gap, d2: d2, area: sArr(area) } } };
  };
  /* ── 2-3 斜角與斜率／兩直線夾角 ── */
  var SLOPES = [{ m: S(1, 3, 3), ang: 30, tex: '\\dfrac{\\sqrt3}{3}' }, { m: S(1, 1, 1), ang: 45, tex: '1' }, { m: S(1, 3, 1), ang: 60, tex: '\\sqrt3' }, { m: S(-1, 3, 1), ang: 120, tex: '-\\sqrt3' }, { m: S(-1, 1, 1), ang: 135, tex: '-1' }, { m: S(-1, 3, 3), ang: 150, tex: '-\\dfrac{\\sqrt3}{3}' }, { m: S(0, 1, 1), ang: 0, tex: '0' }];
  function lineOfSlope(sl, r) {   /* 回傳 ax+by+c=0 的 tex（整數係數） */
    var c = r.nz(-9, 9);
    if (sl.ang === 0) return { tex: 'y=' + c, m: sl };
    if (sl.ang === 45 || sl.ang === 135) { var s = sl.ang === 45 ? '-' : '+'; return { tex: 'x' + s + 'y' + (c > 0 ? '+' : '') + c + '=0', m: sl }; }
    if (sl.ang === 60 || sl.ang === 120) { var s2 = sl.ang === 60 ? '-' : '+'; return { tex: '\\sqrt3x' + s2 + 'y' + (c > 0 ? '+' : '') + c + '=0', m: sl }; }
    var s3 = sl.ang === 30 ? '-' : '+'; return { tex: 'x' + s3 + '\\sqrt3y' + (c > 0 ? '+' : '') + c + '=0', m: sl };
  }
  L1.slopeAngle = function (r) {
    var kind = r.int(0, 2);
    if (kind === 0) {
      var sl = r.pick(SLOPES), L = lineOfSlope(sl, r);
      return { q: '求直線 ' + T(L.tex) + ' 的斜角。',
               a: T(sl.ang + '°'),
               h: '先把直線整理成 $y=mx+k$ 讀出斜率 $m=' + sl.tex + '$，斜角 $\\alpha$ 滿足 $\\tan\\alpha=m$ 且 $0°\\le\\alpha<180°$（$m<0$ 時斜角是鈍角）。',
               p: { kind: 0, ang: sl.ang, ans: sl.ang } };
    }
    if (kind === 1) {
      var s1 = r.pick(SLOPES), s2; do { s2 = r.pick(SLOPES); } while (s2.ang === s1.ang);
      var L1_ = lineOfSlope(s1, r), L2_ = lineOfSlope(s2, r), dif = Math.abs(s1.ang - s2.ang), acute = dif > 90 ? 180 - dif : dif;
      return { q: '求 ' + T('L_1:' + L1_.tex) + ' 與 ' + T('L_2:' + L2_.tex) + ' 的銳夾角（或直角）。',
               a: T(acute + '°'),
               h: '兩條線的斜角分別是 $' + s1.ang + '°$ 與 $' + s2.ang + '°$，夾角就是斜角的差（差超過 $90°$ 就用 $180°$ 減）。',
               p: { kind: 1, a1: s1.ang, a2: s2.ang, ans: acute } };
    }
    var sl3 = r.pick(SLOPES.slice(0, 6)), px = r.nz(-6, 6), py = r.nz(-6, 6), Ptex = '(' + px + ',' + py + ')';
    /* 過 P 斜率 m 的直線：m 為 ±1 → x∓y+c=0；±√3 → √3x∓y+c=0；±√3/3 → x∓√3y+c=0 */
    var tex, c1;
    if (sl3.ang === 45 || sl3.ang === 135) { c1 = sl3.ang === 45 ? py - px : -(px + py); tex = 'x' + (sl3.ang === 45 ? '-' : '+') + 'y' + (c1 === 0 ? '' : (c1 > 0 ? '+' : '') + c1) + '=0'; c1 = { rat: c1, surd: 0 }; }
    else if (sl3.ang === 60 || sl3.ang === 120) { var sgn = sl3.ang === 60 ? -1 : 1, rt = -sgn * py; tex = '\\sqrt3x' + (sgn < 0 ? '-' : '+') + 'y' + (rt === 0 ? '' : (rt > 0 ? '+' : '') + rt) + ((-px) === 0 ? '' : ((-px) > 0 ? '+' : '-') + Math.abs(px) + '\\sqrt3') + '=0'; c1 = { rat: rt, surd: -px }; }
    else { var sg = sl3.ang === 30 ? -1 : 1, sd = -sg * py; tex = 'x' + (sg < 0 ? '-' : '+') + '\\sqrt3y' + ((-px) === 0 ? '' : ((-px) > 0 ? '+' : '') + (-px)) + (sd === 0 ? '' : (sd > 0 ? '+' : '-') + Math.abs(py) + '\\sqrt3') + '=0'; c1 = { rat: -px, surd: sd }; }
    return { q: '直線 $L$ 過點 ' + T('P' + Ptex) + '，且斜角為 ' + T(sl3.ang + '°') + '。求 $L$ 的方程式。',
             a: T(tex),
             h: '斜率 $m=\\tan' + sl3.ang + '°=' + sl3.tex + '$，點斜式 $y-(' + py + ')=m(x-(' + px + '))$ 整理成一般式。',
             p: { kind: 2, ang: sl3.ang, px: px, py: py, ans: { tex: tex } } };
  };

  /* ── 3-1 正弦定理求邊 ── */
  L1.sineLaw = function (r) {
    var A, B; do { A = r.pick([30, 45, 60, 90, 120, 135, 150]); B = r.pick([30, 45, 60]); } while (A + B >= 180);
    var C = 180 - A - B, a = r.pick([2, 4, 6, 8, 10, 12]), b = sMulF(sDiv(tv(B).sin, tv(A).sin), F(a));
    return { q: ABC + ' 中 ' + T('\\angle A=' + A + '°') + '、' + T('\\angle B=' + B + '°') + '、' + T('a=' + a) + '。求 ' + T('\\angle C') + ' 與 ' + T('b') + '。',
             a: T('\\angle C=' + C + '°') + '、' + T('b=' + sTex(b)),
             h: '正弦定理 $\\dfrac{a}{\\sin A}=\\dfrac{b}{\\sin B}$ ⟹ $b=\\dfrac{a\\sin B}{\\sin A}$；兩角都是特殊角，值直接代。',
             p: { A: A, B: B, a: a, ans: { C: C, b: sArr(b) } } };
  };
  /* ── 3-1 外接圓半徑 ── */
  L1.circumR = function (r) {
    var kind = r.int(0, 1);
    if (kind === 0) {
      var A = r.pick([30, 45, 60, 90, 120, 135, 150]), a = r.pick([2, 3, 4, 5, 6, 8, 9, 10, 12]), R = sDiv(S(a, 1, 2), tv(A).sin);
      return { q: ABC + ' 中 ' + T('a=' + a) + '、' + T('\\angle A=' + A + '°') + '。求外接圓半徑 $R$。',
               a: T('R=' + sTex(R)),
               h: '$\\dfrac{a}{\\sin A}=2R$ ⟹ $R=\\dfrac{a}{2\\sin A}$。',
               p: { kind: 0, a: a, A: A, ans: sArr(R) } };
    }
    var R2 = r.pick([5, 6, 8, 10, 12, 13, 15]), b = r.int(2, 2 * R2 - 1), sB = F(b, 2 * R2);
    return { q: ABC + ' 的外接圓半徑為 ' + T(String(R2)) + '，且 ' + T('b=' + b) + '。求 ' + T('\\sin B') + '，並說明 $\\angle B$ 有幾種可能。',
             a: T('\\sin B=' + Fr.tex(sB)) + '，$\\angle B$ 有兩種可能（一銳角一鈍角，互補）',
             h: '$b=2R\\sin B$；$\\sin B<1$ 時，銳角與它的補角有相同的正弦值，所以一題兩解。',
             p: { kind: 1, R: R2, b: b, ans: { sinB: fr2(sB), count: 2 } } };
  };
  /* ── 3-2 餘弦定理求邊（SAS） ── */
  L1.cosLawSide = function (r) {
    var A = r.pick([60, 90, 120]), b = r.int(2, 12), c = r.int(2, 12), a2 = b * b + c * c - 2 * b * c * (A === 60 ? 0.5 : A === 90 ? 0 : -0.5);
    return { q: ABC + ' 中 ' + T('b=' + b) + '、' + T('c=' + c) + '、' + T('\\angle A=' + A + '°') + '。求 $a$。',
             a: T('a=' + sqrtTex(a2)),
             h: '兩邊夾角求第三邊：$a^2=b^2+c^2-2bc\\cos A$，$\\cos' + A + '°=' + (A === 60 ? '\\dfrac12' : A === 90 ? '0' : '-\\dfrac12') + '$。',
             p: { A: A, b: b, c: c, ans: { a2: a2 } } };
  };
  /* ── 3-2 餘弦定理求角（SSS）與形狀 ── */
  L1.cosLawAngle = function (r) {
    var a, b, c; do { a = r.int(2, 12); b = r.int(2, 12); c = r.int(2, 12); } while (!validTri(a, b, c) || (a === b && b === c));
    var m = Math.max(a, b, c), o = [a, b, c].filter(function (v, i, arr) { return i !== arr.indexOf(m); });
    var cs = cosLaw(o[0], o[1], m), sh = shapeOf(a, b, c);
    return { q: ABC + ' 三邊長為 ' + T(a + ',\\ ' + b + ',\\ ' + c) + '。求最大角的餘弦值，並判斷此三角形的形狀。',
             a: T('\\cos=' + Fr.tex(cs)) + '，' + SHAPE[sh],
             h: '最大角對最大邊 $' + m + '$：$\\cos=\\dfrac{' + o[0] + '^2+' + o[1] + '^2-' + m + '^2}{2\\cdot' + o[0] + '\\cdot' + o[1] + '}$；餘弦值正、零、負分別對應銳角、直角、鈍角三角形。',
             p: { a: a, b: b, c: c, ans: { cos: fr2(cs), shape: sh } } };
  };
  /* ── 3-3 三角形的存在條件與鈍角範圍 ── */
  L1.sideRange = function (r) {
    var b, c; do { b = r.int(2, 12); c = r.int(2, 12); } while (b === c);
    var lo = Math.abs(b - c), hi = b + c, big = Math.max(b, c), sm = Math.min(b, c), s1 = big * big - sm * sm, s2 = b * b + c * c;
    return { q: ABC + ' 中 ' + T(ov('AB') + '=' + c) + '、' + T(ov('AC') + '=' + b) + '、' + T(ov('BC') + '=a') + '。(1) 求 $a$ 的範圍。(2) 求 ' + ABC + ' 為鈍角三角形時 $a$ 的範圍。',
             a: '(1) ' + T(lo + '<a<' + hi) + '　(2) ' + T(lo + '<a<' + sqrtTex(s1)) + ' 或 ' + T(sqrtTex(s2) + '<a<' + hi),
             h: '(1) 兩邊之差 $<a<$ 兩邊之和。(2) 分「$a$ 是最大邊」（$a^2>' + b + '^2+' + c + '^2$）與「$' + big + '$ 是最大邊」（$' + big + '^2>a^2+' + sm + '^2$）兩段討論，再與 (1) 取交集。',
             p: { b: b, c: c, ans: { lo: lo, hi: hi, s1: s1, s2: s2 } } };
  };
  /* ── 3-3 SSA 有幾組解 ── */
  L1.ssaCount = function (r) {
    var A = r.pick([30, 30, 45, 60, 120, 150]), b = r.int(3, 12), a = r.int(1, 14), h = b * sNum(tv(A).sin), cnt;
    if (A >= 90) cnt = a > b ? 1 : 0;
    else if (Math.abs(a - h) < 1e-9) cnt = 1; else if (a < h) cnt = 0; else if (a < b) cnt = 2; else cnt = 1;
    return { q: ABC + ' 中 ' + T('\\angle A=' + A + '°') + '、' + T(ov('AC') + '=' + b) + '、' + T(ov('BC') + '=' + a) + '。這樣的三角形有幾組解？',
             a: T(String(cnt)) + ' 組',
             h: (A < 90 ? '先算「高」$h=' + b + '\\sin' + A + '°$：$a<h$ 無解、$a=h$ 一解（直角）、$h<a<' + b + '$ 兩解、$a\\ge' + b + '$ 一解。' : '$\\angle A$ 是鈍角 ⟹ 對邊 $a$ 必須是最大邊：$a>' + b + '$ 才有一解，否則無解。'),
             p: { A: A, b: b, a: a, ans: cnt } };
  };

  /* ── 4-1 面積公式 ── */
  L1.areaSAS = function (r) {
    var kind = r.int(0, 1), a = r.int(2, 12), b = r.int(2, 12);
    if (kind === 0) {
      var C = r.pick([30, 45, 60, 90, 120, 135, 150]), K = sMulF(tv(C).sin, F(a * b, 2));
      return { q: ABC + ' 中 ' + T('a=' + a) + '、' + T('b=' + b) + '、' + T('\\angle C=' + C + '°') + '。求 ' + ABC + ' 的面積。',
               a: T(sTex(K)),
               h: '面積 $=\\dfrac12ab\\sin C$（兩邊夾角）；$\\sin' + C + '°$ 用參考角查值，鈍角的正弦仍為正。',
               p: { kind: 0, a: a, b: b, C: C, ans: sArr(K) } };
    }
    var sC = r.pick([[1, 2], [1, 1]]), K2 = F(a * b * sC[0], 2 * sC[1]), angs = sC[1] === 1 ? [90] : [30, 150];
    return { q: ABC + ' 中 ' + T('a=' + a) + '、' + T('b=' + b) + '，且面積為 ' + T(Fr.tex(K2)) + '。求 ' + T('\\angle C') + '（所有可能）。',
             a: T('\\angle C=' + angs.join('°\\ \\text{或}\\ ') + '°'),
             h: '$\\dfrac12ab\\sin C=$ 面積 ⟹ $\\sin C=' + Fr.tex(F(sC[0], sC[1])) + '$；$\\sin C<1$ 時銳角與鈍角各一解，$\\sin C=1$ 只有 $90°$。',
             p: { kind: 1, a: a, b: b, K: fr2(K2), ans: angs } };
  };
  /* ── 4-2 海龍公式 ── */
  function niceTri(r, maxR) {
    var a, b, c, K2, K, tries = 0;
    do { a = r.int(2, 15); b = r.int(2, 15); c = r.int(2, 15); K2 = validTri(a, b, c) ? heron2(a, b, c) : null; K = K2 ? sqrtF(K2) : null; tries++; }
    while ((!K2 || K.r > maxR || a === b && b === c) && tries < 500);
    return [a, b, c, K];
  }
  L1.heronArea = function (r) {
    var t = niceTri(r, 15), a = t[0], b = t[1], c = t[2], K = t[3], s = F(a + b + c, 2);
    return { q: '求三邊長為 ' + T(a + ',\\ ' + b + ',\\ ' + c) + ' 的三角形面積。',
             a: T(sTex(K)),
             h: '海龍公式：$s=\\dfrac{' + a + '+' + b + '+' + c + '}2=' + Fr.tex(s) + '$，面積 $=\\sqrt{s(s-a)(s-b)(s-c)}$；也可先用餘弦定理求一角再用 $\\dfrac12ab\\sin C$。',
             p: { a: a, b: b, c: c, ans: sArr(K) } };
  };
  /* ── 4-3 內切圓與外接圓半徑 ── */
  L1.inOutRadius = function (r) {
    var t = niceTri(r, 15), a = t[0], b = t[1], c = t[2], K = t[3];
    var rin = sDiv(K, S(a + b + c, 1, 2)), R = sDiv(S(a * b * c, 1, 4), K);
    return { q: ABC + ' 三邊長為 ' + T(a + ',\\ ' + b + ',\\ ' + c) + '。求 (1) 面積　(2) 內切圓半徑 $r$　(3) 外接圓半徑 $R$。',
             a: '(1) ' + T(sTex(K)) + '　(2) ' + T('r=' + sTex(rin)) + '　(3) ' + T('R=' + sTex(R)),
             h: '面積是橋：$r=\\dfrac{K}{s}$（$s$ 為半周長）、$R=\\dfrac{abc}{4K}$。分母有根號要有理化。',
             p: { a: a, b: b, c: c, ans: { K: sArr(K), r: sArr(rin), R: sArr(R) } } };
  };
  /* ── 4-4 中線長 ── */
  L1.medianLen = function (r) {
    var a, b, c; do { a = r.int(2, 14); b = r.int(2, 14); c = r.int(2, 14); } while (!validTri(a, b, c));
    var m = sqrtF(F(2 * b * b + 2 * c * c - a * a, 4));
    return { q: ABC + ' 中 ' + T(ov('AB') + '=' + c) + '、' + T(ov('AC') + '=' + b) + '、' + T(ov('BC') + '=' + a) + '，$M$ 為 $\\overline{BC}$ 的中點。求 ' + T(ov('AM')) + '。',
             a: T(ov('AM') + '=' + sTex(m)),
             h: '中線長公式 $\\overline{AM}^2=\\dfrac{2\\overline{AB}^2+2\\overline{AC}^2-\\overline{BC}^2}{4}$（先求 $\\cos B$ 再在 $\\triangle ABM$ 用餘弦定理也行）。',
             p: { a: a, b: b, c: c, ans: sArr(m) } };
  };
  /* ── 4-4 角平分線長 ── */
  L1.bisectorLen = function (r) {
    var A = r.pick([60, 90, 120]), b = r.int(2, 12), c = r.int(2, 12), half = tv(A / 2).cos, AD = sMulF(half, F(2 * b * c, b + c));
    return { q: ABC + ' 中 ' + T(ov('AB') + '=' + c) + '、' + T(ov('AC') + '=' + b) + '、' + T('\\angle A=' + A + '°') + '，$\\overline{AD}$ 為 $\\angle A$ 的內角平分線（$D$ 在 $\\overline{BC}$ 上）。求 ' + T(ov('BD') + ':' + ov('DC')) + ' 與 ' + T(ov('AD')) + '。',
             a: T(ov('BD') + ':' + ov('DC') + '=' + c + ':' + b) + '、' + T(ov('AD') + '=' + sTex(AD)),
             h: '角平分線把對邊分成兩邊之比；長度用「面積切兩半」：$\\dfrac12bc\\sin' + A + '°=\\dfrac12\\overline{AD}(b+c)\\sin' + (A / 2) + '°$。',
             p: { A: A, b: b, c: c, ans: { ratio: [c, b], AD: sArr(AD) } } };
  };
  /* ── 4-5 圓內接四邊形 ── */
  function cyclic(r) {
    var a, b, c, d, cB, tries = 0;
    do { a = r.int(2, 9); b = r.int(2, 9); c = r.int(2, 9); d = r.int(2, 9); tries++; }
    while ((a >= b + c + d || b >= a + c + d || c >= a + b + d || d >= a + b + c || (a === c && b === d)) && tries < 300);
    cB = F(a * a + b * b - c * c - d * d, 2 * (a * b + c * d));
    var AC2 = Fr.sub(F(a * a + b * b), Fr.mul(F(2 * a * b), cB)), sB = sqrtF(Fr.sub(F(1), Fr.mul(cB, cB))), area = sMulF(sB, F(a * b + c * d, 2));
    return { a: a, b: b, c: c, d: d, cB: cB, AC2: AC2, sB: sB, area: area };
  }
  L1.cyclicQuad = function (r) {
    var Q = cyclic(r);
    return { q: '圓內接四邊形 $ABCD$ 中 ' + T(ov('AB') + '=' + Q.a) + '、' + T(ov('BC') + '=' + Q.b) + '、' + T(ov('CD') + '=' + Q.c) + '、' + T(ov('DA') + '=' + Q.d) + '。求 ' + T('\\cos B') + ' 與對角線 ' + T(ov('AC')) + '。',
             a: T('\\cos B=' + Fr.tex(Q.cB)) + '、' + T(ov('AC') + '=' + sTex(sqrtF(Q.AC2))),
             h: '對角互補 ⟹ $\\cos D=-\\cos B$。在 $\\triangle ABC$ 與 $\\triangle ADC$ 各用一次餘弦定理算 $\\overline{AC}^2$，兩式相等解出 $\\cos B$。',
             p: { a: Q.a, b: Q.b, c: Q.c, d: Q.d, ans: { cosB: fr2(Q.cB), AC2: fr2(Q.AC2) } } };
  };

  /* ── 5-1 正射影 ── */
  L1.projLen = function (r) {
    var kind = r.int(0, 1), L = r.pick([4, 6, 8, 10, 12, 16, 20]);
    if (kind === 0) {
      var th = r.pick([30, 45, 60, 120, 135, 150]), p = sMulF(tv(th).cos, F(th > 90 ? -L : L));
      return { q: '線段 ' + T(ov('AB') + '=' + L) + ' 與直線 $L$ 所夾的角為 ' + T(th + '°') + '。求 $\\overline{AB}$ 在 $L$ 上的正射影長。',
               a: T(sTex(p)),
               h: '正射影長 $=\\overline{AB}\\cdot|\\cos\\theta|$；夾角超過 $90°$ 時用它的補角，長度永遠是正的。',
               p: { kind: 0, L: L, th: th, ans: sArr(p) } };
    }
    var th2 = r.pick([30, 45, 60]), hx = sMulF(tv(th2).cos, F(L)), vy = sMulF(tv(th2).sin, F(L));
    return { q: '一根長 ' + T(String(L)) + ' 公尺的梯子斜靠牆面，與地面夾 ' + T(th2 + '°') + ' 角。求梯腳到牆的距離與梯頂離地的高度。',
             a: '梯腳到牆 ' + T(sTex(hx)) + ' 公尺、梯頂高 ' + T(sTex(vy)) + ' 公尺',
             h: '梯子在地面上的正射影 $=L\\cos\\theta$，在牆上的正射影 $=L\\sin\\theta$。',
             p: { kind: 1, L: L, th: th2, ans: { x: sArr(hx), y: sArr(vy) } } };
  };
  /* ── 5-2 投影定理 ── */
  L1.projTheorem = function (r) {
    var a, b, c; do { a = r.int(3, 13); b = r.int(3, 13); c = r.int(3, 13); } while (!validTri(a, b, c));
    var cB = cosLaw(a, c, b), cC = cosLaw(a, b, c);
    return { q: ABC + ' 中 ' + T('a=' + a) + '、' + T('b=' + b) + '、' + T('c=' + c) + '。求 ' + T('\\cos B') + '、' + T('\\cos C') + '，並驗證 ' + T('b\\cos C+c\\cos B=a') + '。',
             a: T('\\cos B=' + Fr.tex(cB)) + '、' + T('\\cos C=' + Fr.tex(cC)) + '；' + T('b\\cos C+c\\cos B=' + a) + ' ✓',
             h: '餘弦定理各算一次；投影定理的意思是「$\\overline{AB}$、$\\overline{AC}$ 在 $\\overline{BC}$ 上的正射影加起來剛好是 $a$」。',
             p: { a: a, b: b, c: c, ans: { cosB: fr2(cB), cosC: fr2(cC), sum: a } } };
  };
  /* ── 5-3 長方體的立體測量 ── */
  L1.cuboid = function (r) {
    var Q = r.pick([[3, 4, 12, 13], [4, 3, 12, 13], [6, 8, 24, 26], [1, 2, 2, 3], [2, 1, 2, 3], [2, 3, 6, 7], [3, 2, 6, 7], [4, 4, 7, 9], [2, 6, 9, 11], [6, 2, 9, 11], [1, 4, 8, 9], [4, 1, 8, 9], [2, 4, 4, 6], [4, 2, 4, 6], [6, 6, 7, 11]]);
    var p = Q[0], q = Q[1], h = Q[2], D = Q[3], fd2 = p * p + q * q, sn = F(h, D), cs = sqrtF(F(fd2, D * D)), tn = sqrtF(F(h * h, fd2));
    return { q: '長方體 $ABCD$-$EFGH$ 中 ' + T(ov('AB') + '=' + p) + '、' + T(ov('BC') + '=' + q) + '、' + T(ov('AE') + '=' + h) + '（$\\overline{AE}$ 為鉛直稜）。求體對角線 ' + T(ov('AG')) + '，以及 $\\overline{AG}$ 與底面所夾角 $\\theta$ 的 ' + T('\\sin\\theta') + '、' + T('\\cos\\theta') + '、' + T('\\tan\\theta') + '。',
             a: T(ov('AG') + '=' + D) + '、' + T('\\sin\\theta=' + Fr.tex(sn)) + '、' + T('\\cos\\theta=' + sTex(cs)) + '、' + T('\\tan\\theta=' + sTex(tn)),
             h: '先算底面對角線 $\\overline{AC}=\\sqrt{' + p + '^2+' + q + '^2}$，再算 $\\overline{AG}=\\sqrt{\\overline{AC}^2+' + h + '^2}$；$\\theta$ 在直角 $\\triangle ACG$ 裡：對邊 $' + h + '$、鄰邊 $\\overline{AC}$、斜邊 $\\overline{AG}$。',
             p: { p: p, q: q, h: h, ans: { D: D, fd2: fd2, sin: fr2(sn), cos: sArr(cs), tan: sArr(tn) } } };
  };
  /* ── 5-4 正四角錐 ── */
  L1.pyramid = function (r) {
    var t = r.pick([[3, 4, 5], [4, 3, 5], [5, 12, 13], [12, 5, 13], [6, 8, 10], [8, 6, 10], [8, 15, 17], [15, 8, 17], [9, 12, 15], [12, 9, 15]]);
    var s = t[0], h = t[1], l = t[2], e2 = h * h + 2 * s * s, tanD = F(h, s), cosE = sqrtF(F(2 * s * s, e2));
    return { q: '正四角錐 $V$-$ABCD$ 的底面是邊長 ' + T(String(2 * s)) + ' 的正方形，側稜長 ' + T(ov('VA') + '=' + sqrtTex(e2)) + '。求 (1) 體高　(2) 斜高（$V$ 到底邊中點的距離）　(3) 側面與底面所夾角的正切值　(4) 側稜與底面所夾角的餘弦值。',
             a: '(1) ' + T(String(h)) + '　(2) ' + T(String(l)) + '　(3) ' + T(Fr.tex(tanD)) + '　(4) ' + T(sTex(cosE)),
             h: '兩個直角三角形：「體高、半對角線 $' + s + '\\sqrt2$、側稜」給體高；「體高、半邊長 $' + s + '$、斜高」給斜高與側面夾角。側稜與底面的夾角在第一個三角形裡。',
             p: { s: s, h: h, l: l, e2: e2, ans: { h: h, l: l, tan: fr2(tanD), cos: sArr(cosE) } } };
  };

  /* ═══════════════════════ L2 ═══════════════════════ */
  var L2 = {};

  /* 2-1 廣義角的同角關係：象限＋和 → 積、差、tan（例題 11 型；平方關係 10 卷） */
  L2.quadSumProd = function (r) {
    var t = tri(r), a = t[0], b = t[1], c = t[2], quad = r.int(2, 4), sg = { 2: [1, -1], 3: [-1, -1], 4: [-1, 1] }[quad];
    if (r.int(0, 1)) { var tmp = a; a = b; b = tmp; }
    var sn = F(sg[0] * a, c), cs = F(sg[1] * b, c), sum = Fr.add(sn, cs), prod = Fr.mul(sn, cs), diff = Fr.sub(sn, cs), tn = Fr.div(sn, cs);
    return { q: '已知 $\\theta$ 為第' + ['', '', '二', '三', '四'][quad] + '象限角，且 ' + T('\\sin\\theta+\\cos\\theta=' + Fr.tex(sum)) + '。求 (1) ' + T('\\sin\\theta\\cos\\theta') + '　(2) ' + T('\\sin\\theta-\\cos\\theta') + '　(3) ' + T('\\tan\\theta') + '。',
             a: '(1) ' + T(Fr.tex(prod)) + '　(2) ' + T(Fr.tex(diff)) + '　(3) ' + T(Fr.tex(tn)),
             h: '平方：$1+2\\sin\\theta\\cos\\theta=(\\text{和})^2$ 得積；$(\\sin\\theta-\\cos\\theta)^2=1-2\\sin\\theta\\cos\\theta$ 開根號後<b>用象限定號</b>（第' + ['', '', '二', '三', '四'][quad] + '象限 ' + (quad === 2 ? '$\\sin>0>\\cos$ ⟹ 差為正' : quad === 3 ? '兩者皆負，比大小看數值' : '$\\cos>0>\\sin$ ⟹ 差為負') + '）；和差聯立得 $\\sin$、$\\cos$ 再相除。',
             p: { quad: quad, sum: fr2(sum), ans: { prod: fr2(prod), diff: fr2(diff), tan: fr2(tn) } } };
  };
  /* 2-2 誘導公式化簡（誘導 12 卷） */
  function reduceOne(fn, k, m) {   /* fn(k·90° + m·θ) → {sign, es, ec}：結果 = sign·sin^es θ·cos^ec θ */
    var kk = ((k % 4) + 4) % 4, even = (kk % 2 === 0), sg;
    if (fn === 'sin') { if (even) { sg = (kk === 0 ? 1 : -1) * m; return { sign: sg, es: 1, ec: 0 }; } sg = (kk === 1 ? 1 : -1); return { sign: sg, es: 0, ec: 1 }; }
    if (fn === 'cos') { if (even) { sg = (kk === 0 ? 1 : -1); return { sign: sg, es: 0, ec: 1 }; } sg = -(kk === 1 ? 1 : -1) * m; return { sign: sg, es: 1, ec: 0 }; }
    if (even) return { sign: m, es: 1, ec: -1 }; return { sign: -m, es: -1, ec: 1 };
  }
  function argTex(k, m) { var base = k === 0 ? '' : (k * 90) + '°'; if (k === 0) return m > 0 ? '\\theta' : '(-\\theta)'; return '(' + base + (m > 0 ? '+' : '-') + '\\theta)'; }
  function resultTex(sign, es, ec) {
    var body;
    if (es === 0 && ec === 0) body = '1';
    else if (es === -ec) { var e = es; body = e > 0 ? (e === 1 ? '\\tan\\theta' : '\\tan^' + e + '\\theta') : (e === -1 ? '\\dfrac{1}{\\tan\\theta}' : '\\dfrac{1}{\\tan^' + (-e) + '\\theta}'); }
    else { var num = '', den = '';
      if (es > 0) num += (es === 1 ? '\\sin\\theta' : '\\sin^' + es + '\\theta'); if (ec > 0) num += (ec === 1 ? '\\cos\\theta' : '\\cos^' + ec + '\\theta');
      if (es < 0) den += (es === -1 ? '\\sin\\theta' : '\\sin^' + (-es) + '\\theta'); if (ec < 0) den += (ec === -1 ? '\\cos\\theta' : '\\cos^' + (-ec) + '\\theta');
      body = den ? '\\dfrac{' + (num || '1') + '}{' + den + '}' : num; }
    return (sign < 0 ? '-' : '') + body;
  }
  L2.reduceSimplify = function (r) {
    var fns = ['sin', 'cos', 'tan'], ks = [-3, -2, -1, 0, 1, 2, 3, 4, 5, 6], fac, res, tries = 0, ok;
    do {
      fac = []; res = { sign: 1, es: 0, ec: 0 };
      for (var i = 0; i < 4; i++) {
        var fn = r.pick(fns), k = r.pick(ks), m = r.sign(); if (k === 0 && m === 1 && r.int(0, 1)) m = -1;
        var rr = reduceOne(fn, k, m), top = i < 2;
        fac.push({ fn: fn, k: k, m: m }); res.sign *= rr.sign; res.es += top ? rr.es : -rr.es; res.ec += top ? rr.ec : -rr.ec;
      }
      ok = Math.abs(res.es) <= 2 && Math.abs(res.ec) <= 2 && !(res.es === 0 && res.ec === 0 && tries < 40);
      tries++;
    } while (!ok && tries < 200);
    var tex = '\\dfrac{' + FN[fac[0].fn] + argTex(fac[0].k, fac[0].m) + '\\cdot' + FN[fac[1].fn] + argTex(fac[1].k, fac[1].m) + '}{' + FN[fac[2].fn] + argTex(fac[2].k, fac[2].m) + '\\cdot' + FN[fac[3].fn] + argTex(fac[3].k, fac[3].m) + '}';
    return { q: '化簡 ' + T(tex) + '。',
             a: T(resultTex(res.sign, res.es, res.ec)),
             h: '「奇變偶不變，符號看象限」：$90°$、$270°$ 的奇數倍 $\\sin\\leftrightarrow\\cos$、$\\tan\\to\\dfrac1{\\tan}$；把 $\\theta$ 當銳角，看原角落在哪個象限決定每一項的正負。',
             p: { fac: fac, ans: { sign: res.sign, es: res.es, ec: res.ec } } };
  };
  /* 2-3 三個極坐標點圍成的三角形（極坐標 18 卷） */
  L2.polarTriangle = function (r) {
    var gaps = r.pick([[120, 120, 120], [90, 90, 180], [60, 120, 180], [90, 120, 150], [60, 150, 150], [90, 90, 180]]);
    var r1 = r.int(2, 8), r2 = r.int(2, 8), r3 = r.int(2, 8), th1 = r.int(0, 23) * 15, th2 = (th1 + gaps[0]) % 360, th3 = (th2 + gaps[1]) % 360;
    var rat = F(0), surd = S(0, 1, 1), pairs = [[r1, r2, gaps[0]], [r2, r3, gaps[1]], [r3, r1, gaps[2]]];
    pairs.forEach(function (pr) { var v = sMulF(tv(pr[2]).sin, F(pr[0] * pr[1], 2)); if (v.c === 0) return; if (v.r === 1) rat = Fr.add(rat, sToF(v)); else surd = surd.c === 0 ? v : S(surd.c * v.d + v.c * surd.d, 3, surd.d * v.d); });
    var g = gaps[0], AB2 = (g === 60 || g === 90 || g === 120 || g === 180) ? r1 * r1 + r2 * r2 - 2 * r1 * r2 * (g === 60 ? 0.5 : g === 90 ? 0 : g === 120 ? -0.5 : -1) : null;
    return { q: '極坐標平面上 $O$ 為極點，' + T('A[' + r1 + ',' + th1 + '°]') + '、' + T('B[' + r2 + ',' + th2 + '°]') + '、' + T('C[' + r3 + ',' + th3 + '°]') + '。求 ' + (AB2 !== null ? T(ov('AB')) + ' 與 ' : '') + T('\\triangle ABC') + ' 的面積。',
             a: (AB2 !== null ? T(ov('AB') + '=' + sqrtTex(AB2)) + '、' : '') + '面積 ' + T('=' + twoTex(rat, surd)),
             h: '三個極角把 $360°$ 切成 $' + gaps[0] + '°$、$' + gaps[1] + '°$、$' + gaps[2] + '°$，極點在三角形內（或邊上）⟹ $\\triangle ABC=\\triangle OAB+\\triangle OBC+\\triangle OCA$，每塊用 $\\dfrac12r_ir_j\\sin(\\text{夾角})$。' + (AB2 !== null ? '$\\overline{AB}$ 用餘弦定理。' : ''),
             p: { r: [r1, r2, r3], th: [th1, th2, th3], gaps: gaps, ans: { AB2: AB2, rat: fr2(rat), surd: sArr(surd) } } };
  };
  /* 2-4 與已知直線夾特殊角的直線（斜角；建中 113 填 11 型） */
  L2.lineAngle = function (r) {
    var s1 = r.pick(SLOPES.slice(0, 6)), phi = (s1.ang % 45 === 0 && s1.ang % 90 !== 0) ? 45 : r.pick([30, 60]), L = lineOfSlope(s1, r), px = r.nz(-6, 6), py = r.nz(-6, 6);
    var angs = [((s1.ang + phi) % 180 + 180) % 180, ((s1.ang - phi) % 180 + 180) % 180];
    var slopeTex = function (ang) { return ang === 90 ? '不存在（鉛直線 $x=' + px + '$）' : T('m=' + sTex(tv(ang).tan)); };
    return { q: '直線 $L$ 過點 ' + T('P(' + px + ',' + py + ')') + '，且與直線 ' + T('L_1:' + L.tex) + ' 夾 ' + T(phi + '°') + ' 角。求 $L$ 的斜角與斜率（兩解）。',
             a: '斜角 ' + T(angs[0] + '°') + '：斜率' + slopeTex(angs[0]) + '；斜角 ' + T(angs[1] + '°') + '：斜率' + slopeTex(angs[1]),
             h: '用斜角不要用夾角公式：$L_1$ 的斜率 $' + s1.tex + '$ ⟹ 斜角 $' + s1.ang + '°$；$L$ 的斜角 $=' + s1.ang + '°\\pm' + phi + '°$（超出 $0°\\sim180°$ 就加減 $180°$）。斜角 $90°$ 是鉛直線，斜率不存在，最常被漏掉。',
             p: { ang1: s1.ang, phi: phi, px: px, py: py, ans: { angs: angs } } };
  };
  /* 2-5 sin 比 ⟹ 邊比：最大角、形狀、給周長求面積（正弦定理 21 卷） */
  L2.sineRatio = function (r) {
    var p, q, w, K, tries = 0;
    do { p = r.int(2, 9); q = r.int(2, 9); w = r.int(2, 9); tries++; K = validTri(p, q, w) ? sqrtF(heron2(p, q, w)) : null; } while ((!K || (p === q && q === w) || K.r > 15) && tries < 300);
    var m = Math.max(p, q, w), o = [p, q, w].filter(function (v, i, arr) { return i !== arr.indexOf(m); }), cs = cosLaw(o[0], o[1], m), sh = shapeOf(p, q, w);
    var k = r.pick([1, 2, 3]), P = k * (p + q + w), K2 = sMulF(K, F(k * k));
    return { q: ABC + ' 中 ' + T('\\sin A:\\sin B:\\sin C=' + p + ':' + q + ':' + w) + '。(1) 求最大角的餘弦值並判斷形狀。(2) 若周長為 ' + T(String(P)) + '，求 ' + ABC + ' 的面積。',
             a: '(1) ' + T('\\cos=' + Fr.tex(cs)) + '，' + SHAPE[sh] + '　(2) ' + T(sTex(K2)),
             h: '正弦定理 ⟹ $a:b:c=' + p + ':' + q + ':' + w + '$，設三邊 $' + p + 'k,' + q + 'k,' + w + 'k$。最大角對最大邊用餘弦定理（$k$ 會消掉）；周長定出 $k=' + k + '$ 再海龍。',
             p: { p: p, q: q, w: w, P: P, ans: { cos: fr2(cs), shape: sh, K: sArr(K2) } } };
  };
  /* 2-6 D 在 BC 上的餘弦定理串連（餘弦定理 21 卷） */
  L2.cevianLen = function (r) {
    var kind = r.int(0, 1), tries = 0;
    if (kind === 0) {
      var AB, BD, DC, AD, AC2;
      do { AD = r.int(2, 9); BD = r.int(2, 9); DC = r.int(1, 9); AB = r.int(2, 12); tries++;
        if (!validTri(AD, BD, AB)) { AC2 = null; continue; }
        var cADB = cosLaw(AD, BD, AB); AC2 = Fr.add(F(AD * AD + DC * DC), Fr.mul(F(2 * AD * DC), cADB));  /* cos∠ADC = −cos∠ADB */
      } while ((!AC2 || AC2.d !== 1 || Math.round(Math.sqrt(AC2.n)) ** 2 !== AC2.n) && tries < 400);
      return { q: ABC + ' 中，$D$ 在 $\\overline{BC}$ 上，' + T(ov('AB') + '=' + AB) + '、' + T(ov('BD') + '=' + BD) + '、' + T(ov('DC') + '=' + DC) + '、' + T(ov('AD') + '=' + AD) + '。求 ' + T(ov('AC')) + '。',
               a: T(ov('AC') + '=' + sqrtTex(AC2.n)),
               h: '在 $\\triangle ABD$ 用餘弦定理求 $\\cos\\angle ADB$；$\\angle ADC$ 是它的補角 ⟹ $\\cos\\angle ADC=-\\cos\\angle ADB$，再在 $\\triangle ADC$ 用一次餘弦定理。',
               p: { kind: 0, AB: AB, BD: BD, DC: DC, AD: AD, ans: { AC2: fr2(AC2) } } };
    }
    var b, c, m, n, AD2;
    do { c = r.int(2, 12); b = r.int(2, 12); m = r.int(1, 9); n = r.int(1, 9); tries++;
      AD2 = validTri(b, c, m + n) ? Fr.sub(F(c * c * n + b * b * m, m + n), F(m * n)) : null;   /* 斯圖爾特：AD² = (c²n + b²m)/(m+n) − mn */
    } while ((!AD2 || AD2.n <= 0 || AD2.d !== 1 || Math.round(Math.sqrt(AD2.n)) ** 2 !== AD2.n) && tries < 600);
    return { q: ABC + ' 中，$D$ 在 $\\overline{BC}$ 上，' + T(ov('AB') + '=' + c) + '、' + T(ov('AC') + '=' + b) + '、' + T(ov('BD') + '=' + m) + '、' + T(ov('DC') + '=' + n) + '。求 ' + T(ov('AD')) + '。',
             a: T(ov('AD') + '=' + sqrtTex(AD2.n)),
             h: '設 $\\overline{AD}=t$。$\\cos\\angle ADB=-\\cos\\angle ADC$：在 $\\triangle ABD$、$\\triangle ACD$ 各寫一次餘弦定理，兩式消去 $\\cos$ 得 $t$ 的一次方程（$t^2$ 的係數會湊成整理後只剩 $t^2$）。',
             p: { kind: 1, b: b, c: c, m: m, n: n, ans: { AD2: fr2(AD2) } } };
  };
  /* 2-7 SSA 兩解：求第三邊（解三角形 9 卷） */
  L2.ssaSolve = function (r) {
    var A = r.pick([30, 45, 60]), cands = [];
    for (var k = 1; k <= 20; k++) for (var a = 1; a <= 40; a++) {
      var j2 = A === 30 ? a * a - k * k : A === 60 ? a * a - 3 * k * k : a * a - 2 * k * k, j = Math.round(Math.sqrt(Math.max(j2, 0)));
      if (j2 > 0 && j * j === j2 && a < 2 * k) cands.push([k, a, j]);
    }
    var pk = r.pick(cands), kk = pk[0], aa = pk[1], jj = pk[2], c = 2 * kk;
    var surd = A === 30 ? S(kk, 3, 1) : A === 60 ? S(kk, 1, 1) : S(kk, 2, 1), rat = F(jj);   /* b = c cosA ± √(a² − c² sin²A) */
    var b1 = twoTex(rat, surd), b2 = twoTex(F(-jj), surd);
    return { q: ABC + ' 中 ' + T('\\angle A=' + A + '°') + '、' + T(ov('AB') + '=' + c) + '、' + T(ov('BC') + '=' + aa) + '。求 ' + T(ov('AC')) + '（兩解）。',
             a: T(ov('AC') + '=' + b1) + ' 或 ' + T(b2),
             h: '把 $\\overline{AC}=b$ 當未知數放進餘弦定理：$' + aa + '^2=b^2+' + c + '^2-2\\cdot' + c + '\\cdot b\\cos' + A + '°$，解二次方程得兩個正根——這就是 SSA 的兩解。',
             p: { A: A, c: c, a: aa, ans: { surd: sArr(surd), rat: fr2(rat) } } };
  };
  /* 2-8 由邊角關係判定形狀 */
  var RELS = [
    { tex: 'a\\cos A=b\\cos B', ans: 'iso_or_right', txt: '等腰（$a=b$）或直角（$\\angle C=90°$）三角形', how: '化成邊：$a\\cdot\\dfrac{b^2+c^2-a^2}{2bc}=b\\cdot\\dfrac{a^2+c^2-b^2}{2ac}$ ⟹ $(a^2-b^2)(c^2-a^2-b^2)=0$' },
    { tex: 'a\\cos B=b\\cos A', ans: 'iso_ab', txt: '等腰三角形（$a=b$）', how: '化成邊：$a^2+c^2-b^2=b^2+c^2-a^2$ ⟹ $a^2=b^2$' },
    { tex: '\\sin A=2\\sin B\\cos C', ans: 'iso_bc', txt: '等腰三角形（$b=c$）', how: '化成邊：$a=2b\\cdot\\dfrac{a^2+b^2-c^2}{2ab}$ ⟹ $a^2=a^2+b^2-c^2$ ⟹ $b=c$' },
    { tex: 'c=2a\\cos B', ans: 'iso_ab', txt: '等腰三角形（$a=b$）', how: '$c=2a\\cdot\\dfrac{a^2+c^2-b^2}{2ac}$ ⟹ $c^2=a^2+c^2-b^2$ ⟹ $a=b$' },
    { tex: '\\sin A\\cos B=\\sin B\\cos A', ans: 'iso_ab', txt: '等腰三角形（$\\angle A=\\angle B$）', how: '化成邊：$a(a^2+c^2-b^2)=b(b^2+c^2-a^2)$ 整理得 $(a-b)(a+b)^2\\cdots$，或直接看 $\\dfrac{\\sin A}{\\cos A}=\\dfrac{\\sin B}{\\cos B}$ ⟹ $\\tan A=\\tan B$' },
    { tex: 'b\\cos B=c\\cos C', ans: 'iso_or_right_bc', txt: '等腰（$b=c$）或直角（$\\angle A=90°$）三角形', how: '與 $a\\cos A=b\\cos B$ 同型：$(b^2-c^2)(a^2-b^2-c^2)=0$' },
    { tex: '\\sin^2A=\\sin^2B+\\sin^2C', ans: 'right_A', txt: '直角三角形（$\\angle A=90°$）', how: '正弦定理 ⟹ $a^2=b^2+c^2$' },
    { tex: 'a^2\\tan B=b^2\\tan A', ans: 'iso_or_right', txt: '等腰（$a=b$）或直角（$\\angle C=90°$）三角形', how: '$\\dfrac{a^2\\sin B}{\\cos B}=\\dfrac{b^2\\sin A}{\\cos A}$，用 $a=2R\\sin A$ 換掉 $\\sin$ ⟹ $a\\cos A=b\\cos B$' }
  ];
  L2.shapeJudge = function (r) {
    var i1 = r.int(0, RELS.length - 1), i2; do { i2 = r.int(0, RELS.length - 1); } while (i2 === i1 || RELS[i2].ans === RELS[i1].ans);
    return { q: ABC + ' 中 $a,b,c$ 分別為 $\\angle A,\\angle B,\\angle C$ 的對邊。(1) 若 ' + T(RELS[i1].tex) + '，判斷形狀。(2) 若 ' + T(RELS[i2].tex) + '，判斷形狀。',
             a: '(1) ' + RELS[i1].txt + '　(2) ' + RELS[i2].txt,
             h: '一律「化成邊」：$\\sin A\\to\\dfrac{a}{2R}$、$\\cos A\\to\\dfrac{b^2+c^2-a^2}{2bc}$，整理成因式相乘。(1) ' + RELS[i1].how + '。(2) ' + RELS[i2].how + '。',
             p: { rel: [i1, i2], ans: [RELS[i1].ans, RELS[i2].ans] } };
  };
  /* 2-9 三邊全知：面積、r、R、最長邊上的高（海龍 10 卷、外接圓 13 卷） */
  L2.heronFull = function (r) {
    var t = niceTri(r, 10), a = t[0], b = t[1], c = t[2], K = t[3], m = Math.max(a, b, c);
    var rin = sDiv(K, S(a + b + c, 1, 2)), R = sDiv(S(a * b * c, 1, 4), K), hmax = sDiv(K, S(m, 1, 2));
    return { q: ABC + ' 三邊長為 ' + T(a + ',\\ ' + b + ',\\ ' + c) + '。求 (1) 面積　(2) 內切圓半徑　(3) 外接圓半徑　(4) 最長邊上的高。',
             a: '(1) ' + T(sTex(K)) + '　(2) ' + T(sTex(rin)) + '　(3) ' + T(sTex(R)) + '　(4) ' + T(sTex(hmax)),
             h: '海龍先算面積，其餘三個都從面積出發：$r=\\dfrac Ks$、$R=\\dfrac{abc}{4K}$、$h=\\dfrac{2K}{\\text{邊}}$。',
             p: { a: a, b: b, c: c, ans: { K: sArr(K), r: sArr(rin), R: sArr(R), h: sArr(hmax) } } };
  };
  /* 2-10 海龍的經典情境：三高／sin 比＋內切圓半徑（例題 27 型） */
  L2.heightsHeron = function (r) {
    var kind = r.int(0, 1), p, q, w, K0, tries = 0;
    do { p = r.int(2, 8); q = r.int(2, 8); w = r.int(2, 8); tries++; K0 = validTri(p, q, w) ? sqrtF(heron2(p, q, w)) : null; } while ((!K0 || gcd(gcd(p, q), w) !== 1 || (p === q && q === w) || K0.r > 15) && tries < 400);
    var s0 = F(p + q + w, 2), K02 = heron2(p, q, w);
    if (kind === 0) {
      var lcm = p * q / gcd(p, q); lcm = lcm * w / gcd(lcm, w); var L = r.pick([1, 2, 3]) * lcm, srt = [p, q, w].slice().sort().join();
      if (srt === '4,5,6' && L === 60) L = 120; if (srt === '2,3,4' && L === 12) L = 24;   /* 避開例題 27(2) 與類似題 27 的數字 */
      var ha = L / p, hb = L / q, hc = L / w;
      var K = sDiv(S(p * ha * p * ha, 1, 4), K0), rin = F(p * ha, p + q + w), R = Fr.div(F(p * q * w * p * ha, 8), K02);
      return { q: ABC + ' 中三邊上的高分別為 ' + T('h_a=' + ha) + '、' + T('h_b=' + hb) + '、' + T('h_c=' + hc) + '。求 (1) ' + T('a:b:c') + '　(2) 面積　(3) 內切圓半徑　(4) 外接圓半徑。',
               a: '(1) ' + T(p + ':' + q + ':' + w) + '　(2) ' + T(sTex(K)) + '　(3) ' + T(Fr.tex(rin)) + '　(4) ' + T(Fr.tex(R)),
               h: '邊與高成反比 ⟹ $a:b:c=\\dfrac1{' + ha + '}:\\dfrac1{' + hb + '}:\\dfrac1{' + hc + '}$；設 $a=' + p + 'k$，海龍得 $K=(\\ldots)k^2$，另一方面 $K=\\dfrac12(' + p + 'k)(' + ha + ')$，兩式相等解 $k$；再 $r=\\dfrac Ks$、$R=\\dfrac{abc}{4K}$。',
               p: { kind: 0, ha: ha, hb: hb, hc: hc, ans: { ratio: [p, q, w], K: sArr(K), r: fr2(rin), R: fr2(R) } } };
    }
    var rr = r.pick([1, 2, 3, 4, 6]), Rr = Fr.div(Fr.mul(F(p * q * w * rr), s0), Fr.mul(F(4), K02)), Kk = sDiv(sFromF(Fr.mul(F(rr * rr), Fr.mul(s0, s0))), K0);
    return { q: ABC + ' 中 ' + T('\\sin A:\\sin B:\\sin C=' + p + ':' + q + ':' + w) + '，且內切圓半徑為 ' + T(String(rr)) + '。求 (1) 面積　(2) 外接圓半徑。',
             a: '(1) ' + T(sTex(Kk)) + '　(2) ' + T('R=' + Fr.tex(Rr)),
             h: '設三邊 $' + p + 'k,' + q + 'k,' + w + 'k$，海龍得 $K=(\\ldots)k^2$；$r=\\dfrac Ks$ 是 $k$ 的一次式，由 $r=' + rr + '$ 解出 $k$，再 $R=\\dfrac{abc}{4K}$。',
             p: { kind: 1, p: p, q: q, w: w, r: rr, ans: { K: sArr(Kk), R: fr2(Rr) } } };
  };
  /* 2-11 圓內接四邊形：cos、對角線、面積、外接圓半徑（圓內接四邊形 9 卷） */
  L2.cyclicQuadFull = function (r) {
    var Q, tries = 0; do { Q = cyclic(r); tries++; } while ((Q.AC2.d !== 1 || Math.round(Math.sqrt(Q.AC2.n)) ** 2 !== Q.AC2.n || Q.sB.r > 15) && tries < 400);
    var AC = sqrtF(Q.AC2), R = sDiv(sDiv(AC, S(2, 1, 1)), Q.sB);
    return { q: '圓內接四邊形 $ABCD$ 中 ' + T(ov('AB') + '=' + Q.a) + '、' + T(ov('BC') + '=' + Q.b) + '、' + T(ov('CD') + '=' + Q.c) + '、' + T(ov('DA') + '=' + Q.d) + '。求 (1) ' + T('\\cos B') + '　(2) ' + T(ov('AC')) + '　(3) 四邊形面積　(4) 外接圓半徑。',
             a: '(1) ' + T(Fr.tex(Q.cB)) + '　(2) ' + T(sTex(AC)) + '　(3) ' + T(sTex(Q.area)) + '　(4) ' + T('R=' + sTex(R)),
             h: '對角互補：兩個三角形的餘弦定理算同一條 $\\overline{AC}$ 解出 $\\cos B$；面積 $=\\dfrac12(ab+cd)\\sin B$（$\\sin D=\\sin B$）；$R=\\dfrac{\\overline{AC}}{2\\sin B}$（正弦定理用在 $\\triangle ABC$）。',
             p: { a: Q.a, b: Q.b, c: Q.c, d: Q.d, ans: { cosB: fr2(Q.cB), AC2: fr2(Q.AC2), area: sArr(Q.area), R: sArr(R) } } };
  };
  /* 2-12 角平分線：對邊、分比、平分線長（角平分線 7 卷） */
  L2.bisector = function (r) {
    var A = r.pick([60, 120]), b = r.int(2, 12), c = r.int(2, 12), a2 = b * b + c * c - 2 * b * c * (A === 60 ? 0.5 : -0.5);
    var AD = sMulF(tv(A / 2).cos, F(2 * b * c, b + c)), K = sMulF(tv(A).sin, F(b * c, 2));
    return { q: ABC + ' 中 ' + T(ov('AB') + '=' + c) + '、' + T(ov('AC') + '=' + b) + '、' + T('\\angle A=' + A + '°') + '，$\\overline{AD}$ 為 $\\angle A$ 的內角平分線，$D$ 在 $\\overline{BC}$ 上。求 (1) ' + T(ov('BC')) + '　(2) ' + T(ov('BD') + ':' + ov('DC')) + '　(3) ' + T(ov('AD')) + '　(4) ' + T('\\triangle ABD') + ' 的面積。',
             a: '(1) ' + T(sqrtTex(a2)) + '　(2) ' + T(c + ':' + b) + '　(3) ' + T(sTex(AD)) + '　(4) ' + T(sTex(sMulF(K, F(c, b + c)))),
             h: '(1) 餘弦定理。(2) 角平分線 ⟹ $\\overline{BD}:\\overline{DC}=\\overline{AB}:\\overline{AC}$。(3) 面積切兩半：$\\dfrac12bc\\sin' + A + '°=\\dfrac12\\overline{AD}\\,(b+c)\\sin' + (A / 2) + '°$。(4) 同高 ⟹ 面積比 $=$ 底邊比。',
             p: { A: A, b: b, c: c, ans: { a2: a2, ratio: [c, b], AD: sArr(AD), KABD: sArr(sMulF(K, F(c, b + c))) } } };
  };
  /* 2-13 面積條件下的最短線段（面積比 7 卷；例題 32 型） */
  L2.areaMinPQ = function (r) {
    var t = tri(r), cA = F(t[1], t[2]), b, c, k, xy, ok, tries = 0;
    do { b = r.int(4, 13); c = r.int(4, 13); k = r.pick([2, 3, 4]); xy = F(b * c, k); ok = Math.sqrt(Fr.toNum(xy)) <= Math.min(b, c) + 1e-9; tries++; } while (!ok && tries < 200);
    var PQ2 = Fr.mul(Fr.mul(F(2), xy), Fr.sub(F(1), cA)), PQ = sqrtF(PQ2);
    return { q: ABC + ' 中 ' + T(ov('AB') + '=' + c) + '、' + T(ov('AC') + '=' + b) + '、' + T('\\cos A=' + Fr.tex(cA)) + '。$P$、$Q$ 分別在 $\\overline{AB}$、$\\overline{AC}$ 上，且 ' + T('\\triangle ABC') + ' 的面積為 ' + T('\\triangle APQ') + ' 面積的 ' + T(String(k)) + ' 倍。求 ' + T(ov('PQ')) + ' 的最小值。',
             a: T(sTex(PQ)),
             h: '設 $\\overline{AP}=x,\\overline{AQ}=y$：面積條件 ⟹ $xy=\\dfrac{' + c + '\\cdot' + b + '}{' + k + '}=' + Fr.tex(xy) + '$（$\\sin A$ 消掉）；$\\overline{PQ}^2=x^2+y^2-2xy\\cos A\\ge2xy-2xy\\cos A$，等號在 $x=y=\\sqrt{xy}$，要檢查它不超過 $' + Math.min(b, c) + '$。',
             p: { b: b, c: c, cosA: fr2(cA), k: k, ans: { PQ2: fr2(PQ2) } } };
  };
  /* 2-14 三點共線的仰角測高：中點＋中線長公式（例題 35 型；仰角 11 卷） */
  L2.elevMedian = function (r) {
    var cot2 = { 30: F(3), 45: F(1), 60: F(1, 3) }, al, be, ga, v, tries = 0;
    do { al = r.pick([30, 45, 60]); be = r.pick([30, 45, 60]); ga = r.pick([30, 45, 60]); v = Fr.sub(Fr.add(Fr.mul(F(2), cot2[al]), Fr.mul(F(2), cot2[ga])), Fr.mul(F(4), cot2[be])); tries++; } while ((v.n <= 0 || (al === be && be === ga)) && tries < 100);
    var h = r.pick([10, 12, 15, 18, 20, 24, 30, 36, 42, 60]), AB2 = Fr.mul(F(h * h, 4), v), AB = sqrtF(AB2);
    return { q: '地面上三定點 $A$、$B$、$C$ 依序測得塔頂的仰角為 ' + T(al + '°') + '、' + T(be + '°') + '、' + T(ga + '°') + '。已知 $A,B,C$ 與塔底不共線，$B$ 為 $\\overline{AC}$ 的中點，塔高 ' + T(String(h)) + ' 公尺。求 ' + T(ov('AB')) + '。',
             a: T(ov('AB') + '=' + sTex(AB)) + ' 公尺',
             h: '設塔底 $O$：$\\overline{OA}=\\dfrac{h}{\\tan' + al + '°}$、$\\overline{OB}=\\dfrac{h}{\\tan' + be + '°}$、$\\overline{OC}=\\dfrac{h}{\\tan' + ga + '°}$。$\\overline{OB}$ 是 $\\triangle OAC$ 的中線 ⟹ 中線長公式 $4\\overline{OB}^2=2\\overline{OA}^2+2\\overline{OC}^2-\\overline{AC}^2$ 解出 $\\overline{AC}$，再除以 $2$。',
             p: { al: al, be: be, ga: ga, h: h, ans: { AB2: fr2(AB2) } } };
  };
  /* 2-15 方位角＋仰角測山高（91 學測 填 F 型；方位角 7 卷） */
  L2.bearingHeight = function (r) {
    var pair = r.pick([[60, 60], [30, 60], [60, 30], [45, 45], [30, 30], [90, 30], [30, 90], [45, 90], [90, 45]]), Aang = pair[0], Bang = pair[1], Cang = 180 - Aang - Bang;
    var d = r.pick([100, 200, 300, 400, 500, 600, 800, 1000]), alpha = r.pick([30, 45, 60]);
    var AC = sMulF(sDiv(tv(Bang).sin, tv(Cang).sin), F(d)), hgt = sMul(AC, tv(alpha).tan);
    var th1 = 90 - Aang, th2 = 90 - Bang;
    var dirA = th1 === 0 ? '正北' : '北 $' + th1 + '°$ 東', dirB = th2 === 0 ? '正北' : '北 $' + th2 + '°$ 西';
    return { q: '某人在 $A$ 點觀測山，山頂的仰角為 ' + T(alpha + '°') + '，山（山腳 $C$）在 $A$ 的' + dirA + '方向。他自 $A$ 向正東走 ' + T(String(d)) + ' 公尺到 $B$ 點，測得山在 $B$ 的' + dirB + '方向。求山高。',
             a: T(sTex(hgt)) + ' 公尺',
             h: '俯視圖：$\\angle CAB=' + Aang + '°$、$\\angle CBA=' + Bang + '°$（方位角換成與正東方向的夾角）⟹ $\\angle C=' + Cang + '°$，正弦定理求 $\\overline{AC}=' + sTex(AC) + '$；側視圖：山高 $=\\overline{AC}\\tan' + alpha + '°$。',
             p: { Aang: Aang, Bang: Bang, d: d, alpha: alpha, ans: { AC: sArr(AC), h: sArr(hgt) } } };
  };
  /* 2-16 給定範圍內三角方程的解數（廣義角 17 卷；中山女高 113 填 16 型） */
  L2.sinCount = function (r) {
    var kind = r.pick(['abs', 'sin', 'cos', 'ncos']), kf = r.pick([[2, 5], [3, 7], [1, 3], [2, 3], [3, 5], [4, 5], [1, 4], [3, 4], [5, 8]]);
    var M = r.pick([360, 450, 510, 540, 600, 630, 720, 750, 810, 900]), al = Math.asin(kf[0] / kf[1]) * 180 / Math.PI, sols = [], cnt = 0;
    if (kind === 'abs') sols = [al, 180 - al, 180 + al, 360 - al];
    else if (kind === 'sin') sols = [al, 180 - al]; else if (kind === 'cos') sols = [al, 360 - al]; else sols = [180 - al, 180 + al];
    for (var n = -1; n <= 4; n++) sols.forEach(function (s) { var v = s + 360 * n; if (v >= 0 && v < M) cnt++; });
    var eq = kind === 'abs' ? '|\\sin\\theta|=' + Fr.tex(F(kf[0], kf[1])) : kind === 'sin' ? '\\sin\\theta=' + Fr.tex(F(kf[0], kf[1])) : kind === 'cos' ? '\\cos\\theta=' + Fr.tex(F(kf[0], kf[1])) : '\\cos\\theta=-' + Fr.tex(F(kf[0], kf[1]));
    return { q: '在 ' + T('0°\\le\\theta<' + M + '°') + ' 的範圍內，方程式 ' + T(eq) + ' 共有幾個解？',
             a: T(String(cnt)) + ' 個',
             h: '令 $\\alpha$ 為第一象限的參考角（$' + (kind.indexOf('cos') >= 0 ? '\\cos' : '\\sin') + '\\alpha=' + Fr.tex(F(kf[0], kf[1])) + '$）。在單位圓上，' + (kind === 'abs' ? '每一圈有四個終邊（$\\alpha,180°-\\alpha,180°+\\alpha,360°-\\alpha$）' : '每一圈有兩個終邊') + '；把每個解加上 $360°$ 的倍數逐一數到 $' + M + '°$ 為止，注意範圍不是整圈。',
             p: { kind: kind, k: kf, M: M, ans: cnt } };
  };
  /* 2-17 正四角錐反推（立體測量） */
  L2.pyramidSolve = function (r) {
    var t = r.pick([[3, 4, 5], [4, 3, 5], [5, 12, 13], [12, 5, 13], [6, 8, 10], [8, 6, 10], [8, 15, 17], [15, 8, 17]]), s = t[0], h = t[1], l = t[2], e2 = h * h + 2 * s * s;
    var tanD = F(h, s), cosE = sqrtF(F(2 * s * s, e2)), vol = F(4 * s * s * h, 3), side = 4 * s * l;
    return { q: '正四角錐 $V$-$ABCD$ 的底面是邊長 ' + T(String(2 * s)) + ' 的正方形，側面與底面所夾角的正切值為 ' + T(Fr.tex(tanD)) + '。求 (1) 體高　(2) 側稜長　(3) 側稜與底面所夾角的餘弦值　(4) 側面積（四個側面的面積和）。',
             a: '(1) ' + T(String(h)) + '　(2) ' + T(sqrtTex(e2)) + '　(3) ' + T(sTex(cosE)) + '　(4) ' + T(String(side)),
             h: '側面與底面的夾角在「體高—半邊長 $' + s + '$—斜高」的直角三角形裡：$\\tan=\\dfrac{h}{' + s + '}$ 給體高；側稜 $=\\sqrt{h^2+(' + s + '\\sqrt2)^2}$；側面積 $=4\\times\\dfrac12\\times' + (2 * s) + '\\times$ 斜高。',
             p: { s: s, tan: fr2(tanD), ans: { h: h, e2: e2, cos: sArr(cosE), side: side } } };
  };

  /* ══════════════════════════════════════════════════════════ */
  var META = {
    L1: [
      ['triDef', '§1 三角比的定義'], ['specialEval', '§1 特殊角求值'], ['sinToCos', '§1 同角關係：知一求二'], ['sumProdAcute', '§1 對稱式 sin±cos 與 sincos'], ['coAngleSum', '§1 餘角關係：整串求和／求積'], ['elevOne', '§1 仰角測高：一次測量'], ['elevTwo', '§1 仰角測高：兩次測量'],
      ['coterminal', '§2 同界角與象限'], ['pointTrig', '§2 終邊上一點求三角比'], ['quadFind', '§2 象限判定與符號'], ['reduceEval', '§2 廣義角的特殊值'], ['polarConv', '§2 極坐標與直角坐標互換'], ['polarDist', '§2 極坐標下的距離與面積'], ['slopeAngle', '§2 斜角、斜率與夾角'],
      ['sineLaw', '§3 正弦定理求邊'], ['circumR', '§3 外接圓半徑'], ['cosLawSide', '§3 餘弦定理求邊（SAS）'], ['cosLawAngle', '§3 餘弦定理求角（SSS）與形狀'], ['sideRange', '§3 三角形存在條件與鈍角範圍'], ['ssaCount', '§3 SSA 有幾組解'],
      ['areaSAS', '§4 面積公式與已知面積求角'], ['heronArea', '§4 海龍公式'], ['inOutRadius', '§4 內切圓與外接圓半徑'], ['medianLen', '§4 中線長'], ['bisectorLen', '§4 角平分線'], ['cyclicQuad', '§4 圓內接四邊形'],
      ['projLen', '§5 正射影'], ['projTheorem', '§5 投影定理'], ['cuboid', '§5 長方體的立體測量'], ['pyramid', '§5 正四角錐']
    ],
    L2: [
      ['quadSumProd', '§2 廣義角的同角關係（象限定號）'], ['reduceSimplify', '§2 誘導公式化簡'], ['polarTriangle', '§2 三個極坐標點的三角形'], ['lineAngle', '§2 與已知直線夾特殊角的直線'], ['sinCount', '§2 範圍內三角方程的解數'],
      ['sineRatio', '§3 sin 比⟹邊比：形狀與面積'], ['cevianLen', '§3 D 在 BC 上：補角餘弦串連'], ['ssaSolve', '§3 SSA 兩解求第三邊'], ['shapeJudge', '§3 由邊角關係判定形狀'],
      ['heronFull', '§4 三邊全知：K、r、R、高'], ['heightsHeron', '§4 三高／sin 比＋內切圓⟹R'], ['cyclicQuadFull', '§4 圓內接四邊形全套'], ['bisector', '§4 角平分線全套'], ['areaMinPQ', '§4 面積條件下的最短線段'],
      ['elevMedian', '§5 三點仰角＋中點'], ['bearingHeight', '§5 方位角＋仰角測山高'], ['pyramidSolve', '§5 正四角錐反推']
    ]
  };

  function escMath(s) {
    return String(s).replace(/\$([^$]*)\$/g, function (m, inner) {
      /* 原始 <>（瀏覽器會當標籤）、全形頓號（KaTeX 嚴格模式拒收）、\times 後接字母（變成未定義指令）一律在這裡修 */
      return '$' + inner.replace(/</g, '\\lt ').replace(/>/g, '\\gt ').replace(/、/g, ',\\ ').replace(/\\times(?=[A-Za-z])/g, '\\times ') + '$';
    });
  }
  function wrapAll(group) {
    Object.keys(group).forEach(function (k) {
      var f = group[k];
      group[k] = function (r) { var o = f(r); o.q = escMath(o.q); o.a = escMath(o.a); o.h = escMath(o.h); return o; };
    });
  }
  wrapAll(L1); wrapAll(L2);

  return { makeRng: makeRng, L1: L1, L2: L2, META: META, _util: { gcd: gcd, F: F, Fr: Fr, S: S, sTex: sTex, sqrtTex: sqrtTex, tv: tv } };
}));
