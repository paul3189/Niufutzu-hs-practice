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

  /* ── patch_gen_10b4 新增工具與資料表（優化 #7 提示、#6 題幹、#3 排版） ── */
  /* 連乘：等於 1 的因數直接省略（避免印出 2\cdot4\cdot1） */
  function hxMul(list) { var f = [], i; for (i = 0; i < list.length; i++) if (String(list[i]) !== '1') f.push(list[i]); return f.length ? f.join('\\cdot') : '1'; }
  /* 平方：純正整數直接加 ^2，其餘（負數、根式、分數）補 \left(\right) */
  function hxSq(s) { s = String(s); return /^\d+$/.test(s) ? s + '^2' : '\\left(' + s + '\\right)^2'; }
  /* 角度 tex：負角加括號 */
  function hxA(k) { return k < 0 ? '(' + k + '°)' : k + '°'; }
  /* 終邊位置：第幾象限，或落在哪條軸上 */
  function hxPos(deg) {
    var a = ((deg % 360) + 360) % 360;
    if (a % 90 === 0) return ['終邊在 $x$ 軸正向', '終邊在 $y$ 軸正向', '終邊在 $x$ 軸負向', '終邊在 $y$ 軸負向'][a / 90];
    return '第' + ['一', '二', '三', '四'][Math.floor(a / 90)] + '象限';
  }
  /* 參考角：終邊與 x 軸的夾角 */
  function hxRef(deg) { var a = ((deg % 360) + 360) % 360, ref = a % 180; return ref > 90 ? 180 - ref : ref; }
  /* 由 (x, y) 的正負判斷象限（x、y 都不為 0） */
  function hxQuadXY(x, y) { return '第' + ['一', '二', '三', '四'][x > 0 ? (y > 0 ? 0 : 3) : (y > 0 ? 1 : 2)] + '象限'; }
  /* 「函數(角)＝精確值」 */
  function hxEq(fn, deg) { return FN[fn] + hxA(deg) + '=' + sTex(tv(deg)[fn]); }
  /* 有理數＋根式：有理數為負時把根式寫在前面（避免 -5+5\sqrt3） */
  function hxTwo(rat, surd) {
    if (surd.c === 0) return Fr.tex(rat);
    if (rat.n === 0) return sTex(surd);
    if (rat.n < 0 && surd.c > 0) return sTex(surd) + Fr.tex(rat);
    return twoTex(rat, surd);
  }
  /* #6 資料表 */
  var SPA = [[3, 4, 5], [5, 12, 13], [8, 15, 17], [7, 24, 25], [20, 21, 29], [12, 35, 37], [9, 40, 41], [28, 45, 53], [33, 56, 65], [16, 63, 65]];
  var COPAIR = [[5, 85], [10, 80], [12, 78], [15, 75], [18, 72], [20, 70], [25, 65], [30, 60], [35, 55], [40, 50]];
  /* 長方體 [AB, BC, AE, 體對角線]：AB²+BC²+AE² 為完全平方 */
  var CUBOID = [[1, 2, 2, 3], [2, 1, 2, 3], [2, 4, 4, 6], [4, 2, 4, 6], [2, 3, 6, 7], [3, 2, 6, 7], [1, 4, 8, 9], [4, 1, 8, 9], [4, 4, 7, 9], [3, 6, 6, 9],
                [6, 3, 6, 9], [2, 6, 9, 11], [6, 2, 9, 11], [6, 6, 7, 11], [4, 8, 8, 12], [8, 4, 8, 12], [3, 4, 12, 13], [4, 3, 12, 13], [2, 5, 14, 15], [5, 2, 14, 15],
                [2, 10, 11, 15], [10, 2, 11, 15], [5, 10, 10, 15], [1, 12, 12, 17], [12, 1, 12, 17], [6, 12, 12, 18], [6, 10, 15, 19], [10, 6, 15, 19], [4, 5, 20, 21], [5, 4, 20, 21],
                [6, 9, 18, 21], [9, 6, 18, 21], [6, 8, 24, 26], [8, 6, 24, 26], [3, 16, 24, 29], [16, 3, 24, 29]];
  /* 正四角錐 [半邊長 s, 體高 h, 斜高 l]：s²+h²=l²（底面邊長 2s） */
  var PYR = [[3, 4, 5], [4, 3, 5], [6, 8, 10], [8, 6, 10], [5, 12, 13], [12, 5, 13], [9, 12, 15], [12, 9, 15], [8, 15, 17], [15, 8, 17],
             [12, 16, 20], [16, 12, 20], [7, 24, 25], [24, 7, 25], [10, 24, 26], [15, 20, 25], [20, 15, 25], [9, 40, 41]];
  /* ── patch_gen_10b4 新增工具結束 ── */
  /* ═══════════════════════ L1 ═══════════════════════ */
  var L1 = {};

  /* ── 1-1 三角比的定義 ── */
  L1.triDef = function (r) {
    var t = tri(r), a = t[0], b = t[1], c = t[2], kind = r.int(0, 1), which = r.int(0, 1);
    var given = kind === 0 ? ov('BC') + '=' + a + '、' + ov('AC') + '=' + b : ov('AB') + '=' + c + '、' + ov('BC') + '=' + a;
    var mName = kind === 0 ? 'AB' : 'AC', mTex = kind === 0 ? '\\sqrt{' + a + '^2+' + b + '^2}=' + c : '\\sqrt{' + c + '^2-' + a + '^2}=' + b;
    var X = which === 0 ? 'A' : 'B', oppN = which === 0 ? 'BC' : 'AC', oppV = which === 0 ? a : b, adjN = which === 0 ? 'AC' : 'BC', adjV = which === 0 ? b : a;
    var sn = F(oppV, c), cs = F(adjV, c), tn = F(oppV, adjV);
    return { q: '直角三角形 $ABC$ 中 $\\angle C=90°$，' + T(given) + '。求 ' + T('\\sin ' + X) + '、' + T('\\cos ' + X) + '、' + T('\\tan ' + X) + '。',
             a: T('\\sin ' + X + '=' + Fr.tex(sn)) + '、' + T('\\cos ' + X + '=' + Fr.tex(cs)) + '、' + T('\\tan ' + X + '=' + Fr.tex(tn)),
             h: '先用畢氏定理補齊第三邊 ' + T(ov(mName) + '=' + mTex) + '；$\\angle ' + X + '$ 的對邊是 ' + T(ov(oppN) + '=' + oppV) + '、鄰邊是 ' + T(ov(adjN) + '=' + adjV) + '、斜邊是 ' + T(ov('AB') + '=' + c) + '，再套 $\\sin=\\dfrac{\\text{對}}{\\text{斜}}$、$\\cos=\\dfrac{\\text{鄰}}{\\text{斜}}$、$\\tan=\\dfrac{\\text{對}}{\\text{鄰}}$。',
             p: { kind: kind, which: which, a: a, b: b, c: c, ans: { sin: fr2(sn), cos: fr2(cs), tan: fr2(tn) } } };
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
    var used = [], seen = {};
    terms.forEach(function (t) {
      (t.sq ? [[t.f1, t.a1]] : [[t.f1, t.a1], [t.f2, t.a2]]).forEach(function (u) {
        var k = u[0] + u[1]; if (seen[k]) return; seen[k] = 1; used.push(T(hxEq(u[0], u[1])));
      });
    });
    return { q: '求 ' + T(tex) + ' 的值。',
             a: T(sTex(val)),
             h: '把 $30°$、$45°$、$60°$ 畫成 $1:\\sqrt3:2$ 與 $1:1:\\sqrt2$ 的直角三角形，本題用得到的值是 ' + used.join('、') + '；逐項代入相乘後再相加，同類根式才能合併。',
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
    var t = r.pick(SPA), a = t[0], b = t[1], c = t[2], kind = r.int(0, 2);
    if (r.int(0, 1)) { var tmp = a; a = b; b = tmp; }
    var sum = F(a + b, c), prod = F(a * b, c * c), diff = F(a - b, c), adiff = F(Math.abs(a - b), c);
    var sq = function (f) { return Fr.mul(f, f); };
    if (kind === 0)
      return { q: '設 $\\theta$ 為銳角且 ' + T('\\sin\\theta+\\cos\\theta=' + Fr.tex(sum)) + '。求 ' + T('\\sin\\theta\\cos\\theta') + ' 與 ' + T('|\\sin\\theta-\\cos\\theta|') + '。',
               a: T('\\sin\\theta\\cos\\theta=' + Fr.tex(prod)) + '、' + T('|\\sin\\theta-\\cos\\theta|=' + Fr.tex(adiff)),
               h: '兩邊平方：' + T('(\\sin\\theta+\\cos\\theta)^2=' + hxSq(Fr.tex(sum, true)) + '=' + Fr.tex(sq(sum))) + '，而左邊 $=1+2\\sin\\theta\\cos\\theta$，減 $1$ 再除以 $2$ 就是積；再用 $(\\sin\\theta-\\cos\\theta)^2=1-2\\sin\\theta\\cos\\theta$ 開根號。',
               p: { kind: 0, sum: fr2(sum), ans: { prod: fr2(prod), diff: fr2(adiff) } } };
    if (kind === 1)
      return { q: '設 $\\theta$ 為銳角且 ' + T('\\sin\\theta-\\cos\\theta=' + Fr.tex(diff)) + '。求 ' + T('\\sin\\theta\\cos\\theta') + ' 與 ' + T('\\sin\\theta+\\cos\\theta') + '。',
               a: T('\\sin\\theta\\cos\\theta=' + Fr.tex(prod)) + '、' + T('\\sin\\theta+\\cos\\theta=' + Fr.tex(sum)),
               h: '兩邊平方：' + T('(\\sin\\theta-\\cos\\theta)^2=' + hxSq(Fr.tex(diff, true)) + '=' + Fr.tex(sq(diff))) + '，而左邊 $=1-2\\sin\\theta\\cos\\theta$，移項得積；銳角時 $\\sin\\theta$、$\\cos\\theta$ 都是正的，所以 $\\sin\\theta+\\cos\\theta$ 取正根。',
               p: { kind: 1, diff: fr2(diff), ans: { prod: fr2(prod), sum: fr2(sum) } } };
    return { q: '設 $\\theta$ 為銳角且 ' + T('\\sin\\theta\\cos\\theta=' + Fr.tex(prod)) + '。求 ' + T('\\sin\\theta+\\cos\\theta') + ' 與 ' + T('|\\sin\\theta-\\cos\\theta|') + '。',
             a: T('\\sin\\theta+\\cos\\theta=' + Fr.tex(sum)) + '、' + T('|\\sin\\theta-\\cos\\theta|=' + Fr.tex(adiff)),
             h: '把積代進兩個恆等式：' + T('(\\sin\\theta+\\cos\\theta)^2=1+2\\times' + Fr.tex(prod, true) + '=' + Fr.tex(Fr.add(F(1), Fr.mul(F(2), prod)))) + '、' + T('(\\sin\\theta-\\cos\\theta)^2=1-2\\times' + Fr.tex(prod, true) + '=' + Fr.tex(Fr.sub(F(1), Fr.mul(F(2), prod)))) + '，再開根號（銳角 ⟹ 和取正根）。',
             p: { kind: 2, prod: fr2(prod), ans: { sum: fr2(sum), diff: fr2(adiff) } } };
  };
  /* ── 1-1 餘角關係：整串求和／求積 ── */
  L1.coAngleSum = function (r) {
    var kind = r.int(0, 4);
    if (kind === 2) {
      var dd = r.pick([1, 3, 5, 9, 15]), mm = 90 / dd - 1;
      return { q: '求 ' + T('\\tan' + dd + '°\\cdot\\tan' + (2 * dd) + '°\\cdot\\tan' + (3 * dd) + '°\\cdots\\tan' + (mm * dd) + '°') + ' 的值。',
               a: T('1'),
               h: '$\\tan\\theta\\cdot\\tan(90°-\\theta)=1$：頭尾配對 ' + T('\\tan' + dd + '°\\cdot\\tan' + (90 - dd) + '°=1') + '、' + T('\\tan' + (2 * dd) + '°\\cdot\\tan' + (90 - 2 * dd) + '°=1') + '…；本題共 $' + mm + '$ 項（奇數項），中間落單的是 $\\tan45°=1$，所以乘積是 $1$。',
               p: { kind: 2, d: dd, ans: 1 } };
    }
    if (kind >= 3) {
      var n = r.int(2, 3), ps = r.shuffle(COPAIR).slice(0, n), items = [], pairTex = [], pinfo = [];
      ps.forEach(function (pr) {
        var fn = kind === 4 ? 'tan' : r.pick(['sin', 'cos']);
        items.push({ fn: fn, a: pr[0] }); items.push({ fn: fn, a: pr[1] }); pinfo.push({ a: pr[0], fn: fn });
        pairTex.push(T(kind === 4 ? FN[fn] + pr[0] + '°\\cdot' + FN[fn] + pr[1] + '°=1' : FN[fn] + '^2' + pr[0] + '°+' + FN[fn] + '^2' + pr[1] + '°=1'));
      });
      items = r.shuffle(items);
      var tex2 = items.map(function (u, i) { return (i === 0 ? '' : (kind === 4 ? '\\cdot' : '+')) + FN[u.fn] + (kind === 4 ? '' : '^2') + u.a + '°'; }).join('');
      return { q: '求 ' + T(tex2) + ' 的值。',
               a: T(kind === 4 ? '1' : String(n)),
               h: (kind === 4 ? '$\\tan\\theta\\cdot\\tan(90°-\\theta)=1$' : '$\\sin^2\\theta+\\sin^2(90°-\\theta)=\\sin^2\\theta+\\cos^2\\theta=1$（換成 $\\cos$ 也一樣）') + '：把和為 $90°$ 的兩項配成一對：' + pairTex.join('、') + '，本題共 $' + n + '$ 對' + (kind === 4 ? '，乘積是 $1$。' : '，相加得 $' + n + '$。'),
               p: { kind: kind, pairs: pinfo, n: n, ans: kind === 4 ? 1 : n } };
    }
    var d = r.pick([1, 2, 3, 5, 6, 9, 10, 15]), m = 90 / d - 1, fn2 = kind === 0 ? 'sin' : 'cos';
    var tex = FN[fn2] + '^2' + d + '°+' + FN[fn2] + '^2' + (2 * d) + '°+' + FN[fn2] + '^2' + (3 * d) + '°+\\cdots+' + FN[fn2] + '^2' + (m * d) + '°';
    return { q: '求 ' + T(tex) + ' 的值（角度從 $' + d + '°$ 到 $' + (m * d) + '°$，每次加 $' + d + '°$，共 $' + m + '$ 項）。',
             a: T(Fr.tex(F(m, 2))),
             h: '$' + FN[fn2] + '^2\\theta+' + FN[fn2] + '^2(90°-\\theta)=1$：頭尾配對 ' + T(FN[fn2] + '^2' + d + '°+' + FN[fn2] + '^2' + (90 - d) + '°=1') + '、' + T(FN[fn2] + '^2' + (2 * d) + '°+' + FN[fn2] + '^2' + (90 - 2 * d) + '°=1') + '…；本題共 $' + m + '$ 項' + (m % 2 ? '（奇數項，中間 $' + FN[fn2] + '^245°$ 貢獻 $\\dfrac12$）' : '（偶數項，剛好配成 $' + (m / 2) + '$ 對）') + '，答案就是「項數 $\\div2$」。',
             p: { kind: kind, d: d, fn: fn2, ans: fr2(F(m, 2)) } };
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
    var kind = r.int(0, 2), w = r.pick([10, 12, 15, 20, 24, 30, 36, 40, 50, 60, 100]), rat, surd, th1, th2, pair;
    if (kind === 2) {
      /* 塔的兩側：h = w/(cotθ1+cotθ2) */
      pair = r.pick([[30, 30], [45, 45], [60, 60], [30, 45], [30, 60], [45, 60]]); th1 = pair[0]; th2 = pair[1];
      if (th1 === 30 && th2 === 30) { rat = F(0); surd = S(w, 3, 6); }
      else if (th1 === 45 && th2 === 45) { rat = F(w, 2); surd = S(0, 1, 1); }
      else if (th1 === 60 && th2 === 60) { rat = F(0); surd = S(w, 3, 2); }
      else if (th1 === 30 && th2 === 45) { rat = F(-w, 2); surd = S(w, 3, 2); }
      else if (th1 === 30 && th2 === 60) { rat = F(0); surd = S(w, 3, 4); }
      else { rat = F(3 * w, 2); surd = S(-w, 3, 2); }
      return { q: '塔的兩側地面上有甲、乙兩點，塔腳與甲、乙三點共線，甲、乙相距 ' + T(String(w)) + ' 公尺；在甲、乙分別測得塔頂的仰角為 ' + T(th1 + '°') + ' 與 ' + T(th2 + '°') + '。求塔高。',
               a: T(hxTwo(rat, surd)) + ' 公尺',
               h: '設塔高 $h$：甲到塔腳 $=\\dfrac{h}{\\tan' + th1 + '°}$、乙到塔腳 $=\\dfrac{h}{\\tan' + th2 + '°}$；甲、乙在塔的兩側 ⟹ 兩段相加等於 $' + w + '$，解 $h$（分母有根號要有理化）。',
               p: { kind: 2, th1: th1, th2: th2, w: w, ans: { rat: fr2(rat), surd: sArr(surd) } } };
    }
    /* 同側：h = w/(cotθ1−cotθ2)，θ1<θ2 */
    pair = r.pick([[30, 45], [30, 60], [45, 60]]); th1 = pair[0]; th2 = pair[1];
    if (th1 === 30 && th2 === 45) { rat = F(w, 2); surd = S(w, 3, 2); }
    else if (th1 === 30 && th2 === 60) { rat = F(0); surd = S(w, 3, 2); }
    else { rat = F(3 * w, 2); surd = S(w, 3, 2); }
    if (kind === 0)
      return { q: '在地面上甲點測得山頂的仰角為 ' + T(th1 + '°') + '，朝山的方向前進 ' + T(String(w)) + ' 公尺到乙點，測得仰角為 ' + T(th2 + '°') + '（山腳、甲、乙共線）。求山高。',
               a: T(hxTwo(rat, surd)) + ' 公尺',
               h: '設山高 $h$：甲到山腳 $=\\dfrac{h}{\\tan' + th1 + '°}$、乙到山腳 $=\\dfrac{h}{\\tan' + th2 + '°}$；前進了 $' + w + '$ ⟹ 兩段相差 $' + w + '$，解 $h$（分母有根號要有理化）。',
               p: { kind: 0, th1: th1, th2: th2, w: w, ans: { rat: fr2(rat), surd: sArr(surd) } } };
    return { q: '在地面上乙點測得塔頂的仰角為 ' + T(th2 + '°') + '，沿背離塔的方向後退 ' + T(String(w)) + ' 公尺到甲點，測得仰角變為 ' + T(th1 + '°') + '（塔腳、甲、乙共線）。求塔高。',
             a: T(hxTwo(rat, surd)) + ' 公尺',
             h: '設塔高 $h$：乙到塔腳 $=\\dfrac{h}{\\tan' + th2 + '°}$、甲到塔腳 $=\\dfrac{h}{\\tan' + th1 + '°}$；後退了 $' + w + '$ ⟹ 甲比乙遠 $' + w + '$，解 $h$（分母有根號要有理化）。',
             p: { kind: 1, th1: th1, th2: th2, w: w, ans: { rat: fr2(rat), surd: sArr(surd) } } };
  };

  /* ── 2-1 同界角與象限 ── */
  L1.coterminal = function (r) {
    var th; do { th = r.int(-1500, 1500); } while (th % 90 === 0);
    var pos = ((th % 360) + 360) % 360, neg = pos - 360, quad = Math.floor(pos / 90) + 1, kk = (pos - th) / 360;
    var step = kk === 0 ? '' : (kk > 0 ? th + '+360' + (kk === 1 ? '' : '\\times' + kk) : th + '-360' + (kk === -1 ? '' : '\\times' + (-kk)));
    return { q: '求 ' + T(th + '°') + ' 的最小正同界角與最大負同界角，並判斷它是第幾象限角。',
             a: '最小正同界角 ' + T(pos + '°') + '、最大負同界角 ' + T(neg + '°') + '，第' + ['一', '二', '三', '四'][quad - 1] + '象限角',
             h: '一直加減 $360°$ 直到落在 $0°\\sim360°$：' + (kk === 0 ? T(th + '°') + ' 本身就在這個範圍裡' : '本題是 ' + T(step + '=' + pos)) + '，這就是最小正同界角；最大負同界角 $=$ 最小正同界角 $-360°$；象限看 ' + T(pos + '°') + ' 落在 $0°\\sim90°$、$90°\\sim180°$、$180°\\sim270°$、$270°\\sim360°$ 的哪一段。',
             p: { th: th, ans: { pos: pos, neg: neg, quad: quad } } };
  };
  /* ── 2-1 終邊上一點求三角比 ── */
  L1.pointTrig = function (r) {
    var kind = r.int(0, 3), x, y, rr, sn, cs, tn;
    if (kind === 0) { var k = r.int(1, 5) * r.pick([1, 2]), sx = r.sign(), sy = r.sign(); x = sx * k; y = sy * k; sn = S(sy, 2, 2); cs = S(sx, 2, 2); tn = S(sx * sy, 1, 1); }
    else { var t = tri(r), m = r.pick([1, 1, 2]); x = r.sign() * t[0] * m; y = r.sign() * t[1] * m; rr = t[2] * m; sn = S(y, 1, rr); cs = S(x, 1, rr); tn = S(y, 1, x); }
    return { q: '標準位置角 $\\theta$ 的終邊過點 ' + T('P(' + x + ',' + y + ')') + '。求 ' + T('\\sin\\theta') + '、' + T('\\cos\\theta') + '、' + T('\\tan\\theta') + '。',
             a: T('\\sin\\theta=' + sTex(sn)) + '、' + T('\\cos\\theta=' + sTex(cs)) + '、' + T('\\tan\\theta=' + sTex(tn)),
             h: '本題的點在' + hxQuadXY(x, y) + '，先算 ' + T('r=\\sqrt{x^2+y^2}=\\sqrt{' + hxSq(String(x)) + '+' + hxSq(String(y)) + '}=' + sTex(S(1, x * x + y * y, 1))) + '（$r$ 永遠取正）；再用 $\\sin\\theta=\\dfrac yr$、$\\cos\\theta=\\dfrac xr$、$\\tan\\theta=\\dfrac yx$，正負號由 $x=' + x + '$、$y=' + y + '$ 決定。',
             p: { x: x, y: y, ans: { sin: sArr(sn), cos: sArr(cs), tan: sArr(tn) } } };
  };
  /* ── 2-1 象限判定與符號 ── */
  L1.quadFind = function (r) {
    var kind = r.int(0, 1);
    if (kind === 0) {
      var quad = r.int(1, 4), sgn = { 1: [1, 1, 1], 2: [1, -1, -1], 3: [-1, -1, 1], 4: [-1, 1, -1] }[quad];
      var pair = r.pick([[0, 1], [0, 2], [1, 2]]), names = ['\\sin\\theta', '\\cos\\theta', '\\tan\\theta'];
      var zone = [['第一、二象限', '第三、四象限'], ['第一、四象限', '第二、三象限'], ['第一、三象限', '第二、四象限']];
      var c0 = names[pair[0]] + (sgn[pair[0]] > 0 ? '>0' : '<0'), c1 = names[pair[1]] + (sgn[pair[1]] > 0 ? '>0' : '<0');
      var cond = c0 + '\\ \\text{且}\\ ' + c1;
      return { q: '若 ' + T(cond) + '，判斷 $\\theta$ 是第幾象限角。',
               a: '第' + ['一', '二', '三', '四'][quad - 1] + '象限角',
               h: '口訣「一全正、二正弦、三正切、四餘弦」：' + T(c0) + ' ⟹ 終邊落在' + zone[pair[0]][sgn[pair[0]] > 0 ? 0 : 1] + '；' + T(c1) + ' ⟹ 落在' + zone[pair[1]][sgn[pair[1]] > 0 ? 0 : 1] + '；兩者的交集只剩一個象限。',
               p: { kind: 0, pair: pair, signs: [sgn[pair[0]], sgn[pair[1]]], ans: quad } };
    }
    var t = tri(r), a = t[0], b = t[1], c = t[2], q2 = r.int(2, 4), sg = { 2: [1, -1], 3: [-1, -1], 4: [-1, 1] }[q2];
    var sn = F(sg[0] * a, c), cs = F(sg[1] * b, c), tn = F(sg[0] * sg[1] * a, b), which = r.int(0, 2);
    var given = which === 0 ? '\\sin\\theta=' + Fr.tex(sn) : which === 1 ? '\\cos\\theta=' + Fr.tex(cs) : '\\tan\\theta=' + Fr.tex(tn);
    var ask = which === 0 ? T('\\cos\\theta') + ' 與 ' + T('\\tan\\theta') : which === 1 ? T('\\sin\\theta') + ' 與 ' + T('\\tan\\theta') : T('\\sin\\theta') + ' 與 ' + T('\\cos\\theta');
    var ans = which === 0 ? T('\\cos\\theta=' + Fr.tex(cs)) + '、' + T('\\tan\\theta=' + Fr.tex(tn)) : which === 1 ? T('\\sin\\theta=' + Fr.tex(sn)) + '、' + T('\\tan\\theta=' + Fr.tex(tn)) : T('\\sin\\theta=' + Fr.tex(sn)) + '、' + T('\\cos\\theta=' + Fr.tex(cs)),
        qn = ['', '', '二', '三', '四'][q2];
    return { q: '已知 $\\theta$ 為第' + qn + '象限角，且 ' + T(given) + '。求 ' + ask + '。',
             a: ans,
             h: '取終邊上一點：先不管正負，用 ' + T(a + ',' + b + ',' + c) + ' 這組畢氏數（$r=' + c + '$ 永遠為正）；第' + qn + '象限 ⟹ ' + T('x=' + (sg[1] * b)) + '、' + T('y=' + (sg[0] * a)) + '，三個比值就全出來了。',
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
    var used = [], seen = {};
    terms.forEach(function (t) {
      [[t.f1, t.a1], [t.f2, t.a2]].forEach(function (u) {
        var k = u[0] + '_' + u[1]; if (seen[k]) return; seen[k] = 1;
        var co = ((u[1] % 360) + 360) % 360, vv = tv(u[1])[u[0]];
        used.push(T(FN[u[0]] + hxA(u[1])) + '：同界角 ' + T(co + '°') + '，' + hxPos(u[1]) + '，參考角 ' + T(hxRef(u[1]) + '°') + (vv.c === 0 ? '，值為 $0$' : '，值取' + (vv.c > 0 ? '正' : '負')));
      });
    });
    return { q: '求 ' + T(tex) + ' 的值。',
             a: T(sTex(val)),
             h: '每個角先化到 $0°\\sim360°$（同界角），由終邊所在象限決定正負，再用參考角查特殊值：' + used.join('；') + '。',
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
               h: '$x=r\\cos\\theta=' + rr + '\\cos' + th + '°$、$y=r\\sin\\theta=' + rr + '\\sin' + th + '°$；$' + th + '°$ 在' + hxPos(th) + '（參考角 $' + hxRef(th) + '°$）⟹ $\\cos' + th + '°$ 為' + (tv(th).cos.c > 0 ? '正' : '負') + '、$\\sin' + th + '°$ 為' + (tv(th).sin.c > 0 ? '正' : '負') + '。',
               p: { kind: 0, r: rr, th: th, ans: { x: sArr(x), y: sArr(y) } } };
    }
    var m = r.int(1, 5), pat = r.pick([[[1, 1, 1], [1, 3, 1], 60], [[1, 3, 1], [1, 1, 1], 30], [[1, 1, 1], [1, 1, 1], 45], [[0, 1, 1], [1, 1, 1], 90], [[1, 1, 1], [0, 1, 1], 0]]);
    var q = r.int(1, 4), sx = (q === 1 || q === 4) ? 1 : -1, sy = (q === 1 || q === 2) ? 1 : -1;
    var ref = pat[2], ang = q === 1 ? ref : q === 2 ? 180 - ref : q === 3 ? 180 + ref : 360 - ref;
    if (ref === 90) { sx = 1; ang = sy > 0 ? 90 : 270; } if (ref === 0) { sy = 1; ang = sx > 0 ? 0 : 180; }
    var X = S(sx * pat[0][0] * m, pat[0][1], 1), Y = S(sy * pat[1][0] * m, pat[1][1], 1), rad = ref === 45 ? m * Math.SQRT2 : 2 * m;
    var rTex = ref === 45 ? sTex(S(m, 2, 1)) : String(ref === 90 || ref === 0 ? m : 2 * m), rS = ref === 45 ? S(m, 2, 1) : S(ref === 90 || ref === 0 ? m : 2 * m, 1, 1);
    var axis = ref === 90 || ref === 0;
    var rLine = axis ? '$r$ 就是點到原點的距離 $=' + rTex + '$' : '$r=\\sqrt{x^2+y^2}=\\sqrt{' + hxSq(sTex(X)) + '+' + hxSq(sTex(Y)) + '}=' + rTex + '$（$r$ 取正）';
    var where = axis ? '終邊落在' + (ref === 90 ? '$y$' : '$x$') + ' 軸上' : '終邊在' + hxQuadXY(X.c, Y.c) + '，參考角是 $' + ref + '°$（$\\tan' + ref + '°=' + sTex(tv(ref).tan) + '$）';
    return { q: '將直角坐標 ' + T('(' + sTex(X) + ',\\ ' + sTex(Y) + ')') + ' 化為極坐標 ' + T('[r,\\theta]') + '（' + T('r>0') + '，' + T('0°\\le\\theta<360°') + '）。',
             a: T('[' + rTex + ',\\ ' + ang + '°]'),
             h: rLine + '；由 $x=' + sTex(X) + '$、$y=' + sTex(Y) + '$ 的正負判斷' + where + '，再把參考角換成 $0°\\le\\theta<360°$ 的極角。',
             p: { kind: 1, x: sArr(X), y: sArr(Y), ans: { r: sArr(rS), th: ang } } };
  };
  /* ── 2-2 極坐標下的距離與面積 ── */
  L1.polarDist = function (r) {
    var r1 = r.int(2, 9), r2 = r.int(2, 9), gap = r.pick([60, 90, 120]), th1 = r.int(0, 11) * 15, th2 = (th1 + gap) % 360;
    if (r.int(0, 1)) { var tmp = th1; th1 = th2; th2 = tmp; }
    var d2 = r1 * r1 + r2 * r2 - 2 * r1 * r2 * (gap === 60 ? 0.5 : gap === 90 ? 0 : -0.5), area = sMulF(tv(gap).sin, F(r1 * r2, 2));
    return { q: '設 $O$ 為極點，' + T('A[' + r1 + ',' + th1 + '°]') + '、' + T('B[' + r2 + ',' + th2 + '°]') + '。求 ' + T('\\angle AOB') + '、' + T(ov('AB')) + ' 與 ' + T('\\triangle OAB') + ' 的面積。',
             a: T('\\angle AOB=' + gap + '°') + '、' + T(ov('AB') + '=' + sqrtTex(d2)) + '、面積 ' + T('=' + sTex(area)),
             h: '夾角 $=$ 兩極角之差：$|' + th1 + '-' + th2 + '|$（超過 $180°$ 就用 $360°$ 減）$=' + gap + '°$；再用餘弦定理 ' + T(ov('AB') + '^2=' + r1 + '^2+' + r2 + '^2-' + hxMul([2, r1, r2]) + '\\cos' + gap + '°') + ' 與面積公式 ' + T('\\dfrac12\\cdot' + hxMul([r1, r2]) + '\\sin' + gap + '°') + '。極坐標直接給了「兩邊夾角」。',
             p: { r1: r1, th1: th1, r2: r2, th2: th2, ans: { gap: gap, d2: d2, area: sArr(area) } } };
  };
  /* ── 2-3 斜角與斜率／兩直線夾角 ── */
  var SLOPES = [{ m: S(1, 3, 3), ang: 30, tex: '\\dfrac{\\sqrt3}{3}' }, { m: S(1, 1, 1), ang: 45, tex: '1' }, { m: S(1, 3, 1), ang: 60, tex: '\\sqrt3' }, { m: S(-1, 3, 1), ang: -60, tex: '-\\sqrt3' }, { m: S(-1, 1, 1), ang: -45, tex: '-1' }, { m: S(-1, 3, 3), ang: -30, tex: '-\\dfrac{\\sqrt3}{3}' }, { m: S(0, 1, 1), ang: 0, tex: '0' }];
  function angT(a) { return a < 0 ? '(' + a + '°)' : a + '°'; }   /* \tan(-45°) 要加括號 */
  function angNorm(a) { a = ((a % 180) + 180) % 180; return a > 90 ? a - 180 : a; }   /* 斜角範圍 -90°<α≤90° */
  function lineOfSlope(sl, r) {   /* 回傳 ax+by+c=0 的 tex（整數係數） */
    var c = r.nz(-9, 9);
    if (sl.ang === 0) return { tex: 'y=' + c, m: sl };
    if (sl.ang === 45 || sl.ang === -45) { var s = sl.ang === 45 ? '-' : '+'; return { tex: 'x' + s + 'y' + (c > 0 ? '+' : '') + c + '=0', m: sl }; }
    if (sl.ang === 60 || sl.ang === -60) { var s2 = sl.ang === 60 ? '-' : '+'; return { tex: '\\sqrt3x' + s2 + 'y' + (c > 0 ? '+' : '') + c + '=0', m: sl }; }
    var s3 = sl.ang === 30 ? '-' : '+'; return { tex: 'x' + s3 + '\\sqrt3y' + (c > 0 ? '+' : '') + c + '=0', m: sl };
  }
  L1.slopeAngle = function (r) {
    var kind = r.int(0, 2);
    if (kind === 0) {
      var sl = r.pick(SLOPES), L = lineOfSlope(sl, r);
      return { q: '求直線 ' + T(L.tex) + ' 的斜角。',
               a: T(sl.ang + '°'),
               h: '先把直線整理成 $y=mx+k$ 讀出斜率 $m=' + sl.tex + '$，斜角 $\\alpha$ 滿足 $\\tan\\alpha=m$ 且 $-90°\\lt\\alpha\\le90°$（$m<0$ 時斜角是負的）。',
               p: { kind: 0, ang: sl.ang, ans: sl.ang } };
    }
    if (kind === 1) {
      var s1 = r.pick(SLOPES), s2; do { s2 = r.pick(SLOPES); } while (s2.ang === s1.ang);
      var L1_ = lineOfSlope(s1, r), L2_ = lineOfSlope(s2, r), dif = Math.abs(s1.ang - s2.ang), acute = dif > 90 ? 180 - dif : dif;
      return { q: '求 ' + T('L_1:' + L1_.tex) + ' 與 ' + T('L_2:' + L2_.tex) + ' 的銳夾角（或直角）。',
               a: T(acute + '°'),
               h: '兩條線的斜角分別是 $' + s1.ang + '°$ 與 $' + s2.ang + '°$，兩個斜角相減取絕對值就是夾角，差超過 $90°$ 就用 $180°$ 減。',
               p: { kind: 1, a1: s1.ang, a2: s2.ang, ans: acute } };
    }
    var sl3 = r.pick(SLOPES.slice(0, 6)), px = r.nz(-6, 6), py = r.nz(-6, 6), Ptex = '(' + px + ',' + py + ')';
    /* 過 P 斜率 m 的直線：m 為 ±1 → x∓y+c=0；±√3 → √3x∓y+c=0；±√3/3 → x∓√3y+c=0 */
    var tex, c1;
    if (sl3.ang === 45 || sl3.ang === -45) { c1 = sl3.ang === 45 ? py - px : -(px + py); tex = 'x' + (sl3.ang === 45 ? '-' : '+') + 'y' + (c1 === 0 ? '' : (c1 > 0 ? '+' : '') + c1) + '=0'; c1 = { rat: c1, surd: 0 }; }
    else if (sl3.ang === 60 || sl3.ang === -60) { var sgn = sl3.ang === 60 ? -1 : 1, rt = -sgn * py; tex = '\\sqrt3x' + (sgn < 0 ? '-' : '+') + 'y' + (rt === 0 ? '' : (rt > 0 ? '+' : '') + rt) + ((-px) === 0 ? '' : ((-px) > 0 ? '+' : '-') + (Math.abs(px) === 1 ? '' : Math.abs(px)) + '\\sqrt3') + '=0'; c1 = { rat: rt, surd: -px }; }
    else { var sg = sl3.ang === 30 ? -1 : 1, sd = -sg * py; tex = 'x' + (sg < 0 ? '-' : '+') + '\\sqrt3y' + ((-px) === 0 ? '' : ((-px) > 0 ? '+' : '') + (-px)) + (sd === 0 ? '' : (sd > 0 ? '+' : '-') + (Math.abs(py) === 1 ? '' : Math.abs(py)) + '\\sqrt3') + '=0'; c1 = { rat: -px, surd: sd }; }
    return { q: '直線 $L$ 過點 ' + T('P' + Ptex) + '，且斜角為 ' + T(sl3.ang + '°') + '。求 $L$ 的方程式。',
             a: T(tex),
             h: '斜率 $m=\\tan' + angT(sl3.ang) + '=' + sl3.tex + '$，點斜式 $y-(' + py + ')=m(x-(' + px + '))$ 整理成一般式。',
             p: { kind: 2, ang: sl3.ang, px: px, py: py, ans: { tex: tex } } };
  };

  /* ── 3-1 正弦定理求邊 ── */
  L1.sineLaw = function (r) {
    var A, B; do { A = r.pick([30, 45, 60, 90, 120, 135, 150]); B = r.pick([30, 45, 60]); } while (A + B >= 180);
    var C = 180 - A - B, a = r.pick([2, 4, 6, 8, 10, 12]), b = sMulF(sDiv(tv(B).sin, tv(A).sin), F(a));
    return { q: ABC + ' 中 ' + T('\\angle A=' + A + '°') + '、' + T('\\angle B=' + B + '°') + '、' + T('a=' + a) + '。求 ' + T('\\angle C') + ' 與 ' + T('b') + '。',
             a: T('\\angle C=' + C + '°') + '、' + T('b=' + sTex(b)),
             h: '內角和：' + T('\\angle C=180°-' + A + '°-' + B + '°') + '；正弦定理 $\\dfrac{a}{\\sin A}=\\dfrac{b}{\\sin B}$ ⟹ ' + T('b=\\dfrac{a\\sin B}{\\sin A}=\\dfrac{' + a + '\\sin' + B + '°}{\\sin' + A + '°}') + '，兩個角都是特殊角（$\\sin' + A + '°=' + sTex(tv(A).sin) + '$、$\\sin' + B + '°=' + sTex(tv(B).sin) + '$），值直接代。',
             p: { A: A, B: B, a: a, ans: { C: C, b: sArr(b) } } };
  };
  /* ── 3-1 外接圓半徑 ── */
  L1.circumR = function (r) {
    var kind = r.int(0, 1);
    if (kind === 0) {
      var A = r.pick([30, 45, 60, 90, 120, 135, 150]), a = r.pick([2, 3, 4, 5, 6, 8, 9, 10, 12]), R = sDiv(S(a, 1, 2), tv(A).sin);
      return { q: ABC + ' 中 ' + T('a=' + a) + '、' + T('\\angle A=' + A + '°') + '。求外接圓半徑 $R$。',
               a: T('R=' + sTex(R)),
               h: '$\\dfrac{a}{\\sin A}=2R$ ⟹ ' + T('R=\\dfrac{a}{2\\sin A}=\\dfrac{' + a + '}{2\\sin' + A + '°}') + '，其中 $\\sin' + A + '°=' + sTex(tv(A).sin) + '$（分母有根號要有理化）。',
               p: { kind: 0, a: a, A: A, ans: sArr(R) } };
    }
    var R2 = r.pick([5, 6, 8, 10, 12, 13, 15]), b = r.int(2, 2 * R2 - 1), sB = F(b, 2 * R2);
    return { q: ABC + ' 的外接圓半徑為 ' + T(String(R2)) + '，且 ' + T('b=' + b) + '。求 ' + T('\\sin B') + '，並說明 $\\angle B$ 有幾種可能。',
             a: T('\\sin B=' + Fr.tex(sB)) + '，$\\angle B$ 有兩種可能（一銳角一鈍角，互補）',
             h: '$b=2R\\sin B$ ⟹ ' + T('\\sin B=\\dfrac{b}{2R}=\\dfrac{' + b + '}{2\\times' + R2 + '}=' + Fr.tex(sB)) + '；這個值比 $1$ 小，銳角與它的補角有相同的正弦值，所以一題兩解。',
             p: { kind: 1, R: R2, b: b, ans: { sinB: fr2(sB), count: 2 } } };
  };
  /* ── 3-2 餘弦定理求邊（SAS） ── */
  L1.cosLawSide = function (r) {
    var A = r.pick([60, 90, 120]), b = r.int(2, 12), c = r.int(2, 12), a2 = b * b + c * c - 2 * b * c * (A === 60 ? 0.5 : A === 90 ? 0 : -0.5);
    return { q: ABC + ' 中 ' + T('b=' + b) + '、' + T('c=' + c) + '、' + T('\\angle A=' + A + '°') + '。求 $a$。',
             a: T('a=' + sqrtTex(a2)),
             h: '兩邊夾角求第三邊：' + T('a^2=b^2+c^2-2bc\\cos A=' + b + '^2+' + c + '^2-' + hxMul([2, b, c]) + '\\cos' + A + '°') + '，其中 ' + T('\\cos' + A + '°=' + (A === 60 ? '\\dfrac12' : A === 90 ? '0' : '-\\dfrac12')) + '，算完再開根號。',
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
               h: '兩邊夾角 ⟹ 面積 ' + T('=\\dfrac12ab\\sin C=\\dfrac12\\cdot' + hxMul([a, b]) + '\\sin' + C + '°') + '，其中 ' + T('\\sin' + C + '°=' + sTex(tv(C).sin)) + '（鈍角的正弦仍為正）。',
               p: { kind: 0, a: a, b: b, C: C, ans: sArr(K) } };
    }
    var sC = r.pick([[1, 2], [1, 1]]), K2 = F(a * b * sC[0], 2 * sC[1]), angs = sC[1] === 1 ? [90] : [30, 150];
    return { q: ABC + ' 中 ' + T('a=' + a) + '、' + T('b=' + b) + '，且面積為 ' + T(Fr.tex(K2)) + '。求 ' + T('\\angle C') + '（所有可能）。',
             a: T('\\angle C=' + angs.join('°\\ \\text{或}\\ ') + '°'),
             h: '由 ' + T('\\dfrac12\\cdot' + hxMul([a, b]) + '\\sin C=' + Fr.tex(K2)) + ' 解出 ' + T('\\sin C=' + Fr.tex(F(sC[0], sC[1]))) + '；$\\sin C<1$ 時銳角與鈍角各一解，$\\sin C=1$ 只有 $90°$。',
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
    var t = niceTri(r, 15), a = t[0], b = t[1], c = t[2], K = t[3], s = F(a + b + c, 2);
    var rin = sDiv(K, S(a + b + c, 1, 2)), R = sDiv(S(a * b * c, 1, 4), K);
    return { q: ABC + ' 三邊長為 ' + T(a + ',\\ ' + b + ',\\ ' + c) + '。求 (1) 面積　(2) 內切圓半徑 $r$　(3) 外接圓半徑 $R$。',
             a: '(1) ' + T(sTex(K)) + '　(2) ' + T('r=' + sTex(rin)) + '　(3) ' + T('R=' + sTex(R)),
             h: '面積是橋：先用海龍 ' + T('s=\\dfrac{' + a + '+' + b + '+' + c + '}{2}=' + Fr.tex(s)) + '、$K=\\sqrt{s(s-a)(s-b)(s-c)}$（$s-a=' + Fr.tex(Fr.sub(s, F(a))) + '$、$s-b=' + Fr.tex(Fr.sub(s, F(b))) + '$、$s-c=' + Fr.tex(Fr.sub(s, F(c))) + '$）；再用 $r=\\dfrac Ks$ 與 ' + T('R=\\dfrac{abc}{4K}=\\dfrac{' + (a * b * c) + '}{4K}') + '。分母有根號要有理化。',
             p: { a: a, b: b, c: c, ans: { K: sArr(K), r: sArr(rin), R: sArr(R) } } };
  };
  /* ── 4-4 中線長 ── */
  L1.medianLen = function (r) {
    var a, b, c; do { a = r.int(2, 14); b = r.int(2, 14); c = r.int(2, 14); } while (!validTri(a, b, c));
    var m = sqrtF(F(2 * b * b + 2 * c * c - a * a, 4));
    return { q: ABC + ' 中 ' + T(ov('AB') + '=' + c) + '、' + T(ov('AC') + '=' + b) + '、' + T(ov('BC') + '=' + a) + '，$M$ 為 $\\overline{BC}$ 的中點。求 ' + T(ov('AM')) + '。',
             a: T(ov('AM') + '=' + sTex(m)),
             h: '中線長公式 $\\overline{AM}^2=\\dfrac{2\\overline{AB}^2+2\\overline{AC}^2-\\overline{BC}^2}{4}$，代入本題 ' + T('=\\dfrac{2\\cdot' + c + '^2+2\\cdot' + b + '^2-' + a + '^2}{4}') + '，再開根號（先求 $\\cos B$ 再在 $\\triangle ABM$ 用餘弦定理也行）。',
             p: { a: a, b: b, c: c, ans: sArr(m) } };
  };
  /* ── 4-4 角平分線長 ── */
  L1.bisectorLen = function (r) {
    var A = r.pick([60, 90, 120]), b = r.int(2, 12), c = r.int(2, 12), half = tv(A / 2).cos, AD = sMulF(half, F(2 * b * c, b + c)), gR = gcd(b, c);
    return { q: ABC + ' 中 ' + T(ov('AB') + '=' + c) + '、' + T(ov('AC') + '=' + b) + '、' + T('\\angle A=' + A + '°') + '，$\\overline{AD}$ 為 $\\angle A$ 的內角平分線（$D$ 在 $\\overline{BC}$ 上）。求 ' + T(ov('BD') + ':' + ov('DC')) + ' 與 ' + T(ov('AD')) + '。',
             a: T(ov('BD') + ':' + ov('DC') + '=' + (c / gR) + ':' + (b / gR)) + '、' + T(ov('AD') + '=' + sTex(AD)),
             h: '角平分線把對邊分成兩鄰邊之比：' + T(ov('BD') + ':' + ov('DC') + '=' + ov('AB') + ':' + ov('AC') + '=' + c + ':' + b) + '；長度用「面積切兩半」：' + T('\\dfrac12\\cdot' + hxMul([b, c]) + '\\sin' + A + '°=\\dfrac12\\overline{AD}\\,(' + b + '+' + c + ')\\sin' + (A / 2) + '°') + '，解出 $\\overline{AD}$。',
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
             h: '對角互補 ⟹ $\\cos D=-\\cos B$。同一條 $\\overline{AC}$ 算兩次：在 $\\triangle ABC$ ' + T(ov('AC') + '^2=' + Q.a + '^2+' + Q.b + '^2-' + hxMul([2, Q.a, Q.b]) + '\\cos B') + '、在 $\\triangle ACD$ ' + T(ov('AC') + '^2=' + Q.c + '^2+' + Q.d + '^2+' + hxMul([2, Q.c, Q.d]) + '\\cos B') + '，兩式相等解出 $\\cos B$ 再代回去。',
             p: { a: Q.a, b: Q.b, c: Q.c, d: Q.d, ans: { cosB: fr2(Q.cB), AC2: fr2(Q.AC2) } } };
  };

  /* ── 5-1 正射影 ── */
  L1.projLen = function (r) {
    var kind = r.int(0, 1), L = r.pick([4, 6, 8, 10, 12, 16, 20]);
    if (kind === 0) {
      var th = r.pick([30, 45, 60, 120, 135, 150]), p = sMulF(tv(th).cos, F(th > 90 ? -L : L));
      return { q: '線段 ' + T(ov('AB') + '=' + L) + ' 與直線 $L$ 所夾的角為 ' + T(th + '°') + '。求 $\\overline{AB}$ 在 $L$ 上的正射影長。',
               a: T(sTex(p)),
               h: '正射影長 $=\\overline{AB}\\cdot|\\cos\\theta|$，本題 ' + T('=' + L + '|\\cos' + th + '°|') + (th > 90 ? '；夾角是鈍角，改用補角 $' + (180 - th) + '°$（長度永遠是正的）' : '') + '，其中 ' + T('\\cos' + th + '°=' + sTex(tv(th).cos)) + '。',
               p: { kind: 0, L: L, th: th, ans: sArr(p) } };
    }
    var th2 = r.pick([30, 45, 60]), hx = sMulF(tv(th2).cos, F(L)), vy = sMulF(tv(th2).sin, F(L));
    return { q: '一根長 ' + T(String(L)) + ' 公尺的梯子斜靠牆面，與地面夾 ' + T(th2 + '°') + ' 角。求梯腳到牆的距離與梯頂離地的高度。',
             a: '梯腳到牆 ' + T(sTex(hx)) + ' 公尺、梯頂高 ' + T(sTex(vy)) + ' 公尺',
             h: '梯子在地面上的正射影 ' + T('=L\\cos\\theta=' + L + '\\cos' + th2 + '°') + '、在牆上的正射影 ' + T('=L\\sin\\theta=' + L + '\\sin' + th2 + '°') + '，其中 $\\cos' + th2 + '°=' + sTex(tv(th2).cos) + '$、$\\sin' + th2 + '°=' + sTex(tv(th2).sin) + '$。',
             p: { kind: 1, L: L, th: th2, ans: { x: sArr(hx), y: sArr(vy) } } };
  };
  /* ── 5-2 投影定理 ── */
  L1.projTheorem = function (r) {
    var a, b, c; do { a = r.int(3, 13); b = r.int(3, 13); c = r.int(3, 13); } while (!validTri(a, b, c));
    var cB = cosLaw(a, c, b), cC = cosLaw(a, b, c);
    return { q: ABC + ' 中 ' + T('a=' + a) + '、' + T('b=' + b) + '、' + T('c=' + c) + '。求 ' + T('\\cos B') + '、' + T('\\cos C') + '，並驗證 ' + T('b\\cos C+c\\cos B=a') + '。',
             a: T('\\cos B=' + Fr.tex(cB)) + '、' + T('\\cos C=' + Fr.tex(cC)) + '；' + T('b\\cos C+c\\cos B=' + a) + ' ✓',
             h: '餘弦定理各算一次：' + T('\\cos B=\\dfrac{a^2+c^2-b^2}{2ac}=\\dfrac{' + a + '^2+' + c + '^2-' + b + '^2}{' + hxMul([2, a, c]) + '}') + '、' + T('\\cos C=\\dfrac{a^2+b^2-c^2}{2ab}=\\dfrac{' + a + '^2+' + b + '^2-' + c + '^2}{' + hxMul([2, a, b]) + '}') + '；投影定理的意思是「$\\overline{AB}$、$\\overline{AC}$ 在 $\\overline{BC}$ 上的正射影加起來剛好是 $' + a + '$」。',
             p: { a: a, b: b, c: c, ans: { cosB: fr2(cB), cosC: fr2(cC), sum: a } } };
  };
  /* ── 5-3 長方體的立體測量 ── */
  L1.cuboid = function (r) {
    var Q = r.pick(CUBOID), p = Q[0], q = Q[1], h = Q[2], D = Q[3], face = r.int(0, 1);
    var near = face === 0 ? p * p + q * q : p * p + h * h, edge = face === 0 ? h : q;
    var fname = face === 0 ? '底面 $ABCD$' : '側面 $ABFE$', projTex = face === 0 ? ov('AC') + '=\\sqrt{' + p + '^2+' + q + '^2}' : '\\sqrt{' + p + '^2+' + h + '^2}';
    var sn = F(edge, D), cs = sqrtF(F(near, D * D)), tn = sqrtF(F(edge * edge, near));
    return { q: '長方體 $ABCD$-$EFGH$ 中 ' + T(ov('AB') + '=' + p) + '、' + T(ov('BC') + '=' + q) + '、' + T(ov('AE') + '=' + h) + '（$\\overline{AE}$ 為鉛直稜）。求體對角線 ' + T(ov('AG')) + '，以及 $\\overline{AG}$ 與' + fname + ' 所夾角 $\\theta$ 的 ' + T('\\sin\\theta') + '、' + T('\\cos\\theta') + '、' + T('\\tan\\theta') + '。',
             a: T(ov('AG') + '=' + D) + '、' + T('\\sin\\theta=' + Fr.tex(sn)) + '、' + T('\\cos\\theta=' + sTex(cs)) + '、' + T('\\tan\\theta=' + sTex(tn)),
             h: '先算 $\\overline{AG}$ 在' + fname + ' 上的投影 ' + T(projTex) + '，再算 ' + T(ov('AG') + '=\\sqrt{' + p + '^2+' + q + '^2+' + h + '^2}=' + D) + '；$\\theta$ 落在一個直角三角形裡：對邊是垂直於' + fname + ' 的那條稜 ' + T(String(edge)) + '、鄰邊是投影長、斜邊是 ' + T(String(D)) + '。',
             p: { p: p, q: q, h: h, face: face, ans: { D: D, near: near, sin: fr2(sn), cos: sArr(cs), tan: sArr(tn) } } };
  };
  /* ── 5-4 正四角錐 ── */
  L1.pyramid = function (r) {
    var t = r.pick(PYR), s = t[0], h = t[1], l = t[2], e2 = h * h + 2 * s * s, kind = r.int(0, 1);
    var tanD = F(h, s), cosE = sqrtF(F(2 * s * s, e2)), vol = F(4 * s * s * h, 3), side = 4 * s * l;
    var stem = '正四角錐 $V$-$ABCD$ 的底面是邊長 ' + T(String(2 * s)) + ' 的正方形，側稜長 ' + T(ov('VA') + '=' + sqrtTex(e2)) + '。';
    var base = '兩個直角三角形：「體高、半對角線 $' + s + '\\sqrt2$、側稜 $' + sqrtTex(e2) + '$」給體高 ' + T('h=\\sqrt{' + e2 + '-2\\cdot' + s + '^2}=' + h) + '；「體高 $' + h + '$、半邊長 $' + s + '$、斜高」給斜高 ' + T('\\sqrt{' + h + '^2+' + s + '^2}=' + l) + '。';
    if (kind === 0)
      return { q: stem + '求 (1) 體高　(2) 斜高（$V$ 到底邊中點的距離）　(3) 側面與底面所夾角的正切值　(4) 側稜與底面所夾角的餘弦值。',
               a: '(1) ' + T(String(h)) + '　(2) ' + T(String(l)) + '　(3) ' + T(Fr.tex(tanD)) + '　(4) ' + T(sTex(cosE)),
               h: base + '側面與底面的夾角在第二個三角形裡（$\\tan=\\dfrac{\\text{體高}}{\\text{半邊長}}$）、側稜與底面的夾角在第一個三角形裡（$\\cos=\\dfrac{' + s + '\\sqrt2}{' + sqrtTex(e2) + '}$，分母有根號要有理化）。',
               p: { kind: 0, s: s, h: h, l: l, e2: e2, ans: { h: h, l: l, tan: fr2(tanD), cos: sArr(cosE) } } };
    return { q: stem + '求 (1) 體高　(2) 斜高（$V$ 到底邊中點的距離）　(3) 體積　(4) 側面積（四個側面的面積和）。',
             a: '(1) ' + T(String(h)) + '　(2) ' + T(String(l)) + '　(3) ' + T(Fr.tex(vol)) + '　(4) ' + T(String(side)),
             h: base + '體積 $=\\dfrac13\\times$ 底面積 $\\times$ 體高 ' + T('=\\dfrac13\\cdot' + (2 * s) + '^2\\cdot' + h) + '；側面積 $=4\\times$（一個側面的三角形面積）' + T('=4\\cdot\\dfrac12\\cdot' + (2 * s) + '\\cdot' + l) + '（底是底邊、高是斜高）。',
             p: { kind: 1, s: s, h: h, l: l, e2: e2, ans: { h: h, l: l, vol: fr2(vol), side: side } } };
  };

  /* ═══════════════════════ L2 ═══════════════════════ */
  var L2 = {};

  /* 2-1 廣義角的同角關係：象限＋和 → 積、差、tan（例題 11 型；平方關係 10 卷） */
  L2.quadSumProd = function (r) {
    var t = tri(r), a = t[0], b = t[1], c = t[2], quad = r.int(2, 4), sg = { 2: [1, -1], 3: [-1, -1], 4: [-1, 1] }[quad];
    if (r.int(0, 1)) { var tmp = a; a = b; b = tmp; }
    var sn = F(sg[0] * a, c), cs = F(sg[1] * b, c), sum = Fr.add(sn, cs), prod = Fr.mul(sn, cs), diff = Fr.sub(sn, cs), tn = Fr.div(sn, cs);
    /* 第三象限 sin、cos 同為負，只給「和」定不出誰大（兩組解）⟹ 題幹要補大小關係 */
    var q3rel = '\\sin\\theta' + (Fr.lt(cs, sn) ? '>' : '<') + '\\cos\\theta', q3 = quad === 3 ? '，又 ' + T(q3rel) : '';
    var qn = ['', '', '二', '三', '四'][quad];
    return { q: '已知 $\\theta$ 為第' + qn + '象限角，且 ' + T('\\sin\\theta+\\cos\\theta=' + Fr.tex(sum)) + q3 + '。求 (1) ' + T('\\sin\\theta\\cos\\theta') + '　(2) ' + T('\\sin\\theta-\\cos\\theta') + '　(3) ' + T('\\tan\\theta') + '。',
             a: '(1) ' + T(Fr.tex(prod)) + '　(2) ' + T(Fr.tex(diff)) + '　(3) ' + T(Fr.tex(tn)),
             h: '平方：' + T('(\\sin\\theta+\\cos\\theta)^2=' + hxSq(Fr.tex(sum, true)) + '=' + Fr.tex(Fr.mul(sum, sum))) + '，左邊 $=1+2\\sin\\theta\\cos\\theta$ ⟹ 得積；再由 $(\\sin\\theta-\\cos\\theta)^2=1-2\\sin\\theta\\cos\\theta$ 開根號後<b>用象限定號</b>（第' + qn + '象限 ' + (quad === 2 ? '$\\sin>0>\\cos$ ⟹ 差為正' : quad === 3 ? '兩者皆負，要靠題目給的 $' + q3rel + '$ ⟹ 差為' + (Fr.lt(cs, sn) ? '正' : '負') : '$\\cos>0>\\sin$ ⟹ 差為負') + '）；和 $' + Fr.tex(sum) + '$ 與差聯立解出 $\\sin\\theta$、$\\cos\\theta$ 再相除得 $\\tan\\theta$。',
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
    var NEW = { sin: '\\cos\\theta', cos: '\\sin\\theta', tan: '\\dfrac{1}{\\tan\\theta}' };
    var detail = fac.map(function (u) {
      var odd = (((u.k % 4) + 4) % 4) % 2 === 1, ang = u.k * 90 + u.m * 45;
      var v = { sin: Math.sin, cos: Math.cos, tan: Math.tan }[u.fn](ang * Math.PI / 180);
      return T(FN[u.fn] + argTex(u.k, u.m)) + '（' + (odd ? '$' + (u.k * 90) + '°$ 是 $90°$ 的奇數倍 ⟹ 函數變成 $' + NEW[u.fn] + '$' : '$' + (u.k * 90) + '°$ 是 $90°$ 的偶數倍 ⟹ 函數不變') + '；把 $\\theta$ 當銳角時原角落在' + hxPos(ang) + ' ⟹ 取' + (v < 0 ? '負' : '正') + '號）';
    }).join('、');
    return { q: '化簡 ' + T(tex) + '。',
             a: T(resultTex(res.sign, res.es, res.ec)),
             h: '「奇變偶不變，符號看象限」逐項處理：' + detail + '；最後把分子兩項相乘、分母兩項相乘再約分。',
             p: { fac: fac, ans: { sign: res.sign, es: res.es, ec: res.ec } } };
  };
  /* 2-3 三個極坐標點圍成的三角形（極坐標 18 卷） */
  L2.polarTriangle = function (r) {
    var gaps = r.pick([[120, 120, 120], [90, 90, 180], [60, 120, 180], [90, 120, 150], [60, 150, 150], [90, 90, 180]]);
    var r1 = r.int(2, 8), r2 = r.int(2, 8), r3 = r.int(2, 8), th1 = r.int(0, 23) * 15, th2 = (th1 + gaps[0]) % 360, th3 = (th2 + gaps[1]) % 360;
    var rat = F(0), surd = S(0, 1, 1), pairs = [[r1, r2, gaps[0]], [r2, r3, gaps[1]], [r3, r1, gaps[2]]];
    pairs.forEach(function (pr) { var v = sMulF(tv(pr[2]).sin, F(pr[0] * pr[1], 2)); if (v.c === 0) return; if (v.r === 1) rat = Fr.add(rat, sToF(v)); else surd = surd.c === 0 ? v : S(surd.c * v.d + v.c * surd.d, 3, surd.d * v.d); });
    var g = gaps[0], AB2 = (g === 60 || g === 90 || g === 120 || g === 180) ? r1 * r1 + r2 * r2 - 2 * r1 * r2 * (g === 60 ? 0.5 : g === 90 ? 0 : g === 120 ? -0.5 : -1) : null;
    var piece = ['OAB', 'OBC', 'OCA'].map(function (nm, i) { return T('\\triangle ' + nm + '=\\dfrac12\\cdot' + hxMul([pairs[i][0], pairs[i][1]]) + '\\sin' + pairs[i][2] + '°'); }).join('、');
    return { q: '極坐標平面上 $O$ 為極點，' + T('A[' + r1 + ',' + th1 + '°]') + '、' + T('B[' + r2 + ',' + th2 + '°]') + '、' + T('C[' + r3 + ',' + th3 + '°]') + '。求 ' + (AB2 !== null ? T(ov('AB')) + ' 與 ' : '') + T('\\triangle ABC') + ' 的面積。',
             a: (AB2 !== null ? T(ov('AB') + '=' + sqrtTex(AB2)) + '、' : '') + '面積 ' + T('=' + twoTex(rat, surd)),
             h: '三個極角把 $360°$ 切成 $' + gaps[0] + '°$、$' + gaps[1] + '°$、$' + gaps[2] + '°$，極點在三角形內（或邊上）⟹ $\\triangle ABC=\\triangle OAB+\\triangle OBC+\\triangle OCA$：' + piece + '，三塊相加。' + (AB2 !== null ? '$\\overline{AB}$ 用餘弦定理 ' + T(ov('AB') + '^2=' + r1 + '^2+' + r2 + '^2-' + hxMul([2, r1, r2]) + '\\cos' + g + '°') + '。' : ''),
             p: { r: [r1, r2, r3], th: [th1, th2, th3], gaps: gaps, ans: { AB2: AB2, rat: fr2(rat), surd: sArr(surd) } } };
  };
  /* 2-4 與已知直線夾特殊角的直線（斜角；建中 113 填 11 型） */
  L2.lineAngle = function (r) {
    var s1 = r.pick(SLOPES.slice(0, 6)), phi = (s1.ang % 45 === 0 && s1.ang % 90 !== 0) ? 45 : r.pick([30, 60]), L = lineOfSlope(s1, r), px = r.nz(-6, 6), py = r.nz(-6, 6);
    var angs = [angNorm(s1.ang + phi), angNorm(s1.ang - phi)];
    var slopeTex = function (ang) { return ang === 90 ? '不存在（鉛直線 $x=' + px + '$）' : T('m=' + sTex(tv(ang).tan)); };
    return { q: '直線 $L$ 過點 ' + T('P(' + px + ',' + py + ')') + '，且與直線 ' + T('L_1:' + L.tex) + ' 夾 ' + T(phi + '°') + ' 角。求 $L$ 的斜角與斜率（兩解）。',
             a: '斜角 ' + T(angs[0] + '°') + '：斜率' + slopeTex(angs[0]) + '；斜角 ' + T(angs[1] + '°') + '：斜率' + slopeTex(angs[1]),
             h: '用斜角不要用夾角公式：$L_1$ 的斜率是 $' + s1.tex + '$ ⟹ 斜角 $' + s1.ang + '°$；$L$ 的斜角 ' + T('=' + s1.ang + '°\\pm' + phi + '°') + '（不在 $-90°\\lt\\alpha\\le90°$ 裡就加減 $180°$），本題得 $' + angs[0] + '°$ 與 $' + angs[1] + '°$。斜角 $90°$ 是鉛直線（過 $P(' + px + ',' + py + ')$ 就是 $x=' + px + '$），斜率不存在，最常被漏掉。',
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
               h: '在 $\\triangle ABD$ 用餘弦定理求 ' + T('\\cos\\angle ADB=\\dfrac{' + AD + '^2+' + BD + '^2-' + AB + '^2}{' + hxMul([2, AD, BD]) + '}') + '；$\\angle ADC$ 是它的補角 ⟹ $\\cos\\angle ADC=-\\cos\\angle ADB$，再在 $\\triangle ADC$ 用一次：' + T(ov('AC') + '^2=' + AD + '^2+' + DC + '^2-' + hxMul([2, AD, DC]) + '\\cos\\angle ADC') + '。',
               p: { kind: 0, AB: AB, BD: BD, DC: DC, AD: AD, ans: { AC2: fr2(AC2) } } };
    }
    var b, c, m, n, AD2;
    do { c = r.int(2, 12); b = r.int(2, 12); m = r.int(1, 9); n = r.int(1, 9); tries++;
      AD2 = validTri(b, c, m + n) ? Fr.sub(F(c * c * n + b * b * m, m + n), F(m * n)) : null;   /* 斯圖爾特：AD² = (c²n + b²m)/(m+n) − mn */
    } while ((!AD2 || AD2.n <= 0 || AD2.d !== 1 || Math.round(Math.sqrt(AD2.n)) ** 2 !== AD2.n) && tries < 600);
    return { q: ABC + ' 中，$D$ 在 $\\overline{BC}$ 上，' + T(ov('AB') + '=' + c) + '、' + T(ov('AC') + '=' + b) + '、' + T(ov('BD') + '=' + m) + '、' + T(ov('DC') + '=' + n) + '。求 ' + T(ov('AD')) + '。',
             a: T(ov('AD') + '=' + sqrtTex(AD2.n)),
             h: '設 $\\overline{AD}=t$：在 $\\triangle ABD$ 有 ' + T(c + '^2=t^2+' + m + '^2-' + hxMul([2, m]) + 't\\cos\\angle ADB') + '、在 $\\triangle ACD$ 有 ' + T(b + '^2=t^2+' + n + '^2-' + hxMul([2, n]) + 't\\cos\\angle ADC') + '；兩個角互補 ⟹ $\\cos\\angle ADB=-\\cos\\angle ADC$，兩式消去 $\\cos$ 得 $t^2$。',
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
    if (surd.r === 1) { b1 = String(kk + jj); b2 = String(kk - jj); }   /* ∠A=60°：c·cosA 是整數，兩根直接寫成整數（原本會印成 2+8） */
    return { q: ABC + ' 中 ' + T('\\angle A=' + A + '°') + '、' + T(ov('AB') + '=' + c) + '、' + T(ov('BC') + '=' + aa) + '。求 ' + T(ov('AC')) + '（兩解）。',
             a: T(ov('AC') + '=' + b1) + ' 或 ' + T(b2),
             h: '把 $\\overline{AC}=b$ 當未知數放進餘弦定理：$' + aa + '^2=b^2+' + c + '^2-2\\cdot' + c + '\\cdot b\\cos' + A + '°$，解二次方程得兩個正根，這就是 SSA 的兩解。',
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
    var t = niceTri(r, 10), a = t[0], b = t[1], c = t[2], K = t[3], m = Math.max(a, b, c), s = F(a + b + c, 2);
    var rin = sDiv(K, S(a + b + c, 1, 2)), R = sDiv(S(a * b * c, 1, 4), K), hmax = sDiv(K, S(m, 1, 2));
    return { q: ABC + ' 三邊長為 ' + T(a + ',\\ ' + b + ',\\ ' + c) + '。求 (1) 面積　(2) 內切圓半徑　(3) 外接圓半徑　(4) 最長邊上的高。',
             a: '(1) ' + T(sTex(K)) + '　(2) ' + T(sTex(rin)) + '　(3) ' + T(sTex(R)) + '　(4) ' + T(sTex(hmax)),
             h: '海龍先算面積：' + T('s=\\dfrac{' + a + '+' + b + '+' + c + '}{2}=' + Fr.tex(s)) + '、$K=\\sqrt{s(s-a)(s-b)(s-c)}$；其餘三個都從面積出發：$r=\\dfrac Ks$、' + T('R=\\dfrac{abc}{4K}=\\dfrac{' + (a * b * c) + '}{4K}') + '、最長邊是 $' + m + '$ ⟹ ' + T('h=\\dfrac{2K}{' + m + '}') + '。',
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
             h: '對角互補：同一條 $\\overline{AC}$ 算兩次 ' + T(Q.a + '^2+' + Q.b + '^2-' + hxMul([2, Q.a, Q.b]) + '\\cos B=' + Q.c + '^2+' + Q.d + '^2+' + hxMul([2, Q.c, Q.d]) + '\\cos B') + ' 解出 $\\cos B$ 再回代得 $\\overline{AC}$；面積 ' + T('=\\dfrac12(' + hxMul([Q.a, Q.b]) + '+' + hxMul([Q.c, Q.d]) + ')\\sin B') + '（$\\sin D=\\sin B$）；$R=\\dfrac{\\overline{AC}}{2\\sin B}$（正弦定理用在 $\\triangle ABC$）。',
             p: { a: Q.a, b: Q.b, c: Q.c, d: Q.d, ans: { cosB: fr2(Q.cB), AC2: fr2(Q.AC2), area: sArr(Q.area), R: sArr(R) } } };
  };
  /* 2-12 角平分線：對邊、分比、平分線長（角平分線 7 卷） */
  L2.bisector = function (r) {
    var A = r.pick([60, 120]), b = r.int(2, 12), c = r.int(2, 12), a2 = b * b + c * c - 2 * b * c * (A === 60 ? 0.5 : -0.5);
    var AD = sMulF(tv(A / 2).cos, F(2 * b * c, b + c)), K = sMulF(tv(A).sin, F(b * c, 2)), gR = gcd(b, c);
    return { q: ABC + ' 中 ' + T(ov('AB') + '=' + c) + '、' + T(ov('AC') + '=' + b) + '、' + T('\\angle A=' + A + '°') + '，$\\overline{AD}$ 為 $\\angle A$ 的內角平分線，$D$ 在 $\\overline{BC}$ 上。求 (1) ' + T(ov('BC')) + '　(2) ' + T(ov('BD') + ':' + ov('DC')) + '　(3) ' + T(ov('AD')) + '　(4) ' + T('\\triangle ABD') + ' 的面積。',
             a: '(1) ' + T(sqrtTex(a2)) + '　(2) ' + T((c / gR) + ':' + (b / gR)) + '　(3) ' + T(sTex(AD)) + '　(4) ' + T(sTex(sMulF(K, F(c, b + c)))),
             h: '(1) 餘弦定理 ' + T(ov('BC') + '^2=' + c + '^2+' + b + '^2-' + hxMul([2, b, c]) + '\\cos' + A + '°') + '。(2) 角平分線 ⟹ ' + T(ov('BD') + ':' + ov('DC') + '=' + ov('AB') + ':' + ov('AC') + '=' + c + ':' + b) + '。(3) 面積切兩半：' + T('\\dfrac12\\cdot' + hxMul([b, c]) + '\\sin' + A + '°=\\dfrac12\\overline{AD}\\,(' + b + '+' + c + ')\\sin' + (A / 2) + '°') + '。(4) 同高 ⟹ 面積比 $=$ 底邊比 ' + T(ov('BD') + ':' + ov('BC') + '=' + c + ':' + (b + c)) + ' ⟹ ' + T('\\triangle ABD=' + Fr.tex(F(c, b + c)) + '\\triangle ABC') + '。',
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
    do { al = r.pick([30, 45, 60]); be = r.pick([30, 45, 60]); ga = r.pick([30, 45, 60]); v = Fr.sub(Fr.add(Fr.mul(F(2), cot2[al]), Fr.mul(F(2), cot2[ga])), Fr.mul(F(4), cot2[be])); tries++;
      /* △OAC 要存在且不退化：|OA−OC| < 2·OB < OA+OC ⟺ (cot²α+cot²γ−4cot²β)² < 4cot²α·cot²γ；等號＝塔底落在 AC 線上，與題幹「不共線」矛盾 */
      var w_ = Fr.sub(Fr.add(cot2[al], cot2[ga]), Fr.mul(F(4), cot2[be])), flat = !Fr.lt(Fr.mul(w_, w_), Fr.mul(F(4), Fr.mul(cot2[al], cot2[ga])));
    } while ((v.n <= 0 || flat || (al === be && be === ga)) && tries < 100);
    var h = r.pick([10, 12, 15, 18, 20, 24, 30, 36, 42, 60]), AB2 = Fr.mul(F(h * h, 4), v), AB = sqrtF(AB2);
    return { q: '地面上三定點 $A$、$B$、$C$ 依序測得塔頂的仰角為 ' + T(al + '°') + '、' + T(be + '°') + '、' + T(ga + '°') + '。已知 $A,B,C$ 與塔底不共線，$B$ 為 $\\overline{AC}$ 的中點，塔高 ' + T(String(h)) + ' 公尺。求 ' + T(ov('AB')) + '。',
             a: T(ov('AB') + '=' + sTex(AB)) + ' 公尺',
             h: '設塔底 $O$，塔高 $' + h + '$：' + T(ov('OA') + '=\\dfrac{' + h + '}{\\tan' + al + '°}') + '、' + T(ov('OB') + '=\\dfrac{' + h + '}{\\tan' + be + '°}') + '、' + T(ov('OC') + '=\\dfrac{' + h + '}{\\tan' + ga + '°}') + '。$\\overline{OB}$ 是 $\\triangle OAC$ 的中線 ⟹ 中線長公式 $4\\overline{OB}^2=2\\overline{OA}^2+2\\overline{OC}^2-\\overline{AC}^2$ 解出 $\\overline{AC}$，再除以 $2$ 得 $\\overline{AB}$。',
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
    if (kind.indexOf('cos') >= 0) al = 90 - al;   /* cos 型的參考角是 acos(k)＝90°−asin(k)；原本誤用 asin，範圍不是整圈時解數會錯 */
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
    var t = r.pick(PYR), s = t[0], h = t[1], l = t[2], e2 = h * h + 2 * s * s, kind = r.int(0, 1);
    var tanD = F(h, s), cosE = sqrtF(F(2 * s * s, e2)), tanE = sqrtF(F(h * h, 2 * s * s)), vol = F(4 * s * s * h, 3), side = 4 * s * l;
    var stem = '正四角錐 $V$-$ABCD$ 的底面是邊長 ' + T(String(2 * s)) + ' 的正方形，側面與底面所夾角的正切值為 ' + T(Fr.tex(tanD)) + '。',
        base = '側面與底面的夾角在「體高—半邊長 $' + s + '$—斜高」這個直角三角形裡：' + T('\\tan=\\dfrac{h}{' + s + '}=' + Fr.tex(tanD)) + ' ⟹ 體高 $h=' + h + '$，斜高 ' + T('=\\sqrt{' + h + '^2+' + s + '^2}=' + l) + '。';
    if (kind === 0)
      return { q: stem + '求 (1) 體高　(2) 側稜長　(3) 側稜與底面所夾角的餘弦值　(4) 側面積（四個側面的面積和）。',
               a: '(1) ' + T(String(h)) + '　(2) ' + T(sqrtTex(e2)) + '　(3) ' + T(sTex(cosE)) + '　(4) ' + T(String(side)),
               h: base + '側稜 ' + T('=\\sqrt{h^2+(' + s + '\\sqrt2)^2}=\\sqrt{' + h + '^2+' + (2 * s * s) + '}') + '（$' + s + '\\sqrt2$ 是半對角線）；側稜與底面的夾角在同一個三角形裡，$\\cos=\\dfrac{' + s + '\\sqrt2}{\\text{側稜}}$；側面積 ' + T('=4\\cdot\\dfrac12\\cdot' + (2 * s) + '\\cdot' + l) + '。',
               p: { kind: 0, s: s, tan: fr2(tanD), ans: { h: h, e2: e2, cos: sArr(cosE), side: side } } };
    return { q: stem + '求 (1) 體高　(2) 斜高（$V$ 到底邊中點的距離）　(3) 體積　(4) 側稜與底面所夾角的正切值。',
             a: '(1) ' + T(String(h)) + '　(2) ' + T(String(l)) + '　(3) ' + T(Fr.tex(vol)) + '　(4) ' + T(sTex(tanE)),
             h: base + '體積 $=\\dfrac13\\times$ 底面積 $\\times$ 體高 ' + T('=\\dfrac13\\cdot' + (2 * s) + '^2\\cdot' + h) + '；側稜與底面的夾角在「體高 $' + h + '$—半對角線 $' + s + '\\sqrt2$—側稜」的三角形裡，' + T('\\tan=\\dfrac{' + h + '}{' + s + '\\sqrt2}') + '（分母有根號要有理化）。',
             p: { kind: 1, s: s, tan: fr2(tanD), ans: { h: h, l: l, vol: fr2(vol), tan: sArr(tanE) } } };
  };

  /* ══════════ 2026-09-28 擴充（依段考卷出現頻率補題型）：L1 5 型、L2 6 型 ══════════
     頻率：question_bank 14 份高一段考卷（另參考 12 份 99 課綱高二上的三角卷），統計腳本 _scripts/round2/g10b-ch04-expand/freq.py。
     每型開頭先丟掉一次 r()：連號種子的 LCG 首值幾乎相同，變體旗標不能靠它。小工具一律加 n28 前綴。 */
  /* 係數·變數（first：是不是第一項；變數是空字串時照印數字） */
  function n28term(c, v, first) {
    if (c === 0) return '';
    var ab = Math.abs(c), body = (ab === 1 && v !== '') ? v : ab + v;
    return first ? (c < 0 ? '-' : '') + body : (c < 0 ? '-' : '+') + body;
  }
  function n28lin(list) { var s = ''; list.forEach(function (t) { s += n28term(t[0], t[1], s === ''); }); return s === '' ? '0' : s; }
  /* 分數係數（1 省略、-1 只印負號） */
  function n28fc(f, v) { if (f.n === f.d) return v; if (f.n === -f.d) return '-' + v; return Fr.tex(f) + v; }
  function n28sg(s) { return s > 0 ? '正' : '負'; }
  function n28val(fn, deg) { var x = deg * Math.PI / 180; return fn === 'sin' ? Math.sin(x) : fn === 'cos' ? Math.cos(x) : Math.tan(x); }
  function n28pt(x, y) { return '(' + x + ',\\ ' + y + ')'; }

  /* 1-8 直角三角形：已知一個銳角的三角比與一邊，求其他邊（14 份高一段考卷有 10 份考直角三角形） */
  L1.rightSolve = function (r) {
    r();
    var t = r.int(0, 1), tr = tri(r), g = gcd(gcd(tr[0], tr[1]), tr[2]), a = tr[0] / g, b = tr[1] / g, c = tr[2] / g, m = g * r.int(1, 5);
    if (t === 0) {
      var fn = r.pick(['sin', 'cos', 'tan']), side = r.int(0, 2), names = ['BC', 'AC', 'AB'], base = [a, b, c], vals = [m * a, m * b, m * c];
      var ratio = fn === 'sin' ? F(a, c) : fn === 'cos' ? F(b, c) : F(a, b), per = m * (a + b + c);
      var oth = [0, 1, 2].filter(function (i) { return i !== side; });
      var rtxt = fn === 'sin' ? '對邊 $\\overline{BC}$ 比斜邊 $\\overline{AB}$' : fn === 'cos' ? '鄰邊 $\\overline{AC}$ 比斜邊 $\\overline{AB}$' : '對邊 $\\overline{BC}$ 比鄰邊 $\\overline{AC}$';
      return { q: '直角三角形 $ABC$ 中 $\\angle C=90°$，' + T('\\' + fn + ' A=' + Fr.tex(ratio)) + '、' + T(ov(names[side]) + '=' + vals[side]) + '。求 ' + T(ov(names[oth[0]])) + '、' + T(ov(names[oth[1]])) + ' 與 $\\triangle ABC$ 的周長。',
               a: T(ov(names[oth[0]]) + '=' + vals[oth[0]]) + '、' + T(ov(names[oth[1]]) + '=' + vals[oth[1]]) + '、周長 ' + T('=' + per),
               h: T('\\' + fn + ' A=' + Fr.tex(ratio)) + ' 是' + rtxt + '，畢氏定理補第三個數：' + T(ov('BC') + ':' + ov('AC') + ':' + ov('AB') + '=' + a + ':' + b + ':' + c) + '。已知的 ' + T(ov(names[side]) + '=' + vals[side]) + ' 對到比例裡的 $' + base[side] + '$，所以三邊都是比例的 $' + m + '$ 倍。',
               p: { t: 0, fn: fn, side: side, a: a, b: b, c: c, m: m, ans: { BC: vals[0], AC: vals[1], AB: vals[2], per: per } } };
    }
    /* ∠A=90°、AD 是斜邊上的高：AB=ma、AC=mb、BC=mc；cosB=a/c、sinB=b/c、tanB=b/a */
    var fnB = r.pick(['sin', 'cos', 'tan']), gs = r.int(0, 2), ask = r.int(0, 2), AB = m * a, AC = m * b, BC = m * c;
    var ratioB = fnB === 'sin' ? F(b, c) : fnB === 'cos' ? F(a, c) : F(b, a);
    var gN = ['AB', 'AC', 'BC'][gs], gV = [AB, AC, BC][gs], AD = F(m * a * b, c), BD = F(m * a * a, c), CD = F(m * b * b, c);
    var aN = ['AD', 'BD', 'CD'][ask], aV = [AD, BD, CD][ask];
    var how = ask === 0 ? '$\\triangle ABD$ 也是直角三角形（$\\angle ADB=90°$），' + T(ov('AD') + '=' + ov('AB') + '\\sin B=' + AB + '\\cdot' + Fr.tex(F(b, c)))
            : ask === 1 ? '$\\triangle ABD$ 也是直角三角形（$\\angle ADB=90°$），' + T(ov('BD') + '=' + ov('AB') + '\\cos B=' + AB + '\\cdot' + Fr.tex(F(a, c)))
                        : '先在直角 $\\triangle ABD$ 求 ' + T(ov('BD') + '=' + ov('AB') + '\\cos B=' + AB + '\\cdot' + Fr.tex(F(a, c))) + '，再用 ' + T(ov('CD') + '=' + BC + '-' + ov('BD'));
    return { q: '$\\triangle ABC$ 中 $\\angle A=90°$，$\\overline{AD}$ 是斜邊 $\\overline{BC}$ 上的高（$D$ 在 $\\overline{BC}$ 上）。若 ' + T(ov(gN) + '=' + gV) + '、' + T('\\' + fnB + ' B=' + Fr.tex(ratioB)) + '，求 ' + T(ov(aN)) + '。',
             a: T(ov(aN) + '=' + Fr.tex(aV)),
             h: '$\\angle A=90°$，' + T('\\' + fnB + ' B=' + Fr.tex(ratioB)) + ' 給出 ' + T(ov('AB') + ':' + ov('AC') + ':' + ov('BC') + '=' + a + ':' + b + ':' + c) + '，由 ' + T(ov(gN) + '=' + gV) + ' 得三邊 ' + T(ov('AB') + '=' + AB) + '、' + T(ov('AC') + '=' + AC) + '、' + T(ov('BC') + '=' + BC) + '。' + how + '。',
             p: { t: 1, fnB: fnB, gs: gs, ask: ask, a: a, b: b, c: c, m: m, ans: { AD: fr2(AD), BD: fr2(BD), CD: fr2(CD) } } };
  };

  /* 1-9 已知 tanθ 求 sin、cos 的齊次式（同角關係 12 卷；成功 113下、北一女 113下、台中一中 113下 都考） */
  var N28M = [F(1, 2), F(2), F(1, 3), F(3), F(2, 3), F(3, 2), F(3, 4), F(4, 3), F(1, 4), F(4), F(2, 5), F(5, 2), F(5), F(1, 5)];
  L1.tanHomog = function (r) {
    r();
    var t = r.int(0, 2), m = r.pick(N28M), SN = '\\sin\\theta', CS = '\\cos\\theta', TN = '\\tan\\theta';
    if (r() < 0.5) m = F(-m.n, m.d);
    if (t === 1) {
      var qa, qb, qc;
      do { qa = r.int(-4, 4); qb = r.int(-5, 5); qc = r.int(-4, 4); }
      while ([qa, qb, qc].filter(function (x) { return x !== 0; }).length < 2 || (qa === qc && qb === 0));
      var num = Fr.add(Fr.add(Fr.mul(F(qa), Fr.mul(m, m)), Fr.mul(F(qb), m)), F(qc)), den = Fr.add(F(1), Fr.mul(m, m)), v = Fr.div(num, den);
      var ex = n28lin([[qa, '\\sin^2\\theta'], [qb, '\\sin\\theta\\cos\\theta'], [qc, '\\cos^2\\theta']]);
      return { q: '已知 ' + T(TN + '=' + Fr.tex(m)) + '，求 ' + T(ex) + ' 的值。',
               a: T(Fr.tex(v)),
               h: '把式子除以 $\\sin^2\\theta+\\cos^2\\theta=1$（值不變），分子分母再同除以 $\\cos^2\\theta$，得 ' + T('\\dfrac{' + n28lin([[qa, '\\tan^2\\theta'], [qb, TN], [qc, '']]) + '}{\\tan^2\\theta+1}') + '；代 ' + T(TN + '=' + Fr.tex(m)) + '，分子 ' + T('=' + Fr.tex(num)) + '、分母 ' + T('=' + Fr.tex(den)) + '。',
               p: { t: 1, m: fr2(m), co: [qa, qb, qc], num: fr2(num), den: fr2(den), ans: fr2(v) } };
    }
    var a1, b1, c1, d1, num0, den0;
    do {
      a1 = r.int(-5, 5); b1 = r.int(-5, 5); c1 = r.int(-5, 5); d1 = r.int(-5, 5);
      num0 = Fr.add(Fr.mul(F(a1), m), F(b1)); den0 = Fr.add(Fr.mul(F(c1), m), F(d1));
    } while ((a1 === 0 && b1 === 0) || (c1 === 0 && d1 === 0) || (a1 === 0 && c1 === 0) || (b1 === 0 && d1 === 0) || den0.n === 0 || num0.n === 0 || a1 * d1 === b1 * c1 ||
             (t === 2 && Fr.eq(F(a1), Fr.mul(Fr.div(num0, den0), F(c1)))));
    var v0 = Fr.div(num0, den0), top = n28lin([[a1, SN], [b1, CS]]), bot = n28lin([[c1, SN], [d1, CS]]);
    var topT = n28lin([[a1, TN], [b1, '']]), botT = n28lin([[c1, TN], [d1, '']]);
    if (t === 0)
      return { q: '已知 ' + T(TN + '=' + Fr.tex(m)) + '，求 ' + T('\\dfrac{' + top + '}{' + bot + '}') + ' 的值。',
               a: T(Fr.tex(v0)),
               h: '分子分母同除以 $\\cos\\theta$（$\\tan\\theta$ 存在，所以 $\\cos\\theta\\ne0$），得 ' + T('\\dfrac{' + topT + '}{' + botT + '}') + '；代 ' + T(TN + '=' + Fr.tex(m)) + '，分子 ' + T('=' + Fr.tex(num0)) + '、分母 ' + T('=' + Fr.tex(den0)) + '。',
               p: { t: 0, m: fr2(m), co: [a1, b1, c1, d1], num: fr2(num0), den: fr2(den0), ans: fr2(v0) } };
    var A = Fr.sub(F(a1), Fr.mul(v0, F(c1))), Bv = Fr.sub(Fr.mul(v0, F(d1)), F(b1));
    return { q: '若 ' + T('\\dfrac{' + top + '}{' + bot + '}=' + Fr.tex(v0)) + '，求 ' + T(TN) + '。',
             a: T(TN + '=' + Fr.tex(m)),
             h: '左邊分子分母同除以 $\\cos\\theta$，變成 ' + T('\\dfrac{' + topT + '}{' + botT + '}=' + Fr.tex(v0)) + '；交叉相乘後整理成 ' + T(n28fc(A, TN) + '=' + Fr.tex(Bv)) + '。',
             p: { t: 2, m: fr2(m), co: [a1, b1, c1, d1], v: fr2(v0), A: fr2(A), B: fr2(Bv), ans: fr2(m) } };
  };

  /* 2-8 廣義角三角比比大小（9 卷；建中、北一女、台中女中 113下都考） */
  L1.trigCompare = function (r) {
    r();
    var t = r.int(0, 1), labs, i;
    if (t === 0) {
      var refs = [10, 20, 25, 35, 40, 50, 55, 65, 70, 80], ref, qd, al, vals, ok;
      do {
        ref = r.pick(refs); qd = r.int(1, 4);
        var base = [0, ref, 180 - ref, 180 + ref, 360 - ref][qd], sh = r.pick([0, 0, 0, 360, -360]); al = base + sh;
        if (al <= -180) al = base;
        vals = ['sin', 'cos', 'tan'].map(function (f) { return n28val(f, al); });
        ok = (ref > 45 || qd >= 3) && Math.abs(vals[0] - vals[1]) > 1e-3 && Math.abs(vals[0] - vals[2]) > 1e-3 && Math.abs(vals[1] - vals[2]) > 1e-3;
      } while (!ok);
      var fns = r.shuffle(['sin', 'cos', 'tan']); labs = ['a', 'b', 'c'];
      var items = fns.map(function (f, k) { return { l: labs[k], f: f, v: n28val(f, al) }; });
      var ord = items.slice().sort(function (x, y) { return x.v - y.v; }).map(function (x) { return x.l; });
      var sgn = ['sin', 'cos', 'tan'].map(function (f) { return n28val(f, al) > 0 ? 1 : -1; });
      return { q: '設 ' + T(items.map(function (x) { return x.l + '=\\' + x.f + hxA(al); }).join(',\\ ')) + '，將 ' + T('a,b,c') + ' 由小到大排列。',
               a: T(ord.join('\\lt ')),
               h: T(hxA(al)) + ' 的終邊在' + hxPos(al) + '，參考角 $' + ref + '°$：$\\sin$ 為' + n28sg(sgn[0]) + '、$\\cos$ 為' + n28sg(sgn[1]) + '、$\\tan$ 為' + n28sg(sgn[2]) + '。' + (ref > 45 ? '參考角大於 $45°$，所以 $|\\sin|\\gt|\\cos|$，而且 $|\\tan|=\\dfrac{|\\sin|}{|\\cos|}\\gt1$。' : '參考角小於 $45°$，所以 $|\\cos|\\gt|\\sin|$，而 $|\\tan|=\\dfrac{|\\sin|}{|\\cos|}\\gt|\\sin|$。') + '先分正負，負的裡面絕對值大的比較小。',
               p: { t: 0, al: al, ref: ref, fns: fns, ans: ord } };
    }
    var fn = r.pick(['sin', 'cos', 'tan']), angs, vs, good;
    do {
      angs = []; good = true;
      while (angs.length < 4) {
        var d = r.int(-17, 53) * 10;
        if (d % 90 === 0 || d % 30 === 0 || angs.indexOf(d) >= 0) continue;
        angs.push(d);
      }
      vs = angs.map(function (d) { return n28val(fn, d); });
      for (i = 0; i < 4; i++) for (var j = i + 1; j < 4; j++) if (Math.abs(vs[i] - vs[j]) < 1e-3) good = false;
    } while (!good);
    labs = ['a', 'b', 'c', 'd'];
    var it2 = angs.map(function (d, k) { return { l: labs[k], d: d, v: vs[k] }; });
    var ord2 = it2.slice().sort(function (x, y) { return x.v - y.v; }).map(function (x) { return x.l; });
    var conv = it2.map(function (x) {
      var ref2 = hxRef(x.d), s2 = x.v > 0 ? '' : '-';
      return T(FN[fn] + hxA(x.d) + (x.d === ref2 ? '' : '=' + s2 + FN[fn] + ref2 + '°'));
    }).join('、');
    return { q: '設 ' + T(it2.map(function (x) { return x.l + '=' + FN[fn] + hxA(x.d); }).join(',\\ ')) + '，將 ' + T('a,b,c,d') + ' 由小到大排列。',
             a: T(ord2.join('\\lt ')),
             h: '每個都化成參考角（銳角）的' + { sin: '正弦', cos: '餘弦', tan: '正切' }[fn] + '，正負看象限：' + conv + '。銳角的 ' + (fn === 'cos' ? '$\\cos$ 角度越大值越小' : '$' + FN[fn] + '$ 角度越大值越大') + '；先分正負再比。',
             p: { t: 1, fn: fn, angs: angs, ans: ord2 } };
  };

  /* 2-9 對稱點、旋轉點的極坐標（極坐標 13 卷；北一女、武陵、板橋 113下 都考「P 的極坐標是 [r,θ]，別的點怎麼寫」） */
  var N28TR = [
    { f: function (x, y) { return [-x, y]; }, e: '180°-\\theta', w: '對 $y$ 軸對稱', c: '-\\cos\\theta', s: '\\sin\\theta' },
    { f: function (x, y) { return [x, -y]; }, e: '-\\theta', w: '對 $x$ 軸對稱', c: '\\cos\\theta', s: '-\\sin\\theta' },
    { f: function (x, y) { return [-x, -y]; }, e: '180°+\\theta', w: '對原點對稱', c: '-\\cos\\theta', s: '-\\sin\\theta' },
    { f: function (x, y) { return [y, x]; }, e: '90°-\\theta', w: '對直線 $y=x$ 對稱', c: '\\sin\\theta', s: '\\cos\\theta' },
    { f: function (x, y) { return [-y, x]; }, e: '90°+\\theta', w: '繞原點逆時針轉 $90°$', c: '-\\sin\\theta', s: '\\cos\\theta' },
    { f: function (x, y) { return [y, -x]; }, e: '\\theta-90°', w: '繞原點順時針轉 $90°$', c: '\\sin\\theta', s: '-\\cos\\theta' },
    { f: function (x, y) { return [-y, -x]; }, e: '270°-\\theta', w: '對直線 $y=-x$ 對稱', c: '-\\sin\\theta', s: '-\\cos\\theta' }
  ];
  L1.polarSym = function (r) {
    r();
    var t = r.int(0, 1), tr = r.pick([[3, 4, 5], [4, 3, 5], [5, 12, 13], [12, 5, 13], [8, 15, 17], [15, 8, 17], [7, 24, 25], [24, 7, 25], [6, 8, 10], [8, 6, 10]]);
    var x = tr[0] * r.sign(), y = tr[1] * r.sign(), rr = tr[2], k = r.int(0, 6), s = r.pick([1, 1, 1, 2, 3]), TRk = N28TR[k], Q = TRk.f(x, y), X = s * Q[0], Y = s * Q[1];
    var head = '直角坐標 ' + T('P' + n28pt(x, y)) + ' 的極坐標為 ' + T('[' + rr + ',\\theta]') + '。';
    var idt = T('\\cos(' + TRk.e + ')=' + TRk.c) + '、' + T('\\sin(' + TRk.e + ')=' + TRk.s);
    var rel = (s > 1 ? '$Q$ 的坐標除以 $' + s + '$ 之後是 ' + T(n28pt(Q[0], Q[1])) + '，這一點是' : '$Q$ 是') + '由 $P$ ' + TRk.w + '得到的';
    if (t === 0)
      return { q: head + '用 ' + T('\\theta') + ' 表示點 ' + T('Q' + n28pt(X, Y)) + ' 的極坐標。',
               a: T('[' + s * rr + ',' + TRk.e + ']'),
               h: T(ov('OQ') + '=\\sqrt{' + hxSq(X) + '+' + hxSq(Y) + '}=' + s * rr) + '；' + rel + '，所以極角是 $' + TRk.e + '$。可以用 ' + idt + ' 代回驗算。',
               p: { t: 0, x: x, y: y, r: rr, k: k, s: s, tr: k, ans: [X, Y] } };
    return { q: head + '求極坐標 ' + T('[' + s * rr + ',' + TRk.e + ']') + ' 的直角坐標。',
             a: T(n28pt(X, Y)),
             h: T('[' + s * rr + ',' + TRk.e + ']') + ' 的直角坐標是 ' + T('\\left(' + s * rr + '\\cos(' + TRk.e + '),\\ ' + s * rr + '\\sin(' + TRk.e + ')\\right)') + '；' + idt + '，再代 ' + T('\\cos\\theta=' + Fr.tex(F(x, rr)) + ',\\ \\sin\\theta=' + Fr.tex(F(y, rr))) + '。',
             p: { t: 1, x: x, y: y, r: rr, k: k, s: s, tr: k, ans: [X, Y] } };
  };

  /* 4-7 四邊形面積＝½·兩對角線·sin 夾角（三角形面積 14 卷；成功、高雄中學、高雄中學 114 都考對角線夾角） */
  L1.quadDiagArea = function (r) {
    r();
    var t = r.int(0, 2), p = r.int(3, 14), q = r.int(3, 14), phi = t === 2 ? r.pick([30, 45, 60, 90]) : r.pick([30, 45, 60, 90, 120, 135, 150]);
    var K = sMulF(tv(phi).sin, F(p * q, 2)), stem = '凸四邊形 $ABCD$ 的兩條對角線 ' + T(ov('AC') + '=' + p);
    var why = '對角線交於 $O$，切成的四個小三角形都用「兩邊夾角」算面積（相鄰的角互補，正弦相等），合起來 ' + T('[ABCD]=\\dfrac12\\cdot' + ov('AC') + '\\cdot' + ov('BD') + '\\sin\\theta') + '。';
    if (t === 0)
      return { q: stem + '、' + T(ov('BD') + '=' + q) + '，兩條對角線的夾角為 ' + T(phi + '°') + '。求四邊形 $ABCD$ 的面積。',
               a: T(sTex(K)),
               h: why + '代入 ' + T('\\dfrac12\\cdot' + p + '\\cdot' + q + '\\sin' + phi + '°') + '，其中 ' + T(hxEq('sin', phi)) + '。',
               p: { t: 0, p: p, q: q, phi: phi, ans: sArr(K) } };
    if (t === 1)
      return { q: stem + '，兩條對角線的夾角為 ' + T(phi + '°') + '，四邊形 $ABCD$ 的面積為 ' + T(sTex(K)) + '。求 ' + T(ov('BD')) + '。',
               a: T(ov('BD') + '=' + q),
               h: why + '代入：' + T(sTex(K) + '=\\dfrac12\\cdot' + p + '\\cdot' + ov('BD') + (phi === 90 ? '' : '\\cdot' + sTex(tv(phi).sin))) + '，解出 ' + T(ov('BD')) + '。',
               p: { t: 1, p: p, K: sArr(K), phi: phi, ans: q } };
    return { q: stem + '、' + T(ov('BD') + '=' + q) + '，四邊形 $ABCD$ 的面積為 ' + T(sTex(K)) + '。求兩條對角線所夾的銳角（或直角）。',
             a: T(phi + '°'),
             h: why + '代入：' + T(sTex(K) + '=\\dfrac12\\cdot' + p + '\\cdot' + q + '\\sin\\theta') + ' ⟹ ' + T('\\sin\\theta=' + sTex(tv(phi).sin)) + '。' + (phi === 90 ? '' : '夾角有銳角、鈍角兩個，題目問銳角。'),
             p: { t: 2, p: p, q: q, K: sArr(K), ans: phi } };
  };

  /* ═════ L2 ═════ */
  /* 2-18 已知一個廣義角的三角比＝k，以 k 表示另一個（誘導公式 13 卷；高雄中學 113下、成功 113下 都考） */
  var N28X = [10, 20, 25, 35, 40, 50, 55, 65, 70, 80];
  function n28mono(R, G) {   /* 目標 R={sign,es,ec}、已知 G={es,ec}（K=|k|）→ [K 的次方, √(1−K²) 的次方, √(1+K²) 的次方] */
    var s, c;
    if (G.es === 1 && G.ec === 0) { s = [1, 0, 0]; c = [0, 1, 0]; }
    else if (G.es === 0 && G.ec === 1) { s = [0, 1, 0]; c = [1, 0, 0]; }
    else if (G.es === 1) { s = [1, 0, -1]; c = [0, 0, -1]; }
    else { s = [0, 0, -1]; c = [1, 0, -1]; }
    return [0, 1, 2].map(function (i) { return R.es * s[i] + R.ec * c[i]; });
  }
  function n28kTex(sg, e) {   /* 分母有根號一律有理化 */
    var num = [], den = [];
    if (e[0] === 1) num.push('k'); else if (e[0] === -1) den.push('k');
    if (e[1] !== 0) { num.push('\\sqrt{1-k^2}'); if (e[1] === -1) den.push('1-k^2'); }
    if (e[2] !== 0) { num.push('\\sqrt{1+k^2}'); if (e[2] === -1) den.push('1+k^2'); }
    var n = num.join('') || '1', d = den.join('');
    return (sg < 0 ? '-' : '') + (d ? '\\dfrac{' + n + '}{' + d + '}' : n);
  }
  function n28baseTex(R, x) {   /* sin^es·cos^ec（es,ec ∈ 那四種）的銳角寫法 */
    if (R.es === 1 && R.ec === 0) return '\\sin' + x + '°';
    if (R.es === 0 && R.ec === 1) return '\\cos' + x + '°';
    if (R.es === 1) return '\\tan' + x + '°';
    return '\\dfrac{1}{\\tan' + x + '°}';
  }
  L2.reduceK = function (r) {
    r();
    var x = r.pick(N28X), fns = ['sin', 'cos', 'tan'], f1 = r.pick(fns), j1 = r.int(-1, 7), e1 = r.sign(), g = j1 * 90 + e1 * x, R1 = reduceOne(f1, j1, e1);
    var tg = [], used = {}; used[f1 + g] = 1;
    while (tg.length < 2) {
      var f2 = r.pick(fns), j2 = r.int(-2, 7), e2 = r.sign(), a2 = j2 * 90 + e2 * x;
      if (used[f2 + a2] || (tg.length === 1 && tg[0].f === f2)) continue;
      var R2 = reduceOne(f2, j2, e2), ex = n28mono(R2, R1);
      if (ex.some(function (v) { return Math.abs(v) > 1; })) continue;
      var sg = R2.sign * (Math.abs(ex[0]) === 1 ? R1.sign : 1), tx = n28kTex(sg, ex);
      if (tg.length === 1 && tg[0].tex === tx) continue;
      used[f2 + a2] = 1;
      tg.push({ f: f2, a: a2, R: R2, tex: tx });
    }
    var Kt = R1.sign < 0 ? '-k' : 'k', gv = n28baseTex(R1, x);
    var tri3 = (R1.es === 1 && R1.ec === 0) ? '斜邊 $1$、對邊 $' + Kt + '$、鄰邊 $\\sqrt{1-k^2}$' : (R1.es === 0 && R1.ec === 1) ? '斜邊 $1$、鄰邊 $' + Kt + '$、對邊 $\\sqrt{1-k^2}$'
             : R1.es === 1 ? '鄰邊 $1$、對邊 $' + Kt + '$、斜邊 $\\sqrt{1+k^2}$' : '對邊 $1$、鄰邊 $' + Kt + '$、斜邊 $\\sqrt{1+k^2}$';
    var red = tg.map(function (u) { return T(FN[u.f] + hxA(u.a) + '=' + (u.R.sign < 0 ? '-' : '') + n28baseTex(u.R, x)); }).join('、');
    return { q: '已知 ' + T(FN[f1] + hxA(g) + '=k') + '，以 ' + T('k') + ' 表示 ' + T(FN[tg[0].f] + hxA(tg[0].a)) + ' 與 ' + T(FN[tg[1].f] + hxA(tg[1].a)) + '。',
             a: T(FN[tg[0].f] + hxA(tg[0].a) + '=' + tg[0].tex) + '、' + T(FN[tg[1].f] + hxA(tg[1].a) + '=' + tg[1].tex),
             h: '全部化成參考角 $' + x + '°$ 的三角比：' + T(FN[f1] + hxA(g) + '=' + (R1.sign < 0 ? '-' : '') + gv) + '，所以 ' + T(gv + '=' + Kt) + '（' + T('k' + (R1.sign < 0 ? '\\lt0' : '\\gt0')) + '）；' + red + '。畫一個銳角 $' + x + '°$ 的直角三角形：' + tri3 + '，再讀出要的比值（分母有根號要有理化）。',
             p: { x: x, f1: f1, g: g, tg: tg.map(function (u) { return [u.f, u.a]; }), ans: tg.map(function (u) { return u.tex; }) } };
  };

  /* 2-19 平方關係化成二次方程再找角（同角關係 12 卷；高雄中學 113下、高雄女中 114、台中一中 113下） */
  var N28R = [F(0), F(1, 2), F(-1, 2), F(1), F(-1)];
  var N28E = [F(2), F(-2), F(3), F(-3), F(3, 2), F(-3, 2), F(5, 2), F(-5, 2), F(4, 3), F(-4, 3)];
  function n28sol(uf, v) {
    var key = v.n + '/' + v.d, SS = { '0/1': [0, 180], '1/2': [30, 150], '-1/2': [210, 330], '1/1': [90], '-1/1': [270] }, CC = { '0/1': [90, 270], '1/2': [60, 300], '-1/2': [120, 240], '1/1': [0], '-1/1': [180] };
    return (uf === 'sin' ? SS : CC)[key];
  }
  function n28inRange(v) { return v.n * v.n <= v.d * v.d; }
  L2.trigQuadEq = function (r) {
    r();
    var t = r.int(0, 1), uf = r.pick(['sin', 'cos']), vf = uf === 'sin' ? 'cos' : 'sin', U = '\\' + uf + '\\theta', U2 = '\\' + uf + '^2\\theta', V2 = '\\' + vf + '^2\\theta';
    var r1, r2, A, B, C, P, Q, R0, g, rg = 0;
    do {
      if (t === 0) { r1 = r.pick(N28R); do { r2 = r.pick(N28R.concat(N28E)); } while (Fr.eq(r1, r2)); }
      else {
        var pp, qq; do { qq = r.int(3, 7); pp = r.int(1, qq - 1); } while (gcd(pp, qq) !== 1);
        r1 = F(pp, qq); r2 = r.pick(N28E.concat([F(-1, 2), F(-1, 3), F(-2, 3), F(-3, 4)]));
      }
      A = r1.d * r2.d; B = -(r1.d * r2.n + r2.d * r1.n); C = r1.n * r2.n; g = gcd(gcd(A, Math.abs(B)), Math.abs(C)) || 1; A /= g; B /= g; C /= g;
      P = -A; Q = B; R0 = A + C;
      if (P < 0) { P = -P; Q = -Q; R0 = -R0; }
    } while (Q === 0);
    var form = r.int(0, 1), eq;
    if (form === 0 || R0 === 0) eq = n28lin([[P, V2], [Q, U], [R0, '']]) + '=0';
    else if (Q < 0) eq = n28lin([[P, V2], [R0, '']]) + '=' + n28lin([[-Q, U]]);
    else eq = n28lin([[P, V2], [Q, U]]) + '=' + n28lin([[-R0, '']]);
    var fac = '\\left(' + n28lin([[r1.d, U], [-r1.n, '']]) + '\\right)\\left(' + n28lin([[r2.d, U], [-r2.n, '']]) + '\\right)=0';
    var hq = '把 ' + T(V2) + ' 換成 ' + T('1-' + U2) + '，整理成 ' + T(U) + ' 的二次方程式 ' + T(n28lin([[A, U2], [B, U], [C, '']]) + '=0') + '，因式分解 ' + T(fac) + '，得 ' + T(U + '=' + Fr.tex(r1)) + ' 或 ' + T(Fr.tex(r2)) + '。';
    if (t === 0) {
      rg = r.int(0, 1);
      var sols = [];
      [r1, r2].forEach(function (v) { if (n28inRange(v)) n28sol(uf, v).forEach(function (d) { sols.push(rg === 1 && d > 180 ? d - 360 : d); }); });
      sols.sort(function (a, b) { return a - b; });
      var rgT = rg === 0 ? '0°\\le\\theta\\lt360°' : '-180°\\lt\\theta\\le180°', bad = [r1, r2].filter(function (v) { return !n28inRange(v); });
      return { q: '在 ' + T(rgT) + ' 的範圍內解方程式 ' + T(eq) + '。',
               a: T('\\theta=' + sols.map(function (d) { return d + '°'; }).join(',\\ ')),
               h: hq + (bad.length ? T(Fr.tex(bad[0])) + ' 超出 $-1$ 到 $1$，不合。' : '兩個值都在 $-1$ 到 $1$ 之間，都要找角。') + '再用單位圓找出 ' + T(rgT) + ' 裡的每一個角。',
               p: { t: 0, uf: uf, rg: rg, r: [fr2(r1), fr2(r2)], ans: sols } };
    }
    var d2 = r1.d * r1.d - r1.n * r1.n, tn = uf === 'cos' ? S(1, d2, r1.n) : S(r1.n, d2, d2);
    return { q: '已知 $\\theta$ 為銳角，且 ' + T(eq) + '。求 ' + T('\\tan\\theta') + '。',
             a: T('\\tan\\theta=' + sTex(tn)),
             h: hq + '$\\theta$ 是銳角，' + T(U + '\\gt0') + '，只能取 ' + T(Fr.tex(r1)) + '。畫直角三角形：' + (uf === 'cos' ? '鄰邊 $' + r1.n + '$、斜邊 $' + r1.d + '$' : '對邊 $' + r1.n + '$、斜邊 $' + r1.d + '$') + '，第三邊 ' + T('\\sqrt{' + r1.d + '^2-' + r1.n + '^2}=' + sqrtTex(d2)) + '。',
             p: { t: 1, uf: uf, r: [fr2(r1), fr2(r2)], ans: sArr(tn) } };
  };

  /* 3-5 哪些條件能決定唯一的三角形（解三角形論證；14 份高一卷有 7 份考：北一女、建中、台中一中、台中女中、高雄中學、武陵、高雄女中） */
  function n28opt(type, r) {
    var b, c, a, A, B, K, p, q, u, v, x, y, z;
    if (type === 'SSS') {
      x = r.int(2, 9); y = r.int(2, 9); z = r.int(0, 2) === 0 ? x + y + r.int(0, 2) : r.int(Math.abs(x - y) + 1, x + y - 1);
      var ok = x + y > z && y + z > x && z + x > y;
      return { txt: T('a=' + x + ',\\ b=' + y + ',\\ c=' + z), n: ok ? 1 : 0,
               why: ok ? '三邊都給了，兩小邊的和大於最大邊，唯一' : T(x + '+' + y + '\\le ' + z) + '，構不成三角形' };
    }
    if (type === 'SAScos') {
      b = r.int(2, 9); c = r.int(2, 9); do { q = r.int(2, 9); p = r.int(1, q - 1); } while (gcd(p, q) !== 1); var sg = r.sign();
      return { txt: T('b=' + b + ',\\ c=' + c + ',\\ \\cos A=' + (sg < 0 ? '-' : '') + Fr.tex(F(p, q))), n: 1, why: '$\\cos A$ 定了 $\\angle A$（$0°$ 到 $180°$ 之間只有一個角），兩邊夾一角，唯一' };
    }
    if (type === 'SASsin') {
      b = r.int(2, 9); c = r.int(2, 9); do { q = r.int(2, 9); p = r.int(1, q - 1); } while (gcd(p, q) !== 1);
      return { txt: T('b=' + b + ',\\ c=' + c + ',\\ \\sin A=' + Fr.tex(F(p, q))), n: 2, why: T('\\sin A=' + Fr.tex(F(p, q))) + ' 時 $\\angle A$ 可以是銳角也可以是鈍角，有兩個三角形' };
    }
    if (type === 'AAS') {
      A = r.int(2, 30) * 5; B = r.int(2, 30) * 5; c = r.int(2, 12); var sum = A + B;
      if (r.int(0, 3) === 0) { B = 180 - A + r.int(0, 2) * 5; sum = A + B; }
      if (B <= 0 || B >= 180) { B = 40; sum = A + B; }
      return { txt: T('\\angle A=' + A + '°,\\ \\angle B=' + B + '°,\\ c=' + c), n: sum < 180 ? 1 : 0,
               why: sum < 180 ? '兩角一邊（第三個角 $' + (180 - sum) + '°$），唯一' : '兩角和 $' + sum + '°\\ge180°$，構不成三角形' };
    }
    if (type === 'SSA') {
      A = r.pick([30, 30, 45, 120, 150]);
      if (A === 30) {
        b = 2 * r.int(2, 8); var h = b / 2, cs = r.int(0, 3);
        a = cs === 0 ? r.int(1, h - 1) : cs === 1 ? h : cs === 2 ? r.int(h + 1, b - 1) : r.int(b, b + 4);
        var n = a < h ? 0 : a === h ? 1 : a < b ? 2 : 1;
        return { txt: T('a=' + a + ',\\ b=' + b + ',\\ \\angle A=30°'), n: n,
                 why: '高 ' + T('h=b\\sin A=' + h) + '；' + (n === 0 ? T('a\\lt h') + '，無解' : a === h ? T('a=h') + '，恰一個（直角）' : n === 2 ? T('h\\lt a\\lt b') + '，兩個' : T('a\\ge b') + '，一個') };
      }
      if (A === 45) {
        b = r.int(3, 10); var h2 = b * b / 2, cs2 = r.int(0, 2), lo = Math.ceil(Math.sqrt(h2)); if (lo * lo === h2) lo++;
        a = cs2 === 0 ? r.int(1, Math.max(1, lo - 1)) : cs2 === 1 ? r.int(lo, b - 1) : r.int(b, b + 3);
        if (a >= lo && a < b && lo >= b) a = b;
        var n2 = a * a < h2 ? 0 : a < b ? 2 : 1;
        return { txt: T('a=' + a + ',\\ b=' + b + ',\\ \\angle A=45°'), n: n2,
                 why: '高 ' + T('h=b\\sin A=' + sTex(S(b, 2, 2))) + '；' + (n2 === 0 ? T('a\\lt h') + '，無解' : n2 === 2 ? T('h\\lt a\\lt b') + '，兩個' : T('a\\ge b') + '，一個') };
      }
      b = r.int(2, 9); a = r.int(0, 1) ? b + r.int(1, 4) : r.int(1, b);
      return { txt: T('a=' + a + ',\\ b=' + b + ',\\ \\angle A=' + A + '°'), n: a > b ? 1 : 0,
               why: '$\\angle A$ 是鈍角，對邊 $a$ 必須是最大邊：' + (a > b ? T('a\\gt b') + '，一個' : T('a\\le b') + '，無解') };
    }
    if (type === 'area') {
      b = r.int(2, 9); c = r.int(2, 9); var half = b * c; /* 面積上限 bc/2 */
      var cs3 = r.int(0, 2); K = cs3 === 0 ? F(r.int(1, half - 1), 2) : cs3 === 1 ? F(half, 2) : F(half + r.int(1, 6), 2);
      var sn = Fr.div(Fr.mul(F(2), K), F(half)), n3 = Fr.lt(sn, F(1)) ? 2 : Fr.eq(sn, F(1)) ? 1 : 0;
      return { txt: T('b=' + b + ',\\ c=' + c) + '，面積為 ' + T(Fr.tex(K)), n: n3,
               why: T('\\sin A=\\dfrac{2\\times\\text{面積}}{bc}=' + Fr.tex(sn)) + '：' + (n3 === 2 ? '銳角、鈍角各一，兩個' : n3 === 1 ? '$\\angle A=90°$，一個' : '大於 $1$，無解') };
    }
    if (type === 'AAA') {
      A = r.int(4, 20) * 5; B = r.int(4, 20) * 5; if (A + B >= 175) B = 175 - A - 5 * r.int(1, 3); if (B < 5) B = 20;
      return { txt: T('\\angle A=' + A + '°,\\ \\angle B=' + B + '°,\\ \\angle C=' + (180 - A - B) + '°'), n: 9, why: '只給三個角，大小可以任意放大縮小（相似），有無限多個' };
    }
    /* cos2：cosA、cosB＋一邊 */
    do { q = r.int(2, 9); p = r.int(1, q - 1); } while (gcd(p, q) !== 1);
    do { z = r.int(2, 9); y = r.int(1, z - 1); } while (gcd(y, z) !== 1);
    u = F(p * r.sign(), q); v = F(y * r.sign(), z); c = r.int(2, 9);
    if (u.n < 0 && v.n < 0) v = F(-v.n, v.d);
    var s4 = Fr.add(u, v), n4 = s4.n > 0 ? 1 : 0;
    return { txt: T('\\cos A=' + Fr.tex(u) + ',\\ \\cos B=' + Fr.tex(v) + ',\\ c=' + c), n: n4,
             why: n4 ? T('\\cos A\\gt-\\cos B=\\cos(180°-B)') + '，所以 $\\angle A+\\angle B\\lt180°$，兩角一邊，唯一' : T('\\cos A\\le-\\cos B=\\cos(180°-B)') + '，所以 $\\angle A+\\angle B\\ge180°$，構不成三角形' };
  }
  L2.uniqueTri = function (r) {
    r();
    var types, opts, good;
    do {
      types = r.shuffle(['SSS', 'SAScos', 'SASsin', 'AAS', 'SSA', 'SSA', 'area', 'AAA', 'cos2']).slice(0, 5);
      opts = types.map(function (ty) { return n28opt(ty, r); });
      var ones = opts.filter(function (o) { return o.n === 1; }).length;
      good = ones >= 1 && ones <= 4;
    } while (!good);
    var ans = [];
    opts.forEach(function (o, i) { if (o.n === 1) ans.push('(' + (i + 1) + ')'); });
    return { q: '$\\triangle ABC$ 中 $a,b,c$ 分別為 $\\angle A,\\angle B,\\angle C$ 的對邊。下列哪些選項的條件恰可決定唯一的 $\\triangle ABC$？' + opts.map(function (o, i) { return '　(' + (i + 1) + ') ' + o.txt; }).join(''),
             a: ans.join(''),
             h: '逐項數「能畫出幾個不同的三角形」：' + opts.map(function (o, i) { return '(' + (i + 1) + ') ' + o.why; }).join('；') + '。',
             p: { types: types, ns: opts.map(function (o) { return o.n; }), ans: ans } };
  };

  /* 3-6 弦長＝2R sin（圓周角）：共弦的兩圓、共邊的兩三角形、同圓的兩條弦（外接圓 11 卷；建中、北一女 113下、高雄中學 114、台中女中、竹科、武陵） */
  var N28ANG = [30, 45, 60, 90, 120, 135, 150];
  L2.chordSineRatio = function (r) {
    r();
    var t = r.int(0, 2), al, be, m;
    if (t === 0) {
      do { al = r.pick(N28ANG); be = r.pick(N28ANG); } while (!(sNum(tv(al).sin) < sNum(tv(be).sin) - 1e-9));
      var ratio = sToF(sMul(sDiv(tv(be).sin, tv(al).sin), sDiv(tv(be).sin, tv(al).sin)));
      return { q: '兩圓相交於 $A$、$B$ 兩點。$C$ 在大圓上、$D$ 在小圓上，且 ' + T('\\angle ACB=' + al + '°') + '、' + T('\\angle ADB=' + be + '°') + '。求大圓面積與小圓面積的比值。',
               a: T(Fr.tex(ratio)),
               h: '$\\overline{AB}$ 是兩圓的公共弦：在大圓裡 ' + T(ov('AB') + '=2R_1\\sin' + al + '°') + '，在小圓裡 ' + T(ov('AB') + '=2R_2\\sin' + be + '°') + '，所以 ' + T('\\dfrac{R_1}{R_2}=\\dfrac{\\sin' + be + '°}{\\sin' + al + '°}=' + sTex(sDiv(tv(be).sin, tv(al).sin))) + '；面積比是半徑比的平方。',
               p: { t: 0, al: al, be: be, ans: fr2(ratio) } };
    }
    if (t === 1) {
      do { al = r.pick(N28ANG); be = r.pick(N28ANG); } while (al === be);
      m = r.int(2, 12);
      var R1 = sMulF(sDiv(S(1, 1, 1), tv(al).sin), F(m, 2)), R2 = sMulF(sDiv(S(1, 1, 1), tv(be).sin), F(m, 2));
      return { q: '$\\triangle ABC$ 與 $\\triangle ACD$ 有公共邊 ' + T(ov('AC') + '=' + m) + '，且 ' + T('\\angle ABC=' + al + '°') + '、' + T('\\angle ADC=' + be + '°') + '。設兩個三角形的外接圓半徑分別為 ' + T('R_1') + '、' + T('R_2') + '，求 ' + T('R_1') + '、' + T('R_2') + '。',
               a: T('R_1=' + sTex(R1)) + '、' + T('R_2=' + sTex(R2)),
               h: '正弦定理用在公共邊 $\\overline{AC}$ 與它的對角：' + T('\\dfrac{' + m + '}{\\sin' + al + '°}=2R_1') + '、' + T('\\dfrac{' + m + '}{\\sin' + be + '°}=2R_2') + '，分母有根號要有理化。',
               p: { t: 1, al: al, be: be, m: m, ans: [sArr(R1), sArr(R2)] } };
    }
    al = r.pick([30, 45, 60]); do { be = r.pick([30, 45, 60, 90]); } while (be === al); m = r.int(2, 12);
    var AB = sMulF(sDiv(tv(be).sin, tv(al).sin), F(m)), RR = sMulF(sDiv(S(1, 1, 1), tv(al).sin), F(m, 2));
    return { q: '圓內接四邊形 $ABCD$ 中，' + T('\\angle CAD=' + al + '°') + '、' + T('\\angle ACB=' + be + '°') + '、' + T(ov('CD') + '=' + m) + '。求 ' + T(ov('AB')) + ' 與外接圓半徑 ' + T('R') + '。',
             a: T(ov('AB') + '=' + sTex(AB)) + '、' + T('R=' + sTex(RR)),
             h: '四個頂點在同一個圓上，每條弦都等於 ' + T('2R\\sin') + '（它所對的圓周角）：' + T(ov('CD') + '=2R\\sin\\angle CAD') + ' ⟹ ' + T(m + '=2R\\sin' + al + '°') + '；' + T(ov('AB') + '=2R\\sin\\angle ACB=2R\\sin' + be + '°') + '。',
             p: { t: 2, al: al, be: be, m: m, ans: [sArr(AB), sArr(RR)] } };
  };

  /* 4-15 面積拆兩塊求中間的線段（三角形面積 14 卷；台中女中 113下 填 17、高雄女中 113下 填 9、武陵 113下 填 9） */
  L2.areaSplitCevian = function (r) {
    r();
    var t = r.int(0, 2), o = r.int(0, 1), b, c, k, AD, ans, hh, q;
    var pre = '$\\triangle ABC$ 中，$D$ 在 $\\overline{BC}$ 上，';
    if (t === 0) {
      b = r.int(2, 12); c = r.int(2, 12);
      var aB = o === 0 ? 30 : 90, aC = o === 0 ? 90 : 30;
      AD = o === 0 ? S(b * c, 3, c + 2 * b) : S(b * c, 3, 2 * c + b);
      return { q: pre + T('\\angle BAD=' + aB + '°') + '、' + T('\\angle DAC=' + aC + '°') + '，' + T(ov('AB') + '=' + c) + '、' + T(ov('AC') + '=' + b) + '。求 ' + T(ov('AD')) + '。',
               a: T(ov('AD') + '=' + sTex(AD)),
               h: '設 ' + T(ov('AD') + '=x') + '，面積拆兩塊 ' + T('[ABC]=[ABD]+[ADC]') + '，三塊都用「兩邊夾角」：' + T('\\dfrac12\\cdot' + c + '\\cdot' + b + '\\sin120°=\\dfrac12\\cdot' + c + '\\cdot x\\sin' + aB + '°+\\dfrac12\\cdot' + b + '\\cdot x\\sin' + aC + '°') + '，解 $x$。',
               p: { t: 0, o: o, b: b, c: c, ans: sArr(AD) } };
    }
    if (t === 1) {
      /* 90° 那一側的邊 X、30° 那一側的邊 Y、AD=k√3：AD(Y+2X)=√3XY */
      k = r.int(1, 6); var giveX = r.int(0, 1), X, Y, val;
      if (giveX) { X = k + r.int(1, 10); val = F(2 * k * X, X - k); }
      else { Y = 2 * k + r.int(1, 10); val = F(k * Y, Y - 2 * k); }
      var n90 = o === 0 ? 'AC' : 'AB', n30 = o === 0 ? 'AB' : 'AC', ang = o === 0 ? T('\\angle DAC=90°') + '、' + T('\\angle BAD=30°') : T('\\angle BAD=90°') + '、' + T('\\angle DAC=30°');
      var gN = giveX ? n90 : n30, gV = giveX ? X : Y, aN = giveX ? n30 : n90;
      return { q: pre + ang + '，' + T(ov(gN) + '=' + gV) + '、' + T(ov('AD') + '=' + (k === 1 ? '' : k) + '\\sqrt3') + '。求 ' + T(ov(aN)) + '。',
               a: T(ov(aN) + '=' + Fr.tex(val)),
               h: '設 ' + T(ov(aN) + '=y') + '，面積拆兩塊：' + T('\\dfrac12\\cdot ' + (giveX ? X + '\\cdot y' : 'y\\cdot ' + Y) + '\\sin120°=\\dfrac12\\cdot ' + (giveX ? 'y' : Y) + '\\cdot ' + (k === 1 ? '' : k) + '\\sqrt3\\sin30°+\\dfrac12\\cdot ' + (giveX ? X : 'y') + '\\cdot ' + (k === 1 ? '' : k) + '\\sqrt3\\sin90°') + '，兩邊的 $\\sqrt3$ 約掉就是 $y$ 的一次方程式。',
               p: { t: 1, o: o, k: k, giveX: giveX, gv: gV, ans: fr2(val) } };
    }
    var tr = r.pick([[3, 4, 5], [4, 3, 5], [5, 12, 13], [12, 5, 13], [8, 15, 17], [15, 8, 17], [7, 24, 25], [24, 7, 25]]), u = tr[0], v = tr[1], w = tr[2];
    b = r.int(2, 15); c = r.int(2, 15);
    AD = o === 0 ? F(b * c * v, c * u + b * w) : F(b * c * v, b * u + c * w);
    var perp = o === 0 ? T(ov('AC') + '\\perp' + ov('AD')) : T(ov('AB') + '\\perp' + ov('AD')), other = o === 0 ? '\\angle BAD' : '\\angle DAC';
    return { q: '$\\triangle ABC$ 中 ' + T(ov('AB') + '=' + c) + '、' + T(ov('AC') + '=' + b) + '、' + T('\\cos\\angle BAC=-' + Fr.tex(F(u, w))) + '。$D$ 在 $\\overline{BC}$ 上且 ' + perp + '，求 ' + T(ov('AD')) + '。',
             a: T(ov('AD') + '=' + Fr.tex(AD)),
             h: T('\\cos\\angle BAC\\lt0') + '，$\\angle BAC$ 是鈍角，' + T('\\sin\\angle BAC=' + Fr.tex(F(v, w))) + '。' + T(other + '=\\angle BAC-90°') + '，' + T('\\sin(\\angle BAC-90°)=-\\cos\\angle BAC=' + Fr.tex(F(u, w))) + '。設 ' + T(ov('AD') + '=x') + '，面積拆兩塊：' + T('\\dfrac12\\cdot' + c + '\\cdot' + b + '\\cdot' + Fr.tex(F(v, w)) + '=\\dfrac12\\cdot' + (o === 0 ? c : b) + '\\cdot x\\cdot' + Fr.tex(F(u, w)) + '+\\dfrac12\\cdot' + (o === 0 ? b : c) + '\\cdot x') + '。',
             p: { t: 2, o: o, b: b, c: c, tr: [u, v, w], ans: fr2(AD) } };
  };

  /* 4-16 餘弦定理＋最值：相對運動的最短距離、兩邊和固定的最大面積（最值 11 卷；成功、台中一中、高雄女中、武陵 113下） */
  L2.triOptimize = function (r) {
    r();
    var t = r.int(0, 1), th = r.pick([60, 90, 120]);
    if (t === 0) {
      var k = th === 120 ? r.int(1, 2) : r.int(1, 5), d = r.int(5, 30), cs2 = th === 60 ? 1 : th === 90 ? 0 : -1;
      var A2 = k * k + 1 + k * cs2, B1 = -(2 * d * k + d * cs2), sin2 = th === 90 ? F(1) : F(3, 4);
      var xs = F(d * (2 * k + cs2), 2 * A2), mn2 = Fr.div(Fr.mul(F(d * d), sin2), F(A2)), mn = sqrtF(mn2);
      var sp = k === 1 ? '兩人的速度相同' : '乙的速度是甲的 $' + k + '$ 倍', kx = (k === 1 ? '' : k) + 'x';
      return { q: '$A$、$B$ 兩地相距 ' + T(String(d)) + ' 公里，道路 $\\overline{BA}$ 與 $\\overline{BC}$ 的夾角為 ' + T(th + '°') + '。甲從 $B$ 出發沿 $\\overline{BC}$ 前進，同時乙從 $A$ 出發沿 $\\overline{AB}$ 朝 $B$ 前進，' + sp + '。求 (1) 甲、乙兩人的最短距離　(2) 距離最短時甲走了幾公里。',
               a: '(1) ' + T(sTex(mn)) + ' 公里　(2) ' + T(Fr.tex(xs)) + ' 公里',
               h: '甲走 $x$ 公里時乙走 $' + kx + '$ 公里，兩人到 $B$ 的距離是 $x$ 與 $' + d + '-' + kx + '$，夾角 $' + th + '°$。餘弦定理：距離的平方 ' + T('=(' + d + '-' + kx + ')^2+x^2-2x(' + d + '-' + kx + ')\\cos' + th + '°=' + n28lin([[A2, 'x^2'], [B1, 'x'], [d * d, '']])) + '，配方求最小值，並確認這時乙還沒走到 $B$。',
               p: { t: 0, th: th, k: k, d: d, ans: { mn: sArr(mn), x: fr2(xs) } } };
    }
    var L = 2 * r.int(3, 20), hl = L / 2, Kmax = sMulF(tv(th).sin, F(hl * hl, 2)), AB = S(hl, th === 60 ? 1 : th === 90 ? 2 : 3, 1), fence = r.int(0, 1);
    var q = fence ? '用一條長 ' + T(String(L)) + ' 公尺的圍籬靠著一面直牆圍出三角形花圃 $\\triangle ABC$：牆是 $\\overline{AB}$，圍籬是 $\\overline{CA}$ 與 $\\overline{CB}$（' + T(ov('CA') + '+' + ov('CB') + '=' + L) + '，設 $\overline{CB}=a$、$\overline{CA}=b$），且 ' + T('\\angle ACB=' + th + '°') + '。求 (1) 花圃面積的最大值　(2) 面積最大時牆面 $\\overline{AB}$ 的長。'
                  : '$\\triangle ABC$ 中 ' + T('\\angle C=' + th + '°') + '，且 ' + T('a+b=' + L) + '（$a=\\overline{BC}$、$b=\\overline{CA}$）。求 (1) $\\triangle ABC$ 面積的最大值　(2) 面積最大時 $\\overline{AB}$ 的長。';
    return { q: q,
             a: '(1) ' + T(sTex(Kmax)) + '　(2) ' + T(sTex(AB)),
             h: '面積 ' + T('=\\dfrac12ab\\sin' + th + '°') + '；算幾不等式 ' + T('ab\\le\\left(\\dfrac{a+b}{2}\\right)^2=' + hl * hl) + '，' + T('a=b=' + hl) + ' 時取等號。再用餘弦定理 ' + T(ov('AB') + '^2=' + hl + '^2+' + hl + '^2-2\\cdot' + hl + '\\cdot' + hl + '\\cos' + th + '°') + '。',
             p: { t: 1, th: th, L: L, fence: fence, ans: { K: sArr(Kmax), AB: sArr(AB) } } };
  };

  /* ══════════════════════════════════════════════════════════ */
  /* ══════════════════════════════════════════════════════════
     L1 解題步驟（s：每步一段 HTML）與第一層提示（h1：只講「這是哪一型、第一步做什麼」，不帶數字）
     全部由 p（與 o.a）重算，所以與題目、答案一定一致；答案由頁面另行附在步驟後。
     用法：用 splice 腳本插在 META（var META_L1 = [）之前，並把 wrapAll(L1) 換成 wrapAll(L1, L1_SOL, L1_H1)。
     自己加的小工具一律加前綴 sol；patch_gen_10b4 的 hx* 工具（hxMul／hxSq／hxPos／hxRef／hxQuadXY／hxA／hxTwo）可直接用。
     ══════════════════════════════════════════════════════════ */
  function solF(t) { return F(t[0], t[1]); }                      /* p 裡的 [n,d] 還原成分數 */
  function solS(t) { return S(t[0], t[1], t[2]); }                /* p 裡的 [c,r,d] 還原成根式數 */
  function solFin(o) { return '答案：' + o.a + '。'; }
  function solPar(s) { s = String(s); return s.charAt(0) === '-' ? '\\left(' + s + '\\right)' : s; }   /* 負數加括號再相乘 */
  function solQuad(k) { return ['一', '二', '三', '四'][k - 1]; }
  function solEq(raw, red) { return raw === red ? raw : raw + '=' + red; }   /* 代入式已是最簡就不重複寫一次 */
  function solSigned(list) {                                      /* 一串根式數加起來的算式（負項寫成減、值為 0 的項略過） */
    var nz = list.filter(function (w) { return w.c !== 0; });
    if (!nz.length) return '0';
    return nz.map(function (w, i) { return i === 0 ? sTex(w) : (w.c < 0 ? '-' + sTex(S(-w.c, w.r, w.d)) : '+' + sTex(w)); }).join('');
  }

  var L1_H1 = {
    triDef: '這是「直角三角形的三角比定義」：先用畢氏定理把缺的那一邊補齊，再分清楚指定角的對邊、鄰邊與斜邊分別是哪一條。',
    specialEval: '這是「特殊角求值」：把題目用到的每一個特殊角的值先查出來（畫出兩個標準直角三角形最快），再逐項代入運算。',
    sinToCos: '這是「同角關係：知一求二」：把已知的比值畫成一個直角三角形的兩邊，用畢氏定理補出第三邊，三個比值就全出來了。',
    sumProdAcute: '這是「對稱式」：和、差、積三者靠平方關係互通，先把已知的那一個平方，再用平方關係換出另外兩個。',
    coAngleSum: '這是「餘角關係」：把和為直角的兩個角配成一對，每一對的平方和是一、每一對的正切乘積是一，數清楚有幾對就好。',
    elevOne: '這是「一次測量的仰角問題」：畫出一個直角三角形，水平距離是鄰邊、高是對邊，兩者用正切連起來。',
    elevTwo: '這是「兩次測量的仰角問題」：設高為未知數，把兩個測量點到塔腳的水平距離都用它表示，再由兩點的距離列一條方程式。',
    coterminal: '這是「同界角與象限」：一直加減一圈把角搬進零度到三百六十度之間，再看它落在哪一段決定象限。',
    pointTrig: '這是「終邊上一點求三角比」：先算該點到原點的距離（永遠取正），再用坐標與它的比值寫出三個三角比。',
    quadFind: '這是「象限判定與符號」：先用口訣把每個條件對應的象限刷出來取交集，或在指定象限取終邊上一點決定坐標的正負。',
    reduceEval: '這是「廣義角的特殊值」：每個角先化成同界角，由終邊所在的象限決定正負，再用參考角查特殊值。',
    polarConv: '這是「極坐標與直角坐標互換」：一邊用餘弦、正弦乘上半徑，另一邊用距離公式求半徑再由坐標正負與參考角定出極角。',
    polarDist: '這是「極坐標下的距離與面積」：兩個極角的差直接就是夾角，剩下的交給餘弦定理與兩邊夾角的面積公式。',
    slopeAngle: '這是「斜角與斜率」：斜率就是斜角的正切，斜角取在負九十度（不含）到九十度之間；兩線夾角則是兩個斜角相減。',
    sineLaw: '這是「正弦定理求邊」：先用內角和補出第三個角，再用邊與對角正弦的比值相等解出要求的邊。',
    circumR: '這是「外接圓半徑」：正弦定理的比值就是直徑，邊與它的對角正弦知道其中兩個就能求第三個。',
    cosLawSide: '這是「餘弦定理求邊」：已知兩邊與它們的夾角，直接代餘弦定理求第三邊的平方再開根號。',
    cosLawAngle: '這是「餘弦定理求角與形狀」：最大角一定對最大邊，算出它的餘弦值，正負號就決定了三角形的形狀。',
    sideRange: '這是「三角形的存在條件與鈍角範圍」：先用兩邊之差與兩邊之和框出範圍，再分「誰是最大邊」兩種情形討論鈍角。',
    ssaCount: '這是「兩邊一對角有幾組解」：先算對邊能達到的最短長度（也就是高），再拿已知的對邊跟它與另一邊比大小。',
    areaSAS: '這是「兩邊夾角的面積公式」：面積是兩邊乘積的一半再乘夾角的正弦；反過來給面積就先解出正弦值再找角。',
    heronArea: '這是「海龍公式」：先算半周長，再把三個差相乘開根號。',
    inOutRadius: '這是「內切圓與外接圓半徑」：面積是橋，先用海龍算面積，內切圓半徑是面積除以半周長、外接圓半徑是三邊乘積除以四倍面積。',
    medianLen: '這是「中線長」：直接套中線長公式，或先求一個角的餘弦再在小三角形裡用一次餘弦定理。',
    bisectorLen: '這是「角平分線」：分比等於兩鄰邊之比，長度則把大三角形的面積切成兩個小三角形相加。',
    cyclicQuad: '這是「圓內接四邊形」：對角互補所以餘弦互為相反數，同一條對角線用兩次餘弦定理列式相等就解得出來。',
    projLen: '這是「正射影」：線段長乘上夾角餘弦的絕對值就是在直線上的影子，夾角是鈍角時改用它的補角。',
    projTheorem: '這是「投影定理」：兩個角的餘弦各用一次餘弦定理算出來，再驗證兩條邊在第三邊上的正射影加起來剛好是第三邊。',
    cuboid: '這是「長方體的立體測量」：先把體對角線在指定面上的投影算出來，夾角就落在一個看得見的直角三角形裡。',
    pyramid: '這是「正四角錐」：底面正方形的半對角線與半邊長各配體高成一個直角三角形，側稜與斜高分別在這兩個三角形裡。'
  };

  var L1_SOL = {};

  /* ── §1 銳角三角比 ── */
  L1_SOL.triDef = function (p, o) {
    var a = p.a, b = p.b, c = p.c, X = p.which === 0 ? 'A' : 'B';
    var oppN = p.which === 0 ? 'BC' : 'AC', oppV = p.which === 0 ? a : b, adjN = p.which === 0 ? 'AC' : 'BC', adjV = p.which === 0 ? b : a;
    var st1 = p.kind === 0
      ? '兩股已知：' + T(ov('BC') + '=' + a) + '、' + T(ov('AC') + '=' + b) + '，畢氏定理補斜邊 ' + T(ov('AB') + '=\\sqrt{' + a + '^2+' + b + '^2}=' + c)
      : '斜邊與一股已知：' + T(ov('AB') + '=' + c) + '、' + T(ov('BC') + '=' + a) + '，畢氏定理補另一股 ' + T(ov('AC') + '=\\sqrt{' + c + '^2-' + a + '^2}=' + b);
    return [st1 + '。',
      '$\\angle C=90°$，所以 $\\angle ' + X + '$ 的對邊是 ' + T(ov(oppN) + '=' + oppV) + '、鄰邊是 ' + T(ov(adjN) + '=' + adjV) + '、斜邊是 ' + T(ov('AB') + '=' + c) + '。',
      '代進定義：' + T('\\sin ' + X + '=' + solEq('\\dfrac{' + oppV + '}{' + c + '}', Fr.tex(solF(p.ans.sin)))) + '、' + T('\\cos ' + X + '=' + solEq('\\dfrac{' + adjV + '}{' + c + '}', Fr.tex(solF(p.ans.cos)))) + '、' + T('\\tan ' + X + '=' + solEq('\\dfrac{' + oppV + '}{' + adjV + '}', Fr.tex(solF(p.ans.tan)))) + '。' + solFin(o)];
  };

  L1_SOL.specialEval = function (p, o) {
    var vals = [], seen = {}, parts = [];
    p.terms.forEach(function (t) {
      (t.sq ? [[t.f1, t.a1]] : [[t.f1, t.a1], [t.f2, t.a2]]).forEach(function (u) {
        var k = u[0] + u[1]; if (seen[k]) return; seen[k] = 1; vals.push(T(hxEq(u[0], u[1])));
      });
      var v = t.sq ? sMul(tv(t.a1)[t.f1], tv(t.a1)[t.f1]) : sMul(tv(t.a1)[t.f1], tv(t.a2)[t.f2]);
      parts.push(sMulF(v, F(t.sign)));
    });
    var expr = solSigned(parts);
    return ['先把用到的特殊角值查出來：' + vals.join('、') + '。',
      '逐項相乘（有平方就自己乘自己），兩項分別是 ' + parts.map(function (w) { return T(sTex(w)); }).join(' 與 ') + '。',
      '同類根式才能合併：' + T(solEq(expr, sTex(solS(p.ans)))) + '。' + solFin(o)];
  };

  L1_SOL.sinToCos = function (p, o) {
    var a = p.a, b = p.b, c = p.c;
    var g = p.kind === 0 ? ['對邊 $' + a + '$、斜邊 $' + c + '$', '\\sqrt{' + c + '^2-' + a + '^2}=' + b, '鄰邊']
          : p.kind === 1 ? ['鄰邊 $' + b + '$、斜邊 $' + c + '$', '\\sqrt{' + c + '^2-' + b + '^2}=' + a, '對邊']
                         : ['對邊 $' + a + '$、鄰邊 $' + b + '$', '\\sqrt{' + a + '^2+' + b + '^2}=' + c, '斜邊'];
    return ['$\\theta$ 是銳角，把已知的比值畫成一個直角三角形：' + g[0] + '。',
      '畢氏定理補第三邊（' + g[2] + '）：' + T(g[1]) + '。',
      '三個比值都出來了：' + T('\\sin\\theta=' + Fr.tex(solF(p.ans.sin))) + '、' + T('\\cos\\theta=' + Fr.tex(solF(p.ans.cos))) + '、' + T('\\tan\\theta=' + Fr.tex(solF(p.ans.tan))) + '，題目問的兩個就在裡面。' + solFin(o)];
  };

  L1_SOL.sumProdAcute = function (p, o) {
    if (p.kind === 0) {
      var s = solF(p.sum), pr = solF(p.ans.prod), df = solF(p.ans.diff);
      return ['兩邊平方：' + T('(\\sin\\theta+\\cos\\theta)^2=' + hxSq(Fr.tex(s, true)) + '=' + Fr.tex(Fr.mul(s, s))) + '，而左邊 $=\\sin^2\\theta+\\cos^2\\theta+2\\sin\\theta\\cos\\theta=1+2\\sin\\theta\\cos\\theta$。',
        '所以 ' + T('2\\sin\\theta\\cos\\theta=' + Fr.tex(Fr.sub(Fr.mul(s, s), F(1)))) + '，' + T('\\sin\\theta\\cos\\theta=' + Fr.tex(pr)) + '。',
        '再用 ' + T('(\\sin\\theta-\\cos\\theta)^2=1-2\\sin\\theta\\cos\\theta=' + Fr.tex(Fr.sub(F(1), Fr.mul(F(2), pr)))) + '，開根號得 ' + T('|\\sin\\theta-\\cos\\theta|=' + Fr.tex(df)) + '。' + solFin(o)];
    }
    if (p.kind === 1) {
      var d = solF(p.diff), pr1 = solF(p.ans.prod), sm1 = solF(p.ans.sum);
      return ['兩邊平方：' + T('(\\sin\\theta-\\cos\\theta)^2=' + hxSq(Fr.tex(d, true)) + '=' + Fr.tex(Fr.mul(d, d))) + '，而左邊 $=1-2\\sin\\theta\\cos\\theta$。',
        '移項得 ' + T('\\sin\\theta\\cos\\theta=' + Fr.tex(pr1)) + '。',
        '再用 ' + T('(\\sin\\theta+\\cos\\theta)^2=1+2\\sin\\theta\\cos\\theta=' + Fr.tex(Fr.add(F(1), Fr.mul(F(2), pr1)))) + '；銳角時 $\\sin\\theta$、$\\cos\\theta$ 都是正的，取正根得 ' + T('\\sin\\theta+\\cos\\theta=' + Fr.tex(sm1)) + '。' + solFin(o)];
    }
    var pr2 = solF(p.prod), sm2 = solF(p.ans.sum), df2 = solF(p.ans.diff);
    return ['把積代進平方關係：' + T('(\\sin\\theta+\\cos\\theta)^2=1+2\\times' + solPar(Fr.tex(pr2, true)) + '=' + Fr.tex(Fr.add(F(1), Fr.mul(F(2), pr2)))) + '。',
      '銳角 ⟹ 和為正，開根號得 ' + T('\\sin\\theta+\\cos\\theta=' + Fr.tex(sm2)) + '。',
      '同樣地 ' + T('(\\sin\\theta-\\cos\\theta)^2=1-2\\times' + solPar(Fr.tex(pr2, true)) + '=' + Fr.tex(Fr.sub(F(1), Fr.mul(F(2), pr2)))) + '，開根號得 ' + T('|\\sin\\theta-\\cos\\theta|=' + Fr.tex(df2)) + '。' + solFin(o)];
  };

  L1_SOL.coAngleSum = function (p, o) {
    if (p.kind === 2) {
      var d = p.d, m = 90 / d - 1;
      return ['互餘的正切互為倒數：' + T('\\tan\\theta\\cdot\\tan(90°-\\theta)=1') + '，例如 ' + T('\\tan' + d + '°\\cdot\\tan' + (90 - d) + '°=1') + '。',
        '本題從 $' + d + '°$ 到 $' + (m * d) + '°$ 共 $' + m + '$ 項（奇數項），頭尾兩兩配對後中間只剩 $\\tan45°=1$。',
        '每一對的乘積都是 $1$，所以整串乘積 $=1$。' + solFin(o)];
    }
    if (p.kind >= 3) {
      var pl = p.pairs.map(function (u) {
        return T(p.kind === 4 ? FN[u.fn] + u.a + '°\\cdot' + FN[u.fn] + (90 - u.a) + '°=1' : FN[u.fn] + '^2' + u.a + '°+' + FN[u.fn] + '^2' + (90 - u.a) + '°=1');
      }).join('、');
      return ['把和為 $90°$ 的角配成一對：' + pl + '。',
        '本題共 $' + p.n + '$ 對' + (p.kind === 4 ? '，每一對的乘積都是 $1$。' : '，每一對的平方和都是 $1$。'),
        (p.kind === 4 ? '$' + p.n + '$ 個 $1$ 相乘還是 $1$。' : '$' + p.n + '$ 個 $1$ 相加得 $' + p.n + '$。') + solFin(o)];
    }
    var dd = p.d, mm = 90 / dd - 1, fn = FN[p.fn], ans = solF(p.ans);
    var tot = (mm % 2) ? ((mm - 1) / 2) + '+\\dfrac12=' + Fr.tex(ans) : Fr.tex(ans);
    return ['互餘關係：' + T(fn + '^2\\theta+' + fn + '^2(90°-\\theta)=1') + '，例如 ' + T(fn + '^2' + dd + '°+' + fn + '^2' + (90 - dd) + '°=1') + '。',
      '本題從 $' + dd + '°$ 到 $' + (mm * dd) + '°$ 共 $' + mm + '$ 項' + ((mm % 2) ? '（奇數項）：頭尾配成 $' + ((mm - 1) / 2) + '$ 對，中間剩下 $' + fn + '^245°$，值是 $\\dfrac12$。' : '（偶數項）：剛好配成 $' + (mm / 2) + '$ 對。'),
      '總和 ' + T('=' + tot) + '。' + solFin(o)];
  };

  L1_SOL.elevOne = function (p, o) {
    var v = solS(p.ans), tn = sTex(tv(p.th).tan);
    if (p.kind === 0)
      return ['畫直角三角形：水平距離（鄰邊）$=' + p.d + '$，仰角 $' + p.th + '°$，塔高是對邊。',
        '鄰邊求對邊用正切：' + T('\\text{塔高}=' + p.d + '\\tan' + p.th + '°') + '，其中 ' + T('\\tan' + p.th + '°=' + tn) + '。',
        '算出 ' + T(sTex(v)) + ' 公尺。' + solFin(o)];
    return ['畫直角三角形：塔高（對邊）$=' + p.d + '$，仰角 $' + p.th + '°$，要求的是鄰邊。',
      '對邊求鄰邊把正切除回去：' + T('\\text{距離}=\\dfrac{' + p.d + '}{\\tan' + p.th + '°}') + '，其中 ' + T('\\tan' + p.th + '°=' + tn) + '。',
      '分母有根號要有理化，得 ' + T(sTex(v)) + ' 公尺。' + solFin(o)];
  };

  L1_SOL.elevTwo = function (p, o) {
    var rat = solF(p.ans.rat), surd = solS(p.ans.surd), both = p.kind === 2;
    var foot = p.kind === 0 ? '山腳' : '塔腳';
    var tl = p.th1 === p.th2 ? T('\\tan' + p.th1 + '°=' + sTex(tv(p.th1).tan))
                             : T('\\tan' + p.th1 + '°=' + sTex(tv(p.th1).tan)) + '、' + T('\\tan' + p.th2 + '°=' + sTex(tv(p.th2).tan));
    return ['設高為 $h$（甲的仰角是 $' + p.th1 + '°$、乙的仰角是 $' + p.th2 + '°$）：甲到' + foot + ' ' + T('=\\dfrac{h}{\\tan' + p.th1 + '°}') + '、乙到' + foot + ' ' + T('=\\dfrac{h}{\\tan' + p.th2 + '°}') + '。',
      (both ? '甲、乙在兩側 ⟹ 兩段相加等於 $' + p.w + '$：' : '甲、乙在同一側 ⟹ 兩段相差 $' + p.w + '$：') + T('\\dfrac{h}{\\tan' + p.th1 + '°}' + (both ? '+' : '-') + '\\dfrac{h}{\\tan' + p.th2 + '°}=' + p.w) + '。',
      '代入 ' + tl + ' 解 $h$（分母有根號要有理化），得 ' + T('h=' + hxTwo(rat, surd)) + ' 公尺。' + solFin(o)];
  };

  /* ── §2 廣義角與極坐標 ── */
  L1_SOL.coterminal = function (p, o) {
    var pos = p.ans.pos, neg = p.ans.neg, kk = (pos - p.th) / 360;
    var step = kk === 0 ? '' : p.th + (kk > 0 ? '+360' : '-360') + (Math.abs(kk) === 1 ? '' : '\\times' + Math.abs(kk));
    return [(kk === 0 ? T(p.th + '°') + ' 本來就落在 $0°\\sim360°$ 裡' : '加減 $360°$ 的整數倍把角搬進 $0°\\sim360°$：' + T(step + '=' + pos)) + '，所以最小正同界角是 ' + T(pos + '°') + '。',
      '最大負同界角 $=$ 最小正同界角 $-360°$：' + T(pos + '-360=' + neg) + '，即 ' + T(neg + '°') + '。',
      T(pos + '°') + ' 落在 ' + ['$0°\\sim90°$', '$90°\\sim180°$', '$180°\\sim270°$', '$270°\\sim360°$'][p.ans.quad - 1] + ' 之間，是第' + solQuad(p.ans.quad) + '象限角。' + solFin(o)];
  };

  L1_SOL.pointTrig = function (p, o) {
    var x = p.x, y = p.y, rt = sTex(S(1, x * x + y * y, 1));
    return ['點 ' + T('P(' + x + ',' + y + ')') + ' 在' + hxQuadXY(x, y) + '，先算 ' + T('r=\\sqrt{x^2+y^2}=\\sqrt{' + hxSq(String(x)) + '+' + hxSq(String(y)) + '}=' + rt) + '（$r$ 永遠取正）。',
      '代進定義：' + T('\\sin\\theta=\\dfrac yr=' + solEq('\\dfrac{' + y + '}{' + rt + '}', sTex(solS(p.ans.sin)))) + '、' + T('\\cos\\theta=\\dfrac xr=' + solEq('\\dfrac{' + x + '}{' + rt + '}', sTex(solS(p.ans.cos)))) + '。',
      T('\\tan\\theta=\\dfrac yx=' + solEq('\\dfrac{' + y + '}{' + x + '}', sTex(solS(p.ans.tan)))) + '；正負號和「點在' + hxQuadXY(x, y) + '」的判斷一致。' + solFin(o)];
  };

  L1_SOL.quadFind = function (p, o) {
    if (p.kind === 0) {
      var names = ['\\sin\\theta', '\\cos\\theta', '\\tan\\theta'];
      var zone = [['第一、二象限', '第三、四象限'], ['第一、四象限', '第二、三象限'], ['第一、三象限', '第二、四象限']];
      return [T(names[p.pair[0]] + (p.signs[0] > 0 ? '>0' : '<0')) + ' ⟹ 終邊落在' + zone[p.pair[0]][p.signs[0] > 0 ? 0 : 1] + '。',
        T(names[p.pair[1]] + (p.signs[1] > 0 ? '>0' : '<0')) + ' ⟹ 終邊落在' + zone[p.pair[1]][p.signs[1] > 0 ? 0 : 1] + '。',
        '兩個條件取交集，只剩第' + solQuad(p.ans) + '象限。' + solFin(o)];
    }
    var a = p.a, b = p.b, c = p.c, sg = { 2: [1, -1], 3: [-1, -1], 4: [-1, 1] }[p.quad];
    return ['在終邊上取一點，先不管正負用畢氏數 ' + T(a + ',' + b + ',' + c) + '，其中 ' + T('r=' + c) + '（永遠為正）。',
      '第' + solQuad(p.quad) + '象限 ⟹ ' + T('x=' + (sg[1] * b)) + '、' + T('y=' + (sg[0] * a)) + '。',
      '代進定義：' + T('\\sin\\theta=' + solEq('\\dfrac{' + (sg[0] * a) + '}{' + c + '}', Fr.tex(solF(p.ans.sin)))) + '、' + T('\\cos\\theta=' + solEq('\\dfrac{' + (sg[1] * b) + '}{' + c + '}', Fr.tex(solF(p.ans.cos)))) + '、' + T('\\tan\\theta=' + Fr.tex(solF(p.ans.tan))) + '，題目問的兩個就在裡面。' + solFin(o)];
  };

  L1_SOL.reduceEval = function (p, o) {
    var vals = [], seen = {}, parts = [];
    p.terms.forEach(function (t) {
      [[t.f1, t.a1], [t.f2, t.a2]].forEach(function (u) {
        var k = u[0] + '_' + u[1]; if (seen[k]) return; seen[k] = 1;
        vals.push(T(FN[u[0]] + hxA(u[1])) + '（同界角 ' + T((((u[1] % 360) + 360) % 360) + '°') + '，' + hxPos(u[1]) + '，參考角 ' + T(hxRef(u[1]) + '°') + '）$=' + sTex(tv(u[1])[u[0]]) + '$');
      });
      parts.push(sMulF(sMul(tv(t.a1)[t.f1], tv(t.a2)[t.f2]), F(t.sign)));
    });
    var expr = solSigned(parts);
    return ['每個角先化到 $0°\\sim360°$、由象限定正負、再用參考角查值：' + vals.join('；') + '。',
      '兩項各自相乘後是 ' + parts.map(function (w) { return T(sTex(w)); }).join(' 與 ') + '。',
      '同類根式合併：' + T(solEq(expr, sTex(solS(p.ans)))) + '。' + solFin(o)];
  };

  L1_SOL.polarConv = function (p, o) {
    if (p.kind === 0) {
      var cs = tv(p.th).cos, sn = tv(p.th).sin;
      return ['$' + p.th + '°$ 在' + hxPos(p.th) + '，參考角 $' + hxRef(p.th) + '°$ ⟹ ' + T('\\cos' + p.th + '°=' + sTex(cs)) + '、' + T('\\sin' + p.th + '°=' + sTex(sn)) + '。',
        '代公式：' + T('x=r\\cos\\theta=' + p.r + '\\cdot' + solPar(sTex(cs)) + '=' + sTex(solS(p.ans.x))) + '、' + T('y=r\\sin\\theta=' + p.r + '\\cdot' + solPar(sTex(sn)) + '=' + sTex(solS(p.ans.y))) + '。',
        '所以直角坐標是 ' + T('(' + sTex(solS(p.ans.x)) + ',\\ ' + sTex(solS(p.ans.y)) + ')') + '。' + solFin(o)];
    }
    var X = solS(p.x), Y = solS(p.y), rS = solS(p.ans.r), axis = (X.c === 0 || Y.c === 0);
    var line1 = axis ? '點落在坐標軸上，$r$ 就是它到原點的距離 ' + T('=' + sTex(rS))
                     : '先算 ' + T('r=\\sqrt{x^2+y^2}=\\sqrt{' + hxSq(sTex(X)) + '+' + hxSq(sTex(Y)) + '}=' + sTex(rS)) + '（$r$ 取正）';
    return [line1 + '。',
      '再看 ' + T('x=' + sTex(X)) + '、' + T('y=' + sTex(Y)) + ' 的正負決定終邊的位置，配上參考角定出 ' + T('\\theta=' + p.ans.th + '°') + '（要落在 $0°\\le\\theta<360°$）。',
      '所以極坐標是 ' + T('[' + sTex(rS) + ',\\ ' + p.ans.th + '°]') + '。' + solFin(o)];
  };

  L1_SOL.polarDist = function (p, o) {
    var gap = p.ans.gap, area = solS(p.ans.area);
    return ['夾角就是兩個極角的差：' + T('|' + p.th1 + '-' + p.th2 + '|') + '（超過 $180°$ 就用 $360°$ 減）$=' + gap + '°$。',
      '餘弦定理：' + T(ov('AB') + '^2=' + p.r1 + '^2+' + p.r2 + '^2-' + hxMul([2, p.r1, p.r2]) + '\\cos' + gap + '°=' + p.ans.d2) + '，所以 ' + T(ov('AB') + '=' + sqrtTex(p.ans.d2)) + '。',
      '兩邊夾角的面積公式（兩條極徑就是兩邊、夾角已經算出來了）：' + T('\\dfrac12\\cdot' + hxMul([p.r1, p.r2]) + '\\sin' + gap + '°=' + sTex(area)) + '。' + solFin(o)];
  };

  L1_SOL.slopeAngle = function (p, o) {
    if (p.kind === 0)
      return ['把直線整理成 $y=mx+k$，讀出斜率 ' + T('m=' + sTex(tv(p.ang).tan)) + '。',
        '斜角 $\\alpha$ 滿足 $\\tan\\alpha=m$ 且 $-90°\\lt\\alpha\\le90°$' + (p.ang < 0 ? '；斜率是負的 ⟹ 斜角是負的' : '') + '。',
        '所以斜角是 ' + T(p.ang + '°') + '。' + solFin(o)];
    if (p.kind === 1) {
      var dif = Math.abs(p.a1 - p.a2);
      return ['兩條線的斜角分別是 ' + T(p.a1 + '°') + ' 與 ' + T(p.a2 + '°') + '。',
        '兩斜角相減：' + T('|' + p.a1 + '-' + p.a2 + '|=' + dif + '°') + (dif > 90 ? '，超過 $90°$ ⟹ 改用 ' + T('180°-' + dif + '°=' + p.ans + '°') : '') + '。',
        '所以銳夾角（或直角）是 ' + T(p.ans + '°') + '。' + solFin(o)];
    }
    return ['斜率 ' + T('m=\\tan' + angT(p.ang) + '=' + sTex(tv(p.ang).tan)) + '。',
      '點斜式：' + T('y-(' + p.py + ')=m(x-(' + p.px + '))') + '。',
      '兩邊乘開、把係數整理成整數，得一般式 ' + T(p.ans.tex) + '。' + solFin(o)];
  };

  /* ── §3 正弦定理與餘弦定理 ── */
  L1_SOL.sineLaw = function (p, o) {
    return ['內角和：' + T('\\angle C=180°-' + p.A + '°-' + p.B + '°=' + p.ans.C + '°') + '。',
      '正弦定理 $\\dfrac{a}{\\sin A}=\\dfrac{b}{\\sin B}$ ⟹ ' + T('b=\\dfrac{a\\sin B}{\\sin A}=\\dfrac{' + p.a + '\\sin' + p.B + '°}{\\sin' + p.A + '°}') + '。',
      '代入 ' + T('\\sin' + p.A + '°=' + sTex(tv(p.A).sin)) + '、' + T('\\sin' + p.B + '°=' + sTex(tv(p.B).sin)) + '，有理化後得 ' + T('b=' + sTex(solS(p.ans.b))) + '。' + solFin(o)];
  };

  L1_SOL.circumR = function (p, o) {
    if (p.kind === 0)
      return ['正弦定理的比值就是直徑：$\\dfrac{a}{\\sin A}=2R$ ⟹ ' + T('R=\\dfrac{a}{2\\sin A}=\\dfrac{' + p.a + '}{2\\sin' + p.A + '°}') + '。',
        '代入 ' + T('\\sin' + p.A + '°=' + sTex(tv(p.A).sin)) + '，把分母的根號有理化，得 ' + T('R=' + sTex(solS(p.ans))) + '。' + solFin(o)];
    return ['正弦定理的另一個寫法：$b=2R\\sin B$ ⟹ ' + T('\\sin B=\\dfrac{b}{2R}=\\dfrac{' + p.b + '}{2\\times' + p.R + '}=' + Fr.tex(solF(p.ans.sinB))) + '。',
      '這個值比 $1$ 小；銳角與它的補角有相同的正弦值 ⟹ $\\angle B$ 有兩種可能（一銳角一鈍角，互補）。' + solFin(o)];
  };

  L1_SOL.cosLawSide = function (p, o) {
    var cv = p.A === 60 ? '\\dfrac12' : p.A === 90 ? '0' : '-\\dfrac12';
    return ['兩邊夾角求第三邊，用餘弦定理：' + T('a^2=b^2+c^2-2bc\\cos A=' + p.b + '^2+' + p.c + '^2-' + hxMul([2, p.b, p.c]) + '\\cos' + p.A + '°') + '。',
      '代入 ' + T('\\cos' + p.A + '°=' + cv) + '，得 ' + T('a^2=' + p.ans.a2) + '。',
      '開根號並化到最簡：' + T('a=' + sqrtTex(p.ans.a2)) + '。' + solFin(o)];
  };

  L1_SOL.cosLawAngle = function (p, o) {
    var arr = [p.a, p.b, p.c], m = Math.max(p.a, p.b, p.c);
    var ot = arr.filter(function (v, i) { return i !== arr.indexOf(m); }), cs = solF(p.ans.cos);
    return ['最大角一定對最大邊 ' + T(String(m)) + '，另外兩邊是 ' + T(String(ot[0])) + '、' + T(String(ot[1])) + '。',
      '餘弦定理：' + T('\\cos=\\dfrac{' + ot[0] + '^2+' + ot[1] + '^2-' + m + '^2}{' + hxMul([2, ot[0], ot[1]]) + '}=' + Fr.tex(cs)) + '。',
      '餘弦值' + (cs.n > 0 ? '為正 ⟹ 最大角是銳角 ⟹ 銳角三角形' : cs.n === 0 ? '為零 ⟹ 最大角是直角 ⟹ 直角三角形' : '為負 ⟹ 最大角是鈍角 ⟹ 鈍角三角形') + '。' + solFin(o)];
  };

  L1_SOL.sideRange = function (p, o) {
    var b = p.b, c = p.c, big = Math.max(b, c), sm = Math.min(b, c);
    return ['(1) 兩邊之差 $<a<$ 兩邊之和：' + T(p.ans.lo + '<a<' + p.ans.hi) + '。',
      '(2) 鈍角三角形分兩種：$a$ 是最大邊時 $a^2>' + b + '^2+' + c + '^2$ ⟹ ' + T('a>' + sqrtTex(p.ans.s2)) + '；$' + big + '$ 是最大邊時 $' + big + '^2>a^2+' + sm + '^2$ ⟹ ' + T('a<' + sqrtTex(p.ans.s1)) + '。',
      '與 (1) 取交集：' + T(p.ans.lo + '<a<' + sqrtTex(p.ans.s1)) + ' 或 ' + T(sqrtTex(p.ans.s2) + '<a<' + p.ans.hi) + '。' + solFin(o)];
  };

  L1_SOL.ssaCount = function (p, o) {
    if (p.A >= 90)
      return ['$\\angle A=' + p.A + '°$ 是鈍角 ⟹ 它的對邊 $a$ 一定要是最大邊，也就是要 ' + T('a>' + p.b) + '。',
        '本題 ' + T('a=' + p.a) + (p.a > p.b ? '，確實大於 $' + p.b + '$ ⟹ 恰有 ' : '，並沒有大於 $' + p.b + '$ ⟹ 有 ') + T(String(p.ans)) + ' 組解。' + solFin(o)];
    var hh = sMulF(tv(p.A).sin, F(p.b)), hv = sNum(hh);
    var word = Math.abs(p.a - hv) < 1e-9 ? '恰好等於 $h$（垂足落在邊上，是直角）' : p.a < hv ? '比 $h$ 還小（畫不出來）' : p.a < p.b ? '介於 $h$ 與 $' + p.b + '$ 之間' : '不小於 $' + p.b + '$';
    return ['先算「高」' + T('h=' + p.b + '\\sin' + p.A + '°=' + sTex(hh)) + '，這是對邊 $a$ 能達到的最短長度。',
      '判準：$a<h$ 無解、$a=h$ 一解（直角）、$h<a<' + p.b + '$ 兩解、$a\\ge' + p.b + '$ 一解。',
      '本題 ' + T('a=' + p.a) + '，' + word + ' ⟹ ' + T(String(p.ans)) + ' 組解。' + solFin(o)];
  };

  /* ── §4 面積與三角形的線段 ── */
  L1_SOL.areaSAS = function (p, o) {
    if (p.kind === 0)
      return ['兩邊夾角 ⟹ 面積 ' + T('=\\dfrac12ab\\sin C=\\dfrac12\\cdot' + hxMul([p.a, p.b]) + '\\sin' + p.C + '°') + '。',
        '代入 ' + T('\\sin' + p.C + '°=' + sTex(tv(p.C).sin)) + '（鈍角的正弦仍為正），得面積 ' + T(sTex(solS(p.ans))) + '。' + solFin(o)];
    var K2 = solF(p.K), sC = Fr.div(Fr.mul(F(2), K2), F(p.a * p.b));
    return ['由面積公式 ' + T('\\dfrac12\\cdot' + hxMul([p.a, p.b]) + '\\sin C=' + Fr.tex(K2)) + ' 解出 ' + T('\\sin C=' + Fr.tex(sC)) + '。',
      (Fr.eq(sC, F(1)) ? '$\\sin C=1$ 只有一個解：' : '$\\sin C<1$ ⟹ 銳角與它的補角都可以：') + T('\\angle C=' + p.ans.join('°\\ \\text{或}\\ ') + '°') + '。' + solFin(o)];
  };

  L1_SOL.heronArea = function (p, o) {
    var s = F(p.a + p.b + p.c, 2);
    return ['海龍公式先算半周長 ' + T('s=\\dfrac{' + p.a + '+' + p.b + '+' + p.c + '}{2}=' + Fr.tex(s)) + '。',
      '三個差：' + T('s-a=' + Fr.tex(Fr.sub(s, F(p.a)))) + '、' + T('s-b=' + Fr.tex(Fr.sub(s, F(p.b)))) + '、' + T('s-c=' + Fr.tex(Fr.sub(s, F(p.c)))) + '。',
      '面積 ' + T('=\\sqrt{s(s-a)(s-b)(s-c)}=' + sTex(solS(p.ans))) + '。' + solFin(o)];
  };

  L1_SOL.inOutRadius = function (p, o) {
    var s = F(p.a + p.b + p.c, 2);
    return ['(1) 半周長 ' + T('s=\\dfrac{' + p.a + '+' + p.b + '+' + p.c + '}{2}=' + Fr.tex(s)) + '，海龍公式得面積 ' + T('K=\\sqrt{s(s-a)(s-b)(s-c)}=' + sTex(solS(p.ans.K))) + '。',
      '(2) 內切圓半徑 ' + T('r=\\dfrac Ks=' + sTex(solS(p.ans.r))) + '（分母有根號要有理化）。',
      '(3) 外接圓半徑 ' + T('R=\\dfrac{abc}{4K}=\\dfrac{' + (p.a * p.b * p.c) + '}{4K}=' + sTex(solS(p.ans.R))) + '。' + solFin(o)];
  };

  L1_SOL.medianLen = function (p, o) {
    var m2 = F(2 * p.b * p.b + 2 * p.c * p.c - p.a * p.a, 4);
    return ['中線長公式：' + T('\\overline{AM}^2=\\dfrac{2\\overline{AB}^2+2\\overline{AC}^2-\\overline{BC}^2}{4}') + '。',
      '代入本題：' + T('\\overline{AM}^2=\\dfrac{2\\cdot' + p.c + '^2+2\\cdot' + p.b + '^2-' + p.a + '^2}{4}=' + Fr.tex(m2)) + '。',
      '開根號：' + T('\\overline{AM}=' + sTex(solS(p.ans))) + '。' + solFin(o)];
  };

  L1_SOL.bisectorLen = function (p, o) {
    var b = p.b, c = p.c, gR = gcd(b, c);
    return ['角平分線把對邊分成兩鄰邊之比：' + T(ov('BD') + ':' + ov('DC') + '=' + ov('AB') + ':' + ov('AC') + '=' + c + ':' + b + '=' + (c / gR) + ':' + (b / gR)) + '。',
      '長度用「面積切兩半」：' + T('\\dfrac12\\cdot' + hxMul([b, c]) + '\\sin' + p.A + '°=\\dfrac12\\overline{AD}\\,(' + b + '+' + c + ')\\sin' + (p.A / 2) + '°') + '。',
      '代入 ' + T('\\sin' + p.A + '°=' + sTex(tv(p.A).sin)) + '、' + T('\\sin' + (p.A / 2) + '°=' + sTex(tv(p.A / 2).sin)) + ' 解出 ' + T(ov('AD') + '=' + sTex(solS(p.ans.AD))) + '。' + solFin(o)];
  };

  L1_SOL.cyclicQuad = function (p, o) {
    var cB = solF(p.ans.cosB), AC2 = solF(p.ans.AC2);
    return ['圓內接四邊形的對角互補 ⟹ $\\cos D=-\\cos B$。',
      '同一條 $\\overline{AC}$ 算兩次：' + T(ov('AC') + '^2=' + p.a + '^2+' + p.b + '^2-' + hxMul([2, p.a, p.b]) + '\\cos B') + '（在 $\\triangle ABC$）與 ' + T(ov('AC') + '^2=' + p.c + '^2+' + p.d + '^2+' + hxMul([2, p.c, p.d]) + '\\cos B') + '（在 $\\triangle ACD$），兩式相等。',
      '解得 ' + T('\\cos B=' + Fr.tex(cB)) + '，代回去得 ' + T(ov('AC') + '^2=' + Fr.tex(AC2)) + '，開根號 ' + T(ov('AC') + '=' + sTex(sqrtF(AC2))) + '。' + solFin(o)];
  };

  /* ── §5 正射影與立體測量 ── */
  L1_SOL.projLen = function (p, o) {
    if (p.kind === 0) {
      var ref = p.th > 90 ? 180 - p.th : p.th;
      return ['正射影長 $=\\overline{AB}\\cdot|\\cos\\theta|$，本題 ' + T('=' + p.L + '|\\cos' + p.th + '°|') + '。',
        (p.th > 90 ? '夾角是鈍角，改用它的補角 ' + T((180 - p.th) + '°') + '：' : '') + T('|\\cos' + p.th + '°|=' + sTex(tv(ref).cos)) + '。',
        '相乘得正射影長 ' + T(sTex(solS(p.ans))) + '（長度永遠是正的）。' + solFin(o)];
    }
    return ['梯子在地面上的正射影就是梯腳到牆的距離：' + T('L\\cos\\theta=' + p.L + '\\cos' + p.th + '°=' + sTex(solS(p.ans.x))) + ' 公尺。',
      '梯子在牆上的正射影就是梯頂離地的高度：' + T('L\\sin\\theta=' + p.L + '\\sin' + p.th + '°=' + sTex(solS(p.ans.y))) + ' 公尺。' + solFin(o)];
  };

  L1_SOL.projTheorem = function (p, o) {
    var cB = solF(p.ans.cosB), cC = solF(p.ans.cosC);
    return ['餘弦定理算 $\\cos B$：' + T('\\cos B=\\dfrac{a^2+c^2-b^2}{2ac}=\\dfrac{' + p.a + '^2+' + p.c + '^2-' + p.b + '^2}{' + hxMul([2, p.a, p.c]) + '}=' + Fr.tex(cB)) + '。',
      '同樣算 $\\cos C$：' + T('\\cos C=\\dfrac{a^2+b^2-c^2}{2ab}=\\dfrac{' + p.a + '^2+' + p.b + '^2-' + p.c + '^2}{' + hxMul([2, p.a, p.b]) + '}=' + Fr.tex(cC)) + '。',
      '驗證投影定理：' + T('b\\cos C+c\\cos B=' + p.b + '\\times' + solPar(Fr.tex(cC, true)) + '+' + p.c + '\\times' + solPar(Fr.tex(cB, true)) + '=' + p.a) + '，剛好是 $a$。' + solFin(o)];
  };

  L1_SOL.cuboid = function (p, o) {
    var fname = p.face === 0 ? '底面 $ABCD$' : '側面 $ABFE$', edge = p.face === 0 ? p.h : p.q;
    var projTex = p.face === 0 ? ov('AC') + '=\\sqrt{' + p.p + '^2+' + p.q + '^2}=' + sqrtTex(p.ans.near) : '\\sqrt{' + p.p + '^2+' + p.h + '^2}=' + sqrtTex(p.ans.near);
    return ['先算 $\\overline{AG}$ 在' + fname + ' 上的投影長：' + T(projTex) + '。',
      '體對角線 ' + T(ov('AG') + '=\\sqrt{' + p.p + '^2+' + p.q + '^2+' + p.h + '^2}=' + p.ans.D) + '。',
      '$\\theta$ 落在一個直角三角形裡：對邊（垂直於' + fname + ' 的稜）' + T('=' + edge) + '、鄰邊（投影長）' + T('=' + sqrtTex(p.ans.near)) + '、斜邊 ' + T('=' + p.ans.D) + ' ⟹ ' + T('\\sin\\theta=' + Fr.tex(solF(p.ans.sin))) + '、' + T('\\cos\\theta=' + sTex(solS(p.ans.cos))) + '、' + T('\\tan\\theta=' + sTex(solS(p.ans.tan))) + '。' + solFin(o)];
  };

  L1_SOL.pyramid = function (p, o) {
    var s = p.s, h = p.h, l = p.l, e2 = p.e2;
    var st = ['(1) 體高：在「體高、半對角線 $' + s + '\\sqrt2$、側稜 $' + sqrtTex(e2) + '$」的直角三角形裡，' + T('h=\\sqrt{' + e2 + '-2\\cdot' + s + '^2}=' + h) + '。',
      '(2) 斜高：在「體高 $' + h + '$、半邊長 $' + s + '$、斜高」的直角三角形裡，' + T('\\sqrt{' + h + '^2+' + s + '^2}=' + l) + '。'];
    if (p.kind === 0)
      st.push('(3) 側面與底面的夾角在第二個三角形裡：' + T('\\tan=' + solEq('\\dfrac{' + h + '}{' + s + '}', Fr.tex(solF(p.ans.tan)))) + '；(4) 側稜與底面的夾角在第一個三角形裡：' + T('\\cos=\\dfrac{' + s + '\\sqrt2}{' + sqrtTex(e2) + '}=' + sTex(solS(p.ans.cos))) + '。' + solFin(o));
    else
      st.push('(3) 體積 ' + T('=\\dfrac13\\cdot' + (2 * s) + '^2\\cdot' + h + '=' + Fr.tex(solF(p.ans.vol))) + '；(4) 側面積（底是底邊、高是斜高）' + T('=4\\cdot\\dfrac12\\cdot' + (2 * s) + '\\cdot' + l + '=' + p.ans.side) + '。' + solFin(o));
    return st;
  };

  /* ── 2026-09-28 擴充：新 L1 五型的第一層提示與解題步驟 ── */
  L1_H1.rightSolve = '這是「直角三角形：已知一個三角比與一邊」：先把三角比翻成三邊的比，再看已知的那一邊是比例的幾倍。';
  L1_H1.tanHomog = '這是「已知正切求齊次式」：分子分母同除以餘弦（或先除以一再同除以餘弦的平方），整個式子就只剩正切。';
  L1_H1.trigCompare = '這是「三角比比大小」：每個值先看正負，同號的再換成參考角（銳角）的三角比比大小。';
  L1_H1.polarSym = '這是「對稱點、旋轉點的極坐標」：先看新點和原來的點是什麼關係（對稱或旋轉），極角就跟著那樣變，半徑不變或按比例放大。';
  L1_H1.quadDiagArea = '這是「四邊形面積」：兩條對角線把四邊形切成四個小三角形，面積合起來是兩條對角線乘積的一半再乘夾角的正弦。';

  L1_SOL.rightSolve = function (p, o) {
    var a = p.a, b = p.b, c = p.c, m = p.m;
    if (p.t === 0) {
      var names = ['BC', 'AC', 'AB'], base = [a, b, c], v = [p.ans.BC, p.ans.AC, p.ans.AB], ratio = p.fn === 'sin' ? F(a, c) : p.fn === 'cos' ? F(b, c) : F(a, b);
      var two = p.fn === 'sin' ? ['BC', 'AB', a, c] : p.fn === 'cos' ? ['AC', 'AB', b, c] : ['BC', 'AC', a, b];
      var oth = [0, 1, 2].filter(function (i) { return i !== p.side; });
      return ['$\\angle C=90°$，' + T('\\' + p.fn + ' A=' + Fr.tex(ratio)) + ' 表示 ' + T(ov(two[0]) + ':' + ov(two[1]) + '=' + two[2] + ':' + two[3]) + '，可以設三邊是比例的 $k$ 倍。',
        '畢氏定理補第三個數：' + T(ov('BC') + ':' + ov('AC') + ':' + ov('AB') + '=' + a + ':' + b + ':' + c) + '。',
        '已知 ' + T(ov(names[p.side]) + '=' + v[p.side] + '=' + base[p.side] + 'k') + ' ⟹ $k=' + m + '$，所以 ' + T(ov(names[oth[0]]) + '=' + v[oth[0]]) + '、' + T(ov(names[oth[1]]) + '=' + v[oth[1]]) + '，周長 ' + T('=' + v[0] + '+' + v[1] + '+' + v[2] + '=' + p.ans.per) + '。' + solFin(o)];
    }
    var AB = m * a, AC = m * b, BC = m * c, rB = p.fnB === 'sin' ? F(b, c) : p.fnB === 'cos' ? F(a, c) : F(b, a);
    var gN = ['AB', 'AC', 'BC'][p.gs], gV = [AB, AC, BC][p.gs], BD = solF(p.ans.BD);
    var last = p.ask === 0 ? '$\\triangle ABD$ 中 $\\angle ADB=90°$：' + T(ov('AD') + '=' + ov('AB') + '\\sin B=' + AB + '\\cdot' + Fr.tex(F(b, c)) + '=' + Fr.tex(solF(p.ans.AD))) + '。'
             : p.ask === 1 ? '$\\triangle ABD$ 中 $\\angle ADB=90°$：' + T(ov('BD') + '=' + ov('AB') + '\\cos B=' + AB + '\\cdot' + Fr.tex(F(a, c)) + '=' + Fr.tex(BD)) + '。'
                           : '$\\triangle ABD$ 中 $\\angle ADB=90°$：' + T(ov('BD') + '=' + ov('AB') + '\\cos B=' + AB + '\\cdot' + Fr.tex(F(a, c)) + '=' + Fr.tex(BD)) + '，所以 ' + T(ov('CD') + '=' + ov('BC') + '-' + ov('BD') + '=' + BC + '-' + Fr.tex(BD) + '=' + Fr.tex(solF(p.ans.CD))) + '。';
    return ['$\\angle A=90°$，斜邊是 $\\overline{BC}$。' + T('\\' + p.fnB + ' B=' + Fr.tex(rB)) + ' ⟹ ' + T(ov('AB') + ':' + ov('AC') + ':' + ov('BC') + '=' + a + ':' + b + ':' + c) + '（畢氏定理補第三個數）。',
      '由 ' + T(ov(gN) + '=' + gV) + ' 得 ' + T(ov('AB') + '=' + AB) + '、' + T(ov('AC') + '=' + AC) + '、' + T(ov('BC') + '=' + BC) + '。',
      last + solFin(o)];
  };

  L1_SOL.tanHomog = function (p, o) {
    var m = solF(p.m), TN = '\\tan\\theta', co = p.co;
    if (p.t === 1)
      return ['先除以 ' + T('\\sin^2\\theta+\\cos^2\\theta=1') + '（值不變），把式子寫成分式：' + T('\\dfrac{' + n28lin([[co[0], '\\sin^2\\theta'], [co[1], '\\sin\\theta\\cos\\theta'], [co[2], '\\cos^2\\theta']]) + '}{\\sin^2\\theta+\\cos^2\\theta}') + '。',
        '分子分母同除以 $\\cos^2\\theta$：' + T('\\dfrac{' + n28lin([[co[0], '\\tan^2\\theta'], [co[1], TN], [co[2], '']]) + '}{\\tan^2\\theta+1}') + '。',
        '代 ' + T(TN + '=' + Fr.tex(m)) + '：分子 ' + T('=' + Fr.tex(solF(p.num))) + '、分母 ' + T('=' + Fr.tex(solF(p.den))) + '，相除得 ' + T(Fr.tex(solF(p.ans))) + '。' + solFin(o)];
    var topT = n28lin([[co[0], TN], [co[1], '']]), botT = n28lin([[co[2], TN], [co[3], '']]);
    if (p.t === 0)
      return ['$\\tan\\theta$ 存在，所以 $\\cos\\theta\\ne0$，分子分母可以同除以 $\\cos\\theta$。',
        '得 ' + T('\\dfrac{' + topT + '}{' + botT + '}') + '（' + T('\\dfrac{\\sin\\theta}{\\cos\\theta}=\\tan\\theta') + '）。',
        '代 ' + T(TN + '=' + Fr.tex(m)) + '：分子 ' + T('=' + Fr.tex(solF(p.num))) + '、分母 ' + T('=' + Fr.tex(solF(p.den))) + '，相除得 ' + T(Fr.tex(solF(p.ans))) + '。' + solFin(o)];
    var v = solF(p.v), vt = Fr.tex(v);
    return ['左邊分子分母同除以 $\\cos\\theta$：' + T('\\dfrac{' + topT + '}{' + botT + '}=' + vt) + '。',
      '交叉相乘：' + T(topT + '=' + (v.n === v.d ? '' : v.n === -v.d ? '-' : vt) + '\\left(' + botT + '\\right)') + '，把 $\\tan\\theta$ 移到同一邊：' + T(n28fc(solF(p.A), TN) + '=' + Fr.tex(solF(p.B))) + '。',
      '所以 ' + T(TN + '=' + Fr.tex(m)) + '。' + solFin(o)];
  };

  L1_SOL.trigCompare = function (p, o) {
    var ord = p.ans.join('\\lt ');
    if (p.t === 0) {
      var al = p.al, sg = ['sin', 'cos', 'tan'].map(function (f) { return n28val(f, al) > 0 ? '正' : '負'; });
      return [T(hxA(al)) + ' 的終邊在' + hxPos(al) + '，參考角 $' + p.ref + '°$，所以 $\\sin$ 為' + sg[0] + '、$\\cos$ 為' + sg[1] + '、$\\tan$ 為' + sg[2] + '。',
        p.ref > 45 ? '參考角大於 $45°$：$|\\sin|\\gt|\\cos|$；又 $|\\tan|=\\dfrac{|\\sin|}{|\\cos|}\\gt1$，比 $|\\sin|$、$|\\cos|$ 都大。' : '參考角小於 $45°$：$|\\cos|\\gt|\\sin|$；又 $|\\tan|=\\dfrac{|\\sin|}{|\\cos|}\\gt|\\sin|$（除以小於 $1$ 的正數會變大）。',
        '正的比負的大；兩個負的，絕對值大的反而小。所以 ' + T(ord) + '。' + solFin(o)];
    }
    var fn = p.fn, conv = p.angs.map(function (d) {
      var ref = hxRef(d), v = n28val(fn, d);
      return T(FN[fn] + hxA(d) + (d === ref ? '' : '=' + (v > 0 ? '' : '-') + FN[fn] + ref + '°'));
    });
    return ['每個角都化成參考角，正負看象限：' + conv.join('、') + '。',
      '參考角都在 $0°$ 到 $90°$ 之間：' + (fn === 'cos' ? '$\\cos$ 角度越大值越小' : '$' + FN[fn] + '$ 角度越大值越大') + '（看單位圓）。',
      '先分正負，再比同號的大小：' + T(ord) + '。' + solFin(o)];
  };

  L1_SOL.polarSym = function (p, o) {
    var TRk = N28TR[p.k], X = p.ans[0], Y = p.ans[1], sr = p.s * p.r, Q = TRk.f(p.x, p.y);
    var idt = T('\\cos(' + TRk.e + ')=' + TRk.c) + '、' + T('\\sin(' + TRk.e + ')=' + TRk.s);
    if (p.t === 0)
      return [T(ov('OQ') + '=\\sqrt{' + hxSq(X) + '+' + hxSq(Y) + '}=' + sr) + '，所以 $Q$ 的極坐標第一個數是 $' + sr + '$。',
        '比坐標：' + (p.s > 1 ? '$Q$ 的坐標除以 $' + p.s + '$ 是 ' + T(n28pt(Q[0], Q[1])) + '，' : '') + '$P' + n28pt(p.x, p.y) + '$ 到 ' + T(n28pt(Q[0], Q[1])) + ' 是' + TRk.w + '。',
        '所以極角是 $' + TRk.e + '$，驗算：' + idt + '，代 ' + T('\\cos\\theta=' + Fr.tex(F(p.x, p.r)) + ',\\ \\sin\\theta=' + Fr.tex(F(p.y, p.r))) + ' 會回到 $Q$。' + solFin(o)];
    return ['極坐標 ' + T('[' + sr + ',' + TRk.e + ']') + ' 的直角坐標是 ' + T('\\left(' + sr + '\\cos(' + TRk.e + '),\\ ' + sr + '\\sin(' + TRk.e + ')\\right)') + '。',
      '誘導公式：' + idt + '；由 $P$ 得 ' + T('\\cos\\theta=' + Fr.tex(F(p.x, p.r)) + ',\\ \\sin\\theta=' + Fr.tex(F(p.y, p.r))) + '。',
      '代入得 ' + T(n28pt(X, Y)) + '（它是 $P$ ' + TRk.w + (p.s > 1 ? '，再放大 $' + p.s + '$ 倍' : '') + '）。' + solFin(o)];
  };

  L1_SOL.quadDiagArea = function (p, o) {
    var st = ['設兩條對角線交於 $O$，夾角 $\\theta$。四個小三角形都用「兩邊夾角」算面積，夾角是 $\\theta$ 或 $180°-\\theta$，正弦一樣。',
      '四塊相加：' + T('[ABCD]=\\dfrac12(\\overline{OA}+\\overline{OC})(\\overline{OB}+\\overline{OD})\\sin\\theta=\\dfrac12\\cdot' + ov('AC') + '\\cdot' + ov('BD') + '\\sin\\theta') + '。'];
    if (p.t === 0) st.push('代入：' + T('\\dfrac12\\cdot' + p.p + '\\cdot' + p.q + (p.phi === 90 ? '' : '\\cdot' + sTex(tv(p.phi).sin)) + '=' + sTex(solS(p.ans))) + '。' + solFin(o));
    else if (p.t === 1) st.push('代入：' + T(sTex(solS(p.K)) + '=\\dfrac12\\cdot' + p.p + '\\cdot' + ov('BD') + (p.phi === 90 ? '' : '\\cdot' + sTex(tv(p.phi).sin))) + '，解出 ' + T(ov('BD') + '=' + p.ans) + '。' + solFin(o));
    else st.push('代入：' + T(sTex(solS(p.K)) + '=\\dfrac12\\cdot' + p.p + '\\cdot' + p.q + '\\sin\\theta') + ' ⟹ ' + T('\\sin\\theta=' + sTex(tv(p.ans).sin)) + '，銳角（或直角）是 $' + p.ans + '°$。' + solFin(o));
    return st;
  };

  var META_L1 = [
      ['triDef', '§1 三角比的定義'], ['specialEval', '§1 特殊角求值'], ['sinToCos', '§1 同角關係：知一求二'], ['sumProdAcute', '§1 對稱式 sin±cos 與 sincos'], ['coAngleSum', '§1 餘角關係：整串求和／求積'], ['elevOne', '§1 仰角測高：一次測量'], ['elevTwo', '§1 仰角測高：兩次測量'], ['rightSolve', '§1 直角三角形：已知三角比與一邊求其他邊'], ['tanHomog', '§1 已知 tanθ 求 sin、cos 的齊次式'],
      ['coterminal', '§2 同界角與象限'], ['pointTrig', '§2 終邊上一點求三角比'], ['quadFind', '§2 象限判定與符號'], ['reduceEval', '§2 廣義角的特殊值'], ['polarConv', '§2 極坐標與直角坐標互換'], ['polarDist', '§2 極坐標下的距離與面積'], ['slopeAngle', '§2 斜角、斜率與夾角'], ['trigCompare', '§2 廣義角三角比比大小'], ['polarSym', '§2 對稱點、旋轉點的極坐標'],
      ['sineLaw', '§3 正弦定理求邊'], ['circumR', '§3 外接圓半徑'], ['cosLawSide', '§3 餘弦定理求邊（SAS）'], ['cosLawAngle', '§3 餘弦定理求角（SSS）與形狀'], ['sideRange', '§3 三角形存在條件與鈍角範圍'], ['ssaCount', '§3 SSA 有幾組解'],
      ['areaSAS', '§4 面積公式與已知面積求角'], ['heronArea', '§4 海龍公式'], ['inOutRadius', '§4 內切圓與外接圓半徑'], ['medianLen', '§4 中線長'], ['bisectorLen', '§4 角平分線'], ['cyclicQuad', '§4 圓內接四邊形'], ['quadDiagArea', '§4 四邊形面積：對角線與夾角'],
      ['projLen', '§5 正射影'], ['projTheorem', '§5 投影定理'], ['cuboid', '§5 長方體的立體測量'], ['pyramid', '§5 正四角錐']
  ];
  var META_L2 = [
      ['quadSumProd', '§2 廣義角的同角關係（象限定號）'], ['reduceSimplify', '§2 誘導公式化簡'], ['polarTriangle', '§2 三個極坐標點的三角形'], ['lineAngle', '§2 與已知直線夾特殊角的直線'], ['sinCount', '§2 範圍內三角方程的解數'], ['reduceK', '§2 以 k 表示廣義角的三角比'], ['trigQuadEq', '§2 平方關係化成二次方程'],
      ['sineRatio', '§3 sin 比⟹邊比：形狀與面積'], ['cevianLen', '§3 D 在 BC 上：補角餘弦串連'], ['ssaSolve', '§3 SSA 兩解求第三邊'], ['shapeJudge', '§3 由邊角關係判定形狀'], ['uniqueTri', '§3 哪些條件決定唯一的三角形'], ['chordSineRatio', '§3 弦長＝2R sin：共弦兩圓與同圓的弦'],
      ['heronFull', '§4 三邊全知：K、r、R、高'], ['heightsHeron', '§4 三高／sin 比＋內切圓⟹R'], ['cyclicQuadFull', '§4 圓內接四邊形全套'], ['bisector', '§4 角平分線全套'], ['areaMinPQ', '§4 面積條件下的最短線段'], ['areaSplitCevian', '§4 面積拆兩塊求中間的線段'], ['triOptimize', '§4 餘弦定理＋最值（相對運動、定和）'],
      ['elevMedian', '§5 三點仰角＋中點'], ['bearingHeight', '§5 方位角＋仰角測山高'], ['pyramidSolve', '§5 正四角錐反推']
  ];
  /* ══════════════════════════════════════════════════════════
     L3　中上（15 型）：每型對應固定題 L3-1～L3-15 的「類似題」
     ─────────────────────────────────────────────────────────
     同題型換數字／情境，答案一律精確：整數、F()（分數）、S()（根式 c√r/d）。
     設計參數時一律讓答案漂亮：sin／cos 由畢氏三元組造，角度只用 30°／45°
     的倍數，15° 一律以「15°-75°-90° 直角三角形」給出 tan15°=2−√3。
     超綱禁用：弧度、和差角、倍角、半角、疊合、cot／sec／csc、向量與內積。
     p 只放輸入參數與旗標（答案另放 p.ans，驗算器不讀）。
     每型開頭先丟掉一次 r()：連號種子的 LCG 首值幾乎相同，變體旗標不能靠它。
     ══════════════════════════════════════════════════════════ */
  var L3 = {};

  /* ── 小工具（名稱一律加 l3 前綴） ── */
  function l3g3(a, b, c) { return gcd(gcd(Math.abs(a), Math.abs(b)), Math.abs(c)); }
  /* (k + c√r)/d 的排版：先化簡根號、再三項約分；根式為正且常數為負時把根式寫前面 */
  function l3fs(k, c, r, d) {
    if (d < 0) { k = -k; c = -c; d = -d; }
    var s = simpSqrt(r); c *= s[0]; r = s[1];
    if (r === 1) { k += c; c = 0; }
    if (c === 0) return Fr.tex(F(k, d));
    var g = l3g3(k, c, d) || 1; k /= g; c /= g; d /= g;
    var rad = (Math.abs(c) === 1 ? '' : Math.abs(c)) + '\\sqrt{' + r + '}';
    var num;
    if (k === 0) num = (c < 0 ? '-' : '') + rad;
    else if (c > 0) num = (k < 0 ? rad + '-' + (-k) : k + '+' + rad);
    else num = k + '-' + rad;
    return d === 1 ? num : '\\dfrac{' + num + '}{' + d + '}';
  }
  /* (k + c√r)/d 化到最簡後的四元組，給「a+b+c」型題目判斷能不能寫成 (b+√c)/a */
  function l3fsRaw(k, c, r, d) {
    var s = simpSqrt(r); c *= s[0]; r = s[1];
    var g = l3g3(k, c, d) || 1;
    return { k: k / g, c: c / g, r: r, d: d / g };
  }
  /* ℚ(√3)：x + y√3（x、y 為 F），給 tan15°=2−√3 的兩棟樓題用 */
  function l3Q(x, y) { return { x: x, y: y }; }
  function l3Qadd(a, b) { return l3Q(Fr.add(a.x, b.x), Fr.add(a.y, b.y)); }
  function l3Qsub(a, b) { return l3Q(Fr.sub(a.x, b.x), Fr.sub(a.y, b.y)); }
  function l3Qmul(a, b) { return l3Q(Fr.add(Fr.mul(a.x, b.x), Fr.mul(F(3), Fr.mul(a.y, b.y))), Fr.add(Fr.mul(a.x, b.y), Fr.mul(a.y, b.x))); }
  function l3Qdiv(a, b) {
    var cj = l3Q(b.x, Fr.sub(F(0), b.y)), D = Fr.sub(Fr.mul(b.x, b.x), Fr.mul(F(3), Fr.mul(b.y, b.y))), n = l3Qmul(a, cj);
    return l3Q(Fr.div(n.x, D), Fr.div(n.y, D));
  }
  function l3Qtex(v) { return twoTex(v.x, S(v.y.n, 3, v.y.d)); }
  /* 把 ℚ(√3) 的值當成係數貼在變數前面（係數為 1 時不印） */
  function l3Qcoef(v, nm) { return (v.y.n === 0 && v.x.n === v.x.d) ? nm : l3Qtex(v) + nm; }
  /* 「＋ 係數·變數」的排版（係數為分數／負數時自動處理正負號） */
  function l3add(f, v) {
    if (f.n === 0) return '';
    var t = Fr.tex(F(Math.abs(f.n), f.d));
    return (f.n > 0 ? '+' : '-') + (t === '1' ? '' : t) + v;
  }
  /* c·（三角函數）(角度) 的排版 */
  function l3ct(c, fn, ang) { return (c === 1 ? '' : c === -1 ? '-' : String(c)) + FN[fn] + ang + '°'; }
  /* 整數係數的線性組合，例如 a-b+c、\sin A-\sin B+\sin C */
  function l3lc(co, nm) {
    var s = '', i;
    for (i = 0; i < co.length; i++) {
      if (co[i] > 0) s += (i === 0 ? '' : '+') + (co[i] === 1 ? '' : co[i]) + nm[i];
      else s += '-' + (co[i] === -1 ? '' : -co[i]) + nm[i];
    }
    return s;
  }
  function l3coef(n, v) { return (n === 1 ? '' : String(n)) + v; }
  /* 「係數 π」的排版：係數為 1 時只印 \pi */
  function l3pi(f) { var t = Fr.tex(f); return (t === '1' ? '' : t) + '\\pi'; }
  var L3QD = ['', '一', '二', '三', '四'];

  /* ══ L3-1　直角三角形＋互餘換角：化成同一個角再用平方關係解二次 ══ */
  /* u·sinA+sinB=u（u=p/q）⟹ (p²+q²)s²−2p²s+(p²−q²)=0 ⟹ s=1（不合）或 (p²−q²)/(p²+q²） */
  var L31P = [[2, 1], [3, 1], [4, 1], [5, 1], [6, 1], [7, 1], [3, 2], [5, 2], [7, 2], [9, 2],
              [4, 3], [5, 3], [7, 3], [8, 3], [5, 4], [7, 4], [9, 4], [6, 5], [7, 5], [8, 5], [9, 5], [7, 6]];
  L3.rightCoQuad = function (r) {
    r();
    var pq = r.pick(L31P), p = pq[0], q = pq[1], form = r.int(0, 1), ask = r.int(0, 2);
    var X = p * p - q * q, Y = 2 * p * q, Z = p * p + q * q, g = l3g3(X, Y, Z);
    var sn = form === 0 ? F(X, Z) : F(Y, Z), cs = form === 0 ? F(Y, Z) : F(X, Z), tn = Fr.div(sn, cs);
    var u = F(p, q), ut = Fr.tex(u);
    var eq = form === 0 ? ut + '\\sin A+\\sin B=' + ut : '\\sin A+' + ut + '\\sin B=' + ut;
    var eqCA = form === 0 ? ut + '\\sin A+\\cos A=' + ut : '\\sin A+' + ut + '\\cos A=' + ut;
    var ratio = (form === 0 ? [X, Y, Z] : [Y, X, Z]).map(function (t) { return t / g; }).join(':');
    var cosExpr = form === 0 ? (q === 1 ? p + '(1-s)' : '\\dfrac{' + p + '(1-s)}{' + q + '}')
                             : '\\dfrac{' + p + '-' + (q === 1 ? '' : q) + 's}{' + p + '}';
    var quad = form === 0 ? Z + 's^2-' + (2 * p * p) + 's+' + X + '=0' : Z + 's^2-' + Y + 's=0';
    var roots = form === 0 ? '$s=' + Fr.tex(F(X, Z)) + '$ 或 $s=1$' : '$s=0$ 或 $s=' + Fr.tex(F(Y, Z)) + '$';
    var bad = form === 0 ? '$s=1$ 會使 $\\cos A=0$（$\\angle B=0°$，不成三角形）' : '$s=0$ 會使 $\\angle A=0°$，不成三角形';
    var ask_, ans_;
    if (ask === 0) { ask_ = '求 ' + T('a:b:c') + '。'; ans_ = T(ratio); }
    else if (ask === 1) { ask_ = '求 ' + T('\\sin A') + ' 與 ' + T('\\cos A') + '。'; ans_ = T('\\sin A=' + Fr.tex(sn)) + '、' + T('\\cos A=' + Fr.tex(cs)); }
    else { ask_ = '求 ' + T('\\tan A') + ' 與 ' + T('a:b:c') + '。'; ans_ = T('\\tan A=' + Fr.tex(tn)) + '、' + T('a:b:c=' + ratio); }
    return { q: ABC + ' 中 ' + T('\\angle C=90°') + '，' + T('a,b,c') + ' 分別為 ' + T('\\angle A,\\angle B,\\angle C') + ' 的對邊，且 ' + T(eq) + '。' + ask_,
             a: ans_,
             h: '$\\angle A+\\angle B=90°$ ⟹ $\\sin B=\\cos A$，條件變成 $' + eqCA + '$，只剩一個角。令 $\\sin A=s$，則 $\\cos A=' + cosExpr + '$，代入 $s^2+\\cos^2A=1$ 得 $' + quad + '$ ⟹ ' + roots + '；' + bad + '，所以 $\\sin A=' + Fr.tex(sn) + '$、$\\cos A=' + Fr.tex(cs) + '$，而 $a:b:c=\\sin A:\\cos A:1=' + ratio + '$。',
             p: { p: p, q: q, form: form, ask: ask, ans: { sin: fr2(sn), cos: fr2(cs), ratio: ratio } } };
  };

  /* ══ L3-2　a cosθ=b tanθ 型：通分換成 sinθ 的二次方程，用 |sinθ|≤1 刷根 ══ */
  L3.tanCosQuad = function (r) {
    r();
    var a, b, N, rt, tries = 0;
    do { a = r.int(1, 6); b = r.int(1, 6); N = b * b + 4 * a * a; rt = Math.round(Math.sqrt(N)); tries++; }
    while ((gcd(a, b) !== 1 || rt * rt === N) && tries < 200);
    var v = r.int(0, 2);
    var ansTex = l3fs(-b, 1, N, 2 * a), other = l3fs(-b, -1, N, 2 * a);
    var av = (Math.sqrt(N) - b) / (2 * a), ov = (-Math.sqrt(N) - b) / (2 * a);
    var ap = Math.round(av * 100) / 100, op = Math.round(ov * 100) / 100;
    var eq, ask, vn, chain;
    if (v === 0) { eq = l3coef(a, '\\cos\\theta') + '=' + l3coef(b, '\\tan\\theta'); ask = '\\sin\\theta'; vn = 's'; chain = l3coef(a, '\\cos^2\\theta') + '=' + l3coef(b, '\\sin\\theta'); }
    else if (v === 1) { eq = l3coef(b, '\\tan\\theta') + '=' + l3coef(a, '\\cos\\theta'); ask = '\\sin\\theta'; vn = 's'; chain = l3coef(b, '\\sin\\theta') + '=' + l3coef(a, '\\cos^2\\theta'); }
    else { eq = l3coef(a, '\\sin\\theta\\tan\\theta') + '=' + b; ask = '\\cos\\theta'; vn = 'c'; chain = l3coef(a, '\\sin^2\\theta') + '=' + l3coef(b, '\\cos\\theta'); }
    var sq = v === 2 ? '\\cos^2\\theta' : '\\sin^2\\theta', other2 = v === 2 ? '\\sin^2\\theta' : '\\cos^2\\theta';
    return { q: '若 ' + T(eq) + '，求 ' + T(ask) + ' 的值。',
             a: T(ask + '=' + ansTex),
             h: '$\\tan\\theta=\\dfrac{\\sin\\theta}{\\cos\\theta}$，兩邊同乘 $\\cos\\theta$ 通分得 $' + chain + '$；再把 $' + other2 + '$ 換成 $1-' + sq + '$，整理成 $' + l3coef(a, vn + '^2') + '+' + l3coef(b, vn) + '-' + a + '=0$ ⟹ $' + vn + '=\\dfrac{-' + b + '\\pm\\sqrt{' + N + '}}{' + (2 * a) + '}$。因為 $-1\\le' + ask + '\\le1$，只留 $' + ansTex + '\\approx' + ap + '$（另一根 $' + other + '\\approx' + op + '$ 不合）。',
             p: { a: a, b: b, v: v, N: N, ans: ansTex } };
  };

  /* ══ L3-3　互餘配對整串求和：每對得 1、中間 45° 那項得 ½ ══ */
  var L33S = (function () {
    var o = [], d, n, s;
    for (d = 1; d <= 20; d++) for (n = 5; n <= 21; n++) {
      if (((n - 1) * d) % 2) continue;
      s = 45 - (n - 1) * d / 2;
      if (s >= 1 && s + (n - 1) * d <= 89) o.push([s, d, n]);
    }
    return o;
  })();
  L3.coPairSum = function (r) {
    r();
    var t = r.pick(L33S), s = t[0], d = t[1], n = t[2], v = r.int(0, 2);
    var term = function (x) {
      return v === 0 ? '\\dfrac{1}{1+\\tan' + x + '°}' : v === 1 ? '\\dfrac{\\tan' + x + '°}{1+\\tan' + x + '°}' : '\\dfrac{1}{1+\\tan^2' + x + '°}';
    };
    var last = s + (n - 1) * d, ex = term(s) + '+' + term(s + d) + '+' + term(s + 2 * d) + '+\\cdots+' + term(last);
    var np = Math.floor(n / 2), odd = n % 2 === 1;
    var pair = v === 0 ? '$\\dfrac{1}{1+\\tan x}+\\dfrac{1}{1+\\tan(90°-x)}=\\dfrac{1}{1+\\tan x}+\\dfrac{\\tan x}{\\tan x+1}=1$'
             : v === 1 ? '$\\dfrac{\\tan x}{1+\\tan x}+\\dfrac{\\tan(90°-x)}{1+\\tan(90°-x)}=\\dfrac{\\tan x}{1+\\tan x}+\\dfrac{1}{1+\\tan x}=1$'
                       : '$1+\\tan^2x=\\dfrac{1}{\\cos^2x}$ ⟹ 每一項就是 $\\cos^2x$，而 $\\cos^2x+\\cos^2(90°-x)=\\cos^2x+\\sin^2x=1$';
    var head = v === 2 ? '$\\tan(90°-x)=\\dfrac{1}{\\tan x}$ 讓頭尾兩項互相補成 $1$：' : '$\\tan(90°-x)=\\dfrac{1}{\\tan x}$ ⟹ 頭尾配對：';
    return { q: '化簡 ' + T(ex) + '（共 ' + T(String(n)) + ' 項，角度從 ' + T(s + '°') + ' 開始每次加 ' + T(d + '°') + '）。',
             a: T(Fr.tex(F(n, 2))),
             h: head + pair + '。' + T(s + '°') + ' 與 ' + T(last + '°') + '、' + T((s + d) + '°') + ' 與 ' + T((last - d) + '°') + '……共配成 ' + T(String(np)) + ' 對得 ' + T(String(np)) + (odd ? '，中間 ' + T('45°') + ' 那一項是 ' + T('\\dfrac{1}{2}') + '' : '，項數是偶數沒有落單的') + ' ⟹ 總和 ' + T(Fr.tex(F(n, 2))) + '。',
             p: { s: s, d: d, n: n, v: v, ans: fr2(F(n, 2)) } };
  };

  /* ══ L3-4　誘導公式化簡（給範圍）：每一項都化成 ±1 再相加 ══ */
  var L34C = (function () {
    var o = [], fns = ['sin', 'cos', 'tan'], i, k, m;
    for (i = 0; i < 3; i++) for (k = 0; k <= 4; k++) for (m = -1; m <= 1; m += 2) {
      if (k === 0 && m === 1) continue;            /* 排除「原樣」的 sinθ，每個因式都要真的用到誘導公式 */
      var rr = reduceOne(fns[i], k, m);
      o.push({ fn: fns[i], k: k, m: m, tex: FN[fns[i]] + argTex(k, m), sign: rr.sign, es: rr.es, ec: rr.ec,
               key: rr.es + ',' + rr.ec, red: resultTex(rr.sign, rr.es, rr.ec) });
    }
    return o;
  })();
  var L34G = (function () { var g = {}; L34C.forEach(function (c) { (g[c.key] = g[c.key] || []).push(c); }); return g; })();
  function l3same(a, b) { return a.fn === b.fn && (a.k % 4) === (b.k % 4) && a.m === b.m; }
  L3.reduceSum = function (r) {
    r();
    var qd = r.int(1, 4), v = r.int(0, 2), keys = ['1,0', '0,1', '1,-1', '-1,1'];
    var terms, val, tries = 0;
    do {
      terms = []; val = 0;
      var nq = v === 0 ? 3 : 2, i, j, A, B, t2;
      for (i = 0; i < nq; i++) {
        var gp = L34G[r.pick(keys)];
        t2 = 0; do { A = r.pick(gp); B = r.pick(gp); t2++; } while (l3same(A, B) && t2 < 60);
        terms.push({ tex: '\\dfrac{' + A.tex + '}{' + B.tex + '}', val: A.sign * B.sign, fac: [A, B], op: '÷' });
      }
      if (v === 1) {
        A = r.pick(L34G['1,-1']); B = r.pick(L34G['-1,1']);
        terms.push({ tex: A.tex + '\\cdot' + B.tex, val: A.sign * B.sign, fac: [A, B], op: '×' });
      }
      for (i = 0; i < terms.length; i++) terms[i].sg = i === 0 ? 1 : r.sign();
      var dup = false;
      for (i = 0; i < terms.length; i++) for (j = i + 1; j < terms.length; j++) if (terms[i].tex === terms[j].tex) dup = true;
      for (i = 0; i < terms.length; i++) val += terms[i].sg * terms[i].val;
      tries++;
      if (dup) val = 0;
    } while (val === 0 && tries < 60);
    var ex = terms.map(function (t, i) { return (i === 0 ? '' : (t.sg > 0 ? '+' : '-')) + t.tex; }).join('');
    var reds = [], seen = {};
    terms.forEach(function (t) { t.fac.forEach(function (f) { if (!seen[f.tex]) { seen[f.tex] = 1; reds.push('$' + f.tex + '=' + f.red + '$'); } }); });
    var vals = terms.map(function (t, i) { return '第' + ['一', '二', '三'][i] + '項 $=' + t.val + '$'; }).join('、');
    return { q: '若 ' + T(((qd - 1) * 90) + '°\\lt\\theta\\lt' + (qd * 90) + '°') + '，求 ' + T(ex) + ' 的值。',
             a: T(String(val)),
             h: '把 $\\theta$ 當銳角畫圖定號（奇變偶不變、符號看象限）：' + reds.join('、') + '。' + vals + ' ⟹ 總和 $' + val + '$。範圍 $' + ((qd - 1) * 90) + '°\\lt\\theta\\lt' + (qd * 90) + '°$ 只是保證分母不為 $0$，答案與 $\\theta$ 無關。',
             p: { qd: qd, v: v, terms: terms.map(function (t) { return { sg: t.sg, op: t.op, fac: t.fac.map(function (f) { return [f.fn, f.k, f.m]; }) }; }), ans: val } };
  };

  /* ══ L3-5　(±m sinα, ±m cosα) 化極坐標：餘角公式把 sin 換成 cos ══ */
  L3.polarFromTrig = function (r) {
    r();
    var al; do { al = r.int(1, 71) * 5; } while (al % 90 === 0);
    var m = r.pick([1, 1, 2, 3, 4, 5]), s1 = r.sign(), s2 = r.sign(), rk = r.int(0, 1);
    var th = ((s1 > 0 ? (s2 > 0 ? 90 - al : al - 90) : (s2 > 0 ? 90 + al : 270 - al)) % 360 + 360) % 360;
    var shown = rk === 0 ? th : (th > 180 ? th - 360 : th);
    var xT = l3ct(s1 * m, 'sin', al), yT = l3ct(s2 * m, 'cos', al);
    var bs = s1 > 0 ? (s2 > 0 ? '90°-' + al + '°' : al + '°-90°') : (s2 > 0 ? '90°+' + al + '°' : '270°-' + al + '°');
    var idx = (s1 > 0 ? '\\sin' : '-\\sin') + al + '°=\\cos(' + bs + ')$、$' + (s2 > 0 ? '\\cos' : '-\\cos') + al + '°=\\sin(' + bs + ')';
    var base = s1 > 0 ? (s2 > 0 ? 90 - al : al - 90) : (s2 > 0 ? 90 + al : 270 - al);
    var rng = rk === 0 ? '0°\\le\\theta\\lt360°' : '-180°\\lt\\theta\\le180°';
    var quad = Math.floor(th / 90) + 1, qal = Math.floor((al % 360) / 90) + 1;
    return { q: '直角坐標系與極坐標系的原點重合、極軸為 $x$ 軸正向。已知 $P$ 點的直角坐標為 ' + T('(' + xT + ',' + yT + ')') + '，求 $P$ 的極坐標 ' + T('[r,\\theta]') + '（' + T('r\\gt0') + '，' + T(rng) + '）。',
             a: T('[' + m + ',' + shown + '°]'),
             h: '$r=\\sqrt{(' + xT + ')^2+(' + yT + ')^2}=' + l3coef(m, '\\sqrt{\\sin^2' + al + '°+\\cos^2' + al + '°}') + '=' + m + '$。接著要找 $\\theta$ 使 $(\\cos\\theta,\\sin\\theta)=' + (m === 1 ? 'P' : '\\dfrac{1}{' + m + '}P') + '$。用餘角公式把 $\\sin$ 換成 $\\cos$：$' + idx + '$ ⟹ $P=' + l3coef(m, '(\\cos(' + bs + '),\\sin(' + bs + '))') + '$ ⟹ $\\theta=' + base + '°$，取' + (rk === 0 ? '最小正同界角 ' : '落在 $-180°\\lt\\theta\\le180°$ 的同界角 ') + T(shown + '°') + '。檢查：$' + al + '°$ 在第' + L3QD[qal] + '象限，$P$ 與 ' + T(th + '°') + ' 都落在第' + L3QD[quad] + '象限 ✓。',
             p: { al: al, m: m, s1: s1, s2: s2, rk: rk, ans: { r: m, th: shown } } };
  };

  /* ══ L3-6　四個極坐標點的長度比與面積比：極角相減得夾角 ══ */
  var L36P = (function () {
    var o = { 60: [], 90: [], 120: [] }, i, j, v, t;
    for (i = 2; i <= 20; i++) for (j = 2; j <= 20; j++) {
      v = i * i + j * j - i * j; t = Math.round(Math.sqrt(v)); if (t * t === v) o[60].push([i, j, t]);
      v = i * i + j * j; t = Math.round(Math.sqrt(v)); if (t * t === v) o[90].push([i, j, t]);
      v = i * i + j * j + i * j; t = Math.round(Math.sqrt(v)); if (t * t === v) o[120].push([i, j, t]);
    }
    return o;
  })();
  L3.polarRatio = function (r) {
    r();
    var thA = r.int(0, 71) * 5, st = r.int(0, 1), g1, g3, b, d;
    if (st === 0) { g1 = r.pick([60, 90, 120]); g3 = r.pick([60, 90, 120]); b = (360 - g1 - g3) / 2; d = b; }
    else { var gp = r.pick([[60, 120], [120, 60], [90, 90]]); g1 = gp[0]; g3 = gp[1]; b = r.pick([20, 30, 40, 50, 60, 70, 80, 100, 110, 120, 130, 140, 150, 160]); d = 180 - b; }
    var p1 = r.pick(L36P[g1]), p3 = r.pick(L36P[g3]);
    var rA = p1[0], rB = p1[1], rC = p3[0], rD = p3[1], AB = p1[2], CD = p3[2];
    var thB = (thA + g1) % 360, thC = (thB + b) % 360, thD = (thC + g3) % 360;
    var pp = F(AB, CD), qq = F(rB * rC, rA * rD), v = r.int(0, 2);
    var u1 = pp.d, u2 = qq.d;
    if (v === 2 && (u1 > 5 || u2 > 5)) v = 1;
    var pt = function (n, rr, th) { return T(n + '[' + rr + ',' + th + '°]'); };
    var setup = '平面上 $O$ 為極點，四點的極坐標為 ' + pt('A', rA, thA) + '、' + pt('B', rB, thB) + '、' + pt('C', rC, thC) + '、' + pt('D', rD, thD) + '。';
    var hb = '夾角全部由極角相減得到：$\\angle AOB=' + g1 + '°$、$\\angle BOC=' + b + '°$、$\\angle COD=' + g3 + '°$、$\\angle DOA=' + d + '°$。'
           + '餘弦定理：$\\overline{AB}^2=' + (rA * rA) + '+' + (rB * rB) + '-2(' + rA + ')(' + rB + ')\\cos' + g1 + '°=' + (AB * AB) + '$ ⟹ $\\overline{AB}=' + AB + '$；'
           + '$\\overline{CD}^2=' + (rC * rC) + '+' + (rD * rD) + '-2(' + rC + ')(' + rD + ')\\cos' + g3 + '°=' + (CD * CD) + '$ ⟹ $\\overline{CD}=' + CD + '$。'
           + '面積只看 $\\dfrac12r_ir_j\\sin(\\text{夾角})$，' + (b === d ? '兩個夾角都是 $' + b + '°$' : '$\\sin' + b + '°=\\sin' + d + '°$（$' + b + '°+' + d + '°=180°$）') + ' ⟹ 比值 $=\\dfrac{(' + rB + ')(' + rC + ')}{(' + rA + ')(' + rD + ')}=' + Fr.tex(qq) + '$。';
    if (v === 0)
      return { q: setup + '求 (1) ' + T('\\overline{AB}') + '　(2) ' + T('\\overline{CD}') + '　(3) ' + T('\\triangle OBC') + ' 與 ' + T('\\triangle OAD') + ' 的面積比。',
               a: '(1) ' + T('\\overline{AB}=' + AB) + '　(2) ' + T('\\overline{CD}=' + CD) + '　(3) ' + T('\\triangle OBC:\\triangle OAD=' + (qq.n) + ':' + (qq.d)),
               h: hb,
               p: { v: 0, rs: [rA, rB, rC, rD], th: [thA, thB, thC, thD], ans: { AB: AB, CD: CD, ratio: fr2(qq) } } };
    if (v === 1)
      return { q: setup + '若 ' + T('\\overline{AB}') + ' 的長為 ' + T('\\overline{CD}') + ' 的 ' + T('p') + ' 倍，' + T('\\triangle OBC') + ' 的面積為 ' + T('\\triangle OAD') + ' 面積的 ' + T('q') + ' 倍，求 ' + T('p+q') + '。',
               a: T('p=' + Fr.tex(pp)) + '、' + T('q=' + Fr.tex(qq)) + ' ⟹ ' + T('p+q=' + Fr.tex(Fr.add(pp, qq))),
               h: hb + '所以 $p=\\dfrac{' + AB + '}{' + CD + '}' + (Fr.tex(pp) === '\\dfrac{' + AB + '}{' + CD + '}' ? '' : '=' + Fr.tex(pp)) + '$、$q=' + Fr.tex(qq) + '$ ⟹ $p+q=' + Fr.tex(Fr.add(pp, qq)) + '$。',
               p: { v: 1, rs: [rA, rB, rC, rD], th: [thA, thB, thC, thD], ans: { p: fr2(pp), q: fr2(qq), sum: fr2(Fr.add(pp, qq)) } } };
    var tot = pp.n + qq.n;
    return { q: setup + '若 ' + T('\\overline{AB}') + ' 的長為 ' + T('\\overline{CD}') + ' 的 ' + T('p') + ' 倍，' + T('\\triangle OBC') + ' 的面積為 ' + T('\\triangle OAD') + ' 面積的 ' + T('q') + ' 倍，求 ' + T(l3coef(u1, 'p') + '+' + l3coef(u2, 'q')) + '。',
             a: T('p=' + Fr.tex(pp)) + '、' + T('q=' + Fr.tex(qq)) + ' ⟹ ' + T(l3coef(u1, 'p') + '+' + l3coef(u2, 'q') + '=' + tot),
             h: hb + '所以 $p=' + Fr.tex(pp) + '$、$q=' + Fr.tex(qq) + '$ ⟹ $' + l3coef(u1, 'p') + '+' + l3coef(u2, 'q') + '=' + pp.n + '+' + qq.n + '=' + tot + '$。',
             p: { v: 2, rs: [rA, rB, rC, rD], th: [thA, thB, thC, thD], u: [u1, u2], ans: tot } };
  };

  /* ══ L3-7　tanθ+1/tanθ 型：倒數和＝1/(sinθcosθ)，再用範圍定號 ══ */
  L3.tanRecip = function (r) {
    r();
    var t = tri(r), a = t[0], b = t[1], c = t[2], lo = Math.min(a, b), hi = Math.max(a, b);
    var rg = r.int(0, 3), ask = r.int(0, 3), k = F(c * c, lo * hi);
    var sn = rg === 0 ? F(lo, c) : rg === 1 ? F(hi, c) : rg === 2 ? F(-lo, c) : F(-hi, c);
    var cs = rg === 0 ? F(hi, c) : rg === 1 ? F(lo, c) : rg === 2 ? F(-hi, c) : F(-lo, c);
    var pr = Fr.mul(sn, cs), df = Fr.sub(sn, cs), sm = Fr.add(sn, cs);
    var lo2 = [0, 45, 180, 225][rg], hi2 = [45, 90, 225, 270][rg];
    var rng = lo2 + '°\\lt\\theta\\lt' + hi2 + '°';
    var why = rg === 0 ? '$0°\\lt\\theta\\lt45°$ ⟹ $0\\lt\\sin\\theta\\lt\\cos\\theta$'
            : rg === 1 ? '$45°\\lt\\theta\\lt90°$ ⟹ $0\\lt\\cos\\theta\\lt\\sin\\theta$'
            : rg === 2 ? '$180°\\lt\\theta\\lt225°$ ⟹ $\\sin\\theta$、$\\cos\\theta$ 皆為負且 $\\cos\\theta\\lt\\sin\\theta\\lt0$'
                       : '$225°\\lt\\theta\\lt270°$ ⟹ $\\sin\\theta$、$\\cos\\theta$ 皆為負且 $\\sin\\theta\\lt\\cos\\theta\\lt0$';
    var ask_, ans_;
    if (ask === 0) { ask_ = '求 ' + T('\\sin\\theta-\\cos\\theta') + '。'; ans_ = T(Fr.tex(df)); }
    else if (ask === 1) { ask_ = '求 ' + T('\\sin\\theta+\\cos\\theta') + '。'; ans_ = T(Fr.tex(sm)); }
    else if (ask === 2) { ask_ = '求 ' + T('\\sin\\theta') + ' 與 ' + T('\\cos\\theta') + '。'; ans_ = T('\\sin\\theta=' + Fr.tex(sn)) + '、' + T('\\cos\\theta=' + Fr.tex(cs)); }
    else { ask_ = '求 ' + T('\\sin\\theta\\cos\\theta') + ' 與 ' + T('\\sin\\theta-\\cos\\theta') + '。'; ans_ = T('\\sin\\theta\\cos\\theta=' + Fr.tex(pr)) + '、' + T('\\sin\\theta-\\cos\\theta=' + Fr.tex(df)); }
    return { q: '設 ' + T(rng) + '，若 ' + T('\\tan\\theta+\\dfrac{1}{\\tan\\theta}=' + Fr.tex(k)) + '，' + ask_,
             a: ans_,
             h: '$\\tan\\theta+\\dfrac{1}{\\tan\\theta}=\\dfrac{\\sin\\theta}{\\cos\\theta}+\\dfrac{\\cos\\theta}{\\sin\\theta}=\\dfrac{\\sin^2\\theta+\\cos^2\\theta}{\\sin\\theta\\cos\\theta}=\\dfrac{1}{\\sin\\theta\\cos\\theta}$ ⟹ $\\sin\\theta\\cos\\theta=' + Fr.tex(pr) + '$。'
                + '再用 $(\\sin\\theta-\\cos\\theta)^2=1-2\\sin\\theta\\cos\\theta=' + Fr.tex(Fr.mul(df, df)) + '$、$(\\sin\\theta+\\cos\\theta)^2=1+2\\sin\\theta\\cos\\theta=' + Fr.tex(Fr.mul(sm, sm)) + '$ 開根號，' + why + ' ⟹ $\\sin\\theta-\\cos\\theta=' + Fr.tex(df) + '$、$\\sin\\theta+\\cos\\theta=' + Fr.tex(sm) + '$。'
                + (ask === 0 ? '本題只要差，答案就是 $' + Fr.tex(df) + '$，正負號由範圍決定，別漏掉負號。'
                 : ask === 1 ? '本題只要和，答案就是 $' + Fr.tex(sm) + '$，第三、四象限時和為負。'
                 : ask === 2 ? '和差兩式聯立（相加除以 $2$、相減除以 $2$）⟹ $\\sin\\theta=' + Fr.tex(sn) + '$、$\\cos\\theta=' + Fr.tex(cs) + '$。'
                             : '本題要的是 $\\sin\\theta\\cos\\theta=' + Fr.tex(pr) + '$ 與 $\\sin\\theta-\\cos\\theta=' + Fr.tex(df) + '$，開根號那一步的正負是唯一的陷阱。'),
             p: { a: a, b: b, c: c, rg: rg, ask: ask, k: fr2(k), ans: { sin: fr2(sn), cos: fr2(cs), diff: fr2(df), sum: fr2(sm), prod: fr2(pr) } } };
  };

  /* ══ L3-8　tanθ±1/cosθ=k：通分成一次式代入平方關係，cosθ=0 的根不合 ══ */
  var L38K = (function () {
    var o = [], p, q;
    for (q = 1; q <= 5; q++) for (p = 1; p <= 9; p++) if (gcd(p, q) === 1 && p !== q) { o.push([p, q]); o.push([-p, q]); }
    return o;
  })();
  L3.tanSecLin = function (r) {
    r();
    var pq = r.pick(L38K), p = pq[0], q = pq[1];
    var fm = r.int(0, 2), ask = r.int(0, 3), rk = r.int(0, 1);
    var sgT = fm === 2 ? -1 : 1, sgS = fm === 1 ? -1 : 1;
    var lam = sgT * sgS, P = p * sgT, Q = q, Z = P * P + Q * Q;
    var cs = F(2 * P * Q * lam, Z), sn = F(lam * (P * P - Q * Q), Z), tn = Fr.div(sn, cs);
    var kt = Fr.tex(F(p, q));
    var eq = fm === 0 ? '\\tan\\theta+\\dfrac{1}{\\cos\\theta}=' + kt
           : fm === 1 ? '\\tan\\theta-\\dfrac{1}{\\cos\\theta}=' + kt
                      : '\\dfrac{1}{\\cos\\theta}-\\tan\\theta=' + kt;
    var lin = fm === 0 ? '\\dfrac{\\sin\\theta+1}{\\cos\\theta}=' + kt : fm === 1 ? '\\dfrac{\\sin\\theta-1}{\\cos\\theta}=' + kt : '\\dfrac{1-\\sin\\theta}{\\cos\\theta}=' + kt;
    var quad = (sn.n > 0 ? (cs.n > 0 ? 1 : 2) : (cs.n > 0 ? 4 : 3));
    var cond = rk === 0 ? '已知 $\\theta$ 為第' + L3QD[quad] + '象限角，且 ' : '已知 ' + T(((quad - 1) * 90) + '°\\lt\\theta\\lt' + (quad * 90) + '°') + ' 且 ';
    /* 代入後的整係數二次式：Z·cos²θ − 2PQλ·cosθ = 0 */
    var c2 = Z, c1 = -2 * P * Q * lam;
    var quadTex = c2 + '\\cos^2\\theta' + (c1 > 0 ? '+' + c1 : c1) + '\\cos\\theta=0';
    var ask_, ans_;
    if (ask === 0) { ask_ = '求 ' + T('\\cos\\theta') + '。'; ans_ = T('\\cos\\theta=' + Fr.tex(cs)); }
    else if (ask === 1) { ask_ = '求 ' + T('\\sin\\theta') + '。'; ans_ = T('\\sin\\theta=' + Fr.tex(sn)); }
    else if (ask === 2) { ask_ = '求 ' + T('\\sin\\theta') + ' 與 ' + T('\\cos\\theta') + '。'; ans_ = T('\\sin\\theta=' + Fr.tex(sn)) + '、' + T('\\cos\\theta=' + Fr.tex(cs)); }
    else { ask_ = '求 ' + T('\\tan\\theta') + '。'; ans_ = T('\\tan\\theta=' + Fr.tex(tn)); }
    var linSol = fm === 2 ? '\\sin\\theta=1' + l3add(F(-p, q), '\\cos\\theta')
                          : '\\sin\\theta=' + kt + '\\cos\\theta' + (fm === 0 ? '-1' : '+1');
    return { q: cond + T(eq) + '。' + ask_,
             a: ans_,
             h: '同分母通分：$' + lin + '$ ⟹ $' + linSol + '$，這是「一次式代入平方關係」。代進 $\\sin^2\\theta+\\cos^2\\theta=1$ 整理得 $' + quadTex + '$ ⟹ $\\cos\\theta=0$（它是原式的分母，不合）或 $\\cos\\theta=' + Fr.tex(cs) + '$。此時 $\\sin\\theta=' + Fr.tex(sn) + '$，兩者的正負恰為第' + L3QD[quad] + '象限 ✓。',
             p: { p: p, q: q, fm: fm, ask: ask, rk: rk, ans: { sin: fr2(sn), cos: fr2(cs), tan: fr2(tn), quad: quad } } };
  };

  /* ══ L3-9　a cosθ+b sinθ=c（銳角）：用一次式代入平方關係，cosθ>0 刷根 ══ */
  var L39P = (function () {
    var o = [], u, w, v, D, t;
    for (u = 1; u <= 6; u++) for (w = u + 1; w <= 8; w++) for (v = w + 1; v <= 9; v++) {
      if (l3g3(u, w, v) !== 1) continue;
      D = u * u + v * v - w * w; t = Math.round(Math.sqrt(D));
      if (t * t === D) continue;
      o.push([u, v, w, D]);
    }
    return o;
  })();
  L3.linTrigAcute = function (r) {
    r();
    var pk = r.pick(L39P), u = pk[0], v = pk[1], w = pk[2], D = pk[3];
    var od = r.int(0, 1), ask = r.int(0, 2), Z = u * u + v * v;
    var eq = od === 0 ? l3coef(u, '\\cos\\theta') + '+' + l3coef(v, '\\sin\\theta') + '=' + w
                      : l3coef(v, '\\sin\\theta') + '+' + l3coef(u, '\\cos\\theta') + '=' + w;
    var snT = l3fs(v * w, -u, D, Z), csT = l3fs(u * w, v, D, Z), smT = l3fs(w * (u + v), v - u, D, Z);
    var rw = l3fsRaw(w * (u + v), v - u, D, Z);
    if (ask === 2 && !(rw.c === 1 && rw.k > 0 && rw.d > 1 && gcd(rw.k, rw.d) === 1)) ask = 1;
    var bad = l3fs(v * w, u, D, Z), badC = l3fs(u * w, -v, D, Z);
    var sp = simpSqrt(D), uc = u * sp[0];
    var gq = l3g3(Z, 2 * v * w, w * w - u * u) || 1, gr = l3g3(v * w, uc, Z) || 1;
    var hb = '令 $\\sin\\theta=s$，由條件得 $\\cos\\theta=' + (u === 1 ? w + '-' + l3coef(v, 's') : '\\dfrac{' + w + '-' + l3coef(v, 's') + '}{' + u + '}') + '$，代入 $s^2+\\cos^2\\theta=1$ ⟹ $' + l3coef(Z / gq, 's^2') + '-' + l3coef(2 * v * w / gq, 's') + '+' + ((w * w - u * u) / gq) + '=0$ ⟹ $s=\\dfrac{' + (v * w / gr) + '\\pm' + (uc / gr === 1 ? '' : uc / gr) + '\\sqrt{' + sp[1] + '}}{' + (Z / gr) + '}$。'
           + '$\\theta$ 為銳角 ⟹ $\\cos\\theta\\gt0$，取 $s=' + snT + '$（另一根 $' + bad + '$ 會使 $\\cos\\theta=' + badC + '\\lt0$，不合），此時 $\\cos\\theta=' + csT + '$。';
    if (ask === 0)
      return { q: '設 ' + T(eq) + ' 且 ' + T('0°\\lt\\theta\\lt90°') + '。求 ' + T('\\sin\\theta') + ' 與 ' + T('\\cos\\theta') + '。',
               a: T('\\sin\\theta=' + snT) + '、' + T('\\cos\\theta=' + csT),
               h: hb,
               p: { u: u, v: v, w: w, od: od, ask: 0, ans: { sin: snT, cos: csT } } };
    if (ask === 1)
      return { q: '設 ' + T(eq) + ' 且 ' + T('0°\\lt\\theta\\lt90°') + '。求 ' + T('\\sin\\theta+\\cos\\theta') + '。',
               a: T('\\sin\\theta+\\cos\\theta=' + smT),
               h: hb + '相加得 $\\sin\\theta+\\cos\\theta=' + smT + '$。',
               p: { u: u, v: v, w: w, od: od, ask: 1, ans: { sum: smT } } };
    return { q: '設 ' + T(eq) + ' 且 ' + T('0°\\lt\\theta\\lt90°') + '。若 ' + T('\\sin\\theta+\\cos\\theta=\\dfrac{b+\\sqrt c}{a}') + '（' + T('a,b,c') + ' 為正整數且 ' + T('a,b') + ' 互質），求 ' + T('a+b+c') + '。',
             a: T('\\sin\\theta+\\cos\\theta=' + smT) + ' ⟹ ' + T('(a,b,c)=(' + rw.d + ',' + rw.k + ',' + rw.r + ')') + '，' + T('a+b+c=' + (rw.d + rw.k + rw.r)),
             h: hb + '相加得 $\\sin\\theta+\\cos\\theta=' + smT + '$ ⟹ $(a,b,c)=(' + rw.d + ',' + rw.k + ',' + rw.r + ')$ ⟹ $a+b+c=' + (rw.d + rw.k + rw.r) + '$。',
             p: { u: u, v: v, w: w, od: od, ask: 2, ans: { a: rw.d, b: rw.k, c: rw.r, sum: rw.d + rw.k + rw.r } } };
  };

  /* ══ L3-10　兩棟樓＋甲樓頂看乙樓頂仰角 15°：tan15°=2−√3 列一條方程 ══ */
  var L3COT = { 30: l3Q(F(0), F(1)), 45: l3Q(F(1), F(0)), 60: l3Q(F(0), F(1, 3)) };
  L3.twoTowers = function (r) {
    r();
    var H = r.pick([12, 18, 24, 30, 36, 42, 48, 54, 60]), al = r.pick([30, 45, 60]), be = r.pick([30, 45, 60]), v = r.int(0, 2);
    var t15 = l3Q(F(2), F(-1)), ca = L3COT[al], cb = L3COT[be];
    var num = l3Qadd(l3Q(F(1), F(0)), l3Qmul(t15, ca)), den = l3Qsub(l3Q(F(1), F(0)), l3Qmul(t15, cb));
    var h = l3Qmul(l3Q(F(H), F(0)), l3Qdiv(num, den));
    var dist = l3Qadd(l3Qmul(l3Q(F(H), F(0)), ca), l3Qmul(h, cb));
    var hT = l3Qtex(h), dT = l3Qtex(dist), dA = l3Qtex(l3Qmul(l3Q(F(H), F(0)), ca)), cbh = l3Qcoef(cb, 'h');
    var tip = '（提示：' + T('15°') + '-' + T('75°') + '-' + T('90°') + ' 直角三角形的兩股比為 ' + T('(\\sqrt3-1):(\\sqrt3+1)') + '，故 ' + T('\\tan15°=2-\\sqrt3') + '。）';
    var hb = '設乙樓高 $h$：$A$ 到甲樓底 $=\\dfrac{' + H + '}{\\tan' + al + '°}=' + dA + '$、$A$ 到乙樓底 $=\\dfrac{h}{\\tan' + be + '°}=' + cbh + '$，兩樓相距 $' + dA + '+' + cbh + '$。'
           + '從甲樓頂看乙樓頂：高度差 $h-' + H + '$、水平距離就是兩樓的距離 ⟹ $\\dfrac{h-' + H + '}{' + dA + '+' + cbh + '}=\\tan15°=2-\\sqrt3$，解得 $h=' + hT + '$（分母有根號要有理化）。';
    if (v === 0)
      return { q: '甲、乙兩棟大樓，甲樓高 ' + T(String(H)) + ' 公尺。在兩樓之間的地面點 $A$ 分別測得甲、乙樓頂的仰角為 ' + T(al + '°') + ' 與 ' + T(be + '°') + '；又在甲樓頂測得乙樓頂的仰角為 ' + T('15°') + '。求乙樓的高。' + tip,
               a: T(hT) + ' 公尺',
               h: hb,
               p: { v: 0, H: H, al: al, be: be, ans: { h: [fr2(h.x), fr2(h.y)] } } };
    if (v === 1)
      return { q: '甲、乙兩棟大樓，甲樓高 ' + T(String(H)) + ' 公尺。在兩樓之間的地面點 $A$ 分別測得甲、乙樓頂的仰角為 ' + T(al + '°') + ' 與 ' + T(be + '°') + '；又在甲樓頂測得乙樓頂的仰角為 ' + T('15°') + '。求 (1) 乙樓的高　(2) 兩棟樓的水平距離。' + tip,
               a: '(1) ' + T(hT) + ' 公尺　(2) ' + T(dT) + ' 公尺',
               h: hb + '兩樓距離 $=' + dA + '+' + (cb.y.n === 0 ? '(' + hT + ')' : l3Qtex(cb) + '\\times(' + hT + ')') + '=' + dT + '$。',
               p: { v: 1, H: H, al: al, be: be, ans: { h: [fr2(h.x), fr2(h.y)], d: [fr2(dist.x), fr2(dist.y)] } } };
    return { q: '甲、乙兩棟大樓，乙樓高 ' + T(hT) + ' 公尺。在兩樓之間的地面點 $A$ 分別測得甲、乙樓頂的仰角為 ' + T(al + '°') + ' 與 ' + T(be + '°') + '；又在甲樓頂測得乙樓頂的仰角為 ' + T('15°') + '。求甲樓的高。' + tip,
             a: T(String(H)) + ' 公尺',
             h: '設甲樓高 $H$：$A$ 到甲樓底 $=\\dfrac{H}{\\tan' + al + '°}=' + l3Qcoef(ca, 'H') + '$、$A$ 到乙樓底 $=' + (cb.y.n === 0 ? l3Qtex(l3Qmul(h, cb)) : l3Qtex(cb) + '\\times(' + hT + ')=' + l3Qtex(l3Qmul(h, cb))) + '$。從甲樓頂看乙樓頂 ⟹ $\\dfrac{(' + hT + ')-H}{' + l3Qcoef(ca, 'H') + '+' + l3Qtex(l3Qmul(h, cb)) + '}=\\tan15°=2-\\sqrt3$，解得 $H=' + H + '$。',
             p: { v: 2, H: H, al: al, be: be, ans: { H: H } } };
  };

  /* ══ L3-11　箏形：餘弦定理算對稱軸，面積＝½·BD·AC＝2[ABD] 反求另一條對角線 ══ */
  L3.kiteDiag = function (r) {
    r();
    var a = r.int(1, 6), phi = r.pick([30, 45, 60, 90, 120, 135, 150]), b, v = r.int(0, 2);
    var rad = (phi % 60 === 0 || phi === 90) ? 1 : (phi % 45 === 0 ? 2 : 3);
    do { b = r.int(1, 9); } while (rad === 1 && a === b);
    var P = S(a, rad, 1), Q = S(b, 1, 1);
    var P2 = sToF(sMul(P, P)), Q2 = sToF(sMul(Q, Q));
    var cross = sMul(sMul(S(2, 1, 1), sMul(P, Q)), tv(phi).cos);
    var BD2 = Fr.sub(Fr.add(P2, Q2), sToF(cross)), BD = sqrtF(BD2);
    var area = sMul(sMul(P, Q), tv(phi).sin);
    var AC = sDiv(sMulF(area, F(2)), BD);
    var hb = '$\\overline{BD}$ 是箏形的對稱軸，垂直平分 $\\overline{AC}$ ⟹ 面積 $=\\dfrac12\\overline{BD}\\cdot\\overline{AC}$；另一方面面積 $=2[\\triangle ABD]$。'
           + '$\\overline{BD}^2=' + Fr.tex(P2) + '+' + Fr.tex(Q2) + '-2(' + sTex(P) + ')(' + sTex(Q) + ')\\cos' + phi + '°=' + Fr.tex(BD2) + '$ ⟹ $\\overline{BD}=' + sTex(BD) + '$；'
           + '$2[\\triangle ABD]=2\\cdot\\dfrac12(' + sTex(P) + ')(' + sTex(Q) + ')\\sin' + phi + '°=' + sTex(area) + '$ ⟹ $\\overline{AC}=' + (sTex(BD) === '1' ? '2\\times' + sTex(area) : '\\dfrac{2\\times' + sTex(area) + '}{' + sTex(BD) + '}') + '=' + sTex(AC) + '$' + (BD.r !== 1 ? '（分母有根號要有理化）' : '') + '。';
    var setup = '箏形 $ABCD$ 中 ' + T('\\overline{AB}=\\overline{BC}=' + sTex(P)) + '、' + T('\\overline{AD}=\\overline{CD}=' + sTex(Q)) + '、' + T('\\angle BAD=' + phi + '°') + '。';
    var nt1 = AC.r !== 1 ? '（化為最簡根式）' : '', nt2 = (AC.r !== 1 || BD.r !== 1) ? '（化為最簡根式）' : '';
    if (v === 0)
      return { q: setup + '求 ' + T('\\overline{AC}') + nt1 + '。',
               a: T(sTex(AC)),
               h: hb, p: { v: 0, a: a, b: b, rad: rad, phi: phi, ans: { AC: sArr(AC) } } };
    if (v === 1)
      return { q: setup + '求 (1) ' + T('\\overline{BD}') + '　(2) ' + T('\\overline{AC}') + nt2 + '。',
               a: '(1) ' + T(sTex(BD)) + '　(2) ' + T(sTex(AC)),
               h: hb, p: { v: 1, a: a, b: b, rad: rad, phi: phi, ans: { BD: sArr(BD), AC: sArr(AC) } } };
    return { q: setup + '求 (1) 箏形 $ABCD$ 的面積　(2) ' + T('\\overline{AC}') + nt1 + '。',
             a: '(1) ' + T(sTex(area)) + '　(2) ' + T(sTex(AC)),
             h: hb, p: { v: 2, a: a, b: b, rad: rad, phi: phi, ans: { area: sArr(area), AC: sArr(AC) } } };
  };

  /* ══ L3-12　圓內接四邊形＋兩圓周角互餘：AB²+CD²=4R² ══ */
  var L312T = [[6, 8, 10], [8, 6, 10], [12, 16, 20], [16, 12, 20], [10, 24, 26], [24, 10, 26], [18, 24, 30], [24, 18, 30],
               [16, 30, 34], [30, 16, 34], [14, 48, 50], [20, 21, 29], [21, 20, 29], [12, 35, 37], [35, 12, 37], [9, 12, 15], [12, 9, 15]];
  L3.cyclicPerp = function (r) {
    r();
    var v = r.int(0, 2), ph = r.int(0, 1), m, n, R2x4;
    if (v === 2) { var t = r.pick(L312T); m = t[0]; n = t[1]; R2x4 = t[2] * t[2]; }
    else { do { m = r.int(2, 16); n = r.int(2, 16); } while (m === n); R2x4 = m * m + n * n; }
    var cond = ph === 0 ? '且 ' + T('\\angle ACB+\\angle CAD=90°') : '且兩條對角線 ' + T('\\overline{AC}\\perp\\overline{BD}');
    var why = ph === 0 ? '$\\angle ACB$ 是弦 $\\overline{AB}$ 的圓周角、$\\angle CAD$ 是弦 $\\overline{CD}$ 的圓周角'
                       : '設 $\\overline{AC}$、$\\overline{BD}$ 交於 $E$，$\\angle AEB=90°$ ⟹ $\\angle ACB+\\angle CAD=90°$（$\\triangle AEC$ 的兩銳角），而 $\\angle ACB$ 對弦 $\\overline{AB}$、$\\angle CAD$ 對弦 $\\overline{CD}$';
    var hb = '正弦定理的 $2R$ 版本：' + why + ' ⟹ $\\overline{AB}=2R\\sin\\angle ACB$、$\\overline{CD}=2R\\sin\\angle CAD=2R\\cos\\angle ACB$ ⟹ $\\overline{AB}^2+\\overline{CD}^2=4R^2(\\sin^2+\\cos^2)=4R^2$。';
    if (v === 0) {
      var ar = F(R2x4, 4);
      return { q: '圓內接四邊形 $ABCD$ 中 ' + T('\\overline{AB}=' + m) + '、' + T('\\overline{CD}=' + n) + '，' + cond + '。求此圓的面積。',
               a: T(l3pi(ar)),
               h: hb + '代入 $4R^2=' + (m * m) + '+' + (n * n) + '=' + R2x4 + '$ ⟹ $R^2=' + Fr.tex(ar) + '$，面積 $=\\pi R^2=' + l3pi(ar) + '$。',
               p: { v: 0, ph: ph, AB: m, CD: n, ans: fr2(ar) } };
    }
    if (v === 1) {
      var R = sqrtF(F(R2x4, 4));
      return { q: '圓內接四邊形 $ABCD$ 中 ' + T('\\overline{AB}=' + m) + '、' + T('\\overline{CD}=' + n) + '，' + cond + '。求此圓的半徑 ' + T('R') + '。',
               a: T('R=' + sTex(R)),
               h: hb + '代入 $4R^2=' + (m * m) + '+' + (n * n) + '=' + R2x4 + '$ ⟹ $R=\\dfrac{\\sqrt{' + R2x4 + '}}{2}' + (sTex(R) === '\\dfrac{\\sqrt{' + R2x4 + '}}{2}' ? '' : '=' + sTex(R)) + '$。',
               p: { v: 1, ph: ph, AB: m, CD: n, ans: sArr(R) } };
    }
    var Rt = Fr.tex(F(Math.round(Math.sqrt(R2x4)), 2));
    return { q: '圓內接四邊形 $ABCD$ 內接於半徑 ' + T(Rt) + ' 的圓，' + T('\\overline{AB}=' + m) + '，' + cond + '。求 ' + T('\\overline{CD}') + '。',
             a: T('\\overline{CD}=' + n),
             h: hb + '代入 $4R^2=4(' + Rt + ')^2=' + R2x4 + '$ ⟹ $\\overline{CD}^2=' + R2x4 + '-' + (m * m) + '=' + (n * n) + '$ ⟹ $\\overline{CD}=' + n + '$。',
             p: { v: 2, ph: ph, AB: m, R2x4: R2x4, ans: n } };
  };

  /* ══ L3-13　作高把底邊切兩段：各用自己的角算，別去求 sinA ══ */
  var L313T = [[3, 4, 5], [4, 3, 5], [5, 12, 13], [12, 5, 13], [8, 15, 17], [15, 8, 17], [7, 24, 25], [24, 7, 25], [20, 21, 29], [21, 20, 29]];
  L3.altSplit = function (r) {
    r();
    var T1, T2, k, AD, BD, DC, BC, AB, AC, K, ok, tries = 0;
    do {
      T1 = r.pick(L313T); T2 = r.pick(L313T);
      var j = r.int(1, 3), g = gcd(T1[0], T2[0]);
      k = (T2[0] / g) * j;
      AD = k * T1[0]; BD = k * T1[1]; DC = AD * T2[1] / T2[0]; BC = BD + DC; AB = k * T1[2]; AC = AD * T2[2] / T2[0];
      K = F(BC * AD, 2);
      ok = K.d === 1 && AB <= 130 && BC <= 140 && AC <= 130 && BC * BC < AB * AB + AC * AC;
      tries++;
    } while (!ok && tries < 400);
    var gb = r.int(0, 2), gc = r.int(0, 2), ask = r.int(0, 2);
    var gbT = gb === 0 ? '\\tan B=' + Fr.tex(F(T1[0], T1[1])) : gb === 1 ? '\\sin B=' + Fr.tex(F(T1[0], T1[2])) : '\\cos B=' + Fr.tex(F(T1[1], T1[2]));
    var gcT = gc === 0 ? '\\cos C=' + Fr.tex(F(T2[1], T2[2])) : gc === 1 ? '\\tan C=' + Fr.tex(F(T2[0], T2[1])) : '\\sin C=' + Fr.tex(F(T2[0], T2[2]));
    var hb = '作高 $\\overline{AD}\\perp\\overline{BC}$（$D$ 在 $\\overline{BC}$ 上），兩個直角三角形各自用已知的三角比。'
           + '由 $' + gbT + '$ 得 ' + (gb === 1 ? '$\\cos B=' + Fr.tex(F(T1[1], T1[2])) + '$'
               : gb === 2 ? '$\\sin B=' + Fr.tex(F(T1[0], T1[2])) + '$'
               : '$\\sin B=' + Fr.tex(F(T1[0], T1[2])) + '$、$\\cos B=' + Fr.tex(F(T1[1], T1[2])) + '$') + ' ⟹ $\\overline{AD}=' + AB + '\\times' + Fr.tex(F(T1[0], T1[2])) + '=' + AD + '$、$\\overline{BD}=' + AB + '\\times' + Fr.tex(F(T1[1], T1[2])) + '=' + BD + '$。'
           + (gc === 1 ? '由 $' + gcT + '$ 直接得 $\\overline{DC}=' : '由 $' + gcT + '$ 得 $\\tan C=' + Fr.tex(F(T2[0], T2[1])) + '$ ⟹ $\\overline{DC}=')
           + '\\dfrac{\\overline{AD}}{\\tan C}=' + AD + '\\times' + Fr.tex(F(T2[1], T2[0])) + '=' + DC + '$ ⟹ $\\overline{BC}=' + BD + '+' + DC + '=' + BC + '$，面積 $=\\dfrac12\\times' + BC + '\\times' + AD + '=' + K.n + '$。';
    var tail = '想用 $\\dfrac12\\overline{AB}\\cdot\\overline{AC}\\sin A$ 會需要 $\\sin(B+C)$，那是高二上的和角公式；這一章的做法是切高。';
    var setup = '銳角 ' + ABC + ' 中 ' + T('\\overline{AB}=' + AB) + '、' + T(gbT) + '、' + T(gcT) + '。';
    if (ask === 0)
      return { q: setup + '求 ' + ABC + ' 的面積。', a: T(String(K.n)), h: hb + tail,
               p: { ask: 0, AB: AB, T1: T1, T2: T2, gb: gb, gc: gc, ans: { K: K.n } } };
    if (ask === 1)
      return { q: setup + '求 (1) ' + T('\\overline{BC}') + '　(2) ' + ABC + ' 的面積。', a: '(1) ' + T(String(BC)) + '　(2) ' + T(String(K.n)), h: hb + tail,
               p: { ask: 1, AB: AB, T1: T1, T2: T2, gb: gb, gc: gc, ans: { BC: BC, K: K.n } } };
    return { q: setup + '求 (1) ' + T('\\overline{AC}') + '　(2) ' + ABC + ' 的面積。',
             a: '(1) ' + T(String(AC)) + '　(2) ' + T(String(K.n)),
             h: hb + '另外 $\\overline{AC}=\\dfrac{\\overline{AD}}{\\sin C}=' + AD + '\\times' + Fr.tex(F(T2[2], T2[0])) + '=' + AC + '$。' + tail,
             p: { ask: 2, AB: AB, T1: T1, T2: T2, gb: gb, gc: gc, ans: { AC: AC, K: K.n } } };
  };

  /* ══ L3-14　邊與 sin 的同一個線性組合：每個 sin 都是「邊÷2R」 ══ */
  var L314C = [[1, -1, 1], [1, 1, 1], [1, 1, -1], [-1, 1, 1], [2, 1, 1], [1, 2, 1], [1, 1, 2],
               [2, -1, 2], [3, 1, 1], [2, 2, -1], [3, -2, 3], [2, 3, 2], [1, -1, 2], [2, -1, 1], [3, 2, -2], [1, 3, -1]];
  L3.sineLawR = function (r) {
    r();
    var co = r.pick(L314C), u = r.int(1, 6), w = r.int(1, 12), v = r.int(0, 2);
    if (w < u) w = u + r.int(0, 12 - u);
    var g0 = gcd(u, w); u /= g0; w /= g0;                                   /* 兩邊的倍數約到最簡：不出 4(…)=10(…) */
    var R = F(w, 2 * u), sd = l3lc(co, ['a', 'b', 'c']), ss = l3lc(co, ['\\sin A', '\\sin B', '\\sin C']);
    var why = '三角形不等式保證 $' + sd + '\\gt0$，可以約掉';
    var pre = ABC + ' 中 ' + T('a,b,c') + ' 為 ' + T('\\angle A,\\angle B,\\angle C') + ' 的對邊。';
    if (v === 1) {
      var k = F(w, u);
      return { q: pre + '若 ' + T('\\dfrac{' + sd + '}{' + ss + '}=' + Fr.tex(k)) + '，求外接圓半徑 ' + T('R') + '。',
               a: T('R=' + Fr.tex(R)),
               h: '正弦定理 $\\sin A=\\dfrac{a}{2R}$、$\\sin B=\\dfrac{b}{2R}$、$\\sin C=\\dfrac{c}{2R}$ 全部代入 ⟹ 分母 $=\\dfrac{1}{2R}(' + sd + ')$（' + why + '）⟹ 整個分式 $=2R=' + Fr.tex(k) + '$ ⟹ $R=' + Fr.tex(R) + '$。',
               p: { v: 1, co: co, u: u, w: w, ans: fr2(R) } };
    }
    var lhs = (u === 1 ? sd : u + '(' + sd + ')'), rhs = (w === 1 ? ss : w + '(' + ss + ')');
    if (v === 0)
      return { q: pre + '若 ' + T(lhs + '=' + rhs) + '，求外接圓半徑 ' + T('R') + '。',
               a: T('R=' + Fr.tex(R)),
               h: '正弦定理 $\\sin A=\\dfrac{a}{2R}$、$\\sin B=\\dfrac{b}{2R}$、$\\sin C=\\dfrac{c}{2R}$ 全部代入右式 $=\\dfrac{' + w + '}{2R}(' + sd + ')$；' + why + ' ⟹ $' + u + '=\\dfrac{' + w + '}{2R}$ ⟹ $R=' + Fr.tex(R) + '$。',
               p: { v: 0, co: co, u: u, w: w, ans: fr2(R) } };
    var ar = Fr.mul(R, R);
    return { q: pre + '若 ' + T(lhs + '=' + rhs) + '，求外接圓的面積。',
             a: T(l3pi(ar)),
             h: '正弦定理 $\\sin A=\\dfrac{a}{2R}$ 等全部代入右式 $=\\dfrac{' + w + '}{2R}(' + sd + ')$；' + why + ' ⟹ $' + u + '=\\dfrac{' + w + '}{2R}$ ⟹ $R=' + Fr.tex(R) + '$，面積 $=\\pi R^2=' + l3pi(ar) + '$。',
             p: { v: 2, co: co, u: u, w: w, ans: fr2(ar) } };
  };

  /* ══ L3-15　面積＋兩邊求第三邊：sinC 定了但 cosC 有正負兩解 ══ */
  L3.areaTwoSol = function (r) {
    r();
    var t, m, n, K, A1, A2, ok, tries = 0;
    do {
      t = tri(r); m = r.int(1, 2); n = r.int(2, 12);
      K = F(m * n * t[0], 2);
      A1 = t[2] * t[2] * m * m + n * n - 2 * m * n * t[1];
      A2 = t[2] * t[2] * m * m + n * n + 2 * m * n * t[1];
      ok = K.d === 1 && A1 > 0 && A2 <= 4000 && t[2] * m <= 40 && n <= 40;
      tries++;
    } while (!ok && tries < 400);
    var p = t[2] * m, q = n, sC = F(t[0], t[2]), cC = F(t[1], t[2]), v = r.int(0, 2);
    var hb = '$\\dfrac12\\cdot' + p + '\\cdot' + q + '\\sin C=' + K.n + '$ ⟹ $\\sin C=' + Fr.tex(sC) + '$ ⟹ $\\cos C=\\pm' + Fr.tex(cC) + '$。面積只給 $\\sin$，所以要想兩解。'
           + '餘弦定理 $\\overline{AB}^2=' + (p * p) + '+' + (q * q) + '-2(' + p + ')(' + q + ')\\cos C=' + (p * p + q * q) + '\\mp' + (2 * m * n * t[1]) + '$ ⟹ $' + A1 + '$ 或 $' + A2 + '$。';
    var setup = ABC + ' 的面積為 ' + T(String(K.n)) + '，' + T('\\overline{CA}=' + p) + '、' + T('\\overline{CB}=' + q) + '。';
    if (v === 0)
      return { q: setup + '求 ' + T('\\overline{AB}') + ' 的所有可能值。',
               a: T(sqrtTex(A1)) + ' 或 ' + T(sqrtTex(A2)),
               h: hb + '所以 $\\overline{AB}=' + sqrtTex(A1) + '$（$\\angle C$ 為銳角）或 $' + sqrtTex(A2) + '$（$\\angle C$ 為鈍角）。',
               p: { v: 0, p: p, q: q, K: K.n, ans: [A1, A2] } };
    if (v === 1)
      return { q: setup + '若 ' + T('\\angle C') + ' 為鈍角，求 ' + T('\\overline{AB}') + '。',
               a: T(sqrtTex(A2)),
               h: hb + '$\\angle C$ 為鈍角 ⟹ 取 $\\cos C=-' + Fr.tex(cC) + '$ ⟹ $\\overline{AB}^2=' + A2 + '$ ⟹ $\\overline{AB}=' + sqrtTex(A2) + '$。',
               p: { v: 1, p: p, q: q, K: K.n, ans: A2 } };
    return { q: setup + '求 ' + T('\\overline{AB}') + ' 的所有可能值，並指出各自對應 ' + T('\\angle C') + ' 為銳角還是鈍角。',
             a: T('\\overline{AB}=' + sqrtTex(A1)) + ' 時 ' + T('\\angle C') + ' 為銳角、' + T('\\overline{AB}=' + sqrtTex(A2)) + ' 時 ' + T('\\angle C') + ' 為鈍角',
             h: hb + '邊長較短的那個對應 $\\cos C=' + Fr.tex(cC) + '\\gt0$（銳角），較長的對應 $\\cos C=-' + Fr.tex(cC) + '\\lt0$（鈍角）。',
             p: { v: 2, p: p, q: q, K: K.n, ans: [A1, A2] } };
  };

  /* ══════════ 2026-09-28 擴充：L3-16～L3-18 的類似題 ══════════ */
  /* L3-16　四邊形只給四邊與對角線的銳夾角：四個小三角形各寫一次餘弦定理，AB²+CD²−BC²−DA²＝−2·AC·BD·cos∠AOB */
  L3.quadDiagAngle = function (r) {
    r();
    var phi = r.pick([60, 60, 45, 30]), mm = phi === 60 ? 1 : phi === 45 ? 2 : 3, sg = r.sign(), a, b, c, d, s2, ok;
    /* OA=a√mm、OC=c√mm、OB=b、OD=d；∠AOB 的 cos＝sg·cosφ；2·OA·OB·cos∠AOB＝sg·k·a·b（k：60°→1、45°→2、30°→3） */
    var kk = phi === 60 ? 1 : phi === 45 ? 2 : 3;
    do {
      a = r.int(1, 8); b = r.int(1, 9); c = r.int(1, 8); d = r.int(1, 9);
      s2 = [mm * a * a + b * b - sg * kk * a * b, b * b + mm * c * c + sg * kk * b * c, mm * c * c + d * d - sg * kk * c * d, d * d + mm * a * a + sg * kk * d * a];
      ok = s2.every(function (v) { return v > 0; }) && (s2.filter(function (v) { var q = simpSqrt(v); return q[1] === 1; }).length >= 1);
    } while (!ok);
    var Sv = s2[0] + s2[2] - s2[1] - s2[3], area = phi === 60 ? S(Math.abs(Sv), 3, 4) : phi === 45 ? S(Math.abs(Sv), 1, 4) : S(Math.abs(Sv), 3, 12);
    var nm = ['AB', 'BC', 'CD', 'DA'], sides = nm.map(function (n, i) { return T(ov(n) + '=' + sqrtTex(s2[i])); }).join('、');
    return { q: '凸四邊形 $ABCD$ 中 ' + sides + '，兩條對角線所夾的銳角為 ' + T(phi + '°') + '。求四邊形 $ABCD$ 的面積。',
             a: T(sTex(area)),
             h: '設對角線交於 $O$，' + T(ov('OA') + '=p,\\ ' + ov('OB') + '=q,\\ ' + ov('OC') + '=r,\\ ' + ov('OD') + '=s') + '，' + T('\\angle AOB=\\alpha') + '。四個小三角形各寫一次餘弦定理（對頂角相等、鄰角互補，$\\cos$ 差一個負號），相加減得 ' + T(ov('AB') + '^2+' + ov('CD') + '^2-' + ov('BC') + '^2-' + ov('DA') + '^2=-2\\cos\\alpha\\,(p+r)(q+s)') + '。左邊 ' + T('=' + s2[0] + '+' + s2[2] + '-' + s2[1] + '-' + s2[3] + '=' + Sv) + '，所以 ' + T(ov('AC') + '\\cdot' + ov('BD') + '=\\dfrac{' + Math.abs(Sv) + '}{2\\cos' + phi + '°}') + '，面積 ' + T('=\\dfrac12\\cdot' + ov('AC') + '\\cdot' + ov('BD') + '\\sin' + phi + '°') + '。',
             p: { phi: phi, sg: sg, seg: [a, b, c, d], s2: s2, ans: sArr(area) } };
  };

  /* L3-17　角平分線＋等腰（AB＝AD）：分比設 pk、qk，同一個半角在兩個小三角形各寫一次餘弦定理 */
  L3.bisectorIsos = function (r) {
    r();
    var p, q; do { p = r.int(1, 9); q = r.int(2, 12); } while (p >= q || gcd(p, q) !== 1 || q - p > 9);
    var side = r.int(0, 1), t = r.int(0, 2), k2 = F(q, q - p), cosH = F(p + q, 2 * q);
    var eq2 = Fr.mul(F(p * p), k2), ot2 = Fr.mul(F(q * q), k2), cosA = Fr.div(Fr.sub(Fr.add(eq2, ot2), F((p + q) * (p + q))), Fr.mul(F(2 * p * q), k2));
    var E = side === 0 ? 'AB' : 'AC', O = side === 0 ? 'AC' : 'AB', BD = side === 0 ? p : q, DC = side === 0 ? q : p, half = side === 0 ? '\\angle BAD' : '\\angle DAC';
    var ask = t === 0 ? T('\\cos' + half) : t === 1 ? T(ov('AB')) + ' 與 ' + T(ov('AC')) : T('\\cos\\angle BAC');
    var eqS = sqrtF(eq2), otS = sqrtF(ot2);
    var ans = t === 0 ? T('\\cos' + half + '=' + Fr.tex(cosH)) : t === 1 ? T(ov(E) + '=' + sTex(eqS)) + '、' + T(ov(O) + '=' + sTex(otS)) : T('\\cos\\angle BAC=' + Fr.tex(cosA));
    return { q: '$\\triangle ABC$ 中，$\\overline{AD}$ 是 $\\angle BAC$ 的角平分線（$D$ 在 $\\overline{BC}$ 上），' + T(ov('BD') + '=' + BD) + '、' + T(ov('DC') + '=' + DC) + '，且 ' + T(ov(E) + '=' + ov('AD')) + '。求 ' + ask + '。',
             a: ans,
             h: '分比：' + T(ov('AB') + ':' + ov('AC') + '=' + BD + ':' + DC) + '，設 ' + T(ov(E) + '=' + ov('AD') + '=' + (p === 1 ? '' : p) + 'k') + '、' + T(ov(O) + '=' + q + 'k') + '。兩個小三角形共用半角 $\\beta$，各寫一次餘弦定理：' + T(p + '^2=2(' + (p === 1 ? '' : p) + 'k)^2(1-\\cos\\beta)') + '、' + T(q + '^2=(' + (p === 1 ? '' : p) + 'k)^2+(' + q + 'k)^2-2\\cdot' + (p === 1 ? '' : p + '\\cdot') + q + 'k^2\\cos\\beta') + '，消去 $\\cos\\beta$ 得 ' + T('k^2=' + Fr.tex(k2)) + '。' + (t === 2 ? '再對整個 $\\triangle ABC$ 用餘弦定理（' + T(ov('BC') + '=' + (p + q)) + '）。' : ''),
             p: { p: p, q: q, side: side, t: t, ans: { cosH: fr2(cosH), eq2: fr2(eq2), ot2: fr2(ot2), cosA: fr2(cosA) } } };
  };

  /* L3-18　兩個方位＋兩個俯角（或仰角）：俯視圖裡用餘弦定理求兩點距離 */
  function n28bear(b) {
    b = ((b % 360) + 360) % 360;
    if (b % 90 === 0) return ['正北', '正東', '正南', '正西'][b / 90];
    if (b < 90) return '北 $' + b + '°$ 東'; if (b < 180) return '南 $' + (180 - b) + '°$ 東';
    if (b < 270) return '南 $' + (b - 180) + '°$ 西'; return '北 $' + (360 - b) + '°$ 西';
  }
  L3.depressTwoDir = function (r) {
    r();
    var COT = { 30: S(1, 3, 1), 45: S(1, 1, 1), 60: S(1, 3, 3) }, al, be, ga, b1, b2, TP, TQ, cross, pq2, h, ok;
    do {
      al = r.pick([30, 45, 60]); be = r.pick([30, 45, 60]); ga = r.pick([30, 60, 90, 120, 150]); h = r.pick([6, 12, 18, 24, 30, 36, 45, 60, 90, 120]);
      TP = sMulF(COT[al], F(h)); TQ = sMulF(COT[be], F(h));
      cross = sMulF(sMul(sMul(TP, TQ), tv(ga).cos), F(2));
      ok = (cross.c === 0 || cross.r === 1);
      if (ok) pq2 = Fr.sub(Fr.add(sToF(sMul(TP, TP)), sToF(sMul(TQ, TQ))), cross.c === 0 ? F(0) : sToF(cross));
      ok = ok && pq2.n > 0;
    } while (!ok);
    b1 = r.int(0, 11) * 30 + r.pick([0, 0, 15]); b2 = b1 + r.sign() * ga;
    var PQ = sqrtF(pq2), v = r.int(0, 1), dirs = '$P$ 在塔的' + n28bear(b1) + '方、$Q$ 在塔的' + n28bear(b2) + '方';
    var q = v === 0 ? '一座塔高 ' + T(String(h)) + ' 公尺，從塔頂看地面上 $P$、$Q$ 兩點的俯角分別為 ' + T(al + '°') + '、' + T(be + '°') + '；' + dirs + '（塔底與 $P$、$Q$ 在同一水平面上）。求 $P$、$Q$ 兩點的距離。'
                    : '在地面上 $P$、$Q$ 兩點分別測得一座塔頂的仰角為 ' + T(al + '°') + '、' + T(be + '°') + '，' + dirs + '，塔高 ' + T(String(h)) + ' 公尺（塔底與 $P$、$Q$ 在同一水平面上）。求 $P$、$Q$ 兩點的距離。';
    return { q: q,
             a: T(ov('PQ') + '=' + sTex(PQ)) + ' 公尺',
             h: '側視圖：塔底 $T$，' + T(ov('TP') + '=\\dfrac{' + h + '}{\\tan' + al + '°}=' + sTex(TP)) + '、' + T(ov('TQ') + '=\\dfrac{' + h + '}{\\tan' + be + '°}=' + sTex(TQ)) + '。俯視圖：兩個方位相差 ' + T('\\angle PTQ=' + ga + '°') + '，在 $\\triangle PTQ$ 用餘弦定理 ' + T(ov('PQ') + '^2=' + ov('TP') + '^2+' + ov('TQ') + '^2-2\\cdot' + ov('TP') + '\\cdot' + ov('TQ') + '\\cos' + ga + '°') + '。',
             p: { h: h, al: al, be: be, ga: ga, b: [b1, b2], v: v, ans: fr2(pq2) } };
  };

  var META_L3 = [['rightCoQuad', '直角三角形＋互餘換角解二次'], ['tanCosQuad', 'a cosθ＝b tanθ：化 sinθ 的二次方程'], ['coPairSum', '互餘配對整串求和'],
                 ['reduceSum', '誘導公式化簡（給範圍）'], ['polarFromTrig', '(±sinα, ±cosα) 化極坐標'], ['polarRatio', '四個極坐標點的長度比與面積比'],
                 ['tanRecip', 'tanθ＋1/tanθ 型＋範圍定號'], ['tanSecLin', 'tanθ±1/cosθ＝k 與平方關係聯立'], ['linTrigAcute', 'a cosθ＋b sinθ＝c（銳角）'],
                 ['twoTowers', '兩棟樓的仰角（tan15°＝2−√3）'], ['kiteDiag', '箏形：對稱軸與另一條對角線'], ['cyclicPerp', '圓內接四邊形配 2R sin'],
                 ['altSplit', '作高分兩段求面積'], ['sineLawR', '邊化 2R sin 求外接圓半徑'], ['areaTwoSol', '面積反求第三邊的兩解'],
                 ['quadDiagAngle', '四邊形：四邊＋對角線夾角求面積'], ['bisectorIsos', '角平分線＋等腰：兩次餘弦定理'], ['depressTwoDir', '兩個方位＋兩個俯角求兩點距離']];
  /* 固定題 L3-n 對應的類似題型 */
  var L3_FIX = { 'L3-1': 'rightCoQuad', 'L3-2': 'tanCosQuad', 'L3-3': 'coPairSum', 'L3-4': 'reduceSum', 'L3-5': 'polarFromTrig',
                 'L3-6': 'polarRatio', 'L3-7': 'tanRecip', 'L3-8': 'tanSecLin', 'L3-9': 'linTrigAcute', 'L3-10': 'twoTowers',
                 'L3-11': 'kiteDiag', 'L3-12': 'cyclicPerp', 'L3-13': 'altSplit', 'L3-14': 'sineLawR', 'L3-15': 'areaTwoSol', 'L3-16': 'quadDiagAngle', 'L3-17': 'bisectorIsos', 'L3-18': 'depressTwoDir' };

  /* ══════════════════════════════════════════════════════════
     L0　章首先備診斷（5 型）：畢氏定理（國中）、特殊直角三角形的邊長比（國中）、相似三角形的比例（國中）、根式化簡與有理化（高一上 ch1）、兩點的斜率（高一上 ch2）
     ══════════════════════════════════════════════════════════ */
  var L0 = {};
  function l0sn(x) { return x < 0 ? '(' + x + ')' : String(x); }
  L0.pythag = function (r) {
    var v = r.int(0, 1), a = r.int(2, 9), b = r.int(2, 9);
    if (v === 0) {
      var c2 = a * a + b * b;
      return { q: '直角三角形的兩股長為 ' + T(String(a)) + ' 與 ' + T(String(b)) + '，求斜邊長。', a: T(sqrtTex(c2)),
        h: '畢氏定理：斜邊 $^2=' + a + '^2+' + b + '^2=' + c2 + '$，開根號後要化簡。本章「終邊上一點到原點的距離 $r=\\sqrt{x^2+y^2}$」就是它。',
        p: { v: v, a: a, b: b, ans: c2 } };
    }
    var c = Math.max(a, b) + r.int(1, 5), leg = Math.min(a, b), d2 = c * c - leg * leg;
    return { q: '直角三角形的斜邊長為 ' + T(String(c)) + '、一股長為 ' + T(String(leg)) + '，求另一股長。', a: T(sqrtTex(d2)),
      h: '另一股 $^2=' + c + '^2-' + leg + '^2=' + d2 + '$（斜邊的平方<b>減</b>已知股的平方），開根號後要化簡。本章由 $\\sin\\theta$ 求 $\\cos\\theta$ 就是這個算式。',
      p: { v: v, c: c, leg: leg, ans: d2 } };
  };
  L0.specialTri = function (r) {
    var v = r.int(0, 2), k = r.int(2, 16);
    if (v === 0) return { q: T('30°') + '-' + T('60°') + '-' + T('90°') + ' 的直角三角形中，最短邊（' + T('30°') + ' 的對邊）長 ' + T(String(k)) + '。求斜邊長與另一股長。', a: '斜邊 ' + T(String(2 * k)) + '、另一股 ' + T(k + '\\sqrt{3}'),
      h: '三邊的比是 $1:\\sqrt3:2$（對 $30°$：對 $60°$：斜邊），最短邊是 $' + k + '$，所以斜邊 $=2\\times' + k + '$、另一股 $=' + k + '\\sqrt3$。本章 $\\sin30°=\\frac12$、$\\cos30°=\\frac{\\sqrt3}2$ 都是從這個三角形讀出來的。',
      p: { v: v, k: k, ans: [2 * k, k] } };
    if (v === 1) return { q: '等腰直角三角形（' + T('45°') + '-' + T('45°') + '-' + T('90°') + '）的一股長 ' + T(String(k)) + '，求斜邊長。', a: T(k + '\\sqrt{2}'),
      h: '三邊的比是 $1:1:\\sqrt2$，斜邊 $=' + k + '\\sqrt2$。本章 $\\sin45°=\\cos45°=\\frac{\\sqrt2}2$ 就是「股 $\\div$ 斜邊」。',
      p: { v: v, k: k, ans: [k, 2] } };
    var e = 2 * k;
    return { q: '正三角形的邊長為 ' + T(String(e)) + '，求它的高與面積。', a: '高 ' + T(k + '\\sqrt{3}') + '、面積 ' + T(k * k + '\\sqrt{3}'),
      h: '作高把正三角形切成兩個 $30°$-$60°$-$90°$：半邊 $' + k + '$、高 $' + k + '\\sqrt3$，面積 $=\\dfrac12\\times' + e + '\\times' + k + '\\sqrt3$。本章面積公式 $\\frac12ab\\sin C$ 代 $60°$ 會得到同一個數。',
      p: { v: v, e: e, ans: [k, k * k] } };
  };
  L0.similarRatio = function (r) {
    var a = r.int(2, 6), b = r.int(a + 1, 9), m = r.int(2, 5), t = 0;
    while (gcd(a, b) !== 1 && t++ < 20) b = r.int(a + 1, 10);
    var x = F(b * m * a, a);                         /* 小三角形兩邊 a、b；大三角形對應 a 的邊是 a·m，求對應 b 的邊 */
    return { q: '兩個相似三角形中，小三角形的兩邊長為 ' + T(String(a)) + '、' + T(String(b)) + '；大三角形對應 ' + T(String(a)) + ' 的邊長為 ' + T(String(a * m)) + '。求大三角形對應 ' + T(String(b)) + ' 的邊長，以及大、小三角形的面積比。', a: '邊長 ' + T(String(b * m)) + '、面積比 ' + T(m * m + ':1'),
      h: '相似比 $=\\dfrac{' + a * m + '}{' + a + '}=' + m + '$，所以對應邊 $=' + b + '\\times' + m + '$；面積比是相似比的平方 $' + m + '^2:1$。本章的三角比之所以「只跟角度有關」，就是因為相似三角形的邊長比固定。',
      p: { a: a, b: b, m: m, ans: [b * m, m * m] } };
  };
  L0.surdRational = function (r) {
    var v = r.int(0, 1), d = r.pick([2, 3, 5, 6, 7]), a = r.int(1, 9);
    if (v === 0) { var g = gcd(a, d);
      return { q: '化簡 ' + T('\\dfrac{' + a + '}{\\sqrt{' + d + '}}') + '（分母有理化）。', a: T(sTex(S(a, d, d))),
        h: '分子分母同乘 $\\sqrt{' + d + '}$：$\\dfrac{' + a + '\\sqrt{' + d + '}}{' + d + '}$' + (g > 1 ? '，再約分 $' + g + '$' : '') + '。本章 $\\tan30°=\\dfrac1{\\sqrt3}=\\dfrac{\\sqrt3}3$ 就是這一步。',
        p: { v: v, a: a, d: d, ans: sArr(S(a, d, d)) } }; }
    var k = r.pick([2, 3, 5, 6, 7, 10]), m = r.pick([2, 3, 4, 5, 6]), N = k * m * m;
    return { q: '化簡 ' + T('\\sqrt{' + N + '}') + '。', a: T(sqrtTex(N)),
      h: '把 $' + N + '$ 拆成「完全平方數 $\\times$ 剩下的」：$' + N + '=' + (m * m) + '\\times' + k + '$，所以 $\\sqrt{' + N + '}=' + m + '\\sqrt{' + k + '}$。本章餘弦定理算出來的邊長幾乎都要這樣化簡。',
      p: { v: v, N: N, ans: [m, k] } };
  };
  L0.slope2 = function (r) {
    var x1 = r.int(-5, 5), y1 = r.int(-5, 5), dx = r.pick([1, 2, 3, 4, 5, 6]), dy; do { dy = r.int(-6, 6); } while (dy === 0);
    var m = F(dy, dx);
    return { q: '求通過 ' + T('A(' + x1 + ',' + y1 + ')') + '、' + T('B(' + (x1 + dx) + ',' + (y1 + dy) + ')') + ' 兩點的直線斜率，並說明這條直線由左到右是上升還是下降。', a: '斜率 ' + T(Fr.tex(m)) + '，' + (dy > 0 ? '上升' : '下降'),
      h: '斜率 $=\\dfrac{' + (y1 + dy) + '-' + l0sn(y1) + '}{' + (x1 + dx) + '-' + l0sn(x1) + '}=' + Fr.tex(m) + '$；斜率為正是上升、為負是下降。本章「斜率 $=\\tan(\\text{斜角})$」把它和角度接起來：斜率為負時斜角是負的。',
      p: { A: [x1, y1], B: [x1 + dx, y1 + dy], ans: fr2(m) } };
  };
  var META_L0 = [['pythag', '畢氏定理'], ['specialTri', '特殊直角三角形的邊長比'], ['similarRatio', '相似三角形的比例'], ['surdRational', '根式化簡與有理化'], ['slope2', '兩點的斜率']];
  /* 先備題型 → 該去哪裡複習 */
  var PREREQ = {
    pythag: { txt: '畢氏定理（國中）：由 sin 求 cos、終邊上一點到原點的距離，都要用它', link: null },
    specialTri: { txt: '30°-60°-90° 與 45°-45°-90° 的邊長比（國中）：特殊角的三角比都從這兩個三角形讀出來', link: null },
    similarRatio: { txt: '相似三角形的對應邊成比例（國中）：三角比「只跟角度有關」就是靠它', link: null },
    surdRational: { txt: '根式化簡與分母有理化（高一上第一章 數與式）：特殊角的值、餘弦定理的邊長都要化簡', link: '../g10a-ch01/practice.html#L1' },
    slope2: { txt: '兩點的斜率（高一上第二章 直線與圓）：本章的「斜率＝tan(斜角)」從這裡接上角度', link: '../g10a-ch02/practice.html#L1' }
  };
  /* ══════════════════════════════════════════════════════════
     對照題：同一型抽兩題，只差一個關鍵特徵（f 由 p 算出；keep 的欄位要相同）
     ══════════════════════════════════════════════════════════ */
  function sign3(x) { return x > 0 ? 1 : x < 0 ? -1 : 0; }
  function quadOf(x, y) { return x > 0 ? (y > 0 ? 1 : 4) : (y > 0 ? 2 : 3); }
  var CONTRAST = {
    'L1.coterminal': { f: function (p) { return p.ans.quad; }, why: '同界角只差 $360^\\circ$ 的整數倍：先加減 $360^\\circ$ 把角度拉進 $0^\\circ\\sim360^\\circ$，再看落在哪個象限。象限不同，後面三個三角比的正負就不同（一全正、二正弦、三正切、四餘弦）。' },
    'L1.pointTrig': { f: function (p) { return quadOf(p.x, p.y); }, why: '終邊上一點 $(x,y)$：$r=\\sqrt{x^2+y^2}$ 永遠是正的，$\\sin=\\dfrac yr$、$\\cos=\\dfrac xr$、$\\tan=\\dfrac yx$ 的正負直接由 $x,y$ 的正負決定。點換了象限，絕對值的算法一樣，只有符號跟著變。' },
    'L1.quadFind': { f: function (p) { return p.kind === 0 ? p.ans : p.quad; }, keep: ['kind'], why: '象限決定三角比的正負（一全正、二只有 $\\sin$ 正、三只有 $\\tan$ 正、四只有 $\\cos$ 正）。由正負判斷象限，是把這張表倒過來查；已知一個三角比求另外兩個，則是先用直角三角形算出<b>絕對值</b>，再用象限<b>定號</b>，兩題的算法一樣，差別只在象限。' },
    'L1.cosLawSide': { f: function (p) { return p.A > 90; }, why: '餘弦定理 $a^2=b^2+c^2-2bc\\cos A$：夾角是銳角時 $\\cos A\\gt0$、第三邊比畢氏定理短；夾角是鈍角時 $\\cos A\\lt0$，「減負變加」，第三邊比畢氏定理長。' },
    'L1.cosLawAngle': { f: function (p) { return p.ans.shape; }, why: '判斷三角形的形狀只要看<b>最大邊</b>所對的角：$\\cos=\\dfrac{\\text{兩小邊平方和}-\\text{最大邊平方}}{2\\times\\text{兩小邊}}$，正 ⟹ 銳角三角形、$0$ ⟹ 直角、負 ⟹ 鈍角。' },
    'L1.ssaCount': { f: function (p) { return p.ans; }, why: 'SSA（兩邊與其中一邊的對角）要比較對邊 $a$ 與高 $h=b\\sin A$：$a\\lt h$ 無解、$a=h$ 恰一解（直角）、$h\\lt a\\lt b$ 兩解、$a\\ge b$ 一解。畫出「從 $C$ 甩一條長 $a$ 的線段」就看得出來。' },
    'L1.polarDist': { f: function (p) { return p.ans.gap > 90; }, why: '兩個極坐標點的距離用餘弦定理，夾角就是極角的差：夾角是鈍角時 $\\cos$ 為負，距離比「兩個 $r$ 的畢氏」還長；面積 $\\dfrac12r_1r_2\\sin(\\text{夾角})$ 則不受銳角鈍角影響。' },
    'L1.bisectorLen': { f: function (p) { return p.A; }, why: '角平分線長用「面積拆兩塊」：$\\dfrac12bc\\sin A=\\dfrac12(b+c)\\cdot\\overline{AD}\\sin\\dfrac A2$。$A=60^\\circ$、$90^\\circ$、$120^\\circ$ 時半角是 $30^\\circ$、$45^\\circ$、$60^\\circ$，公式一樣、代的特殊角值不同。' },
    'L2.quadSumProd': { f: function (p) { return p.quad; }, why: '已知 $\\sin\\theta+\\cos\\theta$：平方得 $\\sin\\theta\\cos\\theta$，再算 $(\\sin\\theta-\\cos\\theta)^2$；<b>差的正負要靠象限判斷</b>：第二象限 $\\sin\\gt0\\gt\\cos$，差為正；第四象限相反。' },
    'L2.sineRatio': { f: function (p) { return p.ans.shape; }, why: '$\\sin A:\\sin B:\\sin C=a:b:c$，所以給正弦的比就是給邊長的比：最大邊所對的角用餘弦定理算 $\\cos$，正負決定是銳角、直角還是鈍角三角形。' },
    'L2.bisector': { f: function (p) { return p.A; }, why: '角平分線的三件事（分對邊成 $c:b$、長度用面積法、兩塊面積比也是 $c:b$）對任何夾角都成立；夾角換了，只是 $\\sin A$、$\\sin\\dfrac A2$ 代的特殊角值換了。' }
  };
  /* 2026-09-28 擴充題型的對照題 */
  CONTRAST['L1.polarSym'] = { f: function (p) { return p.k; }, keep: ['t'], why: '對 $y$ 軸對稱極角變成 $180°-\\theta$、對 $x$ 軸變成 $-\\theta$、對原點變成 $180°+\\theta$、對 $y=x$ 變成 $90°-\\theta$、逆時針轉 $90°$ 變成 $90°+\\theta$；半徑不變，坐標放大幾倍半徑就放大幾倍。' };
  CONTRAST['L1.quadDiagArea'] = { f: function (p) { return p.t; }, why: '三題用的都是 $[ABCD]=\\dfrac12\\overline{AC}\\cdot\\overline{BD}\\sin\\theta$：求面積就直接代；給面積反求對角線或夾角，就把同一條式子倒過來解。夾角是銳角或鈍角，正弦都一樣。' };
  CONTRAST['L2.trigQuadEq'] = { f: function (p) { return p.uf; }, keep: ['t'], why: '有 $\\cos^2\\theta$ 就換成 $1-\\sin^2\\theta$，有 $\\sin^2\\theta$ 就換成 $1-\\cos^2\\theta$，留下來的那個函數才是未知數。解出來的值要在 $-1$ 到 $1$ 之間，再回單位圓找角。' };
  CONTRAST['L2.chordSineRatio'] = { f: function (p) { return p.t; }, why: '三種情形都是「弦長 $=2R\\sin$（它所對的圓周角）」：同一條弦放在兩個圓裡，圓周角的正弦越小，圓越大；同一個圓裡的兩條弦，長度比就是所對圓周角的正弦比。' };
  CONTRAST['L2.areaSplitCevian'] = { f: function (p) { return p.t; }, why: '都是把大三角形的面積拆成兩塊，三塊都用「兩邊夾角」的面積公式；未知數在哪一塊就解哪一個。夾角若是 $\\angle BAC-90°$，用 $\\sin(\\angle BAC-90°)=-\\cos\\angle BAC$。' };
  /* ══════════════════════════════════════════════════════════
     2026-10-02　附圖題（讀圖型）：圖由產生器依亂數參數即時畫成 inline SVG，放在 q 裡，圖跟著數字變
     共用畫圖小工具 fig*()（與 g11a-ch01 同一套樣式）：三角形與標籤、角的小弧、直角記號、圓與圓上的點、方格。
     規則：坐標一律由參數算（不目測）、圖照比例畫；圖上文字用 <text>（不放 KaTeX、不能出現錢字號與反斜線）；
           圖上的長度標籤由根式數 S(c,r,d) 直接轉成（labS），與精確值一致；
           要給驗算器讀的元素帶 data-k（驗算器從圖上的坐標與標籤文字代回，不看 p）。
     L1 4 型、L2 4 型、L3 3 型（L3-19～L3-21 的類似題）；key 一律接在 META 最後，既有題型同種子輸出不變。
     ══════════════════════════════════════════════════════════ */
  var FIGC = { ink: '#3a2a2e', line: '#7a2e3c', hot: '#b03a55', soft: '#8a7378', grid: '#ddd2d5', fill: 'rgba(176,58,85,.2)' };
  var MINUS = '−';
  function n1(v) { var s = (Math.round(v * 10) / 10).toFixed(1); if (s === '-0.0') s = '0.0'; return s.replace(/\.0$/, ''); }
  function n2(v) { var s = (Math.round(v * 100) / 100).toFixed(2); if (s === '-0.00') s = '0.00'; return s.replace(/\.?0+$/, ''); }
  function figAttr(o) { var s = ''; for (var k in o) { if (o[k] !== undefined && o[k] !== null && o[k] !== false) s += ' ' + k + '="' + o[k] + '"'; } return s; }
  function figSvg(w, h, label, body) { return '<svg class="qfig" viewBox="0 0 ' + w + ' ' + h + '" width="' + w + '" height="' + h + '" role="img" aria-label="' + label + '">' + body + '</svg>'; }
  function figLine(x1, y1, x2, y2, o) { o = o || {}; return '<line' + figAttr({ 'data-k': o.k, x1: n2(x1), y1: n2(y1), x2: n2(x2), y2: n2(y2), stroke: o.c || FIGC.line, 'stroke-width': o.w || 1.6, 'stroke-dasharray': o.dash ? '4 3' : null, 'stroke-linecap': 'round' }) + '/>'; }
  function figText(x, y, s, o) { o = o || {}; return '<text' + figAttr({ 'data-k': o.k, x: n1(x), y: n1(y), 'font-size': o.fs || 14, fill: o.c || FIGC.ink, 'text-anchor': o.anchor || 'middle', 'font-style': o.it ? 'italic' : null }) + '>' + s + '</text>'; }
  function figPath(d, o) { o = o || {}; return '<path' + figAttr({ 'data-k': o.k, d: d, fill: o.fill || 'none', stroke: o.c === 'none' ? null : (o.c || FIGC.line), 'stroke-width': o.c === 'none' ? null : (o.w || 1.8), 'stroke-dasharray': o.dash ? '4 3' : null, 'stroke-linejoin': 'round' }) + '/>'; }
  function figDot(x, y, o) { o = o || {}; return '<circle' + figAttr({ 'data-k': o.k, cx: n2(x), cy: n2(y), r: o.r || 3, fill: o.c || FIGC.line }) + '/>'; }
  function figCircle(cx, cy, R, k) { return '<circle' + figAttr({ 'data-k': k, cx: n2(cx), cy: n2(cy), r: n2(R), fill: 'none', stroke: FIGC.line, 'stroke-width': 1.8 }) + '/>'; }
  function figPt(cx, cy, R, a) { return [cx + R * Math.cos(a), cy - R * Math.sin(a)]; }       /* 數學角 a（逆時針）→ 像素點 */
  function ptS(p) { return n2(p[0]) + ' ' + n2(p[1]); }
  /* 標籤值：字串（整數、θ、30°、3√2…）或 { neg, num, den }（直式分數）。labS：根式數 S → 標籤值 */
  function labS(v) { if (v.c === 0) return '0'; var m = Math.abs(v.c), num = v.r === 1 ? String(m) : (m === 1 ? '' : m) + '√' + v.r; return v.d === 1 ? (v.c < 0 ? MINUS : '') + num : { neg: v.c < 0, num: num, den: String(v.d) }; }
  function labTxt(v) { return typeof v === 'string' ? v : (v.neg ? MINUS : '') + v.num + '/' + v.den; }
  function labW(v, fs) { fs = fs || 14; if (typeof v === 'string') return v.length * fs * 0.58; return Math.max(v.num.length, v.den.length) * fs * 0.58 + 4 + (v.neg ? fs * 0.7 : 0); }
  /* 在 (x, yc) 畫標籤值，yc 是垂直中心；anchor：middle（預設）／start／end */
  function figVal(x, yc, v, o) {
    o = o || {}; var fs = o.fs || 14, w = labW(v, fs), x0 = o.anchor === 'start' ? x : o.anchor === 'end' ? x - w : x - w / 2;
    if (typeof v === 'string') return figText(x0 + w / 2, yc + fs * 0.36, v, { fs: fs, c: o.c, k: o.k, it: o.it });
    var sw = v.neg ? fs * 0.7 : 0, cx = x0 + sw + (w - sw) / 2, s = '<g' + figAttr({ 'data-k': o.k }) + '>';
    if (v.neg) s += figText(x0 + fs * 0.3, yc + fs * 0.36, MINUS, { fs: fs, c: o.c });
    s += figText(cx, yc - 3.5, v.num, { fs: fs, c: o.c }) + figLine(cx - (w - sw) / 2 + 1, yc, cx + (w - sw) / 2 - 1, yc, { c: o.c || FIGC.ink, w: 1 }) + figText(cx, yc + fs * 0.92, v.den, { fs: fs, c: o.c });
    return s + '</g>';
  }
  /* 圓弧（圓心、半徑為像素；a0→a1 為數學角、逆時針、a1>a0）。cont=true 時只給 A 指令（接在前一點後面） */
  function figArcD(cx, cy, R, a0, a1, cont) {
    return (cont ? '' : 'M ' + ptS(figPt(cx, cy, R, a0)) + ' ') + 'A ' + n2(R) + ' ' + n2(R) + ' 0 ' + (a1 - a0 > Math.PI ? 1 : 0) + ' 0 ' + ptS(figPt(cx, cy, R, a1));
  }
  function figArrow(x1, y1, x2, y2, o) {
    o = o || {}; var a = Math.atan2(y2 - y1, x2 - x1), L = 8, wv = 3.2, c = o.c || FIGC.ink, bx = x2 - L * Math.cos(a), by = y2 - L * Math.sin(a);
    return figLine(x1, y1, bx, by, { c: c, w: o.w || 1.2, k: o.k }) + '<path d="M ' + n2(x2) + ' ' + n2(y2) + ' L ' + n2(bx - wv * Math.sin(a)) + ' ' + n2(by + wv * Math.cos(a)) + ' L ' + n2(bx + wv * Math.sin(a)) + ' ' + n2(by - wv * Math.cos(a)) + ' Z" fill="' + c + '"/>';
  }
  /* 數學坐標（y 向上）等比例放進寬 W、圖形最高 maxH 的框；回傳像素點 P、比例尺 sc、畫布高 H */
  function figFit(pts, o) {
    var x0 = Infinity, x1 = -Infinity, y0 = Infinity, y1 = -Infinity;
    pts.forEach(function (p) { x0 = Math.min(x0, p[0]); x1 = Math.max(x1, p[0]); y0 = Math.min(y0, p[1]); y1 = Math.max(y1, p[1]); });
    var W = o.W || 300, l = o.l || 34, rr = o.r || 34, t = o.t || 24, b = o.b || 28;
    var sc = Math.min((W - l - rr) / (x1 - x0 || 1), (o.maxH || 160) / (y1 - y0 || 1)), ox = l + ((W - l - rr) - (x1 - x0) * sc) / 2;
    return { P: pts.map(function (p) { return [ox + (p[0] - x0) * sc, t + (y1 - p[1]) * sc]; }), sc: sc, W: W, H: Math.ceil(t + (y1 - y0) * sc + b) };
  }
  function figCen(P) { var x = 0, y = 0; P.forEach(function (p) { x += p[0]; y += p[1]; }); return [x / P.length, y / P.length]; }
  function figAway(p, c, d) { var dx = p[0] - c[0], dy = p[1] - c[1], L = Math.sqrt(dx * dx + dy * dy) || 1; return [p[0] + dx / L * d, p[1] + dy / L * d]; }
  function figName(p, c, name, d) { var q = figAway(p, c, d || 12); return figText(q[0], q[1] + 4.8, name, { fs: 14, it: 1 }); }       /* 點名：放在離 c 較遠的那一側 */
  function figPoly(P, o) { o = o || {}; return figPath('M ' + P.map(ptS).join(' L ') + ' Z', o); }
  /* 邊 pq 的長度標籤：放在邊的中點、離 c 較遠的那一側（o.inside：靠 c 的那一側） */
  function figSideVal(p, q, c, v, o) {
    o = o || {}; var mx = (p[0] + q[0]) / 2, my = (p[1] + q[1]) / 2, dx = q[0] - p[0], dy = q[1] - p[1], L = Math.sqrt(dx * dx + dy * dy) || 1, nx = -dy / L, ny = dx / L;
    if ((nx * (c[0] - mx) + ny * (c[1] - my) > 0) !== !!o.inside) { nx = -nx; ny = -ny; }
    var fs = o.fs || 14, w = labW(v, fs), hh = typeof v === 'string' ? fs * 0.9 : fs * 2.2, dist = (o.d === undefined ? 5 : o.d) + Math.abs(nx) * w / 2 + Math.abs(ny) * hh / 2;
    return figVal(mx + nx * dist, my + ny * dist, v, { fs: fs, k: o.k, c: o.c, it: o.it });
  }
  /* 由頂點 v 看 p、q 的數學角 [a0, a1]：a0→a1 逆時針且不超過 180° */
  function figAng(v, p, q) {
    var a = Math.atan2(v[1] - p[1], p[0] - v[0]), b = Math.atan2(v[1] - q[1], q[0] - v[0]), d = b - a;
    while (d < 0) d += 2 * Math.PI; while (d >= 2 * Math.PI) d -= 2 * Math.PI;
    return d <= Math.PI ? [a, a + d] : [b, b + 2 * Math.PI - d];
  }
  /* 角的小弧＋標籤（lab 為 null 不標）；標籤放在角的內部、沿角平分線，角越小放得越遠 */
  function figAngMark(v, p, q, lab, o) {
    o = o || {}; var aa = figAng(v, p, q), th = aa[1] - aa[0], rr = o.r || 16, fs = o.fs || 13, s = figPath(figArcD(v[0], v[1], rr, aa[0], aa[1]), { c: o.c || FIGC.soft, w: 1.3, k: o.k });
    if (lab !== null && lab !== undefined) {
      var lw = labW(lab, fs), pad = lab.charAt(lab.length - 1) === '°' ? 3 : 7, lr = o.lr || Math.max(rr + 6 + lw / 2, Math.min(60, (lw / 2 + pad) / Math.sin(th / 2))), m = figPt(v[0], v[1], lr, (aa[0] + aa[1]) / 2);
      s += figVal(m[0], m[1], lab, { fs: fs, k: o.lk, it: lab === 'θ' });
    }
    return s;
  }
  function figRight(v, p, q, sz) {                                                                 /* 直角記號 */
    sz = sz || 8; var u = figAway(v, p, -sz), w = figAway(v, q, -sz), m = [u[0] + w[0] - v[0], u[1] + w[1] - v[1]];
    return '<polyline' + figAttr({ points: n2(u[0]) + ',' + n2(u[1]) + ' ' + n2(m[0]) + ',' + n2(m[1]) + ' ' + n2(w[0]) + ',' + n2(w[1]), fill: 'none', stroke: FIGC.soft, 'stroke-width': 1.2 }) + '/>';
  }
  function figOpt(i, t) { return '<span class="qopt">(' + i + ') ' + t + '</span>'; }
  function sInt(n) { return S(n, 1, 1); }
  function sSqrt(n) { return S(1, n, 1); }

  /* ────────── L1　6 讀圖題：直角三角形、仰角俯角、兩邊夾角、方格紙上的廣義角 ────────── */
  /* 直角三角形：直角在 R，兩股 RP、RQ；tf（0～7）決定擺法（左右翻、上下翻、兩股對調），θ 標在 at（P 或 Q） */
  function figRightTriSvg(pl, ql, tf, at, labs) {
    var pts = [[0, 0], [pl, 0], [0, ql]].map(function (p) { var x = p[0], y = p[1], t; if (tf & 1) x = -x; if (tf & 2) y = -y; if (tf & 4) { t = x; x = y; y = t; } return [x, y]; });
    var ft = figFit(pts, { W: 280, maxH: 150, l: 50, r: 50, t: 26, b: 32 }), R = ft.P[0], P = ft.P[1], Q = ft.P[2], c = figCen(ft.P);
    var s = figPoly(ft.P, { k: 'tri', w: 2, fill: 'rgba(176,58,85,.07)' }) + figRight(R, P, Q);
    s += at === 'P' ? figAngMark(P, R, Q, 'θ', { lk: 'th', fs: 14 }) : figAngMark(Q, R, P, 'θ', { lk: 'th', fs: 14 });
    if (labs.p) s += figSideVal(R, P, c, labs.p, { k: 'len' });
    if (labs.q) s += figSideVal(R, Q, c, labs.q, { k: 'len' });
    if (labs.h) s += figSideVal(P, Q, c, labs.h, { k: 'len' });
    return figSvg(ft.W, ft.H, '直角三角形，兩個邊長與角 θ 標示在圖上', s);
  }
  var FRT_TRI = [[3, 4, 5], [4, 3, 5], [5, 12, 13], [12, 5, 13], [8, 15, 17], [15, 8, 17], [6, 8, 10], [8, 6, 10]];
  L1.figRightTri = function (r) {
    var mode, lp, lq, hyp, rat, guard = 0, t, a, b, c;
    do {
      mode = r.pick(['legs', 'legs', 'hyp']);
      if (r() < 0.35) { t = r.pick(FRT_TRI); lp = sInt(t[0]); lq = sInt(t[1]); hyp = sInt(t[2]); }
      else if (mode === 'legs') { a = r.int(1, 9); b = r.int(1, 9); lp = sInt(a); lq = sInt(b); hyp = sSqrt(a * a + b * b); }
      else { c = r.int(2, 12); a = r.int(1, c - 1); lp = sInt(a); lq = sSqrt(c * c - a * a); hyp = sInt(c); }
      rat = sNum(lp) / sNum(lq);
    } while ((rat < 0.42 || rat > 2.4) && guard++ < 200);
    var known = 'p', tmp; if (r() < 0.5) { tmp = lp; lp = lq; lq = tmp; known = 'q'; }
    var at = r.pick(['P', 'Q']), tf = r.int(0, 7), opp = at === 'P' ? lq : lp, adj = at === 'P' ? lp : lq;
    var sn = sDiv(opp, hyp), cs = sDiv(adj, hyp), tn = sDiv(opp, adj);
    var labs = mode === 'legs' ? { p: labS(lp), q: labS(lq) } : (known === 'p' ? { p: labS(lp), h: labS(hyp) } : { q: labS(lq), h: labS(hyp) });
    var third = mode === 'legs' ? '斜邊 $=\\sqrt{' + hxSq(sTex(lp)) + '+' + hxSq(sTex(lq)) + '}=' + sTex(hyp) + '$' : '另一股 $=\\sqrt{' + hxSq(sTex(hyp)) + '-' + hxSq(sTex(known === 'p' ? lp : lq)) + '}=' + sTex(known === 'p' ? lq : lp) + '$';
    return { q: '如圖，直角三角形有兩個邊長標示在圖上，求 ' + T('\\sin\\theta') + '、' + T('\\cos\\theta') + '、' + T('\\tan\\theta') + '。' + figRightTriSvg(sNum(lp), sNum(lq), tf, at, labs),
      a: T('\\sin\\theta=' + sTex(sn)) + '、' + T('\\cos\\theta=' + sTex(cs)) + '、' + T('\\tan\\theta=' + sTex(tn)),
      h: '先認邊：直角對面的是斜邊，沒有碰到 $\\theta$ 的那條股是對邊，夾出 $\\theta$ 的那條股是鄰邊。用畢氏定理補第三邊：' + third + '。所以對邊 $=' + sTex(opp) + '$、鄰邊 $=' + sTex(adj) + '$、斜邊 $=' + sTex(hyp) + '$，再套 $\\sin=\\dfrac{\\text{對}}{\\text{斜}}$、$\\cos=\\dfrac{\\text{鄰}}{\\text{斜}}$、$\\tan=\\dfrac{\\text{對}}{\\text{鄰}}$。',
      p: { mode: mode, known: known, at: at, tf: tf, lp: sArr(lp), lq: sArr(lq), hyp: sArr(hyp), ans: { sin: sArr(sn), cos: sArr(cs), tan: sArr(tn) } } };
  };

  /* 仰角、俯角測量圖。mode：elev（一個仰角＋水平距離）／dep（俯角＋高）／two（同側兩個仰角＋兩點距離） */
  var FELV_TWO = { '30,45': [1, 1], '30,60': [0, 1], '45,60': [3, 1] };                          /* h = w(rat + surd√3)/2 的 [rat, surd] */
  function figElevSvg(mode, len, th1, th2) {
    var t1 = Math.tan(th1 * Math.PI / 180), t2 = th2 ? Math.tan(th2 * Math.PI / 180) : 0, pts, ft, s = '', A, B, H, Tp, E, gy;
    if (mode === 'elev') {
      pts = [[0, 0], [len, 0], [len, len * t1]]; ft = figFit(pts, { W: 300, maxH: 158, l: 44, r: 50, t: 26, b: 28 }); A = ft.P[0]; H = ft.P[1]; Tp = ft.P[2]; gy = A[1];
      s += figLine(A[0] - 16, gy, H[0] + 20, gy, { c: FIGC.ink, w: 1.2, k: 'ground' }) + figLine(H[0], H[1], Tp[0], Tp[1], { w: 3.2, k: 'tower' }) + figLine(A[0], A[1], Tp[0], Tp[1], { c: FIGC.hot, w: 1.6, k: 'sight' });
      s += figRight(H, A, Tp) + figAngMark(A, H, Tp, th1 + '°', { lk: 'ang' }) + figDot(A[0], A[1], { k: 'A', r: 2.6 });
      s += figText(A[0] - 4, gy + 16, 'A', { it: 1 }) + figText(H[0] + 3, gy + 16, 'H', { it: 1 }) + figText(Tp[0], Tp[1] - 8, 'T', { it: 1 });
      s += figVal((A[0] + H[0]) / 2, gy + 14, String(len), { k: 'len' }) + figText(H[0] + 13, (H[1] + Tp[1]) / 2 + 5, '?', { c: FIGC.hot });
      return figSvg(ft.W, ft.H, '仰角測量圖：A 到塔底 H 的距離與仰角標示在圖上', s);
    }
    if (mode === 'dep') {
      var x = len / t1; pts = [[0, len], [0, 0], [x, 0], [x, len]]; ft = figFit(pts, { W: 300, maxH: 150, l: 56, r: 40, t: 28, b: 28 }); Tp = ft.P[0]; H = ft.P[1]; B = ft.P[2]; E = ft.P[3]; gy = H[1];
      s += figLine(H[0] - 14, gy, B[0] + 22, gy, { c: FIGC.ink, w: 1.2, k: 'ground' }) + figLine(H[0], H[1], Tp[0], Tp[1], { w: 3.2, k: 'tower' }) + figLine(Tp[0], Tp[1], E[0] + 10, E[1], { c: FIGC.soft, w: 1.2, dash: 1, k: 'level' }) + figLine(Tp[0], Tp[1], B[0], B[1], { c: FIGC.hot, w: 1.6, k: 'sight' });
      s += figRight(H, B, Tp) + figAngMark(Tp, E, B, th1 + '°', { lk: 'ang' }) + figDot(B[0], B[1], { k: 'B', r: 2.6 });
      s += figText(Tp[0] - 4, Tp[1] - 8, 'T', { it: 1 }) + figText(H[0] - 3, gy + 16, 'H', { it: 1 }) + figText(B[0] + 4, gy + 16, 'B', { it: 1 });
      s += figVal(H[0] - 9, (H[1] + Tp[1]) / 2, String(len), { k: 'len', anchor: 'end' }) + figText((H[0] + B[0]) / 2, gy + 17, '?', { c: FIGC.hot });
      return figSvg(ft.W, ft.H, '俯角測量圖：崖高與俯角標示在圖上', s);
    }
    var hN = len / (1 / t1 - 1 / t2), xH = len + hN / t2;
    pts = [[0, 0], [len, 0], [xH, 0], [xH, hN]]; ft = figFit(pts, { W: 300, maxH: 150, l: 34, r: 46, t: 26, b: 28 }); A = ft.P[0]; B = ft.P[1]; H = ft.P[2]; Tp = ft.P[3]; gy = A[1];
    s += figLine(A[0] - 14, gy, H[0] + 20, gy, { c: FIGC.ink, w: 1.2, k: 'ground' }) + figLine(H[0], H[1], Tp[0], Tp[1], { w: 3.2, k: 'tower' }) + figLine(A[0], A[1], Tp[0], Tp[1], { c: FIGC.hot, w: 1.6, k: 'sightA' }) + figLine(B[0], B[1], Tp[0], Tp[1], { c: FIGC.hot, w: 1.6, k: 'sightB' });
    s += figRight(H, A, Tp) + figAngMark(A, H, Tp, th1 + '°', { lk: 'angA', r: 20 }) + figAngMark(B, H, Tp, th2 + '°', { lk: 'angB', r: 13 }) + figDot(A[0], A[1], { k: 'A', r: 2.6 }) + figDot(B[0], B[1], { k: 'B', r: 2.6 });
    s += figText(A[0] - 4, gy + 16, 'A', { it: 1 }) + figText(B[0] + 2, gy + 16, 'B', { it: 1 }) + figText(H[0] + 3, gy + 16, 'H', { it: 1 }) + figText(Tp[0], Tp[1] - 8, 'T', { it: 1 });
    s += figVal((A[0] + B[0]) / 2, gy + 14, String(len), { k: 'len' }) + figText(H[0] + 13, (H[1] + Tp[1]) / 2 + 5, '?', { c: FIGC.hot });
    return figSvg(ft.W, ft.H, '兩次仰角測量圖：A、B 的距離與兩個仰角標示在圖上', s);
  }
  L1.figElev = function (r) {
    var mode = r.pick(['elev', 'dep', 'two', 'two']), len = r.pick([10, 12, 15, 18, 20, 24, 30, 36, 40, 45, 50, 60]), th, v;
    if (mode === 'elev') {
      th = r.pick([30, 45, 60]); v = sMulF(tv(th).tan, F(len));
      return { q: '如圖，在地面上 ' + T('A') + ' 點測得塔頂 ' + T('T') + ' 的仰角，仰角與 ' + T('A') + ' 到塔底 ' + T('H') + ' 的距離都標示在圖上（長度單位：公尺）。求塔高 ' + T(ov('TH')) + '。' + figElevSvg('elev', len, th),
        a: T(sTex(v)) + ' 公尺',
        h: '從圖上讀出：鄰邊（水平距離）$\\overline{AH}=' + len + '$，仰角 $' + th + '°$，要求的塔高是對邊。已知鄰邊求對邊用 $\\tan$：$\\overline{TH}=' + len + '\\tan' + th + '°$。',
        p: { mode: mode, len: len, th: th, ans: sArr(v) } };
    }
    if (mode === 'dep') {
      th = r.pick([30, 45, 60]); v = sDiv(sInt(len), tv(th).tan);
      return { q: '如圖，從懸崖頂 ' + T('T') + ' 看海面上的小船 ' + T('B') + '，俯角與崖高 ' + T(ov('TH')) + ' 都標示在圖上（長度單位：公尺），虛線是過 ' + T('T') + ' 的水平線。求小船到崖底 ' + T('H') + ' 的距離 ' + T(ov('BH')) + '。' + figElevSvg('dep', len, th),
        a: T(sTex(v)) + ' 公尺',
        h: '俯角是「水平線往下看」的角，它和 $\\angle TBH$ 是內錯角，所以 $\\angle TBH=' + th + '°$。在直角三角形 $TBH$ 裡，對邊 $\\overline{TH}=' + len + '$，要求鄰邊：$\\overline{BH}=\\dfrac{' + len + '}{\\tan' + th + '°}$（分母有根號要有理化）。',
        p: { mode: mode, len: len, th: th, ans: sArr(v) } };
    }
    var pair = r.pick([[30, 45], [30, 60], [45, 60]]), co = FELV_TWO[pair.join(',')], rat = F(co[0] * len, 2), surd = S(co[1] * len, 3, 2);
    return { q: '如圖，' + T('A') + '、' + T('B') + ' 與塔底 ' + T('H') + ' 在同一直線上。在 ' + T('A') + '、' + T('B') + ' 兩點測得塔頂 ' + T('T') + ' 的仰角，兩個仰角與 ' + T(ov('AB')) + ' 的長都標示在圖上（長度單位：公尺）。求塔高 ' + T(ov('TH')) + '。' + figElevSvg('two', len, pair[0], pair[1]),
      a: T(hxTwo(rat, surd)) + ' 公尺',
      h: '設塔高 $h$。從圖上讀出：$A$ 的仰角 $' + pair[0] + '°$、$B$ 的仰角 $' + pair[1] + '°$、$\\overline{AB}=' + len + '$。$\\overline{AH}=\\dfrac{h}{\\tan' + pair[0] + '°}$、$\\overline{BH}=\\dfrac{h}{\\tan' + pair[1] + '°}$，圖上 $A$、$B$ 在塔的同一側，所以兩段相減等於 $' + len + '$，解 $h$（分母有根號要有理化）。',
      p: { mode: mode, len: len, th1: pair[0], th2: pair[1], ans: { rat: fr2(rat), surd: sArr(surd) } } };
  };

  /* 三角形標兩邊一夾角：A 在原點，AB＝c、AC＝b、∠A；or＝0 底邊 AB 水平、1 左右翻、2 A 在上方 */
  function figSASSvg(bN, cN, Adeg, or, bLab, cLab) {
    var A = Adeg * Math.PI / 180, ph = or === 2 ? -Math.PI / 2 - A / 2 : 0, pts = [[0, 0], [cN * Math.cos(ph), cN * Math.sin(ph)], [bN * Math.cos(ph + A), bN * Math.sin(ph + A)]];
    if (or === 1) pts = pts.map(function (p) { return [-p[0], p[1]]; });
    var ft = figFit(pts, { W: 300, maxH: 150, l: 46, r: 46, t: 28, b: 32 }), P = ft.P, c = figCen(P);
    var s = figPoly(P, { k: 'tri', w: 2, fill: 'rgba(176,58,85,.07)' }) + figAngMark(P[0], P[1], P[2], Adeg + '°', { lk: 'ang' });
    s += figName(P[0], c, 'A') + figName(P[1], c, 'B') + figName(P[2], c, 'C');
    s += figSideVal(P[0], P[1], c, cLab, { k: 'len' }) + figSideVal(P[0], P[2], c, bLab, { k: 'len' });
    return figSvg(ft.W, ft.H, '三角形 ABC，AB、AC 的長與角 A 標示在圖上', s);
  }
  L1.figSAS = function (r) {
    var A, m, n, b, c, a2, rat, guard = 0, k;
    do {
      A = r.pick([30, 45, 60, 60, 120, 120, 135, 150]); m = r.int(1, 6); n = r.int(2, 9);
      k = A === 60 || A === 120 ? 1 : A === 45 || A === 135 ? 2 : 3;                                /* b = m√k，c = n；2bc cosA = ±k·m·n（k=1 時 ±mn） */
      if (k === 1) m = r.int(2, 9);
      b = S(m, k, 1); c = sInt(n); a2 = k * m * m + n * n + (A > 90 ? 1 : -1) * k * m * n; rat = sNum(b) / n;
    } while ((rat < (A <= 45 ? 0.6 : 0.45) || rat > (A <= 45 ? 1.7 : 2.2) || a2 <= 0) && guard++ < 200);
    var swap = r() < 0.5, or = r.int(0, A <= 45 ? 1 : 2),      /* 夾角小的時候 A 不放在上方：角度標籤要離 A 最近 */
        AB = swap ? b : c, AC = swap ? c : b, K = sMulF(sMul(sMul(b, c), tv(A).sin), F(1, 2));
    return { q: '如圖，' + ABC + ' 的兩邊長與它們的夾角標示在圖上。求 ' + T(ov('BC')) + ' 與 ' + ABC + ' 的面積。' + figSASSvg(sNum(AC), sNum(AB), A, or, labS(AC), labS(AB)),
      a: T(ov('BC') + '=' + sqrtTex(a2)) + '，面積 ' + T(sTex(K)),
      h: '從圖上讀出 $\\overline{AB}=' + sTex(AB) + '$、$\\overline{AC}=' + sTex(AC) + '$、夾角 $\\angle A=' + A + '°$。兩邊夾角求第三邊用餘弦定理：$\\overline{BC}^2=' + hxSq(sTex(AB)) + '+' + hxSq(sTex(AC)) + '-2\\cdot' + sTex(AB) + '\\cdot' + sTex(AC) + '\\cos' + A + '°$；面積 $=\\dfrac12\\cdot' + sTex(AB) + '\\cdot' + sTex(AC) + '\\sin' + A + '°$。',
      p: { A: A, AB: sArr(AB), AC: sArr(AC), or: or, ans: { a2: a2, K: sArr(K) } } };
  };

  /* 方格紙上的標準位置角：終邊過格子點 P(x, y) */
  function figGridPtSvg(x, y) {
    var N = Math.max(3, Math.max(Math.abs(x), Math.abs(y)) + 1), c = Math.min(30, Math.floor(208 / (2 * N))), W = 280, gx = (W - 2 * N * c) / 2, gy = 20, H = gy + 2 * N * c + 22, ox = gx + N * c, oy = gy + N * c, i, s = '';
    for (i = 0; i <= 2 * N; i++) s += figLine(gx + i * c, gy, gx + i * c, gy + 2 * N * c, { c: FIGC.grid, w: 1, k: 'gv' }) + figLine(gx, gy + i * c, gx + 2 * N * c, gy + i * c, { c: FIGC.grid, w: 1, k: 'gh' });
    s += figArrow(gx - 6, oy, gx + 2 * N * c + 14, oy, { k: 'xaxis' }) + figArrow(ox, gy + 2 * N * c + 6, ox, gy - 13, { k: 'yaxis' });
    s += figText(gx + 2 * N * c + 12, oy + (y < 0 && x > 0 ? -7 : 15), 'x', { it: 1 }) + figText(ox + (x > 0 ? -10 : 10), gy - 6, 'y', { it: 1 });
    var ang = Math.atan2(y, x); if (ang < 0) ang += 2 * Math.PI;
    var px = ox + x * c, py = oy - y * c, L = Math.sqrt(x * x + y * y), ex = px + x / L * c * 0.55, ey = py - y / L * c * 0.55;
    s += figLine(ox, oy, ex, ey, { c: FIGC.hot, w: 2, k: 'ray' });
    var la = ang / 2; [Math.PI / 2, Math.PI, 3 * Math.PI / 2].forEach(function (ax) { if (Math.abs(la - ax) < 0.28) la = ax - 0.28; });
    s += figPath(figArcD(ox, oy, 13, 0, ang), { c: FIGC.soft, w: 1.3 });
    var lp = figPt(ox, oy, ang < 1.1 ? Math.min(c * 1.9, Math.max(25, 9 / Math.sin(ang / 2))) : 25, la);
    s += figText(lp[0], lp[1] + 5, 'θ', { it: 1 });
    var nx = -y / L, ny = -x / L;                                                                  /* 像素空間裡與 OP 垂直的方向；點名放在離較近那條軸比較遠的一側 */
    if (Math.abs(y) < Math.abs(x) ? ny * (y > 0 ? -1 : 1) < 0 : nx * (x > 0 ? 1 : -1) < 0) { nx = -nx; ny = -ny; }
    s += figDot(px, py, { k: 'P', c: FIGC.hot, r: 3.4 }) + figText(px + nx * 12, py + ny * 12 + 4.8, 'P', { it: 1 });
    s += figText(ox + (y > 0 ? (x > 0 ? -9 : 9) : (x > 0 ? -15 : 9)), oy + (y > 0 || x < 0 ? 14 : 19), 'O', { fs: 13, it: 1 });      /* O 放在角的弧沒有掃到的那一側 */
    return figSvg(W, H, '方格紙上的坐標平面，角 θ 的終邊通過格子點 P', s);
  }
  L1.figGridPoint = function (r) {
    var x, y, guard = 0;
    do {
      if (r() < 0.3) { var t = r.pick([[3, 4], [4, 3]]); x = r.sign() * t[0]; y = r.sign() * t[1]; }
      else { x = r.nz(-4, 4); y = r.nz(-4, 4); }
    } while (gcd(x, y) !== 1 && Math.abs(x) !== Math.abs(y) && guard++ < 50);
    var r2 = x * x + y * y, rr = sSqrt(r2), sn = sDiv(sInt(y), rr), cs = sDiv(sInt(x), rr), tn = S(y, 1, x);
    return { q: '如圖，方格紙上每一小格的邊長都是 ' + T('1') + '，標準位置角 ' + T('\\theta') + ' 的終邊通過格子點 ' + T('P') + '。求 ' + T('\\sin\\theta') + '、' + T('\\cos\\theta') + '、' + T('\\tan\\theta') + '。' + figGridPtSvg(x, y),
      a: T('\\sin\\theta=' + sTex(sn)) + '、' + T('\\cos\\theta=' + sTex(cs)) + '、' + T('\\tan\\theta=' + sTex(tn)),
      h: '先從方格數出 $P$ 的坐標：往' + (x > 0 ? '右' : '左') + ' $' + Math.abs(x) + '$ 格、往' + (y > 0 ? '上' : '下') + ' $' + Math.abs(y) + '$ 格，$P(' + x + ',' + y + ')$ 在' + hxQuadXY(x, y) + '。$r=\\sqrt{' + hxSq(String(x)) + '+' + hxSq(String(y)) + '}=' + sTex(rr) + '$，再用 $\\sin\\theta=\\dfrac yr$、$\\cos\\theta=\\dfrac xr$、$\\tan\\theta=\\dfrac yx$。',
      p: { x: x, y: y, ans: { sin: sArr(sn), cos: sArr(cs), tan: sArr(tn) } } };
  };

  L1_H1.figRightTri = '這是「看圖求直角三角形的三角比」：先認出斜邊（直角對面）、$\\theta$ 的對邊與鄰邊，缺的那一邊用畢氏定理補。';
  L1_H1.figElev = '這是「看圖做仰角、俯角測量」：先在圖上找到直角三角形，看已知的是對邊還是鄰邊，再決定 $\\tan$ 要乘還是除；兩次測量就設高為 $h$ 列一條式子。';
  L1_H1.figSAS = '這是「看圖讀兩邊一夾角」：先確認圖上標的角是不是兩條已知邊夾出來的角，是的話第三邊用餘弦定理、面積用兩邊夾角公式。';
  L1_H1.figGridPoint = '這是「方格紙上的廣義角」：先數格子讀出終邊上那一點的坐標，再算它到原點的距離 $r$，三個三角比就是 $\\dfrac yr$、$\\dfrac xr$、$\\dfrac yx$。';
  L1_SOL.figRightTri = function (p, o) {
    var lp = solS(p.lp), lq = solS(p.lq), hyp = solS(p.hyp), opp = p.at === 'P' ? lq : lp, adj = p.at === 'P' ? lp : lq, kn = p.known === 'p' ? lp : lq, ot = p.known === 'p' ? lq : lp;
    var st1 = p.mode === 'legs' ? '圖上標的兩條邊夾著直角記號，是兩股：$' + sTex(lp) + '$ 與 $' + sTex(lq) + '$。畢氏定理補斜邊：$\\sqrt{' + hxSq(sTex(lp)) + '+' + hxSq(sTex(lq)) + '}=' + sTex(hyp) + '$。'
      : '圖上標的 $' + sTex(hyp) + '$ 在直角的對面，是斜邊；$' + sTex(kn) + '$ 是一股。畢氏定理補另一股：$\\sqrt{' + hxSq(sTex(hyp)) + '-' + hxSq(sTex(kn)) + '}=' + sTex(ot) + '$。';
    return [st1, '認邊：沒有碰到 $\\theta$ 的那條股是對邊 $=' + sTex(opp) + '$；和斜邊一起夾出 $\\theta$ 的那條股是鄰邊 $=' + sTex(adj) + '$；斜邊 $=' + sTex(hyp) + '$。',
      '代進定義：' + T('\\sin\\theta=' + solEq('\\dfrac{' + sTex(opp) + '}{' + sTex(hyp) + '}', sTex(solS(p.ans.sin)))) + '、' + T('\\cos\\theta=' + solEq('\\dfrac{' + sTex(adj) + '}{' + sTex(hyp) + '}', sTex(solS(p.ans.cos)))) + '、' + T('\\tan\\theta=' + solEq('\\dfrac{' + sTex(opp) + '}{' + sTex(adj) + '}', sTex(solS(p.ans.tan)))) + '' + (opp.r > 1 || adj.r > 1 || hyp.r > 1 ? '（分母有根號要有理化）' : '') + '。' + solFin(o)];
  };
  L1_SOL.figElev = function (p, o) {
    if (p.mode === 'elev') return ['從圖上讀出：$\\overline{AH}=' + p.len + '$（水平距離，是仰角的鄰邊），仰角 $\\angle TAH=' + p.th + '°$，$\\angle AHT=90°$。',
      '塔高 $\\overline{TH}$ 是對邊，鄰邊求對邊用正切：' + T(ov('TH') + '=' + p.len + '\\tan' + p.th + '°') + '，其中 ' + T('\\tan' + p.th + '°=' + sTex(tv(p.th).tan)) + '。', '算出 ' + T(sTex(solS(p.ans))) + ' 公尺。' + solFin(o)];
    if (p.mode === 'dep') return ['俯角是從水平線（虛線）往下量到視線 $\\overline{TB}$ 的角。虛線和海面平行，所以內錯角相等：$\\angle TBH=' + p.th + '°$。',
      '在直角三角形 $TBH$ 裡（$\\angle THB=90°$），$\\overline{TH}=' + p.len + '$ 是 $\\angle TBH$ 的對邊，$\\overline{BH}$ 是鄰邊：' + T('\\tan' + p.th + '°=\\dfrac{' + p.len + '}{' + ov('BH') + '}') + '。',
      T(ov('BH') + '=\\dfrac{' + p.len + '}{\\tan' + p.th + '°}') + '，代入 ' + T('\\tan' + p.th + '°=' + sTex(tv(p.th).tan)) + '，分母有根號要有理化，得 ' + T(sTex(solS(p.ans))) + ' 公尺。' + solFin(o)];
    var rat = solF(p.ans.rat), surd = solS(p.ans.surd);
    return ['從圖上讀出：$A$ 的仰角 $' + p.th1 + '°$、$B$ 的仰角 $' + p.th2 + '°$、$\\overline{AB}=' + p.len + '$，而且 $A$、$B$ 在塔的同一側。',
      '設塔高 $h$：' + T(ov('AH') + '=\\dfrac{h}{\\tan' + p.th1 + '°}') + '、' + T(ov('BH') + '=\\dfrac{h}{\\tan' + p.th2 + '°}') + '。同側 ⟹ ' + T(ov('AH') + '-' + ov('BH') + '=' + ov('AB')) + '，也就是 ' + T('\\dfrac{h}{\\tan' + p.th1 + '°}-\\dfrac{h}{\\tan' + p.th2 + '°}=' + p.len) + '。',
      '代入 ' + T('\\tan' + p.th1 + '°=' + sTex(tv(p.th1).tan)) + '、' + T('\\tan' + p.th2 + '°=' + sTex(tv(p.th2).tan)) + ' 解 $h$（分母有根號要有理化），得 ' + T('h=' + hxTwo(rat, surd)) + ' 公尺。' + solFin(o)];
  };
  L1_SOL.figSAS = function (p, o) {
    var AB = solS(p.AB), AC = solS(p.AC), cv = sTex(tv(p.A).cos), sv = sTex(tv(p.A).sin);
    return ['從圖上讀出：' + T(ov('AB') + '=' + sTex(AB)) + '、' + T(ov('AC') + '=' + sTex(AC)) + '，標出的角在頂點 $A$，正好是這兩邊的夾角：' + T('\\angle A=' + p.A + '°') + '。',
      '餘弦定理：' + T(ov('BC') + '^2=' + hxSq(sTex(AB)) + '+' + hxSq(sTex(AC)) + '-2\\cdot' + sTex(AB) + '\\cdot' + sTex(AC) + '\\cos' + p.A + '°') + '，代入 ' + T('\\cos' + p.A + '°=' + cv) + (p.A > 90 ? '（鈍角的餘弦是負的，減負變加）' : '') + '，得 ' + T(ov('BC') + '^2=' + p.ans.a2) + '，' + T(ov('BC') + '=' + sqrtTex(p.ans.a2)) + '。',
      '面積 ' + T('=\\dfrac12\\cdot' + ov('AB') + '\\cdot' + ov('AC') + '\\sin A=\\dfrac12\\cdot' + sTex(AB) + '\\cdot' + sTex(AC) + '\\cdot' + sv + '=' + sTex(solS(p.ans.K))) + '。' + solFin(o)];
  };
  L1_SOL.figGridPoint = function (p, o) {
    var x = p.x, y = p.y, rt = sTex(sSqrt(x * x + y * y));
    return ['數格子：從原點到 $P$ 要往' + (x > 0 ? '右' : '左') + ' $' + Math.abs(x) + '$ 格、往' + (y > 0 ? '上' : '下') + ' $' + Math.abs(y) + '$ 格，所以 ' + T('P(' + x + ',' + y + ')') + '，在' + hxQuadXY(x, y) + '。',
      T('r=' + ov('OP') + '=\\sqrt{' + hxSq(String(x)) + '+' + hxSq(String(y)) + '}=' + rt) + '（$r$ 永遠取正）。',
      '代進定義：' + T('\\sin\\theta=\\dfrac yr=' + solEq('\\dfrac{' + y + '}{' + rt + '}', sTex(solS(p.ans.sin)))) + '、' + T('\\cos\\theta=\\dfrac xr=' + solEq('\\dfrac{' + x + '}{' + rt + '}', sTex(solS(p.ans.cos)))) + '、' + T('\\tan\\theta=\\dfrac yx=' + solEq('\\dfrac{' + y + '}{' + x + '}', sTex(solS(p.ans.tan)))) + '。正負號和「$P$ 在' + hxQuadXY(x, y) + '」一致。' + solFin(o)];
  };
  META_L1.push(['figRightTri', '§6 看圖求直角三角形的三角比'], ['figElev', '§6 看圖做仰角、俯角測量'], ['figSAS', '§6 看圖讀兩邊一夾角：第三邊與面積'], ['figGridPoint', '§6 方格紙上的廣義角']);

  /* ────────── L2　讀圖題：圓內接四邊形、兩棟樓的仰角俯角、圓周角與弦、共用一個角的面積比 ────────── */
  /* 圓上的點：圓心 (cx,cy)、半徑 Rp（像素）、數學角 */
  function figOnCirc(cx, cy, Rp, angs) { return angs.map(function (a) { return figPt(cx, cy, Rp, a); }); }
  function figCyclicSvg(sd, Rn, labs) {
    var W = 300, Rp = 74, cx = 150, cy = 106, H = 212, hs = sd.map(function (v) { return Math.asin(Math.min(1, v / (2 * Rn))); }), sum = hs[0] + hs[1] + hs[2] + hs[3], i, big = 0;
    if (Math.abs(sum - Math.PI) > 1e-6) { for (i = 1; i < 4; i++) if (sd[i] > sd[big]) big = i; hs[big] = Math.PI - hs[big]; }      /* 圓心在四邊形外：最長邊對的是優弧 */
    var a0 = Math.PI / 2 + hs[3], angs = [a0, a0 + 2 * hs[0], a0 + 2 * hs[0] + 2 * hs[1], a0 + 2 * hs[0] + 2 * hs[1] + 2 * hs[2]], P = figOnCirc(cx, cy, Rp, angs), nm = ['A', 'B', 'C', 'D'], s;
    s = figCircle(cx, cy, Rp, 'circ') + figPoly(P, { k: 'quad', w: 2, fill: 'rgba(176,58,85,.07)' }) + figLine(P[0][0], P[0][1], P[2][0], P[2][1], { c: FIGC.hot, w: 1.4, dash: 1, k: 'diag' });
    for (i = 0; i < 4; i++) {
      var np = figPt(cx, cy, Rp + 12, angs[i]), mid = angs[i] + hs[i], lp = figPt(cx, cy, Rp + 13, mid);
      s += figText(np[0], np[1] + 4.8, nm[i], { it: 1 }) + figVal(lp[0], lp[1], labs[i], { k: 'len' });
    }
    return figSvg(W, H, '圓內接四邊形 ABCD，四個邊長標示在圖上，虛線是對角線 AC', s);
  }
  L2.figCyclic = function (r) {
    var Q, tries = 0, ok, Rn, hs;
    do {
      Q = cyclic(r); tries++;
      ok = Q.AC2.d === 1 && simpSqrt(Q.AC2.n)[1] <= 30 && Q.sB.r <= 30 && Q.sB.d <= 12;
      if (ok) {                                                                                      /* 圖要好看：圓心在四邊形內部、每條邊所對的弧不要太短 */
        Rn = Math.sqrt(Q.AC2.n) / (2 * sNum(Q.sB)); hs = [Q.a, Q.b, Q.c, Q.d].map(function (v) { return Math.asin(Math.min(1, v / (2 * Rn))); });
        ok = Math.abs(hs[0] + hs[1] + hs[2] + hs[3] - Math.PI) < 1e-6 && Math.min.apply(null, hs) >= 0.24;
      }
    } while (!ok && tries < 800);
    var AC = sqrtF(Q.AC2);
    return { q: '如圖，圓內接四邊形 ' + T('ABCD') + ' 的四個邊長標示在圖上。求 (1) 對角線 ' + T(ov('AC')) + ' 的長　(2) 四邊形 ' + T('ABCD') + ' 的面積。' + figCyclicSvg([Q.a, Q.b, Q.c, Q.d], Rn, [String(Q.a), String(Q.b), String(Q.c), String(Q.d)]),
      a: '(1) ' + T(sTex(AC)) + '　(2) ' + T(sTex(Q.area)),
      h: '從圖上讀出 $\\overline{AB}=' + Q.a + '$、$\\overline{BC}=' + Q.b + '$、$\\overline{CD}=' + Q.c + '$、$\\overline{DA}=' + Q.d + '$。$\\angle B$ 與 $\\angle D$ 互補 ⟹ $\\cos D=-\\cos B$。同一條 $\\overline{AC}$ 在兩個三角形各寫一次餘弦定理：$' + Q.a + '^2+' + Q.b + '^2-' + hxMul([2, Q.a, Q.b]) + '\\cos B=' + Q.c + '^2+' + Q.d + '^2+' + hxMul([2, Q.c, Q.d]) + '\\cos B$，解出 $\\cos B=' + Fr.tex(Q.cB) + '$ 再代回去；面積 $=\\dfrac12(' + hxMul([Q.a, Q.b]) + '+' + hxMul([Q.c, Q.d]) + ')\\sin B$。',
      p: { a: Q.a, b: Q.b, c: Q.c, d: Q.d, ans: { AC2: fr2(Q.AC2), area: sArr(Q.area) } } };
  };

  /* 兩棟樓：甲樓 PS（高 h）、乙樓 QR；從 P 看 Q 的仰角 al、看 R 的俯角 be */
  function figTwoBldgSvg(h, al, be) {
    var d = h / Math.tan(be * Math.PI / 180), h2 = h + d * Math.tan(al * Math.PI / 180), ft = figFit([[0, 0], [0, h], [d, 0], [d, h2], [d, h]], { W: 300, maxH: 172, l: 58, r: 48, t: 26, b: 34 });
    var Sp = ft.P[0], P = ft.P[1], R = ft.P[2], Q = ft.P[3], E = ft.P[4], gy = Sp[1], s = '';
    s += figLine(Sp[0] - 18, gy, R[0] + 18, gy, { c: FIGC.ink, w: 1.2, k: 'ground' }) + figLine(Sp[0], Sp[1], P[0], P[1], { w: 3.2, k: 'bldA' }) + figLine(R[0], R[1], Q[0], Q[1], { w: 3.2, k: 'bldB' });
    s += figLine(P[0], P[1], E[0], E[1], { c: FIGC.soft, w: 1.2, dash: 1, k: 'level' }) + figLine(P[0], P[1], Q[0], Q[1], { c: FIGC.hot, w: 1.6, k: 'up' }) + figLine(P[0], P[1], R[0], R[1], { c: FIGC.hot, w: 1.6, k: 'down' });
    s += figAngMark(P, E, Q, al + '°', { lk: 'angU', r: 20 }) + figAngMark(P, E, R, be + '°', { lk: 'angD', r: 14 });
    s += figText(P[0] - 9, P[1] - 5, 'P', { it: 1 }) + figText(Sp[0] - 3, gy + 16, 'S', { it: 1 }) + figText(R[0] + 3, gy + 16, 'R', { it: 1 }) + figText(Q[0] + 4, Q[1] - 7, 'Q', { it: 1 });
    s += figVal(Sp[0] - 9, (Sp[1] + P[1]) / 2, String(h), { k: 'len', anchor: 'end' });
    return figSvg(ft.W, ft.H, '甲樓 PS 與乙樓 QR，從 P 看 Q 的仰角、看 R 的俯角與甲樓的高標示在圖上', s);
  }
  L2.figTwoBldg = function (r) {
    var h = r.pick([6, 9, 12, 15, 18, 24, 30, 36, 45, 60]), al = r.pick([30, 45, 60]), be = r.pick([30, 45, 60]);
    var dist = sDiv(sInt(h), tv(be).tan), up = sMul(dist, tv(al).tan), tot = up.r === 1 ? Fr.tex(Fr.add(F(h), sToF(up))) : hxTwo(F(h), up);
    return { q: '如圖，甲樓 ' + T(ov('PS')) + ' 與乙樓 ' + T(ov('QR')) + ' 都垂直於水平地面。從甲樓頂 ' + T('P') + ' 看乙樓頂 ' + T('Q') + ' 的仰角、看乙樓底 ' + T('R') + ' 的俯角，以及甲樓的高都標示在圖上（長度單位：公尺），虛線是過 ' + T('P') + ' 的水平線。求 (1) 兩棟樓的水平距離 ' + T(ov('SR')) + '　(2) 乙樓的高 ' + T(ov('QR')) + '。' + figTwoBldgSvg(h, al, be),
      a: '(1) ' + T(sTex(dist)) + ' 公尺　(2) ' + T(tot) + ' 公尺',
      h: '水平虛線把乙樓切成上下兩段。下面一段和甲樓一樣高，是 $' + h + '$；俯角 $' + be + '°$ 的直角三角形裡 $' + h + '$ 是對邊，水平距離是鄰邊：$\\overline{SR}=\\dfrac{' + h + '}{\\tan' + be + '°}=' + sTex(dist) + '$。上面一段在仰角 $' + al + '°$ 的直角三角形裡是對邊：$' + sTex(dist) + '\\tan' + al + '°=' + sTex(up) + '$。兩段相加就是乙樓的高。',
      p: { h: h, al: al, be: be, ans: { dist: sArr(dist), up: sArr(up) } } };
  };

  /* 圓上四點 A、B、C、D（逆時針）：∠CAD＝al 對弦 CD，∠ACB＝be 對弦 AB；given＝'CD' 或 'AB' 標出長度 */
  function figChordSvg(al, be, given, mLab, tt) {
    var W = 300, Rp = 74, cx = 150, cy = 106, H = 212, d2r = Math.PI / 180, rest = 360 - 2 * al - 2 * be, aBC = rest * tt;
    var angs = [270 - be, 270 + be, 270 + be + aBC, 270 + be + aBC + 2 * al].map(function (v) { return v * d2r; }), P = figOnCirc(cx, cy, Rp, angs), nm = ['A', 'B', 'C', 'D'], i, s;
    s = figCircle(cx, cy, Rp, 'circ') + figPoly(P, { k: 'quad', w: 2, fill: 'rgba(176,58,85,.07)' }) + figLine(P[0][0], P[0][1], P[2][0], P[2][1], { w: 1.6, k: 'diag' });
    s += figAngMark(P[0], P[2], P[3], al + '°', { lk: 'angA', r: 15, fs: 12 }) + figAngMark(P[2], P[0], P[1], be + '°', { lk: 'angC', r: 15, fs: 12 });
    for (i = 0; i < 4; i++) { var np = figPt(cx, cy, Rp + 12, angs[i]); s += figText(np[0], np[1] + 4.8, nm[i], { it: 1 }); }
    var mid = given === 'CD' ? (angs[2] + angs[3]) / 2 : (angs[0] + angs[1]) / 2, lp = figPt(cx, cy, Rp + 14, mid);
    s += figVal(lp[0], lp[1], mLab, { k: 'len' });
    return figSvg(W, H, '圓上四點 A、B、C、D 與弦 AC，兩個圓周角與一條弦的長標示在圖上', s);
  }
  L2.figChord = function (r) {
    var al = r.pick([30, 45, 60]), be, m = r.int(2, 12), given = r.pick(['CD', 'AB']), tt = r.pick([0.4, 0.5, 0.6]);
    do { be = r.pick([30, 45, 60, 90]); } while (be === al);
    var sg = given === 'CD' ? tv(al).sin : tv(be).sin, so = given === 'CD' ? tv(be).sin : tv(al).sin, other = given === 'CD' ? 'AB' : 'CD';
    var RR = sMulF(sDiv(sInt(1), sg), F(m, 2)), oth = sMulF(sDiv(so, sg), F(m)), ga = given === 'CD' ? al : be, oa = given === 'CD' ? be : al, gAng = given === 'CD' ? '\\angle CAD' : '\\angle ACB', oAng = given === 'CD' ? '\\angle ACB' : '\\angle CAD';
    return { q: '如圖，' + T('A') + '、' + T('B') + '、' + T('C') + '、' + T('D') + ' 四點在同一個圓上，兩個角與一條弦的長標示在圖上。求 ' + T(ov(other)) + ' 與圓的半徑 ' + T('R') + '。' + figChordSvg(al, be, given, String(m), tt),
      a: T(ov(other) + '=' + sTex(oth)) + '、' + T('R=' + sTex(RR)),
      h: '先看每個角對著哪一條弦：$\\angle CAD=' + al + '°$ 的兩邊是 $\\overline{AC}$、$\\overline{AD}$，對的是弦 $\\overline{CD}$；$\\angle ACB=' + be + '°$ 對的是弦 $\\overline{AB}$。四點同在一個圓上，每條弦都等於 $2R\\sin$（它所對的圓周角）：$\\overline{' + given + '}=2R\\sin' + gAng + '$ ⟹ $' + m + '=2R\\sin' + ga + '°$，求出 $R$；再算 $\\overline{' + other + '}=2R\\sin' + oAng + '=2R\\sin' + oa + '°$。',
      p: { al: al, be: be, m: m, given: given, ans: [sArr(oth), sArr(RR)] } };
  };

  /* 共用 ∠A 的兩個三角形：D 在 AB 上、E 在 AC 上 */
  function figShareSvg(AD, DB, AE, EC, Adeg) {
    var c = AD + DB, b = AE + EC, A = Adeg * Math.PI / 180, a = Math.sqrt(b * b + c * c - 2 * b * c * Math.cos(A)), xA = (c * c + a * a - b * b) / (2 * a), yA = Math.sqrt(Math.max(0, c * c - xA * xA));
    var Am = [xA, yA], Bm = [0, 0], Cm = [a, 0], Dm = [xA * DB / c, yA * DB / c], Em = [a + (xA - a) * EC / b, yA * EC / b];
    var ft = figFit([Am, Bm, Cm, Dm, Em], { W: 300, maxH: 158, l: 50, r: 50, t: 28, b: 30 }), P = ft.P, cen = figCen([P[0], P[1], P[2]]), s;
    s = figPoly([P[0], P[3], P[4]], { k: 'small', c: 'none', fill: FIGC.fill }) + figPoly([P[0], P[1], P[2]], { k: 'tri', w: 2 }) + figLine(P[3][0], P[3][1], P[4][0], P[4][1], { w: 1.8, k: 'DE' });
    s += figDot(P[3][0], P[3][1], { k: 'D', r: 2.6 }) + figDot(P[4][0], P[4][1], { k: 'E', r: 2.6 });
    s += figName(P[0], cen, 'A') + figName(P[1], cen, 'B') + figName(P[2], cen, 'C') + figText(P[3][0] - 11, P[3][1] + 2, 'D', { it: 1 }) + figText(P[4][0] + 11, P[4][1] + 2, 'E', { it: 1 });
    s += figSideVal(P[0], P[3], cen, String(AD), { k: 'len', d: 7 }) + figSideVal(P[3], P[1], cen, String(DB), { k: 'len', d: 7 }) + figSideVal(P[0], P[4], cen, String(AE), { k: 'len', d: 7 }) + figSideVal(P[4], P[2], cen, String(EC), { k: 'len', d: 7 });
    return figSvg(ft.W, ft.H, '三角形 ABC，D 在 AB 上、E 在 AC 上，四段長標示在圖上，三角形 ADE 塗色', s);
  }
  L2.figShare = function (r) {
    var AD, DB, AE, EC, guard = 0, c, b;
    do { AD = r.int(1, 8); DB = r.int(1, 8); AE = r.int(1, 8); EC = r.int(1, 8); c = AD + DB; b = AE + EC; }
    while ((c / b < 0.6 || c / b > 1.6 || AD * b === AE * c || AD / c < 0.25 || AE / b < 0.25 || DB / c < 0.25 || EC / b < 0.25) && guard++ < 300);
    var Adeg = r.pick([50, 60, 70, 80]), mode = r.pick(['ratio', 'ratio', 'area']), sm = AD * AE, all = c * b, g = gcd(sm, all - sm);
    var svg = figShareSvg(AD, DB, AE, EC, Adeg), frac = '\\dfrac{' + AD + '\\times' + AE + '}{' + c + '\\times' + b + '}=' + Fr.tex(F(sm, all));
    if (mode === 'ratio')
      return { q: '如圖，' + ABC + ' 中，' + T('D') + ' 在 ' + T(ov('AB')) + ' 上、' + T('E') + ' 在 ' + T(ov('AC')) + ' 上，四段的長標示在圖上。求塗色的 ' + T('\\triangle ADE') + ' 與四邊形 ' + T('DBCE') + ' 的面積比。' + svg,
        a: T(sm / g + ':' + (all - sm) / g),
        h: '$\\triangle ADE$ 和 $\\triangle ABC$ 共用 $\\angle A$，面積都用 $\\dfrac12\\times$ 兩邊 $\\times\\sin A$ 寫，$\\sin A$ 會約掉：$\\dfrac{\\triangle ADE}{\\triangle ABC}=\\dfrac{\\overline{AD}\\times\\overline{AE}}{\\overline{AB}\\times\\overline{AC}}=' + frac + '$。注意 $\\overline{AB}=' + AD + '+' + DB + '$、$\\overline{AC}=' + AE + '+' + EC + '$；四邊形是大三角形扣掉 $\\triangle ADE$。',
        p: { mode: mode, AD: AD, DB: DB, AE: AE, EC: EC, ans: [sm / g, (all - sm) / g] } };
    var K = all / gcd(sm, all) * r.int(1, 3), quad = F(K * (all - sm), all);
    return { q: '如圖，' + ABC + ' 中，' + T('D') + ' 在 ' + T(ov('AB')) + ' 上、' + T('E') + ' 在 ' + T(ov('AC')) + ' 上，四段的長標示在圖上。已知 ' + ABC + ' 的面積是 ' + T(String(K)) + '，求四邊形 ' + T('DBCE') + ' 的面積。' + svg,
      a: T(Fr.tex(quad)),
      h: '$\\triangle ADE$ 和 $\\triangle ABC$ 共用 $\\angle A$：$\\dfrac{\\triangle ADE}{\\triangle ABC}=\\dfrac{\\overline{AD}\\times\\overline{AE}}{\\overline{AB}\\times\\overline{AC}}=' + frac + '$（$\\overline{AB}=' + AD + '+' + DB + '$、$\\overline{AC}=' + AE + '+' + EC + '$）。所以 $\\triangle ADE=' + K + '\\times' + Fr.tex(F(sm, all)) + '=' + Fr.tex(F(K * sm, all)) + '$，四邊形是 $' + K + '$ 扣掉它。',
      p: { mode: mode, AD: AD, DB: DB, AE: AE, EC: EC, K: K, ans: fr2(quad) } };
  };
  META_L2.push(['figCyclic', '§6 看圖解圓內接四邊形'], ['figTwoBldg', '§6 兩棟樓的仰角與俯角（附圖）'], ['figChord', '§6 圓周角對哪條弦：2R sin（附圖）'], ['figShare', '§6 共用一個角的面積比（附圖）']);

  /* ────────── L3　L3-19～L3-21 的類似題（附圖） ────────── */
  /* L3-19　圓 O 半徑 r，CD 切圓於 D、長 t，OC 交圓於 A，B 是 A 到 OD 的垂足 */
  var FTAN_TRI = [[3, 4, 5], [4, 3, 5], [3, 4, 5], [4, 3, 5], [12, 5, 13], [15, 8, 17], [20, 21, 29], [21, 20, 29]];   /* [切線段, 半徑, OC] 的比 */
  function figTangentSvg(rN, tN, rLab, tLab) {
    var oc = Math.sqrt(rN * rN + tN * tN), Am = [rN * rN / oc, rN * tN / oc], phA = Math.atan2(tN, rN) + Math.PI / 4;   /* A 的點名放在圓外、OC 的左上方 */
    var ft = figFit([[-rN, -rN], [rN, Math.max(rN, tN)], [0, 0], [rN, 0], [rN, tN], Am, [Am[0], 0]], { W: 300, maxH: 190, l: 30, r: 54, t: 24, b: 22 }), P = ft.P, O = P[2], D = P[3], C = P[4], A = P[5], B = P[6], s;
    s = figCircle(O[0], O[1], rN * ft.sc, 'circ') + figLine(O[0], O[1], D[0], D[1], { w: 1.8, k: 'OD' }) + figLine(D[0], D[1], C[0], C[1], { w: 1.8, k: 'DC' }) + figLine(O[0], O[1], C[0], C[1], { w: 1.8, k: 'OC' }) + figLine(A[0], A[1], B[0], B[1], { c: FIGC.hot, w: 1.6, k: 'AB' });
    s += figRight(D, O, C) + figRight(B, O, A, 7) + figDot(O[0], O[1], { k: 'O', r: 2.6 }) + figDot(A[0], A[1], { k: 'A', r: 2.6 });
    s += figText(O[0] - 10, O[1] + 5, 'O', { it: 1 }) + figText(B[0], B[1] + 16, 'B', { it: 1 }) + figText(D[0] + 10, D[1] + 13, 'D', { it: 1 }) + figText(C[0] + 10, C[1] + 1, 'C', { it: 1 }) + figText(A[0] + 13 * Math.cos(phA), A[1] - 13 * Math.sin(phA) + 4.8, 'A', { it: 1 });
    s += figSideVal(O, A, B, rLab, { k: 'len', d: 6 }) + figVal(D[0] + 9, (D[1] + C[1]) / 2, tLab, { k: 'len', anchor: 'start' });
    return figSvg(ft.W, ft.H, '圓 O、切線段 CD、OC 與圓的交點 A，以及 A 到 OD 的垂足 B', s);
  }
  L3.figTangentFoot = function (r) {
    var t = r.pick(FTAN_TRI), k = r.int(1, t[2] > 20 ? 3 : 6), tN = t[0] * k, rN = t[1] * k, oc = t[2] * k, ask = r.int(0, 2);
    var OB = F(rN * t[1], t[2]), AB = F(rN * t[0], t[2]), BD = Fr.sub(F(rN), OB), nm = ['OB', 'AB', 'BD'][ask], val = [OB, AB, BD][ask];
    return { q: '如圖，' + T(ov('CD')) + ' 切圓 ' + T('O') + ' 於 ' + T('D') + '，' + T(ov('OC')) + ' 交圓 ' + T('O') + ' 於 ' + T('A') + '，' + T('B') + ' 是 ' + T('A') + ' 到 ' + T(ov('OD')) + ' 的垂足。圓的半徑（標在 ' + T(ov('OA')) + ' 上）與 ' + T(ov('CD')) + ' 的長標示在圖上，求 ' + T(ov(nm)) + '。' + figTangentSvg(rN, tN, String(rN), String(tN)),
      a: T(ov(nm) + '=' + Fr.tex(val)),
      h: '切線垂直過切點的半徑 ⟹ $\\angle ODC=90°$，$\\overline{OD}=' + rN + '$（半徑）、$\\overline{CD}=' + tN + '$ ⟹ $\\overline{OC}=\\sqrt{' + rN + '^2+' + tN + '^2}=' + oc + '$，所以 $\\cos\\angle COD=\\dfrac{' + rN + '}{' + oc + '}=' + Fr.tex(F(t[1], t[2])) + '$、$\\sin\\angle COD=' + Fr.tex(F(t[0], t[2])) + '$。直角三角形 $OAB$ 和它共用這個角，斜邊 $\\overline{OA}=' + rN + '$：$\\overline{OB}=' + rN + '\\cos\\angle COD$、$\\overline{AB}=' + rN + '\\sin\\angle COD$' + (ask === 2 ? '，$\\overline{BD}=\\overline{OD}-\\overline{OB}$' : '') + '。',
      p: { r: rN, t: tN, ask: ask, ans: fr2(val) } };
  };

  /* L3-20　正方形 ABCD（邊長 s）＋以 AB 為底的等腰三角形 ABE（腰 leg）：mode＝out 向外、in 向內 */
  var FSQ_OK = [[6, 5, 4, 4], [8, 5, 3, 4], [10, 13, 12, 2], [24, 13, 5, 2], [16, 17, 15, 2], [30, 17, 8, 1], [40, 29, 21, 1], [42, 29, 20, 1], [48, 25, 7, 1]];   /* [邊長 s, 腰, 高 h, 最多放大幾倍]：(s/2)²+h²=腰² */
  function figSqIsosSvg(sN, hN, mode, sLab, legLab) {
    var Em = [sN / 2, mode === 'out' ? sN + hN : sN - hN], ft = figFit([[0, sN], [sN, sN], [sN, 0], [0, 0], Em], { W: 300, maxH: 186, l: 40, r: 40, t: 26, b: 36 }), P = ft.P, A = P[0], B = P[1], C = P[2], D = P[3], E = P[4], s;
    s = figPoly([A, B, C, D], { k: 'sq', w: 2 }) + figPoly([A, B, E], { k: 'isos', w: 2, fill: 'rgba(176,58,85,.12)' }) + figLine(D[0], D[1], E[0], E[1], { c: FIGC.hot, w: 1.6, dash: 1, k: 'DE' });
    s += figText(A[0] - 10, A[1] + (mode === 'out' ? 4 : -2), 'A', { it: 1 }) + figText(B[0] + 10, B[1] + (mode === 'out' ? 4 : -2), 'B', { it: 1 }) + figText(C[0] + 10, C[1] + 12, 'C', { it: 1 }) + figText(D[0] - 10, D[1] + 12, 'D', { it: 1 }) + figText(E[0], E[1] + (mode === 'out' ? -8 : 17), 'E', { it: 1 });
    s += figVal((D[0] + C[0]) / 2, D[1] + 15, sLab, { k: 'len' }) + figSideVal(B, E, A, legLab, { k: 'len', d: 6 });
    return figSvg(ft.W, ft.H, '正方形 ABCD 與以 AB 為底邊的等腰三角形 ABE，E 在正方形' + (mode === 'out' ? '外' : '內'), s);
  }
  L3.figSquareIsos = function (r) {
    var t, mode, guard = 0;
    do { t = r.pick(FSQ_OK); mode = r.pick(['out', 'out', 'in']); } while (((mode === 'in' && t[2] > t[0] * 0.8) || (mode === 'out' && t[2] > t[0] * 1.3)) && guard++ < 100);
    var k = r.int(1, t[3]), s = t[0] * k, leg = t[1] * k, h = t[2] * k, de2 = mode === 'out' ? s * s + leg * leg + 2 * s * h : s * s + leg * leg - 2 * s * h;
    var sinT = Fr.tex(F(h, leg));
    return { q: '如圖，正方形 ' + T('ABCD') + ' 的邊長與等腰三角形 ' + T('ABE') + '（' + T(ov('AE') + '=' + ov('BE')) + '）的腰長標示在圖上，' + T('E') + ' 在正方形的' + (mode === 'out' ? '外部' : '內部') + '。求 ' + T(ov('DE')) + '。' + figSqIsosSvg(s, h, mode, String(s), String(leg)),
      a: T(ov('DE') + '=' + sqrtTex(de2)),
      h: '在 $\\triangle ADE$ 用餘弦定理，需要 $\\cos\\angle DAE$。先看等腰三角形：從 $E$ 作高到 $\\overline{AB}$ 的中點，$\\cos\\angle EAB=' + solEq('\\dfrac{' + s / 2 + '}{' + leg + '}', Fr.tex(F(s / 2, leg))) + '$、$\\sin\\angle EAB=' + sinT + '$。' + (mode === 'out' ? '$E$ 在外部 ⟹ $\\angle DAE=90°+\\angle EAB$，$\\cos\\angle DAE=-\\sin\\angle EAB=-' + sinT + '$。' : '$E$ 在內部 ⟹ $\\angle DAE=90°-\\angle EAB$，$\\cos\\angle DAE=\\sin\\angle EAB=' + sinT + '$。') + '$\\overline{DE}^2=' + s + '^2+' + leg + '^2-2\\cdot' + s + '\\cdot' + leg + '\\cos\\angle DAE$。',
      p: { s: s, leg: leg, h: h, mode: mode, ans: de2 } };
  };

  /* L3-21　方格紙上的角 ∠ABC（A、B、C 在格子點上）：餘弦定理求 cos，再求 tan */
  function figGridAngSvg(A, B, C) {
    var xs = [A[0], B[0], C[0]], ys = [A[1], B[1], C[1]], x0 = Math.min.apply(null, xs), x1 = Math.max.apply(null, xs), y0 = Math.min.apply(null, ys), y1 = Math.max.apply(null, ys), cols = x1 - x0, rows = y1 - y0;
    var c = Math.max(24, Math.min(36, Math.floor(216 / cols), Math.floor(180 / rows))), W = 300, gx = (W - cols * c) / 2, gy = 26, H = gy + rows * c + 28, i, s = '';
    for (i = 0; i <= cols; i++) s += figLine(gx + i * c, gy, gx + i * c, gy + rows * c, { c: FIGC.grid, w: 1, k: 'gv' });
    for (i = 0; i <= rows; i++) s += figLine(gx, gy + i * c, gx + cols * c, gy + i * c, { c: FIGC.grid, w: 1, k: 'gh' });
    function px(p) { return [gx + (p[0] - x0) * c, gy + (y1 - p[1]) * c]; }
    var a = px(A), b = px(B), cc = px(C), cen = figCen([a, b, cc]);
    s += figLine(b[0], b[1], a[0], a[1], { w: 2, k: 'BA' }) + figLine(b[0], b[1], cc[0], cc[1], { w: 2, k: 'BC' }) + figAngMark(b, a, cc, null, { r: 15 });
    s += figDot(a[0], a[1], { k: 'A' }) + figDot(b[0], b[1], { k: 'B' }) + figDot(cc[0], cc[1], { k: 'C' });
    s += figName(a, cen, 'A', 13) + figName(b, cen, 'B', 13) + figName(cc, cen, 'C', 13);
    return figSvg(W, H, '方格紙上的角 ABC，A、B、C 都在格子點上', s);
  }
  L3.figGridAngle = function (r) {
    var u, v, cross, dot, n1v, n2v, guard = 0, ok;
    do {
      u = [r.int(-4, 4), r.int(-3, 3)]; v = [r.int(-4, 4), r.int(-3, 3)]; cross = u[0] * v[1] - u[1] * v[0]; dot = u[0] * v[0] + u[1] * v[1]; n1v = u[0] * u[0] + u[1] * u[1]; n2v = v[0] * v[0] + v[1] * v[1];
      var w = Math.max(0, u[0], v[0]) - Math.min(0, u[0], v[0]), hh = Math.max(0, u[1], v[1]) - Math.min(0, u[1], v[1]);
      ok = cross !== 0 && dot !== 0 && n1v >= 2 && n2v >= 2 && w >= 2 && w <= 7 && hh >= 2 && hh <= 5 && Math.abs(dot) / Math.sqrt(n1v * n2v) < 0.94;
    } while (!ok && guard++ < 500);
    if (!ok) { u = [-1, 2]; v = [2, 2]; cross = -6; dot = 2; n1v = 5; n2v = 8; }
    var A = u, B = [0, 0], C = v, cs = S(dot, n1v * n2v, n1v * n2v), tn = F(Math.abs(cross), dot), ac2 = (u[0] - v[0]) * (u[0] - v[0]) + (u[1] - v[1]) * (u[1] - v[1]);
    return { q: '如圖，方格紙上每一小格的邊長都是 ' + T('1') + '，' + T('A') + '、' + T('B') + '、' + T('C') + ' 都在格子點上。求 ' + T('\\cos\\angle ABC') + ' 與 ' + T('\\tan\\angle ABC') + '。' + figGridAngSvg(A, B, C),
      a: T('\\cos\\angle ABC=' + sTex(cs)) + '、' + T('\\tan\\angle ABC=' + Fr.tex(tn)),
      h: '數格子配畢氏定理，把三邊的平方算出來：$\\overline{AB}^2=' + n1v + '$、$\\overline{BC}^2=' + n2v + '$、$\\overline{AC}^2=' + ac2 + '$。餘弦定理：$\\cos\\angle ABC=\\dfrac{' + n1v + '+' + n2v + '-' + ac2 + '}{2\\cdot' + sqrtTex(n1v) + '\\cdot' + sqrtTex(n2v) + '}$。再用 $\\sin^2+\\cos^2=1$ 求 $\\sin\\angle ABC$（三角形的內角，正弦取正），$\\tan=\\dfrac{\\sin}{\\cos}$' + (dot < 0 ? '；這個角是鈍角，$\\cos$ 與 $\\tan$ 都是負的。' : '。'),
      p: { A: A, C: C, ans: { cos: sArr(cs), tan: fr2(tn) } } };
  };
  META_L3.push(['figTangentFoot', '切線＋垂足：兩個共用一角的直角三角形（附圖）'], ['figSquareIsos', '正方形接等腰三角形：90°±角的餘弦定理（附圖）'], ['figGridAngle', '方格紙上的角：餘弦定理求 cos 與 tan（附圖）']);
  L3_FIX['L3-19'] = 'figTangentFoot'; L3_FIX['L3-20'] = 'figSquareIsos'; L3_FIX['L3-21'] = 'figGridAngle';

  function contrastPair(tier, key, seedA, maxTry) {
    var c = CONTRAST[tier + '.' + key]; if (!c) return null;
    var A = wrapItem(tier, key, seedA), fA = c.f(A.p), keep = c.keep || [];
    for (var n = 1; n < (maxTry || 2000); n++) {
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

  function escMath(s) {
    return String(s).replace(/\$([^$]*)\$/g, function (m, inner) {
      /* 原始 <>（瀏覽器會當標籤）、全形頓號（KaTeX 嚴格模式拒收）、\times 後接字母（變成未定義指令）一律在這裡修 */
      return '$' + inner.replace(/</g, '\\lt ').replace(/>/g, '\\gt ').replace(/、/g, ',\\ ').replace(/\\times(?=[A-Za-z])/g, '\\times ') + '$';
    });
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

  return { makeRng: makeRng, L0: L0, L1: L1, L2: L2, L3: L3, L3_FIX: L3_FIX, META: META, PREREQ: PREREQ, CONTRAST: CONTRAST, contrastPair: contrastPair, _util: { gcd: gcd, F: F, Fr: Fr, S: S, sTex: sTex, sqrtTex: sqrtTex, tv: tv } };
}));
