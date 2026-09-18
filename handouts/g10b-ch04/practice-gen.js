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
               h: (kind === 4 ? '$\\tan\\theta\\cdot\\tan(90°-\\theta)=1$' : '$\\sin^2\\theta+\\sin^2(90°-\\theta)=\\sin^2\\theta+\\cos^2\\theta=1$（換成 $\\cos$ 也一樣）') + '：把和為 $90°$ 的兩項配成一對——' + pairTex.join('、') + '，本題共 $' + n + '$ 對' + (kind === 4 ? '，乘積是 $1$。' : '，相加得 $' + n + '$。'),
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
             h: '每個角先化到 $0°\\sim360°$（同界角），由終邊所在象限決定正負，再用參考角查特殊值——' + used.join('；') + '。',
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
             h: '夾角 $=$ 兩極角之差：$|' + th1 + '-' + th2 + '|$（超過 $180°$ 就用 $360°$ 減）$=' + gap + '°$；再用餘弦定理 ' + T(ov('AB') + '^2=' + r1 + '^2+' + r2 + '^2-' + hxMul([2, r1, r2]) + '\\cos' + gap + '°') + ' 與面積公式 ' + T('\\dfrac12\\cdot' + hxMul([r1, r2]) + '\\sin' + gap + '°') + '——極坐標把「兩邊夾角」直接送給你。',
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
    else if (sl3.ang === 60 || sl3.ang === 120) { var sgn = sl3.ang === 60 ? -1 : 1, rt = -sgn * py; tex = '\\sqrt3x' + (sgn < 0 ? '-' : '+') + 'y' + (rt === 0 ? '' : (rt > 0 ? '+' : '') + rt) + ((-px) === 0 ? '' : ((-px) > 0 ? '+' : '-') + (Math.abs(px) === 1 ? '' : Math.abs(px)) + '\\sqrt3') + '=0'; c1 = { rat: rt, surd: -px }; }
    else { var sg = sl3.ang === 30 ? -1 : 1, sd = -sg * py; tex = 'x' + (sg < 0 ? '-' : '+') + '\\sqrt3y' + ((-px) === 0 ? '' : ((-px) > 0 ? '+' : '') + (-px)) + (sd === 0 ? '' : (sd > 0 ? '+' : '-') + (Math.abs(py) === 1 ? '' : Math.abs(py)) + '\\sqrt3') + '=0'; c1 = { rat: -px, surd: sd }; }
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
    var angs = [((s1.ang + phi) % 180 + 180) % 180, ((s1.ang - phi) % 180 + 180) % 180];
    var slopeTex = function (ang) { return ang === 90 ? '不存在（鉛直線 $x=' + px + '$）' : T('m=' + sTex(tv(ang).tan)); };
    return { q: '直線 $L$ 過點 ' + T('P(' + px + ',' + py + ')') + '，且與直線 ' + T('L_1:' + L.tex) + ' 夾 ' + T(phi + '°') + ' 角。求 $L$ 的斜角與斜率（兩解）。',
             a: '斜角 ' + T(angs[0] + '°') + '：斜率' + slopeTex(angs[0]) + '；斜角 ' + T(angs[1] + '°') + '：斜率' + slopeTex(angs[1]),
             h: '用斜角不要用夾角公式：$L_1$ 的斜率是 $' + s1.tex + '$ ⟹ 斜角 $' + s1.ang + '°$；$L$ 的斜角 ' + T('=' + s1.ang + '°\\pm' + phi + '°') + '（超出 $0°\\sim180°$ 就加減 $180°$），本題得 $' + angs[0] + '°$ 與 $' + angs[1] + '°$。斜角 $90°$ 是鉛直線（過 $P(' + px + ',' + py + ')$ 就是 $x=' + px + '$），斜率不存在，最常被漏掉。',
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
    var t = niceTri(r, 10), a = t[0], b = t[1], c = t[2], K = t[3], m = Math.max(a, b, c), s = F(a + b + c, 2);
    var rin = sDiv(K, S(a + b + c, 1, 2)), R = sDiv(S(a * b * c, 1, 4), K), hmax = sDiv(K, S(m, 1, 2));
    return { q: ABC + ' 三邊長為 ' + T(a + ',\\ ' + b + ',\\ ' + c) + '。求 (1) 面積　(2) 內切圓半徑　(3) 外接圓半徑　(4) 最長邊上的高。',
             a: '(1) ' + T(sTex(K)) + '　(2) ' + T(sTex(rin)) + '　(3) ' + T(sTex(R)) + '　(4) ' + T(sTex(hmax)),
             h: '海龍先算面積：' + T('s=\\dfrac{' + a + '+' + b + '+' + c + '}{2}=' + Fr.tex(s)) + '、$K=\\sqrt{s(s-a)(s-b)(s-c)}$；其餘三個都從面積出發——$r=\\dfrac Ks$、' + T('R=\\dfrac{abc}{4K}=\\dfrac{' + (a * b * c) + '}{4K}') + '、最長邊是 $' + m + '$ ⟹ ' + T('h=\\dfrac{2K}{' + m + '}') + '。',
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
    slopeAngle: '這是「斜角與斜率」：斜率就是斜角的正切，斜角取在零度到平角之間；兩線夾角則是兩個斜角相減。',
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
        '斜角 $\\alpha$ 滿足 $\\tan\\alpha=m$ 且 $0°\\le\\alpha<180°$' + (p.ang > 90 ? '；斜率是負的 ⟹ 斜角是鈍角' : '') + '。',
        '所以斜角是 ' + T(p.ang + '°') + '。' + solFin(o)];
    if (p.kind === 1) {
      var dif = Math.abs(p.a1 - p.a2);
      return ['兩條線的斜角分別是 ' + T(p.a1 + '°') + ' 與 ' + T(p.a2 + '°') + '。',
        '兩斜角相減：' + T('|' + p.a1 + '-' + p.a2 + '|=' + dif + '°') + (dif > 90 ? '，超過 $90°$ ⟹ 改用 ' + T('180°-' + dif + '°=' + p.ans + '°') : '') + '。',
        '所以銳夾角（或直角）是 ' + T(p.ans + '°') + '。' + solFin(o)];
    }
    return ['斜率 ' + T('m=\\tan' + p.ang + '°=' + sTex(tv(p.ang).tan)) + '。',
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

  var META_L1 = [
      ['triDef', '§1 三角比的定義'], ['specialEval', '§1 特殊角求值'], ['sinToCos', '§1 同角關係：知一求二'], ['sumProdAcute', '§1 對稱式 sin±cos 與 sincos'], ['coAngleSum', '§1 餘角關係：整串求和／求積'], ['elevOne', '§1 仰角測高：一次測量'], ['elevTwo', '§1 仰角測高：兩次測量'],
      ['coterminal', '§2 同界角與象限'], ['pointTrig', '§2 終邊上一點求三角比'], ['quadFind', '§2 象限判定與符號'], ['reduceEval', '§2 廣義角的特殊值'], ['polarConv', '§2 極坐標與直角坐標互換'], ['polarDist', '§2 極坐標下的距離與面積'], ['slopeAngle', '§2 斜角、斜率與夾角'],
      ['sineLaw', '§3 正弦定理求邊'], ['circumR', '§3 外接圓半徑'], ['cosLawSide', '§3 餘弦定理求邊（SAS）'], ['cosLawAngle', '§3 餘弦定理求角（SSS）與形狀'], ['sideRange', '§3 三角形存在條件與鈍角範圍'], ['ssaCount', '§3 SSA 有幾組解'],
      ['areaSAS', '§4 面積公式與已知面積求角'], ['heronArea', '§4 海龍公式'], ['inOutRadius', '§4 內切圓與外接圓半徑'], ['medianLen', '§4 中線長'], ['bisectorLen', '§4 角平分線'], ['cyclicQuad', '§4 圓內接四邊形'],
      ['projLen', '§5 正射影'], ['projTheorem', '§5 投影定理'], ['cuboid', '§5 長方體的立體測量'], ['pyramid', '§5 正四角錐']
  ];
  var META_L2 = [
      ['quadSumProd', '§2 廣義角的同角關係（象限定號）'], ['reduceSimplify', '§2 誘導公式化簡'], ['polarTriangle', '§2 三個極坐標點的三角形'], ['lineAngle', '§2 與已知直線夾特殊角的直線'], ['sinCount', '§2 範圍內三角方程的解數'],
      ['sineRatio', '§3 sin 比⟹邊比：形狀與面積'], ['cevianLen', '§3 D 在 BC 上：補角餘弦串連'], ['ssaSolve', '§3 SSA 兩解求第三邊'], ['shapeJudge', '§3 由邊角關係判定形狀'],
      ['heronFull', '§4 三邊全知：K、r、R、高'], ['heightsHeron', '§4 三高／sin 比＋內切圓⟹R'], ['cyclicQuadFull', '§4 圓內接四邊形全套'], ['bisector', '§4 角平分線全套'], ['areaMinPQ', '§4 面積條件下的最短線段'],
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
             h: '$\\angle A+\\angle B=90°$ ⟹ $\\sin B=\\cos A$，條件變成 $' + eqCA + '$——只剩一個角。令 $\\sin A=s$，則 $\\cos A=' + cosExpr + '$，代入 $s^2+\\cos^2A=1$ 得 $' + quad + '$ ⟹ ' + roots + '；' + bad + '，所以 $\\sin A=' + Fr.tex(sn) + '$、$\\cos A=' + Fr.tex(cs) + '$，而 $a:b:c=\\sin A:\\cos A:1=' + ratio + '$。',
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
             h: '$r=\\sqrt{(' + xT + ')^2+(' + yT + ')^2}=' + l3coef(m, '\\sqrt{\\sin^2' + al + '°+\\cos^2' + al + '°}') + '=' + m + '$。接著要找 $\\theta$ 使 $(\\cos\\theta,\\sin\\theta)=' + (m === 1 ? 'P' : '\\dfrac{1}{' + m + '}P') + '$——用餘角公式把 $\\sin$ 換成 $\\cos$：$' + idx + '$ ⟹ $P=' + l3coef(m, '(\\cos(' + bs + '),\\sin(' + bs + '))') + '$ ⟹ $\\theta=' + base + '°$，取' + (rk === 0 ? '最小正同界角 ' : '落在 $-180°\\lt\\theta\\le180°$ 的同界角 ') + T(shown + '°') + '。檢查：$' + al + '°$ 在第' + L3QD[qal] + '象限，$P$ 與 ' + T(th + '°') + ' 都落在第' + L3QD[quad] + '象限 ✓。',
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
                + (ask === 0 ? '本題只要差，答案就是 $' + Fr.tex(df) + '$——符號完全由範圍決定，別漏掉負號。'
                 : ask === 1 ? '本題只要和，答案就是 $' + Fr.tex(sm) + '$——第三、四象限時和為負。'
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
    var tail = '想用 $\\dfrac12\\overline{AB}\\cdot\\overline{AC}\\sin A$ 會需要 $\\sin(B+C)$——那是高二上的和角公式；切高才是這一章的路。';
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
    var hb = '$\\dfrac12\\cdot' + p + '\\cdot' + q + '\\sin C=' + K.n + '$ ⟹ $\\sin C=' + Fr.tex(sC) + '$ ⟹ $\\cos C=\\pm' + Fr.tex(cC) + '$——「面積」只給 $\\sin$，永遠要想兩解。'
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

  var META_L3 = [['rightCoQuad', '直角三角形＋互餘換角解二次'], ['tanCosQuad', 'a cosθ＝b tanθ：化 sinθ 的二次方程'], ['coPairSum', '互餘配對整串求和'],
                 ['reduceSum', '誘導公式化簡（給範圍）'], ['polarFromTrig', '(±sinα, ±cosα) 化極坐標'], ['polarRatio', '四個極坐標點的長度比與面積比'],
                 ['tanRecip', 'tanθ＋1/tanθ 型＋範圍定號'], ['tanSecLin', 'tanθ±1/cosθ＝k 與平方關係聯立'], ['linTrigAcute', 'a cosθ＋b sinθ＝c（銳角）'],
                 ['twoTowers', '兩棟樓的仰角（tan15°＝2−√3）'], ['kiteDiag', '箏形：對稱軸與另一條對角線'], ['cyclicPerp', '圓內接四邊形配 2R sin'],
                 ['altSplit', '作高分兩段求面積'], ['sineLawR', '邊化 2R sin 求外接圓半徑'], ['areaTwoSol', '面積反求第三邊的兩解']];
  /* 固定題 L3-n 對應的類似題型 */
  var L3_FIX = { 'L3-1': 'rightCoQuad', 'L3-2': 'tanCosQuad', 'L3-3': 'coPairSum', 'L3-4': 'reduceSum', 'L3-5': 'polarFromTrig',
                 'L3-6': 'polarRatio', 'L3-7': 'tanRecip', 'L3-8': 'tanSecLin', 'L3-9': 'linTrigAcute', 'L3-10': 'twoTowers',
                 'L3-11': 'kiteDiag', 'L3-12': 'cyclicPerp', 'L3-13': 'altSplit', 'L3-14': 'sineLawR', 'L3-15': 'areaTwoSol' };

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
      h: '斜率 $=\\dfrac{' + (y1 + dy) + '-' + l0sn(y1) + '}{' + (x1 + dx) + '-' + l0sn(x1) + '}=' + Fr.tex(m) + '$；斜率為正是上升、為負是下降。本章「斜率 $=\\tan(\\text{斜角})$」把它和角度接起來：斜率為負時斜角是鈍角。',
      p: { A: [x1, y1], B: [x1 + dx, y1 + dy], ans: fr2(m) } };
  };
  var META_L0 = [['pythag', '畢氏定理'], ['specialTri', '特殊直角三角形的邊長比'], ['similarRatio', '相似三角形的比例'], ['surdRational', '根式化簡與有理化'], ['slope2', '兩點的斜率']];
  /* 先備題型 → 該去哪裡複習 */
  var PREREQ = {
    pythag: { txt: '畢氏定理（國中）——由 sin 求 cos、終邊上一點到原點的距離都是它', link: null },
    specialTri: { txt: '30°-60°-90° 與 45°-45°-90° 的邊長比（國中）——特殊角的三角比全部從這兩個三角形讀出來', link: null },
    similarRatio: { txt: '相似三角形的對應邊成比例（國中）——三角比「只跟角度有關」的理由', link: null },
    surdRational: { txt: '根式化簡與分母有理化（高一上第一章 數與式）——特殊角的值、餘弦定理的邊長都要化簡', link: '../g10a-ch01/practice.html#L1' },
    slope2: { txt: '兩點的斜率（高一上第二章 直線與圓）——本章「斜率＝tan(斜角)」從這裡接上角度', link: '../g10a-ch02/practice.html#L1' }
  };
  /* ══════════════════════════════════════════════════════════
     對照題：同一型抽兩題，只差一個關鍵特徵（f 由 p 算出；keep 的欄位要相同）
     ══════════════════════════════════════════════════════════ */
  function sign3(x) { return x > 0 ? 1 : x < 0 ? -1 : 0; }
  function quadOf(x, y) { return x > 0 ? (y > 0 ? 1 : 4) : (y > 0 ? 2 : 3); }
  var CONTRAST = {
    'L1.coterminal': { f: function (p) { return p.ans.quad; }, why: '同界角只差 $360^\\circ$ 的整數倍：先加減 $360^\\circ$ 把角度拉進 $0^\\circ\\sim360^\\circ$，再看落在哪個象限。象限不同，後面三個三角比的正負就不同（一全正、二正弦、三正切、四餘弦）。' },
    'L1.pointTrig': { f: function (p) { return quadOf(p.x, p.y); }, why: '終邊上一點 $(x,y)$：$r=\\sqrt{x^2+y^2}$ 永遠是正的，$\\sin=\\dfrac yr$、$\\cos=\\dfrac xr$、$\\tan=\\dfrac yx$ 的正負直接由 $x,y$ 的正負決定——點換了象限，絕對值的算法一樣，只有符號跟著變。' },
    'L1.quadFind': { f: function (p) { return p.kind === 0 ? p.ans : p.quad; }, keep: ['kind'], why: '象限決定三角比的正負（一全正、二只有 $\\sin$ 正、三只有 $\\tan$ 正、四只有 $\\cos$ 正）。由正負判斷象限，是把這張表倒過來查；已知一個三角比求另外兩個，則是先用直角三角形算出<b>絕對值</b>，再用象限<b>定號</b>——兩題的算法一樣，差別只在象限。' },
    'L1.cosLawSide': { f: function (p) { return p.A > 90; }, why: '餘弦定理 $a^2=b^2+c^2-2bc\\cos A$：夾角是銳角時 $\\cos A\\gt0$、第三邊比畢氏定理短；夾角是鈍角時 $\\cos A\\lt0$，「減負變加」，第三邊比畢氏定理長。' },
    'L1.cosLawAngle': { f: function (p) { return p.ans.shape; }, why: '判斷三角形的形狀只要看<b>最大邊</b>所對的角：$\\cos=\\dfrac{\\text{兩小邊平方和}-\\text{最大邊平方}}{2\\times\\text{兩小邊}}$，正 ⟹ 銳角三角形、$0$ ⟹ 直角、負 ⟹ 鈍角。' },
    'L1.ssaCount': { f: function (p) { return p.ans; }, why: 'SSA（兩邊與其中一邊的對角）要比較對邊 $a$ 與高 $h=b\\sin A$：$a\\lt h$ 無解、$a=h$ 恰一解（直角）、$h\\lt a\\lt b$ 兩解、$a\\ge b$ 一解。畫出「從 $C$ 甩一條長 $a$ 的線段」就看得出來。' },
    'L1.polarDist': { f: function (p) { return p.ans.gap > 90; }, why: '兩個極坐標點的距離用餘弦定理，夾角就是極角的差：夾角是鈍角時 $\\cos$ 為負，距離比「兩個 $r$ 的畢氏」還長；面積 $\\dfrac12r_1r_2\\sin(\\text{夾角})$ 則不受銳角鈍角影響。' },
    'L1.bisectorLen': { f: function (p) { return p.A; }, why: '角平分線長用「面積拆兩塊」：$\\dfrac12bc\\sin A=\\dfrac12(b+c)\\cdot\\overline{AD}\\sin\\dfrac A2$。$A=60^\\circ$、$90^\\circ$、$120^\\circ$ 時半角是 $30^\\circ$、$45^\\circ$、$60^\\circ$，公式一樣、代的特殊角值不同。' },
    'L2.quadSumProd': { f: function (p) { return p.quad; }, why: '已知 $\\sin\\theta+\\cos\\theta$：平方得 $\\sin\\theta\\cos\\theta$，再算 $(\\sin\\theta-\\cos\\theta)^2$；<b>差的正負要靠象限判斷</b>——第二象限 $\\sin\\gt0\\gt\\cos$，差為正；第四象限相反。' },
    'L2.sineRatio': { f: function (p) { return p.ans.shape; }, why: '$\\sin A:\\sin B:\\sin C=a:b:c$，所以給正弦的比就是給邊長的比：最大邊所對的角用餘弦定理算 $\\cos$，正負決定是銳角、直角還是鈍角三角形。' },
    'L2.bisector': { f: function (p) { return p.A; }, why: '角平分線的三件事（分對邊成 $c:b$、長度用面積法、兩塊面積比也是 $c:b$）對任何夾角都成立；夾角換了，只是 $\\sin A$、$\\sin\\dfrac A2$ 代的特殊角值換了。' }
  };
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
