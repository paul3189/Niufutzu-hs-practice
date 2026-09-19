/* ══════════════════════════════════════════════════════════════
   g11b-ch04 矩陣與三元一次聯立・分級練習本　題目產生器
   ─────────────────────────────────────────────────────────────
   每個產生器：function (rng) → { q, a, h, p }
     q：題目（HTML，可含 KaTeX $…$）   a：答案（HTML）
     h：一行提示（一定要帶本題的數字與關鍵一步，但不直接給最終答案）
     p：輸入參數與結構化答案 p.ans（給 verify_gen11b4.py 從題幹重算後對照）
   排版慣例照主講義 handouts/g11b-ch04/index.html：
     矩陣一律 \begin{bmatrix}…\end{bmatrix}（782 處）、行列式 \begin{vmatrix}（36 處）、
     增廣矩陣 \left[\begin{array}{ccc|c}…\end{array}\right]、方程組 \begin{cases}。
     轉移方陣：每一「行」的和為 1、右乘行向量（X_{n+1}=M X_n）。
   課綱界線（HANDOUT_SPEC §4 約 450–463 列）：不出現「秩／rank」「線性獨立／相依」
     「轉置」「特徵值／特徵向量／對角化」「伴隨矩陣／餘因子」「馬可夫鏈」「基本列運算」；
     確切算出反方陣僅限二階（三階只判斷 det≠0 存不存在）；
     A^n 用找規律／找週期／拆成 kI+N（N^2=O）；穩定狀態解 MX=X 配 x+y=1；轉移方陣限二階；
     解三元一次聯立的主路是消去法／列運算，克拉瑪只在指定要用時用。
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
    r(); r(); r();   /* 暖機：相近的種子（檢測組用連號）第一個 r() 幾乎一樣，會害 r.int 老是抽到同一個分支 */
    return r;
  }
  function gcd(a, b) { a = Math.abs(a); b = Math.abs(b); while (b) { var t = a % b; a = b; b = t; } return a; }
  function F(n, d) { if (d === undefined) d = 1; if (d < 0) { n = -n; d = -d; } var g = gcd(n, d) || 1; return { n: n / g, d: d / g }; }
  var Fr = {
    add: function (x, y) { return F(x.n * y.d + y.n * x.d, x.d * y.d); },
    sub: function (x, y) { return F(x.n * y.d - y.n * x.d, x.d * y.d); },
    mul: function (x, y) { return F(x.n * y.n, x.d * y.d); },
    div: function (x, y) { return F(x.n * y.d, x.d * y.n); },
    neg: function (x) { return F(-x.n, x.d); },
    eq: function (x, y) { return x.n * y.d === y.n * x.d; },
    cmp: function (x, y) { return x.n * y.d - y.n * x.d; },
    num: function (x) { return x.n / x.d; },
    isz: function (x) { return x.n === 0; },
    isint: function (x) { return x.d === 1; },
    pow: function (x, k) { var t = F(1), i; for (i = 0; i < k; i++) t = Fr.mul(t, x); return t; },
    tex: function (x, small) {
      if (x.d === 1) return String(x.n);
      var f = small ? '\\frac' : '\\dfrac';
      return (x.n < 0 ? '-' : '') + f + '{' + Math.abs(x.n) + '}{' + x.d + '}';
    }
  };
  function fp(f) { return [f.n, f.d]; }
  function T(s) { return '$' + s + '$'; }
  function tx(s) { return '\\text{' + s + '}'; }
  function no(i) { return '(' + i + ') '; }
  function jo(a) { return a.join('　'); }
  /* 乘積一律「括號並列」：(3)(-2)；因數是 1 時不印 */
  function par(s) { s = String(s); return s.indexOf('\\') >= 0 ? '\\left(' + s + '\\right)' : '(' + s + ')'; }
  function prod(list) { var t = [], i, s; for (i = 0; i < list.length; i++) { s = String(list[i]); if (s === '' || s === '1') continue; t.push(par(s)); } return t.length ? t.join('') : '1'; }
  function sup(k) { return k < 10 && k >= 0 ? '^' + k : '^{' + k + '}'; }
  /* 帶正負號接在後面：+3、-3（0 不印） */
  function pm(v) { return v === 0 ? '' : (v < 0 ? '-' : '+') + Math.abs(v); }
  /* 列運算記法：R_i → R_i - k R_j（k 為 1 不印、負數變成加） */
  function opT(i, k, j) { return 'R_' + i + '\\to R_' + i + (k === 0 ? '' : (k > 0 ? '-' : '+') + (Math.abs(k) === 1 ? '' : Math.abs(k)) + 'R_' + j); }
  function opS(i, k, j) { return 'R_' + i + (k === 0 ? '' : (k > 0 ? '-' : '+') + (Math.abs(k) === 1 ? '' : Math.abs(k)) + 'R_' + j); }
  /* 帶正負號的一項：+3k、-k、（係數 0 不印、係數 ±1 不印數字） */
  function tm(c, v) { if (c === 0) return ''; return (c < 0 ? '-' : '+') + (Math.abs(c) === 1 ? '' : Math.abs(c)) + v; }
  /* x : y = a : b 的敘述（分母為 1 時不要寫成 \dfrac{a}{1}） */
  function ratT(a, b) {
    var g = gcd(a, b) || 1; a = a / g; b = b / g;
    if (b === 1) return a === 1 ? 'x=y' : 'x=' + a + 'y';
    if (a === 1) return 'y=' + b + 'x';
    return '\\dfrac{x}{y}=\\dfrac{' + a + '}{' + b + '}';
  }
  function trimz(s) { if (s.indexOf('.') < 0) return s; s = s.replace(/0+$/, ''); if (s.charAt(s.length - 1) === '.') s = s.slice(0, -1); return s; }
  function dc(f) { return trimz((f.n / f.d).toFixed(6)); }

  /* ══ 矩陣工具（元素可以是 number、分數物件 {n,d} 或現成的 LaTeX 字串） ══ */
  function EE(x) { if (typeof x === 'number') return String(x); if (typeof x === 'string') return x; return Fr.tex(x, true); }
  function rws(a) { return a.join('\\\\ '); }
  function MF(A) { return A.map(function (r) { return r.map(function (x) { return (typeof x === 'number') ? F(x) : x; }); }); }
  function VF(v) { return v.map(function (x) { return (typeof x === 'number') ? F(x) : x; }); }
  function bm(M) { return '\\begin{bmatrix}' + rws(M.map(function (r) { return r.map(EE).join('&'); })) + '\\end{bmatrix}'; }
  function vmx(M) { return '\\begin{vmatrix}' + rws(M.map(function (r) { return r.map(EE).join('&'); })) + '\\end{vmatrix}'; }
  function cv(v) { return '\\begin{bmatrix}' + rws(v.map(EE)) + '\\end{bmatrix}'; }
  function agm(M, b) { return '\\left[\\begin{array}{ccc|c}' + rws(M.map(function (r, i) { return r.map(EE).join('&') + '&' + EE(b[i]); })) + '\\end{array}\\right]'; }
  function rowT(r, c) { return '(' + r.map(EE).join(',\\,') + '\\mid ' + EE(c) + ')'; }
  function mAdd(A, B) { return A.map(function (r, i) { return r.map(function (x, j) { return Fr.add(x, B[i][j]); }); }); }
  function mSub(A, B) { return A.map(function (r, i) { return r.map(function (x, j) { return Fr.sub(x, B[i][j]); }); }); }
  function mK(k, A) { var kf = (typeof k === 'number') ? F(k) : k; return A.map(function (r) { return r.map(function (x) { return Fr.mul(kf, x); }); }); }
  function mMul(A, B) {
    var n = A.length, m = B[0].length, p = B.length, out = [], i, j, k, s;
    for (i = 0; i < n; i++) { out.push([]); for (j = 0; j < m; j++) { s = F(0); for (k = 0; k < p; k++) s = Fr.add(s, Fr.mul(A[i][k], B[k][j])); out[i].push(s); } }
    return out;
  }
  function mVec(A, v) { var i, j, s, out = []; for (i = 0; i < A.length; i++) { s = F(0); for (j = 0; j < v.length; j++) s = Fr.add(s, Fr.mul(A[i][j], v[j])); out.push(s); } return out; }
  function dt2(A) { return Fr.sub(Fr.mul(A[0][0], A[1][1]), Fr.mul(A[0][1], A[1][0])); }
  function iv2(A) { var d = dt2(A); return [[Fr.div(A[1][1], d), Fr.div(Fr.neg(A[0][1]), d)], [Fr.div(Fr.neg(A[1][0]), d), Fr.div(A[0][0], d)]]; }
  function mPw(A, n) { var R = [[F(1), F(0)], [F(0), F(1)]], i; for (i = 0; i < n; i++) R = mMul(R, A); return R; }
  function mSame(A, B) { var i, j; for (i = 0; i < A.length; i++) for (j = 0; j < A[0].length; j++) if (!Fr.eq(A[i][j], B[i][j])) return false; return true; }
  function dt3(A) {
    var t = F(0), j, a, b, c, d;
    for (j = 0; j < 3; j++) {
      a = A[1][(j + 1) % 3]; b = A[2][(j + 2) % 3]; c = A[1][(j + 2) % 3]; d = A[2][(j + 1) % 3];
      t = Fr.add(t, Fr.mul(A[0][j], Fr.sub(Fr.mul(a, b), Fr.mul(c, d))));
    }
    return t;
  }
  var ID2 = [[F(1), F(0)], [F(0), F(1)]];

  /* ══ 方程組排版 ══ */
  var VS3 = ['x', 'y', 'z'], VS2 = ['x', 'y'];
  function lin(cs, vs) {
    var s = '', i, c, a;
    for (i = 0; i < cs.length; i++) {
      c = cs[i]; if (c === 0) continue;
      a = Math.abs(c);
      if (s === '') { if (c < 0) s += '-'; } else s += (c < 0 ? '-' : '+');
      if (a !== 1) s += a;
      s += vs[i];
    }
    return s === '' ? '0' : s;
  }
  function csys(M, b, vs) { return '\\begin{cases}' + rws(M.map(function (r, i) { return lin(r, vs || VS3) + '=' + b[i]; })) + '\\end{cases}'; }
  /* 三元一次聯立：用整數列運算把係數矩陣造成「有整數唯一解」 */
  function sysUnique(r) {
    var A, b, x, tries = 0, D;
    do {
      A = [[1, r.nz(-3, 3), r.nz(-3, 3)], [r.nz(-3, 3), r.nz(-4, 4), r.nz(-4, 4)], [r.nz(-3, 3), r.nz(-4, 4), r.nz(-4, 4)]];
      D = Fr.num(dt3(MF(A)));
      tries++;
    } while ((D === 0 || Math.abs(D) > 40) && tries < 60);
    x = [r.nz(-4, 4), r.nz(-4, 4), r.nz(-4, 4)];
    b = A.map(function (row) { return row[0] * x[0] + row[1] * x[1] + row[2] * x[2]; });
    return { A: A, b: b, x: x, D: D };
  }
  /* 由兩條「有效方程式」與一條組合列造出「無限多解」或「無解」的三元系統 */
  function sysDegenerate(r, noSol) {
    var r1, r2, k1, k2, r3, b3, x0, t, A, b;
    r1 = [1, r.nz(-3, 3), r.nz(-3, 3)];
    do { r2 = [r.nz(-3, 3), r.nz(-3, 3), r.nz(-3, 3)]; } while (r2[0] * r1[1] - r2[1] * r1[0] === 0 && r2[0] * r1[2] - r2[2] * r1[0] === 0);
    k1 = r.nz(-2, 2); k2 = r.nz(-2, 2);
    x0 = [r.nz(-3, 3), r.nz(-3, 3), 0];          /* 只用來定常數，真正的解集合由驗算器自己算 */
    var b1 = r.int(-8, 8), b2 = r.int(-8, 8);
    r3 = [k1 * r1[0] + k2 * r2[0], k1 * r1[1] + k2 * r2[1], k1 * r1[2] + k2 * r2[2]];
    b3 = k1 * b1 + k2 * b2 + (noSol ? r.nz(1, 4) : 0);
    A = [r1, r2, r3]; b = [b1, b2, b3];
    return { A: A, b: b, k1: k1, k2: k2 };
  }

  /* ══ 特殊角（旋轉／鏡射只用這些角，值全部精確） ══ */
  var ANG = {
    0: { c: '1', s: '0' }, 30: { c: '\\frac{\\sqrt{3}}{2}', s: '\\frac{1}{2}' },
    45: { c: '\\frac{\\sqrt{2}}{2}', s: '\\frac{\\sqrt{2}}{2}' }, 60: { c: '\\frac{1}{2}', s: '\\frac{\\sqrt{3}}{2}' },
    90: { c: '0', s: '1' }, 120: { c: '-\\frac{1}{2}', s: '\\frac{\\sqrt{3}}{2}' },
    135: { c: '-\\frac{\\sqrt{2}}{2}', s: '\\frac{\\sqrt{2}}{2}' }, 150: { c: '-\\frac{\\sqrt{3}}{2}', s: '\\frac{1}{2}' },
    180: { c: '-1', s: '0' }, 210: { c: '-\\frac{\\sqrt{3}}{2}', s: '-\\frac{1}{2}' },
    225: { c: '-\\frac{\\sqrt{2}}{2}', s: '-\\frac{\\sqrt{2}}{2}' }, 240: { c: '-\\frac{1}{2}', s: '-\\frac{\\sqrt{3}}{2}' },
    270: { c: '0', s: '-1' }, 300: { c: '\\frac{1}{2}', s: '-\\frac{\\sqrt{3}}{2}' },
    315: { c: '\\frac{\\sqrt{2}}{2}', s: '-\\frac{\\sqrt{2}}{2}' }, 330: { c: '\\frac{\\sqrt{3}}{2}', s: '-\\frac{1}{2}' }
  };
  function ngt(s) { return s === '0' ? '0' : (s.charAt(0) === '-' ? s.slice(1) : '-' + s); }
  function md360(d) { d = d % 360; return d < 0 ? d + 360 : d; }
  function rotM(deg) { var a = ANG[md360(deg)]; return [[a.c, ngt(a.s)], [a.s, a.c]]; }
  function refM(deg) { var a = ANG[md360(2 * deg)]; return [[a.c, a.s], [a.s, ngt(a.c)]]; }
  function degT(d) { return d + '^\\circ'; }
  /* 鏡射軸：角度 → 題幹敘述（tan 是特殊值） */
  var AXIS = {
    0: { t: '對 ' + T('x') + ' 軸鏡射', m: [[1, 0], [0, -1]] },
    30: { t: '對直線 ' + T('y=\\frac{x}{\\sqrt{3}}') + ' 鏡射' },
    45: { t: '對直線 ' + T('y=x') + ' 鏡射' },
    60: { t: '對直線 ' + T('y=\\sqrt{3}x') + ' 鏡射' },
    90: { t: '對 ' + T('y') + ' 軸鏡射', m: [[-1, 0], [0, 1]] },
    120: { t: '對直線 ' + T('y=-\\sqrt{3}x') + ' 鏡射' },
    135: { t: '對直線 ' + T('y=-x') + ' 鏡射' },
    150: { t: '對直線 ' + T('y=-\\frac{x}{\\sqrt{3}}') + ' 鏡射' }
  };

  /* ══ 五種基本變換（整數矩陣版，供合成用） ══ */
  function basicInt(r) {
    switch (r.int(0, 5)) {
      case 0: var a = r.nz(-3, 3), b2 = r.nz(-3, 3); return { t: '以原點為中心，沿 ' + T('x') + ' 方向伸縮 ' + T(a) + ' 倍、沿 ' + T('y') + ' 方向伸縮 ' + T(b2) + ' 倍', M: [[a, 0], [0, b2]] };
      case 1: var k = r.nz(-3, 3); return { t: '沿 ' + T('x') + ' 軸方向推移 ' + T('y') + ' 坐標的 ' + T(k) + ' 倍', M: [[1, k], [0, 1]] };
      case 2: var k2 = r.nz(-3, 3); return { t: '沿 ' + T('y') + ' 軸方向推移 ' + T('x') + ' 坐標的 ' + T(k2) + ' 倍', M: [[1, 0], [k2, 1]] };
      case 3: var d = r.pick([90, 180, 270]); return { t: '以原點為中心逆時針旋轉 ' + T(degT(d)), M: [[Math.round(Math.cos(d * Math.PI / 180)), -Math.round(Math.sin(d * Math.PI / 180))], [Math.round(Math.sin(d * Math.PI / 180)), Math.round(Math.cos(d * Math.PI / 180))]] };
      case 4: var g = r.pick([0, 45, 90, 135]); return { t: AXIS[g].t, M: g === 0 ? [[1, 0], [0, -1]] : (g === 45 ? [[0, 1], [1, 0]] : (g === 90 ? [[-1, 0], [0, 1]] : [[0, -1], [-1, 0]])) };
      default: var ax = r.pick(['x', 'y']); return { t: '投影到 ' + T(ax) + ' 軸', M: ax === 'x' ? [[1, 0], [0, 0]] : [[0, 0], [0, 1]] };
    }
  }

  /* ══ 隨機二階整數方陣 ══ */
  function rm2(r, lo, hi) { return [[r.int(lo, hi), r.int(lo, hi)], [r.int(lo, hi), r.int(lo, hi)]]; }
  function rm2nz(r, lo, hi) { var A, t = 0; do { A = rm2(r, lo, hi); t++; } while (Fr.num(dt2(MF(A))) === 0 && t < 50); return A; }
  function rm2det(r, lo, hi, want) { var A, t = 0; do { A = rm2(r, lo, hi); t++; } while (Fr.num(dt2(MF(A))) !== want && t < 400); return A; }

  /* ══ 常用敘述 ══ */
  var SOLW = { one: '恰有一組解', inf: '有無限多組解', none: '無解' };
  function paramTex(co, cn, vs) {
    /* co：t 的係數陣列，cn：常數陣列 → (x,y,z)=(cn0+co0 t, …) */
    var ps = co.map(function (c, i) {
      var k = cn[i], s = '';
      if (Fr.num(c) === 0) return EE(k);
      if (Fr.num(k) !== 0) s += EE(k);
      var cnum = Fr.num(c);
      if (s === '') s += (cnum === 1 ? 't' : (cnum === -1 ? '-t' : EE(c) + 't'));
      else s += (cnum > 0 ? '+' : '-') + (Math.abs(cnum) === 1 ? 't' : EE(F(Math.abs(c.n), c.d)) + 't');
      return s;
    });
    return '(' + (vs || VS3).join(',') + ')=(' + ps.join(',\\,') + ')';
  }

  /* ═══════════════════════ L1 ═══════════════════════ */
  var L1 = {};

  /* ── §1 寫出係數方陣與矩陣形式 ── */
  L1.matForm = function (r) {
    var kind = r.int(0, 2), A, b, i, j, q, a, h, p;
    if (kind === 0) {
      A = [[r.nz(-6, 6), r.nz(-6, 6)], [r.nz(-6, 6), r.nz(-6, 6)]];
      b = [r.int(-9, 9), r.int(-9, 9)];
      i = r.int(1, 2); j = r.int(1, 2);
      q = '把方程組 ' + T(csys(A, b, VS2)) + ' 寫成 ' + T('A\\vec{x}=\\vec{b}') + ' 的形式：寫出係數方陣 ' + T('A') + '、常數行向量 ' + T('\\vec{b}') + '，並求元素 ' + T('a_{' + i + j + '}') + '。';
      a = jo([no(1) + T('A=' + bm(A)), no(2) + T('\\vec{b}=' + cv(b)), no(3) + T('a_{' + i + j + '}=' + A[i - 1][j - 1])]);
      h = '係數照原順序抄下來：第一列是 ' + T('(' + A[0][0] + ',\\,' + A[0][1] + ')') + '、第二列是 ' + T('(' + A[1][0] + ',\\,' + A[1][1] + ')') + '；' + T('a_{' + i + j + '}') + ' 是第 ' + T(i) + ' 列第 ' + T(j) + ' 行那一格。';
      p = { kind: 0, A: A, b: b, i: i, j: j, ans: { A: A, b: b, e: A[i - 1][j - 1] } };
    } else if (kind === 1) {
      A = [[1, 0, r.nz(-4, 4)], [r.nz(-3, 3), r.nz(-3, 3), 0], [0, r.nz(-3, 3), r.nz(-3, 3)]];
      if (r.int(0, 1)) { A[0] = [r.nz(-3, 3), r.nz(-3, 3), 0]; A[1] = [0, r.nz(-3, 3), r.nz(-3, 3)]; A[2] = [r.nz(-3, 3), 0, r.nz(-3, 3)]; }
      b = [r.int(-8, 8), r.int(-8, 8), r.int(-8, 8)];
      q = '把方程組 ' + T(csys(A, b)) + ' 寫成 ' + T('A\\vec{x}=\\vec{b}') + ' 的形式（缺的項要補 ' + T(0) + '），並說出 ' + T('A') + ' 是幾階方陣。';
      a = jo([no(1) + T('A=' + bm(A)), no(2) + T('\\vec{b}=' + cv(b)), no(3) + '三階方陣']);
      h = '每一式都要湊滿 ' + T('x,\\,y,\\,z') + ' 三格：第一式是 ' + T(lin(A[0], VS3) + '=' + b[0]) + '，缺的字母那一格填 ' + T(0) + ' ⟹ 第一列 ' + T('(' + A[0].join(',\\,') + ')') + '。';
      p = { kind: 1, A: A, b: b, ans: { A: A, b: b } };
    } else {
      A = rm2nz(r, -5, 5);
      var x = [r.nz(-5, 5), r.nz(-5, 5)];
      b = [A[0][0] * x[0] + A[0][1] * x[1], A[1][0] * x[0] + A[1][1] * x[1]];
      q = '已知 ' + T(bm(A) + cv(VS2) + '=' + cv(b)) + '。' + no(1) + '把它還原成聯立方程組。' + no(2) + '解出 ' + T('(x,y)') + '。';
      a = jo([no(1) + T(csys(A, b, VS2)), no(2) + T('(x,y)=(' + x[0] + ',' + x[1] + ')')]);
      h = '第一列 ' + T('(' + A[0][0] + ',\\,' + A[0][1] + ')') + ' 配上 ' + T('(x,y)') + ' 得 ' + T(lin(A[0], VS2) + '=' + b[0]) + '；第二列同理得 ' + T(lin(A[1], VS2) + '=' + b[1]) + '，再解這個二元一次聯立。';
      p = { kind: 2, A: A, b: b, ans: { x: x } };
    }
    return { q: q, a: a, h: h, p: p };
  };

  /* ── §1 方陣乘向量 ＝ 線性組合 ── */
  L1.matVec = function (r) {
    var A = rm2(r, -5, 5), v = [r.nz(-4, 4), r.nz(-4, 4)], w = mVec(MF(A), VF(v));
    var q = '設 ' + T('A=' + bm(A)) + '。' + no(1) + '求 ' + T('A' + cv(v)) + '。' + no(2) + '把 ' + T('A' + cv(VS2)) + ' 寫成 ' + T('A') + ' 的兩個行向量的線性組合。';
    var a = jo([no(1) + T(cv(w)), no(2) + T('x' + cv([A[0][0], A[1][0]]) + '+y' + cv([A[0][1], A[1][1]]))]);
    var h = '「橫的乘直的再相加」：第一列 ' + T(prod([A[0][0], v[0]]) + '+' + prod([A[0][1], v[1]])) + '、第二列 ' + T(prod([A[1][0], v[0]]) + '+' + prod([A[1][1], v[1]])) + '；' + no(2) + ' 把同一個式子按 ' + T('x') + '、' + T('y') + ' 分組即可。';
    return { q: q, a: a, h: h, p: { A: A, v: v, ans: { w: w.map(fp) } } };
  };

  /* ── §1 二階行列式（值、平行、面積） ── */
  L1.det2 = function (r) {
    var kind = r.int(0, 1), A, B, dA, dB, q, a, h, p;
    if (kind === 0) {
      A = rm2nz(r, -6, 6);
      do { var k = r.nz(-3, 3), u = [r.nz(-4, 4), r.nz(-4, 4)]; B = [[u[0], k * u[0]], [u[1], k * u[1]]]; } while (u[0] === 0 && u[1] === 0);
      dA = Fr.num(dt2(MF(A)));
      q = '設 ' + T('A=' + bm(A)) + '、' + T('B=' + bm(B)) + '。' + no(1) + '求 ' + T('\\det A') + '。' + no(2) + '求 ' + T('\\det B') + '。' + no(3) + '哪一個方陣的兩個行向量互相平行？';
      a = jo([no(1) + T('\\det A=' + dA), no(2) + T('\\det B=0'), no(3) + T('B')]);
      h = T('\\det A=' + prod([A[0][0], A[1][1]]) + '-' + prod([A[0][1], A[1][0]]) + '=' + dA) + '；' + T('B') + ' 的第二行是第一行的 ' + T(k) + ' 倍 ⟹ 兩行平行 ⟹ 行列式為 ' + T(0) + '。';
      p = { kind: 0, A: A, B: B, k: k, ans: { dA: dA, dB: 0 } };
    } else {
      var u2 = [r.nz(-6, 6), r.nz(-6, 6)], v2 = [r.nz(-6, 6), r.nz(-6, 6)];
      var d = u2[0] * v2[1] - u2[1] * v2[0];
      if (d === 0) { v2[1] += 1; d = u2[0] * v2[1] - u2[1] * v2[0]; }
      A = [[u2[0], v2[0]], [u2[1], v2[1]]];
      q = '設 ' + T('\\vec{u}=(' + u2[0] + ',' + u2[1] + ')') + '、' + T('\\vec{v}=(' + v2[0] + ',' + v2[1] + ')') + '。' + no(1) + '求行列式 ' + T(vmx(A)) + ' 的值。' + no(2) + '求以 ' + T('\\vec{u}') + '、' + T('\\vec{v}') + ' 為鄰邊的平行四邊形面積。';
      a = jo([no(1) + T(d), no(2) + T(Math.abs(d))]);
      h = '把 ' + T('\\vec{u}') + ' 當第一行、' + T('\\vec{v}') + ' 當第二行：' + T(prod([u2[0], v2[1]]) + '-' + prod([v2[0], u2[1]]) + '=' + d) + '；面積是它的絕對值（負號只代表轉向）。';
      p = { kind: 1, u: u2, v: v2, ans: { d: d } };
    }
    return { q: q, a: a, h: h, p: p };
  };

  /* ── §1 二元克拉瑪公式 ── */
  L1.cramer2 = function (r) {
    var A, b, D, Dx, Dy, x, y, t = 0;
    do { A = rm2(r, -6, 6); D = A[0][0] * A[1][1] - A[0][1] * A[1][0]; t++; } while ((D === 0 || Math.abs(D) > 24) && t < 200);
    b = [r.int(-9, 9), r.int(-9, 9)];
    Dx = b[0] * A[1][1] - A[0][1] * b[1];
    Dy = A[0][0] * b[1] - b[0] * A[1][0];
    x = F(Dx, D); y = F(Dy, D);
    var q = '用克拉瑪公式解 ' + T(csys(A, b, VS2)) + '：' + no(1) + '求 ' + T('\\Delta') + '、' + T('\\Delta_x') + '、' + T('\\Delta_y') + '。' + no(2) + '求 ' + T('(x,y)') + '。';
    var a = jo([no(1) + T('\\Delta=' + D) + '，' + T('\\Delta_x=' + Dx) + '，' + T('\\Delta_y=' + Dy), no(2) + T('(x,y)=\\left(' + Fr.tex(x, true) + ',\\,' + Fr.tex(y, true) + '\\right)')]);
    var h = T('\\Delta=' + vmx(A) + '=' + prod([A[0][0], A[1][1]]) + '-' + prod([A[0][1], A[1][0]]) + '=' + D) + '，不為 ' + T(0) + ' ⟹ 公式可用；求 ' + T('x') + ' 就把第一行換成常數行 ' + T('(' + b[0] + ',\\,' + b[1] + ')') + '，再除以 ' + T('\\Delta') + '。';
    return { q: q, a: a, h: h, p: { A: A, b: b, ans: { D: D, Dx: Dx, Dy: Dy, x: fp(x), y: fp(y) } } };
  };

  /* ── §1 二元聯立解的三種情況 ── */
  L1.twoLineCase = function (r) {
    var kind = r.int(0, 2), A, b, q, a, h, p, lab, sol = null, par2 = null;
    if (kind === 0) {
      var t = 0, D;
      do { A = rm2(r, -5, 5); D = A[0][0] * A[1][1] - A[0][1] * A[1][0]; t++; } while ((D === 0 || Math.abs(D) > 20) && t < 200);
      var x0 = [r.nz(-4, 4), r.nz(-4, 4)];
      b = [A[0][0] * x0[0] + A[0][1] * x0[1], A[1][0] * x0[0] + A[1][1] * x0[1]];
      lab = SOLW.one; sol = x0;
      a = jo([lab, T('(x,y)=(' + x0[0] + ',' + x0[1] + ')')]);
      h = T('\\Delta=' + prod([A[0][0], A[1][1]]) + '-' + prod([A[0][1], A[1][0]]) + '=' + D) + '，不為 ' + T(0) + ' ⟹ 兩直線不平行 ⟹ 恰交於一點，接著解即可。';
    } else {
      var a1 = r.nz(-4, 4), b1 = r.nz(-4, 4), c1 = r.int(-8, 8), k = r.nz(-3, 3);
      if (k === 1) k = 2;
      A = [[a1, b1], [k * a1, k * b1]];
      b = [c1, k * c1 + (kind === 1 ? 0 : r.nz(1, 5))];
      if (kind === 1) {
        lab = SOLW.inf;
        /* 令 y=|a1| t 避開分數：x=(c1-b1 y)/a1 */
        var co = F(-b1 * Math.abs(a1), a1), cn = F(c1, a1);
        par2 = { cox: co, cnx: cn, coy: Math.abs(a1) };
        a = jo([lab, T(paramTex([co, F(Math.abs(a1))], [cn, F(0)], VS2)) + '，' + T('t') + ' 為實數']);
        h = '第二式 ' + T(lin(A[1], VS2) + '=' + b[1]) + ' 恰好是第一式的 ' + T(k) + ' 倍（連常數項也是）⟹ 兩式其實是同一條直線 ⟹ 只剩一條有效方程式。';
      } else {
        lab = SOLW.none;
        a = lab;
        h = '第二式的左邊是第一式的 ' + T(k) + ' 倍，但右邊 ' + T(b[1]) + ' 不等於 ' + T(prod([k, c1]) + '=' + (k * c1)) + ' ⟹ 化簡後會出現 ' + T('0=' + (b[1] - k * c1)) + ' 的矛盾。';
      }
    }
    q = '判斷方程組 ' + T(csys(A, b, VS2)) + ' 是恰有一組解、無解，還是有無限多組解？有解時請把解寫出來。';
    p = { kind: kind, A: A, b: b, lab: lab, ans: { lab: lab, sol: sol } };
    return { q: q, a: a, h: h, p: p };
  };

  /* ── §1 行向量的線性組合：組得出 b 嗎 ── */
  L1.colCombo = function (r) {
    var kind = r.int(0, 2), u = [r.nz(-5, 5), r.nz(-5, 5)], k = r.nz(-3, 3), B, b, lab, q, a, h;
    if (k === 1) k = 2;
    if (kind === 2) {
      var v = [r.nz(-5, 5), r.nz(-5, 5)], t = 0;
      while (u[0] * v[1] - u[1] * v[0] === 0 && t < 20) { v = [r.nz(-5, 5), r.nz(-5, 5)]; t++; }
      B = [[u[0], v[0]], [u[1], v[1]]];
      b = [r.nz(-8, 8), r.nz(-8, 8)];
      lab = SOLW.one;
      h = T('B') + ' 的兩個行向量 ' + T('(' + u[0] + ',' + u[1] + ')') + ' 與 ' + T('(' + v[0] + ',' + v[1] + ')') + ' 不平行（' + T('\\det B=' + prod([u[0], v[1]]) + '-' + prod([v[0], u[1]]) + '=' + (u[0] * v[1] - u[1] * v[0])) + '，不為 ' + T(0) + '）⟹ 它們可以組合出平面上任何向量。';
    } else {
      B = [[u[0], k * u[0]], [u[1], k * u[1]]];
      var m = r.nz(-4, 4);
      b = kind === 0 ? [m * u[0], m * u[1]] : [m * u[0] + r.nz(1, 3), m * u[1]];
      if (kind === 1 && b[0] * u[1] - b[1] * u[0] === 0) b[0] += 1;
      lab = kind === 0 ? SOLW.inf : SOLW.none;
      h = T('B') + ' 的兩行 ' + T('(' + u[0] + ',' + u[1] + ')') + ' 與 ' + T('(' + (k * u[0]) + ',' + (k * u[1]) + ')') + ' 平行（後者是前者的 ' + T(k) + ' 倍）⟹ 只能組合出這條直線上的向量；再問 ' + T('(' + b[0] + ',' + b[1] + ')') + ' 在不在這條線上。';
    }
    var dB = B[0][0] * B[1][1] - B[0][1] * B[1][0];
    q = '設 ' + T('B=' + bm(B)) + '。' + no(1) + '求 ' + T('\\det B') + '。' + no(2) + '判斷 ' + T('B' + cv(VS2) + '=' + cv(b)) + ' 有幾組解（恰有一組、無解，或無限多組），並用「兩個行向量的線性組合」說明理由。';
    a = jo([no(1) + T('\\det B=' + dB), no(2) + lab]);
    return { q: q, a: a, h: h, p: { kind: kind, B: B, b: b, ans: { dB: dB, lab: lab } } };
  };

  /* ── §2 增廣矩陣與列運算 ── */
  L1.augRowOp = function (r) {
    var S = sysUnique(r), A = S.A, b = S.b;
    var m2 = A[1][0] / A[0][0], m3 = A[2][0] / A[0][0];
    /* A[0][0] 一定是 1，所以倍數就是 A[1][0]、A[2][0] */
    var R2 = [0, A[1][1] - m2 * A[0][1], A[1][2] - m2 * A[0][2]], c2 = b[1] - m2 * b[0];
    var R3 = [0, A[2][1] - m3 * A[0][1], A[2][2] - m3 * A[0][2]], c3 = b[2] - m3 * b[0];
    var op2 = opT(2, m2, 1), op3 = opT(3, m3, 1);
    var q = '設方程組 ' + T(csys(A, b)) + '。' + no(1) + '寫出它的增廣矩陣。' + no(2) + '依序執行 ' + T(op2) + ' 與 ' + T(op3) + '，寫出結果。';
    var a = jo([no(1) + T(agm(A, b)), no(2) + T(agm([A[0], R2, R3], [b[0], c2, c3]))]);
    var h = '列運算是「整列一起動」，最右邊的常數項一個都不能漏：第二列 ' + T(rowT(A[1], b[1])) + ' 做 ' + T(opS(2, m2, 1)) + ' ⟹ ' + T(rowT(R2, c2)) + '。';
    return { q: q, a: a, h: h, p: { A: A, b: b, m2: m2, m3: m3, ans: { R2: R2, c2: c2, R3: R3, c3: c3 } } };
  };

  /* ── §2 消去法解三元一次聯立 ── */
  L1.elim3 = function (r) {
    var S = sysUnique(r), A = S.A, b = S.b, x = S.x;
    var m2 = A[1][0], m3 = A[2][0];
    var R2 = [0, A[1][1] - m2 * A[0][1], A[1][2] - m2 * A[0][2]], c2 = b[1] - m2 * b[0];
    var q = '用消去法（或列運算）解 ' + T(csys(A, b)) + '。';
    var a = T('(x,y,z)=(' + x.join(',') + ')');
    var h = '先用第一式把 ' + T('x') + ' 消掉：' + T(opS(2, m2, 1)) + ' ⟹ ' + T(rowT(R2, c2)) + '；同樣做 ' + T(opS(3, m3, 1)) + '，就只剩 ' + T('y,\\,z') + ' 兩個未知數了。';
    return { q: q, a: a, h: h, p: { A: A, b: b, ans: { x: x } } };
  };

  /* ── §2 由階梯形讀答案 ── */
  L1.echelonRead = function (r) {
    var kind = r.int(0, 2), M, c, q, a, h, lab, p;
    var p11 = r.nz(-3, 3), p12 = r.int(-4, 4), p13 = r.int(-4, 4), d1 = r.int(-8, 8);
    var p22 = r.nz(-4, 4), p23 = r.int(-4, 4), d2 = r.int(-8, 8);
    if (kind === 0) {
      var p33 = r.nz(-4, 4), d3 = p33 * r.nz(-3, 3);
      M = [[p11, p12, p13], [0, p22, p23], [0, 0, p33]]; c = [d1, d2, d3];
      var z = F(d3, p33), y = Fr.div(Fr.sub(F(d2), Fr.mul(F(p23), z)), F(p22));
      var xx = Fr.div(Fr.sub(Fr.sub(F(d1), Fr.mul(F(p12), y)), Fr.mul(F(p13), z)), F(p11));
      lab = SOLW.one;
      a = jo([lab, T('(x,y,z)=\\left(' + Fr.tex(xx, true) + ',\\,' + Fr.tex(y, true) + ',\\,' + Fr.tex(z, true) + '\\right)')]);
      h = '三列都有領導元素 ⟹ 三個未知數都被定住。最後一列是 ' + T(lin([0, 0, p33], VS3) + '=' + d3) + ' ⟹ ' + T('z=' + Fr.tex(z, true)) + '，再由下往上代回。';
      p = { kind: 0, M: M, c: c, ans: { lab: lab } };
    } else if (kind === 1) {
      M = [[p11, p12, p13], [0, p22, p23], [0, 0, 0]]; c = [d1, d2, 0];
      lab = SOLW.inf;
      /* 令 z = |p11 p22| t 避開分數 */
      var s = Math.abs(p11 * p22);
      var yy = Fr.div(F(-p23 * s), F(p22)), ycn = F(d2, p22);
      var xco = Fr.div(Fr.sub(Fr.mul(F(-p12), yy), F(p13 * s)), F(p11)), xcn = Fr.div(Fr.sub(F(d1), Fr.mul(F(p12), ycn)), F(p11));
      a = jo([lab, T(paramTex([xco, yy, F(s)], [xcn, ycn, F(0)])) + '，' + T('t') + ' 為實數']);
      h = '第三列整列是 ' + T('0') + '（也就是 ' + T('0=0') + '，沒有提供新資訊）⟹ 三個未知數只剩兩條有效方程式 ⟹ 有一個字母自由。令 ' + T('z=' + (s === 1 ? 't' : s + 't')) + '（這樣可以避開分數），再由第二列 ' + T(lin([0, p22, p23], VS3) + '=' + d2) + ' 解出 ' + T('y') + '。';
      p = { kind: 1, M: M, c: c, ans: { lab: lab } };
    } else {
      var kk = r.nz(-5, 5);
      M = [[p11, p12, p13], [0, p22, p23], [0, 0, 0]]; c = [d1, d2, kk];
      lab = SOLW.none;
      a = lab;
      h = '第三列的三個係數全部是 ' + T(0) + '，而常數項是 ' + T(kk) + ' ⟹ 還原成方程式就是 ' + T('0=' + kk) + ' ⟹ 矛盾，不必再往下算。';
      p = { kind: 2, M: M, c: c, ans: { lab: lab } };
    }
    q = '某三元一次方程組的增廣矩陣經列運算後化為 ' + T(agm(M, c)) + '。判斷它是恰有一組解、無解，還是有無限多組解？有解時請把所有的解寫出來。';
    return { q: q, a: a, h: h, p: p };
  };

  /* ── §2 三階克拉瑪公式 ── */
  L1.cramer3 = function (r) {
    var S = sysUnique(r), A = S.A, b = S.b, x = S.x, D = S.D;
    var col = function (j) { return A.map(function (row, i) { return row.map(function (v, jj) { return jj === j ? b[i] : v; }); }); };
    var Dx = Fr.num(dt3(MF(col(0)))), Dy = Fr.num(dt3(MF(col(1)))), Dz = Fr.num(dt3(MF(col(2))));
    var q = '用克拉瑪公式解 ' + T(csys(A, b)) + '：' + no(1) + '求 ' + T('\\Delta') + '。' + no(2) + '求 ' + T('\\Delta_x') + '、' + T('\\Delta_y') + '、' + T('\\Delta_z') + '。' + no(3) + '求 ' + T('(x,y,z)') + '。';
    var a = jo([no(1) + T('\\Delta=' + D), no(2) + T('\\Delta_x=' + Dx) + '，' + T('\\Delta_y=' + Dy) + '，' + T('\\Delta_z=' + Dz), no(3) + T('(x,y,z)=(' + x.join(',') + ')')]);
    var h = '先算 ' + T('\\Delta=' + vmx(A) + '=' + D) + '，不為 ' + T(0) + ' 才能用公式；求 ' + T('y') + ' 就把第二行換成常數行 ' + T('(' + b.join(',\\,') + ')') + '，其餘兩行不動。';
    return { q: q, a: a, h: h, p: { A: A, b: b, ans: { D: D, Dx: Dx, Dy: Dy, Dz: Dz, x: x } } };
  };

  /* ── §2 三元聯立解的個數（先算 Δ） ── */
  L1.countSol3 = function (r) {
    var kind = r.int(0, 2), A, b, lab, q, a, h, D;
    if (kind === 0) {
      var S = sysUnique(r); A = S.A; b = S.b; D = S.D; lab = SOLW.one;
      a = jo([T('\\Delta=' + D), lab]);
      h = T('\\Delta=' + D) + '，不為 ' + T(0) + ' ⟹ 第一刀就判完了（克拉瑪公式可用），不必再化階梯形。';
    } else {
      var G = sysDegenerate(r, kind === 2); A = G.A; b = G.b; D = 0; lab = kind === 1 ? SOLW.inf : SOLW.none;
      a = jo([T('\\Delta=0'), lab]);
      h = '第三式 ' + T(lin(A[2], VS3) + '=' + b[2]) + ' 的係數恰是第一式的 ' + T(G.k1) + ' 倍加第二式的 ' + T(G.k2) + ' 倍 ⟹ ' + T('\\Delta=0') + '；再比對常數項：' + T(prod([G.k1, b[0]]) + '+' + prod([G.k2, b[1]]) + '=' + (G.k1 * b[0] + G.k2 * b[1])) + '，和 ' + T(b[2]) + ' 是否相同決定了是哪一種。';
    }
    q = '設方程組 ' + T(csys(A, b)) + '。' + no(1) + '求係數方陣的行列式 ' + T('\\Delta') + '。' + no(2) + '判斷這個方程組是恰有一組解、無解，還是有無限多組解。';
    return { q: q, a: a, h: h, p: { kind: kind, A: A, b: b, ans: { D: D, lab: lab } } };
  };

  /* ── §3 Δ≠0：三平面交於一點 ── */
  L1.planeOne = function (r) {
    var S = sysUnique(r), A = S.A, b = S.b, x = S.x, D = S.D;
    var q = '設三個平面 ' + T('E_1:' + lin(A[0], VS3) + '=' + b[0]) + '、' + T('E_2:' + lin(A[1], VS3) + '=' + b[1]) + '、' + T('E_3:' + lin(A[2], VS3) + '=' + b[2]) + '。' + no(1) + '求 ' + T('\\Delta') + '。' + no(2) + '判斷三平面的位置關係。' + no(3) + '求它們的公共部分。';
    var a = jo([no(1) + T('\\Delta=' + D), no(2) + '三平面交於一點', no(3) + T('(x,y,z)=(' + x.join(',') + ')')]);
    var h = '判定流程第 ' + T(1) + ' 步：' + T('\\Delta=' + D) + ' 不為 ' + T(0) + ' ⟹ 三個法向量張得出整個空間 ⟹ 交於唯一一點，直接解聯立就好。';
    return { q: q, a: a, h: h, p: { A: A, b: b, ans: { D: D, x: x } } };
  };

  /* ── §3 Δ=0 且有解：②③④ ── */
  L1.planeCase = function (r) {
    var kind = r.int(0, 2), A, b, lab, q, a, h, ansTex, p;
    if (kind === 2) {
      /* ④ 三平面重合 */
      var r1 = [1, r.nz(-3, 3), r.nz(-3, 3)], c1 = r.int(-6, 6), k2 = r.pick([2, 3, -2]), k3 = r.pick([-3, 4, 5]);
      A = [r1, r1.map(function (v) { return k2 * v; }), r1.map(function (v) { return k3 * v; })];
      b = [c1, k2 * c1, k3 * c1];
      lab = '三平面重合（剩 ' + T(1) + ' 條有效方程式）';
      ansTex = '公共部分是整個平面 ' + T(lin(r1, VS3) + '=' + c1) + '（要用兩個參數）';
      h = '第二式是第一式的 ' + T(k2) + ' 倍、第三式是第一式的 ' + T(k3) + ' 倍（連常數項也成同一比例）⟹ 化完階梯形只剩 ' + T(1) + ' 條有效方程式 ⟹ 自由度是 ' + T('3-1=2') + '。';
    } else {
      /* ② 三相異平面交於一線；③ 兩平面重合，第三平面與之交於一線 */
      var e1 = [1, r.nz(-3, 3), r.nz(-3, 3)], d1 = r.int(-6, 6);
      var e2, d2, t = 0;
      do { e2 = [r.nz(-3, 3), r.nz(-3, 3), r.nz(-3, 3)]; t++; } while (t < 30 && (e2[0] * e1[1] - e2[1] * e1[0] === 0 && e2[0] * e1[2] - e2[2] * e1[0] === 0));
      d2 = r.int(-6, 6);
      if (kind === 0) {
        var k1 = r.nz(-2, 2), kk2 = r.nz(-2, 2);
        A = [e1, e2, [k1 * e1[0] + kk2 * e2[0], k1 * e1[1] + kk2 * e2[1], k1 * e1[2] + kk2 * e2[2]]];
        b = [d1, d2, k1 * d1 + kk2 * d2];
        lab = '三相異平面共交於一線';
        h = '第三式恰是第一式的 ' + T(k1) + ' 倍加第二式的 ' + T(kk2) + ' 倍（常數項也對得上）⟹ 化完剩 ' + T(2) + ' 條有效方程式，而三個法向量兩兩不平行。';
      } else {
        var kd = r.pick([2, 3, -2, -3]);
        A = [e1, e1.map(function (v) { return kd * v; }), e2];
        b = [d1, kd * d1, d2];
        lab = '兩平面重合，第三平面與它們交於一線';
        h = '第二式 ' + T(lin(A[1], VS3) + '=' + b[1]) + ' 是第一式的 ' + T(kd) + ' 倍（連常數項也是）⟹ 這兩個平面重合；第三式的法向量與它們不平行 ⟹ 交出一條直線。';
      }
      ansTex = '公共部分是一條直線（' + T(1) + ' 個參數）';
    }
    q = '設三個平面 ' + T('E_1:' + lin(A[0], VS3) + '=' + b[0]) + '、' + T('E_2:' + lin(A[1], VS3) + '=' + b[1]) + '、' + T('E_3:' + lin(A[2], VS3) + '=' + b[2]) + '（它們的 ' + T('\\Delta=0') + ' 且有解）。' + no(1) + '化成階梯形後剩幾條有效方程式？' + no(2) + '判斷三平面的位置關係，並說出公共部分是直線還是平面。';
    var nEff = kind === 2 ? 1 : 2;
    a = jo([no(1) + T(nEff) + ' 條', no(2) + lab + '；' + ansTex]);
    p = { kind: kind, A: A, b: b, ans: { nEff: nEff, lab: lab } };
    return { q: q, a: a, h: h, p: p };
  };

  /* ── §3 Δ=0 且無解：⑤⑥⑦⑧ ── */
  L1.planeNoSol = function (r) {
    var kind = r.int(0, 3), A, b, lab, h, e1, d1, e2, d2, k;
    e1 = [1, r.nz(-3, 3), r.nz(-3, 3)]; d1 = r.int(-6, 6);
    if (kind === 0) {
      var k1 = r.nz(-2, 2), k2 = r.nz(-2, 2), t = 0;
      do { e2 = [r.nz(-3, 3), r.nz(-3, 3), r.nz(-3, 3)]; t++; } while (t < 30 && e2[0] * e1[1] - e2[1] * e1[0] === 0 && e2[0] * e1[2] - e2[2] * e1[0] === 0);
      d2 = r.int(-6, 6);
      A = [e1, e2, [k1 * e1[0] + k2 * e2[0], k1 * e1[1] + k2 * e2[1], k1 * e1[2] + k2 * e2[2]]];
      b = [d1, d2, k1 * d1 + k2 * d2 + r.nz(1, 4)];
      lab = '三稜柱型（三平面兩兩相交，三條交線互相平行）';
      h = '三個法向量兩兩不平行；但第三式的係數恰是第一式的 ' + T(k1) + ' 倍加第二式的 ' + T(k2) + ' 倍，常數項卻對不上（' + T(prod([k1, d1]) + '+' + prod([k2, d2]) + '=' + (k1 * d1 + k2 * d2)) + '，題目給的是 ' + T(b[2]) + '）⟹ 無解。';
    } else if (kind === 1) {
      k = r.pick([2, 3, -2]);
      var t2 = 0;
      do { e2 = [r.nz(-3, 3), r.nz(-3, 3), r.nz(-3, 3)]; t2++; } while (t2 < 30 && e2[0] * e1[1] - e2[1] * e1[0] === 0 && e2[0] * e1[2] - e2[2] * e1[0] === 0);
      A = [e1, e1.map(function (v) { return k * v; }), e2];
      b = [d1, k * d1 + r.nz(1, 4), r.int(-6, 6)];
      lab = '兩平面平行且相異，第三平面與它們相交';
      h = '前兩式的法向量成比例（第二式是第一式的 ' + T(k) + ' 倍）但常數項 ' + T(b[1]) + ' 不等於 ' + T(prod([k, d1]) + '=' + (k * d1)) + ' ⟹ 平行不重合；第三個法向量與它們不平行。';
    } else if (kind === 2) {
      var k2b = r.pick([2, 3, -2]), k3 = r.pick([-3, 4, 5]), o2, o3, tt = 0;
      /* ⑦ 三個平面兩兩相異 ⟹ 三個常數項除以各自的比例之後必須兩兩不同 */
      do { o2 = r.nz(1, 4); o3 = r.nz(5, 9); tt++; }
      while (tt < 40 && (o2 * k3 === o3 * k2b));
      A = [e1, e1.map(function (v) { return k2b * v; }), e1.map(function (v) { return k3 * v; })];
      b = [d1, k2b * d1 + o2, k3 * d1 + o3];
      lab = '三平面互相平行且兩兩相異';
      h = '三式的法向量全部平行（比例 ' + T('1:' + k2b + ':' + k3) + '）；常數項 ' + T(d1) + '、' + T(b[1]) + '、' + T(b[2]) + ' 與這個比例都對不上 ⟹ 沒有任兩個重合。';
    } else {
      var kA = r.pick([2, 3, -2]), kB = r.pick([-3, 4, 5]);
      A = [e1, e1.map(function (v) { return kA * v; }), e1.map(function (v) { return kB * v; })];
      b = [d1, kA * d1, kB * d1 + r.nz(2, 6)];
      lab = '兩平面重合，第三平面與它們平行且相異';
      h = '三式的法向量全部平行；前兩式連常數項也成同一比例（' + T(b[1]) + ' 恰是 ' + T(prod([kA, d1])) + '）⟹ 前兩個平面重合，第三式的常數項卻對不上。';
    }
    var q = '設三個平面 ' + T('E_1:' + lin(A[0], VS3) + '=' + b[0]) + '、' + T('E_2:' + lin(A[1], VS3) + '=' + b[1]) + '、' + T('E_3:' + lin(A[2], VS3) + '=' + b[2]) + '。' + no(1) + '說明這個方程組無解。' + no(2) + '看三個法向量，判斷三平面的位置關係。';
    var a = jo([no(1) + '化成階梯形後會出現 ' + T('0=k') + '（' + T('k\\ne0') + '）的矛盾 ⟹ ' + SOLW.none, no(2) + lab]);
    return { q: q, a: a, h: h, p: { kind: kind, A: A, b: b, ans: { lab: lab } } };
  };

  /* ── §4 矩陣加減與係數積 ── */
  L1.matAddK = function (r) {
    var A = rm2(r, -6, 6), B = rm2(r, -6, 6), s = r.nz(-3, 3), u = r.nz(-3, 3), w = r.pick([2, 3, -2]);
    var P = mAdd(MF(A), mK(s, MF(B))), Q = mSub(mK(u, MF(A)), MF(B));
    var X = mK(F(1, w), mSub(MF(B), MF(A)));
    var q = '設 ' + T('A=' + bm(A)) + '、' + T('B=' + bm(B)) + '。' + no(1) + '求 ' + T('A' + (s > 0 ? '+' : '-') + (Math.abs(s) === 1 ? '' : Math.abs(s)) + 'B') + '。' + no(2) + '求 ' + T((u === 1 ? '' : (u === -1 ? '-' : u)) + 'A-B') + '。' + no(3) + '求滿足 ' + T(w + 'X+A=B') + ' 的矩陣 ' + T('X') + '。';
    var a = jo([no(1) + T(bm(P)), no(2) + T(bm(Q)), no(3) + T('X=' + bm(X))]);
    var h = '加減與係數積都是「逐格處理」：' + no(1) + ' ' + (function () { var nm = [['左上角', 0, 0], ['右上角', 0, 1], ['左下角', 1, 0], ['右下角', 1, 1]], c = nm.filter(function (z) { return s * B[z[1]][z[2]] !== 0; })[0] || nm[0]; return c[0] + '是 ' + T(A[c[1]][c[2]] + (s * B[c[1]][c[2]] === 0 ? '+0' : pm(s * B[c[1]][c[2]])) + '=' + (A[c[1]][c[2]] + s * B[c[1]][c[2]])); })() + '；' + no(3) + ' 先移項得 ' + T(w + 'X=B-A=' + bm(mSub(MF(B), MF(A)))) + '，再每格除以 ' + T(w) + '。';
    return { q: q, a: a, h: h, p: { A: A, B: B, s: s, u: u, w: w, ans: { P: P.map(function (x) { return x.map(fp); }), Q: Q.map(function (x) { return x.map(fp); }), X: X.map(function (x) { return x.map(fp); }) } } };
  };

  /* ── §4 矩陣相乘（含可乘條件） ── */
  L1.matMul = function (r) {
    var kind = r.int(0, 1), A, B, q, a, h, p;
    if (kind === 0) {
      A = rm2(r, -5, 5); B = rm2(r, -5, 5);
      var AB = mMul(MF(A), MF(B)), BA = mMul(MF(B), MF(A));
      var same = mSame(AB, BA);
      q = '設 ' + T('A=' + bm(A)) + '、' + T('B=' + bm(B)) + '。' + no(1) + '求 ' + T('AB') + '。' + no(2) + '求 ' + T('BA') + '。' + no(3) + '判斷 ' + T('AB') + ' 與 ' + T('BA') + ' 是否相等。';
      a = jo([no(1) + T('AB=' + bm(AB)), no(2) + T('BA=' + bm(BA)), no(3) + (same ? '相等' : '不相等')]);
      h = T('AB') + ' 的第 ' + T(1) + ' 列第 ' + T(1) + ' 行 ＝ ' + T('A') + ' 的第一列配 ' + T('B') + ' 的第一行：' + T(prod([A[0][0], B[0][0]]) + '+' + prod([A[0][1], B[1][0]]) + '=' + Fr.tex(AB[0][0])) + '；' + T('BA') + ' 要換成 ' + T('B') + ' 的列配 ' + T('A') + ' 的行，位置不一樣。';
      p = { kind: 0, A: A, B: B, ans: { AB: AB.map(function (x) { return x.map(fp); }), BA: BA.map(function (x) { return x.map(fp); }), same: same } };
    } else {
      A = rm2(r, -4, 4);
      var C = [[r.int(-4, 4), r.int(-4, 4), r.int(-4, 4)], [r.int(-4, 4), r.int(-4, 4), r.int(-4, 4)]];
      var AC = mMul(MF(A), MF(C));
      q = '設 ' + T('A=' + bm(A)) + ' 是 ' + T('2\\times2') + ' 方陣、' + T('C=' + bm(C)) + ' 是 ' + T('2\\times3') + ' 矩陣。' + no(1) + '求 ' + T('AC') + '，並說出它是幾乘幾的矩陣。' + no(2) + T('CA') + ' 有沒有意義？為什麼？';
      a = jo([no(1) + T('AC=' + bm(AC)) + '，是 ' + T('2\\times3') + ' 矩陣', no(2) + '沒有意義（' + T('C') + ' 的行數 ' + T(3) + ' 不等於 ' + T('A') + ' 的列數 ' + T(2) + '）']);
      h = '「中間對上才能乘，剩下的就是答案的大小」：' + T('2\\times2') + ' 乘 ' + T('2\\times3') + ' ⟹ 中間的 ' + T(2) + ' 對上了 ⟹ 結果 ' + T('2\\times3') + '。' + T('AC') + ' 的左上角是 ' + T(prod([A[0][0], C[0][0]]) + '+' + prod([A[0][1], C[1][0]]) + '=' + Fr.tex(AC[0][0])) + '。';
      p = { kind: 1, A: A, C: C, ans: { AC: AC.map(function (x) { return x.map(fp); }) } };
    }
    return { q: q, a: a, h: h, p: p };
  };

  /* ── §4 乘法的三個陷阱 ── */
  var TRAP = [
    { s: '(A+B)^2=A^2+2AB+B^2', t: 0 },
    { s: '(A+B)(A-B)=A^2-B^2', t: 0 },
    { s: 'AB=BA', t: 0 },
    { s: '\\det(A+B)=\\det A+\\det B', t: 0 },
    { s: '\\det(2A)=2\\det A', t: 0 },
    { s: '\\det(AB)=\\det A\\cdot\\det B', t: 1 },
    { s: '(AB)C=A(BC)', t: 1 },
    { s: 'A(B+C)=AB+AC', t: 1 },
    { s: '\\det(-A)=\\det A', t: 1 },
    { s: 'A(B-C)=AB-AC', t: 1 }
  ];
  var TRAPW = [
    { s: '若 ' + T('AB=O') + '，則 ' + T('A=O') + ' 或 ' + T('B=O'), t: 0 },
    { s: '若 ' + T('A^2=O') + '，則 ' + T('A=O'), t: 0 },
    { s: '若 ' + T('A^2=I') + '，則 ' + T('A=I') + ' 或 ' + T('A=-I'), t: 0 },
    { s: '若 ' + T('AB=AC') + ' 且 ' + T('A\\ne O') + '，則 ' + T('B=C'), t: 0 },
    { s: '若 ' + T('A') + '、' + T('B') + ' 都可逆，則 ' + T('(AB)^{-1}=A^{-1}B^{-1}'), t: 0 },
    { s: '若 ' + T('\\det A\\ne0') + ' 且 ' + T('AB=AC') + '，則 ' + T('B=C'), t: 1 },
    { s: '若 ' + T('AB=O') + ' 且 ' + T('\\det A\\ne0') + '，則 ' + T('B=O'), t: 1 },
    { s: '若 ' + T('AB=I') + '，則 ' + T('\\det B=\\dfrac{1}{\\det A}'), t: 1 },
    { s: '若 ' + T('A') + '、' + T('B') + ' 都可逆，則 ' + T('(AB)^{-1}=B^{-1}A^{-1}'), t: 1 },
    { s: '若 ' + T('A') + ' 可逆，則 ' + T('\\det(A^{-1})=\\dfrac{1}{\\det A}'), t: 1 }
  ];
  L1.mulTrap = function (r) {
    var pool = TRAP.map(function (o) { return { s: T(o.s), t: o.t }; }).concat(TRAPW);
    var pick = r.shuffle(pool).slice(0, 4);
    var tries = 0;
    while (tries < 20 && (pick.filter(function (o) { return o.t; }).length === 0 || pick.filter(function (o) { return !o.t; }).length === 0)) { pick = r.shuffle(pool).slice(0, 4); tries++; }
    var k = r.nz(-3, 3), m2 = r.nz(-3, 3), nn = r.nz(-4, 4);
    var mA = [[1, k], [0, 1]], mB = [[1, 0], [m2, 1]], mN = [[0, nn], [0, 0]];
    var AB = mMul(MF(mA), MF(mB)), BA = mMul(MF(mB), MF(mA));
    var q = '設 ' + T('A') + '、' + T('B') + '、' + T('C') + ' 都是二階方陣，' + T('I') + ' 是二階單位方陣、' + T('O') + ' 是二階零方陣。判斷下列各敘述是否「恆成立」：' +
      pick.map(function (o, i) { return no(i + 1) + o.s; }).join('　');
    var a = jo(pick.map(function (o, i) { return no(i + 1) + (o.t ? '恆成立' : '不恆成立'); }));
    var bad = [], good = [];
    pick.forEach(function (o, i) { (o.t ? good : bad).push(i + 1); });
    var h = '本題第 ' + bad.map(function (i) { return T(i); }).join('、') + ' 小題要舉得出反例，第 ' + good.map(function (i) { return T(i); }).join('、') + ' 小題才是恆成立的。三組萬用反例：' +
      T('A=' + bm(mA)) + ' 與 ' + T('B=' + bm(mB)) + ' ⟹ ' + T('AB=' + bm(AB)) + ' 而 ' + T('BA=' + bm(BA)) + '（不可交換）；' +
      T('N=' + bm(mN) + '\\ne O') + ' 但 ' + T('N^2=O') + '；' + T('\\det(2A)=2^2\\det A=' + (4 * Fr.num(dt2(MF(mA)))) + '') + '，不是 ' + T('2\\det A=' + (2 * Fr.num(dt2(MF(mA))))) + '。';
    return { q: q, a: a, h: h, p: { ss: pick.map(function (o) { return o.s; }), tt: pick.map(function (o) { return o.t; }), k: k, ans: { tt: pick.map(function (o) { return o.t; }) } } };
  };

  /* ── §4 二階反方陣 ── */
  L1.inv2 = function (r) {
    var A, d, t = 0;
    do { A = rm2(r, -6, 6); d = A[0][0] * A[1][1] - A[0][1] * A[1][0]; t++; } while ((d === 0 || Math.abs(d) > 12) && t < 300);
    var Iv = iv2(MF(A));
    var q = '設 ' + T('A=' + bm(A)) + '。' + no(1) + '求 ' + T('\\det A') + '。' + no(2) + '求 ' + T('A^{-1}') + '。' + no(3) + '驗算 ' + T('AA^{-1}=I') + '。';
    var a = jo([no(1) + T('\\det A=' + d), no(2) + T('A^{-1}=' + bm(Iv)), no(3) + T('AA^{-1}=' + bm(ID2) + '=I')]);
    var h = T('\\det A=' + prod([A[0][0], A[1][1]]) + '-' + prod([A[0][1], A[1][0]]) + '=' + d) + '，不為 ' + T(0) + ' ⟹ 反方陣存在。接著「主對角線 ' + T(A[0][0]) + ' 與 ' + T(A[1][1]) + ' 交換、副對角線 ' + T(A[0][1]) + ' 與 ' + T(A[1][0]) + ' 各加負號、整體除以 ' + T(d) + '」。';
    return { q: q, a: a, h: h, p: { A: A, ans: { d: d, Iv: Iv.map(function (x) { return x.map(fp); }) } } };
  };

  /* ── §4 反方陣的存在性與參數 ── */
  L1.invExist = function (r) {
    var kind = r.int(0, 1), q, a, h, p;
    if (kind === 0) {
      /* det = 一次式：a k + b = 0 */
      var b2 = r.nz(-5, 5), c2 = r.nz(-5, 5), dd = r.nz(-5, 5);
      var A = [['k', b2], [c2, dd]];
      /* det = k*dd - b2*c2 */
      var kv = F(b2 * c2, dd);
      q = '設 ' + T('k') + ' 為實數，' + T('A=' + bm(A)) + '。' + no(1) + '用 ' + T('k') + ' 表示 ' + T('\\det A') + '。' + no(2) + '求使 ' + T('A') + ' 不可逆的 ' + T('k') + ' 值。';
      a = jo([no(1) + T('\\det A=' + (dd === 1 ? 'k' : (dd === -1 ? '-k' : dd + 'k')) + pm(-b2 * c2)), no(2) + T('k=' + Fr.tex(kv, true))]);
      h = T('\\det A=' + prod(['k', dd]) + '-' + prod([b2, c2]) + '=' + (dd === 1 ? 'k' : (dd === -1 ? '-k' : dd + 'k')) + pm(-b2 * c2)) + '；不可逆就是 ' + T('\\det A=0') + '，解這條一次方程式。';
      p = { kind: 0, A: [[null, b2], [c2, dd]], ans: { k: fp(kv) } };
    } else {
      /* det = (k-r1)(k-r2) 型：A = [[k, b],[c, k+m]]，det = k^2+mk-bv*cv
         兩根都取非零整數 ⟹ bc = r1*r2 ≠ 0 ⟹ 一定找得到整數的 bv、cv（bv 取 bc 的因數） */
      var r1 = r.nz(-5, 5), r2 = r.nz(-5, 5), t = 0;
      while (r2 === r1 && t < 12) { r2 = r.nz(-5, 5); t++; }
      if (r2 === r1) r2 = -r1;
      var m = -(r1 + r2), bc = r1 * r2, divs = [], dd;
      for (dd = 1; dd <= Math.abs(bc); dd++) if (bc % dd === 0) { divs.push(dd); divs.push(-dd); }
      var bv = r.pick(divs), cv2 = -bc / bv;
      var A2 = [['k', bv], [cv2, m === 0 ? 'k' : 'k' + pm(m)]];
      var roots = [r1, r2].sort(function (a1, b1) { return a1 - b1; });
      q = '設 ' + T('k') + ' 為實數，' + T('A=' + bm(A2)) + '。求使 ' + T('A') + ' 不可逆的所有 ' + T('k') + ' 值。';
      a = T('k=' + roots[0]) + ' 或 ' + T('k=' + roots[1]);
      h = T('\\det A=k' + (m === 0 ? '^2' : '(k' + pm(m) + ')') + '-' + prod([bv, cv2]) + (m === 0 && prod([bv, cv2]) === String(bv * cv2) ? '' : '=k^2' + tm(m, 'k') + pm(-bv * cv2))) + '；不可逆 ⟺ ' + T('\\det A=0') + '，把它因式分解成兩個一次式。';
      p = { kind: 1, bv: bv, cv: cv2, m: m, ans: { roots: roots } };
    }
    return { q: q, a: a, h: h, p: p };
  };

  /* ── §4 用反方陣解聯立 ── */
  L1.invSolve = function (r) {
    var A, d, t = 0;
    do { A = rm2(r, -5, 5); d = A[0][0] * A[1][1] - A[0][1] * A[1][0]; t++; } while ((Math.abs(d) !== 1 && Math.abs(d) !== 2) && t < 400);
    if (d === 0) { A = [[2, 3], [1, 2]]; d = 1; }
    var Iv = iv2(MF(A));
    var x1 = [r.nz(-4, 4), r.nz(-4, 4)], x2 = [r.nz(-4, 4), r.nz(-4, 4)];
    var b1 = [A[0][0] * x1[0] + A[0][1] * x1[1], A[1][0] * x1[0] + A[1][1] * x1[1]];
    var b2 = [A[0][0] * x2[0] + A[0][1] * x2[1], A[1][0] * x2[0] + A[1][1] * x2[1]];
    var q = '設 ' + T('A=' + bm(A)) + '。' + no(1) + '求 ' + T('A^{-1}') + '。' + no(2) + '用反方陣解 ' + T(csys(A, b1, VS2)) + '。' + no(3) + '用同一個 ' + T('A^{-1}') + ' 解 ' + T(csys(A, b2, VS2)) + '。';
    var a = jo([no(1) + T('A^{-1}=' + bm(Iv)), no(2) + T('(x,y)=(' + x1.join(',') + ')'), no(3) + T('(x,y)=(' + x2.join(',') + ')')]);
    var h = T('\\det A=' + prod([A[0][0], A[1][1]]) + '-' + prod([A[0][1], A[1][0]]) + '=' + d) + ' ⟹ ' + T('A^{-1}=' + bm(Iv)) + '；接著 ' + T('\\vec{x}=A^{-1}\\vec{b}') + '，' + no(2) + ' 只要算一次 ' + T('A^{-1}' + cv(b1)) + '。' + no(3) + ' 換一個 ' + T('\\vec{b}') + ' 而已，' + T('A^{-1}') + ' 不必重算。';
    return { q: q, a: a, h: h, p: { A: A, b1: b1, b2: b2, ans: { Iv: Iv.map(function (x) { return x.map(fp); }), x1: x1, x2: x2 } } };
  };

  /* ── §4 方陣的乘冪 ── */
  L1.matPow = function (r) {
    var kind = r.int(0, 2), q, a, h, p, A, n;
    if (kind === 0) {
      var d1 = r.pick([-2, -1, 2, 3, -3]), d2 = r.pick([-2, -1, 2, 3, -3]);
      n = r.int(4, 7);
      A = [[d1, 0], [0, d2]];
      var P = [[Math.pow(d1, n), 0], [0, Math.pow(d2, n)]];
      q = '設 ' + T('A=' + bm(A)) + '。' + no(1) + '求 ' + T('A^2') + '。' + no(2) + '求 ' + T('A^{' + n + '}') + '。';
      a = jo([no(1) + T(bm([[d1 * d1, 0], [0, d2 * d2]])), no(2) + T(bm(P))]);
      h = '對角方陣的乘冪最省事：每個對角元素各自次方。' + T(par(d1) + sup(n) + '=' + Math.pow(d1, n)) + '、' + T(par(d2) + sup(n) + '=' + Math.pow(d2, n)) + '。';
      p = { kind: 0, A: A, n: n, ans: { P: P } };
    } else if (kind === 1) {
      var k = r.nz(-4, 4), low = r.int(0, 1);
      n = r.int(5, 12);
      A = low ? [[1, 0], [k, 1]] : [[1, k], [0, 1]];
      var N = low ? [[0, 0], [k, 0]] : [[0, k], [0, 0]];
      var Pn = low ? [[1, 0], ['nk'.replace('nk', (k === 1 ? 'n' : (k === -1 ? '-n' : k + 'n'))), 1]] : [[1, (k === 1 ? 'n' : (k === -1 ? '-n' : k + 'n'))], [0, 1]];
      var Pv = low ? [[1, 0], [k * n, 1]] : [[1, k * n], [0, 1]];
      q = '設 ' + T('A=' + bm(A)) + '。' + no(1) + '求 ' + T('A^2') + ' 與 ' + T('A^3') + '。' + no(2) + '求 ' + T('A^n') + ' 的通式（' + T('n') + ' 為正整數）。' + no(3) + '求 ' + T('A^{' + n + '}') + '。';
      a = jo([no(1) + T('A^2=' + bm(low ? [[1, 0], [2 * k, 1]] : [[1, 2 * k], [0, 1]])) + '，' + T('A^3=' + bm(low ? [[1, 0], [3 * k, 1]] : [[1, 3 * k], [0, 1]])), no(2) + T('A^n=' + bm(Pn)), no(3) + T(bm(Pv))]);
      h = '把 ' + T('A') + ' 拆成 ' + T('I+N') + '，其中 ' + T('N=' + bm(N)) + ' 滿足 ' + T('N^2=O') + ' ⟹ ' + T('A^n=I+nN') + '，只有那一格會跟著 ' + T('n') + ' 長大（每乘一次就多 ' + T(k) + '）。';
      p = { kind: 1, A: A, n: n, k: k, low: low, ans: { Pv: Pv } };
    } else {
      var deg = r.pick([90, 180, 270, 120, 60]);
      var per = deg === 180 ? 2 : (deg === 90 || deg === 270 ? 4 : (deg === 120 ? 3 : 6));
      A = deg === 90 ? [[0, -1], [1, 0]] : (deg === 270 ? [[0, 1], [-1, 0]] : (deg === 180 ? [[-1, 0], [0, -1]] : null));
      if (A === null) A = MF([[0, 0], [0, 0]]);
      if (deg === 120) A = [[-1, -1], [1, 0]];
      if (deg === 60) A = [[1, -1], [1, 0]];
      n = r.int(2000, 2100);
      var rem = n % per, Pv2 = mPw(MF(A), rem === 0 ? per : rem);
      q = '設 ' + T('A=' + bm(A)) + '。' + no(1) + '求 ' + T('A^2') + '、' + T('A^3') + '。' + no(2) + '求使 ' + T('A^m=I') + ' 的最小正整數 ' + T('m') + '。' + no(3) + '求 ' + T('A^{' + n + '}') + '。';
      a = jo([no(1) + T('A^2=' + bm(mPw(MF(A), 2))) + '，' + T('A^3=' + bm(mPw(MF(A), 3))), no(2) + T('m=' + per), no(3) + T(bm(Pv2))]);
      h = '一路乘下去會發現 ' + T('A^{' + per + '}=I') + '（週期是 ' + T(per) + '）⟹ 只要看 ' + T(n + '\\div' + per) + ' 的餘數：' + T(n + '=' + per + par(Math.floor(n / per)) + pm(rem)) + ' ⟹ ' + T('A^{' + n + '}=' + (rem === 0 ? 'I' : rem === 1 ? 'A' : 'A^{' + rem + '}')) + '（餘數 ' + T(0) + ' 時就是 ' + T('I') + '）。';
      p = { kind: 2, A: A, n: n, per: per, ans: { Pv: Pv2.map(function (x) { return x.map(fp); }) } };
    }
    return { q: q, a: a, h: h, p: p };
  };

  /* ── §4 行列式的性質 ── */
  L1.detProp = function (r) {
    var da = r.nz(-6, 6), db = r.nz(-6, 6), k = r.pick([2, 3, -2, -3, 4]), n = r.int(2, 4);
    var qs = [
      { t: '\\det(AB)', v: F(da * db) },
      { t: '\\det(' + k + 'A)', v: F(k * k * da) },
      { t: '\\det(A^{-1})', v: F(1, da) },
      { t: '\\det(A^{' + n + '})', v: F(Math.pow(da, n)) },
      { t: '\\det(A^2B^{-1})', v: F(da * da, db) },
      { t: '\\det(-B)', v: F(db) },
      { t: '\\det(' + k + 'B^{-1})', v: F(k * k, db) },
      { t: '\\det(AB^{2})', v: F(da * db * db) }
    ];
    var pick = r.shuffle(qs).slice(0, 4);
    var q = '設 ' + T('A') + '、' + T('B') + ' 都是二階可逆方陣，且 ' + T('\\det A=' + da) + '、' + T('\\det B=' + db) + '。求下列各值：' + pick.map(function (o, i) { return no(i + 1) + T(o.t); }).join('　');
    var a = jo(pick.map(function (o, i) { return no(i + 1) + T(o.t + '=' + Fr.tex(o.v, true)); }));
    var h = '三條性質輪流用：' + T('\\det(AB)=\\det A\\cdot\\det B=' + prod([da, db]) + '=' + (da * db)) + '、' + T('\\det(' + k + 'A)=' + k + '^2\\det A=' + prod([k * k, da]) + '=' + (k * k * da)) + '（二階要乘 ' + T(k + '^2') + '，不是 ' + T(k) + '）、' + T('\\det(A^{-1})=\\dfrac{1}{\\det A}') + '。';
    return { q: q, a: a, h: h, p: { da: da, db: db, k: k, n: n, ts: pick.map(function (o) { return o.t; }), ans: { vs: pick.map(function (o) { return fp(o.v); }) } } };
  };

  /* ── §5 線性變換的像與原像 ── */
  L1.linTrans = function (r) {
    var A, d, t = 0;
    do { A = rm2(r, -5, 5); d = A[0][0] * A[1][1] - A[0][1] * A[1][0]; t++; } while ((d === 0 || Math.abs(d) > 15) && t < 300);
    var P = [r.nz(-4, 4), r.nz(-4, 4)], Q = [r.nz(-4, 4), r.nz(-4, 4)];
    var im = mVec(MF(A), VF(P));
    var tg = mVec(MF(A), VF(Q));
    var q = '設線性變換 ' + T('T') + ' 的矩陣為 ' + T('A=' + bm(A)) + '。' + no(1) + '求點 ' + T('P(' + P.join(',') + ')') + ' 的像。' + no(2) + '求哪一個點的像是 ' + T('(' + tg.map(EE).join(',') + ')') + '。' + no(3) + '求 ' + T('(1,0)') + ' 與 ' + T('(0,1)') + ' 的像。';
    var a = jo([no(1) + T('(' + im.map(EE).join(',') + ')'), no(2) + T('(' + Q.join(',') + ')'), no(3) + T('(1,0)\\to(' + A[0][0] + ',' + A[1][0] + ')') + '，' + T('(0,1)\\to(' + A[0][1] + ',' + A[1][1] + ')')]);
    var h = '求像就是把矩陣乘上去：' + T('A' + cv(P) + '=' + cv([prod([A[0][0], P[0]]) + '+' + prod([A[0][1], P[1]]), prod([A[1][0], P[0]]) + '+' + prod([A[1][1], P[1]])]) + '=' + cv(im)) + '；求原像則反過來乘 ' + T('A^{-1}') + '（' + T('\\det A=' + d) + '）。' + no(3) + ' 的像就是 ' + T('A') + ' 的兩個行向量。';
    return { q: q, a: a, h: h, p: { A: A, P: P, Q: Q, ans: { im: im.map(fp), pre: Q } } };
  };

  /* ── §5 五種基本變換的矩陣 ── */
  L1.basicTrans = function (r) {
    var items = [], used = {}, i, o, t = 0;
    while (items.length < 3 && t < 40) {
      t++;
      switch (r.int(0, 4)) {
        case 0: var a1 = r.nz(-4, 4), b1 = r.nz(-4, 4);
          o = { t: '以原點為中心，沿 ' + T('x') + ' 方向伸縮 ' + T(a1) + ' 倍、沿 ' + T('y') + ' 方向伸縮 ' + T(b1) + ' 倍', M: [[a1, 0], [0, b1]], g: 'scale',
                hh: '伸縮把 ' + T('(1,0)') + ' 送到 ' + T('(' + a1 + ',0)') + '、把 ' + T('(0,1)') + ' 送到 ' + T('(0,' + b1 + ')') + '，這兩個像就是兩個行向量' }; break;
        case 1: var k1 = r.nz(-4, 4), ax = r.int(0, 1);
          o = ax ? { t: '沿 ' + T('x') + ' 軸方向推移 ' + T('y') + ' 坐標的 ' + T(k1) + ' 倍', M: [[1, k1], [0, 1]], g: 'shear',
                     hh: '推移是 ' + T('(x,y)\\to(x' + tm(k1, 'y') + ',\\,y)') + '，只有右上角是 ' + T(k1) }
            : { t: '沿 ' + T('y') + ' 軸方向推移 ' + T('x') + ' 坐標的 ' + T(k1) + ' 倍', M: [[1, 0], [k1, 1]], g: 'shear',
                hh: '推移是 ' + T('(x,y)\\to(x,\\,' + (k1 === 1 ? '' : (k1 === -1 ? '-' : k1)) + 'x+y)') + '，只有左下角是 ' + T(k1) }; break;
        case 2: var dg = r.pick([30, 45, 60, 90, 120, 135, 150, 180]), cw = (dg === 180 ? 0 : r.int(0, 1)), th = cw ? -dg : dg;
          o = { t: '以原點為中心' + (cw ? '順' : '逆') + '時針旋轉 ' + T(degT(dg)), M: rotM(th), g: 'rot',
                hh: '旋轉代 ' + T('\\theta=' + degT(md360(th))) + ' ⟹ ' + T('\\cos\\theta=' + ANG[md360(th)].c) + '、' + T('\\sin\\theta=' + ANG[md360(th)].s) + '，填進 ' + T('\\begin{bmatrix}\\cos\\theta&-\\sin\\theta\\\\ \\sin\\theta&\\cos\\theta\\end{bmatrix}') }; break;
        case 3: var ag = r.pick([0, 30, 45, 60, 90, 120, 135, 150]);
          o = { t: AXIS[ag].t, M: refM(ag), g: 'ref',
                hh: '鏡射填的是 ' + T('2\\theta') + ' 不是 ' + T('\\theta') + '：本題軸的傾角是 ' + T(degT(ag)) + ' ⟹ ' + T('2\\theta=' + degT(2 * ag)) + ' ⟹ ' + T('\\cos2\\theta=' + ANG[md360(2 * ag)].c) + '、' + T('\\sin2\\theta=' + ANG[md360(2 * ag)].s) }; break;
        default: var pa = r.pick(['x', 'y']);
          o = { t: '投影到 ' + T(pa) + ' 軸', M: pa === 'x' ? [[1, 0], [0, 0]] : [[0, 0], [0, 1]], g: 'proj',
                hh: '投影到 ' + T(pa) + ' 軸就是 ' + T(pa === 'x' ? '(x,y)\\to(x,\\,0)' : '(x,y)\\to(0,\\,y)') + '，' + T('\\det=0') + '（被壓扁了，沒有反變換）' }; break;
      }
      if (used[o.g]) continue;
      used[o.g] = 1; items.push(o);
    }
    var q = '寫出下列各變換的矩陣：' + items.map(function (x, ii) { return no(ii + 1) + x.t; }).join('　');
    var a = jo(items.map(function (x, ii) { return no(ii + 1) + T(bm(x.M)); }));
    var h = '全部照「' + T('(1,0)') + ' 與 ' + T('(0,1)') + ' 跑到哪」擺成兩個行向量。' + items.map(function (x, ii) { return no(ii + 1) + x.hh; }).join('；') + '。';
    return { q: q, a: a, h: h, p: { gs: items.map(function (x) { return x.g; }), ans: { Ms: items.map(function (x) { return x.M; }) } } };
  };

  /* ── §5 合成 ＝ 相乘（由右往左） ── */
  L1.compose = function (r) {
    var s1 = basicInt(r), s2 = basicInt(r), t = 0;
    while (t < 20 && mSame(MF(s1.M), MF(s2.M))) { s2 = basicInt(r); t++; }
    var M = mMul(MF(s2.M), MF(s1.M));
    var P = [r.nz(-4, 4), r.nz(-4, 4)], im = mVec(M, VF(P));
    var step1 = mVec(MF(s1.M), VF(P));
    var d = Fr.num(dt2(M));
    var q = '將坐標平面上的點依序做下列兩個動作：' + no('a') + s1.t + '；' + no('b') + '再' + s2.t + '。' + no(1) + '求整體變換的矩陣 ' + T('M') + '。' + no(2) + '求 ' + T('A(' + P.join(',') + ')') + ' 最後落在哪裡。' + no(3) + '求 ' + T('\\det M') + '。';
    var a = jo([no(1) + T('M=' + bm(M)), no(2) + T('(' + im.map(EE).join(',') + ')'), no(3) + T('\\det M=' + d)]);
    var h = '最後做的寫最左邊：' + T('M=BA') + '，其中 ' + T('A=' + bm(s1.M)) + '（動作 ' + T('a') + '）、' + T('B=' + bm(s2.M)) + '（動作 ' + T('b') + '）。逐步追也可以驗算：' + T('(' + P.join(',') + ')\\to(' + step1.map(EE).join(',') + ')') + ' 之後再做第二個動作。';
    return { q: q, a: a, h: h, p: { M1: s1.M, M2: s2.M, P: P, ans: { M: M.map(function (x) { return x.map(fp); }), im: im.map(fp), d: d } } };
  };

  /* ── §5 行列式＝面積伸縮率 ── */
  L1.detArea = function (r) {
    var A, d, t = 0;
    do { A = rm2(r, -5, 5); d = A[0][0] * A[1][1] - A[0][1] * A[1][0]; t++; } while ((d === 0 || Math.abs(d) > 20) && t < 300);
    var S = r.int(2, 12);
    var q = '設線性變換 ' + T('T') + ' 的矩陣為 ' + T('A=' + bm(A)) + '。' + no(1) + '求 ' + T('\\det A') + '。' + no(2) + '求以原點、' + T('(1,0)') + '、' + T('(1,1)') + '、' + T('(0,1)') + ' 為頂點的單位正方形經 ' + T('T') + ' 之後的面積。' + no(3) + '若某區域的面積是 ' + T(S) + '，求它的像的面積。';
    var a = jo([no(1) + T('\\det A=' + d), no(2) + T(Math.abs(d)), no(3) + T(Math.abs(d) * S)]);
    var h = T('\\det A=' + prod([A[0][0], A[1][1]]) + '-' + prod([A[0][1], A[1][0]]) + '=' + d) + '；面積伸縮率是 ' + T('|\\det A|=' + Math.abs(d)) + '（負號只代表左右顛倒），所以第 ' + T(3) + ' 小題是 ' + T(prod([Math.abs(d), S])) + '。';
    return { q: q, a: a, h: h, p: { A: A, S: S, ans: { d: d, area: Math.abs(d), area2: Math.abs(d) * S } } };
  };

  /* ── §5 二階轉移方陣 ── */
  var TRC = [
    { n: ['A', 'B'], w: '超商', u: '市占率', v: '顧客', mo: '每個月', nx: '下個月', p2: '兩個月後' },
    { n: ['甲', '乙'], w: '手機品牌', u: '占有率', v: '使用者', mo: '每年', nx: '一年後', p2: '兩年後' },
    { n: ['市區', '郊區'], w: '住宅區', u: '居住比例', v: '住戶', mo: '每年', nx: '一年後', p2: '兩年後' },
    { n: ['捷運', '公車'], w: '通勤方式', u: '使用比例', v: '通勤族', mo: '每個月', nx: '下個月', p2: '兩個月後' },
    { n: ['甲店', '乙店'], w: '手搖飲', u: '市占率', v: '客人', mo: '每週', nx: '下週', p2: '兩週後' }
  ];
  L1.transMat = function (r) {
    var c = r.pick(TRC);
    var p1 = r.int(5, 9), q1 = r.int(1, 5);      /* 十分之幾 */
    var a0 = r.int(2, 8);
    var M = [[F(p1, 10), F(q1, 10)], [F(10 - p1, 10), F(10 - q1, 10)]];
    var X0 = [F(a0, 10), F(10 - a0, 10)];
    var X1 = mVec(M, X0), X2 = mVec(M, X1);
    var Md = [[dc(M[0][0]), dc(M[0][1])], [dc(M[1][0]), dc(M[1][1])]];
    var q = '某地的' + c.w + '只有 ' + c.n[0] + '、' + c.n[1] + ' 兩種。' + c.mo + '，原本選 ' + c.n[0] + ' 的' + c.v + '有 ' + T(p1 * 10 + '\\%') + ' 留下、' + T((10 - p1) * 10 + '\\%') + ' 改選 ' + c.n[1] + '；原本選 ' + c.n[1] + ' 的有 ' + T(q1 * 10 + '\\%') + ' 改選 ' + c.n[0] + '、' + T((10 - q1) * 10 + '\\%') + ' 留下。目前 ' + c.n[0] + ' 的' + c.u + '是 ' + T(a0 * 10 + '\\%') + '。' +
      no(1) + '寫出轉移方陣 ' + T('M') + '（並檢查每一行的和是 ' + T(1) + '）。' + no(2) + '求' + c.nx + '的' + c.u + ' ' + T('X_1') + '。' + no(3) + '求' + c.p2 + '的 ' + T('X_2') + '。';
    var a = jo([no(1) + T('M=' + bm(Md)), no(2) + T('X_1=' + cv([dc(X1[0]), dc(X1[1])])), no(3) + T('X_2=' + cv([dc(X2[0]), dc(X2[1])]))]);
    var h = '「直的（行）是從哪裡來」：第一行 ' + T(dc(M[0][0]) + '+' + dc(M[1][0]) + '=1') + ' ✓、第二行 ' + T(dc(M[0][1]) + '+' + dc(M[1][1]) + '=1') + ' ✓。接著 ' + T('X_1=MX_0') + '，第一個分量是 ' + T(prod([dc(M[0][0]), dc(X0[0])]) + '+' + prod([dc(M[0][1]), dc(X0[1])])) + '；' + T('X_2=MX_1') + ' 再乘一次。';
    return { q: q, a: a, h: h, p: { p1: p1, q1: q1, a0: a0, ans: { M: M.map(function (x) { return x.map(fp); }), X1: X1.map(fp), X2: X2.map(fp) } } };
  };

  /* ── §5 穩定狀態 ── */
  L1.steady = function (r) {
    var c = r.pick(TRC);
    /* 以二十分之幾為單位（0.05 的倍數），題幹的小數仍然是有限小數 */
    var p1 = r.int(9, 19), q1 = r.int(1, 11), t = 0;
    while (p1 === q1 && t < 12) { q1 = r.int(1, 11); t++; }
    var M = [[F(p1, 20), F(q1, 20)], [F(20 - p1, 20), F(20 - q1, 20)]];
    var Md = [[dc(M[0][0]), dc(M[0][1])], [dc(M[1][0]), dc(M[1][1])]];
    var den = q1 + (20 - p1);
    var xs = F(q1, den), ys = F(20 - p1, den);
    var q = '設 ' + T('M=' + bm(Md)) + ' 是某' + c.w + '的' + c.u + '轉移方陣（' + c.mo + '轉移一次）。' + no(1) + '解 ' + T('MX=X') + ' 配上 ' + T('x+y=1') + '，求穩定狀態 ' + T('X=' + cv(VS2)) + '。' + no(2) + '驗算 ' + T('MX=X') + '。';
    var a = jo([no(1) + T('(x,y)=\\left(' + Fr.tex(xs, true) + ',\\,' + Fr.tex(ys, true) + '\\right)'), no(2) + T('MX=' + cv([Fr.tex(xs, true), Fr.tex(ys, true)]) + '=X') + ' ✓']);
    var h = '由第一列 ' + T(dc(M[0][0]) + 'x+' + dc(M[0][1]) + 'y=x') + ' 移項得 ' + T(dc(M[0][1]) + 'y=' + dc(F(20 - p1, 20)) + 'x') + ' ⟹ ' + T(ratT(q1, 20 - p1)) + '；第二列化簡也是同一條（這就是 ' + T('\\det(M-I)=0') + '），所以一定要再配 ' + T('x+y=1') + ' 才釘得住。';
    return { q: q, a: a, h: h, p: { p1: p1, q1: q1, den: 20, ans: { xs: fp(xs), ys: fp(ys) } } };
  };

  /* ═══════════════════════ L2 ═══════════════════════ */
  var L2 = {};

  /* 造一個「解集合恰是一條直線」的三元系統：X = X0 + t d */
  function lineSys(r) {
    var d, X0, cand, pick = [], i, j, g, t = 0;
    /* 方向向量至少要有兩個非零分量，否則會有一個字母完全不出現在方程組裡 */
    do { d = [r.int(-3, 3), r.int(-3, 3), r.int(-3, 3)]; t++; } while (t < 60 && d.filter(function (v) { return v !== 0; }).length < 2);
    if (d.filter(function (v) { return v !== 0; }).length < 2) d = [1, 1, 1];
    g = gcd(gcd(d[0], d[1]), d[2]) || 1; d = d.map(function (v) { return v / g; });
    X0 = [r.int(-4, 4), r.int(-4, 4), r.int(-4, 4)];
    cand = [[d[1], -d[0], 0], [0, d[2], -d[1]], [d[2], 0, -d[0]]].filter(function (v) { return !(v[0] === 0 && v[1] === 0 && v[2] === 0); });
    cand = r.shuffle(cand);
    pick.push(cand[0]);
    for (i = 1; i < cand.length; i++) {
      var u = pick[0], v2 = cand[i];
      var cr = [u[1] * v2[2] - u[2] * v2[1], u[2] * v2[0] - u[0] * v2[2], u[0] * v2[1] - u[1] * v2[0]];
      if (!(cr[0] === 0 && cr[1] === 0 && cr[2] === 0)) { pick.push(v2); break; }
    }
    var s1 = r.pick([1, 1, -1, 2]), s2 = r.pick([1, 1, -1, 2]);
    var r1 = pick[0].map(function (v) { return s1 * v; }), r2 = pick[1].map(function (v) { return s2 * v; });
    var b1 = r1[0] * X0[0] + r1[1] * X0[1] + r1[2] * X0[2];
    var b2 = r2[0] * X0[0] + r2[1] * X0[1] + r2[2] * X0[2];
    var k1 = r.nz(-2, 2), k2 = r.nz(-2, 2);
    var r3 = [k1 * r1[0] + k2 * r2[0], k1 * r1[1] + k2 * r2[1], k1 * r1[2] + k2 * r2[2]];
    var b3 = k1 * b1 + k2 * b2;
    return { A: [r1, r2, r3], b: [b1, b2, b3], X0: X0, d: d, k1: k1, k2: k2 };
  }

  /* ── §4 矩陣乘法綜合（AB、BA、(A+B)^2） ── */
  L2.mulCombo = function (r) {
    var A = rm2(r, -5, 5), B = rm2(r, -5, 5);
    var AB = mMul(MF(A), MF(B)), BA = mMul(MF(B), MF(A));
    var S = mAdd(MF(A), MF(B)), S2 = mMul(S, S);
    var W = mAdd(mAdd(mMul(MF(A), MF(A)), mK(2, AB)), mMul(MF(B), MF(B)));
    var same = mSame(S2, W);
    var dAB = Fr.num(dt2(AB));
    var q = '設 ' + T('A=' + bm(A)) + '、' + T('B=' + bm(B)) + '。' + no(1) + '求 ' + T('AB') + ' 與 ' + T('BA') + '。' + no(2) + '求 ' + T('(A+B)^2') + '。' + no(3) + '求 ' + T('A^2+2AB+B^2') + '，並與 ' + no(2) + ' 比較。' + no(4) + '求 ' + T('\\det(AB)') + '。';
    var a = jo([no(1) + T('AB=' + bm(AB)) + '，' + T('BA=' + bm(BA)),
      no(2) + T('(A+B)^2=' + bm(S2)), no(3) + T('A^2+2AB+B^2=' + bm(W)) + '，兩者' + (same ? '相等' : '不相等'), no(4) + T('\\det(AB)=' + dAB)]);
    var h = T('(A+B)^2=A^2+AB+BA+B^2') + '，只有在 ' + T('AB=BA') + ' 時才會變回 ' + T('A^2+2AB+B^2') + '。本題 ' + T('AB=' + bm(AB)) + ' 而 ' + T('BA=' + bm(BA)) + '，' + (same ? '這一組剛好可交換' : '兩者不同 ⟹ 展開式不能合併') + '；另外 ' + T('\\det(AB)=\\det A\\cdot\\det B=' + prod([Fr.num(dt2(MF(A))), Fr.num(dt2(MF(B)))]) + '=' + dAB) + '。';
    return { q: q, a: a, h: h, p: { A: A, B: B, ans: { AB: AB.map(function (x) { return x.map(fp); }), BA: BA.map(function (x) { return x.map(fp); }), S2: S2.map(function (x) { return x.map(fp); }), same: same, dAB: dAB } } };
  };

  /* ── §4 行列式的進階計算 ── */
  L2.detAdv = function (r) {
    var A = rm2nz(r, -5, 5), B = rm2nz(r, -5, 5), k = r.pick([2, 3, -2, -3]), n = r.int(3, 5);
    var da = Fr.num(dt2(MF(A))), db = Fr.num(dt2(MF(B)));
    var vs = [F(da * db), F(k * k * da), F(Math.pow(da, n)), F(da * da, db)];
    var q = '設 ' + T('A=' + bm(A)) + '、' + T('B=' + bm(B)) + '。' + no(1) + '求 ' + T('\\det A') + ' 與 ' + T('\\det B') + '。' + no(2) + '求 ' + T('\\det(AB)') + '。' + no(3) + '求 ' + T('\\det(' + k + 'A)') + '。' + no(4) + '求 ' + T('\\det(A^{' + n + '})') + '。' + no(5) + '求 ' + T('\\det(A^2B^{-1})') + '。';
    var a = jo([no(1) + T('\\det A=' + da) + '，' + T('\\det B=' + db), no(2) + T(vs[0].n), no(3) + T(vs[1].n), no(4) + T(vs[2].n), no(5) + T(Fr.tex(vs[3], true))]);
    var h = T('\\det A=' + prod([A[0][0], A[1][1]]) + '-' + prod([A[0][1], A[1][0]]) + '=' + da) + '、' + T('\\det B=' + db) + '；接著全部用乘法性質：' + T('\\det(' + k + 'A)=' + (k < 0 ? '(' + k + ')' : k) + '^2\\det A') + '（二階提兩次 ' + T(k) + '，不是 ' + T('\\det(' + k + 'A)=' + k + '\\det A') + '）、' + T('\\det(A^{' + n + '})=(\\det A)^{' + n + '}') + '、' + T('\\det(B^{-1})=' + Fr.tex(F(1, db))) + '。';
    return { q: q, a: a, h: h, p: { A: A, B: B, k: k, n: n, ans: { da: da, db: db, vs: vs.map(fp) } } };
  };

  /* ── §4 反方陣與矩陣方程：AX=B 與 XA=B ── */
  L2.invAdv = function (r) {
    var A, d, t = 0;
    do { A = rm2(r, -5, 5); d = A[0][0] * A[1][1] - A[0][1] * A[1][0]; t++; } while ((d === 0 || Math.abs(d) > 4) && t < 400);
    if (d === 0) { A = [[1, 2], [2, 3]]; d = -1; }
    var B = rm2(r, -5, 5);
    var Iv = iv2(MF(A)), X1 = mMul(Iv, MF(B)), X2 = mMul(MF(B), Iv);
    var same = mSame(X1, X2);
    var q = '設 ' + T('A=' + bm(A)) + '、' + T('B=' + bm(B)) + '。' + no(1) + '求 ' + T('A^{-1}') + '。' + no(2) + '解矩陣方程式 ' + T('AX=B') + '。' + no(3) + '解矩陣方程式 ' + T('XA=B') + '。' + no(4) + '比較 ' + no(2) + ' 與 ' + no(3) + ' 的答案是否相同。';
    var a = jo([no(1) + T('A^{-1}=' + bm(Iv)), no(2) + T('X=' + bm(X1)), no(3) + T('X=' + bm(X2)), no(4) + (same ? '相同' : '不相同')]);
    var h = T('\\det A=' + prod([A[0][0], A[1][1]]) + '-' + prod([A[0][1], A[1][0]]) + '=' + d) + ' ⟹ ' + T('A^{-1}=' + bm(Iv)) + '。' + T('AX=B') + ' 要在「左邊」乘 ' + T('A^{-1}') + ' ⟹ ' + T('X=A^{-1}B') + '；' + T('XA=B') + ' 要在「右邊」乘 ⟹ ' + T('X=BA^{-1}') + '。乘法不可交換，兩邊不能亂換。';
    return { q: q, a: a, h: h, p: { A: A, B: B, ans: { Iv: Iv.map(function (x) { return x.map(fp); }), X1: X1.map(function (x) { return x.map(fp); }), X2: X2.map(function (x) { return x.map(fp); }), same: same } } };
  };

  /* ── §4 矩陣方程與反方陣的性質 ── */
  L2.matEqAdv = function (r) {
    var A, B, dA, dB, t = 0;
    do { A = rm2(r, -4, 4); dA = A[0][0] * A[1][1] - A[0][1] * A[1][0]; t++; } while ((Math.abs(dA) !== 1 && Math.abs(dA) !== 2) && t < 400);
    if (dA === 0) { A = [[1, 1], [0, 1]]; dA = 1; }
    t = 0;
    do { B = rm2(r, -4, 4); dB = B[0][0] * B[1][1] - B[0][1] * B[1][0]; t++; } while ((Math.abs(dB) !== 1 && Math.abs(dB) !== 2) && t < 400);
    if (dB === 0) { B = [[2, 0], [0, 1]]; dB = 2; }
    var AB = mMul(MF(A), MF(B));
    var P = iv2(AB), Q = mMul(iv2(MF(B)), iv2(MF(A))), R2 = mMul(iv2(MF(A)), iv2(MF(B)));
    var same = mSame(R2, P);
    var q = '設 ' + T('A=' + bm(A)) + '、' + T('B=' + bm(B)) + '（兩者都可逆）。' + no(1) + '求 ' + T('AB') + ' 與 ' + T('(AB)^{-1}') + '。' + no(2) + '求 ' + T('B^{-1}A^{-1}') + '，並與 ' + no(1) + ' 比較。' + no(3) + '求 ' + T('A^{-1}B^{-1}') + '。' + no(4) + '求 ' + T('\\det\\left((AB)^{-1}\\right)') + '。';
    var a = jo([no(1) + T('AB=' + bm(AB)) + '，' + T('(AB)^{-1}=' + bm(P)), no(2) + T('B^{-1}A^{-1}=' + bm(Q)) + '，與 ' + T('(AB)^{-1}') + ' 相同', no(3) + T('A^{-1}B^{-1}=' + bm(R2)) + '，與 ' + T('(AB)^{-1}') + (same ? ' 相同' : ' 不同'), no(4) + T(Fr.tex(F(1, dA * dB), true))]);
    var h = '「先穿襪子再穿鞋，要先脫鞋再脫襪子」：' + T('(AB)^{-1}=B^{-1}A^{-1}') + '，順序一定要反過來。先算 ' + T('AB=' + bm(AB)) + '（左上角是 ' + T(prod([A[0][0], B[0][0]]) + '+' + prod([A[0][1], B[1][0]]) + '=' + Fr.tex(AB[0][0])) + '），再對它套二階反方陣公式。本題 ' + T('\\det A=' + dA) + '、' + T('\\det B=' + dB) + ' ⟹ ' + T('\\det(AB)=' + prod([dA, dB]) + '=' + (dA * dB)) + '，而 ' + T('\\det\\left((AB)^{-1}\\right)=\\dfrac{1}{\\det(AB)}') + '。';
    return { q: q, a: a, h: h, p: { A: A, B: B, ans: { AB: AB.map(function (x) { return x.map(fp); }), P: P.map(function (x) { return x.map(fp); }), Q: Q.map(function (x) { return x.map(fp); }), R: R2.map(function (x) { return x.map(fp); }), same: same, dv: fp(F(1, dA * dB)) } } };
  };

  /* ── §4 方陣的乘冪：找週期與拆成 kI+N ── */
  L2.powPeriod = function (r) {
    var kind = r.int(0, 1), A, q, a, h, p, n;
    if (kind === 0) {
      var opt = r.int(0, 4);
      if (opt === 0) { A = [[0, -1], [1, 0]]; }
      else if (opt === 1) { A = [[0, 1], [-1, 0]]; }
      else if (opt === 2) { A = [[0, -1], [1, -1]]; }
      else if (opt === 3) { A = [[1, -1], [1, 0]]; }
      else { A = [[-1, 0], [0, -1]]; }
      var per = 1, MM = MF(A), t;
      for (per = 1; per <= 12; per++) { if (mSame(mPw(MF(A), per), ID2)) break; }
      n = r.int(2000, 2120);
      var rem = n % per, Pv = mPw(MF(A), rem === 0 ? per : rem);
      q = '設 ' + T('A=' + bm(A)) + '。' + no(1) + '依序求 ' + T('A^2') + '、' + T('A^3') + '。' + no(2) + '求使 ' + T('A^m=I') + ' 的最小正整數 ' + T('m') + '。' + no(3) + '求 ' + T('A^{' + n + '}') + '。' + no(4) + '求 ' + T('A^{-1}') + '。';
      a = jo([no(1) + T('A^2=' + bm(mPw(MF(A), 2))) + '，' + T('A^3=' + bm(mPw(MF(A), 3))), no(2) + T('m=' + per), no(3) + T(bm(Pv)), no(4) + T('A^{-1}=' + bm(iv2(MF(A))))]);
      h = '一路乘會看到 ' + T('A^{' + per + '}=I') + '，週期是 ' + T(per) + ' ⟹ ' + T(n + '=' + per + par(Math.floor(n / per)) + pm(rem)) + '（餘數 ' + T(rem) + '）⟹ ' + T('A^{' + n + '}') + ' 等於 ' + T('A') + ' 的第 ' + T(rem === 0 ? per : rem) + ' 次方；' + no(4) + ' 也可以用 ' + T('A^{-1}=' + (per === 2 ? 'A' : 'A^{' + (per - 1) + '}')) + ' 反推。';
      p = { kind: 0, A: A, n: n, ans: { per: per, Pv: Pv.map(function (x) { return x.map(fp); }) } };
    } else {
      var kk = r.pick([2, 3, -2]), bb = r.nz(-4, 4), low = r.int(0, 1);
      A = low ? [[kk, 0], [bb, kk]] : [[kk, bb], [0, kk]];
      n = r.int(4, 6);
      var Pn = mPw(MF(A), n);
      q = '設 ' + T('A=' + bm(A)) + '。' + no(1) + '把 ' + T('A') + ' 寫成 ' + T('kI+N') + ' 的形式（' + T('N^2=O') + '），並寫出 ' + T('k') + ' 與 ' + T('N') + '。' + no(2) + '求 ' + T('A^2') + ' 與 ' + T('A^3') + '。' + no(3) + '求 ' + T('A^{' + n + '}') + '。';
      var N = low ? [[0, 0], [bb, 0]] : [[0, bb], [0, 0]];
      a = jo([no(1) + T('k=' + kk) + '，' + T('N=' + bm(N)), no(2) + T('A^2=' + bm(mPw(MF(A), 2))) + '，' + T('A^3=' + bm(mPw(MF(A), 3))), no(3) + T(bm(Pn))]);
      h = T('A=' + kk + 'I+N') + '，其中 ' + T('N=' + bm(N)) + ' 滿足 ' + T('N^2=O') + '；因為 ' + T('I') + ' 與任何矩陣可交換，可用二項式展開且第三項以後全消失 ⟹ ' + T('A^n=' + kk + '^nI+n' + par(kk) + '^{n-1}N') + '。對角線是 ' + T(par(kk) + sup(n) + '=' + Math.pow(kk, n)) + '。';
      p = { kind: 1, A: A, n: n, ans: { k: kk, N: N, Pn: Pn.map(function (x) { return x.map(fp); }) } };
    }
    return { q: q, a: a, h: h, p: p };
  };

  /* ── §2 含參數的三元聯立：解的個數 ── */
  L2.solve3Param = function (r) {
    var pp = r.nz(-3, 3), qq = r.nz(-3, 3), u = r.int(-5, 5);
    var s = r.nz(-3, 3), v = r.int(-5, 5), e = r.nz(-3, 3);
    var aa = r.int(1, 5), flip = r.int(0, 1);
    /* R2-2R1 = (0,1,s|v)；(R3-3R1)-e(0,1,s|v) = (0,0,k^2-a^2 | k -+ a) */
    var C3 = 3 * qq + e * s - aa * aa, K0 = 3 * u + e * v + (flip ? aa : -aa);
    var E2 = [2, 2 * pp + 1, 2 * qq + s], d2 = 2 * u + v;
    var zc = 'k^2' + (C3 === 0 ? '' : pm(C3));
    var E3s = lin([3, 3 * pp + e, 0], VS3).replace(/\+0z|-0z/, '') + (3 * pp + e === 0 && false ? '' : '') + '+\\left(' + zc + '\\right)z=k' + (K0 === 0 ? '' : pm(K0));
    var E1s = lin([1, pp, qq], VS3) + '=' + u;
    var E2s = lin(E2, VS3) + '=' + d2;
    var sys = '\\begin{cases}' + rws([E1s, E2s, E3s]) + '\\end{cases}';
    var kInf = flip ? -aa : aa, kNo = flip ? aa : -aa;
    var q = '設 ' + T('k') + ' 為實數，方程組 ' + T(sys) + '。' + no(1) + '求使方程組恰有一組解的 ' + T('k') + ' 值範圍。' + no(2) + '求使方程組有無限多組解的 ' + T('k') + '。' + no(3) + '求使方程組無解的 ' + T('k') + '。';
    var a = jo([no(1) + T('k\\ne' + aa) + ' 且 ' + T('k\\ne' + (-aa)), no(2) + T('k=' + kInf), no(3) + T('k=' + kNo)]);
    var h = '先做 ' + T('R_2-2R_1') + ' 得 ' + T(rowT([0, 1, s], v)) + '；再做 ' + T('R_3-3R_1') + ' 之後減去它的 ' + T(e) + ' 倍，第三列變成 ' + T('\\left(0,\\,0,\\,k^2-' + (aa * aa) + '\\mid k' + (flip ? '+' : '-') + aa + '\\right)') + '。接著看 ' + T('k^2-' + (aa * aa) + '=0') + ' 的兩個根，各自代回去看常數項是不是也是 ' + T(0) + '。';
    return { q: q, a: a, h: h, p: { pp: pp, qq: qq, u: u, s: s, v: v, e: e, aa: aa, flip: flip, ans: { aa: aa, kInf: kInf, kNo: kNo } } };
  };

  /* ── §2 從已知的階梯形反推參數 ── */
  L2.rowOpBack = function (r) {
    var b1 = r.nz(-3, 3), c1 = r.nz(-3, 3), d1 = r.int(-6, 6);
    var e2 = r.nz(-3, 3), f2 = r.int(-6, 6);
    var mu = r.nz(-3, 3), al = r.nz(-3, 3), be = r.nz(-3, 3);
    var R1 = [1, b1, c1], S2 = [0, 1, e2];
    var E2 = [mu, mu * b1 + 1, mu * c1 + e2], kv = mu * d1 + f2;
    var E3 = [al, al * b1 + be, al * c1 + be * e2], cv3 = al * d1 + be * f2;
    /* 未知數：E2 的常數項 k、E3 的 z 係數 m */
    var E1s = lin(R1, VS3) + '=' + d1;
    var E2s = lin(E2, VS3) + '=k';
    var E3s = lin([E3[0], E3[1], 0], VS3).replace(/([+-])0z$/, '') + '+mz=' + cv3;
    var sys = '\\begin{cases}' + rws([E1s, E2s, E3s]) + '\\end{cases}';
    var ech = agm([R1, S2, [0, 0, 0]], [d1, f2, 0]);
    /* 解：令 z=t ⟹ y=f2-e2 t、x=d1-b1 y-c1 t */
    var yco = F(-e2), ycn = F(f2);
    var xco = F(b1 * e2 - c1), xcn = F(d1 - b1 * f2);
    var q = '設 ' + T('k') + '、' + T('m') + ' 為實數，方程組 ' + T(sys) + ' 的增廣矩陣經一系列列運算後化為 ' + T(ech) + '。' + no(1) + '求 ' + T('k') + '。' + no(2) + '求 ' + T('m') + '。' + no(3) + '寫出所有的解。';
    var a = jo([no(1) + T('k=' + kv), no(2) + T('m=' + E3[2]), no(3) + T(paramTex([xco, yco, F(1)], [xcn, ycn, F(0)])) + '，' + T('t') + ' 為實數']);
    var mus = (mu < 0 ? '-' : '+') + (Math.abs(mu) === 1 ? '' : Math.abs(mu));
    var h = '化簡後的第二列 ' + T(rowT(S2, f2)) + ' 是由 ' + T(opS(2, mu, 1)) + ' 得到的 ⟹ 把它加回 ' + T(mu) + ' 倍的第一列就還原成原本的第二列：' + T(rowT(S2, f2) + mus + rowT(R1, d1) + '=' + rowT(E2, kv)) + '；第三列全零 ⟹ 原第三列是前兩列的線性組合，比對 ' + T('z') + ' 的係數就得到 ' + T('m') + '。';
    return { q: q, a: a, h: h, p: { R1: R1, S2: S2, d1: d1, f2: f2, mu: mu, al: al, be: be, ans: { k: kv, m: E3[2] } } };
  };

  /* ── §2 無限多組解的參數式 ── */
  L2.infSol = function (r) {
    var S = lineSys(r), A = S.A, b = S.b, X0 = S.X0, d = S.d;
    var chk = [X0[0] + d[0], X0[1] + d[1], X0[2] + d[2]];
    var q = '用列運算解方程組 ' + T(csys(A, b)) + '：' + no(1) + '判斷解的個數。' + no(2) + '把所有的解寫成參數式。' + no(3) + '取 ' + T('t=1') + ' 驗算你的答案。';
    var a = jo([no(1) + SOLW.inf, no(2) + T(paramTex(VF(d), VF(X0))) + '，' + T('t') + ' 為實數', no(3) + T('(x,y,z)=(' + chk.join(',') + ')') + '，代入三式都成立']);
    var h = '第三式 ' + T(lin(A[2], VS3) + '=' + b[2]) + ' 恰是第一式的 ' + T(S.k1) + ' 倍加第二式的 ' + T(S.k2) + ' 倍（連常數項也是）⟹ 化完會出現一整列 ' + T(0) + ' ⟹ 只剩 ' + T(2) + ' 條有效方程式、' + T('3-2=1') + ' 個自由度。把沒有當過領導元素的那個字母設成 ' + T('t') + '。';
    return { q: q, a: a, h: h, p: { A: A, b: b, ans: { X0: X0, d: d } } };
  };

  /* ── §2 三元一次聯立的應用（文字題） ── */
  var WORD = [
    { s: '某文具店', it: ['原子筆', '筆記本', '資料夾'], u: '元', who: ['甲', '乙', '丙'], vb: '買了', q1: '支', q2: '本', q3: '個', tail: '共花了' },
    { s: '某早餐店', it: ['飯糰', '豆漿', '蛋餅'], u: '元', who: ['小明', '小華', '小美'], vb: '點了', q1: '個', q2: '杯', q3: '份', tail: '共付了' },
    { s: '某五金行', it: ['螺絲', '墊片', '扳手'], u: '元', who: ['甲', '乙', '丙'], vb: '買了', q1: '包', q2: '包', q3: '支', tail: '共花了' },
    { s: '某水果攤', it: ['蘋果', '香蕉', '芭樂'], u: '元', who: ['甲', '乙', '丙'], vb: '買了', q1: '顆', q2: '串', q3: '顆', tail: '共花了' }
  ];
  L2.gaussWord = function (r) {
    var c = r.pick(WORD), A, x, b, D, t = 0;
    do {
      A = [[r.int(1, 4), r.int(1, 4), r.int(1, 4)], [r.int(1, 4), r.int(1, 4), r.int(1, 4)], [r.int(1, 4), r.int(1, 4), r.int(1, 4)]];
      D = Fr.num(dt3(MF(A))); t++;
    } while ((D === 0 || Math.abs(D) > 24) && t < 200);
    x = [r.int(3, 20) * 5, r.int(2, 16) * 5, r.int(4, 24) * 5];
    b = A.map(function (row) { return row[0] * x[0] + row[1] * x[1] + row[2] * x[2]; });
    var qs = [c.q1, c.q2, c.q3];
    var lines = A.map(function (row, i) {
      return c.who[i] + c.vb + row.map(function (v, j) { return T(v) + ' ' + qs[j] + c.it[j]; }).join('、') + '，' + c.tail + ' ' + T(b[i]) + ' ' + c.u;
    });
    var q = c.s + '的' + c.it.join('、') + '每' + qs[0] + '（' + qs[1] + '、' + qs[2] + '）的單價分別是 ' + T('x') + '、' + T('y') + '、' + T('z') + ' ' + c.u + '。' + lines.join('；') + '。' + no(1) + '列出三元一次聯立方程組。' + no(2) + '用消去法求三種商品的單價。';
    var a = jo([no(1) + T(csys(A, b)), no(2) + T('(x,y,z)=(' + x.join(',') + ')')]);
    var h = '把三句話各寫成一條方程式，例如第一句是 ' + T(lin(A[0], VS3) + '=' + b[0]) + '；接著用 ' + T('R_2') + '、' + T('R_3') + ' 減去 ' + T('R_1') + ' 的適當倍數先消掉 ' + T('x') + '（係數方陣的行列式是 ' + T(D) + '，不為 ' + T(0) + ' ⟹ 單價唯一）。';
    return { q: q, a: a, h: h, p: { A: A, b: b, ans: { x: x } } };
  };

  /* ── §3 含參數的三平面 ── */
  L2.planeParam = function (r) {
    var e1 = [1, r.nz(-3, 3), r.nz(-3, 3)], d1 = r.int(-6, 6), e2, d2 = r.int(-6, 6), t = 0;
    do { e2 = [r.nz(-3, 3), r.nz(-3, 3), r.nz(-3, 3)]; t++; } while (t < 40 && e2[0] * e1[1] - e2[1] * e1[0] === 0 && e2[0] * e1[2] - e2[2] * e1[0] === 0);
    var k1 = r.nz(-2, 2), k2 = r.nz(-2, 2);
    var e3 = [k1 * e1[0] + k2 * e2[0], k1 * e1[1] + k2 * e2[1], k1 * e1[2] + k2 * e2[2]];
    var kv = k1 * d1 + k2 * d2;
    var q = '設 ' + T('k') + ' 為實數，三個平面為 ' + T('E_1:' + lin(e1, VS3) + '=' + d1) + '、' + T('E_2:' + lin(e2, VS3) + '=' + d2) + '、' + T('E_3:' + lin(e3, VS3) + '=k') + '。' + no(1) + '求 ' + T('\\Delta') + '。' + no(2) + '求使三平面有公共點的 ' + T('k') + '。' + no(3) + '此時公共部分是點、直線還是平面？' + no(4) + T('k') + ' 取其他值時，三平面是哪一種位置關係？';
    var a = jo([no(1) + T('\\Delta=0'), no(2) + T('k=' + kv), no(3) + '一條直線', no(4) + '三稜柱型（三平面兩兩相交，三條交線互相平行，沒有公共點）']);
    var h = T('E_3') + ' 的係數恰是 ' + T('E_1') + ' 的 ' + T(k1) + ' 倍加 ' + T('E_2') + ' 的 ' + T(k2) + ' 倍 ⟹ ' + T('\\Delta=0') + '；常數項也要跟著對上才會有解：' + T(prod([k1, d1]) + '+' + prod([k2, d2])) + '。三個法向量兩兩不平行，所以 ' + T('k') + ' 只要不對上就是三稜柱型。';
    return { q: q, a: a, h: h, p: { e1: e1, e2: e2, d1: d1, d2: d2, k1: k1, k2: k2, ans: { k: kv } } };
  };

  /* ── §5 由兩個點的像求變換矩陣 ── */
  L2.linTransFind = function (r) {
    var A, d, t = 0;
    do { A = rm2(r, -5, 5); d = A[0][0] * A[1][1] - A[0][1] * A[1][0]; t++; } while ((d === 0 || Math.abs(d) > 18) && t < 300);
    var u = [r.nz(-3, 3), r.nz(-3, 3)], v = [r.nz(-3, 3), r.nz(-3, 3)], s = 0;
    while (u[0] * v[1] - u[1] * v[0] === 0 && s < 30) { v = [r.nz(-3, 3), r.nz(-3, 3)]; s++; }
    var Au = mVec(MF(A), VF(u)), Av = mVec(MF(A), VF(v));
    var P = [r.nz(-4, 4), r.nz(-4, 4)], AP = mVec(MF(A), VF(P));
    var q = '已知平面上的線性變換 ' + T('T') + ' 把 ' + T('(' + u.join(',') + ')') + ' 送到 ' + T('(' + Au.map(EE).join(',') + ')') + '、把 ' + T('(' + v.join(',') + ')') + ' 送到 ' + T('(' + Av.map(EE).join(',') + ')') + '。' + no(1) + '求 ' + T('T') + ' 的矩陣 ' + T('A') + '。' + no(2) + '求 ' + T('(' + P.join(',') + ')') + ' 的像。' + no(3) + '求單位正方形的像的面積。';
    var a = jo([no(1) + T('A=' + bm(A)), no(2) + T('(' + AP.map(EE).join(',') + ')'), no(3) + T(Math.abs(d))]);
    var h = '設 ' + T('A=\\begin{bmatrix}a&b\\\\ c&d\\end{bmatrix}') + '。由第一個條件得 ' + T(lin([u[0], u[1]], ['a', 'b']) + '=' + EE(Au[0])) + ' 與 ' + T(lin([u[0], u[1]], ['c', 'd']) + '=' + EE(Au[1])) + '；第二個條件再給兩條。' + T('a,\\,b') + ' 一組、' + T('c,\\,d') + ' 一組，各解一個二元一次聯立。';
    return { q: q, a: a, h: h, p: { u: u, v: v, Au: Au.map(fp), Av: Av.map(fp), P: P, ans: { A: A, AP: AP.map(fp), area: Math.abs(d) } } };
  };

  /* ── §5 旋轉矩陣與乘冪 ── */
  L2.rotAdv = function (r) {
    /* 180° 的順逆時針是同一件事，不要讓答案的敘述變成兩可 */
    var dg = r.pick([30, 45, 60, 90, 120, 135, 150, 180]), cw = (dg === 180 ? 0 : r.int(0, 1));
    var th = cw ? -dg : dg, A = rotM(th);
    var per = 360 / gcd(md360(th) === 0 ? 360 : md360(th), 360);
    var n = r.int(2000, 2120);
    var A2 = rotM(2 * th), An = rotM(n * th);
    var q = '設 ' + T('A=' + bm(A)) + '。' + no(1) + '判斷 ' + T('A') + ' 是哪一種線性變換（說出方向與角度）。' + no(2) + '求 ' + T('\\det A') + '。' + no(3) + '求 ' + T('A^2') + '。' + no(4) + '求使 ' + T('A^m=I') + ' 的最小正整數 ' + T('m') + '。' + no(5) + '求 ' + T('A^{' + n + '}') + '。';
    var a = jo([no(1) + '以原點為中心' + (cw ? '順' : '逆') + '時針旋轉 ' + T(degT(dg)), no(2) + T('\\det A=1'), no(3) + T('A^2=' + bm(A2)), no(4) + T('m=' + per), no(5) + T(bm(An))]);
    var h = '對照 ' + T('\\begin{bmatrix}\\cos\\theta&-\\sin\\theta\\\\ \\sin\\theta&\\cos\\theta\\end{bmatrix}') + '：本題 ' + T('\\cos\\theta=' + A[0][0]) + '、' + T('\\sin\\theta=' + A[1][0]) + ' ⟹ ' + T('\\theta=' + degT(md360(th))) + '。旋轉的合成就是角度相加：' + T('A^n=R(n\\theta)') + '，把 ' + T(n + '\\times' + md360(th) + '^\\circ') + ' 對 ' + T('360^\\circ') + ' 取餘數即可。';
    return { q: q, a: a, h: h, p: { dg: dg, cw: cw, n: n, ans: { per: per } } };
  };

  /* ── §5 鏡射矩陣與對稱軸 ── */
  var TRIP = [[3, 4, 5], [4, 3, 5], [5, 12, 13], [12, 5, 13], [8, 15, 17], [15, 8, 17], [7, 24, 25], [24, 7, 25], [20, 21, 29], [21, 20, 29],
    [9, 40, 41], [40, 9, 41], [28, 45, 53], [45, 28, 53], [11, 60, 61], [60, 11, 61], [33, 56, 65], [56, 33, 65], [16, 63, 65], [63, 16, 65],
    [48, 55, 73], [55, 48, 73], [13, 84, 85], [84, 13, 85], [36, 77, 85], [77, 36, 85], [39, 80, 89], [80, 39, 89], [65, 72, 97], [72, 65, 97]];
  L2.reflAdv = function (r) {
    var tp = r.pick(TRIP), sg = r.sign(), kind = r.int(0, 1);
    var cN = sg * tp[0], sN = tp[1], h2 = tp[2];
    var c = F(cN, h2), s = F(sN, h2);
    var A, q, a, h, p;
    if (kind === 0) {
      A = [[c, s], [s, Fr.neg(c)]];
      var tanv = Fr.div(s, Fr.add(F(1), c));
      var axis = 'y=' + (Fr.eq(tanv, F(1)) ? 'x' : (Fr.eq(tanv, F(-1)) ? '-x' : Fr.tex(tanv, true) + 'x'));
      q = '設 ' + T('A=' + bm(A)) + '。' + no(1) + '求 ' + T('\\det A') + '。' + no(2) + '求 ' + T('A^2') + '。' + no(3) + '判斷 ' + T('A') + ' 是哪一種線性變換。' + no(4) + '求它的對稱軸方程式。';
      a = jo([no(1) + T('\\det A=-1'), no(2) + T('A^2=' + bm(ID2)) + '（即 ' + T('I') + '）', no(3) + '鏡射', no(4) + T(axis)]);
      h = T('\\det A=' + prod([Fr.tex(c, true), Fr.tex(Fr.neg(c), true)]) + '-' + prod([Fr.tex(s, true), Fr.tex(s, true)]) + '=-1') + ' 且 ' + T('A^2=I') + ' ⟹ 是鏡射。軸的斜率用半角關係 ' + T('\\tan\\theta=\\dfrac{\\sin2\\theta}{1+\\cos2\\theta}=\\dfrac{' + Fr.tex(s, true) + '}{1' + (c.n < 0 ? '-' : '+') + Fr.tex(F(Math.abs(c.n), c.d), true) + '}') + '。';
      p = { kind: 0, c: fp(c), s: fp(s), ans: { d: -1, axis: axis, tan: fp(tanv) } };
    } else {
      A = [[c, Fr.neg(s)], [s, c]];
      var A2 = mMul(A, A);
      q = '設 ' + T('A=' + bm(A)) + '。' + no(1) + '求 ' + T('\\det A') + '。' + no(2) + '求 ' + T('A^2') + '。' + no(3) + '判斷 ' + T('A') + ' 是哪一種線性變換。' + no(4) + '求 ' + T('A^{-1}') + '。';
      a = jo([no(1) + T('\\det A=1'), no(2) + T('A^2=' + bm(A2)), no(3) + '旋轉', no(4) + T('A^{-1}=' + bm(iv2(A)))]);
      h = T('\\det A=' + prod([Fr.tex(c, true), Fr.tex(c, true)]) + '+' + prod([Fr.tex(s, true), Fr.tex(s, true)]) + '=1') + '，而且長得像 ' + T('\\begin{bmatrix}\\cos\\theta&-\\sin\\theta\\\\ \\sin\\theta&\\cos\\theta\\end{bmatrix}') + '（' + T('\\cos^2\\theta+\\sin^2\\theta=1') + ' ✓）⟹ 是旋轉；' + T('A^2') + ' 就是再轉一次（角度加倍）。';
      p = { kind: 1, c: fp(c), s: fp(s), ans: { d: 1, A2: A2.map(function (x) { return x.map(fp); }) } };
    }
    return { q: q, a: a, h: h, p: p };
  };

  /* ── §5 合成的順序 ── */
  L2.composeAdv = function (r) {
    var s1 = basicInt(r), s2 = basicInt(r), s3 = basicInt(r), t = 0;
    while (t < 20 && (mSame(MF(s1.M), MF(s2.M)) || mSame(MF(s2.M), MF(s3.M)) || mSame(MF(s1.M), MF(s3.M)))) { s3 = basicInt(r); s2 = basicInt(r); t++; }
    var M = mMul(mMul(MF(s3.M), MF(s2.M)), MF(s1.M));
    var M2 = mMul(mMul(MF(s1.M), MF(s2.M)), MF(s3.M));
    var P = [r.nz(-3, 3), r.nz(-3, 3)], im = mVec(M, VF(P));
    var d = Fr.num(dt2(M)), d2 = Fr.num(dt2(M2));
    var q = '將坐標平面上的點依序做下列三個動作：' + no('a') + s1.t + '；' + no('b') + '再' + s2.t + '；' + no('c') + '再' + s3.t + '。' + no(1) + '求整體變換的矩陣 ' + T('M') + '。' + no(2) + '求 ' + T('(' + P.join(',') + ')') + ' 最後落在哪裡。' + no(3) + '求 ' + T('\\det M') + '。' + no(4) + '若把順序倒過來做 ' + no('c') + no('b') + no('a') + '，求矩陣 ' + T("M'") + '，並比較 ' + T('\\det M') + ' 與 ' + T("\\det M'") + '。';
    var a = jo([no(1) + T('M=' + bm(M)), no(2) + T('(' + im.map(EE).join(',') + ')'), no(3) + T('\\det M=' + d), no(4) + T("M'=" + bm(M2)) + '，' + T("\\det M'=" + d2) + '（行列式相同，矩陣' + (mSame(M, M2) ? '也相同' : '不同') + '）']);
    var h = '最後做的寫最左邊：' + T('M=CBA') + '，其中 ' + T('A=' + bm(s1.M)) + '、' + T('B=' + bm(s2.M)) + '、' + T('C=' + bm(s3.M)) + '。先算 ' + T('BA=' + bm(mMul(MF(s2.M), MF(s1.M)))) + ' 再左乘 ' + T('C') + '。' + no(4) + ' 的 ' + T("M'=ABC") + '；行列式可以交換相乘，所以 ' + T('\\det') + ' 不受順序影響。';
    return { q: q, a: a, h: h, p: { M1: s1.M, M2: s2.M, M3: s3.M, P: P, ans: { M: M.map(function (x) { return x.map(fp); }), im: im.map(fp), d: d, Mr: M2.map(function (x) { return x.map(fp); }) } } };
  };

  /* ── §5 轉移方陣：兩期後與穩定狀態 ── */
  L2.transAdv = function (r) {
    var c = r.pick(TRC);
    var p1 = r.int(5, 9), q1 = r.int(1, 5), a0 = r.int(2, 8), t = 0;
    while (p1 === q1 && t < 10) { q1 = r.int(1, 5); t++; }
    var M = [[F(p1, 10), F(q1, 10)], [F(10 - p1, 10), F(10 - q1, 10)]];
    var Md = [[dc(M[0][0]), dc(M[0][1])], [dc(M[1][0]), dc(M[1][1])]];
    var M2 = mMul(M, M), X0 = [F(a0, 10), F(10 - a0, 10)];
    var X2 = mVec(M2, X0);
    var den = q1 + (10 - p1), xs = F(q1, den), ys = F(10 - p1, den);
    var q = '某' + c.w + '只有 ' + c.n[0] + '、' + c.n[1] + ' 兩種，' + c.mo + '的轉移方陣為 ' + T('M=' + bm(Md)) + '，目前 ' + T('X_0=' + cv([dc(X0[0]), dc(X0[1])])) + '。' +
      no(1) + '檢查 ' + T('M') + ' 的每一行的和。' + no(2) + '求 ' + T('M^2') + '。' + no(3) + '求' + c.p2 + '的 ' + T('X_2') + '（請用 ' + T('M^2X_0') + '）。' + no(4) + '求穩定狀態。';
    var a = jo([no(1) + '兩行的和都是 ' + T(1), no(2) + T('M^2=' + bm([[dc(M2[0][0]), dc(M2[0][1])], [dc(M2[1][0]), dc(M2[1][1])]])),
      no(3) + T('X_2=' + cv([dc(X2[0]), dc(X2[1])])), no(4) + T('(x,y)=\\left(' + Fr.tex(xs, true) + ',\\,' + Fr.tex(ys, true) + '\\right)')]);
    var X1a = mVec(M, X0);
    var h = T('M^2') + ' 的左上角是 ' + T(prod([dc(M[0][0]), dc(M[0][0])]) + '+' + prod([dc(M[0][1]), dc(M[1][0])]) + '=' + dc(M2[0][0])) + '；' + T('M^2') + ' 每一行的和仍然是 ' + T(1) + '（可以拿來驗算）。也可以走兩步：' + T('X_1=MX_0=' + cv([dc(X1a[0]), dc(X1a[1])])) + ' 再乘一次 ' + T('M') + '。穩定狀態解 ' + T('MX=X') + ' 配 ' + T('x+y=1') + '：由第一列得 ' + T(ratT(q1, 10 - p1)) + '。';
    return { q: q, a: a, h: h, p: { p1: p1, q1: q1, a0: a0, ans: { M2: M2.map(function (x) { return x.map(fp); }), X2: X2.map(fp), xs: fp(xs), ys: fp(ys) } } };
  };

  /* ── §5 轉移方陣的參數題 ── */
  L2.steadyParam = function (r) {
    var dn = r.pick([3, 4, 5, 6, 7, 8, 9, 10, 11, 12]), dnum = r.int(1, dn - 1), g = gcd(dnum, dn);
    dnum = dnum / g; dn = dn / g;
    if (dn === 1) { dn = 4; dnum = 1; }
    var kind = r.int(0, 1);
    var dF = F(dnum, dn), aF = Fr.sub(F(1), dF);        /* a = 1-d */
    var q, a, h, p, N, prodv;
    if (kind === 0) {
      /* 給右下角 d，求 a、b、c */
      N = [['a', 'b'], ['c', Fr.tex(dF, true)]];
      prodv = Fr.mul(Fr.mul(aF, aF), dF);
      q = '設 ' + T('N=' + bm(N)) + ' 是一個二階轉移方陣（每個元素非負、每一行的和都是 ' + T(1) + '），且 ' + T('N') + ' 不存在乘法反方陣。' + no(1) + '求 ' + T('a') + '、' + T('b') + '、' + T('c') + '。' + no(2) + '求 ' + T('abc') + '。' + no(3) + '求 ' + T('N') + ' 的穩定狀態。';
      a = jo([no(1) + T('a=' + Fr.tex(aF, true)) + '，' + T('b=' + Fr.tex(aF, true)) + '，' + T('c=' + Fr.tex(dF, true)), no(2) + T('abc=' + Fr.tex(prodv, true)),
        no(3) + T('(x,y)=\\left(' + Fr.tex(aF, true) + ',\\,' + Fr.tex(dF, true) + '\\right)')]);
      h = '兩個條件一起用：第二行的和是 ' + T(1) + ' ⟹ ' + T('b+' + Fr.tex(dF, true) + '=1') + '；第一行的和是 ' + T(1) + ' ⟹ ' + T('a+c=1') + '；不可逆 ⟹ ' + T('\\det N=' + prod(['a', Fr.tex(dF, true)]) + '-bc=0') + '。三條式子解三個未知數。';
      p = { kind: 0, d: fp(dF), ans: { a: fp(aF), b: fp(aF), c: fp(dF), prod: fp(prodv) } };
    } else {
      /* 給左上角 a，求 b、c、d */
      N = [[Fr.tex(aF, true), 'b'], ['c', 'd']];
      prodv = Fr.mul(Fr.mul(aF, dF), dF);
      q = '設 ' + T('N=' + bm(N)) + ' 是一個二階轉移方陣（每個元素非負、每一行的和都是 ' + T(1) + '），且 ' + T('N') + ' 不可逆。' + no(1) + '求 ' + T('b') + '、' + T('c') + '、' + T('d') + '。' + no(2) + '求 ' + T('bcd') + '。' + no(3) + '求 ' + T('N') + ' 的穩定狀態。';
      a = jo([no(1) + T('b=' + Fr.tex(aF, true)) + '，' + T('c=' + Fr.tex(dF, true)) + '，' + T('d=' + Fr.tex(dF, true)), no(2) + T('bcd=' + Fr.tex(prodv, true)),
        no(3) + T('(x,y)=\\left(' + Fr.tex(aF, true) + ',\\,' + Fr.tex(dF, true) + '\\right)')]);
      h = '第一行的和是 ' + T(1) + ' ⟹ ' + T(Fr.tex(aF, true) + '+c=1') + '；第二行的和是 ' + T(1) + ' ⟹ ' + T('b+d=1') + '；不可逆 ⟹ ' + T('\\det N=' + prod([Fr.tex(aF, true), 'd']) + '-bc=0') + '。把前兩條代進第三條就解得出來。';
      p = { kind: 1, a: fp(aF), ans: { b: fp(aF), c: fp(dF), d: fp(dF), prod: fp(prodv) } };
    }
    return { q: q, a: a, h: h, p: p };
  };

  /* ══════════════════════════════════════════════════════════ */
  /* ══════════════════════════════════════════════════════════
     L1 解題步驟（s：每步一段 HTML）與第一層提示（h1：只講「這是哪一型、第一步做什麼」，不帶數字）
     全部由 p（與 o.q、o.a）重算，所以與題目、答案一定一致；答案由頁面另行附在步驟後。
     用法：用 splice_all_11b4.py 插在 META（var META_L1 = [）之前，並把 wrapAll(L1) 換成 wrapAll(L1, L1_SOL, L1_H1)。
     自己加的小工具一律加前綴 sx；產生器的通用工具（F／Fr／T／prod／par／pm／tm／lin／csys／bm／cv／vmx／agm／
     mMul／mVec／dt2／dt3／iv2／mPw／rotM／refM／ANG／paramTex／ratT／dc／EE／MF／VF／no／jo／sup…）可直接用。
     課綱界線（HANDOUT_SPEC §4 約 450–463 列）：不出現「秩／rank」「線性獨立／相依」「轉置」
     「特徵值／特徵向量／對角化」「伴隨矩陣／餘因子」「馬可夫鏈」「基本列運算」「高斯消去」；
     確切算出反方陣僅限二階；A^n 用找規律／找週期／拆成 kI+N；穩定狀態用解 MX=X 配 x+y=1。
     ══════════════════════════════════════════════════════════ */
  function sxFin(o) { return '答案：' + o.a + '。'; }
  function sxF(t) { return F(t[0], t[1]); }                         /* p 裡的 [n,d] 還原成分數 */
  function sxNg(v) { return v === 0 ? '0' : String(-v); }           /* 變號（0 不要印成 -0） */
  function sxMul(a, b) { if (a === 1) return String(b); if (b === 1) return String(a); return prod([a, b]) + '=' + (a * b); }
  function sxQ2(n, d) {                                             /* n/d 的推導：已最簡就不再寫一次 */
    var v = F(n, d);
    if (d === 1 || d === -1) return String(v.n);                    /* 分母是 ±1 就不要寫成分數 */
    var raw = '\\dfrac{' + n + '}{' + d + '}';
    return (v.n === n && v.d === d) ? raw : raw + '=' + Fr.tex(v, true);
  }
  function sxDet2(A) { return prod([A[0][0], A[1][1]]) + '-' + prod([A[0][1], A[1][0]]); }
  function sxDv2(A) { return A[0][0] * A[1][1] - A[0][1] * A[1][0]; }
  /* 三階行列式沿第一列展開（正負號已經併進去） */
  function sxDet3(A) {
    var out = '', j, a, b, c, d, inner, co;
    for (j = 0; j < 3; j++) {
      co = A[0][j]; if (co === 0) continue;
      a = A[1][(j + 1) % 3]; b = A[2][(j + 2) % 3]; c = A[1][(j + 2) % 3]; d = A[2][(j + 1) % 3];
      inner = '(' + prod([a, b]) + '-' + prod([c, d]) + ')';
      out += (co < 0 ? '-' : (out === '' ? '' : '+')) + (Math.abs(co) === 1 ? '' : '(' + Math.abs(co) + ')') + inner;
    }
    return out === '' ? '0' : out;
  }
  /* 第 i 列配第 j 行：算式＋值 */
  function sxCellN(A, B, i, j) {
    var t = [], k, s = 0;
    for (k = 0; k < B.length; k++) { t.push(prod([A[i][k], B[k][j]])); s += A[i][k] * B[k][j]; }
    return t.join('+') + '=' + s;
  }
  /* r3 = k1 r1 + k2 r2 的係數（找不到回傳 null） */
  function sxCombo(r1, r2, r3) {
    var ps = [[0, 1], [0, 2], [1, 2]], i, u, d, k1, k2, j, ok;
    for (i = 0; i < 3; i++) {
      u = ps[i]; d = r1[u[0]] * r2[u[1]] - r1[u[1]] * r2[u[0]];
      if (d === 0) continue;
      k1 = (r3[u[0]] * r2[u[1]] - r3[u[1]] * r2[u[0]]) / d;
      k2 = (r1[u[0]] * r3[u[1]] - r1[u[1]] * r3[u[0]]) / d;
      ok = true;
      for (j = 0; j < 3; j++) if (k1 * r1[j] + k2 * r2[j] !== r3[j]) ok = false;
      if (ok) return [k1, k2];
    }
    return null;
  }
  /* 兩個三維係數列的第一個不為 0 的二階子式（用來說「不平行」） */
  function sxCross(u, v) {
    var ps = [[0, 1], [0, 2], [1, 2]], i, a, val;
    for (i = 0; i < 3; i++) {
      a = ps[i]; val = u[a[0]] * v[a[1]] - u[a[1]] * v[a[0]];
      if (val !== 0) return { v: val, t: prod([u[a[0]], v[a[1]]]) + '-' + prod([u[a[1]], v[a[0]]]) + '=' + val };
    }
    return null;
  }
  /* 逐格寫出「整列減 m 倍的第一列」（每一格各自包成一段 $…$，等號鏈才查得動） */
  function sxOpRow(row, c, m, r1, c1) {
    var t = [], i;
    for (i = 0; i < row.length; i++) t.push(T(row[i] + '-' + prod([m, r1[i]]) + '=' + (row[i] - m * r1[i])));
    t.push(T(c + '-' + prod([m, c1]) + '=' + (c - m * c1)));
    return t.join('、');
  }
  /* 係數方陣第一行化 0（sysUnique 造出來的 A[0][0] 一定是 1） */
  function sxRed(A, b) {
    var m2 = A[1][0] / A[0][0], m3 = A[2][0] / A[0][0];
    return { m2: m2, m3: m3,
      R2: [0, A[1][1] - m2 * A[0][1], A[1][2] - m2 * A[0][2]], c2: b[1] - m2 * b[0],
      R3: [0, A[2][1] - m3 * A[0][1], A[2][2] - m3 * A[0][2]], c3: b[2] - m3 * b[0] };
  }
  /* 再消一次 + 由下往上代回 */
  function sxBack(A, b) {
    var R = sxRed(A, b), U = [R.R2[1], R.R2[2]], uc = R.c2, V = [R.R3[1], R.R3[2]], vc = R.c3, sw = false, t;
    if (U[0] === 0) { t = U; U = V; V = t; t = uc; uc = vc; vc = t; sw = true; }
    var Dz = U[0] * V[1] - V[0] * U[1], Cz = U[0] * vc - V[0] * uc;
    var z = Cz / Dz, y = (uc - U[1] * z) / U[0], x = (b[0] - A[0][1] * y - A[0][2] * z) / A[0][0];
    return { R: R, U: U, uc: uc, V: V, vc: vc, sw: sw, Dz: Dz, Cz: Cz, x: x, y: y, z: z };
  }
  /* 消去法的完整敘述（兩段字串） */
  function sxElimText(A, b) {
    var S = sxBack(A, b), R = S.R, iU = S.sw ? 3 : 2, iV = S.sw ? 2 : 3;
    var s1 = '先用第一式把 ' + T('x') + ' 消掉。' + T(opT(2, R.m2, 1)) + '：' + sxOpRow(A[1], b[1], R.m2, A[0], b[0]) + ' ⟹ ' + T(rowT(R.R2, R.c2))
      + '；' + T(opT(3, R.m3, 1)) + ' ⟹ ' + T(rowT(R.R3, R.c3)) + '，只剩 ' + T('y,\\,z') + ' 兩個未知數。';
    var s2 = '再消一次 ' + T('y') + '：把第 ' + T(iU) + ' 列的 ' + T(S.U[0]) + ' 與第 ' + T(iV) + ' 列的 ' + T(S.V[0]) + ' 湊掉 ⟹ '
      + T('\\left[' + prod([S.U[0], S.V[1]]) + '-' + prod([S.V[0], S.U[1]]) + '\\right]z=' + prod([S.U[0], S.vc]) + '-' + prod([S.V[0], S.uc]))
      + '，即 ' + T(lin([S.Dz], ['z']) + '=' + S.Cz) + ' ⟹ ' + T('z=' + S.z) + '；代回 ' + T(lin(S.U, VS2.slice(0, 0).concat(['y', 'z'])) + '=' + S.uc)
      + ' 得 ' + T('y=' + S.y) + '，再代回第一式得 ' + T('x=' + S.x) + '。';
    return { s1: s1, s2: s2, x: S.x, y: S.y, z: S.z };
  }
  /* 乘冪的指數寫法（避免印出一次方） */
  function sxPw(m) { return m === 1 ? 'A' : 'A' + sup(m); }
  /* cn + co t */
  function sxPar(co, cn) {
    var s = '', cnum = Fr.num(co);
    if (cnum === 0) return EE(cn);
    if (Fr.num(cn) !== 0) s += EE(cn);
    if (s === '') s += (cnum === 1 ? 't' : (cnum === -1 ? '-t' : EE(co) + 't'));
    else s += (cnum > 0 ? '+' : '-') + (Math.abs(cnum) === 1 ? 't' : EE(F(Math.abs(co.n), co.d)) + 't');
    return s;
  }
  /* 乘法陷阱：一句話的理由 */
  function sxTrap(s, k) {
    var A0 = [[1, k], [0, 1]], B0 = [[1, 0], [1, 1]], N0 = [[0, 1], [0, 0]], J0 = [[1, 0], [0, -1]], C0 = [[1, 1], [0, 1]];
    var AB = mMul(MF(A0), MF(B0)), BA = mMul(MF(B0), MF(A0));
    var cex = T('A=' + bm(A0)) + '、' + T('B=' + bm(B0)) + ' ⟹ ' + T('AB=' + bm(A0) + bm(B0) + '=' + bm(AB)) + ' 而 ' + T('BA=' + bm(B0) + bm(A0) + '=' + bm(BA));
    if (s.indexOf('(A+B)^2') >= 0) return '展開是 ' + T('(A+B)^2=A^2+AB+BA+B^2') + '，中間兩項要 ' + T('AB=BA') + ' 才併得成 ' + T('2AB') + '；反例 ' + cex + ' ⟹ 不恆成立。';
    if (s.indexOf('(A+B)(A-B)') >= 0) return '展開是 ' + T('(A+B)(A-B)=A^2-AB+BA-B^2') + '，中間兩項不會互相消掉；反例 ' + cex + ' ⟹ 不恆成立。';
    if (s.indexOf('\\det(A+B)') >= 0) return '取 ' + T('A=B=I') + '：' + T('\\det(A+B)=\\det(2I)=4') + '，但 ' + T('\\det A+\\det B=2') + ' ⟹ 不恆成立。';
    if (s.indexOf('\\det(2A)') >= 0) return '二階時兩列都乘 ' + T(2) + ' ⟹ ' + T('\\det(2A)=2^2\\det A=4\\det A') + '，不是 ' + T('2\\det A') + ' ⟹ 不恆成立。';
    if (s.indexOf('\\det(AB)=') >= 0) return '行列式對乘法可以拆開：' + T('\\det(AB)=\\det A\\cdot\\det B') + ' ⟹ 恆成立。';
    if (s.indexOf('(AB)C=') >= 0) return '矩陣乘法有結合律（不能交換的是左右順序，不是括號）⟹ 恆成立。';
    if (s.indexOf('A(B+C)') >= 0 || s.indexOf('A(B-C)') >= 0) return '分配律成立（左右兩邊 ' + T('A') + ' 都在左邊，順序沒有換）⟹ 恆成立。';
    if (s.indexOf('\\det(-A)') >= 0) return '二階時 ' + T('\\det(-A)=(-1)^2\\det A=\\det A') + ' ⟹ 恆成立。';
    if (s.indexOf('(AB)^{-1}=A^{-1}B^{-1}') >= 0) return '反方陣要把順序顛倒：' + T('(AB)^{-1}=B^{-1}A^{-1}') + '，而乘法不能交換 ⟹ 不恆成立。';
    if (s.indexOf('(AB)^{-1}=B^{-1}A^{-1}') >= 0) return '驗算 ' + T('(AB)(B^{-1}A^{-1})=A(BB^{-1})A^{-1}=AA^{-1}=I') + ' ⟹ 恆成立。';
    if (s.indexOf('\\det(A^{-1})') >= 0) return '由 ' + T('AA^{-1}=I') + ' 兩邊取行列式得 ' + T('\\det A\\cdot\\det(A^{-1})=1') + ' ⟹ 恆成立。';
    if (s.indexOf('\\det B=\\dfrac{1}{\\det A}') >= 0) return '兩邊取行列式：' + T('\\det A\\cdot\\det B=\\det I=1') + ' ⟹ 恆成立。';
    if (s.indexOf('A^2=I') >= 0) return '取 ' + T('A=' + bm(J0)) + '：' + T('A^2=I') + '，但它既不是 ' + T('I') + ' 也不是 ' + T('-I') + ' ⟹ 不恆成立。';
    if (s.indexOf('A^2=O') >= 0) return '取 ' + T('N=' + bm(N0) + '\\ne O') + '：' + T('N^2=O') + ' ⟹ 不恆成立。';
    if (s.indexOf('AB=AC') >= 0) {
      if (s.indexOf('\\det A\\ne0') >= 0) return T('\\det A\\ne0') + ' ⟹ ' + T('A^{-1}') + ' 存在，兩邊左乘 ' + T('A^{-1}') + ' 就得 ' + T('B=C') + ' ⟹ 恆成立。';
      return '取 ' + T('A=' + bm(N0)) + '、' + T('B=I') + '、' + T('C=' + bm(C0)) + '：' + T('AB=AC=' + bm(N0)) + ' 但 ' + T('B\\ne C') + '（' + T('A') + ' 不可逆時不能消去）⟹ 不恆成立。';
    }
    if (s.indexOf('AB=O') >= 0) {
      if (s.indexOf('\\det A\\ne0') >= 0) return '兩邊左乘 ' + T('A^{-1}') + ' ⟹ ' + T('B=A^{-1}O=O') + ' ⟹ 恆成立。';
      return '取 ' + T('A=B=' + bm(N0) + '\\ne O') + '：' + T('AB=O') + ' ⟹ 不恆成立。';
    }
    if (s.indexOf('AB=BA') >= 0) return '矩陣乘法一般不能交換，反例 ' + cex + ' ⟹ 不恆成立。';
    return '把定義代回去逐項比對即可。';
  }

  var L1_H1 = {
    matForm: '這是「把方程組寫成矩陣形式」：係數照未知數的順序橫著抄成一列，缺的字母那一格要補零，常數項另外排成一行。',
    matVec: '這是「方陣乘行向量」：橫的乘直的再相加；同一個式子按未知數分組，就是兩個行向量的線性組合。',
    det2: '這是「二階行列式」：主對角線相乘減副對角線相乘；值是零代表兩個行向量平行，絕對值就是平行四邊形面積。',
    cramer2: '這是「二元克拉瑪公式」：先算係數行列式，再把要求的那個未知數所在的行換成常數行，兩者相除。',
    twoLineCase: '這是「二元聯立解的三種情況」：先看係數行列式是不是零；是零再比對常數項有沒有成同一個比例。',
    colCombo: '這是「行向量的線性組合」：兩行不平行就填得滿整個平面，平行就只填得滿一條直線，再看常數行向量在不在那條直線上。',
    augRowOp: '這是「增廣矩陣與列運算」：整列一起動，最右邊的常數項一格都不能漏。',
    elim3: '這是「消去法解三元一次聯立」：先用第一式把第一個未知數消掉，剩下兩式再消一個，最後由下往上代回。',
    echelonRead: '這是「由階梯形讀答案」：先看最後一列——係數全是零而常數不是零就矛盾，整列全是零就少一條有效方程式。',
    cramer3: '這是「三階克拉瑪公式」：先算係數行列式，不為零才能用；求哪一個未知數就把它那一行換成常數行。',
    countSol3: '這是「三元聯立解的個數」：先算係數行列式，不為零就恰有一組；是零再比對常數項對不對得上。',
    planeOne: '這是「三平面交於一點」：係數行列式不為零代表三個法向量不共平面，公共部分就是唯一的一點。',
    planeCase: '這是「行列式為零而有解的三平面」：看化成階梯形後剩幾條有效方程式，剩兩條是一條直線，剩一條是整個平面。',
    planeNoSol: '這是「行列式為零且無解的三平面」：先看哪幾個法向量互相平行，再看常數項對不對得上，化簡後一定會冒出矛盾。',
    matAddK: '這是「矩陣的加減與係數積」：全部逐格處理；解矩陣方程式就像解一次方程式，先移項再每格去除。',
    matMul: '這是「矩陣相乘」：中間的維度對上才乘得起來，每一格都是「第幾列配第幾行」乘起來再相加。',
    mulTrap: '這是「矩陣乘法的陷阱」：先問這條性質有沒有用到交換律或消去律，用到了就去找反例。',
    inv2: '這是「二階反方陣」：先算行列式，不為零才存在；主對角線交換、副對角線變號，再整體除以行列式。',
    invExist: '這是「反方陣的存在性」：不可逆就是行列式等於零，先把行列式用參數表示出來，再解那條方程式。',
    invSolve: '這是「用反方陣解聯立」：寫成方陣乘行向量之後左乘反方陣；換一個常數行時反方陣不必重算。',
    matPow: '這是「方陣的乘冪」：先算平方與立方找規律——看是每格各自次方、拆成單位方陣加一個平方為零的方陣，還是有週期。',
    detProp: '這是「行列式的性質」：乘積的行列式等於行列式的乘積，係數積在二階要平方，反方陣的行列式取倒數。',
    linTrans: '這是「線性變換的像與原像」：求像就把矩陣乘上去，求原像就反過來解聯立。',
    basicTrans: '這是「基本變換的矩陣」：看兩個單位方向的點各自跑到哪裡，兩個像擺成兩個行向量就是矩陣。',
    compose: '這是「合成變換」：先做的擺右邊、後做的擺左邊，乘起來就是整體的矩陣。',
    detArea: '這是「行列式與面積伸縮率」：面積會乘上行列式的絕對值，負號只代表左右翻轉。',
    transMat: '這是「轉移方陣」：每一直行代表「原本在這一類的跑去哪」，所以每一行的和是一；下一期的狀態就是方陣乘現在的狀態。',
    steady: '這是「穩定狀態」：解方陣乘向量等於原向量，會化成一條比例式，再配上兩個分量相加等於一才釘得住。'
  };

  var L1_SOL = {};

  /* ── §1 寫出係數方陣與矩陣形式 ── */
  L1_SOL.matForm = function (p, o) {
    var A = p.A, b = p.b;
    if (p.kind === 0) {
      return ['把兩式的係數照 ' + T('x,\\,y') + ' 的順序橫著抄：第一式 ' + T(lin(A[0], VS2) + '=' + b[0]) + ' ⟹ 第一列 ' + T('(' + A[0][0] + ',\\,' + A[0][1] + ')') + '、常數 ' + T(b[0])
        + '；第二式 ' + T(lin(A[1], VS2) + '=' + b[1]) + ' ⟹ 第二列 ' + T('(' + A[1][0] + ',\\,' + A[1][1] + ')') + '、常數 ' + T(b[1]) + '。',
        '兩列疊起來就是係數方陣 ' + T('A=' + bm(A)) + '；常數項單獨排成一行就是 ' + T('\\vec{b}=' + cv(b)) + '。',
        T('a_{' + p.i + p.j + '}') + ' 是第 ' + T(p.i) + ' 列第 ' + T(p.j) + ' 行那一格，數過去得 ' + T('a_{' + p.i + p.j + '}=' + A[p.i - 1][p.j - 1]) + '。' + sxFin(o)];
    }
    if (p.kind === 1) {
      return ['每一式都要湊滿 ' + T('x,\\,y,\\,z') + ' 三格，沒出現的字母那一格補 ' + T(0) + '：第一式 ' + T(lin(A[0], VS3) + '=' + b[0]) + ' ⟹ 第一列 ' + T('(' + A[0].join(',\\,') + ')')
        + '；第二式 ⟹ ' + T('(' + A[1].join(',\\,') + ')') + '；第三式 ⟹ ' + T('(' + A[2].join(',\\,') + ')') + '。',
        '三列疊起來得 ' + T('A=' + bm(A)) + '，常數項排成一行得 ' + T('\\vec{b}=' + cv(b)) + '。',
        T('A') + ' 有三列三行（未知數有三個、方程式也有三條）⟹ 它是三階方陣。' + sxFin(o)];
    }
    var x = p.ans.x, D = sxDv2(A), Dx = b[0] * A[1][1] - A[0][1] * b[1], Dy = A[0][0] * b[1] - b[0] * A[1][0];
    return ['方陣乘行向量是「橫的乘直的再相加」：第一列 ' + T('(' + A[0][0] + ',\\,' + A[0][1] + ')') + ' 配 ' + T('(x,y)') + ' 得 ' + T(lin(A[0], VS2) + '=' + b[0])
      + '，第二列得 ' + T(lin(A[1], VS2) + '=' + b[1]) + '，也就是 ' + T(csys(A, b, VS2)) + '。',
      '再解這個二元一次聯立：' + T('\\Delta=' + sxDet2(A) + '=' + D) + '、' + T('\\Delta_x=' + prod([b[0], A[1][1]]) + '-' + prod([A[0][1], b[1]]) + '=' + Dx)
      + '、' + T('\\Delta_y=' + prod([A[0][0], b[1]]) + '-' + prod([b[0], A[1][0]]) + '=' + Dy) + '。',
      T('x=' + sxQ2(Dx, D)) + '、' + T('y=' + sxQ2(Dy, D)) + ' ⟹ ' + T('(x,y)=(' + x[0] + ',' + x[1] + ')') + '。' + sxFin(o)];
  };

  /* ── §1 方陣乘向量 ＝ 線性組合 ── */
  L1_SOL.matVec = function (p, o) {
    var A = p.A, v = p.v, w = p.ans.w.map(sxF);
    return ['「橫的乘直的再相加」：第一列配上行向量得 ' + T(sxCellN(A, [[v[0]], [v[1]]], 0, 0)) + '，第二列得 ' + T(sxCellN(A, [[v[0]], [v[1]]], 1, 0)) + '。',
      '所以 ' + no(1) + T('A' + cv(v) + '=' + cv(w)) + '。',
      no(2) + '把 ' + T('A' + cv(VS2) + '=' + cv([lin([A[0][0], A[0][1]], VS2), lin([A[1][0], A[1][1]], VS2)])) + ' 按 ' + T('x') + '、' + T('y') + ' 分組，' + T('x') + ' 收走 ' + T('A') + ' 的第一行、' + T('y') + ' 收走第二行 ⟹ ' + T('x' + cv([A[0][0], A[1][0]]) + '+y' + cv([A[0][1], A[1][1]])) + '。' + sxFin(o)];
  };

  /* ── §1 二階行列式（值、平行、面積） ── */
  L1_SOL.det2 = function (p, o) {
    if (p.kind === 0) {
      var A = p.A, B = p.B, k = p.k, dA = p.ans.dA;
      return ['二階行列式是「主對角線相乘減副對角線相乘」：' + T('\\det A=' + sxDet2(A) + '=' + dA) + '。',
        T('B') + ' 的第一行是 ' + T('(' + B[0][0] + ',' + B[1][0] + ')') + '、第二行是 ' + T('(' + B[0][1] + ',' + B[1][1] + ')') + '，後者恰是前者的 ' + T(k) + ' 倍 ⟹ 兩行平行；照公式算也是 ' + T('\\det B=' + sxDet2(B) + '=0') + '。',
        '兩個行向量平行（也就是行列式為 ' + T(0) + '）的是 ' + T('B') + '。' + sxFin(o)];
    }
    var u = p.u, v = p.v, d = p.ans.d, M = [[u[0], v[0]], [u[1], v[1]]];
    return ['把 ' + T('\\vec{u}') + ' 當第一行、' + T('\\vec{v}') + ' 當第二行：' + T(vmx(M) + '=' + sxDet2(M) + '=' + d) + '。',
      '以這兩個向量為鄰邊的平行四邊形面積就是行列式的絕對值（負號只代表兩向量的轉向）⟹ 面積 ' + T(Math.abs(d)) + '。' + sxFin(o)];
  };

  /* ── §1 二元克拉瑪公式 ── */
  L1_SOL.cramer2 = function (p, o) {
    var A = p.A, b = p.b, D = p.ans.D, Dx = p.ans.Dx, Dy = p.ans.Dy, x = sxF(p.ans.x), y = sxF(p.ans.y);
    return [T('\\Delta=' + vmx(A) + '=' + sxDet2(A) + '=' + D) + '，不為 ' + T(0) + ' ⟹ 克拉瑪公式可用。',
      '求 ' + T('x') + ' 就把第一行換成常數行 ' + T('(' + b[0] + ',\\,' + b[1] + ')') + '：' + T('\\Delta_x=' + vmx([[b[0], A[0][1]], [b[1], A[1][1]]]) + '=' + prod([b[0], A[1][1]]) + '-' + prod([A[0][1], b[1]]) + '=' + Dx)
      + '；求 ' + T('y') + ' 換第二行：' + T('\\Delta_y=' + vmx([[A[0][0], b[0]], [A[1][0], b[1]]]) + '=' + prod([A[0][0], b[1]]) + '-' + prod([b[0], A[1][0]]) + '=' + Dy) + '。',
      '兩個都除以 ' + T('\\Delta') + '：' + T('x=' + sxQ2(Dx, D)) + '、' + T('y=' + sxQ2(Dy, D)) + ' ⟹ ' + T('(x,y)=\\left(' + Fr.tex(x, true) + ',\\,' + Fr.tex(y, true) + '\\right)') + '。' + sxFin(o)];
  };

  /* ── §1 二元聯立解的三種情況 ── */
  L1_SOL.twoLineCase = function (p, o) {
    var A = p.A, b = p.b;
    if (p.kind === 0) {
      var D = sxDv2(A), Dx = b[0] * A[1][1] - A[0][1] * b[1], Dy = A[0][0] * b[1] - b[0] * A[1][0], s = p.ans.sol;
      return ['先算係數行列式：' + T('\\Delta=' + sxDet2(A) + '=' + D) + '，不為 ' + T(0) + ' ⟹ 兩條直線不平行 ⟹ 恰交於一點，也就是恰有一組解。',
        '接著解出交點：' + T('\\Delta_x=' + prod([b[0], A[1][1]]) + '-' + prod([A[0][1], b[1]]) + '=' + Dx) + '、' + T('\\Delta_y=' + prod([A[0][0], b[1]]) + '-' + prod([b[0], A[1][0]]) + '=' + Dy) + '。',
        T('x=' + sxQ2(Dx, D)) + '、' + T('y=' + sxQ2(Dy, D)) + ' ⟹ ' + T('(x,y)=(' + s[0] + ',' + s[1] + ')') + '。' + sxFin(o)];
    }
    var k = A[1][0] / A[0][0], kc = k * b[0];
    if (p.kind === 1) {
      var a1 = A[0][0], b1 = A[0][1], c1 = b[0];
      var co = F(-b1 * Math.abs(a1), a1), cn = F(c1, a1), cy = Math.abs(a1);
      return ['比較兩式：第二式 ' + T(lin(A[1], VS2) + '=' + b[1]) + ' 的左邊恰是第一式左邊的 ' + T(k) + ' 倍，右邊也是（' + T(prod([k, c1]) + '=' + kc) + '，和 ' + T(b[1]) + ' 相同）⟹ 兩式其實是同一條直線。',
        '所以只剩一條有效方程式 ' + T(lin(A[0], VS2) + '=' + c1) + '，兩個未知數只被一條式子綁住 ⟹ 有一個字母自由，有無限多組解。',
        '令 ' + T('y=' + (cy === 1 ? 't' : cy + 't')) + '（這樣可以避開分數），代進去得 ' + T('x=' + sxPar(co, cn)) + ' ⟹ ' + T(paramTex([co, F(cy)], [cn, F(0)], VS2)) + '，' + T('t') + ' 為實數。' + sxFin(o)];
    }
    return ['比較兩式：第二式 ' + T(lin(A[1], VS2) + '=' + b[1]) + ' 的左邊恰是第一式左邊的 ' + T(k) + ' 倍 ⟹ 兩條直線平行。',
      '但右邊對不上：' + T(prod([k, b[0]]) + '=' + kc) + '，題目給的卻是 ' + T(b[1]) + '。',
      '把第一式的 ' + T(k) + ' 倍減掉第二式，左邊全消光，剩 ' + T('0=' + (kc - b[1])) + ' 的矛盾 ⟹ 兩條直線平行而不重合，無解。' + sxFin(o)];
  };

  /* ── §1 行向量的線性組合 ── */
  L1_SOL.colCombo = function (p, o) {
    var B = p.B, b = p.b, dB = p.ans.dB, u = [B[0][0], B[1][0]], v = [B[0][1], B[1][1]];
    var s1 = T('\\det B=' + sxDet2(B) + '=' + dB) + '。';
    if (p.kind === 2) {
      return [s1,
        T('B' + cv(VS2)) + ' 展開就是 ' + T('x' + cv(u) + '+y' + cv(v)) + '，也就是兩個行向量 ' + T('(' + u.join(',') + ')') + '、' + T('(' + v.join(',') + ')') + ' 的線性組合；行列式不為 ' + T(0) + ' ⟹ 這兩行不平行。',
        '不平行的兩個向量組合得出平面上任何向量，而且組法唯一 ⟹ 對 ' + T(cv(b)) + ' 恰有一組解。' + sxFin(o)];
    }
    var k = u[0] !== 0 ? v[0] / u[0] : v[1] / u[1], cr = b[0] * u[1] - b[1] * u[0];
    return [s1,
      '兩行 ' + T('(' + u.join(',') + ')') + ' 與 ' + T('(' + v.join(',') + ')') + ' 平行（後者是前者的 ' + T(k) + ' 倍）⟹ ' + T('x' + cv(u) + '+y' + cv(v)) + ' 組合出來的向量全部落在過原點、方向為 ' + T('(' + u.join(',') + ')') + ' 的那一條直線上。',
      '再看 ' + T(cv(b)) + ' 在不在這條線上：' + T(prod([b[0], u[1]]) + '-' + prod([b[1], u[0]]) + '=' + cr)
      + (cr === 0 ? '，是 ' + T(0) + ' ⟹ 在線上，而且 ' + T('x') + '、' + T('y') + ' 可以互相補償 ⟹ 有無限多組解。' : '，不是 ' + T(0) + ' ⟹ 不在線上 ⟹ 湊不出來，無解。') + sxFin(o)];
  };

  /* ── §2 增廣矩陣與列運算 ── */
  L1_SOL.augRowOp = function (p, o) {
    var A = p.A, b = p.b, m2 = p.m2, m3 = p.m3, R2 = p.ans.R2, c2 = p.ans.c2, R3 = p.ans.R3, c3 = p.ans.c3;
    return ['增廣矩陣就是把係數照 ' + T('x,\\,y,\\,z') + ' 的順序排好，常數項放到直線的右邊：' + T(agm(A, b)) + '。',
      T(opT(2, m2, 1)) + '：整列一起動，常數項也要算。' + sxOpRow(A[1], b[1], m2, A[0], b[0]) + ' ⟹ 第二列變成 ' + T(rowT(R2, c2)) + '。',
      T(opT(3, m3, 1)) + ' 同樣做：' + sxOpRow(A[2], b[2], m3, A[0], b[0]) + ' ⟹ 第三列變成 ' + T(rowT(R3, c3)) + '；第一列不動，整個增廣矩陣成為 ' + T(agm([A[0], R2, R3], [b[0], c2, c3])) + '。' + sxFin(o)];
  };

  /* ── §2 消去法解三元一次聯立 ── */
  L1_SOL.elim3 = function (p, o) {
    var E = sxElimText(p.A, p.b);
    return [E.s1, E.s2, '整理得 ' + T('(x,y,z)=(' + E.x + ',' + E.y + ',' + E.z + ')') + '；代回原來的第一式 ' + T(lin(p.A[0], VS3) + '=' + p.b[0]) + ' 驗算相符。' + sxFin(o)];
  };

  /* ── §2 由階梯形讀答案 ── */
  L1_SOL.echelonRead = function (p, o) {
    var M = p.M, c = p.c, p11 = M[0][0], p12 = M[0][1], p13 = M[0][2], p22 = M[1][1], p23 = M[1][2], d1 = c[0], d2 = c[1];
    if (p.kind === 0) {
      var p33 = M[2][2], d3 = c[2];
      var z = F(d3, p33), y = Fr.div(Fr.sub(F(d2), Fr.mul(F(p23), z)), F(p22));
      var x = Fr.div(Fr.sub(Fr.sub(F(d1), Fr.mul(F(p12), y)), Fr.mul(F(p13), z)), F(p11));
      var zt = Fr.tex(z, true), yt = Fr.tex(y, true), xt = Fr.tex(x, true);
      var ry = Fr.sub(F(d2), Fr.mul(F(p23), z)), rx = Fr.sub(Fr.sub(F(d1), Fr.mul(F(p12), y)), Fr.mul(F(p13), z));
      return ['三列的領導元素 ' + T(p11) + '、' + T(p22) + '、' + T(p33) + ' 都不是 ' + T(0) + ' ⟹ 三個未知數都被定住，恰有一組解。最後一列還原成 ' + T(lin([0, 0, p33], VS3) + '=' + d3) + ' ⟹ ' + T('z=' + sxQ2(d3, p33)) + '。',
        '往上代：第二列是 ' + T(lin([0, p22, p23], VS3) + '=' + d2) + ' ⟹ ' + T(lin([p22], ['y']) + '=' + d2 + '-' + prod([p23, zt]) + '=' + Fr.tex(ry, true)) + (p22 === 1 ? '' : ' ⟹ ' + T('y=' + yt)) + '。',
        '再往上代：第一列是 ' + T(lin([p11, p12, p13], VS3) + '=' + d1) + ' ⟹ ' + T(lin([p11], ['x']) + '=' + d1 + '-' + prod([p12, yt]) + '-' + prod([p13, zt]) + '=' + Fr.tex(rx, true)) + (p11 === 1 ? '' : ' ⟹ ' + T('x=' + xt)) + '，所以 ' + T('(x,y,z)=\\left(' + xt + ',\\,' + yt + ',\\,' + zt + '\\right)') + '。' + sxFin(o)];
    }
    if (p.kind === 1) {
      var s = Math.abs(p11 * p22);
      var yy = Fr.div(F(-p23 * s), F(p22)), ycn = F(d2, p22);
      var xco = Fr.div(Fr.sub(Fr.mul(F(-p12), yy), F(p13 * s)), F(p11)), xcn = Fr.div(Fr.sub(F(d1), Fr.mul(F(p12), ycn)), F(p11));
      return ['第三列的係數與常數項全是 ' + T(0) + '，還原成 ' + T('0=0') + '，沒有提供任何新資訊 ⟹ 三個未知數只剩 ' + T(2) + ' 條有效方程式，有一個字母自由，所以有無限多組解。',
        '令 ' + T('z=' + (s === 1 ? 't' : s + 't')) + '（取 ' + T(s) + ' 是為了避開分數）；第二列 ' + T(lin([0, p22, p23], VS3) + '=' + d2) + ' ⟹ ' + T('y=' + sxPar(yy, ycn)) + '。',
        '第一列 ' + T(lin([p11, p12, p13], VS3) + '=' + d1) + ' 再代入 ' + T('y') + '、' + T('z') + ' ⟹ ' + T('x=' + sxPar(xco, xcn)) + '，合起來 ' + T(paramTex([xco, yy, F(s)], [xcn, ycn, F(0)])) + '，' + T('t') + ' 為實數。' + sxFin(o)];
    }
    return ['先看最後一列：三個係數全是 ' + T(0) + '，常數項卻是 ' + T(c[2]) + ' ⟹ 還原成方程式就是 ' + T('0=' + c[2]) + '。',
      '不管 ' + T('x,\\,y,\\,z') + ' 取什麼值，左邊永遠是 ' + T(0) + '，不可能等於 ' + T(c[2]) + ' ⟹ 矛盾，前兩列不必再算 ⟹ 無解。' + sxFin(o)];
  };

  /* ── §2 三階克拉瑪公式 ── */
  L1_SOL.cramer3 = function (p, o) {
    var A = p.A, b = p.b, an = p.ans, x = an.x;
    var col = function (j) { return A.map(function (row, i) { return row.map(function (v, jj) { return jj === j ? b[i] : v; }); }); };
    return ['先把係數行列式沿第一列展開：' + T('\\Delta=' + vmx(A) + '=' + sxDet3(A) + '=' + an.D) + '，不為 ' + T(0) + ' ⟹ 克拉瑪公式可用。',
      '求 ' + T('x') + ' 就把第一行換成常數行 ' + T('(' + b.join(',\\,') + ')') + '、其餘兩行不動：' + T('\\Delta_x=' + vmx(col(0)) + '=' + sxDet3(col(0)) + '=' + an.Dx)
      + '；同法換第二行、第三行得 ' + T('\\Delta_y=' + sxDet3(col(1)) + '=' + an.Dy) + '、' + T('\\Delta_z=' + sxDet3(col(2)) + '=' + an.Dz) + '。',
      '三個都除以 ' + T('\\Delta') + '：' + T('x=' + sxQ2(an.Dx, an.D)) + '、' + T('y=' + sxQ2(an.Dy, an.D)) + '、' + T('z=' + sxQ2(an.Dz, an.D)) + ' ⟹ ' + T('(x,y,z)=(' + x.join(',') + ')') + '。' + sxFin(o)];
  };

  /* ── §2 三元聯立解的個數 ── */
  L1_SOL.countSol3 = function (p, o) {
    var A = p.A, b = p.b, D = p.ans.D;
    if (p.kind === 0) {
      return ['先算係數方陣的行列式，沿第一列展開：' + T('\\Delta=' + vmx(A) + '=' + sxDet3(A) + '=' + D) + '。',
        '判定流程的第一刀就是看 ' + T('\\Delta') + ' 是不是 ' + T(0) + '：本題 ' + T('\\Delta=' + D + '\\ne0') + ' ⟹ 克拉瑪公式可用、解唯一 ⟹ 恰有一組解，不必再化階梯形。' + sxFin(o)];
    }
    var K = sxCombo(A[0], A[1], A[2]), k1 = K ? K[0] : 1, k2 = K ? K[1] : 1;
    var lhs = [], j;
    for (j = 0; j < 3; j++) lhs.push(prod([k1, A[0][j]]) + '+' + prod([k2, A[1][j]]) + '=' + A[2][j]);
    var vc = k1 * b[0] + k2 * b[1];
    return ['第三式的係數恰是第一式的 ' + T(k1) + ' 倍加第二式的 ' + T(k2) + ' 倍：' + T(lhs[0]) + '、' + T(lhs[1]) + '、' + T(lhs[2]) + ' 三格全對上 ⟹ 第三列是前兩列湊出來的 ⟹ ' + T('\\Delta=0') + '。',
      '再比對常數項：' + T(prod([k1, b[0]]) + '+' + prod([k2, b[1]]) + '=' + vc) + '，題目給的是 ' + T(b[2]) + '，兩者' + (vc === b[2] ? '相同' : '不同') + '。',
      (vc === b[2]
        ? '相同 ⟹ 第三式只是前兩式的組合，沒有提供新資訊，化成階梯形後只剩 ' + T(2) + ' 條有效方程式 ⟹ 有無限多組解。'
        : '不同 ⟹ 把第一式的 ' + T(k1) + ' 倍加第二式的 ' + T(k2) + ' 倍再減掉第三式，左邊全消光，剩 ' + T('0=' + (vc - b[2])) + ' 的矛盾 ⟹ 無解。') + sxFin(o)];
  };

  /* ── §3 Δ≠0：三平面交於一點 ── */
  L1_SOL.planeOne = function (p, o) {
    var A = p.A, b = p.b, D = p.ans.D, E = sxElimText(A, b);
    return ['判定流程第一步先算 ' + T('\\Delta') + '：沿第一列展開得 ' + T('\\Delta=' + vmx(A) + '=' + sxDet3(A) + '=' + D) + '。',
      T('\\Delta=' + D + '\\ne0') + ' ⟹ 三個法向量不共平面（誰也不是另外兩個湊出來的）⟹ 三平面恰交於一點，公共部分是唯一的一個點。',
      E.s1 + E.s2 + '所以公共部分是 ' + T('(x,y,z)=(' + E.x + ',' + E.y + ',' + E.z + ')') + '。' + sxFin(o)];
  };

  /* ── §3 Δ=0 且有解 ── */
  L1_SOL.planeCase = function (p, o) {
    var A = p.A, b = p.b;
    if (p.kind === 2) {
      var k2 = A[1][0] / A[0][0], k3 = A[2][0] / A[0][0];
      return ['比較三式的係數：第一式是 ' + T('(' + A[0].join(',\\,') + ')') + '，第二式 ' + T('(' + A[1].join(',\\,') + ')') + ' 恰是它的 ' + T(k2) + ' 倍、第三式 ' + T('(' + A[2].join(',\\,') + ')') + ' 恰是它的 ' + T(k3) + ' 倍。',
        '連常數項也成同一比例：' + T(prod([k2, b[0]]) + '=' + b[1]) + '、' + T(prod([k3, b[0]]) + '=' + b[2]) + ' ⟹ 三式其實是同一條式子，三個平面完全重合。',
        '化成階梯形後第二、三列全變成 ' + T(0) + '，只剩 ' + T(1) + ' 條有效方程式 ' + T(lin(A[0], VS3) + '=' + b[0]) + '；自由度是 ' + T('3-1=2') + ' ⟹ 公共部分是整個平面，要用兩個參數描述。' + sxFin(o)];
    }
    if (p.kind === 1) {
      var kd = A[1][0] / A[0][0], C1 = sxCross(A[0], A[2]);
      return ['第二式 ' + T(lin(A[1], VS3) + '=' + b[1]) + ' 的係數是第一式的 ' + T(kd) + ' 倍，連常數項也是（' + T(prod([kd, b[0]]) + '=' + b[1]) + '）⟹ ' + T('E_1') + ' 與 ' + T('E_2') + ' 是同一個平面（重合）。',
        T('E_3') + ' 的法向量 ' + T('(' + A[2].join(',\\,') + ')') + ' 與它們不平行（例如二階子式 ' + T(C1.t) + '，不為 ' + T(0) + '）⟹ 第三個平面和那個重合的平面交出一條直線。',
        '化成階梯形後第二列整列變 ' + T(0) + '，剩 ' + T(2) + ' 條有效方程式；自由度 ' + T('3-2=1') + ' ⟹ 公共部分是一條直線。' + sxFin(o)];
    }
    var K = sxCombo(A[0], A[1], A[2]), k1 = K ? K[0] : 1, kk = K ? K[1] : 1, C0 = sxCross(A[0], A[1]);
    return ['第三式的係數恰是第一式的 ' + T(k1) + ' 倍加第二式的 ' + T(kk) + ' 倍：' + T(prod([k1, A[0][0]]) + '+' + prod([kk, A[1][0]]) + '=' + A[2][0]) + '、' + T(prod([k1, A[0][1]]) + '+' + prod([kk, A[1][1]]) + '=' + A[2][1]) + '、' + T(prod([k1, A[0][2]]) + '+' + prod([kk, A[1][2]]) + '=' + A[2][2]) + '，常數項也對得上（' + T(prod([k1, b[0]]) + '+' + prod([kk, b[1]]) + '=' + b[2]) + '）。',
      '所以第三式沒有提供新資訊，化成階梯形後第三列全變 ' + T(0) + '，剩 ' + T(2) + ' 條有效方程式；而 ' + T('E_1') + '、' + T('E_2') + ' 的法向量不平行（二階子式 ' + T(C0.t) + '，不為 ' + T(0) + '）⟹ 三個平面兩兩相異。',
      '自由度 ' + T('3-2=1') + ' ⟹ 公共部分是一條直線，三個相異平面共交於這一條線。' + sxFin(o)];
  };

  /* ── §3 Δ=0 且無解 ── */
  L1_SOL.planeNoSol = function (p, o) {
    var A = p.A, b = p.b;
    if (p.kind === 0) {
      var K = sxCombo(A[0], A[1], A[2]), k1 = K ? K[0] : 1, k2 = K ? K[1] : 1, vc = k1 * b[0] + k2 * b[1];
      var C1 = sxCross(A[0], A[1]), C2 = sxCross(A[1], A[2]), C3 = sxCross(A[0], A[2]);
      return ['先看法向量：' + T(C1.t) + '、' + T(C2.t) + '、' + T(C3.t) + ' 都不為 ' + T(0) + ' ⟹ 三個法向量兩兩不平行 ⟹ 三個平面兩兩相交。',
        '但第三式的係數恰是第一式的 ' + T(k1) + ' 倍加第二式的 ' + T(k2) + ' 倍，常數項卻對不上：' + T(prod([k1, b[0]]) + '+' + prod([k2, b[1]]) + '=' + vc) + '，題目給的是 ' + T(b[2]) + '。',
        '把第一式的 ' + T(k1) + ' 倍加第二式的 ' + T(k2) + ' 倍再減第三式，左邊全消光，剩 ' + T('0=' + (vc - b[2])) + ' 的矛盾 ⟹ 無解；三條交線互相平行，圍成三稜柱的形狀。' + sxFin(o)];
    }
    if (p.kind === 1) {
      var k = A[1][0] / A[0][0], kc = k * b[0], C = sxCross(A[0], A[2]);
      return ['前兩式的係數成比例：第一式是 ' + T('(' + A[0].join(',\\,') + ')') + '，第二式 ' + T('(' + A[1].join(',\\,') + ')') + ' 恰是它的 ' + T(k) + ' 倍 ⟹ 兩個法向量平行。',
        '但常數項對不上：' + T(prod([k, b[0]]) + '=' + kc) + '，題目給的是 ' + T(b[1]) + ' ⟹ 這兩個平面平行而不重合。把第一式的 ' + T(k) + ' 倍減掉第二式得 ' + T('0=' + (kc - b[1])) + ' 的矛盾 ⟹ 整個方程組無解。',
        T('E_3') + ' 的法向量與它們不平行（二階子式 ' + T(C.t) + '，不為 ' + T(0) + '）⟹ 第三個平面與那兩個平行平面各交出一條直線。' + sxFin(o)];
    }
    if (p.kind === 2) {
      var q2 = A[1][0] / A[0][0], q3 = A[2][0] / A[0][0];
      return ['三式的係數全部成比例 ' + T('1:' + q2 + ':' + q3) + '（第二式是第一式的 ' + T(q2) + ' 倍、第三式是 ' + T(q3) + ' 倍）⟹ 三個法向量互相平行 ⟹ 三個平面互相平行。',
        '再比常數項：' + T(prod([q2, b[0]]) + '=' + (q2 * b[0])) + ' 但題目是 ' + T(b[1]) + '、' + T(prod([q3, b[0]]) + '=' + (q3 * b[0])) + ' 但題目是 ' + T(b[2]) + '，第二式與第三式之間也對不上 ⟹ 沒有任何兩個平面重合。',
        '把第一式的 ' + T(q2) + ' 倍減掉第二式就得 ' + T('0=' + (q2 * b[0] - b[1])) + ' 的矛盾 ⟹ 無解；三個平面互相平行且兩兩相異。' + sxFin(o)];
    }
    var kA = A[1][0] / A[0][0], kB = A[2][0] / A[0][0];
    return ['三式的係數全部成比例 ' + T('1:' + kA + ':' + kB) + ' ⟹ 三個法向量互相平行。',
      '第二式連常數項也是第一式的 ' + T(kA) + ' 倍（' + T(prod([kA, b[0]]) + '=' + b[1]) + '）⟹ ' + T('E_1') + ' 與 ' + T('E_2') + ' 重合。',
      '第三式的常數項卻對不上：' + T(prod([kB, b[0]]) + '=' + (kB * b[0])) + '，題目給的是 ' + T(b[2]) + ' ⟹ 把第一式的 ' + T(kB) + ' 倍減掉第三式得 ' + T('0=' + (kB * b[0] - b[2])) + ' 的矛盾 ⟹ 無解；' + T('E_3') + ' 與前兩個重合的平面平行且相異。' + sxFin(o)];
  };

  /* ── §4 矩陣加減與係數積 ── */
  L1_SOL.matAddK = function (p, o) {
    var A = p.A, B = p.B, s = p.s, u = p.u, w = p.w;
    var P = p.ans.P.map(function (r) { return r.map(sxF); }), Q = p.ans.Q.map(function (r) { return r.map(sxF); }), X = p.ans.X.map(function (r) { return r.map(sxF); });
    var Dm = mSub(MF(B), MF(A));
    var cell = function (i, j) { return A[i][j] + '+' + prod([s, B[i][j]]) + '=' + (A[i][j] + s * B[i][j]); };
    var cel2 = function (i, j) { return prod([u, A[i][j]]) + '-' + par(B[i][j]) + '=' + (u * A[i][j] - B[i][j]); };
    return [no(1) + '加減與係數積都是「逐格處理」：' + T(cell(0, 0)) + '、' + T(cell(0, 1)) + '、' + T(cell(1, 0)) + '、' + T(cell(1, 1)) + ' ⟹ ' + T(bm(P)) + '。',
      no(2) + '同樣逐格：左上角 ' + T(cel2(0, 0)) + '、右上角 ' + T(cel2(0, 1)) + '，四格算完得 ' + T(bm(Q)) + '。',
      no(3) + '先移項：' + T(w + 'X=B-A=' + bm(Dm)) + '，再每一格除以 ' + T(w) + '：左上 ' + T(sxQ2(Fr.num(Dm[0][0]), w)) + '、右下 ' + T(sxQ2(Fr.num(Dm[1][1]), w)) + ' ⟹ ' + T('X=' + bm(X)) + '。' + sxFin(o)];
  };

  /* ── §4 矩陣相乘 ── */
  L1_SOL.matMul = function (p, o) {
    var A = p.A;
    if (p.kind === 0) {
      var B = p.B, AB = mMul(MF(A), MF(B)), BA = mMul(MF(B), MF(A));
      return ['矩陣相乘是「第 ' + T('i') + ' 列配第 ' + T('j') + ' 行」：' + T('AB') + ' 的第一列第一行 ' + T(sxCellN(A, B, 0, 0)) + '、第一列第二行 ' + T(sxCellN(A, B, 0, 1)) + '、第二列第一行 ' + T(sxCellN(A, B, 1, 0)) + '、第二列第二行 ' + T(sxCellN(A, B, 1, 1)) + ' ⟹ ' + T('AB=' + bm(AB)) + '。',
        T('BA') + ' 要換成 ' + T('B') + ' 的列配 ' + T('A') + ' 的行，位置完全不一樣：第一列第一行 ' + T(sxCellN(B, A, 0, 0)) + '、第二列第二行 ' + T(sxCellN(B, A, 1, 1)) + '，四格算完得 ' + T('BA=' + bm(BA)) + '。',
        '把兩個結果逐格比對 ⟹ ' + (p.ans.same ? '每一格都一樣，這一題剛好 ' + T('AB=BA') + '（但矩陣乘法一般不能交換）。' : '至少有一格不同 ⟹ 不相等（矩陣乘法一般不能交換）。') + sxFin(o)];
    }
    var C = p.C, AC = mMul(MF(A), MF(C));
    return ['「中間對上才能乘，剩下的就是答案的大小」：' + T('A') + ' 是 ' + T('2\\times2') + '、' + T('C') + ' 是 ' + T('2\\times3') + '，中間的 ' + T(2) + ' 對上了 ⟹ ' + T('AC') + ' 乘得起來，而且是 ' + T('2\\times3') + ' 矩陣。',
      '逐格算「第 ' + T('i') + ' 列配第 ' + T('j') + ' 行」：第一列第一行 ' + T(sxCellN(A, C, 0, 0)) + '、第一列第三行 ' + T(sxCellN(A, C, 0, 2)) + '、第二列第二行 ' + T(sxCellN(A, C, 1, 1)) + '，六格算完得 ' + T('AC=' + bm(AC)) + '。',
      '反過來看 ' + T('CA') + '：' + T('C') + ' 是 ' + T('2\\times3') + '、' + T('A') + ' 是 ' + T('2\\times2') + '，中間是 ' + T('C') + ' 的行數 ' + T(3) + ' 對 ' + T('A') + ' 的列數 ' + T(2) + '，對不上 ⟹ 沒有意義。' + sxFin(o)];
  };

  /* ── §4 乘法的三個陷阱 ── */
  L1_SOL.mulTrap = function (p, o) {
    var ss = p.ss, tt = p.tt, k = p.k, i;
    var A0 = [[1, k], [0, 1]], B0 = [[1, 0], [1, 1]], N0 = [[0, 1], [0, 0]];
    var AB = mMul(MF(A0), MF(B0)), BA = mMul(MF(B0), MF(A0));
    var one = function (i2) { return no(i2 + 1) + sxTrap(ss[i2], k); };
    return ['先把兩組萬用反例準備好：取 ' + T('A=' + bm(A0)) + '、' + T('B=' + bm(B0)) + ' 得 ' + T('AB=' + bm(A0) + bm(B0) + '=' + bm(AB)) + ' 而 ' + T('BA=' + bm(B0) + bm(A0) + '=' + bm(BA)) + '（乘法不能交換）；取 ' + T('N=' + bm(N0)) + ' 得 ' + T('N\\ne O') + ' 但 ' + T('N^2=O') + '（沒有消去律）。',
      one(0) + one(1),
      one(2) + one(3) + sxFin(o)];
  };

  /* ── §4 二階反方陣 ── */
  L1_SOL.inv2 = function (p, o) {
    var A = p.A, d = p.ans.d, Iv = p.ans.Iv.map(function (r) { return r.map(sxF); });
    var adj = [[A[1][1], sxNg(A[0][1])], [sxNg(A[1][0]), A[0][0]]];
    return [T('\\det A=' + sxDet2(A) + '=' + d) + '，不為 ' + T(0) + ' ⟹ 反方陣存在。',
      '二階公式：主對角線的 ' + T(A[0][0]) + ' 與 ' + T(A[1][1]) + ' 交換、副對角線的 ' + T(A[0][1]) + ' 與 ' + T(A[1][0]) + ' 各加負號，再整體除以 ' + T('\\det A') + ' ⟹ ' + T('A^{-1}=\\dfrac{1}{' + d + '}' + bm(adj) + '=' + bm(Iv)) + '。',
      '驗算 ' + T('AA^{-1}') + '：第一列第一行 ' + T(prod([A[0][0], Fr.tex(Iv[0][0], true)]) + '+' + prod([A[0][1], Fr.tex(Iv[1][0], true)]) + '=1') + '、第一列第二行 ' + T(prod([A[0][0], Fr.tex(Iv[0][1], true)]) + '+' + prod([A[0][1], Fr.tex(Iv[1][1], true)]) + '=0') + '，四格算完得 ' + T('AA^{-1}=' + bm(ID2) + '=I') + ' ✓。' + sxFin(o)];
  };

  /* ── §4 反方陣的存在性與參數 ── */
  L1_SOL.invExist = function (p, o) {
    if (p.kind === 0) {
      var b2 = p.A[0][1], c2 = p.A[1][0], dd = p.A[1][1], kv = sxF(p.ans.k);
      var lhs = (dd === 1 ? 'k' : (dd === -1 ? '-k' : dd + 'k')) + pm(-b2 * c2);
      return ['把 ' + T('k') + ' 當成普通的數，照二階行列式算：' + T('\\det A=' + prod(['k', dd]) + '-' + prod([b2, c2])) + '，整理成 ' + T('\\det A=' + lhs) + '。',
        '不可逆就是 ' + T('\\det A=0') + '：解 ' + T(lhs + '=0') + ' ⟹ ' + T(lin([dd], ['k']) + '=' + (b2 * c2)) + ' ⟹ ' + T('k=' + Fr.tex(kv, true)) + '。' + sxFin(o)];
    }
    var bv = p.bv, cv2 = p.cv, m = p.m, rt = p.ans.roots;
    var quad = 'k^2' + tm(m, 'k') + pm(-bv * cv2);
    var raw = 'k' + (m === 0 ? '^2' : '(k' + pm(m) + ')') + '-' + prod([bv, cv2]);
    return ['把 ' + T('k') + ' 當成普通的數：' + T('\\det A=' + raw + (raw === quad ? '' : '=' + quad)) + '。',
      '不可逆 ⟺ ' + T('\\det A=0') + '：' + T(quad + '=0') + ' ⟹ 因式分解成 ' + T('(k' + pm(-rt[0]) + ')(k' + pm(-rt[1]) + ')=0') + '。',
      '兩個括號各自為 ' + T(0) + ' ⟹ ' + T('k=' + rt[0]) + ' 或 ' + T('k=' + rt[1]) + '。' + sxFin(o)];
  };

  /* ── §4 用反方陣解聯立 ── */
  L1_SOL.invSolve = function (p, o) {
    var A = p.A, b1 = p.b1, b2 = p.b2, d = sxDv2(A);
    var Iv = p.ans.Iv.map(function (r) { return r.map(sxF); }), x1 = p.ans.x1, x2 = p.ans.x2;
    var adj = [[A[1][1], sxNg(A[0][1])], [sxNg(A[1][0]), A[0][0]]];
    var comp = function (bb, i) { return prod([Fr.tex(Iv[i][0], true), bb[0]]) + '+' + prod([Fr.tex(Iv[i][1], true), bb[1]]); };
    return [T('\\det A=' + sxDet2(A) + '=' + d) + '，不為 ' + T(0) + ' ⟹ 反方陣存在：主對角線交換、副對角線變號再除以 ' + T(d) + ' ⟹ ' + T('A^{-1}=\\dfrac{1}{' + d + '}' + bm(adj) + '=' + bm(Iv)) + '。',
      '方程組就是 ' + T('A\\vec{x}=\\vec{b}') + '，兩邊左乘 ' + T('A^{-1}') + ' 得 ' + T('\\vec{x}=A^{-1}\\vec{b}') + '。' + no(2) + T('A^{-1}' + cv(b1) + '=' + cv([comp(b1, 0), comp(b1, 1)]) + '=' + cv(x1)) + ' ⟹ ' + T('(x,y)=(' + x1.join(',') + ')') + '。',
      no(3) + '只是換一個常數行，' + T('A^{-1}') + ' 不必重算：' + T('A^{-1}' + cv(b2) + '=' + cv([comp(b2, 0), comp(b2, 1)]) + '=' + cv(x2)) + ' ⟹ ' + T('(x,y)=(' + x2.join(',') + ')') + '。' + sxFin(o)];
  };

  /* ── §4 方陣的乘冪 ── */
  L1_SOL.matPow = function (p, o) {
    var A = p.A, n = p.n;
    if (p.kind === 0) {
      var d1 = A[0][0], d2 = A[1][1];
      return ['對角方陣乘對角方陣還是對角方陣：' + T('A^2=' + bm(A) + bm(A) + '=' + bm([[d1 * d1, 0], [0, d2 * d2]])) + '，也就是兩個對角元素各自平方 ' + T(par(d1) + '^2=' + (d1 * d1)) + '、' + T(par(d2) + '^2=' + (d2 * d2)) + '。',
        '同樣的道理，乘 ' + T(n) + ' 次就是各自 ' + T(n) + ' 次方：' + T(par(d1) + sup(n) + '=' + Math.pow(d1, n)) + '、' + T(par(d2) + sup(n) + '=' + Math.pow(d2, n)) + '。',
        '所以 ' + T('A' + sup(n) + '=' + bm([[Math.pow(d1, n), 0], [0, Math.pow(d2, n)]])) + '（非對角的兩格一路都是 ' + T(0) + '）。' + sxFin(o)];
    }
    if (p.kind === 1) {
      var k = p.k, low = p.low;
      var A2 = low ? [[1, 0], [2 * k, 1]] : [[1, 2 * k], [0, 1]], A3 = low ? [[1, 0], [3 * k, 1]] : [[1, 3 * k], [0, 1]];
      var N = low ? [[0, 0], [k, 0]] : [[0, k], [0, 0]];
      var Pn = low ? [[1, 0], [(k === 1 ? 'n' : (k === -1 ? '-n' : k + 'n')), 1]] : [[1, (k === 1 ? 'n' : (k === -1 ? '-n' : k + 'n'))], [0, 1]];
      var Pv = low ? [[1, 0], [k * n, 1]] : [[1, k * n], [0, 1]];
      return ['直接乘：' + T('A^2=' + bm(A) + bm(A) + '=' + bm(A2)) + '、' + T('A^3=A^2A=' + bm(A3)) + '。只有一格在動，而且每乘一次就多 ' + T(k) + '：' + T(k) + '、' + T(2 * k) + '、' + T(3 * k) + '。',
        '看出規律 ' + T('A^n=' + bm(Pn)) + '。也可以拆成 ' + T('A=I+N') + '，其中 ' + T('N=' + bm(N)) + ' 滿足 ' + T('N^2=O') + ' ⟹ 展開後只剩兩項 ' + T('A^n=I+nN') + '，結論一樣。',
        '代 ' + T('n=' + n) + '：那一格是 ' + T(sxMul(k, n)) + ' ⟹ ' + T('A' + sup(n) + '=' + bm(Pv)) + '。' + sxFin(o)];
    }
    var per = p.per, rem = n % per, Pv2 = mPw(MF(A), rem === 0 ? per : rem), q = Math.floor(n / per);
    return ['一路乘上去：' + T('A^2=' + bm(mPw(MF(A), 2))) + '、' + T('A^3=' + bm(mPw(MF(A), 3))) + '，再乘到 ' + T('A' + sup(per) + '=' + bm(ID2) + '=I') + ' 就回到原點 ⟹ 使 ' + T('A^m=I') + ' 的最小正整數是 ' + T('m=' + per) + '。',
      '有週期就只看餘數：' + T(n + '=' + prod([per, q]) + pm(rem)) + ' ⟹ ' + T('A' + sup(n) + '=' + (rem === 0 ? 'I' : sxPw(rem))) + '（餘數是 ' + T(0) + ' 時就回到 ' + T('I') + '）。',
      '所以 ' + T('A' + sup(n) + '=' + bm(Pv2)) + '。' + sxFin(o)];
  };

  /* ── §4 行列式的性質 ── */
  L1_SOL.detProp = function (p, o) {
    var da = p.da, db = p.db, k = p.k, n = p.n, ts = p.ts, vs = p.ans.vs.map(sxF);
    var one = function (i) {
      var t = ts[i], v = Fr.tex(vs[i], true), body;
      if (t === '\\det(AB)') body = '\\det A\\cdot\\det B=' + prod([da, db]) + '=' + v;
      else if (t === '\\det(' + k + 'A)') body = par(k) + '^2\\det A=' + prod([k * k, da]) + '=' + v;
      else if (t === '\\det(A^{-1})') body = '\\dfrac{1}{\\det A}=' + v;
      else if (t === '\\det(A' + sup(n) + ')') body = par('\\det A') + sup(n) + '=' + par(da) + sup(n) + '=' + v;
      else if (t === '\\det(A^2B^{-1})') body = '\\dfrac{(\\det A)^2}{\\det B}=\\dfrac{' + (da * da) + '}{' + db + '}=' + v;
      else if (t === '\\det(-B)') body = '(-1)^2\\det B=\\det B=' + v;
      else if (t === '\\det(' + k + 'B^{-1})') body = '\\dfrac{' + par(k) + '^2}{\\det B}=\\dfrac{' + (k * k) + '}{' + db + '}=' + v;
      else if (t === '\\det(AB^{2})') body = '\\det A\\cdot(\\det B)^2=' + prod([da, db * db]) + '=' + v;
      else body = v;
      return no(i + 1) + T(t + '=' + body);
    };
    return ['三條性質輪流用：' + T('\\det(AB)=\\det A\\cdot\\det B') + '、二階時 ' + T('\\det(cA)=c^2\\det A') + '（兩列都被乘上 ' + T('c') + '）、' + T('\\det(A^{-1})=\\dfrac{1}{\\det A}') + '。本題 ' + T('\\det A=' + da) + '、' + T('\\det B=' + db) + '。',
      one(0) + '　' + one(1) + '。',
      one(2) + '　' + one(3) + '。' + sxFin(o)];
  };

  /* ── §5 線性變換的像與原像 ── */
  L1_SOL.linTrans = function (p, o) {
    var A = p.A, P = p.P, Q = p.Q, im = p.ans.im.map(sxF), d = sxDv2(A);
    var tg = mVec(MF(A), VF(Q)), tgn = tg.map(function (f) { return Fr.num(f); });
    return [no(1) + '求像就是把矩陣乘上去：' + T('A' + cv(P) + '=' + cv([sxCellN(A, [[P[0]], [P[1]]], 0, 0).split('=')[0], sxCellN(A, [[P[0]], [P[1]]], 1, 0).split('=')[0]]) + '=' + cv(im)) + '，寫成坐標就是 ' + T('(' + im.map(EE).join(',') + ')') + '。',
      no(2) + '求原像則反過來：設它是 ' + T('(x,y)') + '，解 ' + T(csys(A, tgn, VS2)) + '（' + T('\\det A=' + sxDet2(A) + '=' + d) + '，不為 ' + T(0) + ' ⟹ 原像唯一）⟹ ' + T('(x,y)=(' + Q.join(',') + ')') + '。',
      no(3) + T('A' + cv([1, 0])) + ' 剛好取出 ' + T('A') + ' 的第一行、' + T('A' + cv([0, 1])) + ' 取出第二行 ⟹ ' + T('(1,0)\\to(' + A[0][0] + ',' + A[1][0] + ')') + '、' + T('(0,1)\\to(' + A[0][1] + ',' + A[1][1] + ')') + '。' + sxFin(o)];
  };

  /* ── §5 五種基本變換的矩陣 ── */
  L1_SOL.basicTrans = function (p, o) {
    var gs = p.gs, Ms = p.ans.Ms;
    var deg = function (c, s) { var d; for (d in ANG) if (ANG[d].c === c && ANG[d].s === s) return d; return null; };
    var one = function (i) {
      var M = Ms[i], g = gs[i], t = no(i + 1);
      if (g === 'scale') return t + '伸縮把 ' + T('(1,0)') + ' 送到 ' + T('(' + M[0][0] + ',0)') + '、把 ' + T('(0,1)') + ' 送到 ' + T('(0,' + M[1][1] + ')') + ' ⟹ ' + T(bm(M)) + '。';
      if (g === 'shear') {
        var up = M[0][1] !== 0, kk = up ? M[0][1] : M[1][0];
        return t + '推移是 ' + T(up ? '(x,y)\\to(' + lin([1, kk], VS2) + ',\\,y)' : '(x,y)\\to(x,\\,' + lin([kk, 1], VS2) + ')') + ' ⟹ ' + T('(1,0)\\to(' + M[0][0] + ',' + M[1][0] + ')') + '、' + T('(0,1)\\to(' + M[0][1] + ',' + M[1][1] + ')') + ' ⟹ ' + T(bm(M)) + '。';
      }
      if (g === 'rot') {
        var dg = deg(M[0][0], M[1][0]);
        return t + '旋轉的矩陣是 ' + T(bm([['\\cos\\theta', '-\\sin\\theta'], ['\\sin\\theta', '\\cos\\theta']])) + '；本題的旋轉角（化到 ' + T('0^\\circ') + ' 與 ' + T('360^\\circ') + ' 之間）是 ' + T(degT(dg)) + ' ⟹ ' + T('\\cos\\theta=' + M[0][0]) + '、' + T('\\sin\\theta=' + M[1][0]) + ' ⟹ ' + T(bm(M)) + '。';
      }
      if (g === 'ref') {
        var d2 = deg(M[0][0], M[0][1]);
        return t + '鏡射填的是 ' + T('2\\theta') + ' 不是 ' + T('\\theta') + '：矩陣長成 ' + T(bm([['\\cos2\\theta', '\\sin2\\theta'], ['\\sin2\\theta', '-\\cos2\\theta']])) + '，軸的傾角是 ' + T(degT(d2 / 2)) + ' ⟹ ' + T('2\\theta=' + degT(d2)) + ' ⟹ ' + T('\\cos2\\theta=' + M[0][0]) + '、' + T('\\sin2\\theta=' + M[0][1]) + ' ⟹ ' + T(bm(M)) + '。';
      }
      return t + '投影把整個平面壓到一條軸上：' + T(M[0][0] === 1 ? '(x,y)\\to(x,\\,0)' : '(x,y)\\to(0,\\,y)') + ' ⟹ ' + T('(1,0)\\to(' + M[0][0] + ',' + M[1][0] + ')') + '、' + T('(0,1)\\to(' + M[0][1] + ',' + M[1][1] + ')') + ' ⟹ ' + T(bm(M)) + '（' + T('\\det=0') + '，被壓扁了）。';
    };
    return ['所有二階線性變換的矩陣都照同一個辦法找：看 ' + T('(1,0)') + ' 的像擺成第一行、' + T('(0,1)') + ' 的像擺成第二行。',
      one(0) + one(1),
      one(2) + sxFin(o)];
  };

  /* ── §5 合成 ＝ 相乘 ── */
  L1_SOL.compose = function (p, o) {
    var M1 = p.M1, M2 = p.M2, P = p.P, M = mMul(MF(M2), MF(M1)), im = p.ans.im.map(sxF), d = p.ans.d;
    var Mn = M.map(function (r) { return r.map(function (f) { return Fr.num(f); }); });
    var st = mVec(MF(M1), VF(P));
    return ['動作 ' + T('a') + ' 的矩陣是 ' + T('A=' + bm(M1)) + '、動作 ' + T('b') + ' 的矩陣是 ' + T('B=' + bm(M2)) + '；先做的擺右邊、後做的擺左邊 ⟹ ' + T('M=BA') + '。',
      T('M=' + bm(M2) + bm(M1) + '=' + bm(M)) + '（例如第一列第一行是 ' + T(sxCellN(M2, M1, 0, 0)) + '）。',
      T('M' + cv(P) + '=' + cv([sxCellN(Mn, [[P[0]], [P[1]]], 0, 0).split('=')[0], sxCellN(Mn, [[P[0]], [P[1]]], 1, 0).split('=')[0]]) + '=' + cv(im)) + '，也就是 ' + T('(' + im.map(EE).join(',') + ')') + '（逐步追也一樣：先落到 ' + T('(' + st.map(EE).join(',') + ')') + ' 再做第二個動作）；' + T('\\det M=' + sxDet2(Mn) + '=' + d) + '。' + sxFin(o)];
  };

  /* ── §5 行列式＝面積伸縮率 ── */
  L1_SOL.detArea = function (p, o) {
    var A = p.A, S = p.S, d = p.ans.d, ar = p.ans.area, ar2 = p.ans.area2;
    return [T('\\det A=' + sxDet2(A) + '=' + d) + '。',
      '線性變換會把每一塊區域的面積乘上 ' + T('|\\det A|=' + ar) + '（負號只代表像被左右翻了一次，面積不會是負的）；單位正方形的面積是 ' + T(1) + ' ⟹ 像的面積是 ' + T(ar) + '。',
      '面積 ' + T(S) + ' 的區域也照同一個倍率放大：' + T(sxMul(ar, S)) + ' ⟹ 像的面積是 ' + T(ar2) + '。' + sxFin(o)];
  };

  /* ── §5 二階轉移方陣 ── */
  L1_SOL.transMat = function (p, o) {
    var p1 = p.p1, q1 = p.q1, a0 = p.a0;
    var M = [[F(p1, 10), F(q1, 10)], [F(10 - p1, 10), F(10 - q1, 10)]];
    var Md = [[dc(M[0][0]), dc(M[0][1])], [dc(M[1][0]), dc(M[1][1])]];
    var X0 = [F(a0, 10), F(10 - a0, 10)], X0d = [dc(X0[0]), dc(X0[1])];
    var X1 = mVec(M, X0), X1d = [dc(X1[0]), dc(X1[1])], X2 = mVec(M, X1), X2d = [dc(X2[0]), dc(X2[1])];
    var cmp = function (Md2, Xd, i) { return prod([Md2[i][0], Xd[0]]) + '+' + prod([Md2[i][1], Xd[1]]); };
    return ['轉移方陣的「直行」代表「原本在這一類的跑去哪」：第一行放原本是第一種的去向 ' + T('(' + Md[0][0] + ',\\,' + Md[1][0] + ')') + '、第二行放原本是第二種的去向 ' + T('(' + Md[0][1] + ',\\,' + Md[1][1] + ')') + ' ⟹ ' + T('M=' + bm(Md)) + '；檢查每一行的和：' + T(Md[0][0] + '+' + Md[1][0] + '=1') + ' ✓、' + T(Md[0][1] + '+' + Md[1][1] + '=1') + ' ✓。',
      '現在的狀態是 ' + T('X_0=' + cv(X0d)) + '（兩個分量相加是 ' + T(1) + '）。' + T('X_1=MX_0') + '：第一個分量 ' + T(cmp(Md, X0d, 0) + '=' + X1d[0]) + '、第二個分量 ' + T(cmp(Md, X0d, 1) + '=' + X1d[1]) + ' ⟹ ' + T('X_1=' + cv(X1d)) + '。',
      '再乘一次 ' + T('X_2=MX_1') + '：' + T(cmp(Md, X1d, 0) + '=' + X2d[0]) + '、' + T(cmp(Md, X1d, 1) + '=' + X2d[1]) + ' ⟹ ' + T('X_2=' + cv(X2d)) + '（兩個分量相加仍是 ' + T(1) + '，可以拿來驗算）。' + sxFin(o)];
  };

  /* ── §5 穩定狀態 ── */
  L1_SOL.steady = function (p, o) {
    var p1 = p.p1, q1 = p.q1, xs = sxF(p.ans.xs), ys = sxF(p.ans.ys);
    var M = [[F(p1, 20), F(q1, 20)], [F(20 - p1, 20), F(20 - q1, 20)]];
    var Md = [[dc(M[0][0]), dc(M[0][1])], [dc(M[1][0]), dc(M[1][1])]];
    var g = gcd(q1, 20 - p1) || 1, ra = q1 / g, rb = (20 - p1) / g;
    return ['穩定狀態就是再轉一次也不變的狀態。' + T('MX=X') + ' 的第一列是 ' + T(Md[0][0] + 'x+' + Md[0][1] + 'y=x') + '，移項得 ' + T(Md[0][1] + 'y=' + dc(F(20 - p1, 20)) + 'x') + ' ⟹ ' + T(ratT(q1, 20 - p1)) + '；第二列化簡後是同一條，所以光靠 ' + T('MX=X') + ' 釘不住。',
      '把它寫成比例 ' + T('x:y=' + ra + ':' + rb) + '，再配上 ' + T('x+y=1') + ' ⟹ ' + T('x=\\dfrac{' + ra + '}{' + ra + '+' + rb + '}=' + Fr.tex(xs, true)) + '、' + T('y=\\dfrac{' + rb + '}{' + ra + '+' + rb + '}=' + Fr.tex(ys, true)) + '，也就是 ' + T('(x,y)=\\left(' + Fr.tex(xs, true) + ',\\,' + Fr.tex(ys, true) + '\\right)') + '。',
      '驗算 ' + T('MX') + '：第一個分量 ' + T(prod([Md[0][0], Fr.tex(xs, true)]) + '+' + prod([Md[0][1], Fr.tex(ys, true)]) + '=' + Fr.tex(xs, true)) + '、第二個分量 ' + T(prod([Md[1][0], Fr.tex(xs, true)]) + '+' + prod([Md[1][1], Fr.tex(ys, true)]) + '=' + Fr.tex(ys, true)) + ' ⟹ ' + T('MX=' + cv([Fr.tex(xs, true), Fr.tex(ys, true)]) + '=X') + ' ✓。' + sxFin(o)];
  };

  var META_L1 = [
      ['matForm', '§1 寫出係數方陣與矩陣形式'], ['matVec', '§1 方陣乘向量與線性組合'], ['det2', '§1 二階行列式與面積'], ['cramer2', '§1 二元克拉瑪公式'], ['twoLineCase', '§1 二元聯立解的三種情況'], ['colCombo', '§1 行向量組合得出來嗎'],
      ['augRowOp', '§2 增廣矩陣與列運算'], ['elim3', '§2 消去法解三元一次聯立'], ['echelonRead', '§2 由階梯形讀答案'], ['cramer3', '§2 三階克拉瑪公式'], ['countSol3', '§2 三元聯立解的個數'],
      ['planeOne', '§3 三平面交於一點'], ['planeCase', '§3 Δ 為零且有解的三種'], ['planeNoSol', '§3 Δ 為零且無解的四種'],
      ['matAddK', '§4 矩陣加減與係數積'], ['matMul', '§4 矩陣相乘與可乘條件'], ['mulTrap', '§4 乘法的三個陷阱'], ['inv2', '§4 二階反方陣'], ['invExist', '§4 反方陣的存在性與參數'], ['invSolve', '§4 用反方陣解聯立'], ['matPow', '§4 方陣的乘冪'], ['detProp', '§4 行列式的性質'],
      ['linTrans', '§5 線性變換的像與原像'], ['basicTrans', '§5 五種基本變換的矩陣'], ['compose', '§5 合成變換'], ['detArea', '§5 行列式與面積伸縮率'], ['transMat', '§5 二階轉移方陣'], ['steady', '§5 穩定狀態']
  ];
  var META_L2 = [
      ['mulCombo', '§4 矩陣乘法綜合'], ['detAdv', '§4 行列式的進階計算'], ['invAdv', '§4 反方陣與矩陣方程'], ['matEqAdv', '§4 反方陣的性質與順序'], ['powPeriod', '§4 方陣的乘冪：週期與拆解'],
      ['transAdv', '§5 轉移方陣與穩定狀態'], ['linTransFind', '§5 由兩個像求變換矩陣'], ['rotAdv', '§5 旋轉矩陣與乘冪'], ['reflAdv', '§5 鏡射與旋轉的辨認'], ['composeAdv', '§5 合成的順序'], ['steadyParam', '§5 轉移方陣的參數題'],
      ['solve3Param', '§2 含參數的三元聯立'], ['rowOpBack', '§2 從階梯形反推參數'], ['infSol', '§2 無限多組解的參數式'], ['gaussWord', '§2 三元一次聯立的應用'],
      ['planeParam', '§3 含參數的三平面']
  ];
  /* ══════════════════════════════════════════════════════════
     L3　中上（15 型）：每型對應固定題 L3-1～L3-15 的「類似題」
     ─────────────────────────────────────────────────────────
     同題型換數字／情境，答案一律精確：整數、最簡分數（Fr.tex）、矩陣每一格最簡、
     無限多組解寫參數式、選項型寫成 (2)(3) 這種純字串。
     課綱界線（HANDOUT_SPEC §4 約 450–463 列）：不出現「秩／rank」「線性獨立／相依」
       「轉置」「特徵值／特徵向量／對角化」「伴隨矩陣／餘因子」「馬可夫鏈」「基本列運算」；
       確切算出反方陣僅限二階；A^n 用找規律／找週期／拆成 kI+N（N^2=O）；
       穩定狀態解 MX=X 配 x+y=1；轉移方陣限二階；三元一次聯立的主路是消去法／列運算。
     排版：矩陣 bmatrix、行列式 vmatrix、增廣矩陣 array{ccc|c}、方程組 cases、角度 ^\circ。
     提示 h 一律給「關鍵一步」但不給最終答案（同一型的不同變體會避開該變體的答案）。
     p 只放輸入參數與旗標（答案另放 p.ans，驗算器不讀）。
     每型開頭先丟掉一次 r()：連號種子的 LCG 首值幾乎相同，變體旗標不能靠它。
     ══════════════════════════════════════════════════════════ */
  var L3 = {};

  /* ── 小工具（名稱一律加 l3 前綴，不依賴產生器裡可能改名的內部函式） ── */
  function l3no(i) { return '(' + i + ') '; }
  function l3jo(a) { return a.join('　'); }
  function l3fp(f) { return [f.n, f.d]; }
  function l3opt(list) { var s = '', i; for (i = 0; i < list.length; i++) s += '(' + list[i] + ')'; return s; }
  function l3num(x) { return (typeof x === 'number') ? F(x) : x; }
  function l3abs(f) { return F(Math.abs(f.n), f.d); }
  function l3rws(a) { return a.join('\\\\ '); }
  function l3E(x) { if (typeof x === 'number') return String(x); if (typeof x === 'string') return x; return Fr.tex(x, true); }
  function l3bm(M) { return '\\begin{bmatrix}' + l3rws(M.map(function (w) { return w.map(l3E).join('&'); })) + '\\end{bmatrix}'; }
  function l3vm(M) { return '\\begin{vmatrix}' + l3rws(M.map(function (w) { return w.map(l3E).join('&'); })) + '\\end{vmatrix}'; }
  function l3cv(v) { return '\\begin{bmatrix}' + l3rws(v.map(l3E)) + '\\end{bmatrix}'; }
  function l3agm(M, b) { return '\\left[\\begin{array}{ccc|c}' + l3rws(M.map(function (w, i) { return w.map(l3E).join('&') + '&' + l3E(b[i]); })) + '\\end{array}\\right]'; }
  function l3MF(A) { return A.map(function (w) { return w.map(l3num); }); }
  function l3mul(A, B) {
    var n = A.length, m = B[0].length, p = B.length, out = [], i, j, k, s;
    for (i = 0; i < n; i++) { out.push([]); for (j = 0; j < m; j++) { s = F(0); for (k = 0; k < p; k++) s = Fr.add(s, Fr.mul(A[i][k], B[k][j])); out[i].push(s); } }
    return out;
  }
  function l3vec(A, v) { var i, j, s, out = []; for (i = 0; i < A.length; i++) { s = F(0); for (j = 0; j < v.length; j++) s = Fr.add(s, Fr.mul(A[i][j], v[j])); out.push(s); } return out; }
  function l3det2(A) { return Fr.sub(Fr.mul(A[0][0], A[1][1]), Fr.mul(A[0][1], A[1][0])); }
  function l3inv2(A) { var d = l3det2(A); return [[Fr.div(A[1][1], d), Fr.div(Fr.neg(A[0][1]), d)], [Fr.div(Fr.neg(A[1][0]), d), Fr.div(A[0][0], d)]]; }
  function l3id2() { return [[F(1), F(0)], [F(0), F(1)]]; }
  function l3mpw(A, n) { var R = l3id2(), i; for (i = 0; i < n; i++) R = l3mul(R, A); return R; }
  function l3same(A, B) { var i, j; for (i = 0; i < A.length; i++) for (j = 0; j < A[0].length; j++) if (!Fr.eq(A[i][j], B[i][j])) return false; return true; }
  function l3det3(A) {
    var t = F(0), j, a, b, c, d;
    for (j = 0; j < 3; j++) {
      a = A[1][(j + 1) % 3]; b = A[2][(j + 2) % 3]; c = A[1][(j + 2) % 3]; d = A[2][(j + 1) % 3];
      t = Fr.add(t, Fr.mul(A[0][j], Fr.sub(Fr.mul(a, b), Fr.mul(c, d))));
    }
    return t;
  }
  var L3VS3 = ['x', 'y', 'z'], L3VS2 = ['x', 'y'];
  /* 一次式（係數可為整數或分數物件）：跳過 0、係數 ±1 不印數字 */
  function l3linf(cs, vs) {
    var s = '', i, c;
    for (i = 0; i < cs.length; i++) {
      c = l3num(cs[i]);
      if (c.n === 0) continue;
      if (s === '') { if (c.n < 0) s += '-'; } else s += (c.n < 0 ? '-' : '+');
      if (!(Math.abs(c.n) === 1 && c.d === 1)) s += Fr.tex(l3abs(c), true);
      s += vs[i];
    }
    return s === '' ? '0' : s;
  }
  function l3cases(M, b, vs) {
    return '\\begin{cases}' + l3rws(M.map(function (w, i) { return l3linf(w, vs || L3VS3) + '=' + l3E(l3num(b[i])); })) + '\\end{cases}';
  }
  /* 一列的方程式（係數可以是未知數的字母） */
  function l3rowEq(row, cst) {
    var s = '', i, c;
    for (i = 0; i < row.length; i++) {
      c = row[i];
      if (typeof c === 'string') { s += (s === '' ? '' : '+') + c + L3VS3[i]; continue; }
      if (c === 0) continue;
      if (s === '') { if (c < 0) s += '-'; } else s += (c < 0 ? '-' : '+');
      if (Math.abs(c) !== 1) s += Math.abs(c);
      s += L3VS3[i];
    }
    return (s === '' ? '0' : s) + '=' + cst;
  }
  /* 含參數 a 的一次式：1-a、1+3a、-a、3a */
  function l3la(al, be) {
    if (al === 0) return String(be);
    var t = (Math.abs(al) === 1 ? '' : Math.abs(al)) + 'a';
    if (be === 0) return (al < 0 ? '-' : '') + t;
    return be + (al < 0 ? '-' : '+') + t;
  }
  /* 字串後面接上「減去一個整數」：不會出現 +- 或 -- */
  function l3sub(s, v) { return v === 0 ? s : s + (v > 0 ? '-' + v : '+' + (-v)); }
  function l3plus(s, v) { return v === 0 ? s : s + (v > 0 ? '+' + v : '-' + (-v)); }
  /* 二次式 L a^2 + M a + N */
  function l3quad(L, M, N) {
    var s = '';
    if (L !== 0) s += (L < 0 ? '-' : '') + (Math.abs(L) === 1 ? '' : Math.abs(L)) + 'a^2';
    if (M !== 0) s += (s === '' ? (M < 0 ? '-' : '') : (M < 0 ? '-' : '+')) + (Math.abs(M) === 1 ? '' : Math.abs(M)) + 'a';
    if (N !== 0) s += (s === '' ? String(N) : (N < 0 ? '-' : '+') + Math.abs(N));
    return s === '' ? '0' : s;
  }
  /* 直線 mx+ny=0（首項係數化為正） */
  function l3ln(m, n) {
    var s = '';
    if (m < 0) { m = -m; n = -n; }
    s += (m === 1 ? '' : m) + 'x';
    if (n !== 0) s += (n < 0 ? '-' : '+') + (Math.abs(n) === 1 ? '' : Math.abs(n)) + 'y';
    return s + '=0';
  }
  /* 參數式的一個分量：cn + co t */
  function l3tt(co, cn) {
    co = l3num(co); cn = l3num(cn);
    if (co.n === 0) return l3E(cn);
    var tp = (Math.abs(co.n) === 1 && co.d === 1) ? 't' : Fr.tex(l3abs(co), true) + 't';
    if (cn.n === 0) return (co.n < 0 ? '-' : '') + tp;
    return l3E(cn) + (co.n < 0 ? '-' : '+') + tp;
  }
  function l3ptex(co, cn, vs) {
    return '(' + (vs || L3VS3).join(',') + ')=(' + co.map(function (c, i) { return l3tt(c, cn[i]); }).join(',\\,') + ')';
  }
  function l3deg(d) { return d + '^\\circ'; }
  function l3pct(n) { return n + '\\%'; }
  /* kI 的寫法：A-3I、A+2I、A-I */
  function l3AkI(k) { return 'A' + (k > 0 ? '-' : '+') + (Math.abs(k) === 1 ? '' : Math.abs(k)) + 'I'; }
  function l3Ak(k) { return 'A' + (k > 0 ? '-' : '+') + Math.abs(k); }
  function l3kX(k) { return (k === 1 ? '' : (k === -1 ? '-' : String(k))) + 'X'; }
  /* 旋轉矩陣：題幹用符號、答案用特殊角的精確值 */
  var L3ANG = {
    0: ['1', '0'], 30: ['\\frac{\\sqrt{3}}{2}', '\\frac{1}{2}'], 45: ['\\frac{\\sqrt{2}}{2}', '\\frac{\\sqrt{2}}{2}'],
    60: ['\\frac{1}{2}', '\\frac{\\sqrt{3}}{2}'], 90: ['0', '1'], 120: ['-\\frac{1}{2}', '\\frac{\\sqrt{3}}{2}'],
    135: ['-\\frac{\\sqrt{2}}{2}', '\\frac{\\sqrt{2}}{2}'], 150: ['-\\frac{\\sqrt{3}}{2}', '\\frac{1}{2}'],
    180: ['-1', '0'], 210: ['-\\frac{\\sqrt{3}}{2}', '-\\frac{1}{2}'], 225: ['-\\frac{\\sqrt{2}}{2}', '-\\frac{\\sqrt{2}}{2}'],
    240: ['-\\frac{1}{2}', '-\\frac{\\sqrt{3}}{2}'], 270: ['0', '-1'], 300: ['\\frac{1}{2}', '-\\frac{\\sqrt{3}}{2}'],
    315: ['\\frac{\\sqrt{2}}{2}', '-\\frac{\\sqrt{2}}{2}'], 330: ['\\frac{\\sqrt{3}}{2}', '-\\frac{1}{2}']
  };
  function l3ng(s) { return s === '0' ? '0' : (s.charAt(0) === '-' ? s.slice(1) : '-' + s); }
  function l3rotV(d) { var a = L3ANG[d]; return [[a[0], l3ng(a[1])], [a[1], a[0]]]; }
  function l3rotS(d) { return '\\begin{bmatrix}\\cos' + d + '^\\circ&-\\sin' + d + '^\\circ\\\\ \\sin' + d + '^\\circ&\\cos' + d + '^\\circ\\end{bmatrix}'; }
  var L3RTH = '\\begin{bmatrix}\\cos\\theta&-\\sin\\theta\\\\ \\sin\\theta&\\cos\\theta\\end{bmatrix}';

  /* ══ L3-1　二元一次含參數說「無解」：Δ=0 只是候選，一定要代回去分辨平行與重合 ══
     係數方陣兩格含 a ⟹ det 是 a 的二次式，兩根都是候選；
     常數行由「無限多組解的那個根」釘死（在該根處兩列成比例且常數項也對上）。 */
  var L31T = (function () {
    var RT = [], out = [], NS = [-6, -5, -4, -3, -2, -1, 1, 2, 3, 4, 5, 6], DS = [1, 2, 3], i, j;
    for (i = 0; i < NS.length; i++) for (j = 0; j < DS.length; j++) if (gcd(Math.abs(NS[i]), DS[j]) === 1) RT.push([NS[i], DS[j]]);
    var e, L, M, N, al, ga, be, de, P, q, w, cnt;
    for (i = 0; i < RT.length; i++) for (j = i + 1; j < RT.length; j++) {
      if (RT[i][0] * RT[j][1] === RT[j][0] * RT[i][1]) continue;
      if (RT[i][1] * RT[j][1] > 6) continue;
      for (e = -1; e <= 1; e += 2) {
        L = e * RT[i][1] * RT[j][1];
        M = -e * (RT[i][0] * RT[j][1] + RT[j][0] * RT[i][1]);
        N = e * RT[i][0] * RT[j][0];
        cnt = 0;
        for (al = -3; al <= 3 && cnt < 6; al++) {
          if (al === 0 || L % al !== 0) continue;
          ga = L / al;
          if (Math.abs(ga) > 3) continue;
          for (be = -6; be <= 6 && cnt < 6; be++) {
            if ((M - be * ga) % al !== 0) continue;
            de = (M - be * ga) / al;
            if (Math.abs(de) > 6) continue;
            P = be * de - N;
            if (P === 0) continue;
            for (q = -9; q <= 9 && cnt < 6; q++) {
              if (q === 0 || P % q !== 0) continue;
              w = P / q;
              if (Math.abs(w) > 9) continue;
              out.push([RT[i][0], RT[i][1], RT[j][0], RT[j][1], al, be, ga, de, q, w]);
              cnt++;
            }
          }
        }
      }
    }
    return out;
  })();
  L3.noSolTwoParam = function (r) {
    r();
    var t, r1, r2, al, be, ga, de, q, w, rInf, rNo, lam, s, b1, b2, tr = 0, ok = false;
    var swapRoot = r.int(0, 1);
    do {
      t = r.pick(L31T);
      r1 = F(t[0], t[1]); r2 = F(t[2], t[3]);
      al = t[4]; be = t[5]; ga = t[6]; de = t[7]; q = t[8]; w = t[9];
      rInf = swapRoot ? r1 : r2; rNo = swapRoot ? r2 : r1;
      lam = Fr.div(F(w), Fr.add(Fr.mul(F(al), rInf), F(be)));
      s = r.pick([1, -1, 2, -2]);
      b1 = lam.d * s; b2 = lam.n * s;
      ok = Math.abs(b1) <= 14 && Math.abs(b2) <= 14 && b1 !== 0;
      tr++;
    } while (!ok && tr < 300);
    if (!ok) { r1 = F(3); r2 = F(-7, 3); rInf = r1; rNo = r2; al = -1; be = 1; ga = 3; de = 1; q = 5; w = -4; b1 = 1; b2 = 2; }
    var v = r.int(0, 2), ori = r.int(0, 1), sw = r.int(0, 1);
    var A = ori ? [[q, l3la(al, be)], [l3la(ga, de), w]] : [[l3la(al, be), q], [w, l3la(ga, de)]];
    var bb = [b1, b2];
    if (sw) { A = [A[1], A[0]]; bb = [b2, b1]; }
    var sg = (ori ? -1 : 1) * (sw ? -1 : 1);
    var QL = sg * al * ga, QM = sg * (al * de + be * ga), QN = sg * (be * de - q * w);
    var lo = Fr.cmp(r1, r2) < 0 ? r1 : r2, hi = Fr.cmp(r1, r2) < 0 ? r2 : r1;
    var sub = function (a) {
      var M2 = ori ? [[F(q), Fr.add(Fr.mul(F(al), a), F(be))], [Fr.add(Fr.mul(F(ga), a), F(de)), F(w)]]
                   : [[Fr.add(Fr.mul(F(al), a), F(be)), F(q)], [F(w), Fr.add(Fr.mul(F(ga), a), F(de))]];
      return sw ? [M2[1], M2[0]] : M2;
    };
    var head = '設 ' + T('a') + ' 為實數，' + T('x') + '、' + T('y') + ' 的方程組 ' + T(l3bm(A) + l3cv(L3VS2) + '=' + l3cv(bb));
    var hb = '先算係數行列式：' + T('\\Delta=' + l3vm(A) + '=' + l3quad(QL, QM, QN)) + '。'
           + T('\\Delta\\ne0') + ' 時必有唯一解 ⟹ 候選只能從 ' + T('\\Delta=0') + ' 的根裡面找；'
           + '但 ' + T('\\Delta=0') + ' 底下還藏著「無解」與「無限多組解」兩種，<b>一定要把每個根代回原方程組</b>，'
           + '比較兩式的係數比與常數比：比值完全一致就是兩式重合（無限多組解），係數比一致而常數比不一致就是平行不重合（無解）。'
           + (v === 2 ? '' : '本題兩個根是 ' + T('a=' + Fr.tex(lo)) + ' 與 ' + T('a=' + Fr.tex(hi)) + '，'
                            + '例如 ' + T('a=' + Fr.tex(lo)) + ' 時方程組成為 ' + T(l3cases(sub(lo), bb, L3VS2)) + '，先看這一組。');
    var pp = { A: [[l3E(A[0][0]), l3E(A[0][1])], [l3E(A[1][0]), l3E(A[1][1])]], b: bb, v: v };
    if (v === 1) {
      pp.ans = l3fp(rInf);
      return { q: head + ' 有無限多組解，求 ' + T('a') + '。', a: T('a=' + Fr.tex(rInf)), h: hb, p: pp };
    }
    if (v === 2) {
      pp.ans = [l3fp(lo), l3fp(hi), l3fp(rNo)];
      return { q: head + '。' + l3no(1) + '求使 ' + T('\\Delta=0') + ' 的所有 ' + T('a') + ' 值。' + l3no(2) + '上述各值之中，哪一個使方程組無解？',
               a: l3jo([l3no(1) + T('a=' + Fr.tex(lo)) + ' 或 ' + T('a=' + Fr.tex(hi)), l3no(2) + T('a=' + Fr.tex(rNo))]), h: hb, p: pp };
    }
    pp.ans = l3fp(rNo);
    return { q: head + ' 無解，求 ' + T('a') + '。', a: T('a=' + Fr.tex(rNo)), h: hb, p: pp };
  };

  /* ══ L3-2　增廣矩陣化到最後一列全零：只剩兩條有效方程式，往下消一次再往上消一次 ══ */
  L3.augZeroRow = function (r) {
    r();
    var a, c, b, d, m1, m2, m3, m4, m5, rows, tr = 0, ok = false, i, j2;
    do {
      a = r.nz(-4, 4); c = r.nz(-4, 4); b = r.nz(-9, 9); d = r.nz(-9, 9);
      m1 = r.nz(-3, 3); m2 = r.int(1, 3); m3 = r.nz(-4, 4); m4 = r.int(1, 3); m5 = r.nz(-4, 4);
      rows = [[1, m1], [m2, m3], [m4, m5]];
      ok = true;
      for (i = 0; i < 3; i++) {
        j2 = (i + 1) % 3;
        if (rows[i][0] * rows[j2][1] - rows[i][1] * rows[j2][0] === 0) ok = false;
      }
      if (ok) for (i = 0; i < 3; i++) {
        if (Math.abs(rows[i][0] * a + rows[i][1] * c) > 14) ok = false;
        if (Math.abs(rows[i][0] * b + rows[i][1] * d) > 34) ok = false;
      }
      tr++;
    } while (!ok && tr < 400);
    if (!ok) { a = 1; c = 1; b = 3; d = 2; m1 = 2; rows = [[1, 2], [2, 5], [1, 3]]; }
    var A = rows.map(function (u) { return [u[0], u[1], u[0] * a + u[1] * c]; });
    var bv = rows.map(function (u) { return u[0] * b + u[1] * d; });
    var v = r.int(0, 2);
    var ech = l3agm([[1, 0, 'a'], [0, 1, 'c'], [0, 0, 0]], ['b', 'd', 0]);
    var head = '聯立方程式 ' + T(l3cases(A, bv)) + ' 的增廣矩陣經列運算後化為 ' + T(ech) + '。';
    var hb = '目標形狀已經寫在題目上：前兩行要變成單位方陣，所以只要「往下消一次、往上消一次」就結束，不必真的去解方程組。'
           + '原增廣矩陣是 ' + T(l3agm(A, bv)) + '；先用第一列把第二、三列的 ' + T('x') + ' 消掉，'
           + '第三列會整列變成 ' + T('(0,\\,0,\\,0\\mid 0)') + ' ⟹ 第三式並沒有提供新資訊，只剩兩條有效方程式。'
           + '再把第二列的 ' + T(m1) + ' 倍從第一列減掉（往上消），第三行與常數行就可以直接對照讀出來。'
           + '判斷有無限多組解時，要同時確認常數項那一格也是 ' + T(0) + '，否則會出現 ' + T('0=k') + ' 的矛盾而變成無解。';
    var pp = { A: A, b: bv, v: v };
    if (v === 1) {
      pp.ans = [a, b, c, d];
      return { q: head + '求 ' + T('(a,b,c,d)') + '。', a: T('(a,b,c,d)=(' + [a, b, c, d].join(',') + ')'), h: hb, p: pp };
    }
    if (v === 2) {
      pp.ans = [a + b + c + d, [-a, b], [-c, d]];
      return { q: head + l3no(1) + '求 ' + T('a+b+c+d') + '。' + l3no(2) + '令 ' + T('z=t') + '，把所有的解寫成參數式。',
               a: l3jo([l3no(1) + T('a+b+c+d=' + (a + b + c + d)), l3no(2) + T(l3ptex([-a, -c, 1], [b, d, 0])) + '，' + T('t') + ' 為實數']), h: hb, p: pp };
    }
    pp.ans = a + b + c + d;
    return { q: head + '求 ' + T('a+b+c+d') + '。', a: T('a+b+c+d=' + (a + b + c + d)), h: hb, p: pp };
  };

  /* ══ L3-3　汙損的增廣矩陣＋最後化成單位矩陣：列運算保解，把解代回原來的每一列 ══ */
  L3.augBlurred = function (r) {
    r();
    var x, A, bv, slots, hid, tr = 0, ok = false, i, L = ['a', 'b', 'c'], nc;
    do {
      ok = true;
      x = [r.nz(-4, 4), r.nz(-4, 4), r.nz(-4, 4)];
      A = [[1, r.nz(-5, 5), r.nz(-5, 5)], [0, 1, r.nz(-6, 6)], [0, r.nz(-6, 6), r.nz(-6, 6)]];
      if (Fr.num(l3det3(l3MF(A))) === 0) { ok = false; continue; }
      bv = A.map(function (u) { return u[0] * x[0] + u[1] * x[1] + u[2] * x[2]; });
      slots = [r.pick([1, 2, 3]), r.pick([2, 3]), r.pick([1, 2, 3])];
      nc = 0;
      for (i = 0; i < 3; i++) if (slots[i] < 3) nc++;
      if (nc < 2) { ok = false; continue; }
      hid = [];
      for (i = 0; i < 3; i++) {
        hid.push(slots[i] < 3 ? A[i][slots[i]] : bv[i]);
        if (slots[i] < 3 && (Math.abs(hid[i]) > 9 || hid[i] === 0)) ok = false;
        if (slots[i] === 3 && Math.abs(hid[i]) > 22) ok = false;
        if (Math.abs(bv[i]) > 34) ok = false;
      }
      tr++;
    } while (!ok && tr < 500);
    if (!ok) { x = [2, 1, -1]; A = [[1, 3, 2], [0, 1, -4], [0, 5, 6]]; bv = [3, 5, -1]; slots = [2, 3, 2]; hid = [2, 5, 6]; }
    var sh = A.map(function (u, i2) { return u.map(function (val, j2) { return (slots[i2] === j2) ? L[i2] : val; }); });
    var sb = bv.map(function (val, i2) { return slots[i2] === 3 ? L[i2] : val; });
    var v = r.int(0, 2);
    /* 提示用第一列做示範：把解代進去之後只剩一個未知數 */
    var kn = 0, j;
    for (j = 0; j < 3; j++) if (slots[0] !== j) kn += A[0][j] * x[j];
    var dem;
    if (slots[0] === 3) dem = kn + '=a';
    else {
      var xv = x[slots[0]];
      dem = (kn === 0 ? (xv > 0 ? '' : '-') : kn + (xv > 0 ? '+' : '-')) + (Math.abs(xv) === 1 ? '' : Math.abs(xv)) + 'a=' + bv[0];
    }
    var head = '用矩陣列運算解某三元一次聯立方程式：' + T(l3agm(sh, sb) + '\\to\\cdots\\to' + l3agm([[1, 0, 0], [0, 1, 0], [0, 0, 1]], x))
             + '，其中 ' + T('a') + '、' + T('b') + '、' + T('c') + ' 三個數字被汙損。';
    var hb = '招式叫做「列運算保解」：列運算不會改變解，右邊的最簡階梯形直接告訴我們 ' + T('x=' + x[0]) + '、' + T('y=' + x[1]) + '、' + T('z=' + x[2]) + '。'
           + '把 ' + T('(x,y,z)=(' + x.join(',') + ')') + ' 代進左邊的<b>每一列</b>，一列就是一條只含一個未知數的一次方程式。'
           + '例如第一列 ' + T(l3rowEq(sh[0], sb[0])) + '，代入後成為 ' + T(dem) + '；第二、三列同樣各解一次。'
           + '看到「經一系列列運算化為⋯⋯」不要急著模擬那一串運算，先問自己：兩邊的方程組同解嗎？同解就把解拿來當橋樑。';
    var pp = { sh: sh.map(function (u) { return u.map(String); }), sb: sb.map(String), x: x, v: v };
    if (v === 1) {
      pp.ans = hid[0] + hid[1] + hid[2];
      return { q: head + '求 ' + T('a+b+c') + '。', a: T('a+b+c=' + (hid[0] + hid[1] + hid[2])), h: hb, p: pp };
    }
    if (v === 2) {
      pp.ans = [hid.slice(), hid[0] * hid[1] * hid[2]];
      return { q: head + l3no(1) + '求 ' + T('(a,b,c)') + '。' + l3no(2) + '求 ' + T('abc') + ' 之值。',
               a: l3jo([l3no(1) + T('(a,b,c)=(' + hid.join(',') + ')'), l3no(2) + T('abc=' + (hid[0] * hid[1] * hid[2]))]), h: hb, p: pp };
    }
    pp.ans = hid.slice();
    return { q: head + '求 ' + T('(a,b,c)') + '。', a: T('(a,b,c)=(' + hid.join(',') + ')'), h: hb, p: pp };
  };

  /* ══ L3-4　三元一次含參數說「無解」：Δ=0 找候選，再用列運算看會不會冒出 0＝非零 ══ */
  L3.noSolThreeParam = function (r) {
    r();
    var R1, R2, k1, k2, j, u, w, a0, tgt, cr, tr = 0, ok = false, i;
    do {
      ok = true;
      R1 = [r.nz(-3, 3), r.nz(-3, 3), r.nz(-3, 3)];
      R2 = [r.nz(-3, 3), r.nz(-4, 4), r.nz(-4, 4)];
      cr = [R1[1] * R2[2] - R1[2] * R2[1], R1[2] * R2[0] - R1[0] * R2[2], R1[0] * R2[1] - R1[1] * R2[0]];
      k1 = r.nz(-2, 2); k2 = r.nz(-2, 2);
      j = r.int(0, 2);
      if (cr[j] === 0) { ok = false; continue; }
      u = r.pick([1, 1, 1, 2, -1]); w = r.int(-6, 6);
      tgt = k1 * R1[j] + k2 * R2[j];
      if ((tgt - w) % u !== 0) { ok = false; continue; }
      a0 = (tgt - w) / u;
      if (Math.abs(a0) > 12 || a0 === 0) { ok = false; continue; }
      for (i = 0; i < 3; i++) if (Math.abs(k1 * R1[i] + k2 * R2[i]) > 12) ok = false;
      tr++;
    } while (!ok && tr < 600);
    if (!ok) { R1 = [2, 1, -3]; R2 = [-2, 5, 1]; k1 = 1; k2 = 1; j = 2; u = 1; w = 0; a0 = -4; tgt = 0; }
    var R3 = [k1 * R1[0] + k2 * R2[0], k1 * R1[1] + k2 * R2[1], k1 * R1[2] + k2 * R2[2]];
    var v = r.int(0, 2);
    var b1 = r.int(-8, 8), b2 = r.int(-8, 8), e = (v === 1) ? 0 : r.nz(-4, 4);
    var b3 = k1 * b1 + k2 * b2 + e;
    var SH = [R1.slice(), R2.slice(), R3.slice()];
    SH[2][j] = l3la(u, w);
    var bb = [b1, b2, b3];
    var head = '已知 ' + T('x') + '、' + T('y') + '、' + T('z') + ' 的方程組 ' + T(l3bm(SH) + l3cv(L3VS3) + '=' + l3cv(bb));
    var hb = T('\\Delta\\ne0') + ' ⟹ 三平面交於一點 ⟹ 必有唯一解，所以「無解」與「無限多組解」都只能發生在 ' + T('\\Delta=0') + '，先把 ' + T('\\Delta') + ' 算出來。'
           + '本題只有一格含 ' + T('a') + '，' + T('\\Delta') + ' 對 ' + T('a') + ' 是一次式：做 '
           + T('R_3' + (k1 > 0 ? '-' : '+') + (Math.abs(k1) === 1 ? '' : Math.abs(k1)) + 'R_1' + (k2 > 0 ? '-' : '+') + (Math.abs(k2) === 1 ? '' : Math.abs(k2)) + 'R_2')
           + ' 之後，第三列的左邊只剩第 ' + T(j + 1) + ' 行的 ' + T(l3sub(l3la(u, w), tgt)) + ' 一格 ⟹ 候選值只有一個。'
           + '求出候選值之後<b>務必代回去做列運算</b>：常數行用同一組合算出來是 ' + T(l3linf([k1, k2], ['b_1', 'b_2']) + '=' + (k1 * b1 + k2 * b2))
           + '，拿它和第三式的常數 ' + T(b3) + ' 比一比——一樣就是無限多組解，不一樣就會冒出 ' + T('0=' + e) + ' 這種矛盾。';
    var pp = { A: SH.map(function (row) { return row.map(String); }), b: bb, v: v };
    if (v === 1) {
      pp.ans = a0;
      return { q: head + ' 有無限多組解，求 ' + T('a') + '。', a: T('a=' + a0), h: hb, p: pp };
    }
    if (v === 2) {
      pp.ans = [a0, a0];
      return { q: head + '。' + l3no(1) + '求使方程組恰有一組解的 ' + T('a') + ' 值範圍。' + l3no(2) + '求使方程組無解的 ' + T('a') + '。',
               a: l3jo([l3no(1) + T('a\\ne' + a0), l3no(2) + T('a=' + a0)]), h: hb, p: pp };
    }
    pp.ans = a0;
    return { q: head + ' 無解，求 ' + T('a') + '。', a: T('a=' + a0), h: hb, p: pp };
  };

  /* ══ L3-5　工作效率：設「每小時完成的比例」，三句話變三條一次方程式 ══ */
  var L35C = [
    { h: '某工廠有甲、乙、丙三條生產線', o: '這批訂單', vb: '開動', w: '生產線' },
    { h: '某水池有甲、乙、丙三支進水管', o: '注水的工作', vb: '開啟', w: '水管' },
    { h: '某辦公室有甲、乙、丙三台影印機', o: '這批文件', vb: '開動', w: '影印機' },
    { h: '某工地有甲、乙、丙三部機具', o: '這項工程', vb: '開動', w: '機具' }
  ];
  var L35T = (function () {
    var out = [], A, B, C, L, D, k, s3, s2;
    function lc(m, n) { return m / gcd(m, n) * n; }
    for (A = 1; A <= 6; A++) for (B = 1; B <= 6; B++) for (C = 1; C <= 6; C++) {
      if (gcd(A, gcd(B, C)) !== 1) continue;
      if (A === B || B === C || A === C) continue;      /* 三者效率相同會讓條件看起來很怪 */
      s3 = A + B + C; s2 = B + C;
      L = lc(s3, s2);
      for (k = 1; k <= 12; k++) {
        D = L * k;
        if (D > 600 || D / s3 < 2 || D / s2 > 200) continue;
        if (D % A !== 0 || D % B !== 0 || D % C !== 0) continue;
        out.push([A, B, C, D]);
      }
    }
    return out;
  })();
  L3.workRate3 = function (r) {
    r();
    var e, A, B, C, D, T3s, T3, T4, m, tr = 0, ok = false;
    var v = r.int(0, 2), form = r.int(0, 1);
    do {
      e = r.pick(L35T); A = e[0]; B = e[1]; C = e[2]; D = e[3];
      ok = true;
      if (v === 2 || form === 1) ok = (D % (A + C) === 0) && (D / (A + C) >= 2);
      if (ok) {
        T3s = [];
        for (m = 1; m * A < D; m++) if ((D - m * A) % C === 0 && (D - m * A) / C <= 250 && m <= 250) T3s.push(m);
        ok = T3s.length > 0;
      }
      tr++;
    } while (!ok && tr < 400);
    if (!ok) { A = 3; B = 2; C = 1; D = 60; T3s = [10]; form = 0; }
    T3 = r.pick(T3s); T4 = (D - T3 * A) / C;
    var ct = r.pick(L35C), T1 = D / (A + B + C), T2 = D / (B + C), T5 = (D % (A + C) === 0) ? D / (A + C) : 0;
    var c3 = form === 1
      ? '若只' + ct.vb + '甲、丙，需 ' + T(T5) + ' 小時完成'
      : '若只' + ct.vb + '甲 ' + T(T3) + ' 小時，再' + ct.vb + '丙 ' + T(T4) + ' 小時，恰好完成';
    var head = ct.h + '，現欲完成' + ct.o + '（各' + ct.w + '的工作效率均固定）。'
             + '若甲、乙、丙同時' + ct.vb + '，需 ' + T(T1) + ' 小時完成；'
             + '若只' + ct.vb + '乙、丙，需 ' + T(T2) + ' 小時完成；' + c3 + '。';
    var eqs = form === 1
      ? '\\begin{cases}' + l3rws([T1 + '(x+y+z)=1', T2 + '(y+z)=1', T5 + '(x+z)=1']) + '\\end{cases}'
      : '\\begin{cases}' + l3rws([T1 + '(x+y+z)=1', T2 + '(y+z)=1', l3linf([T3, 0, T4], L3VS3) + '=1']) + '\\end{cases}';
    var hb = '不要設「時間」當未知數（式子會變成一堆倒數而不是一次式），要設甲、乙、丙<b>每小時各完成整批工作的 '
           + T('x') + '、' + T('y') + '、' + T('z') + '</b>。這樣「時間乘以效率」就是完成的比例，三句話各給一條一次方程式：' + T(eqs) + '。'
           + (v === 1 ? '把前兩式化成 ' + T('x+y+z=\\dfrac{1}{' + T1 + '}') + ' 與 ' + T('y+z=\\dfrac{1}{' + T2 + '}') + ' 再相減，就會一口氣消掉 ' + T('y') + '、' + T('z') + '；'
                      : '把前兩式化成 ' + T('x+y+z=\\dfrac{1}{' + T1 + '}') + ' 與 ' + T('y+z=\\dfrac{1}{' + T2 + '}') + ' 再相減得 ' + T('x=\\dfrac{1}{' + T1 + '}-\\dfrac{1}{' + T2 + '}=' + Fr.tex(F(A, D))) + '；')
           + '代進第三式解出剩下的未知數，最後別忘了「單獨完成需幾小時」是效率的<b>倒數</b>。';
    var pp = { T1: T1, T2: T2, T3: T3, T4: T4, T5: T5, form: form, v: v };
    if (v === 1) {
      pp.ans = [[A, D], D / C];
      return { q: head + l3no(1) + '求甲每小時完成的比例。' + l3no(2) + '問只' + ct.vb + '丙，需幾小時完成？',
               a: l3jo([l3no(1) + T(Fr.tex(F(A, D))), l3no(2) + T(D / C) + ' 小時']), h: hb, p: pp };
    }
    if (v === 2) {
      pp.ans = [D / B, D / (A + C)];
      return { q: head + l3no(1) + '問只' + ct.vb + '乙，需幾小時完成？' + l3no(2) + '問只' + ct.vb + '甲、丙，需幾小時完成？',
               a: l3jo([l3no(1) + T(D / B) + ' 小時', l3no(2) + T(D / (A + C)) + ' 小時']), h: hb, p: pp };
    }
    var who = r.pick(['乙', '丙']), val = who === '乙' ? D / B : D / C;
    pp.ans = val; pp.who = who;
    return { q: head + '問只' + ct.vb + who + '，需幾小時完成？', a: T(val) + ' 小時', h: hb, p: pp };
  };

  /* ══ L3-6　X 同時出現在兩邊：先提出 (A-kI)X=B，注意提出來的是 kI 不是純數字 k ══ */
  L3.matEqShift = function (r) {
    r();
    var C, dC, k, A, B, tr = 0;
    do { C = [[r.int(-4, 4), r.int(-4, 4)], [r.int(-4, 4), r.int(-4, 4)]]; dC = C[0][0] * C[1][1] - C[0][1] * C[1][0]; tr++; }
    while (Math.abs(dC) !== 1 && tr < 400);
    if (Math.abs(dC) !== 1) { C = [[0, 1], [1, 2]]; dC = -1; }
    k = r.nz(-3, 3);
    A = [[C[0][0] + k, C[0][1]], [C[1][0], C[1][1] + k]];
    B = [[r.int(-5, 5), r.int(-5, 5)], [r.int(-5, 5), r.int(-5, 5)]];
    var v = r.int(0, 2), CF = l3MF(C), IV = l3inv2(CF);
    var X = (v === 2) ? l3mul(l3MF(B), IV) : l3mul(IV, l3MF(B));
    var eq = (v === 2 ? 'XA=' : 'AX=') + l3kX(k) + '+B';
    var sum = Fr.add(Fr.add(X[0][0], X[0][1]), Fr.add(X[1][0], X[1][1]));
    var head = '設 ' + T('A=' + l3bm(A)) + '、' + T('B=' + l3bm(B)) + ' 滿足 ' + T(eq) + '。';
    var hb = '先把 ' + T('X') + ' 移到同一邊提出來：' + T(v === 2 ? 'X(' + l3AkI(k) + ')=B' : '(' + l3AkI(k) + ')X=B')
           + '——提出來的是 ' + T(l3AkI(k)) + ' 而不是 ' + T(l3Ak(k)) + '，矩陣只能和同階矩陣相加減，看到「矩陣 ' + T('\\pm') + ' 純數字」就自動補上 ' + T('I') + '。'
           + '本題 ' + T(l3AkI(k) + '=' + l3bm(C)) + '，' + T('\\det(' + l3AkI(k) + ')=' + dC) + ' 不為 ' + T(0) + ' ⟹ 可逆，'
           + T('(' + l3AkI(k) + ')^{-1}=' + l3bm(IV)) + '。'
           + (v === 2 ? '注意 ' + T('X') + ' 在左邊 ⟹ 反方陣要<b>右乘</b>：' + T('X=B(' + l3AkI(k) + ')^{-1}') + '，寫成左乘就錯了。'
                      : '注意 ' + T('X') + ' 在右邊 ⟹ 反方陣要<b>左乘</b>：' + T('X=(' + l3AkI(k) + ')^{-1}B') + '，寫成 ' + T('B(' + l3AkI(k) + ')^{-1}') + ' 就錯了。');
    var pp = { A: A, B: B, k: k, v: v };
    if (v === 0) {
      pp.ans = l3fp(sum);
      return { q: head + '若 ' + T('X=' + l3bm([['a', 'b'], ['c', 'd']])) + '，求 ' + T('a+b+c+d') + '。',
               a: T('a+b+c+d=' + Fr.tex(sum)), h: hb, p: pp };
    }
    pp.ans = X.map(function (u) { return u.map(l3fp); });
    return { q: head + '求二階方陣 ' + T('X') + '。', a: T('X=' + l3bm(X)), h: hb, p: pp };
  };

  /* ══ L3-7　「自己就是自己的反方陣」：兩邊乘 A 得 A^2=I（或 -I），逐格比對 ══ */
  var L37T = (function () {
    var out = [], p, q, a, num, mode;
    for (mode = 0; mode <= 1; mode++) for (p = -6; p <= 6; p++) {
      if (mode === 0 && Math.abs(p) < 2) continue;
      for (q = -9; q <= 9; q++) {
        if (q === 0) continue;
        num = mode === 0 ? (1 - p * p) : -(p * p + 1);
        if (num % q !== 0) continue;
        a = num / q;
        if (Math.abs(a) > 12 || a === 0) continue;
        out.push([mode, p, q, a]);
      }
    }
    return out;
  })();
  L3.selfInverse = function (r) {
    r();
    var v = r.int(0, 2), pos = r.int(0, 3), e, tr = 0;
    do { e = r.pick(L37T); tr++; } while (((v === 2) !== (e[0] === 1)) && tr < 500);
    var mode = e[0], p = e[1], q = e[2], av = e[3];
    var M, ansA, ansB;
    if (pos === 0) { M = [[p, 'a'], [q, 'b']]; ansA = av; ansB = -p; }
    else if (pos === 3) { M = [[p, q], ['a', 'b']]; ansA = av; ansB = -p; }
    else if (pos === 1) { M = [['a', q], ['b', p]]; ansA = -p; ansB = av; }
    else { M = [['a', 'b'], [q, p]]; ansA = -p; ansB = av; }
    var dv = (mode === 0) ? -1 : 1;
    var cond = (mode === 0) ? (r.int(0, 1) ? 'A=A^{-1}' : 'A^{-1}=A') : 'A^{-1}=-A';
    var sq = (mode === 0) ? 'A^2=I' : 'A^2=-I';
    var fac = M[0][1], s12 = (typeof M[0][0] === 'string') ? l3plus(String(M[0][0]), M[1][1]) : l3plus(String(M[1][1]), M[0][0]);
    var head = '若 ' + T('a') + '、' + T('b') + ' 為實數，' + T('A=' + l3bm(M)) + ' 且 ' + T(cond) + '。';
    var hb = '兩邊同時乘 ' + T('A') + '：' + T(cond) + ' ⟹ ' + T(sq) + '，接著把 ' + T('A^2') + ' 乘開，逐格與 ' + T(mode === 0 ? 'I' : '-I') + ' 比較。'
           + T('A^2') + ' 的 ' + T('(1,2)') + ' 格乘開後是 ' + T(l3E(fac) + '\\left(' + s12 + '\\right)') + '，而它必須等於 ' + T(0) + ' ⟹ 先定出其中一個未知數。'
           + '另一條更快的路是用行列式：' + T(sq) + ' ⟹ ' + T('(\\det A)^2=\\det(' + (mode === 0 ? 'I' : '-I') + ')=1') + '，再由 ' + T(cond) + ' 本身比對可知 ' + T('\\det A=' + dv) + '，'
           + '把 ' + T('\\det A=' + l3vm(M) + '=' + dv) + ' 展開就解得出剩下那一個；最後記得回頭檢查對角線的另一格是否也成立。';
    var pp = { M: [[String(M[0][0]), String(M[0][1])], [String(M[1][0]), String(M[1][1])]], cond: cond, v: v };
    if (v === 1) {
      pp.ans = [ansA, ansB, dv];
      return { q: head + l3no(1) + '求數對 ' + T('(a,b)') + '。' + l3no(2) + '求 ' + T('\\det A') + '。',
               a: l3jo([l3no(1) + T('(a,b)=(' + ansA + ',' + ansB + ')'), l3no(2) + T('\\det A=' + dv)]), h: hb, p: pp };
    }
    pp.ans = [ansA, ansB];
    return { q: head + '求數對 ' + T('(a,b)') + '。', a: T('(a,b)=(' + ansA + ',' + ansB + ')'), h: hb, p: pp };
  };

  /* ══ L3-8　矩陣的運算律：分配律與結合律都對，會出事的只有「交換」與「消去」 ══ */
  var L38S = [
    ['$A(B+C)=AB+AC$', 1, 'dist'], ['$(B+C)A=BA+CA$', 1, 'dist'], ['$(AB)C=A(BC)$', 1, 'dist'],
    ['$A^3-I=(A-I)(A^2+A+I)$', 1, 'comm'], ['$(A+I)^2=A^2+2A+I$', 1, 'comm'], ['$A^2-I=(A-I)(A+I)$', 1, 'comm'],
    ['$\\det(AB)=\\det(BA)$', 1, 'det'], ['若 $AB=BA$，則 $(A+B)^2=A^2+2AB+B^2$', 1, 'comm'],
    ['$(A+B)^2=A^2+AB+BA+B^2$', 1, 'comm'], ['若 $A$、$B$ 皆可逆，則 $(AB)^{-1}=B^{-1}A^{-1}$', 1, 'inv'],
    ['$(A+B)C=AC+BC$', 1, 'dist'], ['若 $AB=BA$，則 $A^2-B^2=(A+B)(A-B)$', 1, 'comm'],
    ['$A^2-B^2=(A+B)(A-B)$', 0, 'comm'], ['若 $A\\ne O$ 且 $AB=AC$，則 $B=C$', 0, 'cancel'],
    ['若 $A\\ne O$ 且 $B\\ne O$，則 $AB\\ne O$', 0, 'zero'], ['$(A+B)^2=A^2+2AB+B^2$', 0, 'comm'],
    ['$AB=BA$', 0, 'comm'], ['若 $A^2=O$，則 $A=O$', 0, 'sq'], ['$\\det(A+B)=\\det A+\\det B$', 0, 'det'],
    ['若 $A^2=A$，則 $A=O$ 或 $A=I$', 0, 'sq'], ['若 $A^2=I$，則 $A=I$ 或 $A=-I$', 0, 'sq'],
    ['若 $A$、$B$ 皆可逆，則 $(AB)^{-1}=A^{-1}B^{-1}$', 0, 'inv'], ['若 $AB=O$，則 $A=O$ 或 $B=O$', 0, 'zero'],
    ['若 $A\\ne O$，則 $A$ 必有乘法反方陣', 0, 'inv'], ['$(A+B)(A-B)=(A-B)(A+B)$', 0, 'comm'],
    ['若 $A^2=B^2$，則 $A=B$ 或 $A=-B$', 0, 'sq'], ['若 $A^2=B^2$，則 $A=B$', 0, 'sq']
  ];
  var L38K = ['dist', 'comm', 'cancel', 'zero', 'det', 'inv', 'sq'];
  L3.matLawPick = function (r) {
    r();
    var v = r.int(0, 2), n = (v === 2) ? 6 : 5, sel, hit, i, tr = 0, ok = false;
    do {
      sel = r.shuffle(L38S).slice(0, n);
      hit = [];
      for (i = 0; i < n; i++) if ((v === 1 ? 1 - sel[i][1] : sel[i][1]) === 1) hit.push(i + 1);
      ok = hit.length >= 1 && hit.length <= n - 1;
      tr++;
    } while (!ok && tr < 200);
    var head = '設 ' + T('A') + '、' + T('B') + '、' + T('C') + ' 均為 ' + T('n') + ' 階方陣（' + T('O') + ' 為 ' + T('n') + ' 階零方陣，'
             + T('I') + ' 為 ' + T('n') + ' 階單位方陣），下列 ' + T(n) + ' 個選項之中，'
             + (v === 1 ? '哪幾個<b>不一定</b>成立？' : '哪幾個<b>必</b>成立？') + '（把編號全部寫出來）<br>'
             + sel.map(function (u, i2) { return l3no(i2 + 1) + u[0]; }).join('　');
    var DESC = {
      dist: '直接逐格展開就能定案（分配律與結合律對矩陣恆成立，這一類不必找反例）',
      comm: '把兩邊完整展開，逐項比對有沒有偷偷把兩個矩陣交換位置——' + T('(A+B)(A-B)=A^2-AB+BA-B^2') + '，要收成 ' + T('A^2-B^2') + ' 必須 ' + T('AB=BA') + '；但另一個矩陣是 ' + T('I') + ' 或 ' + T('A') + ' 自己的多項式時就自動可交換',
      cancel: '消去律真正需要的是 ' + T('\\det A\\ne0') + '，光是 ' + T('A\\ne O') + ' 太弱',
      zero: '拿 ' + T(l3bm([[1, 0], [0, 0]])) + ' 與 ' + T(l3bm([[0, 0], [0, 1]])) + ' 這一組試試看：兩個都不是零方陣，乘起來卻是 ' + T('O'),
      det: '行列式的<b>乘法</b>性質可以用，加法可不行',
      inv: '反方陣的順序（先穿襪子再穿鞋，就要先脫鞋再脫襪子），以及「是不是每個非零方陣都有反方陣」',
      sq: '由「平方之後的結果」反推矩陣本身，答案通常不唯一——試試 ' + T(l3bm([[1, 0], [0, -1]])) + ' 與 ' + T(l3bm([[0, 1], [0, 0]]))
    };
    var groups = [], g, kk, idx;
    for (kk = 0; kk < L38K.length; kk++) {
      idx = [];
      for (i = 0; i < n; i++) if (sel[i][2] === L38K[kk]) idx.push(i + 1);
      if (idx.length) groups.push('第 ' + l3opt(idx) + ' 個：' + DESC[L38K[kk]]);
    }
    var hb = '矩陣乘法有結合律與分配律，<b>沒有</b>交換律與消去律；凡是把數字世界的公式直接搬過來的選項，都要先檢查展開的每一步。'
           + '本題 ' + T(n) + ' 個選項可以分成幾類各個擊破——' + groups.join('；') + '。'
           + '逐一檢查之後把' + (v === 1 ? '<b>不一定</b>成立的' : '必成立的') + '編號全部寫出來。';
    return { q: head, a: l3opt(hit), h: hb, p: { sel: sel.map(function (u) { return u[0]; }), want: (v === 1 ? 0 : 1), v: v, ans: hit } };
  };

  /* ══ L3-9　A^n=A 的最小 n：先乘兩三次找週期 ══ */
  var L39T = (function () {
    var out = [], fam = [[-1, 1], [0, 1], [1, 1], [0, -1]], i, tr, dt, a, d, bc, b, c;
    for (i = 0; i < fam.length; i++) {
      tr = fam[i][0]; dt = fam[i][1];
      for (a = -5; a <= 5; a++) {
        d = tr - a;
        if (Math.abs(d) > 5) continue;
        bc = a * d - dt;
        for (b = -6; b <= 6; b++) for (c = -6; c <= 6; c++) {
          if (b * c !== bc) continue;
          if (b === 0 && c === 0) continue;
          out.push([a, b, c, d]);
        }
      }
    }
    return out;
  })();
  L3.powPeriodMin = function (r) {
    r();
    var e, A, AF, per, i, tr = 0, ok = false;
    var v = r.int(0, 2);
    do {
      e = r.pick(L39T);
      A = [[e[0], e[1]], [e[2], e[3]]];
      AF = l3MF(A);
      per = 0;
      for (i = 1; i <= 12; i++) if (l3same(l3mpw(AF, i), l3id2())) { per = i; break; }
      ok = per >= (v === 0 ? 2 : (v === 2 ? 4 : 3)) && per <= 6;
      tr++;
    } while (!ok && tr < 400);
    if (!ok) { A = [[1, 3], [-1, -2]]; AF = l3MF(A); per = v === 2 ? 4 : 3; if (v === 2) A = [[0, -1], [1, 0]]; AF = l3MF(A); }
    var N = r.int(500, 1999);
    /* 避開 A^N 剛好等於 I 或 A 的無聊答案；v=2 還要避開和第一小題的 A^2 重複 */
    if (v === 1 && per >= 3) while (N % per <= 1) N++;
    if (v === 2) while (N % per <= 2) N++;
    var rem = N % per, PN = l3mpw(AF, rem === 0 ? per : rem);
    var A2 = l3mpw(AF, 2), A3 = l3mpw(AF, 3);
    var trA = A[0][0] + A[1][1], dtA = A[0][0] * A[1][1] - A[0][1] * A[1][0];
    var head = '設 ' + T('A=' + l3bm(A)) + '。';
    var hb = '乘冪題一律「先乘兩次看看」：' + (v === 2 ? T('A^3=' + l3bm(A3)) + '（先算 ' + T('A^2') + ' 再乘一次 ' + T('A') + '）'
                                                     : T('A^2=' + l3bm(A2)) + '，再乘一次得 ' + T('A^3'))
           + '。只要某一次方剛好變成 ' + T('I') + '，週期就定下來了，之後全部用<b>餘數</b>處理：'
           + (v === 0 ? T('A^n=A') + ' 等價於 ' + T('A^{n-1}=I') + '，也就是 ' + T('n-1') + ' 必須是週期的倍數。'
                      : '要算 ' + T('A^{' + N + '}') + ' 就把 ' + T(N) + ' 除以週期取餘數，餘數是幾就等於 ' + T('A') + ' 的幾次方（餘 ' + T(0) + ' 就是 ' + T('I') + '）。')
           + '看不出規律時還有一條保險路：任何二階方陣都滿足 ' + T('A^2=(a+d)A-(ad-bc)I') + '，本題 ' + T('a+d=' + trA) + '、' + T('ad-bc=' + dtA)
           + ' ⟹ ' + T('A^2=' + l3linf([trA, -dtA], ['A', 'I'])) + '，一直往下降冪就會看到週期。';
    var pp = { A: A, N: N, v: v };
    if (v === 1) {
      pp.ans = [per, PN.map(function (u) { return u.map(l3fp); })];
      return { q: head + l3no(1) + '求使 ' + T('A^m=I') + ' 的最小正整數 ' + T('m') + '。' + l3no(2) + '求 ' + T('A^{' + N + '}') + '。',
               a: l3jo([l3no(1) + T('m=' + per), l3no(2) + T('A^{' + N + '}=' + l3bm(PN))]), h: hb, p: pp };
    }
    if (v === 2) {
      pp.ans = [A2.map(function (u) { return u.map(l3fp); }), PN.map(function (u) { return u.map(l3fp); })];
      return { q: head + l3no(1) + '求 ' + T('A^2') + '。' + l3no(2) + '求 ' + T('A^{' + N + '}') + '。',
               a: l3jo([l3no(1) + T('A^2=' + l3bm(A2)), l3no(2) + T('A^{' + N + '}=' + l3bm(PN))]), h: hb, p: pp };
    }
    pp.ans = per + 1;
    return { q: head + '若 ' + T('n') + ' 為大於 ' + T(1) + ' 的正整數且 ' + T('A^n=A') + '，求 ' + T('n') + ' 的最小值。',
             a: T('n=' + (per + 1)), h: hb, p: pp };
  };

  /* ══ L3-10　對角線全 1、只有一格有東西：A^n 就是把那一格乘 n 倍，連加變等差級數 ══ */
  L3.shearSum = function (r) {
    r();
    var k = r.nz(-6, 6), up = r.int(0, 1), N = r.int(10, 40), v = r.int(0, 2);
    var A = up ? [[1, k], [0, 1]] : [[1, 0], [k, 1]];
    var S = N * (N + 1) / 2, off = k * S;
    var SM = up ? [[N, off], [0, N]] : [[N, 0], [off, N]];
    var nk = (k === 1 ? 'n' : (k === -1 ? '-n' : k + 'n'));
    var An = up ? [['1', nk], ['0', '1']] : [['1', '0'], [nk, '1']];
    var NN = up ? [[0, k], [0, 0]] : [[0, 0], [k, 0]];
    var cellName = up ? 'b' : 'c';
    var grid = l3bm([['a', 'b'], ['c', 'd']]);
    var head = '設 ' + T('A=' + l3bm(A)) + '。';
    var hb = '先算兩次：' + T('A^2=' + l3bm(l3mpw(l3MF(A), 2))) + '、' + T('A^3=' + l3bm(l3mpw(l3MF(A), 3)))
           + ' ⟹ 對角線永遠是 ' + T(1) + '，只有那一格在動，猜出通式之後用數學歸納法一行就驗完。'
           + (v === 1 ? '' : '也可以拆成 ' + T('A=I+N') + '，其中 ' + T('N=' + l3bm(NN)) + ' 滿足 ' + T('N^2=O') + '；'
                             + T('I') + ' 與 ' + T('N') + ' 可交換，二項式定理放心用，' + T('N^2') + ' 之後全是零 ⟹ ' + T('A^n=I+nN') + '。')
           + '矩陣的連加就是<b>逐格連加</b>：那一格是 ' + T((Math.abs(k) === 1 ? (k < 0 ? '-' : '') : k) + '(1+2+3+\\cdots+' + N + ')=' + (Math.abs(k) === 1 ? (k < 0 ? '-' : '') : k) + '\\times\\dfrac{' + N + '\\times' + (N + 1) + '}{2}')
           + '，其餘三格照抄（對角線各加 ' + T(N) + ' 個 ' + T(1) + '）。';
    var pp = { A: A, N: N, v: v };
    if (v === 1) {
      pp.ans = [nk, SM];
      return { q: head + l3no(1) + '求 ' + T('A^{n}') + '（用 ' + T('n') + ' 表示）。' + l3no(2) + '求 ' + T('A+A^2+A^3+\\cdots+A^{' + N + '}') + '。',
               a: l3jo([l3no(1) + T('A^n=' + l3bm(An)), l3no(2) + T(l3bm(SM))]), h: hb, p: pp };
    }
    if (v === 2) {
      pp.ans = 2 * N + off;
      return { q: head + '若 ' + T('A+A^2+A^3+\\cdots+A^{' + N + '}=' + grid) + '，求 ' + T('a+b+c+d') + '。',
               a: T('a+b+c+d=' + (2 * N + off)), h: hb, p: pp };
    }
    pp.ans = off;
    return { q: head + '若 ' + T('A+A^2+A^3+\\cdots+A^{' + N + '}=' + grid) + '，求實數 ' + T(cellName) + '。',
             a: T(cellName + '=' + off), h: hb, p: pp };
  };

  /* ══ L3-11　旋轉矩陣相乘＝角度相加，再變成同餘方程式 ══ */
  L3.rotCompose = function (r) {
    r();
    var v = r.int(0, 2), nrot = (v === 2) ? 3 : 2;
    var degs, th, phi, n, i, tr = 0, ok = false;
    var PH = [30, 45, 60, 90, 120, 135, 150, 180, 210, 225, 240, 270, 300, 315, 330];
    do {
      degs = []; th = 0;
      for (i = 0; i < nrot; i++) { degs.push(r.int(2, 17) * 5); th += degs[i]; }
      phi = (v === 1) ? 0 : r.pick(PH);
      n = 0;
      for (i = 1; i <= 360; i++) if ((i * th - phi) % 360 === 0) { n = i; break; }
      ok = n >= 2 && n <= 72 && th % 360 !== 0;
      tr++;
    } while (!ok && tr < 600);
    if (!ok) { degs = [18, 32]; th = 50; phi = 90; n = 9; }
    var md = ((th % 360) + 360) % 360;
    var head = '設 ' + T('A=' + degs.map(l3rotS).join('')) + '。';
    var hb = '記號 ' + T('R(\\theta)=' + L3RTH) + '。乘開後用和角公式可得 ' + T('R(\\alpha)R(\\beta)=R(\\alpha+\\beta)') + '——<b>旋轉的合成就是角度相加</b>。'
           + '本題 ' + T('A=R(' + degs.map(l3deg).join(')R(') + ')=R(' + l3deg(th) + ')') + (th >= 360 ? '，而角度要先對 ' + T(l3deg(360)) + ' 取餘數 ⟹ ' + T('A=R(' + l3deg(md) + ')') : '')
           + ' ⟹ ' + T('A^n=R(' + md + 'n^\\circ)') + '。'
           + '接下來是一條同餘方程式：把 ' + T(md + 'n') + ' 依序列出來 ' + T(md + ',\\,' + (2 * md) + ',\\,' + (3 * md) + ',\\,\\ldots') + '，'
           + '找第一個減掉 ' + T(360) + ' 的倍數之後等於目標角度的 ' + T('n') + ' 即可。要注意旋轉角是對 ' + T(l3deg(360)) + ' 取餘數，不是對 ' + T(l3deg(180)) + '。';
    var pp = { degs: degs, v: v };
    if (v === 1) {
      pp.ans = [md, n];
      return { q: head + l3no(1) + T('A') + ' 相當於以原點為中心逆時針旋轉幾度？' + l3no(2) + '求使 ' + T('A^m=I') + ' 的最小正整數 ' + T('m') + '。',
               a: l3jo([l3no(1) + T(l3deg(md)), l3no(2) + T('m=' + n)]), h: hb, p: pp };
    }
    pp.ans = n;
    return { q: head + '求使 ' + T('A^n=' + l3bm(l3rotV(phi))) + ' 的最小自然數 ' + T('n') + '。', a: T('n=' + n), h: hb, p: pp };
  };

  /* ══ L3-12　鏡射矩陣問對稱軸：軸上的點動都不動，解 A[x;y]=[x;y] ══ */
  var L312P = [[3, 4, 5], [4, 3, 5], [5, 12, 13], [12, 5, 13], [8, 15, 17], [15, 8, 17], [7, 24, 25], [24, 7, 25],
               [20, 21, 29], [21, 20, 29], [9, 40, 41], [40, 9, 41], [28, 45, 53], [45, 28, 53], [11, 60, 61], [60, 11, 61],
               [33, 56, 65], [56, 33, 65], [16, 63, 65], [63, 16, 65], [48, 55, 73], [55, 48, 73], [13, 84, 85], [84, 13, 85]];
  L3.reflAxis = function (r) {
    r();
    var tp = r.pick(L312P), s1 = r.sign(), s2 = r.sign(), v = r.int(0, 2);
    var cn = s1 * tp[0], sn = s2 * tp[1], hy = tp[2];
    var c2 = F(cn, hy), s2f = F(sn, hy);
    var A = [[c2, s2f], [s2f, Fr.neg(c2)]];
    var g = gcd(Math.abs(sn), hy + cn), pm = sn / g, qm = (hy + cn) / g;
    var axis = l3ln(pm, -qm);
    var pp = { A: [[l3E(A[0][0]), l3E(A[0][1])], [l3E(A[1][0]), l3E(A[1][1])]], v: v };
    var hb = '先確認它真的是鏡射：' + T('\\det A=' + l3vm(A) + '=-1') + '，而且 ' + T('A^2=' + l3bm(l3id2())) + '（照兩次鏡子回到原地）。'
           + '接著找<b>不動點</b>——對稱軸上的點鏡射之後還在原地，所以解 ' + T(l3bm(A) + l3cv(L3VS2) + '=' + l3cv(L3VS2)) + '，'
           + '也就是第一列 ' + T(l3linf([A[0][0], A[0][1]], L3VS2) + '=x') + ' 移項得 ' + T(l3linf([Fr.sub(A[0][0], F(1)), A[0][1]], L3VS2) + '=0') + '，整理成最簡整係數就是答案。'
           + '（第二列會化出同一條直線，兩列必然一致，剛好拿來驗算。）也可以背公式：以 ' + T('y=(\\tan\\theta)x') + ' 為軸的鏡射矩陣是 '
           + T(l3bm([['\\cos2\\theta', '\\sin2\\theta'], ['\\sin2\\theta', '-\\cos2\\theta']])) + '，本題 ' + T('\\cos2\\theta=' + l3E(c2)) + '、' + T('\\sin2\\theta=' + l3E(s2f))
           + '，再用 ' + T('\\tan\\theta=\\dfrac{\\sin2\\theta}{1+\\cos2\\theta}') + '；但<b>解不動點不必背公式，考場上更保險</b>。';
    if (v === 0) {
      var pool = [], i, j, gg;
      for (i = -6; i <= 6; i++) for (j = 1; j <= 6; j++) {
        if (i === 0) continue;
        gg = gcd(Math.abs(i), j);
        if (gg !== 1) continue;
        if (i === pm && j === qm) continue;
        if (i * qm === pm * j) continue;
        pool.push(l3ln(i, -j));
      }
      var opts = r.shuffle(pool).slice(0, 4);
      opts.push(axis);
      opts = r.shuffle(opts);
      var hit = opts.indexOf(axis) + 1;
      pp.opts = opts; pp.ans = hit;
      return { q: '若二階方陣的平面變換 ' + T(l3bm(A) + l3cv(L3VS2) + '=' + l3cv(["x'", "y'"])) + '，則點 ' + T('P(x,y)') + ' 與 ' + T("P'(x',y')")
                  + ' 必對稱於下列哪一條直線？<br>' + opts.map(function (u, i2) { return l3no(i2 + 1) + T(u); }).join('　'),
               a: l3no(hit) + T(axis), h: hb, p: pp };
    }
    if (v === 2) {
      pp.ans = [-1, axis];
      return { q: '設 ' + T('A=' + l3bm(A)) + ' 為坐標平面上的一個線性變換。' + l3no(1) + '求 ' + T('\\det A') + '。' + l3no(2) + T('A') + ' 是對哪一條直線的鏡射？請寫出該直線方程式。',
               a: l3jo([l3no(1) + T('\\det A=-1'), l3no(2) + T(axis)]), h: hb, p: pp };
    }
    pp.ans = axis;
    return { q: '已知 ' + T('A=' + l3bm(A)) + ' 是坐標平面上的一個鏡射變換，求它的對稱軸方程式。', a: T(axis), h: hb, p: pp };
  };

  /* ══ L3-13　只給兩組「原像→像」問面積倍率：倍率只看 |det M| ══ */
  L3.detAreaRatio = function (r) {
    r();
    var U, V, dU, dV, tr = 0, ok = false;
    do {
      U = [[r.nz(-5, 5), r.nz(-5, 5)], [r.nz(-5, 5), r.nz(-5, 5)]];
      dU = U[0][0] * U[1][1] - U[0][1] * U[1][0];
      V = [[r.nz(-5, 5), r.nz(-5, 5)], [r.nz(-5, 5), r.nz(-5, 5)]];
      dV = V[0][0] * V[1][1] - V[0][1] * V[1][0];
      ok = Math.abs(dU) === 1 && Math.abs(dV) >= 2 && Math.abs(dV) <= 9;
      tr++;
    } while (!ok && tr < 800);
    if (!ok) { U = [[3, 4], [7, 9]]; V = [[1, 3], [2, 1]]; dU = -1; dV = -5; }
    var dM = dV / dU, k = Math.abs(dM), v = r.int(0, 2);
    var u1 = [U[0][0], U[1][0]], u2 = [U[0][1], U[1][1]], v1 = [V[0][0], V[1][0]], v2 = [V[0][1], V[1][1]];
    var cond = '設 ' + T('M') + ' 為二階方陣，滿足 ' + T('M' + l3cv(u1) + '=' + l3cv(v1)) + '、' + T('M' + l3cv(u2) + '=' + l3cv(v2)) + '。';
    var hb = '面積伸縮率就是 ' + T('|\\det M|') + '，與被變換的圖形<b>完全無關</b>，所以不必去算任何一個點的像。'
           + '把兩個條件併成一個矩陣等式：' + T('M' + l3bm(U) + '=' + l3bm(V)) + '（左邊矩陣的兩行就是兩個原像，右邊就是兩個像），'
           + '再對兩邊取行列式並用乘法性質 ' + T('\\det\\left(M' + l3bm(U) + '\\right)=\\det M\\cdot' + l3vm(U)) + '：'
           + '本題 ' + T(l3vm(U) + '=' + dU) + '、' + T(l3vm(V) + '=' + dV) + '，一條一次方程式就解出 ' + T('\\det M') + '，完全不用把 ' + T('M') + ' 解出來。';
    var pp = { u1: u1, u2: u2, v1: v1, v2: v2, v: v };
    if (v === 2) {
      var P, Q, R2, ar, tr2 = 0;
      do {
        P = [r.int(-4, 4), r.int(-4, 4)]; Q = [r.int(-4, 4), r.int(-4, 4)]; R2 = [r.int(-4, 4), r.int(-4, 4)];
        ar = Math.abs((Q[0] - P[0]) * (R2[1] - P[1]) - (Q[1] - P[1]) * (R2[0] - P[0]));
        tr2++;
      } while (ar === 0 && tr2 < 200);
      if (ar === 0) { P = [0, 0]; Q = [2, 0]; R2 = [0, 3]; ar = 6; }
      var S1 = Fr.mul(F(ar, 2), F(k));
      pp.P = P; pp.Q = Q; pp.R = R2; pp.ans = [dM, l3fp(S1)];
      return { q: cond + '已知 ' + T('A(' + P.join(',') + ')') + '、' + T('B(' + Q.join(',') + ')') + '、' + T('C(' + R2.join(',') + ')') + '，且 '
                  + T('M') + ' 將 ' + T('\\triangle ABC') + ' 變換為 ' + T("\\triangle A'B'C'") + '。' + l3no(1) + '求 ' + T('\\det M') + '。' + l3no(2) + '求 ' + T("\\triangle A'B'C'") + ' 的面積。',
               a: l3jo([l3no(1) + T('\\det M=' + dM), l3no(2) + T(Fr.tex(S1))]), h: hb, p: pp };
    }
    if (v === 1) {
      pp.ans = k;
      return { q: cond + '若 ' + T('M') + ' 把坐標平面上任一個三角形變換成另一個三角形，且面積恆為原來的 ' + T('k') + ' 倍，求 ' + T('k') + '。',
               a: T('k=' + k), h: hb, p: pp };
    }
    var cand = [k], c2 = Math.max(1, k - 2);
    while (cand.length < 5) { if (cand.indexOf(c2) < 0) cand.push(c2); c2++; }
    cand = r.shuffle(cand);
    var hit2 = cand.indexOf(k) + 1;
    pp.opts = cand; pp.ans = hit2;
    return { q: cond + '已知 ' + T('M') + ' 將 ' + T('\\triangle ABC') + ' 變換為 ' + T("\\triangle A'B'C'") + '，且面積為原來的 ' + T('k') + ' 倍，求 ' + T('k') + '。<br>'
                + cand.map(function (u, i2) { return l3no(i2 + 1) + T(u); }).join('　'),
             a: l3no(hit2) + T('k=' + k), h: hb, p: pp };
  };

  /* ══ L3-14　轉移方陣：每一行的和是 1，兩期後就是 M^2X_0 ══ */
  var L314C = [
    { s: '店', w: '顧客', u: '個月', head: '甲店、乙店兩家飲料店同日開幕' },
    { s: '牌', w: '用戶', u: '個月', head: '某地的手機市場上只有甲牌、乙牌兩家業者' },
    { s: '案', w: '會員', u: '季', head: '某健身房只推出甲案、乙案兩種方案' },
    { s: '台', w: '觀眾', u: '個月', head: '某時段只有甲台、乙台兩個頻道' }
  ];
  var L314P = [F(1, 2), F(1, 3), F(2, 3), F(1, 4), F(3, 4), F(1, 5), F(2, 5), F(3, 5), F(4, 5), F(1, 6), F(5, 6), F(1, 10), F(3, 10), F(7, 10), F(2, 7), F(3, 8)];
  L3.transTwoStep = function (r) {
    r();
    var ct = r.pick(L314C), mA, mB, a0, tr = 0, ok = false;
    do {
      mA = r.pick(L314P); mB = r.pick(L314P); a0 = r.pick(L314P);
      ok = !Fr.eq(Fr.add(mA, mB), F(1)) && !Fr.eq(mA, mB);
      if (ok) ok = !Fr.eq(a0, Fr.div(mB, Fr.add(mA, mB)));
      tr++;
    } while (!ok && tr < 300);
    if (!ok) { mA = F(1, 2); mB = F(1, 3); a0 = F(1, 2); }
    var M = [[Fr.sub(F(1), mA), mB], [mA, Fr.sub(F(1), mB)]];
    var X0 = [a0, Fr.sub(F(1), a0)];
    var X1 = l3vec(M, X0), X2 = l3vec(M, X1);
    var v = r.int(0, 2), S = ct.s;
    var head = ct.head + '，初始市場占有率甲' + S + '為 ' + T(Fr.tex(a0)) + '、乙' + S + '為 ' + T(Fr.tex(X0[1])) + '。統計顯示：每' + ct.u
             + '甲' + S + '的' + ct.w + '有 ' + T(Fr.tex(mA)) + ' 會轉到乙' + S + '、其餘留在甲' + S + '；乙' + S + '的' + ct.w + '有 ' + T(Fr.tex(mB)) + ' 會轉到甲' + S + '、其餘留在乙' + S + '。';
    var hb = '狀態順序固定為（甲' + S + '，乙' + S + '）。轉移方陣的第一行＝「這一' + ct.u + '在甲' + S + '的人，下一' + ct.u + '分別去哪」，'
           + '所以<b>每一行的和必為 ' + T(1) + '</b>：' + T('M=' + l3bm(M)) + '（' + T(l3E(M[0][0]) + '+' + l3E(M[1][0]) + '=1') + '、' + T(l3E(M[0][1]) + '+' + l3E(M[1][1]) + '=1') + ' ✓）。'
           + '方向要特別小心：「甲的 ' + T(Fr.tex(mA)) + ' 跑去乙」放在第一行第二列（從甲到乙），不是第一列第二行。'
           + '兩期後就是 ' + T('X_2=M^2X_0=M(MX_0)') + '，用手乘兩次最快，不必求通式；'
           + (v === 1 ? '每算完一期就檢查「兩個分量相加是不是 ' + T(1) + '」，這是轉移方陣題最便宜的自我檢查。'
                      : '先算 ' + T('X_1=MX_0=' + l3cv(X1)) + '（兩個分量相加是 ' + T(1) + ' ✓），再乘一次 ' + T('M') + ' 即可。');
    var pp = { mA: l3fp(mA), mB: l3fp(mB), a0: l3fp(a0), v: v };
    if (v === 1) {
      pp.ans = [l3fp(X1[0]), l3fp(X2[1])];
      return { q: head + l3no(1) + '求一' + ct.u + '後甲' + S + '的市場占有率。' + l3no(2) + '求兩' + ct.u + '後乙' + S + '的市場占有率。（化為最簡分數）',
               a: l3jo([l3no(1) + T(Fr.tex(X1[0])), l3no(2) + T(Fr.tex(X2[1]))]), h: hb, p: pp };
    }
    if (v === 2) {
      pp.ans = [M.map(function (u) { return u.map(l3fp); }), l3fp(X2[0])];
      return { q: head + l3no(1) + '寫出轉移方陣 ' + T('M') + '（狀態順序為（甲' + S + '，乙' + S + '））。' + l3no(2) + '求兩' + ct.u + '後甲' + S + '的市場占有率。（化為最簡分數）',
               a: l3jo([l3no(1) + T('M=' + l3bm(M)), l3no(2) + T(Fr.tex(X2[0]))]), h: hb, p: pp };
    }
    pp.ans = l3fp(X2[0]);
    return { q: head + '求兩' + ct.u + '後甲' + S + '的市場占有率。（化為最簡分數）', a: T(Fr.tex(X2[0])), h: hb, p: pp };
  };

  /* ══ L3-15　穩定狀態：解 MX=X 再配上「兩個分量相加為 1」 ══ */
  var L315C = [
    { s: '區', w: '居民', u: '年', vb: '遷往', vs: '住在', head: '某市的市民只住在甲區與乙區兩地，總人口數長期不變' },
    { s: '牌', w: '用戶', u: '個月', vb: '改用', vs: '使用', head: '某地的手機門號只有甲牌與乙牌兩家業者，總用戶數長期不變' },
    { s: '案', w: '會員', u: '季', vb: '改選', vs: '選擇', head: '某健身房只有甲案與乙案兩種方案，總會員數長期不變' }
  ];
  L3.steadyPct = function (r) {
    r();
    var ct = r.pick(L315C), p1, p2, x, tr = 0, ok = false;
    do {
      p1 = r.int(1, 19) * 5; p2 = r.int(1, 19) * 5;
      /* p1+p2=100 會讓轉移方陣兩行完全相同（一期就定住），屬於退化情形 */
      ok = p1 !== p2 && p1 + p2 !== 100 && p1 < 100 && p2 < 100 && (100 * p2) % (p1 + p2) === 0;
      if (ok) { x = 100 * p2 / (p1 + p2); ok = x > 5 && x < 95; }
      tr++;
    } while (!ok && tr < 800);
    if (!ok) { p1 = 10; p2 = 30; x = 75; }
    var S = ct.s, fx = F(p2, p1 + p2), fy = F(p1, p1 + p2);
    var M = [[F(100 - p1, 100), F(p2, 100)], [F(p1, 100), F(100 - p2, 100)]];
    var v = r.int(0, 2), mult = (p1 + p2) / gcd(p1 + p2, p2), N = r.int(2, Math.max(2, Math.floor(400 / mult))) * mult;
    var head = ct.head + '。統計發現：每' + ct.u + ct.vs + '甲' + S + '的' + ct.w + '有 ' + T(l3pct(p1)) + ' 會' + ct.vb + '乙' + S + '、其餘仍' + ct.vs + '甲' + S + '；'
             + ct.vs + '乙' + S + '的' + ct.w + '有 ' + T(l3pct(p2)) + ' 會' + ct.vb + '甲' + S + '、其餘仍' + ct.vs + '乙' + S + '。長期依此慣性會形成穩定狀態。';
    var hb = '穩定狀態的意思是「再轉移一次也不變」，也就是解 ' + T('MX=X') + '。狀態順序（甲' + S + '，乙' + S + '）：'
           + T('M=' + l3bm(M)) + '（每一行的和都是 ' + T(1) + ' ✓）。'
           + '設 ' + T('X=' + l3cv(L3VS2)) + '，' + T('MX=X') + ' 的第一列是 ' + T(l3E(M[0][0]) + 'x+' + l3E(M[0][1]) + 'y=x') + '，'
           + '移項後得 ' + T(l3E(M[0][1]) + 'y=' + l3E(M[1][0]) + 'x') + '——這就是關鍵的一條比例式。'
           + '（第二列會化出完全相同的式子，這正是 ' + T('\\det(M-I)=0') + ' 的意思；所以真正把答案釘死的是「兩個分量相加為 ' + T(1) + '」那一條。）'
           + '順帶一提，穩定狀態與一開始的分配完全無關，這是轉移方陣最漂亮的性質之一。';
    var pp = { p1: p1, p2: p2, v: v };
    if (v === 1) {
      pp.ans = [M.map(function (u) { return u.map(l3fp); }), l3fp(fx), l3fp(fy)];
      return { q: head + l3no(1) + '寫出轉移方陣 ' + T('M') + '（狀態順序為（甲' + S + '，乙' + S + '））。' + l3no(2) + '求穩定狀態 ' + T('(x,y)') + '。（化為最簡分數）',
               a: l3jo([l3no(1) + T('M=' + l3bm(M)), l3no(2) + T('(x,y)=\\left(' + Fr.tex(fx, true) + ',\\,' + Fr.tex(fy, true) + '\\right)')]), h: hb, p: pp };
    }
    if (v === 2) {
      pp.N = N; pp.ans = N * p2 / (p1 + p2);
      return { q: head + '若全體共 ' + T(N) + ' 萬' + ct.w + '，求穩定狀態時甲' + S + '有幾萬' + ct.w + '？',
               a: T(N * p2 / (p1 + p2)) + ' 萬' + ct.w, h: hb, p: pp };
    }
    pp.ans = x;
    return { q: head + '求穩定狀態時甲' + S + '的' + ct.w + '占全體的百分比。', a: T(l3pct(x)), h: hb, p: pp };
  };

  var META_L3 = [['noSolTwoParam', '§1 二元含參數說無解：Δ 只是候選'], ['augZeroRow', '§2 增廣矩陣最後一列全零'], ['augBlurred', '§2 汙損的增廣矩陣（列運算保解）'],
                 ['noSolThreeParam', '§2 三元含參數說無解'], ['workRate3', '§2 工作效率的三元應用題'], ['matEqShift', '§4 X 在兩邊：提出 (A-kI)X=B'],
                 ['selfInverse', '§4 A 等於自己的反方陣'], ['matLawPick', '§4 矩陣運算律何者必成立'], ['powPeriodMin', '§4 A^n=A 的最小 n（找週期）'],
                 ['shearSum', '§4 推移方陣的乘冪與連加'], ['rotCompose', '§5 旋轉的合成與同餘'], ['reflAxis', '§5 鏡射矩陣求對稱軸'],
                 ['detAreaRatio', '§5 兩組像求面積伸縮率'], ['transTwoStep', '§5 轉移方陣：兩期後'], ['steadyPct', '§5 穩定狀態的百分比']];
  /* 固定題 L3-n 對應的類似題型 */
  var L3_FIX = { 'L3-1': 'noSolTwoParam', 'L3-2': 'augZeroRow', 'L3-3': 'augBlurred', 'L3-4': 'noSolThreeParam', 'L3-5': 'workRate3',
                 'L3-6': 'matEqShift', 'L3-7': 'selfInverse', 'L3-8': 'matLawPick', 'L3-9': 'powPeriodMin', 'L3-10': 'shearSum',
                 'L3-11': 'rotCompose', 'L3-12': 'reflAxis', 'L3-13': 'detAreaRatio', 'L3-14': 'transTwoStep', 'L3-15': 'steadyPct' };

  /* ══════════════════════════════════════════════════════════
     L0　章首先備診斷（5 型）：二元一次聯立（國中）、兩直線的關係（高一上 ch2）、平面向量的線性組合（高二上 ch3）、三階行列式（本冊 ch1）、特殊角的三角函數值（高一下 ch4）
     ══════════════════════════════════════════════════════════ */
  var L0 = {};
  function l0a(f) { return [f.n, f.d]; }
  function l0t(k, v, first) { if (k === 0) return ''; var s = k < 0 ? '-' : (first ? '' : '+'), ab = Math.abs(k); return s + (ab === 1 ? '' : ab) + v; }   /* 係數 ±1 不印 1 */
  function l0lin(a, b, c) { return (l0t(a, 'x', true) + l0t(b, 'y', a === 0)) + '=' + c; }
  function l0sn(x) { return x < 0 ? '(' + x + ')' : String(x); }
  function l0pp(x) { return '(' + x + ')'; }
  L0.solve2 = function (r) {
    r();
    var x = r.nz(-6, 6), y = r.int(-6, 6), a, b, c, d, t = 0;                     /* 不出 (0,0)：右邊全是 0 就沒得練 */
    do { a = r.nz(-5, 5); b = r.nz(-5, 5); c = r.nz(-5, 5); d = r.nz(-5, 5); } while (a * d - b * c === 0 && t++ < 50);
    var e = a * x + b * y, f = c * x + d * y;
    return { q: '解聯立方程式 ' + T('\\begin{cases}' + l0lin(a, b, e) + '\\\\' + l0lin(c, d, f) + '\\end{cases}') + '。',
             a: T('(x,y)=(' + x + ',' + y + ')'),
             h: '加減消去法：把第一式乘以 $' + l0sn(d) + '$、第二式乘以 $' + l0sn(b) + '$，兩式相減就消掉 $y$，剩下 $' + l0t(a * d - b * c, 'x', true) + '=' + (e * d - f * b) + '$；求出 $x$ 再代回任一式求 $y$，<b>最後兩式都要代回去檢查</b>。這一章只是把同樣的動作寫成「列運算」，並推廣到三個未知數。',
             p: { a: a, b: b, c: c, d: d, e: e, f: f, ans: [x, y] } };
  };
  L0.twoLinesRel = function (r) {
    r();
    var kind = r.int(0, 2), a = r.nz(-5, 5), b = r.nz(-5, 5), c = r.int(-8, 8), k = r.pick([2, 3, -1, -2, -3]), a2, b2, c2;
    if (kind === 0) { a2 = k * a; b2 = k * b; c2 = k * c + r.nz(-5, 5); }            /* 平行 */
    else if (kind === 1) { a2 = k * a; b2 = k * b; c2 = k * c; }                       /* 重合 */
    else { a2 = k * a; b2 = k * b + r.nz(-3, 3); c2 = r.int(-8, 8); if (a * b2 - a2 * b === 0) b2 += 1; }
    var ans = ['平行（沒有交點）', '重合（無限多個交點）', '恰交於一點'][kind];
    return { q: '判斷兩直線 ' + T('L_1:' + l0lin(a, b, c)) + ' 與 ' + T('L_2:' + l0lin(a2, b2, c2)) + ' 的關係：恰交於一點、平行，還是重合？',
             a: ans,
             h: '先算 $a_1b_2-a_2b_1=' + l0sn(a) + l0pp(b2) + '-' + l0sn(a2) + l0pp(b) + '$：不是 $0$ ⟹ 兩條線方向不同，恰交於一點；是 $0$ ⟹ 方向相同，再算 $a_1c_2-a_2c_1=' + l0sn(a) + l0pp(c2) + '-' + l0sn(a2) + l0pp(c) + '$：也是 $0$ 就是同一條線（重合），不是 $0$ 就是平行。這一章把這三種情形叫做「恰一組解／無限多組解／無解」，第一個式子就是 $\\Delta$。',
             p: { L1: [a, b, c], L2: [a2, b2, c2], kind: kind, ans: kind } };
  };
  L0.linComb2 = function (r) {
    r();
    var a, b, t = 0; do { a = [r.nz(-4, 4), r.nz(-4, 4)]; b = [r.nz(-4, 4), r.nz(-4, 4)]; } while (a[0] * b[1] - a[1] * b[0] === 0 && t++ < 50);
    var x = r.nz(-4, 4), y = r.nz(-4, 4), c = [x * a[0] + y * b[0], x * a[1] + y * b[1]];
    function v(u) { return '(' + u[0] + ',' + u[1] + ')'; }
    return { q: '設 ' + T('\\vec a=' + v(a)) + '、' + T('\\vec b=' + v(b)) + '、' + T('\\vec c=' + v(c)) + '。若 ' + T('\\vec c=x\\,\\vec a+y\\,\\vec b') + '，求 ' + T('(x,y)') + '。',
             a: T('(x,y)=(' + x + ',' + y + ')'),
             h: '兩個分量各寫一條式子：$' + l0lin(a[0], b[0], c[0]) + '$、$' + l0lin(a[1], b[1], c[1]) + '$，解這組二元一次聯立。這一章的第一件事就是反過來讀：<b>一組聯立方程式＝「用兩個行向量組合出右邊的向量」</b>，係數排起來就是方陣。',
             p: { a: a, b: b, c: c, ans: [x, y] } };
  };
  L0.det3 = function (r) {
    r();
    var M = [[r.int(-4, 4), r.int(-4, 4), r.int(-4, 4)], [r.int(-4, 4), r.int(-4, 4), r.int(-4, 4)], [r.int(-4, 4), r.int(-4, 4), r.int(-4, 4)]];
    M[r.int(0, 2)][r.int(0, 2)] = 0;                                                  /* 放一個 0，鼓勵沿有 0 的那一列展開 */
    var a = M[0], b = M[1], c = M[2];
    var m1 = b[1] * c[2] - b[2] * c[1], m2 = b[0] * c[2] - b[2] * c[0], m3 = b[0] * c[1] - b[1] * c[0], d = a[0] * m1 - a[1] * m2 + a[2] * m3;
    return { q: '計算三階行列式 ' + T('\\begin{vmatrix}' + M.map(function (row) { return row.join('&'); }).join('\\\\') + '\\end{vmatrix}') + '。',
             a: T(String(d)),
             h: (function () {
               var mn = [[b[1], b[2], c[1], c[2]], [b[0], b[2], c[0], c[2]], [b[0], b[1], c[0], c[1]]], sg = [1, -1, 1], out = '';
               for (var i = 0; i < 3; i++) { if (a[i] === 0) continue; out += (sg[i] < 0 ? '-' : (out ? '+' : '')) + l0sn(a[i]) + '\\begin{vmatrix}' + mn[i][0] + '&' + mn[i][1] + '\\\\' + mn[i][2] + '&' + mn[i][3] + '\\end{vmatrix}'; }
               return '沿第一列展開（符號 $+,-,+$' + (a.indexOf(0) >= 0 ? '；第一列是 $0$ 的那一項直接跳過' : '') + '）：' + (out ? '$' + out + '$' : '第一列全是 $0$，行列式就是 $0$') + '。每個二階行列式都是「交叉相乘相減」。這一章用它來判斷三元一次聯立是不是「恰有一組解」（$\\Delta\\ne0$）。';
             })(),
             p: { M: M, ans: d } };
  };
  var L0TRIG = { 0: ['1', '0'], 30: ['\\dfrac{\\sqrt{3}}{2}', '\\dfrac{1}{2}'], 45: ['\\dfrac{\\sqrt{2}}{2}', '\\dfrac{\\sqrt{2}}{2}'], 60: ['\\dfrac{1}{2}', '\\dfrac{\\sqrt{3}}{2}'], 90: ['0', '1'] };
  function l0neg(s, neg) { return (neg && s !== '0') ? '-' + s : s; }
  L0.trigSpecial = function (r) {
    r();
    var th = r.pick([120, 135, 150, 180, 210, 225, 240, 270, 300, 315, 330, 480, 495, 510, 540, 570, 585, 600, 630, 660, 675, 690, -30, -45, -60, -90, -120, -135, -150, -180, -210, -225, -240, -270, -300, -315, -330]);
    var t = ((th % 360) + 360) % 360, quad = t < 90 ? 1 : t < 180 ? 2 : t < 270 ? 3 : 4, ref = quad === 1 ? t : quad === 2 ? 180 - t : quad === 3 ? t - 180 : 360 - t;
    if (t === 90) { ref = 90; } if (t === 180) { ref = 0; } if (t === 270) { ref = 90; }
    var cs = L0TRIG[ref], cneg = (t > 90 && t < 270) || t === 180, sneg = t > 180;
    var rule = (t % 90 === 0) ? '終邊落在坐標軸上：直接讀單位圓上那一點的坐標。' : '先找參考角 $' + ref + '^\\circ$（終邊與 $x$ 軸的夾角），值和 $' + ref + '^\\circ$ 的一樣；再依第' + ['', '一', '二', '三', '四'][quad] + '象限決定正負（$\\cos$ 看 $x$ 坐標、$\\sin$ 看 $y$ 坐標）。';
    var ang = th < 0 ? '(' + th + '^\\circ)' : th + '^\\circ';
    return { q: '求 ' + T('\\cos' + ang) + ' 與 ' + T('\\sin' + ang) + ' 的值。',
             a: T('\\cos' + ang + '=' + l0neg(cs[0], cneg)) + '、' + T('\\sin' + ang + '=' + l0neg(cs[1], sneg)),
             h: (th < 0 ? '負角是順時針轉，$' + th + '^\\circ$ 與 $' + t + '^\\circ$ 同界。' : th > 360 ? '超過一圈先減 $360^\\circ$：$' + th + '^\\circ$ 與 $' + t + '^\\circ$ 同界。' : '') + rule + '這一章的旋轉矩陣 $\\begin{bmatrix}\\cos\\theta&-\\sin\\theta\\\\\\sin\\theta&\\cos\\theta\\end{bmatrix}$ 就是把這兩個值填進去。',
             p: { th: th, ans: [l0neg(cs[0], cneg), l0neg(cs[1], sneg)] } };
  };
  var META_L0 = [['solve2', '二元一次聯立方程式'], ['twoLinesRel', '兩直線的關係'], ['linComb2', '平面向量的線性組合'], ['det3', '三階行列式'], ['trigSpecial', '特殊角的三角函數值']];
  /* 先備題型 → 該去哪裡複習 */
  var PREREQ = {
    solve2: { txt: '二元一次聯立的加減消去法（國中）——本章的列運算就是把它寫成機械動作', link: null },
    twoLinesRel: { txt: '兩直線的相交、平行與重合（高一上第二章 直線與圓）——就是聯立方程式的恰一解、無解、無限多解', link: '../g10a-ch02/practice.html#L1' },
    linComb2: { txt: '平面向量的線性組合（高二上第三章 平面向量）——方陣乘向量就是行向量的線性組合', link: '../g11a-ch03/practice.html#L1' },
    det3: { txt: '三階行列式的展開（本冊第一章 空間向量）——判斷三元一次聯立是否恰有一組解要用到', link: '../g11b-ch01/practice.html#L1' },
    trigSpecial: { txt: '廣義角的特殊角三角函數值（高一下第四章 三角比）——旋轉矩陣與鏡射矩陣要填這些值', link: '../g10b-ch04/practice.html#L1' }
  };
  /* ══════════════════════════════════════════════════════════
     對照題：同一型抽兩題，只差一個關鍵特徵（f 由 p 算出；keep 的欄位要相同）
     ══════════════════════════════════════════════════════════ */
  var CONTRAST = {
    'L1.twoLineCase': { f: function (p) { return p.lab; }, why: '二元一次聯立就是兩條直線：先看 $\\Delta=a_1b_2-a_2b_1$。$\\Delta\\ne0$ ⟹ 方向不同，恰交於一點（恰有一組解）；$\\Delta=0$ ⟹ 方向相同，這時<b>還要再比常數項</b>——整條式子成比例就是同一條線（無限多組解），只有左邊成比例、常數項對不上就是平行（無解）。' },
    'L1.colCombo': { f: function (p) { return p.ans.lab; }, why: '$B\\begin{bmatrix}x\\\\y\\end{bmatrix}$ 是「用 $B$ 的兩個行向量做線性組合」。兩個行向量<b>不平行</b>（$\\det B\\ne0$）⟹ 平面上任何向量都組得出來，而且只有一種組法；兩個行向量<b>平行</b>（$\\det B=0$）⟹ 只組得出那條線上的向量：右邊剛好在線上就有無限多種組法，不在線上就組不出來。' },
    'L1.echelonRead': { f: function (p) { return p.kind; }, why: '階梯形由最後一列讀起：最後一列是 $0\\ 0\\ 0\\mid k$（$k\\ne0$）⟹ 出現矛盾 $0=k$，<b>無解</b>；最後一列整列都是 $0$ ⟹ 少一條有效方程式，<b>無限多組解</b>（令一個未知數為 $t$）；三列都有帶頭的非零數 ⟹ 由下往上代回，<b>恰有一組解</b>。' },
    'L1.countSol3': { f: function (p) { return p.ans.lab; }, why: '$\\Delta\\ne0$ 可以直接下結論「恰有一組解」；但 <b>$\\Delta=0$ 只告訴你「不是恰一組」</b>，到底是無解還是無限多組解，行列式分不出來，一定要回到消去法，看最後會不會出現 $0=k$ 的矛盾。' },
    'L1.planeCase': { f: function (p) { return p.kind; }, why: '$\\Delta=0$ 又有解時，數「化成階梯形後剩幾條有效方程式」：剩 $2$ 條 ⟹ 公共部分是一條直線（可能是三個相異平面共線，也可能是兩平面重合、第三面與它們相交）；剩 $1$ 條 ⟹ 三個方程式其實是同一個平面，三平面重合。要分辨前兩種，再回頭看原來的係數有沒有整條成比例的。' },
    'L1.planeNoSol': { f: function (p) { return p.kind; }, why: '無解的四種擺法要<b>回頭看原來的三個法向量</b>：三個兩兩平行 ⟹ 三平面兩兩平行；只有兩個平行 ⟹ 兩平行平面被第三個平面截過；都不平行 ⟹ 三稜柱型（兩兩相交、三條交線互相平行）；三個法向量平行而且其中兩條方程式整條成比例 ⟹ 兩平面重合、第三面與它們平行。<b>最後一種與「三平面兩兩平行」化成階梯形一模一樣</b>，只有看原係數才分得出來。' },
    'L1.matMul': { f: function (p) { return p.kind; }, why: '兩個同階方陣 $AB$、$BA$ 都能乘，但<b>結果通常不同</b>；換成 $2\\times2$ 與 $2\\times3$ 時，連能不能乘都要先檢查：<b>左邊的行數要等於右邊的列數</b>，$AC$ 可以（$2\\times\\underline2$ 配 $\\underline2\\times3$），$CA$ 不行（$2\\times\\underline3$ 配 $\\underline2\\times2$）。' },
    'L1.matPow': { f: function (p) { return p.kind; }, why: '求 $A^n$ 先看 $A$ 長什麼樣子：<b>對角方陣</b>就對角線各自 $n$ 次方；<b>$I+N$ 型（$N^2=O$）</b>算到 $A^2$、$A^3$ 就看得出某一格每次加一個固定的數；<b>會循環的</b>（旋轉、鏡射這一類）先找使 $A^m=I$ 的最小 $m$，再把 $n$ 除以 $m$ 取餘數。三種都是「先算前幾次、找規律」，不需要任何大學的工具。' },
    'L1.detArea': { f: function (p) { return p.ans.d > 0 ? 1 : -1; }, why: '面積的伸縮倍率是 <b>$|\\det A|$</b>，永遠取絕對值；$\\det A$ 的<b>正負號</b>說的是另一件事：正 ⟹ 圖形的轉向（逆時針順序）不變；負 ⟹ 被翻面了（像鏡射那樣，逆時針變順時針）。兩題的面積算法一樣，差在翻不翻面。' },
    'L2.solve3Param': { f: function (p) { return p.flip; }, why: '化到最後一列是 $(k^2-a^2)\\,z=(\\text{含 }k\\text{ 的一次式})$。左邊在 $k=\\pm a$ 時都是 $0$，<b>這兩個臨界值要分別代進右邊檢查</b>：右邊也是 $0$ ⟹ $0=0$，無限多組解；右邊不是 $0$ ⟹ 矛盾，無解。哪一個 $k$ 是哪一種，完全看右邊那個一次式的根落在哪裡——兩題剛好相反。' },
    'L2.powPeriod': { f: function (p) { return p.kind; }, why: '$A^n$ 的兩條路：<b>會循環</b>的方陣找週期（$A^m=I$ ⟹ 指數除以 $m$ 取餘數）；<b>不會循環、但能寫成 $kI+N$ 且 $N^2=O$</b> 的，因為 $I$ 與 $N$ 可交換，展開後 $N^2$ 以上全部消失，$A^n=k^nI+nk^{n-1}N$。看到對角線兩個數相同、另一個角是 $0$，就是第二種。' },
    'L2.rotAdv': { f: function (p) { return p.cw; }, why: '旋轉矩陣 $\\begin{bmatrix}\\cos\\theta&-\\sin\\theta\\\\\\sin\\theta&\\cos\\theta\\end{bmatrix}$ 的 $\\theta$ 是<b>逆時針</b>的角度；順時針轉 $\\theta$ 就是逆時針轉 $-\\theta$，矩陣變成 $\\begin{bmatrix}\\cos\\theta&\\sin\\theta\\\\-\\sin\\theta&\\cos\\theta\\end{bmatrix}$——<b>只有兩個 $\\sin$ 的位置換了正負號</b>。辨認時看左下角：正的是逆時針、負的是順時針（$0^\\circ\\lt\\theta\\lt180^\\circ$ 時）。' },
    'L2.reflAdv': { f: function (p) { return p.kind; }, why: '兩個行向量都是單位長而且互相垂直時，<b>$\\det=1$ 是旋轉、$\\det=-1$ 是鏡射</b>。長相也不同：旋轉是 $\\begin{bmatrix}c&-s\\\\s&c\\end{bmatrix}$（對角線相同、另一條對角線差一個負號）；鏡射是 $\\begin{bmatrix}c&s\\\\s&-c\\end{bmatrix}$（對角線差一個負號、另一條對角線相同），而且鏡射做兩次會回到原位，$A^2=I$。' }
  };
  function contrastPair(tier, key, seedA, maxTry) {
    var c = CONTRAST[tier + '.' + key]; if (!c) return null;
    var A = wrapItem(tier, key, seedA), fA = c.f(A.p), keep = c.keep || [];
    for (var n = 1; n < (maxTry || 4000); n++) {
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
      /* 原始 <>（瀏覽器會當標籤）、全形頓號（KaTeX 嚴格模式拒收）、\times 後接字母一律在這裡修 */
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

  return { makeRng: makeRng, L0: L0, L1: L1, L2: L2, L3: L3, L3_FIX: L3_FIX, META: META, PREREQ: PREREQ, CONTRAST: CONTRAST, contrastPair: contrastPair, _util: { gcd: gcd, F: F, Fr: Fr, fp: fp, bm: bm, vmx: vmx, cv: cv, agm: agm, mMul: mMul, mAdd: mAdd, mSub: mSub, mK: mK, mVec: mVec, dt2: dt2, dt3: dt3, iv2: iv2, mPw: mPw, mSame: mSame, MF: MF, VF: VF, lin: lin, csys: csys, rotM: rotM, refM: refM, ANG: ANG, basicInt: basicInt, paramTex: paramTex, sysUnique: sysUnique, lineSys: lineSys } };
}));
