/* ══════════════════════════════════════════════════════════════
   g11b-ch02 空間中的直線與平面・分級練習本　題目產生器
   ─────────────────────────────────────────────────────────────
   每個產生器：function (rng) → { q, a, h, p }
     q：題目（HTML，可含 KaTeX $…$）   a：答案（HTML）
     h：一行提示（一定要帶本題的數字）   p：輸入參數（給 verify_gen11b2.py 從題幹重算後對照）
   平面一律寫成 ax+by+cz=d，且化成最簡整數係數、首個非零係數為正（generator 內先 redPos 法向量，
   讓「顯示出來的法向量」與「計算用的法向量」永遠是同一個）。
   直線用參數式 \begin{cases}…\end{cases}、比例式（分母 0 改寫成 x=常數）或簡記 (P)+t(d)。
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
    eq: function (x, y) { return x.n * y.d === y.n * x.d; },
    tex: function (x, small) {
      if (x.d === 1) return String(x.n);
      var f = small ? '\\frac' : '\\dfrac';
      return (x.n < 0 ? '-' : '') + f + '{' + Math.abs(x.n) + '}{' + x.d + '}';
    }
  };
  function fr2(f) { return [f.n, f.d]; }
  function simpSqrt(n) { var c = 1, r = n; for (var k = 2; k * k <= r; k++) { while (r % (k * k) === 0) { r /= k * k; c *= k; } } return { c: c, r: r }; }
  function sqrtTex(n) { if (n === 0) return '0'; var s = simpSqrt(n); if (s.r === 1) return String(s.c); return (s.c === 1 ? '' : s.c) + '\\sqrt{' + s.r + '}'; }
  /* √(n/d)（n,d 正整數）化簡成 (c√r)/d' */
  function sqrtFracTex(n, d, neg) {
    if (n === 0) return '0';
    var g = gcd(n, d); n /= g; d /= g;
    var s = simpSqrt(n * d), c = s.c, r = s.r;              /* √(n/d) = √(nd)/d */
    var g2 = gcd(c, d); c /= g2; var dd = d / g2;
    var body = (c === 1 ? (r === 1 ? '1' : '') : c) + (r === 1 ? '' : '\\sqrt{' + r + '}');
    if (r === 1) body = String(c);
    var t = dd === 1 ? body : '\\dfrac{' + body + '}{' + dd + '}';
    return (neg ? '-' : '') + t;
  }
  /* num·√rad / den */
  function radTex(num, rad, den) {
    if (num === 0) return '0';
    var s = simpSqrt(rad); num *= s.c; rad = s.r;
    var g = gcd(Math.abs(num), den); num /= g; den /= g;
    var body = (Math.abs(num) === 1 ? '' : Math.abs(num)) + (rad === 1 ? (Math.abs(num) === 1 ? '1' : '') : '\\sqrt{' + rad + '}');
    if (rad === 1) body = String(Math.abs(num));
    return (num < 0 ? '-' : '') + (den === 1 ? body : '\\dfrac{' + body + '}{' + den + '}');
  }
  function T(s) { return '$' + s + '$'; }
  function term(coef, v, first) {
    if (coef === 0) return '';
    var sgn = coef < 0 ? '-' : (first ? '' : '+');
    var ab = Math.abs(coef);
    return sgn + (ab === 1 && v ? '' : ab) + v;
  }
  /* ── 三維向量工具 ── */
  function vt(v) { return '(' + v[0] + ',' + v[1] + ',' + v[2] + ')'; }
  function vtF(v) { return '\\left(' + Fr.tex(v[0]) + ',\\ ' + Fr.tex(v[1]) + ',\\ ' + Fr.tex(v[2]) + '\\right)'; }
  function add(u, v) { return [u[0] + v[0], u[1] + v[1], u[2] + v[2]]; }
  function sub(u, v) { return [u[0] - v[0], u[1] - v[1], u[2] - v[2]]; }
  function sc(k, v) { return [k * v[0], k * v[1], k * v[2]]; }
  function dot(u, v) { return u[0] * v[0] + u[1] * v[1] + u[2] * v[2]; }
  function cross(u, v) { return [u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2], u[0] * v[1] - u[1] * v[0]]; }
  function n2(v) { return dot(v, v); }
  function det3(a, b, c) { return dot(a, cross(b, c)); }
  function ov(s) { return '\\overrightarrow{' + s + '}'; }
  function vec(s) { return '\\vec ' + s; }
  function comb(k, s, first) { if (k === 0) return ''; var sgn = k < 0 ? '-' : (first ? '' : '+'), ab = Math.abs(k); return sgn + (ab === 1 ? '' : ab) + s; }
  function rv(r, lo, hi) { return [r.nz(lo, hi), r.nz(lo, hi), r.nz(lo, hi)]; }
  function rp(r, lo, hi) { return [r.int(lo, hi), r.int(lo, hi), r.int(lo, hi)]; }
  function isZero(v) { return v[0] === 0 && v[1] === 0 && v[2] === 0; }
  function parallel(u, v) { return isZero(cross(u, v)); }
  var AXES = ['x', 'y', 'z'], PLANES = ['xy', 'yz', 'zx'];
  /* PLANES[i] 缺席的坐標索引：xy→z(2)、yz→x(0)、zx→y(1) */
  var PLMISS = [2, 0, 1];

  /* ── 本章新增的工具 ── */
  function nzc(v) { return (v[0] ? 1 : 0) + (v[1] ? 1 : 0) + (v[2] ? 1 : 0); }
  function gcd3(v) { return gcd(gcd(Math.abs(v[0]), Math.abs(v[1])), Math.abs(v[2])); }
  function red(v) { var g = gcd3(v) || 1; return [v[0] / g, v[1] / g, v[2] / g]; }
  function redPos(v) { var w = red(v), f = (w[0] !== 0 ? w[0] : (w[1] !== 0 ? w[1] : w[2])); return f < 0 ? sc(-1, w) : w; }
  /* 隨機的「最簡整數」向量（至少 minNz 個非零分量、三分量公因數為 1） */
  function rnv(r, lo, hi, minNz) {
    minNz = minNz || 2;
    var v, t = 0;
    do { v = [r.int(lo, hi), r.int(lo, hi), r.int(lo, hi)]; t++; } while ((nzc(v) < minNz || gcd3(v) !== 1) && t < 300);
    if (nzc(v) < minNz || gcd3(v) !== 1) v = [1, 2, 3];
    return v;
  }
  /* 指定「恰好 nz 個非零分量」的最簡整數方向向量 */
  function dirZeros(r, nz) {
    var idx = r.shuffle([0, 1, 2]), d, t = 0;
    if (nz === 1) { d = [0, 0, 0]; d[idx[0]] = r.sign(); return d; }
    do { d = [0, 0, 0]; for (var k = 0; k < nz; k++) d[idx[k]] = r.nz(-5, 5); t++; } while (gcd3(d) !== 1 && t < 80);
    if (gcd3(d) !== 1) { d = [0, 0, 0]; d[idx[0]] = 1; for (var j = 1; j < nz; j++) d[idx[j]] = j + 1; }
    return d;
  }
  /* 整數長度的最簡法向量（讓距離、夾角出現有理數答案） */
  var PYN = [[[1, 2, 2], 3], [[2, 3, 6], 7], [[1, 4, 8], 9], [[4, 4, 7], 9], [[2, 6, 9], 11], [[3, 4, 12], 13], [[2, 10, 11], 15], [[6, 6, 7], 11]];
  function pyn(r) { var e = r.pick(PYN), v = r.shuffle(e[0]); return { v: redPos([v[0] * r.sign(), v[1] * r.sign(), v[2] * r.sign()]), L: e[1] }; }
  /* 顯示用法向量：最簡整數、首個非零係數為正（normPlane 不會再動它） */
  function genN(r) { return (r() < 0.6) ? pyn(r) : { v: redPos(rnv(r, -5, 5, 2)), L: 0 }; }
  /* 分量較小的法向量：坐標會被 n 放大的題型（正射影、最短路徑）用 */
  var PYS = [[[1, 2, 2], 3], [[2, 3, 6], 7], [[1, 2, 2], 3], [[4, 4, 7], 9]];
  function genNs(r) {
    if (r() < 0.45) { var e = r.pick(PYS), v = r.shuffle(e[0]); return { v: redPos([v[0] * r.sign(), v[1] * r.sign(), v[2] * r.sign()]), L: e[1] }; }
    return { v: redPos(rnv(r, -3, 3, 2)), L: 0 };
  }
  /* 垂直於 n 的兩個整數向量（張出整個垂直平面） */
  function perpBasis(n) {
    var e = [[1, 0, 0], [0, 1, 0], [0, 0, 1]], u = null, v = null;
    for (var i = 0; i < 3; i++) {
      var c = cross(n, e[i]);
      if (isZero(c)) continue;
      if (!u) u = red(c); else if (!parallel(u, c)) { v = red(c); break; }
    }
    if (!v) v = u;
    return [u, v];
  }
  function perpRand(r, n, lo, hi) {
    var b = perpBasis(n), w, t = 0;
    do { w = add(sc(r.int(lo, hi), b[0]), sc(r.int(lo, hi), b[1])); t++; } while (isZero(w) && t < 60);
    if (isZero(w)) w = b[0];
    return w;
  }
  /* 平面：[a,b,c,d] 表示 ax+by+cz=d，化最簡整數且首個非零係數為正 */
  function normPlane(pl) {
    var g = gcd(gcd3([pl[0], pl[1], pl[2]]), Math.abs(pl[3])) || 1;
    var a = pl[0] / g, b = pl[1] / g, c = pl[2] / g, d = pl[3] / g;
    var f = (a !== 0 ? a : (b !== 0 ? b : c));
    if (f < 0) { a = -a; b = -b; c = -c; d = -d; }
    return [a, b, c, d];
  }
  function lhsTex(a, b, c) {
    var s = '';
    s += term(a, 'x', s === ''); s += term(b, 'y', s === ''); s += term(c, 'z', s === '');
    return s === '' ? '0' : s;
  }
  function planeTex(pl) { var q = normPlane(pl); return lhsTex(q[0], q[1], q[2]) + '=' + q[3]; }
  /* 把法向量與過點寫成 ax+by+cz=d */
  function planeOf(n, P) { return normPlane([n[0], n[1], n[2], dot(n, P)]); }
  /* 代入左式的算式：(2)(1)+(-3)(4)+(1)(0) */
  function subTex(n, P) {
    var s = '';
    for (var i = 0; i < 3; i++) { if (n[i] === 0) continue; s += (s === '' ? '' : '+') + '(' + n[i] + ')(' + P[i] + ')'; }
    return s === '' ? '0' : s;
  }
  function lin(p, k, vr) { if (k === 0) return String(p); return (p === 0 ? '' : String(p)) + term(k, vr, p === 0); }
  function paramTex(P, d, vr) {
    vr = vr || 't';
    var v = ['x', 'y', 'z'], rows = [];
    for (var i = 0; i < 3; i++) rows.push(v[i] + '=' + lin(P[i], d[i], vr));
    return '\\begin{cases}' + rows.join('\\\\ ') + '\\end{cases}';
  }
  function ratioTex(P, d) {
    var v = ['x', 'y', 'z'], fr = [], fx = [];
    for (var i = 0; i < 3; i++) {
      var t = v[i] + (P[i] === 0 ? '' : (P[i] < 0 ? '+' + (-P[i]) : '-' + P[i]));
      if (d[i] === 0) fx.push(v[i] + '=' + P[i]); else fr.push('\\dfrac{' + t + '}{' + d[i] + '}');
    }
    if (fr.length >= 2) return fr.join('=') + (fx.length ? ',\\ ' + fx.join(',\\ ') : '');
    return fx.join(',\\ ');
  }
  function lineShort(P, d, vr) { return vt(P) + '+' + (vr || 't') + vt(d); }
  /* 長方體 ABCD-EFGH：ABCD 為底面、AE 鉛直 */
  function boxV(a, b, c) { return { A: [0, 0, 0], B: [a, 0, 0], C: [a, b, 0], D: [0, b, 0], E: [0, 0, c], F: [a, 0, c], G: [a, b, c], H: [0, b, c] }; }
  var VN = ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H'];

  /* ═══════════════════════ L1 ═══════════════════════ */
  var L1 = {};

  /* ── §1-1 由點與法向量寫平面 ── */
  L1.planePointNormal = function (r) {
    var P0 = rp(r, -6, 6), n = rnv(r, -5, 5, 2), d = dot(n, P0);
    var Q = add(P0, perpRand(r, n, -1, 1)), on = r() < 0.5;
    if (!on) { var ax = 0; while (n[ax] === 0) ax++; Q = Q.slice(); Q[ax] += r.pick([1, -1, 2, -2]); }
    var pl = normPlane([n[0], n[1], n[2], d]), pn = [pl[0], pl[1], pl[2]];
    var qv = dot(pn, Q), L = lhsTex(n[0], n[1], n[2]);
    return { q: '設平面 ' + T('E') + ' 通過點 ' + T('P_0' + vt(P0)) + '，且 ' + T(vec('n') + '=' + vt(n)) + ' 為 ' + T('E') + ' 的一個法向量。(1) 求 ' + T('E') + ' 的方程式（化為最簡整數係數）。(2) 判斷點 ' + T('Q' + vt(Q)) + ' 是否在 ' + T('E') + ' 上。',
             a: '(1) ' + T('E:' + planeTex(pl)) + '　(2) 把 ' + T('Q') + ' 代入 (1) 的左式得 ' + T(String(qv)) + '，' + (on ? '與常數項 ' + T(String(pl[3])) + ' 相等，所以 ' + T('Q') + ' 在 ' + T('E') + ' 上' : '與常數項 ' + T(String(pl[3])) + ' 不相等，所以 ' + T('Q') + ' 不在 ' + T('E') + ' 上'),
             h: '法向量的三個分量就是 ' + T('x,y,z') + ' 的係數：先寫成 ' + T(L + '=d') + '，再把 ' + T('P_0') + ' 代進去定 ' + T('d') + '：' + T(subTex(n, P0) + '=' + d) + '；最後確認係數已是最簡整數、首項為正（必要時兩邊同乘 ' + T('-1') + '）。',
             p: { P0: P0, n: n, Q: Q } };
  };

  /* ── §1-2 三點決定平面 ── */
  L1.planeThreePts = function (r) {
    var A, B, C, n, t = 0;
    do { A = rp(r, -4, 4); B = rp(r, -4, 4); C = rp(r, -4, 4); n = cross(sub(B, A), sub(C, A)); t++; } while (isZero(n) && t < 80);
    var nr = redPos(n);
    return { q: '求通過 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '、' + T('C' + vt(C)) + ' 三點的平面 ' + T('E') + ' 的方程式（化為最簡整數係數）。',
             a: T('E:' + planeTex(planeOf(nr, A))),
             h: T(ov('AB') + '=' + vt(sub(B, A))) + '、' + T(ov('AC') + '=' + vt(sub(C, A))) + '；法向量取外積 ' + T(ov('AB') + '\\times' + ov('AC') + '=' + vt(n)) + '（化成首項為正的最簡整數 ' + T(vt(nr)) + '），再把 ' + T('A') + ' 代進去定常數。',
             p: { A: A, B: B, C: C } };
  };

  /* ── §1-3 讀係數：法向量與坐標軸交點 ── */
  L1.planeIntercepts = function (r) {
    var n, d, t = 0;
    do { n = rv(r, -6, 6); d = r.nz(-12, 12); t++; } while (gcd3(n) !== 1 && t < 200);
    if (gcd3(n) !== 1) n = [1, 2, 3];
    var pl = normPlane([n[0], n[1], n[2], d]);
    var X = [F(pl[3], pl[0]), F(0), F(0)], Y = [F(0), F(pl[3], pl[1]), F(0)], Z = [F(0), F(0), F(pl[3], pl[2])];
    var V = F(Math.abs(pl[3] * pl[3] * pl[3]), 6 * Math.abs(pl[0] * pl[1] * pl[2]));
    return { q: '設平面 ' + T('E:' + planeTex(pl)) + '。(1) 寫出 ' + T('E') + ' 的一個法向量。(2) 求 ' + T('E') + ' 與 ' + T('x') + ' 軸、' + T('y') + ' 軸、' + T('z') + ' 軸的交點。(3) 求 ' + T('E') + ' 與三個坐標平面所圍成的四面體體積。',
             a: '(1) ' + T(vec('n') + '=' + vt([pl[0], pl[1], pl[2]])) + '（或其非零倍數）　(2) ' + T(vtF(X)) + '、' + T(vtF(Y)) + '、' + T(vtF(Z)) + '　(3) ' + T('V=' + Fr.tex(V)),
             h: '與 ' + T('x') + ' 軸的交點就是把 ' + T('y=z=0') + ' 代進去：' + T(term(pl[0], 'x', true) + '=' + pl[3]) + '，另兩軸同理。(3) 這是第一章的牆角型四面體，' + T('V=\\dfrac16\\left|x_0y_0z_0\\right|') + '，其中 ' + T('x_0,y_0,z_0') + ' 就是 (2) 的三個非零坐標。',
             p: { pl: pl } };
  };

  /* ── §1-4 特殊位置的平面 ── */
  L1.planeSpecial = function (r) {
    var P = rv(r, -6, 6), ax = r.int(0, 2), pl = r.int(0, 2);
    var i = (ax + 1) % 3, j = (ax + 2) % 3;
    var co = [0, 0, 0]; co[i] = P[j]; co[j] = -P[i];
    var E1 = normPlane([co[0], co[1], co[2], 0]);
    var mi = PLMISS[pl], E2 = [0, 0, 0, P[mi]]; E2[mi] = 1;
    var LT = ['a', 'b', 'c'], form = ax === 0 ? 'by+cz=0' : ax === 1 ? 'ax+cz=0' : 'ax+by=0';
    return { q: '設 ' + T('P' + vt(P)) + '。(1) 求通過 ' + T(AXES[ax]) + ' 軸與 ' + T('P') + ' 的平面 ' + T('E_1') + ' 的方程式。(2) 求通過 ' + T('P') + ' 且平行於 ' + T(PLANES[pl]) + ' 平面的平面 ' + T('E_2') + ' 的方程式。',
             a: '(1) ' + T('E_1:' + planeTex(E1)) + '　(2) ' + T('E_2:' + planeTex(E2)),
             h: '(1) 含 ' + T(AXES[ax]) + ' 軸 ⟹ 平面過原點（常數為 ' + T('0') + '）且沒有 ' + T(AXES[ax]) + ' 這一項，形如 ' + T(form) + '；代 ' + T('P') + ' 得 ' + T(term(P[i], LT[i], true) + term(P[j], LT[j], false) + '=0') + '，取 ' + T('(' + LT[i] + ',' + LT[j] + ')=(' + P[j] + ',' + (-P[i]) + ')') + '。(2) 平行 ' + T(PLANES[pl]) + ' 平面 ⟹ 形如 ' + T(AXES[mi] + '=k') + '，' + T('k') + ' 就是 ' + T('P') + ' 的 ' + T(AXES[mi]) + ' 坐標 ' + T(String(P[mi])) + '。',
             p: { P: P, ax: ax, pl: pl } };
  };

  /* ── §1-5 兩平面的位置關係與夾角 ── */
  L1.twoPlanesRel = function (r) {
    var mode = r.int(0, 2), n1 = genN(r).v, d1 = r.int(-9, 9), pl2, nb, t = 0;
    if (mode === 0) {
      var k = r.pick([2, 3, -2, -3]), d2;
      do { d2 = r.int(-24, 24); t++; } while (gcd(Math.abs(k), Math.abs(d2)) !== 1 && t < 200);
      pl2 = normPlane([k * n1[0], k * n1[1], k * n1[2], d2]);
    } else if (mode === 1) {
      var w;
      do { w = redPos(perpRand(r, n1, -3, 3)); t++; } while ((isZero(w) || parallel(n1, w)) && t < 80);
      pl2 = [w[0], w[1], w[2], r.int(-9, 9)];
    } else {
      var u;
      do { u = genN(r).v; t++; } while ((parallel(n1, u) || dot(n1, u) === 0) && t < 120);
      pl2 = [u[0], u[1], u[2], r.int(-9, 9)];
    }
    nb = [pl2[0], pl2[1], pl2[2]];
    var dv = dot(n1, nb), cs = dv === 0 ? '0' : sqrtFracTex(dv * dv, n2(n1) * n2(nb));
    var ans = mode === 0 ? '兩平面平行（不重合）' : mode === 1 ? '兩平面垂直，' + T('\\cos\\theta=0') : '兩平面相交（不垂直），' + T('\\cos\\theta=' + cs);
    return { q: '設平面 ' + T('E_1:' + planeTex([n1[0], n1[1], n1[2], d1])) + '、' + T('E_2:' + planeTex(pl2)) + '。判斷兩平面的位置關係；若相交，求兩平面夾角 ' + T('\\theta') + ' 的餘弦值（取銳角或直角）。',
             a: ans,
             h: '兩平面的關係看法向量 ' + T(vec('n_1') + '=' + vt(n1)) + '、' + T(vec('n_2') + '=' + vt(nb)) + '：成比例就平行、內積為 ' + T('0') + ' 就垂直，否則 ' + T('\\cos\\theta=\\dfrac{\\left|' + vec('n_1') + '\\cdot' + vec('n_2') + '\\right|}{\\left|' + vec('n_1') + '\\right|\\left|' + vec('n_2') + '\\right|}') + '；本題內積 ' + T('=' + dv) + '、' + T('\\left|' + vec('n_1') + '\\right|^2=' + n2(n1)) + '、' + T('\\left|' + vec('n_2') + '\\right|^2=' + n2(nb)) + '。',
             p: { n1: n1, d1: d1, pl2: pl2, mode: mode } };
  };

  /* ── §1-6 四點共平面求未知數 ── */
  L1.coplanarK = function (r) {
    var A, B, C, n, t = 0;
    do { A = rp(r, -4, 4); B = rp(r, -4, 4); C = rp(r, -4, 4); n = cross(sub(B, A), sub(C, A)); t++; } while (isZero(n) && t < 80);
    var nr = redPos(n), s = r.nz(-2, 2), u = r.nz(-2, 2);
    var D = add(A, add(sc(s, sub(B, A)), sc(u, sub(C, A)))), hide = r.int(0, 2), g = 0;
    while (nr[hide] === 0 && g < 3) { hide = (hide + 1) % 3; g++; }
    var dTex = '(' + [0, 1, 2].map(function (i) { return i === hide ? 'k' : String(D[i]); }).join(',') + ')';
    return { q: '已知 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '、' + T('C' + vt(C)) + '、' + T('D' + dTex) + ' 四點共平面。(1) 求通過 ' + T('A,B,C') + ' 的平面方程式。(2) 求 ' + T('k') + '。',
             a: '(1) ' + T(planeTex(planeOf(nr, A))) + '　(2) ' + T('k=' + D[hide]),
             h: '先用 ' + T(ov('AB') + '\\times' + ov('AC') + '=' + vt(n)) + '（化簡為 ' + T(vt(nr)) + '）求法向量、寫出平面方程式；四點共平面就是 ' + T('D') + ' 也滿足這個方程式，代進去解 ' + T('k') + ' 這條一次方程式。',
             p: { A: A, B: B, C: C, D: D, hide: hide } };
  };

  /* ── §2-1 點到平面的距離 ── */
  L1.ptPlaneDist = function (r) {
    var n = genN(r).v, P, d, t = 0;
    do { P = rp(r, -8, 8); d = r.nz(-12, 12); t++; } while (dot(n, P) === d && t < 80);
    var N = n2(n), v1 = dot(n, P) - d;
    return { q: '設點 ' + T('P' + vt(P)) + '、平面 ' + T('E:' + planeTex([n[0], n[1], n[2], d])) + '。(1) 求 ' + T('P') + ' 到 ' + T('E') + ' 的距離。(2) 求原點 ' + T('O') + ' 到 ' + T('E') + ' 的距離。',
             a: '(1) ' + T(sqrtFracTex(v1 * v1, N)) + '　(2) ' + T(sqrtFracTex(d * d, N)),
             h: '距離 ' + T('=\\dfrac{\\left|ax_0+by_0+cz_0-d\\right|}{\\sqrt{a^2+b^2+c^2}}') + '：分子把 ' + T('P') + ' 代入左式再減常數，得 ' + T('\\left|' + v1 + '\\right|') + '；分母 ' + T('=\\sqrt{' + N + '}') + '。(2) 原點代入左式得 ' + T('0') + '，分子就是 ' + T('\\left|' + (-d) + '\\right|') + '。',
             p: { P: P, n: n, d: d } };
  };

  /* ── §2-2 平行平面與兩平行平面的距離 ── */
  L1.parallelPlaneDist = function (r) {
    var n = genN(r).v, N = n2(n), mode = r.int(0, 1), d1 = r.nz(-10, 10), t = 0;
    if (mode === 0) {
      var k = r.pick([2, 3, -2, -3]), d2;
      do { d2 = r.int(-24, 24); t++; } while (gcd(Math.abs(k), Math.abs(d2)) !== 1 && t < 200);
      var pl2 = normPlane([k * n[0], k * n[1], k * n[2], d2]);
      var kk = 0;
      for (var i = 0; i < 3; i++) if (n[i] !== 0) { kk = pl2[i] / n[i]; break; }
      var df = Fr.sub(F(d1), F(pl2[3], kk));
      return { q: '設平面 ' + T('E_1:' + planeTex([n[0], n[1], n[2], d1])) + '、' + T('E_2:' + planeTex(pl2)) + '。(1) 說明兩平面平行且不重合。(2) 求兩平面的距離。',
               a: '(1) ' + T(vec('n_2') + '=' + (kk < 0 ? '-' : '') + (Math.abs(kk) === 1 ? '' : Math.abs(kk)) + vec('n_1')) + '，但常數項不成同一比例，故平行且不重合　(2) ' + T(radTex(Math.abs(df.n), N, df.d * N)),
               h: '先把 ' + T('E_2') + ' 兩邊同除以 ' + T(String(kk)) + '，讓兩式的左邊完全一樣：常數變成 ' + T(Fr.tex(F(pl2[3], kk))) + '；兩平行平面的距離 ' + T('=\\dfrac{\\left|d_1-d_2\\right|}{\\left|' + vec('n') + '\\right|}=\\dfrac{' + Fr.tex(F(Math.abs(df.n), df.d), true) + '}{\\sqrt{' + N + '}}') + '。',
               p: { n: n, d1: d1, pl2: pl2, mode: 0 } };
    }
    var P;
    do { P = rp(r, -7, 7); t++; } while (dot(n, P) === d1 && t < 80);
    var d2b = dot(n, P), df2 = d1 - d2b;
    return { q: '設平面 ' + T('E:' + planeTex([n[0], n[1], n[2], d1])) + '、點 ' + T('P' + vt(P)) + '。(1) 求通過 ' + T('P') + ' 且與 ' + T('E') + ' 平行的平面 ' + T('F') + ' 的方程式。(2) 求 ' + T('E') + ' 與 ' + T('F') + ' 的距離。',
             a: '(1) ' + T('F:' + planeTex([n[0], n[1], n[2], d2b])) + '　(2) ' + T(sqrtFracTex(df2 * df2, N)),
             h: '平行 ⟹ 法向量一樣，只有常數項不同：把 ' + T('P') + ' 代入左式得 ' + T(String(d2b)) + '，這就是 ' + T('F') + ' 的常數項；距離 ' + T('=\\dfrac{\\left|' + d1 + '-(' + d2b + ')\\right|}{\\sqrt{' + N + '}}') + '。',
             p: { n: n, d1: d1, P: P, mode: 1 } };
  };

  /* ── §2-3 點對平面的投影點與對稱點 ── */
  L1.planeProjSym = function (r) {
    var n = genN(r).v, N = n2(n), H = rp(r, -5, 5), m = r.pick([1, -1, 2, -2]);
    var P = add(H, sc(m, n)), d = dot(n, H), S = sub(H, sc(m, n));
    return { q: '設平面 ' + T('E:' + planeTex([n[0], n[1], n[2], d])) + '、點 ' + T('P' + vt(P)) + '。(1) 求 ' + T('P') + ' 在 ' + T('E') + ' 上的投影點 ' + T('H') + '。(2) 求 ' + T('P') + ' 對 ' + T('E') + ' 的對稱點 ' + T("P'") + '。(3) 求 ' + T('P') + ' 到 ' + T('E') + ' 的距離。',
             a: '(1) ' + T('H' + vt(H)) + '　(2) ' + T("P'" + vt(S)) + '　(3) ' + T(sqrtTex(m * m * N)),
             h: '令 ' + T('H=P+t' + vec('n')) + ' 代入 ' + T('E') + '：把 ' + T('P') + ' 代入左式得 ' + T(String(dot(n, P))) + '，' + T('\\left|' + vec('n') + '\\right|^2=' + N) + '，解得 ' + T('t=' + (-m)) + '；對稱點是 ' + T("P'=P+2t" + vec('n')) + '（投影點恰好是 ' + T('P') + ' 與 ' + T("P'") + ' 的中點）。',
             p: { n: n, d: d, P: P } };
  };

  /* ── §2-4 已知距離求未知數 ── */
  L1.planeDistUnknown = function (r) {
    var e = pyn(r), n = e.v, L = e.L, P = rp(r, -7, 7), D = r.int(1, 6), mode = r.int(0, 1);
    var v1 = dot(n, P), M = D * L;
    if (mode === 0) {
      return { q: '已知點 ' + T('P' + vt(P)) + ' 到平面 ' + T('E:' + lhsTex(n[0], n[1], n[2]) + '=k') + ' 的距離為 ' + T(String(D)) + '，求 ' + T('k') + '。',
               a: T('k=' + (v1 - M)) + ' 或 ' + T('k=' + (v1 + M)) + '（兩解）',
               h: '把 ' + T('P') + ' 代入左式得 ' + T(String(v1)) + '，' + T('\\left|' + vec('n') + '\\right|=\\sqrt{' + n2(n) + '}=' + L) + '；距離式 ' + T('\\dfrac{\\left|' + v1 + '-k\\right|}{' + L + '}=' + D) + ' ⟹ ' + T('\\left|' + v1 + '-k\\right|=' + M) + '，去絕對值有兩個答案。',
               p: { n: n, P: P, D: D, mode: 0 } };
    }
    var ax = r.int(0, 2), d = r.int(-10, 10), rest = 0;
    for (var i = 0; i < 3; i++) if (i !== ax) rest += n[i] * P[i];
    var t1 = F(d - rest - M, n[ax]), t2 = F(d - rest + M, n[ax]);
    var pt = [0, 1, 2].map(function (i2) { return i2 === ax ? 't' : String(P[i2]); }).join(',');
    return { q: '已知點 ' + T('P(' + pt + ')') + ' 到平面 ' + T('E:' + planeTex([n[0], n[1], n[2], d])) + ' 的距離為 ' + T(String(D)) + '，求 ' + T('t') + '。',
             a: T('t=' + Fr.tex(t1)) + ' 或 ' + T('t=' + Fr.tex(t2)) + '（兩解）',
             h: '把 ' + T('P') + ' 代入左式得 ' + T(term(n[ax], 't', true) + term(rest, '', false)) + '；分母 ' + T('=\\sqrt{' + n2(n) + '}=' + L) + '，所以 ' + T('\\left|' + term(n[ax], 't', true) + term(rest - d, '', false) + '\\right|=' + D + '\\times ' + L + '=' + M) + '，去絕對值解兩次。',
             p: { n: n, P: P, D: D, ax: ax, d: d, mode: 1 } };
  };

  /* ── §2-5 三頂點的平面與體積法對照 ── */
  L1.tetraPlaneDist = function (r) {
    var A, B, C, D, cr, dv, t = 0;
    do { A = rp(r, -3, 3); B = rp(r, -3, 3); C = rp(r, -3, 3); D = rp(r, -3, 3); cr = cross(sub(B, A), sub(C, A)); dv = dot(cr, sub(D, A)); t++; } while ((isZero(cr) || dv === 0) && t < 150);
    var nr = redPos(cr), V = F(Math.abs(dv), 6);
    return { q: '設 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '、' + T('C' + vt(C)) + '、' + T('D' + vt(D)) + '。(1) 求平面 ' + T('ABC') + ' 的方程式。(2) 求 ' + T('D') + ' 到平面 ' + T('ABC') + ' 的距離。(3) 求四面體 ' + T('ABCD') + ' 的體積。',
             a: '(1) ' + T(planeTex(planeOf(nr, A))) + '　(2) ' + T(sqrtFracTex(dv * dv, n2(cr))) + '　(3) ' + T('V=' + Fr.tex(V)),
             h: '(1) 法向量 ' + T(ov('AB') + '\\times' + ov('AC') + '=' + vt(cr)) + '（化簡為 ' + T(vt(nr)) + '）。(2) 直接用點到平面的距離公式，分子 ' + T('=\\left|' + dv + '\\right|') + '、分母 ' + T('=\\sqrt{' + n2(cr) + '}') + '。(3) ' + T('V=\\dfrac16\\left|' + dv + '\\right|') + '——和 (2) 的 ' + T('\\dfrac{3V}{S}') + ' 是同一件事。',
             p: { A: A, B: B, C: C, D: D } };
  };

  /* ── §3-1 參數式與比例式 ── */
  L1.lineParamRatio = function (r) {
    var mode = r.int(0, 2), d = dirZeros(r, 3 - mode), P0 = rp(r, -6, 6);
    var free = [0, 1, 2].filter(function (i) { return d[i] !== 0; })[0];
    var zi = [0, 1, 2].filter(function (i) { return d[i] === 0; });
    var extra = mode === 2 ? '（' + T(AXES[free]) + ' 任意）' : '';
    var note = mode === 0 ? '三個分量都不是 ' + T('0') + '，可以直接寫成三個分式相等。'
      : mode === 1 ? T(vec('d')) + ' 的 ' + T(AXES[zi[0]]) + ' 分量是 ' + T('0') + '，那一項不能當分母，要單獨寫成 ' + T(AXES[zi[0]] + '=' + P0[zi[0]]) + '。'
      : T(vec('d')) + ' 有兩個分量是 ' + T('0') + '（直線平行 ' + T(AXES[free]) + ' 軸），兩條式子都寫成常數。';
    return { q: '求通過點 ' + T('P_0' + vt(P0)) + ' 且方向向量為 ' + T(vec('d') + '=' + vt(d)) + ' 的直線 ' + T('L') + ' 的參數式與比例式。',
             a: '參數式：' + T(paramTex(P0, d, 't')) + '（' + T('t\\in\\mathbb{R}') + '）；比例式：' + T(ratioTex(P0, d)) + extra,
             h: '參數式是「起點坐標加上 ' + T('t') + ' 乘方向分量」：' + T('x=' + lin(P0[0], d[0], 't')) + ' 等三條。比例式是把 ' + T('t') + ' 消掉。' + note,
             p: { P0: P0, d: d, mode: mode } };
  };

  /* ── §3-2 由方程式讀回點與方向 ── */
  L1.lineReadBack = function (r) {
    var form = r.int(0, 1), zeros = r.int(0, 1), d = dirZeros(r, 3 - zeros), P0 = rp(r, -6, 6);
    var onQ = r() < 0.5, m = r.pick([1, -1, 2, -2, 3]), Q = add(P0, sc(m, d)), t = 0;
    if (!onQ) { var j; do { j = r.int(0, 2); Q = add(P0, sc(m, d)); Q[j] += r.pick([1, -1, 2, -2]); t++; } while (parallel(sub(Q, P0), d) && t < 60); }
    var given = form === 0 ? ratioTex(P0, d) : paramTex(P0, d, 't');
    var other = form === 0 ? paramTex(P0, d, 't') : ratioTex(P0, d);
    var oname = form === 0 ? '參數式' : '比例式';
    var hi = -1;
    for (var s2 = 0; s2 < 3; s2++) if (d[s2] !== 0 && P0[s2] < 0) { hi = s2; break; }
    if (hi < 0) for (var s3 = 0; s3 < 3; s3++) if (d[s3] !== 0 && P0[s3] !== 0) { hi = s3; break; }
    var hex = hi < 0 ? '分子裡被減掉的數就是點的坐標（本題起點取 ' + T('P_0' + vt(P0)) + '）'
      : '分子裡被減掉的數就是點的坐標——' + T(AXES[hi] + (P0[hi] < 0 ? '+' + (-P0[hi]) : '-' + P0[hi])) + ' 要讀成 ' + T(AXES[hi] + '-(' + P0[hi] + ')') + '，符號要翻過來';
    return { q: '設直線 ' + T('L:' + given) + '。(1) 寫出 ' + T('L') + ' 的一個方向向量與 ' + T('L') + ' 上的一點。(2) 判斷點 ' + T('Q' + vt(Q)) + ' 是否在 ' + T('L') + ' 上。(3) 把 ' + T('L') + ' 改寫成' + oname + '。',
             a: '(1) ' + T(vec('d') + '=' + vt(d)) + '（或其非零倍數）、' + T('P_0' + vt(P0)) + '　(2) ' + (onQ ? T('Q') + ' 在 ' + T('L') + ' 上（取 ' + T('t=' + m) + '）' : T('Q') + ' 不在 ' + T('L') + ' 上（三個坐標無法用同一個 ' + T('t') + ' 同時滿足）') + '　(3) ' + T(other),
             h: '分母（或 ' + T('t') + ' 的係數）就是方向向量 ' + T(vt(d)) + '；' + hex + '。(2) 把 ' + T('Q') + ' 代進去看三式能不能給出同一個 ' + T('t') + '。',
             p: { P0: P0, d: d, Q: Q, form: form } };
  };

  /* ── §3-3 兩點決定直線 ── */
  L1.lineTwoPts = function (r) {
    var A, B, d, t = 0;
    do { A = rp(r, -6, 6); B = rp(r, -6, 6); t++; } while (isZero(sub(B, A)) && t < 60);
    d = red(sub(B, A));
    var onC = r() < 0.5, k = r.pick([2, -1, 3, -2]), C = add(A, sc(k, d));
    if (!onC) { var j; do { j = r.int(0, 2); C = add(A, sc(k, d)); C[j] += r.pick([1, -1, 2]); t++; } while (parallel(sub(C, A), d) && t < 80); }
    return { q: '設 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '。(1) 求通過 ' + T('A') + '、' + T('B') + ' 的直線 ' + T('L') + ' 的參數式。(2) 求 ' + T('L') + ' 的比例式。(3) 判斷 ' + T('C' + vt(C)) + ' 是否在 ' + T('L') + ' 上。',
             a: '(1) ' + T(paramTex(A, d, 't')) + '　(2) ' + T(ratioTex(A, d)) + '　(3) ' + (onC ? T('C') + ' 在 ' + T('L') + ' 上' : T('C') + ' 不在 ' + T('L') + ' 上'),
             h: '方向向量取 ' + T(ov('AB') + '=' + vt(sub(B, A))) + '，可先約掉公因數變成 ' + T(vt(d)) + '（同一條直線）；起點用 ' + T('A') + ' 或 ' + T('B') + ' 都可以。(3) 看 ' + T(ov('AC') + '=' + vt(sub(C, A))) + ' 是不是 ' + T(vt(d)) + ' 的倍數。',
             p: { A: A, B: B, C: C } };
  };

  /* ── §3-4 直線與平面的交點 ── */
  L1.linePlaneInt = function (r) {
    var n, dd, t = 0;
    do { n = redPos(rnv(r, -4, 4, 2)); dd = rnv(r, -4, 4, 1); t++; } while ((dot(n, dd) === 0 || parallel(n, dd)) && t < 150);
    var X = rp(r, -5, 5), m = r.pick([1, -1, 2, -2]);
    var P0 = add(X, sc(m, dd)), d = dot(n, X);
    return { q: '求直線 ' + T('L:' + paramTex(P0, dd, 't')) + ' 與平面 ' + T('E:' + planeTex([n[0], n[1], n[2], d])) + ' 的交點。',
             a: T(vt(X)) + '（此時 ' + T('t=' + (-m)) + '）',
             h: '把參數式的三條代入 ' + T('E') + ' 的左式，整理成 ' + T('t') + ' 的一次方程式：' + T('\\left(' + vec('n') + '\\cdot' + vec('d') + '\\right)t=' + d + '-\\left(' + vec('n') + '\\cdot P_0\\right)') + '，本題 ' + T(vec('n') + '\\cdot' + vec('d') + '=' + dot(n, dd)) + '、' + T(vec('n') + '\\cdot P_0=' + dot(n, P0)) + '。',
             p: { n: n, d: d, P0: P0, dd: dd } };
  };

  /* ── §3-5 直線與平面的位置關係 ── */
  L1.linePlaneRel = function (r) {
    var mode = r.int(0, 2), n = redPos(rnv(r, -4, 4, 2)), dd, P0, X = [0, 0, 0], d, t = 0;
    if (mode === 0) {
      do { dd = rnv(r, -4, 4, 1); t++; } while (dot(n, dd) === 0 && t < 150);
      X = rp(r, -5, 5); P0 = add(X, sc(r.pick([1, -1, 2, -2]), dd)); d = dot(n, X);
    } else {
      do { dd = red(perpRand(r, n, -3, 3)); t++; } while (isZero(dd) && t < 80);
      P0 = rp(r, -5, 5);
      d = mode === 2 ? dot(n, P0) : dot(n, P0) + r.pick([1, -1, 2, -2, 3]);
    }
    var ans = mode === 0 ? '相交於一點 ' + T(vt(X)) : mode === 1 ? T('L') + ' 與 ' + T('E') + ' 平行（沒有交點）' : T('L') + ' 在 ' + T('E') + ' 上（有無限多個交點）';
    return { q: '判斷直線 ' + T('L:' + lineShort(P0, dd, 't')) + ' 與平面 ' + T('E:' + planeTex([n[0], n[1], n[2], d])) + ' 的位置關係；若相交於一點，求出交點。',
             a: ans,
             h: '先算 ' + T(vec('n') + '\\cdot' + vec('d') + '=' + dot(n, dd)) + '：不為 ' + T('0') + ' 就交於一點；為 ' + T('0') + ' 再看 ' + T('P_0') + ' 在不在 ' + T('E') + ' 上（把 ' + T('P_0') + ' 代入左式得 ' + T(String(dot(n, P0))) + '，常數項是 ' + T(String(d)) + '）。',
             p: { n: n, d: d, P0: P0, dd: dd, mode: mode } };
  };

  /* ── §3-6 直線與平面的夾角 ── */
  L1.linePlaneAngle = function (r) {
    var n = genN(r).v, dd = genN(r).v, t = 0;
    while (dot(n, dd) === 0 && t < 80) { dd = genN(r).v; t++; }
    var P0 = rp(r, -5, 5), d = r.int(-9, 9), dv = dot(n, dd);
    return { q: '設直線 ' + T('L:' + lineShort(P0, dd, 't')) + '、平面 ' + T('E:' + planeTex([n[0], n[1], n[2], d])) + '。(1) 求 ' + T('L') + ' 與 ' + T('E') + ' 的夾角 ' + T('\\theta') + ' 的正弦值。(2) 判斷 ' + T('L') + ' 與 ' + T('E') + ' 是否垂直。',
             a: '(1) ' + T('\\sin\\theta=' + sqrtFracTex(dv * dv, n2(n) * n2(dd))) + '　(2) ' + (parallel(n, dd) ? T('L') + ' 與 ' + T('E') + ' 垂直（' + T(vec('d')) + ' 與 ' + T(vec('n')) + ' 平行）' : T('L') + ' 與 ' + T('E') + ' 不垂直'),
             h: '線與面的夾角用 ' + T('\\sin') + '（不是 ' + T('\\cos') + '）：' + T('\\sin\\theta=\\dfrac{\\left|' + vec('d') + '\\cdot' + vec('n') + '\\right|}{\\left|' + vec('d') + '\\right|\\left|' + vec('n') + '\\right|}') + '。本題 ' + T(vec('d') + '\\cdot' + vec('n') + '=' + dv) + '、' + T('\\left|' + vec('d') + '\\right|^2=' + n2(dd)) + '、' + T('\\left|' + vec('n') + '\\right|^2=' + n2(n)) + '。',
             p: { n: n, d: d, P0: P0, dd: dd } };
  };

  /* ── §4-1 點到直線的距離 ── */
  L1.ptLineDist = function (r) {
    var A, dd, P, cr, t = 0;
    do { A = rp(r, -5, 5); dd = rnv(r, -4, 4, 1); P = rp(r, -5, 5); cr = cross(sub(P, A), dd); t++; } while (isZero(cr) && t < 150);
    return { q: '求點 ' + T('P' + vt(P)) + ' 到直線 ' + T('L:' + lineShort(A, dd, 't')) + ' 的距離。',
             a: T(sqrtFracTex(n2(cr), n2(dd))),
             h: '用外積：' + T('d=\\dfrac{\\left|' + ov('AP') + '\\times' + vec('d') + '\\right|}{\\left|' + vec('d') + '\\right|}') + '。本題 ' + T(ov('AP') + '=' + vt(sub(P, A))) + '，' + T(ov('AP') + '\\times' + vec('d') + '=' + vt(cr)) + '，' + T('\\left|' + vec('d') + '\\right|^2=' + n2(dd)) + '。',
             p: { A: A, dd: dd, P: P } };
  };

  /* ── §4-2 垂足 ── */
  L1.footPerp = function (r) {
    var A, dd, P, t = 0;
    do { A = rp(r, -5, 5); dd = rnv(r, -4, 4, 1); P = rp(r, -5, 5); t++; } while (parallel(sub(P, A), dd) && t < 150);
    var k = F(dot(sub(P, A), dd), n2(dd));
    var H = [0, 1, 2].map(function (i) { return Fr.add(F(A[i]), Fr.mul(k, F(dd[i]))); });
    var cr = cross(sub(P, A), dd);
    return { q: '設點 ' + T('P' + vt(P)) + '、直線 ' + T('L:' + lineShort(A, dd, 't')) + '。(1) 求 ' + T('P') + ' 在 ' + T('L') + ' 上的垂足 ' + T('H') + '。(2) 求 ' + T('\\overline{PH}') + '。',
             a: '(1) ' + T('H' + vtF(H)) + '　(2) ' + T(sqrtFracTex(n2(cr), n2(dd))),
             h: '令 ' + T('H=A+t' + vec('d')) + '，由 ' + T(ov('PH') + '\\cdot' + vec('d') + '=0') + ' 解 ' + T('t') + '：' + T('t=\\dfrac{' + ov('AP') + '\\cdot' + vec('d') + '}{\\left|' + vec('d') + '\\right|^2}=\\dfrac{' + dot(sub(P, A), dd) + '}{' + n2(dd) + '}') + '（其中 ' + T(ov('AP') + '=' + vt(sub(P, A))) + '）。',
             p: { A: A, dd: dd, P: P } };
  };

  /* ── §4-3 兩平行線的距離 ── */
  L1.parallelLineDist = function (r) {
    var A, dd, B, cr, t = 0;
    do { A = rp(r, -5, 5); dd = rnv(r, -4, 4, 1); B = rp(r, -5, 5); cr = cross(sub(B, A), dd); t++; } while (isZero(cr) && t < 150);
    var k = r.pick([2, -2, 3, -3, -1]);
    return { q: '設 ' + T('L_1:' + lineShort(A, dd, 't')) + '、' + T('L_2:' + lineShort(B, sc(k, dd), 's')) + '。(1) 說明 ' + T('L_1') + ' 與 ' + T('L_2') + ' 平行且不重合。(2) 求兩平行線的距離。',
             a: '(1) ' + T(vt(sc(k, dd)) + '=' + (k < 0 ? '-' : '') + (Math.abs(k) === 1 ? '' : Math.abs(k)) + vt(dd)) + ' 成比例，且 ' + T('L_2') + ' 上的點 ' + T(vt(B)) + ' 不在 ' + T('L_1') + ' 上　(2) ' + T(sqrtFracTex(n2(cr), n2(dd))),
             h: '兩平行線的距離 ＝ 其中一條上的點到另一條的距離：取 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '，' + T(ov('AB') + '=' + vt(sub(B, A))) + '，' + T('d=\\dfrac{\\left|' + ov('AB') + '\\times' + vec('d') + '\\right|}{\\left|' + vec('d') + '\\right|}') + '，其中 ' + T(ov('AB') + '\\times' + vec('d') + '=' + vt(cr)) + '。',
             p: { A: A, dd: dd, B: B, k: k } };
  };

  /* ── §4-4 兩直線的位置關係 ── */
  L1.twoLinesRel = function (r) {
    var mode = r.int(0, 2), d1, d2, P1, P2, X = [0, 0, 0], t = 0;
    if (mode === 0) {
      do { d1 = rnv(r, -4, 4, 1); d2 = rnv(r, -4, 4, 1); t++; } while (parallel(d1, d2) && t < 150);
      X = rp(r, -5, 5); P1 = add(X, sc(r.pick([1, -1, 2, -2]), d1)); P2 = add(X, sc(r.pick([1, -1, 2, -2]), d2));
    } else if (mode === 1) {
      d1 = rnv(r, -4, 4, 1); d2 = sc(r.pick([2, -2, 3, -1]), d1);
      P1 = rp(r, -5, 5);
      do { P2 = rp(r, -5, 5); t++; } while (parallel(sub(P2, P1), d1) && t < 80);
    } else {
      do { d1 = rnv(r, -4, 4, 1); d2 = rnv(r, -4, 4, 1); P1 = rp(r, -5, 5); P2 = rp(r, -5, 5); t++; } while ((parallel(d1, d2) || det3(d1, d2, sub(P2, P1)) === 0) && t < 250);
    }
    var dt = det3(d1, d2, sub(P2, P1));
    var ans = mode === 0 ? '相交，交點為 ' + T(vt(X)) : mode === 1 ? '平行（不重合）' : '歪斜（不共平面）';
    return { q: '判斷兩直線 ' + T('L_1:' + lineShort(P1, d1, 't')) + '、' + T('L_2:' + lineShort(P2, d2, 's')) + ' 的位置關係；若相交，求出交點。',
             a: ans,
             h: '先看方向向量 ' + T(vt(d1)) + ' 與 ' + T(vt(d2)) + ' 是否成比例；不成比例就算三重積 ' + T('\\det\\left(' + vec('d_1') + ',' + vec('d_2') + ',' + ov('P_1P_2') + '\\right)=' + dt) + '：等於 ' + T('0') + ' 表示共平面（相交），不等於 ' + T('0') + ' 就是歪斜。',
             p: { P1: P1, d1: d1, P2: P2, d2: d2, mode: mode } };
  };

  /* ── §4-5 兩歪斜線的距離 ── */
  L1.skewLineDist = function (r) {
    var d1, d2, P1, P2, cr, dt, t = 0;
    do { d1 = rnv(r, -4, 4, 1); d2 = rnv(r, -4, 4, 1); P1 = rp(r, -5, 5); P2 = rp(r, -5, 5); cr = cross(d1, d2); dt = det3(d1, d2, sub(P2, P1)); t++; } while ((isZero(cr) || dt === 0) && t < 250);
    return { q: '設 ' + T('L_1:' + lineShort(P1, d1, 't')) + '、' + T('L_2:' + lineShort(P2, d2, 's')) + ' 為兩歪斜線。求 ' + T('L_1') + ' 與 ' + T('L_2') + ' 的距離。',
             a: T(sqrtFracTex(dt * dt, n2(cr))),
             h: '把兩條線夾在兩個平行平面之間，共同法向量就是 ' + T(vec('d_1') + '\\times' + vec('d_2') + '=' + vt(cr)) + '；距離 ' + T('=\\dfrac{\\left|' + ov('P_1P_2') + '\\cdot\\left(' + vec('d_1') + '\\times' + vec('d_2') + '\\right)\\right|}{\\left|' + vec('d_1') + '\\times' + vec('d_2') + '\\right|}') + '，本題分子 ' + T('=\\left|' + dt + '\\right|') + '、分母 ' + T('=\\sqrt{' + n2(cr) + '}') + '。',
             p: { P1: P1, d1: d1, P2: P2, d2: d2 } };
  };

  /* ── §5-1 點對直線的對稱點 ── */
  L1.symPtLine = function (r) {
    var dd, w, H, P, t = 0;
    do { dd = rnv(r, -4, 4, 1); w = perpRand(r, dd, -1, 1); t++; } while (isZero(w) && t < 100);
    H = rp(r, -5, 5); P = add(H, w);
    var A = add(H, sc(r.pick([1, -1, 2, -2]), dd)), S = sub(H, w);
    return { q: '求點 ' + T('P' + vt(P)) + ' 對直線 ' + T('L:' + lineShort(A, dd, 't')) + ' 的對稱點 ' + T("P'") + '，並求 ' + T('P') + ' 到 ' + T('L') + ' 的距離。',
             a: T("P'" + vt(S)) + '，距離 ' + T(sqrtTex(n2(w))),
             h: '先求垂足 ' + T('H') + '：令 ' + T('H=A+t' + vec('d')) + '，由 ' + T(ov('PH') + '\\cdot' + vec('d') + '=0') + ' 解 ' + T('t') + '，本題得 ' + T('H' + vt(H)) + '；再用「' + T('H') + ' 是 ' + T('P') + ' 與 ' + T("P'") + ' 的中點」得 ' + T("P'=2H-P") + '。',
             p: { A: A, dd: dd, P: P } };
  };

  /* ── §5-2 對坐標平面的鏡面反射 ── */
  L1.mirrorReflect = function (r) {
    var pl = r.int(0, 2), mi = PLMISS[pl], M = rp(r, -6, 6); M[mi] = 0;
    var P, t = 0;
    do { P = rp(r, -6, 6); t++; } while ((P[mi] === 0 || isZero(sub(M, P))) && t < 80);
    var Pp = P.slice(); Pp[mi] = -Pp[mi];
    var v = sub(M, P), w = v.slice(); w[mi] = -w[mi];
    var wr = red(w);
    return { q: '在空間坐標中以 ' + T(PLANES[pl]) + ' 平面為鏡面，一光線從 ' + T('P' + vt(P)) + ' 射向鏡面上的點 ' + T('M' + vt(M)) + '。(1) 求 ' + T('P') + ' 對鏡面的對稱點 ' + T("P'") + '。(2) 求反射光線的方向向量（化為最簡整數）。(3) 寫出反射光線所在直線的參數式。',
             a: '(1) ' + T("P'" + vt(Pp)) + '　(2) ' + T(vt(wr)) + '　(3) ' + T(paramTex(M, wr, 's')),
             h: '對 ' + T(PLANES[pl]) + ' 平面對稱只把 ' + T(AXES[mi]) + ' 坐標變號。入射方向 ' + T(ov('PM') + '=' + vt(v)) + '，反射時垂直鏡面的那個分量（' + T(AXES[mi]) + ' 分量）變號 ⟹ ' + T(vt(w)) + '；它正好與 ' + T(ov("P'M")) + ' 同方向。',
             p: { pl: pl, P: P, M: M } };
  };

  /* ── §5-3 長方體的坐標化 ── */
  L1.boxCoord = function (r) {
    var a = r.int(1, 6), b = r.int(1, 6), c = r.int(1, 6);
    var n = [b * c, a * c, a * b], g = gcd3(n), nr = red(n), d = a * b * c / g;
    var N = n2(nr), num2 = Math.abs(dot(nr, [a, b, c]) - d);
    return { q: '長方體 ' + T('ABCD') + '-' + T('EFGH') + ' 中 ' + T('\\overline{AB}=' + a) + '、' + T('\\overline{AD}=' + b) + '、' + T('\\overline{AE}=' + c) + '（' + T('ABCD') + ' 為底面、' + T('\\overline{AE}') + ' 鉛直）。以 ' + T('A') + ' 為原點，' + T(ov('AB')) + '、' + T(ov('AD')) + '、' + T(ov('AE')) + ' 的方向為 ' + T('x,y,z') + ' 軸正向建立坐標。(1) 求平面 ' + T('BDE') + ' 的方程式。(2) 求 ' + T('A') + ' 到平面 ' + T('BDE') + ' 的距離。(3) 求 ' + T('G') + ' 到平面 ' + T('BDE') + ' 的距離。',
             a: '(1) ' + T(planeTex([nr[0], nr[1], nr[2], d])) + '　(2) ' + T(sqrtFracTex(d * d, N)) + '　(3) ' + T(sqrtFracTex(num2 * num2, N)),
             h: T('B(' + a + ',0,0)') + '、' + T('D(0,' + b + ',0)') + '、' + T('E(0,0,' + c + ')') + '、' + T('G(' + a + ',' + b + ',' + c + ')') + '；平面 ' + T('BDE') + ' 的法向量可取 ' + T(ov('BD') + '\\times' + ov('BE')) + '，化簡後是 ' + T(vt(nr)) + '。再用點到平面的距離公式，分母 ' + T('=\\sqrt{' + N + '}') + '。',
             p: { a: a, b: b, c: c } };
  };

  /* ═══════════════════════ L2 ═══════════════════════ */
  var L2 = {};

  /* 一條整數直線 ＋ 兩個含它的平面（法向量都垂直於方向向量、都已是最簡且首項為正） */
  function lineTwoPlanes(r) {
    var X, dd, b, n1, n2, t = 0;
    do {
      dd = rnv(r, -4, 4, 1); b = perpBasis(dd);
      n1 = redPos(add(sc(r.int(-2, 2), b[0]), sc(r.int(-2, 2), b[1])));
      n2 = redPos(add(sc(r.int(-2, 2), b[0]), sc(r.int(-2, 2), b[1])));
      t++;
    } while ((isZero(n1) || isZero(n2) || parallel(n1, n2)) && t < 150);
    if (isZero(n1) || isZero(n2) || parallel(n1, n2)) { dd = [1, 1, 1]; n1 = [1, -1, 0]; n2 = [0, 1, -1]; }
    X = rp(r, -5, 5);
    return { X: X, dd: dd, n1: n1, n2: n2 };
  }

  /* ── §1 三平面的位置關係 ── */
  L2.threePlanesRel = function (r) {
    var cse = r.int(0, 3), pl1, pl2, pl3, ans, hint, X, dd, n1, n2;
    if (cse === 0) {
      var m1, m2, m3, t = 0;
      do { m1 = redPos(rnv(r, -4, 4, 2)); m2 = redPos(rnv(r, -4, 4, 2)); m3 = redPos(rnv(r, -4, 4, 2)); t++; } while (det3(m1, m2, m3) === 0 && t < 200);
      X = rp(r, -5, 5);
      pl1 = [m1[0], m1[1], m1[2], dot(m1, X)]; pl2 = [m2[0], m2[1], m2[2], dot(m2, X)]; pl3 = [m3[0], m3[1], m3[2], dot(m3, X)];
      ans = '交於一點 ' + T(vt(X));
      hint = '三個法向量 ' + T(vt(m1)) + '、' + T(vt(m2)) + '、' + T(vt(m3)) + ' 的三重積 ' + T('=' + det3(m1, m2, m3)) + '，不為 ' + T('0') + ' ⟹ 三平面恰交於一點；用消去法解三元一次聯立即可。';
    } else if (cse === 3) {
      var g = lineTwoPlanes(r), k = r.pick([2, 3, -2, -3]), d2;
      n1 = g.n1; var d1 = r.int(-9, 9), t2 = 0;
      do { d2 = r.int(-24, 24); t2++; } while (gcd(Math.abs(k), Math.abs(d2)) !== 1 && t2 < 200);
      pl1 = [n1[0], n1[1], n1[2], d1];
      pl2 = normPlane([k * n1[0], k * n1[1], k * n1[2], d2]);
      var m3b = g.n2;
      pl3 = [m3b[0], m3b[1], m3b[2], r.int(-9, 9)];
      var kk = 0;
      for (var i3 = 0; i3 < 3; i3++) if (n1[i3] !== 0) { kk = pl2[i3] / n1[i3]; break; }
      ans = '交集是空集合（' + T('E_1') + ' 與 ' + T('E_2') + ' 平行且不重合，' + T('E_3') + ' 分別與它們交於兩條平行直線）';
      hint = T(vec('n_2') + '=' + (kk < 0 ? '-' : '') + (Math.abs(kk) === 1 ? '' : Math.abs(kk)) + vec('n_1')) + '，但把 ' + T('E_2') + ' 同除以 ' + T(String(kk)) + ' 後常數變成 ' + T(Fr.tex(F(pl2[3], kk))) + '，與 ' + T(String(pl1[3])) + ' 不同 ⟹ ' + T('E_1') + '、' + T('E_2') + ' 沒有共同點，三平面當然也沒有。';
    } else {
      var gg = lineTwoPlanes(r);
      X = gg.X; dd = gg.dd; n1 = gg.n1; n2 = gg.n2;
      var d1b = dot(n1, X), d2b = dot(n2, X), p = r.nz(-2, 2), q = r.nz(-2, 2);
      var n3 = add(sc(p, n1), sc(q, n2)), dlt = cse === 1 ? 0 : r.pick([1, -1, 2, -2, 3]);
      pl1 = [n1[0], n1[1], n1[2], d1b]; pl2 = [n2[0], n2[1], n2[2], d2b];
      pl3 = normPlane([n3[0], n3[1], n3[2], p * d1b + q * d2b + dlt]);
      var n3d = [pl3[0], pl3[1], pl3[2]], C = dot(n3d, X), D = pl3[3];
      ans = cse === 1 ? '交於一直線 ' + T(paramTex(X, red(dd), 't')) : '交集是空集合（三平面兩兩相交，但三條交線互相平行，沒有共同點）';
      hint = T('\\det\\left(' + vec('n_1') + ',' + vec('n_2') + ',' + vec('n_3') + '\\right)=0') + '，表示 ' + T(vec('n_3')) + ' 落在 ' + T(vec('n_1') + ',' + vec('n_2')) + ' 張出的平面上，第三式不是新的獨立條件。先解 ' + T('E_1,E_2') + ' 得交線（過 ' + T(vt(X)) + '、方向 ' + T(vt(red(dd))) + '），代入 ' + T('E_3') + ' 的左式恆得 ' + T(String(C)) + '，而 ' + T('E_3') + ' 的常數是 ' + T(String(D)) + '——' + (cse === 1 ? '兩者相同，整條交線都在 ' + T('E_3') + ' 上。' : '兩者不同，所以沒有共同點。');
    }
    return { q: '判斷三平面 ' + T('E_1:' + planeTex(pl1)) + '、' + T('E_2:' + planeTex(pl2)) + '、' + T('E_3:' + planeTex(pl3)) + ' 的交集是一點、一直線還是空集合；若是一點請求出該點，若是一直線請寫出它的參數式。',
             a: ans, h: hint, p: { pl1: normPlane(pl1), pl2: normPlane(pl2), pl3: normPlane(pl3), cse: cse } };
  };

  /* ── §1 過兩平面交線且過一點的平面 ── */
  L2.planeThroughInter = function (r) {
    var g, P, n, t = 0;
    do {
      g = lineTwoPlanes(r);
      P = rp(r, -6, 6);
      n = cross(g.dd, sub(P, g.X));
      t++;
    } while ((isZero(n) || parallel(n, g.n1) || parallel(n, g.n2)) && t < 200);
    var nr = redPos(n), X2 = add(g.X, g.dd), cn = red(cross(g.n1, g.n2));
    return { q: '設平面 ' + T('E_1:' + planeTex([g.n1[0], g.n1[1], g.n1[2], dot(g.n1, g.X)])) + '、' + T('E_2:' + planeTex([g.n2[0], g.n2[1], g.n2[2], dot(g.n2, g.X)])) + '。求通過 ' + T('E_1') + ' 與 ' + T('E_2') + ' 的交線且通過點 ' + T('P' + vt(P)) + ' 的平面 ' + T('E') + ' 的方程式。',
             a: T('E:' + planeTex(planeOf(nr, P))),
             h: '先把交線求出來：方向向量 ' + T(vec('n_1') + '\\times' + vec('n_2')) + ' 化簡後為 ' + T(vt(cn)) + '，交線上一點可取 ' + T(vt(g.X)) + '。在交線上取兩點 ' + T(vt(g.X)) + '、' + T(vt(X2)) + '，加上 ' + T('P') + ' 就是三點決定平面：法向量取 ' + T(vt(nr)) + '。',
             p: { X: g.X, dd: g.dd, n1: g.n1, n2: g.n2, P: P } };
  };

  /* ── §2 兩平面的角平分面 ── */
  L2.bisectPlanes = function (r) {
    var e1 = pyn(r), e2 = pyn(r), t = 0;
    while (parallel(e1.v, e2.v) && t < 80) { e2 = pyn(r); t++; }
    var n1 = e1.v, n2 = e2.v, L1n = e1.L, L2n = e2.L, d1 = r.int(-9, 9), d2 = r.int(-9, 9);
    var A = normPlane([L2n * n1[0] - L1n * n2[0], L2n * n1[1] - L1n * n2[1], L2n * n1[2] - L1n * n2[2], L2n * d1 - L1n * d2]);
    var B = normPlane([L2n * n1[0] + L1n * n2[0], L2n * n1[1] + L1n * n2[1], L2n * n1[2] + L1n * n2[2], L2n * d1 + L1n * d2]);
    return { q: '設平面 ' + T('E_1:' + planeTex([n1[0], n1[1], n1[2], d1])) + '、' + T('E_2:' + planeTex([n2[0], n2[1], n2[2], d2])) + '。(1) 求 ' + T('E_1') + ' 與 ' + T('E_2') + ' 的兩個角平分面的方程式。(2) 驗證這兩個角平分面互相垂直。',
             a: '(1) ' + T(planeTex(A)) + ' 與 ' + T(planeTex(B)) + '　(2) 兩法向量的內積 ' + T('=' + dot([A[0], A[1], A[2]], [B[0], B[1], B[2]])) + '，故互相垂直',
             h: '角平分面 ＝ 到兩平面等距的點：' + T('\\dfrac{\\left|' + lhsTex(n1[0], n1[1], n1[2]) + '-(' + d1 + ')\\right|}{' + L1n + '}=\\dfrac{\\left|' + lhsTex(n2[0], n2[1], n2[2]) + '-(' + d2 + ')\\right|}{' + L2n + '}') + '（分母 ' + T('\\left|' + vec('n_1') + '\\right|=' + L1n) + '、' + T('\\left|' + vec('n_2') + '\\right|=' + L2n) + '）；去絕對值取 ' + T('\\pm') + ' 兩種，各乘 ' + T(L1n + '\\times ' + L2n) + ' 化成整數。',
             p: { n1: n1, d1: d1, n2: n2, d2: d2, L1: L1n, L2: L2n } };
  };

  /* ── §2 被兩平行平面截出的線段 ── */
  L2.chordTwoPlanes = function (r) {
    var n = genN(r).v, dd, A, m, j, t = 0;
    do { dd = rnv(r, -4, 4, 1); t++; } while (dot(n, dd) === 0 && t < 150);
    A = rp(r, -4, 4); m = r.pick([1, -1, 2, -2]); j = r.pick([1, -1, 2, -2]);
    var d1 = dot(n, A), nd = dot(n, dd), d2 = d1 + m * nd, B = add(A, sc(m, dd)), P0 = add(A, sc(j, dd));
    return { q: '設兩平行平面 ' + T('E_1:' + planeTex([n[0], n[1], n[2], d1])) + '、' + T('E_2:' + planeTex([n[0], n[1], n[2], d2])) + '，直線 ' + T('L:' + lineShort(P0, dd, 't')) + ' 與它們分別交於 ' + T('A') + '、' + T('B') + '。(1) 求 ' + T('A') + '、' + T('B') + ' 的坐標。(2) 求 ' + T('\\overline{AB}') + '。(3) 求兩平面的距離。',
             a: '(1) ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '　(2) ' + T(sqrtTex(m * m * n2(dd))) + '　(3) ' + T(sqrtFracTex((d2 - d1) * (d2 - d1), n2(n))),
             h: '把 ' + T('L') + ' 的參數式代入兩個平面各解一次：' + T(vec('n') + '\\cdot' + vec('d') + '=' + nd) + '、' + T(vec('n') + '\\cdot P_0=' + dot(n, P0)) + '，分別得 ' + T('t=' + (-j)) + ' 與 ' + T('t=' + (m - j)) + '。(3) 兩平行平面的距離 ' + T('=\\dfrac{\\left|' + d1 + '-(' + d2 + ')\\right|}{\\sqrt{' + n2(n) + '}}') + '——注意它一般小於 ' + T('\\overline{AB}') + '。',
             p: { n: n, d1: d1, d2: d2, P0: P0, dd: dd } };
  };

  /* ── §2 四面體的體積與高 ── */
  L2.tetraVolHeight = function (r) {
    var A, B, C, D, cr, dv, t = 0;
    do { A = rp(r, -4, 4); B = rp(r, -4, 4); C = rp(r, -4, 4); D = rp(r, -4, 4); cr = cross(sub(C, B), sub(D, B)); dv = dot(cr, sub(A, B)); t++; } while ((isZero(cr) || dv === 0) && t < 200);
    var nr = redPos(cr), V = F(Math.abs(dv), 6), N = n2(cr);
    return { q: '設 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '、' + T('C' + vt(C)) + '、' + T('D' + vt(D)) + '。(1) 求平面 ' + T('BCD') + ' 的方程式。(2) 求 ' + T('\\triangle BCD') + ' 的面積。(3) 求四面體 ' + T('ABCD') + ' 的體積。(4) 求以 ' + T('\\triangle BCD') + ' 為底時的高。',
             a: '(1) ' + T(planeTex(planeOf(nr, B))) + '　(2) ' + T(radTex(1, N, 2)) + '　(3) ' + T('V=' + Fr.tex(V)) + '　(4) ' + T(sqrtFracTex(dv * dv, N)),
             h: T(ov('BC') + '=' + vt(sub(C, B))) + '、' + T(ov('BD') + '=' + vt(sub(D, B))) + '，外積 ' + T('=' + vt(cr)) + '（長度平方 ' + T('=' + N) + '）；面積 ' + T('=\\dfrac12\\left|' + ov('BC') + '\\times' + ov('BD') + '\\right|') + '，' + T('V=\\dfrac16\\left|' + dv + '\\right|') + '，高 ' + T('=\\dfrac{3V}{S}=\\dfrac{\\left|' + dv + '\\right|}{\\sqrt{' + N + '}}') + '。',
             p: { A: A, B: B, C: C, D: D } };
  };

  /* ── §2 過定直線的平面：到定點的最大距離 ── */
  L2.maxDistPlaneLine = function (r) {
    var A, dd, Q, cr, t = 0;
    do { A = rp(r, -5, 5); dd = rnv(r, -4, 4, 1); Q = rp(r, -5, 5); cr = cross(sub(Q, A), dd); t++; } while (isZero(cr) && t < 150);
    var AQ = sub(Q, A), nv = sub(sc(n2(dd), AQ), sc(dot(AQ, dd), dd)), nr = redPos(nv);
    return { q: '平面 ' + T('E') + ' 通過直線 ' + T('L:' + lineShort(A, dd, 't')) + '，點 ' + T('Q' + vt(Q)) + ' 不在 ' + T('L') + ' 上。(1) 求 ' + T('Q') + ' 到 ' + T('E') + ' 的距離的最大值。(2) 求此時 ' + T('E') + ' 的方程式。',
             a: '(1) ' + T(sqrtFracTex(n2(cr), n2(dd))) + '　(2) ' + T('E:' + planeTex(planeOf(nr, A))),
             h: '設 ' + T('H') + ' 是 ' + T('Q') + ' 在 ' + T('L') + ' 上的垂足。' + T('E') + ' 含 ' + T('L') + ' ⟹ ' + T('H') + ' 在 ' + T('E') + ' 上 ⟹ ' + T('Q') + ' 到 ' + T('E') + ' 的距離 ' + T('\\le\\overline{QH}') + '，等號在 ' + T('E\\perp\\overline{QH}') + '（即 ' + T(vec('n') + '=' + ov('HQ')) + '）時成立。所以最大值就是 ' + T('Q') + ' 到 ' + T('L') + ' 的距離：' + T(ov('AQ') + '=' + vt(AQ)) + '、' + T(ov('AQ') + '\\times' + vec('d') + '=' + vt(cr)) + '、' + T('\\left|' + vec('d') + '\\right|^2=' + n2(dd)) + '；法向量取 ' + T('\\left|' + vec('d') + '\\right|^2' + ov('AQ') + '-\\left(' + ov('AQ') + '\\cdot' + vec('d') + '\\right)' + vec('d') + '=' + vt(nv)) + '。',
             p: { A: A, dd: dd, Q: Q } };
  };

  /* ── §3 含直線且與已知平面垂直的平面 ── */
  L2.planeContainLinePerp = function (r) {
    var n, dd, P0, nf, t = 0;
    do { n = genN(r).v; dd = rnv(r, -4, 4, 1); nf = cross(dd, n); t++; } while (isZero(nf) && t < 150);
    P0 = rp(r, -6, 6);
    var d = r.int(-9, 9), nr = redPos(nf);
    return { q: '求包含直線 ' + T('L:' + lineShort(P0, dd, 't')) + ' 且與平面 ' + T('E:' + planeTex([n[0], n[1], n[2], d])) + ' 垂直的平面 ' + T('F') + ' 的方程式，並寫出 ' + T('F') + ' 的一個法向量。',
             a: T(vec('n_F') + '=' + vt(nr)) + '（或其非零倍數），' + T('F:' + planeTex(planeOf(nr, P0))),
             h: T('F') + ' 含 ' + T('L') + ' ⟹ ' + T(vec('n_F') + '\\perp' + vec('d')) + '；' + T('F\\perp E') + ' ⟹ ' + T(vec('n_F') + '\\perp' + vec('n')) + '。兩個垂直條件 ⟹ ' + T(vec('n_F') + '=' + vec('d') + '\\times' + vec('n') + '=' + vt(nf)) + '（約簡為 ' + T(vt(nr)) + '），再把 ' + T('L') + ' 上的點 ' + T(vt(P0)) + ' 代進去定常數。',
             p: { P0: P0, dd: dd, n: n, d: d } };
  };

  /* ── §3 兩平面的交線與坐標軸 ── */
  L2.interLineAxis = function (r) {
    var g, pli, ax, t = 0;
    do { g = lineTwoPlanes(r); t++; } while (nzc(g.dd) < 2 && t < 150);
    var cand = [0, 1, 2].filter(function (i) { return g.dd[PLMISS[i]] !== 0; });
    pli = cand.length ? r.pick(cand) : 0;
    var mi = PLMISS[pli];
    ax = r.int(0, 2);
    var tt = F(-g.X[mi], g.dd[mi]);
    var Pt = [0, 1, 2].map(function (i) { return Fr.add(F(g.X[i]), Fr.mul(tt, F(g.dd[i]))); });
    var cn = red(cross(g.n1, g.n2));
    return { q: '設平面 ' + T('E_1:' + planeTex([g.n1[0], g.n1[1], g.n1[2], dot(g.n1, g.X)])) + '、' + T('E_2:' + planeTex([g.n2[0], g.n2[1], g.n2[2], dot(g.n2, g.X)])) + '，兩平面交於直線 ' + T('L') + '。(1) 求 ' + T('L') + ' 的方向向量與參數式。(2) 求 ' + T('L') + ' 與 ' + T(PLANES[pli]) + ' 平面的交點。(3) 求 ' + T('L') + ' 與 ' + T(AXES[ax]) + ' 軸夾角的餘弦值。',
             a: '(1) ' + T(vec('d') + '=' + vt(cn)) + '（或其非零倍數），例如 ' + T(paramTex(g.X, red(g.dd), 't')) + '　(2) ' + T(vtF(Pt)) + '　(3) ' + T(sqrtFracTex(red(g.dd)[ax] * red(g.dd)[ax], n2(red(g.dd)))),
             h: '交線同時在兩平面上 ⟹ 方向向量同時垂直兩個法向量 ⟹ 取 ' + T(vec('n_1') + '\\times' + vec('n_2') + '=' + vt(cross(g.n1, g.n2))) + '（約簡為 ' + T(vt(cn)) + '）；再找交線上一點（本題可取 ' + T(vt(g.X)) + '）。(2) ' + T(PLANES[pli]) + ' 平面就是 ' + T(AXES[mi] + '=0') + '，代進參數式解 ' + T('t') + '。(3) 與 ' + T(AXES[ax]) + ' 軸的夾角就是方向向量與 ' + T(vt([ax === 0 ? 1 : 0, ax === 1 ? 1 : 0, ax === 2 ? 1 : 0])) + ' 的夾角。',
             p: { X: g.X, dd: g.dd, n1: g.n1, n2: g.n2, pli: pli, ax: ax } };
  };

  /* ── §4 公垂線段的兩端點 ── */
  L2.commonPerpSeg = function (r) {
    var d1, d2, cr, t = 0;
    do { d1 = rnv(r, -3, 3, 1); d2 = rnv(r, -3, 3, 1); cr = cross(d1, d2); t++; } while (isZero(cr) && t < 200);
    var crr = red(cr), P = rp(r, -4, 4), k = r.pick([1, -1, 2, -2]), Q = add(P, sc(k, crr));
    var P1 = add(P, sc(r.pick([1, -1, 2, -2]), d1)), P2 = add(Q, sc(r.pick([1, -1, 2, -2]), d2));
    return { q: '設 ' + T('L_1:' + lineShort(P1, d1, 't')) + '、' + T('L_2:' + lineShort(P2, d2, 's')) + ' 為兩歪斜線。(1) 求公垂線段的兩端點 ' + T('P\\in L_1') + '、' + T('Q\\in L_2') + '。(2) 求 ' + T('\\overline{PQ}') + '。(3) 驗證 ' + T(ov('PQ')) + ' 平行於 ' + T(vec('d_1') + '\\times' + vec('d_2')) + '。',
             a: '(1) ' + T('P' + vt(P)) + '、' + T('Q' + vt(Q)) + '　(2) ' + T(sqrtTex(k * k * n2(crr))) + '　(3) ' + T(ov('PQ') + '=' + vt(sc(k, crr))) + '，而 ' + T(vec('d_1') + '\\times' + vec('d_2') + '=' + vt(cr)) + '，兩者成比例，故平行',
             h: '令 ' + T('P=P_1+t' + vec('d_1')) + '、' + T('Q=P_2+s' + vec('d_2')) + '（兩條線一定要用不同的參數），由 ' + T(ov('PQ') + '\\cdot' + vec('d_1') + '=0') + ' 與 ' + T(ov('PQ') + '\\cdot' + vec('d_2') + '=0') + ' 解二元一次聯立。本題 ' + T('\\left|' + vec('d_1') + '\\right|^2=' + n2(d1)) + '、' + T('\\left|' + vec('d_2') + '\\right|^2=' + n2(d2)) + '、' + T(vec('d_1') + '\\cdot' + vec('d_2') + '=' + dot(d1, d2)) + '、' + T(ov('P_1P_2') + '=' + vt(sub(P2, P1))) + '。',
             p: { P1: P1, d1: d1, P2: P2, d2: d2 } };
  };

  /* ── §4 兩直線的角平分線 ── */
  L2.lineBisector = function (r) {
    var e1 = pyn(r), e2 = pyn(r), t = 0;
    while ((parallel(e1.v, e2.v) || dot(e1.v, e2.v) === 0) && t < 120) { e2 = pyn(r); t++; }
    var d1 = e1.v, d2 = e2.v, La = e1.L, Lb = e2.L, A = rp(r, -5, 5);
    var u = red(add(sc(Lb, d1), sc(La, d2))), v = red(sub(sc(Lb, d1), sc(La, d2))), dv = dot(d1, d2);
    var acute = dv > 0 ? u : v, name = dv > 0 ? '兩單位向量的和 ' : '兩單位向量的差 ';
    return { q: '設直線 ' + T('L_1') + '、' + T('L_2') + ' 交於點 ' + T('A' + vt(A)) + '，方向向量分別為 ' + T(vec('d_1') + '=' + vt(d1)) + '、' + T(vec('d_2') + '=' + vt(d2)) + '。(1) 求兩條角平分線的方向向量（化為最簡整數）。(2) 判斷哪一條是銳角平分線。(3) 寫出銳角平分線的參數式。',
             a: '(1) ' + T(vt(u)) + ' 與 ' + T(vt(v)) + '　(2) ' + T(vec('d_1') + '\\cdot' + vec('d_2') + '=' + dv) + (dv > 0 ? '，兩方向夾銳角 ⟹ ' : '，兩方向夾鈍角 ⟹ ') + name + T(vt(acute)) + ' 才是銳角平分線　(3) ' + T(paramTex(A, acute, 't')),
             h: '一定要先化成單位向量：' + T('\\dfrac{' + vt(d1) + '}{' + La + '}') + '、' + T('\\dfrac{' + vt(d2) + '}{' + Lb + '}') + '（' + T('\\left|' + vec('d_1') + '\\right|=' + La) + '、' + T('\\left|' + vec('d_2') + '\\right|=' + Lb) + '）；相加、相減後各乘 ' + T(La + '\\times ' + Lb) + ' 化成整數，再約分。',
             p: { A: A, d1: d1, d2: d2, L1: La, L2: Lb } };
  };

  /* ── §4 長方體中的歪斜線 ── */
  L2.boxSkewDist = function (r) {
    var cube = r() < 0.4, a = r.int(2, 6), b = cube ? a : r.int(2, 6), c = cube ? a : r.int(2, 6);
    var V = boxV(a, b, c), s1 = 'AG', s2 = 'BF', t = 0, u, v, cr, dt;
    do {
      var p1 = r.shuffle(VN).slice(0, 2).sort(), p2 = r.shuffle(VN).slice(0, 2).sort();
      s1 = p1.join(''); s2 = p2.join('');
      u = sub(V[p1[1]], V[p1[0]]); v = sub(V[p2[1]], V[p2[0]]); cr = cross(u, v);
      dt = det3(u, v, sub(V[p2[0]], V[p1[0]]));
      t++;
    } while ((isZero(cr) || dt === 0) && t < 300);
    if (isZero(cr) || dt === 0) { s1 = 'AG'; s2 = 'BF'; u = sub(V.G, V.A); v = sub(V.F, V.B); cr = cross(u, v); dt = det3(u, v, sub(V.B, V.A)); }
    var crr = red(cr), num = Math.abs(dt) / gcd3(cr);
    return { q: (cube ? '正立方體 ' : '長方體 ') + T('ABCD') + '-' + T('EFGH') + ' 中 ' + (cube ? T('\\overline{AB}=\\overline{AD}=\\overline{AE}=' + a) : T('\\overline{AB}=' + a) + '、' + T('\\overline{AD}=' + b) + '、' + T('\\overline{AE}=' + c)) + '（' + T('ABCD') + ' 為底面、' + T('\\overline{AE}') + ' 鉛直）。已知 ' + T('\\overline{' + s1 + '}') + ' 與 ' + T('\\overline{' + s2 + '}') + ' 所在的兩直線歪斜，求這兩條直線的距離與夾角的餘弦值。',
             a: '距離 ' + T(sqrtFracTex(num * num, n2(crr))) + '，' + T('\\cos\\theta=' + sqrtFracTex(dot(u, v) * dot(u, v), n2(u) * n2(v))),
             h: '以 ' + T('A') + ' 為原點建立坐標：' + T(ov(s1) + '=' + vt(u)) + '、' + T(ov(s2) + '=' + vt(v)) + '，' + T(ov(s1) + '\\times' + ov(s2) + '=' + vt(cr)) + '。距離 ' + T('=\\dfrac{\\left|' + ov(s1[0] + s2[0]) + '\\cdot\\left(' + ov(s1) + '\\times' + ov(s2) + '\\right)\\right|}{\\left|' + ov(s1) + '\\times' + ov(s2) + '\\right|}') + '（分子 ' + T('=\\left|' + dt + '\\right|') + '）；夾角用內積 ' + T('=' + dot(u, v)) + '。',
             p: { a: a, b: b, c: c, s1: s1, s2: s2 } };
  };

  /* ── §5 直線在平面上的投影 ── */
  L2.lineProjPlane = function (r) {
    var n = genNs(r).v, N, w, m, dd, t = 0;
    N = n2(n);
    do { w = perpRand(r, n, -1, 1); t++; } while ((isZero(w) || n2(w) > 60) && t < 120);
    if (isZero(w)) w = perpBasis(n)[0];
    w = red(w); m = r.pick([1, -1]);
    dd = add(w, sc(m, n));
    var X = rp(r, -5, 5), d = dot(n, X), j = r.pick([1, -1]), P0 = add(X, sc(j, dd));
    var Yp = add(X, sc(j, w)), sn = sqrtFracTex(m * m * N * N, N * n2(dd));
    return { q: '設直線 ' + T('L:' + lineShort(P0, dd, 't')) + '、平面 ' + T('E:' + planeTex([n[0], n[1], n[2], d])) + '。(1) 求 ' + T('L') + ' 與 ' + T('E') + ' 的交點。(2) 求 ' + T('L') + ' 在 ' + T('E') + ' 上的投影直線（寫成參數式）。(3) 求 ' + T('L') + ' 與這條投影直線的夾角正弦值。',
             a: '(1) ' + T(vt(X)) + '　(2) ' + T(paramTex(X, w, 's')) + '　(3) ' + T('\\sin\\theta=' + sn),
             h: '(1) 交點本身就在 ' + T('E') + ' 上，是現成的投影點（' + T(vec('n') + '\\cdot' + vec('d') + '=' + dot(n, dd)) + '、' + T(vec('n') + '\\cdot P_0=' + dot(n, P0)) + '）。(2) 再投影 ' + T('L') + ' 上另一點 ' + T('P_0' + vt(P0)) + '：它的投影點是 ' + T(vt(Yp)) + '，兩個投影點連起來就是投影直線，方向為 ' + T(vt(w)) + '。(3) 直線與它的投影的夾角就是直線與平面的夾角，用 ' + T('\\sin\\theta=\\dfrac{\\left|' + vec('d') + '\\cdot' + vec('n') + '\\right|}{\\left|' + vec('d') + '\\right|\\left|' + vec('n') + '\\right|}') + '。',
             p: { n: n, d: d, P0: P0, dd: dd } };
  };

  /* ── §5 線段在平面上的正射影長 ── */
  L2.segProjPlane = function (r) {
    var n = genNs(r).v, A0 = rp(r, -4, 4), w, t = 0;
    do { w = red(perpRand(r, n, -1, 1)); t++; } while (isZero(w) && t < 120);
    var p = r.pick([1, -1, 2, -2]), q;
    do { q = r.pick([1, -1, 2, -2, 3]); t++; } while (q === p && t < 60);
    var d = dot(n, A0), A = add(A0, sc(p, n)), B = add(add(A0, w), sc(q, n)), AB = sub(B, A);
    return { q: '設 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '、平面 ' + T('E:' + planeTex([n[0], n[1], n[2], d])) + '。(1) 求 ' + T('A') + '、' + T('B') + ' 在 ' + T('E') + ' 上的投影點 ' + T("A'") + '、' + T("B'") + '。(2) 求 ' + T('\\overline{AB}') + '。(3) 求線段 ' + T('\\overline{AB}') + ' 在 ' + T('E') + ' 上的正射影長 ' + T("\\overline{A'B'}") + '。',
             a: '(1) ' + T("A'" + vt(A0)) + '、' + T("B'" + vt(add(A0, w))) + '　(2) ' + T(sqrtTex(n2(AB))) + '　(3) ' + T(sqrtTex(n2(w))),
             h: '投影點用 ' + T("X'=X+t" + vec('n')) + ' 代入 ' + T('E') + ' 解 ' + T('t') + '：' + T('A') + ' 代入左式得 ' + T(String(dot(n, A))) + '、' + T('B') + ' 得 ' + T(String(dot(n, B))) + '，常數是 ' + T(String(d)) + '，' + T('\\left|' + vec('n') + '\\right|^2=' + n2(n)) + '。(3) 也可以用 ' + T("\\overline{A'B'}^2=\\overline{AB}^2-\\left(\\dfrac{" + ov('AB') + '\\cdot' + vec('n') + '}{\\left|' + vec('n') + '\\right|}\\right)^2') + ' 檢查。',
             p: { n: n, d: d, A: A, B: B } };
  };

  /* ── §5 光線的反射 ── */
  L2.rayReflectPlane = function (r) {
    var n = genNs(r).v, M = rp(r, -4, 4), w, t = 0;
    do { w = red(perpRand(r, n, -1, 1)); t++; } while ((isZero(w) || n2(w) > 60) && t < 120);
    if (isZero(w)) w = red(perpBasis(n)[0]);
    var m = r.pick([1, -1]), v = add(w, sc(m, n)), j = r.pick([1, 2, 3]);
    var P = sub(M, sc(j, v)), d = dot(n, M), refl = red(sub(w, sc(m, n))), N = n2(n);
    return { q: '空間中以平面 ' + T('E:' + planeTex([n[0], n[1], n[2], d])) + ' 為鏡面。一光線從點 ' + T('P' + vt(P)) + ' 沿方向 ' + T(vec('v') + '=' + vt(v)) + ' 前進。(1) 求光線射到 ' + T('E') + ' 上的入射點 ' + T('M') + '。(2) 求反射光線的方向向量（化為最簡整數）。(3) 寫出反射光線所在直線的參數式。',
             a: '(1) ' + T('M' + vt(M)) + '　(2) ' + T(vt(refl)) + '　(3) ' + T(paramTex(M, refl, 's')),
             h: '(1) 把 ' + T('P+t' + vec('v')) + ' 代入 ' + T('E') + '：' + T(vec('n') + '\\cdot P=' + dot(n, P)) + '、' + T(vec('n') + '\\cdot' + vec('v') + '=' + dot(n, v)) + ' ⟹ ' + T('t=' + j) + '。(2) 反射只把「平行 ' + T(vec('n')) + '」的分量變號：' + T(vec("v") + "'=" + vec('v') + '-\\dfrac{2\\left(' + vec('v') + '\\cdot' + vec('n') + '\\right)}{\\left|' + vec('n') + '\\right|^2}' + vec('n')) + '，本題 ' + T('\\left|' + vec('n') + '\\right|^2=' + N) + '。',
             p: { n: n, d: d, P: P, v: v } };
  };

  /* ── §5 平面上動點的最短路徑 ── */
  L2.shortestPath = function (r) {
    var n = genNs(r).v, N = n2(n), A0 = rp(r, -3, 3), w, t = 0;
    do { w = red(perpRand(r, n, -1, 1)); t++; } while (isZero(w) && t < 120);
    if (isZero(w)) w = red(perpBasis(n)[0]);
    var p = r.int(1, 2), q = r.int(1, 2), sg = r.sign(), B0 = add(A0, w);
    var d = dot(n, A0), A = add(A0, sc(sg * p, n)), B = add(B0, sc(sg * q, n));
    var Ap = sub(A0, sc(sg * p, n)), AB = sub(B, Ap);
    var tt = F(p, p + q);
    var Pt = [0, 1, 2].map(function (i) { return Fr.add(F(Ap[i]), Fr.mul(tt, F(AB[i]))); });
    return { q: '設平面 ' + T('E:' + planeTex([n[0], n[1], n[2], d])) + '、點 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '。(1) 說明 ' + T('A') + '、' + T('B') + ' 在 ' + T('E') + ' 的同一側。(2) 設 ' + T('P') + ' 為 ' + T('E') + ' 上的動點，求 ' + T('\\overline{PA}+\\overline{PB}') + ' 的最小值與此時 ' + T('P') + ' 的坐標。',
             a: '(1) 把 ' + T('A') + '、' + T('B') + ' 代入左式再減常數，分別得 ' + T(String(dot(n, A) - d)) + '、' + T(String(dot(n, B) - d)) + '，同號 ⟹ 同側　(2) 最小值 ' + T(sqrtTex(n2(AB))) + '，此時 ' + T('P' + vtF(Pt)),
             h: '把 ' + T('A') + ' 對 ' + T('E') + ' 作對稱點 ' + T("A'" + vt(Ap)) + '，則對 ' + T('E') + ' 上任何點都有 ' + T("\\overline{PA}=\\overline{PA'}") + '，於是 ' + T("\\overline{PA}+\\overline{PB}=\\overline{PA'}+\\overline{PB}\\ge\\overline{A'B}") + '；等號在 ' + T('P') + ' 為 ' + T("\\overline{A'B}") + ' 與 ' + T('E') + ' 的交點時成立（' + T(ov("A'B") + '=' + vt(AB)) + '）。',
             p: { n: n, d: d, A: A, B: B } };
  };

  /* ── §5 長方體中點到截面的距離 ── */
  L2.boxPlaneDist = function (r) {
    var cube = r() < 0.4, a = r.int(2, 6), b = cube ? a : r.int(2, 6), c = cube ? a : r.int(2, 6);
    var V = boxV(a, b, c), nm = ['A', 'C', 'H'], xn = 'F', nv = null, t = 0;
    do {
      var pick = r.shuffle(VN).slice(0, 3).sort();
      var cc = cross(sub(V[pick[1]], V[pick[0]]), sub(V[pick[2]], V[pick[0]]));
      t++;
      if (isZero(cc) || nzc(cc) < 2) continue;
      var rest = VN.filter(function (s) { return pick.indexOf(s) < 0; });
      var cand = rest.filter(function (s) { return dot(cc, sub(V[s], V[pick[0]])) !== 0; });
      if (!cand.length) continue;
      nm = pick; xn = r.pick(cand); nv = cc; break;
    } while (t < 300);
    if (!nv) { nm = ['A', 'C', 'H']; xn = 'F'; nv = cross(sub(V.C, V.A), sub(V.H, V.A)); }
    var nr = redPos(nv), num = Math.abs(dot(nr, sub(V[xn], V[nm[0]]))), N = n2(nr);
    var pn = nm.join('');
    return { q: (cube ? '正立方體 ' : '長方體 ') + T('ABCD') + '-' + T('EFGH') + ' 中 ' + (cube ? T('\\overline{AB}=\\overline{AD}=\\overline{AE}=' + a) : T('\\overline{AB}=' + a) + '、' + T('\\overline{AD}=' + b) + '、' + T('\\overline{AE}=' + c)) + '（' + T('ABCD') + ' 為底面、' + T('\\overline{AE}') + ' 鉛直）。(1) 以 ' + T('A') + ' 為原點建立坐標，求平面 ' + T(pn) + ' 的方程式。(2) 求點 ' + T(xn) + ' 到平面 ' + T(pn) + ' 的距離。(3) 求平面 ' + T(pn) + ' 與底面 ' + T('ABCD') + ' 夾角的餘弦值。',
             a: '(1) ' + T(planeTex(planeOf(nr, V[nm[0]]))) + '　(2) ' + T(sqrtFracTex(num * num, N)) + '　(3) ' + T(nr[2] === 0 ? '0\\ \\text{（兩平面垂直）}' : sqrtFracTex(nr[2] * nr[2], N)),
             h: '三個頂點的坐標是 ' + T(nm[0] + vt(V[nm[0]])) + '、' + T(nm[1] + vt(V[nm[1]])) + '、' + T(nm[2] + vt(V[nm[2]])) + '，法向量取外積並約簡得 ' + T(vt(nr)) + '；' + T(xn + vt(V[xn])) + ' 代入左式再減常數得 ' + T('\\left|' + (dot(nr, sub(V[xn], V[nm[0]]))) + '\\right|') + '。(3) 底面 ' + T('ABCD') + ' 的法向量是 ' + T('(0,0,1)') + '。',
             p: { a: a, b: b, c: c, nm: pn, xn: xn } };
  };

  /* ══════════════════════════════════════════════════════════ */
  /* ══════════════════════════════════════════════════════════
     L1 解題步驟（s：每步一段 HTML）與第一層提示（h1：只講「這是哪一型、第一步做什麼」，不帶數字）
     全部由 p（與 o.a）重算，所以與題目、答案一定一致；最後一步以「答案：」收尾。
     用法：用 splice_all_11b2.py 插在 META_L1（var META_L1 = [）之前，並把 wrapAll(L1) 換成 wrapAll(L1, L1_SOL, L1_H1)。
     ══════════════════════════════════════════════════════════ */
  function solFin(o) { return '答案：' + o.a + '。'; }
  function solAbsT(s) { return '\\left|' + s + '\\right|'; }
  function solParT(s) { return '\\left(' + s + '\\right)'; }
  function solIsq(n) { return Math.round(Math.sqrt(n)); }
  function solNeg(x) { return x < 0 ? '(' + x + ')' : String(x); }
  function solK(k) { return (k < 0 ? '-' : '') + (Math.abs(k) === 1 ? '' : Math.abs(k)); }   /* 倍數寫在向量前面 */
  function solFp(f) { return f.n < 0 ? solParT(Fr.tex(f, true)) : Fr.tex(f, true); }         /* 負分數當乘數要加括號 */
  function solDistT(num, N) { return '\\dfrac{' + solAbsT(String(num)) + '}{\\sqrt{' + N + '}}'; }

  var L1_H1 = {
    planePointNormal: '這是「由點與法向量寫平面」：法向量的三個分量就是 $x,y,z$ 的係數，先寫出左式，再把已知點代進去定常數。',
    planeThreePts: '這是「三點決定平面」：先把兩個邊向量算出來，法向量取這兩個向量的外積。',
    planeIntercepts: '這是「讀平面的係數」：法向量直接從係數讀出來；求與某一軸的交點就把另外兩個坐標設成 $0$。',
    planeSpecial: '這是「特殊位置的平面」：含某條坐標軸的平面過原點又缺那一項，平行某個坐標平面的平面只剩一個變數。',
    twoPlanesRel: '這是「兩平面的位置關係」：一切看兩個法向量，先判斷成不成比例，再算內積。',
    coplanarK: '這是「四點共平面求未知數」：先用前三點寫出平面方程式，再把第四點代進去解一次方程式。',
    ptPlaneDist: '這是「點到平面的距離」：分子是把點代入左式再減常數後取絕對值，分母是法向量的長度。',
    parallelPlaneDist: '這是「平行平面與兩平面的距離」：先把兩個方程式的左邊調成完全一樣，再比較常數項。',
    planeProjSym: '這是「點對平面的投影點與對稱點」：投影點在過該點的法線上，令它等於原點加 $t$ 倍法向量再代入平面解 $t$。',
    planeDistUnknown: '這是「已知距離求未知數」：先把點代入左式，再用距離公式列出帶絕對值的方程式，去絕對值會有兩個解。',
    tetraPlaneDist: '這是「三頂點的平面與體積法」：法向量取兩個邊向量的外積，距離與體積都靠同一個三重積。',
    lineParamRatio: '這是「直線的參數式與比例式」：參數式是起點坐標加上 $t$ 倍的方向分量，比例式是把 $t$ 消掉。',
    lineReadBack: '這是「由直線方程式讀回點與方向」：分母（或 $t$ 的係數）就是方向向量，分子裡被減掉的數就是點的坐標。',
    lineTwoPts: '這是「兩點決定直線」：方向向量取兩點相減，可以先約掉公因數再寫參數式。',
    linePlaneInt: '這是「直線與平面的交點」：把參數式的三條代入平面左式，整理成 $t$ 的一次方程式。',
    linePlaneRel: '這是「直線與平面的位置關係」：先算方向向量與法向量的內積，內積是 $0$ 再看線上的點在不在平面上。',
    linePlaneAngle: '這是「直線與平面的夾角」：線與面的夾角用正弦，分子是方向向量與法向量內積的絕對值。',
    ptLineDist: '這是「點到直線的距離」：用外積，分子是連接向量與方向向量的外積長度，分母是方向向量的長度。',
    footPerp: '這是「垂足」：令垂足等於直線上一點加 $t$ 倍方向向量，再用垂直條件解出 $t$。',
    parallelLineDist: '這是「兩平行線的距離」：先確認方向成比例、點不在另一條上，再算其中一點到另一條的距離。',
    twoLinesRel: '這是「兩直線的位置關係」：先看方向向量成不成比例，不成比例就用三重積判斷共不共平面。',
    skewLineDist: '這是「兩歪斜線的距離」：共同法向量取兩個方向向量的外積，再把連接向量投影到它上面。',
    symPtLine: '這是「點對直線的對稱點」：先求垂足，再用「垂足是原來的點與對稱點的中點」。',
    mirrorReflect: '這是「對坐標平面的鏡面反射」：對某個坐標平面對稱，只要把那一個坐標變號。',
    boxCoord: '這是「長方體的坐標化」：先以一個頂點為原點把各頂點坐標寫出來，再用向量方法算平面與距離。'
  };

  var L1_SOL = {};

  /* §1-1 由點與法向量寫平面 */
  L1_SOL.planePointNormal = function (p, o) {
    var n = p.n, P0 = p.P0, Q = p.Q, d = dot(n, P0);
    var pl = normPlane([n[0], n[1], n[2], d]), pn = [pl[0], pl[1], pl[2]], qv = dot(pn, Q);
    return ['(1) 法向量的三個分量就是 ' + T('x,y,z') + ' 的係數，先把平面寫成 ' + T(lhsTex(n[0], n[1], n[2]) + '=d') + '。',
      '把 ' + T('P_0' + vt(P0)) + ' 代入左式定常數：' + T(subTex(n, P0) + '=' + d) + '，化成最簡整數、首項為正得 ' + T('E:' + planeTex(pl)) + '。',
      '(2) 把 ' + T('Q' + vt(Q)) + ' 代入左式：' + T(subTex(pn, Q) + '=' + qv) + '，與常數項 ' + T(String(pl[3]))
        + (qv === pl[3] ? ' 相等，所以 ' + T('Q') + ' 在 ' + T('E') + ' 上。' : ' 不相等，所以 ' + T('Q') + ' 不在 ' + T('E') + ' 上。') + solFin(o)];
  };

  /* §1-2 三點決定平面 */
  L1_SOL.planeThreePts = function (p, o) {
    var A = p.A, u = sub(p.B, A), v = sub(p.C, A), n = cross(u, v), nr = redPos(n), pl = planeOf(nr, A);
    return ['先做兩個邊向量：' + T(ov('AB') + '=' + vt(p.B) + '-' + vt(A) + '=' + vt(u)) + '、' + T(ov('AC') + '=' + vt(p.C) + '-' + vt(A) + '=' + vt(v)) + '。',
      '法向量取外積：' + T(ov('AB') + '\\times' + ov('AC') + '=' + vt(n)) + '，化成最簡整數、首項為正得 ' + T(vec('n') + '=' + vt(nr)) + '。',
      '把 ' + T('A' + vt(A)) + ' 代入 ' + T(lhsTex(nr[0], nr[1], nr[2]) + '=d') + '：' + T(subTex(nr, A) + '=' + pl[3]) + '，所以 ' + T('E:' + planeTex(pl)) + '。' + solFin(o)];
  };

  /* §1-3 讀係數：法向量與坐標軸交點 */
  L1_SOL.planeIntercepts = function (p, o) {
    var pl = p.pl, x0 = F(pl[3], pl[0]), y0 = F(pl[3], pl[1]), z0 = F(pl[3], pl[2]);
    var V = F(Math.abs(pl[3] * pl[3] * pl[3]), 6 * Math.abs(pl[0] * pl[1] * pl[2]));
    return ['(1) 法向量直接讀 ' + T('x,y,z') + ' 的係數：' + T(vec('n') + '=' + vt([pl[0], pl[1], pl[2]])) + '（或它的非零倍數）。',
      '(2) 與 ' + T('x') + ' 軸的交點：令 ' + T('y=z=0') + ' 得 ' + T(term(pl[0], 'x', true) + '=' + pl[3]) + '，' + T('x=' + Fr.tex(x0)) + '；同理令 ' + T('x=z=0') + ' 得 ' + T('y=' + Fr.tex(y0)) + '、令 ' + T('x=y=0') + ' 得 ' + T('z=' + Fr.tex(z0)) + '，三個交點是 ' + T(vtF([x0, F(0), F(0)])) + '、' + T(vtF([F(0), y0, F(0)])) + '、' + T(vtF([F(0), F(0), z0])) + '。',
      '(3) 這三個交點與原點圍成牆角型四面體：' + T('V=\\dfrac16' + solAbsT('x_0y_0z_0') + '=\\dfrac16' + solAbsT(solFp(x0) + '\\cdot' + solFp(y0) + '\\cdot' + solFp(z0)) + '=' + Fr.tex(V)) + '。' + solFin(o)];
  };

  /* §1-4 特殊位置的平面 */
  L1_SOL.planeSpecial = function (p, o) {
    var P = p.P, ax = p.ax, i = (ax + 1) % 3, j = (ax + 2) % 3;
    var co = [0, 0, 0]; co[i] = P[j]; co[j] = -P[i];
    var E1 = normPlane([co[0], co[1], co[2], 0]);
    var mi = PLMISS[p.pl], E2 = [0, 0, 0, P[mi]]; E2[mi] = 1;
    var LT = ['a', 'b', 'c'], form = ax === 0 ? 'by+cz=0' : ax === 1 ? 'ax+cz=0' : 'ax+by=0';
    return ['(1) 平面含 ' + T(AXES[ax]) + ' 軸 ⟹ 它通過原點（常數項為 ' + T('0') + '），而且式子裡不會出現 ' + T(AXES[ax]) + ' 這一項，形如 ' + T(form) + '。',
      '把 ' + T('P' + vt(P)) + ' 代進去：' + T(term(P[i], LT[i], true) + term(P[j], LT[j], false) + '=0') + '，可取 ' + T('(' + LT[i] + ',' + LT[j] + ')=(' + P[j] + ',' + (-P[i]) + ')') + '，整理得 ' + T('E_1:' + planeTex(E1)) + '。',
      '(2) 平行 ' + T(PLANES[p.pl]) + ' 平面 ⟹ 形如 ' + T(AXES[mi] + '=k') + '，而 ' + T('k') + ' 就是 ' + T('P') + ' 的 ' + T(AXES[mi]) + ' 坐標 ' + T(String(P[mi])) + '，即 ' + T('E_2:' + planeTex(E2)) + '。' + solFin(o)];
  };

  /* §1-5 兩平面的位置關係與夾角 */
  L1_SOL.twoPlanesRel = function (p, o) {
    var n1 = p.n1, d1 = p.d1, pl2 = p.pl2, nb = [pl2[0], pl2[1], pl2[2]], dv = dot(n1, nb), i;
    var s1 = '兩平面的關係全看法向量：' + T(vec('n_1') + '=' + vt(n1)) + '、' + T(vec('n_2') + '=' + vt(nb)) + '。';
    if (p.mode === 0) {
      var kk = 1;
      for (i = 0; i < 3; i++) if (n1[i] !== 0) { kk = nb[i] / n1[i]; break; }
      return [s1,
        T(vec('n_2') + '=' + vt(nb) + '=' + solK(kk) + vt(n1) + '=' + solK(kk) + vec('n_1')) + '，兩個法向量成比例，所以兩平面平行。',
        '再比常數：' + T('E_2') + ' 兩邊同除以 ' + T(String(kk)) + ' 得 ' + T(lhsTex(n1[0], n1[1], n1[2]) + '=' + Fr.tex(F(pl2[3], kk))) + '，與 ' + T('E_1') + ' 的常數 ' + T(String(d1)) + ' 不同 ⟹ 兩平面平行而不重合（沒有夾角要算）。' + solFin(o)];
    }
    if (p.mode === 1) {
      return [s1,
        '算內積：' + T(vec('n_1') + '\\cdot' + vec('n_2') + '=' + subTex(n1, nb) + '=0') + '，兩個法向量互相垂直。',
        '法向量垂直 ⟹ 兩平面垂直，夾角 ' + T('\\theta=90^\\circ') + '，' + T('\\cos\\theta=0') + '。' + solFin(o)];
    }
    return [s1,
      '算內積：' + T(vec('n_1') + '\\cdot' + vec('n_2') + '=' + subTex(n1, nb) + '=' + dv) + '，不是 ' + T('0') + '，兩向量也不成比例，所以兩平面相交且不垂直。',
      '夾角取銳角：' + T('\\cos\\theta=\\dfrac{' + solAbsT(vec('n_1') + '\\cdot' + vec('n_2')) + '}{' + solAbsT(vec('n_1')) + solAbsT(vec('n_2')) + '}=\\dfrac{' + solAbsT(String(dv)) + '}{\\sqrt{' + n2(n1) + '}\\sqrt{' + n2(nb) + '}}=' + sqrtFracTex(dv * dv, n2(n1) * n2(nb))) + '。' + solFin(o)];
  };

  /* §1-6 四點共平面求未知數 */
  L1_SOL.coplanarK = function (p, o) {
    var A = p.A, u = sub(p.B, A), v = sub(p.C, A), n = cross(u, v), nr = redPos(n), pl = planeOf(nr, A);
    var D = p.D, hide = p.hide, rest = 0, lhs = '', i;
    for (i = 0; i < 3; i++) {
      if (i === hide) { lhs += (lhs === '' ? '' : '+') + '(' + nr[i] + ')k'; continue; }
      rest += nr[i] * D[i];
      if (nr[i] !== 0) lhs += (lhs === '' ? '' : '+') + '(' + nr[i] + ')(' + D[i] + ')';
    }
    return ['(1) ' + T(ov('AB') + '=' + vt(u)) + '、' + T(ov('AC') + '=' + vt(v)) + '，法向量取 ' + T(ov('AB') + '\\times' + ov('AC') + '=' + vt(n)) + '，化簡為 ' + T(vt(nr)) + '。',
      '把 ' + T('A' + vt(A)) + ' 代入定常數：' + T(subTex(nr, A) + '=' + pl[3]) + '，所以平面是 ' + T(planeTex(pl)) + '。',
      '(2) 四點共平面 ⟹ ' + T('D') + ' 也滿足這個方程式：' + T(lhs + '=' + pl[3]) + '，即 ' + T(term(nr[hide], 'k', true) + '=' + (pl[3] - rest)) + '，所以 ' + T('k=' + D[hide]) + '。' + solFin(o)];
  };

  /* §2-1 點到平面的距離 */
  L1_SOL.ptPlaneDist = function (p, o) {
    var n = p.n, P = p.P, d = p.d, N = n2(n), v0 = dot(n, P), v1 = v0 - d;
    return ['距離公式 ' + T('=\\dfrac{' + solAbsT('ax_0+by_0+cz_0-d') + '}{\\sqrt{a^2+b^2+c^2}}') + '，本題分母 ' + T('=\\sqrt{' + N + '}') + '。',
      '(1) 把 ' + T('P' + vt(P)) + ' 代入左式：' + T(subTex(n, P) + '=' + v0) + '，再減常數 ' + T(String(d)) + ' 得 ' + T(String(v1)) + '，所以距離 ' + T('=' + solDistT(v1, N) + '=' + sqrtFracTex(v1 * v1, N)) + '。',
      '(2) 原點代入左式得 ' + T('0') + '，分子是 ' + T(solAbsT('0-' + solNeg(d)) + '=' + Math.abs(d)) + '，距離 ' + T('=' + solDistT(Math.abs(d), N) + '=' + sqrtFracTex(d * d, N)) + '。' + solFin(o)];
  };

  /* §2-2 平行平面與兩平行平面的距離 */
  L1_SOL.parallelPlaneDist = function (p, o) {
    var n = p.n, N = n2(n), d1 = p.d1, i;
    if (p.mode === 0) {
      var pl2 = p.pl2, kk = 1;
      for (i = 0; i < 3; i++) if (n[i] !== 0) { kk = pl2[i] / n[i]; break; }
      var c2 = F(pl2[3], kk), df = Fr.sub(F(d1), c2);
      return ['(1) ' + T(vec('n_2') + '=' + vt([pl2[0], pl2[1], pl2[2]]) + '=' + solK(kk) + vt(n) + '=' + solK(kk) + vec('n_1')) + '，兩個法向量成比例 ⟹ 兩平面平行。',
        '把 ' + T('E_2') + ' 兩邊同除以 ' + T(String(kk)) + '，左邊就與 ' + T('E_1') + ' 完全一樣：' + T(lhsTex(n[0], n[1], n[2]) + '=' + Fr.tex(c2)) + '；常數 ' + T(Fr.tex(c2)) + ' 與 ' + T(String(d1)) + ' 不同，所以不重合。',
        '(2) 兩平行平面的距離 ' + T('=\\dfrac{' + solAbsT('d_1-d_2') + '}{' + solAbsT(vec('n')) + '}=\\dfrac{' + Fr.tex(F(Math.abs(df.n), df.d), true) + '}{\\sqrt{' + N + '}}=' + radTex(Math.abs(df.n), N, df.d * N)) + '。' + solFin(o)];
    }
    var P = p.P, d2b = dot(n, P), df2 = d1 - d2b;
    return ['(1) 平行 ⟹ 法向量一樣，只有常數項不同，先設 ' + T('F:' + lhsTex(n[0], n[1], n[2]) + '=k') + '。',
      '把 ' + T('P' + vt(P)) + ' 代入左式：' + T(subTex(n, P) + '=' + d2b) + '，所以 ' + T('F:' + planeTex([n[0], n[1], n[2], d2b])) + '。',
      '(2) 距離 ' + T('=\\dfrac{' + solAbsT(d1 + '-' + solNeg(d2b)) + '}{\\sqrt{' + N + '}}=' + sqrtFracTex(df2 * df2, N)) + '。' + solFin(o)];
  };

  /* §2-3 點對平面的投影點與對稱點 */
  L1_SOL.planeProjSym = function (p, o) {
    var n = p.n, d = p.d, P = p.P, N = n2(n), v0 = dot(n, P), t = (d - v0) / N;
    var H = add(P, sc(t, n)), S = add(P, sc(2 * t, n)), at = Math.abs(t);
    var raw = (at === 1 ? '' : at) + '\\sqrt{' + N + '}', fin = sqrtTex(t * t * N);
    return ['(1) 投影點在過 ' + T('P') + ' 的法線上，令 ' + T('H=P+t' + vec('n')) + '；代入 ' + T('E') + ' 得 ' + T(vec('n') + '\\cdot P+t' + solAbsT(vec('n')) + '^2=' + d) + '。',
      '本題 ' + T(vec('n') + '\\cdot P=' + subTex(n, P) + '=' + v0) + '、' + T(solAbsT(vec('n')) + '^2=' + N) + '，解 ' + T(v0 + term(N, 't', false) + '=' + d) + ' 得 ' + T('t=' + t) + '，所以 ' + T('H=' + vt(P) + term(t, vt(n), false) + '=' + vt(H)) + '，即 ' + T('H' + vt(H)) + '。',
      '(2) ' + T('H') + ' 是 ' + T('P') + ' 與 ' + T("P'") + ' 的中點 ⟹ ' + T("P'=P+2t" + vec('n') + '=' + vt(S)) + '，即 ' + T("P'" + vt(S)) + '。(3) 距離 ' + T('\\overline{PH}=' + solAbsT('t') + solAbsT(vec('n')) + '=' + raw + (fin === raw ? '' : '=' + fin)) + '。' + solFin(o)];
  };

  /* §2-4 已知距離求未知數 */
  L1_SOL.planeDistUnknown = function (p, o) {
    var n = p.n, P = p.P, D = p.D, N = n2(n), L = solIsq(N), M = D * L, i;
    if (p.mode === 0) {
      var v1 = dot(n, P);
      return ['先把 ' + T('P' + vt(P)) + ' 代入左式：' + T(subTex(n, P) + '=' + v1) + '；法向量的長度 ' + T(solAbsT(vec('n')) + '=\\sqrt{' + N + '}=' + L) + '。',
        '距離公式給出 ' + T('\\dfrac{' + solAbsT(v1 + '-k') + '}{' + L + '}=' + D) + '，兩邊乘 ' + T(String(L)) + ' 得 ' + T(solAbsT(v1 + '-k') + '=' + M) + '。',
        '去絕對值：' + T(v1 + '-k=' + M) + ' 或 ' + T(v1 + '-k=' + (-M)) + '，解得 ' + T('k=' + (v1 - M)) + ' 或 ' + T('k=' + (v1 + M)) + '（兩解）。' + solFin(o)];
    }
    var ax = p.ax, d = p.d, rest = 0;
    for (i = 0; i < 3; i++) if (i !== ax) rest += n[i] * P[i];
    var t1 = F(d - rest - M, n[ax]), t2 = F(d - rest + M, n[ax]);
    var lhsT = term(n[ax], 't', true) + term(rest, '', false), core = term(n[ax], 't', true) + term(rest - d, '', false);
    return ['把 ' + T('P') + ' 代入左式（只有 ' + T(AXES[ax]) + ' 坐標帶未知數）：' + T(lhsT) + '；法向量的長度 ' + T(solAbsT(vec('n')) + '=\\sqrt{' + N + '}=' + L) + '。',
      '距離公式的分子是左式再減常數 ' + T(String(d)) + '：' + T('\\dfrac{' + solAbsT(lhsT + '-' + solNeg(d)) + '}{' + L + '}=\\dfrac{' + solAbsT(core) + '}{' + L + '}=' + D) + '，所以 ' + T(solAbsT(core) + '=' + D + '\\times ' + L + '=' + M) + '。',
      '去絕對值解兩次：' + T(term(n[ax], 't', true) + '=' + (d - rest - M)) + ' 或 ' + T(term(n[ax], 't', true) + '=' + (d - rest + M)) + '，得 ' + T('t=' + Fr.tex(t1)) + ' 或 ' + T('t=' + Fr.tex(t2)) + '（兩解）。' + solFin(o)];
  };

  /* §2-5 三頂點的平面與體積法對照 */
  L1_SOL.tetraPlaneDist = function (p, o) {
    var A = p.A, u = sub(p.B, A), v = sub(p.C, A), w = sub(p.D, A);
    var cr = cross(u, v), nr = redPos(cr), pl = planeOf(nr, A), dv = dot(cr, w), V = F(Math.abs(dv), 6);
    return ['(1) ' + T(ov('AB') + '=' + vt(u)) + '、' + T(ov('AC') + '=' + vt(v)) + '，法向量取 ' + T(ov('AB') + '\\times' + ov('AC') + '=' + vt(cr)) + '，化簡為 ' + T(vt(nr)) + '。',
      '把 ' + T('A' + vt(A)) + ' 代入：' + T(subTex(nr, A) + '=' + pl[3]) + '，所以平面 ' + T('ABC:' + planeTex(pl)) + '。',
      '(2) ' + T(ov('AD') + '=' + vt(w)) + '，三重積 ' + T(ov('AD') + '\\cdot' + solParT(ov('AB') + '\\times' + ov('AC')) + '=' + dv) + '；距離 ' + T('=' + solDistT(dv, n2(cr)) + '=' + sqrtFracTex(dv * dv, n2(cr))) + '。',
      '(3) 四面體體積 ' + T('V=\\dfrac16' + solAbsT(String(dv)) + '=' + Fr.tex(V)) + '——和 (2) 用的是同一個三重積。' + solFin(o)];
  };

  /* §3-1 參數式與比例式 */
  L1_SOL.lineParamRatio = function (p, o) {
    var P0 = p.P0, d = p.d, nz = [], zr = [], i;
    for (i = 0; i < 3; i++) { if (d[i] === 0) zr.push(i); else nz.push(i); }
    var solve = 't=' + nz.map(function (k) { return '\\dfrac{' + AXES[k] + (P0[k] === 0 ? '' : (P0[k] < 0 ? '+' + (-P0[k]) : '-' + P0[k])) + '}{' + d[k] + '}'; }).join('=');
    var note = zr.length === 0 ? '三個分量都不是 ' + T('0') + '，三條式子都解得出 ' + T('t') + '，所以三個分式相等。'
      : zr.map(function (k) { return T(vec('d')) + ' 的 ' + T(AXES[k]) + ' 分量是 ' + T('0') + '，那一條與 ' + T('t') + ' 無關，要單獨寫成 ' + T(AXES[k] + '=' + P0[k]); }).join('；') + '。';
    return ['參數式就是「起點坐標加上 ' + T('t') + ' 倍的方向分量」：' + T(paramTex(P0, d, 't')) + '（' + T('t\\in\\mathbb{R}') + '）。',
      '再把 ' + T('t') + ' 消掉：' + T(solve) + '。' + note,
      '所以比例式是 ' + T(ratioTex(P0, d)) + '。' + solFin(o)];
  };

  /* §3-2 由方程式讀回點與方向 */
  L1_SOL.lineReadBack = function (p, o) {
    var P0 = p.P0, d = p.d, Q = p.Q, form = p.form, i;
    var u = sub(Q, P0), cr = cross(u, d), on = isZero(cr), m = 0;
    for (i = 0; i < 3; i++) if (d[i] !== 0) { m = u[i] / d[i]; break; }
    var other = form === 0 ? paramTex(P0, d, 't') : ratioTex(P0, d);
    return ['(1) ' + (form === 0 ? '比例式的分母' : '參數式裡 ' + T('t') + ' 的係數') + '就是方向向量 ' + T(vec('d') + '=' + vt(d)) + '；'
        + (form === 0 ? '分子裡被減掉的數（符號要翻過來）' : '常數的部分') + '就是直線上的一點 ' + T('P_0' + vt(P0)) + '。',
      '(2) ' + T(ov('P_0Q') + '=' + vt(Q) + '-' + vt(P0) + '=' + vt(u)) + '，' + T(ov('P_0Q') + '\\times' + vec('d') + '=' + vt(cr))
        + (on ? '，外積是零向量 ⟹ 兩向量平行，取 ' + T('t=' + m) + ' 就得到 ' + T('Q') + '，所以 ' + T('Q') + ' 在 ' + T('L') + ' 上。'
              : '，外積不是零向量 ⟹ 兩向量不平行，所以 ' + T('Q') + ' 不在 ' + T('L') + ' 上。'),
      '(3) 同一個點配同一個方向，改寫成' + (form === 0 ? '參數式' : '比例式') + '：' + T(other) + '。' + solFin(o)];
  };

  /* §3-3 兩點決定直線 */
  L1_SOL.lineTwoPts = function (p, o) {
    var A = p.A, B = p.B, C = p.C, AB = sub(B, A), d = red(AB), g = gcd3(AB) || 1;
    var AC = sub(C, A), cr = cross(AC, d), on = isZero(cr);
    return ['方向向量取 ' + T(ov('AB') + '=' + vt(B) + '-' + vt(A) + '=' + vt(AB))
        + (g === 1 ? '（三個分量已經沒有公因數）。' : '，約掉公因數 ' + T(String(g)) + ' 得 ' + T(vec('d') + '=' + vt(d)) + '（同一條直線）。'),
      '(1) 以 ' + T('A') + ' 為起點：' + T(paramTex(A, d, 't')) + '。(2) 消去 ' + T('t') + ' 得比例式 ' + T(ratioTex(A, d)) + '。',
      '(3) ' + T(ov('AC') + '=' + vt(AC)) + '，' + T(ov('AC') + '\\times' + vec('d') + '=' + vt(cr))
        + (on ? '，外積是零向量 ⟹ ' + T('C') + ' 在 ' + T('L') + ' 上。' : '，外積不是零向量 ⟹ ' + T('C') + ' 不在 ' + T('L') + ' 上。') + solFin(o)];
  };

  /* §3-4 直線與平面的交點 */
  L1_SOL.linePlaneInt = function (p, o) {
    var n = p.n, d = p.d, P0 = p.P0, dd = p.dd, a = dot(n, dd), b = dot(n, P0), t = (d - b) / a;
    var X = add(P0, sc(t, dd));
    return ['把參數式的三條代入 ' + T('E') + ' 的左式，整理成 ' + T('t') + ' 的一次方程式：' + T(solParT(vec('n') + '\\cdot' + vec('d')) + 't+' + vec('n') + '\\cdot P_0=' + d) + '。',
      '本題 ' + T(vec('n') + '\\cdot' + vec('d') + '=' + subTex(n, dd) + '=' + a) + '、' + T(vec('n') + '\\cdot P_0=' + subTex(n, P0) + '=' + b) + '，所以 ' + T(term(a, 't', true) + term(b, '', false) + '=' + d) + '，' + T('t=' + t) + '。',
      '把 ' + T('t=' + t) + ' 回代參數式：' + T(vt(P0) + term(t, vt(dd), false) + '=' + vt(X)) + '，交點是 ' + T(vt(X)) + '。' + solFin(o)];
  };

  /* §3-5 直線與平面的位置關係 */
  L1_SOL.linePlaneRel = function (p, o) {
    var n = p.n, d = p.d, P0 = p.P0, dd = p.dd, a = dot(n, dd), b = dot(n, P0);
    var s1 = '先算 ' + T(vec('n') + '\\cdot' + vec('d') + '=' + subTex(n, dd) + '=' + a) + '。';
    if (p.mode === 0) {
      var t = (d - b) / a, X = add(P0, sc(t, dd));
      return [s1 + '不是 ' + T('0') + '，所以直線與平面恰好交於一點。',
        '把 ' + T('P=P_0+t' + vec('d')) + ' 代入左式（其中 ' + T(vec('n') + '\\cdot P_0=' + b) + '）：' + T(term(a, 't', true) + term(b, '', false) + '=' + d) + '，解得 ' + T('t=' + t) + '。',
        '回代得交點 ' + T(vt(P0) + term(t, vt(dd), false) + '=' + vt(X)) + '。' + solFin(o)];
    }
    return [s1 + '等於 ' + T('0') + '，表示 ' + T(vec('d')) + ' 與 ' + T(vec('n')) + ' 垂直，直線不是平行於平面就是落在平面上。',
      '再看 ' + T('P_0' + vt(P0)) + ' 在不在 ' + T('E') + ' 上：代入左式得 ' + T(subTex(n, P0) + '=' + b) + '，而 ' + T('E') + ' 的常數項是 ' + T(String(d)) + '。',
      (p.mode === 2 ? '兩者相同 ⟹ ' + T('P_0') + ' 在平面上，整條 ' + T('L') + ' 都落在 ' + T('E') + ' 上（有無限多個交點）。'
                    : '兩者不同 ⟹ ' + T('P_0') + ' 不在平面上，所以 ' + T('L') + ' 與 ' + T('E') + ' 平行、沒有交點。') + solFin(o)];
  };

  /* §3-6 直線與平面的夾角 */
  L1_SOL.linePlaneAngle = function (p, o) {
    var n = p.n, dd = p.dd, dv = dot(n, dd), cr = cross(dd, n);
    return ['線與面的夾角要用正弦（不是餘弦）：' + T('\\sin\\theta=\\dfrac{' + solAbsT(vec('d') + '\\cdot' + vec('n')) + '}{' + solAbsT(vec('d')) + solAbsT(vec('n')) + '}') + '。',
      '(1) 本題 ' + T(vec('d') + '\\cdot' + vec('n') + '=' + subTex(dd, n) + '=' + dv) + '、' + T(solAbsT(vec('d')) + '^2=' + n2(dd)) + '、' + T(solAbsT(vec('n')) + '^2=' + n2(n)) + '，所以 ' + T('\\sin\\theta=\\dfrac{' + solAbsT(String(dv)) + '}{\\sqrt{' + n2(dd) + '}\\sqrt{' + n2(n) + '}}=' + sqrtFracTex(dv * dv, n2(dd) * n2(n))) + '。',
      '(2) 線與面垂直 ⟺ ' + T(vec('d')) + ' 與 ' + T(vec('n')) + ' 平行：' + T(vec('d') + '\\times' + vec('n') + '=' + vt(cr))
        + (isZero(cr) ? '，是零向量 ⟹ 兩者平行，所以 ' + T('L') + ' 與 ' + T('E') + ' 垂直。' : '，不是零向量 ⟹ 兩者不平行，所以 ' + T('L') + ' 與 ' + T('E') + ' 不垂直。') + solFin(o)];
  };

  /* §4-1 點到直線的距離 */
  L1_SOL.ptLineDist = function (p, o) {
    var A = p.A, dd = p.dd, P = p.P, u = sub(P, A), cr = cross(u, dd);
    return ['取直線上的點 ' + T('A' + vt(A)) + '，' + T(ov('AP') + '=' + vt(P) + '-' + vt(A) + '=' + vt(u)) + '。',
      '用外積：' + T(ov('AP') + '\\times' + vec('d') + '=' + vt(cr)) + '，' + T(solAbsT(ov('AP') + '\\times' + vec('d')) + '^2=' + n2(cr)) + '、' + T(solAbsT(vec('d')) + '^2=' + n2(dd)) + '。',
      '距離 ' + T('=\\dfrac{' + solAbsT(ov('AP') + '\\times' + vec('d')) + '}{' + solAbsT(vec('d')) + '}=\\sqrt{\\dfrac{' + n2(cr) + '}{' + n2(dd) + '}}=' + sqrtFracTex(n2(cr), n2(dd))) + '。' + solFin(o)];
  };

  /* §4-2 垂足 */
  L1_SOL.footPerp = function (p, o) {
    var A = p.A, dd = p.dd, P = p.P, u = sub(P, A), num = dot(u, dd), N = n2(dd), k = F(num, N);
    var H = [0, 1, 2].map(function (i) { return Fr.add(F(A[i]), Fr.mul(k, F(dd[i]))); });
    var cr = cross(u, dd);
    return ['令垂足 ' + T('H=A+t' + vec('d')) + '，由 ' + T(ov('PH') + '\\cdot' + vec('d') + '=0') + ' 得 ' + T('t=\\dfrac{' + ov('AP') + '\\cdot' + vec('d') + '}{' + solAbsT(vec('d')) + '^2}') + '。',
      '(1) 本題 ' + T(ov('AP') + '=' + vt(u)) + '，' + T(ov('AP') + '\\cdot' + vec('d') + '=' + subTex(u, dd) + '=' + num) + '、' + T(solAbsT(vec('d')) + '^2=' + N) + '，所以 ' + T('t=' + Fr.tex(k)) + '，' + T('H=A+' + solParT(Fr.tex(k, true)) + vec('d') + '=' + vtF(H)) + '，即 ' + T('H' + vtF(H)) + '。',
      '(2) ' + T('\\overline{PH}') + ' 用外積算比較快：' + T(ov('AP') + '\\times' + vec('d') + '=' + vt(cr)) + '，' + T('\\overline{PH}=\\dfrac{' + solAbsT(ov('AP') + '\\times' + vec('d')) + '}{' + solAbsT(vec('d')) + '}=\\sqrt{\\dfrac{' + n2(cr) + '}{' + N + '}}=' + sqrtFracTex(n2(cr), N)) + '。' + solFin(o)];
  };

  /* §4-3 兩平行線的距離 */
  L1_SOL.parallelLineDist = function (p, o) {
    var A = p.A, dd = p.dd, B = p.B, k = p.k, u = sub(B, A), cr = cross(u, dd), N = n2(dd);
    return ['(1) ' + T('L_2') + ' 的方向向量 ' + T(vt(sc(k, dd)) + '=' + solK(k) + vt(dd)) + ' 與 ' + T('L_1') + ' 的成比例，所以兩直線平行。',
      T(ov('AB') + '=' + vt(B) + '-' + vt(A) + '=' + vt(u)) + '，' + T(ov('AB') + '\\times' + vec('d') + '=' + vt(cr)) + ' 不是零向量 ⟹ ' + T('B') + ' 不在 ' + T('L_1') + ' 上，所以兩線不重合。',
      '(2) 兩平行線的距離就是 ' + T('B') + ' 到 ' + T('L_1') + ' 的距離：' + T('=\\dfrac{' + solAbsT(ov('AB') + '\\times' + vec('d')) + '}{' + solAbsT(vec('d')) + '}=\\sqrt{\\dfrac{' + n2(cr) + '}{' + N + '}}=' + sqrtFracTex(n2(cr), N)) + '。' + solFin(o)];
  };

  /* §4-4 兩直線的位置關係 */
  L1_SOL.twoLinesRel = function (p, o) {
    var P1 = p.P1, d1 = p.d1, P2 = p.P2, d2 = p.d2, w = sub(P2, P1), cr = cross(d1, d2), dt = det3(d1, d2, w), i;
    if (p.mode === 1) {
      var kk = 1;
      for (i = 0; i < 3; i++) if (d1[i] !== 0) { kk = d2[i] / d1[i]; break; }
      var c2 = cross(w, d1);
      return [T(vec('d_1') + '\\times' + vec('d_2') + '=' + vt(cr)) + ' 是零向量，' + T(vec('d_2') + '=' + vt(d2) + '=' + solK(kk) + vt(d1) + '=' + solK(kk) + vec('d_1')) + '，兩方向成比例 ⟹ 兩直線平行或重合。',
        '再看 ' + T(ov('P_1P_2') + '=' + vt(w)) + '：' + T(ov('P_1P_2') + '\\times' + vec('d_1') + '=' + vt(c2)) + ' 不是零向量 ⟹ ' + T('P_2') + ' 不在 ' + T('L_1') + ' 上。',
        '所以 ' + T('L_1') + ' 與 ' + T('L_2') + ' 平行而不重合（沒有交點）。' + solFin(o)];
    }
    var s1 = T(vec('d_1') + '\\times' + vec('d_2') + '=' + vt(cr)) + ' 不是零向量 ⟹ 兩個方向向量不成比例，兩直線不平行。';
    var s2 = '再算三重積 ' + T('\\det' + solParT(vec('d_1') + ',' + vec('d_2') + ',' + ov('P_1P_2')) + '=' + dt) + '（其中 ' + T(ov('P_1P_2') + '=' + vt(w)) + '）';
    if (p.mode === 2) return [s1, s2 + '。', '三重積不是 ' + T('0') + ' ⟹ 兩直線不共平面，所以是歪斜線（沒有交點）。' + solFin(o)];
    var t = dot(cross(w, d2), cr) / n2(cr), X = add(P1, sc(t, d1));
    return [s1, s2 + '，等於 ' + T('0') + ' ⟹ 兩直線共平面，所以相交於一點。',
      '解 ' + T('P_1+t' + vec('d_1') + '=P_2+s' + vec('d_2')) + ' 得 ' + T('t=' + t) + '，交點 ' + T('=' + vt(P1) + term(t, vt(d1), false) + '=' + vt(X)) + '。' + solFin(o)];
  };

  /* §4-5 兩歪斜線的距離 */
  L1_SOL.skewLineDist = function (p, o) {
    var P1 = p.P1, d1 = p.d1, P2 = p.P2, d2 = p.d2, w = sub(P2, P1), cr = cross(d1, d2), dt = det3(d1, d2, w);
    return ['把兩條線夾在兩個平行平面之間，共同的法向量就是 ' + T(vec('d_1') + '\\times' + vec('d_2') + '=' + vt(cr)) + '，' + T(solAbsT(vec('d_1') + '\\times' + vec('d_2')) + '^2=' + n2(cr)) + '。',
      '連接兩線上各一點：' + T(ov('P_1P_2') + '=' + vt(P2) + '-' + vt(P1) + '=' + vt(w)) + '，' + T(ov('P_1P_2') + '\\cdot' + solParT(vec('d_1') + '\\times' + vec('d_2')) + '=' + subTex(w, cr) + '=' + dt) + '。',
      '距離就是這個連接向量在共同法向量上的投影長：' + T('=\\dfrac{' + solAbsT(String(dt)) + '}{\\sqrt{' + n2(cr) + '}}=' + sqrtFracTex(dt * dt, n2(cr))) + '。' + solFin(o)];
  };

  /* §5-1 點對直線的對稱點 */
  L1_SOL.symPtLine = function (p, o) {
    var A = p.A, dd = p.dd, P = p.P, u = sub(P, A), num = dot(u, dd), N = n2(dd), t = num / N;
    var H = add(A, sc(t, dd)), w = sub(P, H), S = sub(sc(2, H), P);
    return ['先求垂足：令 ' + T('H=A+t' + vec('d')) + '，由 ' + T(ov('PH') + '\\cdot' + vec('d') + '=0') + ' 得 ' + T('t=\\dfrac{' + ov('AP') + '\\cdot' + vec('d') + '}{' + solAbsT(vec('d')) + '^2}=\\dfrac{' + num + '}{' + N + '}=' + t) + '（其中 ' + T(ov('AP') + '=' + vt(u)) + '）。',
      '所以 ' + T('H=' + vt(A) + term(t, vt(dd), false) + '=' + vt(H)) + '；' + T('H') + ' 是 ' + T('P') + ' 與 ' + T("P'") + ' 的中點 ⟹ ' + T("P'=2H-P=" + vt(sc(2, H)) + '-' + vt(P) + '=' + vt(S)) + '，即 ' + T("P'" + vt(S)) + '。',
      '距離 ' + T('\\overline{PH}=' + solAbsT(vt(w)) + '=\\sqrt{' + n2(w) + '}' + (sqrtTex(n2(w)) === '\\sqrt{' + n2(w) + '}' ? '' : '=' + sqrtTex(n2(w)))) + '。' + solFin(o)];
  };

  /* §5-2 對坐標平面的鏡面反射 */
  L1_SOL.mirrorReflect = function (p, o) {
    var mi = PLMISS[p.pl], P = p.P, M = p.M, Pp = P.slice();
    Pp[mi] = -Pp[mi];
    var v = sub(M, P), w = v.slice();
    w[mi] = -w[mi];
    var wr = red(w), g = gcd3(w) || 1;
    return ['(1) 以 ' + T(PLANES[p.pl]) + ' 平面為鏡面，對稱時只把 ' + T(AXES[mi]) + ' 坐標變號：' + T("P'" + vt(Pp)) + '。',
      '(2) 入射方向 ' + T(ov('PM') + '=' + vt(M) + '-' + vt(P) + '=' + vt(v)) + '；反射時垂直鏡面的 ' + T(AXES[mi]) + ' 分量變號，得 ' + T(vt(w))
        + (g === 1 ? '（已經是最簡整數）。' : '，約掉公因數 ' + T(String(g)) + ' 得 ' + T(vt(wr)) + '。'),
      '(3) 反射光線通過鏡面上的 ' + T('M' + vt(M)) + '、方向為 ' + T(vt(wr)) + '：' + T(paramTex(M, wr, 's')) + '。' + solFin(o)];
  };

  /* §5-3 長方體的坐標化 */
  L1_SOL.boxCoord = function (p, o) {
    var a = p.a, b = p.b, c = p.c, n = [b * c, a * c, a * b], nr = red(n), g = gcd3(n) || 1, d = a * b * c / g;
    var N = n2(nr), G = [a, b, c], vg = dot(nr, G);
    return ['以 ' + T('A') + ' 為原點建坐標：' + T('A(0,0,0)') + '、' + T('B(' + a + ',0,0)') + '、' + T('D(0,' + b + ',0)') + '、' + T('E(0,0,' + c + ')') + '、' + T('G(' + a + ',' + b + ',' + c + ')') + '。',
      '(1) ' + T(ov('BD') + '=' + vt(sub([0, b, 0], [a, 0, 0]))) + '、' + T(ov('BE') + '=' + vt(sub([0, 0, c], [a, 0, 0]))) + '，法向量取 ' + T(ov('BD') + '\\times' + ov('BE') + '=' + vt(n))
        + (g === 1 ? '' : '，約掉公因數 ' + T(String(g)) + ' 得 ' + T(vt(nr))) + '；代 ' + T('B') + ' 得常數 ' + T(String(d)) + '，所以平面 ' + T('BDE:' + planeTex([nr[0], nr[1], nr[2], d])) + '。',
      '(2) 把 ' + T('A') + ' 代入左式得 ' + T('0') + '，距離 ' + T('=' + solDistT('0-' + d, N) + '=' + sqrtFracTex(d * d, N)) + '。',
      '(3) 把 ' + T('G') + ' 代入左式得 ' + T(subTex(nr, G) + '=' + vg) + '，距離 ' + T('=' + solDistT(vg + '-' + d, N) + '=' + sqrtFracTex((vg - d) * (vg - d), N)) + '。' + solFin(o)];
  };

  var META_L1 = [
      ['planePointNormal', '§1 由點與法向量寫平面'], ['planeThreePts', '§1 三點決定平面'], ['planeIntercepts', '§1 讀係數與坐標軸交點'], ['planeSpecial', '§1 特殊位置的平面'], ['twoPlanesRel', '§1 兩平面的位置關係與夾角'], ['coplanarK', '§1 四點共平面求未知數'],
      ['ptPlaneDist', '§2 點到平面的距離'], ['parallelPlaneDist', '§2 平行平面與兩平面距離'], ['planeProjSym', '§2 投影點與對稱點'], ['planeDistUnknown', '§2 已知距離求未知數'], ['tetraPlaneDist', '§2 三點的平面與體積法'],
      ['lineParamRatio', '§3 參數式與比例式'], ['lineReadBack', '§3 讀回點與方向向量'], ['lineTwoPts', '§3 兩點決定直線'], ['linePlaneInt', '§3 直線與平面的交點'], ['linePlaneRel', '§3 直線與平面的位置關係'], ['linePlaneAngle', '§3 直線與平面的夾角'],
      ['ptLineDist', '§4 點到直線的距離'], ['footPerp', '§4 垂足與最近點'], ['parallelLineDist', '§4 兩平行線的距離'], ['twoLinesRel', '§4 兩直線的位置關係'], ['skewLineDist', '§4 兩歪斜線的距離'],
      ['symPtLine', '§5 點對直線的對稱點'], ['mirrorReflect', '§5 對坐標平面的鏡面反射'], ['boxCoord', '§5 長方體的坐標化']
  ];
  var META_L2 = [
      ['threePlanesRel', '§1 三平面的位置關係'], ['planeThroughInter', '§1 過兩平面交線的平面'],
      ['bisectPlanes', '§2 兩平面的角平分面'], ['chordTwoPlanes', '§2 兩平行平面截出的線段'], ['tetraVolHeight', '§2 四面體的體積與高'], ['maxDistPlaneLine', '§2 過定直線的平面：最大距離'],
      ['planeContainLinePerp', '§3 含直線且垂直已知平面的平面'], ['interLineAxis', '§3 兩平面交線與坐標軸'],
      ['commonPerpSeg', '§4 公垂線段的兩端點'], ['lineBisector', '§4 兩直線的角平分線'], ['boxSkewDist', '§4 長方體中的歪斜線'],
      ['lineProjPlane', '§5 直線在平面上的投影'], ['segProjPlane', '§5 線段的正射影長'], ['rayReflectPlane', '§5 光線的反射'], ['shortestPath', '§5 平面上動點的最短路徑'], ['boxPlaneDist', '§5 長方體中點到截面的距離']
  ];
  /* ══════════════════════════════════════════════════════════
     L3　中上（15 型）：每型對應固定題 L3-1～L3-15 的「類似題」
     答案一律整數／Fraction／根式；p 只放輸入參數與旗標（另附 ans 方便對照），
     驗算器一律從題幹重算。自己新增的工具一律 l3 開頭，避免與產生器撞名。
     ══════════════════════════════════════════════════════════ */
  var L3 = {};
  function l3lcm(a, b) { return Math.abs(a * b) / (gcd(a, b) || 1); }
  function l3mx(v) { return Math.max(Math.abs(v[0]), Math.abs(v[1]), Math.abs(v[2])); }
  /* 三個兩兩垂直、長度相同的整數向量：讓垂足、對稱點、距離全是整數 */
  var L3ORTH = [
    [3, [[1, 2, 2], [2, 1, -2], [2, -2, 1]]],
    [5, [[3, 4, 0], [4, -3, 0], [0, 0, 5]]],
    [7, [[2, 3, 6], [3, -6, 2], [6, 2, -3]]],
    [9, [[1, 4, 8], [8, -4, 1], [4, 7, -4]]],
    [13, [[3, 4, 12], [4, -12, 3], [12, 3, -4]]]
  ];
  function l3orth(r) {
    var e = r.pick(L3ORTH), vs = r.shuffle(e[1]), pm = r.shuffle([0, 1, 2]), s = [r.sign(), r.sign(), r.sign()], out = [], i;
    for (i = 0; i < 3; i++) {
      var v = vs[i], g = r.sign();
      out.push([g * s[0] * v[pm[0]], g * s[1] * v[pm[1]], g * s[2] * v[pm[2]]]);
    }
    return { L: e[0], v: out[0], w: out[1], u: out[2] };
  }
  /* 整數長度的向量（給「最大距離＝兩點距離」「等速運動」用） */
  var L3TRI = [[[1, 2, 2], 3], [[2, 3, 6], 7], [[1, 4, 8], 9], [[4, 4, 7], 9], [[2, 6, 9], 11], [[3, 4, 12], 13], [[2, 10, 11], 15], [[6, 6, 7], 11]];
  function l3tri(r) {
    var e = r.pick(L3TRI), b = r.shuffle(e[0]);
    return { v: [b[0] * r.sign(), b[1] * r.sign(), b[2] * r.sign()], L: e[1] };
  }
  function l3cases(rows) { return '\\begin{cases}' + rows.join('\\\\ ') + '\\end{cases}'; }
  /* [[軸索引, 值], …] → ['y=14','z=10']（依軸的順序排好） */
  function l3fixEq(pairs) {
    var a = pairs.slice().sort(function (x, y) { return x[0] - y[0]; }), out = [], i;
    for (i = 0; i < a.length; i++) out.push(AXES[a[i][0]] + '=' + a[i][1]);
    return out;
  }
  function l3sq(v, p) { return p === 0 ? v + '^2' : '\\left(' + v + (p < 0 ? '+' + (-p) : '-' + p) + '\\right)^2'; }
  function l3lineTex(P, d, form) { return form ? paramTex(P, d) : ratioTex(P, d); }
  function l3coef(k, v) { return (k === 1 ? '' : (k === -1 ? '-' : String(k))) + v; }
  /* 兩個變數的一次式（首項不加正號、係數 0 不出現） */
  function l3two(c1, v1, c2, v2) { var s = term(c1, v1, true); s += term(c2, v2, s === ''); return s === '' ? '0' : s; }
  /* k 倍的寫法：1 倍不寫係數 */
  function l3times(k, s) { return (k === 1 ? '' : (k === -1 ? '-' : String(k))) + s; }
  /* √(n/d) 化簡後根號裡剩下的數（用來擋掉太醜的根式答案） */
  function l3rad(n, d) { var g = gcd(n, d) || 1; return simpSqrt((n / g) * (d / g)).r; }

  /* L3-1　三點各在一條坐標軸上：設 ax+by+cz=d 代三點讀出係數，再套點到平面的距離 */
  var L3AX = [[[2, 3, 6], 7, 6], [[1, 2, 2], 3, 2], [[3, 4, 12], 13, 12], [[1, 4, 8], 9, 8], [[4, 4, 7], 9, 28], [[2, 6, 9], 11, 18], [[6, 6, 7], 11, 42]];
  L3.axisTriDist = function (r) {
    var e = r.pick(L3AX), b = r.shuffle(e[0]), L = e[1];
    var n0 = [b[0] * r.sign(), b[1] * r.sign(), b[2] * r.sign()], m = r.pick([1, 1, 2]);
    var pl = normPlane([n0[0], n0[1], n0[2], m * e[2]]), n = [pl[0], pl[1], pl[2]], d = pl[3];
    var A = [d / n[0], 0, 0], B = [0, d / n[1], 0], C = [0, 0, d / n[2]];
    var P, num, t = 0;
    do { P = rp(r, -6, 6); num = dot(n, P) - d; t++; } while (num === 0 && t < 80);
    if (num === 0) { P = add(P, [1, 0, 0]); num = dot(n, P) - d; }
    var v = r.int(0, 2), dist = F(Math.abs(num), L), dist0 = F(Math.abs(d), L);
    var head = '空間中有 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '、' + T('C' + vt(C));
    var hint = '三點分別落在 ' + T('x') + '、' + T('y') + '、' + T('z') + ' 軸上，不必算外積：設平面為 ' + T('ax+by+cz=d') + '，代三點得 ' + T(l3coef(A[0], 'a') + '=d') + '、' + T(l3coef(B[1], 'b') + '=d') + '、' + T(l3coef(C[2], 'c') + '=d') + '，取 ' + T('d=' + d) + ' 就一次讀出 ' + T('(a,b,c)=' + vt(n)) + '；這個法向量的長度剛好是整數 ' + T('\\sqrt{' + n2(n) + '}=' + L) + '，再套距離公式 ' + T('\\dfrac{\\left|ax_0+by_0+cz_0-d\\right|}{' + L + '}') + '。';
    if (v === 0) {
      return { q: head + ' 與 ' + T('P' + vt(P)) + '。求 ' + T('P') + ' 點到平面 ' + T('ABC') + ' 的距離' + (dist.d === 1 ? '' : '（以最簡分數表示）') + '。',
               a: T(Fr.tex(dist)),
               h: hint + '把 ' + T('P') + ' 代入左式：' + T(subTex(n, P) + '=' + dot(n, P)) + '。',
               p: { A: A, B: B, C: C, P: P, v: v, ans: fr2(dist) } };
    }
    if (v === 1) {
      return { q: head + ' 與 ' + T('P' + vt(P)) + '。(1) 求平面 ' + T('ABC') + ' 的方程式（化為最簡整數係數）。(2) 求 ' + T('P') + ' 到平面 ' + T('ABC') + ' 的距離。',
               a: '(1) ' + T(planeTex(pl)) + '　(2) ' + T(Fr.tex(dist)),
               h: hint + '把 ' + T('P') + ' 代入左式：' + T(subTex(n, P) + '=' + dot(n, P)) + '。',
               p: { A: A, B: B, C: C, P: P, v: v, ans: [pl, fr2(dist)] } };
    }
    return { q: head + '。(1) 求平面 ' + T('ABC') + ' 的方程式（化為最簡整數係數）。(2) 求原點 ' + T('O') + ' 到平面 ' + T('ABC') + ' 的距離。',
             a: '(1) ' + T(planeTex(pl)) + '　(2) ' + T(Fr.tex(dist0)),
             h: hint + '原點代入左式得 ' + T('0') + '，所以距離 ' + T('=\\dfrac{\\left|0-(' + d + ')\\right|}{' + L + '}') + '。',
             p: { A: A, B: B, C: C, v: v, ans: [pl, fr2(dist0)] } };
  };

  /* L3-2　直線與平面沒有交點：n·v=0 且直線上的點不在平面上（兩個條件缺一不可） */
  L3.parallelLineChoice = function (r) {
    var n, P0, dc, d2, d4, tries = 0;
    do {
      n = redPos(rnv(r, -4, 4, 2)); P0 = rp(r, -4, 4);
      dc = red(perpRand(r, n, -2, 2)); d2 = red(perpRand(r, n, -2, 2)); d4 = rnv(r, -4, 4, 2);
      tries++;
    } while ((isZero(dc) || isZero(d2) || parallel(dc, d2) || l3mx(dc) > 9 || l3mx(d2) > 9 || dot(n, d4) === 0 || parallel(d4, n)) && tries < 300);
    var d = dot(n, P0), ax = [], i;
    for (i = 0; i < 3; i++) if (n[i] !== 0) ax.push(i);
    var ei = r.pick(ax), off = [0, 0, 0];
    off[ei] = r.pick([1, -1, 2, -2]);
    var Pc = add(P0, off), P3 = rp(r, -4, 4), P4 = rp(r, -4, 4), aj = r.pick(ax);
    var av = [0, 0, 0]; av[aj] = 1;
    var f1 = r.int(0, 1), f2 = r.int(0, 1), f3 = r.int(0, 1), f4 = r.int(0, 1), v = r.int(0, 2);
    var items = r.shuffle([
      { k: 'par', d: dc, disp: T(l3lineTex(Pc, dc, f1)) },
      { k: 'in', d: d2, disp: T(l3lineTex(P0, d2, f2)) },
      { k: 'perp', d: n, disp: T(l3lineTex(P3, n, f3)) },
      { k: 'cut', d: d4, disp: T(l3lineTex(P4, d4, f4)) },
      { k: 'axis', d: av, disp: T(AXES[aj]) + ' 軸' }
    ]);
    var want = v === 0 ? 'par' : (v === 1 ? 'in' : 'perp'), idx = 0, opts = [], dots = [];
    for (i = 0; i < 5; i++) {
      if (items[i].k === want) idx = i;
      opts.push('(' + (i + 1) + ') ' + items[i].disp);
      dots.push('(' + (i + 1) + ') ' + T(vec('n') + '\\cdot' + vec('v') + '=' + dot(n, items[i].d)));
    }
    var ask = v === 0 ? '與平面 ' + T('E') + ' 平行（即沒有交點）' : (v === 1 ? '完全落在平面 ' + T('E') + ' 上' : '與平面 ' + T('E') + ' 垂直');
    var tail = v === 2 ? '垂直於平面就是方向向量平行法向量，只要找 ' + T(vec('v') + '\\parallel' + vec('n')) + ' 的那一個。'
      : (v === 1 ? '內積為 ' + T('0') + ' 的有兩個，再各代一個點：代進去等於 ' + T(String(d)) + ' 的才是落在 ' + T('E') + ' 上。'
        : '內積不等於 ' + T('0') + ' 的一定相交（直接刪）；等於 ' + T('0') + ' 的再代一個點看在不在 ' + T('E') + ' 上——在的話是落在 ' + T('E') + ' 上，也有交點。');
    return { q: '設空間中平面 ' + T('E') + ' 的方程式為 ' + T(planeTex([n[0], n[1], n[2], d])) + '。若直線 ' + T('L') + ' ' + ask + '，試問 ' + T('L') + ' 的方程式可以是下列哪一個選項？<br>' + opts.join('　'),
             a: '(' + (idx + 1) + ')　' + items[idx].disp,
             h: T(vec('n') + '=' + vt(n)) + '：五個選項的 ' + T(vec('n') + '\\cdot' + vec('v')) + ' 依序為 ' + dots.join('、') + '。' + tail,
             p: { n: n, d: d, v: v, ans: idx + 1 } };
  };

  /* L3-3　直線給成兩個方程式：先化成一個參數的點，再把長度條件寫成參數的方程式 */
  L3.lineTwoEqLen = function (r) {
    var pm = r.shuffle([0, 1, 2]), a, b, h, u0, al, be, co, tries = 0;
    do {
      a = r.int(1, 4); b = r.int(1, 4); h = r.pick([0, 0, 1, -1, 2, -2, 3, -3]); u0 = r.int(1, 4);
      al = r.nz(-3, 3); be = r.nz(-3, 3); co = al * b + be * a; tries++;
    } while ((gcd(a, b) !== 1 || co === 0) && tries < 300);
    var X3 = AXES[pm[2]];
    var K = (a * a + b * b) * u0 * u0 + h * h;
    var Pp = [0, 0, 0], Pm = [0, 0, 0];
    Pp[pm[0]] = b * u0; Pp[pm[1]] = a * u0; Pp[pm[2]] = h;
    Pm[pm[0]] = -b * u0; Pm[pm[1]] = -a * u0; Pm[pm[2]] = h;
    var cL = [0, 0, 0], cP = [0, 0, 0];
    cL[pm[0]] = a; cL[pm[1]] = -b; cP[pm[0]] = al; cP[pm[1]] = be;
    var fL = cL[0] !== 0 ? cL[0] : (cL[1] !== 0 ? cL[1] : cL[2]);
    if (fL < 0) cL = sc(-1, cL);
    var fp = cP[0] !== 0 ? cP[0] : (cP[1] !== 0 ? cP[1] : cP[2]);
    if (fp < 0) cP = sc(-1, cP);
    var tp = dot(cP, Pp), tv = Math.abs(tp);
    var lineEq = lhsTex(cL[0], cL[1], cL[2]) + '=0';
    var lineT = l3cases([lineEq, X3 + '=' + h]);
    var planeT = lhsTex(cP[0], cP[1], cP[2]) + '=t';
    var gen = '(' + [0, 1, 2].map(function (i) {
      return i === pm[0] ? term(b, 'u', true) : (i === pm[1] ? term(a, 'u', true) : String(h));
    }).join(',\\ ') + ')';
    var v = r.int(0, 2);
    var hint = '由 ' + T(X3 + '=' + h) + ' 與 ' + T(lineEq) + ' 可知直線上的點長成 ' + T(gen) + '（只剩一個參數 ' + T('u') + '）；長度條件先用：' + T('\\overline{OP}^2=' + (a * a + b * b) + 'u^2' + term(h * h, '', false) + '=' + K) + ' ⟹ ' + T('u=\\pm' + u0) + '，再把 ' + T('P') + ' 代進 ' + T(planeT) + ' 算 ' + T('t') + '。';
    if (v === 0) {
      return { q: '在坐標空間中，設 ' + T('O') + ' 為原點，且點 ' + T('P') + ' 為直線 ' + T(lineT) + ' 與平面 ' + T(planeT) + ' 的交點。若 ' + T('\\overline{OP}=' + sqrtTex(K)) + '，則 ' + T('t=') + ' ＿＿＿。',
               a: T('t=\\pm' + tv), h: hint, p: { a: a, b: b, h: h, al: al, be: be, ax: pm, K: K, v: v, ans: tv } };
    }
    if (v === 1) {
      return { q: '在坐標空間中，設 ' + T('O') + ' 為原點，且點 ' + T('P') + ' 為直線 ' + T(lineT) + ' 與平面 ' + T(planeT) + ' 的交點（' + T('t') + ' 為實數）。若 ' + T('\\overline{OP}=' + sqrtTex(K)) + '，求 ' + T('P') + ' 所有可能的坐標。',
               a: T(vt(Pp)) + ' 或 ' + T(vt(Pm)), h: hint, p: { a: a, b: b, h: h, al: al, be: be, ax: pm, K: K, v: v, ans: [Pp, Pm] } };
    }
    return { q: '在坐標空間中，設 ' + T('O') + ' 為原點，且點 ' + T('P') + ' 為直線 ' + T(lineT) + ' 與平面 ' + T(planeT) + ' 的交點。若 ' + T('\\overline{OP}=' + sqrtTex(K)) + '，求 ' + T('P') + ' 的坐標與 ' + T('t') + ' 的值。',
             a: T('P' + vt(Pp)) + ' 時 ' + T('t=' + tp) + '；' + T('P' + vt(Pm)) + ' 時 ' + T('t=' + (-tp)),
             h: hint, p: { a: a, b: b, h: h, al: al, be: be, ax: pm, K: K, v: v, ans: [[Pp, tp], [Pm, -tp]] } };
  };

  /* L3-4　平面通過定點、法向量任意：最大距離就是「定點到該點」的長度 */
  L3.maxDistThroughPt = function (r) {
    var e = l3tri(r), w = e.v, L = e.L, B = rp(r, -5, 5), v = r.int(0, 2);
    var A = add(B, w), Aw = w;
    if (v !== 1) { B = [0, 0, 0]; A = w; }
    var nr = redPos(Aw);
    if (v === 1) {
      return { q: '設 ' + T('a,b,c') + ' 為不全為零的實數，平面 ' + T('E') + ' 通過點 ' + T('B' + vt(B)) + '（' + T('E') + ' 的法向量為 ' + T('(a,b,c)') + '）。試求點 ' + T('A' + vt(A)) + ' 到平面 ' + T('E') + ' 的最大距離。',
               a: T(String(L)),
               h: T('B') + ' 在 ' + T('E') + ' 上 ⟹ 垂線段不長於斜線段，' + T('d(A,E)\\le\\overline{AB}=\\sqrt{' + n2(w) + '}=' + L) + '；等號在 ' + T(ov('BA') + '=' + vt(w)) + ' 與 ' + T('E') + ' 垂直（也就是取 ' + T('(a,b,c)=' + vt(nr)) + '）時成立。',
               p: { A: A, B: B, v: v, ans: L } };
    }
    if (v === 0) {
      return { q: '設 ' + T('a,b,c') + ' 為不全為零的實數，試求點 ' + T('A' + vt(A)) + ' 到平面 ' + T('E:ax+by+cz=0') + ' 的最大距離。',
               a: T(String(L)),
               h: T('E') + ' 通過原點 ' + T('O') + '，而 ' + T('O') + ' 在 ' + T('E') + ' 上 ⟹ ' + T('d(A,E)\\le\\overline{OA}=\\sqrt{' + n2(w) + '}=' + L) + '；等號在 ' + T(ov('OA') + '\\perp E') + ' 時成立。用公式看也一樣：' + T('d=\\dfrac{\\left|' + (term(w[0], 'a', true) + term(w[1], 'b', false) + term(w[2], 'c', false)) + '\\right|}{\\sqrt{a^2+b^2+c^2}}') + ' 正是柯西不等式。',
               p: { A: A, v: v, ans: L } };
    }
    return { q: '設 ' + T('a,b,c') + ' 為不全為零的實數，平面 ' + T('E:ax+by+cz=0') + '。(1) 求點 ' + T('A' + vt(A)) + ' 到 ' + T('E') + ' 的最大距離。(2) 求距離最大時 ' + T('E') + ' 的方程式（化為最簡整數係數）。',
             a: '(1) ' + T(String(L)) + '　(2) ' + T(planeTex(planeOf(nr, [0, 0, 0]))),
             h: T('E') + ' 通過原點 ' + T('O') + ' ⟹ ' + T('d(A,E)\\le\\overline{OA}=\\sqrt{' + n2(w) + '}=' + L) + '；等號在 ' + T(ov('OA')) + ' 就是法向量時成立，此時把 ' + T('(a,b,c)=' + vt(nr)) + ' 代回 ' + T('ax+by+cz=0') + '。',
             p: { A: A, v: v, ans: [L, planeOf(nr, [0, 0, 0])] } };
  };

  /* L3-5　兩平行平面：係數先對齊（整條除以倍數），再取常數差除以法向量長度 */
  L3.parPlanesScaled = function (r) {
    var pr, n, L, k, e, f, c1, c2, diff, tries = 0;
    do {
      pr = pyn(r); n = pr.v; L = pr.L;
      k = r.pick([2, 3, 4, 5]); e = r.nz(-9, 9); f = r.nz(-15, 15);
      c1 = F(-e); c2 = F(-f, k); diff = Fr.sub(c1, c2); tries++;
    } while (diff.n === 0 && tries < 200);
    var dist = F(Math.abs(diff.n), diff.d * L), v = r.int(0, 2);
    var mid = Fr.mul(Fr.add(c1, c2), F(1, 2));
    var mp = normPlane([n[0] * mid.d, n[1] * mid.d, n[2] * mid.d, mid.n]);
    var lhs1 = lhsTex(n[0], n[1], n[2]), lhs2 = lhsTex(k * n[0], k * n[1], k * n[2]);
    var p1 = lhs1 + term(e, '', false) + '=0', p2 = lhs2 + term(f, '', false) + '=0';
    var p1b = lhs1 + '=' + (-e), p2b = lhs2 + '=' + (-f);
    var hint = '係數沒對齊就先除：第二式整條除以 ' + T(String(k)) + ' 得 ' + T(lhs1 + '=' + Fr.tex(c2)) + '（分數也沒關係）。兩式寫成 ' + T(lhs1 + '=' + Fr.tex(c1)) + ' 與 ' + T(lhs1 + '=' + Fr.tex(c2)) + '，' + T('\\left|' + vec('n') + '\\right|=\\sqrt{' + n2(n) + '}=' + L) + '，距離 ' + T('=\\dfrac{\\left|' + Fr.tex(c1) + '-\\left(' + Fr.tex(c2) + '\\right)\\right|}{' + L + '}') + '。忘記先除以 ' + T(String(k)) + ' 就會整個算錯。';
    if (v === 0) {
      return { q: '兩平行平面 ' + T(p1) + ' 和 ' + T(p2) + ' 的距離為何？', a: T(Fr.tex(dist)), h: hint,
               p: { n: n, k: k, e: e, f: f, v: v, ans: fr2(dist) } };
    }
    if (v === 1) {
      return { q: '設兩平行平面 ' + T('E_1:' + p1) + '、' + T('E_2:' + p2) + '。(1) 求 ' + T('E_1') + ' 與 ' + T('E_2') + ' 的距離。(2) 求夾在兩者之間且與兩者等距的平面方程式（化為最簡整數係數）。',
               a: '(1) ' + T(Fr.tex(dist)) + '　(2) ' + T(planeTex(mp)),
               h: hint + '(2) 常數項取兩者的平均 ' + T('\\dfrac12\\left(' + Fr.tex(c1) + (c2.n < 0 ? '-' : '+') + Fr.tex(F(Math.abs(c2.n), c2.d)) + '\\right)') + '，再乘掉分母化成整數係數。',
               p: { n: n, k: k, e: e, f: f, v: v, ans: [fr2(dist), mp] } };
    }
    return { q: '兩平行平面 ' + T('E_1:' + p1b) + ' 與 ' + T('E_2:' + p2b) + ' 的距離為何？', a: T(Fr.tex(dist)), h: hint,
             p: { n: n, k: k, e: e, f: f, v: v, ans: fr2(dist) } };
  };

  /* L3-6　兩平面的交線方向＝兩法向量的外積；指定某分量的值就整條乘倍數去湊 */
  L3.interLineDirComp = function (r) {
    var n1, nB, w, tries = 0;
    do { n1 = redPos(rnv(r, -4, 4, 2)); nB = redPos(rnv(r, -4, 4, 2)); w = cross(n1, nB); tries++; }
    while ((isZero(w) || l3mx(red(w)) > 12 || parallel(n1, nB)) && tries < 300);
    var w0 = red(w), d1 = r.int(-8, 8), d2 = r.int(-8, 8), st1 = r.int(0, 1), st2 = r.int(0, 1);
    var nz = [], i;
    for (i = 0; i < 3; i++) if (w0[i] !== 0) nz.push(i);
    var ix = r.pick(nz), lam = r.pick([1, -1, 2, -2, 3, -3]), v = r.int(0, 1);
    var tgt = lam * w0[ix], full = sc(lam, w0), names = ['\\alpha', '\\beta'], cnt = 0, comps = [], got = [];
    for (i = 0; i < 3; i++) {
      if (i === ix) comps.push(String(tgt));
      else { comps.push(names[cnt]); got.push(full[i]); cnt++; }
    }
    var e1 = st1 ? lhsTex(n1[0], n1[1], n1[2]) + term(-d1, '', false) + '=0' : lhsTex(n1[0], n1[1], n1[2]) + '=' + d1;
    var e2 = st2 ? lhsTex(nB[0], nB[1], nB[2]) + term(-d2, '', false) + '=0' : lhsTex(nB[0], nB[1], nB[2]) + '=' + d2;
    var hint = T(vec('v') + '\\parallel' + vec('n_1') + '\\times' + vec('n_2')) + '。' + T(vec('n_1') + '=' + vt(n1)) + '、' + T(vec('n_2') + '=' + vt(nB)) + '，外積 ' + T('=' + vt(w)) + '，約成最簡整數是 ' + T(vt(w0)) + '；';
    if (v === 0) {
      return { q: '平面 ' + T('E_1:' + e1) + ' 與 ' + T('E_2:' + e2) + ' 相交於直線 ' + T('L') + '。若 ' + T(vec('v') + '=(' + comps.join(',') + ')') + ' 為 ' + T('L') + ' 的一個方向向量，則 ' + T('(\\alpha,\\beta)=') + ' ＿＿＿。',
               a: T('(\\alpha,\\beta)=' + '(' + got.join(',') + ')'),
               h: hint + '再整條乘上適當的倍數，使第 ' + (ix + 1) + ' 個分量變成 ' + T(String(tgt)) + '。算完用 ' + T(vec('v') + '\\cdot' + vec('n_1') + '=0') + '、' + T(vec('v') + '\\cdot' + vec('n_2') + '=0') + ' 驗算。',
               p: { n1: n1, d1: d1, nB: nB, d2: d2, ix: ix, tgt: tgt, v: v, ans: got } };
    }
    return { q: '平面 ' + T('E_1:' + e1) + ' 與 ' + T('E_2:' + e2) + ' 相交於直線 ' + T('L') + '。求 ' + T('L') + ' 的一個方向向量（化為最簡整數且第一個非零分量為正）。',
             a: T(vt(redPos(w0))),
             h: hint + '最後把它調成第一個非零分量為正。算完用 ' + T(vec('v') + '\\cdot' + vec('n_1') + '=0') + '、' + T(vec('v') + '\\cdot' + vec('n_2') + '=0') + ' 驗算。',
             p: { n1: n1, d1: d1, nB: nB, d2: d2, v: v, ans: redPos(w0) } };
  };

  /* L3-7　等速直線運動：位移＝（速率×時間）×單位方向向量 */
  L3.uniformMotion = function (r) {
    var e = l3tri(r), dv = e.v, L = e.L, P = rp(r, -6, 6), m = r.pick([1, 2, 3]), tm = r.int(3, 15);
    var v = r.int(0, 2), j = r.int(1, 3), s = m * L, X = add(P, sc(m * tm, dv));
    var Q = add(P, sc(j, dv));
    var unit = '\\left(' + [0, 1, 2].map(function (i) { return Fr.tex(F(dv[i], L), true); }).join(',\\ ') + '\\right)';
    var base = T('\\left|' + vec('v') + '\\right|=\\sqrt{' + n2(dv) + '}=' + L) + ' ⟹ 單位方向 ' + T(unit) + '；';
    if (v === 0) {
      return { q: '質點 ' + T('S') + ' 以 ' + T('P' + vt(P)) + ' 為起點，朝 ' + T(vec('v') + '=' + vt(dv)) + ' 的方向以每分鐘 ' + T(String(s)) + ' 單位的速率等速直線前進，則 ' + T(String(tm)) + ' 分鐘後 ' + T('S') + ' 的坐標為 ＿＿＿。',
               a: T(vt(X)),
               h: base + '走的總長度 ' + T('=' + s + '\\times ' + tm + '=' + s * tm) + '，位移 ' + T('=' + s * tm + '\\cdot' + unit) + '，也就是走了 ' + T(String(m * tm)) + ' 倍的 ' + T(vec('v')) + '，再加上起點。',
               p: { P: P, dv: dv, s: s, tm: tm, v: v, ans: X } };
    }
    if (v === 1) {
      return { q: '質點 ' + T('S') + ' 以 ' + T('P' + vt(P)) + ' 為起點，朝向點 ' + T('Q' + vt(Q)) + ' 的方向以每分鐘 ' + T(String(s)) + ' 單位的速率等速直線前進，則 ' + T(String(tm)) + ' 分鐘後 ' + T('S') + ' 的坐標為 ＿＿＿。',
               a: T(vt(X)),
               h: '方向 ' + T(ov('PQ') + '=' + vt(sc(j, dv)) + '\\parallel' + vt(dv)) + '，' + base + '走的總長度 ' + T('=' + s + '\\times ' + tm + '=' + s * tm) + '，位移 ' + T('=' + s * tm + '\\cdot' + unit + '=' + vt(sc(m * tm, dv))) + '。',
               p: { P: P, Q: Q, s: s, tm: tm, v: v, ans: X } };
    }
    return { q: '質點 ' + T('S') + ' 以 ' + T('P' + vt(P)) + ' 為起點，朝 ' + T(vec('v') + '=' + vt(dv)) + ' 的方向以每分鐘 ' + T(String(s)) + ' 單位的速率等速直線前進。若 ' + T('S') + ' 抵達點 ' + T('R' + vt(X)) + '，求所經過的時間與所走的路徑長度。',
             a: T(String(tm)) + ' 分鐘、長度 ' + T(String(s * tm)),
             h: base + T(ov('PR') + '=' + vt(sc(m * tm, dv)) + '=' + (m * tm) + vt(dv)) + '，長度 ' + T('=' + (m * tm) + '\\times ' + L + '=' + s * tm) + '；再除以速率 ' + T(String(s)) + ' 就是時間。',
             p: { P: P, dv: dv, s: s, R: X, v: v, ans: [tm, s * tm] } };
  };

  /* L3-8　點到直線的距離：|AP×v|÷|v| */
  L3.ptLineDistCross = function (r) {
    var o = l3orth(r), A = rp(r, -5, 5), t0 = r.int(-3, 3), k = r.pick([1, 1, 2]), v = r.int(0, 2);
    var H = add(A, sc(t0, o.v)), P = add(H, sc(k, o.w)), dd = k * o.L;
    var AP = sub(P, A), cr = cross(AP, o.v);
    var base = T('L') + ' 上取一點 ' + T('A' + vt(A)) + '、方向 ' + T(vec('v') + '=' + vt(o.v)) + '（' + T('\\left|' + vec('v') + '\\right|=\\sqrt{' + n2(o.v) + '}=' + o.L) + '），' + T('d=\\dfrac{\\left|' + ov('AP') + '\\times' + vec('v') + '\\right|}{\\left|' + vec('v') + '\\right|}') + '。' + T(ov('AP') + '=' + vt(AP)) + '，' + T(ov('AP') + '\\times' + vec('v') + '=' + vt(cr)) + '，長度 ' + T('=\\sqrt{' + n2(cr) + '}=' + (k * o.L * o.L)) + '。';
    if (v === 0) {
      return { q: '點 ' + T('P' + vt(P)) + ' 到直線 ' + T('L:' + ratioTex(A, o.v)) + ' 的距離為何？', a: T(String(dd)), h: base,
               p: { P: P, A: A, dv: o.v, v: v, ans: dd } };
    }
    if (v === 1) {
      return { q: '設 ' + T('Q') + ' 為直線 ' + T('L:' + paramTex(A, o.v)) + ' 上的動點，' + T('P' + vt(P)) + ' 為定點，求 ' + T('\\overline{PQ}') + ' 的最小值。',
               a: T(String(dd)), h: T('\\overline{PQ}') + ' 的最小值就是 ' + T('P') + ' 到 ' + T('L') + ' 的距離。' + base,
               p: { P: P, A: A, dv: o.v, v: v, ans: dd } };
    }
    return { q: '設點 ' + T('P' + vt(P)) + '、直線 ' + T('L:' + ratioTex(A, o.v)) + '。(1) 求 ' + T('P') + ' 到 ' + T('L') + ' 的距離。(2) 求 ' + T('P') + ' 在 ' + T('L') + ' 上的垂足坐標。',
             a: '(1) ' + T(String(dd)) + '　(2) ' + T(vt(H)),
             h: base + '(2) 垂足 ' + T('H=A+t' + vec('v')) + '，其中 ' + T('t=\\dfrac{' + ov('AP') + '\\cdot' + vec('v') + '}{\\left|' + vec('v') + '\\right|^2}=\\dfrac{' + dot(AP, o.v) + '}{' + n2(o.v) + '}') + '。',
             p: { P: P, A: A, dv: o.v, v: v, ans: [dd, H] } };
  };

  /* L3-9　點在直線上的投影點：t=(AC·v)÷|v|²，再代回 A+tv */
  L3.projOnLine = function (r) {
    var A, B, C, dv, AC, cr, tries = 0;
    do {
      A = rp(r, -5, 5); B = rp(r, -5, 5); C = rp(r, -5, 5);
      dv = sub(B, A); AC = sub(C, A); cr = cross(AC, dv); tries++;
    } while ((isZero(dv) || isZero(cr) || n2(dv) > 70 || l3mx(dv) > 7 || l3rad(n2(cr), n2(dv)) > 600) && tries < 400);
    var dp = dot(AC, dv), NN = n2(dv), t = F(dp, NN), i;
    var H = [];
    for (i = 0; i < 3; i++) H.push(Fr.add(F(A[i]), Fr.mul(t, F(dv[i]))));
    var v = r.int(0, 2);
    var base = T(vec('v') + '=' + ov('AB') + '=' + vt(dv)) + '，' + T('\\left|' + vec('v') + '\\right|^2=' + NN) + '；' + T(ov('AC') + '=' + vt(AC)) + '，' + T(ov('AC') + '\\cdot' + vec('v') + '=' + dp) + ' ⟹ ' + T('t=\\dfrac{' + dp + '}{' + NN + '}' + (Fr.tex(t) === '\\dfrac{' + dp + '}{' + NN + '}' ? '' : '=' + Fr.tex(t))) + '，投影點 ' + T('H=A+t' + vec('v')) + '。驗算：' + T(ov('HC') + '\\cdot' + vec('v') + '=0') + '。';
    if (v === 0) {
      return { q: '空間中三點 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + ' 與 ' + T('C' + vt(C)) + '。設 ' + T('C') + ' 點在直線 ' + T('\\overleftrightarrow{AB}') + ' 上的投影點坐標為 ' + T('(a,b,c)') + '，則 ' + T('(a,b,c)=') + ' ＿＿＿。',
               a: T(vtF(H)), h: base, p: { A: A, B: B, C: C, v: v, ans: H.map(fr2) } };
    }
    if (v === 1) {
      return { q: '空間中三點 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + ' 與 ' + T('C' + vt(C)) + '。(1) 求 ' + T('C') + ' 在直線 ' + T('\\overleftrightarrow{AB}') + ' 上的投影點。(2) 求 ' + T('C') + ' 到直線 ' + T('\\overleftrightarrow{AB}') + ' 的距離。',
               a: '(1) ' + T(vtF(H)) + '　(2) ' + T(sqrtFracTex(n2(cr), NN)),
               h: base + '(2) 距離 ' + T('=\\dfrac{\\left|' + ov('AC') + '\\times' + vec('v') + '\\right|}{\\left|' + vec('v') + '\\right|}=\\dfrac{\\sqrt{' + n2(cr) + '}}{\\sqrt{' + NN + '}}') + '。',
               p: { A: A, B: B, C: C, v: v, ans: [H.map(fr2), [n2(cr), NN]] } };
    }
    return { q: '空間中三點 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + ' 與 ' + T('C' + vt(C)) + '。設 ' + T('C') + ' 在直線 ' + T('\\overleftrightarrow{AB}') + ' 上的投影點為 ' + T('H=A+t' + ov('AB')) + '，求 ' + T('t') + ' 與 ' + T('H') + '。',
             a: T('t=' + Fr.tex(t)) + '、' + T('H=' + vtF(H)), h: base,
             p: { A: A, B: B, C: C, v: v, ans: [fr2(t), H.map(fr2)] } };
  };

  /* L3-10　點對直線的對稱點：先求垂足 H 再用 2H−P；動點到定點的最短距離就是 PH */
  L3.symPtLineMin = function (r) {
    var o = l3orth(r), A0 = rp(r, -6, 6), t0 = r.int(-2, 3), k = r.pick([1, 1, 2]), v = r.int(0, 2);
    var H = add(A0, sc(t0, o.v)), P = add(H, sc(k, o.w)), S = sub(sc(2, H), P), dmin = k * o.L;
    var AP = sub(P, A0), rootT = '\\sqrt{' + l3sq('x', P[0]) + '+' + l3sq('y', P[1]) + '+' + l3sq('z', P[2]) + '}';
    var base = T(vec('v') + '=' + vt(o.v)) + '、' + T('\\left|' + vec('v') + '\\right|^2=' + n2(o.v)) + '、' + T('L') + ' 上一點 ' + T('A_0' + vt(A0)) + '；' + T(ov('A_0P') + '=' + vt(AP)) + '，' + T(ov('A_0P') + '\\cdot' + vec('v') + '=' + dot(AP, o.v)) + ' ⟹ ' + T('t=' + t0) + ' ⟹ 垂足 ' + T('H=' + vt(H)) + '。';
    if (v === 0) {
      return { q: '設直線 ' + T('L:' + ratioTex(A0, o.v)) + '，點 ' + T('P' + vt(P)) + '。<br>(1) 求點 ' + T('P') + ' 對直線 ' + T('L') + ' 的對稱點坐標。<br>(2) 設點 ' + T('A(x,y,z)') + ' 為直線 ' + T('L') + ' 上的動點，求 ' + T(rootT) + ' 的最小值。',
               a: '(1) ' + T(vt(S)) + '　(2) ' + T(String(dmin)),
               h: base + '(1) 對稱點 ' + T('=2H-P') + '。(2) 那一長串根號就是 ' + T('\\overline{PA}') + '，最小值就是 ' + T('\\overline{PH}=\\sqrt{' + n2(sub(P, H)) + '}') + '。',
               p: { A0: A0, dv: o.v, P: P, v: v, ans: [S, dmin] } };
    }
    if (v === 1) {
      return { q: '設直線 ' + T('L:' + ratioTex(A0, o.v)) + '，點 ' + T('P' + vt(P)) + '。求 ' + T('P') + ' 對 ' + T('L') + ' 的對稱點坐標與 ' + T('P') + ' 到 ' + T('L') + ' 的距離。',
               a: T(vt(S)) + '、距離 ' + T(String(dmin)),
               h: base + '對稱點 ' + T('=2H-P') + '；距離 ' + T('=\\overline{PH}=\\sqrt{' + n2(sub(P, H)) + '}') + '。',
               p: { A0: A0, dv: o.v, P: P, v: v, ans: [S, dmin] } };
    }
    return { q: '設直線 ' + T('L:' + paramTex(A0, o.v)) + '，點 ' + T('P' + vt(P)) + '。(1) 求 ' + T('L') + ' 上與 ' + T('P') + ' 最近的點。(2) 求 ' + T('P') + ' 對 ' + T('L') + ' 的對稱點坐標。',
             a: '(1) ' + T(vt(H)) + '　(2) ' + T(vt(S)),
             h: base + '(2) 對稱點 ' + T('=2H-P') + '（' + T('H') + ' 是 ' + T('P') + ' 與對稱點的中點）。',
             p: { A0: A0, dv: o.v, P: P, v: v, ans: [H, S] } };
  };

  /* L3-11　兩直線各自平行一條坐標軸：公垂線方向就是第三個軸，距離直接讀常數差 */
  L3.axisSkewDist = function (r) {
    var ix = r.shuffle([0, 1, 2]), i = ix[0], j = ix[1], kk = ix[2];
    var aj = r.int(-12, 14), ak = r.int(-12, 14), bi = r.int(-12, 14), gap = r.nz(-12, 12);
    var bk = ak + gap, D = Math.abs(gap), v = r.int(0, 2);
    var L1 = l3cases(l3fixEq([[j, aj], [kk, ak]])), L2 = l3cases(l3fixEq([[i, bi], [kk, bk]]));
    var L2m = l3cases(l3fixEq([[i, bi], [kk, 'm']]));
    var Q1 = [0, 0, 0], Q2 = [0, 0, 0];
    Q1[i] = bi; Q1[j] = aj; Q1[kk] = ak;
    Q2[i] = bi; Q2[j] = aj; Q2[kk] = bk;
    var ei = [0, 0, 0], ej = [0, 0, 0], ek = [0, 0, 0];
    ei[i] = 1; ej[j] = 1; ek[kk] = 1;
    var bkT = v === 2 ? 'm' : String(bk);
    var base = T('L_1') + ' 的方向是 ' + T(vt(ei)) + '（平行 ' + T(AXES[i]) + ' 軸，躺在 ' + T(AXES[kk] + '=' + ak) + ' 這個平面上）、' + T('L_2') + ' 的方向是 ' + T(vt(ej)) + '（平行 ' + T(AXES[j]) + ' 軸，躺在 ' + T(AXES[kk] + '=' + bkT) + ' 上）；兩方向的外積 ' + T('=\\pm' + vt(ek)) + ' ⟹ 公垂線就是 ' + T(AXES[kk]) + ' 軸方向。';
    if (v === 0) {
      return { q: '在坐標空間中，兩歪斜線 ' + T('L_1:' + L1) + '、' + T('L_2:' + L2) + ' 的距離為何？',
               a: T(String(D)),
               h: base + '兩條線分別在 ' + T(AXES[kk] + '=' + ak) + ' 與 ' + T(AXES[kk] + '=' + bk) + ' 上 ⟹ 距離 ' + T('=\\left|' + ak + '-(' + bk + ')\\right|') + '。',
               p: { i: i, j: j, k: kk, aj: aj, ak: ak, bi: bi, bk: bk, v: v, ans: D } };
    }
    if (v === 1) {
      return { q: '在坐標空間中，兩歪斜線 ' + T('L_1:' + L1) + '、' + T('L_2:' + L2) + '。(1) 求兩線的距離。(2) 求公垂線段的兩個端點坐標。',
               a: '(1) ' + T(String(D)) + '　(2) ' + T('L_1') + ' 上的 ' + T(vt(Q1)) + ' 與 ' + T('L_2') + ' 上的 ' + T(vt(Q2)),
               h: base + '公垂線段只在 ' + T(AXES[kk]) + ' 這個坐標上有差：' + T('L_1') + ' 上取 ' + T(AXES[i] + '=' + bi) + '、' + T('L_2') + ' 上取 ' + T(AXES[j] + '=' + aj) + '，兩點的另外兩個坐標就一樣了。',
               p: { i: i, j: j, k: kk, aj: aj, ak: ak, bi: bi, bk: bk, v: v, ans: [D, Q1, Q2] } };
    }
    return { q: '在坐標空間中，兩歪斜線 ' + T('L_1:' + L1) + '、' + T('L_2:' + L2m) + ' 的距離為 ' + T(String(D)) + '，求 ' + T('m') + ' 的值。',
             a: T('m=' + bk) + ' 或 ' + T('m=' + (2 * ak - bk)),
             h: base + '距離 ' + T('=\\left|' + ak + '-m\\right|=' + D) + '，去絕對值有兩個解（' + T('m') + ' 在 ' + T(String(ak)) + ' 的兩側各一個）。',
             p: { i: i, j: j, k: kk, aj: aj, ak: ak, bi: bi, D: D, v: v, ans: [bk, 2 * ak - bk] } };
  };

  /* L3-12　2x=3y=6z 這種寫法：令它等於 lcm·k 翻成參數式；兩平行線距離＝點到線的距離 */
  L3.chainLineDist = function (r) {
    var a, b, c, M, raw, dd, Q, cr, tries = 0;
    do {
      a = r.int(1, 6); b = r.int(1, 6); c = r.int(1, 6);
      M = l3lcm(l3lcm(a, b), c); raw = [M / a, M / b, M / c]; dd = red(raw);
      Q = rp(r, -6, 6); cr = cross(Q, dd); tries++;
    } while ((M > 60 || (a === b && b === c) || gcd3([a, b, c]) !== 1 || isZero(cr) || n2(dd) > 120 || l3rad(n2(cr), n2(dd)) > 600) && tries < 400);
    var chain = l3coef(a, 'x') + '=' + l3coef(b, 'y') + '=' + l3coef(c, 'z'), v = r.int(0, 2);
    var par = paramTex([0, 0, 0], raw, 'k');
    var base = '令 ' + T(chain + '=' + M + 'k') + ' ⟹ ' + T(AXES[0] + '=' + term(raw[0], 'k', true)) + '、' + T(AXES[1] + '=' + term(raw[1], 'k', true)) + '、' + T(AXES[2] + '=' + term(raw[2], 'k', true)) + '，可見 ' + T('L_1') + ' 通過原點、方向為 ' + T(vt(raw)) + (l3mx(raw) !== l3mx(dd) ? '（約簡成 ' + T(vt(dd)) + '）' : '') + '。兩平行線的距離就是其中一點到另一條線的距離：' + T(ov('OQ') + '=' + vt(Q)) + '，' + T(ov('OQ') + '\\times' + vec('v') + '=' + vt(cr)) + ' ⟹ ' + T('d=\\dfrac{\\sqrt{' + n2(cr) + '}}{\\sqrt{' + n2(dd) + '}}') + '。';
    var ansT = sqrtFracTex(n2(cr), n2(dd));
    if (v === 0) {
      return { q: '直線 ' + T('L_1:' + chain) + ' 與 ' + T('L_2:' + ratioTex(Q, dd)) + ' 為兩平行線，則 ' + T('L_1') + '、' + T('L_2') + ' 的距離為何？',
               a: T(ansT), h: base, p: { a: a, b: b, c: c, Q: Q, v: v, ans: [n2(cr), n2(dd)] } };
    }
    if (v === 1) {
      return { q: '直線 ' + T('L_1:' + chain) + ' 與 ' + T('L_2:' + paramTex(Q, dd)) + ' 為兩平行線，則 ' + T('L_1') + '、' + T('L_2') + ' 的距離為何？',
               a: T(ansT), h: base, p: { a: a, b: b, c: c, Q: Q, v: v, ans: [n2(cr), n2(dd)] } };
    }
    return { q: '設直線 ' + T('L_1:' + chain) + ' 與點 ' + T('Q' + vt(Q)) + '。(1) 把 ' + T('L_1') + ' 改寫成參數式。(2) 求 ' + T('Q') + ' 到 ' + T('L_1') + ' 的距離。',
             a: '(1) ' + T(par) + '（' + T('k') + ' 為實數）　(2) ' + T(ansT),
             h: base, p: { a: a, b: b, c: c, Q: Q, v: v, ans: [n2(cr), n2(dd)] } };
  };

  /* L3-13　兩條「兩平面交線」型的直線相交求參數：先用不含參數的三式定出交點 */
  L3.twoLineSysK = function (r) {
    var X, n1, nB, n3, n4, w, tries = 0;
    do {
      X = rp(r, -4, 4);
      n1 = redPos(rnv(r, -3, 3, 2)); nB = redPos(rnv(r, -3, 3, 2)); n3 = redPos(rnv(r, -3, 3, 2)); n4 = redPos(rnv(r, -3, 3, 2));
      w = cross(n1, nB); tries++;
    } while ((isZero(w) || isZero(cross(n3, n4)) || dot(w, n3) === 0 || (n1[0] * nB[1] - nB[0] * n1[1]) === 0 || parallel(n1, n3) || parallel(nB, n3)) && tries < 600);
    var d1 = dot(n1, X), d2 = dot(nB, X), d3 = dot(n3, X), kk = dot(n4, X), v = r.int(0, 1);
    var e1 = lhsTex(n1[0], n1[1], n1[2]) + '=' + d1, e2 = lhsTex(nB[0], nB[1], nB[2]) + '=' + d2;
    var e3 = lhsTex(n3[0], n3[1], n3[2]) + '=' + d3, e4 = lhsTex(n4[0], n4[1], n4[2]) + '=k';
    var Lq1 = l3cases([e1, e2]), Lq2 = l3cases([e3, e4]);
    var base = T('L_2') + ' 的兩式中，' + T(e3) + ' 沒有 ' + T('k') + '——交點一定同時在 ' + T('L_1') + ' 與這個平面上，先用這三式把交點定死，' + T('k') + ' 最後代進去就好。把 ' + T('L_1') + ' 化成參數式：令 ' + T('z=u') + '，由 ' + T(e1) + ' 與 ' + T(e2) + ' 消去法解出 ' + T('x') + '、' + T('y') + '（方向向量 ' + T(vec('n_1') + '\\times' + vec('n_2') + '=' + vt(w)) + '），代入 ' + T(e3) + ' 解出 ' + T('u') + '，就得到交點；再算 ' + T(lhsTex(n4[0], n4[1], n4[2])) + ' 即為 ' + T('k') + '。';
    if (v === 0) {
      return { q: '空間中兩直線 ' + T('L_1:' + Lq1) + ' 與 ' + T('L_2:' + Lq2) + ' 相交於一點，則 ' + T('k') + ' 值為何？',
               a: T('k=' + kk), h: base, p: { n1: n1, d1: d1, nB: nB, d2: d2, n3: n3, d3: d3, n4: n4, v: v, ans: kk } };
    }
    return { q: '空間中兩直線 ' + T('L_1:' + Lq1) + ' 與 ' + T('L_2:' + Lq2) + ' 相交於一點 ' + T('S') + '。求 ' + T('S') + ' 的坐標與 ' + T('k') + ' 值。',
             a: T('S' + vt(X)) + '、' + T('k=' + kk), h: base,
             p: { n1: n1, d1: d1, nB: nB, d2: d2, n3: n3, d3: d3, n4: n4, v: v, ans: [X, kk] } };
  };

  /* L3-14　直線與坐標平面的交點：與哪個坐標平面交，就令哪個字母為 0 */
  L3.lineCoordPlaneInt = function (r) {
    var pi = r.int(0, 2), mi = PLMISS[pi], nm = PLANES[pi], X, n1, nB, w, tries = 0;
    do {
      X = rp(r, -5, 5); X[mi] = 0;
      n1 = redPos(rnv(r, -3, 3, 2)); nB = redPos(rnv(r, -3, 3, 2)); w = cross(n1, nB); tries++;
    } while ((isZero(w) || w[mi] === 0 || parallel(n1, nB) || (X[0] === 0 && X[1] === 0 && X[2] === 0)) && tries < 600);
    var d1 = dot(n1, X), d2 = dot(nB, X), v = r.int(0, 2), oi = [], i;
    for (i = 0; i < 3; i++) if (i !== mi) oi.push(i);
    var e1 = lhsTex(n1[0], n1[1], n1[2]) + '=' + d1, e2 = lhsTex(nB[0], nB[1], nB[2]) + '=' + d2;
    var Lq = l3cases([e1, e2]);
    var r1 = l3two(n1[oi[0]], AXES[oi[0]], n1[oi[1]], AXES[oi[1]]) + '=' + d1;
    var r2 = l3two(nB[oi[0]], AXES[oi[0]], nB[oi[1]], AXES[oi[1]]) + '=' + d2;
    var base = T(nm) + ' 平面就是 ' + T(AXES[mi] + '=0') + '。直線本來就是兩個平面的交集，再加上 ' + T(AXES[mi] + '=0') + ' 這一條，三式聯立解一點：把 ' + T(AXES[mi] + '=0') + ' 代進兩式得 ' + T(l3cases([r1, r2])) + '，用消去法解二元一次聯立。算完記得代回原來兩式驗算。';
    if (v === 0) {
      return { q: '直線 ' + T('L:' + Lq) + ' 與 ' + T(nm) + ' 平面的交點坐標為 ＿＿＿。', a: T(vt(X)), h: base,
               p: { n1: n1, d1: d1, nB: nB, d2: d2, pl: nm, v: v, ans: X } };
    }
    if (v === 1) {
      return { q: '直線 ' + T('L:' + Lq) + '。(1) 求 ' + T('L') + ' 與 ' + T(nm) + ' 平面的交點坐標。(2) 求 ' + T('L') + ' 的一個方向向量（化為最簡整數且第一個非零分量為正）。',
               a: '(1) ' + T(vt(X)) + '　(2) ' + T(vt(redPos(w))),
               h: base + '(2) 方向向量取兩法向量的外積 ' + T(vt(n1) + '\\times' + vt(nB) + '=' + vt(w)) + '，再約成最簡整數。',
               p: { n1: n1, d1: d1, nB: nB, d2: d2, pl: nm, v: v, ans: [X, redPos(w)] } };
    }
    return { q: '直線 ' + T('L:' + Lq) + ' 與 ' + T(nm) + ' 平面交於點 ' + T('S') + '。求 ' + T('S') + ' 的坐標與 ' + T('\\overline{OS}') + '（' + T('O') + ' 為原點）。',
             a: T('S' + vt(X)) + '、' + T('\\overline{OS}=' + sqrtTex(n2(X))),
             h: base + '求出 ' + T('S') + ' 後再算 ' + T('\\overline{OS}=\\sqrt{' + n2(X) + '}') + '。',
             p: { n1: n1, d1: d1, nB: nB, d2: d2, pl: nm, v: v, ans: [X, n2(X)] } };
  };

  /* L3-15　兩束光線的交點：平行某坐標軸代表另外兩個坐標固定，交點的兩個坐標先讀出來 */
  L3.rayMeet = function (r) {
    var ai, dv, P, t0, j, tries = 0;
    do {
      ai = r.int(0, 2); dv = rnv(r, -3, 3, 2); P = rp(r, -5, 5);
      t0 = r.int(1, 3); j = r.int(1, 3); tries++;
    } while ((j === t0 || l3mx(dv) > 3) && tries < 300);
    var X = add(P, sc(t0, dv)), Q = add(P, sc(j, dv)), R = X.slice();
    R[ai] = X[ai] + r.nz(-6, 6);
    var v = r.int(0, 2), oi = [], i;
    for (i = 0; i < 3; i++) if (i !== ai) oi.push(i);
    var bi = dv[oi[0]] !== 0 ? oi[0] : oi[1];
    var L2q = l3cases(l3fixEq([[oi[0], X[oi[0]]], [oi[1], X[oi[1]]]]));
    var dirT = j === 1 ? '=' + vt(dv) : '=' + vt(sc(j, dv)) + '\\parallel' + vt(dv);
    var base = '乙的光束平行 ' + T(AXES[ai]) + ' 軸 ⟹ 上頭每一點都是 ' + T(AXES[oi[0]] + '=' + X[oi[0]]) + '、' + T(AXES[oi[1]] + '=' + X[oi[1]]) + '，所以交點的這兩個坐標已經知道了。甲的方向 ' + T(dirT) + ' ⟹ 參數式 ' + T(paramTex(P, dv)) + '；令 ' + T(AXES[bi] + '=' + X[bi]) + ' 解出 ' + T('t') + '，再拿另一個坐標驗算（對不上就代表兩束光歪斜、根本不相交）。';
    if (v === 0) {
      return { q: '甲、乙兩人進行射擊練習。甲從 ' + T(vt(P)) + ' 朝向 ' + T(vt(Q)) + ' 發射一固定雷射光束；乙從點 ' + T(vt(R)) + ' 沿平行於 ' + T(AXES[ai]) + ' 軸的方向發射另一雷射光束。則兩雷射光束的交點為 ' + T('(\\underline{\\quad},\\underline{\\quad},\\underline{\\quad})') + '。',
               a: T(vt(X)), h: base, p: { P: P, Q: Q, R: R, ai: ai, v: v, ans: X } };
    }
    if (v === 1) {
      return { q: '甲、乙兩人進行射擊練習。甲從 ' + T('A' + vt(P)) + ' 朝向 ' + T('B' + vt(Q)) + ' 發射一固定雷射光束；乙從點 ' + T('C' + vt(R)) + ' 沿平行於 ' + T(AXES[ai]) + ' 軸的方向發射另一雷射光束。(1) 求兩雷射光束的交點。(2) 求 ' + T('A') + ' 到該交點的距離。',
               a: '(1) ' + T(vt(X)) + '　(2) ' + T(sqrtTex(t0 * t0 * n2(dv))),
               h: base + '(2) 交點 ' + T('=A+' + l3times(t0, vt(dv))) + '，距離 ' + T('=' + l3times(t0, '\\sqrt{' + n2(dv) + '}')) + '。',
               p: { P: P, Q: Q, R: R, ai: ai, v: v, ans: [X, t0 * t0 * n2(dv)] } };
    }
    return { q: '空間中直線 ' + T('L_1') + ' 通過 ' + T('A' + vt(P)) + '、' + T('B' + vt(Q)) + ' 兩點，直線 ' + T('L_2:' + L2q) + '。求 ' + T('L_1') + ' 與 ' + T('L_2') + ' 的交點坐標。',
             a: T(vt(X)),
             h: T('L_2') + ' 平行 ' + T(AXES[ai]) + ' 軸，上頭每一點都是 ' + T(AXES[oi[0]] + '=' + X[oi[0]]) + '、' + T(AXES[oi[1]] + '=' + X[oi[1]]) + '；' + T('L_1') + ' 的方向 ' + T('=' + ov('AB') + dirT) + ' ⟹ 參數式 ' + T(paramTex(P, dv)) + '，令 ' + T(AXES[bi] + '=' + X[bi]) + ' 解出 ' + T('t') + '，另一個坐標要記得驗算。',
             p: { P: P, Q: Q, ai: ai, fixv: [X[oi[0]], X[oi[1]]], v: v, ans: X } };
  };

  var META_L3 = [
    ['axisTriDist', '三點在坐標軸上求點到平面距離'], ['parallelLineChoice', '直線與平面沒有交點的判別'], ['lineTwoEqLen', '兩方程式的直線＋長度條件'], ['maxDistThroughPt', '過定點的平面：最大距離'], ['parPlanesScaled', '係數要先對齊的兩平行平面距離'],
    ['interLineDirComp', '兩平面交線方向指定分量'], ['uniformMotion', '等速直線運動的位置'], ['ptLineDistCross', '點到直線的距離（外積）'], ['projOnLine', '點在直線上的投影點'], ['symPtLineMin', '點對直線的對稱點與最短距離'],
    ['axisSkewDist', '各自平行坐標軸的兩歪斜線'], ['chainLineDist', 'ax=by=cz 與平行線距離'], ['twoLineSysK', '兩交線型直線相交求參數'], ['lineCoordPlaneInt', '直線與坐標平面的交點'], ['rayMeet', '兩束光線的交點']
  ];
  /* 固定題 L3-n 對應的類似題型 */
  var L3_FIX = { 'L3-1': 'axisTriDist', 'L3-2': 'parallelLineChoice', 'L3-3': 'lineTwoEqLen', 'L3-4': 'maxDistThroughPt', 'L3-5': 'parPlanesScaled', 'L3-6': 'interLineDirComp', 'L3-7': 'uniformMotion', 'L3-8': 'ptLineDistCross', 'L3-9': 'projOnLine', 'L3-10': 'symPtLineMin', 'L3-11': 'axisSkewDist', 'L3-12': 'chainLineDist', 'L3-13': 'twoLineSysK', 'L3-14': 'lineCoordPlaneInt', 'L3-15': 'rayMeet' };

  /* ══════════════════════════════════════════════════════════
     L0　章首先備診斷（5 型）：空間向量的內積與外積（高二下 ch1）、三階行列式與體積（高二下 ch1）、三元一次聯立的消去法（國中／本冊）、平面上點到直線的距離（高一上 ch2）、根式化簡（高一上 ch1）
     ══════════════════════════════════════════════════════════ */
  var L0 = {};
  function l0vt(v) { return '(' + v[0] + ',' + v[1] + ',' + v[2] + ')'; }
  function l0sn(x) { return x < 0 ? '(' + x + ')' : String(x); }   /* 放在乘號後面的數 */
  function l0m(x, y, z, w) { return l0sn(x) + '\\cdot' + l0sn(y) + '-' + l0sn(z) + '\\cdot' + l0sn(w); }   /* xy − zw */
  var L0PY2 = [[3, 4], [4, 3], [5, 12], [12, 5], [8, 15], [15, 8], [7, 24], [1, 2], [2, 3], [1, 1], [3, 1], [1, 3], [2, 1]];
  L0.vec3Ops = function (r) {
    var a, b, v = r.int(0, 1), t = 0;
    do { a = rv(r, -4, 4); b = rv(r, -4, 4); t++; } while ((parallel(a, b) || dot(a, b) === 0) && t < 60);
    var c = cross(a, b), dp = dot(a, b);
    var dotT = [0, 1, 2].map(function (i) { return l0sn(a[i]) + '\\cdot' + l0sn(b[i]); }).join('+');
    if (v === 0) return { q: '已知 ' + T('\\vec a=' + l0vt(a)) + '、' + T('\\vec b=' + l0vt(b)) + '，求 ' + T('\\vec a\\cdot\\vec b') + ' 與 ' + T('\\vec a\\times\\vec b') + '。', a: T('\\vec a\\cdot\\vec b=' + dp) + '、' + T('\\vec a\\times\\vec b=' + l0vt(c)),
      h: '內積是分量相乘再相加：$' + dotT + '=' + dp + '$；外積用「遮一行交叉相乘」：第一個分量 $=' + l0m(a[1], b[2], a[2], b[1]) + '=' + c[0] + '$，其餘輪換。本章的法向量幾乎都是外積算出來的。',
      p: { v: v, a: a, b: b, ans: { dot: dp, cross: c } } };
    var chkT = [0, 1, 2].map(function (i) { return l0sn(c[i]) + '\\cdot' + l0sn(a[i]); }).join('+');
    return { q: '已知 ' + T('\\vec a=' + l0vt(a)) + '、' + T('\\vec b=' + l0vt(b)) + '，求同時垂直於 ' + T('\\vec a') + '、' + T('\\vec b') + ' 的一個向量，並驗證它與 ' + T('\\vec a') + ' 的內積為 ' + T('0') + '。', a: T('\\vec a\\times\\vec b=' + l0vt(c)) + '（或其任意非零倍數），內積 ' + T(String(dot(a, c))),
      h: '同時垂直兩個向量的方向就是外積：$' + l0vt(a) + '\\times' + l0vt(b) + '=' + l0vt(c) + '$；驗證 $' + chkT + '=0$。本章「三點決定平面」的法向量就是這樣來的。',
      p: { v: v, a: a, b: b, ans: { cross: c } } };
  };
  L0.det3Vol = function (r) {
    var a, b, c, D, t = 0, v = r.int(0, 1);
    do { a = rv(r, -3, 3); b = rv(r, -3, 3); c = rv(r, -3, 3); D = det3(a, b, c); t++; } while ((D === 0 || Math.abs(D) > 40) && t < 100);
    var rows = a[0] + '&' + a[1] + '&' + a[2] + '\\\\' + b[0] + '&' + b[1] + '&' + b[2] + '\\\\' + c[0] + '&' + c[1] + '&' + c[2];
    if (v === 0) return { q: '計算三階行列式 ' + T('\\begin{vmatrix}' + rows + '\\end{vmatrix}') + '。', a: T(String(D)),
      h: '沿第一列展開：$' + l0sn(a[0]) + '(' + l0m(b[1], c[2], b[2], c[1]) + ')-' + l0sn(a[1]) + '(' + l0m(b[0], c[2], b[2], c[0]) + ')+' + l0sn(a[2]) + '(' + l0m(b[0], c[1], b[1], c[0]) + ')=' + D + '$。本章判斷兩直線是否共面、四點是否共面，都在算這個。',
      p: { v: v, a: a, b: b, c: c, ans: D } };
    var V6 = Math.abs(D), vol = F(V6, 6);
    return { q: '以 ' + T('\\vec u=' + l0vt(a)) + '、' + T('\\vec v=' + l0vt(b)) + '、' + T('\\vec w=' + l0vt(c)) + ' 為三稜的平行六面體體積為多少？以它們為三稜的四面體體積又是多少？', a: '平行六面體 ' + T(String(V6)) + '、四面體 ' + T(Fr.tex(vol)),
      h: '平行六面體體積 $=|\\det(\\vec u,\\vec v,\\vec w)|=|' + D + '|=' + V6 + '$，四面體是它的 $\\dfrac16$。本章「體積法求點到平面的距離 $h=\\dfrac{3V}{S}$」就從這裡出發。',
      p: { v: v, a: a, b: b, c: c, ans: { box: V6, tetra: fr2(vol) } } };
  };
  L0.linSys3 = function (r) {
    var X = rp(r, -3, 4), rows, t = 0;
    do { rows = [rv(r, -3, 3), rv(r, -3, 3), rv(r, -3, 3)]; t++; } while (det3(rows[0], rows[1], rows[2]) === 0 && t < 100);
    var eqs = rows.map(function (q) { return term(q[0], 'x', true) + term(q[1], 'y', false) + term(q[2], 'z', false) + '=' + dot(q, X); });
    var k = rows[1][0] * rows[0][0] > 0 ? '同號相減、異號相加' : '異號相加、同號相減';
    return { q: '解三元一次聯立方程式 ' + T('\\begin{cases}' + eqs.join('\\\\ ') + '\\end{cases}') + '。', a: T('(x,y,z)=' + l0vt(X)),
      h: '消去法：先用第一式分別與第二、第三式消掉 $x$（$x$ 的係數 $' + rows[0][0] + '$、$' + rows[1][0] + '$、$' + rows[2][0] + '$，乘到相同後' + k + '），剩下 $y,z$ 的二元一次聯立，解完回代。本章「三平面交於一點」「兩平面的交線」就是在解它——消到剩一個未知數就停。',
      p: { rows: rows, ans: X } };
  };
  L0.ptLineDist2D = function (r) {
    var n0 = r.pick(L0PY2), n = [n0[0], n0[1] * r.sign()];
    var L2 = n[0] * n[0] + n[1] * n[1], P = [r.int(-6, 6), r.int(-6, 6)], c = r.int(-9, 9), num = Math.abs(n[0] * P[0] + n[1] * P[1] + c);
    if (num === 0) { c += 1; num = Math.abs(n[0] * P[0] + n[1] * P[1] + c); }
    var line = term(n[0], 'x', true) + term(n[1], 'y', false) + term(c, '', false) + '=0';
    return { q: '平面上，求點 ' + T('P(' + P[0] + ',' + P[1] + ')') + ' 到直線 ' + T('L:' + line) + ' 的距離。', a: T(sqrtFracTex(num * num, L2)),
      h: '公式 $d=\\dfrac{|ax_0+by_0+c|}{\\sqrt{a^2+b^2}}$：分子 $|' + n[0] + '\\cdot' + l0sn(P[0]) + (n[1] < 0 ? '-' : '+') + Math.abs(n[1]) + '\\cdot' + l0sn(P[1]) + term(c, '', false) + '|=' + num + '$，分母 $\\sqrt{' + L2 + '}$，根號要化簡或有理化。本章「點到平面的距離」只是把它多加一個坐標。',
      p: { n: n, c: c, P: P, ans: [num, L2] } };
  };
  L0.sqrtSimp = function (r) {
    var v = r.int(0, 1), k = r.pick([2, 3, 5, 6, 7, 10, 11, 13, 14]), m = r.pick([2, 3, 4, 5, 6]), N = k * m * m;
    if (v === 0) return { q: '化簡 ' + T('\\sqrt{' + N + '}') + '。', a: T(sqrtTex(N)),
      h: '把 $' + N + '$ 拆成「完全平方數 $\\times$ 剩下的」：$' + N + '=' + (m * m) + '\\times' + k + '$，所以 $\\sqrt{' + N + '}=' + m + '\\sqrt{' + k + '}$。本章的距離、外積長度都會冒出這種根號。',
      p: { v: v, N: N, ans: [m, k] } };
    var a = r.int(1, 9), d = r.pick([2, 3, 5, 6, 7]), g = gcd(a, d);
    return { q: '化簡 ' + T('\\dfrac{' + a + '}{\\sqrt{' + d + '}}') + '（分母有理化）。', a: T(sqrtFracTex(a * a, d)),
      h: '分子分母同乘 $\\sqrt{' + d + '}$：$\\dfrac{' + a + '\\sqrt{' + d + '}}{' + d + '}$' + (g > 1 ? '，再約分 $' + g + '$' : '') + '。本章的點到平面距離 $\\dfrac{|\\cdots|}{\\sqrt{a^2+b^2+c^2}}$ 幾乎每題都要做這一步。',
      p: { v: v, a: a, d: d, ans: [a * a, d] } };
  };
  var META_L0 = [['vec3Ops', '空間向量的內積與外積'], ['det3Vol', '三階行列式與體積'], ['linSys3', '三元一次聯立的消去法'], ['ptLineDist2D', '平面上點到直線的距離'], ['sqrtSimp', '根式化簡與有理化']];
  /* 先備題型 → 該去哪裡複習 */
  var PREREQ = {
    vec3Ops: { txt: '空間向量的內積與外積（高二下第一章 空間向量）——法向量、交線方向、三種距離公式全靠它們', link: '../g11b-ch01/practice.html#L1' },
    det3Vol: { txt: '三階行列式與平行六面體體積（高二下第一章）——判共面、體積法求距離都在算它', link: '../g11b-ch01/practice.html#L1' },
    linSys3: { txt: '三元一次聯立的消去法（國中）——三平面的交點、兩平面的交線就是在解它', link: null },
    ptLineDist2D: { txt: '平面上點到直線的距離（高一上第二章 直線與圓）——點到平面的距離公式只是多一個坐標', link: '../g10a-ch02/practice.html#L1' },
    sqrtSimp: { txt: '根式化簡與分母有理化（高一上第一章 數與式）——每一個距離的答案都要化到最簡', link: '../g10a-ch01/practice.html#L1' }
  };
  /* ══════════════════════════════════════════════════════════
     對照題：同一型抽兩題，只差一個關鍵特徵（f 由 p 算出；keep 的欄位要相同）
     ══════════════════════════════════════════════════════════ */
  function sign3(x) { return x > 0 ? 1 : x < 0 ? -1 : 0; }
  var CONTRAST = {
    'L1.planeSpecial': { f: function (p) { return p.pl; }, why: '含某坐標軸的平面：常數項是 $0$、且少掉該軸的變數（含 $z$ 軸 ⟹ $ax+by=0$）；平行某坐標平面的平面只剩「缺席」的那個坐標（平行 $xy$ 平面 ⟹ $z=k$、平行 $yz$ 平面 ⟹ $x=k$）。這兩題只差平行的是哪一個坐標平面——看法向量是哪一個坐標軸的方向。' },
    'L1.twoPlanesRel': { f: function (p) { return p.mode; }, why: '兩平面的關係只看法向量：法向量平行 ⟹ 平面平行（常數項也成比例就重合）；法向量內積 $0$ ⟹ 垂直；其餘相交成一個夾角，$\\cos\\theta=\\dfrac{|\\vec n_1\\cdot\\vec n_2|}{|\\vec n_1||\\vec n_2|}$ 取絕對值只算銳角。' },
    'L1.coplanarK': { f: function (p) { return p.hide; }, why: '四點共平面就是「第四點滿足前三點的平面方程式」：不管未知數藏在哪一個坐標，都是先用三個已知點算出平面，再把第四點代入解一次方程式——藏的坐標不同，只是解的是 $x$、$y$ 或 $z$。' },
    'L1.parallelPlaneDist': { f: function (p) { return p.mode; }, why: '兩平行平面的距離公式 $\\dfrac{|d_1-d_2|}{|\\vec n|}$ 只有在**兩式的左邊完全一樣**時才能用：係數成倍數的要先除成一樣，否則就改用「在其中一個平面上任取一點，算它到另一個平面的距離」。' },
    'L1.planeDistUnknown': { f: function (p) { return p.mode; }, why: '「已知距離求未知數」去絕對值一定得到兩個答案：未知數在常數項時是平面往法向量兩側各平移一次；未知數在點的坐標時是點落在平面兩側各一個位置。' },
    'L1.lineParamRatio': { f: function (p) { return p.mode; }, why: '參數式改比例式是「把 $t$ 解出來讓三個式子相等」：方向向量的分量都不為 $0$ 時三段直接相等；有 $0$ 分量時那一項不能當分母，要單獨寫成「$y=y_0$」——兩個 $0$ 就剩一個分式加兩條常數式。' },
    'L1.lineReadBack': { f: function (p) { return p.form; }, why: '從參數式讀回：起點是常數項、方向是 $t$ 的係數；從比例式讀回：分子的 $x-x_0$ 給起點（$x+2$ 要讀成 $x-(-2)$）、分母給方向，分母寫成負數時方向向量那個分量也是負的。' },
    'L1.linePlaneRel': { f: function (p) { return p.mode; }, why: '先看 $\\vec n\\cdot\\vec d$：不是 $0$ 就一定相交於一點；是 $0$ 再看直線上的一點在不在平面上——在就是「直線在平面上」，不在就是「平行」。兩步缺一不可。' },
    'L1.twoLinesRel': { f: function (p) { return p.mode; }, why: '先看方向向量是否成比例：成比例再看一點在不在另一條上，分「平行／重合」；不成比例則算 $\\det(\\vec d_1,\\vec d_2,\\overrightarrow{P_1P_2})$，為 $0$ 是相交（要解出交點），不為 $0$ 是歪斜。' },
    'L1.mirrorReflect': { f: function (p) { return p.pl; }, why: '對坐標平面反射只改「缺席」的那個坐標的正負：對 $xy$ 平面改 $z$、對 $yz$ 平面改 $x$、對 $zx$ 平面改 $y$；反射光線的方向就是「入射點 → 對稱點」。' },
    'L2.threePlanesRel': { f: function (p) { return p.cse; }, why: '三平面用消去法：三個未知數都解得出來就是交於一點；消到某一式變成 $0=0$ 是少一條有效方程式（交於一直線）；變成 $0=\\text{非零}$ 就沒有共同點——沒有共同點又分「三面兩兩相交成三條平行線（三稜柱型）」與「有兩面平行」，看法向量是否平行來區分。' },
    'L2.interLineAxis': { f: function (p) { return p.ax; }, why: '交線與某坐標軸的關係：先由 $\\vec n_1\\times\\vec n_2$ 得交線方向，再看它與該軸方向 $(1,0,0)$、$(0,1,0)$、$(0,0,1)$ 的關係——平行看是否成比例，相交看交線上的點能否讓另外兩個坐標同時為 $0$；問的是哪一軸，看的分量就不同。' },
    'L2.boxSkewDist': { f: function (p) { return p.s1 + '-' + p.s2; }, why: '長方體裡的歪斜線一律坐標化：同一個長方體，選的兩條稜或對角線不同，方向向量與連接向量就不同，但距離永遠是 $\\dfrac{|\\overrightarrow{P_1P_2}\\cdot(\\vec d_1\\times\\vec d_2)|}{|\\vec d_1\\times\\vec d_2|}$，只是套的數字換了。' },
    'L3.axisTriDist': { f: function (p) { return p.v; }, why: '三點各在一軸上：設 $ax+by+cz=d$ 代三點，三個係數一次到手（每個坐標都只留一項）。之後不管問的是定點、原點還是先寫方程式，距離公式只差分子代誰。' },
    'L3.parallelLineChoice': { f: function (p) { return p.v; }, why: '直線與平面三種關係的判法：$\\vec n\\cdot\\vec d=0$ 且點不在平面上 ⟹ 平行；$\\vec n\\cdot\\vec d=0$ 且點在平面上 ⟹ 落在平面上；$\\vec d\\parallel\\vec n$ ⟹ 垂直。五個選項一律先算 $\\vec n\\cdot\\vec d$，再代點。' },
    'L3.lineTwoEqLen': { f: function (p) { return p.v; }, why: '兩方程式的直線先把點寫成一個參數的形式，長度條件就變成一個二次方程式、恆有正負兩解；問 $t$ 就把兩個點代入平面，問點就直接列出兩個點，問兩者就要一一配對。' },
    'L3.maxDistThroughPt': { f: function (p) { return p.v; }, why: '平面過定點 $B$（或原點）而法向量任意時，$A$ 到平面的距離永遠 $\\le\\overline{AB}$，等號在 $\\vec n\\parallel\\overrightarrow{AB}$ 時；求最大值只要算兩點距離，求「此時的平面」才需要把 $\\overrightarrow{AB}$ 當法向量寫出來。' },
    'L3.parPlanesScaled': { f: function (p) { return p.v; }, why: '兩平行平面的係數若差一個倍數，要先除成完全一樣再用 $\\dfrac{|d_1-d_2|}{|\\vec n|}$；「與兩者等距的平面」就是常數項取兩者的平均（左式對齊之後），寫成最簡整數係數時常數項可能要一起乘。' },
    'L3.interLineDirComp': { f: function (p) { return p.v; }, why: '交線方向永遠是 $\\vec n_1\\times\\vec n_2$：問「最簡方向向量」就約分並把首個非零分量調正；問「指定某分量為 $-3$ 的 $(\\alpha,\\beta)$」就把外積整條乘上同一個倍數。' },
    'L3.uniformMotion': { f: function (p) { return p.v; }, why: '等速運動的位置 $=$ 起點 $+$（速率 $\\times$ 時間）$\\times$ 單位方向向量：方向給向量或給目標點都要先除以長度；反過來給終點求時間，就用位移長度除以速率，並確認位移與方向同向。' },
    'L3.ptLineDistCross': { f: function (p) { return p.v; }, why: '點到直線的距離 $=\\dfrac{|\\overrightarrow{AP}\\times\\vec d|}{|\\vec d|}$，「動點到定點的最小值」問的是同一個數；要垂足時才需要再算 $t=\\dfrac{\\overrightarrow{AP}\\cdot\\vec d}{|\\vec d|^2}$。' },
    'L3.symPtLineMin': { f: function (p) { return p.v; }, why: '對直線的對稱點一定先求垂足 $H$（$t=\\dfrac{\\overrightarrow{A_0P}\\cdot\\vec d}{|\\vec d|^2}$），$P\'=2H-P$；根號式的最小值只是「點到直線的距離」換個寫法，最近點就是 $H$ 本身。' },
    'L3.axisSkewDist': { f: function (p) { return p.v; }, why: '各自平行坐標軸的兩條歪斜線，公垂線就是第三個軸的方向，距離是那個坐標的差；反過來給距離求 $m$ 就是解 $|m-c|=D$，兩解；要公垂線段端點就把另外兩個坐標各取對方的固定值。' },
    'L3.chainLineDist': { f: function (p) { return p.v; }, why: '連等式 $ax=by=cz$ 先令 $=$ 公倍數 $\\times k$ 才讀得出方向向量；之後不管另一條線是比例式、參數式，或改問點到 $L_1$ 的距離，都是同一條 $\\dfrac{|\\overrightarrow{PQ}\\times\\vec d|}{|\\vec d|}$。' },
    'L3.twoLineSysK': { f: function (p) { return p.v; }, why: '含未知數 $k$ 的方程式最後才用：先用不含 $k$ 的三條把交點定死，再把交點代入含 $k$ 的那條；問交點與 $k$ 只是多寫出那個點。' },
    'L3.lineCoordPlaneInt': { f: function (p) { return p.pl; }, why: '直線與 $xy$、$yz$、$zx$ 平面的交點，就是令「缺席」的那個坐標為 $0$：與 $xy$ 平面交 ⟹ $z=0$、與 $yz$ 平面交 ⟹ $x=0$、與 $zx$ 平面交 ⟹ $y=0$，剩下的二元一次聯立直接解。' },
    'L3.rayMeet': { f: function (p) { return p.v; }, why: '平行某坐標軸的直線，另外兩個坐標是固定的：把它們代進另一條直線的參數式解出 $t$，再用第三個坐標驗算才算真的相交；情境題與純幾何題只是包裝不同。' }
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

  return { makeRng: makeRng, L0: L0, L1: L1, L2: L2, L3: L3, L3_FIX: L3_FIX, META: META, PREREQ: PREREQ, CONTRAST: CONTRAST, contrastPair: contrastPair, _util: { gcd: gcd, F: F, Fr: Fr, dot: dot, cross: cross, normPlane: normPlane, planeTex: planeTex } };
}));
