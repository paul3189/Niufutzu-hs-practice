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
             h: '(1) 法向量 ' + T(ov('AB') + '\\times' + ov('AC') + '=' + vt(cr)) + '（化簡為 ' + T(vt(nr)) + '）。(2) 直接用點到平面的距離公式，分子 ' + T('=\\left|' + dv + '\\right|') + '、分母 ' + T('=\\sqrt{' + n2(cr) + '}') + '。(3) ' + T('V=\\dfrac16\\left|' + dv + '\\right|') + '，和 (2) 的 ' + T('\\dfrac{3V}{S}') + ' 是同一件事。',
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
      : '分子裡被減掉的數就是點的坐標：' + T(AXES[hi] + (P0[hi] < 0 ? '+' + (-P0[hi]) : '-' + P0[hi])) + ' 要讀成 ' + T(AXES[hi] + '-(' + P0[hi] + ')') + '，符號要翻過來';
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
      hint = T('\\det\\left(' + vec('n_1') + ',' + vec('n_2') + ',' + vec('n_3') + '\\right)=0') + '，表示 ' + T(vec('n_3')) + ' 落在 ' + T(vec('n_1') + ',' + vec('n_2')) + ' 張出的平面上，第三式不是新的獨立條件。先解 ' + T('E_1,E_2') + ' 得交線（過 ' + T(vt(X)) + '、方向 ' + T(vt(red(dd))) + '），代入 ' + T('E_3') + ' 的左式恆得 ' + T(String(C)) + '，而 ' + T('E_3') + ' 的常數是 ' + T(String(D)) + '，' + (cse === 1 ? '兩者相同，整條交線都在 ' + T('E_3') + ' 上。' : '兩者不同，所以沒有共同點。');
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
             h: '把 ' + T('L') + ' 的參數式代入兩個平面各解一次：' + T(vec('n') + '\\cdot' + vec('d') + '=' + nd) + '、' + T(vec('n') + '\\cdot P_0=' + dot(n, P0)) + '，分別得 ' + T('t=' + (-j)) + ' 與 ' + T('t=' + (m - j)) + '。(3) 兩平行平面的距離 ' + T('=\\dfrac{\\left|' + d1 + '-(' + d2 + ')\\right|}{\\sqrt{' + n2(n) + '}}') + '，注意它一般小於 ' + T('\\overline{AB}') + '。',
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

  /* ══════════════════════════════════════════════════════════
     2026-09-29 擴充（依段考卷出現頻率補題型）：L1 五型、L2 六型
     只新增、不改任何既有產生器（既有題型同種子出同一題，錯題本與檢測紀錄的 t.k#seed 仍有效）。
     ══════════════════════════════════════════════════════════ */
  /* 一次式左邊，其中第 u 個坐標的係數是字母 sym */
  function xpSymLhs(n, u, sym) {
    var s = '';
    for (var i = 0; i < 3; i++) {
      if (i === u) { s += (s === '' ? '' : '+') + sym + AXES[i]; continue; }
      s += term(n[i], AXES[i], s === '');
    }
    return s;
  }
  /* 兩個變數的一次方程式：c1·v1 + c2·v2 = rhs */
  function xpEq2(c1, v1, c2, v2, rhs) { var s = term(c1, v1, true); s += term(c2, v2, s === ''); return (s === '' ? '0' : s) + '=' + rhs; }
  /* 比例式，但某一個分子或分母換成字母：P[j] 換成 ps（ps 為 null 就照常）、d[i] 換成 ds */
  function xpRatioSym(P, d, j, ps, i, ds, i2, ds2) {
    var out = [];
    for (var k = 0; k < 3; k++) {
      var num = AXES[k] + (k === j && ps ? '-' + ps : (P[k] === 0 ? '' : (P[k] < 0 ? '+' + (-P[k]) : '-' + P[k])));
      var den = k === i && ds ? ds : (k === i2 && ds2 ? ds2 : String(d[k]));
      out.push('\\dfrac{' + num + '}{' + den + '}');
    }
    return out.join('=');
  }
  function xpSq(v, p) { return p === 0 ? v + '^2' : '(' + v + (p < 0 ? '+' + (-p) : '-' + p) + ')^2'; }
  function xpAllNz(v) { return v[0] !== 0 && v[1] !== 0 && v[2] !== 0; }

  /* ── §1 過兩點（或一點）且垂直已知平面的平面 ── */
  L1.planeTwoPtsPerp = function (r) {
    var mode = r.int(0, 1), t = 0, nF, nr, pl;
    if (mode === 0) {
      var nE, A, AB;
      do { nE = genN(r).v; A = rp(r, -5, 5); AB = rnv(r, -4, 4, 2); nF = cross(AB, nE); t++; } while (isZero(nF) && t < 200);
      var Bp = add(A, AB), dE = r.int(-9, 9);
      nr = redPos(nF); pl = planeOf(nr, A);
      return { q: '求通過 ' + T('A' + vt(A)) + '、' + T('B' + vt(Bp)) + ' 兩點，且與平面 ' + T('E:' + planeTex([nE[0], nE[1], nE[2], dE])) + ' 垂直的平面 ' + T('F') + ' 的方程式。',
               a: T('F:' + planeTex(pl)),
               h: T('F\\perp E') + ' ⟹ ' + T(vec('n_F') + '\\perp' + vec('n_E') + '=' + vt(nE)) + '；' + T('F') + ' 通過 ' + T('A,B') + ' ⟹ ' + T(vec('n_F') + '\\perp' + ov('AB') + '=' + vt(AB)) + '。取 ' + T(vec('n_F') + '=' + ov('AB') + '\\times' + vec('n_E') + '=' + vt(nF)) + '，再代 ' + T('A') + ' 定常數。',
               p: { mode: 0, A: A, B: Bp, nE: nE, dE: dE } };
    }
    var n1, n2, P;
    do { n1 = genN(r).v; n2 = genN(r).v; nF = cross(n1, n2); t++; } while (isZero(nF) && t < 200);
    P = rp(r, -5, 5);
    var d1 = r.int(-9, 9), d2 = r.int(-9, 9);
    nr = redPos(nF); pl = planeOf(nr, P);
    return { q: '求通過點 ' + T('P' + vt(P)) + '，而且與兩平面 ' + T('E_1:' + planeTex([n1[0], n1[1], n1[2], d1])) + '、' + T('E_2:' + planeTex([n2[0], n2[1], n2[2], d2])) + ' 都垂直的平面 ' + T('F') + ' 的方程式。',
             a: T('F:' + planeTex(pl)),
             h: T('F') + ' 同時垂直 ' + T('E_1') + '、' + T('E_2') + ' ⟹ ' + T(vec('n_F')) + ' 同時垂直 ' + T(vec('n_1') + '=' + vt(n1)) + ' 與 ' + T(vec('n_2') + '=' + vt(n2)) + '，取 ' + T(vec('n_1') + '\\times' + vec('n_2') + '=' + vt(nF)) + '，再代 ' + T('P') + ' 定常數。',
             p: { mode: 1, P: P, n1: n1, n2: n2, d1: d1, d2: d2 } };
  };

  /* ── §1 由兩面角求平面的係數（與兩軸的交點已知、第三個係數未知） ── */
  var XP45 = [[3, 4, 5], [4, 3, 5], [5, 12, 13], [12, 5, 13], [8, 15, 17], [15, 8, 17], [6, 8, 10], [8, 6, 10]];
  L1.planeAngleCoef = function (r) {
    var u = r.int(0, 2), oth = [0, 1, 2].filter(function (i) { return i !== u; }), m, n = [0, 0, 0], deg45 = r() < 0.3, L = 0, e, g0;
    if (deg45) {
      e = r.pick(XP45); m = r.pick(oth); var jj = oth[0] === m ? oth[1] : oth[0];
      n[u] = e[0] * r.sign(); n[jj] = e[1] * r.sign(); n[m] = e[2] * r.sign();
      g0 = gcd3(n); n = [n[0] / g0, n[1] / g0, n[2] / g0];
    } else {
      e = r.pick(PYN); var b = r.shuffle(e[0]); L = e[1];
      n = [b[0] * r.sign(), b[1] * r.sign(), b[2] * r.sign()]; m = r.pick(oth);
    }
    var j = oth[0], k = oth[1], lc = Math.abs(n[j] * n[k]) / gcd(n[j], n[k]), D = lc * r.pick([1, -1, 2, -2]);
    var Pj = [0, 0, 0], Pk = [0, 0, 0]; Pj[j] = D / n[j]; Pk[k] = D / n[k];
    var plName = PLANES[PLMISS.indexOf(m)];
    var nPos = n.slice(), nNeg = n.slice(); nPos[u] = Math.abs(n[u]); nNeg[u] = -Math.abs(n[u]);
    var E1 = normPlane([nPos[0], nPos[1], nPos[2], D]), E2 = normPlane([nNeg[0], nNeg[1], nNeg[2], D]);
    var cosT = deg45 ? '' : Fr.tex(F(Math.abs(n[m]), L));
    var cond = deg45 ? '的兩面角為 ' + T('45^\\circ') : '的兩面角 ' + T('\\theta') + '（取銳角）滿足 ' + T('\\cos\\theta=' + cosT);
    return { q: '平面 ' + T('E') + ' 與 ' + T(AXES[j]) + ' 軸、' + T(AXES[k]) + ' 軸分別交於 ' + T(vt(Pj)) + '、' + T(vt(Pk)) + '，而且 ' + T('E') + ' 與 ' + T(plName) + ' 平面' + cond + '。求 ' + T('E') + ' 的方程式（有兩解）。',
             a: T('E:' + planeTex(E1)) + ' 或 ' + T('E:' + planeTex(E2)),
             h: '把兩個交點代進去，可設 ' + T('E:' + xpSymLhs(n, u, 'k') + '=' + D) + '；' + T(plName) + ' 平面的法向量是 ' + T(vt([m === 0 ? 1 : 0, m === 1 ? 1 : 0, m === 2 ? 1 : 0])) + '，所以 ' + T('\\cos\\theta=\\dfrac{' + Math.abs(n[m]) + '}{\\sqrt{k^2+' + (n[j] * n[j] + n[k] * n[k]) + '}}') + '，解出 ' + T('k') + ' 會有正負兩個值。',
             p: { u: u, m: m, n: n, D: D, deg45: deg45 ? 1 : 0 } };
  };

  /* ── §2 兩點在平面的同側或異側；異側時求交點與分比 ── */
  L1.planeSideRatio = function (r) {
    var n = genN(r).v, P = rp(r, -4, 4), D = dot(n, P), w, t = 0;
    do { w = rnv(r, -3, 3, 2); t++; } while (dot(n, w) === 0 && t < 100);
    if (dot(n, w) === 0) w = n.slice();
    var opp = r() < 0.6, mm, kk;
    do { mm = r.int(1, 4); kk = r.int(1, 4); } while (gcd(mm, kk) !== 1 || (!opp && mm === kk));
    var A = opp ? sub(P, sc(mm, w)) : add(P, sc(mm, w)), Bp = add(P, sc(kk, w));
    var fA = dot(n, A) - D, fB = dot(n, Bp) - D;
    return { q: '設平面 ' + T('E:' + planeTex([n[0], n[1], n[2], D])) + '，點 ' + T('A' + vt(A)) + '、' + T('B' + vt(Bp)) + '。(1) ' + T('A') + '、' + T('B') + ' 在 ' + T('E') + ' 的同側還是異側？(2) 若在異側，求線段 ' + T('\\overline{AB}') + ' 與 ' + T('E') + ' 的交點 ' + T('P') + ' 及 ' + T('\\overline{AP}:\\overline{PB}') + '；若在同側，求 ' + T('A') + '、' + T('B') + ' 到 ' + T('E') + ' 的距離比。',
             a: opp ? '(1) 異側　(2) ' + T('P' + vt(P)) + '，' + T('\\overline{AP}:\\overline{PB}=' + mm + ':' + kk) : '(1) 同側　(2) ' + T('d(A,E):d(B,E)=' + mm + ':' + kk),
             h: '把兩點代入 ' + T(lhsTex(n[0], n[1], n[2]) + '-' + (D < 0 ? '(' + D + ')' : D)) + '：' + T('A') + ' 得 ' + T(String(fA)) + '、' + T('B') + ' 得 ' + T(String(fB)) + '。同號在同側、異號在異側；兩點到 ' + T('E') + ' 的距離比就是這兩個值的絕對值比（分母都是 ' + T('\\left|' + vec('n') + '\\right|') + '）。',
             p: { n: n, D: D, A: A, B: Bp, opp: opp ? 1 : 0 } };
  };

  /* ── §3 兩平面的交線化成參數式 ── */
  L1.interLineParam = function (r) {
    var g = lineTwoPlanes(r), dd = red(g.dd), X = g.X, i = -1, k;
    for (k = 0; k < 3; k++) if (Math.abs(dd[k]) === 1) { i = k; break; }
    if (i >= 0) X = sub(X, sc(X[i] * dd[i], dd)); else { for (k = 0; k < 3; k++) if (dd[k] !== 0) { i = k; break; } }
    var d1 = dot(g.n1, X), d2 = dot(g.n2, X), cr = cross(g.n1, g.n2);
    return { q: '求兩平面 ' + T('E_1:' + planeTex([g.n1[0], g.n1[1], g.n1[2], d1])) + '、' + T('E_2:' + planeTex([g.n2[0], g.n2[1], g.n2[2], d2])) + ' 的交線 ' + T('L') + '：(1) 寫出 ' + T('L') + ' 的一個方向向量。(2) 寫出 ' + T('L') + ' 的參數式。',
             a: '(1) ' + T(vec('d') + '=' + vt(dd)) + '（或其非零倍數）　(2) ' + T('L:' + paramTex(X, dd)) + '（點的取法不唯一）',
             h: '方向取 ' + T(vec('n_1') + '\\times' + vec('n_2') + '=' + vt(g.n1) + '\\times' + vt(g.n2) + '=' + vt(cr)) + '；再找一點：令 ' + T(AXES[i] + '=' + X[i]) + ' 代入兩式解二元一次。',
             p: { n1: g.n1, n2: g.n2, X: X, dd: dd, i: i } };
  };

  /* ── §3 含一直線且過線外一點（或含兩平行線）的平面 ── */
  L1.planeLinePt = function (r) {
    var mode = r.int(0, 1), dd = rnv(r, -4, 4, 2), P0 = rp(r, -5, 5), Q, nv, t = 0, form = r.int(0, 1);
    do { Q = rp(r, -5, 5); nv = cross(dd, sub(Q, P0)); t++; } while (isZero(nv) && t < 100);
    var nr = redPos(nv), pl = planeOf(nr, P0);
    var Ltex = function (P, nm) { return T(nm + ':' + (form ? paramTex(P, dd, nm === 'L_2' ? 's' : 't') : ratioTex(P, dd))); };
    if (mode === 0) {
      return { q: '求包含直線 ' + Ltex(P0, 'L') + '，而且通過點 ' + T('P' + vt(Q)) + ' 的平面 ' + T('E') + ' 的方程式。',
               a: T('E:' + planeTex(pl)),
               h: T('L') + ' 上有點 ' + T('P_0' + vt(P0)) + '、方向 ' + T(vec('d') + '=' + vt(dd)) + '；' + T('E') + ' 的法向量要同時垂直 ' + T(vec('d')) + ' 與 ' + T(ov('P_0P') + '=' + vt(sub(Q, P0))) + '，取兩者的外積 ' + T(vt(nv)) + '。',
               p: { mode: 0, P0: P0, dd: dd, Q: Q, form: form } };
    }
    return { q: '兩直線 ' + Ltex(P0, 'L_1') + '、' + Ltex(Q, 'L_2') + ' 互相平行。求包含 ' + T('L_1') + '、' + T('L_2') + ' 的平面 ' + T('E') + ' 的方程式。',
             a: T('E:' + planeTex(pl)),
             h: '兩平行線方向相同 ' + T(vec('d') + '=' + vt(dd)) + '，只給一個方向；另一個方向取兩線上各一點的連線 ' + T(ov('P_1P_2') + '=' + vt(sub(Q, P0))) + '，法向量是兩者的外積 ' + T(vt(nv)) + '。',
             p: { mode: 1, P0: P0, dd: dd, Q: Q, form: form } };
  };

  /* ── L2 §4 含一直線且平行另一直線的平面，兩歪斜線的距離 ── */
  L2.planeParLine = function (r) {
    var d1, d2, P1, P2, n, t = 0, mode = r.int(0, 1);
    do { d1 = rnv(r, -3, 3, 2); d2 = rnv(r, -3, 3, 2); P1 = rp(r, -4, 4); P2 = rp(r, -4, 4); n = cross(d1, d2); t++; } while ((isZero(n) || dot(n, sub(P2, P1)) === 0) && t < 300);
    var nr = redPos(n), pl = planeOf(nr, P1), num = Math.abs(dot(nr, sub(P2, P1))), dist = sqrtFracTex(num * num, n2(nr));
    if (mode === 0) {
      return { q: '設兩直線 ' + T('L_1:' + ratioTex(P1, d1)) + '、' + T('L_2:' + paramTex(P2, d2, 's')) + '。(1) 求包含 ' + T('L_1') + ' 且與 ' + T('L_2') + ' 平行的平面 ' + T('E') + '。(2) 求 ' + T('L_1') + ' 與 ' + T('L_2') + ' 的距離。',
               a: '(1) ' + T('E:' + planeTex(pl)) + '　(2) ' + T(dist),
               h: T('E') + ' 含 ' + T('L_1') + ' 又平行 ' + T('L_2') + ' ⟹ 法向量同時垂直 ' + T(vec('d_1') + '=' + vt(d1)) + '、' + T(vec('d_2') + '=' + vt(d2)) + '，取 ' + T(vec('d_1') + '\\times' + vec('d_2') + '=' + vt(n)) + '，代 ' + T('L_1') + ' 上的點 ' + T(vt(P1)) + ' 定常數。' + T('L_2') + ' 整條與 ' + T('E') + ' 平行，所以兩線距離＝' + T('L_2') + ' 上的點 ' + T(vt(P2)) + ' 到 ' + T('E') + ' 的距離。',
               p: { mode: 0, P1: P1, d1: d1, P2: P2, d2: d2 } };
    }
    var k1 = r.pick([1, 1, 2, -1]), k2 = r.pick([1, 1, 2, -1]);
    var A = P1, Bq = add(P1, sc(k1, d1)), C = P2, Dq = add(P2, sc(k2, d2));
    return { q: '空間中有 ' + T('A' + vt(A)) + '、' + T('B' + vt(Bq)) + '、' + T('C' + vt(C)) + '、' + T('D' + vt(Dq)) + ' 四點。(1) 求包含直線 ' + T('AB') + ' 且與直線 ' + T('CD') + ' 平行的平面 ' + T('E') + '。(2) 求直線 ' + T('AB') + ' 與直線 ' + T('CD') + ' 的距離。',
             a: '(1) ' + T('E:' + planeTex(pl)) + '　(2) ' + T(dist),
             h: T(ov('AB') + '=' + vt(sc(k1, d1))) + '、' + T(ov('CD') + '=' + vt(sc(k2, d2))) + '；法向量取兩者的外積（化簡為 ' + T(vt(nr)) + '），代 ' + T('A') + ' 定常數。' + T('CD') + ' 與 ' + T('E') + ' 平行，所以兩線距離＝' + T('C') + ' 到 ' + T('E') + ' 的距離。',
             p: { mode: 1, A: A, B: Bq, C: C, D: Dq } };
  };

  /* ── L2 §4 兩直線相交求未知數、交點與含兩線的平面 ── */
  L2.linesCoplanarK = function (r) {
    var d1, d2, cr, X, t = 0, j;
    do { d1 = rnv(r, -3, 3, 2); d2 = dirZeros(r, 3); cr = cross(d1, d2); t++; } while ((isZero(cr) || !xpAllNz(d2)) && t < 300);
    X = rp(r, -4, 4);
    var a = r.nz(-2, 2), b = r.nz(-2, 2), P1 = add(X, sc(a, d1)), P2 = add(X, sc(b, d2));
    var cand = [0, 1, 2].filter(function (i) { return cr[i] !== 0; });
    j = r.pick(cand);
    var form = r.int(0, 1), nr = redPos(cr), pl = planeOf(nr, X);
    var L1t = form ? paramTex(P1, d1) : lineShort(P1, d1, 't');
    return { q: '設兩直線 ' + T('L_1:' + L1t) + '、' + T('L_2:' + xpRatioSym(P2, d2, j, 'k', -1, null)) + '。若 ' + T('L_1') + ' 與 ' + T('L_2') + ' 相交，(1) 求 ' + T('k') + '。(2) 求交點坐標。(3) 求包含 ' + T('L_1') + '、' + T('L_2') + ' 的平面方程式。',
             a: '(1) ' + T('k=' + P2[j]) + '　(2) ' + T(vt(X)) + '　(3) ' + T('E:' + planeTex(pl)),
             h: '兩直線方向 ' + T(vt(d1)) + '、' + T(vt(d2)) + ' 不平行，相交 ⟺ 共平面 ⟺ ' + T('\\left(' + vec('d_1') + '\\times' + vec('d_2') + '\\right)\\cdot' + ov('P_1P_2') + '=0') + '，其中 ' + T(vec('d_1') + '\\times' + vec('d_2') + '=' + vt(cr)) + '，' + T('P_2') + ' 的 ' + T(AXES[j]) + ' 坐標是 ' + T('k') + '，得到 ' + T('k') + ' 的一次方程式。含兩線的平面，法向量就用這個外積。',
             p: { P1: P1, d1: d1, P2: P2, d2: d2, j: j, form: form } };
  };

  /* ── L2 §1 空間中直線與平面的敘述判斷（多選） ── */
  var XPFACT = [
    ['垂直於同一個平面的兩相異直線互相平行。', 1, '兩條線的方向都平行於那個平面的法向量，所以互相平行'],
    ['垂直於同一條直線的兩相異平面互相平行。', 1, '兩個平面的法向量都平行於那條直線的方向，所以兩平面平行'],
    ['與同一個平面平行的兩相異平面互相平行。', 1, '三個平面的法向量都平行'],
    ['兩平行線中的一條垂直於平面 $E$，另一條也垂直於 $E$。', 1, '兩條線方向相同，都平行於 $E$ 的法向量'],
    ['過平面外一點，恰有一條直線與該平面垂直。', 1, '方向只能是法向量，過定點的直線就唯一'],
    ['過直線外一點，恰有一個平面與該直線垂直。', 1, '法向量只能是直線的方向，過定點的平面就唯一'],
    ['過平面外一點，恰有一個平面與該平面平行。', 1, '法向量相同、又過定點，所以唯一'],
    ['兩相交平面的交線，與兩個平面的法向量都垂直。', 1, '交線在兩個平面上，所以與兩個法向量都垂直，方向可取 $\\vec n_1\\times\\vec n_2$'],
    ['兩歪斜線恰有一條公垂線（與兩線都垂直且都相交的直線）。', 1, '公垂線方向只能是 $\\vec d_1\\times\\vec d_2$，兩個垂足由兩條垂直條件唯一決定'],
    ['若直線 $L$ 與平面 $E$ 上兩條相交直線都垂直，則 $L$ 垂直於 $E$。', 1, '兩條相交直線的方向張出整個 $E$，$L$ 的方向與它們都垂直，就平行於 $E$ 的法向量'],
    ['不共線的相異三點恰決定一個平面。', 1, '兩個邊向量不平行，外積不為零向量，法向量就定了'],
    ['若直線 $L$ 與兩個相交平面都平行（$L$ 不在兩平面上），則 $L$ 與這兩個平面的交線平行。', 1, '$L$ 的方向與兩個法向量都垂直，所以平行於 $\\vec n_1\\times\\vec n_2$，也就是交線的方向'],
    ['相異三點恰決定一個平面。', 0, '三點共線時，含這三點的平面有無限多個'],
    ['垂直於同一條直線的兩相異直線互相平行。', 0, '例如 $x$ 軸與 $y$ 軸都垂直於 $z$ 軸，但兩者相交'],
    ['與同一個平面平行的兩相異直線互相平行。', 0, '例如 $x$ 軸與 $y$ 軸都與平面 $z=1$ 平行，但兩者相交'],
    ['垂直於同一個平面的兩相異平面互相平行。', 0, '例如 $yz$ 平面與 $zx$ 平面都垂直於 $xy$ 平面，但兩者相交於 $z$ 軸'],
    ['沒有交點的兩相異直線一定互相平行。', 0, '也可能是歪斜線，例如 $x$ 軸與過 $(0,0,1)$ 平行 $y$ 軸的直線'],
    ['兩直線的方向向量不平行，則兩直線必相交。', 0, '方向不平行也可能歪斜，要再看 $\\det(\\vec d_1,\\vec d_2,\\overrightarrow{P_1P_2})$ 是否為 $0$'],
    ['過直線外一點，恰有一條直線與該直線垂直。', 0, '過該點且與直線垂直的直線有無限多條（都在過該點、以直線方向為法向量的平面上）；與它垂直且相交的才只有一條'],
    ['過平面外一點，恰有一條直線與該平面平行。', 0, '過該點且與平面平行的直線有無限多條（都在過該點的平行平面上）'],
    ['若直線 $L$ 與平面 $E$ 上的一條直線垂直，則 $L$ 垂直於 $E$。', 0, '只垂直一條不夠，例如 $x$ 軸垂直於 $xy$ 平面上的 $y$ 軸，但 $x$ 軸落在 $xy$ 平面上'],
    ['若平面 $E_1\\perp E_2$、$E_2\\perp E_3$，則 $E_1$ 與 $E_3$ 平行。', 0, '例如 $E_1$ 取 $yz$ 平面、$E_2$ 取 $xy$ 平面、$E_3$ 取 $zx$ 平面，$E_1$ 與 $E_3$ 相交'],
    ['與同一條直線平行的兩相異平面互相平行。', 0, '例如平面 $x=1$ 與平面 $y=1$ 都與 $z$ 軸平行，但兩者相交'],
    ['過直線外一點，恰有一個平面與該直線平行。', 0, '過該點且與直線平行的平面有無限多個（繞著過該點、平行該直線的那條線轉）'],
    ['若直線 $L$ 與平面 $E$ 沒有交點，則 $L$ 與 $E$ 上的每一條直線都平行。', 0, '$L$ 與 $E$ 上的直線也可能歪斜'],
    ['兩相異直線都與第三條直線歪斜，則這兩條直線互相歪斜。', 0, '例如 $x$ 軸與 $y$ 軸都與過 $(0,0,1)$、方向 $(1,1,0)$ 的直線歪斜，但 $x$ 軸與 $y$ 軸相交']
  ];
  L2.spaceFacts = function (r) {
    var idx, nt, t = 0;
    do { idx = r.shuffle(XPFACT.map(function (x, i) { return i; })).slice(0, 5); nt = idx.filter(function (i) { return XPFACT[i][1]; }).length; t++; } while ((nt === 0 || nt === 5) && t < 50);
    var q = '下列有關空間中直線與平面的敘述，哪些正確？', ans = '', wrong = [];
    idx.forEach(function (i, k) { q += '<br>(' + (k + 1) + ') ' + XPFACT[i][0]; if (XPFACT[i][1]) ans += '(' + (k + 1) + ')'; else wrong.push('(' + (k + 1) + ') ' + XPFACT[i][2]); });
    return { q: q, a: ans,
             h: '每一項都想成「方向向量、法向量」的關係，錯的找一個坐標軸、坐標平面當反例。本題錯的有：' + wrong.join('；') + '。',
             p: { idx: idx } };
  };

  /* ── L2 §3 直線在平面上、與平面平行或垂直：求直線方程式裡的未知數 ── */
  L2.linePlaneParam = function (r) {
    var mode = r.int(0, 2), t = 0, d, n, P0 = rp(r, -5, 5), i, j, pl, q, a, h, p;
    if (mode < 2) {
      do { d = dirZeros(r, 3); n = redPos(perpRand(r, d, -2, 2)); t++; } while ((!xpAllNz(d) || nzc(n) < 2) && t < 200);
      var ci = [0, 1, 2].filter(function (x) { return n[x] !== 0; });
      i = r.pick(ci); j = r.pick(ci);
      pl = [n[0], n[1], n[2], dot(n, P0)];
      var Lt = xpRatioSym(P0, d, j, 'b', i, 'a');
      var sumK = 0; for (var k = 0; k < 3; k++) if (k !== i) sumK += n[k] * d[k];
      if (mode === 0) {
        q = '直線 ' + T('L:' + Lt) + ' 落在平面 ' + T('E:' + planeTex(pl)) + ' 上，求 ' + T('a') + '、' + T('b') + '。';
        a = T('a=' + d[i]) + '，' + T('b=' + P0[j]);
        h = T('L') + ' 在 ' + T('E') + ' 上要兩個條件：方向 ' + T('\\perp') + ' 法向量 ' + T(vt(n)) + '（內積為 ' + T('0') + '，得 ' + T(term(n[i], 'a', true) + (sumK === 0 ? '' : (sumK > 0 ? '+' : '') + sumK) + '=0') + '），而且 ' + T('L') + ' 上的點 ' + T('P_0') + '（' + T(AXES[j]) + ' 坐標是 ' + T('b') + '）也在 ' + T('E') + ' 上。';
      } else {
        q = '直線 ' + T('L:' + Lt) + ' 與平面 ' + T('E:' + planeTex(pl)) + ' 平行（' + T('L') + ' 不在 ' + T('E') + ' 上）。求 ' + T('a') + '，並說明 ' + T('b') + ' 不可以是多少。';
        a = T('a=' + d[i]) + '，' + T('b\\ne ' + P0[j]);
        h = '平行只要方向 ' + T('\\perp') + ' 法向量 ' + T(vt(n)) + '：' + T(term(n[i], 'a', true) + (sumK === 0 ? '' : (sumK > 0 ? '+' : '') + sumK) + '=0') + '。再來 ' + T('L') + ' 上的點 ' + T('P_0') + ' 不能在 ' + T('E') + ' 上，否則整條線落在平面上；把 ' + T('P_0') + ' 代入 ' + T('E') + ' 解出會讓它落在平面上的 ' + T('b') + '，那就是不行的值。';
      }
      p = { mode: mode, P0: P0, d: d, n: n, i: i, j: j };
    } else {
      do { n = genN(r).v; t++; } while (!xpAllNz(n) && t < 100);
      if (!xpAllNz(n)) n = [1, 2, 2];
      var kk = r.pick([1, -1, 2, -2]); d = sc(kk, n);
      var ord = r.shuffle([0, 1, 2]); i = Math.min(ord[0], ord[1]); j = Math.max(ord[0], ord[1]);
      var c3 = ord[2], dE = r.int(-9, 9);
      pl = [n[0], n[1], n[2], dE];
      q = '直線 ' + T('L:' + xpRatioSym(P0, d, -1, null, i, 'a', j, 'b')) + ' 與平面 ' + T('E:' + planeTex(pl)) + ' 垂直，求 ' + T('a') + '、' + T('b') + '。';
      a = T('a=' + d[i]) + '，' + T('b=' + d[j]);
      h = T('L\\perp E') + ' ⟹ 方向向量與法向量 ' + T(vt(n)) + ' 平行：' + T('(' + [0, 1, 2].map(function (x) { return x === i ? 'a' : x === j ? 'b' : String(d[x]); }).join(',') + ')') + ' 是 ' + T(vt(n)) + ' 的倍數，由已知的 ' + T(AXES[c3]) + ' 分量 ' + T(String(d[c3])) + ' 定出倍數是 ' + T(String(kk)) + '。';
      p = { mode: 2, P0: P0, d: d, n: n, i: i, j: j };
    }
    return { q: q, a: a, h: h, p: p };
  };

  /* ── L2 §2 平面上的點：距離平方和最小（點到平面的距離、投影點） ── */
  L2.planeMinDist = function (r) {
    var mode = r.int(0, 2), n = genN(r).v, A = mode === 0 ? [0, 0, 0] : rp(r, -5, 5), N = n2(n), D, tt;
    if (r() < 0.5) { var ti = r.pick([1, -1, 2, -2]); D = dot(n, A) + ti * N; }
    else { do { D = dot(n, A) + r.nz(-12, 12); } while (D === dot(n, A)); }
    tt = F(D - dot(n, A), N);
    var H = [0, 1, 2].map(function (k) { return Fr.add(F(A[k]), Fr.mul(tt, F(n[k]))); });
    var num = Math.abs(D - dot(n, A));
    var expr = xpSq('x', A[0]) + '+' + xpSq('y', A[1]) + '+' + xpSq('z', A[2]);
    var obj = mode === 2 ? '\\sqrt{' + expr + '}' : expr;
    var minT = mode === 2 ? sqrtFracTex(num * num, N) : Fr.tex(F(num * num, N));
    return { q: '實數 ' + T('x,y,z') + ' 滿足 ' + T(planeTex([n[0], n[1], n[2], D])) + '。求 ' + T(obj) + ' 的最小值，以及此時的 ' + T('(x,y,z)') + '。',
             a: '最小值 ' + T(minT) + '，此時 ' + T('(x,y,z)=' + vtF(H)),
             h: T(mode === 2 ? obj : '\\sqrt{' + expr + '}') + ' 是點 ' + T('(x,y,z)') + ' 到 ' + T(vt(A)) + ' 的距離，而 ' + T('(x,y,z)') + ' 在平面上，所以最小值就是 ' + T(vt(A)) + ' 到平面的距離' + (mode === 2 ? '' : '的平方') + '（距離 ' + T('=\\dfrac{' + num + '}{\\sqrt{' + N + '}}') + '）；取到最小的點是投影點，令 ' + T(vt(A) + '+t' + vt(n)) + ' 代入平面解 ' + T('t') + '。',
             p: { mode: mode, n: n, D: D, A: A } };
  };

  /* ── L2 §5 正四角錐坐標化：側面方程式、兩面角 ── */
  L2.pyramidCoord = function (r) {
    var a = r.int(1, 4), h = r.int(1, 6), f = r.int(0, 3);
    var V = [0, 0, h], P = { A: [a, a, 0], B: [-a, a, 0], C: [-a, -a, 0], D: [a, -a, 0] }, nm = ['A', 'B', 'C', 'D'];
    var f1 = 'V' + nm[f] + nm[(f + 1) % 4], f2 = 'V' + nm[(f + 1) % 4] + nm[(f + 2) % 4];
    var P1 = P[nm[f]], P2 = P[nm[(f + 1) % 4]], nv = cross(sub(P2, P1), sub(V, P1)), pl = planeOf(redPos(nv), V);
    var Q3 = P[nm[(f + 2) % 4]], nv2 = cross(sub(Q3, P2), sub(V, P2));
    var S = a * a + h * h;
    return { q: '正四角錐 ' + T('V\\text{-}ABCD') + ' 的底面 ' + T('ABCD') + ' 是邊長 ' + T(String(2 * a)) + ' 的正方形、高為 ' + T(String(h)) + '。以底面中心為原點建立坐標：' + T('A' + vt(P.A)) + '、' + T('B' + vt(P.B)) + '、' + T('C' + vt(P.C)) + '、' + T('D' + vt(P.D)) + '、' + T('V' + vt(V)) + '。(1) 求平面 ' + T(f1) + ' 的方程式。(2) 求側面 ' + T(f1) + ' 與底面 ' + T('ABCD') + ' 所成兩面角 ' + T('\\alpha') + ' 的 ' + T('\\cos\\alpha') + '。(3) 求平面 ' + T(f1) + ' 與平面 ' + T(f2) + ' 夾角 ' + T('\\beta') + '（取銳角）的 ' + T('\\cos\\beta') + '。',
             a: '(1) ' + T(planeTex(pl)) + '　(2) ' + T(sqrtFracTex(a * a, S)) + '　(3) ' + T(Fr.tex(F(a * a, S))),
             h: T(f1) + ' 的法向量取 ' + T(ov(nm[f] + nm[(f + 1) % 4]) + '\\times' + ov(nm[f] + 'V') + '=' + vt(nv)) + '（約簡為 ' + T(vt(redPos(nv))) + '），底面的法向量是 ' + T('(0,0,1)') + '；' + T(f2) + ' 的法向量同理約簡為 ' + T(vt(redPos(nv2))) + '。兩面角的餘弦都用 ' + T('\\dfrac{\\left|' + vec('n_1') + '\\cdot' + vec('n_2') + '\\right|}{\\left|' + vec('n_1') + '\\right|\\left|' + vec('n_2') + '\\right|}') + '。',
             p: { a: a, h: h, f: f } };
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
      '(3) 四面體體積 ' + T('V=\\dfrac16' + solAbsT(String(dv)) + '=' + Fr.tex(V)) + '，和 (2) 用的是同一個三重積。' + solFin(o)];
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

  /* ── 2026-09-29 擴充：新 L1 五型的第一層提示與解題步驟 ── */
  L1_H1.planeTwoPtsPerp = '這是「過兩點（或一點）且垂直已知平面」：所求平面的法向量要同時垂直兩個已知的向量，取它們的外積，再代點定常數。';
  L1_H1.planeAngleCoef = '這是「由兩面角求平面的係數」：先用與坐標軸的交點把平面設成只剩一個未知係數，再用兩個法向量的夾角餘弦列方程式。';
  L1_H1.planeSideRatio = '這是「兩點在平面的同側或異側」：把兩點代入「左式減常數」，同號在同側、異號在異側；兩個值的絕對值比就是到平面的距離比。';
  L1_H1.interLineParam = '這是「兩平面的交線化成參數式」：方向取兩個法向量的外積，再令其中一個坐標為定值，解二元一次找出交線上的一點。';
  L1_H1.planeLinePt = '這是「含一直線且過一點（或含兩平行線）的平面」：直線給一個方向，再用兩點連線給第二個方向，法向量取兩者的外積。';

  function xpNf(nv, nr) { return (nv[0] === nr[0] && nv[1] === nr[1] && nv[2] === nr[2]) ? '' : '，化成最簡整數、首項為正得 ' + T(vt(nr)); }

  L1_SOL.planeTwoPtsPerp = function (p, o) {
    if (p.mode === 0) {
      var AB = sub(p.B, p.A), nF = cross(AB, p.nE), nr = redPos(nF), pl = planeOf(nr, p.A);
      return [T('F\\perp E') + ' ⟹ ' + T(vec('n_F') + '\\perp' + vec('n_E') + '=' + vt(p.nE)) + '；' + T('F') + ' 通過 ' + T('A,B') + ' ⟹ ' + T(vec('n_F') + '\\perp' + ov('AB') + '=' + vt(AB)) + '。',
        '法向量取 ' + T(ov('AB') + '\\times' + vec('n_E') + '=' + vt(nF)) + xpNf(nF, nr) + '。',
        '代入 ' + T('A' + vt(p.A)) + ' 定常數：' + T(subTex(nr, p.A) + '=' + pl[3]) + '，所以 ' + T('F:' + planeTex(pl)) + '。' + solFin(o)];
    }
    var nF2 = cross(p.n1, p.n2), nr2 = redPos(nF2), pl2 = planeOf(nr2, p.P);
    return [T('F') + ' 同時垂直 ' + T('E_1') + '、' + T('E_2') + ' ⟹ ' + T(vec('n_F')) + ' 同時垂直 ' + T(vec('n_1') + '=' + vt(p.n1)) + '、' + T(vec('n_2') + '=' + vt(p.n2)) + '。',
      '法向量取 ' + T(vec('n_1') + '\\times' + vec('n_2') + '=' + vt(nF2)) + xpNf(nF2, nr2) + '。',
      '代入 ' + T('P' + vt(p.P)) + ' 定常數：' + T(subTex(nr2, p.P) + '=' + pl2[3]) + '，所以 ' + T('F:' + planeTex(pl2)) + '。' + solFin(o)];
  };

  L1_SOL.planeAngleCoef = function (p, o) {
    var n = p.n, u = p.u, m = p.m, oth = [0, 1, 2].filter(function (i) { return i !== u; }), j = oth[0], k = oth[1];
    var S = n[j] * n[j] + n[k] * n[k], Q = p.deg45 ? 2 * n[m] * n[m] : n2(n), plName = PLANES[PLMISS.indexOf(m)];
    var nPos = n.slice(), nNeg = n.slice(); nPos[u] = Math.abs(n[u]); nNeg[u] = -Math.abs(n[u]);
    var E1 = normPlane([nPos[0], nPos[1], nPos[2], p.D]), E2 = normPlane([nNeg[0], nNeg[1], nNeg[2], p.D]);
    var Pj = [0, 0, 0], Pk = [0, 0, 0]; Pj[j] = p.D / n[j]; Pk[k] = p.D / n[k];
    var cosT = p.deg45 ? '\\cos45^\\circ=\\dfrac{1}{\\sqrt2}' : '\\cos\\theta=' + Fr.tex(F(Math.abs(n[m]), Math.sqrt(n2(n))));
    return ['平面過 ' + T(vt(Pj)) + '、' + T(vt(Pk)) + '，可設 ' + T('E:' + xpSymLhs(n, u, 'k') + '=' + p.D) + '（兩點代入左式都得 ' + T(String(p.D)) + '）。',
      T(plName) + ' 平面的法向量是 ' + T(vt([m === 0 ? 1 : 0, m === 1 ? 1 : 0, m === 2 ? 1 : 0])) + '，所以 ' + T('\\dfrac{' + Math.abs(n[m]) + '}{\\sqrt{k^2+' + S + '}}') + ' 要等於 ' + T(cosT) + '；平方後 ' + T('k^2+' + S + '=' + Q) + '，' + T('k^2=' + (Q - S)) + '，' + T('k=\\pm' + Math.abs(n[u])) + '。',
      '所以 ' + T('E:' + planeTex(E1)) + ' 或 ' + T('E:' + planeTex(E2)) + '。' + solFin(o)];
  };

  L1_SOL.planeSideRatio = function (p, o) {
    var n = p.n, D = p.D, fA = dot(n, p.A) - D, fB = dot(n, p.B) - D, g = gcd(fA, fB), m = Math.abs(fA) / g, k = Math.abs(fB) / g;
    var s1 = '把兩點代入「左式減常數」：' + T('A') + '：' + T(subTex(n, p.A) + '-' + solNeg(D) + '=' + fA) + '；' + T('B') + '：' + T(subTex(n, p.B) + '-' + solNeg(D) + '=' + fB) + '。';
    if (!p.opp) return [s1, T(String(fA)) + ' 與 ' + T(String(fB)) + ' 同號 ⟹ 同側；兩點到 ' + T('E') + ' 的距離分母相同，比值 ' + T('d(A,E):d(B,E)=' + Math.abs(fA) + ':' + Math.abs(fB) + '=' + m + ':' + k) + '。' + solFin(o)];
    var AB = sub(p.B, p.A), tt = F(m, m + k), P = [0, 1, 2].map(function (i) { return Fr.add(F(p.A[i]), Fr.mul(tt, F(AB[i]))); });
    return [s1,
      T(String(fA)) + ' 與 ' + T(String(fB)) + ' 異號 ⟹ 異側；交點把 ' + T('\\overline{AB}') + ' 分成距離的比：' + T('\\overline{AP}:\\overline{PB}=' + Math.abs(fA) + ':' + Math.abs(fB) + '=' + m + ':' + k) + '。',
      T(ov('AB') + '=' + vt(AB)) + '，' + T('P=A+' + Fr.tex(tt) + ov('AB')) + '，得交點 ' + T('P' + vtF(P).replace(/\\left|\\right|\\ /g, '')) + '。' + solFin(o)];
  };

  L1_SOL.interLineParam = function (p, o) {
    var n1 = p.n1, n2_ = p.n2, X = p.X, dd = p.dd, i = p.i, cr = cross(n1, n2_), oth = [0, 1, 2].filter(function (k) { return k !== i; }), j = oth[0], k = oth[1];
    var d1 = dot(n1, X), d2 = dot(n2_, X);
    return ['方向：' + T(vec('n_1') + '\\times' + vec('n_2') + '=' + vt(n1) + '\\times' + vt(n2_) + '=' + vt(cr)) + ((cr[0] === dd[0] && cr[1] === dd[1] && cr[2] === dd[2]) ? '，取 ' + T(vec('d') + '=' + vt(dd)) : '，約成最簡得 ' + T(vec('d') + '=' + vt(dd))) + '。',
      '找一點：令 ' + T(AXES[i] + '=' + X[i]) + '，代入兩式得 ' + T(xpEq2(n1[j], AXES[j], n1[k], AXES[k], d1 - n1[i] * X[i])) + '、' + T(xpEq2(n2_[j], AXES[j], n2_[k], AXES[k], d2 - n2_[i] * X[i])) + '，解得 ' + T(AXES[j] + '=' + X[j]) + '、' + T(AXES[k] + '=' + X[k]) + '，交線過 ' + T(vt(X)) + '。',
      '參數式 ' + T('L:' + paramTex(X, dd)) + '。' + solFin(o)];
  };

  L1_SOL.planeLinePt = function (p, o) {
    var dd = p.dd, P0 = p.P0, Q = p.Q, w = sub(Q, P0), nv = cross(dd, w), nr = redPos(nv), pl = planeOf(nr, P0);
    var s1 = p.mode === 0 ? T('L') + ' 上取點 ' + T('P_0' + vt(P0)) + '、方向 ' + T(vec('d') + '=' + vt(dd)) + '；再取 ' + T(ov('P_0P') + '=' + vt(w)) + '，兩者都在 ' + T('E') + ' 上。'
      : T('L_1') + ' 上取 ' + T('P_1' + vt(P0)) + '、' + T('L_2') + ' 上取 ' + T('P_2' + vt(Q)) + '；共同方向 ' + T(vec('d') + '=' + vt(dd)) + '，另一個方向取 ' + T(ov('P_1P_2') + '=' + vt(w)) + '。';
    return [s1,
      '法向量取外積 ' + T(vec('d') + '\\times' + (p.mode === 0 ? ov('P_0P') : ov('P_1P_2')) + '=' + vt(nv)) + xpNf(nv, nr) + '。',
      '代入 ' + T(vt(P0)) + ' 定常數：' + T(subTex(nr, P0) + '=' + pl[3]) + '，所以 ' + T('E:' + planeTex(pl)) + '。' + solFin(o)];
  };

  /* ══════════════════════════════════════════════════════════
     2026-09-29 新增小節 3-5「直線與平面的夾角」：L1 一型（linePlaneAngleDeg）、L2 一型（linePlaneAngleParam）
     只新增、不改任何既有產生器（既有題型同種子出同一題，錯題本與檢測紀錄的 t.k#seed 仍有效）。
     ══════════════════════════════════════════════════════════ */
  /* 特別角的 sin²：[分子, 分母] */
  var LPA_S2 = { 0: [0, 1], 30: [1, 4], 45: [1, 2], 60: [3, 4], 90: [1, 1] };
  var lpaCache = null;
  /* 所有「小整數法向量 n、小整數方向 d」使夾角恰為 30°、45°、60° 的組合（第一次用到時才列舉） */
  function lpaPairs() {
    if (lpaCache) return lpaCache;
    var ns = [], ds = [], i, j, k;
    for (i = -2; i <= 2; i++) for (j = -2; j <= 2; j++) for (k = -2; k <= 2; k++) {
      var v = [i, j, k]; if (nzc(v) < 2 || gcd3(v) !== 1) continue;
      var w = redPos(v); if (w[0] === v[0] && w[1] === v[1] && w[2] === v[2]) ns.push(v);
    }
    for (i = -3; i <= 3; i++) for (j = -3; j <= 3; j++) for (k = -3; k <= 3; k++) {
      var u = [i, j, k]; if (nzc(u) >= 2 && gcd3(u) === 1) ds.push(u);
    }
    lpaCache = { 30: [], 45: [], 60: [] };
    ns.forEach(function (n) {
      ds.forEach(function (d) {
        var dv = dot(n, d), P = n2(n) * n2(d);
        [30, 45, 60].forEach(function (g) { var s2 = LPA_S2[g]; if (dv * dv * s2[1] === s2[0] * P) lpaCache[g].push([n, d]); });
      });
    });
    return lpaCache;
  }
  function lpaDegTex(g) { return g + '^\\circ'; }
  /* 帶一個字母的向量：(2,k,-1) */
  function lpaSymVec(v, i, sym) { return '(' + [0, 1, 2].map(function (m) { return m === i ? sym : String(v[m]); }).join(',') + ')'; }
  /* 一元二次式 c2·k²+c1·k+c0（首項為正、約去公因數） */
  function lpaQuad(c2, c1, c0) {
    var g = gcd(gcd(Math.abs(c2), Math.abs(c1)), Math.abs(c0)) || 1;
    if (c2 < 0) g = -g;
    c2 /= g; c1 /= g; c0 /= g;
    var s = term(c2, 'k^2', true) + term(c1, 'k', false) + (c0 === 0 ? '' : (c0 > 0 ? '+' : '') + c0);
    return { tex: s + '=0', c: [c2, c1, c0] };
  }
  /* 有理根（兩相異）：回傳 [F, F] 由小到大，否則 null */
  function lpaRoots(c2, c1, c0) {
    if (c2 === 0) return null;
    var D = c1 * c1 - 4 * c2 * c0; if (D <= 0) return null;
    var q = Math.round(Math.sqrt(D)); if (q * q !== D) return null;
    var r1 = F(-c1 - q, 2 * c2), r2 = F(-c1 + q, 2 * c2);
    if (r1.n * r2.d > r2.n * r1.d) { var tt = r1; r1 = r2; r2 = tt; }
    return [r1, r2];
  }

  /* ── §3-5 線面夾角：求角度（特別角）與 0°、90° 的特例 ── */
  L1.linePlaneAngleDeg = function (r) {
    var g = r.pick([30, 45, 60, 0, 30, 45, 60, 90]), n, dd, P0 = rp(r, -4, 4), dE, onE = false;
    if (g === 0 || g === 90) {
      n = redPos(rnv(r, -3, 3, 2));
      if (g === 90) dd = sc(r.pick([1, -1]), n);
      else { var t0 = 0; do { dd = red(perpRand(r, n, -2, 2)); t0++; } while ((isZero(dd) || nzc(dd) < 1) && t0 < 60); }
      onE = g === 0 && r() < 0.5;
      dE = dot(n, P0) + (onE ? 0 : r.pick([1, -1, 2, -2, 3, -3]));
    } else {
      var pr = r.pick(lpaPairs()[g]); n = pr[0]; dd = pr[1];
      dE = r.int(-9, 9);
    }
    var form = r.int(0, 1), Lt = form === 0 ? lineShort(P0, dd, 't') : ratioTex(P0, dd);
    var dv = dot(n, dd), prod = n2(n) * n2(dd);
    var tail = g === 0 ? '（' + (onE ? T('L') + ' 在 ' + T('E') + ' 上' : T('L') + ' 與 ' + T('E') + ' 平行') + '）' : (g === 90 ? '（' + T('L\\perp E') + '）' : '');
    return { q: '求直線 ' + T('L:' + Lt) + ' 與平面 ' + T('E:' + planeTex([n[0], n[1], n[2], dE])) + ' 的夾角 ' + T('\\theta') + '（' + T('0^\\circ\\le\\theta\\le90^\\circ') + '）；若 ' + T('\\theta=0^\\circ') + '，再判斷 ' + T('L') + ' 與 ' + T('E') + ' 平行，還是 ' + T('L') + ' 在 ' + T('E') + ' 上。',
             a: T('\\theta=' + lpaDegTex(g)) + tail,
             h: '用 ' + T('\\sin\\theta=\\dfrac{\\left|' + vec('d') + '\\cdot' + vec('n') + '\\right|}{\\left|' + vec('d') + '\\right|\\left|' + vec('n') + '\\right|}') + '：本題 ' + T(vec('d') + '=' + vt(dd)) + '、' + T(vec('n') + '=' + vt(n)) + '，' + T(vec('d') + '\\cdot' + vec('n') + '=' + dv) + '，' + T('\\sin^2\\theta=\\dfrac{' + (dv * dv) + '}{' + n2(dd) + '\\times' + n2(n) + '}') + '。再對照 ' + T('\\sin30^\\circ=\\dfrac12') + '、' + T('\\sin45^\\circ=\\dfrac{\\sqrt2}{2}') + '、' + T('\\sin60^\\circ=\\dfrac{\\sqrt3}{2}') + (dv === 0 ? '；內積是 ' + T('0') + '，還要把 ' + T('P_0' + vt(P0)) + ' 代進 ' + T('E') + ' 看看在不在平面上。' : '。'),
             p: { n: n, dd: dd, P0: P0, dE: dE, deg: g, onE: onE } };
  };

  /* ── §3-5 由線面夾角求未知數（方向向量或平面係數裡有一個 k） ── */
  L2.linePlaneAngleParam = function (r) {
    var mode = r.int(0, 1), t = 0, g, n, dd, i, rts, c2, c1, c0, A, Bc, S, fix, s2;
    do {
      g = r.pick([30, 45, 60]); s2 = LPA_S2[g];
      i = r.int(0, 2);
      if (mode === 0) {                 /* 方向向量 dd 的第 i 個分量是 k，平面固定 */
        n = redPos(rnv(r, -2, 2, 2)); dd = rp(r, -3, 3); dd[i] = 0;
        if (nzc(dd) < 1) { t++; continue; }
        fix = n; A = n[i]; Bc = dot(n, dd); S = n2(dd);
        c2 = s2[1] * A * A - s2[0] * n2(n); c1 = 2 * s2[1] * A * Bc; c0 = s2[1] * Bc * Bc - s2[0] * n2(n) * S;
      } else {                          /* 平面法向量的第 i 個係數是 k，直線固定 */
        dd = rnv(r, -3, 3, 2); n = rp(r, -3, 3); n[i] = 0;
        if (nzc(n) < 1) { t++; continue; }
        fix = dd; A = dd[i]; Bc = dot(n, dd); S = n2(n);
        c2 = s2[1] * A * A - s2[0] * n2(dd); c1 = 2 * s2[1] * A * Bc; c0 = s2[1] * Bc * Bc - s2[0] * n2(dd) * S;
      }
      rts = lpaRoots(c2, c1, c0);
      if (rts && rts.every(function (x) { return x.d <= 4 && Math.abs(x.n) <= 12 * x.d; })) break;
      rts = null; t++;
    } while (t < 3000);
    if (!rts) { mode = 0; g = 60; i = 2; n = [1, 0, 1]; dd = [2, 1, 0]; A = 1; Bc = 2; S = 5; s2 = LPA_S2[60]; c2 = 4 - 6; c1 = 16; c0 = 16 - 30; rts = lpaRoots(c2, c1, c0); }
    var P0 = rp(r, -4, 4), qd = lpaQuad(c2, c1, c0), Lt, Et, dvT, dT, nT;
    if (mode === 0) {
      var dE = r.int(-9, 9);
      Lt = '(x,y,z)=' + vt(P0) + '+t' + lpaSymVec(dd, i, 'k'); Et = planeTex([n[0], n[1], n[2], dE]);
      dvT = lin(Bc, A, 'k'); dT = 'k^2+' + S; nT = String(n2(n));
    } else {
      var dE2 = r.nz(-9, 9);
      Lt = r() < 0.5 ? lineShort(P0, dd, 't') : ratioTex(P0, dd); Et = xpSymLhs(n, i, 'k') + '=' + dE2;
      dvT = lin(Bc, A, 'k'); dT = String(n2(dd)); nT = 'k^2+' + S;
    }
    var ans = T('k=' + Fr.tex(rts[0])) + ' 或 ' + T('k=' + Fr.tex(rts[1]));
    return { q: '直線 ' + T('L:' + Lt) + ' 與平面 ' + T('E:' + Et) + ' 的夾角為 ' + T(lpaDegTex(g)) + '，求 ' + T('k') + ' 的所有可能值。',
             a: ans,
             h: '把 ' + T('\\sin\\theta=\\dfrac{\\left|' + vec('d') + '\\cdot' + vec('n') + '\\right|}{\\left|' + vec('d') + '\\right|\\left|' + vec('n') + '\\right|}') + ' 兩邊平方：' + T('\\left(' + vec('d') + '\\cdot' + vec('n') + '\\right)^2=\\sin^2' + lpaDegTex(g) + '\\cdot\\left|' + vec('d') + '\\right|^2\\left|' + vec('n') + '\\right|^2') + '。本題 ' + T(vec('d') + '\\cdot' + vec('n') + '=' + dvT) + '、' + T('\\left|' + vec('d') + '\\right|^2=' + dT) + '、' + T('\\left|' + vec('n') + '\\right|^2=' + nT) + '、' + T('\\sin^2' + lpaDegTex(g) + '=' + Fr.tex(F(s2[0], s2[1]))) + '，整理得 ' + T(qd.tex) + '，平方後兩個解都要代回檢查。',
             p: { mode: mode, n: n, dd: dd, i: i, deg: g, P0: P0 } };
  };

  /* ── L1 新型的第一層提示與解題步驟 ── */
  L1_H1.linePlaneAngleDeg = '這是「線面夾角的角度與特例」：用正弦公式算出夾角的正弦值，再對照特別角；正弦值是 0 時，還要代點分辨直線與平面平行或直線在平面上。';
  L1_SOL.linePlaneAngleDeg = function (p, o) {
    var n = p.n, dd = p.dd, dv = dot(n, dd), prod = n2(n) * n2(dd), g = p.deg, b = dot(n, p.P0);
    var s1 = '讀出 ' + T(vec('d') + '=' + vt(dd)) + '、' + T(vec('n') + '=' + vt(n)) + '，' + T(vec('d') + '\\cdot' + vec('n') + '=' + subTex(dd, n) + '=' + dv) + '，' + T(solAbsT(vec('d')) + '^2=' + n2(dd)) + '、' + T(solAbsT(vec('n')) + '^2=' + n2(n)) + '。';
    if (g === 0) return [s1,
      '內積為 ' + T('0') + ' ⟹ ' + T('\\sin\\theta=0') + '，' + T('\\theta=0^\\circ') + '。',
      '再看 ' + T('P_0' + vt(p.P0)) + '：代入 ' + T('E') + ' 的左式得 ' + T(subTex(n, p.P0) + '=' + b) + '，常數項是 ' + T(String(p.dE)) + '，' + (p.onE ? '相等 ⟹ ' + T('L') + ' 在 ' + T('E') + ' 上。' : '不相等 ⟹ ' + T('L') + ' 與 ' + T('E') + ' 平行。') + solFin(o)];
    if (g === 90) return [s1,
      T(vec('d') + '=' + (dv > 0 ? '' : '-') + vec('n')) + '，方向與法向量平行 ⟹ ' + T('L\\perp E') + '；公式也給 ' + T('\\sin\\theta=\\dfrac{' + Math.abs(dv) + '}{' + Math.abs(dv) + '}=1') + '，' + T('\\theta=90^\\circ') + '。' + solFin(o)];
    var sv = { 30: '\\dfrac12', 45: '\\dfrac{\\sqrt2}{2}', 60: '\\dfrac{\\sqrt3}{2}' }[g];
    return [s1,
      T('\\sin^2\\theta=\\dfrac{' + (dv * dv) + '}{' + prod + '}' + (F(dv * dv, prod).d === prod ? '' : '=' + Fr.tex(F(dv * dv, prod)))) + '，所以 ' + T('\\sin\\theta=' + sv) + '。',
      '夾角在 ' + T('0^\\circ') + ' 到 ' + T('90^\\circ') + ' 之間，正弦是 ' + T(sv) + ' 的角是 ' + T(lpaDegTex(g)) + '。' + solFin(o)];
  };
  var META_L1 = [
      ['planePointNormal', '§1 由點與法向量寫平面'], ['planeThreePts', '§1 三點決定平面'], ['planeIntercepts', '§1 讀係數與坐標軸交點'], ['planeSpecial', '§1 特殊位置的平面'], ['twoPlanesRel', '§1 兩平面的位置關係與夾角'], ['coplanarK', '§1 四點共平面求未知數'], ['planeTwoPtsPerp', '§1 過兩點（或一點）且垂直已知平面'], ['planeAngleCoef', '§1 由兩面角求平面的係數'],
      ['ptPlaneDist', '§2 點到平面的距離'], ['parallelPlaneDist', '§2 平行平面與兩平面距離'], ['planeProjSym', '§2 投影點與對稱點'], ['planeDistUnknown', '§2 已知距離求未知數'], ['tetraPlaneDist', '§2 三點的平面與體積法'], ['planeSideRatio', '§2 兩點在平面的同側或異側'],
      ['lineParamRatio', '§3 參數式與比例式'], ['lineReadBack', '§3 讀回點與方向向量'], ['lineTwoPts', '§3 兩點決定直線'], ['linePlaneInt', '§3 直線與平面的交點'], ['linePlaneRel', '§3 直線與平面的位置關係'], ['linePlaneAngle', '§3 直線與平面的夾角'], ['interLineParam', '§3 兩平面的交線化成參數式'], ['planeLinePt', '§3 含直線且過一點的平面'], ['linePlaneAngleDeg', '§3 線面夾角的角度與特例'],
      ['ptLineDist', '§4 點到直線的距離'], ['footPerp', '§4 垂足與最近點'], ['parallelLineDist', '§4 兩平行線的距離'], ['twoLinesRel', '§4 兩直線的位置關係'], ['skewLineDist', '§4 兩歪斜線的距離'],
      ['symPtLine', '§5 點對直線的對稱點'], ['mirrorReflect', '§5 對坐標平面的鏡面反射'], ['boxCoord', '§5 長方體的坐標化']
  ];
  var META_L2 = [
      ['threePlanesRel', '§1 三平面的位置關係'], ['planeThroughInter', '§1 過兩平面交線的平面'],
      ['bisectPlanes', '§2 兩平面的角平分面'], ['chordTwoPlanes', '§2 兩平行平面截出的線段'], ['tetraVolHeight', '§2 四面體的體積與高'], ['maxDistPlaneLine', '§2 過定直線的平面：最大距離'],
      ['planeContainLinePerp', '§3 含直線且垂直已知平面的平面'], ['interLineAxis', '§3 兩平面交線與坐標軸'],
      ['commonPerpSeg', '§4 公垂線段的兩端點'], ['lineBisector', '§4 兩直線的角平分線'], ['boxSkewDist', '§4 長方體中的歪斜線'],
      ['lineProjPlane', '§5 直線在平面上的投影'], ['segProjPlane', '§5 線段的正射影長'], ['rayReflectPlane', '§5 光線的反射'], ['shortestPath', '§5 平面上動點的最短路徑'], ['boxPlaneDist', '§5 長方體中點到截面的距離'],
      ['planeParLine', '§4 含一直線且平行另一直線的平面'], ['linesCoplanarK', '§4 兩直線相交求未知數'], ['spaceFacts', '§1 直線與平面的敘述判斷'], ['linePlaneParam', '§3 直線在平面上、平行或垂直求未知數'], ['planeMinDist', '§2 平面上的點：距離平方和最小'], ['pyramidCoord', '§5 正四角錐的坐標化與兩面角'],
      ['linePlaneAngleParam', '§3 由線面夾角求未知數']
  ];
  /* ══════════════════════════════════════════════════════════
     L3　中上（19 型；2026-09-29 擴充 3 型＋新小節 3-5 一型）：每型對應固定題 L3-1～L3-15 的「類似題」
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
        : '內積不等於 ' + T('0') + ' 的一定相交（直接刪）；等於 ' + T('0') + ' 的再代一個點看在不在 ' + T('E') + ' 上：在的話是落在 ' + T('E') + ' 上，也有交點。');
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
    var base = T('L_2') + ' 的兩式中，' + T(e3) + ' 沒有 ' + T('k') + '，交點一定同時在 ' + T('L_1') + ' 與這個平面上，先用這三式把交點定出來，' + T('k') + ' 最後代進去就好。把 ' + T('L_1') + ' 化成參數式：令 ' + T('z=u') + '，由 ' + T(e1) + ' 與 ' + T(e2) + ' 消去法解出 ' + T('x') + '、' + T('y') + '（方向向量 ' + T(vec('n_1') + '\\times' + vec('n_2') + '=' + vt(w)) + '），代入 ' + T(e3) + ' 解出 ' + T('u') + '，就得到交點；再算 ' + T(lhsTex(n4[0], n4[1], n4[2])) + ' 即為 ' + T('k') + '。';
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

  /* ══════════ 2026-09-29 擴充：L3-16～L3-18 的類似題 ══════════ */
  function l3xAllNz(v) { return v[0] !== 0 && v[1] !== 0 && v[2] !== 0; }
  /* 坐標裡有兩個換成字母：idx 是字母的位置、names 是字母 */
  function l3symPt(P, idx, names) { return '(' + [0, 1, 2].map(function (k) { var w = idx.indexOf(k); return w >= 0 ? names[w] : String(P[k]); }).join(',') + ')'; }

  /* L3-16　與兩歪斜線都垂直且都相交的直線（公垂線）上的點 */
  L3.commonPerpPoint = function (r) {
    var d1, d2, c, t = 0;
    do { d1 = rnv(r, -3, 3, 3); d2 = rnv(r, -3, 3, 3); c = cross(d1, d2); t++; } while ((isZero(c) || l3mx(red(c)) > 6) && t < 300);
    c = red(c);
    var F1 = rp(r, -4, 4), mm = r.pick([1, -1, 2, -2]), F2 = add(F1, sc(mm, c));
    var a = r.pick([1, -1, 2, -2]), b = r.pick([1, -1, 2, -2]), P1 = add(F1, sc(a, d1)), P2 = add(F2, sc(b, d2));
    var ws = [0, 1, 2].filter(function (k) { return c[k] !== 0; }), w = r.pick(ws), tau = r.pick([2, -2, 3, -3]), A = add(F1, sc(tau, c));
    var hid = [0, 1, 2].filter(function (k) { return k !== w; }), v = r.int(0, 1);
    var head = '兩歪斜線 ' + T('L_1:' + ratioTex(P1, d1)) + '、' + T('L_2:' + ratioTex(P2, d2)) + '。直線 ' + T('L_3') + ' 與 ' + T('L_1') + '、' + T('L_2') + ' 都垂直而且都相交，點 ' + T('A' + l3symPt(A, hid, ['p', 'q'])) + ' 在 ' + T('L_3') + ' 上。';
    var h = T('L_3') + ' 就是公垂線，方向取 ' + T(vec('d_1') + '\\times' + vec('d_2') + '=' + vt(cross(d1, d2))) + '（約簡為 ' + T(vt(c)) + '）。再求公垂線段的一個端點：令 ' + T('M=' + vt(P1) + '+t' + vt(d1)) + '、' + T('N=' + vt(P2) + '+s' + vt(d2)) + '，由 ' + T(ov('MN') + '\\cdot' + vec('d_1') + '=0') + '、' + T(ov('MN') + '\\cdot' + vec('d_2') + '=0') + ' 解 ' + T('t,s') + '；' + T('L_3:M+u' + vt(c)) + '，用 ' + T('A') + ' 的 ' + T(AXES[w]) + ' 坐標 ' + T(String(A[w])) + ' 定出 ' + T('u') + '。';
    if (v === 0) return { q: head + '求 ' + T('(p,q)') + '。', a: T('(p,q)=(' + A[hid[0]] + ',' + A[hid[1]] + ')'), h: h, p: { v: 0, P1: P1, d1: d1, P2: P2, d2: d2, w: w, ans: A } };
    return { q: head + '(1) 求公垂線段的兩端點 ' + T('M\\in L_1') + '、' + T('N\\in L_2') + '。(2) 求 ' + T('(p,q)') + '。',
             a: '(1) ' + T('M' + vt(F1)) + '、' + T('N' + vt(F2)) + '　(2) ' + T('(p,q)=(' + A[hid[0]] + ',' + A[hid[1]] + ')'), h: h, p: { v: 1, P1: P1, d1: d1, P2: P2, d2: d2, w: w, ans: A } };
  };

  /* L3-17　兩平面交線上、到兩點等距的點：中垂面與直線的交點 */
  L3.equidistOnLine = function (r) {
    var g = lineTwoPlanes(r), Q = add(g.X, sc(r.int(-2, 2), g.dd)), w, t = 0;
    do { w = rnv(r, -3, 3, 2); t++; } while (dot(w, g.dd) === 0 && t < 100);
    if (dot(w, g.dd) === 0) w = g.dd.slice();
    var u = perpRand(r, w, -2, 2), M = add(Q, u), A = sub(M, w), Bp = add(M, w);
    var d1 = dot(g.n1, g.X), d2 = dot(g.n2, g.X), v = r.int(0, 1), wr = redPos(w);
    var Ltex = l3cases([planeTex([g.n1[0], g.n1[1], g.n1[2], d1]), planeTex([g.n2[0], g.n2[1], g.n2[2], d2])]);
    var h = T('\\overline{QA}=\\overline{QB}') + ' ⟹ ' + T('Q') + ' 在 ' + T('\\overline{AB}') + ' 的中垂面上：過中點 ' + T(vt(M)) + '、法向量 ' + T(ov('AB') + '=' + vt(sc(2, w))) + '（約簡為 ' + T(vt(wr)) + '），中垂面 ' + T(planeTex([wr[0], wr[1], wr[2], dot(wr, M)])) + '。把它和 ' + T('L') + ' 的兩個平面方程式聯立（三元一次），解出來的點就是 ' + T('Q') + '。';
    var q = '空間中有 ' + T('A' + vt(A)) + '、' + T('B' + vt(Bp)) + ' 兩點，點 ' + T('Q') + ' 在直線 ' + T('L:' + Ltex) + ' 上，而且 ' + T('Q') + ' 到 ' + T('A') + '、' + T('B') + ' 的距離相等。';
    if (v === 0) return { q: q + '求 ' + T('Q') + ' 的坐標。', a: T('Q' + vt(Q)), h: h, p: { v: 0, n1: g.n1, n2: g.n2, X: g.X, A: A, B: Bp, ans: Q } };
    return { q: q + '(1) 求 ' + T('Q') + ' 的坐標。(2) 求 ' + T('\\overline{QA}') + '。', a: '(1) ' + T('Q' + vt(Q)) + '　(2) ' + T(sqrtTex(n2(sub(Q, A)))), h: h, p: { v: 1, n1: g.n1, n2: g.n2, X: g.X, A: A, B: Bp, ans: Q } };
  };

  /* L3-18　第三頂點在坐標平面上、周長最小：對稱點連線，再算面積 */
  L3.perimMinArea = function (r) {
    var pli = r.int(0, 2), mi = PLMISS[pli], C = rp(r, -4, 4), w, t = 0;
    C[mi] = 0;
    do { w = rp(r, -3, 3); w[mi] = r.int(1, 2); t++; } while (((w[(mi + 1) % 3] === 0 && w[(mi + 2) % 3] === 0) || gcd3(w) !== 1) && t < 100);
    var mu = r.int(1, 3), nu = r.int(1, 3), Ap = sub(C, sc(mu, w)), A = Ap.slice(), Bp = add(C, sc(nu, w));
    A[mi] = -Ap[mi];
    var cr = cross(sub(Bp, A), sub(C, A)), area = sqrtFracTex(n2(cr), 4), v = r.int(0, 2);
    var Cq = '(' + [0, 1, 2].map(function (k) { return k === mi ? '0' : AXES[k]; }).join(',') + ')';
    var head = T('\\triangle ABC') + ' 中，' + T('A' + vt(A)) + '、' + T('B' + vt(Bp)) + '，頂點 ' + T('C' + Cq) + ' 在 ' + T(PLANES[pli]) + ' 平面上移動。';
    var h = T('\\overline{AB}') + ' 固定，周長最小 ⟺ ' + T('\\overline{AC}+\\overline{CB}') + ' 最小。' + T('A') + '、' + T('B') + ' 的 ' + T(AXES[mi]) + ' 坐標同號（同側），把 ' + T('A') + ' 對 ' + T(PLANES[pli]) + ' 平面作對稱點 ' + T("A'" + vt(Ap)) + '，' + T('C') + ' 取 ' + T("\\overline{A'B}") + ' 與平面的交點；面積用 ' + T('\\dfrac12\\left|' + ov('AB') + '\\times' + ov('AC') + '\\right|') + '。';
    if (v === 0) return { q: head + '當 ' + T('\\triangle ABC') + ' 的周長最小時，求 ' + T('C') + ' 的坐標與 ' + T('\\triangle ABC') + ' 的面積。', a: T('C' + vt(C)) + '，面積 ' + T(area), h: h, p: { v: 0, A: A, B: Bp, pli: pli, ans: C } };
    if (v === 1) return { q: head + '(1) 求 ' + T('\\overline{AC}+\\overline{CB}') + ' 的最小值。(2) 此時 ' + T('C') + ' 的坐標為何？', a: '(1) ' + T(sqrtTex((mu + nu) * (mu + nu) * n2(w))) + '　(2) ' + T('C' + vt(C)), h: h, p: { v: 1, A: A, B: Bp, pli: pli, ans: C } };
    return { q: head + '當 ' + T('\\triangle ABC') + ' 的周長最小時，求 ' + T('\\triangle ABC') + ' 的面積。', a: T(area), h: h, p: { v: 2, A: A, B: Bp, pli: pli, ans: C } };
  };

  /* ══════════ 2026-09-29 新增小節 3-5：L3-19 的類似題 ══════════ */
  /* L3-19　坐標軸（或直線）與平面的夾角：問餘弦或正切，先求正弦再用 sin²θ+cos²θ=1 */
  L3.linePlaneTrig = function (r) {
    var v = r.int(0, 1), ask = r.int(0, 2), n, dd, t = 0, dv, P, Q, ax = 0;
    var L3N = [[1, 2, 2], [2, 3, 6], [1, 4, 8], [4, 4, 7]];
    function l3pv(lst) { var v0 = r.shuffle(r.pick(lst)); return redPos([v0[0] * r.sign(), v0[1] * r.sign(), v0[2] * r.sign()]); }
    do {
      n = l3pv(L3N);
      if (v === 0) { ax = r.int(0, 2); dd = [0, 0, 0]; dd[ax] = 1; }
      else dd = l3pv([[1, 2, 2], [2, 3, 6]]);
      dv = dot(n, dd); P = n2(n) * n2(dd); Q = dv * dv; t++;
    } while ((Q === 0 || Q === P) && t < 200);
    if (Q === 0 || Q === P) { v = 0; ax = 1; n = [6, 2, 3]; dd = [0, 1, 0]; dv = 2; P = 49; Q = 4; }
    var dE = r.int(-9, 9), P0 = rp(r, -4, 4);
    var obj = v === 0 ? T(AXES[ax]) + ' 軸' : '直線 ' + T('L:' + lineShort(P0, dd, 't'));
    var Ft = 'F:' + planeTex([n[0], n[1], n[2], dE]);
    var cosT = sqrtFracTex(P - Q, P), tanT = sqrtFracTex(Q, P - Q), sinT = sqrtFracTex(Q, P);
    var askT = ask === 0 ? T('\\cos\\theta') : (ask === 1 ? T('\\tan\\theta') : '(1) ' + T('\\cos\\theta') + '　(2) ' + T('\\tan\\theta'));
    var a = ask === 0 ? T('\\cos\\theta=' + cosT) : (ask === 1 ? T('\\tan\\theta=' + tanT) : '(1) ' + T('\\cos\\theta=' + cosT) + '　(2) ' + T('\\tan\\theta=' + tanT));
    var h = '先用線面夾角的公式求正弦：' + (v === 0 ? T(AXES[ax]) + ' 軸的方向 ' + T(vt(dd)) : T(vec('d') + '=' + vt(dd))) + '、' + T(vec('n') + '=' + vt(n)) + '，' + T('\\sin\\theta=\\dfrac{' + Math.abs(dv) + '}{\\sqrt{' + n2(dd) + '}\\sqrt{' + n2(n) + '}}=' + sinT) + '。' + T('\\theta') + ' 在 ' + T('0^\\circ') + ' 到 ' + T('90^\\circ') + ' 之間，' + T('\\cos\\theta=\\sqrt{1-\\sin^2\\theta}') + ' 取正的，' + T('\\tan\\theta=\\dfrac{\\sin\\theta}{\\cos\\theta}') + '。';
    return { q: obj + (v === 0 ? '與平面 ' : ' 與平面 ') + T(Ft) + ' 的夾角為 ' + T('\\theta') + '，求 ' + askT + '。', a: a, h: h,
             p: { v: v, ax: ax, n: n, dd: dd, ask: ask } };
  };
  var META_L3 = [
    ['axisTriDist', '三點在坐標軸上求點到平面距離'], ['parallelLineChoice', '直線與平面沒有交點的判別'], ['lineTwoEqLen', '兩方程式的直線＋長度條件'], ['maxDistThroughPt', '過定點的平面：最大距離'], ['parPlanesScaled', '係數要先對齊的兩平行平面距離'],
    ['interLineDirComp', '兩平面交線方向指定分量'], ['uniformMotion', '等速直線運動的位置'], ['ptLineDistCross', '點到直線的距離（外積）'], ['projOnLine', '點在直線上的投影點'], ['symPtLineMin', '點對直線的對稱點與最短距離'],
    ['axisSkewDist', '各自平行坐標軸的兩歪斜線'], ['chainLineDist', 'ax=by=cz 與平行線距離'], ['twoLineSysK', '兩交線型直線相交求參數'], ['lineCoordPlaneInt', '直線與坐標平面的交點'], ['rayMeet', '兩束光線的交點'],
    ['commonPerpPoint', '公垂線上的點'], ['equidistOnLine', '直線上到兩點等距的點'], ['perimMinArea', '周長最小的三角形面積'],
    ['linePlaneTrig', '線面夾角的餘弦與正切']
  ];
  /* 固定題 L3-n 對應的類似題型 */
  var L3_FIX = { 'L3-1': 'axisTriDist', 'L3-2': 'parallelLineChoice', 'L3-3': 'lineTwoEqLen', 'L3-4': 'maxDistThroughPt', 'L3-5': 'parPlanesScaled', 'L3-6': 'interLineDirComp', 'L3-7': 'uniformMotion', 'L3-8': 'ptLineDistCross', 'L3-9': 'projOnLine', 'L3-10': 'symPtLineMin', 'L3-11': 'axisSkewDist', 'L3-12': 'chainLineDist', 'L3-13': 'twoLineSysK', 'L3-14': 'lineCoordPlaneInt', 'L3-15': 'rayMeet', 'L3-16': 'commonPerpPoint', 'L3-17': 'equidistOnLine', 'L3-18': 'perimMinArea', 'L3-19': 'linePlaneTrig' };

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
      h: '消去法：先用第一式分別與第二、第三式消掉 $x$（$x$ 的係數 $' + rows[0][0] + '$、$' + rows[1][0] + '$、$' + rows[2][0] + '$，乘到相同後' + k + '），剩下 $y,z$ 的二元一次聯立，解完回代。本章「三平面交於一點」「兩平面的交線」就是在解它，消到剩一個未知數就停。',
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
    vec3Ops: { txt: '空間向量的內積與外積（高二下第一章 空間向量），法向量、交線方向、三種距離公式全靠它們', link: '../g11b-ch01/practice.html#L1' },
    det3Vol: { txt: '三階行列式與平行六面體體積（高二下第一章），判共面、體積法求距離都在算它', link: '../g11b-ch01/practice.html#L1' },
    linSys3: { txt: '三元一次聯立的消去法（國中），三平面的交點、兩平面的交線就是在解它', link: null },
    ptLineDist2D: { txt: '平面上點到直線的距離（高一上第二章 直線與圓），點到平面的距離公式只是多一個坐標', link: '../g10a-ch02/practice.html#L1' },
    sqrtSimp: { txt: '根式化簡與分母有理化（高一上第一章 數與式），每一個距離的答案都要化到最簡', link: '../g10a-ch01/practice.html#L1' }
  };
  /* ══════════════════════════════════════════════════════════
     對照題：同一型抽兩題，只差一個關鍵特徵（f 由 p 算出；keep 的欄位要相同）
     ══════════════════════════════════════════════════════════ */
  function sign3(x) { return x > 0 ? 1 : x < 0 ? -1 : 0; }
  var CONTRAST = {
    'L1.planeSpecial': { f: function (p) { return p.pl; }, why: '含某坐標軸的平面：常數項是 $0$、且少掉該軸的變數（含 $z$ 軸 ⟹ $ax+by=0$）；平行某坐標平面的平面只剩「缺席」的那個坐標（平行 $xy$ 平面 ⟹ $z=k$、平行 $yz$ 平面 ⟹ $x=k$）。這兩題只差平行的是哪一個坐標平面，看法向量是哪一個坐標軸的方向。' },
    'L1.twoPlanesRel': { f: function (p) { return p.mode; }, why: '兩平面的關係只看法向量：法向量平行 ⟹ 平面平行（常數項也成比例就重合）；法向量內積 $0$ ⟹ 垂直；其餘相交成一個夾角，$\\cos\\theta=\\dfrac{|\\vec n_1\\cdot\\vec n_2|}{|\\vec n_1||\\vec n_2|}$ 取絕對值只算銳角。' },
    'L1.coplanarK': { f: function (p) { return p.hide; }, why: '四點共平面就是「第四點滿足前三點的平面方程式」：不管未知數藏在哪一個坐標，都是先用三個已知點算出平面，再把第四點代入解一次方程式。藏的坐標不同，只是解的是 $x$、$y$ 或 $z$。' },
    'L1.parallelPlaneDist': { f: function (p) { return p.mode; }, why: '兩平行平面的距離公式 $\\dfrac{|d_1-d_2|}{|\\vec n|}$ 只有在**兩式的左邊完全一樣**時才能用：係數成倍數的要先除成一樣，否則就改用「在其中一個平面上任取一點，算它到另一個平面的距離」。' },
    'L1.planeDistUnknown': { f: function (p) { return p.mode; }, why: '「已知距離求未知數」去絕對值一定得到兩個答案：未知數在常數項時是平面往法向量兩側各平移一次；未知數在點的坐標時是點落在平面兩側各一個位置。' },
    'L1.lineParamRatio': { f: function (p) { return p.mode; }, why: '參數式改比例式是「把 $t$ 解出來讓三個式子相等」：方向向量的分量都不為 $0$ 時三段直接相等；有 $0$ 分量時那一項不能當分母，要單獨寫成「$y=y_0$」；兩個 $0$ 就剩一個分式加兩條常數式。' },
    'L1.lineReadBack': { f: function (p) { return p.form; }, why: '從參數式讀回：起點是常數項、方向是 $t$ 的係數；從比例式讀回：分子的 $x-x_0$ 給起點（$x+2$ 要讀成 $x-(-2)$）、分母給方向，分母寫成負數時方向向量那個分量也是負的。' },
    'L1.linePlaneRel': { f: function (p) { return p.mode; }, why: '先看 $\\vec n\\cdot\\vec d$：不是 $0$ 就一定相交於一點；是 $0$ 再看直線上的一點在不在平面上：在就是「直線在平面上」，不在就是「平行」。兩步缺一不可。' },
    'L1.twoLinesRel': { f: function (p) { return p.mode; }, why: '先看方向向量是否成比例：成比例再看一點在不在另一條上，分「平行／重合」；不成比例則算 $\\det(\\vec d_1,\\vec d_2,\\overrightarrow{P_1P_2})$，為 $0$ 是相交（要解出交點），不為 $0$ 是歪斜。' },
    'L1.mirrorReflect': { f: function (p) { return p.pl; }, why: '對坐標平面反射只改「缺席」的那個坐標的正負：對 $xy$ 平面改 $z$、對 $yz$ 平面改 $x$、對 $zx$ 平面改 $y$；反射光線的方向是「對稱點 → 入射點」，即 $\\overrightarrow{P\'M}$。' },
    'L2.threePlanesRel': { f: function (p) { return p.cse; }, why: '三平面用消去法：三個未知數都解得出來就是交於一點；消到某一式變成 $0=0$ 是少一條有效方程式（交於一直線）；變成 $0=\\text{非零}$ 就沒有共同點。沒有共同點又分「三面兩兩相交成三條平行線（三稜柱型）」與「有兩面平行」，看法向量是否平行來區分。' },
    'L2.interLineAxis': { f: function (p) { return p.ax; }, why: '交線與某坐標軸的關係：先由 $\\vec n_1\\times\\vec n_2$ 得交線方向，再看它與該軸方向 $(1,0,0)$、$(0,1,0)$、$(0,0,1)$ 的關係：平行看是否成比例，相交看交線上的點能否讓另外兩個坐標同時為 $0$；問的是哪一軸，看的分量就不同。' },
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
  /* 2026-09-29 擴充題型的對照題 */
  CONTRAST['L1.planeTwoPtsPerp'] = { f: function (p) { return p.mode; }, why: '兩題都是「法向量要同時垂直兩個向量，取外積」：過兩點且垂直一個平面，兩個向量是 $\\overrightarrow{AB}$ 與 $\\vec n_E$；過一點且垂直兩個平面，兩個向量是 $\\vec n_1$ 與 $\\vec n_2$。先認出是哪兩個向量，再代點定常數。' };
  CONTRAST['L1.planeSideRatio'] = { f: function (p) { return p.opp; }, why: '代入「左式減常數」得到的兩個值，同號是同側、異號是異側。異側時線段 $\\overline{AB}$ 穿過平面，交點分 $\\overline{AB}$ 的比就是兩個值的絕對值比；同側時沒有交點，這個比是兩點到平面的距離比。' };
  CONTRAST['L1.planeLinePt'] = { f: function (p) { return p.mode; }, why: '平面的法向量要兩個不平行的方向：含一直線過一點，用直線的方向與「線上一點到那個點」的連線；含兩平行線，兩條線只提供同一個方向，第二個方向一定要取兩線上各一點的連線。' };
  CONTRAST['L2.linePlaneParam'] = { f: function (p) { return p.mode; }, why: '直線在平面上：方向垂直法向量，而且線上的點在平面上（兩個條件）；直線與平面平行：只要方向垂直法向量，線上的點不能在平面上（所以是「不等於」）；直線與平面垂直：方向與法向量平行（成比例）。' };
  CONTRAST['L2.planeMinDist'] = { f: function (p) { return p.mode; }, why: '平面上的點 $(x,y,z)$ 到定點的距離最小值就是定點到平面的距離：問平方和就答距離的平方，問根號就答距離本身；取到最小值的點都是定點在平面上的投影點。' };
  CONTRAST['L3.commonPerpPoint'] = { f: function (p) { return p.v; }, why: '「與兩歪斜線都垂直且都相交」的直線只有一條，就是公垂線：方向 $\\vec d_1\\times\\vec d_2$，還要一個端點才寫得出來；問線上的點只要再用已知的那個坐標定參數。' };
  CONTRAST['L3.perimMinArea'] = { f: function (p) { return p.v; }, why: '周長最小只看 $\\overline{AC}+\\overline{CB}$：同側兩點先把 $A$ 對平面作對稱點，最小值是 $\\overline{A\'B}$，取到最小的 $C$ 是 $\\overline{A\'B}$ 與平面的交點；問面積就再用外積。' };

  /* 2026-09-29 新增小節 3-5 的對照題 */
  CONTRAST['L1.linePlaneAngleDeg'] = { f: function (p) { return p.deg === 0 ? 0 : (p.deg === 90 ? 2 : 1); }, why: '三種情形都先算 $\\vec d\\cdot\\vec n$：等於 $0$ 是 $0^\\circ$（平行或在平面上，要代點分辨）；$\\vec d$ 與 $\\vec n$ 平行是 $90^\\circ$；其他就算出 $\\sin\\theta$，再對照 $\\frac12$、$\\frac{\\sqrt2}{2}$、$\\frac{\\sqrt3}{2}$。' };
  CONTRAST['L2.linePlaneAngleParam'] = { f: function (p) { return p.mode; }, why: '未知數在方向向量裡，它會出現在 $\\vec d\\cdot\\vec n$ 與 $\\left|\\vec d\\right|^2$；未知數在平面的係數裡，它會出現在 $\\vec d\\cdot\\vec n$ 與 $\\left|\\vec n\\right|^2$。兩種都是把正弦公式平方，得到一元二次方程式。' };
  CONTRAST['L3.linePlaneTrig'] = { f: function (p) { return p.ask; }, why: '公式算出來的永遠是 $\\sin\\theta$：問 $\\cos\\theta$ 就用 $\\sqrt{1-\\sin^2\\theta}$，問 $\\tan\\theta$ 就再除一次，$\\tan\\theta=\\dfrac{\\sin\\theta}{\\cos\\theta}$。' };
  /* ══════════════════════════════════════════════════════════
     2026-10-02　附圖題（讀圖型）：圖由產生器依亂數參數即時畫成 inline SVG，放在 q 裡，圖跟著數字變
     立體圖一律用同一個斜投影：x 軸朝觀察者（畫面上往左下）、y 軸向右、z 軸向上；
       x 方向每 1 單位在畫面上往左 FG_AX、往下 FG_AY 單位，y、z 方向不縮短。
     凸多面體的稜：相鄰兩面都背對觀察者 ⟹ 被遮住，畫虛線；其他線段落在看得見的面上畫實線，否則畫虛線。
     規則：坐標一律由參數算（不目測）；圖上文字用 <text>（不放 KaTeX、不能出現錢字號與反斜線）；
           給驗算器讀的元素帶 data-k（驗算器從圖上的坐標與標籤文字代回，不看 p）。
     立體圖工具（fg*）沿用同冊第一章練習本的同一套。L1 3 型、L2 3 型、L3 2 型（L3-20、L3-21 的類似題）；key 一律接在 META 最後，既有題型同種子輸出不變。
     ══════════════════════════════════════════════════════════ */
  /* <fig3d-tools> */
  var FGC = { ink: '#3a2a2e', line: '#7a2e3c', hot: '#c8324f', soft: '#8a7378', fill: 'rgba(176,58,85,.16)' };
  var FG_AX = 0.5, FG_AY = 0.3, FGM = '−';
  function fgN(v) { var s = (Math.round(v * 100) / 100).toFixed(2); if (s === '-0.00') s = '0.00'; return s.replace(/\.?0+$/, ''); }
  function fgAttr(o) { var s = '', k; for (k in o) { if (o[k] !== undefined && o[k] !== null && o[k] !== false) s += ' ' + k + '="' + o[k] + '"'; } return s; }
  function fgP(P) { return [P[1] - FG_AX * P[0], P[2] - FG_AY * P[0]]; }                      /* 三維點 → 畫面方向（y 向上） */
  function fgSub(u, v) { return [u[0] - v[0], u[1] - v[1], u[2] - v[2]]; }
  function fgDot(u, v) { return u[0] * v[0] + u[1] * v[1] + u[2] * v[2]; }
  function fgCross(u, v) { return [u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2], u[0] * v[1] - u[1] * v[0]]; }
  function fgMix(P, Q, t) { return [P[0] + (Q[0] - P[0]) * t, P[1] + (Q[1] - P[1]) * t, P[2] + (Q[2] - P[2]) * t]; }
  function fgInt(v) { return v < 0 ? FGM + (-v) : String(v); }
  function fgSegD(p, s) {                                                                    /* 畫面上點到線段的距離 */
    var ax = s.a[0], ay = s.a[1], dx = s.b[0] - ax, dy = s.b[1] - ay, L = dx * dx + dy * dy, t = L ? ((p[0] - ax) * dx + (p[1] - ay) * dy) / L : 0;
    t = Math.max(0, Math.min(1, t)); return Math.sqrt(Math.pow(p[0] - ax - t * dx, 2) + Math.pow(p[1] - ay - t * dy, 2));
  }
  /* 場景：o = { pts:{名:[x,y,z]}, faces:[[名…]]（凸多面體的面）, extra:[[x,y,z]…]（算外框用）, W, H, pad:[左,右,上,下], maxU, minW } */
  function fgScene(o) {
    var S = { pts: o.pts || {}, faces: o.faces || [], segs: [], dots: [], names: [], lens: [], under: '', over: '' };
    var W = o.W || 300, Hm = o.H || 196, pad = o.pad || [26, 26, 22, 22], k, all = [], xs = [], ys = [], c3 = [0, 0, 0], n = 0;
    for (k in S.pts) { all.push(S.pts[k]); c3 = [c3[0] + S.pts[k][0], c3[1] + S.pts[k][1], c3[2] + S.pts[k][2]]; n++; }
    c3 = [c3[0] / (n || 1), c3[1] / (n || 1), c3[2] / (n || 1)];
    (o.extra || []).forEach(function (p) { all.push(p); });
    all.forEach(function (p) { var u = fgP(p); xs.push(u[0]); ys.push(u[1]); });
    var x0 = Math.min.apply(null, xs), x1 = Math.max.apply(null, xs), y0 = Math.min.apply(null, ys), y1 = Math.max.apply(null, ys);
    var u = Math.min((W - pad[0] - pad[1]) / (x1 - x0), (Hm - pad[2] - pad[3]) / (y1 - y0), o.maxU || 40);
    S.u = u; S.W = Math.max(o.minW || 150, Math.ceil((x1 - x0) * u + pad[0] + pad[1])); S.H = Math.ceil((y1 - y0) * u + pad[2] + pad[3]);
    var ox = pad[0] + (S.W - pad[0] - pad[1] - (x1 - x0) * u) / 2 - x0 * u, oy = pad[2] + y1 * u;
    S.p3 = function (P) { return typeof P === 'string' ? S.pts[P] : P; };
    S.at = function (P) { var q = fgP(S.p3(P)); return [ox + q[0] * u, oy - q[1] * u]; };
    var cs = S.at(c3);
    var VIEW = [1, FG_AX, FG_AY];
    S.fv = S.faces.map(function (f) {
      var p0 = S.pts[f[0]], nn = fgCross(fgSub(S.pts[f[1]], p0), fgSub(S.pts[f[2]], p0));
      if (fgDot(nn, fgSub(p0, c3)) < 0) nn = [-nn[0], -nn[1], -nn[2]];
      return { n: nn, p0: p0, vis: fgDot(nn, VIEW) > 1e-9, len: Math.sqrt(fgDot(nn, nn)) };
    });
    S.onVis = function (P, Q) {                                                               /* 兩點是否同在某個看得見的面上 */
      P = S.p3(P); Q = S.p3(Q);
      return S.fv.some(function (f) { return f.vis && Math.abs(fgDot(f.n, fgSub(P, f.p0))) < 1e-7 * f.len * 10 + 1e-9 && Math.abs(fgDot(f.n, fgSub(Q, f.p0))) < 1e-7 * f.len * 10 + 1e-9; });
    };
    S.seg = function (P, Q, q) {
      q = q || {}; var a = S.at(P), b = S.at(Q), dash = q.dash !== undefined ? q.dash : (S.faces.length ? !S.onVis(P, Q) : false);
      S.segs.push({ a: a, b: b, svg: '<line' + fgAttr({ 'data-k': q.k || 'seg', x1: fgN(a[0]), y1: fgN(a[1]), x2: fgN(b[0]), y2: fgN(b[1]), stroke: q.c || FGC.line, 'stroke-width': q.w || 1.6, 'stroke-dasharray': dash ? '4 3' : null, 'stroke-linecap': 'round' }) + '/>' });
      return S;
    };
    S.edges = function () {
      var seen = {};
      S.faces.forEach(function (f) { f.forEach(function (nm, i) { var m = f[(i + 1) % f.length], key = nm < m ? nm + '|' + m : m + '|' + nm; if (!seen[key]) { seen[key] = 1; S.seg(nm, m, { k: 'edge', w: 1.7 }); } }); });
      return S;
    };
    S.poly = function (list, q) {                                                             /* 塗色的多邊形（畫在最底層） */
      q = q || {}; S.under += '<polygon' + fgAttr({ 'data-k': q.k || 'shade', points: list.map(function (P) { var a = S.at(P); return fgN(a[0]) + ',' + fgN(a[1]); }).join(' '), fill: q.fill || FGC.fill, stroke: 'none' }) + '/>';
      return S;
    };
    S.dot = function (P, q) { q = q || {}; var a = S.at(P); S.dots.push({ a: a, svg: '<circle' + fgAttr({ 'data-k': q.k || 'pt', cx: fgN(a[0]), cy: fgN(a[1]), r: q.r || 2.7, fill: q.c || FGC.line }) + '/>' }); return S; };
    S.name = function (P, txt, q) { q = q || {}; S.names.push({ a: S.at(P), t: txt === undefined ? P : txt, it: q.it !== false, dir: q.dir, k: q.k || 'nm', fs: q.fs || 15, d: q.d || 12, c: q.c }); return S; };
    S.len = function (P, Q, txt, q) { q = q || {}; S.lens.push({ a: S.at(P), b: S.at(Q), t: String(txt), k: q.k || 'len', fs: q.fs || 14, side: q.side, c: q.c }); return S; };
    S.arrow = function (P, Q, q) {                                                            /* 帶箭頭的線（坐標軸）：Q 端有箭頭 */
      q = q || {}; var a = S.at(P), b = S.at(Q), ang = Math.atan2(b[1] - a[1], b[0] - a[0]), L = 8, wv = 3.2, c = q.c || FGC.ink, bx = b[0] - L * Math.cos(ang), by = b[1] - L * Math.sin(ang);
      S.segs.push({ a: a, b: b, svg: '<line' + fgAttr({ 'data-k': q.k || 'ax', x1: fgN(a[0]), y1: fgN(a[1]), x2: fgN(bx), y2: fgN(by), stroke: c, 'stroke-width': q.w || 1.2, 'stroke-linecap': 'round' }) + '/><path d="M ' + fgN(b[0]) + ' ' + fgN(b[1]) + ' L ' + fgN(bx - wv * Math.sin(ang)) + ' ' + fgN(by + wv * Math.cos(ang)) + ' L ' + fgN(bx + wv * Math.sin(ang)) + ' ' + fgN(by - wv * Math.cos(ang)) + ' Z" fill="' + c + '"/>' });
      return S;
    };
    S.render = function (label) {
      var placed = [], out = '';
      function boxOf(c, t, fs) { return { c: c, hw: Math.max(4.5, String(t).length * fs * 0.29), hh: fs * 0.42 }; }
      function cost(bx, skip, anchor) {
        var pen = 0, samp = [bx.c, [bx.c[0] - Math.max(0, bx.hw - 4), bx.c[1]], [bx.c[0] + Math.max(0, bx.hw - 4), bx.c[1]]];
        S.segs.forEach(function (s) { if (s === skip) return; var d = Math.min(fgSegD(samp[0], s), fgSegD(samp[1], s), fgSegD(samp[2], s)); if (d < 8.5) pen += (8.5 - d) * 3; });
        S.dots.forEach(function (dt) { if (anchor && Math.abs(dt.a[0] - anchor[0]) + Math.abs(dt.a[1] - anchor[1]) < 0.5) return; var d = Math.min.apply(null, samp.map(function (p) { return Math.sqrt(Math.pow(p[0] - dt.a[0], 2) + Math.pow(p[1] - dt.a[1], 2)); })); if (d < 14) pen += (14 - d) * 3; });
        if (anchor) Object.keys(S.pts).forEach(function (k) {                                  /* 點名不要靠近別的頂點（會看成那個頂點的名字） */
          var q = S.at(k); if (Math.abs(q[0] - anchor[0]) + Math.abs(q[1] - anchor[1]) < 0.5) return;
          var d = Math.min.apply(null, samp.map(function (p) { return Math.sqrt(Math.pow(p[0] - q[0], 2) + Math.pow(p[1] - q[1], 2)); })); if (d < 15) pen += (15 - d) * 2.5;
        });
        placed.forEach(function (b) { if (Math.abs(b.c[0] - bx.c[0]) < b.hw + bx.hw + 1.5 && Math.abs(b.c[1] - bx.c[1]) < b.hh + bx.hh + 1) pen += 40; });
        if (bx.c[0] - bx.hw < 2 || bx.c[0] + bx.hw > S.W - 2 || bx.c[1] - bx.hh < 2 || bx.c[1] + bx.hh > S.H - 2) pen += 60;
        return pen;
      }
      function put(c, t, fs, it, k, col) { return '<text' + fgAttr({ 'data-k': k, x: fgN(c[0]), y: fgN(c[1] + fs * 0.35), 'font-size': fs, fill: col || FGC.ink, 'text-anchor': 'middle', 'font-style': it ? 'italic' : null }) + '>' + t + '</text>'; }
      var texts = '';
      S.lens.forEach(function (l) {                                                           /* 長度標籤：線段中點的外側 */
        var m = [(l.a[0] + l.b[0]) / 2, (l.a[1] + l.b[1]) / 2], dx = l.b[0] - l.a[0], dy = l.b[1] - l.a[1], L = Math.sqrt(dx * dx + dy * dy) || 1, nx = -dy / L, ny = dx / L, best = null;
        var me = null; S.segs.forEach(function (s) { if (Math.abs(s.a[0] - l.a[0]) + Math.abs(s.a[1] - l.a[1]) + Math.abs(s.b[0] - l.b[0]) + Math.abs(s.b[1] - l.b[1]) < 0.5) me = s; });
        [1, -1].forEach(function (sd) {
          [11, 14].forEach(function (d) {
            var hw = Math.max(4.5, l.t.length * l.fs * 0.29), dd = d + Math.abs(nx) * Math.max(0, hw - 6), c = [m[0] + sd * nx * dd, m[1] + sd * ny * dd], bx = boxOf(c, l.t, l.fs);
            var out2 = (c[0] - cs[0]) * (m[0] - cs[0]) + (c[1] - cs[1]) * (m[1] - cs[1]) > (m[0] - cs[0]) * (m[0] - cs[0]) + (m[1] - cs[1]) * (m[1] - cs[1]);
            var pen = cost(bx, me) + (out2 ? 0 : 6) + (d - 11) * 0.3 + (l.side !== undefined && l.side !== sd ? 100 : 0);
            if (!best || pen < best.pen) best = { pen: pen, bx: bx };
          });
        });
        placed.push(best.bx); texts += put(best.bx.c, l.t, l.fs, false, l.k, l.c);
      });
      S.names.forEach(function (nm) {                                                         /* 點名：繞一圈找離線段、點、其他標籤最遠的位置，偏好朝外 */
        var best = null, th0 = Math.atan2(-(nm.a[1] - cs[1]), nm.a[0] - cs[0]), i;
        for (i = 0; i < 24; i++) {
          var th = nm.dir !== undefined ? nm.dir * Math.PI / 180 : i * Math.PI / 12, hw = Math.max(4.5, String(nm.t).length * nm.fs * 0.29);
          var d = nm.d + Math.abs(Math.cos(th)) * Math.max(0, hw - 5), c = [nm.a[0] + d * Math.cos(th), nm.a[1] - d * Math.sin(th)], bx = boxOf(c, nm.t, nm.fs);
          var pen = cost(bx, null, nm.a) + (1 - Math.cos(th - th0)) * 2.5;
          if (!best || pen < best.pen - 1e-9) best = { pen: pen, bx: bx };
          if (nm.dir !== undefined) break;
        }
        placed.push(best.bx); texts += put(best.bx.c, nm.t, nm.fs, nm.it, nm.k, nm.c);
      });
      out = S.under + S.segs.map(function (s) { return s.svg; }).join('') + S.dots.map(function (d) { return d.svg; }).join('') + S.over + texts;
      return '<svg class="qfig" viewBox="0 0 ' + S.W + ' ' + S.H + '" width="' + S.W + '" height="' + S.H + '" role="img" aria-label="' + label + '">' + out + '</svg>';
    };
    return S;
  }
  /* 長方體／平行六面體的頂點命名：一圈四個角（前左、前右、後右、後左）從第 st 個起、依 dir 方向繞，
     top=1 時這一圈在頂面；另一圈（第 5～8 個字母）在正對面。回傳 名稱 → 角的 0／1 坐標 [x,y,z]。 */
  var FG_RING = [[1, 0], [1, 1], [0, 1], [0, 0]];
  function fgBoxNames(st, dir, top, names) {
    var m = {}, i, c; names = names || 'ABCDEFGH';
    for (i = 0; i < 4; i++) { c = FG_RING[((st + dir * i) % 4 + 4) % 4]; m[names.charAt(i)] = [c[0], c[1], top ? 1 : 0]; m[names.charAt(i + 4)] = [c[0], c[1], top ? 0 : 1]; }
    return m;
  }
  function fgCorner(nm, i, j, k) { for (var n in nm) if (nm[n][0] === i && nm[n][1] === j && nm[n][2] === k) return n; return null; }
  function fgBoxFaces(nm) {
    var out = [], t, v, ord = [[0, 0], [0, 1], [1, 1], [1, 0]];
    for (t = 0; t < 3; t++) for (v = 0; v < 2; v++) {
      out.push(ord.map(function (c) { var q = [0, 0, 0]; q[t] = v; q[(t + 1) % 3] = c[0]; q[(t + 2) % 3] = c[1]; return fgCorner(nm, q[0], q[1], q[2]); }));
    }
    return out;
  }
  /* 平行六面體（長方體是特例）：角 (i,j,k) 的位置 = i·e1 + j·e2 + k·e3；回傳已畫好 12 條稜的場景 */
  function fgPara(e1, e2, e3, nm, o) {
    var pts = {}, n, c;
    for (n in nm) { c = nm[n]; pts[n] = [c[0] * e1[0] + c[1] * e2[0] + c[2] * e3[0], c[0] * e1[1] + c[1] * e2[1] + c[2] * e3[1], c[0] * e1[2] + c[1] * e2[2] + c[2] * e3[2]]; }
    o = o || {}; o.pts = pts; o.faces = fgBoxFaces(nm);
    return fgScene(o).edges();
  }
  function fgBox(a, b, c, nm, o) { return fgPara([a, 0, 0], [0, b, 0], [0, 0, c], nm, o); }
  /* 在輪廓上標三個稜長：前下（y 方向）、右下（x 方向）、前左直立（z 方向） */
  function fgBoxDims(S, nm, a, b, c) {
    return S.len(fgCorner(nm, 1, 0, 0), fgCorner(nm, 1, 1, 0), b).len(fgCorner(nm, 1, 1, 0), fgCorner(nm, 0, 1, 0), a).len(fgCorner(nm, 1, 0, 0), fgCorner(nm, 1, 0, 1), c);
  }
  /* 圖上的點 P（三維）是否清楚：離不經過它的線段都至少 lim 像素（避免剛好疊在別的稜上） */
  function fgClear(S, P, lim, U, V) {                                                         /* U、V：P 所在線段的兩端（那一條不算） */
    var a = S.at(P), u = S.at(U), v = S.at(V), near = function (p, q) { return Math.abs(p[0] - q[0]) + Math.abs(p[1] - q[1]) < 0.5; };
    return S.segs.every(function (s) { return (near(s.a, u) && near(s.b, v)) || (near(s.a, v) && near(s.b, u)) || fgSegD(a, s) >= lim; });
  }
  /* 長方體的稜長：避開畫出來會有兩條稜（幾乎）重疊的比例 */
  function fgBoxOK(a, b, c) {
    var u = Math.min(230 / (b + FG_AX * a), 140 / (c + FG_AY * a), 40);                       /* 大約的比例尺（像素／單位） */
    return Math.abs(b - FG_AX * a) * u >= 12 && Math.abs(c - FG_AY * a) * u >= 12 && Math.abs(FG_AY * b - FG_AX * c) / Math.sqrt(FG_AX * FG_AX + FG_AY * FG_AY) * u >= 12;
  }
  function fgDims(r, lo, hi) { var d; do { d = [r.int(lo[0], hi[0]), r.int(lo[1], hi[1]), r.int(lo[2], hi[2])]; } while (!fgBoxOK(d[0], d[1], d[2])); return d; }
  function fgNameAll(S, list) { (list || Object.keys(S.pts)).forEach(function (n) { S.name(n); }); return S; }
  /* 示意用的平行六面體形狀（不照比例） */
  var FG_SKEW = [[2.3, 0, 0], [0, 3.6, 0], [0, 1.1, 2.4]];
  /* </fig3d-tools> */

  function fgOpt(i, t) { return '<span class="qopt">(' + i + ') ' + t + '</span>'; }           /* 圖後面的選項：每個選項自成一塊，不從中間斷行 */
  function fgSeg(X, Y) { return '\\overline{' + X + Y + '}'; }
  function fgVecD(nm, X, Y, dims) { return [0, 1, 2].map(function (t) { return (nm[Y][t] - nm[X][t]) * dims[t]; }); }   /* 向量 XY（以角 000 為原點、三稜為軸） */
  function fgNb(nm, X, t) { var q = nm[X].slice(); q[t] = 1 - q[t]; return fgCorner(nm, q[0], q[1], q[2]); }           /* X 沿第 t 個方向的鄰點 */
  function fgLay(r) { return [r.int(0, 3), r.pick([1, -1]), r.int(0, 1)]; }
  var FG_V = 'ABCDEFGH'.split('');

  function fgNice(n, d) { if (n === 0) return true; var g = gcd(n, d); n /= g; d /= g; var s = simpSqrt(n * d); return s.r <= 30 && d / gcd(s.c, d) <= 40; }   /* √(n/d) 化簡後根號內 ≤30、分母 ≤40 */
  function fgMax(v) { return Math.max(Math.abs(v[0]), Math.abs(v[1]), Math.abs(v[2])); }
  function fgLcm(a, b) { a = Math.abs(a); b = Math.abs(b); return a * b / (gcd(a, b) || 1); }
  function fgCo(nm, X, dims) { return [nm[X][0] * dims[0], nm[X][1] * dims[1], nm[X][2] * dims[2]]; }   /* 以角 000 為原點、三稜為軸時 X 的坐標 */
  function fgTri(S, tri, q) {                                    /* 塗色的三角形（截面）與它的三邊 */
    q = q || {}; S.poly(tri);
    [[0, 1], [1, 2], [2, 0]].forEach(function (e) { S.seg(tri[e[0]], tri[e[1]], { k: 'tri', c: q.c || FGC.hot, w: q.w || 2 }); });
    return S;
  }
  function fgTriOK(S, tri, lim) {                                 /* 畫出來的三角形不能太扁（截面幾乎側對著觀察者時看不出是哪個面）：最短的高至少 lim 像素 */
    var a = S.at(tri[0]), b = S.at(tri[1]), c = S.at(tri[2]), ar = Math.abs((b[0] - a[0]) * (c[1] - a[1]) - (c[0] - a[0]) * (b[1] - a[1]));
    var L = Math.max(Math.pow(b[0] - a[0], 2) + Math.pow(b[1] - a[1], 2), Math.pow(c[0] - b[0], 2) + Math.pow(c[1] - b[1], 2), Math.pow(a[0] - c[0], 2) + Math.pow(a[1] - c[1], 2));
    return ar / Math.sqrt(L) >= (lim || 18);
  }
  function fgFar(S, P, Q, lim) { var a = S.at(P), b = S.at(Q); return Math.sqrt(Math.pow(a[0] - b[0], 2) + Math.pow(a[1] - b[1], 2)) >= lim; }   /* 圖上兩點至少相距 lim 像素（標籤才不會擠在一起） */
  function fgPtList(names, co) { return names.map(function (X, i) { return T(X + vt(co[i])); }).join('、'); }
  /* 坐標系中的長方體 OABC-DEFG：O 在原點、三稜在坐標軸正向；sw=1 時 A 在 y 軸上、C 在 x 軸上 */
  function fgAxNames(sw) { return sw ? { O: [0, 0, 0], A: [0, 1, 0], B: [1, 1, 0], C: [1, 0, 0], D: [0, 0, 1], E: [0, 1, 1], F: [1, 1, 1], G: [1, 0, 1] } : { O: [0, 0, 0], A: [1, 0, 0], B: [1, 1, 0], C: [0, 1, 0], D: [0, 0, 1], E: [1, 0, 1], F: [1, 1, 1], G: [0, 1, 1] }; }
  function fgAxBox(a, b, c, nm, o) {                              /* 軸從稜的端點畫出去 */
    o = o || {}; o.extra = [[a + 1.5, 0, 0], [0, b + 1.3, 0], [0, 0, c + 1.2]]; o.pad = o.pad || [26, 26, 22, 22];
    var S = fgBox(a, b, c, nm, o);
    S.arrow([a, 0, 0], [a + 1.5, 0, 0], { k: 'ax' }).arrow([0, b, 0], [0, b + 1.3, 0], { k: 'ax' }).arrow([0, 0, c], [0, 0, c + 1.2], { k: 'ax' });
    S.name([a + 1.5, 0, 0], 'x', { k: 'axn', d: 10 }).name([0, b + 1.3, 0], 'y', { k: 'axn', d: 10 }).name([0, 0, c + 1.2], 'z', { k: 'axn', d: 10 });
    return S;
  }
  var FG_AXV = 'OABCDEFG'.split('');
  function fgAxSort(list) { return list.slice().sort(function (x, y) { return FG_AXV.indexOf(x) - FG_AXV.indexOf(y); }); }
  function fgAxRead(sw, dims) {                                   /* 步驟第一句：從圖上讀稜長 */
    var xa = sw ? 'C' : 'A', ya = sw ? 'A' : 'C';
    return '從圖上讀出：' + T(xa) + ' 在 ' + T('x') + ' 軸上、' + T('\\overline{O' + xa + '}=' + dims[0]) + '；' + T(ya) + ' 在 ' + T('y') + ' 軸上、' + T('\\overline{O' + ya + '}=' + dims[1]) + '；' + T('D') + ' 在 ' + T('z') + ' 軸上、' + T('\\overline{OD}=' + dims[2]) + '（對面的稜一樣長）。';
  }

  /* ────────── L1　6 讀圖題：軸上三個交點決定的平面、坐標系中的長方體（三頂點的平面、兩點的直線） ────────── */
  /* 平面與三個坐標軸的交點畫在圖上：讀出三點，寫平面方程式、求原點到平面的距離 */
  function fgAxisScene(I) {
    var O = [0, 0, 0], Pt = [[I[0], 0, 0], [0, I[1], 0], [0, 0, I[2]]], ends = [], t, lo, hi;
    for (t = 0; t < 3; t++) { lo = [0, 0, 0]; hi = [0, 0, 0]; lo[t] = I[t] < 0 ? I[t] - 0.9 : 0; hi[t] = Math.max(1.6, I[t] + 1.5); ends.push([lo, hi]); }
    var S = fgScene({ pts: { O: O }, extra: Pt.concat(ends.map(function (e) { return e[0]; }), ends.map(function (e) { return e[1]; })), pad: [24, 24, 22, 22], maxU: 30, W: 300, H: 220 });
    S.poly(Pt);
    ends.forEach(function (e, i) { S.arrow(e[0], e[1], { k: 'ax' }).name(e[1], AXES[i], { k: 'axn', d: 10 }); });
    [[0, 1], [1, 2], [2, 0]].forEach(function (e) { S.seg(Pt[e[0]], Pt[e[1]], { k: 'tri', c: FGC.hot, w: 2, dash: false }); });
    Pt.forEach(function (P, i) { S.dot(P, { k: 'ft', c: FGC.hot, r: 2.8 }); });
    Pt.forEach(function (P, i) { S.name(P, fgInt(I[i]), { it: false, k: 'tk' }); });
    Pt.forEach(function (P, i) { S.name(P, 'ABC'.charAt(i)); });
    S.name(O, 'O', { k: 'nmO' });
    S.tri3 = Pt; return S;
  }
  L1.figAxisPlane = function (r) {
    r();
    var I, pl, N, S, guard = 0, j;
    do {
      I = [r.int(2, 6), r.int(2, 6), r.int(2, 6)];
      if (r() < 0.35) { j = r.int(1, 2); I[j] = -I[j]; }                           /* 負的只放 y 或 z（x 軸負向在圖的後方，三角形會和坐標軸疊在一起） */
      pl = normPlane([I[1] * I[2], I[0] * I[2], I[0] * I[1], I[0] * I[1] * I[2]]); N = pl[0] * pl[0] + pl[1] * pl[1] + pl[2] * pl[2]; guard++;
      S = fgAxisScene(I);
    } while ((fgMax(pl) > 12 || !fgNice(pl[3] * pl[3], N) || !fgTriOK(S, S.tri3, 16)) && guard < 400);
    var neg = I[0] < 0 || I[1] < 0 || I[2] < 0;
    return { q: '如圖，平面 ' + T('E') + ' 與 ' + T('x') + ' 軸、' + T('y') + ' 軸、' + T('z') + ' 軸分別交於 ' + T('A') + '、' + T('B') + '、' + T('C') + ' 三點，軸上標的數字是交點在該軸上的坐標。(1) 求 ' + T('E') + ' 的方程式（化為最簡整數係數）。(2) 求原點 ' + T('O') + ' 到 ' + T('E') + ' 的距離。' + S.render('坐標空間中，平面與三個坐標軸交於 A、B、C 三點，軸上標出交點的坐標'),
      a: '(1) ' + T('E:' + planeTex(pl)) + '　(2) ' + T(sqrtFracTex(pl[3] * pl[3], N)),
      h: '從圖上讀出 ' + T('A' + vt([I[0], 0, 0])) + '、' + T('B' + vt([0, I[1], 0])) + '、' + T('C' + vt([0, 0, I[2]])) + (neg ? '（交點在軸的負向那一側，坐標是負的）' : '') + '。設 ' + T('E:ax+by+cz=d') + '，三點各代一次：' + T(term(I[0], 'a', true) + '=d') + '、' + T(term(I[1], 'b', true) + '=d') + '、' + T(term(I[2], 'c', true) + '=d') + '；取 ' + T('d=' + fgLcm(fgLcm(I[0], I[1]), I[2])) + ' 就能把 ' + T('a,b,c') + ' 都解成整數。(2) 原點代入左式是 ' + T('0') + '，距離 ' + T('=\\dfrac{|0-d|}{\\sqrt{a^2+b^2+c^2}}') + '。',
      p: { I: I } };
  };

  /* 坐標系中的長方體：讀三個頂點的坐標，求它們決定的平面 */
  L1.figBoxPlane = function (r) {
    r();
    var sw = r.int(0, 1), nm = fgAxNames(sw), dims, tri, co, n, nr, S, guard = 0;
    do {
      dims = fgDims(r, [2, 3, 2], [6, 6, 6]); tri = fgAxSort(r.shuffle(FG_AXV).slice(0, 3));
      co = tri.map(function (X) { return fgCo(nm, X, dims); });
      n = cross(sub(co[1], co[0]), sub(co[2], co[0])); nr = redPos(n); guard++;
      S = fgAxBox(dims[0], dims[1], dims[2], nm);
    } while ((nzc(n) < 2 || fgMax(nr) > 12 || !fgTriOK(S, tri)) && guard < 400);
    var pl = planeOf(nr, co[0]), pn = tri.join('');
    fgBoxDims(S, nm, dims[0], dims[1], dims[2]); fgTri(S, tri); fgNameAll(S);
    return { q: '如圖，長方體 ' + T('OABC') + '-' + T('DEFG') + ' 的頂點 ' + T('O') + ' 在原點，三條稜分別在三個坐標軸的正向上，稜長標示在圖上。(1) 寫出 ' + T(tri[0]) + '、' + T(tri[1]) + '、' + T(tri[2]) + ' 的坐標。(2) 求平面 ' + T(pn) + '（塗色的三角形所在的平面）的方程式（化為最簡整數係數）。' + S.render('坐標空間中的長方體 OABC-DEFG，O 在原點，稜長標示在圖上，三個頂點連成的三角形塗色'),
      a: '(1) ' + fgPtList(tri, co) + '　(2) ' + T(planeTex(pl)),
      h: '先看每個頂點在哪個位置：在哪一條軸上、或是在哪個頂點的正上方，從 ' + T('O') + ' 沿三個軸各走多少就是坐標。再做兩個邊向量 ' + T(ov(tri[0] + tri[1]) + '=' + vt(sub(co[1], co[0]))) + '、' + T(ov(tri[0] + tri[2]) + '=' + vt(sub(co[2], co[0]))) + '，法向量取外積 ' + T(vt(n)) + '（化成首項為正的最簡整數 ' + T(vt(nr)) + '），最後代 ' + T(tri[0]) + ' 定常數。',
      p: { a: dims[0], b: dims[1], c: dims[2], sw: sw, tri: tri } };
  };

  /* 坐標系中的長方體：讀圖上兩點（頂點或稜的中點）的坐標，寫直線的參數式 */
  L1.figBoxLine = function (r) {
    r();
    var sw = r.int(0, 1), nm = fgAxNames(sw), dims, P, Q, U, V, mid, S, d2v, M3, guard = 0, ok, e;
    do {
      dims = fgDims(r, [2, 3, 2], [6, 6, 6]); mid = r() < 0.45; P = r.pick(FG_AXV); U = V = null; guard++;
      S = fgAxBox(dims[0], dims[1], dims[2], nm);
      if (mid) {
        U = r.pick(FG_AXV); V = fgNb(nm, U, r.int(0, 2)); e = fgAxSort([U, V]); U = e[0]; V = e[1]; Q = 'M';
        d2v = [0, 1, 2].map(function (s) { return (nm[U][s] + nm[V][s] - 2 * nm[P][s]) * dims[s]; });   /* 2×(M−P) */
        M3 = fgMix(S.pts[U], S.pts[V], 0.5);
        ok = U !== P && V !== P && nzc(d2v) >= 2 && fgClear(S, M3, 7, U, V);
      } else {
        Q = r.pick(FG_AXV); e = fgAxSort([P, Q]); P = e[0]; Q = e[1];
        d2v = [0, 1, 2].map(function (s) { return 2 * (nm[Q][s] - nm[P][s]) * dims[s]; }); ok = nzc(d2v) >= 2;
      }
    } while (!ok && guard < 400);
    var Pc = fgCo(nm, P, dims), d = red(d2v), Qf = mid ? [0, 1, 2].map(function (s) { return F((nm[U][s] + nm[V][s]) * dims[s], 2); }) : fgCo(nm, Q, dims).map(function (x) { return F(x); });
    var QT = Qf.every(function (f) { return f.d === 1; }) ? vt(Qf.map(function (f) { return f.n; })) : vtF(Qf);
    fgBoxDims(S, nm, dims[0], dims[1], dims[2]);
    S.seg(P, mid ? M3 : Q, { k: 'hot', c: FGC.hot, w: 2.4 });
    fgNameAll(S);
    if (mid) S.dot(M3, { k: 'pM', c: FGC.hot }).name(M3, 'M');
    return { q: '如圖，長方體 ' + T('OABC') + '-' + T('DEFG') + ' 的頂點 ' + T('O') + ' 在原點，三條稜分別在三個坐標軸的正向上，稜長標示在圖上' + (mid ? '，' + T('M') + ' 是 ' + T(fgSeg(U, V)) + ' 的中點' : '') + '。(1) 寫出 ' + T(P) + '、' + T(Q) + ' 的坐標。(2) 求直線 ' + T(P + Q) + '（粗線）的參數式。' + S.render('坐標空間中的長方體 OABC-DEFG，O 在原點，稜長標示在圖上，一條直線用粗線標出' + (mid ? '，M 是一條稜的中點' : '')),
      a: '(1) ' + T(P + vt(Pc)) + '、' + T(Q + QT) + '　(2) ' + T(paramTex(Pc, d, 't')),
      h: '先從圖上讀出兩個點的坐標（從 ' + T('O') + ' 沿三個軸各走多少' + (mid ? '；中點是兩個端點坐標的平均' : '') + '）。方向向量用終點減起點：' + T(ov(P + Q) + '=' + QT + '-' + vt(Pc)) + '，可以乘或除一個數化成最簡整數 ' + T(vt(d)) + '（同一條直線）。參數式寫成「起點的坐標＋' + T('t') + '×方向向量」，起點用 ' + T(P) + ' 或 ' + T(Q) + ' 都可以。',
      p: { a: dims[0], b: dims[1], c: dims[2], sw: sw, P: P, Q: Q, U: U, V: V } };
  };

  L1_H1.figAxisPlane = '這是「看圖寫出平面方程式」：平面與坐標軸的交點，有兩個坐標是 $0$；把三個交點從圖上讀出來，代進 $ax+by+cz=d$ 就能定出係數。';
  L1_H1.figBoxPlane = '這是「坐標系中的長方體：三個頂點的平面」：頂點的坐標由「沿三個軸各走多少」決定，圖上的稜長就是要走的距離；三點決定平面，法向量取兩個邊向量的外積。';
  L1_H1.figBoxLine = '這是「坐標系中的長方體：兩點的直線」：先從圖上讀出兩個點的坐標，方向向量用終點減起點，再寫成「起點＋$t$×方向向量」。';
  L1_SOL.figAxisPlane = function (p, o) {
    var I = p.I, L = fgLcm(fgLcm(I[0], I[1]), I[2]), co = [L / I[0], L / I[1], L / I[2]], pl = normPlane([co[0], co[1], co[2], L]), N = pl[0] * pl[0] + pl[1] * pl[1] + pl[2] * pl[2];
    var neg = I[0] < 0 || I[1] < 0 || I[2] < 0;
    return ['從圖上讀出三個交點：' + T('A' + vt([I[0], 0, 0])) + '、' + T('B' + vt([0, I[1], 0])) + '、' + T('C' + vt([0, 0, I[2]])) + '（在哪一條軸上，就只有那個坐標不是 ' + T('0') + (neg ? '；交點在軸的負向那一側，坐標是負的' : '') + '）。',
      '(1) 設 ' + T('E:ax+by+cz=d') + '。代 ' + T('A') + ' 得 ' + T(term(I[0], 'a', true) + '=d') + '，代 ' + T('B') + ' 得 ' + T(term(I[1], 'b', true) + '=d') + '，代 ' + T('C') + ' 得 ' + T(term(I[2], 'c', true) + '=d') + '。',
      '取 ' + T('d=' + L) + '（三個坐標的最小公倍數）：' + T('a=' + co[0]) + '、' + T('b=' + co[1]) + '、' + T('c=' + co[2]) + '，得 ' + (co[0] < 0 ? T(lhsTex(co[0], co[1], co[2]) + '=' + L) + '；兩邊同乘 ' + T('-1') + ' 讓首項為正，' : '') + T('E:' + planeTex(pl)) + '。',
      '(2) 原點代入左式得 ' + T('0') + '，距離 ' + T('=' + solDistT('0-' + solNeg(pl[3]), N) + '=' + sqrtFracTex(pl[3] * pl[3], N)) + '。' + solFin(o)];
  };
  L1_SOL.figBoxPlane = function (p, o) {
    var nm = fgAxNames(p.sw), dims = [p.a, p.b, p.c], tri = p.tri, co = tri.map(function (X) { return fgCo(nm, X, dims); });
    var u = sub(co[1], co[0]), v = sub(co[2], co[0]), n = cross(u, v), nr = redPos(n), pl = planeOf(nr, co[0]), same = n[0] === nr[0] && n[1] === nr[1] && n[2] === nr[2];
    return [fgAxRead(p.sw, dims),
      '(1) 從 ' + T('O') + ' 走到各個頂點，沿三個軸各走的距離就是坐標：' + fgPtList(tri, co) + '。',
      '(2) 兩個邊向量 ' + T(ov(tri[0] + tri[1]) + '=' + vt(u)) + '、' + T(ov(tri[0] + tri[2]) + '=' + vt(v)) + '，法向量取外積：' + T(ov(tri[0] + tri[1]) + '\\times' + ov(tri[0] + tri[2]) + '=' + vt(n)) + (same ? '。' : '，化成最簡整數、首項為正得 ' + T(vec('n') + '=' + vt(nr)) + '。'),
      '把 ' + T(tri[0] + vt(co[0])) + ' 代入 ' + T(lhsTex(nr[0], nr[1], nr[2]) + '=d') + '：' + T(subTex(nr, co[0]) + '=' + pl[3]) + '，所以平面 ' + T(tri.join('') + ':' + planeTex(pl)) + '。' + solFin(o)];
  };
  L1_SOL.figBoxLine = function (p, o) {
    var nm = fgAxNames(p.sw), dims = [p.a, p.b, p.c], P = p.P, Q = p.Q, mid = Q === 'M', Pc = fgCo(nm, P, dims);
    var Qf = mid ? [0, 1, 2].map(function (s) { return F((nm[p.U][s] + nm[p.V][s]) * dims[s], 2); }) : fgCo(nm, Q, dims).map(function (x) { return F(x); });
    var isInt = function (v) { return v.every(function (f) { return f.d === 1; }); }, tx = function (v) { return isInt(v) ? vt(v.map(function (f) { return f.n; })) : vtF(v); };
    var dv = Qf.map(function (f, i) { return Fr.sub(f, F(Pc[i])); }), d = red(dv.map(function (f) { return f.n * 2 / f.d; })), same = isInt(dv) && dv.every(function (f, i) { return f.n === d[i]; });
    return [fgAxRead(p.sw, dims),
      '(1) 從 ' + T('O') + ' 走到各點，沿三個軸各走的距離就是坐標：' + T(P + vt(Pc)) + (mid ? '；' + T(p.U + vt(fgCo(nm, p.U, dims))) + '、' + T(p.V + vt(fgCo(nm, p.V, dims))) + ' 的中點是 ' + T('M' + tx(Qf)) : '、' + T(Q + tx(Qf))) + '。',
      '(2) 方向向量用終點減起點：' + T(ov(P + Q) + '=' + tx(dv)) + (same ? '（三個分量已經是沒有公因數的整數）。' : '，乘或除一個數化成最簡整數，取 ' + T(vec('d') + '=' + vt(d)) + '（同一條直線）。'),
      '以 ' + T(P) + ' 為起點：' + T(paramTex(Pc, d, 't')) + '（' + T('t') + ' 為實數）。' + solFin(o)];
  };
  META_L1.push(['figAxisPlane', '§6 看圖寫平面方程式：與三軸的交點'], ['figBoxPlane', '§6 坐標系中的長方體：三頂點的平面'], ['figBoxLine', '§6 坐標系中的長方體：兩點的直線']);

  /* ────────── L2　讀圖題：長方體上（頂點怎麼排只畫在圖上）稜上的點到截面的距離、截面與一個面的夾角、直線與截面的夾角 ────────── */
  /* 提示的開頭：照圖放坐標。以角 000（左後下方的頂點）為原點，三條稜依序是 x、y、z 軸 */
  function fgFrameH(nm, dims, cube) {
    var O0 = fgCorner(nm, 0, 0, 0), N = [0, 1, 2].map(function (s) { return fgNb(nm, O0, s); });
    return '照圖放坐標：以 ' + T(O0) + ' 為原點，' + T(ov(O0 + N[0])) + '、' + T(ov(O0 + N[1])) + '、' + T(ov(O0 + N[2])) + ' 的方向為 ' + T('x') + '、' + T('y') + '、' + T('z') + ' 軸的正向'
      + (cube ? '' : '（從圖上讀出 ' + T(fgSeg(O0, N[0]) + '=' + dims[0]) + '、' + T(fgSeg(O0, N[1]) + '=' + dims[1]) + '、' + T(fgSeg(O0, N[2]) + '=' + dims[2]) + '，對面的稜一樣長）');
  }
  function fgPlaneH(tri, co, n, nr, pl) {                         /* 提示的中段：三點的平面 */
    var same = n[0] === nr[0] && n[1] === nr[1] && n[2] === nr[2];
    return '法向量取 ' + T(ov(tri[0] + tri[1]) + '\\times' + ov(tri[0] + tri[2]) + '=' + vt(sub(co[1], co[0])) + '\\times' + vt(sub(co[2], co[0])) + '=' + vt(n)) + (same ? '' : '，化成首項為正的最簡整數 ' + T(vt(nr))) + '，平面 ' + T(tri.join('') + ':' + planeTex(pl));
  }
  function fgFaceName(nm, t, v) {                                 /* 第 t 個坐標等於 v 的那個面：四個頂點依序一圈，從字母最小的開始 */
    var f = fgBoxFaces(nm)[2 * t + v], i = f.indexOf(f.slice().sort()[0]), g = [f[i], f[(i + 1) % 4], f[(i + 2) % 4], f[(i + 3) % 4]];
    return g[1] < g[3] ? g.join('') : [g[0], g[3], g[2], g[1]].join('');
  }
  function fgTriPick(r) { return r.shuffle(FG_V).slice(0, 3).sort(); }

  /* 稜上的一點到截面（三個頂點的平面）的距離 */
  L2.figBoxPtPlane = function (r) {
    r();
    var lay = fgLay(r), nm = fgBoxNames(lay[0], lay[1], lay[2]), dims, tri, co, n, nr, U, V, t, k, Pc, num, N, S, P3, ok, guard = 0;
    do {
      dims = fgDims(r, [3, 2, 2], [8, 8, 8]); tri = fgTriPick(r);
      co = tri.map(function (X) { return fgCo(nm, X, dims); }); n = cross(sub(co[1], co[0]), sub(co[2], co[0])); nr = redPos(n);
      U = r.pick(FG_V); t = r.int(0, 2); V = fgNb(nm, U, t); k = r.int(1, dims[t] - 1);
      Pc = fgCo(nm, U, dims); Pc[t] += (nm[V][t] - nm[U][t]) * k;
      num = Math.abs(dot(nr, sub(Pc, co[0]))); N = n2(nr); guard++;
      ok = nzc(n) >= 2 && fgMax(nr) <= 24 && num !== 0 && fgNice(num * num, N);
      if (ok) { S = fgBox(dims[0], dims[1], dims[2], nm); fgTri(S, tri); P3 = fgMix(S.pts[U], S.pts[V], k / dims[t]); ok = fgTriOK(S, tri) && fgClear(S, P3, 7, U, V) && fgFar(S, P3, U, 20) && fgFar(S, P3, V, 20); }
    } while (!ok && guard < 800);
    var pl = planeOf(nr, co[0]), pn = tri.join('');
    fgBoxDims(S, nm, dims[0], dims[1], dims[2]); fgNameAll(S);
    S.dot(P3, { k: 'pP', c: FGC.hot }).name(P3, 'P');
    return { q: '如圖，長方體的三個稜長標示在圖上，' + T('P') + ' 點在稜 ' + T(fgSeg(U, V)) + ' 上（位置如圖），' + T(fgSeg(U, 'P') + '=' + k) + '。求 ' + T('P') + ' 到平面 ' + T(pn) + '（塗色的三角形所在的平面）的距離。' + S.render('長方體，三個稜長標示在圖上，三個頂點連成的三角形塗色，P 點在一條稜上'),
      a: T(sqrtFracTex(num * num, N)),
      h: fgFrameH(nm, dims) + '：' + fgPtList(tri, co) + '；' + T('P') + ' 在 ' + T(fgSeg(U, V)) + ' 上、離 ' + T(U) + ' 是 ' + T(k) + '，所以 ' + T('P' + vt(Pc)) + '。' + fgPlaneH(tri, co, n, nr, pl) + '。' + T('P') + ' 到平面的距離 ' + T('=\\dfrac{\\left|' + subTex(nr, Pc) + '-' + solNeg(pl[3]) + '\\right|}{\\sqrt{' + N + '}}') + '，再化簡。',
      p: { a: dims[0], b: dims[1], c: dims[2], lay: lay, tri: tri, U: U, V: V, k: k } };
  };

  /* 截面與長方體的一個面的夾角 */
  L2.figBoxDihedral = function (r) {
    r();
    var lay = fgLay(r), nm = fgBoxNames(lay[0], lay[1], lay[2]), dims, tri, co, n, nr, t, v, N, S, ok, guard = 0;
    do {
      dims = fgDims(r, [3, 2, 2], [8, 8, 8]); tri = fgTriPick(r);
      co = tri.map(function (X) { return fgCo(nm, X, dims); }); n = cross(sub(co[1], co[0]), sub(co[2], co[0])); nr = redPos(n);
      t = r.int(0, 2); v = r.int(0, 1); N = n2(nr); guard++;
      ok = nzc(n) >= 2 && fgMax(nr) <= 24 && nr[t] !== 0 && fgNice(nr[t] * nr[t], N);
      if (ok) { S = fgBox(dims[0], dims[1], dims[2], nm); ok = fgTriOK(S, tri); }
    } while (!ok && guard < 800);
    var pl = planeOf(nr, co[0]), pn = tri.join(''), fn = fgFaceName(nm, t, v), e = [0, 0, 0]; e[t] = 1;
    fgTri(S, tri); fgBoxDims(S, nm, dims[0], dims[1], dims[2]); fgNameAll(S);
    return { q: '如圖，長方體的三個稜長標示在圖上。求平面 ' + T(pn) + '（塗色的三角形所在的平面）與平面 ' + T(fn) + ' 的夾角 ' + T('\\theta') + ' 的餘弦值（取銳角）。' + S.render('長方體，三個稜長標示在圖上，三個頂點連成的三角形塗色'),
      a: T('\\cos\\theta=' + sqrtFracTex(nr[t] * nr[t], N)),
      h: fgFrameH(nm, dims) + '：' + fgPtList(tri, co) + '。' + fgPlaneH(tri, co, n, nr, pl) + '。平面 ' + T(fn) + ' 上每一點的 ' + T(AXES[t]) + ' 坐標都相同，它的法向量取 ' + T(vt(e)) + '。兩平面的夾角看兩個法向量：' + T('\\cos\\theta=\\dfrac{\\left|' + vec('n_1') + '\\cdot' + vec('n_2') + '\\right|}{\\left|' + vec('n_1') + '\\right|\\left|' + vec('n_2') + '\\right|}=\\dfrac{' + Math.abs(nr[t]) + '}{\\sqrt{' + N + '}}') + '，再化簡。',
      p: { a: dims[0], b: dims[1], c: dims[2], lay: lay, tri: tri, t: t, v: v } };
  };

  /* 直線（兩個頂點的連線）與截面的夾角 */
  L2.figBoxLinePlane = function (r) {
    r();
    var lay = fgLay(r), nm = fgBoxNames(lay[0], lay[1], lay[2]), dims, tri, co, n, nr, P, Q, d, dv, N, e, S, ok, guard = 0;
    do {
      dims = fgDims(r, [3, 2, 2], [8, 8, 8]); tri = fgTriPick(r);
      co = tri.map(function (X) { return fgCo(nm, X, dims); }); n = cross(sub(co[1], co[0]), sub(co[2], co[0])); nr = redPos(n);
      e = [r.pick(FG_V), r.pick(FG_V)].sort(); P = e[0]; Q = e[1];
      d = sub(fgCo(nm, Q, dims), fgCo(nm, P, dims)); dv = dot(d, nr); N = n2(nr); guard++;
      ok = nzc(n) >= 2 && fgMax(nr) <= 24 && nzc(d) >= 2 && dv !== 0 && fgNice(dv * dv, n2(d) * N);
      if (ok) { S = fgBox(dims[0], dims[1], dims[2], nm); ok = fgTriOK(S, tri); }
    } while (!ok && guard < 800);
    var pl = planeOf(nr, co[0]), pn = tri.join(''), ex = [P, Q].filter(function (X) { return tri.indexOf(X) < 0; });
    fgTri(S, tri, { c: FGC.line, w: 1.5 }); S.seg(P, Q, { k: 'hot', c: FGC.hot, w: 2.6 });
    fgBoxDims(S, nm, dims[0], dims[1], dims[2]); fgNameAll(S);
    return { q: '如圖，長方體的三個稜長標示在圖上。求直線 ' + T(P + Q) + '（粗線）與平面 ' + T(pn) + '（塗色的三角形所在的平面）的夾角 ' + T('\\theta') + ' 的正弦值。' + S.render('長方體，三個稜長標示在圖上，三個頂點連成的三角形塗色，另有一條頂點連線用粗線標出'),
      a: T('\\sin\\theta=' + sqrtFracTex(dv * dv, n2(d) * N)),
      h: fgFrameH(nm, dims) + '：' + fgPtList(tri.concat(ex), tri.concat(ex).map(function (X) { return fgCo(nm, X, dims); })) + '。' + fgPlaneH(tri, co, n, nr, pl) + '。直線的方向 ' + T(ov(P + Q) + '=' + vt(d)) + '。線與面的夾角用正弦：' + T('\\sin\\theta=\\dfrac{\\left|' + vec('d') + '\\cdot' + vec('n') + '\\right|}{\\left|' + vec('d') + '\\right|\\left|' + vec('n') + '\\right|}=\\dfrac{' + Math.abs(dv) + '}{\\sqrt{' + n2(d) + '}\\sqrt{' + N + '}}') + '，再化簡。',
      p: { a: dims[0], b: dims[1], c: dims[2], lay: lay, tri: tri, P: P, Q: Q } };
  };
  META_L2.push(['figBoxPtPlane', '§6 看圖求稜上的點到截面的距離'], ['figBoxDihedral', '§6 看圖求截面與一個面的夾角'], ['figBoxLinePlane', '§6 看圖求直線與截面的夾角']);

  /* ────────── L3　附圖固定題 L3-20、L3-21 的類似題 ────────── */
  /* ══ L3-20　正立方體的頂點到截面的距離：頂點怎麼排要看圖，照圖放坐標再用公式 ══ */
  L3.figCubeDist = function (r) {
    r();
    var lay = fgLay(r), nm = fgBoxNames(lay[0], lay[1], lay[2]), e = r.pick([1, 2, 3, 4, 6]), dims = [e, e, e], tri, W, co, n, nr, num, N, S, ok, guard = 0;
    do {
      tri = fgTriPick(r); W = r.pick(FG_V.filter(function (X) { return tri.indexOf(X) < 0; }));
      co = tri.map(function (X) { return fgCo(nm, X, dims); }); n = cross(sub(co[1], co[0]), sub(co[2], co[0])); nr = redPos(n);
      num = Math.abs(dot(nr, sub(fgCo(nm, W, dims), co[0]))); N = n2(nr); guard++;
      ok = nzc(n) >= 2 && num !== 0;
      if (ok) { S = fgBox(3, 3, 3, nm); ok = fgTriOK(S, tri); }
    } while (!ok && guard < 400);
    var pl = planeOf(nr, co[0]), pn = tri.join(''), Wc = fgCo(nm, W, dims);
    fgTri(S, tri); fgNameAll(S); S.dot(W, { k: 'pW', c: FGC.hot, r: 3.2 });
    return { q: '如圖，' + T('ABCDEFGH') + ' 為稜長 ' + T(e) + ' 的正立方體。求點 ' + T(W) + ' 到平面 ' + T(pn) + '（塗色的三角形所在的平面）的距離。' + S.render('正立方體，三個頂點連成的三角形塗色，另有一個頂點用圓點標出'),
      a: T(sqrtFracTex(num * num, N)),
      h: fgFrameH(nm, dims, true) + '，稜長 ' + T(e) + '：' + fgPtList(tri.concat([W]), co.concat([Wc])) + '。' + fgPlaneH(tri, co, n, nr, pl) + '。' + T(W) + ' 到平面的距離 ' + T('=\\dfrac{\\left|' + subTex(nr, Wc) + '-' + solNeg(pl[3]) + '\\right|}{\\sqrt{' + N + '}}') + '，再化簡。',
      p: { e: e, lay: lay, tri: tri, W: W } };
  };

  /* ══ L3-21　長方體的截面上一點：把三條稜的係數當坐標，截面上的點滿足一個一次式 ══ */
  var FG_FR = [[1, 2], [1, 3], [2, 3], [1, 4], [3, 4], [1, 6], [5, 6], [2, 5], [3, 5], [1, 5], [4, 5]];
  L3.figBoxCoplanar = function (r) {
    r();
    var lay = fgLay(r), nm = fgBoxNames(lay[0], lay[1], lay[2]), dims = fgDims(r, [3, 3, 2], [5, 6, 4]), V, nb, perm, tri, pts, n, nr, pl, u, cs, a, S, ok, guard = 0, i, rest;
    do {
      V = r.pick(FG_V); tri = fgTriPick(r); u = r.int(0, 2); guard++;
      nb = [0, 1, 2].map(function (s) { return fgNb(nm, V, s); });
      perm = [0, 1, 2].sort(function (x, y) { return nb[x] < nb[y] ? -1 : 1; });               /* 三條稜依另一端的字母排，係數就照這個順序當坐標 */
      pts = tri.map(function (X) { return perm.map(function (s) { return Math.abs(nm[X][s] - nm[V][s]); }); });
      n = cross(sub(pts[1], pts[0]), sub(pts[2], pts[0])); nr = redPos(n); pl = planeOf(nr, pts[0]);
      cs = [0, 1, 2].map(function () { var f = r.pick(FG_FR); return F(f[0], f[1]); });
      ok = nzc(n) >= 2 && pl[u] !== 0 && !Fr.eq(cs[(u + 1) % 3], cs[(u + 2) % 3]);
      if (ok) {
        rest = F(pl[3]);
        for (i = 0; i < 3; i++) if (i !== u) rest = Fr.sub(rest, Fr.mul(F(pl[i]), cs[i]));
        S = fgBox(dims[0], dims[1], dims[2], nm);
        a = Fr.div(rest, F(pl[u])); ok = fgTriOK(S, tri) && a.n !== 0 && a.d <= 12 && Math.abs(a.n) <= 2 * a.d && !(a.d === 1 && Math.abs(a.n) === 1 && nzc(nr) < 3);
      }
    } while (!ok && guard < 800);
    var names = perm.map(function (s) { return nb[s]; }), pn = tri.join('');
    var coefT = function (k) { return k === u ? 'a' : Fr.tex(cs[k]); }, sum = '', lhs = '';
    for (i = 0; i < 3; i++) sum += (i ? '+' : '') + coefT(i) + ov(V + names[i]);
    for (i = 0; i < 3; i++) {
      if (pl[i] === 0) continue;
      if (i === u) lhs += term(pl[i], 'a', lhs === '');
      else { var f = Fr.mul(F(pl[i]), cs[i]); lhs += (f.n < 0 ? '-' : (lhs === '' ? '' : '+')) + Fr.tex(F(Math.abs(f.n), f.d), true); }
    }
    fgTri(S, tri); fgNameAll(S);
    return { q: '如圖，' + T('ABCD') + '-' + T('EFGH') + ' 為一長方體。若平面 ' + T(pn) + '（塗色的三角形所在的平面）上一點 ' + T('P') + ' 滿足 ' + T(ov(V + 'P') + '=' + sum) + '，求實數 ' + T('a') + '。' + S.render('長方體 ABCD-EFGH，三個頂點連成的三角形塗色'),
      a: T('a=' + Fr.tex(a)),
      h: '把 ' + T(ov(V + 'P') + '=x' + ov(V + names[0]) + '+y' + ov(V + names[1]) + '+z' + ov(V + names[2])) + ' 的係數 ' + T('(x,y,z)') + ' 當作 ' + T('P') + ' 的坐標（' + T(V) + ' 是原點，三條稜各當 ' + T('1') + ' 個單位；共平面只看係數，與稜長無關）。從圖上看每個頂點要沿哪幾條稜走：' + fgPtList(tri, pts) + '。設平面 ' + T(pn + ':px+qy+rz=d') + '，三點代入解得 ' + T(planeTex(pl)) + '。' + T('P') + ' 的坐標是 ' + T('\\left(' + [0, 1, 2].map(coefT).join(',\\ ') + '\\right)') + '，代入：' + T(lhs + '=' + pl[3]) + ' ⟹ ' + T('a=' + Fr.tex(a)) + '。',
      p: { lay: lay, dims: dims, V: V, tri: tri, u: u, cs: cs.map(function (f) { return [f.n, f.d]; }) } };
  };
  META_L3.push(['figCubeDist', '正立方體的頂點到截面的距離（附圖）'], ['figBoxCoplanar', '長方體截面上一點的向量係數（附圖）']);
  L3_FIX['L3-20'] = 'figCubeDist'; L3_FIX['L3-21'] = 'figBoxCoplanar';

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
