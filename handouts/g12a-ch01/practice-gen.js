/* ══════════════════════════════════════════════════════════════
   g12a-ch01 數列與函數的極限・分級練習本　題目產生器
   ─────────────────────────────────────────────────────────────
   每個產生器：function (rng) → { q, a, h, p }
     q：題目（HTML，可含 KaTeX $…$）   a：答案（HTML）
     h：第二層提示（一定帶本題的數字與關鍵一步，但不直接寫最終答案）
     p：輸入參數（給 L1_SOL 重算步驟；驗算器 verify_gen12a1.py 不讀 p，一律從題幹重算）
   排版慣例：數列極限 \lim_{n\to\infty}、函數極限 \lim_{x\to a}、右／左極限 x\to a^{+}／a^{-}；
     高斯符號 [x]（題幹一律註明「不大於 x 的最大整數」）；絕對值 \left|…\right|；
     循環小數 0.\overline{12}；常數 e 寫成 e；合成 (f\circ g)(x)；反函數 f^{-1}(x)。
   課綱界線（HANDOUT_SPEC §4、OUTLINE §2）：不出現羅必達、ε-δ、漸近線、導數；
     極限不寫成 =\infty（發散就寫「發散」）；遞迴求極限一律寫「若極限存在」或「已知收斂」；
     x→∞ 的函數極限不進 L1／L2；非等比級數只做裂項（部分和求得出來）。
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
    r(); r(); r();   /* 暖機：連號種子的第一個 r() 幾乎一樣 */
    return r;
  }
  function gcd(a, b) { a = Math.abs(a); b = Math.abs(b); while (b) { var t = a % b; a = b; b = t; } return a; }
  function F(n, d) { if (d === undefined) d = 1; if (d < 0) { n = -n; d = -d; } var g = gcd(n, d) || 1; return { n: n / g, d: d / g }; }
  function N(x) { return (typeof x === 'number') ? F(x) : x; }
  var Fr = {
    add: function (x, y) { x = N(x); y = N(y); return F(x.n * y.d + y.n * x.d, x.d * y.d); },
    sub: function (x, y) { x = N(x); y = N(y); return F(x.n * y.d - y.n * x.d, x.d * y.d); },
    mul: function (x, y) { x = N(x); y = N(y); return F(x.n * y.n, x.d * y.d); },
    div: function (x, y) { x = N(x); y = N(y); return F(x.n * y.d, x.d * y.n); },
    neg: function (x) { x = N(x); return F(-x.n, x.d); },
    abs: function (x) { x = N(x); return F(Math.abs(x.n), x.d); },
    eq: function (x, y) { x = N(x); y = N(y); return x.n * y.d === y.n * x.d; },
    cmp: function (x, y) { x = N(x); y = N(y); return x.n * y.d - y.n * x.d; },
    num: function (x) { x = N(x); return x.n / x.d; },
    pow: function (x, k) { var t = F(1), i; for (i = 0; i < k; i++) t = Fr.mul(t, x); return t; },
    tex: function (x, small) {
      x = N(x);
      if (x.d === 1) return String(x.n);
      var f = small ? '\\frac' : '\\dfrac';
      return (x.n < 0 ? '-' : '') + f + '{' + Math.abs(x.n) + '}{' + x.d + '}';
    }
  };
  function fp(f) { f = N(f); return [f.n, f.d]; }
  function fT(x) { return Fr.tex(N(x)); }
  function fS(x) { return Fr.tex(N(x), true); }
  function T(s) { return '$' + s + '$'; }
  function no(i) { return '(' + i + ') '; }
  function jo(a) { return a.join('　'); }
  /* 負數加括號：(-3)、\left(-\dfrac{1}{2}\right) */
  function pn(x) { x = N(x); var s = fT(x); if (x.n >= 0) return s; return x.d === 1 ? '(' + s + ')' : '\\left(' + s + '\\right)'; }
  /* 帶號接在後面：+3、-\dfrac{1}{2}（0 不印） */
  function sg(x) { x = N(x); if (x.n === 0) return ''; return (x.n < 0 ? '-' : '+') + fT(Fr.abs(x)); }
  /* 多項式：cs 由高次到低次（整數或分數） */
  function polyT(cs, v) {
    v = v || 'x';
    var s = '', deg = cs.length - 1, i, c, a, d, body;
    for (i = 0; i < cs.length; i++) {
      c = N(cs[i]); if (c.n === 0) continue; d = deg - i;
      a = Fr.abs(c);
      body = (d > 0 && a.n === 1 && a.d === 1) ? '' : fT(a);
      if (d === 1) body += v; else if (d > 1) body += v + (d < 10 ? '^' + d : '^{' + d + '}');
      s += (c.n < 0 ? '-' : (s === '' ? '' : '+')) + body;
    }
    return s === '' ? '0' : s;
  }
  function pval(cs, x) { var t = F(0), i; for (i = 0; i < cs.length; i++) t = Fr.add(Fr.mul(t, x), N(cs[i])); return t; }
  function pmul(A, B) { var out = [], i, j; for (i = 0; i < A.length + B.length - 1; i++) out.push(F(0)); for (i = 0; i < A.length; i++) for (j = 0; j < B.length; j++) out[i + j] = Fr.add(out[i + j], Fr.mul(N(A[i]), N(B[j]))); return out; }
  function padd(A, B) { var n = Math.max(A.length, B.length), out = [], i, a, b; for (i = 0; i < n; i++) { a = i - (n - A.length) >= 0 ? N(A[i - (n - A.length)]) : F(0); b = i - (n - B.length) >= 0 ? N(B[i - (n - B.length)]) : F(0); out.push(Fr.add(a, b)); } return out; }
  function pnum(cs) { return cs.map(function (c) { return Fr.num(N(c)); }); }
  /* (x-a) 的寫法：a=0 → x；a<0 → x+3 */
  function xm(a, v) { v = v || 'x'; a = N(a); if (a.n === 0) return v; return v + (a.n < 0 ? '+' : '-') + fT(Fr.abs(a)); }
  function pxm(a, v) { return N(a).n === 0 ? (v || 'x') : '(' + xm(a, v) + ')'; }
  function pp(v) { return '(' + fT(v) + ')'; }
  /* 高斯符號：裡面有 \dfrac 就用 \left[ \right] */
  function gb(s) { return s.indexOf('\\dfrac') >= 0 ? '\\left[' + s + '\\right]' : '[' + s + ']'; }
  /* 函數的引數：分數加 \left( \right) */
  function ar(x) { var s = fT(x); return s.indexOf('\\dfrac') >= 0 ? '\\left(' + s + '\\right)' : '(' + s + ')'; }
  /* 根式：n = c^2 r */
  function sqf(n) { var c = 1, r = n, k; for (k = 2; k * k <= r; k++) while (r % (k * k) === 0) { r /= k * k; c *= k; } return [c, r]; }
  function isq(n) { var s = Math.round(Math.sqrt(n)); return s * s === n; }
  /* b√r（b 是分數；r 無平方因數） */
  function surdT(b, r) {
    b = N(b); if (b.n === 0) return '0'; if (r === 1) return fT(b);
    var neg = b.n < 0, an = Math.abs(b.n), core = (an === 1 ? '' : an) + '\\sqrt{' + r + '}';
    return (neg ? '-' : '') + (b.d === 1 ? core : '\\dfrac{' + core + '}{' + b.d + '}');
  }
  /* a + b√r */
  function qrT(a, b, r) {
    a = N(a); b = N(b);
    if (r === 1) return fT(Fr.add(a, b));
    if (b.n === 0) return fT(a);
    if (a.n === 0) return surdT(b, r);
    return fT(a) + (b.n < 0 ? '-' : '+') + surdT(Fr.abs(b), r);
  }
  /* √n 化簡後的 LaTeX */
  function sqrtT(n) { var q = sqf(n); return surdT(F(q[0]), q[1]); }
  function trimz(s) { if (s.indexOf('.') < 0) return s; s = s.replace(/0+$/, ''); if (s.charAt(s.length - 1) === '.') s = s.slice(0, -1); return s; }
  function decT(f) { f = N(f); return trimz((f.n / f.d).toFixed(6)); }
  /* e 的次方 */
  function eT(k) { k = N(k); if (k.n === 0) return '1'; if (k.n === 1 && k.d === 1) return 'e'; return 'e^{' + fS(k) + '}'; }
  var LN = '\\lim_{n\\to\\infty}';
  function LX(a, side) { return '\\lim_{x\\to ' + fT(a) + (side ? '^{' + side + '}' : '') + '}'; }
  var GAUSS = '（' + T('[x]') + ' 表示不大於 ' + T('x') + ' 的最大整數）';
  var SUMI = '\\sum_{n=1}^{\\infty}';
  /* 各項係數接在一起：係數 1 不印、-1 印負號 */
  function cf(c) { c = N(c); if (c.n === 1 && c.d === 1) return ''; if (c.n === -1 && c.d === 1) return '-'; return fT(c); }

  /* ══ 區間集合（定義域、收斂範圍、高斯方程式）：{lo,hi,li,hi_}，lo／hi 是分數或 null（無限） ══ */
  function IV(lo, hi, li, hi_) { return { lo: lo === null ? null : N(lo), hi: hi === null ? null : N(hi), li: !!li, hi_: !!hi_ }; }
  function ivInter(A, B) {
    var out = [];
    A.forEach(function (a) {
      B.forEach(function (b) {
        var lo, li, hi, hi_, c;
        if (a.lo === null) { lo = b.lo; li = b.li; } else if (b.lo === null) { lo = a.lo; li = a.li; }
        else { c = Fr.cmp(a.lo, b.lo); if (c > 0) { lo = a.lo; li = a.li; } else if (c < 0) { lo = b.lo; li = b.li; } else { lo = a.lo; li = a.li && b.li; } }
        if (a.hi === null) { hi = b.hi; hi_ = b.hi_; } else if (b.hi === null) { hi = a.hi; hi_ = a.hi_; }
        else { c = Fr.cmp(a.hi, b.hi); if (c < 0) { hi = a.hi; hi_ = a.hi_; } else if (c > 0) { hi = b.hi; hi_ = b.hi_; } else { hi = a.hi; hi_ = a.hi_ && b.hi_; } }
        if (lo !== null && hi !== null) { c = Fr.cmp(lo, hi); if (c > 0 || (c === 0 && !(li && hi_))) return; }
        out.push({ lo: lo, hi: hi, li: li, hi_: hi_ });
      });
    });
    return out;
  }
  function ivMinus(S, c) {
    var out = [];
    c = N(c);
    S.forEach(function (a) {
      var inLo = a.lo === null || Fr.cmp(c, a.lo) > 0 || (Fr.cmp(c, a.lo) === 0 && a.li);
      var inHi = a.hi === null || Fr.cmp(c, a.hi) < 0 || (Fr.cmp(c, a.hi) === 0 && a.hi_);
      if (!(inLo && inHi)) { out.push(a); return; }
      if (a.lo === null || Fr.cmp(c, a.lo) > 0) out.push({ lo: a.lo, hi: c, li: a.li, hi_: false });
      if (a.hi === null || Fr.cmp(c, a.hi) < 0) out.push({ lo: c, hi: a.hi, li: false, hi_: a.hi_ });
    });
    return out;
  }
  function ivGe(a) { return [IV(a, null, true, false)]; }
  function ivGt(a) { return [IV(a, null, false, false)]; }
  function ivLe(a) { return [IV(null, a, false, true)]; }
  function ivLt(a) { return [IV(null, a, false, false)]; }
  var ivAll = function () { return [IV(null, null, false, false)]; };
  function ivFmt(S, v) {
    v = v || 'x';
    return S.map(function (a) {
      if (a.lo === null && a.hi === null) return '\\text{任意實數}';
      if (a.lo === null) return v + (a.hi_ ? '\\le ' : '\\lt ') + fT(a.hi);
      if (a.hi === null) return v + (a.li ? '\\ge ' : '\\gt ') + fT(a.lo);
      return fT(a.lo) + (a.li ? '\\le ' : '\\lt ') + v + (a.hi_ ? '\\le ' : '\\lt ') + fT(a.hi);
    }).join('\\ \\text{或}\\ ');
  }
  /* 隨機整係數多項式（首項不為 0） */
  function rpoly(r, d, lo, hi) { var cs = [r.nz(lo, hi)], i; for (i = 0; i < d; i++) cs.push(r.int(-9, 9)); return cs; }
  /* 數列的一般項同除以 n^D：c n^k → c、\frac{c}{n^{D-k}}、c n^{k-D} */
  function divT(cs, D) {
    var deg = cs.length - 1, s = '', i, c, k, e, a, body;
    for (i = 0; i < cs.length; i++) {
      c = N(cs[i]); if (c.n === 0) continue; k = deg - i; a = Fr.abs(c);
      if (k === D) body = fT(a);
      else if (k < D) { e = D - k; body = '\\frac{' + fT(a) + '}{n' + (e === 1 ? '' : '^' + e) + '}'; }
      else { e = k - D; body = (a.n === 1 && a.d === 1 ? '' : fT(a)) + 'n' + (e === 1 ? '' : '^' + e); }
      s += (c.n < 0 ? '-' : (s === '' ? '' : '+')) + body;
    }
    return s;
  }

  /* ═══════════════════════ L1 ═══════════════════════ */
  var L1 = {};

  /* ── 1-2 有理式數列的極限（看最高次） ── */
  L1.seqRational = function (r) {
    r();
    var kind = r.int(0, 4), num, den, numT, d, t = 0, ok, i, lim = null, a1, b1, a2, b2;
    do {
      if (kind === 0 || kind === 4) { d = r.int(1, 3); num = rpoly(r, d, -7, 7); den = rpoly(r, d, -7, 7); }
      else if (kind === 1) { a1 = r.nz(-4, 4); b1 = r.nz(-6, 6); a2 = r.nz(-4, 4); b2 = r.nz(-6, 6); num = [a1 * a2, a1 * b2 + a2 * b1, b1 * b2]; den = rpoly(r, 2, -7, 7); }
      else if (kind === 2) { d = r.int(1, 2); num = rpoly(r, d, -7, 7); den = rpoly(r, d + r.int(1, 2), -7, 7); }
      else { d = r.int(1, 2); den = rpoly(r, d, -7, 7); num = rpoly(r, d + 1, -7, 7); }
      ok = true; for (i = 1; i <= 40; i++) if (Fr.num(pval(den, F(i))) === 0) ok = false;
      if (kind === 0 || kind === 4) { if (num[0] === den[0] && kind === 0 && r() < 0.5) ok = false; }
    } while (!ok && t++ < 80);
    numT = kind === 1 ? '(' + polyT([a1, b1], 'n') + ')(' + polyT([a2, b2], 'n') + ')' : polyT(num, 'n');
    var D = den.length - 1;
    if (num.length === den.length) lim = F(num[0], den[0]); else if (num.length < den.length) lim = F(0);
    var q = '判斷數列 ' + T('a_n=\\dfrac{' + numT + '}{' + polyT(den, 'n') + '}') + ' 是否收斂；若收斂，求 ' + T(LN + 'a_n') + '。';
    var a = lim === null ? '發散' : '收斂，' + T(LN + 'a_n=' + fT(lim));
    var h = (kind === 1 ? '先把分子乘開得 ' + T(polyT(num, 'n')) + '；' : '') + '分子、分母同除以 ' + T('n' + (D === 1 ? '' : '^' + D)) + '（分母的最高次）：' + T('a_n=\\dfrac{' + divT(num, D) + '}{' + divT(den, D) + '}') + '，再看 ' + T('n\\to\\infty') + ' 時哪些項趨近 ' + T(0) + '、哪些項會越來越大。';
    return { q: q, a: a, h: h, p: { kind: kind, num: num, den: den, lim: lim === null ? null : fp(lim) } };
  };

  /* ── 1-1 r^n 依 r 判斷收斂 ── */
  L1.rPow = function (r) {
    r();
    var kind = r.int(0, 6), c = r.int(-5, 5), d = r.nz(-4, 4), u, v, base, bT, lim = null, rv, absT;
    if (kind === 0 || kind === 1) {                       /* |r|<1 的分數 */
      v = r.int(2, 7); do { u = r.int(1, v - 1); } while (gcd(u, v) !== 1);
      rv = F(kind === 1 ? -u : u, v);
      bT = '\\left(' + fT(rv) + '\\right)^{n}'; lim = F(c);
    } else if (kind === 2) {                              /* |r|>1 */
      u = r.int(3, 9); do { v = r.int(2, u - 1); } while (gcd(u, v) !== 1);
      rv = F(r.sign() * u, v);
      bT = '\\left(' + fT(rv) + '\\right)^{n}';
    } else if (kind === 3) { rv = F(-1); bT = '(-1)^{n}'; }
    else if (kind === 4) { rv = F(1); bT = '(-1)^{2n}'; lim = F(c + d); }
    else if (kind === 5) {                                /* 小數底 */
      u = r.pick([2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 15]); u = r.sign() * u; rv = F(u, 10);
      bT = '(' + decT(rv) + ')^{n}'; if (Math.abs(u) < 10) lim = F(c);
    } else {                                              /* 整數底 */
      u = r.pick([-3, -2, 2, 3]); rv = F(u); bT = (u < 0 ? '(' + u + ')' : u) + '^{n}';
    }
    var term = (c === 0 ? '' : String(c)) + (d < 0 ? '-' : (c === 0 ? '' : '+')) + (Math.abs(d) === 1 ? '' : Math.abs(d) + (bT.charAt(0) === '\\' || bT.charAt(0) === '(' ? '' : '\\cdot ')) + bT;
    var q = '判斷數列 ' + T('a_n=' + term) + ' 是否收斂；若收斂，求 ' + T(LN + 'a_n') + '。';
    var a = lim === null ? '發散' : '收斂，' + T(LN + 'a_n=' + fT(lim));
    absT = kind === 3 ? '|-1|=1' : (kind === 4 ? '' : '\\left|' + (kind === 5 ? decT(rv) : fT(rv)) + '\\right|=' + (kind === 5 ? decT(Fr.abs(rv)) : fT(Fr.abs(rv))));
    var h = kind === 4 ? '先化簡：' + T('(-1)^{2n}=\\left((-1)^2\\right)^{n}=1^{n}') + '，所以 ' + T('a_n=' + (c === 0 ? d + '\\cdot 1' : c + sg(d) + '\\cdot 1')) + ' 每一項都一樣——常數數列收斂到哪裡？'
      : '看底數 ' + T('r=' + (kind === 5 ? decT(rv) : fT(rv))) + '：' + T(absT) + '。' + T('|r|\\lt 1') + ' 時 ' + T('r^n\\to 0') + '；' + T('r=-1') + ' 時在 ' + T('\\pm1') + ' 之間跳；' + T('|r|\\gt 1') + ' 時越跳越大。';
    return { q: q, a: a, h: h, p: { kind: kind, c: c, d: d, r: fp(rv), lim: lim === null ? null : fp(lim) } };
  };

  /* ── 1-2 指數型：同除以最大的底 ── */
  function expTerm(c, b, s) { var e = 'n' + (s > 0 ? '+' + s : (s < 0 ? s : '')); return (c === 1 ? '' : (c === -1 ? '-' : c + '\\cdot ')) + b + '^{' + e + '}'; }
  function joinT(a, b) { return b.charAt(0) === '-' ? a + b : a + '+' + b; }
  L1.expDiv = function (r) {
    r();
    var p, q0, s, t, a, b, c, d, tries = 0, ok, n, M, NM, DM, lim, numT, denT, sw;
    do {
      p = r.int(2, 7); do { q0 = r.int(2, 7); } while (q0 === p);
      s = r.int(0, 2); t = r.int(0, 1);
      a = r() < 0.2 ? 0 : r.nz(-5, 5); b = r.nz(-5, 5); c = r.nz(-5, 5); d = r.nz(-5, 5);
      ok = true;
      for (n = 1; n <= 10; n++) if (c * Math.pow(p, n) + d * Math.pow(q0, n + t) === 0) ok = false;
    } while (!ok && tries++ < 60);
    /* 分子 a p^{n+s} + b q^n；分母 c p^n + d q^{n+t} */
    M = Math.max(p, q0);
    NM = M === p ? a * Math.pow(p, s) : b; DM = M === p ? c : d * Math.pow(q0, t);
    lim = F(NM, DM);
    sw = r() < 0.5;
    var nA = a === 0 ? '' : expTerm(a, p, s), nB = expTerm(b, q0, 0);
    numT = a === 0 ? nB : (sw ? joinT(nB, nA) : joinT(nA, nB));
    var dA = expTerm(c, p, 0), dB = expTerm(d, q0, t);
    denT = sw ? joinT(dB, dA) : joinT(dA, dB);
    var m = Math.min(p, q0);
    var qq = '求 ' + T(LN + '\\dfrac{' + numT + '}{' + denT + '}') + '。';
    var topN = M === p ? (a === 0 ? '' : nA) : nB, topD = M === p ? dA : dB;
    var h = '最大的底是 ' + T(M) + '：' + (topN === '' ? '分子裡沒有 ' + T(M + '^{n}') + ' 的項' : '分子裡是 ' + T(topN)) + '、分母裡是 ' + T(topD) + '。分子、分母同除以 ' + T(M + '^{n}') + '。像 ' + T(M + '^{n+1}') + ' 除以 ' + T(M + '^{n}') + ' 剩 ' + T(M) + '；' + T('\\dfrac{' + m + '^{n}}{' + M + '^{n}}=\\left(\\frac{' + m + '}{' + M + '}\\right)^{n}\\to 0') + '。';
    return { q: qq, a: T(fT(lim)), h: h, p: { p: p, q: q0, s: s, t: t, a: a, b: b, c: c, d: d, lim: fp(lim) } };
  };

  /* ── 1-2 根式有理化 ── */
  L1.rootRat = function (r) {
    r();
    var kind = r.int(0, 4), a, b, m, ex, lim, h, i, ok, t = 0, rad, conj, top;
    if (kind === 0) {
      do { a = r.nz(-8, 8); b = r.nz(-9, 9); ok = true; for (i = 1; i <= 30; i++) if (i * i + a * i + b < 0) ok = false; } while (!ok && t++ < 50);
      rad = polyT([1, a, b], 'n'); ex = '\\sqrt{' + rad + '}-n'; lim = F(a, 2);
      top = '(' + rad + ')-n^2=' + polyT([a, b], 'n'); conj = '\\sqrt{' + rad + '}+n';
    } else if (kind === 1) {
      a = r.int(-1, 9); do { b = r.int(-1, 9); } while (Math.abs(b - a) < 2);
      ex = '\\sqrt{' + polyT([1, a, 0], 'n') + '}-\\sqrt{' + polyT([1, b, 0], 'n') + '}'; lim = F(a - b, 2);
      top = '(' + polyT([1, a, 0], 'n') + ')-(' + polyT([1, b, 0], 'n') + ')=' + polyT([a - b, 0], 'n'); conj = '\\sqrt{' + polyT([1, a, 0], 'n') + '}+\\sqrt{' + polyT([1, b, 0], 'n') + '}';
    } else if (kind === 2) {
      a = r.pick([-1, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
      rad = polyT([1, 0, a], 'n'); ex = 'n\\left(\\sqrt{' + rad + '}-n\\right)'; lim = F(a, 2);
      top = 'n\\left[(' + rad + ')-n^2\\right]=' + a + 'n'; conj = '\\sqrt{' + rad + '}+n';
    } else if (kind === 3) {
      m = r.int(2, 4); a = r.nz(-9, 9); if (a < 0 && a > -m * m) a = -a; if (a < -m * m + 1) a = Math.abs(a);
      rad = polyT([m * m, a, 0], 'n'); ex = '\\sqrt{' + rad + '}-' + m + 'n'; lim = F(a, 2 * m);
      top = '(' + rad + ')-' + (m * m) + 'n^2=' + polyT([a, 0], 'n'); conj = '\\sqrt{' + rad + '}+' + m + 'n';
    } else {
      a = r.int(1, 9); rad = polyT([1, a, 0], 'n'); ex = '\\dfrac{1}{\\sqrt{' + rad + '}-n}'; lim = F(2, a);
      top = '\\sqrt{' + rad + '}+n'; conj = '\\sqrt{' + rad + '}+n';
    }
    var q = '求 ' + T(LN + (kind === 4 || kind === 2 ? ex : '\\left(' + ex + '\\right)')) + '。';
    h = kind === 4 ? '分母是「根號減 ' + T('n') + '」：分子分母同乘 ' + T(conj) + '，分母變成 ' + T('(' + rad + ')-n^2=' + a + 'n') + '，再同除以 ' + T('n') + '。'
      : '「根號減根號」型先有理化：乘以 ' + T('\\dfrac{' + conj + '}{' + conj + '}') + '，分子變成 ' + T(top) + '，再同除以 ' + T('n') + '。';
    return { q: q, a: T(fT(lim)), h: h, p: { kind: kind, a: a, b: b, m: m, lim: fp(lim) } };
  };

  /* ── 1-3 夾擠定理：[αn]／n 型 ── */
  function alphaPick(r) {
    var k = r.int(0, 2), m, q, u, v;
    if (k === 0) { do { m = r.int(2, 15); } while (isq(m)); q = sqf(m); return { kind: 'sqrt', m: m, c: q[0], rr: q[1], tex: surdT(F(q[0]), q[1]), inT: (q[0] === 1 ? '' : q[0]) + 'n\\sqrt{' + q[1] + '}', inT2: (q[0] === 1 ? '' : q[0]) + 'n^2\\sqrt{' + q[1] + '}', approx: Math.sqrt(m) }; }
    if (k === 1) { v = r.int(2, 7); do { u = r.int(1, 3 * v); } while (gcd(u, v) !== 1 || u % v === 0); return { kind: 'frac', u: u, v: v, tex: fT(F(u, v)), inT: '\\dfrac{' + (u === 1 ? '' : u) + 'n}{' + v + '}', approx: u / v }; }
    return { kind: 'pi', tex: '\\pi', inT: 'n\\pi', approx: Math.PI };
  }
  function alphaOver(al, b) {           /* α/b 的 LaTeX */
    if (al.kind === 'sqrt') return surdT(F(al.c, b), al.rr);
    if (al.kind === 'frac') return fT(F(al.u, al.v * b));
    return b === 1 ? '\\pi' : '\\dfrac{\\pi}{' + b + '}';
  }
  L1.squeezeFloor = function (r) {
    r();
    var kind = r.int(0, 2), al = alphaPick(r), b = r.int(1, 5), c = r.int(1 - b, 5), ex, ans, h, dn;
    if (kind === 0) {
      dn = polyT([b, c], 'n'); ex = '\\dfrac{' + gb(al.inT) + '}{' + dn + '}'; ans = alphaOver(al, b);
      h = T(al.inT + '-1\\lt ' + gb(al.inT) + '\\le ' + al.inT) + '，三邊同除以 ' + T(dn) + '（' + T('n\\ge1') + ' 時為正），兩邊的極限都算得出來，再用夾擠定理。';
    } else if (kind === 1) {
      b = 1; c = 0; ex = '\\dfrac{' + gb(al.inT) + '}{n}'; ans = alphaOver(al, 1);
      h = T(al.inT + '-1\\lt ' + gb(al.inT) + '\\le ' + al.inT) + '，三邊同除以 ' + T('n') + '：左邊是 ' + T(al.tex + '-\\dfrac{1}{n}') + '，右邊是 ' + T(al.tex) + '。';
    } else {
      dn = polyT([b, 0, c], 'n'); var inT2 = al.kind === 'frac' ? '\\dfrac{' + (al.u === 1 ? '' : al.u) + 'n^2}{' + al.v + '}' : (al.kind === 'pi' ? 'n^2\\pi' : al.inT2);
      ex = '\\dfrac{' + gb(inT2) + '}{' + dn + '}'; ans = alphaOver(al, b);
      h = T(inT2 + '-1\\lt ' + gb(inT2) + '\\le ' + inT2) + '，三邊同除以 ' + T(dn) + '，左右兩邊的極限相同，就能夾出答案。';
    }
    var q = '求 ' + T(LN + ex) + GAUSS + '。';
    return { q: q, a: T(ans), h: h, p: { kind: kind, al: al, b: b, c: c } };
  };

  /* ── 1-4 遞迴數列 a_{n+1}=p a_n + q 的極限 ── */
  L1.recurLimit = function (r) {
    r();
    var P = r.pick([[1, 2], [-1, 2], [1, 3], [-1, 3], [2, 3], [-2, 3], [1, 4], [3, 4], [-1, 4], [1, 5], [2, 5], [-2, 5], [3, 5]]);
    var p = F(P[0], P[1]), L = r.int(-6, 6), q0 = Fr.mul(L, Fr.sub(1, p)), a1, form = r.int(0, 2), rec;
    do { a1 = r.int(-6, 8); } while (a1 === L);
    if (form === 1 && P[0] === 1 && q0.d === 1) {
      rec = 'a_{n+1}=\\dfrac{a_n' + sg(Fr.mul(q0, P[1])) + '}{' + P[1] + '}';
    } else if (form === 2 && q0.d === 1) {
      rec = P[1] + 'a_{n+1}=' + cf(P[0]) + 'a_n' + sg(Fr.mul(q0, P[1]));
    } else { form = 0; rec = 'a_{n+1}=' + cf(p) + 'a_n' + sg(q0); }
    var a2 = Fr.add(Fr.mul(p, a1), q0), a3 = Fr.add(Fr.mul(p, a2), q0);
    var q = '數列 ' + T('\\langle a_n\\rangle') + ' 滿足 ' + T('a_1=' + a1) + '、' + T(rec) + '（' + T('n\\ge1') + '）。' + no(1) + '求 ' + T('a_3') + '。' + no(2) + '已知此數列收斂，求 ' + T(LN + 'a_n') + '。';
    var a = jo([no(1) + T('a_3=' + fT(a3)), no(2) + T(LN + 'a_n=' + fT(L))]);
    var h = no(1) + T('a_2=' + fT(a2)) + '，再代一次。' + no(2) + '令 ' + T(LN + 'a_n=L') + '，則 ' + T(LN + 'a_{n+1}') + ' 也是 ' + T('L') + '：兩邊取極限得 ' + T('L=' + cf(p) + 'L' + sg(q0)) + '。';
    return { q: q, a: a, h: h, p: { p: fp(p), q: fp(q0), a1: a1, L: L, form: form, a2: fp(a2), a3: fp(a3) } };
  };

  /* ── 1-4 牛頓求根法：√a 的迭代 ── */
  L1.newtonSqrt = function (r) {
    r();
    var A, x1, form = r.int(0, 1), x2, x3, rec;
    do { A = r.int(2, 60); } while (isq(A));
    x1 = r() < 0.5 ? Math.floor(Math.sqrt(A)) : Math.ceil(Math.sqrt(A));
    x2 = Fr.mul(F(1, 2), Fr.add(x1, F(A, x1)));
    x3 = Fr.mul(F(1, 2), Fr.add(x2, Fr.div(A, x2)));
    rec = form === 0 ? 'x_{n+1}=\\dfrac{1}{2}\\left(x_n+\\dfrac{' + A + '}{x_n}\\right)' : 'x_{n+1}=x_n-\\dfrac{x_n^2-' + A + '}{2x_n}';
    var q = '用牛頓法求 ' + T('x^2=' + A) + ' 的正根：取 ' + T('x_1=' + x1) + '，' + T(rec) + '。' + no(1) + '求 ' + T('x_2') + '。' + no(2) + '求 ' + T('x_3') + '。' + no(3) + '若此數列收斂，求 ' + T(LN + 'x_n') + '。';
    var a = jo([no(1) + T('x_2=' + fT(x2)), no(2) + T('x_3=' + fT(x3)), no(3) + T(LN + 'x_n=' + sqrtT(A))]);
    var h = no(1) + T('x_2=' + (form === 0 ? '\\dfrac{1}{2}\\left(' + x1 + '+\\dfrac{' + A + '}{' + x1 + '}\\right)' : x1 + '-\\dfrac{' + x1 + '^2-' + A + '}{2\\cdot ' + x1 + '}')) + '。' + no(3) + '令極限為 ' + T('L\\gt 0') + '，代入 ' + T('L=\\dfrac{1}{2}\\left(L+\\dfrac{' + A + '}{L}\\right)') + ' 解 ' + T('L') + '。';
    return { q: q, a: a, h: h, p: { A: A, x1: x1, form: form, x2: fp(x2), x3: fp(x3) } };
  };

  /* ── 1-5 連續複利與 e ── */
  L1.compound = function (r) {
    r();
    var kind = r.int(0, 6), k, m, c, ex, ans, h, q;
    if (kind === 6) {
      var P = r.pick([10000, 20000, 50000, 100000, 30000]), rt = r.pick([2, 3, 4, 5, 6, 8]), yr = r.int(1, 5), kk = F(rt * yr, 100);
      q = '本金 ' + T(P) + ' 元、年利率 ' + T(rt + '\\%') + '，每年平均分成 ' + T('m') + ' 期複利計息。存 ' + T(yr) + ' 年後的本利和是 ' + T(P + '\\left(1+\\dfrac{' + decT(F(rt, 100)) + '}{m}\\right)^{' + (yr === 1 ? '' : yr) + 'm}') + ' 元。當 ' + T('m\\to\\infty') + '（連續複利）時，本利和趨近多少元？（答案用 ' + T('e') + ' 表示）';
      ans = P + 'e^{' + decT(kk) + '}';
      h = '令 ' + T('t=\\dfrac{m}{' + decT(F(rt, 100)) + '}') + '：' + T('\\left(1+\\dfrac{' + decT(F(rt, 100)) + '}{m}\\right)^{' + (yr === 1 ? '' : yr) + 'm}=\\left[\\left(1+\\dfrac{1}{t}\\right)^{t}\\right]^{' + decT(kk) + '}') + '，而 ' + T('\\left(1+\\dfrac{1}{t}\\right)^{t}\\to e') + '。';
      return { q: q, a: T(ans), h: h, p: { kind: kind, P: P, rt: rt, yr: yr, k: fp(kk) } };
    }
    k = r.nz(-4, 4); m = r.int(2, 4); c = r.nz(-3, 3);
    if (kind === 0) { ex = '\\left(1+\\dfrac{' + k + '}{n}\\right)^{n}'; if (k < 0) ex = '\\left(1-\\dfrac{' + (-k) + '}{n}\\right)^{n}'; ans = F(k); }
    else if (kind === 1) { ex = '\\left(1+\\dfrac{1}{n}\\right)^{' + m + 'n}'; ans = F(m); k = 1; }
    else if (kind === 2) { k = Math.abs(k); ex = '\\left(1' + (r() < 0.5 ? '+' : '-') + '\\dfrac{' + k + '}{n}\\right)^{' + m + 'n}'; ans = F(ex.indexOf('1-') >= 0 ? -k * m : k * m); if (ex.indexOf('1-') >= 0) k = -k; }
    else if (kind === 3) { m = r.int(2, 5); ex = '\\left(1+\\dfrac{1}{' + m + 'n}\\right)^{n}'; ans = F(1, m); k = 1; }
    else if (kind === 4) { ex = '\\left(\\dfrac{n' + sg(k) + '}{n}\\right)^{n}'; ans = F(k); }
    else { ex = '\\left(1+\\dfrac{' + Math.abs(k) + '}{n}\\right)^{n' + sg(c) + '}'; k = Math.abs(k); ans = F(k); }
    q = '求 ' + T(LN + ex) + '。（答案用 ' + T('e') + ' 表示）';
    if (kind === 3) h = '令 ' + T('t=' + m + 'n') + '：' + T('\\left(1+\\dfrac{1}{t}\\right)^{n}=\\left[\\left(1+\\dfrac{1}{t}\\right)^{t}\\right]^{\\frac{1}{' + m + '}}') + '。';
    else if (kind === 1) h = T('\\left(1+\\dfrac{1}{n}\\right)^{' + m + 'n}=\\left[\\left(1+\\dfrac{1}{n}\\right)^{n}\\right]^{' + m + '}') + '，而 ' + T('\\left(1+\\dfrac{1}{n}\\right)^{n}\\to e') + '。';
    else if (kind === 5) h = '拆成 ' + T('\\left(1+\\dfrac{' + k + '}{n}\\right)^{n}\\cdot\\left(1+\\dfrac{' + k + '}{n}\\right)^{' + c + '}') + '：後面那個因式的次方固定，趨近 ' + T('1^{' + c + '}') + '。';
    else h = '令 ' + T('t=\\dfrac{n}{' + Math.abs(k) + '}') + '（' + T('n\\to\\infty') + ' 時 ' + T('t\\to\\infty') + '），把式子湊成 ' + T('\\left[\\left(1+\\dfrac{1}{t}\\right)^{t}\\right]^{\\cdots}') + ' 或 ' + T('\\left[\\left(1-\\dfrac{1}{t}\\right)^{t}\\right]^{\\cdots}') + '；注意 ' + T('\\left(1-\\dfrac{1}{t}\\right)^{t}\\to e^{-1}') + '。這題的 ' + T('k=' + k) + (kind === 2 ? '、次方還要再乘 ' + T(m) : '') + '。';
    return { q: q, a: T(eT(ans)), h: h, p: { kind: kind, k: k, m: m, c: c, ans: fp(ans) } };
  };

  /* ═══ §2 無窮級數 ═══ */
  /* 無窮等比級數的一項：c·r^k */
  function termsT(ts) { var s = '', i; for (i = 0; i < ts.length; i++) s += (i === 0 ? fT(ts[i]) : sg(ts[i])); return s + '+\\cdots'; }
  function rPick(r, big) {
    var u, v;
    if (big) return r.pick([F(-1), F(1), F(3, 2), F(-3, 2), F(2), F(-2), F(4, 3), F(-5, 4)]);
    v = r.int(2, 5); do { u = r.int(1, v - 1); } while (gcd(u, v) !== 1);
    return F(r.sign() * u, v);
  }
  L1.geoSum = function (r) {
    r();
    var kind = r.int(0, 4), rv = rPick(r, kind === 4), a1, ts, q, S = null, form;
    if (kind <= 1 || kind === 4) {
      form = 'list';
      a1 = F(r.nz(-9, 9) * Math.pow(rv.d, 2));
      if (r() < 0.3) a1 = F(r.nz(-9, 9), r.int(2, 3));
      ts = [a1, Fr.mul(a1, rv), Fr.mul(Fr.mul(a1, rv), rv)];
      q = '判斷無窮級數 ' + T(termsT(ts)) + '（每一項是前一項的固定倍數）是否收斂；若收斂，求其和。';
      if (Math.abs(Fr.num(rv)) < 1) S = Fr.div(a1, Fr.sub(1, rv));
    } else {
      form = kind === 2 ? 'nm1' : 'n';
      a1 = F(r.nz(-9, 9));
      q = '判斷無窮級數 ' + T(SUMI + (a1.n === 1 ? '' : (a1.n < 0 ? '(' + a1.n + ')' : a1.n)) + '\\left(' + fT(rv) + '\\right)^{' + (kind === 2 ? 'n-1' : 'n') + '}') + ' 是否收斂；若收斂，求其和。';
      if (kind === 3) a1 = Fr.mul(a1, rv);           /* 首項 */
      S = Fr.div(a1, Fr.sub(1, rv));
      ts = [a1];
    }
    var a = S === null ? '發散' : '收斂，和為 ' + T(fT(S));
    var h = '首項 ' + T('a=' + fT(a1)) + '、公比 ' + T('r=' + fT(rv)) + '。先看 ' + T('|r|') + ' 有沒有小於 ' + T(1) + '：小於 ' + T(1) + ' 才收斂，和是 ' + T('\\dfrac{a}{1-r}') + '。';
    return { q: q, a: a, h: h, p: { kind: kind, form: form, a1: fp(a1), r: fp(rv), S: S === null ? null : fp(S) } };
  };

  /* ── 2-2 收斂條件求 x 的範圍 ── */
  L1.geoXRange = function (r) {
    r();
    var kind = r.int(0, 3), a, b, c, ex, S, h, lo, hi;
    a = r.pick([1, 2, 3, -1, -2]); b = r.int(-6, 6); c = r.int(2, 6);
    if (kind === 1) c = 1;
    if (kind >= 2 && b === 0) b = r.pick([-1, 1]);
    if (kind === 0 || kind === 1) {
      lo = F(-c - b, a); hi = F(c - b, a); if (a < 0) { var tt = lo; lo = hi; hi = tt; }
      S = [IV(lo, hi, false, false)];
      ex = kind === 0 ? SUMI + '\\left(\\dfrac{' + polyT([a, b]) + '}{' + c + '}\\right)^{n}' : '\\sum_{n=0}^{\\infty}(' + polyT([a, b]) + ')^{n}';
      h = '公比是 ' + T(kind === 0 ? '\\dfrac{' + polyT([a, b]) + '}{' + c + '}' : polyT([a, b])) + '。收斂 ⟺ ' + T('|r|\\lt 1') + '：' + T('-' + c + '\\lt ' + polyT([a, b]) + '\\lt ' + c) + (a < 0 ? '，除以負數要變號' : '') + '。';
    } else if (kind === 2) {
      a = 1; S = [IV(b - c, b + c, false, false)];
      ex = SUMI + '\\dfrac{' + pxm(b) + '^{n}}{' + c + '^{n}}';
      h = '一般項是 ' + T('\\left(\\dfrac{' + xm(b) + '}{' + c + '}\\right)^{n}') + '，公比 ' + T('\\dfrac{' + xm(b) + '}{' + c + '}') + '：收斂 ⟺ ' + T('|' + xm(b) + '|\\lt ' + c) + '。';
    } else {
      a = 1; S = [IV(null, b - c, false, false), IV(b + c, null, false, false)];
      ex = SUMI + '\\left(\\dfrac{' + c + '}{' + xm(b) + '}\\right)^{n}';
      h = '公比 ' + T('\\dfrac{' + c + '}{' + xm(b) + '}') + '（' + T('x\\ne ' + b) + '）：收斂 ⟺ ' + T('\\left|\\dfrac{' + c + '}{' + xm(b) + '}\\right|\\lt 1') + ' ⟺ ' + T('|' + xm(b) + '|\\gt ' + c) + '。';
    }
    var q = '若無窮級數 ' + T(ex) + ' 收斂，求實數 ' + T('x') + ' 的範圍。';
    return { q: q, a: T(ivFmt(S)), h: h, p: { kind: kind, a: a, b: b, c: c } };
  };

  /* ── 2-3 循環小數化分數 ── */
  function digs(r, k, nz) { var s = '', i; for (i = 0; i < k; i++) s += String((i === 0 && nz) ? r.int(1, 9) : r.int(0, 9)); return s; }
  function minPeriod(s) { var L = s.length, d; for (d = 1; d < L; d++) if (L % d === 0 && s.slice(0, d).repeat(L / d) === s) return false; return true; }
  L1.repDec = function (r) {
    r();
    var kind = r.int(0, 4), ip = 0, nr = '', rp = '', t = 0;
    do {
      if (kind === 0) rp = digs(r, 2);
      else if (kind === 1) { nr = digs(r, 1); rp = digs(r, 2); }
      else if (kind === 2) { ip = r.int(1, 5); rp = digs(r, 1); }
      else if (kind === 3) rp = digs(r, 3);
      else { nr = digs(r, 2); rp = digs(r, 1); }
      t++;
    } while ((!minPeriod(rp) || /^9+$/.test(rp) || /^0+$/.test(rp) || (nr !== '' && nr.charAt(nr.length - 1) === rp.charAt(rp.length - 1))) && t < 80);
    var k = nr.length, m = rp.length;
    /* 等比級數的想法：ip + nr/10^k + rp/10^k × (1/10^m + 1/10^{2m} + …) */
    var val = Fr.add(F(ip), Fr.add(F(nr === '' ? 0 : parseInt(nr, 10), Math.pow(10, k)), Fr.mul(F(parseInt(rp, 10), Math.pow(10, k)), F(1, Math.pow(10, m) - 1))));
    var x = ip + '.' + nr + '\\overline{' + rp + '}';
    var q = '把循環小數 ' + T(x) + ' 化成最簡分數。';
    var big = Math.pow(10, k + m), small = Math.pow(10, k);
    var h = '設 ' + T('x=' + x) + '，則 ' + T(big + 'x=' + (ip * big + parseInt((nr + rp) || '0', 10)) + '.\\overline{' + rp + '}') + (k > 0 ? '、' + T(small + 'x=' + (ip * small + parseInt(nr, 10)) + '.\\overline{' + rp + '}') : '') + '，' + (k > 0 ? '兩式相減' : '減去 ' + T('x')) + '，循環的部分就消掉了。';
    return { q: q, a: T(fT(val)), h: h, p: { kind: kind, ip: ip, nr: nr, rp: rp, val: fp(val) } };
  };

  /* ── 2-1 裂項相消 ── */
  function harm(k) { var s = F(0), i; for (i = 1; i <= k; i++) s = Fr.add(s, F(1, i)); return s; }
  L1.telescoping = function (r) {
    r();
    var kind = r.int(0, 2), c = r.nz(-6, 9), a, b, k, S, ex, h;
    if (c === 0) c = 1;
    if (kind === 0 || kind === 2) {
      a = r.int(1, 4); b = r.int(1 - a, 4);
      var f1 = polyT([a, b], 'n'), f2 = polyT([a, a + b], 'n'), pr = (b === 0 ? f1 : '(' + f1 + ')') + '(' + f2 + ')';
      var dT = kind === 0 ? pr : polyT([a * a, a * (a + b) + a * b, b * (a + b)], 'n');
      ex = SUMI + '\\dfrac{' + c + '}{' + dT + '}';
      S = F(c, a * (a + b));
      h = (kind === 2 ? '分母先分解：' + T(dT + '=' + pr) + '；' : '') + '裂項：' + T('\\dfrac{1}{' + pr + '}=' + (a === 1 ? '' : '\\dfrac{1}{' + a + '}') + '\\left(\\dfrac{1}{' + f1 + '}-\\dfrac{1}{' + f2 + '}\\right)') + '，部分和 ' + T('S_n') + ' 中間全部消掉。';
    } else {
      k = r.int(1, 4);
      ex = SUMI + '\\dfrac{' + c + '}{n(n+' + k + ')}';
      S = Fr.mul(F(c, k), harm(k));
      h = '裂項：' + T('\\dfrac{1}{n(n+' + k + ')}=' + (k === 1 ? '' : '\\dfrac{1}{' + k + '}') + '\\left(\\dfrac{1}{n}-\\dfrac{1}{n+' + k + '}\\right)') + '，寫出部分和後，前面剩下 ' + T(k) + ' 項沒被消掉。';
    }
    var q = '求無窮級數 ' + T(ex) + ' 的和。';
    return { q: q, a: T(fT(S)), h: h, p: { kind: kind, c: c, a: a, b: b, k: k, S: fp(S) } };
  };

  /* ── 2-2 拆成兩個無窮等比級數 ── */
  L1.geoSplit = function (r) {
    r();
    var c = r.int(3, 9), a, b, A, B, s, t = 0, S1, S2;
    do { a = r.nz(1 - c, c - 1); b = r.nz(1 - c, c - 1); t++; } while ((a === b || Math.abs(a) < 2 || Math.abs(b) < 2) && t < 50);
    A = r.pick([1, 1, 2, 3, -1, -2]); B = r.pick([1, 1, 2, -1, -2, -3]); s = r.int(-1, 1);
    function pw(base, ex) { return (base < 0 ? '(' + base + ')' : base) + '^{' + ex + '}'; }
    var t1 = (A === 1 ? '' : (A === -1 ? '-' : A + '\\cdot ')) + pw(a, 'n');
    var t2 = (B === 1 ? '' : (B === -1 ? '-' : B + '\\cdot ')) + pw(b, 'n' + (s > 0 ? '+1' : (s < 0 ? '-1' : '')));
    var numT = joinT(t1, t2);
    /* Σ A a^n/c^n = A·(a/c)/(1-a/c)；Σ B b^{n+s}/c^n = B b^s (b/c)/(1-b/c) */
    S1 = Fr.mul(A, Fr.div(F(a, c), Fr.sub(1, F(a, c))));
    S2 = Fr.mul(Fr.mul(B, s === 1 ? F(b) : (s === -1 ? F(1, b) : F(1))), Fr.div(F(b, c), Fr.sub(1, F(b, c))));
    var S = Fr.add(S1, S2);
    var q = '求無窮級數 ' + T(SUMI + '\\dfrac{' + numT + '}{' + c + '^{n}}') + ' 的和。';
    var h = '拆成兩個無窮等比級數：' + T(SUMI + cf(A) + '\\left(' + fT(F(a, c)) + '\\right)^{n}') + ' 與 ' + T(SUMI + cf(Fr.mul(B, s === 1 ? F(b) : (s === -1 ? F(1, b) : F(1)))) + '\\left(' + fT(F(b, c)) + '\\right)^{n}') + '，兩個公比的絕對值都小於 ' + T(1) + '，各自用 ' + T('\\dfrac{\\text{首項}}{1-r}') + '。';
    return { q: q, a: T(fT(S)), h: h, p: { a: a, b: b, c: c, A: A, B: B, s: s, S1: fp(S1), S2: fp(S2), S: fp(S) } };
  };

  /* ═══ §3 函數 ═══ */
  /* ── 3-1 定義域 ── */
  L1.domain = function (r) {
    r();
    var kind = r.int(0, 6), a, b, c, m, fx, S, h, lo, t = 0;
    if (kind === 0) {
      a = r.pick([1, 2, 3, -1, -2]); b = r.int(-8, 8); c = r.int(-6, 6);
      lo = F(-b, a); S = a > 0 ? ivGe(lo) : ivLe(lo); S = ivMinus(S, F(c));
      fx = '\\sqrt{' + polyT([a, b]) + '}+\\dfrac{1}{' + xm(c) + '}';
      h = '根號裡要 ' + T('\\ge 0') + '：' + T(polyT([a, b]) + '\\ge 0') + '；分母不能是 ' + T(0) + '：' + T('x\\ne ' + c) + '。兩個條件取交集。';
    } else if (kind === 1) {
      a = r.int(-6, 6); do { b = r.int(-6, 8); } while (b === a);
      S = ivMinus(ivGe(F(a)), F(b));
      fx = '\\dfrac{\\sqrt{' + xm(a) + '}}{' + xm(b) + '}';
      h = '分子的根號要 ' + T(xm(a) + '\\ge 0') + '，分母 ' + T(xm(b) + '\\ne 0') + '；檢查 ' + T('x=' + b) + ' 有沒有落在 ' + T('x\\ge ' + a) + ' 裡面。';
    } else if (kind === 2) {
      a = r.int(-6, 4); b = a + r.int(1, 7);
      S = [IV(a, b, true, true)];
      fx = r() < 0.5 ? '\\sqrt{' + pxm(a) + '(' + (b === 0 ? '-x' : b + '-x') + ')}' : '\\sqrt{' + polyT([-1, a + b, -a * b]) + '}';
      h = '根號裡要 ' + T('\\ge 0') + '：' + T(pxm(a) + '(' + (b === 0 ? '-x' : b + '-x') + ')\\ge 0') + '，也就是 ' + T(pxm(a) + pxm(b) + '\\le 0') + '，解在兩根之間（含端點）。';
    } else if (kind === 3) {
      a = r.int(-6, 4); c = a + r.int(1, 7);
      S = [IV(a, c, true, false)];
      fx = '\\dfrac{1}{\\sqrt{' + (c === 0 ? '-x' : c + '-x') + '}}+\\sqrt{' + xm(a) + '}';
      h = '分母的根號要 ' + T('\\gt 0') + '（不能等於 ' + T(0) + '）：' + T(c + '-x\\gt 0') + '；另一個根號 ' + T(xm(a) + '\\ge 0') + '。';
    } else if (kind === 4) {
      m = r.int(1, 6); b = r.int(-9, 9);
      S = ivMinus(ivMinus(ivAll(), F(-m)), F(m));
      fx = '\\dfrac{' + polyT([1, b]) + '}{x^2-' + (m * m) + '}';
      h = '分母不能是 ' + T(0) + '：' + T('x^2-' + (m * m) + '=0') + ' 的兩個根要挖掉。';
    } else if (kind === 5) {
      a = r.int(-6, 4); b = a + r.int(1, 7);
      S = [IV(null, a, false, true), IV(b, null, true, false)];
      fx = '\\sqrt{' + polyT([1, -(a + b), a * b]) + '}';
      h = '根號裡要 ' + T('\\ge 0') + '：' + T(polyT([1, -(a + b), a * b]) + '=' + pxm(a) + pxm(b) + '\\ge 0') + '，解在兩根之外（含端點）。';
    } else {
      do { a = r.int(-6, 6); b = r.int(-6, 6); } while (a === b && t++ < 30);
      if (a === b) b = a + 1;
      S = a < b ? [IV(null, a, false, true), IV(b, null, false, false)] : [IV(null, b, false, false), IV(a, null, true, false)];
      fx = '\\sqrt{\\dfrac{' + xm(a) + '}{' + xm(b) + '}}';
      h = '根號裡的分式要 ' + T('\\ge 0') + '，而且分母 ' + T(xm(b) + '\\ne 0') + '：分子是 ' + T(0) + ' 可以、分母是 ' + T(0) + ' 不行。看 ' + T(a) + '、' + T(b) + ' 把數線切成三段。';
    }
    var q = '求函數 ' + T('f(x)=' + fx) + ' 的定義域（' + T('x') + ' 為實數）。';
    return { q: q, a: T(ivFmt(S)), h: h, p: { kind: kind, a: a, b: b, c: c, m: m } };
  };

  /* ── 3-2 奇偶判斷 ── */
  L1.parity = function (r) {
    r();
    var kind = r.int(0, 11), a = r.int(1, 6), b = r.int(1, 7), c = r.nz(-5, 5), fx, lab, fv;
    switch (kind) {
      case 0: fx = polyT([1, 0, c, 0]); lab = 1; fv = function (x) { return F(x * x * x + c * x); }; break;
      case 1: fx = polyT([a, 0, -b, 0, 0, 0]); lab = 1; fv = function (x) { return F(a * Math.pow(x, 5) - b * x * x * x); }; break;
      case 2: fx = '\\dfrac{' + polyT([c, 0]) + '}{x^2+' + b + '}'; lab = 1; fv = function (x) { return F(c * x, x * x + b); }; break;
      case 3: fx = cf(c) + 'x\\left|x\\right|' + sg(a) + 'x'; lab = 1; fv = function (x) { return F(c * x * Math.abs(x) + a * x); }; break;
      case 4: fx = '\\left|' + xm(a) + '\\right|-\\left|' + xm(-a) + '\\right|'; lab = 1; fv = function (x) { return F(Math.abs(x - a) - Math.abs(x + a)); }; break;
      case 5: fx = polyT([1, 0, c, 0, b]); lab = 0; fv = function (x) { return F(Math.pow(x, 4) + c * x * x + b); }; break;
      case 6: fx = '\\dfrac{' + c + '}{x^2+' + b + '}'; lab = 0; fv = function (x) { return F(c, x * x + b); }; break;
      case 7: fx = cf(c) + '\\left|x\\right|' + sg(a) + 'x^2'; lab = 0; fv = function (x) { return F(c * Math.abs(x) + a * x * x); }; break;
      case 8: fx = '\\left|' + xm(a) + '\\right|+\\left|' + xm(-a) + '\\right|'; lab = 0; fv = function (x) { return F(Math.abs(x - a) + Math.abs(x + a)); }; break;
      case 9: fx = polyT([1, 0, c, b]); lab = 2; fv = function (x) { return F(x * x * x + c * x + b); }; break;
      case 10: fx = polyT([1, c, 0]); lab = 2; fv = function (x) { return F(x * x + c * x); }; break;
      default: fx = '\\left|' + xm(c) + '\\right|' + sg(a) + 'x^2'; lab = 2; fv = function (x) { return F(Math.abs(x - c) + a * x * x); };
    }
    var LAB = ['偶函數', '奇函數', '既不是奇函數也不是偶函數'];
    var q = '判斷 ' + T('f(x)=' + fx) + ' 是奇函數、偶函數，還是兩者都不是。';
    var tx2 = r.int(2, 3);
    var h = '把 ' + T('x') + ' 換成 ' + T('-x') + ' 算 ' + T('f(-x)') + '，再和 ' + T('f(x)') + '、' + T('-f(x)') + ' 比。先用數字試：' + T('f(' + tx2 + ')=' + fT(fv(tx2))) + '、' + T('f(-' + tx2 + ')=' + fT(fv(-tx2))) + '——但試幾個數字只能「排除」，要下結論還是得對所有 ' + T('x') + ' 比較 ' + T('f(-x)') + '。';
    return { q: q, a: LAB[lab], h: h, p: { kind: kind, a: a, b: b, c: c, lab: lab, fx: fx } };
  };

  /* ── 3-3 合成函數 ── */
  L1.compose = function (r) {
    r();
    var a = r.nz(-4, 4), b = r.int(-5, 5), c = r.int(-5, 5), d = r.int(-6, 6), k = r.int(-3, 3), ord = r.int(0, 1), lead = r.pick([1, 1, 2, -1]);
    if (a === 1 && b === 0) b = 1;
    var f = [a, b], g = [lead, c, d];
    var fT_ = polyT(f), gT_ = polyT(g);
    var v1, e2, inner;
    if (ord === 0) { inner = pval(g, F(k)); v1 = pval(f, inner); e2 = padd(padd(pmul([lead], pmul(f, f)), pmul([c], f)), [d]); }
    else { inner = pval(f, F(k)); v1 = pval(g, inner); e2 = padd(pmul([a], g), [b]); }
    var one = ord === 0 ? 'f\\circ g' : 'g\\circ f', two = ord === 0 ? 'g\\circ f' : 'f\\circ g';
    var q = '設 ' + T('f(x)=' + fT_) + '、' + T('g(x)=' + gT_) + '。' + no(1) + '求 ' + T('(' + one + ')(' + k + ')') + '。' + no(2) + '求 ' + T('(' + two + ')(x)') + '（乘開整理）。';
    var a_ = jo([no(1) + T('(' + one + ')(' + k + ')=' + fT(v1)), no(2) + T('(' + two + ')(x)=' + polyT(e2))]);
    var h = no(1) + '先算內層：' + T((ord === 0 ? 'g' : 'f') + '(' + k + ')=' + fT(inner)) + '，再代進外層 ' + T(ord === 0 ? 'f' : 'g') + '。' + no(2) + T('(' + two + ')(x)=' + (ord === 0 ? 'g(f(x))=g(' + fT_ + ')' : 'f(g(x))=f(' + gT_ + ')')) + '：把整個內層代進外層的 ' + T('x') + '。';
    return { q: q, a: a_, h: h, p: { f: f, g: g, k: k, ord: ord, inner: fp(inner), v1: fp(v1), e2: e2.map(fp) } };
  };

  /* ── 3-4 反函數 ── */
  L1.inverse = function (r) {
    r();
    var kind = r.int(0, 2), a, b, c, d, m, k, fx, gx, h, t = 0;
    m = r.int(-4, 4);
    if (kind === 0) {
      do { a = r.nz(-5, 5); } while (Math.abs(a) === 1);
      b = r.int(-8, 8);
      fx = polyT([a, b]); gx = polyT([F(1, a), F(-b, a)]); k = a * m + b;
      h = '令 ' + T('y=' + fx) + '，解出 ' + T('x=\\dfrac{y' + sg(-b) + '}{' + a + '}') + '，再把 ' + T('x') + '、' + T('y') + ' 的名字互換。';
    } else if (kind === 1) {
      do { a = r.int(-4, 4); b = r.int(-6, 6); c = r.nz(-3, 3); d = r.int(-5, 5); t++; } while ((a * d - b * c === 0 || c * m + d === 0) && t < 80);
      if (c < 0) { a = -a; b = -b; c = -c; d = -d; }
      fx = '\\dfrac{' + polyT([a, b]) + '}{' + polyT([c, d]) + '}';
      /* f^{-1}(x) = (dx-b)/(-cx+a)，分母首項化正 */
      gx = '\\dfrac{' + polyT([-d, b]) + '}{' + polyT([c, -a]) + '}';
      k = F(a * m + b, c * m + d);
      h = '令 ' + T('y=' + fx) + '：' + T('y(' + polyT([c, d]) + ')=' + polyT([a, b])) + '，把含 ' + T('x') + ' 的項移到同一邊、提出 ' + T('x') + '，最後 ' + T('x') + '、' + T('y') + ' 互換。';
    } else {
      b = r.int(-9, 9); a = r.pick([1, -1]);
      fx = polyT([a, 0, 0, b]); gx = '\\sqrt[3]{' + (a === 1 ? polyT([1, -b]) : (b === 0 ? '-x' : b + '-x')) + '}';
      k = a * m * m * m + b;
      h = '令 ' + T('y=' + fx) + '，先解出 ' + T('x^3=' + (a === 1 ? polyT([1, -b], 'y') : (b === 0 ? '-y' : b + '-y'))) + '，再開立方；' + T('x\\mapsto x^3') + ' 是一對一，所以反函數存在。';
    }
    var q = '設 ' + T('f(x)=' + fx) + '。' + no(1) + '求反函數 ' + T('f^{-1}(x)') + '。' + no(2) + '求 ' + T('f^{-1}' + ar(k)) + '。';
    var a_ = jo([no(1) + T('f^{-1}(x)=' + gx), no(2) + T('f^{-1}' + ar(k) + '=' + m)]);
    h += no(2) + '也可以不用第 (1) 小題：' + T('f^{-1}' + ar(k)) + ' 就是解 ' + T('f(x)=' + fT(k)) + '。';
    return { q: q, a: a_, h: h, p: { kind: kind, a: a, b: b, c: c, d: d, m: m, k: fp(N(k)) } };
  };

  /* ── 3-5 高斯函數求值 ── */
  function gaussItem(r, sgn) {
    var k = r.int(0, 4), v, tex, fl, lo;
    if (k === 0) { v = r.nz(-99, 99); while (v % 10 === 0) v = r.nz(-99, 99); tex = decT(F(v, 10)); fl = Math.floor(v / 10); }
    else if (k === 1) { var dd = r.int(2, 7), nn; do { nn = r.nz(-40, 40); } while (nn % dd === 0); tex = fT(F(nn, dd)); fl = Math.floor(nn / dd); }
    else if (k === 2) { var m; do { m = r.int(2, 90); } while (isq(m)); var s = r.sign(); tex = (s < 0 ? '-' : '') + '\\sqrt{' + m + '}'; lo = Math.floor(Math.sqrt(m)); while ((lo + 1) * (lo + 1) <= m) lo++; while (lo * lo > m) lo--; fl = s > 0 ? lo : -lo - 1; }
    else if (k === 3) { var c = r.pick([1, 2, 3, -1, -2]); tex = (c === 1 ? '' : (c === -1 ? '-' : c)) + '\\pi'; fl = Math.floor(c * Math.PI); }
    else { var bse = r.pick([2, 3]), mm, e; do { mm = r.int(3, 60); e = 0; var tt = 1; while (tt * bse <= mm) { tt *= bse; e++; } } while (Math.pow(bse, e) === mm); tex = '\\log_{' + bse + '}' + mm; fl = e; }
    return { tex: tex, fl: fl, k: k };
  }
  L1.gaussVal = function (r) {
    r();
    var n = r.int(2, 3), items = [], sg_ = [], i, s = '', tot = 0, hs = [];
    for (i = 0; i < n; i++) { items.push(gaussItem(r)); sg_.push(i === 0 ? 1 : r.sign()); }
    for (i = 0; i < n; i++) {
      s += (i === 0 ? '' : (sg_[i] > 0 ? '+' : '-')) + gb(items[i].tex);
      tot += sg_[i] * items[i].fl;
      hs.push(T(items[i].fl + '\\le ' + items[i].tex + '\\lt ' + (items[i].fl + 1)));
    }
    var q = '求 ' + T(s) + ' 的值' + GAUSS + '。';
    var h = '每一項先找夾住它的兩個相鄰整數：' + hs.join('、') + '。負數要特別小心：' + T('[-2.3]') + ' 是不大於 ' + T('-2.3') + ' 的最大整數，是 ' + T('-3') + '。';
    return { q: q, a: T(tot), h: h, p: { items: items, sg: sg_, ans: tot } };
  };

  /* ═══ §4 函數的極限 ═══ */
  /* ── 4-1 直接代入型 ── */
  L1.limSub = function (r) {
    r();
    var kind = r.int(0, 3), a = r.int(-4, 4), b, c, d, ex, val, h;
    if (kind === 0) {
      var cs = [r.nz(-3, 3), r.int(-6, 6), r.int(-9, 9)]; if (r() < 0.4) cs = [r.nz(-2, 2), r.int(-4, 4), r.int(-5, 5), r.int(-9, 9)];
      ex = polyT(cs); val = pval(cs, F(a));
      h = '多項式在每一點都連續 ⟹ 直接代 ' + T('x=' + a) + '：' + T(ex.replace(/x/g, '(' + a + ')')) + '。';
      return { q: '求 ' + T(LX(a) + '(' + ex + ')') + '。', a: T(fT(val)), h: h, p: { kind: kind, a: a, cs: cs } };
    }
    if (kind === 1) {
      var nm = [1, r.int(-6, 6), r.int(-9, 9)]; do { d = r.int(-6, 6); } while (a + d === 0);
      ex = '\\dfrac{' + polyT(nm) + '}{' + polyT([1, d]) + '}'; val = Fr.div(pval(nm, F(a)), F(a + d));
      h = '代 ' + T('x=' + a) + ' 時分母 ' + T(polyT([1, d]).replace(/x/g, '(' + a + ')') + '=' + (a + d) + '\\ne 0') + ' ⟹ 不是 ' + T('\\frac{0}{0}') + '，直接代入：分子是 ' + T(fT(pval(nm, F(a)))) + '。';
      return { q: '求 ' + T(LX(a) + ex) + '。', a: T(fT(val)), h: h, p: { kind: kind, a: a, nm: nm, d: d } };
    }
    if (kind === 2) {
      do { b = r.int(-8, 12); } while (a * a + b <= 0);
      c = r.nz(-4, 4); var R = a * a + b, qq = sqf(R);
      ex = '\\sqrt{' + polyT([1, 0, b]) + '}' + (c === 1 ? '+' : (c === -1 ? '-' : sg(c))) + 'x';
      if (Math.abs(c) === 1) ex = '\\sqrt{' + polyT([1, 0, b]) + '}' + (c > 0 ? '+x' : '-x');
      else ex = '\\sqrt{' + polyT([1, 0, b]) + '}' + sg(c) + 'x';
      val = qrT(F(c * a), F(qq[0]), qq[1]);
      h = '根號裡在 ' + T('x=' + a) + ' 是 ' + T(pn(a) + '^2' + sg(b) + '=' + R + '\\gt 0') + '，函數在這裡連續，直接代入。';
      return { q: '求 ' + T(LX(a) + '\\left(' + ex + '\\right)') + '。', a: T(val), h: h, p: { kind: kind, a: a, b: b, c: c } };
    }
    b = r.int(-9, 12); c = r.nz(-4, 4);
    ex = '\\left|' + polyT([1, 0, -b]) + '\\right|' + sg(c) + 'x'; val = F(Math.abs(a * a - b) + c * a);
    h = '絕對值函數是連續的 ⟹ 直接代入：' + T('\\left|' + pn(a) + '^2' + sg(-b) + '\\right|=\\left|' + (a * a - b) + '\\right|') + '。';
    return { q: '求 ' + T(LX(a) + '\\left(' + ex + '\\right)') + '。', a: T(fT(val)), h: h, p: { kind: kind, a: a, b: b, c: c } };
  };

  /* ── 4-2 0/0 型：因式分解 ── */
  L1.limFactor = function (r) {
    r();
    var kind = r.int(0, 4), a = r.nz(-5, 5), b, c, e, num, den, val = null, h, ex, t = 0;
    if (kind === 0 || kind === 4) {
      do { b = r.int(-6, 6); c = r.int(-6, 6); t++; } while ((c === a || b === c) && t < 40);
      num = pmul([1, -a], [1, -b]); den = pmul([1, -a], [1, -c]); val = F(a - b, a - c);
      ex = '\\dfrac{' + polyT(num) + '}{' + polyT(den) + '}';
      h = '代 ' + T('x=' + a) + ' 分子、分母都是 ' + T(0) + ' ⟹ 都有因式 ' + T(pxm(a)) + '：分子 ' + T('=' + pxm(a) + pxm(b)) + '、分母 ' + T('=' + pxm(a) + pxm(c)) + '，約掉再代入。';
    } else if (kind === 1) {
      var s = r.int(0, 2);
      if (s === 0) { num = [1, 0, 0, -a * a * a]; den = [1, -a]; val = F(3 * a * a); h = '分子是立方差：' + T(polyT(num) + '=' + pxm(a) + '(' + polyT([1, a, a * a]) + ')') + '，約掉 ' + T(pxm(a)) + ' 再代入。'; }
      else if (s === 1) { num = [1, 0, 0, -a * a * a]; den = [1, 0, -a * a]; val = F(3 * a, 2); h = '分子立方差、分母平方差：' + T('\\dfrac{' + pxm(a) + '(' + polyT([1, a, a * a]) + ')}{' + pxm(a) + pxm(-a) + '}') + '，約掉再代入。'; }
      else { b = r.int(2, 4); num = [1, 0, -(a * a)]; num = (function () { var p = [1], i; for (i = 0; i < b; i++) p = pmul(p, [1, 0]); p[p.length - 1] = Fr.sub(p[p.length - 1], Fr.pow(F(a), b)); return p; })(); den = [1, -a]; val = Fr.mul(b, Fr.pow(F(a), b - 1)); h = T(polyT(num) + '=' + pxm(a) + '(x^{' + (b - 1) + '}+\\cdots)') + '：用長除法或綜合除法把 ' + T(pxm(a)) + ' 除掉，商式再代 ' + T('x=' + a) + '。'; }
      ex = '\\dfrac{' + polyT(num) + '}{' + polyT(den) + '}';
    } else if (kind === 3) {
      do { e = r.int(-6, 6); } while (e === a || e === -a);
      num = pmul([1, -a], [1, -e]); den = [1, 0, -a * a]; val = F(a - e, 2 * a);
      ex = '\\dfrac{' + polyT(num) + '}{' + polyT(den) + '}';
      h = '代 ' + T('x=' + a) + ' 得 ' + T('\\frac{0}{0}') + '：分子 ' + T('=' + pxm(a) + pxm(e)) + '、分母 ' + T('=' + pxm(a) + pxm(-a)) + '。';
    } else {
      do { b = r.int(-6, 6); c = r.int(-6, 6); e = r.int(-6, 6); t++; } while ((b === a || e === a || c === a) && t < 60);
      num = pmul([1, -b], [1, -e]); den = pmul([1, -a], [1, -c]);
      ex = '\\dfrac{' + polyT(num) + '}{' + polyT(den) + '}';
      h = '先代 ' + T('x=' + a) + ' 檢查：分子 ' + T('=' + fT(pval(num, F(a)))) + '、分母 ' + T('=0') + '。這不是 ' + T('\\frac{0}{0}') + '，分子不趨近 ' + T(0) + '、分母趨近 ' + T(0) + '，商會怎樣？';
    }
    var q = '求 ' + T(LX(a) + ex) + '（若極限不存在，寫「不存在」）。';
    return { q: q, a: val === null ? '不存在' : T(fT(val)), h: h, p: { kind: kind, a: a, num: num.map(fp), den: den.map(fp), val: val === null ? null : fp(val) } };
  };

  /* ── 4-2 0/0 型：有理化 ── */
  L1.limRational = function (r) {
    r();
    var kind = r.int(0, 4), c = r.int(1, 5), a = r.int(-5, 6), b = c * c - a, p, q0, ex, val, h, e;
    if (kind === 0) { ex = '\\dfrac{\\sqrt{' + polyT([1, b]) + '}-' + c + '}{' + xm(a) + '}'; val = F(1, 2 * c); h = '分子分母同乘 ' + T('\\sqrt{' + polyT([1, b]) + '}+' + c) + '：分子變成 ' + T('(' + polyT([1, b]) + ')-' + (c * c) + '=' + xm(a)) + '，和分母約掉。'; }
    else if (kind === 1) { ex = '\\dfrac{' + xm(a) + '}{\\sqrt{' + polyT([1, b]) + '}-' + c + '}'; val = F(2 * c); h = '分子分母同乘 ' + T('\\sqrt{' + polyT([1, b]) + '}+' + c) + '：分母變成 ' + T('(' + polyT([1, b]) + ')-' + (c * c) + '=' + xm(a)) + '。'; }
    else if (kind === 2) {
      p = r.int(2, 4); q0 = c * c - p * a; ex = '\\dfrac{\\sqrt{' + polyT([p, q0]) + '}-' + c + '}{' + xm(a) + '}'; val = F(p, 2 * c);
      h = '分子分母同乘 ' + T('\\sqrt{' + polyT([p, q0]) + '}+' + c) + '：分子變成 ' + T(polyT([p, q0 - c * c]) + '=' + p + pxm(a)) + '。';
    } else if (kind === 3) {
      e = c * c - 2 * a; ex = '\\dfrac{\\sqrt{' + polyT([1, b]) + '}-\\sqrt{' + polyT([2, e]) + '}}{' + xm(a) + '}'; val = F(-1, 2 * c);
      h = '代 ' + T('x=' + a) + ' 兩個根號都是 ' + T(c) + '；分子分母同乘 ' + T('\\sqrt{' + polyT([1, b]) + '}+\\sqrt{' + polyT([2, e]) + '}') + '：分子變成 ' + T('(' + polyT([1, b]) + ')-(' + polyT([2, e]) + ')=' + polyT([-1, b - e])) + '。';
    } else {
      if (a === 0) a = 1; b = c * c - a;
      ex = '\\dfrac{' + polyT([1, 0, -a * a]) + '}{\\sqrt{' + polyT([1, b]) + '}-' + c + '}'; val = F(4 * a * c);
      h = '分母有理化：同乘 ' + T('\\sqrt{' + polyT([1, b]) + '}+' + c) + '，分母變成 ' + T(xm(a)) + '；分子 ' + T(polyT([1, 0, -a * a]) + '=' + pxm(a) + pxm(-a)) + '。';
    }
    var q = '求 ' + T(LX(a) + ex) + '。';
    return { q: q, a: T(fT(val)), h: h, p: { kind: kind, a: a, b: b, c: c, p: p, q: q0, e: e, val: fp(val) } };
  };

  /* ── 4-3 左右極限（絕對值、高斯、分段） ── */
  L1.oneSided = function (r) {
    r();
    var kind = r.int(0, 4), a = r.nz(-4, 4), fx, Rv, Lv, k, m, b, h, c1, c2, eq;
    if (kind === 0) {
      k = r.nz(-4, 4); m = r.int(-5, 5);
      fx = '\\dfrac{' + (k === 1 ? '' : (k === -1 ? '-' : k)) + '\\left|' + xm(a) + '\\right|}{' + xm(a) + '}' + sg(m);
      Rv = F(k + m); Lv = F(-k + m);
      h = T('x\\to ' + a + '^{+}') + ' 時 ' + T(xm(a) + '\\gt 0') + '，' + T('\\left|' + xm(a) + '\\right|=' + xm(a)) + '；' + T('x\\to ' + a + '^{-}') + ' 時 ' + T(xm(a) + '\\lt 0') + '，' + T('\\left|' + xm(a) + '\\right|=-' + pxm(a)) + '。';
    } else if (kind === 1) {
      fx = '\\dfrac{x^2-' + (a * a) + '}{\\left|' + xm(a) + '\\right|}';
      Rv = F(2 * a); Lv = F(-2 * a);
      h = '分子 ' + T('=' + pxm(a) + pxm(-a)) + '。右邊 ' + T('\\left|' + xm(a) + '\\right|=' + xm(a)) + '、左邊 ' + T('\\left|' + xm(a) + '\\right|=-' + pxm(a)) + '，約掉後代 ' + T('x=' + a) + '。';
    } else if (kind === 2) {
      m = r.nz(-3, 3); b = r.int(-3, 3);
      fx = (m === 1 ? '' : (m === -1 ? '-' : m)) + '[x]' + (b === 0 ? '' : (b === 1 ? '+x' : (b === -1 ? '-x' : sg(b) + 'x')));
      Rv = F(m * a + b * a); Lv = F(m * (a - 1) + b * a);
      h = T('x\\to ' + a + '^{+}') + ' 時 ' + T(a + '\\lt x\\lt ' + (a + 1)) + '，' + T('[x]=' + a) + '；' + T('x\\to ' + a + '^{-}') + ' 時 ' + T((a - 1) + '\\lt x\\lt ' + a) + '，' + T('[x]=' + (a - 1)) + '。';
    } else {
      eq = kind === 3 ? r() < 0.5 : r() < 0.3;
      var p1 = [1, r.int(-4, 4), r.int(-5, 5)], v1 = pval(p1, F(a)), s2 = r.nz(-3, 3), c2b = eq ? Fr.sub(v1, F(s2 * a)) : Fr.add(Fr.sub(v1, F(s2 * a)), F(r.nz(-4, 4)));
      var p2 = [s2, c2b];
      fx = '\\begin{cases}' + polyT(p1) + ', & x\\lt ' + a + '\\\\ ' + polyT(p2) + ', & x\\ge ' + a + '\\end{cases}';
      Rv = pval(p2, F(a)); Lv = v1; c1 = p1; c2 = p2;
      h = '右極限看 ' + T('x\\ge ' + a) + ' 那一段：代入 ' + T(polyT(p2)) + '；左極限看 ' + T('x\\lt ' + a) + ' 那一段：代入 ' + T(polyT(p1)) + '。';
    }
    var ex3 = Fr.eq(Rv, Lv);
    var q = '設 ' + T('f(x)=' + fx) + (kind === 2 ? GAUSS : '') + '。' + no(1) + '求 ' + T(LX(a, '+') + 'f(x)') + '。' + no(2) + '求 ' + T(LX(a, '-') + 'f(x)') + '。' + no(3) + T(LX(a) + 'f(x)') + ' 存在嗎？存在的話寫出它的值。';
    var a_ = jo([no(1) + T(fT(Rv)), no(2) + T(fT(Lv)), no(3) + (ex3 ? '存在，' + T(LX(a) + 'f(x)=' + fT(Rv)) : '不存在')]);
    return { q: q, a: a_, h: h, p: { kind: kind, a: a, k: k, m: m, b: b, p1: c1, p2: c2 ? c2.map(fp) : null, R: fp(Rv), L: fp(Lv) } };
  };

  /* ── 4-2 已知極限存在，反求參數 ── */
  L1.limParam = function (r) {
    r();
    var kind = r.int(0, 2), a = r.nz(-5, 5), rr, k, c, ex, L, h;
    if (kind <= 1) {
      rr = r.int(-6, 6); k = -(a + rr); c = a * rr; L = F(a - rr);
      if (c === 0) { rr = rr === 0 ? 1 : rr; k = -(a + rr); c = a * rr; L = F(a - rr); }
      ex = '\\dfrac{x^2+kx' + sg(c) + '}{' + xm(a) + '}';
      h = '分母 ' + T('\\to 0') + '，極限又存在 ⟹ 分子也要 ' + T('\\to 0') + '：代 ' + T('x=' + a) + ' 得 ' + T(pp(a) + '^2+' + pp(a) + 'k' + sg(c) + '=0') + '，先解出 ' + T('k') + '，再因式分解約掉 ' + T(pxm(a)) + '。';
      var q = '已知 ' + T(LX(a) + ex) + ' 存在。' + no(1) + '求 ' + T('k') + ' 的值。' + no(2) + '求此極限值。';
      return { q: q, a: jo([no(1) + T('k=' + k), no(2) + T(fT(L))]), h: h, p: { kind: kind, a: a, r: rr, k: k, c: c, L: fp(L) } };
    }
    c = r.int(1, 5); k = c * c - a; L = F(1, 2 * c);
    ex = '\\dfrac{\\sqrt{x+k}-' + c + '}{' + xm(a) + '}';
    h = '分母 ' + T('\\to 0') + ' 而極限存在 ⟹ 分子 ' + T('\\sqrt{' + a + '+k}-' + c + '=0') + '，得 ' + T(a + '+k=' + (c * c)) + '；再分子有理化。';
    var q2 = '已知 ' + T(LX(a) + ex) + ' 存在。' + no(1) + '求 ' + T('k') + ' 的值。' + no(2) + '求此極限值。';
    return { q: q2, a: jo([no(1) + T('k=' + k), no(2) + T(fT(L))]), h: h, p: { kind: kind, a: a, c: c, k: k, L: fp(L) } };
  };

  /* ═══ §5 連續 ═══ */
  /* ── 5-2 分段函數連續求參數 ── */
  L1.contParam = function (r) {
    r();
    var kind = r.int(0, 3), c = r.nz(-4, 4), k, fx, h, a, b, m, p;
    if (kind === 0) {
      a = r.nz(-4, 4); b = r.int(-6, 6);
      k = F(c * c + b - a * c);
      fx = '\\begin{cases}' + polyT([a, 0]) + '+k, & x\\lt ' + c + '\\\\ ' + polyT([1, 0, b]) + ', & x\\ge ' + c + '\\end{cases}';
      h = '在 ' + T('x=' + c) + ' 連續 ⟺ 左極限 ＝ 右極限 ＝ 函數值：左邊代 ' + T(polyT([a, 0]) + '+k') + ' 得 ' + T(fT(F(a * c)) + '+k') + '，右邊與 ' + T('f(' + c + ')') + ' 都是 ' + T(c * c + b) + '。';
    } else if (kind === 1) {
      p = r.int(-6, 6); var rr = -(c + p);                        /* x^2+px+q 以 c 為根：q = -c^2-pc */
      var qq = -c * c - p * c;
      k = F(2 * c + p);
      fx = '\\begin{cases}\\dfrac{' + polyT([1, p, qq]) + '}{' + xm(c) + '}, & x\\ne ' + c + '\\\\ k, & x=' + c + '\\end{cases}';
      h = '連續 ⟺ ' + T(LX(c) + 'f(x)=f(' + c + ')=k') + '。分子 ' + T(polyT([1, p, qq]) + '=' + pxm(c) + pxm(rr)) + '，約掉後代 ' + T('x=' + c) + '。';
    } else if (kind === 2) {
      m = r.int(1, 5); b = m * m - c;
      k = F(1, 2 * m);
      fx = '\\begin{cases}\\dfrac{\\sqrt{' + polyT([1, b]) + '}-' + m + '}{' + xm(c) + '}, & x\\ne ' + c + '\\\\ k, & x=' + c + '\\end{cases}';
      h = '連續 ⟺ ' + T('k=' + LX(c) + 'f(x)') + '；這是 ' + T('\\frac{0}{0}') + ' 型，分子分母同乘 ' + T('\\sqrt{' + polyT([1, b]) + '}+' + m) + '。';
    } else {
      b = r.int(-6, 6); var kv = r.nz(-3, 3);
      var rhs = 2 * c + b;
      var cst = rhs - kv * c * c;                               /* kx^2 + cst 在 c 等於 2c+b */
      k = F(kv);
      fx = '\\begin{cases}kx^2' + sg(cst) + ', & x\\lt ' + c + '\\\\ ' + polyT([2, b]) + ', & x\\ge ' + c + '\\end{cases}';
      h = '左極限 ' + T(pn(c) + '^2k' + sg(cst) + '=' + (c * c) + 'k' + sg(cst)) + '，右極限與函數值 ' + T('=' + rhs) + '，兩者相等解 ' + T('k') + '。';
    }
    var q = '設 ' + T('f(x)=' + fx) + '。若 ' + T('f') + ' 在 ' + T('x=' + c) + ' 連續，求 ' + T('k') + '。';
    return { q: q, a: T('k=' + fT(k)), h: h, p: { kind: kind, c: c, a: a, b: b, m: m, p: p, k: fp(k) } };
  };

  /* ── 5-2 高斯函數的不連續點個數 ── */
  L1.gaussDiscont = function (r) {
    r();
    var kind = r.int(0, 3), a = r.int(-4, 2), b = a + r.int(2, 5), k = r.int(2, 4), fx, cnt, h;
    if (kind === 0) { fx = '[' + k + 'x]'; cnt = k * b - k * a - 1; h = T('[' + k + 'x]') + ' 在 ' + T(k + 'x') + ' 是整數的地方跳一格：' + T(a + '\\lt x\\lt ' + b) + ' ⟹ ' + T((k * a) + '\\lt ' + k + 'x\\lt ' + (k * b)) + '，數一數這中間有幾個整數。'; }
    else if (kind === 1) { a = 0; b = r.int(2, 4); fx = '[x^2]'; cnt = b * b - 1; h = T('[x^2]') + ' 在 ' + T('x^2') + ' 是整數的地方跳一格：' + T('0\\lt x\\lt ' + b) + ' ⟹ ' + T('0\\lt x^2\\lt ' + (b * b)) + '，數一數 ' + T('x^2') + ' 能等於哪些整數。'; }
    else if (kind === 2) { fx = '[x]+[-x]'; cnt = b - a - 1; h = '當 ' + T('x') + ' 是整數時 ' + T('[x]+[-x]=0') + '；不是整數時 ' + T('[x]+[-x]=-1') + '（例如 ' + T('[0.3]+[-0.3]=0+(-1)') + '）。所以只在整數點不連續：數 ' + T(a + '\\lt x\\lt ' + b) + ' 裡的整數。'; }
    else { fx = 'x-[x]'; cnt = b - a - 1; h = T('x-[x]') + ' 是 ' + T('x') + ' 的小數部分：在每個整數點從接近 ' + T(1) + ' 掉回 ' + T(0) + '。數 ' + T(a + '\\lt x\\lt ' + b) + ' 裡的整數。'; }
    var q = '函數 ' + T('f(x)=' + fx) + GAUSS + ' 在 ' + T(a + '\\lt x\\lt ' + b) + ' 的範圍內，有幾個不連續的點？';
    return { q: q, a: T(cnt) + ' 個', h: h, p: { kind: kind, a: a, b: b, k: k, cnt: cnt } };
  };

  /* ── 5-3 勘根定理：唯一實根在哪兩個相鄰整數之間 ── */
  L1.ivtRoot = function (r) {
    r();
    var kind = r.int(0, 2), p, q0, fx, f, n, t = 0, root, vals;
    do {
      if (kind === 0) { p = r.int(1, 6); q0 = r.nz(-25, 25); f = function (x) { return x * x * x + p * x + q0; }; fx = polyT([1, 0, p, q0]); }
      else if (kind === 1) { p = r.int(1, 4); q0 = r.nz(-30, 30); f = function (x) { return x * x * x * x * x + p * x + q0; }; fx = polyT([1, 0, 0, 0, p, q0]); }
      else { p = r.int(1, 4); q0 = r.int(2, 30); f = function (x) { return Math.pow(2, x) + p * x - q0; }; fx = '2^{x}+' + (p === 1 ? '' : p) + 'x' + sg(-q0); }
      n = null;
      for (var i = -10; i < 10; i++) { if (f(i) === 0) { n = 'int'; break; } if (f(i) < 0 && f(i + 1) > 0) n = i; }
      t++;
    } while ((n === null || n === 'int') && t < 100);
    var q = '已知 ' + T('f(x)=' + fx) + ' 在實數上嚴格遞增，所以 ' + T('f(x)=0') + ' 恰有一個實根 ' + T('\\alpha') + '。找出整數 ' + T('n') + '，使得 ' + T('n\\lt\\alpha\\lt n+1') + '。';
    var a = T('n=' + n) + '（' + T(n + '\\lt\\alpha\\lt ' + (n + 1)) + '）';
    var h = '勘根定理：連續函數在兩端異號，中間就有根。先算 ' + T('f(0)=' + f(0)) + '，' + (f(0) < 0 ? '是負的，往右' : '是正的，往左') + '一個一個整數代，找到函數值變號的地方。';
    return { q: q, a: a, h: h, p: { kind: kind, p: p, q: q0, n: n } };
  };

  /* ═══ 2026-10-23 主線裁定補的三型：5-1 連續的三條件、4-4 函數版夾擠、2-4 等比應用基本型 ═══ */

  /* ── 5-1 連續的三個條件：哪一條先不成立 ── */
  var CONTLAB = function (c) {
    return ['連續', '不連續：' + T('f(' + c + ')') + ' 沒有定義', '不連續：' + T(LX(c) + 'f(x)') + ' 不存在', '不連續：極限存在但不等於 ' + T('f(' + c + ')')];
  };
  L1.contCheck = function (r) {
    r();
    var kind = r.int(0, 4), c = r.nz(-4, 4), rr, k, fx, lab, h, p1, p2, m;
    if (kind === 0) {                                   /* 補洞：函數值對或不對 */
      do { rr = r.int(-5, 5); } while (rr === c || rr === 0);
      var lim = c - rr; k = r() < 0.5 ? lim : lim + r.nz(-3, 3);
      fx = '\\begin{cases}\\dfrac{' + polyT(pmul([1, -c], [1, -rr])) + '}{' + xm(c) + '}, & x\\ne ' + c + '\\\\ ' + k + ', & x=' + c + '\\end{cases}';
      lab = k === lim ? 0 : 3;
      h = '三個條件依序檢查：' + T('f(' + c + ')=' + k) + ' 有定義；分子 ' + T('=' + pxm(c) + pxm(rr)) + '，約分後極限是 ' + T(LX(c) + '(' + xm(rr) + ')') + '；再和 ' + T(k) + ' 比。';
      return { q: '設 ' + T('f(x)=' + fx) + '。判斷 ' + T('f') + ' 在 ' + T('x=' + c) + ' 是否連續；若不連續，指出連續的三個條件（' + T('f(' + c + ')') + ' 有定義、' + T(LX(c) + 'f(x)') + ' 存在、兩者相等）中<b>第一個</b>不成立的是哪一個。', a: CONTLAB(c)[lab], h: h, p: { kind: kind, c: c, r: rr, k: k, lab: lab } };
    }
    if (kind === 1) {                                   /* 分母為 0：沒有定義 */
      do { rr = r.int(-5, 5); } while (rr === c || rr === 0);
      fx = '\\dfrac{' + polyT(pmul([1, -c], [1, -rr])) + '}{' + xm(c) + '}';
      lab = 1;
      h = '先看第一個條件：代 ' + T('x=' + c) + '，分母 ' + T(xm(c).replace(/x/g, '(' + c + ')') + '=0') + '。極限雖然存在（約分後是 ' + T(c - rr) + '），但 ' + T('f(' + c + ')') + ' 本身算不出來。';
      return { q: '設 ' + T('f(x)=' + fx) + '。判斷 ' + T('f') + ' 在 ' + T('x=' + c) + ' 是否連續；若不連續，指出連續的三個條件（' + T('f(' + c + ')') + ' 有定義、' + T(LX(c) + 'f(x)') + ' 存在、兩者相等）中<b>第一個</b>不成立的是哪一個。', a: CONTLAB(c)[lab], h: h, p: { kind: kind, c: c, r: rr, lab: lab } };
    }
    if (kind === 2 || kind === 3) {                     /* 分段：接得起來嗎 */
      p1 = [1, r.int(-4, 4), r.int(-5, 5)]; var v1 = pval(p1, F(c)), s2 = r.nz(-3, 3);
      var eq = kind === 2;
      p2 = [s2, eq ? Fr.sub(v1, F(s2 * c)) : Fr.add(Fr.sub(v1, F(s2 * c)), F(r.nz(-4, 4)))];
      fx = '\\begin{cases}' + polyT(p1) + ', & x\\lt ' + c + '\\\\ ' + polyT(p2) + ', & x\\ge ' + c + '\\end{cases}';
      lab = eq ? 0 : 2;
      h = T('f(' + c + ')') + ' 用 ' + T('x\\ge ' + c) + ' 那一段：' + T(fT(pval(p2, F(c)))) + '；左極限用 ' + T('x\\lt ' + c) + ' 那一段：' + T(fT(v1)) + '。兩段在接縫處接不接得起來？';
      return { q: '設 ' + T('f(x)=' + fx) + '。判斷 ' + T('f') + ' 在 ' + T('x=' + c) + ' 是否連續；若不連續，指出連續的三個條件（' + T('f(' + c + ')') + ' 有定義、' + T(LX(c) + 'f(x)') + ' 存在、兩者相等）中<b>第一個</b>不成立的是哪一個。', a: CONTLAB(c)[lab], h: h, p: { kind: kind, c: c, p1: p1, p2: p2.map(fp), lab: lab } };
    }
    /* 高斯：整數點跳、非整數點連續 */
    m = r.nz(-3, 3); var half = r() < 0.4, cc = half ? F(2 * c + 1, 2) : F(c);
    fx = (m === 1 ? '' : (m === -1 ? '-' : m)) + '[x]+x';
    lab = half ? 0 : 2;
    h = T('x=' + fT(cc)) + (half ? ' 不是整數：附近 ' + T('[x]') + ' 都等於 ' + T(Math.floor(Fr.num(cc))) + '，是常數' : ' 是整數：右邊 ' + T('[x]=' + c) + '、左邊 ' + T('[x]=' + (c - 1)) + '，左右極限差 ' + T(Math.abs(m))) + '。';
    var cT = fT(cc);
    var labs = ['連續', '不連續：' + T('f(' + cT + ')') + ' 沒有定義', '不連續：' + T(LX(cc) + 'f(x)') + ' 不存在', '不連續：極限存在但不等於 ' + T('f(' + cT + ')')];
    return { q: '設 ' + T('f(x)=' + fx) + GAUSS + '。判斷 ' + T('f') + ' 在 ' + T('x=' + cT) + ' 是否連續；若不連續，指出連續的三個條件（函數值有定義、極限存在、兩者相等）中<b>第一個</b>不成立的是哪一個。', a: labs[lab], h: h, p: { kind: kind, c: fp(cc), m: m, lab: lab } };
  };

  /* ── 4-4 函數版夾擠 ── */
  L1.squeezeFunc = function (r) {
    r();
    var kind = r.int(0, 2), a = r.int(-3, 3), q, ans, h;
    if (kind === 0) {
      var pp1 = r.int(-5, 5), qq = r.int(-6, 6), g2 = [1, pp1, qq], va = pval(g2, F(a)), sl = 2 * a + pp1;
      var g1 = [sl, Fr.sub(va, F(sl * a))];
      q = '函數 ' + T('f(x)') + ' 對所有實數 ' + T('x') + ' 都滿足 ' + T(polyT(g1) + '\\le f(x)\\le ' + polyT(g2)) + '，求 ' + T(LX(a) + 'f(x)') + '。';
      ans = va;
      h = '兩邊的式子在 ' + T('x=' + a) + ' 的值：左邊 ' + T(polyT(g1).replace(/x/g, '(' + a + ')') + '=' + fT(pval(g1, F(a)))) + '、右邊 ' + T(polyT(g2).replace(/x/g, '(' + a + ')') + '=' + fT(va)) + '。兩邊都連續、極限相同，就用夾擠定理。';
      return { q: q, a: T(fT(ans)), h: h, p: { kind: kind, a: a, g1: g1.map(fp), g2: g2 } };
    }
    if (kind === 1) {
      var L = r() < 0.7 ? F(r.int(-9, 9)) : F(r.nz(-9, 9), r.int(2, 5)), k = r.int(1, 5), m = r.int(1, 3);
      q = '函數 ' + T('f(x)') + ' 在 ' + T('x=' + a) + ' 附近滿足 ' + T('\\left|f(x)' + sg(Fr.neg(L)) + '\\right|\\le ' + (k === 1 ? '' : k) + '\\left|' + xm(a) + '\\right|' + (m === 1 ? '' : '^{' + m + '}')) + '，求 ' + T(LX(a) + 'f(x)') + '。';
      if (L.n === 0) q = q.replace('f(x)\\right|', 'f(x)\\right|');
      h = '拆開絕對值：' + T(fT(L) + '-' + (k === 1 ? '' : k) + '\\left|' + xm(a) + '\\right|' + (m === 1 ? '' : '^{' + m + '}') + '\\le f(x)\\le ' + fT(L) + '+' + (k === 1 ? '' : k) + '\\left|' + xm(a) + '\\right|' + (m === 1 ? '' : '^{' + m + '}')) + '；' + T('x\\to ' + a) + ' 時 ' + T('\\left|' + xm(a) + '\\right|\\to 0') + '。';
      return { q: q, a: T(fT(L)), h: h, p: { kind: kind, a: a, L: fp(L), k: k, m: m } };
    }
    var c = r.int(-6, 6), b = r.nz(-4, 4), mm = r.int(1, 3), fn = r.pick(['\\sin', '\\cos']), kk = r.int(1, 5);
    var term = (b === 1 ? '' : (b === -1 ? '-' : b)) + 'x' + (mm === 1 ? '' : '^{' + mm + '}') + fn + '\\dfrac{' + kk + '}{x}';
    q = '求 ' + T('\\lim_{x\\to 0}\\left(' + (c === 0 ? '' : c + (b > 0 ? '+' : '')) + term + '\\right)') + '。';
    h = T('-1\\le ' + fn + '\\dfrac{' + kk + '}{x}\\le 1') + ' ⟹ ' + T('\\left|' + term + '\\right|\\le ' + Math.abs(b) + '|x|' + (mm === 1 ? '' : '^{' + mm + '}')) + '，右邊在 ' + T('x\\to 0') + ' 時趨近 ' + T(0) + '；' + T(fn + '\\dfrac{' + kk + '}{x}') + ' 本身沒有極限，不能拆開用運算性質。';
    return { q: q, a: T(c), h: h, p: { kind: kind, c: c, b: b, m: mm, fn: fn, k: kk } };
  };

  /* ── 2-4 無窮等比的應用：基本型（找首項與公比） ── */
  L1.geoApply = function (r) {
    r();
    var kind = r.int(0, 3), P = r.pick([[1, 2], [1, 3], [2, 3], [3, 4], [2, 5], [3, 5], [4, 5], [1, 4]]), rv = F(P[0], P[1]), s = r.int(2, 12), q, ans, h;
    if (kind === 0) {
      q = '有無窮多個正方形，第一個邊長為 ' + T(s) + '，之後每一個的邊長都是前一個的 ' + T(fT(rv)) + ' 倍。求這些正方形的面積總和。';
      ans = fT(Fr.div(s * s, Fr.sub(1, Fr.mul(rv, rv))));
      h = '面積是邊長的平方：首項 ' + T(s + '^2=' + (s * s)) + '，公比是 ' + T('\\left(' + fT(rv) + '\\right)^2=' + fT(Fr.mul(rv, rv))) + '（不是 ' + T(fT(rv)) + '）。';
    } else if (kind === 1) {
      q = '有無窮多個圓，第一個半徑為 ' + T(s) + '，之後每一個的半徑都是前一個的 ' + T(fT(rv)) + ' 倍。求這些圓的面積總和。';
      var v = Fr.div(s * s, Fr.sub(1, Fr.mul(rv, rv)));
      ans = (v.d === 1 ? (v.n === 1 ? '' : v.n) + '\\pi' : '\\dfrac{' + v.n + '\\pi}{' + v.d + '}');
      h = '首項 ' + T('\\pi\\cdot ' + s + '^2=' + (s * s) + '\\pi') + '，面積的公比是半徑比的平方 ' + T(fT(Fr.mul(rv, rv))) + '。';
    } else if (kind === 2) {
      q = '一顆球從 ' + T(s) + ' 公尺高處落下，每次反彈的高度都是前一次落下高度的 ' + T(fT(rv)) + '，無限地彈跳下去。求這顆球每次「反彈上升」的高度總和（公尺）。';
      ans = fT(Fr.div(Fr.mul(s, rv), Fr.sub(1, rv)));
      h = '第一次反彈上升 ' + T(s + '\\times ' + fS(rv) + '=' + fT(Fr.mul(s, rv))) + '，之後每次是前一次的 ' + T(fT(rv)) + ' 倍：首項 ' + T(fT(Fr.mul(s, rv))) + '、公比 ' + T(fT(rv)) + '（只算上升，不算落下）。';
    } else {
      q = '小明第一天跑了 ' + T(s) + ' 公里，之後每天跑的距離都是前一天的 ' + T(fT(rv)) + '。如果一直這樣跑下去，他總共跑的距離會趨近多少公里？';
      ans = fT(Fr.div(s, Fr.sub(1, rv)));
      h = '每天的距離成等比：首項 ' + T(s) + '、公比 ' + T(fT(rv)) + '，' + T('|r|\\lt 1') + '，總和用 ' + T('\\dfrac{' + s + '}{1-' + fS(rv) + '}') + '。';
    }
    return { q: q, a: T(ans), h: h, p: { kind: kind, s: s, r: fp(rv) } };
  };

  /* ═══════════════════════ L2（依段考出現率排序） ═══════════════════════ */
  var L2 = {};
  var RSMALL = [[1, 2], [-1, 2], [1, 3], [-1, 3], [2, 3], [-2, 3], [1, 4], [-1, 4], [3, 4], [-3, 4], [2, 5], [-2, 5], [3, 5], [-3, 5], [1, 5], [-1, 5]];

  /* ── 2-2 含參數的無窮等比級數：收斂且和為定值 ── */
  L2.geoParamSum = function (r) {
    r();
    var kind = r.int(0, 2), P = r.pick(RSMALL), rv = F(P[0], P[1]), a, S1, S2, q, ans, h, b, x, S;
    if (kind === 0) {
      a = r.nz(-6, 6);
      S1 = Fr.div(a, Fr.sub(1, rv)); S2 = Fr.div(a * a, Fr.sub(1, Fr.mul(rv, rv)));
      q = '一個無窮等比級數的和是 ' + T(fT(S1)) + '，把它的每一項平方，所成的無窮等比級數的和是 ' + T(fT(S2)) + '。求原級數的首項 ' + T('a') + ' 與公比 ' + T('r') + '。';
      ans = T('a=' + a) + '、' + T('r=' + fT(rv));
      h = T('\\dfrac{a}{1-r}=' + fT(S1)) + '、' + T('\\dfrac{a^2}{1-r^2}=' + fT(S2)) + '；因為 ' + T('1-r^2=(1-r)(1+r)') + '，第二式除以第一式得 ' + T('\\dfrac{a}{1+r}=' + fT(Fr.div(S2, S1))) + '，和第一式聯立。';
      return { q: q, a: ans, h: h, p: { kind: kind, a: a, r: fp(rv), S1: fp(S1), S2: fp(S2) } };
    }
    if (kind === 1) {
      a = r.int(-5, 5); b = r.int(2, 6);
      S = Fr.div(1, Fr.sub(1, rv)); x = Fr.add(a, Fr.mul(b, rv));
      var rt = '\\dfrac{' + xm(a) + '}{' + b + '}';
      q = '已知無窮級數 ' + T('1+' + rt + '+\\left(' + rt + '\\right)^2+\\left(' + rt + '\\right)^3+\\cdots') + ' 收斂，且和為 ' + T(fT(S)) + '，求 ' + T('x') + '。';
      ans = T('x=' + fT(x));
      h = '首項 ' + T(1) + '、公比 ' + T('r=' + rt) + '：' + T('\\dfrac{1}{1-r}=' + fT(S)) + ' ⟹ ' + T('r=1-' + fS(Fr.div(1, S))) + '，再檢查 ' + T('|r|\\lt 1') + '，最後解 ' + T('x') + '。';
      return { q: q, a: ans, h: h, p: { kind: kind, a: a, b: b, r: fp(rv), S: fp(S), x: fp(x) } };
    }
    /* 和 S、第二項 t：r(1-r)=t/S，兩根 r 與 1-r，刪掉 |r|≥1 的 */
    S = F(r.nz(-9, 9) * rv.d * rv.d);
    var tt = Fr.mul(S, Fr.mul(rv, Fr.sub(1, rv))), r2 = Fr.sub(1, rv), rs = [rv];
    if (!Fr.eq(r2, rv) && Math.abs(Fr.num(r2)) < 1) rs.push(r2);
    rs.sort(function (u, v) { return Fr.cmp(u, v); });
    q = '一個無窮等比級數收斂，和為 ' + T(fT(S)) + '，第二項為 ' + T(fT(tt)) + '。求公比 ' + T('r') + '（所有可能的值）。';
    ans = rs.map(function (z) { return T('r=' + fT(z)); }).join(' 或 ');
    h = '首項 ' + T('a=' + fT(S) + '(1-r)') + '，第二項 ' + T('ar=' + fT(S) + 'r(1-r)=' + fT(tt)) + ' ⟹ ' + T('r^2-r' + sg(Fr.div(tt, S)) + '=0') + '；解出兩根後，<b>刪掉不滿足 ' + T('|r|\\lt 1') + ' 的</b>。';
    return { q: q, a: ans, h: h, p: { kind: kind, S: fp(S), t: fp(tt), rs: rs.map(fp) } };
  };

  /* ── 2-2 x 的無窮等比級數：收斂範圍與和函數 ── */
  L2.geoXFunc = function (r) {
    r();
    var kind = r.int(0, 2), a, b, c, d, S, q, ans, h, P, rv, k, x;
    if (kind === 0) {
      do { a = r.pick([1, 2, 3, -1, -2]); b = r.int(-5, 5); c = r.int(2, 5); } while (gcd(gcd(a, b), c) !== 1);
      var lo = F(-c - b, a), hi = F(c - b, a); if (a < 0) { var tt = lo; lo = hi; hi = tt; }
      S = [IV(lo, hi, false, false)];
      P = r.pick(RSMALL); rv = F(P[0], P[1]); k = Fr.div(rv, Fr.sub(1, rv)); x = Fr.div(Fr.sub(Fr.mul(c, rv), b), a);
      var rt = '\\dfrac{' + polyT([a, b]) + '}{' + c + '}';
      q = '設 ' + T('f(x)=' + SUMI + '\\left(' + rt + '\\right)^{n}') + '。' + no(1) + '求使 ' + T('f(x)') + ' 有意義（級數收斂）的 ' + T('x') + ' 的範圍。' + no(2) + '若 ' + T('f(x)=' + fT(k)) + '，求 ' + T('x') + '。';
      ans = jo([no(1) + T(ivFmt(S)), no(2) + T('x=' + fT(x))]);
      h = no(1) + T('\\left|' + rt + '\\right|\\lt 1') + '。' + no(2) + '收斂時 ' + T('f(x)=\\dfrac{r}{1-r}') + '（首項就是公比 ' + T('r') + '），' + T('\\dfrac{r}{1-r}=' + fT(k)) + ' ⟹ 先解 ' + T('r') + '，再解 ' + T('x') + '。';
      return { q: q, a: ans, h: h, p: { kind: kind, a: a, b: b, c: c, r: fp(rv), k: fp(k), x: fp(x) } };
    }
    if (kind === 1) {
      b = r.int(-5, 5); c = r.int(1, 4);
      do { d = r.nz(-9, 9); } while (Math.abs(d) <= c);
      S = [IV(null, b - c, false, false), IV(b + c, null, false, false)];
      var x0 = b + d, val = F(c, d - c);
      q = '設 ' + T('f(x)=' + SUMI + '\\left(\\dfrac{' + c + '}{' + xm(b) + '}\\right)^{n}') + '。' + no(1) + '求使級數收斂的 ' + T('x') + ' 的範圍。' + no(2) + '求 ' + T('f(' + x0 + ')') + '。';
      ans = jo([no(1) + T(ivFmt(S)), no(2) + T('f(' + x0 + ')=' + fT(val))]);
      h = no(1) + T('\\left|\\dfrac{' + c + '}{' + xm(b) + '}\\right|\\lt 1') + ' ⟺ ' + T('|' + xm(b) + '|\\gt ' + c) + '。' + no(2) + T('x=' + x0) + ' 時公比 ' + T('r=\\dfrac{' + c + '}{' + d + '}') + '，' + T('f=\\dfrac{r}{1-r}') + '。';
      return { q: q, a: ans, h: h, p: { kind: kind, b: b, c: c, d: d, x0: x0, val: fp(val) } };
    }
    /* m x^2 + m x^2/(k+x^2) + …：x=0 時每一項都是 0 */
    var m = r.int(1, 5), kk = r.int(1, 3), x0b = r.nz(-3, 3);
    var X2 = x0b * x0b, v0 = Fr.div(F(m * X2 * (kk + X2)), F(kk + X2 - 1));
    var t1 = (m === 1 ? '' : m) + 'x^2', den = kk === 1 ? '1+x^2' : kk + '+x^2';
    q = '設 ' + T('f(x)=' + t1 + '+\\dfrac{' + t1 + '}{' + den + '}+\\dfrac{' + t1 + '}{(' + den + ')^2}+\\dfrac{' + t1 + '}{(' + den + ')^3}+\\cdots') + '（' + T('x') + ' 為實數）。' + no(1) + '求 ' + T('f(0)') + '。' + no(2) + '求 ' + T('f(' + x0b + ')') + '。';
    ans = jo([no(1) + T('f(0)=0'), no(2) + T('f(' + x0b + ')=' + fT(v0))]);
    h = no(1) + T('x=0') + ' 時每一項都是 ' + T(0) + '（這時不能套公比公式）。' + no(2) + T('x=' + x0b) + ' 時首項 ' + T(m * X2) + '、公比 ' + T('\\dfrac{1}{' + (kk + X2) + '}') + '。';
    return { q: q, a: ans, h: h, p: { kind: kind, m: m, k: kk, x0: x0b, val: fp(v0) } };
  };

  /* ── 1-3 夾擠定理（數列）──：Σ[kα]／n²、n 次方根、n 項和 ── */
  L2.squeezeL2 = function (r) {
    r();
    var kind = r.int(0, 2), q, ans, h, b, c, a, bs, i, M;
    if (kind === 0) {
      var al = alphaPick(r); if (al.kind === 'pi') al = alphaPick(r); if (al.kind === 'pi') { al = { kind: 'sqrt', m: 2, c: 1, rr: 2, tex: '\\sqrt{2}', inT: 'n\\sqrt{2}' }; }
      b = r.int(1, 4); c = r.int(0, 5);
      var one = al.kind === 'sqrt' ? al.tex : fT(F(al.u, al.v)), kT = al.kind === 'sqrt' ? (al.c === 1 ? '' : al.c) + 'k\\sqrt{' + al.rr + '}' : '\\dfrac{' + (al.u === 1 ? '' : al.u) + 'k}{' + al.v + '}';
      var two = al.kind === 'sqrt' ? (2 * al.c) + '\\sqrt{' + al.rr + '}' : '\\dfrac{' + (2 * al.u) + '}{' + al.v + '}';
      var nn = al.inT;
      var dn = polyT([b, 0, c], 'n');
      q = '求 ' + T(LN + '\\dfrac{' + gb(one) + '+' + gb(two) + '+\\cdots+' + gb(nn) + '}{' + dn + '}') + GAUSS + '。';
      ans = al.kind === 'sqrt' ? surdT(F(al.c, 2 * b), al.rr) : fT(F(al.u, 2 * al.v * b));
      h = '每一項 ' + T(kT + '-1\\lt ' + gb(kT) + '\\le ' + kT) + '，' + T('k=1') + ' 加到 ' + T('n') + '：分子介於 ' + T(al.tex + '\\cdot\\dfrac{n(n+1)}{2}-n') + ' 與 ' + T(al.tex + '\\cdot\\dfrac{n(n+1)}{2}') + ' 之間，再同除以 ' + T(dn) + '。';
      return { q: q, a: T(ans), h: h, p: { kind: kind, al: al, b: b, c: c } };
    }
    if (kind === 1) {
      var cnt = r.int(2, 3); bs = [];
      while (bs.length < cnt) { var v = r.int(1, 9); if (bs.indexOf(v) < 0) bs.push(v); }
      M = Math.max.apply(null, bs);
      var co = bs.map(function () { return r() < 0.3 ? r.int(2, 5) : 1; });
      var inner = bs.map(function (x, j) { return (co[j] === 1 ? '' : co[j] + '\\cdot ') + x + '^{n}'; }).join('+');
      var tot = co.reduce(function (s, x) { return s + x; }, 0);
      q = '求 ' + T(LN + '\\sqrt[n]{' + inner + '}') + '。';
      ans = String(M);
      h = '最大的底是 ' + T(M) + '：' + T(M + '^{n}\\le ' + inner + '\\le ' + tot + '\\cdot ' + M + '^{n}') + '，開 ' + T('n') + ' 次方得 ' + T(M + '\\le\\sqrt[n]{\\cdots}\\le ' + M + '\\sqrt[n]{' + tot + '}') + '，而 ' + T('\\sqrt[n]{' + tot + '}\\to 1') + '。';
      return { q: q, a: T(ans), h: h, p: { kind: kind, bs: bs, co: co } };
    }
    a = r.int(1, 9); var sub = r.int(0, 1); b = r.int(1, 4);
    if (sub === 0) {
      q = '求 ' + T(LN + '\\left(\\dfrac{' + a + '}{\\sqrt{n^2+1}}+\\dfrac{' + a + '}{\\sqrt{n^2+2}}+\\cdots+\\dfrac{' + a + '}{\\sqrt{n^2+n}}\\right)') + '。';
      h = '共 ' + T('n') + ' 項，每一項介於 ' + T('\\dfrac{' + a + '}{\\sqrt{n^2+n}}') + ' 與 ' + T('\\dfrac{' + a + '}{\\sqrt{n^2+1}}') + ' 之間 ⟹ 總和介於 ' + T('\\dfrac{' + (a === 1 ? '' : a) + 'n}{\\sqrt{n^2+n}}') + ' 與 ' + T('\\dfrac{' + (a === 1 ? '' : a) + 'n}{\\sqrt{n^2+1}}') + ' 之間。';
    } else {
      var bk = b === 1 ? '' : b, an = a === 1 ? 'n' : a + 'n';
      q = '求 ' + T(LN + '\\left(\\dfrac{' + an + '}{n^2+' + bk + '1}+\\dfrac{' + an + '}{n^2+' + bk + '2}+\\cdots+\\dfrac{' + an + '}{n^2+' + bk + 'n}\\right)').replace('+' + bk + '1}', '+' + b + '}').replace('+' + bk + '2}', '+' + (2 * b) + '}') + '。';
      h = '共 ' + T('n') + ' 項，每一項介於 ' + T('\\dfrac{' + an + '}{n^2+' + bk + 'n}') + ' 與 ' + T('\\dfrac{' + an + '}{n^2+' + b + '}') + ' 之間 ⟹ 總和介於 ' + T('\\dfrac{' + (a === 1 ? '' : a) + 'n^2}{n^2+' + bk + 'n}') + ' 與 ' + T('\\dfrac{' + (a === 1 ? '' : a) + 'n^2}{n^2+' + b + '}') + ' 之間。';
    }
    return { q: q, a: T(a), h: h, p: { kind: kind, a: a, b: b, sub: sub } };
  };

  /* ── 1-2 數列極限綜合：連加的公式、根式同除 n ── */
  L2.seqLimitL2 = function (r) {
    r();
    var kind = r.int(0, 6), b = r.int(1, 5), c = r.int(1 - b, 6), q, num, den, lim, h, fmla;
    if (kind <= 5) {
      if (kind === 0) { num = '1+2+3+\\cdots+n'; den = polyT([b, 0, c], 'n'); lim = F(1, 2 * b); fmla = '1+2+\\cdots+n=\\dfrac{n(n+1)}{2}'; }
      else if (kind === 1) { num = '1^2+2^2+3^2+\\cdots+n^2'; den = polyT([b, 0, 0, c], 'n'); lim = F(1, 3 * b); fmla = '1^2+2^2+\\cdots+n^2=\\dfrac{n(n+1)(2n+1)}{6}'; }
      else if (kind === 2) { num = '1^3+2^3+3^3+\\cdots+n^3'; den = polyT([b, 0, 0, 0, c], 'n'); lim = F(1, 4 * b); fmla = '1^3+2^3+\\cdots+n^3=\\left[\\dfrac{n(n+1)}{2}\\right]^2'; }
      else if (kind === 3) { num = '1+3+5+\\cdots+(2n-1)'; den = polyT([b, 0, c], 'n'); lim = F(1, b); fmla = '1+3+\\cdots+(2n-1)=n^2'; }
      else if (kind === 4) { num = '2+4+6+\\cdots+2n'; den = polyT([b, 0, c], 'n'); lim = F(1, b); fmla = '2+4+\\cdots+2n=n(n+1)'; }
      else { num = '1\\cdot 2+2\\cdot 3+3\\cdot 4+\\cdots+n(n+1)'; den = polyT([b, 0, 0, c], 'n'); lim = F(1, 3 * b); fmla = '\\sum_{k=1}^{n}k(k+1)=\\dfrac{n(n+1)(n+2)}{3}'; }
      q = '求 ' + T(LN + '\\dfrac{' + num + '}{' + den + '}') + '。';
      h = '分子先用公式化成 ' + T('n') + ' 的多項式：' + T(fmla) + '，再和分母 ' + T(den) + ' 比最高次（同除以 ' + T('n') + ' 的最高次方）。';
      return { q: q, a: T(fT(lim)), h: h, p: { kind: kind, b: b, c: c, lim: fp(lim) } };
    }
    var s = r.int(1, 4), cc = r.nz(-4, 4), d = r.int(1, 4), e = r.int(1 - d, 5), bb = r.int(1, 9);
    if (s + cc === 0) cc = cc + 1 === 0 ? 2 : cc + 1;
    q = '求 ' + T(LN + '\\dfrac{\\sqrt{' + polyT([s * s, 0, bb], 'n') + '}' + sg(cc) + 'n}{' + polyT([d, e], 'n') + '}') + '。';
    lim = F(s + cc, d);
    h = '分子分母同除以 ' + T('n') + '：' + T('\\dfrac{\\sqrt{' + polyT([s * s, 0, bb], 'n') + '}}{n}=\\sqrt{' + (s * s) + '+\\frac{' + bb + '}{n^2}}\\to ' + s) + '。';
    return { q: q, a: T(fT(lim)), h: h, p: { kind: kind, s: s, c: cc, d: d, e: e, b: bb, lim: fp(lim) } };
  };

  /* ── 1-1 以數列極限定義的函數 ── */
  L2.limFuncDef = function (r) {
    r();
    var P = [r.nz(-4, 4), r.int(-5, 5)], Q = r() < 0.5 ? [r.nz(-3, 3), r.int(-4, 4), r.int(-5, 5)] : [r.nz(-4, 4), r.int(-5, 5)];
    var x1 = r.pick([F(1, 2), F(-1, 2), F(1, 3), F(-1, 3), F(0), F(2, 3), F(-2, 3)]), x2 = F(r.pick([2, -2, 3, -3])), x3 = F(r.pick([1, -1]));
    var v1 = pval(Q, x1), v2 = pval(P, x2), v3 = Fr.mul(F(1, 2), Fr.add(pval(P, x3), pval(Q, x3)));
    var fx = LN + '\\dfrac{' + '(' + polyT(P) + ')x^{2n}' + sg(0) + (function () { var s = polyT(Q); return s.charAt(0) === '-' ? s : '+' + s; })() + '}{x^{2n}+1}';
    var q = '設 ' + T('f(x)=' + fx) + '。求 ' + no(1) + T('f\\left(' + fT(x1) + '\\right)') + '　' + no(2) + T('f(' + fT(x2) + ')') + '　' + no(3) + T('f(' + fT(x3) + ')') + '。';
    var a = jo([no(1) + T(fT(v1)), no(2) + T(fT(v2)), no(3) + T(fT(v3))]);
    var h = '看 ' + T('|x|') + ' 和 ' + T(1) + ' 比：' + T('\\left|' + fT(x1) + '\\right|\\lt 1') + ' 時 ' + T('x^{2n}\\to 0') + '；' + T('|' + fT(x2) + '|\\gt 1') + ' 時分子分母同除以 ' + T('x^{2n}') + '；' + T('x=' + fT(x3)) + ' 時 ' + T('x^{2n}=1') + '，分母是 ' + T(2) + '。';
    return { q: q, a: a, h: h, p: { P: P, Q: Q, x1: fp(x1), x2: fp(x2), x3: fp(x3) } };
  };

  /* ── 3-3 合成函數綜合：拆解、定義域、合成的反函數 ── */
  L2.composeInv = function (r) {
    r();
    var kind = r.int(0, 2), a, b, c, d, q, ans, h;
    if (kind === 0) {
      a = r.pick([2, 3, -2, -3]); b = r.int(-4, 4);
      var L = r.pick([1, 1, 2, -1]), p = r.int(-5, 5), qq = r.int(-6, 6), g = [L, p, qq];
      var comp = padd(padd(pmul([L], pmul([a, b], [a, b])), pmul([p], [a, b])), [qq]);
      q = '設 ' + T('f(x)=' + polyT([a, b])) + '，且 ' + T('(g\\circ f)(x)=' + polyT(comp)) + '。求 ' + T('g(x)') + '。';
      ans = T('g(x)=' + polyT(g));
      h = '令 ' + T('t=' + polyT([a, b])) + '，則 ' + T('x=\\dfrac{t' + sg(-b) + '}{' + a + '}') + '；把它代進 ' + T(polyT(comp)) + '，就得到 ' + T('g(t)') + '。';
      return { q: q, a: ans, h: h, p: { kind: kind, a: a, b: b, g: g, comp: comp.map(fp) } };
    }
    if (kind === 1) {
      a = r.int(-4, 4); var m = r.int(1, 5); b = a + m * m;
      q = '設 ' + T('f(x)=\\sqrt{' + xm(a) + '}') + '、' + T('g(x)=' + b + '-x^2') + '。求 ' + no(1) + T('f\\circ g') + ' 的定義域　' + no(2) + T('g\\circ f') + ' 的定義域。';
      ans = jo([no(1) + T(ivFmt([IV(-m, m, true, true)])), no(2) + T(ivFmt(ivGe(F(a))))]);
      h = no(1) + T('(f\\circ g)(x)=\\sqrt{(' + b + '-x^2)' + sg(-a) + '}') + '：要 ' + T(b + '-x^2' + sg(-a) + '\\ge 0') + '。' + no(2) + T('(g\\circ f)(x)=' + b + '-\\left(\\sqrt{' + xm(a) + '}\\right)^2') + '：雖然化簡後像多項式，' + T('x') + ' 仍必須先在 ' + T('f') + ' 的定義域裡。';
      return { q: q, a: ans, h: h, p: { kind: kind, a: a, b: b, m: m } };
    }
    do { a = r.nz(-4, 4); } while (Math.abs(a) === 1 && r() < 0.7);
    do { c = r.nz(-4, 4); } while (Math.abs(c) === 1 && r() < 0.7);
    b = r.int(-5, 5); d = r.int(-5, 5);
    var k = r.int(-6, 6), A = a * c, Bc = a * d + b;
    var inv = polyT([F(1, A), F(-Bc, A)]), val = F(k - Bc, A);
    q = '設 ' + T('f(x)=' + polyT([a, b])) + '、' + T('g(x)=' + polyT([c, d])) + '。' + no(1) + '求 ' + T('(f\\circ g)^{-1}(x)') + '。' + no(2) + '求 ' + T('(g^{-1}\\circ f^{-1})(' + k + ')') + '。';
    ans = jo([no(1) + T('(f\\circ g)^{-1}(x)=' + inv), no(2) + T(fT(val))]);
    h = no(1) + '先合成：' + T('(f\\circ g)(x)=' + a + '(' + polyT([c, d]) + ')' + sg(b) + '=' + polyT([A, Bc])) + '，再求反函數。' + no(2) + '先算 ' + T('f^{-1}(' + k + ')') + '，再代進 ' + T('g^{-1}') + '；比一比和 ' + no(1) + ' 代 ' + T('x=' + k) + ' 的結果。';
    return { q: q, a: ans, h: h, p: { kind: kind, a: a, b: b, c: c, d: d, k: k, val: fp(val) } };
  };

  /* ── 4-2 0/0 待定係數：求兩個參數 ── */
  L2.limTwoParam = function (r) {
    r();
    var kind = r.int(0, 2), c = r.nz(-4, 4), a, b, L, q, h, ex, d, rr, m;
    if (kind === 0) {
      b = r.int(1, 6); a = b * b - c; L = F(1, 2 * b);
      ex = '\\dfrac{\\sqrt{x+a}-b}{' + xm(c) + '}';
      h = '分母 ' + T('\\to 0') + ' 而極限存在 ⟹ 分子 ' + T('\\sqrt{' + c + '+a}-b=0') + '，即 ' + T('a=b^2' + sg(-c)) + '；有理化後極限是 ' + T('\\dfrac{1}{\\sqrt{' + c + '+a}+b}=\\dfrac{1}{2b}') + '，令它等於 ' + T(fT(L)) + '。';
    } else if (kind === 1) {
      a = r.nz(-3, 3); b = r.int(-6, 6); m = -(a * c * c + b * c); L = F(2 * a * c + b);
      ex = '\\dfrac{ax^2+bx' + sg(m) + '}{' + xm(c) + '}';
      h = '分子在 ' + T('x=' + c) + ' 要等於 ' + T(0) + '：' + T(pp(c) + '^2a+' + pp(c) + 'b' + sg(m) + '=0') + '；把分子寫成 ' + T(pxm(c) + '(ax+\\cdots)') + '，約分後再代 ' + T('x=' + c) + ' 得第二條式子。';
    } else {
      do { d = r.int(-5, 5); } while (d === c);
      rr = r.int(-6, 6); a = -(c + rr); b = c * rr; L = F(c - rr, c - d);
      ex = '\\dfrac{x^2+ax+b}{' + polyT([1, -(c + d), c * d]) + '}';
      h = '分母 ' + T('=' + pxm(c) + pxm(d)) + '，在 ' + T('x=' + c) + ' 是 ' + T(0) + ' ⟹ 分子也要以 ' + T(pxm(c)) + ' 為因式：設分子 ' + T('=' + pxm(c) + '(x-s)') + '，約掉後代 ' + T('x=' + c) + ' 得 ' + T('\\dfrac{' + c + '-s}{' + (c - d) + '}=' + fT(L)) + '。';
    }
    q = '已知 ' + T(LX(c) + ex + '=' + fT(L)) + '，求實數 ' + T('a') + '、' + T('b') + '。';
    return { q: q, a: T('a=' + a) + '、' + T('b=' + b), h: h, p: { kind: kind, a: a, b: b, c: c, d: d, m: m, L: fp(L) } };
  };

  /* ── 2-1 裂項與部分和 ── */
  L2.telescopeL2 = function (r) {
    r();
    var kind = r.int(0, 5), c = r.nz(-6, 9), q, ans, h, k, S;
    if (kind === 0) { S = F(2 * c); q = '求 ' + T(SUMI + '\\dfrac{' + c + '}{1+2+3+\\cdots+n}') + '。'; h = '分母 ' + T('1+2+\\cdots+n=\\dfrac{n(n+1)}{2}') + '，一般項 ' + T('=\\dfrac{' + (2 * c) + '}{n(n+1)}=' + (2 * c) + '\\left(\\dfrac{1}{n}-\\dfrac{1}{n+1}\\right)') + '。'; }
    else if (kind === 1) { S = F(c, 4); q = '求 ' + T(SUMI + '\\dfrac{' + c + '}{n(n+1)(n+2)}') + '。'; h = '裂項：' + T('\\dfrac{1}{n(n+1)(n+2)}=\\dfrac{1}{2}\\left[\\dfrac{1}{n(n+1)}-\\dfrac{1}{(n+1)(n+2)}\\right]') + '，部分和只剩第一個括號的頭和最後一個括號的尾。'; }
    else if (kind === 2) { k = r.int(1, 3); S = Fr.mul(F(c, 2 * k), harm(2 * k)); q = '求 ' + T('\\sum_{n=' + (k + 1) + '}^{\\infty}\\dfrac{' + c + '}{n^2-' + (k * k) + '}') + '。'; h = '裂項：' + T('\\dfrac{1}{n^2-' + (k * k) + '}=\\dfrac{1}{' + (2 * k) + '}\\left(\\dfrac{1}{n-' + k + '}-\\dfrac{1}{n+' + k + '}\\right)') + '，從 ' + T('n=' + (k + 1)) + ' 寫起，前面會剩 ' + T(2 * k) + ' 項沒被消掉。'; }
    else if (kind === 3) { S = F(c); q = '求 ' + T(SUMI + '\\dfrac{' + (c === 1 ? '' : (c === -1 ? '-' : c)) + '(2n+1)}{n^2(n+1)^2}') + '。'; h = '分子 ' + T('2n+1=(n+1)^2-n^2') + ' ⟹ ' + T('\\dfrac{2n+1}{n^2(n+1)^2}=\\dfrac{1}{n^2}-\\dfrac{1}{(n+1)^2}') + '。'; }
    else if (kind === 4) {
      var A = r.nz(-5, 6), B = r.int(-5, 5), C = r.int(1, 4), Dd = r.int(1 - C, 5); if (A * Dd - B * C === 0) B += 1;
      var S1 = F(A + B, C + Dd); S = F(A, C);
      q = '無窮級數 ' + T(SUMI + 'a_n') + ' 的前 ' + T('n') + ' 項和 ' + T('S_n=\\dfrac{' + polyT([A, B], 'n') + '}{' + polyT([C, Dd], 'n') + '}') + '。' + no(1) + '求 ' + T('a_1') + '。' + no(2) + '求 ' + T(SUMI + 'a_n') + '。';
      ans = jo([no(1) + T('a_1=' + fT(S1)), no(2) + T(fT(S))]);
      h = no(1) + T('a_1=S_1') + '：把 ' + T('n=1') + ' 代進 ' + T('S_n=\\dfrac{' + polyT([A, B], 'n') + '}{' + polyT([C, Dd], 'n') + '}') + '。' + no(2) + '級數的和就是 ' + T(LN + 'S_n') + '：分子分母同除以 ' + T('n') + '。';
      return { q: q, a: ans, h: h, p: { kind: kind, A: A, B: B, C: C, D: Dd } };
    } else {
      var sub = r.int(0, 1);
      if (sub === 0) { q = '判斷 ' + T(SUMI + '\\dfrac{' + c + '}{\\sqrt{n}+\\sqrt{n+1}}') + ' 是否收斂；若收斂，求其和。'; h = '有理化：' + T('\\dfrac{1}{\\sqrt{n}+\\sqrt{n+1}}=\\sqrt{n+1}-\\sqrt{n}') + '，部分和 ' + T('S_n=' + c + '(\\sqrt{n+1}-1)') + '，看它有沒有極限。'; }
      else { var bb = r.pick([2, 3, 10]); q = '判斷 ' + T(SUMI + (c === 1 ? '' : (c === -1 ? '-' : c)) + '\\log_{' + bb + '}\\dfrac{n+1}{n}') + ' 是否收斂；若收斂，求其和。'; h = T('\\log_{' + bb + '}\\dfrac{n+1}{n}=\\log_{' + bb + '}(n+1)-\\log_{' + bb + '}n') + '，部分和 ' + T('S_n=' + cf(c) + '\\log_{' + bb + '}(n+1)') + '，看它有沒有極限。'; }
      return { q: q, a: '發散', h: h, p: { kind: kind, c: c, sub: sub } };
    }
    return { q: q, a: T(fT(S)), h: h, p: { kind: kind, c: c, k: k, S: fp(S) } };
  };

  /* ── 5-2 分段函數連續：求兩個參數 ── */
  L2.contTwoParam = function (r) {
    r();
    var kind = r.int(0, 2), a, b, q, h, fx, p, qq, k, c0, e;
    if (kind <= 1) {
      p = r.nz(-3, 2); do { qq = p + r.int(1, 3); } while (qq === 0);
      a = r.nz(-5, 5); b = r.nz(-4, 4); k = r.int(-4, 4);
      c0 = p * p + a * p - b * p; e = b * qq + c0 - qq * qq - k * qq;
      fx = '\\begin{cases}x^2+ax, & x\\lt ' + p + '\\\\ bx' + sg(c0) + ', & ' + p + '\\le x\\lt ' + qq + '\\\\ ' + polyT([1, k, e]) + ', & x\\ge ' + qq + '\\end{cases}';
      h = '只要檢查兩個接點：在 ' + T('x=' + p) + '，左邊 ' + T(pp(p) + '^2+' + pp(p) + 'a') + ' 要等於右邊 ' + T(pp(p) + 'b' + sg(c0)) + '；在 ' + T('x=' + qq) + '，' + T(pp(qq) + 'b' + sg(c0)) + ' 要等於 ' + T(fT(pval([1, k, e], F(qq)))) + '。先由第二個接點解 ' + T('b') + '。';
    } else {
      p = r.nz(-4, 4); k = r.int(-6, 6); a = k - 2 * p; b = -p * p - a * p;
      fx = '\\begin{cases}\\dfrac{x^2+ax+b}{' + xm(p) + '}, & x\\ne ' + p + '\\\\ ' + k + ', & x=' + p + '\\end{cases}';
      h = '在 ' + T('x=' + p) + ' 連續 ⟹ ' + T(LX(p) + 'f(x)=' + k) + '：分母 ' + T('\\to 0') + '，所以分子 ' + T(pp(p) + '^2+' + pp(p) + 'a+b=0') + '；分子 ' + T('=' + pxm(p) + '(x-s)') + '，極限 ' + T(p + '-s=' + k) + '。';
    }
    q = '設 ' + T('f(x)=' + fx) + '。若 ' + T('f') + ' 在所有實數都連續，求 ' + T('a') + '、' + T('b') + '。';
    return { q: q, a: T('a=' + a) + '、' + T('b=' + b), h: h, p: { kind: kind, a: a, b: b, p: p, q: qq, k: k, c0: c0, e: e } };
  };

  /* ── 3-4 反函數綜合 ── */
  L2.inverseL2 = function (r) {
    r();
    var kind = r.int(0, 2), k, m, s, v, q, ans, h, a, b, d, t;
    if (kind === 0) {
      k = r.int(-3, 3); m = r.int(-6, 6); s = r.int(1, 5); v = s * s + m - k * k;
      var fx = polyT([1, -2 * k, m]), inside = polyT([1, k * k - m]);
      q = '設 ' + T('f(x)=' + fx) + '，定義域 ' + T('x\\ge ' + k) + '。' + no(1) + '求反函數 ' + T('f^{-1}(x)') + '（寫出定義域）。' + no(2) + '求 ' + T('f^{-1}(' + v + ')') + '。';
      ans = jo([no(1) + T('f^{-1}(x)=' + (k === 0 ? '' : k + '+') + '\\sqrt{' + inside + '}') + '，' + T('x\\ge ' + (m - k * k)), no(2) + T(k + s)]);
      h = no(1) + '配方：' + T('y=' + (k === 0 ? 'x^2' : '(' + xm(k) + ')^2') + sg(m - k * k)) + '，因為 ' + T('x\\ge ' + k) + '，開根號取正：' + T(xm(k) + '=\\sqrt{y' + sg(k * k - m) + '}') + '；值域 ' + T('y\\ge ' + (m - k * k)) + ' 就是反函數的定義域。' + no(2) + '解 ' + T('f(x)=' + v) + '（' + T('x\\ge ' + k) + '）。';
      return { q: q, a: ans, h: h, p: { kind: kind, k: k, m: m, s: s, v: v } };
    }
    if (kind === 1) {
      a = r.nz(-5, 5); do { b = r.int(-8, 8); } while (b === -a * a);
      m = r.int(-4, 4); while (m === a) m = r.int(-4, 4);                 /* d=-a，分母 x-a 在 m 不為 0 */
      var val = F(a * m + b, m - a);
      q = '設 ' + T('f(x)=\\dfrac{' + polyT([a, b]) + '}{x+d}') + '。若 ' + T('f^{-1}(x)=f(x)') + '（對定義域內的 ' + T('x') + ' 都成立），求 ' + no(1) + T('d') + '　' + no(2) + T('f^{-1}\\left(' + fT(val) + '\\right)') + '。';
      ans = jo([no(1) + T('d=' + (-a)), no(2) + T(m)]);
      h = no(1) + '先求 ' + T('f^{-1}(x)=\\dfrac{-dx' + sg(b) + '}{x' + sg(-a) + '}') + '，和 ' + T('f(x)') + ' 比對係數。' + no(2) + T('f^{-1}=f') + '，所以 ' + T('f^{-1}\\left(' + fT(val) + '\\right)') + ' 就是 ' + T('f\\left(' + fT(val) + '\\right)') + '；也可以解 ' + T('f(x)=' + fT(val)) + '。';
      return { q: q, a: ans, h: h, p: { kind: kind, a: a, b: b, m: m } };
    }
    a = r.pick([F(2), F(3), F(4), F(1, 2), F(1, 3), F(3, 2), F(2, 3)]); t = r.nz(-6, 6);
    b = Fr.mul(Fr.sub(1, a), t);
    q = '設 ' + T('f(x)=' + polyT([a, b])) + '。求 ' + T('y=f(x)') + ' 與 ' + T('y=f^{-1}(x)') + ' 兩圖形的交點坐標。';
    ans = T('(' + t + ',' + t + ')');
    h = T('f') + ' 是遞增函數，' + T('y=f(x)') + ' 與 ' + T('y=f^{-1}(x)') + ' 對 ' + T('y=x') + ' 對稱，交點落在 ' + T('y=x') + ' 上：解 ' + T(polyT([a, b]) + '=x') + '。';
    return { q: q, a: ans, h: h, p: { kind: kind, a: fp(a), b: fp(b), t: t } };
  };

  /* ── 4-3 絕對值、高斯函數的極限 ── */
  L2.limAbsGauss = function (r) {
    r();
    var kind = r.int(0, 3), a = r.nz(-4, 4), q, ans, h, rr, Rv, Lv, k, m, fx;
    if (kind === 0 || kind === 3) {
      if (kind === 0) {
        do { rr = r.int(-5, 5); } while (rr === a);
        fx = '\\dfrac{' + polyT(pmul([1, -a], [1, -rr])) + '}{\\left|' + xm(a) + '\\right|}';
        Rv = F(a - rr); Lv = F(rr - a);
        h = '分子 ' + T('=' + pxm(a) + pxm(rr)) + '；' + T('x\\to ' + a + '^{+}') + ' 時 ' + T('\\left|' + xm(a) + '\\right|=' + xm(a)) + '，' + T('x\\to ' + a + '^{-}') + ' 時 ' + T('\\left|' + xm(a) + '\\right|=-' + pxm(a)) + '。';
      } else {
        fx = '\\dfrac{\\left|x^2-' + (a * a) + '\\right|}{' + xm(a) + '}';
        Rv = F(2 * Math.abs(a)); Lv = F(-2 * Math.abs(a));
        h = T('x^2-' + (a * a) + '=' + pxm(a) + pxm(-a)) + '；在 ' + T('x=' + a) + ' 附近 ' + T(xm(-a)) + ' 的正負號固定（接近 ' + T(2 * a) + '），' + T(xm(a)) + ' 的正負號左右相反。';
      }
      q = '設 ' + T('f(x)=' + fx) + '。' + no(1) + '求 ' + T(LX(a, '+') + 'f(x)') + '。' + no(2) + '求 ' + T(LX(a, '-') + 'f(x)') + '。' + no(3) + T(LX(a) + 'f(x)') + ' 存在嗎？';
      ans = jo([no(1) + T(fT(Rv)), no(2) + T(fT(Lv)), no(3) + '不存在']);
      return { q: q, a: ans, h: h, p: { kind: kind, a: a, r: rr } };
    }
    if (kind === 1) {
      k = r.int(-5, 5);
      fx = '[x]+[' + (k === 0 ? '-x' : k + '-x') + ']';
      q = '設 ' + T('f(x)=' + fx) + GAUSS + '。' + no(1) + '求 ' + T(LX(a) + 'f(x)') + '。' + no(2) + '求 ' + T('f(' + a + ')') + '。' + no(3) + T('f') + ' 在 ' + T('x=' + a) + ' 連續嗎？';
      ans = jo([no(1) + T(k - 1), no(2) + T(k), no(3) + '不連續']);
      h = T('x\\to ' + a + '^{+}') + '：' + T('[x]=' + a) + '、' + T(k === 0 ? '-x' : k + '-x') + ' 略小於 ' + T(k - a) + '，所以 ' + T('[' + (k === 0 ? '-x' : k + '-x') + ']=' + (k - a - 1)) + '；左極限同樣分開算。' + T('x=' + a) + ' 本身兩個中括號裡都是整數。';
      return { q: q, a: ans, h: h, p: { kind: kind, a: a, k: k } };
    }
    k = r.nz(-9, 9); m = r.nz(-4, 4);
    fx = (m === 1 ? '' : (m === -1 ? '-' : m)) + 'x\\left[\\dfrac{' + k + '}{x}\\right]';
    q = '求 ' + T('\\lim_{x\\to 0}' + fx) + GAUSS + '。';
    ans = T(fT(F(m * k)));
    h = T('\\dfrac{' + k + '}{x}-1\\lt\\left[\\dfrac{' + k + '}{x}\\right]\\le\\dfrac{' + k + '}{x}') + '：' + T('x\\gt 0') + ' 時乘 ' + T('x') + ' 不變號，' + T('x\\lt 0') + ' 時要變號；兩種情形都得到 ' + T(k + '-x') + ' 與 ' + T(k) + ' 夾住 ' + T('x\\left[\\dfrac{' + k + '}{x}\\right]') + '。';
    return { q: q, a: ans, h: h, p: { kind: kind, k: k, m: m } };
  };

  /* ── 3-5 高斯函數方程式與不等式 ── */
  L2.gaussEq = function (r) {
    r();
    var kind = r.int(0, 2), q, S, h, a, b, k, m1, m2, t = 0, rel;
    if (kind === 0) {
      a = r.pick([2, 3, -2, -3, 4]); b = r.int(-5, 5); k = r.int(-6, 6);
      var lo = F(k - b, a), hi = F(k + 1 - b, a);
      S = a > 0 ? [IV(lo, hi, true, false)] : [IV(hi, lo, false, true)];
      q = '解方程式 ' + T('[' + polyT([a, b]) + ']=' + k) + GAUSS + '。';
      h = T('[t]=' + k) + ' ⟺ ' + T(k + '\\le t\\lt ' + (k + 1)) + '：' + T(k + '\\le ' + polyT([a, b]) + '\\lt ' + (k + 1)) + (a < 0 ? '，除以負數 ' + T(a) + ' 不等號要反向' : '') + '。';
      return { q: q, a: T(ivFmt(S)), h: h, p: { kind: kind, a: a, b: b, k: k } };
    }
    do { m1 = r.int(-5, 5); m2 = r.int(-5, 5); t++; } while (Math.abs(m1 - m2) < 2 && t < 50);
    if (m1 > m2) { t = m1; m1 = m2; m2 = t; }
    var pT = polyT([1, -(m1 + m2), m1 * m2]).replace(/x/g, '[x]');
    if (kind === 1) {
      S = [IV(m1, m1 + 1, true, false), IV(m2, m2 + 1, true, false)];
      q = '解方程式 ' + T(pT + '=0') + GAUSS + '。';
      h = '把 ' + T('[x]') + ' 當成一個未知數 ' + T('t') + '：' + T(polyT([1, -(m1 + m2), m1 * m2], 't') + '=' + pxm(m1, 't') + pxm(m2, 't') + '=0') + '，' + T('t') + ' 是整數；再由 ' + T('[x]=t') + ' 得 ' + T('t\\le x\\lt t+1') + '。';
    } else {
      rel = r() < 0.5 ? '\\lt ' : '\\le ';
      S = rel === '\\lt ' ? [IV(m1 + 1, m2, true, false)] : [IV(m1, m2 + 1, true, false)];
      q = '解不等式 ' + T(pT + rel + '0') + GAUSS + '。';
      h = '令 ' + T('t=[x]') + '：' + T(pxm(m1, 't') + pxm(m2, 't') + rel + '0') + ' ⟹ ' + T(m1 + (rel === '\\lt ' ? '\\lt ' : '\\le ') + 't' + rel + m2) + '，而 ' + T('t') + ' 只能是整數；再把每個 ' + T('t') + ' 換回 ' + T('x') + ' 的範圍。';
    }
    return { q: q, a: T(ivFmt(S)), h: h, p: { kind: kind, m1: m1, m2: m2, rel: rel } };
  };

  /* ── 2-3 循環小數綜合 ── */
  function repVal(ip, nr, rp) { var k = nr.length, m = rp.length; return Fr.add(F(ip), Fr.add(F(nr === '' ? 0 : parseInt(nr, 10), Math.pow(10, k)), Fr.mul(F(parseInt(rp, 10), Math.pow(10, k)), F(1, Math.pow(10, m) - 1)))); }
  L2.repDecOps = function (r) {
    r();
    var kind = r.int(0, 2), q, ans, h;
    if (kind === 0) {
      var r1, r2, n1 = '', t = 0;
      do { r1 = digs(r, r.int(1, 2)); r2 = digs(r, r.int(1, 2)); n1 = r() < 0.4 ? digs(r, 1) : ''; t++; }
      while ((!minPeriod(r1) || !minPeriod(r2) || /^[09]+$/.test(r1) || /^[09]+$/.test(r2) || (n1 !== '' && n1.charAt(0) === r1.charAt(r1.length - 1))) && t < 80);
      var x1 = repVal(0, n1, r1), x2 = repVal(0, '', r2), op = r.pick(['+', '-', '\\times ']), v;
      v = op === '+' ? Fr.add(x1, x2) : (op === '-' ? Fr.sub(x1, x2) : Fr.mul(x1, x2));
      q = '計算 ' + T('0.' + n1 + '\\overline{' + r1 + '}' + op + '0.\\overline{' + r2 + '}') + '，答案寫成最簡分數。';
      ans = T(fT(v));
      h = '先各自化成分數：' + T('0.\\overline{' + r2 + '}=\\dfrac{' + parseInt(r2, 10) + '}{' + ('9'.repeat(r2.length)) + '}') + '；' + T('0.' + n1 + '\\overline{' + r1 + '}') + ' 也用「乘 ' + T(10) + ' 的次方再相減」化成分數，再計算。';
      return { q: q, a: ans, h: h, p: { kind: kind, n1: n1, r1: r1, r2: r2, op: op } };
    }
    if (kind === 1) {
      var qd = r.pick([7, 13, 27, 37, 41, 11, 21, 33]), p, digits = '', rem, i, L;
      do { p = r.int(1, qd - 1); } while (gcd(p, qd) !== 1);
      rem = p; for (i = 0; i < 60; i++) { rem *= 10; digits += Math.floor(rem / qd); rem = rem % qd; }
      L = 1; rem = 10 % qd; while (rem !== 1) { rem = (rem * 10) % qd; L++; }
      var per = digits.slice(0, L), Nn = r.int(20, 200), dig = per.charAt((Nn - 1) % L);
      q = '把 ' + T('\\dfrac{' + p + '}{' + qd + '}') + ' 化成循環小數，' + no(1) + '寫出它的循環小數表示法；' + no(2) + '小數點後第 ' + T(Nn) + ' 位數字是多少？';
      ans = jo([no(1) + T('0.\\overline{' + per + '}'), no(2) + T(dig)]);
      h = no(1) + '用長除法：' + T(p + '\\div ' + qd) + '，餘數第一次重複時開始循環，循環節長 ' + T(L) + '。' + no(2) + T(Nn + '=' + L + '\\times ' + Math.floor((Nn - 1) / L) + '+' + ((Nn - 1) % L + 1)) + '，看循環節的第幾位。';
      return { q: q, a: ans, h: h, p: { kind: kind, p: p, q: qd, per: per, N: Nn } };
    }
    var ip = r.int(0, 5), nr = r() < 0.7 ? digs(r, r.int(1, 2)) : '';
    while (nr !== '' && /9$/.test(nr)) nr = digs(r, nr.length);
    var x = ip + '.' + nr + '\\overline{9}', val = repVal(ip, nr, '9');
    q = '把 ' + T(x) + ' 化成最簡分數（或整數）。';
    ans = T(fT(val));
    h = '設 ' + T('x=' + x) + '，' + T('10x') + ' 與 ' + T('x') + (nr === '' ? '' : '（先各乘 ' + T(Math.pow(10, nr.length)) + '）') + ' 相減把 ' + T('\\overline{9}') + ' 消掉——結果會是一個有限小數，就像 ' + T('0.\\overline{9}=1') + '。';
    return { q: q, a: ans, h: h, p: { kind: kind, ip: ip, nr: nr } };
  };

  /* ── 1-4 遞迴數列：極限與一般項 ── */
  L2.recurL2 = function (r) {
    r();
    var kind = r.int(0, 2), q, ans, h, L, k, m, s, a2, qq;
    if (kind === 0) {
      L = r.int(2, 6); k = r.int(1, L - 1); m = L * L - k * L;
      do { s = r.int(0, L + 4); } while (s === L);
      qq = sqf(k * s + m); a2 = surdT(F(qq[0]), qq[1]);
      q = '數列 ' + T('\\langle a_n\\rangle') + ' 滿足 ' + T('a_1=' + s) + '、' + T('a_{n+1}=\\sqrt{' + (k === 1 ? '' : k) + 'a_n+' + m + '}') + '。' + no(1) + '求 ' + T('a_2') + '。' + no(2) + '若此數列收斂，求 ' + T(LN + 'a_n') + '。';
      ans = jo([no(1) + T('a_2=' + a2), no(2) + T(L)]);
      h = no(2) + '令 ' + T(LN + 'a_n=L') + '：' + T('L=\\sqrt{' + (k === 1 ? '' : k) + 'L+' + m + '}') + ' ⟹ ' + T('L^2-' + (k === 1 ? '' : k) + 'L-' + m + '=0') + '；每一項都是根號開出來的，' + T('L\\ge 0') + '，負根要刪掉。';
      return { q: q, a: ans, h: h, p: { kind: kind, s: s, k: k, m: m, L: L } };
    }
    if (kind === 1) {
      var P = r.pick(RSMALL), p = F(P[0], P[1]), a1; L = r.int(-5, 5); qq = Fr.mul(L, Fr.sub(1, p));
      do { a1 = r.int(-5, 8); } while (a1 === L);
      var cc = a1 - L;
      var gen = (L === 0 ? '' : L) + (cc < 0 ? '-' : (L === 0 ? '' : '+')) + (Math.abs(cc) === 1 ? '' : Math.abs(cc)) + '\\left(' + fT(p) + '\\right)^{n-1}';
      q = '數列 ' + T('\\langle a_n\\rangle') + ' 滿足 ' + T('a_1=' + a1) + '、' + T('a_{n+1}=' + cf(p) + 'a_n' + sg(qq)) + '。' + no(1) + '求一般項 ' + T('a_n') + '。' + no(2) + '求 ' + T(LN + 'a_n') + '。';
      ans = jo([no(1) + T('a_n=' + gen), no(2) + T(L)]);
      h = '先找「不動點」' + T('L=' + cf(p) + 'L' + sg(qq)) + ' ⟹ ' + T('L=' + L) + '；兩式相減得 ' + T('a_{n+1}-' + pn(L) + '=' + fS(p) + '(a_n-' + pn(L) + ')') + '，' + T('\\langle a_n-' + pn(L) + '\\rangle') + ' 是等比數列。';
      return { q: q, a: ans, h: h, p: { kind: kind, p: fp(p), q: fp(qq), a1: a1, L: L } };
    }
    var u = r.int(1, 6); k = r.int(1, 4);
    q = '數列 ' + T('\\langle a_n\\rangle') + ' 滿足 ' + T('a_1=' + u) + '、' + T('a_{n+1}=\\dfrac{a_n}{' + (k === 1 ? '' : k) + 'a_n+1}') + '。' + no(1) + '求一般項 ' + T('a_n') + '。' + no(2) + '求 ' + T(LN + 'a_n') + '。';
    ans = jo([no(1) + T('a_n=\\dfrac{' + u + '}{' + polyT([k * u, 1 - k * u], 'n') + '}'), no(2) + T(0)]);
    h = '取倒數：' + T('\\dfrac{1}{a_{n+1}}=\\dfrac{' + (k === 1 ? '' : k) + 'a_n+1}{a_n}=\\dfrac{1}{a_n}+' + k) + ' ⟹ ' + T('\\left\\langle\\dfrac{1}{a_n}\\right\\rangle') + ' 是首項 ' + T('\\dfrac{1}{' + u + '}') + '、公差 ' + T(k) + ' 的等差數列。';
    return { q: q, a: ans, h: h, p: { kind: kind, u: u, k: k } };
  };

  /* ── 2-4 應用：無窮多個相似圖形、彈跳球 ── */
  L2.similarArea = function (r) {
    r();
    var kind = r.int(0, 2), s = r.int(2, 10), what = r.int(0, 1), q, ans, h;
    if (kind === 0) {
      q = '正方形的邊長為 ' + T(s) + '。連接它四邊的中點得到第二個正方形，再連接第二個正方形四邊的中點得到第三個正方形，如此無限地做下去。求所有正方形的' + (what === 0 ? '面積' : '周長') + '總和。';
      ans = what === 0 ? T(2 * s * s) : T(qrT(F(8 * s), F(4 * s), 2));
      h = '新正方形的邊長是舊的 ' + T('\\dfrac{\\sqrt{2}}{2}') + ' 倍（半邊長 ' + T(fT(F(s, 2))) + ' 的兩股所成斜邊）⟹ ' + (what === 0 ? '面積的公比是 ' + T('\\dfrac{1}{2}') + '，首項 ' + T(s * s) : '周長的公比是 ' + T('\\dfrac{\\sqrt{2}}{2}') + '，首項 ' + T(4 * s)) + '。';
    } else if (kind === 1) {
      q = '正三角形的邊長為 ' + T(s) + '。連接它三邊的中點得到第二個正三角形，再連接第二個正三角形三邊的中點得到第三個正三角形，如此無限地做下去。求所有正三角形的' + (what === 0 ? '面積' : '周長') + '總和。';
      ans = what === 0 ? T(surdT(F(s * s, 3), 3)) : T(6 * s);
      h = '中點連線是對邊的一半 ⟹ 邊長公比 ' + T('\\dfrac{1}{2}') + '：' + (what === 0 ? '面積公比 ' + T('\\dfrac{1}{4}') + '，首項 ' + T('\\dfrac{\\sqrt{3}}{4}\\cdot ' + s + '^2') : '周長公比 ' + T('\\dfrac{1}{2}') + '，首項 ' + T(3 * s)) + '。';
    } else {
      var P = r.pick([[1, 2], [1, 3], [2, 3], [3, 4], [2, 5], [3, 5], [4, 5]]), rv = F(P[0], P[1]), H = r.pick([5, 6, 8, 9, 10, 12, 15, 20, 24, 30]);
      q = '一顆球從 ' + T(H) + ' 公尺高的地方自由落下，每次著地後反彈的高度是它落下高度的 ' + T(fT(rv)) + '，如此無限地彈跳下去。求這顆球經過的總路徑長（公尺）。';
      ans = T(fT(Fr.div(Fr.mul(H, Fr.add(1, rv)), Fr.sub(1, rv))));
      h = '第一次只有落下 ' + T(H) + '；之後每次反彈都「上去再下來」走兩趟：' + T('2\\left(' + H + '\\cdot ' + fS(rv) + '+' + H + '\\cdot ' + fS(Fr.mul(rv, rv)) + '+\\cdots\\right)') + '。';
      return { q: q, a: ans, h: h, p: { kind: kind, H: H, r: fp(rv) } };
    }
    return { q: q, a: ans, h: h, p: { kind: kind, s: s, what: what } };
  };

  /* ── 2-4 應用：輪流擲骰，先成功者勝 ── */
  var EVT = [
    { act: '擲一顆公正骰子', c: '擲出 $6$ 點', p: [1, 6] }, { act: '擲一顆公正骰子', c: '擲出 $1$ 點', p: [1, 6] },
    { act: '擲一顆公正骰子', c: '擲出偶數點', p: [1, 2] }, { act: '擲一顆公正骰子', c: '擲出奇數點', p: [1, 2] },
    { act: '擲一顆公正骰子', c: '點數大於 $4$', p: [1, 3] }, { act: '擲一顆公正骰子', c: '點數小於 $3$', p: [1, 3] },
    { act: '擲一顆公正骰子', c: '點數是 $3$ 的倍數', p: [1, 3] }, { act: '擲一顆公正骰子', c: '點數大於 $2$', p: [2, 3] },
    { act: '擲一顆公正骰子', c: '擲出質數點', p: [1, 2] },
    { act: '擲兩顆公正骰子', c: '點數和為 $7$', p: [1, 6] }, { act: '擲兩顆公正骰子', c: '兩顆點數相同', p: [1, 6] },
    { act: '擲兩顆公正骰子', c: '點數和為 $5$', p: [1, 9] }, { act: '擲兩顆公正骰子', c: '點數和大於 $9$', p: [1, 6] },
    { act: '擲兩顆公正骰子', c: '點數和為 $8$', p: [5, 36] }, { act: '擲兩枚公正硬幣', c: '兩枚都出現正面', p: [1, 4] }
  ];
  L2.firstSuccess = function (r) {
    r();
    var np = r.int(2, 3), same = r() < 0.4, names = ['甲', '乙', '丙'], ev = [], i, who = r.int(0, np - 1), q;
    var e0 = r.pick(EVT);
    for (i = 0; i < np; i++) ev.push(same ? e0 : r.pick(EVT));
    var ps = ev.map(function (e) { return F(e.p[0], e.p[1]); });
    var fail = F(1); ps.forEach(function (p) { fail = Fr.mul(fail, Fr.sub(1, p)); });
    var pre = F(1); for (i = 0; i < who; i++) pre = Fr.mul(pre, Fr.sub(1, ps[i]));
    var ans = Fr.div(Fr.mul(pre, ps[who]), Fr.sub(1, fail));
    var nm = names.slice(0, np).join('、');
    if (same) q = nm + '輪流' + e0.act + '，依 ' + names.slice(0, np).join('→') + '→' + names[0] + '→⋯ 的順序進行，最先成功（' + e0.c + '）的人獲勝，遊戲結束。求' + names[who] + '獲勝的機率。';
    else {
      q = nm + '依 ' + names.slice(0, np).join('→') + '→' + names[0] + '→⋯ 的順序輪流進行：';
      for (i = 0; i < np; i++) q += '輪到' + names[i] + '時，' + names[i] + ev[i].act + '，若' + ev[i].c + '，' + names[i] + '就獲勝' + (i < np - 1 ? '；' : '。');
      q += '有人獲勝遊戲就結束。求' + names[who] + '獲勝的機率。';
    }
    var h = '每人每次成功的機率：' + ev.map(function (e, j) { return names[j] + ' ' + T(fT(ps[j])); }).join('、') + '。一輪全部失敗的機率 ' + T(fT(fail)) + '；' + names[who] + '在第一輪獲勝的機率是 ' + T(fT(Fr.mul(pre, ps[who]))) + '，之後每多一輪就乘一次 ' + T(fT(fail)) + '，是無窮等比級數。';
    return { q: q, a: T(fT(ans)), h: h, p: { np: np, same: same, ev: ev.map(function (e) { return EVT.indexOf(e); }), who: who } };
  };

  /* ── 5-3 介值定理：根的個數下界、根所在的區間 ── */
  L2.ivtCount = function (r) {
    r();
    var kind = r.int(0, 1), q, ans, h, i, t = 0;
    if (kind === 0) {
      var x0 = r.int(-3, 0), vals = [], cnt;
      do { vals = []; for (i = 0; i < 6; i++) vals.push(r.nz(-9, 9)); cnt = 0; for (i = 0; i < 5; i++) if (vals[i] * vals[i + 1] < 0) cnt++; t++; } while ((cnt === 0 || cnt === 5) && t < 50);
      var xs = []; for (i = 0; i < 6; i++) xs.push(x0 + i);
      q = '連續函數 ' + T('f(x)') + ' 的部分函數值如下表：' + T('\\begin{array}{c|cccccc}x&' + xs.join('&') + '\\\\ \\hline f(x)&' + vals.join('&') + '\\end{array}') + '。由勘根定理，方程式 ' + T('f(x)=0') + ' 在 ' + T(x0 + '\\le x\\le ' + (x0 + 5)) + ' 之間<b>至少</b>有幾個實根？';
      ans = T(cnt) + ' 個';
      h = '一格一格看相鄰兩個函數值有沒有變號：' + T('f(' + xs[0] + ')=' + vals[0]) + '、' + T('f(' + xs[1] + ')=' + vals[1]) + ' …每變號一次，那一段就至少有一個根。';
      return { q: q, a: ans, h: h, p: { kind: kind, x0: x0, vals: vals } };
    }
    var b, c, d, f, ch;
    do {
      b = r.int(-4, 4); c = r.int(-14, 4); d = r.int(-12, 12);
      f = function (x) { return x * x * x + b * x * x + c * x + d; };
      ch = []; var zero = false;
      for (i = -7; i < 7; i++) { if (f(i) === 0) zero = true; if (f(i) * f(i + 1) < 0) ch.push(i); }
      if (f(7) === 0) zero = true;
      t++;
    } while ((zero || ch.length !== 3) && t < 400);
    if (ch.length !== 3) { b = 0; c = -7; d = 3; f = function (x) { return x * x * x - 7 * x + 3; }; ch = [-3, 0, 2]; }
    q = '三次方程式 ' + T(polyT([1, b, c, d]) + '=0') + ' 有三個實根。利用勘根定理，找出每一個根分別落在哪兩個相鄰整數之間。';
    ans = ch.map(function (n) { return T(n + '\\lt x\\lt ' + (n + 1)); }).join('、');
    h = '令 ' + T('f(x)=' + polyT([1, b, c, d])) + '，從 ' + T('f(0)=' + d) + ' 開始往兩邊代整數，例如 ' + T('f(1)=' + f(1)) + '、' + T('f(-1)=' + f(-1)) + '，找出所有變號的相鄰整數；三次方程式最多三個根，找到三段就夠了。';
    return { q: q, a: ans, h: h, p: { kind: kind, b: b, c: c, d: d, ch: ch } };
  };

  /* ══════════════════════════════════════════════════════════
     L3　中上（15 型）：每型對應固定題 L3-1～L3-15 的「類似題」（frag_L3_12a1.html）
     同題型換數字，答案一律精確；p 放輸入參數（驗算器 verify_l0l3_12a1.py 不讀 p，從題幹重算）。
     每型開頭先丟掉一次 r()：連號種子的 LCG 首值幾乎相同。
     ══════════════════════════════════════════════════════════ */
  var L3 = {};
  function l3exp(e) { return 'n' + (e > 0 ? '+' + e : (e < 0 ? String(e) : '')); }
  function l3term(coef, baseT, e) { return (coef === 1 ? '' : (coef === -1 ? '-' : coef + (baseT.charAt(0) === '(' ? '' : '\\cdot '))) + baseT + '^{' + l3exp(e) + '}'; }
  function l3join(a, b) { return b.charAt(0) === '-' ? a + b : a + '+' + b; }

  /* L3-1 負底數的指數型 */
  L3.expNeg = function (r) {
    r();
    var p, q, A, B, C, Dd, s1, s2, s3, s4, ok, n, t = 0;
    do {
      p = r.int(2, 6); q = r.int(p + 1, 8); A = r.pick([1, 1, 2, 3, -1]); B = r.pick([1, 2, -1, 3]); C = r.pick([1, 1, 2, -1]); Dd = r.pick([1, 2, -1, 3]);
      s1 = r.int(-2, 2); s2 = r.int(-1, 3); s3 = r.int(-2, 2); s4 = r.int(-1, 3);
      ok = true; for (n = 1; n <= 10; n++) if (C * Math.pow(p, n + s3) + Dd * Math.pow(-q, n + s4) === 0) ok = false;
    } while ((!ok || s2 === s4 && B === Dd) && t++ < 50);
    var nq = '(-' + q + ')';
    var num = l3join(l3term(A, String(p), s1), l3term(B, nq, s2)), den = l3join(l3term(C, String(p), s3), l3term(Dd, nq, s4));
    var lim = Fr.mul(F(B, Dd), Fr.pow(F(-q), Math.max(s2 - s4, 0)));
    if (s2 < s4) lim = Fr.div(F(B, Dd), Fr.pow(F(-q), s4 - s2));
    var qq = '求 ' + T(LN + '\\dfrac{' + num + '}{' + den + '}') + '。';
    var h = '絕對值最大的底是 ' + T('-' + q) + '：分子分母同除以 ' + T(nq + '^{n}') + '（連負號一起除），' + T('\\left(\\dfrac{' + p + '}{-' + q + '}\\right)^{n}\\to 0') + '；剩下 ' + T(nq + '^{' + s2 + '}') + ' 與 ' + T(nq + '^{' + s4 + '}') + ' 這種常數。';
    return { q: qq, a: T(fT(lim)), h: h, p: { p: p, q: q, A: A, B: B, C: C, D: Dd, s: [s1, s2, s3, s4], lim: fp(lim) } };
  };

  /* L3-2 連加公式除以 n^m 再減 an：一次項要被抵消 */
  var L3SUM = [
    { t: '1+2+3+\\cdots+n', c: [F(1, 2), F(1, 2), F(0)], m: 1 },
    { t: '1^2+2^2+3^2+\\cdots+n^2', c: [F(1, 3), F(1, 2), F(1, 6), F(0)], m: 2 },
    { t: '1^3+2^3+3^3+\\cdots+n^3', c: [F(1, 4), F(1, 2), F(1, 4), F(0), F(0)], m: 3 },
    { t: '1+3+5+\\cdots+(2n-1)', c: [F(1), F(0), F(0)], m: 1 },
    { t: '1\\cdot 2+2\\cdot 3+\\cdots+n(n+1)', c: [F(1, 3), F(1), F(2, 3), F(0)], m: 2 }
  ];
  L3.sumMinusAn = function (r) {
    r();
    var S = r.pick(L3SUM), c = r.int(1, 4), d = r.int(-3, 3), m = S.m;
    var den = [c, d]; for (var i = 1; i < m; i++) den.push(0);
    var al = Fr.div(S.c[0], c), be = Fr.div(Fr.sub(S.c[1], Fr.mul(al, d)), c);
    var q = '已知實數 ' + T('a') + '、' + T('b') + ' 滿足 ' + T(LN + '\\left(\\dfrac{' + S.t + '}{' + polyT(den, 'n') + '}-an\\right)=b') + '，求數對 ' + T('(a,b)') + '。';
    var h = '分子先用公式寫成 ' + T('n') + ' 的多項式，再除以 ' + T(polyT(den, 'n')) + '（長除法）寫成「' + T('pn+q') + '＋趨近 ' + T(0) + ' 的項」；' + T('pn') + ' 必須被 ' + T('an') + ' 抵消，所以 ' + T('a=p') + '，剩下的常數就是 ' + T('b') + '。';
    return { q: q, a: T('(a,b)=\\left(' + fT(al) + ',' + fT(be) + '\\right)'), h: h, p: { t: S.t, c: c, d: d, a: fp(al), b: fp(be) } };
  };

  /* L3-3 由一串不等式夾出 lim b_n */
  L3.squeezeIneq = function (r) {
    r();
    var c = r.int(1, 2), k = c + r.int(1, 3), t = r.nz(-4, 4), p = t * (k - c), qq = r.nz(-5, 5), L = k * t;
    var left = (c === 1 ? '' : c) + 'b_n+\\dfrac{' + polyT([p, qq], 'n') + '}{n}';
    var q = '已知對任意正整數 ' + T('n') + '，不等式 ' + T(left + '\\le a_n\\le ' + k + 'b_n') + ' 恆成立，且 ' + T(LN + 'a_n=' + L) + '，求 ' + T(LN + 'b_n') + '。';
    var h = '把 ' + T('b_n') + ' 單獨夾在中間：右半邊得 ' + T('b_n\\ge\\dfrac{a_n}{' + k + '}') + '，左半邊得 ' + T('b_n\\le ' + (c === 1 ? '' : '\\dfrac{1}{' + c + '}') + '\\left(a_n-\\dfrac{' + polyT([p, qq], 'n') + '}{n}\\right)') + '；兩邊的極限都算算看。';
    return { q: q, a: T(t), h: h, p: { c: c, k: k, p: p, q: qq, L: L, t: t } };
  };

  /* L3-4 ⟨r^n⟩ 收斂，r 是含 x 的分式：-1 < r ≤ 1 */
  function l3lf(u1, u0, v1, v0, op) {        /* (u1 x+u0)/(v1 x+v0) op 0；op: 'le' 或 'gt' */
    var z = F(-u0, u1), w = F(-v0, v1), lo, hi, zlo, pos = u1 * v1 > 0;
    if (Fr.cmp(z, w) < 0) { lo = z; hi = w; zlo = true; } else { lo = w; hi = z; zlo = false; }
    var eqz = op === 'le';
    var between = (op === 'le') === pos;          /* 商 ≤0 在兩根之間（首項同號時）；>0 在兩根之外 */
    if (between) return [IV(lo, hi, zlo && eqz, !zlo && eqz)];
    return [IV(null, lo, false, zlo && eqz), IV(hi, null, !zlo && eqz, false)];
  }
  L3.rnConvX = function (r) {
    r();
    var a, b, c, d, t = 0, S;
    do {
      a = r.nz(-4, 4); b = r.int(-4, 4); c = r.nz(-3, 3); d = r.int(-4, 4); t++;
      S = null;
      if (a * d - b * c !== 0 && a !== c && a !== -c) {
        S = ivInter(l3lf(a - c, b - d, c, d, 'le'), l3lf(a + c, b + d, c, d, 'gt'));
        S.forEach(function (I) { if (I.lo && I.hi && Fr.eq(I.lo, I.hi)) S = null; });
        if (S && !S.length) S = null;
      }
    } while (!S && t < 200);
    var rt = '\\dfrac{' + polyT([a, b]) + '}{' + polyT([c, d]) + '}';
    var q = '若無窮數列 ' + T('\\left\\langle\\left(' + rt + '\\right)^{n}\\right\\rangle') + ' 收斂，求實數 ' + T('x') + ' 的範圍。';
    var h = T('\\langle r^n\\rangle') + ' 收斂 ⟺ ' + T('-1\\lt r\\le 1') + '（' + T('r=1') + ' 每項都是 ' + T(1) + '，可以取等號）。拆成兩個分式不等式：' + T(rt + '\\le 1') + ' 與 ' + T(rt + '\\gt -1') + '，移項通分後看分子分母的正負，最後取交集。';
    return { q: q, a: T(ivFmt(S)), h: h, p: { a: a, b: b, c: c, d: d } };
  };

  /* L3-5 一般項含部分和 S_n＝等比和 */
  L3.sumSnGeo = function (r) {
    r();
    var p = r.int(2, 5), qd = r.int(p + 1, 9), c = r.pick([1, 1, 2, 3]);
    var Sn = c === 1 ? '1+' + p + '+' + p + '^2+\\cdots+' + p + '^{n-1}' : c + '+' + c + '\\cdot ' + p + '+' + c + '\\cdot ' + p + '^2+\\cdots+' + c + '\\cdot ' + p + '^{n-1}';
    var ans = Fr.mul(F(c, p - 1), Fr.sub(F(p, qd - p), F(1, qd - 1)));
    var q = '已知 ' + T('S_n=' + Sn) + '，求無窮級數 ' + T(SUMI + '\\dfrac{S_n}{' + qd + '^{n}}') + '。';
    var h = '先把 ' + T('S_n') + ' 用等比求和寫成封閉式：' + T('S_n=' + (p === 2 ? (c === 1 ? '2^n-1' : c + '(2^n-1)') : '\\dfrac{' + (c === 1 ? '' : c) + '(' + p + '^n-1)}{' + (p - 1) + '}')) + '，一般項拆成 ' + T('\\left(\\dfrac{' + p + '}{' + qd + '}\\right)^n') + ' 與 ' + T('\\left(\\dfrac{1}{' + qd + '}\\right)^n') + ' 兩個等比級數。';
    return { q: q, a: T(fT(ans)), h: h, p: { p: p, q: qd, c: c, ans: fp(ans) } };
  };

  /* L3-6 由 S_n 求等差的一般項，再裂項 */
  L3.snTelescope = function (r) {
    r();
    var al = r.int(1, 3), be = r.int(1 - al, 6), k = r.int(1, 2), d = 2 * al, s = F(0), j;
    for (j = 1; j <= k; j++) s = Fr.add(s, F(1, d * j + be - al));
    var ans = Fr.mul(F(1, k * d), s);
    var q = '數列 ' + T('\\langle a_n\\rangle') + ' 的前 ' + T('n') + ' 項和 ' + T('S_n=' + polyT([al, be, 0], 'n')) + '，求 ' + T(SUMI + '\\dfrac{1}{a_n\\cdot a_{n+' + k + '}}') + '。';
    var h = T('a_1=S_1=' + (al + be)) + '，' + T('n\\ge 2') + ' 時 ' + T('a_n=S_n-S_{n-1}') + '，得公差 ' + T(d) + ' 的等差數列；再裂項 ' + T('\\dfrac{1}{a_na_{n+' + k + '}}=\\dfrac{1}{' + (k * d) + '}\\left(\\dfrac{1}{a_n}-\\dfrac{1}{a_{n+' + k + '}}\\right)') + (k === 2 ? '，中間隔一項，前面留下兩項' : '') + '。';
    return { q: q, a: T(fT(ans)), h: h, p: { al: al, be: be, k: k, ans: fp(ans) } };
  };

  /* L3-7 首項、第二項是循環小數的無窮等比級數 */
  function l3rep(f) {                          /* 0<f<1 的分數 → {nr, rp}（不循環部分、循環節），不是無限循環或太長就回傳 null */
    var seen = {}, digs = '', rem = f.n % f.d, i;
    for (i = 0; i < 12; i++) {
      if (rem === 0) return null;
      if (seen[rem] !== undefined) { var k = seen[rem]; return { nr: digs.slice(0, k), rp: digs.slice(k) }; }
      seen[rem] = i; rem *= 10; digs += Math.floor(rem / f.d); rem = rem % f.d;
    }
    return null;
  }
  L3.geoRepDec = function (r) {
    r();
    var x1, x2, rv, R1, R2, t = 0;
    do {
      var nr = r() < 0.5 ? String(r.int(0, 9)) : '', rp = String(r.int(1, 98));
      if (rp.length === 1 && r() < 0.5) rp = '0' + rp;
      R1 = { nr: nr, rp: rp };
      x1 = repVal(0, nr, rp);
      rv = r.pick([F(1, 2), F(1, 3), F(1, 4), F(2, 5), F(1, 5), F(2, 3), F(3, 10), F(1, 6)]);
      x2 = Fr.mul(x1, rv); R2 = l3rep(x2); R1 = l3rep(x1); t++;
    } while ((!R1 || !R2 || R1.rp.length > 3 || R2.rp.length > 3 || R1.nr.length > 2 || R2.nr.length > 3 || x1.n === 0) && t < 200);
    var s1 = '0.' + R1.nr + '\\overline{' + R1.rp + '}', s2 = '0.' + R2.nr + '\\overline{' + R2.rp + '}';
    var S = Fr.div(x1, Fr.sub(1, rv));
    var q = '設無窮等比級數的首項為 ' + T(s1) + '，第二項為 ' + T(s2) + '，求此級數的和。';
    var h = '先把兩個循環小數化成分數：' + T(s1 + '=' + fT(x1)) + '；第二項同樣化成分數，公比 ' + T('r=\\dfrac{\\text{第二項}}{\\text{首項}}') + '，確認 ' + T('|r|\\lt 1') + ' 再用 ' + T('\\dfrac{a}{1-r}') + '。';
    return { q: q, a: T(fT(S)), h: h, p: { x1: fp(x1), x2: fp(x2), r: fp(rv), S: fp(S) } };
  };

  /* L3-8 一般項是「n 的一次式乘等比」：錯位相減 */
  L3.nGeo = function (r) {
    r();
    var P = r.pick([[1, 2], [1, 3], [1, 4], [1, 5], [2, 3], [3, 4], [2, 5], [-1, 2], [-1, 3]]), x = F(P[0], P[1]), al = r.int(1, 3), be = r.int(-2, 3);
    var one = Fr.sub(1, x), ans = Fr.add(Fr.div(Fr.mul(al, x), Fr.mul(one, one)), Fr.div(Fr.mul(be, x), one));
    var lin = polyT([al, be], 'n'), ex;
    if (P[0] === 1) ex = '\\dfrac{' + lin + '}{' + P[1] + '^{n}}';
    else ex = (be === 0 ? lin : '(' + lin + ')') + '\\left(' + fT(x) + '\\right)^{n}';
    var q = '求 ' + T(SUMI + ex) + '。';
    var h = '令部分和 ' + T('S_N') + '，算 ' + T('S_N-' + pn(x) + 'S_N') + '：錯開一位相減後，' + T('n') + ' 的係數部分變成公比 ' + T(fT(x)) + ' 的普通等比級數；也可以拆成 ' + T((al === 1 ? '' : al) + '\\sum n\\left(' + fT(x) + '\\right)^n') + (be === 0 ? '' : ' 與 ' + T(be + '\\sum\\left(' + fT(x) + '\\right)^n')) + '。';
    return { q: q, a: T(fT(ans)), h: h, p: { x: fp(x), al: al, be: be, ans: fp(ans) } };
  };

  /* L3-9 由 f(x+s) 還原 f，再求 f∘g 的定義域 */
  L3.composeDomain = function (r) {
    r();
    var s, e, m, p, qq, t = 0, x1, x2;
    do { s = r.pick([1, 2, -1, 3, -2]); e = r.int(-4, 4); m = r.int(-3, 4); p = r.int(-5, 5); qq = r.int(-5, 5); t++; }
    while ((m === 1 || e === -m || p === qq) && t < 100);
    x1 = F(-qq); x2 = F(m * qq - p, 1 - m);
    var top = polyT([1, s + e]), bot = (m - s === 0 ? '-x' : (m - s) + '-x');
    var q = '設 ' + T('f(x' + sg(s) + ')=\\dfrac{' + top + '}{' + bot + '}') + '，' + T('g(x)=\\dfrac{' + polyT([1, p]) + '}{' + polyT([1, qq]) + '}') + '，求 ' + T('f\\circ g') + ' 的定義域。';
    var ex = [x1, x2].sort(function (u, v) { return Fr.cmp(u, v); });
    var a = '所有實數，但 ' + T('x\\ne ' + fT(ex[0])) + ' 且 ' + T('x\\ne ' + fT(ex[1]));
    var h = '令 ' + T('t=x' + sg(s)) + ' 還原出 ' + T('f(t)') + '，它要求 ' + T('t\\ne ' + m) + '；' + T('f\\circ g') + ' 要「' + T('g(x)') + ' 有意義（' + T('x\\ne ' + (-qq)) + '）」而且「' + T('g(x)\\ne ' + m) + '」。';
    return { q: q, a: a, h: h, p: { s: s, e: e, m: m, p: p, q: qq } };
  };

  /* L3-10 哪一個函數的值域包含最多個正整數 */
  function l3range(r, L, U) {
    var k = r.int(0, 6), c, d, f, lo, hi, tex, disc = false, sq;
    if (k === 0) { tex = 'x+\\left|x\\right|'; lo = F(L < 0 ? 0 : 2 * L); hi = F(2 * U); }
    else if (k === 1) { c = r.int(L, U); tex = '\\left|' + xm(c) + '\\right|'; lo = F(0); hi = F(Math.max(Math.abs(L - c), Math.abs(U - c))); }
    else if (k === 2) { c = r.int(L, U); d = r.int(-3, 2); tex = (c === 0 ? 'x^2' : '(' + xm(c) + ')^2') + sg(d); lo = F(d); hi = F(Math.max((L - c) * (L - c), (U - c) * (U - c)) + d); }
    else if (k === 3) { c = r.int(L, U); d = r.int(-3, 3); tex = (c === 0 ? 'x^3' : '(' + xm(c) + ')^3') + sg(d); lo = F(Math.pow(L - c, 3) + d); hi = F(Math.pow(U - c, 3) + d); }
    else if (k === 4) { tex = '2^{x}'; lo = L >= 0 ? F(Math.pow(2, L)) : F(1, Math.pow(2, -L)); hi = F(Math.pow(2, U)); }
    else if (k === 5) { tex = '[x]'; disc = true; lo = F(L); hi = F(U); }
    else { c = r.nz(-3, 3); d = r.int(-4, 4); tex = polyT([c, d]); var v1 = c * L + d, v2 = c * U + d; lo = F(Math.min(v1, v2)); hi = F(Math.max(v1, v2)); }
    var lo1 = Math.max(1, Math.ceil(Fr.num(lo) - 1e-12)), cnt = Math.max(0, Math.floor(Fr.num(hi) + 1e-12) - lo1 + 1);
    return { k: k, tex: tex, cnt: cnt, lo: lo, hi: hi };
  }
  L3.rangeCount = function (r) {
    r();
    var L, U, fs, i, best, t = 0, cnts;
    do {
      L = r.int(-3, 0); U = r.int(2, 5); fs = []; var used = {};
      while (fs.length < 5) { var f = l3range(r, L, U); if (used[f.tex]) continue; used[f.tex] = 1; fs.push(f); }
      cnts = fs.map(function (f) { return f.cnt; }); best = Math.max.apply(null, cnts); t++;
    } while (cnts.filter(function (c) { return c === best; }).length !== 1 && t < 100);
    var ans = cnts.indexOf(best) + 1;
    var opts = fs.map(function (f, j) { return no(j + 1) + T('f_' + (j + 1) + '(x)=' + f.tex); }).join('　');
    var q = '設 ' + T(L + '\\le x\\le ' + U) + '，下列哪一個函數的值域包含最多個正整數？' + GAUSS + '<br>' + opts;
    var h = '每個函數先求它在 ' + T(L + '\\le x\\le ' + U) + ' 的值域（單調的看端點；絕對值、平方要看轉折點；高斯函數只取整數值），例如 ' + T('f_1') + ' 的值域' + (fs[0].k === 5 ? '是 ' + T(L) + ' 到 ' + T(U) + ' 的整數' : '從 ' + T(fT(fs[0].lo)) + ' 到 ' + T(fT(fs[0].hi))) + '，再數裡面有幾個正整數。';
    return { q: q, a: no(ans).trim(), h: h, p: { L: L, U: U, ks: fs.map(function (f) { return f.k; }), cnts: cnts } };
  };

  /* L3-11 高斯符號在整數點的左右極限 */
  function l3dec(v10) { return v10 % 10 === 0 ? String(v10 / 10) : decT(F(v10, 10)); }
  L3.gaussSides = function (r) {
    r();
    var c = r.int(-3, 4), al = r.pick([5, 15, 25, -5, -15, 3, 7, 12, -25, 10, 20, -10]), be = r.pick([0, 10, 20, 30, 40, 25, 15, 35, -10, 5]);
    /* 單位：十分之一。右極限：[c+α+ε]=floor(c+α)；[β-c-ε]：β-c 是整數就減 1 */
    function fl(v10) { return Math.floor(v10 / 10); }
    var A = 10 * c + al, Bv = be - 10 * c;
    var Ra = fl(A) + (Bv % 10 === 0 ? Bv / 10 - 1 : fl(Bv)), La = (A % 10 === 0 ? A / 10 - 1 : fl(A)) + fl(Bv);
    var inner1 = 'x' + (al > 0 ? '+' : '-') + l3dec(Math.abs(al)), inner2 = (be === 0 ? '' : l3dec(be)) + '-x';
    var q = T('[x]') + ' 表示不大於 ' + T('x') + ' 的最大整數。已知 ' + T('f(x)=[' + inner1 + ']+[' + inner2 + ']') + '，且 ' + T(LX(c, '+') + 'f(x)=a') + '、' + T(LX(c, '-') + 'f(x)=b') + '，求數對 ' + T('(a,b)') + '。';
    var h = '右極限：' + T('x') + ' 比 ' + T(c) + ' 大一點點，' + T(inner1) + ' 比 ' + T(l3dec(A)) + ' 大一點點、' + T(inner2) + ' 比 ' + T(l3dec(Bv)) + ' 小一點點；左極限反過來。整數加減一點點時高斯值會不會掉一格要特別小心。';
    return { q: q, a: T('(a,b)=(' + Ra + ',' + La + ')'), h: h, p: { c: c, al: al, be: be, R: Ra, L: La } };
  };

  /* L3-12 兩個極限條件決定三次多項式 */
  L3.polyTwoLimits = function (r) {
    r();
    var p, q0, k, m, s, t = 0;
    do { p = r.int(-3, 3); q0 = r.int(-3, 4); k = r.nz(-3, 3); m = r.int(-4, 4); s = r.nz(-3, 3); t++; } while ((p === q0 || s === p || s === q0) && t < 100);
    var A = (p - q0) * (k * p + m), B = (q0 - p) * (k * q0 + m);
    var fs = (s - p) * (s - q0) * (k * s + m), V = F(fs, s);
    var q = '三次多項式 ' + T('f(x)') + ' 滿足 ' + T(LX(p) + '\\dfrac{f(x)}{' + xm(p) + '}=' + A) + '、' + T(LX(q0) + '\\dfrac{f(x)}{' + xm(q0) + '}=' + B) + '，求 ' + T(LX(s) + '\\dfrac{f(x)}{x}') + '。';
    var h = '分母趨近 ' + T(0) + '、極限存在 ⟹ ' + T('f(' + p + ')=0') + '、' + T('f(' + q0 + ')=0') + '，設 ' + T('f(x)=' + pxm(p) + pxm(q0) + '(kx+m)') + '；約分後代入：' + T('(' + p + sg(-q0) + ')(' + p + 'k+m)=' + A) + '，另一式同理，解 ' + T('k') + '、' + T('m') + '。';
    return { q: q, a: T(fT(V)), h: h, p: { p: p, q: q0, k: k, m: m, s: s } };
  };

  /* L3-13 0/0 型的極限值已知，反求兩個參數 */
  L3.limMN = function (r) {
    r();
    var c, rr, n, t = 0;
    do { c = r.nz(-4, 4); rr = r.int(-6, 6); n = r.int(-6, 6); t++; } while ((rr === c || n === c) && t < 100);
    var m = c + rr, e = c * rr, L = F(c - rr, c - n);
    var den = 'x^2-(n' + sg(c) + ')x' + (c > 0 ? '+' + (c === 1 ? '' : c) + 'n' : '-' + (c === -1 ? '' : -c) + 'n');
    var q = '若 ' + T(LX(c) + '\\dfrac{x^2-mx' + sg(e) + '}{' + den + '}=' + fT(L)) + '，求數對 ' + T('(m,n)') + '。';
    var h = '分母 ' + T('=' + pxm(c) + '(x-n)') + '，在 ' + T('x=' + c) + ' 是 ' + T(0) + ' ⟹ 分子在 ' + T('x=' + c) + ' 也要是 ' + T(0) + '：' + T(pp(c) + '^2-' + pp(c) + 'm' + sg(e) + '=0') + ' 先解 ' + T('m') + '；約掉 ' + T(pxm(c)) + ' 再代 ' + T('x=' + c) + ' 解 ' + T('n') + '。';
    return { q: q, a: T('(m,n)=(' + m + ',' + n + ')'), h: h, p: { c: c, r: rr, n: n, m: m, e: e } };
  };

  /* L3-14 分子含絕對值：極限與連續的選項判斷 */
  L3.absPick = function (r) {
    r();
    var c = r.int(1, 5), d = c + r.int(1, 5), u = c + d, v = c * d, pt0 = r() < 0.6 ? 0 : u;
    var f0 = pt0 === 0 ? F(v, c) : F(-v, d), t3 = r() < 0.5, t5 = r() < 0.5;
    var v3 = t3 ? f0 : Fr.add(f0, r.nz(-2, 2)), v5 = t5 ? F(d - c) : F(c - d);
    var f = '\\dfrac{\\left|x^2-' + u + 'x\\right|-' + v + '}{' + xm(c) + '}';
    var opts = [no(1) + T('f(x)') + ' 在 ' + T('x=' + pt0) + ' 連續', no(2) + T('f(x)') + ' 在 ' + T('x=' + c) + ' 連續',
      no(3) + T(LX(pt0) + 'f(x)=' + fT(v3)), no(4) + T(LX(c) + 'f(x)') + ' 不存在', no(5) + T(LX(c) + 'f(x)=' + fT(v5))];
    var ans = '(1)' + (t3 ? '(3)' : '') + (t5 ? '(5)' : '');
    var q = '已知 ' + T('f(x)=' + f) + '，下列選項何者正確？（多選）<br>' + opts.join('　');
    var h = '在 ' + T('0\\lt x\\lt ' + u) + ' 時 ' + T('\\left|x^2-' + u + 'x\\right|=' + u + 'x-x^2') + '，分子 ' + T('=-x^2+' + u + 'x-' + v + '=-' + pxm(c) + pxm(d)) + '；' + T('f(' + c + ')') + ' 的分母是 ' + T(0) + '、沒有定義。連續要三個條件都成立；' + T('x=' + pt0) + ' 處分母是 ' + T(pt0 - c + '\\ne 0') + '，' + (pt0 === 0 ? '絕對值裡 ' + T('x^2-' + u + 'x') + ' 在 ' + T(0) + ' 的兩側都很小，直接代入' : '這裡正好是 ' + T('x^2-' + u + 'x') + ' 變號的地方，但絕對值仍是連續函數') + '。';
    return { q: q, a: ans, h: h, p: { c: c, d: d, pt0: pt0, t3: t3, t5: t5 } };
  };

  /* L3-15 勘根：x^m·b^x＝b^N 的根在哪兩個整數之間 */
  L3.ivtBig = function (r) {
    r();
    var b, m, N, k, t = 0, eq;
    do {
      b = r.pick([2, 2, 3]); m = r.pick([1, 1, 2]); N = b === 2 ? r.int(40, 200) : r.int(30, 120);
      k = N; eq = false;
      while (k > 0 && !(Math.pow(k, m) < Math.pow(b, N - k))) { if (Math.pow(k, m) === Math.pow(b, N - k)) eq = true; k--; }
      if (k > 0 && Math.pow(k + 1, m) === Math.pow(b, N - k - 1)) eq = true;
      t++;
    } while (eq && t < 50);
    var fx = (m === 1 ? 'x' : 'x^2') + '\\cdot ' + b + '^x';
    var q = '已知 ' + T('f(x)=' + fx) + ' 為連續函數。求正整數 ' + T('k') + '，使得在 ' + T('k') + ' 與 ' + T('k+1') + ' 之間有一實數 ' + T('c') + ' 滿足 ' + T('f(c)=' + b + '^{' + N + '}') + '。';
    var h = '令 ' + T('g(x)=' + fx + '-' + b + '^{' + N + '}') + '。兩邊取 ' + T('\\log_{' + b + '}') + ' 估計：' + T((m === 1 ? '' : '2') + '\\log_{' + b + '}x+x=' + N) + '，' + T('x') + ' 比 ' + T(N) + ' 小一點；再把 ' + T(b + '^{' + N + '}') + ' 寫成 ' + T(b + '^{' + N + '-k}\\cdot ' + b + '^{k}') + ' 和 ' + T((m === 1 ? 'k' : 'k^2') + '\\cdot ' + b + '^{k}') + ' 比大小。';
    return { q: q, a: T('k=' + k), h: h, p: { b: b, m: m, N: N, k: k } };
  };

  var META_L3 = [['expNeg', '1-2 負底數的指數型極限'], ['sumMinusAn', '1-2 連加除以 n 次方再減 an'], ['squeezeIneq', '1-3 由不等式夾出極限'],
                 ['rnConvX', '1-1 ⟨rⁿ⟩ 收斂、r 含 x'], ['sumSnGeo', '2-2 一般項含等比部分和'], ['snTelescope', '2-1 由 Sₙ 求一般項再裂項'],
                 ['geoRepDec', '2-3 首項是循環小數的等比級數'], ['nGeo', '2-1 n 乘等比：錯位相減'], ['composeDomain', '3-3 還原 f 再求 f∘g 定義域'],
                 ['rangeCount', '3-1 比較值域裡的正整數'], ['gaussSides', '4-3 高斯符號的左右極限'], ['polyTwoLimits', '4-2 兩個極限條件決定三次式'],
                 ['limMN', '4-2 0/0 型反求兩個參數'], ['absPick', '5-1 絕對值函數的極限與連續'], ['ivtBig', '5-3 勘根：xᵐ·bˣ＝bᴺ']];
  var L3_FIX = { 'L3-1': 'expNeg', 'L3-2': 'sumMinusAn', 'L3-3': 'squeezeIneq', 'L3-4': 'rnConvX', 'L3-5': 'sumSnGeo',
                 'L3-6': 'snTelescope', 'L3-7': 'geoRepDec', 'L3-8': 'nGeo', 'L3-9': 'composeDomain', 'L3-10': 'rangeCount',
                 'L3-11': 'gaussSides', 'L3-12': 'polyTwoLimits', 'L3-13': 'limMN', 'L3-14': 'absPick', 'L3-15': 'ivtBig' };

  /* ══════════════════════════════════════════════════════════
     L1 解題步驟（s：每步一段 HTML）與第一層提示（h1：只講「這是哪一型、第一步做什麼」，不帶數字）
     全部由 p（與 o.a）重算，所以與題目、答案一定一致；最後一步附上答案。
     ══════════════════════════════════════════════════════════ */
  function sxFin(o) { return '答案：' + o.a + '。'; }
  function sxF(t) { return F(t[0], t[1]); }
  /* 綜合除法：cs ÷ (x-a) 的商（cs 由高次到低次） */
  function sxDiv(cs, a) { var out = [], acc = F(0), i; cs = cs.map(N); for (i = 0; i < cs.length - 1; i++) { acc = Fr.add(Fr.mul(acc, a), cs[i]); out.push(acc); } return out; }
  /* 「n 次方」的寫法 */
  /* raw=val 時不要重複寫兩次 */
  function sxEq(raw, val) { return raw === val ? raw : raw + '=' + val; }
  function sxPw(e, v) { v = v || 'n'; return e === 0 ? '1' : (e === 1 ? v : v + '^' + e); }

  var L1_SOL = {};

  L1_SOL.seqRational = function (p, o) {
    var D = p.den.length - 1, s = [];
    if (p.kind === 1) s.push('先把分子乘開：' + T('a_n=\\dfrac{' + polyT(p.num, 'n') + '}{' + polyT(p.den, 'n') + '}') + '。');
    s.push('分母的最高次是 ' + T(sxPw(D)) + '，分子、分母同除以 ' + T(sxPw(D)) + '：' + T('a_n=\\dfrac{' + divT(p.num, D) + '}{' + divT(p.den, D) + '}') + '。');
    if (p.num.length === p.den.length) s.push('當 ' + T('n\\to\\infty') + '，所有 ' + T('\\frac{c}{n^k}') + ' 都趨近 ' + T(0) + '：分子趨近 ' + T(p.num[0]) + '、分母趨近 ' + T(p.den[0]) + '，極限 ' + T('=\\dfrac{' + p.num[0] + '}{' + p.den[0] + '}=' + fT(sxF(p.lim))) + '。' + sxFin(o));
    else if (p.num.length < p.den.length) s.push('當 ' + T('n\\to\\infty') + '，分子每一項都趨近 ' + T(0) + '、分母趨近 ' + T(p.den[0]) + '（不是 ' + T(0) + '）⟹ 極限是 ' + T(0) + '，數列收斂。' + sxFin(o));
    else s.push('分子還剩 ' + T(fT(p.num[0]) + 'n') + ' 這一項，絕對值越來越大；分母趨近 ' + T(p.den[0]) + ' ⟹ ' + T('|a_n|') + ' 沒有上限，數列發散。' + sxFin(o));
    return s;
  };
  L1_SOL.rPow = function (p, o) {
    var rv = sxF(p.r), s = [], rt = p.kind === 5 ? decT(rv) : fT(rv);
    if (p.kind === 4) {
      s.push(T('(-1)^{2n}=\\left((-1)^2\\right)^{n}=1^{n}=1') + '，所以 ' + T('a_n=' + p.c + sg(p.d) + '=' + (p.c + p.d)) + ' 對每個 ' + T('n') + ' 都一樣。');
      s.push('常數數列收斂到它自己：極限是 ' + T(p.c + p.d) + '。' + sxFin(o));
      return s;
    }
    s.push('底數 ' + T('r=' + rt) + '，' + T('|r|=' + (p.kind === 5 ? decT(Fr.abs(rv)) : fT(Fr.abs(rv)))) + '。');
    if (Math.abs(Fr.num(rv)) < 1) s.push(T('|r|\\lt 1') + ' ⟹ ' + T('r^n\\to 0') + '，所以 ' + T(p.d + '\\cdot r^n\\to 0') + '，' + T('a_n\\to ' + p.c) + '。' + sxFin(o));
    else if (Fr.eq(rv, -1)) s.push(T('(-1)^n') + ' 在 ' + T(1) + ' 與 ' + T(-1) + ' 之間跳 ⟹ ' + T('a_n') + ' 在 ' + T(p.c + p.d) + ' 與 ' + T(p.c - p.d) + ' 之間跳，不會靠近同一個數，發散。' + sxFin(o));
    else s.push(T('|r|\\gt 1') + ' ⟹ ' + T('|r^n|') + ' 越來越大、沒有上限，' + T('a_n') + ' 不會靠近任何一個數，發散。' + sxFin(o));
    return s;
  };
  L1_SOL.expDiv = function (p, o) {
    var M = Math.max(p.p, p.q), m = Math.min(p.p, p.q), NP = p.a * Math.pow(p.p, p.s), NQ = p.b, DP = p.c, DQ = p.d * Math.pow(p.q, p.t);
    var big = M === p.p, rat = '\\left(\\frac{' + m + '}{' + M + '}\\right)^{n}';
    function two(cb, cs_) { /* cb：最大底那一項的係數，cs_：小底那一項的係數 */
      var t1 = cb === 0 ? '' : String(cb), t2 = cs_ === 0 ? '' : (cs_ < 0 ? '-' : (t1 === '' ? '' : '+')) + (Math.abs(cs_) === 1 ? '' : Math.abs(cs_)) + rat;
      return (t1 + t2) || '0';
    }
    var nT = big ? two(NP, NQ) : two(NQ, NP), dT = big ? two(DP, DQ) : two(DQ, DP);
    var NM = big ? NP : NQ, DM = big ? DP : DQ;
    return ['最大的底是 ' + T(M) + '：分子、分母同除以 ' + T(M + '^{n}') + '（' + T(M + '^{n+k}\\div ' + M + '^{n}=' + M + '^{k}') + '）。',
      '得 ' + T('\\dfrac{' + nT + '}{' + dT + '}') + '。',
      T('n\\to\\infty') + ' 時 ' + T(rat + '\\to 0') + '，極限 ' + T('=' + sxEq(DM === 1 ? String(NM) : '\\dfrac{' + NM + '}{' + DM + '}', fT(sxF(p.lim)))) + '。' + sxFin(o)];
  };
  L1_SOL.rootRat = function (p, o) {
    var a = p.a, b = p.b, m = p.m, L = fT(sxF(p.lim));
    if (p.kind === 0) {
      var rad = polyT([1, a, b], 'n');
      return ['分子分母同乘 ' + T('\\sqrt{' + rad + '}+n') + '：分子 ' + T('=(' + rad + ')-n^2=' + polyT([a, b], 'n')) + '。',
        '原式 ' + T('=\\dfrac{' + polyT([a, b], 'n') + '}{\\sqrt{' + rad + '}+n}') + '，同除以 ' + T('n') + '：' + T('\\dfrac{' + divT([a, b], 1) + '}{\\sqrt{' + divT([1, a, b], 2) + '}+1}') + '。',
        T('n\\to\\infty') + ' 時分子 ' + T('\\to ' + a) + '、分母 ' + T('\\to\\sqrt{1}+1=2') + '，極限 ' + T('=' + sxEq('\\dfrac{' + a + '}{2}', L)) + '。' + sxFin(o)];
    }
    if (p.kind === 1) {
      var A = polyT([1, a, 0], 'n'), Bq = polyT([1, b, 0], 'n');
      return ['分子分母同乘 ' + T('\\sqrt{' + A + '}+\\sqrt{' + Bq + '}') + '：分子 ' + T('=(' + A + ')-(' + Bq + ')=' + polyT([a - b, 0], 'n')) + '。',
        '同除以 ' + T('n') + '：' + T('\\dfrac{' + (a - b) + '}{\\sqrt{' + divT([1, a, 0], 2) + '}+\\sqrt{' + divT([1, b, 0], 2) + '}}') + '。',
        '分母 ' + T('\\to 1+1=2') + '，極限 ' + T('=' + sxEq('\\dfrac{' + (a - b) + '}{2}', L)) + '。' + sxFin(o)];
    }
    if (p.kind === 2) {
      var R2 = polyT([1, 0, a], 'n');
      return ['括號裡有理化：' + T('\\sqrt{' + R2 + '}-n=\\dfrac{(' + R2 + ')-n^2}{\\sqrt{' + R2 + '}+n}=\\dfrac{' + a + '}{\\sqrt{' + R2 + '}+n}') + '。',
        '乘上前面的 ' + T('n') + ' 再同除以 ' + T('n') + '：' + T('\\dfrac{' + a + 'n}{\\sqrt{' + R2 + '}+n}=\\dfrac{' + a + '}{\\sqrt{' + divT([1, 0, a], 2) + '}+1}') + '。',
        '分母 ' + T('\\to 2') + '，極限 ' + T('=' + sxEq('\\dfrac{' + a + '}{2}', L)) + '。' + sxFin(o)];
    }
    if (p.kind === 3) {
      var R3 = polyT([m * m, a, 0], 'n');
      return ['分子分母同乘 ' + T('\\sqrt{' + R3 + '}+' + m + 'n') + '：分子 ' + T('=(' + R3 + ')-' + (m * m) + 'n^2=' + polyT([a, 0], 'n')) + '。',
        '同除以 ' + T('n') + '：' + T('\\dfrac{' + a + '}{\\sqrt{' + divT([m * m, a, 0], 2) + '}+' + m + '}') + '。',
        '分母 ' + T('\\to\\sqrt{' + (m * m) + '}+' + m + '=' + (2 * m)) + '，極限 ' + T('=' + sxEq('\\dfrac{' + a + '}{' + (2 * m) + '}', L)) + '。' + sxFin(o)];
    }
    var R4 = polyT([1, a, 0], 'n');
    return ['分子分母同乘 ' + T('\\sqrt{' + R4 + '}+n') + '：分母 ' + T('=(' + R4 + ')-n^2=' + a + 'n') + '，原式 ' + T('=\\dfrac{\\sqrt{' + R4 + '}+n}{' + a + 'n}') + '。',
      '同除以 ' + T('n') + '：' + T('\\dfrac{\\sqrt{' + divT([1, a, 0], 2) + '}+1}{' + a + '}') + '。',
      '分子 ' + T('\\to 2') + '，極限 ' + T('=' + sxEq('\\dfrac{2}{' + a + '}', L)) + '。' + sxFin(o)];
  };
  L1_SOL.squeezeFloor = function (p, o) {
    var al = p.al, x = p.kind === 2 ? (al.kind === 'frac' ? '\\dfrac{' + (al.u === 1 ? '' : al.u) + 'n^2}{' + al.v + '}' : (al.kind === 'pi' ? 'n^2\\pi' : al.inT2)) : al.inT;
    var dn = p.kind === 1 ? 'n' : (p.kind === 2 ? polyT([p.b, 0, p.c], 'n') : polyT([p.b, p.c], 'n'));
    return ['高斯符號的基本不等式：' + T(x + '-1\\lt ' + gb(x) + '\\le ' + x) + '。',
      '三邊同除以 ' + T(dn) + '（正數，不等號不變）：' + T('\\dfrac{' + x + '-1}{' + dn + '}\\lt a_n\\le\\dfrac{' + x + '}{' + dn + '}') + '。',
      '左右兩邊都趨近 ' + T(alphaOver(al, p.b)) + '（分子分母同除以 ' + T(p.kind === 2 ? 'n^2' : 'n') + '，多出來的 ' + T('-1') + ' 除完趨近 ' + T(0) + '）⟹ 由夾擠定理，' + T('a_n') + ' 也趨近它。' + sxFin(o)];
  };
  L1_SOL.recurLimit = function (p, o) {
    var pr = sxF(p.p), q = sxF(p.q), s = [];
    var rw = p.form === 0 ? '' : '先把遞迴式寫成 ' + T('a_{n+1}=' + cf(pr) + 'a_n' + sg(q)) + '。';
    s.push(rw + T('a_2=' + fT(pr) + '\\cdot ' + pn(p.a1) + sg(q) + '=' + fT(sxF(p.a2))) + '。');
    s.push(T('a_3=' + fT(pr) + '\\cdot ' + pn(sxF(p.a2)) + sg(q) + '=' + fT(sxF(p.a3))) + '。');
    s.push('已知收斂，令 ' + T('\\lim a_n=L') + '，兩邊取極限：' + T('L=' + cf(pr) + 'L' + sg(q)) + ' ⟹ ' + T(fT(Fr.sub(1, pr)) + 'L=' + fT(q)) + ' ⟹ ' + T('L=' + p.L) + '。' + sxFin(o));
    return s;
  };
  L1_SOL.newtonSqrt = function (p, o) {
    var x2 = sxF(p.x2), x3 = sxF(p.x3), q = sqf(p.A);
    return [(p.form === 1 ? '先化簡：' + T('x_n-\\dfrac{x_n^2-' + p.A + '}{2x_n}=\\dfrac{x_n^2+' + p.A + '}{2x_n}=\\dfrac{1}{2}\\left(x_n+\\dfrac{' + p.A + '}{x_n}\\right)') + '。' : '') + T('x_2=\\dfrac{1}{2}\\left(' + p.x1 + '+\\dfrac{' + p.A + '}{' + p.x1 + '}\\right)=' + fT(x2)) + '。',
      T('x_3=\\dfrac{1}{2}\\left(' + fT(x2) + '+' + p.A + '\\div ' + fT(x2) + '\\right)=' + fT(x3)) + '（約 ' + T(decT(x3)) + '）。',
      '若收斂，令極限為 ' + T('L') + '（每一項都是正數，' + T('L\\gt 0') + '）：' + T('L=\\dfrac{1}{2}\\left(L+\\dfrac{' + p.A + '}{L}\\right)') + ' ⟹ ' + T('L^2=' + p.A) + ' ⟹ ' + T('L=' + surdT(F(q[0]), q[1])) + '。' + sxFin(o)];
  };
  L1_SOL.compound = function (p, o) {
    var k = p.k, m = p.m, c = p.c, kk;
    if (p.kind === 6) {
      kk = sxF(p.k);
      return ['令 ' + T('t=\\dfrac{m}{' + decT(F(p.rt, 100)) + '}') + '，' + T('m\\to\\infty') + ' 時 ' + T('t\\to\\infty') + '，而 ' + T('\\dfrac{' + decT(F(p.rt, 100)) + '}{m}=\\dfrac{1}{t}') + '、' + T((p.yr === 1 ? '' : p.yr) + 'm=' + decT(kk) + 't') + '。',
        T(p.P + '\\left(1+\\dfrac{1}{t}\\right)^{' + decT(kk) + 't}=' + p.P + '\\left[\\left(1+\\dfrac{1}{t}\\right)^{t}\\right]^{' + decT(kk) + '}\\to ' + p.P + 'e^{' + decT(kk) + '}') + '。' + sxFin(o)];
    }
    if (p.kind === 1) return [T('\\left(1+\\dfrac{1}{n}\\right)^{' + m + 'n}=\\left[\\left(1+\\dfrac{1}{n}\\right)^{n}\\right]^{' + m + '}') + '。', '中括號裡趨近 ' + T('e') + '，所以整個趨近 ' + T('e^{' + m + '}') + '。' + sxFin(o)];
    if (p.kind === 3) return ['令 ' + T('t=' + m + 'n') + '，則 ' + T('n=\\dfrac{t}{' + m + '}') + '：' + T('\\left(1+\\dfrac{1}{t}\\right)^{n}=\\left[\\left(1+\\dfrac{1}{t}\\right)^{t}\\right]^{\\frac{1}{' + m + '}}') + '。', T('n\\to\\infty') + ' 時 ' + T('t\\to\\infty') + '，中括號趨近 ' + T('e') + ' ⟹ 極限 ' + T('e^{\\frac{1}{' + m + '}}') + '。' + sxFin(o)];
    if (p.kind === 5) return ['拆開：' + T('\\left(1+\\dfrac{' + k + '}{n}\\right)^{n' + sg(c) + '}=\\left(1+\\dfrac{' + k + '}{n}\\right)^{n}\\cdot\\left(1+\\dfrac{' + k + '}{n}\\right)^{' + c + '}') + '。',
      '令 ' + T('t=\\dfrac{n}{' + k + '}') + '：第一個因式 ' + T('=\\left[\\left(1+\\dfrac{1}{t}\\right)^{t}\\right]^{' + k + '}\\to e^{' + k + '}') + '；第二個因式的次方固定，趨近 ' + T('1^{' + c + '}=1') + '。',
      '極限 ' + T('=e^{' + k + '}\\cdot 1') + '。' + sxFin(o)];
    var K = Math.abs(k), ex = p.kind === 2 ? K * m : K, neg = k < 0;
    var base = p.kind === 4 ? '先改寫 ' + T('\\dfrac{n' + sg(k) + '}{n}=1' + sg(k) + '\\cdot\\dfrac{1}{n}') + '。' : '';
    return [base + '令 ' + T('t=\\dfrac{n}{' + K + '}') + '，則 ' + T('\\dfrac{' + K + '}{n}=\\dfrac{1}{t}') + '、' + T((p.kind === 2 ? m : '') + 'n=' + ex + 't') + '。',
      '原式 ' + T('=\\left[\\left(1' + (neg ? '-' : '+') + '\\dfrac{1}{t}\\right)^{t}\\right]^{' + ex + '}') + '，而 ' + T('\\left(1' + (neg ? '-' : '+') + '\\dfrac{1}{t}\\right)^{t}\\to ' + (neg ? 'e^{-1}' : 'e')) + '。',
      '極限 ' + T('=' + (neg ? '\\left(e^{-1}\\right)^{' + ex + '}' : 'e^{' + ex + '}') + '=' + eT(sxF(p.ans))) + '。' + sxFin(o)];
  };
  L1_SOL.geoSum = function (p, o) {
    var a = sxF(p.a1), rv = sxF(p.r), s = [];
    if (p.form === 'list') s.push('首項 ' + T('a=' + fT(a)) + '，公比 ' + T('r=\\dfrac{\\text{第二項}}{\\text{第一項}}=' + fT(rv)) + '。');
    else s.push('這是無窮等比級數：首項（' + T('n=1') + ' 那一項）' + T('a=' + fT(a)) + '，公比 ' + T('r=' + fT(rv)) + '。');
    if (p.S === null) { s.push(T('|r|=' + fT(Fr.abs(rv)) + '\\ge 1') + ' ⟹ 每一項不趨近 ' + T(0) + '，部分和沒有極限，級數發散（不能套 ' + T('\\frac{a}{1-r}') + '）。' + sxFin(o)); return s; }
    s.push(T('|r|=' + fT(Fr.abs(rv)) + '\\lt 1') + ' ⟹ 收斂。');
    s.push('和 ' + T('=\\dfrac{a}{1-r}=\\dfrac{' + fT(a) + '}{1-' + pn(rv) + '}=' + fT(sxF(p.S))) + '。' + sxFin(o));
    return s;
  };
  L1_SOL.geoXRange = function (p, o) {
    var a = p.a, b = p.b, c = p.c, L = polyT([a, b]);
    if (p.kind <= 1) {
      var rt = p.kind === 0 ? '\\dfrac{' + L + '}{' + c + '}' : L;
      return ['公比 ' + T('r=' + rt) + '，無窮等比級數收斂 ⟺ ' + T('|r|\\lt 1') + '。',
        T('\\left|' + rt + '\\right|\\lt 1') + ' ⟹ ' + T('-' + c + '\\lt ' + L + '\\lt ' + c) + ' ⟹ ' + T((-c - b) + '\\lt ' + polyT([a, 0]) + '\\lt ' + (c - b)) + (a < 0 ? '，同除以負數 ' + T(a) + '，不等號反向' : (a === 1 ? '' : '，同除以 ' + T(a))) + '。', sxFin(o)];
    }
    if (p.kind === 2) return ['一般項 ' + T('=\\left(\\dfrac{' + xm(b) + '}{' + c + '}\\right)^{n}') + '，公比 ' + T('\\dfrac{' + xm(b) + '}{' + c + '}') + '。', '收斂 ⟺ ' + T('|' + xm(b) + '|\\lt ' + c) + ' ⟺ ' + T('-' + c + '\\lt ' + xm(b) + '\\lt ' + c) + '，各加 ' + T(-b) + '。', sxFin(o)];
    return ['公比 ' + T('\\dfrac{' + c + '}{' + xm(b) + '}') + '（' + T('x\\ne ' + b) + '），收斂 ⟺ ' + T('\\dfrac{' + c + '}{|' + xm(b) + '|}\\lt 1') + ' ⟺ ' + T('|' + xm(b) + '|\\gt ' + c) + '。',
      T(xm(b) + '\\lt -' + c) + ' 或 ' + T(xm(b) + '\\gt ' + c) + '，各加 ' + T(-b) + '。', sxFin(o)];
  };
  L1_SOL.repDec = function (p, o) {
    var k = p.nr.length, m = p.rp.length, big = Math.pow(10, k + m), small = Math.pow(10, k);
    var x = p.ip + '.' + p.nr + '\\overline{' + p.rp + '}';
    var B1 = p.ip * big + parseInt(p.nr + p.rp, 10), S1 = p.ip * small + (k ? parseInt(p.nr, 10) : 0);
    var den = big - small, num = B1 - S1;
    return ['設 ' + T('x=' + x) + '，乘 ' + T(big) + ' 讓一個循環節移到小數點左邊：' + T(big + 'x=' + B1 + '.\\overline{' + p.rp + '}') + '。',
      (k ? '再乘 ' + T(small) + ' 讓不循環的部分移過去：' + T(small + 'x=' + S1 + '.\\overline{' + p.rp + '}') + '。兩式相減：' : '減去原數 ' + T('x=' + S1 + '.\\overline{' + p.rp + '}') + '：') + T(den + 'x=' + num) + '。',
      T('x=' + sxEq('\\dfrac{' + num + '}{' + den + '}', fT(sxF(p.val)))) + '（約分到最簡）。' + sxFin(o)];
  };
  L1_SOL.telescoping = function (p, o) {
    var c = p.c, S = fT(sxF(p.S));
    if (p.kind === 1) {
      var k = p.k, head = [], i, tail = [], co = cf(F(c, k));
      for (i = 1; i <= k; i++) { head.push(i === 1 ? '1' : '\\frac{1}{' + i + '}'); tail.push('\\frac{1}{n+' + i + '}'); }
      var hd = k === 1 ? '1' : '\\left(' + head.join('+') + '\\right)', tl = k === 1 ? tail[0] : '\\left(' + tail.join('+') + '\\right)';
      return ['裂項：' + T('\\dfrac{' + c + '}{n(n+' + k + ')}=' + co + '\\left(\\dfrac{1}{n}-\\dfrac{1}{n+' + k + '}\\right)') + '。',
        '部分和寫開，相隔 ' + T(k) + ' 項的會互相消掉：' + T('S_n=' + co + '\\left[' + hd + '-' + tl + '\\right]') + '。',
        T('n\\to\\infty') + ' 時後面那一組趨近 ' + T(0) + '：和 ' + T('=' + sxEq(co + (k === 1 ? '\\cdot 1' : hd), S)) + '。' + sxFin(o)];
    }
    var a = p.a, b = p.b, f1 = polyT([a, b], 'n'), f2 = polyT([a, a + b], 'n'), pr = (b === 0 ? f1 : '(' + f1 + ')') + '(' + f2 + ')', ca = cf(F(c, a)), c1 = a === 1 ? '' : '\\dfrac{1}{' + a + '}';
    return [(p.kind === 2 ? '分母因式分解成 ' + T(pr) + '（兩個因式相差 ' + T(a) + '）。' : '') + '裂項：' + T('\\dfrac{1}{' + pr + '}=' + c1 + '\\left(\\dfrac{1}{' + f1 + '}-\\dfrac{1}{' + f2 + '}\\right)') + '。',
      '部分和中間全部消掉，只剩頭尾：' + T('S_n=' + ca + '\\left(\\dfrac{1}{' + (a + b) + '}-\\dfrac{1}{' + f2 + '}\\right)') + '。',
      T('n\\to\\infty') + ' 時 ' + T('\\dfrac{1}{' + f2 + '}\\to 0') + '：和 ' + T('=' + sxEq(ca + '\\cdot\\dfrac{1}{' + (a + b) + '}', S)) + '。' + sxFin(o)];
  };
  L1_SOL.geoSplit = function (p, o) {
    var r1 = F(p.a, p.c), r2 = F(p.b, p.c), k2 = Fr.mul(p.B, p.s === 1 ? F(p.b) : (p.s === -1 ? F(1, p.b) : F(1)));
    return ['拆成兩個無窮等比級數：' + T(SUMI + cf(p.A) + '\\left(' + fT(r1) + '\\right)^{n}') + ' 與 ' + T(SUMI + cf(k2) + '\\left(' + fT(r2) + '\\right)^{n}') + '，兩個公比的絕對值都小於 ' + T(1) + '，都收斂。',
      '第一個：首項 ' + T(fT(Fr.mul(p.A, r1))) + '、和 ' + T('\\dfrac{' + fT(Fr.mul(p.A, r1)) + '}{1-' + pn(r1) + '}=' + fT(sxF(p.S1))) + '；第二個：首項 ' + T(fT(Fr.mul(k2, r2))) + '、和 ' + T('\\dfrac{' + fT(Fr.mul(k2, r2)) + '}{1-' + pn(r2) + '}=' + fT(sxF(p.S2))) + '。',
      '兩個收斂的級數可以相加：' + T(fT(sxF(p.S1)) + sg(sxF(p.S2)) + '=' + fT(sxF(p.S))) + '。' + sxFin(o)];
  };
  L1_SOL.domain = function (p, o) {
    var a = p.a, b = p.b, c = p.c, m = p.m;
    var cond = {
      0: function () { return '根號裡 ' + T(polyT([a, b]) + '\\ge 0') + ' ⟹ ' + T('x' + (a > 0 ? '\\ge ' : '\\le ') + fT(F(-b, a))) + '；分母 ' + T(xm(c) + '\\ne 0') + ' ⟹ ' + T('x\\ne ' + c) + '。'; },
      1: function () { return '根號裡 ' + T(xm(a) + '\\ge 0') + ' ⟹ ' + T('x\\ge ' + a) + '；分母 ' + T(xm(b) + '\\ne 0') + ' ⟹ ' + T('x\\ne ' + b) + '。'; },
      2: function () { return '根號裡要 ' + T('\\ge 0') + '：等價於 ' + T(pxm(a) + pxm(b) + '\\le 0') + '，解在兩根 ' + T(a) + '、' + T(b) + ' 之間（含端點）。'; },
      3: function () { return '分母的根號 ' + T((c === 0 ? '-x' : c + '-x') + '\\gt 0') + ' ⟹ ' + T('x\\lt ' + c) + '（等於 ' + T(0) + ' 會讓分母是 ' + T(0) + '）；另一個根號 ' + T(xm(a) + '\\ge 0') + ' ⟹ ' + T('x\\ge ' + a) + '。'; },
      4: function () { return '分母 ' + T('x^2-' + (m * m) + '\\ne 0') + ' ⟹ ' + T('x\\ne\\pm' + m) + '；分子是多項式，沒有限制。'; },
      5: function () { return '根號裡 ' + T(pxm(a) + pxm(b) + '\\ge 0') + '，解在兩根 ' + T(a) + '、' + T(b) + ' 之外（含端點）。'; },
      6: function () { return '根號裡的分式 ' + T('\\dfrac{' + xm(a) + '}{' + xm(b) + '}\\ge 0') + '：分子分母同號，或分子為 ' + T(0) + '；但分母不能是 ' + T(0) + '，所以 ' + T('x=' + b) + ' 不行、' + T('x=' + a) + ' 可以。'; }
    }[p.kind]();
    return [cond, '把條件畫在數線上取交集（兩個條件都要成立）。', sxFin(o)];
  };
  function sxPar(p, x) {
    var a = p.a, b = p.b, c = p.c;
    switch (p.kind) {
      case 0: return F(x * x * x + c * x); case 1: return F(a * Math.pow(x, 5) - b * x * x * x); case 2: return F(c * x, x * x + b);
      case 3: return F(c * x * Math.abs(x) + a * x); case 4: return F(Math.abs(x - a) - Math.abs(x + a)); case 5: return F(Math.pow(x, 4) + c * x * x + b);
      case 6: return F(c, x * x + b); case 7: return F(c * Math.abs(x) + a * x * x); case 8: return F(Math.abs(x - a) + Math.abs(x + a));
      case 9: return F(x * x * x + c * x + b); case 10: return F(x * x + c * x); default: return F(Math.abs(x - c) + a * x * x);
    }
  }
  L1_SOL.parity = function (p, o) {
    var a = p.a, b = p.b, c = p.c, fm;
    switch (p.kind) {
      case 0: fm = 'f(-x)=(-x)^3' + sg(c) + '(-x)=' + polyT([-1, 0, -c, 0]) + '=-f(x)'; break;
      case 1: fm = 'f(-x)=' + a + '(-x)^5-' + b + '(-x)^3=' + polyT([-a, 0, b, 0, 0, 0]) + '=-f(x)'; break;
      case 2: fm = 'f(-x)=\\dfrac{' + c + '(-x)}{(-x)^2+' + b + '}=\\dfrac{' + polyT([-c, 0]) + '}{x^2+' + b + '}=-f(x)'; break;
      case 3: fm = 'f(-x)=' + c + '(-x)\\left|-x\\right|' + sg(a) + '(-x)=' + cf(-c) + 'x\\left|x\\right|' + sg(-a) + 'x=-f(x)'; break;
      case 4: fm = 'f(-x)=\\left|-x-' + a + '\\right|-\\left|-x+' + a + '\\right|=\\left|x+' + a + '\\right|-\\left|x-' + a + '\\right|=-f(x)'; break;
      case 5: fm = 'f(-x)=(-x)^4' + sg(c) + '(-x)^2+' + b + '=f(x)'; break;
      case 6: fm = 'f(-x)=\\dfrac{' + c + '}{(-x)^2+' + b + '}=f(x)'; break;
      case 7: fm = 'f(-x)=' + c + '\\left|-x\\right|' + sg(a) + '(-x)^2=f(x)'; break;
      case 8: fm = 'f(-x)=\\left|-x-' + a + '\\right|+\\left|-x+' + a + '\\right|=\\left|x+' + a + '\\right|+\\left|x-' + a + '\\right|=f(x)'; break;
      case 9: fm = 'f(-x)=' + polyT([-1, 0, -c, b]); break;
      case 10: fm = 'f(-x)=' + polyT([1, -c, 0]); break;
      default: fm = 'f(-x)=\\left|-x' + sg(-c) + '\\right|' + sg(a) + 'x^2=\\left|x' + sg(c) + '\\right|' + sg(a) + 'x^2';
    }
    var s = ['把 ' + T('x') + ' 換成 ' + T('-x') + '：' + T(fm) + '。'];
    if (p.lab === 0) s.push(T('f(-x)=f(x)') + ' 對所有 ' + T('x') + ' 成立 ⟹ 偶函數（圖形對 ' + T('y') + ' 軸對稱）。' + sxFin(o));
    else if (p.lab === 1) s.push(T('f(-x)=-f(x)') + ' 對所有 ' + T('x') + ' 成立 ⟹ 奇函數（圖形對原點對稱）。' + sxFin(o));
    else s.push('舉反例：' + T('f(1)=' + fT(sxPar(p, 1))) + '、' + T('f(-1)=' + fT(sxPar(p, -1))) + '，' + T('f(-1)\\ne f(1)') + ' 也 ' + T('f(-1)\\ne -f(1)') + ' ⟹ 既不是奇函數也不是偶函數。' + sxFin(o));
    return s;
  };
  L1_SOL.compose = function (p, o) {
    var f = p.f, g = p.g, k = p.k, fT_ = polyT(f), gT_ = polyT(g), inner = sxF(p.inner), e2 = p.e2.map(sxF);
    var s1 = p.ord === 0 ? T('g(' + k + ')=' + fT(inner)) + '，' + T('f(' + fT(inner) + ')=' + fT(sxF(p.v1))) : T('f(' + k + ')=' + fT(inner)) + '，' + T('g(' + fT(inner) + ')=' + fT(sxF(p.v1)));
    var s2 = p.ord === 0 ? T('(g\\circ f)(x)=g(f(x))=' + cf(g[0]) + '(' + fT_ + ')^2' + (g[1] === 0 ? '' : sg(g[1]) + '(' + fT_ + ')') + sg(g[2]))
      : T('(f\\circ g)(x)=f(g(x))=' + cf(f[0]) + '(' + gT_ + ')' + sg(f[1]));
    return [no(1) + '由內往外算：' + s1 + '。', no(2) + '把內層整個代進外層：' + s2 + '。', '乘開整理得 ' + T(polyT(e2)) + '。' + sxFin(o)];
  };
  L1_SOL.inverse = function (p, o) {
    var a = p.a, b = p.b, c = p.c, d = p.d, m = p.m, k = sxF(p.k);
    if (p.kind === 0) return ['令 ' + T('y=' + polyT([a, b])) + '，解出 ' + T('x=\\dfrac{y' + sg(-b) + '}{' + a + '}') + '。',
      T('x') + '、' + T('y') + ' 互換：' + T('f^{-1}(x)=' + polyT([F(1, a), F(-b, a)])) + '。',
      T('f^{-1}' + ar(k) + '=' + polyT([F(1, a), F(-b, a)]).replace(/x/g, ar(k)) + '=' + m) + '（驗算：' + T('f(' + m + ')=' + fT(k)) + '）。' + sxFin(o)];
    if (p.kind === 1) return ['令 ' + T('y=\\dfrac{' + polyT([a, b]) + '}{' + polyT([c, d]) + '}') + '，去分母：' + T('y(' + polyT([c, d]) + ')=' + polyT([a, b])) + ' ⟹ ' + T('(' + polyT([c, -a], 'y') + ')x=' + polyT([-d, b], 'y')) + '。',
      '解出 ' + T('x=\\dfrac{' + polyT([-d, b], 'y') + '}{' + polyT([c, -a], 'y') + '}') + '，' + T('x') + '、' + T('y') + ' 互換得 ' + T('f^{-1}(x)=\\dfrac{' + polyT([-d, b]) + '}{' + polyT([c, -a]) + '}') + '。',
      T('f^{-1}' + ar(k)) + ' 就是 ' + T('f(x)=' + fT(k)) + ' 的解：代入反函數得 ' + T(m) + '（驗算：' + T('f(' + m + ')=\\dfrac{' + (a * m + b) + '}{' + (c * m + d) + '}=' + fT(k)) + '）。' + sxFin(o)];
    var inside = a === 1 ? polyT([1, -b], 'y') : (b === 0 ? '-y' : b + '-y');
    return ['令 ' + T('y=' + polyT([a, 0, 0, b])) + '，' + T('x^3=' + inside) + ' ⟹ ' + T('x=\\sqrt[3]{' + inside + '}') + '（立方根對所有實數都有定義，而且只有一個）。',
      T('x') + '、' + T('y') + ' 互換：' + T('f^{-1}(x)=\\sqrt[3]{' + inside.replace(/y/g, 'x') + '}') + '。',
      T('f^{-1}' + ar(k) + '=\\sqrt[3]{' + fT(a === 1 ? Fr.sub(k, b) : Fr.sub(b, k)) + '}=' + m) + '。' + sxFin(o)];
  };
  L1_SOL.gaussVal = function (p, o) {
    var it = p.items, s = [], parts = [], i;
    for (i = 0; i < it.length; i++) {
      s.push(T(it[i].fl + '\\le ' + it[i].tex + '\\lt ' + (it[i].fl + 1)) + ' ⟹ ' + T(gb(it[i].tex) + '=' + it[i].fl) + '。');
      parts.push((i === 0 ? '' : (p.sg[i] > 0 ? '+' : '-')) + pn(it[i].fl));
    }
    s.push('代回：' + T(parts.join('') + '=' + p.ans) + '。' + sxFin(o));
    return s;
  };
  L1_SOL.limSub = function (p, o) {
    var a = p.a;
    if (p.kind === 0) return ['多項式函數處處連續 ⟹ 極限就是函數值，直接代 ' + T('x=' + a) + '。', T(polyT(p.cs).replace(/x/g, '(' + a + ')') + '=' + fT(pval(p.cs, F(a)))) + '。' + sxFin(o)];
    if (p.kind === 1) return ['代 ' + T('x=' + a) + '：分母 ' + T('=' + (a + p.d) + '\\ne 0') + '，有理函數在這裡連續，直接代入。', '分子 ' + T(polyT(p.nm).replace(/x/g, '(' + a + ')') + '=' + fT(pval(p.nm, F(a)))) + '，極限 ' + T('=\\dfrac{' + fT(pval(p.nm, F(a))) + '}{' + (a + p.d) + '}=' + fT(Fr.div(pval(p.nm, F(a)), F(a + p.d)))) + '。' + sxFin(o)];
    if (p.kind === 2) { var R = a * a + p.b; return ['根號裡在 ' + T('x=' + a) + ' 附近是正的（' + T(pp(a) + '^2' + sg(p.b) + '=' + R) + '），函數連續，直接代入。', T('\\sqrt{' + R + '}' + sg(p.c) + '\\cdot ' + pp(a) + '=' + sqrtT(R) + sg(p.c * a)) + '。' + sxFin(o)]; }
    return ['絕對值函數、多項式都連續 ⟹ 直接代入。', T('\\left|' + pp(a) + '^2' + sg(-p.b) + '\\right|' + sg(p.c) + '\\cdot ' + pp(a) + '=' + Math.abs(a * a - p.b) + sg(p.c * a) + '=' + (Math.abs(a * a - p.b) + p.c * a)) + '。' + sxFin(o)];
  };
  L1_SOL.limFactor = function (p, o) {
    var a = F(p.a), num = p.num.map(sxF), den = p.den.map(sxF), nA = pval(num, a), dA = pval(den, a);
    if (p.val === null) return ['代 ' + T('x=' + p.a) + '：分子 ' + T('=' + fT(nA) + '\\ne 0') + '，分母 ' + T('=0') + ' ⟹ 不是 ' + T('\\frac{0}{0}') + ' 型。',
      '分子趨近 ' + T(fT(nA)) + '、分母趨近 ' + T(0) + '：商的絕對值越來越大，而且分母在 ' + T('x=' + p.a) + ' 左右兩側異號（' + T(pxm(p.a)) + ' 是分母的單一因式）⟹ 左右極限不會相等，極限不存在。' + sxFin(o)];
    var qn = sxDiv(num, a), qd = sxDiv(den, a);
    return ['代 ' + T('x=' + p.a) + '：分子、分母都是 ' + T(0) + '（' + T('\\frac{0}{0}') + ' 型）⟹ 都有因式 ' + T(pxm(p.a)) + '。',
      '用綜合除法：分子 ' + T('=' + pxm(p.a) + '(' + polyT(qn) + ')') + '、分母 ' + T('=' + pxm(p.a) + '(' + polyT(qd) + ')') + '，' + T('x\\ne ' + p.a) + ' 時約掉 ' + T(pxm(p.a)) + '。',
      '再代 ' + T('x=' + p.a) + '：' + T('\\dfrac{' + fT(pval(qn, a)) + '}{' + fT(pval(qd, a)) + '}=' + fT(sxF(p.val))) + '。' + sxFin(o)];
  };
  L1_SOL.limRational = function (p, o) {
    var a = p.a, b = p.b, c = p.c, V = fT(sxF(p.val));
    if (p.kind === 0) return ['分子分母同乘 ' + T('\\sqrt{' + polyT([1, b]) + '}+' + c) + '：分子 ' + T('=(' + polyT([1, b]) + ')-' + (c * c) + '=' + xm(a)) + '。', '約掉 ' + T(pxm(a)) + '：原式 ' + T('=\\dfrac{1}{\\sqrt{' + polyT([1, b]) + '}+' + c + '}') + '。', '代 ' + T('x=' + a) + '：' + T('\\dfrac{1}{\\sqrt{' + (c * c) + '}+' + c + '}=' + V) + '。' + sxFin(o)];
    if (p.kind === 1) return ['分子分母同乘 ' + T('\\sqrt{' + polyT([1, b]) + '}+' + c) + '：分母 ' + T('=(' + polyT([1, b]) + ')-' + (c * c) + '=' + xm(a)) + '。', '約掉 ' + T(pxm(a)) + '：原式 ' + T('=\\sqrt{' + polyT([1, b]) + '}+' + c) + '。', '代 ' + T('x=' + a) + '：' + T('\\sqrt{' + (c * c) + '}+' + c + '=' + V) + '。' + sxFin(o)];
    if (p.kind === 2) return ['分子分母同乘 ' + T('\\sqrt{' + polyT([p.p, p.q]) + '}+' + c) + '：分子 ' + T('=(' + polyT([p.p, p.q]) + ')-' + (c * c) + '=' + p.p + pxm(a)) + '。', '約掉 ' + T(pxm(a)) + '：原式 ' + T('=\\dfrac{' + p.p + '}{\\sqrt{' + polyT([p.p, p.q]) + '}+' + c + '}') + '。', '代 ' + T('x=' + a) + '：' + T('\\dfrac{' + p.p + '}{' + c + '+' + c + '}=' + V) + '。' + sxFin(o)];
    if (p.kind === 3) return ['分子分母同乘 ' + T('\\sqrt{' + polyT([1, b]) + '}+\\sqrt{' + polyT([2, p.e]) + '}') + '：分子 ' + T('=(' + polyT([1, b]) + ')-(' + polyT([2, p.e]) + ')=' + polyT([-1, b - p.e]) + '=-' + pxm(a)) + '。', '約掉 ' + T(pxm(a)) + '：原式 ' + T('=\\dfrac{-1}{\\sqrt{' + polyT([1, b]) + '}+\\sqrt{' + polyT([2, p.e]) + '}}') + '。', '代 ' + T('x=' + a) + '（兩個根號都是 ' + T(c) + '）：' + T('\\dfrac{-1}{' + c + '+' + c + '}=' + V) + '。' + sxFin(o)];
    return ['分母有理化：同乘 ' + T('\\sqrt{' + polyT([1, b]) + '}+' + c) + '，分母 ' + T('=' + xm(a)) + '；分子 ' + T(polyT([1, 0, -a * a]) + '=' + pxm(a) + pxm(-a)) + '。', '約掉 ' + T(pxm(a)) + '：原式 ' + T('=' + pxm(-a) + '\\left(\\sqrt{' + polyT([1, b]) + '}+' + c + '\\right)') + '。', '代 ' + T('x=' + a) + '：' + T('(' + (2 * a) + ')(' + c + '+' + c + ')=' + V) + '。' + sxFin(o)];
  };
  L1_SOL.oneSided = function (p, o) {
    var a = p.a, R = fT(sxF(p.R)), L = fT(sxF(p.L)), s = [], eq = Fr.eq(sxF(p.R), sxF(p.L));
    if (p.kind === 0) {
      s.push(T('x\\to ' + a + '^{+}') + '：' + T(xm(a) + '\\gt 0') + '，' + T('\\dfrac{\\left|' + xm(a) + '\\right|}{' + xm(a) + '}=1') + '，' + T('f(x)\\to ' + p.k + sg(p.m) + '=' + R) + '。');
      s.push(T('x\\to ' + a + '^{-}') + '：' + T(xm(a) + '\\lt 0') + '，' + T('\\dfrac{\\left|' + xm(a) + '\\right|}{' + xm(a) + '}=-1') + '，' + T('f(x)\\to ' + (-p.k) + sg(p.m) + '=' + L) + '。');
    } else if (p.kind === 1) {
      s.push('右側 ' + T('\\left|' + xm(a) + '\\right|=' + xm(a)) + '：' + T('f(x)=\\dfrac{' + pxm(a) + pxm(-a) + '}{' + xm(a) + '}=' + xm(-a) + '\\to ' + R) + '。');
      s.push('左側 ' + T('\\left|' + xm(a) + '\\right|=-' + pxm(a)) + '：' + T('f(x)=-' + pxm(-a) + '\\to ' + L) + '。');
    } else if (p.kind === 2) {
      s.push('右側 ' + T(a + '\\lt x\\lt ' + (a + 1)) + '，' + T('[x]=' + a) + '：' + T('f(x)\\to ' + pp(p.m) + pp(a) + sg(p.b) + '\\cdot ' + pp(a) + '=' + R) + '。');
      s.push('左側 ' + T((a - 1) + '\\lt x\\lt ' + a) + '，' + T('[x]=' + (a - 1)) + '：' + T('f(x)\\to ' + pp(p.m) + pp(a - 1) + sg(p.b) + '\\cdot ' + pp(a) + '=' + L) + '。');
    } else {
      s.push('右極限用 ' + T('x\\ge ' + a) + ' 那一段：' + T(polyT(p.p2.map(sxF)).replace(/x/g, '(' + a + ')') + '=' + R) + '。');
      s.push('左極限用 ' + T('x\\lt ' + a) + ' 那一段：' + T(polyT(p.p1).replace(/x/g, '(' + a + ')') + '=' + L) + '。');
    }
    s.push(eq ? '左右極限相等 ⟹ 極限存在，等於 ' + T(R) + '。' + sxFin(o) : '左右極限不相等 ⟹ 極限不存在。' + sxFin(o));
    return s;
  };
  L1_SOL.limParam = function (p, o) {
    var a = p.a;
    if (p.kind <= 1) return ['分母 ' + T('\\to 0') + '，極限要存在，分子也必須 ' + T('\\to 0') + '：' + T(pp(a) + '^2+' + pp(a) + 'k' + sg(p.c) + '=0') + ' ⟹ ' + T('k=' + p.k) + '。',
      '分子 ' + T(polyT([1, p.k, p.c]) + '=' + pxm(a) + pxm(p.r)) + '，約掉 ' + T(pxm(a)) + '：原式 ' + T('=\\lim(' + xm(p.r) + ')') + '。',
      '代 ' + T('x=' + a) + '：' + T(a + sg(-p.r) + '=' + fT(sxF(p.L))) + '。' + sxFin(o)];
    return ['分母 ' + T('\\to 0') + '，分子也必須 ' + T('\\to 0') + '：' + T('\\sqrt{' + a + '+k}=' + p.c) + ' ⟹ ' + T('k=' + p.k) + '。',
      '分子有理化：' + T('\\dfrac{\\sqrt{' + polyT([1, p.k]) + '}-' + p.c + '}{' + xm(a) + '}=\\dfrac{1}{\\sqrt{' + polyT([1, p.k]) + '}+' + p.c + '}') + '。',
      '代 ' + T('x=' + a) + '：' + T('\\dfrac{1}{' + p.c + '+' + p.c + '}=' + fT(sxF(p.L))) + '。' + sxFin(o)];
  };
  L1_SOL.contParam = function (p, o) {
    var c = p.c, K = fT(sxF(p.k));
    if (p.kind === 0) return ['右極限與函數值：' + T('f(' + c + ')=' + pp(c) + '^2' + sg(p.b) + '=' + (c * c + p.b)) + '。', '左極限：' + T(LX(c, '-') + '(' + polyT([p.a, 0]) + '+k)=' + (p.a * c) + '+k') + '。', '連續 ⟺ 相等：' + T((p.a * c) + '+k=' + (c * c + p.b)) + ' ⟹ ' + T('k=' + K) + '。' + sxFin(o)];
    if (p.kind === 1) { var qq = -c * c - p.p * c, rr = -(c + p.p); return ['連續 ⟺ ' + T(LX(c) + 'f(x)=f(' + c + ')=k') + '。', '分子 ' + T(polyT([1, p.p, qq]) + '=' + pxm(c) + pxm(rr)) + '，約分後 ' + T(LX(c) + '(' + xm(rr) + ')=' + c + sg(-rr) + '=' + (2 * c + p.p)) + '。', T('k=' + K) + '。' + sxFin(o)]; }
    if (p.kind === 2) { var b = p.b, m = p.m; return ['連續 ⟺ ' + T('k=' + LX(c) + 'f(x)') + '，這是 ' + T('\\frac{0}{0}') + ' 型。', '分子有理化：' + T('\\dfrac{\\sqrt{' + polyT([1, b]) + '}-' + m + '}{' + xm(c) + '}=\\dfrac{1}{\\sqrt{' + polyT([1, b]) + '}+' + m + '}') + '。', '代 ' + T('x=' + c) + '：' + T('\\dfrac{1}{' + m + '+' + m + '}=' + K) + '。' + sxFin(o)]; }
    var rhs = 2 * c + p.b, cst = rhs - Fr.num(sxF(p.k)) * c * c;
    return ['右極限與函數值：' + T('f(' + c + ')=2' + pp(c) + sg(p.b) + '=' + rhs) + '。', '左極限：' + T(pp(c) + '^2k' + sg(cst) + '=' + (c * c) + 'k' + sg(cst)) + '。', '相等：' + T((c * c) + 'k' + sg(cst) + '=' + rhs) + ' ⟹ ' + T('k=' + K) + '。' + sxFin(o)];
  };
  L1_SOL.gaussDiscont = function (p, o) {
    var a = p.a, b = p.b, k = p.k;
    if (p.kind === 0) return [T('[' + k + 'x]') + ' 只在 ' + T(k + 'x') + ' 是整數的地方跳（左邊差 ' + T(1) + '）。', T(a + '\\lt x\\lt ' + b) + ' ⟹ ' + T((k * a) + '\\lt ' + k + 'x\\lt ' + (k * b)) + '，中間的整數是 ' + T((k * a + 1) + ',\\ \\ldots,\\ ' + (k * b - 1)) + '，共 ' + T(p.cnt) + ' 個，各對應一個 ' + T('x=\\frac{m}{' + k + '}') + '。', sxFin(o)];
    if (p.kind === 1) return [T('[x^2]') + ' 只在 ' + T('x^2') + ' 是整數的地方跳。', T('0\\lt x\\lt ' + b) + ' ⟹ ' + T('0\\lt x^2\\lt ' + (b * b)) + '，' + T('x^2=1,\\ 2,\\ \\ldots,\\ ' + (b * b - 1)) + '，即 ' + T('x=1,\\ \\sqrt{2},\\ \\ldots') + '，共 ' + T(p.cnt) + ' 個。', sxFin(o)];
    return [(p.kind === 2 ? T('[x]+[-x]') + ' 在整數點是 ' + T(0) + '、其他地方都是 ' + T(-1) : T('x-[x]') + ' 在每個整數點左極限是 ' + T(1) + '、函數值是 ' + T(0)) + ' ⟹ 只在整數點不連續。', T(a + '\\lt x\\lt ' + b) + ' 裡的整數是 ' + T((a + 1) + ',\\ \\ldots,\\ ' + (b - 1)) + '，共 ' + T(p.cnt) + ' 個。', sxFin(o)];
  };
  function sxIvt(p, x) {
    if (p.kind === 0) return F(x * x * x + p.p * x + p.q);
    if (p.kind === 1) return F(Math.pow(x, 5) + p.p * x + p.q);
    return Fr.add(x >= 0 ? F(Math.pow(2, x)) : F(1, Math.pow(2, -x)), F(p.p * x - p.q));
  }
  L1_SOL.ivtRoot = function (p, o) {
    var n = p.n, f0 = sxIvt(p, n), f1 = sxIvt(p, n + 1);
    return ['代相鄰整數找變號：' + T('f(' + n + ')=' + fT(f0) + '\\lt 0') + '、' + T('f(' + (n + 1) + ')=' + fT(f1) + '\\gt 0') + '。',
      T('f') + ' 是連續函數，' + T('f(' + n + ')') + ' 與 ' + T('f(' + (n + 1) + ')') + ' 異號 ⟹ 由勘根定理，' + T(n + '\\lt x\\lt ' + (n + 1)) + ' 之間有根；又 ' + T('f') + ' 嚴格遞增只有一個根，就是 ' + T('\\alpha') + '。' + sxFin(o)];
  };

  var L1_H1 = {
    seqRational: '這是「有理式數列的極限」：分子分母同除以分母的最高次，再比較分子、分母的次數。',
    rPow: '這是「r 的 n 次方」：只看底數 r 的絕對值和 1 比大小，r 等於負 1 要特別小心。',
    expDiv: '這是「指數型數列」：分子分母同除以最大的底的 n 次方，比它小的底都會趨近 0。',
    rootRat: '這是「根號減根號」：先乘以共軛式有理化，再同除以 n。',
    squeezeFloor: '這是「高斯符號的夾擠」：先寫出 t 減 1 小於 [t]、[t] 小於等於 t，三邊同除，再用夾擠定理。',
    recurLimit: '這是「遞迴數列」：前幾項照遞迴式一項一項代；求極限時令極限為 L，代進遞迴式兩邊解 L。',
    newtonSqrt: '這是「牛頓求根法」：照迭代式把前一項代進去算下一項；極限 L 滿足 L 等於迭代式本身。',
    compound: '這是「常數 e」：把式子湊成「1 加 t 分之 1」的 t 次方，它趨近 e，外面再補次方。',
    telescoping: '這是「裂項相消」：把一般項拆成兩個分式相減，寫出部分和看哪些項互相消掉，再取極限。',
    geoSum: '這是「無窮等比級數」：先找首項和公比，公比的絕對值小於 1 才收斂，和是首項除以 1 減公比。',
    geoXRange: '這是「無窮等比級數的收斂條件」：寫出公比，令公比的絕對值小於 1，解不等式。',
    geoSplit: '這是「兩個等比級數相加」：把分子拆開，各自是一個無窮等比級數，分別求和再相加。',
    repDec: '這是「循環小數化分數」：乘以 10 的次方讓循環節對齊，兩式相減消掉無窮的循環部分。',
    domain: '這是「函數的定義域」：根號裡要大於等於 0、分母不能是 0，把所有條件取交集。',
    parity: '這是「奇偶性」：把 x 換成負 x 算 f(負 x)，和 f(x)、負 f(x) 比較。',
    compose: '這是「合成函數」：由內往外，先算右邊那個函數，再把結果整個代進左邊那個函數。',
    inverse: '這是「反函數」：令 y 等於 f(x)，解出 x，再把 x 和 y 互換。',
    gaussVal: '這是「高斯符號求值」：每一項找出夾住它的兩個相鄰整數，取比較小的那個，負數要特別小心。',
    limSub: '這是「連續函數的極限」：先確認分母不是 0、根號裡是正的，就直接代入。',
    oneSided: '這是「左右極限」：接縫兩側分開算，絕對值、高斯符號要依左右側拆掉，兩邊相等極限才存在。',
    limFactor: '這是「分式函數的極限」：先代入檢查是不是 0 比 0；是的話分子分母都有共同因式，約掉再代。',
    limRational: '這是「0 比 0 的根式」：乘以共軛式有理化，約掉讓分母變 0 的因式，再代入。',
    limParam: '這是「已知極限存在求參數」：分母趨近 0 而極限存在，分子也一定趨近 0，先由這個條件解參數。',
    contParam: '這是「分段函數連續」：在接縫處令左極限、右極限、函數值三者相等，解出參數。',
    gaussDiscont: '這是「高斯函數的不連續點」：中括號裡的式子跨過整數的地方就會跳，數一數範圍內有幾個這樣的點。',
    ivtRoot: '這是「勘根定理」：連續函數在兩個相鄰整數的函數值異號，中間就有根；從 0 開始代整數找變號。'
  };
  /* ── 2026-10-23 補的三型：步驟與第一層提示 ── */
  L1_SOL.contCheck = function (p, o) {
    var c = p.c, s = [];
    if (p.kind === 0) {
      var lim = c - p.r;
      s.push('① 函數值：' + T('f(' + c + ')=' + p.k) + '，有定義。');
      s.push('② 極限：' + T('x\\ne ' + c) + ' 時分子 ' + T('=' + pxm(c) + pxm(p.r)) + '，約分得 ' + T(xm(p.r)) + '，' + T(LX(c) + 'f(x)=' + sxEq(c + sg(-p.r), String(lim))) + '，存在。');
      s.push('③ 比較：極限 ' + T(lim) + (lim === p.k ? ' ＝ ' : ' ≠ ') + '函數值 ' + T(p.k) + '。' + sxFin(o));
      return s;
    }
    if (p.kind === 1) return ['① 函數值：代 ' + T('x=' + c) + ' 分母是 ' + T(0) + '，' + T('f(' + c + ')') + ' 沒有定義——第一個條件就不成立。', '（雖然約分後 ' + T(LX(c) + 'f(x)=' + (c - p.r)) + ' 存在，但連續要三個條件都成立。）' + sxFin(o)];
    if (p.kind === 2 || p.kind === 3) {
      var p2 = p.p2.map(sxF), vR = pval(p2, F(c)), vL = pval(p.p1, F(c));
      return ['① 函數值：' + T('f(' + c + ')=' + polyT(p2).replace(/x/g, '(' + c + ')') + '=' + fT(vR)) + '，有定義。',
        '② 右極限 ' + T('=' + fT(vR)) + '、左極限 ' + T('=' + polyT(p.p1).replace(/x/g, '(' + c + ')') + '=' + fT(vL)) + '，' + (Fr.eq(vR, vL) ? '相等，極限存在。' : '不相等，極限不存在。'),
        (Fr.eq(vR, vL) ? '③ 極限 ＝ 函數值 ＝ ' + T(fT(vR)) + '。' : '第二個條件不成立，就不必再看第三個。') + sxFin(o)];
    }
    var cc = sxF(p.c), m = p.m;
    if (cc.d === 1) return ['① ' + T('f(' + cc.n + ')=' + pp(m) + '(' + cc.n + ')+' + pp(cc.n) + '=' + (m * cc.n + cc.n)) + '，有定義。',
      '② 右側 ' + T('[x]=' + cc.n) + '：右極限 ' + T('=' + (m * cc.n + cc.n)) + '；左側 ' + T('[x]=' + (cc.n - 1)) + '：左極限 ' + T('=' + (m * (cc.n - 1) + cc.n)) + '，不相等，極限不存在。' + sxFin(o)];
    var fl = Math.floor(Fr.num(cc));
    return ['在 ' + T('x=' + fT(cc)) + ' 附近（' + T(fl + '\\lt x\\lt ' + (fl + 1)) + '）' + T('[x]=' + fl) + ' 是常數，' + T('f(x)=' + (m * fl) + '+x') + ' 是多項式。', '三個條件都成立：' + T('f\\left(' + fT(cc) + '\\right)=' + fT(Fr.add(m * fl, cc))) + ' ＝ 極限。' + sxFin(o)];
  };
  L1_SOL.squeezeFunc = function (p, o) {
    if (p.kind === 0) {
      var g1 = p.g1.map(sxF), a = p.a, va = pval(p.g2, F(a));
      return ['兩邊都是多項式（連續），' + T('x\\to ' + a) + ' 的極限就是代入：左邊 ' + T(LX(a) + '(' + polyT(g1) + ')=' + fT(pval(g1, F(a)))) + '、右邊 ' + T(LX(a) + '(' + polyT(p.g2) + ')=' + fT(va)) + '。',
        '左右兩邊的極限相同，' + T('f(x)') + ' 被夾在中間 ⟹ 由夾擠定理 ' + T(LX(a) + 'f(x)=' + fT(va)) + '。' + sxFin(o)];
    }
    if (p.kind === 1) {
      var L = fT(sxF(p.L)), k = p.k === 1 ? '' : p.k, e = p.m === 1 ? '' : '^{' + p.m + '}';
      return ['把絕對值不等式拆開：' + T(L + '-' + k + '\\left|' + xm(p.a) + '\\right|' + e + '\\le f(x)\\le ' + L + '+' + k + '\\left|' + xm(p.a) + '\\right|' + e) + '。',
        T('x\\to ' + p.a) + ' 時 ' + T('\\left|' + xm(p.a) + '\\right|\\to 0') + '，左右兩邊都趨近 ' + T(L) + ' ⟹ 由夾擠定理，' + T(LX(p.a) + 'f(x)=' + L) + '。' + sxFin(o)];
    }
    var e2 = p.m === 1 ? '' : '^{' + p.m + '}', B = Math.abs(p.b);
    return [T('-1\\le ' + p.fn + '\\dfrac{' + p.k + '}{x}\\le 1') + '，所以 ' + T('-' + (B === 1 ? '' : B) + '|x|' + e2 + '\\le ' + cf(p.b) + 'x' + e2 + p.fn + '\\dfrac{' + p.k + '}{x}\\le ' + (B === 1 ? '' : B) + '|x|' + e2) + '。',
      T('x\\to 0') + ' 時兩邊都趨近 ' + T(0) + ' ⟹ 中間那一項趨近 ' + T(0) + '（夾擠定理），原式 ' + T('\\to ' + p.c + '+0=' + p.c) + '。' + sxFin(o)];
  };
  L1_SOL.geoApply = function (p, o) {
    var s = p.s, rv = sxF(p.r), r2 = Fr.mul(rv, rv);
    if (p.kind === 0) return ['面積依序是 ' + T(s + '^2,\\ (' + s + '\\cdot ' + fS(rv) + ')^2,\\ \\ldots') + '：首項 ' + T(s * s) + '、公比 ' + T(fT(r2)) + '。', T('|r|\\lt 1') + '，總和 ' + T('=\\dfrac{' + (s * s) + '}{1-' + fS(r2) + '}=' + fT(Fr.div(s * s, Fr.sub(1, r2)))) + '。' + sxFin(o)];
    if (p.kind === 1) return ['面積依序是 ' + T('\\pi\\cdot ' + s + '^2,\\ \\pi\\left(' + s + '\\cdot ' + fS(rv) + '\\right)^2,\\ \\ldots') + '：首項 ' + T((s * s) + '\\pi') + '、公比 ' + T(fT(r2)) + '。', '總和 ' + T('=\\dfrac{' + (s * s) + '\\pi}{1-' + fS(r2) + '}') + '。' + sxFin(o)];
    if (p.kind === 2) return ['反彈上升的高度依序是 ' + T(s + '\\cdot ' + fS(rv) + ',\\ ' + s + '\\cdot ' + fS(r2) + ',\\ \\ldots') + '：首項 ' + T(fT(Fr.mul(s, rv))) + '、公比 ' + T(fT(rv)) + '。', '總和 ' + T('=\\dfrac{' + fT(Fr.mul(s, rv)) + '}{1-' + fS(rv) + '}=' + fT(Fr.div(Fr.mul(s, rv), Fr.sub(1, rv)))) + '。' + sxFin(o)];
    return ['每天的距離 ' + T(s + ',\\ ' + s + '\\cdot ' + fS(rv) + ',\\ \\ldots') + '：首項 ' + T(s) + '、公比 ' + T(fT(rv)) + '。', '總和 ' + T('=\\dfrac{' + s + '}{1-' + fS(rv) + '}=' + fT(Fr.div(s, Fr.sub(1, rv)))) + '。' + sxFin(o)];
  };
  L1_H1.contCheck = '這是「連續的三個條件」：依序檢查函數值有沒有定義、極限存不存在（左右極限相等）、兩者相不相等。';
  L1_H1.squeezeFunc = '這是「函數版的夾擠定理」：把要求的函數夾在兩個極限算得出來的式子中間，兩邊極限相同就是答案。';
  L1_H1.geoApply = '這是「無窮等比級數的應用」：先寫出前兩、三項，找出首項和公比（面積要用比例的平方），再用首項除以 1 減公比。';
  var META_L1 = [
      ['rPow', '1-1 rⁿ 的收斂與發散'], ['seqRational', '1-2 有理式數列：看最高次'], ['expDiv', '1-2 指數型：同除以最大的底'], ['rootRat', '1-2 根式有理化'],
      ['squeezeFloor', '1-3 夾擠定理：[αn]／n 型'], ['recurLimit', '1-4 遞迴數列的極限'], ['newtonSqrt', '1-4 牛頓求根法'], ['compound', '1-5 連續複利與 e'],
      ['telescoping', '2-1 裂項相消求級數和'], ['geoSum', '2-2 無窮等比級數求和'], ['geoXRange', '2-2 收斂條件求 x 的範圍'], ['geoSplit', '2-2 拆成兩個等比級數'], ['repDec', '2-3 循環小數化分數'], ['geoApply', '2-4 無窮等比的應用：找首項與公比'],
      ['domain', '3-1 函數的定義域'], ['parity', '3-2 奇函數與偶函數'], ['compose', '3-3 合成函數'], ['inverse', '3-4 反函數'], ['gaussVal', '3-5 高斯函數求值'],
      ['limSub', '4-1 直接代入求極限'], ['limFactor', '4-2 0/0 型：因式分解'], ['limRational', '4-2 0/0 型：有理化'], ['limParam', '4-2 已知極限存在求參數'], ['oneSided', '4-3 左右極限：絕對值、高斯、分段'], ['squeezeFunc', '4-4 函數版夾擠定理'],
      ['contCheck', '5-1 連續的三個條件'], ['contParam', '5-2 分段函數連續求參數'], ['gaussDiscont', '5-2 高斯函數的不連續點'], ['ivtRoot', '5-3 勘根定理找根的位置']
  ];
  var META_L2 = [
      ['geoParamSum', '2-2 含參數的無窮等比級數：收斂且和為定值'], ['geoXFunc', '2-2 x 的無窮等比級數：收斂範圍與和函數'],
      ['squeezeL2', '1-3 夾擠定理求數列極限'], ['seqLimitL2', '1-2 數列極限綜合：連加公式、根式'], ['limFuncDef', '1-1 以數列極限定義的函數'],
      ['composeInv', '3-3 合成函數：拆解、定義域、反函數'], ['limTwoParam', '4-2 0/0 待定係數求兩個參數'], ['telescopeL2', '2-1 裂項、部分和與發散'],
      ['contTwoParam', '5-2 分段函數連續求兩個參數'], ['inverseL2', '3-4 反函數綜合'], ['limAbsGauss', '4-3 絕對值與高斯函數的極限'], ['gaussEq', '3-5 高斯函數方程式與不等式'],
      ['repDecOps', '2-3 循環小數綜合'], ['recurL2', '1-4 遞迴數列：極限與一般項'], ['similarArea', '2-4 無窮多個相似圖形與彈跳球'], ['firstSuccess', '2-4 輪流擲骰，先成功者勝'], ['ivtCount', '5-3 介值定理：根的個數與位置']
  ];

  /* ══════════════════════════════════════════════════════════
     L0　章首先備診斷（5 型）：等比數列（高一下 ch1）、多項式因式分解（高一上 ch3）、根式有理化（高一上 ch1）、指數與對數（高二上 ch2）、二次函數圖形（國中／高一上 ch3）
     ══════════════════════════════════════════════════════════ */
  var L0 = {};
  L0.geoSeq = function (r) {
    r();
    var a1 = r.nz(-5, 5), rv = r.pick([F(2), F(3), F(-2), F(1, 2), F(-1, 2), F(-3), F(1, 3)]), k = r.int(4, 7), S;
    S = Fr.div(Fr.mul(a1, Fr.sub(1, Fr.pow(rv, k))), Fr.sub(1, rv));
    var an = cf(a1) + (rv.d === 1 && rv.n > 0 ? (a1 === 1 || a1 === -1 ? '' : '\\cdot ') + rv.n : (rv.d === 1 ? '(' + rv.n + ')' : '\\left(' + fT(rv) + '\\right)')) + '^{n-1}';
    var q = '等比數列的首項 ' + T('a_1=' + a1) + '、公比 ' + T('r=' + fT(rv)) + '。' + no(1) + '寫出一般項 ' + T('a_n') + '。' + no(2) + '求前 ' + T(k) + ' 項的和 ' + T('S_{' + k + '}') + '。';
    var h = no(1) + T('a_n=a_1r^{n-1}') + '。' + no(2) + T('S_n=\\dfrac{a_1(1-r^n)}{1-r}') + '，代 ' + T('a_1=' + a1) + '、' + T('r=' + fT(rv)) + '、' + T('n=' + k) + '。這一章的無窮等比級數，就是讓這裡的 ' + T('n\\to\\infty') + '：' + T('|r|\\lt 1') + ' 時 ' + T('r^n\\to 0') + '。';
    return { q: q, a: jo([no(1) + T('a_n=' + an), no(2) + T('S_{' + k + '}=' + fT(S))]), h: h, p: { a1: a1, r: fp(rv), k: k } };
  };
  L0.polyFactor = function (r) {
    r();
    var kind = r.int(0, 2), m1, m2, a, q, ans, h, P;
    if (kind === 0) {
      m1 = r.nz(-7, 7); do { m2 = r.nz(-7, 7); } while (m2 === m1 || m1 + m2 === 0 && r() < 0.5);
      P = pmul([1, -m1], [1, -m2]);
      ans = pxm(m1) + pxm(m2);
      h = '找兩數乘積 ' + T(fT(P[2])) + '、和 ' + T(fT(Fr.neg(P[1]))) + '（十字交乘）。這一章的 ' + T('\\frac{0}{0}') + ' 型：代 ' + T('x=a') + ' 分子分母都是 ' + T(0) + '，就一定都有因式 ' + T('(x-a)') + '。';
    } else {
      a = r.int(1, 5); var plus = kind === 2;
      P = [1, 0, 0, plus ? a * a * a : -a * a * a];
      ans = plus ? '(x+' + a + ')(' + polyT([1, -a, a * a]) + ')' : '(x-' + a + ')(' + polyT([1, a, a * a]) + ')';
      h = (plus ? '立方和' : '立方差') + '公式：' + T(plus ? 'x^3+a^3=(x+a)(x^2-ax+a^2)' : 'x^3-a^3=(x-a)(x^2+ax+a^2)') + '，這題 ' + T((a * a * a) + '=' + a + '^3') + '，' + T('a=' + a) + '。';
    }
    q = '因式分解 ' + T(polyT(P)) + '（在整係數範圍內分解到不能再分解）。';
    return { q: q, a: T(ans), h: h, p: { kind: kind, m1: m1, m2: m2, a: a } };
  };
  L0.ratRoot = function (r) {
    r();
    var kind = r.int(0, 1), a, b, c = r.int(1, 9), k, q, ans, h, den, g;
    var SQ = [2, 3, 5, 6, 7, 10, 11];
    if (kind === 0) {
      a = r.pick(SQ); do { b = r.pick(SQ); } while (b === a); if (a < b) { var t = a; a = b; b = t; }
      den = a - b; g = gcd(c, den);
      var sum = '\\sqrt{' + a + '}+\\sqrt{' + b + '}';
      ans = den / g === 1 ? (c / g === 1 ? sum : c / g + '(' + sum + ')') : '\\dfrac{' + (c / g === 1 ? sum : c / g + '(' + sum + ')') + '}{' + den / g + '}';
      q = '把 ' + T('\\dfrac{' + c + '}{\\sqrt{' + a + '}-\\sqrt{' + b + '}}') + ' 的分母有理化。';
      h = '分子分母同乘 ' + T(sum) + '：分母變成 ' + T('(\\sqrt{' + a + '})^2-(\\sqrt{' + b + '})^2=' + den) + '。這一章求 ' + T('\\sqrt{\\ }-\\sqrt{\\ }') + ' 的極限，第一步都是這個動作。';
    } else {
      a = r.pick(SQ); do { k = r.int(1, 4); } while (k * k === a);
      den = a - k * k; g = gcd(c, Math.abs(den));
      /* 分母 a-k^2 是負數時，把負號吸進括號：-(√a-k) 寫成 (k-√a)，不要寫成 -√a-k（2026-10-22 驗算器抓到的 bug） */
      var cj = '\\sqrt{' + a + '}-' + k, sgn = den < 0 ? -1 : 1, nn = c / g, dd = Math.abs(den) / g;
      var cj2 = sgn < 0 ? k + '-\\sqrt{' + a + '}' : cj;
      var body = nn === 1 ? cj2 : nn + '(' + cj2 + ')';
      ans = dd === 1 ? body : '\\dfrac{' + body + '}{' + dd + '}';
      q = '把 ' + T('\\dfrac{' + c + '}{\\sqrt{' + a + '}+' + k + '}') + ' 的分母有理化。';
      h = '分子分母同乘 ' + T(cj) + '：分母變成 ' + T(a + '-' + (k * k) + '=' + den) + '。';
    }
    return { q: q, a: T(ans), h: h, p: { kind: kind, a: a, b: b, c: c, k: k } };
  };
  L0.expLog = function (r) {
    r();
    var kind = r.int(0, 2), q, ans, h, b, m, n, p, qq, A, B;
    if (kind === 0) {
      b = r.pick([2, 3, 5]); m = r.int(1, 4); n = r.int(-2, 3);
      do { A = r.pick([3, 6, 7, 12, 10, 14, 15, 20, 24]); } while (A % b === 0 && r() < 0.5);
      var num = A * Math.pow(b, m + Math.max(n, 0)), dn = Math.pow(b, Math.max(-n, 0));
      /* log_b(num/dn) - log_b A = m + n */
      q = '求 ' + T('\\log_{' + b + '}' + (dn === 1 ? num : '\\dfrac{' + num + '}{' + dn + '}') + '-\\log_{' + b + '}' + A) + '。';
      ans = String(m + n);
      h = '同底相減 ＝ 真數相除：' + T('\\log_{' + b + '}\\dfrac{' + (dn === 1 ? num : '\\frac{' + num + '}{' + dn + '}') + '}{' + A + '}') + '，再看真數是 ' + T(b) + ' 的幾次方。';
    } else if (kind === 1) {
      b = r.int(2, 5); qq = r.pick([2, 3]); p = r.nz(-4, 4); while (gcd(Math.abs(p), qq) !== 1) p = r.nz(-4, 4);
      var base = Math.pow(b, qq);
      q = '求 ' + T(base + '^{' + fS(F(p, qq)) + '}') + '。';
      ans = fT(Fr.pow(p > 0 ? F(b) : F(1, b), Math.abs(p)));
      h = T(base + '=' + b + '^{' + qq + '}') + ' ⟹ ' + T(base + '^{' + fS(F(p, qq)) + '}=' + b + '^{' + qq + '\\cdot ' + fS(F(p, qq)) + '}') + '。';
    } else {
      b = r.pick([2, 3, 10]); m = r.int(1, 4); var e = r.int(1, 3);
      q = '求 ' + T('\\log_{' + b + '}\\sqrt[' + (e + 1) + ']{' + Math.pow(b, m) + '}') + '。';
      ans = fT(F(m, e + 1));
      h = T('\\sqrt[' + (e + 1) + ']{' + Math.pow(b, m) + '}=' + b + '^{\\frac{' + m + '}{' + (e + 1) + '}}') + '，而 ' + T('\\log_{' + b + '}' + b + '^{t}=t') + '。這一章的 ' + T('\\ln x=\\log_{e}x') + ' 也照這些規則算。';
    }
    return { q: q, a: T(ans), h: h, p: { kind: kind } };
  };
  L0.quadVertex = function (r) {
    r();
    var a = r.nz(-3, 3), hh = r.int(-4, 4), k = r.int(-6, 6), P = [a, -2 * a * hh, a * hh * hh + k];
    var q = '二次函數 ' + T('y=' + polyT(P)) + '。' + no(1) + '求頂點坐標。' + no(2) + '圖形開口向上還是向下？';
    var h = (hh === 0 ? '沒有一次項：' + T('y=' + polyT(P)) + ' 的對稱軸就是 ' + T('x=0') + '（' + T('y') + ' 軸）'
      : '配方：' + T('y=' + cf(a) + '\\left(x^2' + sg(-2 * hh) + 'x\\right)' + sg(a * hh * hh + k)) + '，括號裡補上 ' + T('(' + (-hh) + ')^2') + ' 再扣掉') + '；' + T('x^2') + ' 的係數 ' + T(a) + ' 決定開口。這一章看函數圖形（定義域、值域、反函數）都從這裡出發。';
    return { q: q, a: jo([no(1) + T('(' + hh + ',' + k + ')'), no(2) + (a > 0 ? '向上' : '向下')]), h: h, p: { a: a, h: hh, k: k } };
  };
  var META_L0 = [['geoSeq', '等比數列的一般項與前 n 項和'], ['polyFactor', '多項式的因式分解'], ['ratRoot', '分母有理化'], ['expLog', '指數與對數的運算'], ['quadVertex', '二次函數的頂點與開口']];
  /* 先備題型 → 該去哪裡複習 */
  var PREREQ = {
    geoSeq: { txt: '等比數列的一般項與有限項和（高一下第一章 數列與級數）：無窮等比級數就是讓前 n 項和的 n 趨近無限大', link: '../g10b-ch01/practice.html#L1' },
    polyFactor: { txt: '多項式的因式分解與除法（高一上第三章 多項式函數）：0/0 型的極限要先找出共同因式約掉', link: '../g10a-ch03/practice.html#L1' },
    ratRoot: { txt: '分式與根式的有理化（高一上第一章 數與式）：根式的極限、0/0 型都要先有理化', link: '../g10a-ch01/practice.html#L1' },
    expLog: { txt: '指數律與對數律（高二上第二章 指數與對數函數）：連續複利、常數 e 與 ln 都要用到', link: '../g11a-ch02/practice.html#L1' },
    quadVertex: { txt: '一次與二次函數的圖形（國中、高一上第三章 多項式函數）：定義域、值域、反函數都要會看圖', link: '../g10a-ch03/practice.html#L1' }
  };
  /* ══════════════════════════════════════════════════════════
     對照題：同一型抽兩題，只差一個關鍵特徵（f 由 p 算出；keep 的欄位要相同）
     ══════════════════════════════════════════════════════════ */
  var CONTRAST = {
    'L1.rPow': { f: function (p) { return p.lim === null ? 'div' : 'conv'; }, why: '數列 $r^n$ 只看 $r$：<b>$-1\\lt r\\lt 1$</b> 收斂到 $0$；<b>$r=1$</b> 是常數 $1$；<b>$r=-1$</b> 在 $1$ 與 $-1$ 之間跳，<b>發散</b>；<b>$|r|\\gt 1$</b> 越來越大（或正負跳著越來越大），發散。小心 $(-1)^{2n}$ 其實就是 $1^n$。' },
    'L1.seqRational': { f: function (p) { return p.num.length === p.den.length ? 0 : (p.num.length < p.den.length ? -1 : 1); }, why: '有理式數列同除以分母的最高次：<b>分子分母同次</b> ⟹ 極限是最高次係數的比；<b>分子次數較低</b> ⟹ 極限是 $0$；<b>分子次數較高</b> ⟹ 分子還剩 $n$ 的正次方，越來越大，發散。' },
    'L1.expDiv': { f: function (p) { return p.p > p.q ? 'p' : 'q'; }, why: '指數型一律<b>同除以最大的底</b>的 $n$ 次方：比它小的底都變成 $\\left(\\frac{\\text{小}}{\\text{大}}\\right)^n\\to 0$。最大的底出現在哪一項，就由那一項的係數決定極限——兩題最大的底換了位置，答案也跟著換成另一組係數的比。' },
    'L1.geoSum': { f: function (p) { return p.S === null ? 'div' : 'conv'; }, why: '無窮等比級數<b>先看公比</b>：$|r|\\lt 1$ 才收斂，和是 $\\dfrac{a}{1-r}$；$|r|\\ge 1$ 時部分和沒有極限，不能套公式（套下去會得到一個假的數字，例如 $r=2$ 時 $\\frac{a}{1-2}=-a$）。' },
    'L1.geoXRange': { f: function (p) { return p.kind === 3 ? 'out' : 'in'; }, why: '收斂條件永遠是 <b>$|\\text{公比}|\\lt 1$</b>，但公比長怎樣會改變答案的樣子：公比是 $\\frac{x-b}{c}$（$x$ 在分子）⟹ $|x-b|\\lt c$，答案是<b>一段</b>；公比是 $\\frac{c}{x-b}$（$x$ 在分母）⟹ $|x-b|\\gt c$，答案是<b>兩段</b>。' },
    'L1.repDec': { f: function (p) { return p.nr === '' ? 'pure' : 'mixed'; }, why: '<b>純循環</b>（小數點後立刻循環）乘 $10^{\\text{循環節長}}$ 再減原數；<b>混循環</b>（前面有不循環的數字）要先乘 $10$ 的次方把不循環的部分移到小數點左邊，再做一次，用兩式相減。分母因此多出 $10$ 的因數。' },
    'L1.parity': { f: function (p) { return p.lab; }, why: '判斷奇偶一律算 $f(-x)$：等於 $f(x)$ 是偶函數（圖形對 $y$ 軸對稱）、等於 $-f(x)$ 是奇函數（對原點對稱）、兩個都不是就是非奇非偶。多項式只有偶次項 ⟹ 偶；只有奇次項 ⟹ 奇；<b>有常數項的奇次多項式</b>就不是奇函數了。' },
    'L1.compose': { f: function (p) { return p.ord; }, why: '$(f\\circ g)(x)=f(g(x))$：<b>先做右邊的 $g$</b>，再把結果丟給 $f$。順序一換，$(g\\circ f)(x)=g(f(x))$ 通常是完全不同的函數——合成函數沒有交換律。' },
    'L1.limFactor': { f: function (p) { return p.val === null ? 'none' : 'ok'; }, why: '代入 $x=a$ 先檢查：<b>分子分母都是 $0$</b>（$\\frac00$ 型）⟹ 都有因式 $(x-a)$，約掉再代；<b>只有分母是 $0$</b> ⟹ 商的絕對值越來越大，而且左右正負號相反，極限不存在。不先檢查就硬約，會約出錯的答案。' },
    'L1.oneSided': { f: function (p) { return p.R[0] * p.L[1] === p.L[0] * p.R[1] ? 'eq' : 'ne'; }, why: '<b>極限存在 ⟺ 左極限 ＝ 右極限</b>。絕對值、高斯函數、分段函數在「接縫」處左右要分開算：兩邊算出來一樣，極限就存在（和 $f(a)$ 本身是多少無關）；不一樣就不存在。' },
    'L1.compound': { f: function (p) { return (p.ans || p.k)[0] > 0 ? '+' : '-'; }, why: '核心公式只有一個：$\\left(1+\\frac1t\\right)^t\\to e$。把式子湊成 $\\left[\\left(1+\\frac1t\\right)^t\\right]^{k}$ 就得 $e^k$；括號裡是<b>減號</b>時，$\\left(1-\\frac1t\\right)^t\\to e^{-1}$，指數會帶負號。' },
    'L1.inverse': { f: function (p) { return p.kind; }, why: '求反函數的動作都一樣：令 $y=f(x)$、解出 $x$、再把 $x$、$y$ 互換。一次函數解一次方程；分式型 $\\frac{ax+b}{cx+d}$ 要先去分母、把含 $x$ 的項集中；三次方型要開立方。前提是 $f$ 一對一。' },
    'L1.contCheck': { f: function (p) { return p.lab; }, why: '連續要<b>三個條件依序都成立</b>：① $f(a)$ 有定義；② $\lim_{x\to a}f(x)$ 存在（左極限＝右極限）；③ 兩者相等。分母是 $0$ 卡在①；分段接不起來、高斯函數在整數點卡在②；補了洞但補錯值卡在③。極限存在不代表連續。' },
    'L2.telescopeL2': { f: function (p) { return p.kind === 5 ? 'div' : 'conv'; }, why: '非等比級數只看<b>部分和 $S_n$ 有沒有極限</b>：裂項後 $S_n$ 只剩頭尾，尾巴趨近 $0$ ⟹ 收斂；像 $\\sqrt{n+1}-1$ 或 $\\log(n+1)$ 這種尾巴越來越大 ⟹ 發散。<b>每一項都趨近 $0$ 不代表級數收斂</b>。' },
    'L2.limAbsGauss': { f: function (p) { return p.kind; }, why: '絕對值在接縫兩側要拆成正負兩種寫法；高斯函數在整數兩側取不同的整數；夾擠 $x\\left[\\frac kx\\right]$ 則用 $\\frac kx-1\\lt\\left[\\frac kx\\right]\\le\\frac kx$。三種都是「把左右分開、把不好處理的符號換成能算的式子」。' },
    'L2.recurL2': { f: function (p) { return p.kind; }, why: '遞迴數列的極限：<b>若極限存在</b>，令 $\\lim a_n=L$ 代進遞迴式解 $L$（根號型要刪負根）。要一般項就看結構：$a_{n+1}=pa_n+q$ 減掉不動點變等比；$\\frac{a_n}{ka_n+1}$ 取倒數變等差。' },
    'L2.gaussEq': { f: function (p) { return p.kind; }, why: '高斯符號的方程式、不等式都先把 $[\\ ]$ 整塊當成一個<b>整數</b>未知數 $t$ 解出來，再用 $[u]=t\\iff t\\le u\\lt t+1$ 換回 $x$ 的範圍——所以答案都是一段一段「左閉右開」的區間。' }
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

  return { makeRng: makeRng, L0: L0, L1: L1, L2: L2, L3: L3, L3_FIX: L3_FIX, META: META, PREREQ: PREREQ, CONTRAST: CONTRAST, contrastPair: contrastPair, _util: { gcd: gcd, F: F, Fr: Fr, fp: fp, fT: fT, polyT: polyT, pval: pval, pmul: pmul, surdT: surdT, qrT: qrT, sqf: sqf, ivFmt: ivFmt } };
}));
