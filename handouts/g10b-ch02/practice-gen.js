/* ══════════════════════════════════════════════════════════════
   g10b-ch02 排列組合與機率・分級練習本　題目產生器
   ─────────────────────────────────────────────────────────────
   每個產生器：function (rng) → { q, a, h, p }
     q：題目（HTML，可含 KaTeX $…$）   a：答案（HTML）
     h：一行提示                         p：參數與結構化答案（給 verify_gen10b2.py 用窮舉獨立重算）
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
    toNum: function (x) { return x.n / x.d; },
    tex: function (x, small) {
      if (x.d === 1) return String(x.n);
      var f = small ? '\\frac' : '\\dfrac';
      return (x.n < 0 ? '-' : '') + f + '{' + Math.abs(x.n) + '}{' + x.d + '}';
    }
  };
  function fr2(f) { return [f.n, f.d]; }
  function T(s) { return '$' + s + '$'; }
  function fact(n) { var v = 1; for (var i = 2; i <= n; i++) v *= i; return v; }
  function C(n, k) { if (k < 0 || k > n) return 0; k = Math.min(k, n - k); var v = 1; for (var i = 1; i <= k; i++) v = v * (n - k + i) / i; return Math.round(v); }
  function P(n, k) { var v = 1; for (var i = 0; i < k; i++) v *= (n - i); return v; }
  function cT(n, k) { return 'C^{' + n + '}_{' + k + '}'; }
  function pT(n, k) { return 'P^{' + n + '}_{' + k + '}'; }
  function ipow(b, e) { var v = 1; for (var i = 0; i < e; i++) v *= b; return v; }
  function pr(num, den) { return Fr.tex(F(num, den)); }               /* 機率的排版 */
  var NAMES = ['甲', '乙', '丙', '丁', '戊', '己', '庚', '辛'];
  function people(n) { return NAMES.slice(0, n).join('、'); }
  /* 三個位置的排列（供小型窮舉） */
  function perms3(digits, fn) {
    var n = 0;
    for (var i = 0; i < digits.length; i++) for (var j = 0; j < digits.length; j++) for (var k = 0; k < digits.length; k++)
      if (i !== j && j !== k && i !== k && fn(digits[i], digits[j], digits[k])) n++;
    return n;
  }

  /* ═══════════════════════ L1 ═══════════════════════ */
  var L1 = {};

  /* ── §1 計數原理 ── */
  /* 1-1 加法原理 vs 乘法原理：路線 */
  L1.routes = function (r) {
    var a = r.int(2, 5), b = r.int(2, 5), c = r.int(1, 3);
    var one = a * b + c, rt = one * one;
    return { q: '從甲地到乙地有 ' + T(String(a)) + ' 條路，從乙地到丙地有 ' + T(String(b)) + ' 條路，另外還有 ' + T(String(c)) + ' 條路可以從甲地直達丙地。(1) 從甲地到丙地共有幾種走法？(2) 從甲地到丙地再回到甲地（路線可以重複）共有幾種走法？',
             a: '(1) ' + T(a + '\\times' + b + '+' + c + '=' + one) + ' 種　(2) ' + T(one + '^2=' + rt) + ' 種',
             h: '「經乙地」與「直達」是分類（加），去程與回程是分步（乘）。',
             p: { a: a, b: b, c: c, ans: { one: one, rt: rt } } };
  };
  /* 1-2 乘法原理三變化：密碼 */
  L1.passcode = function (r) {
    var k = r.int(3, 5);
    var a1 = ipow(10, k), a2 = P(10, k), a3 = 9 * P(9, k - 1);
    return { q: '某系統的密碼由 ' + T(String(k)) + ' 個數字組成，每一位都可以是 ' + T('0\\sim9') + '。(1) 若數字可以重複，共有幾組密碼？(2) 若數字不可重複，共有幾組？(3) 若數字不可重複且第一位不能是 ' + T('0') + '，共有幾組？',
             a: '(1) ' + T('10^{' + k + '}=' + a1) + '　(2) ' + T(pT(10, k) + '=' + a2) + '　(3) ' + T('9\\times' + pT(9, k - 1) + '=' + a3),
             h: '(3) 先排最受限的第一位（9 種），其餘 ' + (k - 1) + ' 位從剩下 9 個數字中不重複地排。',
             p: { k: k, ans: { a1: a1, a2: a2, a3: a3 } } };
  };
  /* 1-3 數字排列：含 0 的三位數與偶數 */
  L1.digitsEven = function (r) {
    var m = r.int(4, 7), digits = [];
    for (var i = 0; i <= m; i++) digits.push(i);
    var tot = perms3(digits, function (a) { return a !== 0; });
    var ev = perms3(digits, function (a, b, c) { return a !== 0 && c % 2 === 0; });
    return { q: '用 ' + T(digits.join(',')) + ' 這 ' + T(String(m + 1)) + ' 個數字組成數字不重複的三位數。(1) 共可組成幾個？(2) 其中是偶數的有幾個？',
             a: '(1) ' + T(m + '\\times' + m + '\\times' + (m - 1) + '=' + tot) + ' 個　(2) ' + T(String(ev)) + ' 個',
             h: '(1) 百位不能是 0。(2) 個位是 0 與個位不是 0 兩類分開算——個位不是 0 時，百位要同時避開 0 與個位的數字。',
             p: { m: m, ans: { tot: tot, ev: ev } } };
  };
  /* 1-4 倍數計數（取捨原理） */
  L1.multiples = function (r) {
    var N = r.pick([100, 200, 300, 500, 1000]), pair = r.pick([[2, 3], [2, 5], [3, 5], [3, 4], [4, 6], [3, 7], [2, 7], [5, 7]]), a = pair[0], b = pair[1];
    var l = a * b / gcd(a, b), nA = Math.floor(N / a), nB = Math.floor(N / b), nAB = Math.floor(N / l);
    var kind = r.int(0, 1), ans = kind === 0 ? nA + nB - nAB : nA - nAB;
    var qtxt = kind === 0 ? '是 ' + T(String(a)) + ' 或 ' + T(String(b)) + ' 的倍數' : '是 ' + T(String(a)) + ' 的倍數但不是 ' + T(String(b)) + ' 的倍數';
    return { q: '在 ' + T('1') + ' 到 ' + T(String(N)) + ' 的自然數中，' + qtxt + '的數共有幾個？',
             a: T(String(ans)) + ' 個',
             h: (kind === 0 ? '$n(A\\cup B)=n(A)+n(B)-n(A\\cap B)$' : '$n(A)-n(A\\cap B)$') + '，交集是 ' + T(String(l)) + ' 的倍數（最小公倍數）。',
             p: { N: N, a: a, b: b, kind: kind, ans: ans } };
  };
  /* 1-5 三集合取捨（文氏圖七區） */
  L1.venn3 = function (r) {
    var oA = r.int(4, 15), oB = r.int(4, 15), oC = r.int(3, 12), ab = r.int(2, 8), bc = r.int(2, 8), ac = r.int(2, 8), abc = r.int(1, 6), none = r.int(2, 12);
    var A = oA + ab + ac + abc, B = oB + ab + bc + abc, Cc = oC + ac + bc + abc, AB = ab + abc, BC = bc + abc, AC = ac + abc;
    var union = A + B + Cc - AB - BC - AC + abc, N = union + none, only = oA + oB + oC;
    return { q: '某班共 ' + T(String(N)) + ' 人，調查參加社團的情形：參加 A 社的 ' + T(String(A)) + ' 人、B 社的 ' + T(String(B)) + ' 人、C 社的 ' + T(String(Cc)) + ' 人；同時參加 A、B 的 ' + T(String(AB)) + ' 人、B、C 的 ' + T(String(BC)) + ' 人、A、C 的 ' + T(String(AC)) + ' 人；三社都參加的 ' + T(String(abc)) + ' 人。(1) 至少參加一個社團的有幾人？(2) 三社都沒參加的有幾人？(3) 恰參加一個社團的有幾人？',
             a: '(1) ' + T(String(union)) + ' 人　(2) ' + T(String(none)) + ' 人　(3) ' + T(String(only)) + ' 人',
             h: '(1) 三集合取捨：加三個、減三個、再加回三個都有的。(3) 從最裡面往外填七塊區域，再把「只有一個」的三塊相加。',
             p: { N: N, A: A, B: B, C: Cc, AB: AB, BC: BC, AC: AC, ABC: abc, ans: { union: union, none: none, only: only } } };
  };
  /* 1-6 補集法：「至少」 */
  L1.complement = function (r) {
    var kind = r.int(0, 2), q, a, h, p;
    if (kind === 0) {
      var n = r.int(2, 4), tot = ipow(6, n), bad = ipow(5, n);
      q = '擲一顆公正骰子 ' + T(String(n)) + ' 次，依序記錄點數。至少有一次出現 ' + T('6') + ' 點的情形有幾種？';
      a = T('6^{' + n + '}-5^{' + n + '}=' + (tot - bad)) + ' 種'; h = '反面是「每一次都不是 6 點」，每次只有 5 種。'; p = { kind: 0, n: n, ans: tot - bad };
    } else if (kind === 1) {
      var k = r.int(3, 4), d = r.int(1, 9), t2 = ipow(10, k), b2 = ipow(9, k);
      q = '由 ' + T('0\\sim9') + ' 組成 ' + T(String(k)) + ' 位數的密碼（數字可重複），其中至少出現一個 ' + T(String(d)) + ' 的密碼有幾組？';
      a = T('10^{' + k + '}-9^{' + k + '}=' + (t2 - b2)) + ' 組'; h = '反面是「沒有任何一位是 ' + d + '」，每一位只剩 9 種。'; p = { kind: 1, k: k, d: d, ans: t2 - b2 };
    } else {
      var m = r.int(3, 4), t3 = ipow(6, m), b3 = P(6, m);
      q = '擲一顆公正骰子 ' + T(String(m)) + ' 次，依序記錄點數。至少有兩次點數相同的情形有幾種？';
      a = T('6^{' + m + '}-' + pT(6, m) + '=' + (t3 - b3)) + ' 種'; h = '反面是「' + m + ' 次點數全不相同」，用排列數。'; p = { kind: 2, m: m, ans: t3 - b3 };
    }
    return { q: q, a: a, h: h, p: p };
  };

  /* ── §2 排列 ── */
  /* 2-1 排列數的基本運算 */
  L1.permBasic = function (r) {
    var n = r.int(5, 8), k = r.int(2, 4);
    return { q: '有 ' + people(n) + ' 共 ' + T(String(n)) + ' 人。(1) 全部排成一列有幾種排法？(2) 從中選出 ' + T(String(k)) + ' 人排成一列有幾種？(3) 全部排成一列且甲必須排在第一位，有幾種？',
             a: '(1) ' + T(n + '!=' + fact(n)) + '　(2) ' + T(pT(n, k) + '=' + P(n, k)) + '　(3) ' + T((n - 1) + '!=' + fact(n - 1)),
             h: '(3) 甲固定後，其餘 ' + (n - 1) + ' 人任意排。',
             p: { n: n, k: k, ans: { all: fact(n), sel: P(n, k), first: fact(n - 1) } } };
  };
  /* 2-2 捆綁法：相鄰 */
  L1.bundle = function (r) {
    var n = r.int(5, 8), m = r.int(2, 3), ans = fact(n - m + 1) * fact(m);
    return { q: T(String(n)) + ' 人排成一列，其中' + NAMES.slice(0, m).join('、') + ' ' + T(String(m)) + ' 人必須相鄰，共有幾種排法？',
             a: T((n - m + 1) + '!\\times' + m + '!=' + ans) + ' 種',
             h: '把 ' + m + ' 人綁成一包當一個單位（共 ' + (n - m + 1) + ' 個單位），包內再自排 ' + m + '!。',
             p: { n: n, m: m, ans: ans } };
  };
  /* 2-3 插空法：不相鄰 */
  L1.gaps = function (r) {
    var m = r.int(3, 5), k = r.int(2, Math.min(3, m + 1)), ans = fact(m) * P(m + 1, k), together = fact(m + 1) * fact(k);
    return { q: T(String(m)) + ' 位男生與 ' + T(String(k)) + ' 位女生排成一列。(1) 若女生互不相鄰，有幾種排法？(2) 若女生必須全部相鄰，有幾種排法？',
             a: '(1) ' + T(m + '!\\times' + pT(m + 1, k) + '=' + ans) + ' 種　(2) ' + T((m + 1) + '!\\times' + k + '!=' + together) + ' 種',
             h: '(1) 先排男生（' + m + '!），造出 ' + (m + 1) + ' 個空隙，再把女生排進去（' + pT(m + 1, k) + '）。(2) 捆綁法。',
             p: { m: m, k: k, ans: { apart: ans, together: together } } };
  };
  /* 2-4 固定順序：除法 */
  L1.fixedOrder = function (r) {
    var n = r.int(5, 8), m = r.int(2, 3), ans = fact(n) / fact(m);
    var who = NAMES.slice(0, m).join('、');
    return { q: T(String(n)) + ' 人排成一列，要求' + who + '由左到右的順序必須是' + NAMES.slice(0, m).join('') + '（不必相鄰），有幾種排法？',
             a: T('\\dfrac{' + n + '!}{' + m + '!}=' + ans) + ' 種',
             h: '先當 ' + n + ' 人任意排，' + who + ' 的 ' + m + '! 種相對順序中只有 1 種合格 ⟹ 除以 ' + m + '!。',
             p: { n: n, m: m, ans: ans } };
  };
  /* 2-5 不盡相異物排列 */
  L1.multisetPerm = function (r) {
    var a = r.int(2, 4), c = r.int(1, 2), b = 2, n = a + b + c;
    var tot = fact(n) / (fact(a) * fact(b) * fact(c)), others = fact(a + c) / (fact(a) * fact(c)), apart = others * C(a + c + 1, 2);
    return { q: '有 ' + T(String(a)) + ' 顆相同的紅球、' + T('2') + ' 顆相同的白球、' + T(String(c)) + ' 顆' + (c === 1 ? '' : '相同的') + '藍球，排成一列。(1) 共有幾種排法？(2) 若要求兩顆白球不相鄰，有幾種排法？',
             a: '(1) ' + T('\\dfrac{' + n + '!}{' + a + '!\\,2!\\,' + c + '!}=' + tot) + ' 種　(2) ' + T(String(apart)) + ' 種',
             h: '(2) 先排紅、藍球（' + others + ' 種），造出 ' + (a + c + 1) + ' 個空隙，白球相同 ⟹ 選 2 個空隙 ' + cT(a + c + 1, 2) + '。',
             p: { a: a, b: b, c: c, ans: { tot: tot, apart: apart } } };
  };
  /* 2-6 格子路徑 */
  L1.gridPath = function (r) {
    var R = r.int(3, 6), U = r.int(2, 4), px = r.int(1, R - 1), py = r.int(1, U - 1);
    var tot = C(R + U, U), via = C(px + py, py) * C(R - px + U - py, U - py);
    return { q: '在向右 ' + T(String(R)) + ' 格、向上 ' + T(String(U)) + ' 格的方格網上，從左下角 ' + T('A') + ' 走到右上角 ' + T('B') + '，每一步只能向右或向上。(1) 最短路徑共有幾條？(2) 其中必須經過「向右 ' + T(String(px)) + ' 格、向上 ' + T(String(py)) + ' 格」的那一點 ' + T('P') + ' 的有幾條？',
             a: '(1) ' + T(cT(R + U, U) + '=' + tot) + ' 條　(2) ' + T(cT(px + py, py) + '\\times' + cT(R - px + U - py, U - py) + '=' + via) + ' 條',
             h: '路徑＝「右右上上…」的不盡相異物排列；經過 P 就拆成 A→P、P→B 兩段相乘。',
             p: { R: R, U: U, px: px, py: py, ans: { tot: tot, via: via } } };
  };
  /* 2-7 重複排列：球放箱 */
  L1.repPerm = function (r) {
    var k = r.int(4, 6), n = r.int(3, 4), tot = ipow(n, k), atLeast = tot - ipow(n - 1, k);
    return { q: '將 ' + T(String(k)) + ' 個不同的球放進 ' + T(String(n)) + ' 個不同的箱子（箱子可以空）。(1) 共有幾種放法？(2) 其中第一個箱子至少有一球的放法有幾種？',
             a: '(1) ' + T(n + '^{' + k + '}=' + tot) + ' 種　(2) ' + T(n + '^{' + k + '}-' + (n - 1) + '^{' + k + '}=' + atLeast) + ' 種',
             h: '「球選箱」：每顆球各自有 ' + n + ' 種選擇。(2) 反面是每顆球都不放第一箱。',
             p: { k: k, n: n, ans: { tot: tot, atLeast: atLeast } } };
  };

  /* ── §3 組合 ── */
  /* 3-1 組合與排列的分辨 */
  L1.combVsPerm = function (r) {
    var n = r.int(7, 12), k = r.int(2, 4), c = C(n, k), p = P(n, k);
    return { q: '某社團有 ' + T(String(n)) + ' 位社員。(1) 選出 ' + T(String(k)) + ' 位擔任代表（職位相同），有幾種選法？(2) 選出 ' + T(String(k)) + ' 位分別擔任 ' + T(String(k)) + ' 個不同的職位，有幾種選法？',
             a: '(1) ' + T(cT(n, k) + '=' + c) + '　(2) ' + T(pT(n, k) + '=' + p),
             h: '職位相同 ⟹ 組合；職位不同 ⟹ 排列，兩者差 ' + k + '! 倍。',
             p: { n: n, k: k, ans: { c: c, p: p } } };
  };
  /* 3-2 「至少」型組合 */
  L1.atLeastComb = function (r) {
    var m = r.int(4, 6), w = r.int(3, 5), k = r.int(3, 4), j = r.int(1, Math.min(2, k - 1));
    var tot = C(m + w, k), a1 = tot - C(m, k), a2 = C(w, j) * C(m, k - j);
    return { q: '從 ' + T(String(m)) + ' 位男生與 ' + T(String(w)) + ' 位女生中選出 ' + T(String(k)) + ' 人。(1) 至少有 ' + T('1') + ' 位女生的選法有幾種？(2) 恰好有 ' + T(String(j)) + ' 位女生的選法有幾種？',
             a: '(1) ' + T(cT(m + w, k) + '-' + cT(m, k) + '=' + a1) + ' 種　(2) ' + T(cT(w, j) + cT(m, k - j) + '=' + a2) + ' 種',
             h: '「至少一女」用補集扣掉「全男」；「恰好」直接分步：先選女再選男。',
             p: { m: m, w: w, k: k, j: j, ans: { a1: a1, a2: a2 } } };
  };
  /* 3-3 分組與分堆 */
  var SPLITS = [[6, [3, 3]], [6, [2, 2, 2]], [8, [4, 4]], [9, [3, 3, 3]], [6, [4, 2]], [7, [3, 3, 1]], [8, [4, 2, 2]], [9, [4, 4, 1]], [10, [5, 5]]];
  L1.groups = function (r) {
    var s = r.pick(SPLITS), n = s[0], sizes = s[1], named = 1, rem = n, sameCount = {};
    sizes.forEach(function (z) { named *= C(rem, z); rem -= z; sameCount[z] = (sameCount[z] || 0) + 1; });
    var div = 1; Object.keys(sameCount).forEach(function (z) { div *= fact(sameCount[z]); });
    var unnamed = named / div;
    var desc = sizes.map(function (z) { return T(String(z)) + ' 件'; }).join('、');
    return { q: '將 ' + T(String(n)) + ' 件不同的物品分成 ' + desc + '。(1) 分給 ' + NAMES.slice(0, sizes.length).join('、') + ' ' + T(String(sizes.length)) + ' 人（依此件數），有幾種分法？(2) 分成 ' + T(String(sizes.length)) + ' 堆（堆與堆之間沒有區別），有幾種分法？',
             a: '(1) ' + T(String(named)) + ' 種　(2) ' + T(String(unnamed)) + ' 種',
             h: '(1) 有名字：連續組合相乘，不除。(2) 沒名字：人數相同的堆會重複計數，每 $k$ 堆同人數就除以 $k!$（本題除以 ' + div + '）。',
             p: { n: n, sizes: sizes, ans: { named: named, unnamed: unnamed } } };
  };
  /* 3-4 隔板法 */
  L1.bars = function (r) {
    var n = r.int(7, 15), k = r.int(3, 4), pos = C(n - 1, k - 1), non = C(n + k - 1, k - 1);
    return { q: '將 ' + T(String(n)) + ' 顆相同的球放進 ' + T(String(k)) + ' 個不同的箱子。(1) 若每箱至少一球，有幾種放法？(2) 若允許空箱，有幾種放法？',
             a: '(1) ' + T(cT(n - 1, k - 1) + '=' + pos) + ' 種　(2) ' + T(cT(n + k - 1, k - 1) + '=' + non) + ' 種',
             h: '(1) ' + n + ' 顆球排成一列，' + (n - 1) + ' 個空隙插 ' + (k - 1) + ' 塊板。(2) 先借 ' + k + ' 顆球使每箱至少一顆，再套 (1)。',
             p: { n: n, k: k, ans: { pos: pos, non: non } } };
  };
  /* 3-5 幾何計數：共線點修正 */
  L1.geomLines = function (r) {
    var n = r.int(8, 12), m = r.int(3, 5), lines = C(n, 2) - C(m, 2) + 1, tris = C(n, 3) - C(m, 3);
    return { q: '平面上有 ' + T(String(n)) + ' 個點，其中恰有 ' + T(String(m)) + ' 點共線，其餘任三點不共線。(1) 可決定幾條相異直線？(2) 可決定幾個三角形？',
             a: '(1) ' + T(cT(n, 2) + '-' + cT(m, 2) + '+1=' + lines) + ' 條　(2) ' + T(cT(n, 3) + '-' + cT(m, 3) + '=' + tris) + ' 個',
             h: '共線的 ' + m + ' 點兩兩連線只算一條（先扣 ' + cT(m, 2) + ' 再補 1）；共線三點圍不出三角形，直接扣。',
             p: { n: n, m: m, ans: { lines: lines, tris: tris } } };
  };
  /* 3-6 矩形與正方形計數 */
  L1.rectCount = function (r) {
    var rr = r.int(3, 5), cc = r.int(rr, 7), rect = C(rr + 1, 2) * C(cc + 1, 2), sqs = 0;
    for (var k = 1; k <= rr; k++) sqs += (rr - k + 1) * (cc - k + 1);
    return { q: '在一個 ' + T(String(rr)) + ' 列 ' + T(String(cc)) + ' 行的方格網（' + T(rr + '\\times' + cc) + ' 個單位小方格）中：(1) 共可數出幾個矩形？(2) 共可數出幾個正方形？',
             a: '(1) ' + T(cT(rr + 1, 2) + '\\times' + cT(cc + 1, 2) + '=' + rect) + ' 個　(2) ' + T(String(sqs)) + ' 個',
             h: '矩形＝從 ' + (rr + 1) + ' 條橫線選 2 條、' + (cc + 1) + ' 條直線選 2 條；正方形依邊長 $1,2,\\dots$ 分類：邊長 $k$ 的有 $(' + rr + '-k+1)(' + cc + '-k+1)$ 個。',
             p: { r: rr, c: cc, ans: { rect: rect, sq: sqs } } };
  };
  /* 3-7 二項式展開的特定項 */
  L1.binomTerm = function (r) {
    var n = r.int(5, 9), a = r.pick([1, 1, 2, 3]), b = r.pick([1, -1, 2, -2, 3]), kk = r.int(1, n - 1), m = n - 2 * kk;
    var coef = C(n, kk) * ipow(a, n - kk) * ipow(b, kk);
    var bTex = (b < 0 ? '-' : '') + '\\dfrac{' + Math.abs(b) + '}{x}', aTex = (a === 1 ? '' : a) + 'x';
    var mTex = m === 0 ? '常數項' : T('x^{' + m + '}') + ' 的係數';
    return { q: '求 ' + T('\\left(' + aTex + (b < 0 ? '' : '+') + bTex + '\\right)^{' + n + '}') + ' 展開式中的' + mTex + '。',
             a: T(String(coef)),
             h: '一般項 $T_{k+1}=' + cT(n, 'k') + '(' + aTex + ')^{' + n + '-k}\\left(' + bTex + '\\right)^k$，$x$ 的次數是 $' + n + '-2k$，令它等於 ' + m + ' 得 $k=' + kk + '$。',
             p: { n: n, a: a, b: b, m: m, ans: coef } };
  };
  /* 3-8 代值法求係數和 */
  L1.coefSum = function (r) {
    var n = r.int(4, 7), a = r.pick([1, 2, 3]), b = r.pick([-3, -2, -1, 1, 2, 3]);
    var all = ipow(a + b, n), c0 = ipow(b, n), even = (ipow(a + b, n) + ipow(b - a, n)) / 2;
    var bTex = (b < 0 ? '-' : '+') + Math.abs(b);
    return { q: '設 ' + T('(' + (a === 1 ? '' : a) + 'x' + bTex + ')^{' + n + '}=a_0+a_1x+a_2x^2+\\cdots+a_{' + n + '}x^{' + n + '}') + '。求 (1) ' + T('a_0+a_1+\\cdots+a_{' + n + '}') + '　(2) ' + T('a_0') + '　(3) 偶次項係數和 ' + T('a_0+a_2+a_4+\\cdots') + '。',
             a: '(1) ' + T(String(all)) + '　(2) ' + T(String(c0)) + '　(3) ' + T(String(even)),
             h: '代 $x=1$ 得全部係數和、代 $x=0$ 得 $a_0$、$\\dfrac{f(1)+f(-1)}2$ 得偶次項和。',
             p: { n: n, a: a, b: b, ans: { all: all, c0: c0, even: even } } };
  };
  /* 3-9 曲棍棒恆等式 */
  L1.hockey = function (r) {
    var k = r.int(2, 3), m = r.int(k + 4, k + 9), terms = [], v = C(m + 1, k + 1);
    for (var i = k; i <= m; i++) terms.push(cT(i, k));
    var tex = terms.length > 5 ? terms[0] + '+' + terms[1] + '+' + terms[2] + '+\\cdots+' + terms[terms.length - 1] : terms.join('+');
    return { q: '求 ' + T(tex) + ' 的值。',
             a: T(cT(m + 1, k + 1) + '=' + v),
             h: '下標固定為 ' + k + '、上標從 ' + k + ' 連到 ' + m + ' ⟹ $\\sum_{n=' + k + '}^{' + m + '}' + cT('n', k) + '=' + cT(m + 1, k + 1) + '$（曲棍棒）。',
             p: { k: k, m: m, ans: v } };
  };

  /* ── §4 古典機率 ── */
  /* 4-1 兩顆骰子 */
  L1.dice2 = function (r) {
    var kind = r.int(0, 3), s = r.int(4, 10), cnt = 0, q, h;
    for (var i = 1; i <= 6; i++) for (var j = 1; j <= 6; j++) {
      if (kind === 0 && i + j === s) cnt++;
      if (kind === 1 && i + j >= s) cnt++;
      if (kind === 2 && (i * j) % 2 === 0) cnt++;
      if (kind === 3 && Math.abs(i - j) === s - 4) cnt++;
    }
    if (kind === 0) { q = '點數和為 ' + T(String(s)); h = '列出和為 ' + s + ' 的有序對 $(a,b)$，共 ' + cnt + ' 個。'; }
    else if (kind === 1) { q = '點數和至少為 ' + T(String(s)); h = '「至少 ' + s + '」把和 $=' + s + ',' + (s + 1) + ',\\dots,12$ 的個數加起來。'; }
    else if (kind === 2) { q = '點數積為偶數'; h = '用餘事件：積為奇數 ⟺ 兩顆都是奇數 ⟹ $3\\times3=9$。'; }
    else { q = '點數差的絕對值為 ' + T(String(s - 4)); h = '差為 $d$ 的有序對有 $2(6-d)$ 個（$d\\ge1$），差為 0 有 6 個。'; }
    return { q: '投擲兩顆公正骰子，求「' + q + '」的機率。', a: T(pr(cnt, 36)), h: '$n(S)=6\\times6=36$。' + h,
             p: { kind: kind, s: s, ans: fr2(F(cnt, 36)) } };
  };
  /* 4-2 硬幣：恰 k 正／至少 k 正 */
  L1.coins = function (r) {
    var n = r.int(3, 5), k = r.int(1, n - 1), ex = C(n, k), al = 0;
    for (var i = k; i <= n; i++) al += C(n, i);
    var tot = ipow(2, n);
    return { q: '連續投擲一枚公正硬幣 ' + T(String(n)) + ' 次。(1) 恰有 ' + T(String(k)) + ' 次正面的機率？(2) 至少有 ' + T(String(k)) + ' 次正面的機率？',
             a: '(1) ' + T('\\dfrac{' + cT(n, k) + '}{2^{' + n + '}}=' + pr(ex, tot)) + '　(2) ' + T(pr(al, tot)),
             h: '$n(S)=2^{' + n + '}$；恰 $k$ 次正面＝選哪 $k$ 次是正面 ' + cT(n, k) + '。(2) 把 $k,\\dots,' + n + '$ 次的情形加起來（或用餘事件）。',
             p: { n: n, k: k, ans: { ex: fr2(F(ex, tot)), al: fr2(F(al, tot)) } } };
  };
  /* 4-3 事件的運算 */
  L1.eventOps = function (r) {
    var a = r.int(4, 8), b = r.int(3, 7), ab = r.int(Math.max(1, a + b - 10), Math.min(a, b) - 1);
    var un = a + b - ab, na = 10 - a, nn = 10 - un, aOnly = a - ab, one = a + b - 2 * ab;
    var d = function (x) { return '0.' + x; };
    return { q: '已知 ' + T('P(A)=' + d(a)) + '、' + T('P(B)=' + d(b)) + '、' + T('P(A\\cap B)=' + d(ab)) + '。求 (1) ' + T('P(A\\cup B)') + '　(2) ' + T("P(A')") + '　(3) ' + T("P(A'\\cap B')") + '　(4) ' + T("P(A\\cap B')") + '　(5)「' + T('A') + '、' + T('B') + ' 恰有一個發生」的機率。',
             a: '(1) ' + T(d(un)) + '　(2) ' + T(d(na)) + '　(3) ' + T(d(nn)) + '　(4) ' + T(d(aOnly)) + '　(5) ' + T(d(one)),
             h: '畫文氏圖四塊：只 $A$＝' + d(aOnly) + '、只 $B$＝' + d(b - ab) + '、都有＝' + d(ab) + '、都沒有＝' + d(nn) + '，合計 1。',
             p: { a: a, b: b, ab: ab, ans: { un: un, na: na, nn: nn, aOnly: aOnly, one: one } } };
  };
  /* 4-4 取球：同色／至少一紅 */
  L1.drawBalls = function (r) {
    var a = r.int(3, 6), b = r.int(3, 6), k = r.int(2, 3), tot = C(a + b, k);
    var same = C(a, k) + C(b, k), atLeast = tot - C(b, k);
    return { q: '袋中有 ' + T(String(a)) + ' 顆紅球與 ' + T(String(b)) + ' 顆白球（每顆被取到的機會相等）。同時取出 ' + T(String(k)) + ' 顆，求 (1) ' + T(String(k)) + ' 顆同色的機率　(2) 至少一顆紅球的機率。',
             a: '(1) ' + T('\\dfrac{' + cT(a, k) + '+' + cT(b, k) + '}{' + cT(a + b, k) + '}=' + pr(same, tot)) + '　(2) ' + T('1-\\dfrac{' + cT(b, k) + '}{' + cT(a + b, k) + '}=' + pr(atLeast, tot)),
             h: '同色球仍視為不同的球，$n(S)=' + cT(a + b, k) + '=' + tot + '$。(2) 用餘事件「全白」。',
             p: { a: a, b: b, k: k, ans: { same: fr2(F(same, tot)), atLeast: fr2(F(atLeast, tot)) } } };
  };
  /* 4-5 抽籤的公平性 */
  L1.lottery = function (r) {
    var n = r.int(8, 15), k = r.int(2, 4), i = r.int(2, n - 1), j = r.int(2, n); if (j === i) j = j === n ? 1 : j + 1;
    var p1 = F(k, n), p2 = F(k * (k - 1), n * (n - 1));
    return { q: T(String(n)) + ' 支籤中有 ' + T(String(k)) + ' 支中獎籤，' + T(String(n)) + ' 人依序各抽一支且不放回。求 (1) 第 ' + T(String(i)) + ' 位抽中的機率　(2) 第 ' + T(String(i)) + ' 位與第 ' + T(String(j)) + ' 位都抽中的機率。',
             a: '(1) ' + T(Fr.tex(p1)) + '　(2) ' + T('\\dfrac{' + k + '\\times' + (k - 1) + '}{' + n + '\\times' + (n - 1) + '}=' + Fr.tex(p2)),
             h: '抽籤與順序無關：任何一個指定位置是中獎籤的機率都是 $\\dfrac{' + k + '}{' + n + '}$；兩個指定位置都中獎 $=\\dfrac{' + pT(k, 2) + '}{' + pT(n, 2) + '}$。',
             p: { n: n, k: k, i: i, j: j, ans: { p1: fr2(p1), p2: fr2(p2) } } };
  };

  /* ── §5 期望值 ── */
  /* 5-1 期望值的定義 */
  L1.expBasic = function (r) {
    var a = r.int(2, 6), b = r.int(2, 6), x = r.pick([50, 100, 150, 200]), y = r.pick([10, 20, 30, 50, 60]);
    var E = F(a * x + b * y, a + b);
    return { q: '袋中有 ' + T(String(a)) + ' 顆紅球與 ' + T(String(b)) + ' 顆藍球，任取一球：取到紅球得 ' + T(String(x)) + ' 元、藍球得 ' + T(String(y)) + ' 元。求獎金的期望值。',
             a: T(x + '\\cdot\\dfrac{' + a + '}{' + (a + b) + '}+' + y + '\\cdot\\dfrac{' + b + '}{' + (a + b) + '}=' + Fr.tex(E)) + ' 元',
             h: '期望值＝各結果的「值 × 機率」相加。',
             p: { a: a, b: b, x: x, y: y, ans: fr2(E) } };
  };
  /* 5-2 平移與伸縮：骰子 */
  L1.expShift = function (r) {
    var two = r() < 0.5, a = r.int(2, 5), b = r.nz(-8, 10), E = two ? F(7 * a + b) : F(7 * a + 2 * b, 2);
    var bTex = (b < 0 ? '-' : '+') + Math.abs(b);
    return { q: (two ? '擲兩顆公正骰子，若點數和為 ' : '擲一顆公正骰子，若點數為 ') + T('k') + '，則可得 ' + T(a + 'k' + bTex) + ' 元。求所得金額的期望值。',
             a: T(Fr.tex(E)) + ' 元',
             h: '線性：$E(ak+b)=a\\,E(k)+b$，' + (two ? '兩骰點數和的期望值是 $7$' : '一顆骰子的期望值是 $3.5$') + '。',
             p: { two: two, a: a, b: b, ans: fr2(E) } };
  };
  /* 5-3 公平遊戲反求賠額 */
  L1.fairGame = function (r) {
    var kind = r.int(0, 1), w = r.pick([10, 15, 20, 25, 30]) * (kind === 0 ? 1 : 1), pw = kind === 0 ? F(1, 6) : F(5, 36);
    var lose = Fr.div(Fr.mul(F(w), pw), Fr.sub(F(1), pw));
    var ev = kind === 0 ? '兩顆點數相同' : '點數和為 $8$';
    return { q: '同時投擲兩顆公正骰子。若' + ev + '可得 ' + T(String(w)) + ' 元，否則要賠 ' + T('x') + ' 元。若此遊戲公平，求 ' + T('x') + '。',
             a: T('x=' + Fr.tex(lose)) + ' 元',
             h: '公平 ⟺ 期望值為 $0$：$' + w + '\\cdot' + Fr.tex(pw, true) + '-x\\cdot' + Fr.tex(Fr.sub(F(1), pw), true) + '=0$。',
             p: { kind: kind, w: w, ans: fr2(lose) } };
  };
  /* 5-4 期望值的線性：取 k 張 */
  L1.expLinear = function (r) {
    var a = r.int(2, 5), b = r.int(2, 6), x = r.pick([100, 200, 500]), y = r.pick([10, 20, 50]), k = r.int(2, 3);
    var one = F(a * x + b * y, a + b), tot = Fr.mul(one, F(k));
    return { q: '袋中裝有 ' + T(String(x)) + ' 元商品卡 ' + T(String(a)) + ' 張、' + T(String(y)) + ' 元商品卡 ' + T(String(b)) + ' 張，每張被取到的機會相等。同時取出 ' + T(String(k)) + ' 張，求所得總金額的期望值。',
             a: T(k + '\\times' + Fr.tex(one) + '=' + Fr.tex(tot)) + ' 元',
             h: '期望值的線性：總金額＝每張金額相加，每張的期望值都等於單張平均 $' + Fr.tex(one, true) + '$，不放回也成立。',
             p: { a: a, b: b, x: x, y: y, k: k, ans: fr2(tot) } };
  };
  /* 5-5 較大號碼的期望值 */
  L1.expMax = function (r) {
    var n = r.int(4, 7), s = 0;
    for (var m = 2; m <= n; m++) s += m * (m - 1);
    var E = F(s, C(n, 2));
    var lst = []; for (var ii = 1; ii <= n; ii++) lst.push(ii);
    return { q: '從 ' + T(lst.join(',')) + ' 這 ' + T(String(n)) + ' 個號碼球中同時取出 ' + T('2') + ' 顆，求兩球中較大號碼的期望值。',
             a: T(Fr.tex(E)),
             h: '較大號碼為 $m$ 的取法有 $m-1$ 種（另一顆比它小），$n(S)=' + cT(n, 2) + '=' + C(n, 2) + '$。',
             p: { n: n, ans: fr2(E) } };
  };

  /* ═══════════════════════ L2 ═══════════════════════ */
  var L2 = {};

  /* 2-1 相鄰＋不相鄰並存 */
  L2.adjNotAdj = function (r) {
    var n = r.int(5, 7), both = 2 * fact(n - 1), bad = 2 * fact(n - 2), ans = both - bad;
    return { q: T(String(n)) + ' 人排成一列，若甲、乙必須相鄰，但甲、丙不可相鄰，共有幾種排法？',
             a: T('2\\times' + (n - 1) + '!-2\\times' + (n - 2) + '!=' + both + '-' + bad + '=' + ans) + ' 種',
             h: '先算甲乙相鄰（捆綁 $2\\times' + (n - 1) + '!$），再扣掉「甲乙相鄰且甲丙也相鄰」——此時甲必夾在中間，三人塊只有乙甲丙、丙甲乙 2 種。',
             p: { n: n, ans: ans } };
  };
  /* 2-2 相異物分配：每人至少一件（取捨） */
  L2.distributeAll = function (r) {
    var k = r.int(4, 6), kind = r.int(0, 1), t = ipow(3, k), ans = kind === 0 ? t - 3 * ipow(2, k) + 3 : t - 2 * ipow(2, k) + 1;
    var cond = kind === 0 ? '三人都至少得一件' : '甲、乙都至少得一件';
    return { q: T(String(k)) + ' 件不同的物品分給甲、乙、丙三人（每人可兼得，也可以沒拿到），若' + cond + '，有幾種分法？',
             a: T(kind === 0 ? '3^{' + k + '}-3\\cdot2^{' + k + '}+3=' + ans : '3^{' + k + '}-2\\cdot2^{' + k + '}+1=' + ans) + ' 種',
             h: '「物選人」總數 $3^{' + k + '}$；扣掉「某人沒拿到」（每件只能給另兩人 $2^{' + k + '}$），再補回「某兩人都沒拿到」（$1^{' + k + '}$）。',
             p: { k: k, kind: kind, ans: ans } };
  };
  /* 2-3 不盡相異物＋不相鄰 */
  L2.multisetGap = function (r) {
    var a = r.int(2, 3), b = r.int(1, 3), c = r.int(1, 3); if (a > b + c + 1) c = a - b - 1 + r.int(0, 1);
    var others = fact(b + c) / (fact(b) * fact(c)), ans = others * C(b + c + 1, a), tot = fact(a + b + c) / (fact(a) * fact(b) * fact(c));
    var word = 'a'.repeat(a) + 'b'.repeat(b) + 'c'.repeat(c);
    return { q: '將 ' + T(String(a)) + ' 個 ' + T('a') + '、' + T(String(b)) + ' 個 ' + T('b') + '、' + T(String(c)) + ' 個 ' + T('c') + ' 排成一列。(1) 共有幾種排法？(2) 其中 ' + T('a') + ' 互不相鄰的有幾種？',
             a: '(1) ' + T('\\dfrac{' + (a + b + c) + '!}{' + a + '!\\,' + b + '!\\,' + c + '!}=' + tot) + ' 種　(2) ' + T(String(others) + '\\times' + cT(b + c + 1, a) + '=' + ans) + ' 種',
             h: '(2) 先排 $b,c$（不盡相異物 ' + others + ' 種），造出 ' + (b + c + 1) + ' 個空隙；$a$ 相同 ⟹ 用組合選 ' + a + ' 個空隙。',
             p: { word: word, a: a, b: b, c: c, ans: { tot: tot, apart: ans } } };
  };
  /* 2-4 數字排列：3 的倍數要「先選後排」 */
  L2.digitsMult3 = function (r) {
    var withZero = r() < 0.5, m = r.int(5, 7), digits = [], i;
    for (i = withZero ? 0 : 1; i <= m; i++) digits.push(i);
    var ans = perms3(digits, function (a, b, c) { return a !== 0 && (a + b + c) % 3 === 0; });
    return { q: '從 ' + T(digits.join(',')) + ' 中任取三個不同的數字排成三位數，其中是 ' + T('3') + ' 的倍數的共有幾個？',
             a: T(String(ans)) + ' 個',
             h: '先把數字依除以 3 的餘數分成三堆，選出「數字和是 3 的倍數」的三數組合（三堆各一個、或同一堆取三個），再排列' + (withZero ? '——含 0 的組合首位不能是 0，要另外算' : '') + '。',
             p: { withZero: withZero, m: m, ans: ans } };
  };
  /* 2-5 路徑：必經與迴避 */
  L2.gridAvoid = function (r) {
    var R = r.int(4, 6), U = r.int(3, 4), px = r.int(1, R - 2), py = r.int(0, U - 2), qx = r.int(px + 1, R - 1), qy = r.int(py + 1, U - 1);
    var paths = function (x1, y1, x2, y2) { return C(x2 - x1 + y2 - y1, y2 - y1); };
    var tot = paths(0, 0, R, U), viaP = paths(0, 0, px, py) * paths(px, py, R, U), viaQ = paths(0, 0, qx, qy) * paths(qx, qy, R, U), both = paths(0, 0, px, py) * paths(px, py, qx, qy) * paths(qx, qy, R, U);
    var a1 = tot - viaQ, a2 = viaP - both;
    return { q: '在向右 ' + T(String(R)) + ' 格、向上 ' + T(String(U)) + ' 格的方格網上，從左下角 ' + T('A') + ' 走到右上角 ' + T('B') + '（只能向右或向上）。' + T('P') + ' 在向右 ' + T(String(px)) + ' 格、向上 ' + T(String(py)) + ' 格處，' + T('Q') + ' 在向右 ' + T(String(qx)) + ' 格、向上 ' + T(String(qy)) + ' 格處。(1) 不經過 ' + T('Q') + ' 的最短路徑有幾條？(2) 經過 ' + T('P') + ' 但不經過 ' + T('Q') + ' 的最短路徑有幾條？',
             a: '(1) ' + T(tot + '-' + viaQ + '=' + a1) + ' 條　(2) ' + T(viaP + '-' + both + '=' + a2) + ' 條',
             h: '「不經過」＝總數 − 經過；(2) 經 P 的路徑（' + viaP + ' 條）扣掉「經 P 又經 Q」的（拆成 A→P→Q→B 三段相乘 ' + both + ' 條）。',
             p: { R: R, U: U, P: [px, py], Q: [qx, qy], ans: { a1: a1, a2: a2 } } };
  };
  /* 2-6 整數解：有下限／不等式 */
  L2.barsBound = function (r) {
    var kind = r.int(0, 1), n = r.int(10, 20), a = r.int(1, 3), b = r.int(1, 3), ans, q, h;
    if (kind === 0) {
      ans = C(n - a - b + 2, 2);
      q = '求方程式 ' + T('x+y+z=' + n) + ' 滿足 ' + T('x\\ge' + a) + '、' + T('y\\ge' + b) + '、' + T('z\\ge0') + ' 的整數解共有幾組？';
      h = '換元 $x=x\'+' + a + '$、$y=y\'+' + b + '$ 變成 $x\'+y\'+z=' + (n - a - b) + '$ 的非負整數解 ⟹ ' + cT(n - a - b + 2, 2) + '。';
    } else {
      ans = C(n + 3, 3);
      q = '求不等式 ' + T('x+y+z\\le' + n) + ' 的非負整數解共有幾組？';
      h = '引入鬆弛變數 $w=' + n + '-x-y-z\\ge0$，變成 $x+y+z+w=' + n + '$ 的非負整數解 ⟹ ' + cT(n + 3, 3) + '。';
    }
    return { q: q, a: T(String(ans)) + ' 組', h: h, p: { kind: kind, n: n, a: a, b: b, ans: ans } };
  };
  /* 2-7 平分成堆＋甲乙同堆 */
  var EQSPLIT = [[6, 3, 2], [6, 2, 3], [8, 4, 2], [9, 3, 3], [8, 2, 4]];
  L2.groupsEqual = function (r) {
    var s = r.pick(EQSPLIT), n = s[0], k = s[1], m = s[2];
    var tot = fact(n) / (ipow(fact(m), k) * fact(k));
    var same = C(n - 2, m - 2) * fact(n - m) / (ipow(fact(m), k - 1) * fact(k - 1));
    return { q: '將甲、乙等 ' + T(String(n)) + ' 人平分成 ' + T(String(k)) + ' 組，每組 ' + T(String(m)) + ' 人（組與組之間沒有區別）。(1) 共有幾種分法？(2) 甲、乙在同一組的分法有幾種？',
             a: '(1) ' + T(String(tot)) + ' 種　(2) ' + T(String(same)) + ' 種',
             h: '(1) 連續組合再除以 $' + k + '!$。(2) 甲乙那一組再從其餘 ' + (n - 2) + ' 人選 ' + (m - 2) + ' 人，剩下 ' + (n - m) + ' 人分成 ' + (k - 1) + ' 個沒區別的組（除以 $' + (k - 1) + '!$）。',
             p: { n: n, k: k, m: m, ans: { tot: tot, same: same } } };
  };
  /* 2-8 二項式：x^2 與 1/x 的混合 */
  L2.binomGeneral = function (r) {
    var n = r.int(6, 9), a = r.pick([1, 1, 2]), b = r.pick([1, -1, 2, -2, 3, -3]), kk = r.int(1, n - 1), m = 2 * n - 3 * kk;
    var coef = C(n, kk) * ipow(a, n - kk) * ipow(b, kk);
    var aTex = (a === 1 ? '' : a) + 'x^2', bTex = (b < 0 ? '-' : '+') + '\\dfrac{' + Math.abs(b) + '}{x}';
    var mTex = m === 0 ? '常數項' : T('x^{' + m + '}') + ' 的係數';
    return { q: '求 ' + T('\\left(' + aTex + bTex + '\\right)^{' + n + '}') + ' 展開式中的' + mTex + '。',
             a: T(String(coef)),
             h: '一般項 $' + cT(n, 'k') + '(' + aTex + ')^{' + n + '-k}\\left(' + bTex.replace(/^\+/, '') + '\\right)^k$，$x$ 的次數 $2(' + n + '-k)-k=' + (2 * n) + '-3k$，令其為 ' + m + ' 得 $k=' + kk + '$。',
             p: { n: n, a: a, b: b, m: m, ans: coef } };
  };
  /* 2-9 組合恆等式求值 */
  L2.combIdentityVal = function (r) {
    var n = r.int(5, 9), kind = r.int(0, 3), q, a, h;
    if (kind === 0) { a = ipow(3, n); q = cT(n, 0) + '+2' + cT(n, 1) + '+2^2' + cT(n, 2) + '+\\cdots+2^{' + n + '}' + cT(n, n); h = '$(1+x)^{' + n + '}$ 代 $x=2$。'; }
    else if (kind === 1) { a = ipow(2, n - 1); q = cT(n, 1) + '+' + cT(n, 3) + '+' + cT(n, 5) + '+\\cdots'; h = '奇次項和＝偶次項和＝$2^{' + n + '-1}$（$f(1)-f(-1)=2^{' + n + '}$）。'; }
    else if (kind === 2) { a = n * ipow(2, n - 1); q = cT(n, 1) + '+2' + cT(n, 2) + '+3' + cT(n, 3) + '+\\cdots+' + n + cT(n, n); h = '用 $k' + cT(n, 'k') + '=' + n + cT(n - 1, 'k-1') + '$ 化成 $' + n + '\\cdot2^{' + (n - 1) + '}$。'; }
    else { a = C(2 * n, n); q = '\\left(' + cT(n, 0) + '\\right)^2+\\left(' + cT(n, 1) + '\\right)^2+\\cdots+\\left(' + cT(n, n) + '\\right)^2'; h = '范德蒙：從 ' + n + ' 男 ' + n + ' 女中選 ' + n + ' 人，依「幾個男生」分類 ⟹ $' + cT(2 * n, n) + '$。'; }
    return { q: '求 ' + T(q) + ' 的值。', a: T(String(a)), h: h, p: { n: n, kind: kind, ans: a } };
  };
  /* 2-10 不相連的選法 */
  L2.nonAdjSelect = function (r) {
    var n = r.int(10, 16), k = r.int(3, 4), apart = C(n - k + 1, k), atLeast = C(n, k) - apart;
    return { q: '從 ' + T('1') + ' 到 ' + T(String(n)) + ' 的整數中選出 ' + T(String(k)) + ' 個數。(1) 任兩個都不相連（不含相鄰的整數）的選法有幾種？(2) 至少有兩個相連的選法有幾種？',
             a: '(1) ' + T(cT(n - k + 1, k) + '=' + apart) + ' 種　(2) ' + T(cT(n, k) + '-' + apart + '=' + atLeast) + ' 種',
             h: '沒被選的 ' + (n - k) + ' 個數排好造出 ' + (n - k + 1) + ' 個空隙，選 ' + k + ' 個放被選的數 ⟹ $C^{n-r+1}_r$；(2) 用補集。',
             p: { n: n, k: k, ans: { apart: apart, atLeast: atLeast } } };
  };
  /* 2-11 機率：至少 2 個 */
  L2.probAtLeast2 = function (r) {
    var m = r.int(5, 7), w = r.int(3, 5), k = r.int(4, 5), tot = C(m + w, k), bad = C(m, k) + C(w, 1) * C(m, k - 1), ans = F(tot - bad, tot);
    return { q: '某專輯共 ' + T(String(m + w)) + ' 首歌，其中 ' + T(String(w)) + ' 首抒情歌、' + T(String(m)) + ' 首快歌。隨機挑選 ' + T(String(k)) + ' 首來演唱，求至少選中 ' + T('2') + ' 首抒情歌的機率。',
             a: T('1-\\dfrac{' + cT(m, k) + '+' + cT(w, 1) + cT(m, k - 1) + '}{' + cT(m + w, k) + '}=' + Fr.tex(ans)),
             h: '「至少 2」的反面是「0 首或 1 首」兩類；$n(S)=' + cT(m + w, k) + '=' + tot + '$。',
             p: { m: m, w: w, k: k, ans: fr2(ans) } };
  };
  /* 2-12 機率的可能範圍 */
  L2.probRange = function (r) {
    var a = r.int(5, 8), b = r.int(4, 8); if (a + b <= 10) b = 11 - a + r.int(0, 1);
    var lo = a + b - 10, hi = Math.min(a, b), d = function (x) { return x === 10 ? '1' : (x === 0 ? '0' : '0.' + x); };
    return { q: '設 ' + T('P(A)=' + d(a)) + '、' + T('P(B)=' + d(b)) + '。求 (1) ' + T('P(A\\cup B)') + ' 的範圍　(2) ' + T('P(A\\cap B)') + ' 的範圍　(3) ' + T("P(A\\cap B')") + ' 的範圍。',
             a: '(1) ' + T(d(Math.max(a, b)) + '\\le P(A\\cup B)\\le1') + '　(2) ' + T(d(lo) + '\\le P(A\\cap B)\\le' + d(hi)) + '　(3) ' + T(d(a - hi) + "\\le P(A\\cap B')\\le" + d(a - lo)),
             h: '聯集至少是較大者、至多 1；交集下限 $P(A)+P(B)-1$、上限 $\\min$；$P(A\\cap B\')=P(A)-P(A\\cap B)$ 隨交集反向。',
             p: { a: a, b: b, ans: { u: [Math.max(a, b), 10], i: [lo, hi], d: [a - hi, a - lo] } } };
  };
  /* 2-13 取完全部球：首末同色／指定位置 */
  L2.drawOrder = function (r) {
    var a = r.int(3, 6), b = r.int(2, 6), k = r.int(2, a + b - 1), n = a + b;
    var same = F(a * (a - 1) + b * (b - 1), n * (n - 1)), pk = F(a, n);
    return { q: '箱中有 ' + T(String(a)) + ' 顆紅球與 ' + T(String(b)) + ' 顆白球（每球被取到的機會相等）。一次取一球、取後不放回，直到取完為止。求 (1) 首、末兩球同色的機率　(2) 第 ' + T(String(k)) + ' 球是紅球的機率。',
             a: '(1) ' + T('\\dfrac{' + a + '\\cdot' + (a - 1) + '+' + b + '\\cdot' + (b - 1) + '}{' + n + '\\cdot' + (n - 1) + '}=' + Fr.tex(same)) + '　(2) ' + T(Fr.tex(pk)),
             h: '只看首末兩個位置：$n(S)=' + n + '\\times' + (n - 1) + '$（有序）；(2) 由對稱性，任何指定位置是紅球的機率都是紅球比例。',
             p: { a: a, b: b, k: k, ans: { same: fr2(same), pk: fr2(pk) } } };
  };
  /* 2-14 號碼球成對：號碼差的期望值 */
  L2.expectPairs = function (r) {
    var n = r.int(3, 5), balls = [], i, j;
    for (i = 1; i <= n; i++) { balls.push(i); balls.push(i); }
    var tot = C(2 * n, 2), sameCnt = 0, diffSum = 0;
    for (i = 0; i < balls.length; i++) for (j = i + 1; j < balls.length; j++) { if (balls[i] === balls[j]) sameCnt++; diffSum += Math.abs(balls[i] - balls[j]); }
    var pSame = F(sameCnt, tot), E = F(diffSum, tot);
    var lst = []; for (i = 1; i <= n; i++) lst.push(i);
    return { q: '袋中有 ' + T(lst.join(',')) + ' 號球各 ' + T('2') + ' 顆，共 ' + T(String(2 * n)) + ' 顆，每球被抽中的機會均等。同時取出兩球，求 (1) 兩球號碼相同的機率　(2) 若兩球號碼差為 ' + T('k') + ' 時可得 ' + T('k') + ' 元，求獎金的期望值。',
             a: '(1) ' + T(Fr.tex(pSame)) + '　(2) ' + T(Fr.tex(E)) + ' 元',
             h: '$n(S)=' + cT(2 * n, 2) + '=' + tot + '$。同號 $=' + n + '$ 種；差為 $k$ 的取法有 $2\\cdot2\\cdot(' + n + '-k)$ 種（兩個號碼各 2 顆）。',
             p: { n: n, ans: { pSame: fr2(pSame), E: fr2(E) } } };
  };
  /* 2-15 三顆骰子的公平遊戲 */
  L2.fairMulti = function (r) {
    var A = r.pick([50, 60, 100, 120]), B = r.pick([10, 15, 20, 25]), Cc = r.pick([2, 3, 4, 5]);
    var win = A * 1 + B * 15 + Cc * 75, x = F(win, 125);
    return { q: '同時投擲三顆公正骰子。三顆都是 ' + T('6') + ' 點可得 ' + T(String(A)) + ' 元、恰有兩顆 ' + T('6') + ' 點可得 ' + T(String(B)) + ' 元、恰有一顆 ' + T('6') + ' 點可得 ' + T(String(Cc)) + ' 元；一顆 ' + T('6') + ' 點都沒有則要賠 ' + T('x') + ' 元。為使遊戲公平，' + T('x') + ' 應為多少？',
             a: T('x=' + Fr.tex(x)) + ' 元',
             h: '$n(S)=216$；三個 6：1 種、恰兩個 6：$C^3_2\\cdot5=15$ 種、恰一個 6：$C^3_1\\cdot5^2=75$ 種、沒有 6：$125$ 種。公平 ⟺ $' + A + '\\cdot1+' + B + '\\cdot15+' + Cc + '\\cdot75=125x$。',
             p: { A: A, B: B, C: Cc, ans: fr2(x) } };
  };
  /* 2-16 摸彩進行到一半：更新後的期望值 */
  L2.expectUpdated = function (r) {
    var pk = r.pick([[2, 500], [1, 1000], [5, 200], [4, 250]]), pct = pk[0], n = pk[1];
    var a = r.int(3, 6), b = 10 - a, A = r.pick([2000, 3000, 5000, 6000]), B = A + r.pick([2000, 3000, 4000, 5000]);
    var m = r.pick([50, 100]), i = r.int(0, Math.min(2, a - 1)), j = r.int(0, Math.min(1, b - 1));
    var E = F((a - i) * A + (b - j) * B, n - m);
    var seen = (i === 0 ? '無人抽中 ' + T(String(A)) + ' 元' : '恰有 ' + T(String(i)) + ' 人抽中 ' + T(String(A)) + ' 元') + '、' + (j === 0 ? '無人抽中 ' + T(String(B)) + ' 元' : '恰有 ' + T(String(j)) + ' 人抽中 ' + T(String(B)) + ' 元');
    return { q: '某商場摸彩，主持人依報名人數置入同數量的摸彩球，其中只有 ' + T('10') + ' 顆為幸運獎：' + T(String(A)) + ' 元禮券 ' + T(String(a)) + ' 顆、' + T(String(B)) + ' 元禮券 ' + T(String(b)) + ' 顆。抽後不放回，每人一次機會，公告中獎機率為 ' + T(pct + '\\%') + '。若前 ' + T(String(m)) + ' 位抽獎者中' + seen + '，求第 ' + T(String(m + 1)) + ' 號者可獲禮券金額的期望值。',
             a: T('\\dfrac{' + (a - i) + '(' + A + ')+' + (b - j) + '(' + B + ')}{' + (n - m) + '}=' + Fr.tex(E)) + ' 元',
             h: '① $\\dfrac{10}{n}=' + pct + '\\%$ ⟹ $n=' + n + '$；② 剩 $' + (n - m) + '$ 顆，其中 ' + A + ' 元 ' + (a - i) + ' 顆、' + B + ' 元 ' + (b - j) + ' 顆；③ 剩下的球等可能，直接算期望值。',
             p: { pct: pct, n: n, a: a, b: b, A: A, B: B, m: m, i: i, j: j, ans: fr2(E) } };
  };
  /* 2-17 從重複字母中選與排 */
  var WORDS = ['SUCCESS', 'BANANA', 'LETTER', 'COFFEE', 'GOOGLE', 'ASSESS', 'PEPPER', 'BALLOON', 'TATTOO', 'CHEESE', 'BUTTER', 'APPLE', 'HAPPY', 'MAMMAL'];
  L2.lettersSelect = function (r) {
    var w = r.pick(WORDS), seen = {}, sel = {}, i, j, k, cnt = 0, cs = 0, L = w.length;
    for (i = 0; i < L; i++) for (j = 0; j < L; j++) for (k = 0; k < L; k++) {
      if (i === j || j === k || i === k) continue;
      var s = w[i] + w[j] + w[k]; if (!seen[s]) { seen[s] = 1; cnt++; }
      var t = [w[i], w[j], w[k]].sort().join(''); if (!sel[t]) { sel[t] = 1; cs++; }
    }
    return { q: '從 ' + T('\\text{' + w + '}') + ' 這個字的諸字母中任取 ' + T('3') + ' 個：(1) 共有幾種選法？(2) 排成一列共有幾種排法？',
             a: '(1) ' + T(String(cs)) + ' 種　(2) ' + T(String(cnt)) + ' 種',
             h: '先數清各字母的個數，依「三個全同／兩同一異／三個相異」分類：選法逐類相加；排法各類再乘 $1$、$\\dfrac{3!}{2!}=3$、$3!=6$。',
             p: { w: w, ans: { sel: cs, arr: cnt } } };
  };
  /* 2-18 三顆骰子的結構機率 */
  L2.dice3 = function (r) {
    var kind = r.int(0, 2), cnt = 0, a, b, c;
    for (a = 1; a <= 6; a++) for (b = 1; b <= 6; b++) for (c = 1; c <= 6; c++) {
      var s = [a, b, c].sort(function (u, v) { return u - v; });
      if (kind === 0 && s[0] + s[1] > s[2]) cnt++;
      if (kind === 1 && (a === b || b === c || a === c) && !(a === b && b === c)) cnt++;
      if (kind === 2 && s[1] - s[0] === s[2] - s[1] && s[0] !== s[2]) cnt++;
    }
    var ev = ['三個點數可以作為一個三角形的三邊長', '恰有兩顆點數相同', '三個點數由小到大排成公差不為 $0$ 的等差數列'][kind];
    var hs = ['依最大點數分類，檢查「兩小邊之和 $\\gt$ 最大邊」；等腰、正三角形都算。', '選哪兩顆相同 $C^3_2$、那個點數 6 種、第三顆 5 種。', '先找出等差三元組（公差 1、2 各幾組），再乘上排列 $3!$。'][kind];
    return { q: '同時投擲三顆公正骰子，求「' + ev + '」的機率。', a: T(pr(cnt, 216)), h: '$n(S)=6^3=216$。' + hs,
             p: { kind: kind, ans: fr2(F(cnt, 216)) } };
  };

  /* ══════════════════════════════════════════════════════════ */
  var META = {
    L1: [
      ['routes', '§1 加法原理 vs 乘法原理'], ['passcode', '§1 乘法原理的三種變化'], ['digitsEven', '§1 分類討論：含 0 的三位數'], ['multiples', '§1 倍數計數（取捨）'], ['venn3', '§1 三集合取捨'], ['complement', '§1 補集法：「至少」'],
      ['permBasic', '§2 排列數的基本運算'], ['bundle', '§2 捆綁法：相鄰'], ['gaps', '§2 插空法：不相鄰'], ['fixedOrder', '§2 固定順序：除法'], ['multisetPerm', '§2 不盡相異物排列'], ['gridPath', '§2 格子路徑'], ['repPerm', '§2 重複排列：球放箱'],
      ['combVsPerm', '§3 組合與排列的分辨'], ['atLeastComb', '§3 「至少」型組合'], ['groups', '§3 分組 vs 分堆'], ['bars', '§3 隔板法'], ['geomLines', '§3 幾何計數：共線修正'], ['rectCount', '§3 矩形與正方形計數'], ['binomTerm', '§3 二項式的特定項'], ['coefSum', '§3 代值法求係數和'], ['hockey', '§3 曲棍棒恆等式'],
      ['dice2', '§4 兩顆骰子'], ['coins', '§4 硬幣：恰 k 次正面'], ['eventOps', '§4 事件的運算'], ['drawBalls', '§4 取球：同色與至少'], ['lottery', '§4 抽籤的公平性'],
      ['expBasic', '§5 期望值的定義'], ['expShift', '§5 平移與伸縮'], ['fairGame', '§5 公平遊戲'], ['expLinear', '§5 期望值的線性'], ['expMax', '§5 較大號碼的期望值']
    ],
    L2: [
      ['adjNotAdj', '§2 相鄰＋不相鄰並存'], ['distributeAll', '§2 分配：每人至少一件'], ['multisetGap', '§2 不盡相異物＋不相鄰'], ['digitsMult3', '§2 3 的倍數：先選後排'], ['gridAvoid', '§2 路徑：必經與迴避'], ['lettersSelect', '§2 重複字母的選與排'],
      ['barsBound', '§3 整數解：下限與不等式'], ['groupsEqual', '§3 平分成堆與同堆'], ['binomGeneral', '§3 二項式：x² 與 1/x'], ['combIdentityVal', '§3 組合恆等式求值'], ['nonAdjSelect', '§3 不相連的選法'],
      ['probAtLeast2', '§4 機率：至少 2 個'], ['probRange', '§4 機率的可能範圍'], ['drawOrder', '§4 取完全部球的位置'], ['dice3', '§4 三顆骰子的結構'],
      ['expectPairs', '§5 號碼差的期望值'], ['fairMulti', '§5 三骰公平遊戲'], ['expectUpdated', '§5 摸彩進行到一半']
    ]
  };

  function escMath(s) {
    return String(s).replace(/\$([^$]*)\$/g, function (m, inner) {
      return '$' + inner.replace(/</g, '\\lt ').replace(/>/g, '\\gt ').replace(/\\times(?=[A-Za-z])/g, '\\times ') + '$';
    });
  }
  function wrapAll(group) {
    Object.keys(group).forEach(function (k) {
      var f = group[k];
      group[k] = function (r) { var o = f(r); o.q = escMath(o.q); o.a = escMath(o.a); o.h = escMath(o.h); return o; };
    });
  }
  wrapAll(L1); wrapAll(L2);

  return { makeRng: makeRng, L1: L1, L2: L2, META: META, _util: { gcd: gcd, F: F, Fr: Fr, C: C, P: P } };
}));
