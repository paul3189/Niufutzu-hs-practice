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

  /* ── patch_gen_10b2 新增工具（優化 #6／#7 用） ── */
  /* digits 取 k 個不重複排成一列，逐一交給 fn 判斷，回傳符合的個數（窮舉，不套公式） */
  function permsK(digits, k, fn) {
    var n = 0, used = [], cur = [];
    (function rec() {
      if (cur.length === k) { if (fn(cur)) n++; return; }
      for (var i = 0; i < digits.length; i++) if (!used[i]) { used[i] = 1; cur.push(digits[i]); rec(); cur.pop(); used[i] = 0; }
    })();
    return n;
  }
  /* 乘法算式：係數 1 不寫「1\times」 */
  function xT(a, b) { return (a === 1 ? '' : a + '\\times') + b; }
  /* 一串因數相乘的 LaTeX：等於 1 的因數一律省略；全是 1 才寫 1 */
  function mulT(list) {
    var f = [], i;
    for (i = 0; i < list.length; i++) if (String(list[i]) !== '1') f.push(list[i]);
    return f.length ? f.join('\\times') : '1';
  }
  /* 同上但用 \cdot 連接 */
  function dotT(list) {
    var f = [], i;
    for (i = 0; i < list.length; i++) if (String(list[i]) !== '1') f.push(list[i]);
    return f.length ? f.join('\\cdot') : '1';
  }
  /* ── patch_gen_10b2 新增工具結束 ── */
  /* ═══════════════════════ L1 ═══════════════════════ */
  var L1 = {};

  /* ── §1 計數原理 ── */
  /* 1-1 加法原理 vs 乘法原理：路線 */
  L1.routes = function (r) {
    var a = r.int(2, 5), b = r.int(2, 5), c = r.int(1, 3);
    var one = a * b + c, rt = one * one;
    return { q: '從甲地到乙地有 ' + T(String(a)) + ' 條路，從乙地到丙地有 ' + T(String(b)) + ' 條路，另外還有 ' + T(String(c)) + ' 條路可以從甲地直達丙地。(1) 從甲地到丙地共有幾種走法？(2) 從甲地到丙地再回到甲地（路線可以重複）共有幾種走法？',
             a: '(1) ' + T(a + '\\times' + b + '+' + c + '=' + one) + ' 種　(2) ' + T(one + '^2=' + rt) + ' 種',
             h: '「經乙地」與「直達」是分類（加）：經乙地 ' + T(a + '\\times' + b + '=' + (a * b)) + ' 種，再加直達的 ' + T(String(c)) + ' 種，共 ' + T(String(one)) + ' 種；去程與回程是分步（乘）：' + T(one + '\\times' + one + '=' + rt) + ' 種。',
             p: { a: a, b: b, c: c, ans: { one: one, rt: rt } } };
  };
  /* 1-2 乘法原理三變化：密碼 */
  L1.passcode = function (r) {
    var ctx = r.pick(['某系統的密碼', '某置物櫃的密碼', '某保險箱的密碼']);
    var k = r.int(3, 6), m = r.int(6, 9), v = r.int(0, 1), base = m + 1;
    var odd = Math.floor((m + 1) / 2);                                  /* 0~m 之中的奇數個數 */
    var lead = v === 0 ? m : odd, a1 = ipow(base, k), a2 = P(base, k), a3 = lead * P(m, k - 1);
    var cond = v === 0 ? '第一位不能是 ' + T('0') : '第一位是奇數';
    return { q: ctx + '由 ' + T(String(k)) + ' 個數字組成，每一位都可以是 ' + T('0\\sim' + m) + '。(1) 若數字可以重複，共有幾組密碼？(2) 若數字不可重複，共有幾組？(3) 若數字不可重複且' + cond + '，共有幾組？',
             a: '(1) ' + T(base + '^{' + k + '}=' + a1) + '　(2) ' + T(pT(base, k) + '=' + a2) + '　(3) ' + T(xT(lead, pT(m, k - 1)) + '=' + a3),
             h: '(1) 每一位都有 ' + base + ' 種選擇：' + T(base + '^{' + k + '}=' + a1) + '。(2) 不重複就是排列 ' + T(pT(base, k) + '=' + a2) + '。(3) 先排最受限的第一位（' + (v === 0 ? '不能是 0，共 ' : '奇數有 ') + lead + ' 種），其餘 ' + (k - 1) + ' 位再從剩下 ' + m + ' 個數字中不重複地排：' + T(xT(lead, pT(m, k - 1)) + '=' + a3) + '。',
             p: { k: k, m: m, v: v, ans: { a1: a1, a2: a2, a3: a3 } } };
  };
  /* 1-3 數字排列：含 0 的三位數與偶數 */
  L1.digitsEven = function (r) {
    var m = r.int(4, 9), k = r.int(3, 4), v = r.int(0, 2), digits = [], i;
    if (v === 2 && m < 5) m = 5;                                        /* 「5 的倍數」要有 5 可用 */
    for (i = 0; i <= m; i++) digits.push(i);
    var test = [function (x) { return x % 2 === 0; }, function (x) { return x % 2 === 1; }, function (x) { return x === 0 || x === 5; }][v];
    var tot = permsK(digits, k, function (t2) { return t2[0] !== 0; });
    var cnt = permsK(digits, k, function (t2) { return t2[0] !== 0 && test(t2[k - 1]); });
    var name = ['偶數', '奇數', ' ' + T('5') + ' 的倍數'][v], kw = k === 3 ? '三' : '四';
    var nOdd = Math.floor((m + 1) / 2);
    var h2 = [
      '(2) 依個位分類：個位是 ' + T('0') + ' 時最高位有 ' + m + ' 種；個位是其他偶數時，最高位還要避開 ' + T('0') + ' 與個位那個數字，兩類相加共 ' + cnt + ' 個。',
      '(2) 個位必須是奇數（' + nOdd + ' 種，其中沒有 ' + T('0') + '），最高位再從剩下的 ' + m + ' 個數字中避開 ' + T('0') + '，共 ' + cnt + ' 個。',
      '(2) 個位只能是 ' + T('0') + ' 或 ' + T('5') + '，兩類分開算（個位是 ' + T('5') + ' 時最高位要避開 ' + T('0') + '），共 ' + cnt + ' 個。'][v];
    return { q: '用 ' + T(digits.join(',')) + ' 這 ' + T(String(m + 1)) + ' 個數字組成數字不重複的' + kw + '位數。(1) 共可組成幾個？(2) 其中是' + name + '的有幾個？',
             a: '(1) ' + T(xT(m, pT(m, k - 1)) + '=' + tot) + ' 個　(2) ' + T(String(cnt)) + ' 個',
             h: '(1) 最高位不能是 ' + T('0') + '（' + m + ' 種），其餘 ' + (k - 1) + ' 位從剩下 ' + m + ' 個數字排：' + T(xT(m, pT(m, k - 1)) + '=' + tot) + '。' + h2,
             p: { m: m, k: k, v: v, ans: { tot: tot, ev: cnt } } };
  };
  /* 1-4 倍數計數（取捨原理） */
  L1.multiples = function (r) {
    var N = r.pick([100, 200, 300, 500, 1000]), pair = r.pick([[2, 3], [2, 5], [3, 5], [3, 4], [4, 6], [3, 7], [2, 7], [5, 7]]), a = pair[0], b = pair[1];
    var l = a * b / gcd(a, b), nA = Math.floor(N / a), nB = Math.floor(N / b), nAB = Math.floor(N / l);
    var kind = r.int(0, 1), ans = kind === 0 ? nA + nB - nAB : nA - nAB;
    var qtxt = kind === 0 ? '是 ' + T(String(a)) + ' 或 ' + T(String(b)) + ' 的倍數' : '是 ' + T(String(a)) + ' 的倍數但不是 ' + T(String(b)) + ' 的倍數';
    return { q: '在 ' + T('1') + ' 到 ' + T(String(N)) + ' 的自然數中，' + qtxt + '的數共有幾個？',
             a: T(String(ans)) + ' 個',
             h: (kind === 0 ? '$n(A\\cup B)=n(A)+n(B)-n(A\\cap B)$' : '$n(A)-n(A\\cap B)$') + '：' + a + ' 的倍數有 ' + T(String(nA)) + ' 個、' + b + ' 的倍數有 ' + T(String(nB)) + ' 個，交集是 ' + T(String(l)) + ' 的倍數（最小公倍數）有 ' + T(String(nAB)) + ' 個，' + (kind === 0 ? T(nA + '+' + nB + '-' + nAB + '=' + ans) : T(nA + '-' + nAB + '=' + ans)) + '。',
             p: { N: N, a: a, b: b, kind: kind, ans: ans } };
  };
  /* 1-5 三集合取捨（文氏圖七區） */
  L1.venn3 = function (r) {
    var oA = r.int(4, 15), oB = r.int(4, 15), oC = r.int(3, 12), ab = r.int(2, 8), bc = r.int(2, 8), ac = r.int(2, 8), abc = r.int(1, 6), none = r.int(2, 12);
    var A = oA + ab + ac + abc, B = oB + ab + bc + abc, Cc = oC + ac + bc + abc;
    var AB = ab + abc, BC = bc + abc, AC = ac + abc;
    var union = A + B + Cc - AB - BC - AC + abc, N = union + none, only = oA + oB + oC;
    return { q: '某班共 ' + T(String(N)) + ' 人，調查參加社團的情形：參加 A 社的 ' + T(String(A)) + ' 人、B 社的 ' + T(String(B)) + ' 人、C 社的 ' + T(String(Cc)) + ' 人；同時參加 A、B 的 ' + T(String(AB)) + ' 人、B、C 的 ' + T(String(BC)) + ' 人、A、C 的 ' + T(String(AC)) + ' 人；三社都參加的 ' + T(String(abc)) + ' 人。(1) 至少參加一個社團的有幾人？(2) 三社都沒參加的有幾人？(3) 恰參加一個社團的有幾人？',
             a: '(1) ' + T(String(union)) + ' 人　(2) ' + T(String(none)) + ' 人　(3) ' + T(String(only)) + ' 人',
             h: '(1) 三集合取捨（加三個、減三個、再加回三個都有的）：' + T(A + '+' + B + '+' + Cc + '-' + AB + '-' + BC + '-' + AC + '+' + abc + '=' + union) + ' 人。(2) ' + T(N + '-' + union + '=' + none) + ' 人。(3) 從最裡面往外填七塊：只參加 A 的 ' + T(String(oA)) + ' 人、只 B 的 ' + T(String(oB)) + ' 人、只 C 的 ' + T(String(oC)) + ' 人，' + T(oA + '+' + oB + '+' + oC + '=' + only) + ' 人。',
             p: { N: N, A: A, B: B, C: Cc, AB: AB, BC: BC, AC: AC, ABC: abc, ans: { union: union, none: none, only: only } } };
  };
  /* 1-6 補集法：「至少」 */
  L1.complement = function (r) {
    var kind = r.int(0, 2), q, a, h, p;
    if (kind === 0) {
      var n = r.int(2, 5), f = r.int(1, 6), tot = ipow(6, n), bad = ipow(5, n);
      q = '擲一顆公正骰子 ' + T(String(n)) + ' 次，依序記錄點數。至少有一次出現 ' + T(String(f)) + ' 點的情形有幾種？';
      a = T('6^{' + n + '}-5^{' + n + '}=' + (tot - bad)) + ' 種';
      h = '反面是「每一次都不是 ' + f + ' 點」，每次只剩 5 種：' + T('5^{' + n + '}=' + bad) + '；總數 ' + T('6^{' + n + '}=' + tot) + '，相減得 ' + T(String(tot - bad)) + ' 種。';
      p = { kind: 0, n: n, f: f, ans: tot - bad };
    } else if (kind === 1) {
      var k = r.int(3, 5), d = r.int(0, 9), t2 = ipow(10, k), b2 = ipow(9, k);
      q = '由 ' + T('0\\sim9') + ' 組成 ' + T(String(k)) + ' 位數的密碼（數字可重複），其中至少出現一個 ' + T(String(d)) + ' 的密碼有幾組？';
      a = T('10^{' + k + '}-9^{' + k + '}=' + (t2 - b2)) + ' 組';
      h = '反面是「沒有任何一位是 ' + d + '」，每一位只剩 9 種：' + T('9^{' + k + '}=' + b2) + '；總數 ' + T('10^{' + k + '}=' + t2) + '，相減得 ' + T(String(t2 - b2)) + ' 組。';
      p = { kind: 1, k: k, d: d, ans: t2 - b2 };
    } else {
      var m = r.int(3, 5), t3 = ipow(6, m), b3 = P(6, m);
      q = '擲一顆公正骰子 ' + T(String(m)) + ' 次，依序記錄點數。至少有兩次點數相同的情形有幾種？';
      a = T('6^{' + m + '}-' + pT(6, m) + '=' + (t3 - b3)) + ' 種';
      h = '反面是「' + m + ' 次點數全不相同」，用排列數 ' + T(pT(6, m) + '=' + b3) + '；總數 ' + T('6^{' + m + '}=' + t3) + '，相減得 ' + T(String(t3 - b3)) + ' 種。';
      p = { kind: 2, m: m, ans: t3 - b3 };
    }
    return { q: q, a: a, h: h, p: p };
  };

  /* ── §2 排列 ── */
  /* 2-1 排列數的基本運算 */
  L1.permBasic = function (r) {
    var n = r.int(5, 8), k = r.int(2, 4), v = r.int(0, 2);              /* NAMES 只有 8 個名字 */
    var all = fact(n), sel = P(n, k);
    var third = [fact(n - 1), (n - 1) * fact(n - 1), 2 * fact(n - 2)][v];
    var cond = ['甲必須排在第一位', '甲不排在第一位', '甲、乙分別排在最左端與最右端'][v];
    var tTex = [T((n - 1) + '!=' + third), T((n - 1) + '\\times' + (n - 1) + '!=' + third), T('2\\times' + (n - 2) + '!=' + third)][v];
    var tHint = ['甲固定在第一位後，其餘 ' + (n - 1) + ' 人任意排：' + T((n - 1) + '!=' + third) + ' 種。',
      '甲有 ' + (n - 1) + ' 個位置可選（不能是第一位），其餘 ' + (n - 1) + ' 人任意排：' + T((n - 1) + '\\times' + (n - 1) + '!=' + third) + ' 種。',
      '甲、乙誰在左端有 2 種，中間 ' + (n - 2) + ' 人任意排：' + T('2\\times' + (n - 2) + '!=' + third) + ' 種。'][v];
    return { q: '有 ' + people(n) + ' 共 ' + T(String(n)) + ' 人。(1) 全部排成一列有幾種排法？(2) 從中選出 ' + T(String(k)) + ' 人排成一列有幾種？(3) 全部排成一列且' + cond + '，有幾種？',
             a: '(1) ' + T(n + '!=' + all) + '　(2) ' + T(pT(n, k) + '=' + sel) + '　(3) ' + tTex,
             h: '(1) ' + n + ' 人全排 ' + T(n + '!=' + all) + '。(2) 選 ' + k + ' 人再排 ' + T(pT(n, k) + '=' + sel) + '。(3) ' + tHint,
             p: { n: n, k: k, v: v, ans: { all: all, sel: sel, first: third } } };
  };
  /* 2-2 捆綁法：相鄰 */
  L1.bundle = function (r) {
    var n = r.int(5, 9), m = r.int(2, 4), v = r.int(0, 2);
    if (v === 2 && 2 * m > n + 1) m = Math.floor((n + 1) / 2);          /* 互不相鄰要有足夠空隙 */
    var who = NAMES.slice(0, m).join('、'), ans, aTex, hTex;
    if (v === 0) {
      ans = fact(n - m + 1) * fact(m);
      aTex = T((n - m + 1) + '!\\times' + m + '!=' + ans);
      hTex = '把 ' + m + ' 人綁成一包當一個單位（連同其他 ' + (n - m) + ' 人共 ' + (n - m + 1) + ' 個單位，' + T((n - m + 1) + '!=' + fact(n - m + 1)) + ' 種），包內再自排 ' + T(m + '!=' + fact(m)) + ' 種：' + aTex + ' 種。';
    } else if (v === 1) {
      ans = fact(n - m + 1);
      aTex = T((n - m + 1) + '!=' + ans);
      hTex = '一樣先捆成一包（' + (n - m + 1) + ' 個單位，' + T((n - m + 1) + '!=' + ans) + ' 種），但包內順序已被指定，只有 1 種，所以不再乘 ' + T(m + '!') + '。';
    } else {
      ans = fact(n - m) * P(n - m + 1, m);
      aTex = T(xT(fact(n - m), pT(n - m + 1, m)) + '=' + ans);
      hTex = '先排其他 ' + (n - m) + ' 人（' + T((n - m) + '!=' + fact(n - m)) + ' 種），造出 ' + (n - m + 1) + ' 個空隙，再把 ' + m + ' 人插進不同的空隙（' + T(pT(n - m + 1, m) + '=' + P(n - m + 1, m)) + ' 種）：' + aTex + ' 種。';
    }
    var cond = ['必須相鄰', '必須相鄰，且由左到右的順序恰為' + NAMES.slice(0, m).join(''), m === 2 ? '不相鄰' : '兩兩都不相鄰'][v];
    return { q: T(String(n)) + ' 人排成一列，其中' + who + ' ' + T(String(m)) + ' 人' + cond + '，共有幾種排法？',
             a: aTex + ' 種',
             h: hTex,
             p: { n: n, m: m, v: v, ans: ans } };
  };
  /* 2-3 插空法：不相鄰 */
  L1.gaps = function (r) {
    var pair = r.pick([['男生', '女生'], ['大人', '小孩'], ['老師', '學生']]), A = pair[0], B = pair[1];
    var m = r.int(3, 6), k = r.int(2, 4);
    var apart = fact(m) * P(m + 1, k), together = fact(m + 1) * fact(k);
    return { q: T(String(m)) + ' 位' + A + '與 ' + T(String(k)) + ' 位' + B + '排成一列。(1) 若' + B + '互不相鄰，有幾種排法？(2) 若' + B + '必須全部相鄰，有幾種排法？',
             a: '(1) ' + T(m + '!\\times' + pT(m + 1, k) + '=' + apart) + ' 種　(2) ' + T((m + 1) + '!\\times' + k + '!=' + together) + ' 種',
             h: '(1) 先排' + A + '（' + T(m + '!=' + fact(m)) + ' 種），造出 ' + (m + 1) + ' 個空隙，再把 ' + k + ' 位' + B + '排進不同的空隙（' + T(pT(m + 1, k) + '=' + P(m + 1, k)) + ' 種），共 ' + T(String(apart)) + ' 種。(2) 捆綁法：' + k + ' 位' + B + '當一包，' + T((m + 1) + '!=' + fact(m + 1)) + ' 再乘包內 ' + T(k + '!=' + fact(k)) + '，共 ' + T(String(together)) + ' 種。',
             p: { m: m, k: k, ans: { apart: apart, together: together } } };
  };
  /* 2-4 固定順序：除法 */
  L1.fixedOrder = function (r) {
    var n = r.int(5, 9), m = r.int(2, 4), v = r.int(0, 2);
    if (v === 1 && m === 2) m = 3;                                      /* 否則分母會寫成 1! */
    var who = NAMES.slice(0, m).join('、'), ord = NAMES.slice(0, m).join('');
    var last = NAMES[m];
    var ans = [fact(n) / fact(m), fact(n - 1) / fact(m - 1), fact(n - 1) / fact(m)][v];
    var num = [n, n - 1, n - 1][v], den = [m, m - 1, m][v];
    var aTex = T('\\dfrac{' + num + '!}{' + den + '!}=' + ans);
    var extra = ['', '，且甲必須排在第一位', '，且' + last + '必須排在最後一位'][v];
    var hTex = v === 0
      ? '先當 ' + n + ' 人任意排（' + T(n + '!=' + fact(n)) + ' 種），' + who + ' 的 ' + T(m + '!=' + fact(m)) + ' 種相對順序中只有 1 種合格 ⟹ 除以 ' + T(m + '!') + '：' + aTex + ' 種。'
      : v === 1
        ? '甲已固定在第一位，剩下 ' + (n - 1) + ' 人任意排（' + T((n - 1) + '!=' + fact(n - 1)) + ' 種），其中' + NAMES.slice(1, m).join('、') + '這 ' + (m - 1) + ' 人的 ' + T((m - 1) + '!=' + fact(m - 1)) + ' 種相對順序只有 1 種合格 ⟹ 除以 ' + T((m - 1) + '!') + '：' + aTex + ' 種。'
        : last + '已固定在最後一位，剩下 ' + (n - 1) + ' 人任意排（' + T((n - 1) + '!=' + fact(n - 1)) + ' 種），' + who + '的 ' + T(m + '!=' + fact(m)) + ' 種相對順序中只有 1 種合格 ⟹ 除以 ' + T(m + '!') + '：' + aTex + ' 種。';
    return { q: T(String(n)) + ' 人排成一列，要求' + who + '由左到右的順序必須是' + ord + '（不必相鄰）' + extra + '，有幾種排法？',
             a: aTex + ' 種',
             h: hTex,
             p: { n: n, m: m, v: v, ans: ans } };
  };
  /* 2-5 不盡相異物排列 */
  L1.multisetPerm = function (r) {
    var col = r.pick([['紅', '白', '藍'], ['黃', '綠', '紫']]);
    var a = r.int(2, 4), b = r.int(2, 3), c = r.int(1, 3), n = a + b + c;
    var tot = fact(n) / (fact(a) * fact(b) * fact(c));
    var others = fact(a + c) / (fact(a) * fact(c)), apart = others * C(a + c + 1, b);
    var cw = b === 2 ? '兩顆' : '三顆';
    return { q: '有 ' + T(String(a)) + ' 顆相同的' + col[0] + '球、' + T(String(b)) + ' 顆相同的' + col[1] + '球、' + T(String(c)) + ' 顆' + (c === 1 ? '' : '相同的') + col[2] + '球，排成一列。(1) 共有幾種排法？(2) 若要求' + cw + col[1] + '球兩兩不相鄰，有幾種排法？',
             a: '(1) ' + T('\\dfrac{' + n + '!}{' + a + '!\\,' + b + '!\\,' + c + '!}=' + tot) + ' 種　(2) ' + T(String(apart)) + ' 種',
             h: '(1) 不盡相異物排列：' + T('\\dfrac{' + n + '!}{' + a + '!\\,' + b + '!\\,' + c + '!}=' + tot) + ' 種。(2) 先排' + col[0] + '、' + col[2] + '球（' + T('\\dfrac{' + (a + c) + '!}{' + a + '!\\,' + c + '!}=' + others) + ' 種），造出 ' + (a + c + 1) + ' 個空隙，' + col[1] + '球相同 ⟹ 選 ' + b + ' 個空隙 ' + T(cT(a + c + 1, b) + '=' + C(a + c + 1, b)) + '，共 ' + T(String(apart)) + ' 種。',
             p: { a: a, b: b, c: c, ans: { tot: tot, apart: apart } } };
  };
  /* 2-6 格子路徑 */
  L1.gridPath = function (r) {
    var R = r.int(3, 6), U = r.int(2, 4), px = r.int(1, R - 1), py = r.int(1, U - 1);
    var toP = C(px + py, py), toB = C(R - px + U - py, U - py), tot = C(R + U, U), via = toP * toB;
    return { q: '在向右 ' + T(String(R)) + ' 格、向上 ' + T(String(U)) + ' 格的方格網上，從左下角 ' + T('A') + ' 走到右上角 ' + T('B') + '，每一步只能向右或向上。(1) 最短路徑共有幾條？(2) 其中必須經過「向右 ' + T(String(px)) + ' 格、向上 ' + T(String(py)) + ' 格」的那一點 ' + T('P') + ' 的有幾條？',
             a: '(1) ' + T(cT(R + U, U) + '=' + tot) + ' 條　(2) ' + T(cT(px + py, py) + '\\times' + cT(R - px + U - py, U - py) + '=' + via) + ' 條',
             h: '(1) 路徑就是 ' + R + ' 個「右」與 ' + U + ' 個「上」的排列，從 ' + (R + U) + ' 步中選 ' + U + ' 步向上：' + T(cT(R + U, U) + '=' + tot) + ' 條。(2) 經過 P 就拆成兩段相乘：' + T('A') + ' 到 ' + T('P') + ' 有 ' + T(cT(px + py, py) + '=' + toP) + ' 條、' + T('P') + ' 到 ' + T('B') + ' 有 ' + T(cT(R - px + U - py, U - py) + '=' + toB) + ' 條，共 ' + T(String(via)) + ' 條。',
             p: { R: R, U: U, px: px, py: py, ans: { tot: tot, via: via } } };
  };
  /* 2-7 重複排列：球放箱 */
  L1.repPerm = function (r) {
    /* [物品（含量詞）, 容器（含量詞）, 容器, 單一物品量詞, 「每…」, 物品簡稱] */
    var ctx = r.pick([['顆不同的球', '個不同的箱子', '箱子', '顆球', '每顆球', '球'], ['封不同的信', '個不同的郵筒', '郵筒', '封信', '每封信', '信']]);
    var k = r.int(4, 7), n = r.int(3, 5), v = r.int(0, 1);
    var tot = ipow(n, k), atLeast = tot - ipow(n - 1, k), exactly = k * ipow(n - 1, k - 1);
    var ans = v === 0 ? atLeast : exactly;
    var cond = '第一個' + ctx[2] + (v === 0 ? '至少有一' : '恰有一') + ctx[3];
    var aTex = v === 0 ? T(n + '^{' + k + '}-' + (n - 1) + '^{' + k + '}=' + ans) : T(k + '\\times' + (n - 1) + '^{' + (k - 1) + '}=' + ans);
    var hTex = v === 0
      ? '反面是「' + ctx[4] + '都不放進第一個' + ctx[2] + '」，各有 ' + (n - 1) + ' 種：' + T((n - 1) + '^{' + k + '}=' + ipow(n - 1, k)) + '，相減得 ' + aTex + ' 種。'
      : '先選哪一' + ctx[3] + '放進第一個' + ctx[2] + '（' + k + ' 種），其餘 ' + (k - 1) + ' ' + ctx[3] + '各有 ' + (n - 1) + ' 種選擇：' + aTex + ' 種。';
    return { q: '將 ' + T(String(k)) + ' ' + ctx[0] + '放進 ' + T(String(n)) + ' ' + ctx[1] + '（' + ctx[2] + '可以空）。(1) 共有幾種放法？(2) 其中' + cond + '的放法有幾種？',
             a: '(1) ' + T(n + '^{' + k + '}=' + tot) + ' 種　(2) ' + aTex + ' 種',
             h: '(1) 「' + ctx[5] + '選' + ctx[2] + '」：' + ctx[4] + '各自有 ' + n + ' 種選擇，' + T(n + '^{' + k + '}=' + tot) + ' 種。(2) ' + hTex,
             p: { k: k, n: n, v: v, ans: { tot: tot, atLeast: ans } } };
  };

  /* ── §3 組合 ── */
  /* 3-1 組合與排列的分辨 */
  L1.combVsPerm = function (r) {
    var ctx = r.pick([['某社團有', '位社員', '社員'], ['某班有', '位同學', '同學']]);
    var n = r.int(7, 14), k = r.int(2, 4), c = C(n, k), pp = P(n, k);
    return { q: ctx[0] + ' ' + T(String(n)) + ' ' + ctx[1] + '。(1) 選出 ' + T(String(k)) + ' 位擔任代表（職位相同），有幾種選法？(2) 選出 ' + T(String(k)) + ' 位分別擔任 ' + T(String(k)) + ' 個不同的職位，有幾種選法？',
             a: '(1) ' + T(cT(n, k) + '=' + c) + '　(2) ' + T(pT(n, k) + '=' + pp),
             h: '(1) 職位相同 ⟹ 只問「選哪 ' + k + ' 位' + ctx[2] + '」，是組合 ' + T(cT(n, k) + '=' + c) + '。(2) 職位不同 ⟹ 選完還要排，是排列 ' + T(pT(n, k) + '=' + pp) + '，兩者差 ' + T(k + '!=' + fact(k)) + ' 倍。',
             p: { n: n, k: k, ans: { c: c, p: pp } } };
  };
  /* 3-2 「至少」型組合 */
  L1.atLeastComb = function (r) {
    var m = r.int(4, 6), w = r.int(3, 5), k = r.int(3, 4), j = r.int(1, Math.min(2, k - 1));
    var tot = C(m + w, k), allMen = C(m, k), a1 = tot - allMen, cw = C(w, j), cm = C(m, k - j), a2 = cw * cm;
    return { q: '從 ' + T(String(m)) + ' 位男生與 ' + T(String(w)) + ' 位女生中選出 ' + T(String(k)) + ' 人。(1) 至少有 ' + T('1') + ' 位女生的選法有幾種？(2) 恰好有 ' + T(String(j)) + ' 位女生的選法有幾種？',
             a: '(1) ' + T(cT(m + w, k) + '-' + cT(m, k) + '=' + a1) + ' 種　(2) ' + T(cT(w, j) + cT(m, k - j) + '=' + a2) + ' 種',
             h: '(1)「至少一女」用補集：全部 ' + T(cT(m + w, k) + '=' + tot) + ' 扣掉「全是男生」' + T(cT(m, k) + '=' + allMen) + '，得 ' + T(String(a1)) + ' 種。(2)「恰好」直接分步：先選 ' + j + ' 位女生 ' + T(cT(w, j) + '=' + cw) + '，再選 ' + (k - j) + ' 位男生 ' + T(cT(m, k - j) + '=' + cm) + '，相乘得 ' + T(String(a2)) + ' 種。',
             p: { m: m, w: w, k: k, j: j, ans: { a1: a1, a2: a2 } } };
  };
  /* 3-3 分組與分堆 */
  var SPLITS = [[6, [3, 3]], [6, [2, 2, 2]], [8, [4, 4]], [9, [3, 3, 3]], [6, [4, 2]], [7, [3, 3, 1]], [8, [4, 2, 2]], [9, [4, 4, 1]], [10, [5, 5]],
                [7, [4, 3]], [8, [3, 3, 2]], [10, [4, 3, 3]], [9, [5, 4]], [10, [4, 4, 2]], [7, [5, 2]], [8, [5, 3]], [10, [6, 2, 2]]];
  L1.groups = function (r) {
    var ctx = r.pick([['件', '物品'], ['本', '書']]);
    var s = r.pick(SPLITS), n = s[0], sizes = s[1], named = 1, rem = n, sameCount = {}, steps = [];
    sizes.forEach(function (z) { if (C(rem, z) > 1) steps.push(cT(rem, z)); named *= C(rem, z); rem -= z; sameCount[z] = (sameCount[z] || 0) + 1; });
    var div = 1; Object.keys(sameCount).forEach(function (z) { div *= fact(sameCount[z]); });
    var unnamed = named / div;
    var desc = sizes.map(function (z) { return T(String(z)) + ' ' + ctx[0]; }).join('、');
    return { q: '將 ' + T(String(n)) + ' ' + ctx[0] + '不同的' + ctx[1] + '分成 ' + desc + '。(1) 分給 ' + NAMES.slice(0, sizes.length).join('、') + ' ' + T(String(sizes.length)) + ' 人（依此' + ctx[0] + '數），有幾種分法？(2) 分成 ' + T(String(sizes.length)) + ' 堆（堆與堆之間沒有區別），有幾種分法？',
             a: '(1) ' + T(String(named)) + ' 種　(2) ' + T(String(unnamed)) + ' 種',
             h: '(1) 有名字：連續組合相乘，不除 ⟹ ' + T(steps.join('\\times') + '=' + named) + ' 種。(2) 沒名字：' + ctx[0] + '數相同的堆會重複計數，每 $k$ 堆同' + ctx[0] + '數就除以 $k!$（本題除以 ' + div + '）⟹ ' + (div === 1 ? '沒有兩堆' + ctx[0] + '數相同，答案仍是 ' + T(String(unnamed)) : T('\\dfrac{' + named + '}{' + div + '}=' + unnamed)) + ' 種。',
             p: { n: n, sizes: sizes, ans: { named: named, unnamed: unnamed } } };
  };
  /* 3-4 隔板法 */
  L1.bars = function (r) {
    var n = r.int(7, 18), k = r.int(3, 5), pos = C(n - 1, k - 1), non = C(n + k - 1, k - 1);
    return { q: '將 ' + T(String(n)) + ' 顆相同的球放進 ' + T(String(k)) + ' 個不同的箱子。(1) 若每箱至少一球，有幾種放法？(2) 若允許空箱，有幾種放法？',
             a: '(1) ' + T(cT(n - 1, k - 1) + '=' + pos) + ' 種　(2) ' + T(cT(n + k - 1, k - 1) + '=' + non) + ' 種',
             h: '(1) ' + n + ' 顆球排成一列，' + (n - 1) + ' 個空隙插 ' + (k - 1) + ' 塊板：' + T(cT(n - 1, k - 1) + '=' + pos) + ' 種。(2) 先借 ' + k + ' 顆球給每箱各一顆（變成 ' + (n + k) + ' 顆、每箱至少一顆），再套 (1)：' + T(cT(n + k - 1, k - 1) + '=' + non) + ' 種。',
             p: { n: n, k: k, ans: { pos: pos, non: non } } };
  };
  /* 3-5 幾何計數：共線點修正 */
  L1.geomLines = function (r) {
    var n = r.int(8, 15), m = r.int(3, 6);
    var c2n = C(n, 2), c2m = C(m, 2), c3n = C(n, 3), c3m = C(m, 3);
    var lines = c2n - c2m + 1, tris = c3n - c3m;
    return { q: '平面上有 ' + T(String(n)) + ' 個點，其中恰有 ' + T(String(m)) + ' 點共線，其餘任三點不共線。(1) 可決定幾條相異直線？(2) 可決定幾個三角形？',
             a: '(1) ' + T(cT(n, 2) + '-' + cT(m, 2) + '+1=' + lines) + ' 條　(2) ' + T(cT(n, 3) + '-' + cT(m, 3) + '=' + tris) + ' 個',
             h: '(1) 任兩點決定一線共 ' + T(cT(n, 2) + '=' + c2n) + ' 條，但共線的 ' + m + ' 點兩兩連線 ' + T(cT(m, 2) + '=' + c2m) + ' 條其實是同一條（先扣掉再補 1）⟹ ' + T(String(lines)) + ' 條。(2) 任三點 ' + T(cT(n, 3) + '=' + c3n) + ' 個，扣掉共線三點 ' + T(cT(m, 3) + '=' + c3m) + ' 個（圍不出三角形）⟹ ' + T(String(tris)) + ' 個。',
             p: { n: n, m: m, ans: { lines: lines, tris: tris } } };
  };
  /* 3-6 矩形與正方形計數 */
  L1.rectCount = function (r) {
    var rr = r.int(2, 6), cc = r.int(rr, 9), v = r.int(0, 1), k;
    var rect = C(rr + 1, 2) * C(cc + 1, 2), sqs = 0, terms = [];
    for (k = 1; k <= rr; k++) { sqs += (rr - k + 1) * (cc - k + 1); terms.push(xT(rr - k + 1, cc - k + 1)); }
    var ans2 = v === 0 ? sqs : rect - sqs;
    var name2 = v === 0 ? '正方形' : '長與寬不相等的矩形';
    var h2 = v === 0
      ? '正方形依邊長分類：邊長 ' + T('k') + ' 的有 ' + T('(' + rr + '-k+1)(' + cc + '-k+1)') + ' 個，' + T(terms.join('+') + '=' + sqs) + ' 個。'
      : '正方形依邊長分類共 ' + T(terms.join('+') + '=' + sqs) + ' 個，從所有矩形中扣掉：' + T(rect + '-' + sqs + '=' + ans2) + ' 個。';
    return { q: '在一個 ' + T(String(rr)) + ' 列 ' + T(String(cc)) + ' 行的方格網（' + T(rr + '\\times' + cc) + ' 個單位小方格）中：(1) 共可數出幾個矩形？(2) 共可數出幾個' + name2 + '？',
             a: '(1) ' + T(cT(rr + 1, 2) + '\\times' + cT(cc + 1, 2) + '=' + rect) + ' 個　(2) ' + T(String(ans2)) + ' 個',
             h: '(1) 矩形＝從 ' + (rr + 1) + ' 條橫線選 2 條、' + (cc + 1) + ' 條直線選 2 條：' + T(cT(rr + 1, 2) + '\\times' + cT(cc + 1, 2) + '=' + rect) + ' 個。(2) ' + h2,
             p: { r: rr, c: cc, v: v, ans: { rect: rect, sq: ans2 } } };
  };
  /* 3-7 二項式展開的特定項 */
  L1.binomTerm = function (r) {
    var n = r.int(5, 9), a = r.pick([1, 1, 2, 3]), b = r.pick([1, -1, 2, -2, 3]), kk = r.int(1, n - 1), m = n - 2 * kk;
    var coef = C(n, kk) * ipow(a, n - kk) * ipow(b, kk);
    var bTex = (b < 0 ? '-' : '') + '\\dfrac{' + Math.abs(b) + '}{x}', aTex = (a === 1 ? '' : a) + 'x';
    var mTex = m === 0 ? '常數項' : ' ' + T(m === 1 ? 'x' : 'x^{' + m + '}') + ' 的係數';
    return { q: '求 ' + T('\\left(' + aTex + (b < 0 ? '' : '+') + bTex + '\\right)^{' + n + '}') + ' 展開式中的' + mTex + '。',
             a: T(String(coef)),
             h: '一般項 $T_{k+1}=' + cT(n, 'k') + '(' + aTex + ')^{' + n + '-k}\\left(' + bTex + '\\right)^k$，$x$ 的次數是 $' + n + '-2k$，令它等於 ' + m + ' 得 $k=' + kk + '$。',
             p: { n: n, a: a, b: b, m: m, ans: coef } };
  };
  /* 3-8 代值法求係數和 */
  L1.coefSum = function (r) {
    var n = r.int(4, 7), a = r.pick([1, 2, 3]), b = r.pick([-3, -2, -1, 1, 2, 3]);
    var f1 = ipow(a + b, n), fm1 = ipow(b - a, n), c0 = ipow(b, n), even = (f1 + fm1) / 2;
    var bTex = (b < 0 ? '-' : '+') + Math.abs(b);
    var addT = (fm1 < 0 ? '-' + Math.abs(fm1) : '+' + fm1);
    return { q: '設 ' + T('(' + (a === 1 ? '' : a) + 'x' + bTex + ')^{' + n + '}=a_0+a_1x+a_2x^2+\\cdots+a_{' + n + '}x^{' + n + '}') + '。求 (1) ' + T('a_0+a_1+\\cdots+a_{' + n + '}') + '　(2) ' + T('a_0') + '　(3) 偶次項係數和 ' + T('a_0+a_2+a_4+\\cdots') + '。',
             a: '(1) ' + T(String(f1)) + '　(2) ' + T(String(c0)) + '　(3) ' + T(String(even)),
             h: '(1) 代 ' + T('x=1') + '：' + T('(' + (a === 1 ? '' : a) + bTex + ')^{' + n + '}=' + f1) + ' 就是全部係數和。(2) 代 ' + T('x=0') + '：' + T('(' + bTex.replace('+', '') + ')^{' + n + '}=' + c0) + ' 就是 ' + T('a_0') + '。(3) 再代 ' + T('x=-1') + ' 得 ' + T(String(fm1)) + '，奇次項會變號而相消 ⟹ 偶次項和 ' + T('\\dfrac{' + f1 + addT + '}{2}=' + even) + '。',
             p: { n: n, a: a, b: b, ans: { all: f1, c0: c0, even: even } } };
  };
  /* 3-9 曲棍棒恆等式 */
  L1.hockey = function (r) {
    var k = r.int(2, 4), m = r.int(k + 4, k + 13), terms = [], v = C(m + 1, k + 1);
    for (var i = k; i <= m; i++) terms.push(cT(i, k));
    var tex = terms.length > 5 ? terms[0] + '+' + terms[1] + '+' + terms[2] + '+\\cdots+' + terms[terms.length - 1] : terms.join('+');
    return { q: '求 ' + T(tex) + ' 的值。',
             a: T(cT(m + 1, k + 1) + '=' + v),
             h: '下標固定為 ' + k + '、上標從 ' + k + ' 連到 ' + m + '（共 ' + (m - k + 1) + ' 項）⟹ 曲棍棒恆等式 $\\sum_{n=' + k + '}^{' + m + '}' + cT('n', k) + '=' + cT(m + 1, k + 1) + '$，算出來是 ' + T(String(v)) + '。',
             p: { k: k, m: m, ans: v } };
  };

  /* ── §4 古典機率 ── */
  /* 4-1 兩顆骰子 */
  L1.dice2 = function (r) {
    var kind = r.int(0, 5), cnt = 0, i, j, q, h, s = 0, w = 0, tt = 0, d = 0, mm = 0, sums = [];
    if (kind === 0) s = r.int(3, 11);
    else if (kind === 1) s = r.int(4, 11);
    else if (kind === 2) w = r.int(0, 1);
    else if (kind === 3) d = r.int(0, 5);
    else if (kind === 4) tt = r.int(1, 4);
    else { mm = r.pick([3, 4]); for (i = 2; i <= 12; i++) if (i % mm === 0) sums.push(i); }
    for (i = 1; i <= 6; i++) for (j = 1; j <= 6; j++) {
      if (kind === 0 && i + j === s) cnt++;
      if (kind === 1 && i + j >= s) cnt++;
      if (kind === 2 && ((i * j) % 2 === 0) === (w === 0)) cnt++;
      if (kind === 3 && Math.abs(i - j) === d) cnt++;
      if (kind === 4 && i > tt && j > tt) cnt++;
      if (kind === 5 && (i + j) % mm === 0) cnt++;
    }
    if (kind === 0) { q = '點數和為 ' + T(String(s)); h = '列出和為 ' + s + ' 的有序對 $(a,b)$，共 ' + cnt + ' 個。'; }
    else if (kind === 1) { q = '點數和至少為 ' + T(String(s)); h = '「至少 ' + s + '」把和 $=' + (s >= 10 ? (s === 11 ? '11,12' : '10,11,12') : s + ',' + (s + 1) + ',\\dots,12') + '$ 的個數加起來，共 ' + cnt + ' 個。'; }
    else if (kind === 2) {
      q = '點數積為' + (w === 0 ? '偶數' : '奇數');
      h = w === 0 ? '用餘事件：積為奇數 ⟺ 兩顆都是奇數 ⟹ $3\\times3=9$ 種，' + T('36-9=' + cnt) + ' 種。' : '積為奇數 ⟺ 兩顆都是奇數 ⟹ ' + T('3\\times3=' + cnt) + ' 種。';
    } else if (kind === 3) {
      q = '點數差的絕對值為 ' + T(String(d));
      h = d === 0 ? '差為 $0$ 就是兩顆點數相同，共 ' + cnt + ' 個。' : '差為 $d$ 的有序對有 $2(6-d)$ 個，本題 $d=' + d + '$ ⟹ ' + T('2\\times(6-' + d + ')=' + cnt) + ' 個。';
    } else if (kind === 4) {
      q = '兩顆點數都大於 ' + T(String(tt));
      h = '每一顆都只能是 ' + T((tt + 1) + '\\sim6') + ' 這 ' + (6 - tt) + ' 種 ⟹ ' + T((6 - tt) + '\\times' + (6 - tt) + '=' + cnt) + ' 個。';
    } else {
      q = '點數和是 ' + T(String(mm)) + ' 的倍數';
      h = '和是 ' + mm + ' 的倍數 ⟹ 和 ' + T('=' + sums.join(',')) + '，把各自的個數加起來共 ' + cnt + ' 個。';
    }
    return { q: '投擲兩顆公正骰子，求「' + q + '」的機率。', a: T(pr(cnt, 36)), h: '$n(S)=6\\times6=36$。' + h,
             p: { kind: kind, s: s, w: w, d: d, t: tt, m: mm, ans: fr2(F(cnt, 36)) } };
  };
  /* 4-2 硬幣：恰 k 正／至少 k 正 */
  L1.coins = function (r) {
    var n = r.int(3, 7), k = r.int(1, n - 1), v = r.int(0, 1), i;
    var ex = C(n, k), acc = 0, terms = [];
    if (v === 0) { for (i = k; i <= n; i++) { acc += C(n, i); terms.push(cT(n, i)); } }
    else { for (i = 0; i <= k; i++) { acc += C(n, i); terms.push(cT(n, i)); } }
    var tot = ipow(2, n), word = v === 0 ? '至少' : '至多';
    return { q: '連續投擲一枚公正硬幣 ' + T(String(n)) + ' 次。(1) 恰有 ' + T(String(k)) + ' 次正面的機率？(2) ' + word + '有 ' + T(String(k)) + ' 次正面的機率？',
             a: '(1) ' + T('\\dfrac{' + cT(n, k) + '}{2^{' + n + '}}=' + pr(ex, tot)) + '　(2) ' + T(pr(acc, tot)),
             h: '$n(S)=2^{' + n + '}=' + tot + '$；(1) 恰 ' + k + ' 次正面＝選哪 ' + k + ' 次是正面 ' + T(cT(n, k) + '=' + ex) + '，機率 ' + T(pr(ex, tot)) + '。(2) 把 ' + (v === 0 ? k + ' 到 ' + n : '0 到 ' + k) + ' 次的情形加起來：' + T(terms.join('+') + '=' + acc) + '，機率 ' + T(pr(acc, tot)) + '。',
             p: { n: n, k: k, v: v, ans: { ex: fr2(F(ex, tot)), al: fr2(F(acc, tot)) } } };
  };
  /* 4-3 事件的運算 */
  L1.eventOps = function (r) {
    var a = r.int(4, 8), b = r.int(3, 7), ab = r.int(Math.max(1, a + b - 10), Math.min(a, b) - 1);
    var un = a + b - ab, na = 10 - a, nn = 10 - un, aOnly = a - ab, one = a + b - 2 * ab;
    var d = function (x) { return x === 10 ? '1' : (x === 0 ? '0' : '0.' + x); };   /* 10 → 1、0 → 0（原本會寫成 0.10、0.0） */
    return { q: '已知 ' + T('P(A)=' + d(a)) + '、' + T('P(B)=' + d(b)) + '、' + T('P(A\\cap B)=' + d(ab)) + '。求 (1) ' + T('P(A\\cup B)') + '　(2) ' + T("P(A')") + '　(3) ' + T("P(A'\\cap B')") + '　(4) ' + T("P(A\\cap B')") + '　(5)「' + T('A') + '、' + T('B') + ' 恰有一個發生」的機率。',
             a: '(1) ' + T(d(un)) + '　(2) ' + T(d(na)) + '　(3) ' + T(d(nn)) + '　(4) ' + T(d(aOnly)) + '　(5) ' + T(d(one)),
             h: '畫文氏圖四塊：只 $A$＝' + d(aOnly) + '、只 $B$＝' + d(b - ab) + '、都有＝' + d(ab) + '、都沒有＝' + d(nn) + '，合計 1。',
             p: { a: a, b: b, ab: ab, ans: { un: un, na: na, nn: nn, aOnly: aOnly, one: one } } };
  };
  /* 4-4 取球：同色／至少一紅 */
  L1.drawBalls = function (r) {
    var a = r.int(3, 7), b = r.int(3, 7), k = r.int(2, 3), tot = C(a + b, k);
    var ca = C(a, k), cb = C(b, k), same = ca + cb, atLeast = tot - cb;
    return { q: '袋中有 ' + T(String(a)) + ' 顆紅球與 ' + T(String(b)) + ' 顆白球（每顆被取到的機會相等）。同時取出 ' + T(String(k)) + ' 顆，求 (1) ' + T(String(k)) + ' 顆同色的機率　(2) 至少一顆紅球的機率。',
             a: '(1) ' + T('\\dfrac{' + cT(a, k) + '+' + cT(b, k) + '}{' + cT(a + b, k) + '}=' + pr(same, tot)) + '　(2) ' + T('1-\\dfrac{' + cT(b, k) + '}{' + cT(a + b, k) + '}=' + pr(atLeast, tot)),
             h: '同色球仍視為不同的球，' + T('n(S)=' + cT(a + b, k) + '=' + tot) + '。(1) 全紅 ' + T(cT(a, k) + '=' + ca) + '、全白 ' + T(cT(b, k) + '=' + cb) + '，相加 ' + T(ca + '+' + cb + '=' + same) + ' 種。(2) 用餘事件「全白」' + T(cT(b, k) + '=' + cb) + '，' + T(tot + '-' + cb + '=' + atLeast) + ' 種。',
             p: { a: a, b: b, k: k, ans: { same: fr2(F(same, tot)), atLeast: fr2(F(atLeast, tot)) } } };
  };
  /* 4-5 抽籤的公平性 */
  L1.lottery = function (r) {
    var n = r.int(8, 15), k = r.int(2, 4), i = r.int(2, n - 1), j = r.int(2, n); if (j === i) j = j === n ? 1 : j + 1;
    var p1 = F(k, n), p2 = F(k * (k - 1), n * (n - 1));
    var fr2T = '\\dfrac{' + mulT([k, k - 1]) + '}{' + mulT([n, n - 1]) + '}';
    return { q: T(String(n)) + ' 支籤中有 ' + T(String(k)) + ' 支中獎籤，' + T(String(n)) + ' 人依序各抽一支且不放回。求 (1) 第 ' + T(String(i)) + ' 位抽中的機率　(2) 第 ' + T(String(i)) + ' 位與第 ' + T(String(j)) + ' 位都抽中的機率。',
             a: '(1) ' + T(Fr.tex(p1)) + '　(2) ' + T(fr2T + '=' + Fr.tex(p2)),
             h: '抽籤與順序無關：第 ' + i + ' 位抽中的機率跟第 1 位一樣都是 ' + T('\\dfrac{' + k + '}{' + n + '}' + (Fr.tex(p1) === '\\dfrac{' + k + '}{' + n + '}' ? '' : '=' + Fr.tex(p1))) + '。(2) 第 ' + i + ' 位與第 ' + j + ' 位都中獎 ' + T('=\\dfrac{' + pT(k, 2) + '}{' + pT(n, 2) + '}=' + fr2T + '=' + Fr.tex(p2)) + '。',
             p: { n: n, k: k, i: i, j: j, ans: { p1: fr2(p1), p2: fr2(p2) } } };
  };

  /* ── §5 期望值 ── */
  /* 5-1 期望值的定義 */
  L1.expBasic = function (r) {
    var a = r.int(2, 6), b = r.int(2, 6), x = r.pick([50, 100, 150, 200]), y = r.pick([10, 20, 30, 50, 60]);
    if (y === x) y = 20;                                                /* 兩種球獎金相同就沒得算了 */
    var n = a + b, E = F(a * x + b * y, n), pa = F(a, n), pb = F(b, n);
    return { q: '袋中有 ' + T(String(a)) + ' 顆紅球與 ' + T(String(b)) + ' 顆藍球，任取一球：取到紅球得 ' + T(String(x)) + ' 元、藍球得 ' + T(String(y)) + ' 元。求獎金的期望值。',
             a: T(x + '\\cdot' + Fr.tex(pa) + '+' + y + '\\cdot' + Fr.tex(pb) + '=' + Fr.tex(E)) + ' 元',
             h: '期望值＝各結果的「值 × 機率」相加：取到紅球的機率 ' + T('\\dfrac{' + a + '}{' + n + '}=' + Fr.tex(pa)) + '、藍球 ' + T('\\dfrac{' + b + '}{' + n + '}=' + Fr.tex(pb)) + '，所以 ' + T('\\dfrac{' + x + '\\times' + a + '+' + y + '\\times' + b + '}{' + n + '}=' + Fr.tex(E)) + ' 元。',
             p: { a: a, b: b, x: x, y: y, ans: fr2(E) } };
  };
  /* 5-2 平移與伸縮：骰子 */
  L1.expShift = function (r) {
    var two = r() < 0.5, a = r.int(2, 5), b = r.nz(-8, 10), E = two ? F(7 * a + b) : F(7 * a + 2 * b, 2);
    var bTex = (b < 0 ? '-' : '+') + Math.abs(b);
    var base = two ? '7' : '3.5';
    return { q: (two ? '擲兩顆公正骰子，若點數和為 ' : '擲一顆公正骰子，若點數為 ') + T('k') + '，則可得 ' + T(a + 'k' + bTex) + ' 元。求所得金額的期望值。',
             a: T(Fr.tex(E)) + ' 元',
             h: '線性：$E(ak+b)=a\\,E(k)+b$，' + (two ? '兩骰點數和的期望值是 $7$' : '一顆骰子的期望值是 $3.5$') + '，所以 ' + T(a + '\\times' + base + bTex + '=' + Fr.tex(E)) + ' 元。',
             p: { two: two, a: a, b: b, ans: fr2(E) } };
  };
  /* 5-3 公平遊戲反求賠額 */
  L1.fairGame = function (r) {
    var EV = [['兩顆點數相同', 6], ['點數和為 $8$ ', 5], ['點數和為 $9$ ', 4], ['點數和為 $10$ ', 3], ['點數差的絕對值為 $1$ ', 10], ['至少有一顆是 $6$ 點', 11]];
    var e = r.pick(EV), ev = e[0], win = e[1], w = r.pick([10, 15, 20, 25, 30, 40, 50, 60]);
    var pw = F(win, 36), pl = Fr.sub(F(1), pw);
    var lose = Fr.div(Fr.mul(F(w), pw), pl);
    return { q: '同時投擲兩顆公正骰子。若' + ev + '可得 ' + T(String(w)) + ' 元，否則要賠 ' + T('x') + ' 元。若此遊戲公平，求 ' + T('x') + '。',
             a: T('x=' + Fr.tex(lose)) + ' 元',
             h: '得獎的情形共 ' + win + ' 種 ⟹ 機率 ' + T('\\dfrac{' + win + '}{36}=' + Fr.tex(pw)) + '，賠錢的機率 ' + T(Fr.tex(pl)) + '。公平 ⟺ 期望值為 $0$：$' + w + '\\cdot' + Fr.tex(pw, true) + '-x\\cdot' + Fr.tex(pl, true) + '=0$ ⟹ ' + T('x=' + Fr.tex(lose)) + '。',
             p: { win: win, w: w, ans: fr2(lose) } };
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
    var ctx = r.pick([['號碼球', '顆'], ['號碼籤', '支'], ['號碼卡', '張']]);
    var n = r.int(4, 9), big = r.int(0, 1) === 0, s = 0, m;
    for (m = 1; m <= n; m++) s += m * (big ? m - 1 : n - m);
    var E = F(s, C(n, 2)), lst = [], ii;
    for (ii = 1; ii <= n; ii++) lst.push(ii);
    var word = big ? '較大' : '較小', cond = big ? '另一' + ctx[1] + '比它小' : '另一' + ctx[1] + '比它大';
    var cntT = big ? 'm-1' : n + '-m';
    return { q: '從 ' + T(lst.join(',')) + ' 這 ' + T(String(n)) + ' ' + ctx[1] + ctx[0] + '中同時取出 ' + T('2') + ' ' + ctx[1] + '，求兩' + ctx[1] + '中' + word + '號碼的期望值。',
             a: T(Fr.tex(E)),
             h: ctx[0] + '共 ' + n + ' ' + ctx[1] + '，' + T('n(S)=' + cT(n, 2) + '=' + C(n, 2)) + '；' + word + '號碼為 ' + T('m') + ' 的取法有 ' + T(cntT) + ' 種（' + cond + '），把 ' + T('m\\times(' + cntT + ')') + ' 全部加起來得 ' + T(String(s)) + '，除以 ' + C(n, 2) + ' 得 ' + T(Fr.tex(E)) + '。',
             p: { n: n, big: big, ans: fr2(E) } };
  };

  /* ═══════════════════════ L2 ═══════════════════════ */
  var L2 = {};

  /* 2-1 相鄰＋不相鄰並存 */
  L2.adjNotAdj = function (r) {
    var n = r.int(5, 10), v = r.int(0, 5);
    var F1 = fact(n - 1), F2 = fact(n - 2);
    var COND = ['甲、乙必須相鄰，但甲、丙不可相鄰', '甲、乙必須相鄰，但丙、丁不可相鄰', '甲、乙必須相鄰，且丙必須排在最左端或最右端',
                '甲、乙不可相鄰，且丙必須排在最左端', '甲、乙必須相鄰且甲在乙的左邊，但甲、丙不可相鄰', '甲、乙必須相鄰，丙、丁也必須相鄰'];
    var ANS = [2 * F1 - 2 * F2, 2 * F1 - 4 * F2, 4 * F2, F1 - 2 * F2, F1 - F2, 4 * F2];
    var ATX = ['2\\times' + (n - 1) + '!-2\\times' + (n - 2) + '!', '2\\times' + (n - 1) + '!-4\\times' + (n - 2) + '!', '4\\times' + (n - 2) + '!',
               (n - 1) + '!-2\\times' + (n - 2) + '!', (n - 1) + '!-' + (n - 2) + '!', '4\\times' + (n - 2) + '!'];
    var HTX = [
      '先算甲乙相鄰（捆綁 ' + T('2\\times' + (n - 1) + '!=' + (2 * F1)) + '），再扣掉「甲乙相鄰且甲丙也相鄰」——此時甲必夾在中間，三人塊只有乙甲丙、丙甲乙 2 種，共 ' + T('2\\times' + (n - 2) + '!=' + (2 * F2)) + ' 種。',
      '甲乙相鄰共 ' + T('2\\times' + (n - 1) + '!=' + (2 * F1)) + ' 種，扣掉「甲乙相鄰且丙丁也相鄰」——兩塊各自可對調，' + T('2\\times2\\times' + (n - 2) + '!=' + (4 * F2)) + ' 種。',
      '丙排最左或最右 2 種，剩下 ' + (n - 1) + ' 個位置裡甲乙要相鄰（捆綁 ' + T('2\\times' + (n - 2) + '!=' + (2 * F2)) + ' 種），相乘得 ' + T('2\\times2\\times' + (n - 2) + '!=' + (4 * F2)) + ' 種。',
      '丙固定在最左端後，其餘 ' + (n - 1) + ' 人任意排 ' + T((n - 1) + '!=' + F1) + ' 種，再扣掉其中甲乙相鄰的 ' + T('2\\times' + (n - 2) + '!=' + (2 * F2)) + ' 種。',
      '「甲在乙的左邊」讓捆綁後的塊內只有 1 種順序，甲乙相鄰共 ' + T((n - 1) + '!=' + F1) + ' 種；其中甲丙相鄰只能是丙甲乙，' + T((n - 2) + '!=' + F2) + ' 種，相減即可。',
      '兩塊各自捆綁：' + (n - 2) + ' 個單位排 ' + T((n - 2) + '!=' + F2) + ' 種，甲乙塊內 2 種、丙丁塊內 2 種 ⟹ ' + T('2\\times2\\times' + (n - 2) + '!=' + (4 * F2)) + ' 種。'];
    return { q: T(String(n)) + ' 人排成一列，若' + COND[v] + '，共有幾種排法？',
             a: T(ATX[v] + '=' + ANS[v]) + ' 種',
             h: HTX[v],
             p: { n: n, v: v, ans: ANS[v] } };
  };
  /* 2-2 相異物分配：每人至少一件（取捨） */
  L2.distributeAll = function (r) {
    var word = r.pick(['物品', '獎品']), g = r.int(3, 4), k = r.int(4, 8), kind = r.int(0, 1), i;
    var who = NAMES.slice(0, g).join('、'), ans = 0, tex = '';
    if (kind === 0) {
      for (i = 0; i < g; i++) {
        var sgn = i % 2 === 0 ? 1 : -1, co = C(g, i), bs = g - i;
        ans += sgn * co * ipow(bs, k);
        tex += (i === 0 ? '' : (sgn > 0 ? '+' : '-')) + (bs === 1 ? String(co) : (co === 1 ? '' : co + '\\cdot') + bs + '^{' + k + '}');
      }
    } else {
      ans = ipow(g, k) - 2 * ipow(g - 1, k) + ipow(g - 2, k);
      tex = g + '^{' + k + '}-2\\cdot' + (g - 1) + '^{' + k + '}' + (g - 2 === 1 ? '+1' : '+' + (g - 2) + '^{' + k + '}');
    }
    var cond = kind === 0 ? who + ' ' + g + ' 人都至少得一件' : '甲、乙都至少得一件';
    var hTail = kind === 0
      ? '扣掉「某一人沒拿到」（' + C(g, 1) + ' 種選法，每件只能給另 ' + (g - 1) + ' 人 ' + T((g - 1) + '^{' + k + '}=' + ipow(g - 1, k)) + '），再依取捨原理逐層補回，得 ' + T(String(ans)) + ' 種。'
      : '扣掉「甲沒拿到」與「乙沒拿到」（各 ' + T((g - 1) + '^{' + k + '}=' + ipow(g - 1, k)) + '），再補回「甲、乙都沒拿到」（' + T((g - 2) + '^{' + k + '}=' + ipow(g - 2, k)) + '），得 ' + T(String(ans)) + ' 種。';
    return { q: T(String(k)) + ' 件不同的' + word + '分給' + who + ' ' + T(String(g)) + ' 人（每人可兼得，也可以沒拿到），若' + cond + '，有幾種分法？',
             a: T(tex + '=' + ans) + ' 種',
             h: '「' + word + '選人」總數 ' + T(g + '^{' + k + '}=' + ipow(g, k)) + '；' + hTail,
             p: { k: k, g: g, kind: kind, ans: ans } };
  };
  /* 2-3 不盡相異物＋不相鄰 */
  L2.multisetGap = function (r) {
    var L = r.pick([['a', 'b', 'c'], ['x', 'y', 'z']]);
    var a = r.int(2, 4), b = r.int(1, 3), c = r.int(1, 3);
    if (a > b + c + 1) c = a - b - 1 + r.int(0, 1);
    var others = fact(b + c) / (fact(b) * fact(c)), gapC = C(b + c + 1, a), ans = others * gapC;
    var tot = fact(a + b + c) / (fact(a) * fact(b) * fact(c));
    var word = L[0].repeat(a) + L[1].repeat(b) + L[2].repeat(c);
    return { q: '將 ' + T(String(a)) + ' 個 ' + T(L[0]) + '、' + T(String(b)) + ' 個 ' + T(L[1]) + '、' + T(String(c)) + ' 個 ' + T(L[2]) + ' 排成一列。(1) 共有幾種排法？(2) 其中 ' + T(L[0]) + ' 互不相鄰的有幾種？',
             a: '(1) ' + T('\\dfrac{' + (a + b + c) + '!}{' + a + '!\\,' + b + '!\\,' + c + '!}=' + tot) + ' 種　(2) ' + T(String(others) + '\\times' + cT(b + c + 1, a) + '=' + ans) + ' 種',
             h: '(1) 不盡相異物排列 ' + T('\\dfrac{' + (a + b + c) + '!}{' + a + '!\\,' + b + '!\\,' + c + '!}=' + tot) + ' 種。(2) 先排 ' + T(L[1] + ',' + L[2]) + '（不盡相異物 ' + others + ' 種），造出 ' + (b + c + 1) + ' 個空隙；' + T(L[0]) + ' 相同 ⟹ 用組合選 ' + a + ' 個空隙 ' + T(cT(b + c + 1, a) + '=' + gapC) + '，共 ' + T(String(ans)) + ' 種。',
             p: { word: word, a: a, b: b, c: c, ans: { tot: tot, apart: ans } } };
  };
  /* 2-4 數字排列：3 的倍數要「先選後排」 */
  L2.digitsMult3 = function (r) {
    var withZero = r() < 0.5, m = r.int(5, 9), mult = r.pick([3, 6]), k = r.int(3, 4), digits = [], i;
    for (i = withZero ? 0 : 1; i <= m; i++) digits.push(i);
    var ans = permsK(digits, k, function (t2) {
      if (t2[0] === 0) return false;
      var v = 0; for (var u = 0; u < k; u++) v = v * 10 + t2[u];
      return v % mult === 0;
    });
    var kw = k === 3 ? '三' : '四';
    var h = mult === 3
      ? '先把 ' + digits.length + ' 個數字依除以 3 的餘數分成三堆，選出「數字和是 3 的倍數」的' + kw + '數組合，再各自排列' + (withZero ? '——含 0 的組合首位不能是 0，要另外扣掉' : '') + '，合計 ' + ans + ' 個。'
      : T('6') + ' 的倍數 ⟺ 同時是 ' + T('2') + ' 與 ' + T('3') + ' 的倍數：先挑出「數字和是 3 的倍數」的' + kw + '數組合，再要求個位是偶數' + (withZero ? '、首位不是 0' : '') + '，合計 ' + ans + ' 個。';
    return { q: '從 ' + T(digits.join(',')) + ' 中任取' + kw + '個不同的數字排成' + kw + '位數，其中是 ' + T(String(mult)) + ' 的倍數的共有幾個？',
             a: T(String(ans)) + ' 個',
             h: h,
             p: { withZero: withZero, m: m, mult: mult, k: k, ans: ans } };
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
      h = '換元 $x=x\'+' + a + '$、$y=y\'+' + b + '$ 變成 $x\'+y\'+z=' + (n - a - b) + '$ 的非負整數解 ⟹ ' + T(cT(n - a - b + 2, 2)) + '。';
    } else {
      ans = C(n + 3, 3);
      q = '求不等式 ' + T('x+y+z\\le' + n) + ' 的非負整數解共有幾組？';
      h = '引入鬆弛變數 $w=' + n + '-x-y-z\\ge0$，變成 $x+y+z+w=' + n + '$ 的非負整數解 ⟹ ' + T(cT(n + 3, 3)) + '。';
    }
    return { q: q, a: T(String(ans)) + ' 組', h: h, p: { kind: kind, n: n, a: a, b: b, ans: ans } };
  };
  /* 2-7 平分成堆＋甲乙同堆 */
  var EQSPLIT = [[6, 3, 2], [6, 2, 3], [8, 4, 2], [8, 2, 4], [9, 3, 3], [10, 5, 2], [10, 2, 5], [12, 6, 2], [12, 4, 3], [12, 3, 4], [12, 2, 6]];
  L2.groupsEqual = function (r) {
    var ctx = r.pick([['同學', '位'], ['球員', '名']]);
    var s = r.pick(EQSPLIT), n = s[0], k = s[1], m = s[2], v = r.int(0, 1);
    var tot = fact(n) / (ipow(fact(m), k) * fact(k));
    var pick2 = C(n - 2, m - 2), rest = fact(n - m) / (ipow(fact(m), k - 1) * fact(k - 1));
    var same = pick2 * rest, ans = v === 0 ? same : tot - same;
    var cond = v === 0 ? '甲、乙在同一組' : '甲、乙不在同一組';
    var pair = '甲、乙這兩' + ctx[1] + ctx[0];
    var pickTx = m === 2 ? pair + '自成一組' : pair + '所在的那一組，再從其餘 ' + (n - 2) + ' ' + ctx[1] + ctx[0] + '中選 ' + (m - 2) + ' ' + ctx[1] + '（' + T(cT(n - 2, m - 2) + '=' + pick2) + '）';
    var restTx = k === 2 ? '剩下 ' + (n - m) + ' ' + ctx[1] + '自成最後一組' : '剩下 ' + (n - m) + ' ' + ctx[1] + '再分成 ' + (k - 1) + ' 個沒區別的組（' + T(String(rest)) + ' 種）';
    var sameTx = T((pick2 === 1 || rest === 1) ? String(same) : pick2 + '\\times' + rest + '=' + same);
    var hTail = v === 0
      ? '(2) ' + pickTx + '，' + restTx + '，共 ' + sameTx + ' 種。'
      : '(2) 先算「' + pair + '同組」：' + pickTx + '，' + restTx + '，共 ' + sameTx + ' 種；再用補集 ' + T(tot + '-' + same + '=' + ans) + ' 種。';
    return { q: '將甲、乙等 ' + T(String(n)) + ' ' + ctx[1] + ctx[0] + '平分成 ' + T(String(k)) + ' 組，每組 ' + T(String(m)) + ' ' + ctx[1] + '（組與組之間沒有區別）。(1) 共有幾種分法？(2) ' + cond + '的分法有幾種？',
             a: '(1) ' + T(String(tot)) + ' 種　(2) ' + T(String(ans)) + ' 種',
             h: '(1) 連續組合相乘之後，因為組沒有名字要再除以 ' + T(k + '!=' + fact(k)) + ' ⟹ ' + T('\\dfrac{' + n + '!}{(' + m + '!)^{' + k + '}\\cdot' + k + '!}=' + tot) + ' 種。' + hTail,
             p: { n: n, k: k, m: m, v: v, ans: { tot: tot, same: ans } } };
  };
  /* 2-8 二項式：x^2 與 1/x 的混合 */
  L2.binomGeneral = function (r) {
    var n = r.int(6, 9), a = r.pick([1, 1, 2]), b = r.pick([1, -1, 2, -2, 3, -3]), kk = r.int(1, n - 1), m = 2 * n - 3 * kk;
    var coef = C(n, kk) * ipow(a, n - kk) * ipow(b, kk);
    var aTex = (a === 1 ? '' : a) + 'x^2', bTex = (b < 0 ? '-' : '+') + '\\dfrac{' + Math.abs(b) + '}{x}';
    var mTex = m === 0 ? '常數項' : ' ' + T(m === 1 ? 'x' : 'x^{' + m + '}') + ' 的係數';
    return { q: '求 ' + T('\\left(' + aTex + bTex + '\\right)^{' + n + '}') + ' 展開式中的' + mTex + '。',
             a: T(String(coef)),
             h: '一般項 $' + cT(n, 'k') + '(' + aTex + ')^{' + n + '-k}\\left(' + bTex.replace(/^\+/, '') + '\\right)^k$，$x$ 的次數 $2(' + n + '-k)-k=' + (2 * n) + '-3k$，令其為 ' + m + ' 得 $k=' + kk + '$。',
             p: { n: n, a: a, b: b, m: m, ans: coef } };
  };
  /* 2-9 組合恆等式求值 */
  L2.combIdentityVal = function (r) {
    var n = r.int(5, 12), kind = r.int(0, 3), q, a, h, t2;
    if (kind === 0) {
      a = ipow(3, n); q = cT(n, 0) + '+2' + cT(n, 1) + '+2^2' + cT(n, 2) + '+\\cdots+2^{' + n + '}' + cT(n, n);
      h = '這是 $(1+x)^{' + n + '}$ 的展開式代 $x=2$ ⟹ ' + T('3^{' + n + '}=' + a) + '。';
    } else if (kind === 1) {
      a = ipow(2, n - 1); var odd = []; for (t2 = 1; t2 <= n; t2 += 2) odd.push(cT(n, t2)); q = odd.join('+');
      h = '奇次項和＝偶次項和：由 $f(1)-f(-1)=2^{' + n + '}$ 得奇次項和 ' + T('2^{' + (n - 1) + '}=' + a) + '。';
    } else if (kind === 2) {
      a = n * ipow(2, n - 1); q = cT(n, 1) + '+2' + cT(n, 2) + '+3' + cT(n, 3) + '+\\cdots+' + n + cT(n, n);
      h = '用 $k' + cT(n, 'k') + '=' + n + cT(n - 1, 'k-1') + '$ 把係數吸收掉，剩下 ' + n + ' 乘上 $(1+1)^{' + (n - 1) + '}$ ⟹ ' + T(n + '\\cdot2^{' + (n - 1) + '}=' + a) + '。';
    } else {
      a = C(2 * n, n); q = '\\left(' + cT(n, 0) + '\\right)^2+\\left(' + cT(n, 1) + '\\right)^2+\\cdots+\\left(' + cT(n, n) + '\\right)^2';
      h = '范德蒙：從 ' + n + ' 男 ' + n + ' 女中選 ' + n + ' 人，依「幾個男生」分類 ⟹ ' + T(cT(2 * n, n) + '=' + a) + '。';
    }
    return { q: '求 ' + T(q) + ' 的值。', a: T(String(a)), h: h, p: { n: n, kind: kind, ans: a } };
  };
  /* 2-10 不相連的選法 */
  L2.nonAdjSelect = function (r) {
    var n = r.int(9, 20), k = r.int(3, 5), apart = C(n - k + 1, k), all = C(n, k), atLeast = all - apart;
    return { q: '從 ' + T('1') + ' 到 ' + T(String(n)) + ' 的整數中選出 ' + T(String(k)) + ' 個數。(1) 任兩個都不相連（不含相鄰的整數）的選法有幾種？(2) 至少有兩個相連的選法有幾種？',
             a: '(1) ' + T(cT(n - k + 1, k) + '=' + apart) + ' 種　(2) ' + T(cT(n, k) + '-' + apart + '=' + atLeast) + ' 種',
             h: '(1) 沒被選的 ' + (n - k) + ' 個數先排好，造出 ' + (n - k + 1) + ' 個空隙，從中選 ' + k + ' 個放被選的數 ⟹ ' + T(cT(n - k + 1, k) + '=' + apart) + ' 種。(2) 用補集：全部 ' + T(cT(n, k) + '=' + all) + ' 扣掉 (1) ⟹ ' + T(all + '-' + apart + '=' + atLeast) + ' 種。',
             p: { n: n, k: k, ans: { apart: apart, atLeast: atLeast } } };
  };
  /* 2-11 機率：至少 2 個 */
  L2.probAtLeast2 = function (r) {
    var m = r.int(5, 8), w = r.int(3, 6), k = r.int(4, 6);
    var tot = C(m + w, k), b0 = C(m, k), b1 = C(w, 1) * C(m, k - 1), bad = b0 + b1, ans = F(tot - bad, tot);
    return { q: '某專輯共 ' + T(String(m + w)) + ' 首歌，其中 ' + T(String(w)) + ' 首抒情歌、' + T(String(m)) + ' 首快歌。隨機挑選 ' + T(String(k)) + ' 首來演唱，求至少選中 ' + T('2') + ' 首抒情歌的機率。',
             a: T('1-\\dfrac{' + cT(m, k) + '+' + cT(w, 1) + cT(m, k - 1) + '}{' + cT(m + w, k) + '}=' + Fr.tex(ans)),
             h: '「至少 2」的反面是「0 首或 1 首抒情歌」：0 首 ' + T(cT(m, k) + '=' + b0) + ' 種、1 首 ' + T(cT(w, 1) + '\\times' + cT(m, k - 1) + '=' + b1) + ' 種，共 ' + T(String(bad)) + ' 種；' + T('n(S)=' + cT(m + w, k) + '=' + tot) + '，所以答案是 ' + T('1-\\dfrac{' + bad + '}{' + tot + '}=' + Fr.tex(ans)) + '。',
             p: { m: m, w: w, k: k, ans: fr2(ans) } };
  };
  /* 2-12 機率的可能範圍 */
  L2.probRange = function (r) {
    var a = r.int(3, 9), b = r.int(3, 9); if (a + b <= 10) b = 11 - a + r.int(0, Math.max(0, 9 - (11 - a)));
    var lo = a + b - 10, hi = Math.min(a, b), big = Math.max(a, b);
    var d = function (x) { return x === 10 ? '1' : (x === 0 ? '0' : '0.' + x); };
    return { q: '設 ' + T('P(A)=' + d(a)) + '、' + T('P(B)=' + d(b)) + '。求 (1) ' + T('P(A\\cup B)') + ' 的範圍　(2) ' + T('P(A\\cap B)') + ' 的範圍　(3) ' + T("P(A\\cap B')") + ' 的範圍。',
             a: '(1) ' + T(d(big) + '\\le P(A\\cup B)\\le1') + '　(2) ' + T(d(lo) + '\\le P(A\\cap B)\\le' + d(hi)) + '　(3) ' + T(d(a - hi) + "\\le P(A\\cap B')\\le" + d(a - lo)),
             h: '(1) 聯集至少是兩者中較大的 ' + T(d(big)) + '、至多是 ' + T('1') + '。(2) 交集下限 ' + T('P(A)+P(B)-1=' + d(a) + '+' + d(b) + '-1=' + d(lo)) + '、上限 ' + T('\\min=' + d(hi)) + '。(3) ' + T("P(A\\cap B')=P(A)-P(A\\cap B)") + ' 隨交集反向：交集最大 ' + T(d(hi)) + ' 時它最小 ' + T(d(a - hi)) + '，交集最小 ' + T(d(lo)) + ' 時它最大 ' + T(d(a - lo)) + '。',
             p: { a: a, b: b, ans: { u: [big, 10], i: [lo, hi], d: [a - hi, a - lo] } } };
  };
  /* 2-13 取完全部球：首末同色／指定位置 */
  L2.drawOrder = function (r) {
    var a = r.int(3, 6), b = r.int(2, 6), k = r.int(2, a + b - 1), n = a + b;
    var same = F(a * (a - 1) + b * (b - 1), n * (n - 1)), pk = F(a, n);
    return { q: '箱中有 ' + T(String(a)) + ' 顆紅球與 ' + T(String(b)) + ' 顆白球（每球被取到的機會相等）。一次取一球、取後不放回，直到取完為止。求 (1) 首、末兩球同色的機率　(2) 第 ' + T(String(k)) + ' 球是紅球的機率。',
             a: '(1) ' + T('\\dfrac{' + dotT([a, a - 1]) + '+' + dotT([b, b - 1]) + '}{' + dotT([n, n - 1]) + '}=' + Fr.tex(same)) + '　(2) ' + T(Fr.tex(pk)),
             h: '(1) 只看首末兩個位置（有序）' + T('n(S)=' + mulT([n, n - 1]) + '=' + (n * (n - 1))) + '；兩球都紅 ' + T(mulT([a, a - 1]) + '=' + (a * (a - 1))) + '、都白 ' + T(mulT([b, b - 1]) + '=' + (b * (b - 1))) + '，相加再除得 ' + T(Fr.tex(same)) + '。(2) 由對稱性，第 ' + k + ' 球是紅球的機率就等於紅球比例 ' + T('\\dfrac{' + a + '}{' + n + '}=' + Fr.tex(pk)) + '。',
             p: { a: a, b: b, k: k, ans: { same: fr2(same), pk: fr2(pk) } } };
  };
  /* 2-14 號碼球成對：號碼差的期望值 */
  L2.expectPairs = function (r) {
    var n = r.int(3, 8), cp = r.int(2, 3), pk = r.int(0, 2), balls = [], i, j;
    for (i = 1; i <= n; i++) for (j = 0; j < cp; j++) balls.push(i);
    var tot = C(cp * n, 2), sameCnt = 0, sum = 0;
    for (i = 0; i < balls.length; i++) for (j = i + 1; j < balls.length; j++) {
      if (balls[i] === balls[j]) sameCnt++;
      sum += pk === 0 ? Math.abs(balls[i] - balls[j]) : (pk === 1 ? balls[i] + balls[j] : balls[i] * balls[j]);
    }
    var pSame = F(sameCnt, tot), E = F(sum, tot), lst = [];
    for (i = 1; i <= n; i++) lst.push(i);
    var name = ['號碼差的絕對值', '號碼和', '號碼乘積'][pk];
    return { q: '袋中有 ' + T(lst.join(',')) + ' 號球各 ' + T(String(cp)) + ' 顆，共 ' + T(String(cp * n)) + ' 顆，每球被抽中的機會均等。同時取出兩球，求 (1) 兩球號碼相同的機率　(2) 若兩球的' + name + '為 ' + T('k') + ' 時可得 ' + T('k') + ' 元，求獎金的期望值。',
             a: '(1) ' + T(Fr.tex(pSame)) + '　(2) ' + T(Fr.tex(E)) + ' 元',
             h: T('n(S)=' + cT(cp * n, 2) + '=' + tot) + '。(1) 同號的取法有 ' + T(n + '\\times' + cT(cp, 2) + '=' + sameCnt) + ' 種，機率 ' + T(Fr.tex(pSame)) + '。(2) 把 ' + tot + ' 種取法的' + name + '全部加起來得 ' + T(String(sum)) + '，再除以 ' + tot + ' ⟹ ' + T(Fr.tex(E)) + ' 元。',
             p: { n: n, c: cp, pk: pk, ans: { pSame: fr2(pSame), E: fr2(E) } } };
  };
  /* 2-15 三顆骰子的公平遊戲 */
  L2.fairMulti = function (r) {
    var A = r.pick([50, 60, 100, 120]), B = r.pick([10, 15, 20, 25]), Cc = r.pick([2, 3, 4, 5]);
    var win = A * 1 + B * 15 + Cc * 75, x = F(win, 125);
    return { q: '同時投擲三顆公正骰子。三顆都是 ' + T('6') + ' 點可得 ' + T(String(A)) + ' 元、恰有兩顆 ' + T('6') + ' 點可得 ' + T(String(B)) + ' 元、恰有一顆 ' + T('6') + ' 點可得 ' + T(String(Cc)) + ' 元；一顆 ' + T('6') + ' 點都沒有則要賠 ' + T('x') + ' 元。為使遊戲公平，' + T('x') + ' 應為多少？',
             a: T('x=' + Fr.tex(x)) + ' 元',
             h: '$n(S)=216$；三個 6：1 種、恰兩個 6：$C^3_2\\cdot5=15$ 種、恰一個 6：$C^3_1\\cdot5^2=75$ 種、沒有 6：$125$ 種。公平 ⟺ ' + T(dotT([A, 1]) + '+' + dotT([B, 15]) + '+' + dotT([Cc, 75]) + '=' + win) + '，再除以 125 得 ' + T('x=' + Fr.tex(x)) + '。',
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
  var WORDS = ['SUCCESS', 'BANANA', 'LETTER', 'COFFEE', 'GOOGLE', 'ASSESS', 'PEPPER', 'BALLOON', 'TATTOO', 'CHEESE', 'BUTTER', 'APPLE', 'HAPPY', 'MAMMAL',
               'PARALLEL', 'COMMITTEE', 'TOMORROW', 'ADDRESS', 'SUCCEED', 'ARRANGE'];
  L2.lettersSelect = function (r) {
    var w = r.pick(WORDS), t = r.int(3, 4), seen = {}, sel = {}, cntMap = {}, i;
    for (i = 0; i < w.length; i++) cntMap[w[i]] = (cntMap[w[i]] || 0) + 1;
    permsK(w.split(''), t, function (cur) {
      seen[cur.join('')] = 1; sel[cur.slice().sort().join('')] = 1; return false;
    });
    var cnt = Object.keys(seen).length, cs = Object.keys(sel).length;
    var desc = Object.keys(cntMap).map(function (ch) { return T('\\text{' + ch + '}') + ' ' + cntMap[ch] + ' 個'; }).join('、');
    return { q: '從 ' + T('\\text{' + w + '}') + ' 這個字的諸字母中任取 ' + T(String(t)) + ' 個：(1) 共有幾種選法？(2) 排成一列共有幾種排法？',
             a: '(1) ' + T(String(cs)) + ' 種　(2) ' + T(String(cnt)) + ' 種',
             h: '先數清各字母的個數：' + desc + '。再依「重複的字母各取幾個」分類（全部相異／恰有兩個相同／…），每一類的選法相加得 ' + T(String(cs)) + ' 種；每一類再乘上該類的相異排列數 ' + T('\\dfrac{' + t + '!}{\\cdots}') + '，合計 ' + T(String(cnt)) + ' 種。',
             p: { w: w, t: t, ans: { sel: cs, arr: cnt } } };
  };
  /* 2-18 三顆骰子的結構機率 */
  L2.dice3 = function (r) {
    var kind = r.int(0, 10), par = 0, a, b, c, cnt = 0;
    if (kind === 3) par = r.int(4, 15);
    else if (kind === 4) par = r.int(2, 6);
    else if (kind === 5) par = r.int(1, 5);
    else if (kind === 10) par = r.int(12, 16);
    for (a = 1; a <= 6; a++) for (b = 1; b <= 6; b++) for (c = 1; c <= 6; c++) {
      var s = [a, b, c].sort(function (u, v) { return u - v; }), sum = a + b + c, ok;
      if (kind === 0) ok = s[0] + s[1] > s[2];
      else if (kind === 1) ok = (a === b || b === c || a === c) && !(a === b && b === c);
      else if (kind === 2) ok = s[1] - s[0] === s[2] - s[1] && s[0] !== s[2];
      else if (kind === 3) ok = sum === par;
      else if (kind === 4) ok = s[2] === par;
      else if (kind === 5) ok = s[0] === par;
      else if (kind === 6) ok = s[0] !== s[1] && s[1] !== s[2];
      else if (kind === 7) ok = (a * b * c) % 2 === 0;
      else if (kind === 8) ok = a === 6 || b === 6 || c === 6;
      else if (kind === 9) ok = sum % 3 === 0;
      else ok = sum >= par;
      if (ok) cnt++;
    }
    var EV = ['三個點數可以作為一個三角形的三邊長', '恰有兩顆點數相同', '三個點數由小到大排成公差不為 ' + T('0') + ' 的等差數列',
      '三顆點數和為 ' + T(String(par)), '三顆之中最大的點數為 ' + T(String(par)), '三顆之中最小的點數為 ' + T(String(par)),
      '三顆點數兩兩不同', '三顆點數的乘積為偶數', '至少有一顆是 ' + T('6') + ' 點', '三顆點數和是 ' + T('3') + ' 的倍數',
      '三顆點數和至少為 ' + T(String(par))];
    var HS = ['依最大點數分類，檢查「兩小邊之和 $\\gt$ 最大邊」；等腰、正三角形都算，共 ' + cnt + ' 種。',
      '選哪兩顆相同 ' + T(cT(3, 2) + '=3') + '、那個點數 6 種、第三顆與它們不同 5 種 ⟹ ' + T('3\\times6\\times5=' + cnt) + ' 種。',
      '先找出等差三元組（公差 $1$、$2$ 各幾組），每組再乘上排列 ' + T('3!=6') + ' ⟹ 共 ' + cnt + ' 種。',
      '把和為 ' + par + ' 的有序三元組逐一列出來數，共 ' + cnt + ' 種。',
      '最大點數為 ' + par + ' ⟺ 三顆都 ' + T('\\le' + par) + ' 但不是三顆都 ' + T('\\le' + (par - 1)) + ' ⟹ ' + T(par + '^3-' + (par - 1) + '^3=' + cnt) + ' 種。',
      '最小點數為 ' + par + ' ⟺ 三顆都 ' + T('\\ge' + par) + ' 但不是三顆都 ' + T('\\ge' + (par + 1)) + ' ⟹ ' + T((7 - par) + '^3-' + (6 - par) + '^3=' + cnt) + ' 種。',
      '第一顆 6 種、第二顆 5 種、第三顆 4 種 ⟹ ' + T('6\\times5\\times4=' + cnt) + ' 種。',
      '用餘事件：乘積為奇數 ⟺ 三顆都是奇數 ' + T('3^3=27') + ' 種 ⟹ ' + T('216-27=' + cnt) + ' 種。',
      '用餘事件：一顆 $6$ 點都沒有 ' + T('5^3=125') + ' 種 ⟹ ' + T('216-125=' + cnt) + ' 種。',
      '每顆骰子除以 3 的餘數 $0,1,2$ 各有 2 個點數，餘數和是 3 的倍數的組合只有 $(0,0,0)$、$(1,1,1)$、$(2,2,2)$、$(0,1,2)$ 四類 ⟹ 共 ' + cnt + ' 種。',
      '把和 ' + T('\\ge' + par) + '（即 ' + par + ' 到 $18$）的個數加起來，共 ' + cnt + ' 種。'];
    return { q: '同時投擲三顆公正骰子，求「' + EV[kind] + '」的機率。', a: T(pr(cnt, 216)), h: '$n(S)=6^3=216$。' + HS[kind],
             p: { kind: kind, par: par, ans: fr2(F(cnt, 216)) } };
  };

  /* ══════════════════════════════════════════════════════════ */
  /* ══════════════════════════════════════════════════════════
     L1 解題步驟（s：每步一段 HTML）與第一層提示（h1：只講「這是哪一型、第一步做什麼」，不帶數字）
     全部由 p（與 o.a）重算，所以與題目、答案一定一致；答案由頁面另行附在步驟後。
     用法：用 splice 腳本插在 META（var META_L1 = [）之前，並把 wrapAll(L1) 換成 wrapAll(L1, L1_SOL, L1_H1)。
     自己加的小工具一律加前綴 sol。
     ══════════════════════════════════════════════════════════ */
  function solF(t) { return F(t[0], t[1]); }                      /* p 裡的 [n,d] 還原成分數 */
  function solFin(o) { return '答案：' + o.a + '。'; }
  function solDigits(m) { var d = [], i; for (i = 0; i <= m; i++) d.push(i); return d; }
  function solMulT(list) {                                        /* 等於 1 的因數省略 */
    var f = [], i;
    for (i = 0; i < list.length; i++) if (String(list[i]) !== '1') f.push(list[i]);
    return f.length ? f.join('\\times') : '1';
  }
  function solDec(x) { return x === 10 ? '1' : (x === 0 ? '0' : '0.' + x); }   /* eventOps 的 0.x */
  function solFrac(num, den) {                                    /* \dfrac{num}{den}；約分後長得不一樣才再寫一次 */
    var f = F(num, den), raw = '\\dfrac{' + num + '}{' + den + '}';
    return Fr.tex(f) === raw ? raw : raw + '=' + Fr.tex(f);
  }
  function solPow(base, e) {                                      /* 乘上 base^e：底數 1 整個省略、指數 1 不寫 */
    if (base === 1) return '';
    return '\\cdot' + (base < 0 ? '(' + base + ')' : String(base)) + (e === 1 ? '' : '^{' + e + '}');
  }

  var L1_H1 = {
    routes: '這是「加法原理 vs 乘法原理」：先分清楚哪些是「分類」（要相加）、哪些是「分步」（要相乘），再逐段算。',
    passcode: '這是「乘法原理的三種變化」：可重複用次方、不可重複用排列數；有位置限制時一定要先排最受限的那一位。',
    digitsEven: '這是「含 $0$ 的數字排列」：先處理最高位不能是 $0$ 的限制，再依個位的條件分類討論。',
    multiples: '這是「倍數計數」：兩個條件的交集是最小公倍數的倍數，用取捨原理加加減減。',
    venn3: '這是「三集合取捨」：把文氏圖的七塊區域從最裡面往外一塊一塊填出來，要哪一塊就讀哪一塊。',
    complement: '這是「補集法」：看到「至少」就先想反面，用全部扣掉反面比正面分類快得多。',
    permBasic: '這是「排列數的基本運算」：全排列用階乘、選一部分來排用排列數，有限制的位置先固定再排其餘。',
    bundle: '這是「捆綁法／插空法」：要相鄰就綁成一包當一個單位，要不相鄰就先排別人再把他們插進空隙。',
    gaps: '這是「插空法」：先把沒有限制的人排好，數出空隙，再把有「不相鄰」限制的人放進不同的空隙。',
    fixedOrder: '這是「固定順序」：先當成全部任意排，再除以那幾個人所有相對順序的個數，因為只有一種合格。',
    multisetPerm: '這是「不盡相異物排列」：先用階乘除以各色相同球個數的階乘；要不相鄰再用插空法選空隙。',
    gridPath: '這是「格子路徑」：一條路徑就是「右」與「上」的一個排列；必須經過某點就拆成兩段相乘。',
    repPerm: '這是「重複排列」：用「球選箱」的角度想，每顆球各自獨立地選一個箱子。',
    combVsPerm: '這是「組合與排列的分辨」：職位相同只要選人（組合），職位不同還要排（排列）。',
    atLeastComb: '這是「至少型組合」：「至少」用補集扣掉反面，「恰好」直接分步先選這邊再選那邊。',
    groups: '這是「分組 vs 分堆」：有名字的直接連續組合相乘，沒名字的要再除以「同人數的堆」個數的階乘。',
    bars: '這是「隔板法」：相同的球排成一列，在球與球之間的空隙插隔板；允許空箱就先借球給每箱一顆。',
    geomLines: '這是「幾何計數的共線修正」：先當成沒有共線點來算，再把共線造成的重複或不合格扣掉。',
    rectCount: '這是「矩形與正方形計數」：矩形＝橫線選兩條、直線選兩條；正方形要依邊長分類再相加。',
    binomTerm: '這是「二項式的特定項」：先寫出一般項，讓 $x$ 的次數等於題目要的次數，解出是第幾項。',
    coefSum: '這是「代值法求係數和」：把 $x$ 代成 $1$、$0$、$-1$，就能把想要的那一組係數湊出來。',
    hockey: '這是「曲棍棒恆等式」：下標固定、上標連續相加，答案就是「上標加一、下標加一」的那個組合數。',
    dice2: '這是「兩顆骰子的古典機率」：樣本空間是有序對，先數出符合事件的有序對個數再除以總數。',
    coins: '這是「硬幣的古典機率」：樣本空間是正反面的字串，恰有幾次正面就是「選哪幾次是正面」。',
    eventOps: '這是「事件的運算」：把文氏圖切成「只有 $A$、只有 $B$、都有、都沒有」四塊，四塊加起來是 $1$。',
    drawBalls: '這是「取球的古典機率」：同色球也要視為不同的球，樣本空間用組合數；「至少」改算餘事件。',
    lottery: '這是「抽籤的公平性」：抽籤與順序無關，任何一個指定位置中獎的機率都跟第一位一樣。',
    expBasic: '這是「期望值的定義」：把每一種結果的「值 × 機率」全部加起來。',
    expShift: '這是「期望值的線性」：先知道點數本身的期望值，再套 $E(ak+b)=a\\,E(k)+b$。',
    fairGame: '這是「公平遊戲」：公平的意思就是期望值為 $0$，把得與賠的「值 × 機率」相加後解方程式。',
    expLinear: '這是「期望值的線性」：總金額是每一張金額的和，每一張的期望值都等於單張平均，不放回也一樣。',
    expMax: '這是「較大（較小）號碼的期望值」：先數出「較大號碼剛好是某個值」的取法有幾種，再加權平均。'
  };

  var L1_SOL = {};

  /* ── §1 計數原理 ── */
  L1_SOL.routes = function (p, o) {
    var via = p.a * p.b, one = p.ans.one, rt = p.ans.rt;
    return ['(1) 先分類：走法只有「經過乙地」與「直接到丙地」兩類。經乙地是分步（甲→乙、乙→丙），' + T(p.a + '\\times' + p.b + '=' + via) + ' 種；直達 ' + T(String(p.c)) + ' 種。',
      '兩類沒有重疊，用加法原理：' + T(via + '+' + p.c + '=' + one) + ' 種。',
      '(2) 去程與回程是分步，而且路線可以重複，所以各有 ' + one + ' 種：' + T(one + '\\times' + one + '=' + rt) + ' 種。' + solFin(o)];
  };

  L1_SOL.passcode = function (p, o) {
    var base = p.m + 1, k = p.k, lead = p.v === 0 ? p.m : Math.floor(base / 2);
    var rest = P(p.m, k - 1);
    return ['(1) 數字可以重複時每一位互不影響，每位都有 ' + base + ' 種選擇，用乘法原理：' + T(base + '^{' + k + '}=' + p.ans.a1) + ' 組。',
      '(2) 不可重複就是「從 ' + base + ' 個數字取 ' + k + ' 個排成一列」：' + T(pT(base, k) + '=' + p.ans.a2) + ' 組。',
      '(3) 有限制的位置要先排：第一位' + (p.v === 0 ? '不能是 ' + T('0') + '，有 ' + lead + ' 種' : '必須是奇數，有 ' + lead + ' 種') + '；第一位定了之後，其餘 ' + (k - 1) + ' 位從剩下的 ' + p.m + ' 個數字排 ' + T(pT(p.m, k - 1) + '=' + rest) + ' 種。',
      '相乘得 ' + T(solMulT([lead, rest]) + '=' + p.ans.a3) + ' 組。' + solFin(o)];
  };

  L1_SOL.digitsEven = function (p, o) {
    var ds = solDigits(p.m), k = p.k, m = p.m, rest = P(m, k - 1);
    var zero = permsK(ds, k, function (t) { return t[0] !== 0 && t[k - 1] === 0; });
    var other = p.ans.ev - zero;
    var mid = p.v === 1
      ? '(2) 個位必須是奇數，' + m + ' 以內的奇數不含 ' + T('0') + '，所以個位選完之後最高位只要避開 ' + T('0') + ' 與個位那個數字即可，合計 ' + p.ans.ev + ' 個。'
      : '(2) 條件在個位，依「個位是不是 ' + T('0') + '」分成兩類：個位是 ' + T('0') + ' 的有 ' + zero + ' 個；個位不是 ' + T('0') + ' 的有 ' + other + ' 個（此時最高位要同時避開 ' + T('0') + ' 與個位那個數字）。';
    return ['(1) 最高位不能是 ' + T('0') + '，有 ' + m + ' 種；其餘 ' + (k - 1) + ' 位從剩下的 ' + m + ' 個數字取排列 ' + T(pT(m, k - 1) + '=' + rest) + ' 種。相乘得 ' + T(solMulT([m, rest]) + '=' + p.ans.tot) + ' 個。',
      mid,
      '兩類相加共 ' + T(String(p.ans.ev)) + ' 個。' + solFin(o)];
  };

  L1_SOL.multiples = function (p, o) {
    var l = p.a * p.b / gcd(p.a, p.b);
    var nA = Math.floor(p.N / p.a), nB = Math.floor(p.N / p.b), nAB = Math.floor(p.N / l);
    return ['先數出兩個集合：' + p.a + ' 的倍數有 ' + T(String(nA)) + ' 個、' + p.b + ' 的倍數有 ' + T(String(nB)) + ' 個。',
      '交集是「同時是 ' + p.a + ' 與 ' + p.b + ' 的倍數」，也就是最小公倍數 ' + T(String(l)) + ' 的倍數，有 ' + T(String(nAB)) + ' 個。',
      p.kind === 0
        ? '「或」是聯集，用取捨原理 ' + T('n(A\\cup B)=' + nA + '+' + nB + '-' + nAB + '=' + p.ans) + ' 個。' + solFin(o)
        : '「是 ' + p.a + ' 的倍數但不是 ' + p.b + ' 的倍數」是差集，從 ' + p.a + ' 的倍數扣掉交集 ' + T(nA + '-' + nAB + '=' + p.ans) + ' 個。' + solFin(o)];
  };

  L1_SOL.venn3 = function (p, o) {
    var ab = p.AB - p.ABC, bc = p.BC - p.ABC, ac = p.AC - p.ABC;
    var oA = p.A - ab - ac - p.ABC, oB = p.B - ab - bc - p.ABC, oC = p.C - ac - bc - p.ABC;
    return ['(1) 三集合取捨：加三個單獨的、減三個兩兩的、再把三個都有的加回來 ⟹ ' + T(p.A + '+' + p.B + '+' + p.C + '-' + p.AB + '-' + p.BC + '-' + p.AC + '+' + p.ABC + '=' + p.ans.union) + ' 人。',
      '(2) 全班扣掉「至少參加一個」就是「都沒參加」：' + T(p.N + '-' + p.ans.union + '=' + p.ans.none) + ' 人。',
      '(3) 從最裡面往外填七塊：三社都參加 ' + p.ABC + ' 人；只 A、B 兩社 ' + T(p.AB + '-' + p.ABC + '=' + ab) + ' 人，只 B、C ' + T(String(bc)) + ' 人，只 A、C ' + T(String(ac)) + ' 人。',
      '再往外：只 A 社 ' + T(p.A + '-' + ab + '-' + ac + '-' + p.ABC + '=' + oA) + ' 人，同理只 B 社 ' + T(String(oB)) + ' 人、只 C 社 ' + T(String(oC)) + ' 人，相加 ' + T(oA + '+' + oB + '+' + oC + '=' + p.ans.only) + ' 人。' + solFin(o)];
  };

  L1_SOL.complement = function (p, o) {
    if (p.kind === 0) {
      var n = p.n, tot0 = ipow(6, n), bad0 = ipow(5, n);
      return ['「至少有一次」正面算要分成恰一次、恰兩次…很麻煩，改算反面。',
        '反面是「' + n + ' 次都不是 ' + p.f + ' 點」，每次只剩 5 種：' + T('5^{' + n + '}=' + bad0) + ' 種；全部的情形有 ' + T('6^{' + n + '}=' + tot0) + ' 種。',
        '相減得 ' + T(tot0 + '-' + bad0 + '=' + p.ans) + ' 種。' + solFin(o)];
    }
    if (p.kind === 1) {
      var k = p.k, tot1 = ipow(10, k), bad1 = ipow(9, k);
      return ['「至少出現一個 ' + p.d + '」的反面是「每一位都不是 ' + p.d + '」。',
        '每一位只剩 9 種：' + T('9^{' + k + '}=' + bad1) + ' 組；全部的密碼有 ' + T('10^{' + k + '}=' + tot1) + ' 組。',
        '相減得 ' + T(tot1 + '-' + bad1 + '=' + p.ans) + ' 組。' + solFin(o)];
    }
    var m = p.m, tot2 = ipow(6, m), bad2 = P(6, m);
    return ['「至少有兩次點數相同」的反面是「' + m + ' 次點數全都不一樣」。',
      '全不相同就是從 6 個點數取 ' + m + ' 個排列：' + T(pT(6, m) + '=' + bad2) + ' 種；全部的情形有 ' + T('6^{' + m + '}=' + tot2) + ' 種。',
      '相減得 ' + T(tot2 + '-' + bad2 + '=' + p.ans) + ' 種。' + solFin(o)];
  };

  /* ── §2 排列 ── */
  L1_SOL.permBasic = function (p, o) {
    var n = p.n, third = ['甲固定在第一位，其餘 ' + (n - 1) + ' 人任意排 ' + T((n - 1) + '!=' + fact(n - 1)) + ' 種',
      '甲可以站在第 2 到第 ' + n + ' 位共 ' + (n - 1) + ' 個位置，其餘 ' + (n - 1) + ' 人任意排 ' + T((n - 1) + '!=' + fact(n - 1)) + ' 種，相乘 ' + T((n - 1) + '\\times' + (n - 1) + '!=' + p.ans.first) + ' 種',
      '甲、乙誰在左端有 2 種，中間 ' + (n - 2) + ' 人任意排 ' + T((n - 2) + '!=' + fact(n - 2)) + ' 種，相乘 ' + T('2\\times' + (n - 2) + '!=' + p.ans.first) + ' 種'][p.v];
    return ['(1) ' + n + ' 個人全部排成一列就是 ' + n + ' 的階乘：' + T(n + '!=' + p.ans.all) + ' 種。',
      '(2) 只選 ' + p.k + ' 人出來排，是排列數 ' + T(pT(n, p.k) + '=' + p.ans.sel) + ' 種（選完還要排，所以不是組合）。',
      '(3) 有限制的位置先處理：' + third + '。' + solFin(o)];
  };

  L1_SOL.bundle = function (p, o) {
    var n = p.n, m = p.m;
    if (p.v === 0) {
      return ['要「相鄰」就用捆綁法：把這 ' + m + ' 人綁成一包，當成一個單位。',
        '這樣總共有 ' + (n - m) + ' 個散的人加 1 包＝' + (n - m + 1) + ' 個單位，先排單位 ' + T((n - m + 1) + '!=' + fact(n - m + 1)) + ' 種。',
        '包裡面這 ' + m + ' 人自己還能排 ' + T(m + '!=' + fact(m)) + ' 種，相乘 ' + T((n - m + 1) + '!\\times' + m + '!=' + p.ans) + ' 種。' + solFin(o)];
    }
    if (p.v === 1) {
      return ['一樣先捆綁：' + m + ' 人綁成一包，連同其他 ' + (n - m) + ' 人共 ' + (n - m + 1) + ' 個單位。',
        '單位之間任意排 ' + T((n - m + 1) + '!=' + fact(n - m + 1)) + ' 種。',
        '但包內的左右順序已經被題目指定死了，只有 1 種，所以不再乘 ' + T(m + '!') + '，答案就是 ' + T(String(p.ans)) + ' 種。' + solFin(o)];
    }
    return ['要「兩兩不相鄰」就用插空法：先把沒有限制的另外 ' + (n - m) + ' 人排好，' + T((n - m) + '!=' + fact(n - m)) + ' 種。',
      '這 ' + (n - m) + ' 人會造出 ' + (n - m + 1) + ' 個空隙（含頭尾），把 ' + m + ' 人放進其中 ' + m + ' 個不同的空隙，因為人不同所以是排列 ' + T(pT(n - m + 1, m) + '=' + P(n - m + 1, m)) + ' 種。',
      '相乘得 ' + T(solMulT([fact(n - m), pT(n - m + 1, m)]) + '=' + p.ans) + ' 種。' + solFin(o)];
  };

  L1_SOL.gaps = function (p, o) {
    var m = p.m, k = p.k;
    return ['(1) 「互不相鄰」用插空法：先把 ' + m + ' 位沒有限制的人排好，' + T(m + '!=' + fact(m)) + ' 種。',
      '他們之間（含頭尾）有 ' + (m + 1) + ' 個空隙，把 ' + k + ' 位有限制的人放進 ' + k + ' 個不同的空隙：' + T(pT(m + 1, k) + '=' + P(m + 1, k)) + ' 種，相乘得 ' + T(m + '!\\times' + pT(m + 1, k) + '=' + p.ans.apart) + ' 種。',
      '(2) 「全部相鄰」改用捆綁法：' + k + ' 人綁成一包，連同另外 ' + m + ' 人共 ' + (m + 1) + ' 個單位排 ' + T((m + 1) + '!=' + fact(m + 1)) + ' 種，包內再排 ' + T(k + '!=' + fact(k)) + ' 種，相乘 ' + T(String(p.ans.together)) + ' 種。' + solFin(o)];
  };

  L1_SOL.fixedOrder = function (p, o) {
    var n = p.n, m = p.m;
    if (p.v === 0) {
      return ['先不管順序限制，' + n + ' 人任意排有 ' + T(n + '!=' + fact(n)) + ' 種。',
        '把這 ' + n + '! 種依「那 ' + m + ' 人的相對順序」分堆，每一堆都有 ' + T(m + '!=' + fact(m)) + ' 種，而題目要的順序只是其中 1 種。',
        '所以要除掉：' + T('\\dfrac{' + n + '!}{' + m + '!}=' + p.ans) + ' 種。' + solFin(o)];
    }
    if (p.v === 1) {
      return ['甲已經被固定在第一位，剩下的 ' + (n - 1) + ' 人任意排有 ' + T((n - 1) + '!=' + fact(n - 1)) + ' 種。',
        '甲已經在最左邊，所以只剩另外 ' + (m - 1) + ' 人的相對順序要管，他們共有 ' + T((m - 1) + '!=' + fact(m - 1)) + ' 種相對順序，只有 1 種合格。',
        '除掉得 ' + T('\\dfrac{' + (n - 1) + '!}{' + (m - 1) + '!}=' + p.ans) + ' 種。' + solFin(o)];
    }
    return [NAMES[m] + ' 已經被固定在最後一位，剩下的 ' + (n - 1) + ' 人任意排有 ' + T((n - 1) + '!=' + fact(n - 1)) + ' 種。',
      '其中那 ' + m + ' 人的 ' + T(m + '!=' + fact(m)) + ' 種相對順序只有 1 種合格。',
      '除掉得 ' + T('\\dfrac{' + (n - 1) + '!}{' + m + '!}=' + p.ans) + ' 種。' + solFin(o)];
  };

  L1_SOL.multisetPerm = function (p, o) {
    var a = p.a, b = p.b, c = p.c, n = a + b + c;
    var others = fact(a + c) / (fact(a) * fact(c)), gapC = C(a + c + 1, b);
    return ['(1) 同色球彼此相同，是不盡相異物排列：' + n + ' 顆球先當成都不同有 ' + T(n + '!=' + fact(n)) + ' 種，再把每一色內部的重複除掉。',
      '得 ' + T('\\dfrac{' + n + '!}{' + a + '!\\,' + b + '!\\,' + c + '!}=' + p.ans.tot) + ' 種。',
      '(2) 要不相鄰用插空法：先把另外兩色的 ' + (a + c) + ' 顆球排好 ' + T('\\dfrac{' + (a + c) + '!}{' + a + '!\\,' + c + '!}=' + others) + ' 種，造出 ' + (a + c + 1) + ' 個空隙。',
      '這 ' + b + ' 顆球彼此相同，只要選 ' + b + ' 個空隙即可（組合）：' + T(cT(a + c + 1, b) + '=' + gapC) + '，相乘得 ' + T(others + '\\times' + gapC + '=' + p.ans.apart) + ' 種。' + solFin(o)];
  };

  L1_SOL.gridPath = function (p, o) {
    var R = p.R, U = p.U, toP = C(p.px + p.py, p.py), toB = C(R - p.px + U - p.py, U - p.py);
    return ['(1) 每一條最短路徑都要走 ' + R + ' 步「右」與 ' + U + ' 步「上」，共 ' + (R + U) + ' 步；決定哪 ' + U + ' 步向上，路徑就定了。',
      '所以是 ' + T(cT(R + U, U) + '=' + p.ans.tot) + ' 條。',
      '(2) 必須經過 ' + T('P') + ' 就把路徑拆成兩段相乘：' + T('A') + ' 到 ' + T('P') + ' 要走右 ' + p.px + '、上 ' + p.py + '，有 ' + T(cT(p.px + p.py, p.py) + '=' + toP) + ' 條；' + T('P') + ' 到 ' + T('B') + ' 要走右 ' + (R - p.px) + '、上 ' + (U - p.py) + '，有 ' + T(cT(R - p.px + U - p.py, U - p.py) + '=' + toB) + ' 條。',
      '相乘得 ' + T(toP + '\\times' + toB + '=' + p.ans.via) + ' 條。' + solFin(o)];
  };

  L1_SOL.repPerm = function (p, o) {
    var k = p.k, n = p.n;
    return ['(1) 這是重複排列，要站在「每一個物品各自選一個容器」的角度想（不是容器選物品）。',
      '每一個物品都有 ' + n + ' 種選擇、彼此獨立，' + T(n + '^{' + k + '}=' + p.ans.tot) + ' 種。',
      p.v === 0
        ? '(2) 「至少一個」用餘事件：反面是「每一個都不選第一個容器」，各剩 ' + (n - 1) + ' 種 ' + T((n - 1) + '^{' + k + '}=' + ipow(n - 1, k)) + ' 種，相減得 ' + T(n + '^{' + k + '}-' + (n - 1) + '^{' + k + '}=' + p.ans.atLeast) + ' 種。' + solFin(o)
        : '(2) 「恰有一個」先選是哪一個物品放進第一個容器（' + k + ' 種），其餘 ' + (k - 1) + ' 個都不能放進去，各剩 ' + (n - 1) + ' 種，得 ' + T(k + '\\times' + (n - 1) + '^{' + (k - 1) + '}=' + p.ans.atLeast) + ' 種。' + solFin(o)];
  };

  /* ── §3 組合 ── */
  L1_SOL.combVsPerm = function (p, o) {
    var n = p.n, k = p.k;
    return ['(1) 「職位相同」代表選出來的 ' + k + ' 個人不分先後，只要問「選哪 ' + k + ' 位」，是組合：' + T(cT(n, k) + '=' + p.ans.c) + ' 種。',
      '(2) 「' + k + ' 個不同的職位」代表選完還要決定誰擔任哪一個，是排列：' + T(pT(n, k) + '=' + p.ans.p) + ' 種。',
      '兩者剛好差 ' + T(k + '!=' + fact(k)) + ' 倍（每一種選法都能再排 ' + T(k + '!') + ' 次）：' + T(p.ans.c + '\\times' + fact(k) + '=' + p.ans.p) + '。' + solFin(o)];
  };

  L1_SOL.atLeastComb = function (p, o) {
    var m = p.m, w = p.w, k = p.k, j = p.j;
    var tot = C(m + w, k), allMen = C(m, k), cw = C(w, j), cm = C(m, k - j);
    return ['(1) 「至少 1 位女生」的反面是「一位女生都沒有」，也就是 ' + k + ' 人全是男生。',
      '全部選法 ' + T(cT(m + w, k) + '=' + tot) + ' 種，全男 ' + T(cT(m, k) + '=' + allMen) + ' 種，相減得 ' + T(tot + '-' + allMen + '=' + p.ans.a1) + ' 種。',
      '(2) 「恰好 ' + j + ' 位女生」不用補集，直接分步：先從 ' + w + ' 位女生選 ' + j + ' 位 ' + T(cT(w, j) + '=' + cw) + '，再從 ' + m + ' 位男生選 ' + (k - j) + ' 位 ' + T(cT(m, k - j) + '=' + cm) + '。',
      '相乘得 ' + T(cw + '\\times' + cm + '=' + p.ans.a2) + ' 種。' + solFin(o)];
  };

  L1_SOL.groups = function (p, o) {
    var n = p.n, sizes = p.sizes, steps = [], rem = n, cnt = {}, i;
    for (i = 0; i < sizes.length; i++) { if (C(rem, sizes[i]) > 1) steps.push(cT(rem, sizes[i])); rem -= sizes[i]; cnt[sizes[i]] = (cnt[sizes[i]] || 0) + 1; }
    var div = 1; Object.keys(cnt).forEach(function (z) { div *= fact(cnt[z]); });
    return ['(1) 有名字（分給指定的人）就直接一堆一堆地選：先選第一個人的，再從剩下的選第二個人的，依此類推。',
      '連續組合相乘 ' + T(steps.join('\\times') + '=' + p.ans.named) + ' 種，這裡不用除。',
      div === 1
        ? '(2) 沒名字（只分成幾堆）時，只有「個數相同的堆」互換才會被重複算；本題每一堆的個數都不一樣，所以不必除，答案仍是 ' + T(String(p.ans.unnamed)) + ' 種。' + solFin(o)
        : '(2) 沒名字（只分成幾堆）時，個數相同的堆互換會被重複算：本題要除以 ' + T(String(div)) + '。',
      div === 1 ? '' : T('\\dfrac{' + p.ans.named + '}{' + div + '}=' + p.ans.unnamed) + ' 種。' + solFin(o)].filter(function (x) { return x !== ''; });
  };

  L1_SOL.bars = function (p, o) {
    var n = p.n, k = p.k;
    return ['(1) 球都一樣、箱子不同，所以只要決定「每箱各幾顆」。把 ' + n + ' 顆球排成一列，它們之間有 ' + (n - 1) + ' 個空隙。',
      '每箱至少一球 ⟹ 從這 ' + (n - 1) + ' 個空隙選 ' + (k - 1) + ' 個插隔板：' + T(cT(n - 1, k - 1) + '=' + p.ans.pos) + ' 種。',
      '(2) 允許空箱時先「借」' + k + ' 顆球，每箱先各放一顆，就變成把 ' + (n + k) + ' 顆球放進 ' + k + ' 箱且每箱至少一顆。',
      '再套 (1)：' + T(cT(n + k - 1, k - 1) + '=' + p.ans.non) + ' 種（借的球最後再還回來，不影響計數）。' + solFin(o)];
  };

  L1_SOL.geomLines = function (p, o) {
    var n = p.n, m = p.m;
    return ['(1) 先當成任三點都不共線：任兩點決定一條直線 ' + T(cT(n, 2) + '=' + C(n, 2)) + ' 條。',
      '但那共線的 ' + m + ' 點，兩兩連出的 ' + T(cT(m, 2) + '=' + C(m, 2)) + ' 條其實是同一條，所以要扣掉再補回 1 條：' + T(C(n, 2) + '-' + C(m, 2) + '+1=' + p.ans.lines) + ' 條。',
      '(2) 任三點 ' + T(cT(n, 3) + '=' + C(n, 3)) + ' 組，其中共線的三點圍不出三角形，共 ' + T(cT(m, 3) + '=' + C(m, 3)) + ' 組，直接扣掉：' + T(C(n, 3) + '-' + C(m, 3) + '=' + p.ans.tris) + ' 個。' + solFin(o)];
  };

  L1_SOL.rectCount = function (p, o) {
    var rr = p.r, cc = p.c, terms = [], sq = 0, k;
    for (k = 1; k <= rr; k++) { sq += (rr - k + 1) * (cc - k + 1); terms.push(solMulT([rr - k + 1, cc - k + 1])); }
    var rect = p.ans.rect;
    return ['(1) 一個矩形由兩條橫線與兩條直線圍成。' + rr + ' 列的方格網有 ' + (rr + 1) + ' 條橫線、' + cc + ' 行有 ' + (cc + 1) + ' 條直線。',
      '選兩條橫線 ' + T(cT(rr + 1, 2) + '=' + C(rr + 1, 2)) + '、兩條直線 ' + T(cT(cc + 1, 2) + '=' + C(cc + 1, 2)) + '，相乘得 ' + T(String(rect)) + ' 個。',
      '(2) 正方形要依邊長分類：邊長 ' + T('k') + ' 的正方形左上角有 ' + T('(' + rr + '-k+1)(' + cc + '-k+1)') + ' 種放法，' + T(terms.join('+') + '=' + sq) + ' 個。',
      p.v === 0
        ? '所以正方形有 ' + T(String(sq)) + ' 個。' + solFin(o)
        : '題目要的是「長與寬不相等」的矩形，把正方形扣掉：' + T(rect + '-' + sq + '=' + p.ans.sq) + ' 個。' + solFin(o)];
  };

  L1_SOL.binomTerm = function (p, o) {
    var n = p.n, kk = (n - p.m) / 2, a = p.a, b = p.b;
    var aTex = (a === 1 ? '' : a) + 'x', bTex = (b < 0 ? '-' : '') + '\\dfrac{' + Math.abs(b) + '}{x}';
    return ['先寫一般項：' + T('T_{k+1}=' + cT(n, 'k') + '\\left(' + aTex + '\\right)^{' + n + '-k}\\left(' + bTex + '\\right)^{k}') + '。',
      '把 ' + T('x') + ' 的次數算出來：前面貢獻 ' + T(n + '-k') + ' 次、後面貢獻 ' + T('-k') + ' 次，合計 ' + T(n + '-2k') + '。令 ' + T(n + '-2k=' + p.m) + ' 解得 ' + T('k=' + kk) + '。',
      '代回係數：' + T(cT(n, kk) + solPow(a, n - kk) + solPow(b, kk) + '=' + p.ans) + '。' + solFin(o)];
  };

  L1_SOL.coefSum = function (p, o) {
    var n = p.n, a = p.a, b = p.b, f1 = ipow(a + b, n), fm1 = ipow(b - a, n);
    var bT = (b < 0 ? '-' : '+') + Math.abs(b);
    var add = fm1 < 0 ? '-' + Math.abs(fm1) : '+' + fm1;
    return ['(1) 想要「全部係數相加」，就把 ' + T('x=1') + ' 代進去（每一項的 ' + T('x') + ' 都變成 1）：' + T('(' + (a === 1 ? '' : a) + bT + ')^{' + n + '}=' + f1) + '。',
      '(2) 想要 ' + T('a_0') + ' 就代 ' + T('x=0') + '，其他項都被 ' + T('x') + ' 吃掉：' + T('(' + bT.replace('+', '') + ')^{' + n + '}=' + p.ans.c0) + '。',
      '(3) 再代 ' + T('x=-1') + ' 得 ' + T(String(fm1)) + '。此時奇次項變號、偶次項不變，所以 ' + T('f(1)+f(-1)') + ' 剛好把奇次項消掉、偶次項變兩倍。',
      '偶次項係數和 ' + T('\\dfrac{' + f1 + add + '}{2}=' + p.ans.even) + '。' + solFin(o)];
  };

  L1_SOL.hockey = function (p, o) {
    var k = p.k, m = p.m;
    return ['觀察這一串組合數：下標全部固定是 ' + T(String(k)) + '，上標從 ' + T(String(k)) + ' 一路連到 ' + T(String(m)) + '，共 ' + (m - k + 1) + ' 項。',
      '這正是曲棍棒恆等式的形狀 ' + T('\\sum_{n=' + k + '}^{' + m + '}' + cT('n', k) + '=' + cT(m + 1, k + 1)) + '（上標加一、下標加一）。',
      '算出來 ' + T(cT(m + 1, k + 1) + '=' + p.ans) + '。' + solFin(o)];
  };

  /* ── §4 古典機率 ── */
  L1_SOL.dice2 = function (p, o) {
    var f = solF(p.ans), cnt = f.n * 36 / f.d;
    var how = ['把和為 ' + p.s + ' 的有序對 ' + T('(a,b)') + ' 一個一個列出來數',
      '把和 ' + T('\\ge' + p.s) + ' 的各種和（' + p.s + ' 一直到 12）的個數全部加起來',
      p.w === 0 ? '用餘事件：積為奇數 ⟺ 兩顆都是奇數，有 ' + T('3\\times3=9') + ' 種，' + T('36-9=27') + ' 種' : '積為奇數 ⟺ 兩顆都是奇數，每顆 3 種',
      p.d === 0 ? '差為 ' + T('0') + ' 就是兩顆點數相同' : '差為 ' + T(String(p.d)) + ' 的有序對，大的那顆可以是 ' + (p.d + 1) + ' 到 6，再乘 2（誰大誰小）',
      '兩顆都必須是 ' + T((p.t + 1) + '\\sim6') + ' 這 ' + (6 - p.t) + ' 種，兩顆獨立',
      '把和是 ' + p.m + ' 的倍數的那幾種和的個數加起來'][p.kind];
    return ['樣本空間：兩顆骰子要看成有序對（第一顆、第二顆），' + T('n(S)=6\\times6=36') + '。',
      '再數符合事件的有序對：' + how + '，共 ' + T(String(cnt)) + ' 個。',
      '機率 ' + T(solFrac(cnt, 36)) + '。' + solFin(o)];
  };

  L1_SOL.coins = function (p, o) {
    var n = p.n, k = p.k, tot = ipow(2, n), ex = C(n, k), terms = [], i, acc = 0;
    if (p.v === 0) { for (i = k; i <= n; i++) { terms.push(cT(n, i)); acc += C(n, i); } }
    else { for (i = 0; i <= k; i++) { terms.push(cT(n, i)); acc += C(n, i); } }
    return ['樣本空間：每一次都有正、反 2 種，' + n + ' 次共 ' + T('n(S)=2^{' + n + '}=' + tot) + ' 種結果。',
      '(1) 「恰有 ' + k + ' 次正面」就是從 ' + n + ' 次之中決定「哪 ' + k + ' 次是正面」：' + T(cT(n, k) + '=' + ex) + ' 種，機率 ' + T(solFrac(ex, tot)) + '。',
      '(2) 「' + (p.v === 0 ? '至少' : '至多') + ' ' + k + ' 次正面」是把 ' + (p.v === 0 ? k + ' 到 ' + n : '0 到 ' + k) + ' 次的情形全部加起來：' + T(terms.join('+') + '=' + acc) + '，機率 ' + T(solFrac(acc, tot)) + '。' + solFin(o)];
  };

  L1_SOL.eventOps = function (p, o) {
    var a = p.a, b = p.b, ab = p.ab, aOnly = a - ab, bOnly = b - ab, nn = 10 - (a + b - ab);
    return ['先畫文氏圖，把它切成不重疊的四塊：只有 ' + T('A') + '、只有 ' + T('B') + '、兩個都有、兩個都沒有。',
      '「兩個都有」題目給了 ' + T(solDec(ab)) + '；只有 ' + T('A') + ' 是 ' + T(solDec(a) + '-' + solDec(ab) + '=' + solDec(aOnly)) + '，只有 ' + T('B') + ' 是 ' + T(solDec(b) + '-' + solDec(ab) + '=' + solDec(bOnly)) + '；四塊加起來是 1，所以都沒有是 ' + T(solDec(nn)) + '。',
      '有了四塊，每一小題都只是把需要的塊相加：' + T('P(A\\cup B)') + ' 是前三塊 ' + T(solDec(p.ans.un)) + '、' + T("P(A')") + ' 是 ' + T('1-' + solDec(a) + '=' + solDec(p.ans.na)) + '、' + T("P(A'\\cap B')") + ' 就是第四塊 ' + T(solDec(p.ans.nn)) + '、' + T("P(A\\cap B')") + ' 就是「只有 ' + T('A') + '」那塊 ' + T(solDec(p.ans.aOnly)) + '。',
      '「恰有一個發生」是「只有 ' + T('A') + '」加「只有 ' + T('B') + '」：' + T(solDec(aOnly) + '+' + solDec(bOnly) + '=' + solDec(p.ans.one)) + '。' + solFin(o)];
  };

  L1_SOL.drawBalls = function (p, o) {
    var a = p.a, b = p.b, k = p.k, tot = C(a + b, k), ca = C(a, k), cb = C(b, k);
    return ['同色球雖然顏色一樣，仍要視為不同的球（否則各種結果不等機率）。樣本空間 ' + T('n(S)=' + cT(a + b, k) + '=' + tot) + '。',
      '(1) 「' + k + ' 顆同色」分兩類：全紅 ' + T(cT(a, k) + '=' + ca) + ' 種、全白 ' + T(cT(b, k) + '=' + cb) + ' 種，相加 ' + T(ca + '+' + cb + '=' + (ca + cb)) + ' 種，機率 ' + T(Fr.tex(solF(p.ans.same))) + '。',
      '(2) 「至少一顆紅球」的反面是「全部都是白球」' + T(cT(b, k) + '=' + cb) + ' 種，用餘事件 ' + T(tot + '-' + cb + '=' + (tot - cb)) + ' 種，機率 ' + T(Fr.tex(solF(p.ans.atLeast))) + '。' + solFin(o)];
  };

  L1_SOL.lottery = function (p, o) {
    var n = p.n, k = p.k;
    return ['抽籤的公平性：把 ' + n + ' 支籤想成排成一列，' + n + ' 個人依序拿走第 1、第 2…支，每一種排法等機率。',
      '(1) 因此「第 ' + p.i + ' 位抽中」跟「第 1 位抽中」完全對稱，機率都是 ' + T(solFrac(k, n)) + '。',
      '(2) 「第 ' + p.i + ' 位與第 ' + p.j + ' 位都抽中」＝這兩個指定位置都是中獎籤：' + T('\\dfrac{' + pT(k, 2) + '}{' + pT(n, 2) + '}=\\dfrac{' + solMulT([k, k - 1]) + '}{' + solMulT([n, n - 1]) + '}=' + Fr.tex(solF(p.ans.p2))) + '。' + solFin(o)];
  };

  /* ── §5 期望值 ── */
  L1_SOL.expBasic = function (p, o) {
    var a = p.a, b = p.b, n = a + b, E = solF(p.ans);
    return ['期望值＝每一種結果的「值 × 機率」全部加起來，所以先算兩種機率。',
      '取到紅球 ' + T('\\dfrac{' + a + '}{' + n + '}') + '、取到藍球 ' + T('\\dfrac{' + b + '}{' + n + '}') + '（兩者相加是 1，檢查無誤）。',
      '期望值 ' + T(p.x + '\\cdot\\dfrac{' + a + '}{' + n + '}+' + p.y + '\\cdot\\dfrac{' + b + '}{' + n + '}=\\dfrac{' + (p.x * a) + '+' + (p.y * b) + '}{' + n + '}=' + Fr.tex(E)) + ' 元。' + solFin(o)];
  };

  L1_SOL.expShift = function (p, o) {
    var a = p.a, b = p.b, E = solF(p.ans), bT = (b < 0 ? '-' : '+') + Math.abs(b);
    return ['先算點數本身的期望值：' + (p.two ? '兩顆骰子點數和的期望值是 ' + T('3.5+3.5=7') : '一顆公正骰子的期望值是 ' + T('\\dfrac{1+2+3+4+5+6}{6}=3.5')) + '。',
      '獎金是點數的一次式，直接套期望值的線性 ' + T('E(' + a + 'k' + bT + ')=' + a + 'E(k)' + bT) + '。',
      '代入得 ' + T(a + '\\times' + (p.two ? '7' : '3.5') + bT + '=' + Fr.tex(E)) + ' 元。' + solFin(o)];
  };

  L1_SOL.fairGame = function (p, o) {
    var win = p.win, lose = 36 - win, x = solF(p.ans);
    var pw = F(win, 36), pl = F(lose, 36);
    return ['先算兩種機率：' + T('n(S)=36') + '，得獎的情形有 ' + T(String(win)) + ' 種 ⟹ ' + T('\\dfrac{' + win + '}{36}=' + Fr.tex(pw)) + '；其餘 ' + T(String(lose)) + ' 種要賠 ⟹ ' + T('\\dfrac{' + lose + '}{36}=' + Fr.tex(pl)) + '。',
      '「公平」的意思是期望值為 ' + T('0') + '：' + T(p.w + '\\cdot' + Fr.tex(pw, true) + '-x\\cdot' + Fr.tex(pl, true) + '=0') + '。',
      '解得 ' + T('x=\\dfrac{' + p.w + '\\times' + win + '}{' + lose + '}=' + Fr.tex(x)) + ' 元。' + solFin(o)];
  };

  L1_SOL.expLinear = function (p, o) {
    var a = p.a, b = p.b, n = a + b, one = F(a * p.x + b * p.y, n), E = solF(p.ans);
    return ['期望值有線性：總金額＝第 1 張金額＋第 2 張金額＋…，所以總期望值＝各張期望值相加。',
      '每一張卡（不論第幾張抽到）的期望值都等於單張的平均 ' + T('\\dfrac{' + (p.x * a) + '+' + (p.y * b) + '}{' + n + '}=' + Fr.tex(one)) + ' 元——不放回也一樣，因為每一張被抽到的機會相同。',
      '取 ' + p.k + ' 張就是 ' + T(p.k + '\\times' + Fr.tex(one) + '=' + Fr.tex(E)) + ' 元。' + solFin(o)];
  };

  L1_SOL.expMax = function (p, o) {
    var n = p.n, s = 0, terms = [], m, c;
    for (m = 1; m <= n; m++) {
      c = p.big ? m - 1 : n - m;
      if (c > 0) { s += m * c; terms.push(solMulT([m, c])); }
    }
    var tot = C(n, 2), E = solF(p.ans), word = p.big ? '較大' : '較小';
    return ['樣本空間：同時取 2 顆，' + T('n(S)=' + cT(n, 2) + '=' + tot) + '。',
      word + '號碼剛好是 ' + T('m') + ' 的取法有幾種？另一顆必須' + (p.big ? '比 ' + T('m') + ' 小' : '比 ' + T('m') + ' 大') + '，所以有 ' + T(p.big ? 'm-1' : n + '-m') + ' 種。',
      '把「號碼 × 種數」全部加起來 ' + T(terms.join('+') + '=' + s) + '，再除以 ' + tot + '：' + T(solFrac(s, tot)) + '。' + solFin(o)];
  };
  var META_L1 = [
      ['routes', '§1 加法原理 vs 乘法原理'], ['passcode', '§1 乘法原理的三種變化'], ['digitsEven', '§1 分類討論：含 0 的三位數'], ['multiples', '§1 倍數計數（取捨）'], ['venn3', '§1 三集合取捨'], ['complement', '§1 補集法：「至少」'],
      ['permBasic', '§2 排列數的基本運算'], ['bundle', '§2 捆綁法：相鄰'], ['gaps', '§2 插空法：不相鄰'], ['fixedOrder', '§2 固定順序：除法'], ['multisetPerm', '§2 不盡相異物排列'], ['gridPath', '§2 格子路徑'], ['repPerm', '§2 重複排列：球放箱'],
      ['combVsPerm', '§3 組合與排列的分辨'], ['atLeastComb', '§3 「至少」型組合'], ['groups', '§3 分組 vs 分堆'], ['bars', '§3 隔板法'], ['geomLines', '§3 幾何計數：共線修正'], ['rectCount', '§3 矩形與正方形計數'], ['binomTerm', '§3 二項式的特定項'], ['coefSum', '§3 代值法求係數和'], ['hockey', '§3 曲棍棒恆等式'],
      ['dice2', '§4 兩顆骰子'], ['coins', '§4 硬幣：恰 k 次正面'], ['eventOps', '§4 事件的運算'], ['drawBalls', '§4 取球：同色與至少'], ['lottery', '§4 抽籤的公平性'],
      ['expBasic', '§5 期望值的定義'], ['expShift', '§5 平移與伸縮'], ['fairGame', '§5 公平遊戲'], ['expLinear', '§5 期望值的線性'], ['expMax', '§5 較大號碼的期望值']
  ];
  var META_L2 = [
      ['adjNotAdj', '§2 相鄰＋不相鄰並存'], ['distributeAll', '§2 分配：每人至少一件'], ['multisetGap', '§2 不盡相異物＋不相鄰'], ['digitsMult3', '§2 3 的倍數：先選後排'], ['gridAvoid', '§2 路徑：必經與迴避'], ['lettersSelect', '§2 重複字母的選與排'],
      ['barsBound', '§3 整數解：下限與不等式'], ['groupsEqual', '§3 平分成堆與同堆'], ['binomGeneral', '§3 二項式：x² 與 1/x'], ['combIdentityVal', '§3 組合恆等式求值'], ['nonAdjSelect', '§3 不相連的選法'],
      ['probAtLeast2', '§4 機率：至少 2 個'], ['probRange', '§4 機率的可能範圍'], ['drawOrder', '§4 取完全部球的位置'], ['dice3', '§4 三顆骰子的結構'],
      ['expectPairs', '§5 號碼差的期望值'], ['fairMulti', '§5 三骰公平遊戲'], ['expectUpdated', '§5 摸彩進行到一半']
  ];
  /* ══════════════════════════════════════════════════════════
     L3　中上（15 型）：每型對應固定題 L3-1～L3-15 的「類似題」
     計數與機率一律用「可用 itertools 窮舉」的定義；小規模直接列舉、
     大規模才用公式。p 只放輸入參數與旗標，驗算器一律從題幹重算。
     ══════════════════════════════════════════════════════════ */
  var L3 = {};

  /* ── 列舉用小工具（名稱一律加 l3 前綴） ── */
  function l3range(a, b) { var o = [], i; for (i = a; i <= b; i++) o.push(i); return o; }
  function l3asc(x, y) { return x - y; }
  function l3comb(list, k, fn) {                 /* 所有遞增的 k 元子集 */
    var n = list.length, cur = [], out = 0;
    (function go(start, depth) {
      if (depth === k) { out += (fn(cur) || 0); return; }
      for (var i = start; i <= n - (k - depth); i++) { cur.push(list[i]); go(i + 1, depth + 1); cur.pop(); }
    })(0, 0);
    return out;
  }
  function l3ordered(list, k, fn) {              /* 相異元素的有序排列 */
    var n = list.length, used = [], cur = [], out = 0, i;
    for (i = 0; i < n; i++) used.push(0);
    (function go(depth) {
      if (depth === k) { out += (fn(cur) || 0); return; }
      for (var j = 0; j < n; j++) if (!used[j]) { used[j] = 1; cur.push(list[j]); go(depth + 1); cur.pop(); used[j] = 0; }
    })(0);
    return out;
  }
  function l3words(alpha, k, fn) {               /* 可重複的 k 元序列 */
    var cur = [], out = 0;
    (function go(depth) {
      if (depth === k) { out += (fn(cur) || 0); return; }
      for (var i = 0; i < alpha.length; i++) { cur.push(alpha[i]); go(depth + 1); cur.pop(); }
    })(0);
    return out;
  }
  function l3lcm(a, b) { return a * b / gcd(a, b); }
  function l3vp(x, p) { var e = 0; while (x % p === 0) { x = x / p; e++; } return e; }
  function l3set(arr) { return '\\{' + arr.join(',') + '\\}'; }
  function l3has(arr, x) { for (var i = 0; i < arr.length; i++) if (arr[i] === x) return true; return false; }
  function l3nums(arr) { var o = [], i; for (i = 0; i < arr.length; i++) o.push(T(String(arr[i]))); return o.join('、'); }

  /* ══ L3-1　三集合取捨：a、b、c 的倍數（交集是最小公倍數的倍數） ══ */
  var L3TRIP = [[4, 6, 9], [6, 8, 9], [4, 6, 15], [6, 10, 15], [4, 10, 15], [6, 9, 10], [8, 12, 18], [4, 6, 10],
                [9, 12, 15], [6, 8, 10], [4, 9, 10], [6, 14, 21], [4, 6, 21], [8, 10, 12], [9, 10, 12], [4, 14, 21]];
  L3.multiples3 = function (r) {
    var t = r.pick(L3TRIP), N = r.pick([180, 240, 252, 300, 336, 360, 420, 480, 504, 540, 600, 630, 720, 840, 900]);
    var a = t[0], b = t[1], c = t[2], v = r.int(0, 2), i, k, cnt = 0;
    for (i = 1; i <= N; i++) {
      k = (i % a === 0 ? 1 : 0) + (i % b === 0 ? 1 : 0) + (i % c === 0 ? 1 : 0);
      if ((v === 0 && k >= 1) || (v === 1 && k === 0) || (v === 2 && k === 1)) cnt++;
    }
    var lab = l3lcm(a, b), lbc = l3lcm(b, c), lac = l3lcm(a, c), labc = l3lcm(lab, c);
    var evt = v === 0 ? '是 ' + T(String(a)) + '、' + T(String(b)) + ' 或 ' + T(String(c)) + ' 的倍數'
            : v === 1 ? '不是 ' + T(String(a)) + '、' + T(String(b)) + '、' + T(String(c)) + ' 中任何一個的倍數'
            : '恰好是 ' + T(String(a)) + '、' + T(String(b)) + '、' + T(String(c)) + ' 其中一個的倍數';
    var base = '$n(A\\cup B\\cup C)=n(A)+n(B)+n(C)-n(A\\cap B)-n(B\\cap C)-n(A\\cap C)+n(A\\cap B\\cap C)$：'
      + '$\\left[\\dfrac{' + N + '}{' + a + '}\\right]=' + Math.floor(N / a) + '$、$\\left[\\dfrac{' + N + '}{' + b + '}\\right]=' + Math.floor(N / b) + '$、$\\left[\\dfrac{' + N + '}{' + c + '}\\right]=' + Math.floor(N / c) + '$；'
      + '兩兩交集分別是 $' + lab + '$、$' + lbc + '$、$' + lac + '$ 的倍數（取最小公倍數，不是相乘），三者交集是 $' + labc + '$ 的倍數。';
    var tail = v === 0 ? '' : v === 1 ? '算出聯集後用 $' + N + '-n(A\\cup B\\cup C)$。' : '「恰好一個」$=n(A\\cup B\\cup C)-($ 兩兩交集之和 $)+2\\times($ 三者交集 $)$，也可以把七塊區域從最裡面往外填。';
    return { q: '在 ' + T('1') + ' 到 ' + T(String(N)) + ' 的正整數中，' + evt + '的數共有幾個？',
             a: T(String(cnt)) + ' 個',
             h: base + tail,
             p: { N: N, a: a, b: b, c: c, v: v, ans: cnt } };
  };

  /* ══ L3-2　含奇數個某數字：依「恰幾個」分類 ══ */
  L3.oddCount = function (r) {
    var m = r.int(5, 8), k = r.int(3, 4), pool = r.shuffle(l3range(1, 9)), v;
    var digs = pool.slice(0, m).sort(l3asc), d = r.pick(digs);
    v = r.int(0, 2);
    var cnt = l3words(digs, k, function (w) {
      var c = 0, i; for (i = 0; i < w.length; i++) if (w[i] === d) c++;
      return v === 0 ? (c % 2 === 1) : (v === 1 ? (c % 2 === 0) : (c >= 2));
    });
    var evt = v === 0 ? '含有奇數個 ' + T(String(d)) + ' 的' : v === 1 ? '含有偶數個 ' + T(String(d)) + '（一個都沒有也算）的' : '至少含有兩個 ' + T(String(d)) + ' 的';
    var cls = [], j;
    for (j = 0; j <= k; j++) if ((v === 0 && j % 2 === 1) || (v === 1 && j % 2 === 0) || (v === 2 && j >= 2))
      cls.push('$' + cT(k, j) + (k - j === 0 ? '' : '\\times' + (k - j === 1 ? String(m - 1) : (m - 1) + '^{' + (k - j) + '}')) + '$');
    return { q: '由 ' + T(digs.join(',')) + ' 這 ' + T(String(m)) + ' 個數字組成（數字可以重複）的 ' + T(String(k)) + ' 位數中，' + evt + '共有幾個？',
             a: T(String(cnt)) + ' 個',
             h: '每一位都能填 ' + T(String(m)) + ' 種，全部共 $' + m + '^{' + k + '}$ 個。依「恰好幾個 ' + T(String(d)) + '」分類：恰 $j$ 個 $=' + cT(k, 'j') + '\\times' + (m - 1) + '^{' + k + '-j}$（先選哪 $j$ 個位置放 ' + T(String(d)) + '，其餘位置從另外 $' + (m - 1) + '$ 個數字任填）。本題要把 ' + cls.join('、') + ' 相加。',
             p: { digs: digs, k: k, d: d, v: v, ans: cnt } };
  };

  /* ══ L3-3　相異數字排成的數是 t 的倍數：先排個位再排首位 ══ */
  L3.distinctMult = function (r) {
    var size = r.int(6, 9), n = r.int(3, 4), pool = r.shuffle(l3range(1, 9)), t = r.pick([2, 5]);
    var digs = pool.slice(0, size - 1), i, hasEven = false;
    for (i = 0; i < digs.length; i++) if (digs[i] % 2 === 0) hasEven = true;
    if (t === 5 && !l3has(digs, 5)) digs[0] = 5;
    if (t === 2 && !hasEven) digs[0] = r.pick([2, 4, 6, 8]);
    digs.push(0); digs = digs.sort(l3asc);
    var all = l3ordered(digs, n, function (w) { return w[0] !== 0; });
    var cnt = l3ordered(digs, n, function (w) {
      if (w[0] === 0) return false;
      var val = 0, j; for (j = 0; j < w.length; j++) val = val * 10 + w[j];
      return val % t === 0;
    });
    var v = r.int(0, 1), nm = n === 3 ? '三' : '四';
    var ends = t === 5 ? (l3has(digs, 5) ? '$0$ 或 $5$' : '$0$') : '$0$ 或其他偶數';
    var h = '先排受限最多的個位，再排首位。' + (t === 5
      ? '個位只能是 ' + ends + '：個位 $=0$ 時，其餘 $' + (n - 1) + '$ 位從剩下 $' + (size - 1) + '$ 個數字不重複地排；' + (l3has(digs, 5) ? '個位 $=5$ 時，首位不能是 $0$ 也不能是 $5$，只剩 $' + (size - 2) + '$ 種，中間再從剩下的數字排。' : '')
      : '個位必須是偶數。個位 $=0$ 時，其餘 $' + (n - 1) + '$ 位從剩下 $' + (size - 1) + '$ 個數字不重複地排；個位是非零偶數時，首位要同時避開 $0$ 與這個偶數，只剩 $' + (size - 2) + '$ 種。') + '兩類相加。';
    return { q: '從 ' + T(digs.join(',')) + ' 這 ' + T(String(size)) + ' 個數字中取相異 ' + T(String(n)) + ' 個排成' + nm + '位數。'
               + (v === 0 ? '其中是 ' + T(String(t)) + ' 的倍數的共有幾個？' : '(1) 這樣的' + nm + '位數共有幾個？(2) 其中是 ' + T(String(t)) + ' 的倍數的有幾個？'),
             a: v === 0 ? T(String(cnt)) + ' 個' : '(1) ' + T(String(all)) + ' 個　(2) ' + T(String(cnt)) + ' 個',
             h: (v === 0 ? '' : '(1) 首位 $' + (size - 1) + '$ 種，其餘 $' + (n - 1) + '$ 位從剩下的 $' + (size - 1) + '$ 個數字排。(2) ') + h,
             p: { digs: digs, n: n, t: t, v: v, ans: v === 0 ? cnt : [all, cnt] } };
  };

  /* ══ L3-4　各自遞增 ⟹ 順序被定死，只剩「選」 ══ */
  L3.orderedPick = function (r) {
    var Oall = r.shuffle([1, 3, 5, 7, 9]), Eall = r.shuffle([2, 4, 6, 8]);
    var so = r.int(4, 5), se = r.int(3, 4), st = r.pick([[2, 2], [2, 3], [3, 2]]);
    var O = Oall.slice(0, so).sort(l3asc), E = Eall.slice(0, se).sort(l3asc);
    var s = st[0], t = st[1], v = r.int(0, 2), n = s + t, U = O.concat(E);
    var cnt = l3ordered(U, n, function (w) {
      var od = [], ev = [], i;
      for (i = 0; i < w.length; i++) { if (w[i] % 2 === 1) od.push(w[i]); else ev.push(w[i]); }
      if (od.length !== s || ev.length !== t) return false;
      for (i = 1; i < od.length; i++) if (od[i] < od[i - 1]) return false;
      if (v === 0) { for (i = 1; i < ev.length; i++) if (ev[i] < ev[i - 1]) return false; }
      if (v === 1) { for (i = 1; i < ev.length; i++) if (ev[i] > ev[i - 1]) return false; }
      return true;
    });
    var nm = ['三', '四', '五', '六'][n - 3];
    var rule = v === 0 ? '奇數與偶數由左而右均依小而大排列'
             : v === 1 ? '奇數由左而右依小而大排列、偶數由左而右依大而小排列'
             : '奇數由左而右依小而大排列（偶數的順序不限）';
    var hh = '順序被規定死了就只剩「選」：選奇數 $' + cT(so, s) + '$、選偶數 $' + cT(se, t) + '$、再選哪 $' + t + '$ 個位置放偶數 $' + cT(n, t) + '$。'
      + (v === 2 ? '位置決定後奇數只有一種擺法，偶數的順序沒有限制，還要再乘 $' + t + '!$ 種。'
         : v === 1 ? '位置決定後，奇數「由小到大」、偶數「由大到小」各自都只有一種擺法（由大而小與由小而大的種數一樣多），不必再乘排列。'
         : '位置決定後，奇數與偶數各自只有一種擺法，不必再乘排列。');
    return { q: '從 ' + T(O.join(',')) + ' 中任取 ' + T(String(s)) + ' 個數字，從 ' + T(E.join(',')) + ' 中任取 ' + T(String(t)) + ' 個數字，排成一個數字不重複的' + nm + '位數。若' + rule + '，則共有多少個' + nm + '位數？',
             a: T(String(cnt)) + ' 個',
             h: hh,
             p: { O: O, E: E, s: s, t: t, v: v, ans: cnt } };
  };

  /* ══ L3-5　座位不相鄰＋禁用座位 ══ */
  L3.seatBlock = function (r) {
    var n = r.int(10, 15), k = r.int(3, 4), b1 = r.int(3, n - 2), v = r.int(0, 1), b2 = 0, tries = 0;
    if (v === 1) {
      do { b2 = r.int(2, n - 1); } while (Math.abs(b2 - b1) < 3 && tries++ < 60);
      if (Math.abs(b2 - b1) < 3) { v = 0; b2 = 0; }
    }
    var banned = (v === 1 ? [b1, b2] : [b1]).sort(l3asc);
    var cnt = l3comb(l3range(1, n), k, function (s) {
      var i;
      for (i = 0; i < s.length; i++) { if (l3has(banned, s[i])) return false; if (i > 0 && s[i] - s[i - 1] === 1) return false; }
      return true;
    });
    var ans = cnt * fact(k), free = C(n - k + 1, k), nm = k === 3 ? '三' : '四';
    return { q: '一排座椅有 ' + T(String(n)) + ' 個座位，由左至右編號 ' + T('1\\sim' + n) + '。' + NAMES.slice(0, k).join('、') + ' ' + T(String(k)) + ' 人各選一個座位入座，' + nm + '人的座位彼此不相鄰；又編號 ' + l3nums(banned) + ' 的座位無人入座。共有幾種入座方法？',
             a: T(String(ans)) + ' 種',
             h: '先數「座位組合」再乘 $' + k + '!$ 把人排上去。$' + n + '$ 個座位選 $' + k + '$ 個兩兩不相鄰共 $' + cT(n - k + 1, k) + '=' + free + '$ 組（沒被選的 $' + (n - k) + '$ 個座位造出 $' + (n - k + 1) + '$ 個空隙）。'
               + (banned.length > 1
                  ? '再用取捨扣掉用到禁用座位的組合：含 $' + banned[0] + '$ 號的、含 $' + banned[1] + '$ 號的各數一次，兩個都含的再加回來——含某個編號時，它左右相鄰的座位也都不能選，在剩下的座位中重新數一次不相鄰的選法。'
                  : '再扣掉用到 $' + banned[0] + '$ 號的組合——含 $' + banned[0] + '$ 號時，它左右相鄰的座位也都不能選，在剩下的座位中重新數一次不相鄰的選法。')
               + '最後答案 $=($ 合格組合數 $)\\times' + k + '!$。',
             p: { n: n, k: k, banned: banned, ans: ans } };
  };

  /* ══ L3-6　取 k 個數，乘積為 M 的倍數：依含幾個因數 p 分堆 ══ */
  L3.prodMultiple = function (r) {
    var N = r.int(9, 14), k = r.int(3, 4), M = r.pick([4, 8, 9, 12, 6, 16]), v, cnt, tot, tries = 0;
    var list = l3range(1, N);
    do {
      cnt = l3comb(list, k, function (s) {
        var pd = 1, i; for (i = 0; i < s.length; i++) pd *= s[i];
        return pd % M === 0;
      });
      tot = C(N, k);
      if (cnt > 0 && cnt < tot) break;
      M = r.pick([4, 8, 9, 12, 6]); N = r.int(9, 14); list = l3range(1, N);
    } while (tries++ < 20);
    v = r.int(0, 2);
    var e2 = l3vp(M, 2), e3 = l3vp(M, 3), parts = [], pr2 = [];
    if (e2 > 0) pr2.push([2, e2]);
    if (e3 > 0) pr2.push([3, e3]);
    var i, j, p2;
    for (i = 0; i < pr2.length; i++) {
      var p = pr2[i][0], mx = 0, seg = [];
      for (j = 1; j <= N; j++) if (l3vp(j, p) > mx) mx = l3vp(j, p);
      for (p2 = mx; p2 >= 1; p2--) {
        var grp = [];
        for (j = 1; j <= N; j++) if (l3vp(j, p) === p2) grp.push(j);
        if (grp.length) seg.push('含 $' + p2 + '$ 個的是 $' + l3set(grp) + '$');
      }
      var zero = [];
      for (j = 1; j <= N; j++) if (l3vp(j, p) === 0) zero.push(j);
      parts.push('依「含幾個因數 $' + p + '$」分堆：' + seg.join('、') + '，其餘 $' + zero.length + '$ 個都不含；取出的 $' + k + '$ 個數所含因數 $' + p + '$ 的個數合計要 $\\ge' + pr2[i][1] + '$。');
    }
    var evt = v === 0 ? '乘積是 ' + T(String(M)) + ' 的倍數的取法有幾種' : v === 1 ? '乘積不是 ' + T(String(M)) + ' 的倍數的取法有幾種' : '乘積是 ' + T(String(M)) + ' 的倍數的機率是多少（化為最簡分數）';
    var ansv = v === 0 ? T(String(cnt)) + ' 種' : v === 1 ? T(String(tot - cnt)) + ' 種' : T(pr(cnt, tot));
    return { q: '從 ' + T('1,2,3,\\dots,' + N) + ' 這 ' + T(String(N)) + ' 個數中任取 ' + T(String(k)) + ' 個數（每種取法的機會相等），則' + evt + '？',
             a: ansv,
             h: '全部取法 $' + cT(N, k) + '=' + tot + '$。' + parts.join('') + (pr2.length === 1 ? '數反面（合計不足）常常比正面快。' : '兩個質因數要同時滿足，直接依「誰提供因數 $2$、誰提供因數 $3$」分類討論。'),
             p: { N: N, k: k, M: M, v: v, ans: v === 0 ? cnt : (v === 1 ? tot - cnt : fr2(F(cnt, tot))) } };
  };

  /* ══ L3-7　一人得 a 個、另兩人各得 b 個 ══ */
  var L3GIVE = [[5, 1, 2], [7, 3, 2], [8, 4, 2], [9, 5, 2], [7, 1, 3], [8, 2, 3], [9, 1, 4]];
  var L3ITEM = [['本', '不同的書'], ['個', '不同的玩具'], ['張', '不同的卡片'], ['份', '不同的獎品'], ['個', '不同的紀念品'], ['支', '不同的原子筆']];
  L3.shareItems = function (r) {
    var g = r.pick(L3GIVE), it = r.pick(L3ITEM), v = r.int(0, 2), n = g[0], a = g[1], b = g[2];
    var labeled = l3words([0, 1, 2], n, function (w) {
      var c = [0, 0, 0], i; for (i = 0; i < n; i++) c[w[i]]++;
      var d = c.slice().sort(l3asc), tgt = [a, b, b].sort(l3asc);
      return d[0] === tgt[0] && d[1] === tgt[1] && d[2] === tgt[2];
    });
    var fixed = l3words([0, 1, 2], n, function (w) {
      var c = [0, 0, 0], i; for (i = 0; i < n; i++) c[w[i]]++;
      return c[0] === a && c[1] === b && c[2] === b;
    });
    var piles = labeled / 6;
    var ask = v === 0 ? '其中一人得 ' + T(String(a)) + ' ' + it[0] + '、另兩人各得 ' + T(String(b)) + ' ' + it[0] + '，則共有多少種分法？'
            : v === 1 ? '甲得 ' + T(String(a)) + ' ' + it[0] + '、乙與丙各得 ' + T(String(b)) + ' ' + it[0] + '，則共有多少種分法？'
            : '';
    var qq = v === 2
      ? '有 ' + T(String(n)) + ' ' + it[0] + it[1] + '，要分成三堆：一堆 ' + T(String(a)) + ' ' + it[0] + '、另兩堆各 ' + T(String(b)) + ' ' + it[0] + '（堆與堆之間不分先後），則共有多少種分法？'
      : '有 ' + T(String(n)) + ' ' + it[0] + it[1] + '分給甲、乙、丙 ' + T('3') + ' 人，' + ask;
    var ansn = v === 0 ? labeled : v === 1 ? fixed : piles;
    var hh = v === 0 ? '「誰拿 $' + a + '$ ' + it[0] + '」還沒定 ⟹ 先選人 $' + cT(3, 1) + '$，人有名字所以之後不必再除：$' + cT(3, 1) + '\\times' + cT(n, a) + '\\times' + cT(n - a, b) + '\\times' + cT(b, b) + '$。'
           : v === 1 ? '人已指定，直接連續組合：$' + cT(n, a) + '\\times' + cT(n - a, b) + '\\times' + cT(b, b) + '$，不必乘也不必除。'
           : '堆沒有名字：先當成有名字算 $' + cT(n, a) + '\\times' + cT(n - a, b) + '\\times' + cT(b, b) + '=' + fixed + '$，兩個 $' + b + '$ ' + it[0] + '的堆彼此沒有區別，要再除以 $2!$。';
    var chk = v === 2 ? '驗算：這 $' + piles + '$ 種分堆法各自貼上甲乙丙的名字（$\\times3!$）得 $' + labeled + '$，正好是「分給三人」的答案。' : (v === 0 ? '驗算：先分堆 $\\dfrac{' + cT(n, a) + cT(n - a, b) + cT(b, b) + '}{2!}=' + piles + '$ 再貼名字 $\\times3!$，結果相同。' : '');
    return { q: qq, a: T(String(ansn)) + ' 種', h: hh + chk,
             p: { n: n, a: a, b: b, v: v, ans: ansn } };
  };

  /* ══ L3-8　Σ(j−c)C(n,j)：拆成 ΣjC 與 ΣC ══ */
  L3.sumCoefC = function (r) {
    var n = r.int(8, 12), c = r.int(0, 2), m = c + r.int(1, 2), v = r.int(0, 1), j;
    var S = 0; for (j = m; j <= n; j++) S += (j - c) * C(n, j);
    var S1 = n * ipow(2, n - 1), S2 = ipow(2, n), cut1 = 0, cut2 = 0;
    for (j = 0; j < m; j++) { cut1 += j * C(n, j); cut2 += C(n, j); }
    var tms = [];
    for (j = m; j <= m + 2; j++) tms.push((j - c) + '\\cdot ' + cT(n, j));
    var expr = v === 0 ? tms.join('+') + '+\\cdots+' + (n - c) + '\\cdot ' + cT(n, n)
                       : '\\displaystyle\\sum_{j=' + m + '}^{' + n + '}' + (c === 0 ? 'j' : '(j-' + c + ')') + cT(n, 'j');
    var hh = '把下標統一寫成 $j$：原式 $=\\displaystyle\\sum_{j=' + m + '}^{' + n + '}' + (c === 0 ? 'j' : '(j-' + c + ')') + cT(n, 'j')
      + (c === 0 ? '' : '=\\sum_{j=' + m + '}^{' + n + '}j' + cT(n, 'j') + '-' + (c === 1 ? '' : c) + '\\sum_{j=' + m + '}^{' + n + '}' + cT(n, 'j')) + '$。'
      + '用 $j' + cT(n, 'j') + '=' + n + cT(n - 1, 'j-1') + '$ 得 $\\displaystyle\\sum_{j=0}^{' + n + '}j' + cT(n, 'j') + '=' + n + '\\cdot2^{' + (n - 1) + '}=' + S1 + '$，扣掉 $j\\lt ' + m + '$ 的 $' + cut1 + '$ 得 $' + (S1 - cut1) + '$。'
      + (c === 0 ? '本題的係數就是 $j$ 本身，到這裡就結束了。'
         : '再用 $\\displaystyle\\sum_{j=0}^{' + n + '}' + cT(n, 'j') + '=2^{' + n + '}=' + S2 + '$，扣掉 $j\\lt ' + m + '$ 的 $' + cut2 + '$ 得 $' + (S2 - cut2) + '$。最後相減：$' + (S1 - cut1) + (c === 1 ? '-' : '-' + c + '\\times') + (S2 - cut2) + '$。');
    return { q: '求 ' + T(expr) + ' 的值。', a: T(String(S)), h: hh,
             p: { n: n, c: c, m: m, v: v, ans: S } };
  };

  /* ══ L3-9　各位數字互異且某位最小／最大 ══ */
  L3.digitExtreme = function (r) {
    var n = r.int(3, 4), kind = r.int(0, 3), pos = r.int(1, n), ask = r.int(0, 1);
    var NAM = n === 3 ? ['百', '十', '個'] : ['千', '百', '十', '個'];
    var lo = ipow(10, n - 1), hi = ipow(10, n) - 1, tot = hi - lo + 1, cnt = 0, x, i, dg, ok;
    for (x = lo; x <= hi; x++) {
      dg = []; var y = x;
      for (i = 0; i < n; i++) { dg.unshift(y % 10); y = Math.floor(y / 10); }
      ok = true;
      for (i = 0; i < n && ok; i++) for (var j = i + 1; j < n; j++) if (dg[i] === dg[j]) { ok = false; break; }
      if (!ok) continue;
      if (kind === 0) { for (i = 0; i < n; i++) if (dg[i] < dg[pos - 1]) ok = false; }
      else if (kind === 1) { for (i = 0; i < n; i++) if (dg[i] > dg[pos - 1]) ok = false; }
      else if (kind === 2) { for (i = 1; i < n; i++) if (dg[i] <= dg[i - 1]) ok = false; }
      else { for (i = 1; i < n; i++) if (dg[i] >= dg[i - 1]) ok = false; }
      if (ok) cnt++;
    }
    var nm = n === 3 ? '三' : '四', dstr = NAM.join('位、') + '位數字互異';
    var evt = kind === 0 ? dstr + '，且' + NAM[pos - 1] + '位數字最小'
            : kind === 1 ? dstr + '，且' + NAM[pos - 1] + '位數字最大'
            : kind === 2 ? '各位數字由左而右依次變大' : '各位數字由左而右依次變小';
    var hh = ask === 0 ? '$n(S)=' + tot + '$。' : '所有' + (n === 3 ? '三' : '四') + '位正整數共 $' + tot + '$ 個。';
    if (kind === 0) hh += pos === 1
      ? '合格 ⟺ 取 $' + n + '$ 個相異數字，最小的必須放首位——但首位不能是 $0$，所以含 $0$ 的選法全部不合格：只能從 $1\\sim9$ 取，$' + cT(9, n) + '\\times' + (n - 1) + '!$。'
      : '合格 ⟺ 從 $0\\sim9$ 取 $' + n + '$ 個相異數字，最小的一定放' + NAM[pos - 1] + '位，其餘 $' + (n - 1) + '$ 個任排 $' + (n - 1) + '!$ 種：$' + cT(10, n) + '\\times' + (n - 1) + '!$。若 $0$ 被選到，它必是最小的、必在' + NAM[pos - 1] + '位，首位自動不會是 $0$，所以不必再扣。';
    else if (kind === 1) hh += pos === 1
      ? '合格 ⟺ 取 $' + n + '$ 個相異數字，最大的放首位（最大的一定不是 $0$，首位自動合法），其餘 $' + (n - 1) + '$ 個任排：$' + cT(10, n) + '\\times' + (n - 1) + '!$。'
      : '先不管首位：取 $' + n + '$ 個相異數字，最大的放' + NAM[pos - 1] + '位，其餘任排 $' + cT(10, n) + '\\times' + (n - 1) + '!$；再扣掉首位是 $0$ 的——$0$ 入選（另外 $' + (n - 1) + '$ 個從 $1\\sim9$ 取 $' + cT(9, n - 1) + '$）、最大的在' + NAM[pos - 1] + '位、$0$ 在首位，剩 $' + (n - 2) + '$ 個任排 $' + (n - 2) + '!$。';
    else if (kind === 2) hh += '由左而右嚴格變大 ⟹ 選好數字後排法唯一。$0$ 若被選到會是最小的、只能排最前面，但首位不能是 $0$，所以只能從 $1\\sim9$ 取 $' + n + '$ 個：$' + cT(9, n) + '$。';
    else hh += '由左而右嚴格變小 ⟹ 選好數字後排法唯一，而且 $0$ 若被選到一定落在最後一位，首位不會是 $0$：直接 $' + cT(10, n) + '$。';
    hh += ask === 0 ? '數出合格的個數後再除以 $' + tot + '$ 並約成最簡分數。' : '本題只問個數，算完就是答案，不必再除以 $' + tot + '$。';
    var pf = F(cnt, tot);
    return { q: ask === 0
               ? '從所有' + nm + '位正整數中隨機選取一個數，每個數被取出的機會相等。設 ' + T('p') + ' 為取出的數其' + evt + '的機率，求 ' + T('p') + '（化為最簡分數）。'
               : '在所有' + nm + '位正整數中，' + evt + '的數共有幾個？',
             a: ask === 0 ? T('p=' + Fr.tex(pf)) : T(String(cnt)) + ' 個',
             h: hh, p: { n: n, kind: kind, pos: pos, ask: ask, ans: ask === 0 ? fr2(pf) : cnt } };
  };

  /* ══ L3-10　編號都不相連的機率 ══ */
  var L3ROSTER = [['位學生', '座號', '隨機派 ', ' 人打掃', '人'], ['位社員', '編號', '隨機抽出 ', ' 人擔任幹部', '人'], ['本書', '編號', '隨機取出 ', ' 本', '本書']];
  L3.nonAdjProb = function (r) {
    var n = r.int(9, 14), k = r.int(3, 4), ctx = r.pick(L3ROSTER), v = r.int(0, 2);
    var cnt = l3comb(l3range(1, n), k, function (s) {
      var adj = 0, i;
      for (i = 1; i < s.length; i++) if (s[i] - s[i - 1] === 1) adj++;
      return v === 0 ? adj === 0 : (v === 1 ? adj >= 1 : adj === 1);
    });
    var tot = C(n, k), pf = F(cnt, tot), apart = C(n - k + 1, k);
    var evt = v === 0 ? '的' + ctx[1] + '都不相連' : v === 1 ? '中至少有兩' + ctx[4] + '的' + ctx[1] + '相連' : '中恰有兩' + ctx[4] + '的' + ctx[1] + '相連（其餘的' + ctx[1] + '不與它們相連）';
    var hh = '$n(S)=' + cT(n, k) + '=' + tot + '$。都不相連 $=' + cT(n - k + 1, k) + '=' + apart + '$（沒被選的 $' + (n - k) + '$ 個排好造出 $' + (n - k + 1) + '$ 個空隙，選 $' + k + '$ 個空隙放被選的）。'
      + (v === 1 ? '「至少有兩個相連」用補集：$' + tot + '-' + apart + '$。' : v === 2 ? '「恰有一對相連」：先把相連的一對綁成一個單位，再要求這個單位與其餘 $' + (k - 2) + '$ 個彼此不相連——等於在 $' + n + '$ 個位置中排一個「寬 $2$ 的塊」與 $' + (k - 2) + '$ 個「寬 $1$ 的塊」且兩兩不相鄰。' : '');
    return { q: '有 ' + T(String(n)) + ' ' + ctx[0] + '，' + ctx[1] + '為 ' + T('1\\sim' + n) + ' 號。若' + ctx[2] + T(String(k)) + ctx[3] + '，則這 ' + T(String(k)) + ' ' + ctx[4] + evt + '的機率為多少？（化為最簡分數）',
             a: T(Fr.tex(pf)), h: hh, p: { n: n, k: k, v: v, ans: fr2(pf) } };
  };

  /* ══ L3-11　至少兩人「同一組」：反面是全部不同 ══ */
  L3.sameGroup = function (r) {
    var m = r.int(5, 9), k = r.int(3, 4), ctxi = r.int(0, 2), v = r.int(0, 2);
    if (k > m) k = 3;
    var cnt = l3words(l3range(1, m), k, function (w) {
      var c = {}, i, mx = 0, pairs = 0;
      for (i = 0; i < w.length; i++) { c[w[i]] = (c[w[i]] || 0) + 1; }
      for (i in c) { if (c[i] > mx) mx = c[i]; if (c[i] === 2) pairs++; }
      return v === 0 ? mx >= 2 : (v === 1 ? mx === 1 : (mx === 2 && pairs === 1));
    });
    var tot = ipow(m, k), pf = F(cnt, tot);
    var ctx = [
      [T(String(k)) + ' 位同學都選了第一類組，明年高二將有 ' + T(String(m)) + ' 個第一類組班。在每人被編入每個班的機會都一樣的情況下', '同班'],
      [T(String(k)) + ' 位乘客在一樓一起進入電梯，電梯之後會停 ' + T('2') + ' 樓到 ' + T(String(m + 1)) + ' 樓共 ' + T(String(m)) + ' 層。在每人於各樓層走出電梯的機會都一樣的情況下', '在同一層樓走出電梯'],
      [T(String(k)) + ' 位同學各自從 ' + T('1\\sim' + m) + ' 這 ' + T(String(m)) + ' 個號碼中挑一個（號碼可以重複）。在每人挑到每個號碼的機會都一樣的情況下', '挑到相同號碼']
    ][ctxi];
    var evt = v === 0 ? '這 ' + T(String(k)) + ' 人中至少有兩人' + ctx[1] : v === 1 ? '這 ' + T(String(k)) + ' 人' + (ctxi === 0 ? '兩兩不同班' : ctxi === 1 ? '走出電梯的樓層兩兩不同' : '挑到的號碼兩兩不同') : '這 ' + T(String(k)) + ' 人中恰有兩人' + ctx[1] + '（其餘的人彼此不同也與這兩人不同）';
    var hh = '$n(S)=' + m + '^{' + k + '}=' + tot + '$（每個人各自挑，是「人選組」不是「組選人」）。'
      + '全部不同 $=' + pT(m, k) + '=' + P(m, k) + '$。'
      + (v === 0 ? '「至少兩人相同」用補集：$1-\\dfrac{' + P(m, k) + '}{' + tot + '}$。' : v === 1 ? '直接 $\\dfrac{' + P(m, k) + '}{' + tot + '}$。' : '「恰有一對相同」：選哪兩人 $' + cT(k, 2) + '$、他們共用的那一個 $' + m + '$ 種，其餘 $' + (k - 2) + '$ 人從剩下 $' + (m - 1) + '$ 個中兩兩不同地選 $' + pT(m - 1, k - 2) + '$。');
    return { q: ctx[0] + '，求「' + evt + '」的機率。（化為最簡分數）',
             a: T(Fr.tex(pf)), h: hh, p: { m: m, k: k, ctx: ctxi, v: v, ans: fr2(pf) } };
  };

  /* ══ L3-12　某色先取完：只看最後一顆 ══ */
  var L3BAG = [['袋中', '顆紅球', '顆白球', '紅球', '白球', '每次取一球、取後不放回，直到取完為止'],
               ['盒中', '枚黑棋', '枚白棋', '黑棋', '白棋', '每次取一枚、取後不放回，直到取完為止'],
               ['箱中', '張紅卡', '張藍卡', '紅卡', '藍卡', '每次抽一張、抽後不放回，直到抽完為止']];
  L3.drawUntilEmpty = function (r) {
    var a = r.int(3, 7), b = r.int(2, 6), ctx = r.pick(L3BAG), v = r.int(0, 2), tries = 0;
    while (a === b && tries++ < 20) b = r.int(2, 6);
    if (a === b) b = a + 1;
    var n = a + b, kpos = r.int(b + 1, n - 1);
    var tot = C(n, b);
    var cnt = l3comb(l3range(1, n), b, function (s) {       /* s = 白（第二色）所在位置 */
      var last = s[s.length - 1];
      return v === 0 ? last !== n : (v === 1 ? last === n : last === kpos);
    });
    var pf = F(cnt, tot);
    var evt = v === 0 ? ctx[4] + '先取完' : v === 1 ? ctx[3] + '先取完' : '第 ' + T(String(kpos)) + ' 次取出的恰好是最後一' + ctx[2].charAt(0) + ctx[4];
    var hh = '把整個過程看成「' + n + ' 個位置中哪 ' + b + ' 個放' + ctx[4] + '」：$n(S)=' + cT(n, b) + '=' + tot + '$（每種排列等可能）。'
      + (v === 0 ? ctx[4] + '先取完 ⟺ 最後一' + ctx[1].charAt(0) + '是' + ctx[3] + '：$\\dfrac{' + cT(n - 1, b) + '}{' + cT(n, b) + '}=\\dfrac{' + a + '}{' + n + '}$，其實就是' + ctx[3] + '所佔的比例。'
         : v === 1 ? ctx[3] + '先取完 ⟺ 最後一' + ctx[1].charAt(0) + '是' + ctx[4] + '：$\\dfrac{' + cT(n - 1, b - 1) + '}{' + cT(n, b) + '}=\\dfrac{' + b + '}{' + n + '}$。'
         : '最後一' + ctx[2].charAt(0) + ctx[4] + '在第 $' + kpos + '$ 個位置 ⟺ 另外 $' + (b - 1) + '$ ' + ctx[2].charAt(0) + ctx[4] + '全在前 $' + (kpos - 1) + '$ 個位置：$\\dfrac{' + cT(kpos - 1, b - 1) + '}{' + cT(n, b) + '}$。');
    return { q: ctx[0] + '有 ' + T(String(a)) + ' ' + ctx[1] + '、' + T(String(b)) + ' ' + ctx[2] + '，' + ctx[5] + '（每' + ctx[1].charAt(0) + '被取到的機會相等）。求' + evt + '的機率。（化為最簡分數）',
             a: T(Fr.tex(pf)), h: hh, p: { a: a, b: b, v: v, kpos: kpos, ctx: L3BAG.indexOf(ctx), ans: fr2(pf) } };
  };

  /* ══ L3-13　兩顆黑球之間的白球數：只看兩顆黑球的位置 ══ */
  L3.gapPrize = function (r) {
    var w = r.int(3, 8), c = r.pick([4, 5, 6, 8, 10, 12, 15, 20]), d = r.pick([5, 10, 20, 25, 30]), v = r.int(0, 2);
    var n = w + 2, tot = C(n, 2), sumK = 0, i, j;
    for (i = 1; i <= n; i++) for (j = i + 1; j <= n; j++) sumK += (j - i - 1);
    var E = v === 0 ? F(c * sumK, tot) : v === 1 ? F(c * sumK + d * tot, tot) : F(sumK, tot);
    var dist = [], cntK;
    for (i = 0; i <= w; i++) { cntK = w + 1 - i; dist.push('$k=' + i + '$ 有 $' + cntK + '$ 種'); }
    var rule = v === 0 ? '可得獎金 ' + T(c + 'k') + ' 元' : v === 1 ? '可得獎金 ' + T(c + 'k+' + d) + ' 元' : '';
    var qq = '將 ' + T('2') + ' 顆相同的黑球和 ' + T(String(w)) + ' 顆相同的白球隨機排成一列（每種排法的機會相等）。若 ' + T('2') + ' 顆黑球之間恰有 ' + T('k') + ' 顆白球'
      + (v === 2 ? '，求 ' + T('k') + ' 的期望值。（化為最簡分數）' : '，' + rule + '，求獎金的期望值。（化為最簡分數）');
    var hh = '樣本空間就是「兩顆黑球佔哪兩個位置」：$' + cT(n, 2) + '=' + tot + '$ 種等可能。位置差為 $k+1$ 的有 $' + w + '+1-k$ 種——' + dist.join('、') + '，合計 $' + tot + '$ 種。'
      + '先算 $k$ 的期望值 $\\dfrac{' + sumK + '}{' + tot + '}=' + Fr.tex(F(sumK, tot)) + '$'
      + (v === 0 ? '，再乘 $' + c + '$。' : v === 1 ? '，再乘 $' + c + '$ 後加上固定的 $' + d + '$（平移不影響權重）。' : '。');
    return { q: qq, a: T(Fr.tex(E)) + (v === 2 ? ' 顆' : ' 元'), h: hh,
             p: { w: w, c: c, d: d, v: v, ans: fr2(E) } };
  };

  /* ══ L3-14　公平遊戲反求賠額：期望值 = 0 ══ */
  L3.fairPenalty = function (r) {
    var ctx = r.int(0, 1), aa = r.pick([4, 5, 6, 8, 10, 12, 15, 20]), bb = r.pick([0, 0, 5, 10]);
    var n = ctx === 0 ? r.int(3, 5) : r.int(3, 4);
    var alpha = ctx === 0 ? [0, 1] : l3range(1, 6), hitv = ctx === 0 ? 1 : 6;
    var cntArr = [], i;
    for (i = 0; i <= n; i++) cntArr.push(0);
    l3words(alpha, n, function (w) {
      var c = 0, j; for (j = 0; j < w.length; j++) if (w[j] === hitv) c++;
      cntArr[c]++; return 0;
    });
    var tot = ipow(alpha.length, n), win = 0, lst = [];
    for (i = 1; i <= n; i++) { win += (aa * i + bb) * cntArr[i]; lst.push('恰 $' + i + '$ 個有 $' + cntArr[i] + '$ 種'); }
    var x = F(win, cntArr[0]);
    var thing = ctx === 0 ? '枚均勻硬幣' : '顆公正骰子', face = ctx === 0 ? '正面' : T('6') + ' 點';
    var prizes = [];
    for (i = 1; i <= n; i++) prizes.push((i === 1 ? '出現 ' : '') + T(String(i)) + ' 個' + face + '得 ' + T(String(aa * i + bb)) + ' 元');
    var lhs = [];
    for (i = 1; i <= n; i++) lhs.push((aa * i + bb) + '\\times' + cntArr[i]);
    return { q: '玩家同時' + (ctx === 0 ? '丟 ' : '擲 ') + T(String(n)) + ' ' + thing + '，' + prizes.join('、') + '；若一個' + face + '都沒有出現，玩家須付給莊家 ' + T('x') + ' 元。若此遊戲對莊家與玩家公平，求 ' + T('x') + '。',
             a: T('x=' + Fr.tex(x)) + ' 元',
             h: '$n(S)=' + alpha.length + '^{' + n + '}=' + tot + '$，' + lst.join('、') + '、一個都沒有的有 $' + cntArr[0] + '$ 種。公平 ⟺ 期望值為 $0$（獎金與賠額的加權和相等）：$' + lhs.join('+') + '=x\\times' + cntArr[0] + '$，所以 $x=' + (cntArr[0] === 1 ? String(win) : '\\dfrac{' + win + '}{' + cntArr[0] + '}=' + Fr.tex(x)) + '$。',
             p: { ctx: ctx, n: n, a: aa, b: bb, ans: fr2(x) } };
  };

  /* ══ L3-15　取 k 個中特定品項個數的期望值 ══ */
  var L3PLATE = [['盤中', '顆雞蛋', '顆土雞蛋', '顆普通雞蛋', '土雞蛋'],
                 ['袋中', '顆球', '顆紅球', '顆白球', '紅球'],
                 ['盒中', '張卡片', '張特獎卡', '張普通卡', '特獎卡'],
                 ['箱中', '顆水果', '顆進口水果', '顆國產水果', '進口水果']];
  L3.drawExpect = function (r) {
    var N = r.int(8, 15), m = r.int(2, 5), k = r.int(2, 4), ctx = r.pick(L3PLATE), v = r.int(0, 2);
    if (k > N - m) k = 2;
    var tot = C(N, k), sum = 0, one = 0;
    l3comb(l3range(1, N), k, function (s) {                 /* 1..m 視為特定品項 */
      var c = 0, i; for (i = 0; i < s.length; i++) if (s[i] <= m) c++;
      sum += c; if (c === 1) one++; return 0;
    });
    var E = F(sum, tot), p1 = F(one, tot), cc = r.pick([20, 25, 30, 50, 100]);
    var head = ctx[0] + '有 ' + T(String(N)) + ' ' + ctx[1] + '：' + T(String(m)) + ' ' + ctx[2] + '、' + T(String(N - m)) + ' ' + ctx[3] + '。從' + ctx[0].charAt(0) + '中任取 ' + T(String(k)) + ' ' + ctx[1] + '（每種取法的機會相等），';
    var hh = '$n(S)=' + cT(N, k) + '=' + tot + '$。老實列表：恰取到 $i$ ' + ctx[2].charAt(0) + ctx[4] + '的取法有 $' + cT(m, 'i') + cT(N - m, k + '-i') + '$ 種，把 $i\\times($ 取法數 $)$ 相加再除以 $' + tot + '$。'
      + '也可以把「' + ctx[4] + '的個數」拆成每一' + ctx[1].charAt(0) + '各算一次：任取的每一' + ctx[1].charAt(0) + '是' + ctx[4] + '的機會都是 $\\dfrac{' + m + '}{' + N + '}$（抽籤公平性，不放回也一樣），乘上 $' + k + '$ 就是期望值 $' + k + '\\times\\dfrac{' + m + '}{' + N + '}$。';
    if (v === 0) return { q: head + '求取出的' + ctx[4] + '個數的期望值。（化為最簡分數）', a: T(Fr.tex(E)) + ' ' + ctx[1].charAt(0), h: hh, p: { N: N, m: m, k: k, v: v, ans: fr2(E) } };
    if (v === 1) { var Ec = Fr.mul(E, F(cc)); return { q: head + '若每取到一' + ctx[1].charAt(0) + ctx[4] + '可得 ' + T(String(cc)) + ' 元，求所得金額的期望值。（化為最簡分數）', a: T(Fr.tex(Ec)) + ' 元', h: hh + '最後再乘上 $' + cc + '$。', p: { N: N, m: m, k: k, v: v, c: cc, ans: fr2(Ec) } }; }
    return { q: head + '求 (1) 恰取到 ' + T('1') + ' ' + ctx[1].charAt(0) + ctx[4] + '的機率　(2) 取出的' + ctx[4] + '個數的期望值。（都化為最簡分數）',
             a: '(1) ' + T(Fr.tex(p1)) + '　(2) ' + T(Fr.tex(E)) + ' ' + ctx[1].charAt(0),
             h: '(1) $\\dfrac{' + cT(m, 1) + cT(N - m, k - 1) + '}{' + cT(N, k) + '}$。(2) ' + hh,
             p: { N: N, m: m, k: k, v: v, ans: [fr2(p1), fr2(E)] } };
  };

  var META_L3 = [['multiples3', '三集合取捨：三個數的倍數'], ['oddCount', '含奇數個某數字的 k 位數'], ['distinctMult', '相異數字排成的倍數'], ['orderedPick', '各自遞增：只剩「選」'], ['seatBlock', '座位不相鄰＋禁用座位'], ['prodMultiple', '乘積為 M 的倍數'], ['shareItems', '一人 a 個另兩人各 b 個'], ['sumCoefC', 'Σ(j−c)C(n,j) 求值'], ['digitExtreme', '各位互異且某位最小／最大'], ['nonAdjProb', '編號都不相連的機率'], ['sameGroup', '至少兩人同一組的機率'], ['drawUntilEmpty', '某色先取完的機率'], ['gapPrize', '兩黑球之間白球數的期望值'], ['fairPenalty', '公平遊戲反求賠額'], ['drawExpect', '取 k 個中特定品項的期望值']];
  /* 固定題 L3-n 對應的類似題型 */
  var L3_FIX = { 'L3-1': 'multiples3', 'L3-2': 'oddCount', 'L3-3': 'distinctMult', 'L3-4': 'orderedPick', 'L3-5': 'seatBlock', 'L3-6': 'prodMultiple', 'L3-7': 'shareItems', 'L3-8': 'sumCoefC', 'L3-9': 'digitExtreme', 'L3-10': 'nonAdjProb', 'L3-11': 'sameGroup', 'L3-12': 'drawUntilEmpty', 'L3-13': 'gapPrize', 'L3-14': 'fairPenalty', 'L3-15': 'drawExpect' };

  /* ══════════════════════════════════════════════════════════
     L0　章首先備診斷（5 型）：因數與倍數的個數（國中）、分數的約分與四則（國中）、集合的聯集與交集個數（國中）、階乘與連乘的化簡（國中）、加權平均（國中）
     ══════════════════════════════════════════════════════════ */
  var L0 = {};
  function l0floor(a, b) { return Math.floor(a / b); }
  function l0lcm(a, b) { return a * b / gcd(a, b); }
  L0.multCount = function (r) {
    var v = r.int(0, 1), N = r.pick([50, 60, 80, 100, 120, 150, 200]), a = r.pick([2, 3, 4, 5, 6, 7, 8, 9]);
    if (v === 0) return { q: T('1') + ' 到 ' + T(String(N)) + ' 的整數中，' + T(String(a)) + ' 的倍數有幾個？', a: T(String(l0floor(N, a))) + ' 個',
      h: '$\\left\\lfloor\\dfrac{' + N + '}{' + a + '}\\right\\rfloor=' + l0floor(N, a) + '$（商取整數）。本章「取捨原理」的每一塊都是這樣數出來的。',
      p: { v: v, N: N, a: a, ans: l0floor(N, a) } };
    var b; do { b = r.pick([2, 3, 4, 5, 6, 7, 9]); } while (b === a || b % a === 0 || a % b === 0);
    var L = l0lcm(a, b), both = l0floor(N, L), either = l0floor(N, a) + l0floor(N, b) - both;
    return { q: T('1') + ' 到 ' + T(String(N)) + ' 的整數中，同時是 ' + T(String(a)) + ' 的倍數也是 ' + T(String(b)) + ' 的倍數的有幾個？是 ' + T(String(a)) + ' 的倍數或 ' + T(String(b)) + ' 的倍數的又有幾個？', a: '同時是：' + T(String(both)) + ' 個；至少是其一：' + T(String(either)) + ' 個',
      h: '「同時是 $' + a + '$ 與 $' + b + '$ 的倍數」就是最小公倍數 $' + L + '$ 的倍數：$\\left\\lfloor\\dfrac{' + N + '}{' + L + '}\\right\\rfloor=' + both + '$；「或」用取捨：$' + l0floor(N, a) + '+' + l0floor(N, b) + '-' + both + '=' + either + '$。',
      p: { v: v, N: N, a: a, b: b, ans: [both, either] } };
  };
  L0.fracOps = function (r) {
    var v = r.int(0, 1), d1 = r.pick([4, 6, 8, 9, 10, 12]), d2 = r.pick([3, 4, 5, 6, 8]), n1 = r.int(1, d1 - 1), n2 = r.int(1, d2 - 1);
    if (v === 0) {
      var s = Fr.add(F(n1, d1), F(n2, d2));
      return { q: '計算 ' + T('\\dfrac{' + n1 + '}{' + d1 + '}+\\dfrac{' + n2 + '}{' + d2 + '}') + '（化為最簡分數）。', a: T(Fr.tex(s)),
        h: '通分到 $' + l0lcm(d1, d2) + '$：$\\dfrac{' + n1 * (l0lcm(d1, d2) / d1) + '+' + n2 * (l0lcm(d1, d2) / d2) + '}{' + l0lcm(d1, d2) + '}$，再約分。本章機率的加法（互斥事件相加）就是分數相加。',
        p: { v: v, f1: [n1, d1], f2: [n2, d2], ans: fr2(s) } };
    }
    var m = Fr.mul(F(n1, d1), F(n2, d2));
    return { q: '計算 ' + T('\\dfrac{' + n1 + '}{' + d1 + '}\\times\\dfrac{' + n2 + '}{' + d2 + '}') + '（化為最簡分數）。', a: T(Fr.tex(m)),
      h: '分子乘分子、分母乘分母：$\\dfrac{' + n1 * n2 + '}{' + d1 * d2 + '}$，先約分再乘更快。本章「連續抽取」的機率就是一串分數相乘。',
      p: { v: v, f1: [n1, d1], f2: [n2, d2], ans: fr2(m) } };
  };
  L0.setCount = function (r) {
    var v = r.int(0, 1), N = r.pick([30, 35, 40, 45, 50]), both = r.int(3, 10), onlyA = r.int(4, 14), onlyB = r.int(3, 12), A = both + onlyA, B = both + onlyB, none = N - (A + B - both);
    if (none < 0) { N = A + B - both + r.int(0, 6); none = N - (A + B - both); }
    if (v === 0) return { q: '班上 ' + T(String(N)) + ' 人，參加籃球社的有 ' + T(String(A)) + ' 人、參加美術社的有 ' + T(String(B)) + ' 人，兩個都參加的有 ' + T(String(both)) + ' 人。至少參加一個社團的有幾人？兩個都沒參加的有幾人？', a: '至少一個：' + T(String(A + B - both)) + ' 人；都沒有：' + T(String(none)) + ' 人',
      h: '$|A\\cup B|=|A|+|B|-|A\\cap B|=' + A + '+' + B + '-' + both + '=' + (A + B - both) + '$；都沒參加 $=' + N + '-' + (A + B - both) + '=' + none + '$。本章取捨原理與補集法從這裡出發。',
      p: { v: v, N: N, A: A, B: B, both: both, ans: [A + B - both, none] } };
    return { q: '班上 ' + T(String(N)) + ' 人，參加籃球社的有 ' + T(String(A)) + ' 人、參加美術社的有 ' + T(String(B)) + ' 人，兩個都沒參加的有 ' + T(String(none)) + ' 人。兩個都參加的有幾人？只參加籃球社的有幾人？', a: '都參加：' + T(String(both)) + ' 人；只有籃球：' + T(String(onlyA)) + ' 人',
      h: '至少參加一個 $=' + N + '-' + none + '=' + (N - none) + '$，再由 $|A|+|B|-|A\\cap B|=' + (N - none) + '$ 得 $|A\\cap B|=' + A + '+' + B + '-' + (N - none) + '=' + both + '$；只有籃球 $=' + A + '-' + both + '=' + onlyA + '$。',
      p: { v: v, N: N, A: A, B: B, none: none, ans: [both, onlyA] } };
  };
  L0.factCalc = function (r) {
    var v = r.int(0, 1), n = r.int(5, 10), k = r.int(1, 4);
    if (v === 0) return { q: '計算 ' + T('\\dfrac{' + n + '!}{' + (n - k) + '!}') + '。', a: T(String(P(n, k))),
      h: '分子的 $' + n + '!$ 展開到 $' + (n - k + 1) + '$ 就會和分母的 $' + (n - k) + '!$ 全部約掉，只剩 $' + (k === 1 ? String(n) : (function () { var s = []; for (var i = 0; i < k; i++) s.push(String(n - i)); return s.join('\\times'); })() + '=' + P(n, k)) + '$。本章排列數 $P^n_k$ 就是這個算式。',
      p: { v: v, n: n, k: k, ans: P(n, k) } };
    var m = r.int(2, Math.min(5, n - 1));
    return { q: '計算 ' + T('\\dfrac{' + n + '!}{' + m + '!\\,' + (n - m) + '!}') + '。', a: T(String(C(n, m))),
      h: '先約掉 $' + (n - m) + '!$：$\\dfrac{' + (function () { var s = []; for (var i = 0; i < m; i++) s.push(String(n - i)); return s.join('\\times'); })() + '}{' + m + '!}=\\dfrac{' + P(n, m) + '}{' + fact(m) + '}=' + C(n, m) + '$。本章組合數 $C^n_m$ 就是這個算式。',
      p: { v: v, n: n, m: m, ans: C(n, m) } };
  };
  L0.weightedAvg = function (r) {
    var v = r.int(0, 1), a = r.int(60, 95), b = r.int(60, 95), wa = r.int(1, 5), wb = r.int(1, 5), t = 0;
    while (a === b && t++ < 10) b = r.int(60, 95);
    var avg = F(a * wa + b * wb, wa + wb);
    if (v === 0) return { q: '某科目平時成績 ' + T(String(a)) + ' 分、期末成績 ' + T(String(b)) + ' 分，若平時與期末的權重為 ' + T(wa + ':' + wb) + '，學期成績（加權平均）是幾分？', a: T(Fr.tex(avg)) + ' 分',
      h: '加權平均 $=\\dfrac{' + a + (wa === 1 ? '' : '\\times' + wa) + '+' + b + (wb === 1 ? '' : '\\times' + wb) + '}{' + wa + '+' + wb + '}=\\dfrac{' + (a * wa + b * wb) + '}{' + (wa + wb) + '}$。本章期望值就是「值 $\\times$ 機率」的加權平均，權重換成機率。',
      p: { v: v, a: a, b: b, wa: wa, wb: wb, ans: fr2(avg) } };
    var p1 = F(wa, wa + wb), p2 = F(wb, wa + wb), E = Fr.add(Fr.mul(F(a), p1), Fr.mul(F(b), p2));
    return { q: '一個數有 ' + T(Fr.tex(p1)) + ' 的機會是 ' + T(String(a)) + '、' + T(Fr.tex(p2)) + ' 的機會是 ' + T(String(b)) + '，求「值 ' + T('\\times') + ' 機會」相加的結果。', a: T(Fr.tex(E)),
      h: '$' + a + '\\times' + Fr.tex(p1) + '+' + b + '\\times' + Fr.tex(p2) + '=' + Fr.tex(E) + '$，兩個機會加起來是 $1$，所以它就是以機會當權重的加權平均——本章的期望值。',
      p: { v: v, a: a, b: b, wa: wa, wb: wb, ans: fr2(E) } };
  };
  var META_L0 = [['multCount', '倍數的個數'], ['fracOps', '分數的加法與乘法'], ['setCount', '兩個集合的聯集與交集個數'], ['factCalc', '階乘與連乘的化簡'], ['weightedAvg', '加權平均']];
  /* 先備題型 → 該去哪裡複習 */
  var PREREQ = {
    multCount: { txt: '1 到 N 的倍數個數與最小公倍數（國中）——取捨原理每一塊都靠它', link: null },
    fracOps: { txt: '分數的通分、約分、相乘（國中）——機率的加法與連續抽取就是分數運算', link: null },
    setCount: { txt: '兩個集合的聯集、交集與補集個數（國中）——取捨原理、補集法的起點', link: null },
    factCalc: { txt: '階乘與連乘的約分（國中）——排列數 P、組合數 C 全是這個算式', link: null },
    weightedAvg: { txt: '加權平均（國中）——期望值就是以機率當權重的加權平均', link: null }
  };
  /* ══════════════════════════════════════════════════════════
     對照題：同一型抽兩題，只差一個關鍵特徵（f 由 p 算出；keep 的欄位要相同）
     ══════════════════════════════════════════════════════════ */
  function sign3(x) { return x > 0 ? 1 : x < 0 ? -1 : 0; }
  var CONTRAST = {
    'L1.multiples': { f: function (p) { return p.kind; }, why: '「$a$ 或 $b$ 的倍數」是聯集：$|A|+|B|-|A\\cap B|$；「$a$ 的倍數但不是 $b$ 的倍數」是差集：$|A|-|A\\cap B|$。兩題都要先算交集（最小公倍數的倍數），差別只在最後加還是減。' },
    'L1.dice2': { f: function (p) { return p.kind; }, why: '兩顆骰子的樣本空間永遠是 $36$ 個等可能的有序點對：問「和」就數斜線上的點、問「差」要記得正負兩邊都算、問「至少」就把後面的和全部加起來。分母不變，只是數分子的方式不同。' },
    'L1.fairGame': { f: function (p) { return p.win; }, why: '公平就是期望值為 $0$：$w\\cdot P(\\text{贏})=x\\cdot P(\\text{輸})$。得獎事件換了（$36$ 個點對裡佔幾個），只是 $P(\\text{贏})$ 的分子換了，公式與解法完全一樣。' },
    'L1.expShift': { f: function (p) { return !!p.two; }, why: '$E(ak+b)=aE(k)+b$：一顆骰子 $E(k)=\\frac72$、兩顆骰子點數和 $E(k)=7$。不必重列分布表，只要知道 $k$ 的期望值，再平移伸縮。' },
    'L1.gaps': { f: function (p) { return p.k; }, why: '女生互不相鄰用插空：先排男生造出 $m+1$ 個空隙，再把 $k$ 位女生排進不同的空隙 $P^{m+1}_k$；女生人數變多，空隙數不變、只是排進去的方式數變了——而「全部相鄰」永遠是捆綁法 $(m+1)!\\,k!$。' },
    'L1.coins': { f: function (p) { return p.v; }, why: '「恰有 $k$ 次正面」是 $\\dfrac{C^n_k}{2^n}$；「至少 $k$ 次」把 $k,k+1,\\dots,n$ 的 $C^n_i$ 加起來、「至多 $k$ 次」把 $0,1,\\dots,k$ 的加起來——方向相反，兩者相加再扣掉恰 $k$ 次就是全部。' },
    'L2.distributeAll': { f: function (p) { return p.kind; }, why: '「每人至少一件」要扣三個「某人沒拿到」再補回兩兩的交集：$3^k-3\\cdot2^k+3$；只要求「甲、乙都至少一件」則只扣兩個、補回一個：$3^k-2\\cdot2^k+1$。取捨的項數看條件裡有幾個人。' },
    'L2.barsBound': { f: function (p) { return p.kind; }, why: '下界 $x\\ge a$ 就先把 $a$ 個分掉再隔板；上界 $x\\le a$ 要用補集：先算全部，再扣掉 $x\\ge a+1$ 的解。一個是「先給」、一個是「先扣」。' },
    'L2.combIdentityVal': { f: function (p) { return p.kind; }, why: '組合恆等式的來源只有兩種：把 $x$ 代進 $(1+x)^n$（代 $2$、代 $-1$ 取奇偶）、或用 $kC^n_k=nC^{n-1}_{k-1}$ 把係數吃掉。看清楚題目的係數是 $2^k$、還是 $k$，就知道走哪一條。' },
    'L2.dice3': { f: function (p) { return p.kind; }, why: '三顆骰子的樣本空間是 $216$ 個有序點；「能圍成三角形」「三數成等差」「最大值恰為某數」都要**先排序再判斷條件**，數的時候別忘了把同一組數字的不同排列都算進去。' },
    'L2.digitsMult3': { f: function (p) { return !!p.withZero; }, why: '$3$ 的倍數看數字和：先把可用的數字依除以 $3$ 的餘數分成三堆，再挑「三個餘數加起來是 $3$ 的倍數」的組合；有 $0$ 時多一個陷阱——$0$ 不能當首位，含 $0$ 的組合排法只剩 $2\\times2$。' },
    'L3.multiples3': { f: function (p) { return p.v; }, why: '三集合取捨的骨架一樣：$|A\\cup B\\cup C|=\\sum|A|-\\sum|A\\cap B|+|A\\cap B\\cap C|$，交集是最小公倍數的倍數。「都不是」用全部減聯集；「恰好是其中一個」要把兩兩交集扣兩次、三重交集加三次。' },
    'L3.oddCount': { f: function (p) { return p.v; }, why: '依「含幾個 $d$」分類：恰 $j$ 個是 $C^k_j\\times(\\text{其餘數字數})^{k-j}$。問奇數個就加 $j=1,3,\\dots$、偶數個就加 $j=0,2,\\dots$、至少兩個用全部減 $j=0,1$——分類的方法相同，只是把哪幾類加起來。' },
    'L3.distinctMult': { f: function (p) { return p.t; }, why: '$5$ 的倍數看個位是 $0$ 或 $5$、$2$ 的倍數看個位是偶數：一律先排個位再排首位，**個位不是 $0$ 時首位要同時避開 $0$ 與個位那個數字**，這是 $0$ 帶來的唯一陷阱。' },
    'L3.orderedPick': { f: function (p) { return p.v; }, why: '順序被規定死的那一群只剩「選」：奇數、偶數都遞增 ⟹ $C\\times C\\times C(\\text{選位置})$；一群遞增一群遞減 ⟹ 一樣（遞減也只有一種排法）；只規定奇數 ⟹ 偶數還要乘上自己的排列數 $t!$。' },
    'L3.prodMultiple': { f: function (p) { return p.v; }, why: '乘積是 $M$ 的倍數看質因數：把數依「含幾個因數 $2$（或 $3$）」分堆再組合。問取法數直接數、問「不是」用全部減、問機率再除以 $C^N_k$——分堆的方式完全相同。' },
    'L3.shareItems': { f: function (p) { return p.v; }, why: '指定甲拿 $a$ 個是 $C^n_a C^{n-a}_b$；「其中一人拿 $a$ 個」要先選是誰（乘 $3$）；「分成三堆、堆不分先後」則兩堆一樣大要除以 $2!$。同一個數字乘 $3$ 或除 $2$，全看堆有沒有名字。' },
    'L3.sumCoefC': { f: function (p) { return p.v; }, why: '不管寫成一長串還是 $\\sum$ 記號，都是 $\\sum(j-c)C^n_j$：拆成 $\\sum jC^n_j-c\\sum C^n_j$，前者用 $jC^n_j=nC^{n-1}_{j-1}$ 化成 $n\\cdot2^{n-1}$、後者是 $2^n$，再扣掉起始下標前面漏算的幾項。' },
    'L3.digitExtreme': { f: function (p) { return p.kind; }, why: '「某一位最小／最大」：選 $n$ 個相異數字後，極值的位置固定、其餘任排，$0$ 只可能落在最小那一位；「依次變大／變小」：選完數字順序就唯一，變大時 $0$ 選不進來、變小時 $0$ 可以在個位。' },
    'L3.nonAdjProb': { f: function (p) { return p.v; }, why: '編號都不相連的取法是 $C^{n-k+1}_k$（把每個被取的號碼後面「墊一個空位」）；「至少兩個相連」用 $1$ 減它；「恰有一對相連」把那一對綁成寬 $2$ 的塊再插空。分母永遠是 $C^n_k$。' },
    'L3.sameGroup': { f: function (p) { return p.v; }, why: '$k$ 人各選 $m$ 個之一，樣本空間 $m^k$；「兩兩不同」是 $P^m_k$，「至少兩人同」用 $1$ 減它，「恰有一對相同」要先選那一對、再選號碼、其餘各不相同。' },
    'L3.drawUntilEmpty': { f: function (p) { return p.v; }, why: '「某色先取完」等價於「最後一顆是另一色」，機率就是另一色的比例，不必模擬抽取過程；「第 $k$ 次取出最後一張某色」則要求前 $k-1$ 次含其餘的同色、第 $k$ 次是它，分母是位置的組合數。' },
    'L3.gapPrize': { f: function (p) { return p.v; }, why: '只看兩顆黑球的位置：$C^{w+2}_2$ 種等可能，間隔 $k$ 的有 $w+1-k$ 種。獎金是 $ck+d$ 時，$E=cE(k)+d$，先算 $E(k)$ 再平移伸縮就好。' },
    'L3.drawExpect': { f: function (p) { return p.v; }, why: '取 $k$ 個中特定品項個數的期望值 $=k\\cdot\\dfrac{m}{N}$（每一個被取到的機會都是 $\\frac mN$，線性相加）；乘上單價就是金額的期望值；問「恰取到 $1$ 個的機率」才需要真的算 $\\dfrac{C^m_1C^{N-m}_{k-1}}{C^N_k}$。' }
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
      return '$' + inner.replace(/</g, '\\lt ').replace(/>/g, '\\gt ').replace(/\\times(?=[A-Za-z])/g, '\\times ') + '$';
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

  return { makeRng: makeRng, L0: L0, L1: L1, L2: L2, L3: L3, L3_FIX: L3_FIX, META: META, PREREQ: PREREQ, CONTRAST: CONTRAST, contrastPair: contrastPair, _util: { gcd: gcd, F: F, Fr: Fr, C: C, P: P } };
}));
