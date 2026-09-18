/* ══════════════════════════════════════════════════════════════
   g11b-ch03 條件機率與貝氏定理・分級練習本　題目產生器
   ─────────────────────────────────────────────────────────────
   每個產生器：function (rng) → { q, a, h, p }
     q：題目（HTML，可含 KaTeX $…$）   a：答案（HTML）
     h：一行提示（一定要帶本題的數字與關鍵一步）
     p：輸入參數與結構化答案 p.ans（給 verify_gen11b3.py 從題幹重算後對照）
   答案一律是精確分數（Fr.tex，最簡）；題幹可以用百分比或小數，答案不用小數。
   課綱界線（HANDOUT_SPEC §4）：不出現隨機變數／二項分布／期望值／常態分布／馬可夫；
   不用「全機率公式」這個名詞（說「把所有路徑加起來」）；
   不用偽陽性／偽陰性／敏感度／特異度（改用中文敘述「沒生病卻驗出陽性」…）。
   重複試驗一律用高一下的組合硬乘 C^n_k p^k (1-p)^{n-k}（主講義用 C^n_k，不用 \binom）。
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
    cmp: function (x, y) { return x.n * y.d - y.n * x.d; },
    num: function (x) { return x.n / x.d; },
    cp: function (x) { return F(x.d - x.n, x.d); },
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
  function trimz(s) { if (s.indexOf('.') < 0) return s; s = s.replace(/0+$/, ''); if (s.charAt(s.length - 1) === '.') s = s.slice(0, -1); return s; }
  function dec(x, k) { return trimz(x.toFixed(k === undefined ? 6 : k)); }
  function decF(f, k) { return dec(f.n / f.d, k); }
  function pc(f) { return trimz((f.n * 100 / f.d).toFixed(4)) + '\\%'; }
  /* 乘積一律「括號並列」：(3)(5)、\left(\dfrac12\right)(4)；因數是 1 時不會印出來 */
  function par(s) { s = String(s); return s.indexOf('\\') >= 0 ? '\\left(' + s + '\\right)' : '(' + s + ')'; }
  function sup(k) { return k < 10 ? '^' + k : '^{' + k + '}'; }
  function pw(b, k) { if (k === 0) return ''; if (k === 1) return par(b); return par(b) + sup(k); }
  function prod(list) { var t = [], i, s; for (i = 0; i < list.length; i++) { s = String(list[i]); if (s === '' || s === '1') continue; t.push(par(s)); } return t.length ? t.join('') : '1'; }
  function prodF(fs) { var t = [], i; for (i = 0; i < fs.length; i++) t.push(Fr.tex(fs[i])); return prod(t); }
  function nCr(n, k) { if (k < 0 || k > n) return 0; var t = 1, i; for (i = 1; i <= k; i++) t = t * (n - k + i) / i; return Math.round(t); }
  function CT(n, k) { return 'C^' + (n < 10 ? n : '{' + n + '}') + '_' + (k < 10 ? k : '{' + k + '}'); }
  /* C^n_k p^k (1-p)^{n-k}；C=1、指數為 0 的因式都不印 */
  function binTex(n, k, pT, qT) { var s = (nCr(n, k) === 1) ? '' : CT(n, k); s += pw(pT, k); s += pw(qT, n - k); return s === '' ? '1' : s; }
  function binP(n, k, p) { return Fr.mul(F(nCr(n, k)), Fr.mul(Fr.pow(p, k), Fr.pow(Fr.cp(p), n - k))); }
  function ansEq(e, v) { return T(e + '=' + Fr.tex(v)); }
  function no(i) { return '(' + i + ') '; }
  function jo(a) { return a.join('　'); }
  function sumF(fs) { var t = F(0), i; for (i = 0; i < fs.length; i++) t = Fr.add(t, fs[i]); return t; }

  /* ── 2×2 列聯表情境（列標籤、欄標籤兩兩相異，驗算器用完全比對認標籤） ── */
  var TB = [
    { h: '某校高二學生', r: ['有參加社團', '未參加社團'], c: ['數學及格', '數學不及格'], u: '位', one: '任選一位學生' },
    { h: '某次健康檢查', r: ['有運動習慣', '沒有運動習慣'], c: ['血壓正常', '血壓偏高'], u: '位', one: '任選一個人' },
    { h: '某路口的駕駛人', r: ['有駕照', '無駕照'], c: ['曾經肇事', '未曾肇事'], u: '位', one: '任選一位駕駛人' },
    { h: '某問卷的受訪者', r: ['已婚', '未婚'], c: ['有訂閱', '未訂閱'], u: '位', one: '任選一位受訪者' },
    { h: '某校學生', r: ['男生', '女生'], c: ['有搭校車', '沒搭校車'], u: '位', one: '任選一位學生' },
    { h: '某工廠的產品', r: ['甲廠製造', '乙廠製造'], c: ['通過檢驗', '未通過檢驗'], u: '件', one: '任取一件產品' },
    { h: '某班學生', r: ['住校', '通勤'], c: ['有近視', '沒有近視'], u: '位', one: '任選一位學生' },
    { h: '某次模擬考的考生', r: ['有補習', '沒有補習'], c: ['英文及格', '英文不及格'], u: '位', one: '任選一位考生' },
    { h: '某社區的住戶', r: ['有養寵物', '沒有養寵物'], c: ['住一樓', '不住一樓'], u: '戶', one: '任選一戶' },
    { h: '某公司的員工', r: ['常常加班', '很少加班'], c: ['通勤超過一小時', '通勤不到一小時'], u: '位', one: '任選一位員工' }
  ];
  /* ── 兩分支「原因 → 結果」情境：[原因1, 原因2, 結果, 結果的反面, 個體, 取樣句] ── */
  var CS2 = [
    { a: '甲生產線', b: '乙生產線', y: '不良品', n: '良品', o: '產品', pick: '任取一件產品', w: '產量' },
    { a: '甲工廠', b: '乙工廠', y: '瑕疵品', n: '正常品', o: '零件', pick: '任取一個零件', w: '產量' },
    { a: '甲農場', b: '乙農場', y: '特級果', n: '普通果', o: '水果', pick: '任取一顆水果', w: '產量' },
    { a: '甲供應商', b: '乙供應商', y: '延遲到貨', n: '準時到貨', o: '訂單', pick: '任取一筆訂單', w: '供貨量' },
    { a: '白天班', b: '夜間班', y: '出錯', n: '沒有出錯', o: '作業', pick: '任取一件作業', w: '件數' },
    { a: '甲機器', b: '乙機器', y: '不合格', n: '合格', o: '成品', pick: '任取一件成品', w: '產量' }
  ];
  /* ── 三分支 ── */
  var CS3 = [
    { a: ['甲生產線', '乙生產線', '丙生產線'], y: '不良品', n: '良品', o: '產品', pick: '任取一件產品', w: '產量' },
    { a: ['甲供應商', '乙供應商', '丙供應商'], y: '瑕疵品', n: '完好', o: '零件', pick: '任取一個零件', w: '供貨量' },
    { a: ['高一', '高二', '高三'], y: '有近視', n: '沒有近視', o: '學生', pick: '任選一位學生', w: '人數' },
    { a: ['甲班', '乙班', '丙班'], y: '通過檢定', n: '沒通過檢定', o: '學生', pick: '任選一位學生', w: '人數' }
  ];
  /* ── 袋子與球 ── */
  var BAG = [
    { b: '袋', o: '球', c: ['紅', '白'] }, { b: '盒', o: '球', c: ['黑', '白'] },
    { b: '箱', o: '球', c: ['紅', '藍'] }, { b: '袋', o: '球', c: ['黃', '綠'] },
    { b: '盒', o: '球', c: ['白', '黑'] }, { b: '箱', o: '球', c: ['藍', '紅'] }
  ];
  /* ── 獨立重複試驗的情境：[主詞, 一次試驗, 成功] ── */
  var RT = [
    { s: '某射手每次射擊', y: '命中目標', n: '沒有命中', u: '次', vb: '射擊' },
    { s: '某人每次投籃', y: '投進', n: '沒投進', u: '次', vb: '投籃' },
    { s: '某機器每小時', y: '故障', n: '沒有故障', u: '小時', vb: '運轉' },
    { s: '某遊戲每次抽卡', y: '抽中稀有卡', n: '沒抽中', u: '次', vb: '抽卡' },
    { s: '某考生每題作答', y: '答對', n: '答錯', u: '題', vb: '作答' },
    { s: '某球隊每場比賽', y: '獲勝', n: '沒有獲勝', u: '場', vb: '比賽' },
    { s: '某農場每顆種子', y: '發芽', n: '沒有發芽', u: '顆', vb: '種下' }
  ];
  /* ── 篩檢情境（不使用偽陽性／偽陰性／敏感度／特異度） ── */
  var SCR = [
    { d: '罹患某疾病', nd: '沒有罹患該疾病', y: '檢驗結果為陽性', n: '檢驗結果為陰性', pop: '受檢者', one: '任選一位受檢者' },
    { d: '已感染', nd: '沒有感染', y: '快篩結果為陽性', n: '快篩結果為陰性', pop: '船上人員', one: '任選一位人員' },
    { d: '零件有瑕疵', nd: '零件沒有瑕疵', y: '儀器判定為不良', n: '儀器判定為良好', pop: '零件', one: '任取一個零件' },
    { d: '有作弊', nd: '沒有作弊', y: '系統標記為可疑', n: '系統沒有標記', pop: '考生', one: '任選一位考生' }
  ];

  /* ── 骰子事件：t 是題幹裡的敘述（驗算器照字串重建集合），f 是判斷函式 ── */
  function dieEv1(r) {
    var k;
    switch (r.int(0, 7)) {
      case 0: return { t: '點數為奇數', f: function (n) { return n % 2 === 1; } };
      case 1: return { t: '點數為偶數', f: function (n) { return n % 2 === 0; } };
      case 2: return { t: '點數為質數', f: function (n) { return n === 2 || n === 3 || n === 5; } };
      case 3: k = r.int(1, 4); return { t: '點數大於 ' + T(k), f: function (n) { return n > k; } };
      case 4: k = r.int(3, 6); return { t: '點數小於 ' + T(k), f: function (n) { return n < k; } };
      case 5: k = r.pick([2, 3]); return { t: '點數為 ' + T(k) + ' 的倍數', f: function (n) { return n % k === 0; } };
      case 6: k = r.int(2, 5); return { t: '點數至少為 ' + T(k), f: function (n) { return n >= k; } };
      default: k = r.int(2, 5); return { t: '點數不超過 ' + T(k), f: function (n) { return n <= k; } };
    }
  }
  function dieEv2(r) {
    var k;
    switch (r.int(0, 7)) {
      case 0: k = r.int(4, 10); return { t: '兩顆的點數和為 ' + T(k), f: function (a, b) { return a + b === k; } };
      case 1: k = r.int(5, 9); return { t: '兩顆的點數和大於 ' + T(k), f: function (a, b) { return a + b > k; } };
      case 2: return { t: '兩顆的點數和為偶數', f: function (a, b) { return (a + b) % 2 === 0; } };
      case 3: k = r.int(1, 6); return { t: '至少有一顆是 ' + T(k) + ' 點', f: function (a, b) { return a === k || b === k; } };
      case 4: return { t: '兩顆的點數相同', f: function (a, b) { return a === b; } };
      case 5: return { t: '兩顆的點數相異', f: function (a, b) { return a !== b; } };
      case 6: k = r.int(1, 4); return { t: '兩顆的點數差為 ' + T(k), f: function (a, b) { return Math.abs(a - b) === k; } };
      default: k = r.pick([6, 8, 12, 10, 4, 16, 18, 24]); return { t: '兩顆的點數乘積為 ' + T(k), f: function (a, b) { return a * b === k; } };
    }
  }
  function cnt1(e) { var c = 0, n; for (n = 1; n <= 6; n++) if (e(n)) c++; return c; }
  function cnt2(e) { var c = 0, a, b; for (a = 1; a <= 6; a++) for (b = 1; b <= 6; b++) if (e(a, b)) c++; return c; }
  /* 列聯表：四格敘述（驗算器用「「列」且「欄」有 $n$」的正則抓） */
  function tabTex(tb, M) {
    var out = [], i, j;
    for (i = 0; i < 2; i++) for (j = 0; j < 2; j++) out.push('「' + tb.r[i] + '」且「' + tb.c[j] + '」有 ' + T(M[i][j]) + ' ' + tb.u);
    return out.join('、');
  }
  function tabHead(tb, M) {
    var N = M[0][0] + M[0][1] + M[1][0] + M[1][1];
    return tb.h + '共 ' + T(N) + ' ' + tb.u + '，其中' + tabTex(tb, M) + '。';
  }
  function rowSum(M, i) { return M[i][0] + M[i][1]; }
  function colSum(M, j) { return M[0][j] + M[1][j]; }

  /* ═══════════════════════ L1 ═══════════════════════ */
  var L1 = {};

  /* ── §1 從次數表得到客觀機率 ── */
  L1.freqTable = function (r) {
    var kind = r.int(0, 1), i, f, N, e1, e2, n1, n2, ans1, ans2, body, t = 0;
    if (kind === 0) {
      do {
        f = []; N = 0;
        for (i = 0; i < 6; i++) { f.push(r.int(8, 30)); N += f[i]; }
        e1 = dieEv1(r); e2 = dieEv1(r);
        n1 = 0; n2 = 0;
        for (i = 1; i <= 6; i++) { if (e1.f(i)) n1 += f[i - 1]; if (e2.f(i)) n2 += f[i - 1]; }
        t++;
      } while ((e1.t === e2.t || n1 === 0 || n2 === 0 || n1 === N || n2 === N) && t < 200);
      ans1 = F(n1, N); ans2 = F(n2, N);
      var th = F(cnt1(e1.f), 6);
      body = '一顆來路不明的骰子投擲 ' + T(N) + ' 次，點數 ' + T(1) + ' 到 ' + T(6) + ' 出現的次數依序為 ' + T(f.join(',\\ ')) + '。用客觀機率（相對次數）的觀點回答：';
      return { q: body + no(1) + '求擲出「' + e1.t + '」的機率。' + no(2) + '求擲出「' + e2.t + '」的機率。' + no(3) + '若這顆骰子是公正的，' + no(1) + '的理論值應該是多少？',
               a: jo([no(1) + T(Fr.tex(ans1)), no(2) + T(Fr.tex(ans2)), no(3) + T(Fr.tex(th))]),
               h: '客觀機率就是相對次數：把該事件包含的點數次數加起來再除以總次數 ' + T(N) + '。' + no(1) + '「' + e1.t + '」的次數合計 ' + T(n1) + '；' + no(2) + '合計 ' + T(n2) + '；' + no(3) + '公正骰子每點都是 ' + T('\\dfrac16') + '，符合的點數有 ' + T(cnt1(e1.f)) + ' 個。',
               p: { kind: 0, N: N, f: f, e1: e1.t, e2: e2.t, ans: [fp(ans1), fp(ans2), fp(th)] } };
    }
    var GS = [
      { h: '某超商統計顧客購買的飲料', k: ['咖啡', '茶', '果汁', '汽水'], one: '下一位顧客', u: '人', v: '買' },
      { h: '某書店統計顧客購買的書籍', k: ['小說', '漫畫', '參考書', '雜誌'], one: '下一位顧客', u: '人', v: '買' },
      { h: '某校統計學生的上學方式', k: ['走路', '腳踏車', '公車', '家長接送'], one: '任選一位學生', u: '人', v: '是' },
      { h: '某餐廳統計顧客點的主餐', k: ['牛肉麵', '燉飯', '咖哩', '沙拉'], one: '下一位顧客', u: '人', v: '點' }
    ];
    var g = r.pick(GS), cs = [], j;
    for (j = 0; j < 4; j++) cs.push(r.int(15, 90));
    var Ntot = cs[0] + cs[1] + cs[2] + cs[3];
    var id = r.shuffle([0, 1, 2, 3]), i0 = id[0], i1 = id[1], i2 = id[2];
    var a1 = F(cs[i0], Ntot), a2 = F(cs[i0] + cs[i1], Ntot), a3 = F(Ntot - cs[i2], Ntot);
    body = g.h + '，共 ' + T(Ntot) + ' ' + g.u + '：' + g.k.map(function (nm, ii) { return nm + ' ' + T(cs[ii]) + ' ' + g.u; }).join('、') + '。用客觀機率的觀點，求' + g.one;
    return { q: body + no(1) + g.v + g.k[i0] + '、' + no(2) + g.v + g.k[i0] + '或' + g.k[i1] + '、' + no(3) + '不' + g.v + g.k[i2] + ' 的機率。',
             a: jo([no(1) + T(Fr.tex(a1)), no(2) + T(Fr.tex(a2)), no(3) + T(Fr.tex(a3))]),
             h: '相對次數就是客觀機率，分母一律是總數 ' + T(Ntot) + '。' + no(2) + '兩類互斥可以直接相加：' + T(cs[i0] + '+' + cs[i1] + '=' + (cs[i0] + cs[i1])) + '；' + no(3) + '走餘事件最快：' + T(Ntot + '-' + cs[i2] + '=' + (Ntot - cs[i2])) + '。',
             p: { kind: 1, N: Ntot, cs: cs, ks: g.k, ask: [g.k[i0], g.k[i1], g.k[i2]], ans: [fp(a1), fp(a2), fp(a3)] } };
  };

  /* ── §1 檢視主觀機率的合理性 ── */
  var SJ3 = [['甲勝', '乙勝', '和局'], ['贏', '輸', '平手'], ['晴天', '陰天', '雨天'], ['搭公車', '騎腳踏車', '走路'], ['優等', '甲等', '乙等'], ['同意', '不同意', '沒意見']];
  var SJ2 = [['下雨', '下大雨'], ['投進球', '投進三分球'], ['及格', '滿分'], ['有養寵物', '有養狗'], ['搭乘大眾運輸', '搭捷運'], ['看電影', '看國片']];
  var SJ1 = ['這件事發生', '明天會下雪', '中獎', '球隊晉級', '這班車誤點'];
  function subjItem(r, ok) {
    var kind = r.int(0, 2), a, b, c, e;
    if (kind === 0) {
      e = r.pick(SJ3); a = r.int(20, 40); b = r.int(20, 40); c = 100 - a - b;
      if (!ok) c += r.pick([-20, -15, -10, 10, 15, 20]);
      return { txt: '某活動的三種結果「' + e[0] + '」的機率 ' + T(dec(a / 100)) + '、「' + e[1] + '」的機率 ' + T(dec(b / 100)) + '、「' + e[2] + '」的機率 ' + T(dec(c / 100)) + '，三者互斥又窮盡。', ok: (a + b + c === 100), law: '②',
               hi: '三個機率相加得 ' + T(dec(a / 100) + '+' + dec(b / 100) + '+' + dec(c / 100) + '=' + dec((a + b + c) / 100)) + '（互斥又窮盡就必須恰好是 ' + T(1) + '）' };
    }
    if (kind === 1) {
      e = r.pick(SJ2); a = r.int(30, 70); b = ok ? r.int(5, a - 5) : a + r.int(5, 25);
      return { txt: '「' + e[0] + '」的機率 ' + T(dec(a / 100)) + '、「' + e[1] + '」的機率 ' + T(dec(b / 100)) + '，其中「' + e[1] + '」包含於「' + e[0] + '」。', ok: (b <= a), law: '③',
               hi: '比 ' + T(dec(b / 100)) + ' 與 ' + T(dec(a / 100)) + ' 的大小（子事件的機率不可以比較大）' };
    }
    e = r.pick(SJ1); a = ok ? r.int(5, 95) : r.pick([-30, -20, -10, 110, 120, 140]);
    return { txt: '「' + e + '」的機率是 ' + T(dec(a / 100)) + '。', ok: (a >= 0 && a <= 100), law: '①',
             hi: '看 ' + T(dec(a / 100)) + ' 有沒有落在 ' + T(0) + ' 與 ' + T(1) + ' 之間' };
  }
  L1.subjCheck = function (r) {
    var n = 3, its = [], i, t = 0;
    do {
      its = []; for (i = 0; i < n; i++) its.push(subjItem(r, r() < 0.45));
      t++;
    } while ((its[0].law === its[1].law && its[1].law === its[2].law) && t < 60);
    var qs = its.map(function (it, i) { return no(i + 1) + it.txt; }).join('');
    var as = its.map(function (it, i) { return no(i + 1) + (it.ok ? '合理' : '不合理（違反性質 ' + it.law + '）'); });
    return { q: '機率有三條基本性質：① ' + T('0\\le P(A)\\le1') + '；② 互斥且窮盡的所有情形機率和為 ' + T(1) + '；③ ' + T('A\\subset B\\Rightarrow P(A)\\le P(B)') + '。下列各組是某人憑感覺給出的主觀機率，請逐組判斷是否合理，不合理者指出違反哪一條。' + qs,
             a: jo(as),
             h: '逐組檢查：' + its.map(function (it, i) { return no(i + 1) + '看性質 ' + it.law + '，' + it.hi; }).join('；') + '。',
             p: { laws: its.map(function (it) { return it.law; }), ans: its.map(function (it) { return it.ok ? 1 : 0; }) } };
  };

  /* ── §1 列聯表：邊際、聯合、條件三種機率 ── */
  L1.tableThree = function (r) {
    var tb = r.pick(TB), M, i, j, t = 0;
    do {
      M = [[r.int(20, 240), r.int(20, 240)], [r.int(20, 240), r.int(20, 240)]];
      t++;
    } while ((rowSum(M, 0) === 0 || colSum(M, 0) === 0) && t < 50);
    var ri = r.int(0, 1), ci = r.int(0, 1), N = rowSum(M, 0) + rowSum(M, 1);
    var a1 = F(rowSum(M, ri), N), a2 = F(M[ri][ci], N), a3 = F(M[ri][ci], rowSum(M, ri)), a4 = F(M[ri][ci], colSum(M, ci));
    var R = tb.r[ri], C = tb.c[ci];
    return { q: tabHead(tb, M) + tb.one + '，求下列機率（化為最簡分數）：' + no(1) + T(PTx(tx(R))) + '　' + no(2) + T(PTx(tx(R) + '\\cap' + tx(C))) + '　' + no(3) + T(PTx(tx(C) + '\\mid' + tx(R))) + '　' + no(4) + T(PTx(tx(R) + '\\mid' + tx(C))) + '。',
             a: jo([no(1) + T(Fr.tex(a1)), no(2) + T(Fr.tex(a2)), no(3) + T(Fr.tex(a3)), no(4) + T(Fr.tex(a4))]),
             h: '邊際與聯合的分母都是總數 ' + T(N) + '；條件機率的分母要換成「已知」那一類的合計。' + no(3) + '分母是「' + R + '」的合計 ' + T(rowSum(M, ri)) + '，' + no(4) + '分母是「' + C + '」的合計 ' + T(colSum(M, ci)) + '，兩題的分子都是同一格的 ' + T(M[ri][ci]) + '。',
             p: { M: M, ri: ri, ci: ci, ans: [fp(a1), fp(a2), fp(a3), fp(a4)] } };
  };
  function PTx(e) { return 'P(' + e + ')'; }

  /* ── §1 機率的基本性質 ── */
  var EXPS = ['A\\cap B', 'A\\cup B', "A\\cap B'", "A'\\cap B", "A'\\cap B'", "A'\\cup B'"];
  function atoms(m) { return { 'A': m[0] + m[1], 'B': m[0] + m[2] }; }
  /* 由四塊機率 m=[A∩B, A∩B', A'∩B, A'∩B'] 算集合運算式 */
  function evalSet(e, m) {
    var S = { 'A': [1, 1, 0, 0], "A'": [0, 0, 1, 1], 'B': [1, 0, 1, 0], "B'": [0, 1, 0, 1] };
    var ps = e.split(/\\cap|\\cup/), op = e.indexOf('\\cup') >= 0 ? 'u' : 'i';
    var v = S[ps[0].trim()].slice(), i, k;
    for (k = 1; k < ps.length; k++) {
      var w = S[ps[k].trim()];
      for (i = 0; i < 4; i++) v[i] = (op === 'u') ? (v[i] || w[i] ? 1 : 0) : (v[i] && w[i] ? 1 : 0);
    }
    var s = F(0);
    for (i = 0; i < 4; i++) if (v[i]) s = Fr.add(s, m[i]);
    return s;
  }
  function evalTarget(e, m) {
    var k = e.indexOf('\\mid');
    if (k < 0) return evalSet(e, m);
    var num = e.slice(0, k), con = e.slice(k + 4);     /* P(X|Y)=P(X∩Y)/P(Y) */
    return Fr.div(evalSet(num + '\\cap' + con, m), evalSet(con, m));
  }
  /* 四塊機率：以 P(A)=a、P(B)=b、P(A∩B)=x 決定 */
  function mkM(a, b, x) { return [x, Fr.sub(a, x), Fr.sub(b, x), Fr.add(Fr.sub(Fr.sub(F(1), a), b), x)]; }
  function okM(m) { var i; for (i = 0; i < 4; i++) if (m[i].n <= 0) return false; return true; }

  function decOK(f) { var d = f.d; while (d % 2 === 0) d /= 2; while (d % 5 === 0) d /= 5; return d === 1; }
  function shw(f, useDec) { return (useDec && decOK(f)) ? dec(f.n / f.d) : Fr.tex(f); }
  /* 隨機四塊機率（都是正的、分母整齊） */
  function randM(r) {
    var D = r.pick([10, 20, 5, 4, 100, 25, 8, 50, 40]), m, i, t = 0;
    do {
      m = [r.int(1, D - 3), r.int(1, D - 3), r.int(1, D - 3), 0];
      m[3] = D - m[0] - m[1] - m[2]; t++;
    } while (m[3] <= 0 && t < 200);
    if (m[3] <= 0) m = [D - 3, 1, 1, 1];
    var out = [];
    for (i = 0; i < 4; i++) out.push(F(m[i], D));
    return out;
  }
  function factLine(e, v, useDec) { return T(PTx(e) + '=' + shw(v, useDec)); }

  /* ── §1 機率的基本性質：由兩三個已知推其餘 ── */
  L1.probRules = function (r) {
    var m = randM(r), useDec = r() < 0.5;
    var giv = r.pick([['A', 'B', 'A\\cap B'], ['A', 'B', 'A\\cup B'], ['A', 'B', "A'\\cap B'"], ['A', 'B', "A\\cap B'"]]);
    var pool = ['A\\cap B', 'A\\cup B', "A\\cap B'", "A'\\cap B", "A'\\cap B'", "A'\\cup B'"];
    var tg = r.shuffle(pool.filter(function (e) { return giv.indexOf(e) < 0; })).slice(0, 3);
    var gv = giv.map(function (e) { return evalTarget(e, m); });
    var av = tg.map(function (e) { return evalTarget(e, m); });
    return { q: '設 ' + T('A') + '、' + T('B') + ' 為樣本空間 ' + T('S') + ' 中的兩個事件，已知 ' + giv.map(function (e, i) { return factLine(e, gv[i], useDec); }).join('、') + '。求下列各值（化為最簡分數）：' + tg.map(function (e, i) { return no(i + 1) + T(PTx(e)); }).join('　') + '。',
             a: jo(tg.map(function (e, i) { return no(i + 1) + ansEq(PTx(e), av[i]); })),
             h: '把樣本空間切成四塊：' + T(PTx('A\\cap B')) + '、' + T(PTx("A\\cap B'")) + '、' + T(PTx("A'\\cap B")) + '、' + T(PTx("A'\\cap B'")) + '，四塊相加為 ' + T(1) + '。本題由已知先解出 ' + T(PTx('A\\cap B') + '=' + Fr.tex(m[0])) + '，其餘三塊依序是 ' + T(Fr.tex(m[1])) + '、' + T(Fr.tex(m[2])) + '、' + T(Fr.tex(m[3])) + '，要哪一個就把對應的幾塊加起來。',
             p: { m: m.map(fp), giv: giv, tg: tg, ans: av.map(fp) } };
  };

  /* ── §2 條件機率：骰子（直接數縮小後的樣本空間） ── */
  L1.condDice = function (r) {
    var two = r() < 0.55, eA, eB, nB, nAB, t = 0, i, a, b;
    if (!two) {
      do { eA = dieEv1(r); eB = dieEv1(r); nB = 0; nAB = 0;
           for (i = 1; i <= 6; i++) { if (eB.f(i)) { nB++; if (eA.f(i)) nAB++; } } t++;
      } while ((nB < 3 || nAB === 0 || nAB === nB || eA.t === eB.t) && t < 300);
      var lst = [];
      for (i = 1; i <= 6; i++) if (eB.f(i)) lst.push(i);
      var ansS = F(nAB, nB);
      return { q: '擲一顆公正骰子。已知「' + eB.t + '」，求「' + eA.t + '」的機率。',
               a: T(Fr.tex(ansS)),
               h: '「已知」只做一件事：把樣本空間換掉。滿足「' + eB.t + '」的結果是 ' + T('\\{' + lst.join(',') + '\\}') + ' 共 ' + T(nB) + ' 個，其中同時滿足「' + eA.t + '」的有 ' + T(nAB) + ' 個 ⟹ 分母改成 ' + T(nB) + ' 而不是 ' + T(6) + '。',
               p: { kind: 0, eA: eA.t, eB: eB.t, nB: nB, nAB: nAB, ans: fp(ansS) } };
    }
    do { eA = dieEv2(r); eB = dieEv2(r); nB = 0; nAB = 0;
         for (a = 1; a <= 6; a++) for (b = 1; b <= 6; b++) if (eB.f(a, b)) { nB++; if (eA.f(a, b)) nAB++; }
         t++;
    } while ((nB < 4 || nAB === 0 || nAB === nB || eA.t === eB.t) && t < 400);
    var ans2 = F(nAB, nB);
    return { q: '擲兩顆公正骰子（視為可分辨的兩顆）。已知「' + eB.t + '」，求「' + eA.t + '」的機率。',
             a: T(Fr.tex(ans2)),
             h: '全部 ' + T('6\\times6=36') + ' 種有序結果；滿足「' + eB.t + '」的有 ' + T(nB) + ' 種，這 ' + T(nB) + ' 種就是新的樣本空間，其中同時滿足「' + eA.t + '」的有 ' + T(nAB) + ' 種 ⟹ ' + T(PTx('A\\mid B') + '=\\dfrac{n(A\\cap B)}{n(B)}') + '。',
             p: { kind: 1, eA: eA.t, eB: eB.t, nB: nB, nAB: nAB, ans: fp(ans2) } };
  };

  /* ── §2 用公式算條件機率 ── */
  L1.condFormula = function (r) {
    var m = randM(r), useDec = r() < 0.5;
    var giv = r.pick([['A', 'B', 'A\\cap B'], ['A', 'B', 'A\\cup B'], ['A', 'B', "A'\\cap B'"]]);
    var pool = ['A\\mid B', 'B\\mid A', "A'\\mid B", "A\\mid B'", "B\\mid A'", "B'\\mid A"];
    var tg = r.shuffle(pool).slice(0, 4);
    var gv = giv.map(function (e) { return evalTarget(e, m); });
    var av = tg.map(function (e) { return evalTarget(e, m); });
    return { q: '設 ' + T('A') + '、' + T('B') + ' 為兩事件，已知 ' + giv.map(function (e, i) { return factLine(e, gv[i], useDec); }).join('、') + '。求 ' + tg.map(function (e, i) { return no(i + 1) + T(PTx(e)); }).join('　') + '。',
             a: jo(tg.map(function (e, i) { return no(i + 1) + ansEq(PTx(e), av[i]); })),
             h: '先把四塊算出來：' + T(PTx('A\\cap B') + '=' + Fr.tex(m[0])) + '、' + T(PTx("A\\cap B'") + '=' + Fr.tex(m[1])) + '、' + T(PTx("A'\\cap B") + '=' + Fr.tex(m[2])) + '、' + T(PTx("A'\\cap B'") + '=' + Fr.tex(m[3])) + '。條件機率 ' + T(PTx('X\\mid Y') + '=\\dfrac{' + PTx('X\\cap Y') + '}{' + PTx('Y') + '}') + '，直線後面的才是分母；注意 ' + T(PTx("A\\mid B'")) + ' 不能寫成 ' + T('1-' + PTx('A\\mid B')) + '。',
             p: { m: m.map(fp), giv: giv, tg: tg, ans: av.map(fp) } };
  };

  /* ── §2 從列聯表讀條件機率（兩個方向對照） ── */
  L1.condTable = function (r) {
    var tb = r.pick(TB), M = [[r.int(20, 260), r.int(20, 260)], [r.int(20, 260), r.int(20, 260)]];
    var ri = r.int(0, 1), ci = r.int(0, 1), N = rowSum(M, 0) + rowSum(M, 1);
    var R = tb.r[ri], C = tb.c[ci], R2 = tb.r[1 - ri];
    var a1 = F(M[ri][ci], rowSum(M, ri)), a2 = F(M[ri][ci], colSum(M, ci)), a3 = F(M[1 - ri][ci], rowSum(M, 1 - ri));
    var a4 = Fr.div(a1, a3);
    return { q: tabHead(tb, M) + tb.one + '，求' + no(1) + T(PTx(tx(C) + '\\mid' + tx(R))) + '　' + no(2) + T(PTx(tx(R) + '\\mid' + tx(C))) + '　' + no(3) + T(PTx(tx(C) + '\\mid' + tx(R2))) + '　' + no(4) + '求比值 ' + T('\\dfrac{' + PTx(tx(C) + '\\mid' + tx(R)) + '}{' + PTx(tx(C) + '\\mid' + tx(R2)) + '}') + '。',
             a: jo([no(1) + T(Fr.tex(a1)), no(2) + T(Fr.tex(a2)), no(3) + T(Fr.tex(a3)), no(4) + T(Fr.tex(a4))]),
             h: '同樣兩個字順序一換分母就不同：' + no(1) + '分母是「' + R + '」的合計 ' + T(rowSum(M, ri)) + '，' + no(2) + '分母是「' + C + '」的合計 ' + T(colSum(M, ci)) + '，分子都是同一格的 ' + T(M[ri][ci]) + '。' + no(4) + '要比「風險」就得比兩個條件機率，不能拿 ' + T(M[ri][ci]) + ' 與 ' + T(M[1 - ri][ci]) + ' 直接比，因為兩列的總數 ' + T(rowSum(M, ri)) + ' 與 ' + T(rowSum(M, 1 - ri)) + ' 不一樣。',
             p: { M: M, ri: ri, ci: ci, N: N, ans: [fp(a1), fp(a2), fp(a3), fp(a4)] } };
  };

  /* ── §2 乘法公式 ── */
  L1.multRule = function (r) {
    var m = randM(r), useDec = r() < 0.5;
    var giv = ['A', 'B\\mid A', 'B'];
    var tg = r.shuffle(['A\\cap B', "A\\cap B'", 'A\\mid B', "A'\\cap B"]).slice(0, 3);
    var gv = giv.map(function (e) { return evalTarget(e, m); });
    var av = tg.map(function (e) { return evalTarget(e, m); });
    var ctx = r.pick([['某班學生', '有手機', '用甲廠牌'], ['某社區住戶', '有訂報', '訂甲報'], ['某校學生', '住校', '有腳踏車'], ['某公司員工', '開車上班', '有停車位']]);
    return { q: '（乘法公式：' + T(PTx('A\\cap B') + '=' + PTx('A') + '\\cdot ' + PTx('B\\mid A')) + '）設 ' + T('A') + ' 表「' + ctx[0] + '中' + ctx[1] + '」、' + T('B') + ' 表「' + ctx[2] + '」，已知 ' + giv.map(function (e, i) { return factLine(e, gv[i], useDec); }).join('、') + '。求 ' + tg.map(function (e, i) { return no(i + 1) + T(PTx(e)); }).join('　') + '。',
             a: jo(tg.map(function (e, i) { return no(i + 1) + ansEq(PTx(e), av[i]); })),
             h: '乘法公式是把 ' + T(PTx('B\\mid A') + '=\\dfrac{' + PTx('A\\cap B') + '}{' + PTx('A') + '}') + ' 兩邊乘 ' + T(PTx('A')) + '：本題 ' + T(PTx('A\\cap B') + '=' + prodF([gv[0], gv[1]]) + '=' + Fr.tex(m[0])) + '。再用 ' + T(PTx("A\\cap B'") + '=' + PTx('A') + '-' + PTx('A\\cap B')) + ' 與 ' + T(PTx("A'\\cap B") + '=' + PTx('B') + '-' + PTx('A\\cap B')) + ' 補完四塊。',
             p: { m: m.map(fp), giv: giv, tg: tg, ans: av.map(fp) } };
  };

  /* ── §2 已知條件機率反求其他機率 ── */
  L1.condInverse = function (r) {
    var m, t = 0, useDec = r() < 0.4;
    do { m = randM(r); t++; } while ((m[0].n === 0) && t < 50);
    var giv = r.pick([['A', 'B\\mid A', 'A\\mid B'], ['B', 'A\\mid B', 'B\\mid A'], ['A', 'A\\mid B', 'B\\mid A']]);
    var tg = r.shuffle(['A\\cap B', 'A\\cup B', "A'\\cap B'", "A\\mid B'", 'B', 'A']).filter(function (e) { return giv.indexOf(e) < 0; }).slice(0, 3);
    var gv = giv.map(function (e) { return evalTarget(e, m); });
    var av = tg.map(function (e) { return evalTarget(e, m); });
    return { q: '設 ' + T('A') + '、' + T('B') + ' 為兩事件，已知 ' + giv.map(function (e, i) { return factLine(e, gv[i], useDec); }).join('、') + '。求 ' + tg.map(function (e, i) { return no(i + 1) + T(PTx(e)); }).join('　') + '。',
             a: jo(tg.map(function (e, i) { return no(i + 1) + ansEq(PTx(e), av[i]); })),
             h: '先用乘法版求交集：' + T(PTx('A\\cap B') + '=' + Fr.tex(m[0])) + '；再用除法版把另一個邊際機率反解出來（' + T(PTx('B') + '=' + Fr.tex(Fr.add(m[0], m[2]))) + '、' + T(PTx('A') + '=' + Fr.tex(Fr.add(m[0], m[1]))) + '）。最後四塊是 ' + T(Fr.tex(m[0])) + '、' + T(Fr.tex(m[1])) + '、' + T(Fr.tex(m[2])) + '、' + T(Fr.tex(m[3])) + '。',
             p: { m: m.map(fp), giv: giv, tg: tg, ans: av.map(fp) } };
  };

  /* ── §2 放回與不放回 ── */
  L1.drawBalls = function (r) {
    var bg = r.pick(BAG), back = r() < 0.5, a = r.int(2, 7), b = r.int(2, 7), n = a + b;
    var c1 = bg.c[0], c2 = bg.c[1];
    var p1, p2, p3, p4;
    if (back) {
      var p = F(a, n);
      p1 = Fr.mul(p, p);
      p2 = Fr.mul(F(2), Fr.mul(p, Fr.cp(p)));
      p3 = p; p4 = p;
    } else {
      p1 = Fr.mul(F(a, n), F(a - 1, n - 1));
      p2 = Fr.mul(F(2), Fr.mul(F(a, n), F(b, n - 1)));
      p3 = F(a, n);
      p4 = F(a - 1, n - 1);
    }
    return { q: bg.b + '中有 ' + T(a) + ' 顆' + c1 + bg.o + '與 ' + T(b) + ' 顆' + c2 + bg.o + '，連續抽取兩次，' + (back ? '每次抽完都放回' : '抽完不放回') + '。求' + no(1) + '兩次都是' + c1 + bg.o + '　' + no(2) + '恰有一次是' + c1 + bg.o + '　' + no(3) + '第二次是' + c1 + bg.o + '　' + no(4) + '已知第一次是' + c1 + bg.o + '，第二次也是' + c1 + bg.o + ' 的機率。',
             a: jo([no(1) + T(Fr.tex(p1)), no(2) + T(Fr.tex(p2)), no(3) + T(Fr.tex(p3)), no(4) + T(Fr.tex(p4))]),
             h: (back ? bg.b + '的狀態每次都一樣，兩次互相獨立：每次抽到' + c1 + bg.o + '的機率都是 ' + T(Fr.tex(F(a, n))) + '，' + no(1) + '直接相乘、' + no(4) + '就等於 ' + no(3) + '。'
                      : '第一次抽走一顆後只剩 ' + T(n - 1) + ' 顆：' + no(1) + T(prodF([F(a, n), F(a - 1, n - 1)])) + '；' + no(3) + '把「第一次' + c1 + '」與「第一次' + c2 + '」兩條路加起來 ' + T(prodF([F(a, n), F(a - 1, n - 1)]) + '+' + prodF([F(b, n), F(a, n - 1)])) + '，會發現答案仍是 ' + T(Fr.tex(F(a, n))) + '。')
                + no(2) + '「恰一次」有兩種順序，記得乘 ' + T(2) + '。',
             p: { a: a, b: b, back: back ? 1 : 0, ans: [fp(p1), fp(p2), fp(p3), fp(p4)] } };
  };

  /* ── §2 三層樹狀圖：依序抽籤不放回 ── */
  L1.treeThree = function (r) {
    var w = r.int(2, 4), l = r.int(2, 5), n = w + l;
    var nm = r.pick([['甲', '乙', '丙'], ['小文', '阿遠', '小美'], ['第一位', '第二位', '第三位']]);
    var ctx = r.pick([{ o: '籤', y: '中獎', x: '沒中獎', c: '籤筒' }, { o: '球', y: '紅球', x: '白球', c: '袋子' }, { o: '卡片', y: '有獎', x: '沒有獎', c: '卡堆' }]);
    var P1 = Fr.mul(F(w, n), Fr.mul(F(l, n - 1), F(l - 1, n - 2)));                     /* 只有第一位中 */
    var P2 = Fr.mul(F(3), P1);                                                          /* 恰一人中（對稱） */
    var P3 = F(w, n);                                                                   /* 第二位中 */
    var P4 = Fr.mul(F(w, n), Fr.mul(F(w - 1, n - 1), F(w - 2, n - 2)));                 /* 三人都中 */
    return { q: ctx.c + '中原有 ' + T(w) + ' ' + (ctx.o === '籤' ? '張' : '顆') + '「' + ctx.y + '」與 ' + T(l) + ' ' + (ctx.o === '籤' ? '張' : '顆') + '「' + ctx.x + '」的' + ctx.o + '，' + nm.join('、') + ' 依序各抽一' + (ctx.o === '籤' ? '張' : '顆') + '且抽後不放回。求' + no(1) + '只有 ' + nm[0] + ' 抽到「' + ctx.y + '」　' + no(2) + '恰有一人抽到「' + ctx.y + '」　' + no(3) + nm[1] + ' 抽到「' + ctx.y + '」　' + no(4) + '三人都抽到「' + ctx.y + '」的機率。',
             a: jo([no(1) + T(Fr.tex(P1)), no(2) + T(Fr.tex(P2)), no(3) + T(Fr.tex(P3)), no(4) + T(Fr.tex(P4))]),
             h: '沿一條路徑相乘就是那條路徑的機率：' + no(1) + T(prodF([F(w, n), F(l, n - 1), F(l - 1, n - 2)])) + '。' + no(2) + '中獎的人可以是三人中任一位，三條路徑的機率相同 ⟹ 乘 ' + T(3) + '。' + no(3) + '把「' + nm[0] + '中、' + nm[1] + '中」與「' + nm[0] + '沒中、' + nm[1] + '中」兩條路加起來，結果和第一位一樣是 ' + T(Fr.tex(F(w, n))) + '——先抽後抽一樣公平。',
             p: { w: w, l: l, ans: [fp(P1), fp(P2), fp(P3), fp(P4)] } };
  };

  /* ── §2 縮小樣本空間：撲克牌與小孩 ── */
  /* 花色 0 紅心 1 方塊 2 黑桃 3 梅花；點數 1（A）～13（K） */
  var CARD_B = [{ t: '抽到的是紅色的牌', f: function (s, v) { return s < 2; } },
                { t: '抽到的是花牌（J、Q、K）', f: function (s, v) { return v >= 11 && v <= 13; } },
                { t: '抽到的是黑色的牌', f: function (s, v) { return s >= 2; } },
                { t: '抽到的點數大於 $9$（J、Q、K 分別視為 $11$、$12$、$13$）', f: function (s, v) { return v > 9; } },
                { t: '抽到的不是花牌', f: function (s, v) { return v < 11; } },
                { t: '抽到的點數是偶數', f: function (s, v) { return v % 2 === 0; } },
                { t: '抽到的點數不超過 $7$（A 視為 $1$）', f: function (s, v) { return v <= 7; } },
                { t: '抽到的是紅心或黑桃', f: function (s, v) { return s === 0 || s === 2; } },
                { t: '抽到的點數是 $3$ 的倍數', f: function (s, v) { return v % 3 === 0; } }];
  var CARD_A = [{ t: '這張牌是 K', f: function (s, v) { return v === 13; } },
                { t: '這張牌是紅心', f: function (s, v) { return s === 0; } },
                { t: '這張牌是黑桃', f: function (s, v) { return s === 2; } },
                { t: '這張牌是紅色的', f: function (s, v) { return s < 2; } },
                { t: '這張牌的點數小於 $5$（A 視為 $1$）', f: function (s, v) { return v < 5; } },
                { t: '這張牌是花牌（J、Q、K）', f: function (s, v) { return v >= 11 && v <= 13; } },
                { t: '這張牌是 A', f: function (s, v) { return v === 1; } },
                { t: '這張牌的點數是偶數', f: function (s, v) { return v % 2 === 0; } },
                { t: '這張牌是梅花', f: function (s, v) { return s === 3; } },
                { t: '這張牌的點數大於 $10$', f: function (s, v) { return v > 10; } }];
  L1.cardKids = function (r) {
    if (r() < 0.55) {
      var eA, eB, nB, nAB, s, v, t = 0;
      do {
        eA = r.pick(CARD_A); eB = r.pick(CARD_B); nB = 0; nAB = 0;
        for (s = 0; s < 4; s++) for (v = 1; v <= 13; v++) if (eB.f(s, v)) { nB++; if (eA.f(s, v)) nAB++; }
        t++;
      } while ((nAB === 0 || nAB === nB) && t < 200);
      var an = F(nAB, nB);
      return { q: '從一副 ' + T(52) + ' 張撲克牌中任抽一張。已知' + eB.t + '，求' + eA.t + ' 的機率。',
               a: T(Fr.tex(an)),
               h: '不必用公式，直接數新的樣本空間：符合「' + eB.t + '」的牌共 ' + T(nB) + ' 張，這 ' + T(nB) + ' 張就是新的分母；其中還符合「' + eA.t + '」的有 ' + T(nAB) + ' 張。',
               p: { kind: 0, eA: eA.t, eB: eB.t, nB: nB, nAB: nAB, ans: fp(an) } };
    }
    var k = r.int(2, 4), g = r.pick([['男孩', '女孩'], ['女孩', '男孩']]);
    var least = r.int(1, Math.min(2, k - 1));
    var allSame = r() < 0.5;   /* 目標：全部同一性別，或恰有 least 個 */
    var tot = Math.pow(2, k), nB = 0, nAB = 0, i, j, c;
    for (i = 0; i < tot; i++) {
      c = 0; for (j = 0; j < k; j++) if ((i >> j) & 1) c++;
      if (c >= least) { nB++; if (allSame ? (c === k) : (c === least)) nAB++; }
    }
    var an2 = F(nAB, nB);
    return { q: '某家庭有 ' + T(k) + ' 個小孩（每個小孩是' + g[0] + '或' + g[1] + '的機率相同且互相獨立）。已知其中至少有 ' + T(least) + ' 個是' + g[0] + '，求' + (allSame ? T(k) + ' 個都是' + g[0] : '恰有 ' + T(least) + ' 個是' + g[0]) + ' 的機率。',
             a: T(Fr.tex(an2)),
             h: '把 ' + T(k) + ' 個小孩的性別依出生順序排成一列，樣本空間有 ' + T('2^' + k + '=' + tot) + ' 種（' + g[0] + g[1] + '與' + g[1] + g[0] + '要算成兩種）。「至少 ' + T(least) + ' 個' + g[0] + '」有 ' + T(nB) + ' 種 ⟹ 分母不再是 ' + T(tot) + '；其中符合所求的有 ' + T(nAB) + ' 種。',
             p: { kind: 1, k: k, least: least, allSame: allSame ? 1 : 0, ans: fp(an2) } };
  };

  /* ── §3 判斷兩事件是否獨立 ── */
  L1.indepCheck = function (r) {
    var kind = r.int(0, 2), indep = r() < 0.5, i;
    if (kind === 2) {
      var eA, eB, nA, nB, nAB, t = 0;
      do {
        eA = dieEv1(r); eB = dieEv1(r); nA = 0; nB = 0; nAB = 0;
        for (i = 1; i <= 6; i++) { if (eA.f(i)) nA++; if (eB.f(i)) nB++; if (eA.f(i) && eB.f(i)) nAB++; }
        t++;
      } while ((eA.t === eB.t || nA === 0 || nB === 0 || nA === 6 || nB === 6) && t < 300);
      var pA = F(nA, 6), pB = F(nB, 6), pAB = F(nAB, 6), pp = Fr.mul(pA, pB);
      var ok = Fr.eq(pAB, pp);
      return { q: '擲一顆公正骰子，設 ' + T('A') + ' 表「' + eA.t + '」、' + T('B') + ' 表「' + eB.t + '」。判斷 ' + T('A') + '、' + T('B') + ' 是否獨立，並寫出比較的三個機率。',
               a: (ok ? '獨立' : '不獨立') + '　' + ansEq(PTx('A'), pA) + '　' + ansEq(PTx('B'), pB) + '　' + ansEq(PTx('A\\cap B'), pAB) + '　' + ansEq(PTx('A') + PTx('B'), pp),
               h: '獨立的定義是 ' + T(PTx('A\\cap B') + '=' + PTx('A') + PTx('B')) + '。本題 ' + T('A') + ' 有 ' + T(nA) + ' 個結果、' + T('B') + ' 有 ' + T(nB) + ' 個、' + T('A\\cap B') + ' 有 ' + T(nAB) + ' 個，全部除以 ' + T(6) + ' 之後比一比 ' + T(Fr.tex(pAB)) + ' 與 ' + T(prodF([pA, pB])) + '。獨不獨立看數字湊不湊得起來，不是看意義像不像有關。',
               p: { kind: 2, eA: eA.t, eB: eB.t, indep: ok ? 1 : 0, ans: [fp(pA), fp(pB), fp(pAB), fp(pp)] } };
    }
    var D = r.pick([10, 20, 100, 5, 25, 50]), na = r.int(1, D - 1), nb = r.int(1, D - 1), a = F(na, D), b = F(nb, D), x;
    var t2 = 0;
    do {
      a = F(r.int(1, D - 1), D); b = F(r.int(1, D - 1), D);
      x = Fr.mul(a, b);
      if (!indep) x = Fr.add(x, F(r.pick([-3, -2, -1, 1, 2, 3]), D));
      t2++;
    } while ((x.n <= 0 || Fr.cmp(x, a) >= 0 || Fr.cmp(x, b) >= 0 || Fr.cmp(Fr.sub(Fr.add(a, b), x), F(1)) >= 0 || (indep && !decOK(x))) && t2 < 400);
    var m = mkM(a, b, x), pp2 = Fr.mul(a, b), ok2 = Fr.eq(x, pp2), useDec = r() < 0.5;
    var u = Fr.sub(Fr.add(a, b), x);
    var giv = (kind === 0) ? ['A', 'B', 'A\\cap B'] : ['A', 'B', 'A\\cup B'];
    var gv = [a, b, (kind === 0) ? x : u];
    return { q: '設 ' + T('A') + '、' + T('B') + ' 為兩事件，已知 ' + giv.map(function (e, i2) { return factLine(e, gv[i2], useDec); }).join('、') + '。' + no(1) + '求 ' + T(PTx('A\\cap B')) + '　' + no(2) + '判斷 ' + T('A') + '、' + T('B') + ' 是否獨立，並寫出 ' + T(PTx('A') + PTx('B')) + ' 的值。',
             a: no(1) + ansEq(PTx('A\\cap B'), x) + '　' + no(2) + (ok2 ? '獨立' : '不獨立') + '，' + ansEq(PTx('A') + PTx('B'), pp2),
             h: (kind === 0 ? '已知就直接給了 ' + T(PTx('A\\cap B') + '=' + Fr.tex(x)) : '先由 ' + T(PTx('A\\cap B') + '=' + PTx('A') + '+' + PTx('B') + '-' + PTx('A\\cup B') + '=' + Fr.tex(a) + '+' + Fr.tex(b) + '-' + Fr.tex(u) + '=' + Fr.tex(x)) + '') + '。再算 ' + T(PTx('A') + PTx('B') + '=' + prodF([a, b]) + '=' + Fr.tex(pp2)) + '，和 ' + T(Fr.tex(x)) + ' 比一比：相等才叫獨立。',
             p: { kind: kind, m: m.map(fp), indep: ok2 ? 1 : 0, ans: [fp(x), fp(pp2)] } };
  };

  /* ── §3 獨立 vs 互斥 ── */
  function stTrue(id, a, b, v) {
    var ab = Fr.mul(a, b);
    switch (id) {
      case 0: return Fr.cmp(Fr.add(a, b), F(1)) <= 0;
      case 1: return true;
      case 2: return true;
      case 3: return Fr.eq(v, Fr.sub(Fr.add(a, b), ab));
      case 4: return Fr.cmp(Fr.add(a, b), F(1)) <= 0 && Fr.eq(v, Fr.add(a, b));
      case 5: return Fr.eq(v, a);
      case 6: return Fr.eq(v, F(0));
      case 7: return true;
      case 8: return Fr.eq(v, ab);
      default: return Fr.eq(a, b);
    }
  }
  function stText(id, a, b, v, useDec) {
    switch (id) {
      case 0: return T('A') + '、' + T('B') + ' 有可能互斥。';
      case 1: return T('A') + '、' + T('B') + ' 有可能獨立。';
      case 2: return '若 ' + T('A') + '、' + T('B') + ' 互斥，則 ' + T('A') + '、' + T('B') + ' 必不獨立。';
      case 3: return '若 ' + T('A') + '、' + T('B') + ' 獨立，則 ' + T(PTx('A\\cup B') + '=' + shw(v, useDec)) + '。';
      case 4: return '若 ' + T('A') + '、' + T('B') + ' 互斥，則 ' + T(PTx('A\\cup B') + '=' + shw(v, useDec)) + '。';
      case 5: return '若 ' + T('A') + '、' + T('B') + ' 獨立，則 ' + T(PTx('A\\mid B') + '=' + shw(v, useDec)) + '。';
      case 6: return '若 ' + T('A') + '、' + T('B') + ' 互斥，則 ' + T(PTx('A\\mid B') + '=' + shw(v, useDec)) + '。';
      case 7: return '若 ' + T('A') + '、' + T('B') + ' 獨立，則 ' + T("A'") + '、' + T("B'") + ' 亦獨立。';
      case 8: return '若 ' + T('A') + '、' + T('B') + ' 獨立，則 ' + T(PTx('A\\cap B') + '=' + shw(v, useDec)) + '。';
      default: return '若 ' + T('A') + '、' + T('B') + ' 獨立，則 ' + T(PTx('A\\mid B') + '=' + PTx('B\\mid A')) + '。';
    }
  }
  L1.indepVsExcl = function (r) {
    var D = r.pick([10, 20, 100, 5, 25]), a = F(r.int(1, D - 1), D), b = F(r.int(1, D - 1), D), useDec = r() < 0.5;
    var ab = Fr.mul(a, b), canX = Fr.cmp(Fr.add(a, b), F(1)) <= 0;
    /* 「若互斥，則…」只在互斥有可能時才出（否則前提不可能成立，真假難定） */
    var pool = canX ? [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : [0, 1, 2, 3, 5, 7, 8, 9];
    var ids = r.shuffle(pool).slice(0, 4), vs = [], ok = [], i;
    for (i = 0; i < ids.length; i++) {
      var id = ids[i], v = F(0), tr = r() < 0.5;
      if (id === 3) v = tr ? Fr.sub(Fr.add(a, b), ab) : Fr.add(a, b);
      else if (id === 4) v = tr ? Fr.add(a, b) : Fr.sub(Fr.add(a, b), ab);
      else if (id === 5) v = tr ? a : b;
      else if (id === 6) v = tr ? F(0) : a;
      else if (id === 8) v = tr ? ab : Fr.sub(Fr.add(a, b), ab);
      vs.push(v); ok.push(stTrue(id, a, b, v));
    }
    return { q: '設 ' + T('A') + '、' + T('B') + ' 為樣本空間中的兩事件，' + factLine('A', a, useDec) + '、' + factLine('B', b, useDec) + '（兩者機率都不為 ' + T(0) + '）。判斷下列各敘述的真假：' + ids.map(function (id, i2) { return no(i2 + 1) + stText(id, a, b, vs[i2], useDec); }).join(''),
             a: jo(ok.map(function (t2, i2) { return no(i2 + 1) + (t2 ? '真' : '假'); })),
             h: '三件事要分清楚：互斥是 ' + T(PTx('A\\cap B') + '=0') + '、獨立是 ' + T(PTx('A\\cap B') + '=' + PTx('A') + PTx('B') + '=' + Fr.tex(ab)) + '；機率都不為 ' + T(0) + ' 時兩者不可能同時成立。本題 ' + T(PTx('A') + '+' + PTx('B') + '=' + Fr.tex(Fr.add(a, b))) + '（' + (Fr.cmp(Fr.add(a, b), F(1)) <= 0 ? '不超過' : '超過') + ' ' + T(1) + ' ⟹ ' + (Fr.cmp(Fr.add(a, b), F(1)) <= 0 ? '可以' : '不可能') + '互斥）；獨立時 ' + T(PTx('A\\cup B') + '=' + Fr.tex(Fr.sub(Fr.add(a, b), ab))) + '、' + T(PTx('A\\mid B') + '=' + Fr.tex(a)) + '，互斥時 ' + T(PTx('A\\mid B') + '=0') + '。',
             p: { a: fp(a), b: fp(b), ids: ids, vs: vs.map(fp), ans: ok.map(function (t2) { return t2 ? 1 : 0; }) } };
  };

  /* ── §3 從列聯表判斷獨立 ── */
  L1.indepTable = function (r) {
    var tb = r.pick(TB), indep = r() < 0.5, M, t = 0;
    do {
      if (indep) {
        var k1 = r.int(2, 12), k2 = r.int(2, 12), s1 = r.int(3, 16), s2 = r.int(3, 16);
        M = [[k1 * s1, k1 * s2], [k2 * s1, k2 * s2]];
      } else {
        M = [[r.int(20, 220), r.int(20, 220)], [r.int(20, 220), r.int(20, 220)]];
      }
      t++;
    } while ((M[0][0] * M[1][1] === M[0][1] * M[1][0]) !== indep && t < 200);
    var ri = r.int(0, 1), ci = r.int(0, 1);
    var a1 = F(M[ri][ci], rowSum(M, ri)), a2 = F(M[1 - ri][ci], rowSum(M, 1 - ri)), a3 = F(colSum(M, ci), rowSum(M, 0) + rowSum(M, 1));
    var ad = M[0][0] * M[1][1], bc = M[0][1] * M[1][0];
    return { q: tabHead(tb, M) + no(1) + '求 ' + T(PTx(tx(tb.c[ci]) + '\\mid' + tx(tb.r[ri]))) + ' 與 ' + T(PTx(tx(tb.c[ci]) + '\\mid' + tx(tb.r[1 - ri]))) + '　' + no(2) + '用交叉相乘判斷「' + tb.r[0] + '／' + tb.r[1] + '」與「' + tb.c[0] + '／' + tb.c[1] + '」是否獨立。',
             a: no(1) + T(Fr.tex(a1)) + '、' + T(Fr.tex(a2)) + '　' + no(2) + (indep ? '獨立' : '不獨立') + '，' + T(M[0][0] + '\\times' + M[1][1] + '=' + ad) + '、' + T(M[0][1] + '\\times' + M[1][0] + '=' + bc),
             h: '兩列的內部比例一樣就是獨立。' + no(1) + '兩個條件機率的分母分別是該列的合計 ' + T(rowSum(M, ri)) + ' 與 ' + T(rowSum(M, 1 - ri)) + '，' + T(PTx(tx(tb.c[ci])) + '=' + Fr.tex(a3)) + ' 可以一起比。' + no(2) + '四格寫成 ' + T('\\begin{matrix}a&b\\\\c&d\\end{matrix}') + ' 時，獨立的充要條件是 ' + T('ad=bc') + '：本題 ' + T(ad) + ' 與 ' + T(bc) + '。',
             p: { M: M, ri: ri, ci: ci, indep: indep ? 1 : 0, ans: [fp(a1), fp(a2)] } };
  };

  /* ── §3 重複試驗：恰有幾次成功 ── */
  L1.repeatTrial = function (r) {
    var sc = r.pick(RT), p = r.pick([F(1, 2), F(1, 3), F(2, 3), F(1, 4), F(3, 4), F(2, 5), F(3, 5), F(1, 5), F(1, 6), F(5, 6)]);
    var n = r.int(4, 7), k = r.int(1, n - 1), q = Fr.cp(p);
    var A1 = Fr.pow(p, n), A2 = binP(n, k, p), A3 = Fr.add(binP(n, n, p), binP(n, n - 1, p)), A4 = Fr.add(binP(n, 0, p), binP(n, 1, p));
    return { q: sc.s + '「' + sc.y + '」的機率為 ' + T(Fr.tex(p)) + '，且各次互相獨立。一共' + sc.vb + ' ' + T(n) + ' ' + sc.u + '，求' + no(1) + '全部都「' + sc.y + '」　' + no(2) + '恰好有 ' + T(k) + ' ' + sc.u + '「' + sc.y + '」　' + no(3) + '至少有 ' + T(n - 1) + ' ' + sc.u + '「' + sc.y + '」　' + no(4) + '至多有 ' + T(1) + ' ' + sc.u + '「' + sc.y + '」的機率。',
             a: jo([no(1) + T(Fr.tex(A1)), no(2) + T(Fr.tex(A2)), no(3) + T(Fr.tex(A3)), no(4) + T(Fr.tex(A4))]),
             h: '先問「哪幾次成功」再乘機率：恰 ' + T(k) + ' 次是 ' + T(binTex(n, k, Fr.tex(p), Fr.tex(q))) + '，其中 ' + T(CT(n, k) + '=' + nCr(n, k)) + ' 是「挑哪 ' + T(k) + ' 次成功」的方法數。' + no(3) + '＝恰 ' + T(n) + ' 次 ' + T('+') + ' 恰 ' + T(n - 1) + ' 次；' + no(4) + '＝恰 ' + T(0) + ' 次 ' + T('+') + ' 恰 ' + T(1) + ' 次，失敗一次的機率是 ' + T(Fr.tex(q)) + '。',
             p: { n: n, k: k, p: fp(p), ans: [fp(A1), fp(A2), fp(A3), fp(A4)] } };
  };

  /* ── §3 至少一次 ── */
  L1.atLeastOne = function (r) {
    var sc = r.pick(RT), p = r.pick([F(1, 6), F(1, 5), F(1, 4), F(1, 3), F(1, 2), F(2, 5), F(1, 10), F(3, 10), F(1, 20), F(2, 3)]);
    var n = r.int(3, 6), q = Fr.cp(p);
    var A1 = Fr.pow(q, n), A2 = Fr.cp(A1), A3 = Fr.sub(A2, binP(n, 1, p));
    return { q: sc.s + '「' + sc.y + '」的機率為 ' + T(Fr.tex(p)) + '，各次互相獨立，共' + sc.vb + ' ' + T(n) + ' ' + sc.u + '。求' + no(1) + '一次也沒有「' + sc.y + '」　' + no(2) + '至少有一' + sc.u + '「' + sc.y + '」　' + no(3) + '至少有兩' + sc.u + '「' + sc.y + '」的機率。',
             a: jo([no(1) + T(Fr.tex(A1)), no(2) + T(Fr.tex(A2)), no(3) + T(Fr.tex(A3))]),
             h: '看到「至少」先寫反面：' + no(1) + T(pw(Fr.tex(q), n) + '=' + Fr.tex(A1)) + '，' + no(2) + T('1-' + pw(Fr.tex(q), n) + '=' + Fr.tex(A2)) + '。' + no(3) + '的反面是「' + T(0) + ' 次或恰 ' + T(1) + ' 次」，恰 ' + T(1) + ' 次是 ' + T(binTex(n, 1, Fr.tex(p), Fr.tex(q)) + '=' + Fr.tex(binP(n, 1, p))) + '。',
             p: { n: n, p: fp(p), ans: [fp(A1), fp(A2), fp(A3)] } };
  };

  /* ── §3 三個機率不同的獨立事件 ── */
  L1.threeIndep = function (r) {
    var nm = r.pick([['甲', '乙', '丙'], ['小文', '阿遠', '小美'], ['第一台機器', '第二台機器', '第三台機器']]);
    var act = r.pick([{ v: '解出一道題', y: '解出' }, { v: '射擊一次', y: '命中' }, { v: '投籃一次', y: '投進' }, { v: '各自抽一次獎', y: '抽中' }]);
    var ps = [], used = {}, cand = [F(1, 2), F(1, 3), F(2, 3), F(1, 4), F(3, 4), F(2, 5), F(3, 5), F(1, 5), F(4, 5), F(1, 6), F(5, 6), F(3, 10), F(7, 10)], i, f;
    while (ps.length < 3) { f = r.pick(cand); if (used[f.n + '/' + f.d]) continue; used[f.n + '/' + f.d] = 1; ps.push(f); }
    var qs = ps.map(Fr.cp);
    var all = Fr.mul(ps[0], Fr.mul(ps[1], ps[2]));
    var none = Fr.mul(qs[0], Fr.mul(qs[1], qs[2]));
    var atl = Fr.cp(none);
    var one = Fr.add(Fr.mul(ps[0], Fr.mul(qs[1], qs[2])), Fr.add(Fr.mul(qs[0], Fr.mul(ps[1], qs[2])), Fr.mul(qs[0], Fr.mul(qs[1], ps[2]))));
    return { q: nm.join('、') + ' 三者' + act.v + '，' + act.y + '的機率分別為 ' + ps.map(function (f2) { return T(Fr.tex(f2)); }).join('、') + '，且互相獨立。求' + no(1) + '三者都' + act.y + '　' + no(2) + '沒有人' + act.y + '　' + no(3) + '至少有一' + (nm[0].length > 1 ? '個' : '人') + act.y + '　' + no(4) + '恰有一' + (nm[0].length > 1 ? '個' : '人') + act.y + ' 的機率。',
             a: jo([no(1) + T(Fr.tex(all)), no(2) + T(Fr.tex(none)), no(3) + T(Fr.tex(atl)), no(4) + T(Fr.tex(one))]),
             h: '機率不同就不能用 ' + T('(1-p)^3') + '，要各自取反面再連乘：' + no(2) + T(prodF(qs) + '=' + Fr.tex(none)) + '，' + no(3) + T('1-' + Fr.tex(none) + '=' + Fr.tex(atl)) + '。' + no(4) + '要列三種情形（只有 ' + nm[0] + '、只有 ' + nm[1] + '、只有 ' + nm[2] + '）各自算完再相加，' + T('C^3_1') + ' 只在三人機率相同時才能用。',
             p: { ps: ps.map(fp), ans: [fp(all), fp(none), fp(atl), fp(one)] } };
  };

  /* ── §3 要試幾次才夠（常用對數） ── */
  var LOG2 = 0.3010, LOG3 = 0.4771;
  function lg(f) {   /* 只含 2、3、5 的有理數用查表值算 log */
    var n = f.n, d = f.d, v = 0, e;
    var fac = function (x, s) { var c = 0; while (x % 2 === 0) { x /= 2; c += s * LOG2; } while (x % 3 === 0) { x /= 3; c += s * LOG3; } while (x % 5 === 0) { x /= 5; c += s * (1 - LOG2); } return x === 1 ? c : null; };
    v = fac(n, 1); if (v === null) return null;
    e = fac(d, -1); if (e === null) return null;
    return v + e;
  }
  function need23(f) {  /* 回傳 [用到 log2, 用到 log3] */
    var n = f.n, d = f.d, u2 = false, u3 = false, g = function (x) { while (x % 2 === 0) { x /= 2; u2 = true; } while (x % 3 === 0) { x /= 3; u3 = true; } while (x % 5 === 0) { x /= 5; u2 = true; } };
    g(n); g(d); return [u2, u3];
  }
  L1.needTrials = function (r) {
    var sc = r.pick(RT), QS = [F(1, 2), F(2, 3), F(3, 4), F(4, 5), F(5, 6), F(9, 10), F(3, 5), F(8, 9), F(1, 4), F(2, 5), F(1, 3), F(5, 8), F(4, 9)];
    var TH = [F(1, 10), F(1, 100), F(1, 2), F(1, 5), F(1, 4), F(1, 20), F(3, 10), F(2, 5), F(1, 8), F(1, 1000)];
    var q1, th1, th2, n1, n2, t = 0, ok = false, p;
    while (t < 500 && !ok) {
      t++;
      q1 = r.pick(QS); p = Fr.cp(q1);
      th1 = r.pick(TH); th2 = r.pick(TH);
      if (Fr.eq(th1, th2)) continue;
      var x1 = Math.log(Fr.num(th1)) / Math.log(Fr.num(q1)), x2 = Math.log(Fr.num(th2)) / Math.log(Fr.num(q1));
      if (Math.abs(x1 - Math.round(x1)) < 0.08 || Math.abs(x2 - Math.round(x2)) < 0.08) continue;
      n1 = Math.floor(x1) + 1; n2 = Math.floor(x2) + 1;
      if (n1 < 2 || n2 < 2 || n1 > 40 || n2 > 40 || n1 === n2) continue;
      var l1 = lg(th1), l2 = lg(th2), lq = lg(q1);
      if (l1 === null || l2 === null || lq === null) continue;
      if (Math.floor(l1 / lq) + 1 !== n1 || Math.floor(l2 / lq) + 1 !== n2) continue;   /* 查表值也要給出同一個整數 */
      ok = true;
    }
    if (!ok) { q1 = F(5, 6); p = F(1, 6); th1 = F(1, 2); th2 = F(1, 10); n1 = 4; n2 = 13; }
    var u = need23(q1), u2 = need23(th1), u3 = need23(th2);
    var logs = [];
    if (u[0] || u2[0] || u3[0]) logs.push(T('\\log2\\approx' + LOG2.toFixed(4)));
    if (u[1] || u2[1] || u3[1]) logs.push(T('\\log3\\approx' + LOG3.toFixed(4)));
    var k1 = Fr.cp(th1), k2 = Fr.cp(th2);
    return { q: sc.s + '「' + sc.y + '」的機率為 ' + T(Fr.tex(p)) + '，各次互相獨立。' + no(1) + '至少要' + sc.vb + '幾' + sc.u + '，才能使「至少有一' + sc.u + sc.y + '」的機率大於 ' + T(Fr.tex(k1)) + '？' + no(2) + '若要讓這個機率大於 ' + T(Fr.tex(k2)) + '，至少要' + sc.vb + '幾' + sc.u + '？（' + logs.join('、') + '）',
             a: jo([no(1) + T(n1) + ' ' + sc.u, no(2) + T(n2) + ' ' + sc.u]),
             h: '列式 ' + T('1-' + pw(Fr.tex(q1), 'n') + '\\gt k') + ' ⟺ ' + T(pw(Fr.tex(q1), 'n') + '\\lt 1-k') + '，本題 ' + no(1) + '是 ' + T(par(Fr.tex(q1)) + '^n\\lt ' + Fr.tex(th1)) + '。兩邊取常用對數，因為 ' + T('\\log' + par(Fr.tex(q1)) + '\\lt 0') + '，除過去時不等號要變向 ⟹ ' + T('n\\gt\\dfrac{\\log' + par(Fr.tex(th1)) + '}{\\log' + par(Fr.tex(q1)) + '}') + '，再取大於它的最小整數；算完把 ' + T(n1) + ' 與 ' + T(n1 - 1) + ' 各代回去確認。',
             p: { q1: fp(q1), th1: fp(th1), th2: fp(th2), ans: [n1, n2] } };
  };

  /* ── §4 把所有路徑加起來 ── */
  L1.totalPath = function (r) {
    if (r() < 0.5) {
      var sc = r.pick(CS2), m = r.int(1, 7), n = r.int(1, 7), t = 0;
      while (m === n && t++ < 20) n = r.int(1, 7);
      var r1 = F(r.pick([1, 2, 3, 4, 5, 6, 8, 10]), 100), r2 = F(r.pick([1, 2, 3, 4, 5, 6, 8, 10, 12]), 100);
      var tz = 0;
      while (Fr.eq(r1, r2) && tz++ < 60) r2 = F(r.pick([1, 2, 3, 4, 5, 6, 8, 10, 12]), 100);
      if (Fr.eq(r1, r2)) r2 = Fr.add(r1, F(1, 100));
      var w1 = F(m, m + n), w2 = F(n, m + n);
      var A1 = Fr.add(Fr.mul(w1, r1), Fr.mul(w2, r2));
      var A2 = Fr.mul(F(1, 2), Fr.add(r1, r2));
      return { q: '某工廠的' + sc.a + '與' + sc.b + sc.w + '比為 ' + T(m + ':' + n) + '，' + sc.a + '產出「' + sc.y + '」的比率為 ' + T(pc(r1)) + '、' + sc.b + '為 ' + T(pc(r2)) + '。' + no(1) + '求' + sc.pick + '為「' + sc.y + '」的機率。' + no(2) + '若' + sc.w + '比改成 ' + T('1:1') + '（其他不變），這個機率會變成多少？',
               a: jo([no(1) + T(Fr.tex(A1)), no(2) + T(Fr.tex(A2))]),
               h: sc.w + '比要先化成機率：' + T(PTx(tx(sc.a)) + '=' + Fr.tex(w1)) + '、' + T(PTx(tx(sc.b)) + '=' + Fr.tex(w2)) + '（相加為 ' + T(1) + '）。兩條路各走一次再加起來：' + T(prodF([w1, r1]) + '+' + prodF([w2, r2]) + '=' + Fr.tex(A1)) + '。合理性檢查：答案一定落在 ' + T(Fr.tex(r1)) + ' 與 ' + T(Fr.tex(r2)) + ' 之間。',
               p: { kind: 0, m: m, n: n, r1: fp(r1), r2: fp(r2), ans: [fp(A1), fp(A2)] } };
    }
    var bg = r.pick(BAG), a1 = r.int(1, 5), b1 = r.int(1, 5), a2 = r.int(1, 5), b2 = r.int(1, 5);
    var tz = 0;
    while (a1 * (a2 + b2) === a2 * (a1 + b1) && tz++ < 60) { a2 = r.int(1, 5); b2 = r.int(1, 5); }
    if (a1 * (a2 + b2) === a2 * (a1 + b1)) { a2 = 1; b2 = 4; a1 = 3; b1 = 2; }
    var k = r.int(2, 5);                     /* 點數大於 k 用甲袋 */
    var wA = F(6 - k, 6), wB = F(k, 6);
    var q1 = F(a1, a1 + b1), q2 = F(a2, a2 + b2);
    var B1 = Fr.add(Fr.mul(wA, q1), Fr.mul(wB, q2));
    var B2 = Fr.add(Fr.mul(F(1, 6), q1), Fr.mul(F(5, 6), q2));
    return { q: '甲' + bg.b + '有 ' + T(a1) + ' 顆' + bg.c[0] + bg.o + '與 ' + T(b1) + ' 顆' + bg.c[1] + bg.o + '，乙' + bg.b + '有 ' + T(a2) + ' 顆' + bg.c[0] + bg.o + '與 ' + T(b2) + ' 顆' + bg.c[1] + bg.o + '。先擲一顆公正骰子：點數大於 ' + T(k) + ' 就從甲' + bg.b + '抽一顆，否則從乙' + bg.b + '抽一顆。' + no(1) + '求抽到' + bg.c[0] + bg.o + '的機率。' + no(2) + '若改成「點數為 ' + T(6) + ' 才從甲' + bg.b + '抽」，這個機率會變成多少？',
             a: jo([no(1) + T(Fr.tex(B1)), no(2) + T(Fr.tex(B2))]),
             h: '先算選到哪個' + bg.b + '的機率：點數大於 ' + T(k) + ' 有 ' + T(6 - k) + ' 種 ⟹ ' + T(PTx(tx('甲' + bg.b)) + '=' + Fr.tex(wA)) + '、' + T(PTx(tx('乙' + bg.b)) + '=' + Fr.tex(wB)) + '。兩條路徑加起來：' + T(prodF([wA, q1]) + '+' + prodF([wB, q2]) + '=' + Fr.tex(B1)) + '；甲' + bg.b + '的' + bg.c[0] + '球比例是 ' + T(Fr.tex(q1)) + '、乙' + bg.b + '是 ' + T(Fr.tex(q2)) + '，少走比例高的那一袋，機率就會往另一邊靠。',
             p: { kind: 1, a1: a1, b1: b1, a2: a2, b2: b2, k: k, ans: [fp(B1), fp(B2)] } };
  };

  /* ── §4 兩分支的貝氏 ── */
  L1.bayesTwo = function (r) {
    var sc = r.pick(CS2), wp = r.pick([50, 55, 60, 65, 70, 75, 80, 40, 30, 25, 20]);
    var w1 = F(wp, 100), w2 = Fr.cp(w1);
    var r1 = F(r.pick([1, 2, 3, 4, 5, 6, 8]), 100), r2 = F(r.pick([2, 3, 4, 5, 6, 8, 10, 12, 15]), 100);
    var tz2 = 0;
    while (Fr.eq(r1, r2) && tz2++ < 60) r2 = F(r.pick([2, 3, 4, 5, 6, 8, 10, 12, 15]), 100);
    if (Fr.eq(r1, r2)) r2 = Fr.add(r1, F(2, 100));
    var L1p = Fr.mul(w1, r1), L2p = Fr.mul(w2, r2), Py = Fr.add(L1p, L2p);
    var G1 = Fr.mul(w1, Fr.cp(r1)), G2 = Fr.mul(w2, Fr.cp(r2)), Pn = Fr.add(G1, G2);
    var A1 = Py, A2 = Fr.div(L1p, Py), A3 = Fr.div(G1, Pn);
    return { q: '某工廠的' + sc.a + '佔' + sc.w + ' ' + T(pc(w1)) + '、產出「' + sc.y + '」的比率為 ' + T(pc(r1)) + '；' + sc.b + '佔' + sc.w + ' ' + T(pc(w2)) + '、產出「' + sc.y + '」的比率為 ' + T(pc(r2)) + '。' + no(1) + '求' + sc.pick + '為「' + sc.y + '」的機率。' + no(2) + '已知取到一件「' + sc.y + '」，求它來自' + sc.a + '的機率。' + no(3) + '已知取到一件「' + sc.n + '」，求它來自' + sc.a + '的機率。',
             a: jo([no(1) + T(Fr.tex(A1)), no(2) + T(Fr.tex(A2)), no(3) + T(Fr.tex(A3))]),
             h: '先算兩片葉子：' + T(prodF([w1, r1]) + '=' + Fr.tex(L1p)) + '（' + sc.a + '且「' + sc.y + '」）與 ' + T(prodF([w2, r2]) + '=' + Fr.tex(L2p)) + '。' + no(1) + '是兩片相加 ' + T(Fr.tex(Py)) + '；' + no(2) + '是「要的那一片 ÷ 同一種結果的所有葉子之和」' + T('\\dfrac{' + Fr.tex(L1p) + '}{' + Fr.tex(Py) + '}') + '。' + no(3) + '換成「' + sc.n + '」的兩片：' + T(Fr.tex(G1)) + ' 與 ' + T(Fr.tex(G2)) + '。',
             p: { w1: fp(w1), r1: fp(r1), r2: fp(r2), ans: [fp(A1), fp(A2), fp(A3)] } };
  };

  /* ── §4 醫學篩檢 ── */
  L1.bayesScreen = function (r) {
    var sc = r.pick(SCR), pv = F(r.pick([1, 2, 4, 5, 8, 10]), 100);
    var s = F(r.pick([80, 85, 90, 95, 96, 98, 99]), 100), t = F(r.pick([85, 90, 92, 95, 96, 98, 99]), 100);
    var N = r.pick([10000, 20000, 50000, 100000]);   /* 一律是 10000 的倍數：四格人數必為整數 */
    var d = Fr.mul(pv, s), nd = Fr.mul(Fr.cp(pv), Fr.cp(t));
    var Ppos = Fr.add(d, nd);
    var dneg = Fr.mul(pv, Fr.cp(s)), ndneg = Fr.mul(Fr.cp(pv), t), Pneg = Fr.add(dneg, ndneg);
    var A1 = Ppos, A2 = Fr.div(d, Ppos), A3 = Fr.div(dneg, Pneg);
    return { q: '某地區「' + sc.d + '」的比例為 ' + T(pc(pv)) + '。有一種檢驗：' + sc.d + '的人「' + sc.y + '」的機率為 ' + T(Fr.tex(s)) + '；' + sc.nd + '的人「' + sc.n + '」的機率為 ' + T(Fr.tex(t)) + '。' + sc.one + '，求' + no(1) + T(PTx(tx(sc.y))) + '　' + no(2) + '已知此人「' + sc.y + '」，求他' + sc.d + '的機率　' + no(3) + '已知此人「' + sc.n + '」，求他' + sc.d + '的機率。',
             a: jo([no(1) + T(Fr.tex(A1)), no(2) + T(Fr.tex(A2)), no(3) + T(Fr.tex(A3))]),
             h: '假設共 ' + T(N) + ' 人：' + sc.d + '的有 ' + T(Math.round(Fr.num(pv) * N)) + ' 人（其中「' + sc.y + '」' + T(Math.round(Fr.num(d) * N)) + ' 人）、' + sc.nd + '的有 ' + T(Math.round(N - Fr.num(pv) * N)) + ' 人（其中' + sc.nd + '卻「' + sc.y + '」的有 ' + T(Math.round(Fr.num(nd) * N)) + ' 人）。' + no(2) + '的分母就是這兩格相加 ' + T(Math.round(Fr.num(Ppos) * N)) + ' 人 ⟹ ' + T('\\dfrac{' + Math.round(Fr.num(d) * N) + '}{' + Math.round(Fr.num(Ppos) * N) + '}') + '。' + sc.nd + '的人本來就佔絕大多數，即使誤判的比例很小，被誤判的人數也可能和真正' + sc.d + '的人一樣多。',
             p: { pv: fp(pv), s: fp(s), t: fp(t), N: N, ans: [fp(A1), fp(A2), fp(A3)] } };
  };

  /* ── §4 三分支的貝氏 ── */
  L1.bayesThree = function (r) {
    var sc = r.pick(CS3), ws = [r.int(1, 6), r.int(1, 6), r.int(1, 6)], S = ws[0] + ws[1] + ws[2];
    var rs = [], i, cand = [1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20];
    for (i = 0; i < 3; i++) rs.push(F(r.pick(cand), 100));
    var tz = 0;
    while ((Fr.eq(rs[0], rs[1]) || Fr.eq(rs[1], rs[2]) || Fr.eq(rs[0], rs[2])) && tz++ < 80) { rs[1] = F(r.pick(cand), 100); rs[2] = F(r.pick(cand), 100); }
    if (Fr.eq(rs[0], rs[1]) || Fr.eq(rs[1], rs[2]) || Fr.eq(rs[0], rs[2])) { rs = [F(1, 100), F(3, 100), F(6, 100)]; }
    var lf = [], W = [];
    for (i = 0; i < 3; i++) { W.push(F(ws[i], S)); lf.push(Fr.mul(W[i], rs[i])); }
    var Py = sumF(lf), i1 = r.int(0, 2), i2 = (i1 + 1 + r.int(0, 1)) % 3;
    var A1 = Py, A2 = Fr.div(lf[i1], Py), A3 = Fr.div(lf[i2], Py);
    return { q: sc.a.join('、') + ' 三者的' + sc.w + '比為 ' + T(ws.join(':')) + '，產生「' + sc.y + '」的比率分別為 ' + rs.map(function (f) { return T(pc(f)); }).join('、') + '。' + no(1) + '求' + sc.pick + '為「' + sc.y + '」的機率。' + no(2) + '已知是「' + sc.y + '」，求它來自' + sc.a[i1] + '的機率。' + no(3) + '已知是「' + sc.y + '」，求它來自' + sc.a[i2] + '的機率。',
             a: jo([no(1) + T(Fr.tex(A1)), no(2) + T(Fr.tex(A2)), no(3) + T(Fr.tex(A3))]),
             h: '比 ' + T(ws.join(':')) + ' 要先化成機率 ' + W.map(function (f) { return T(Fr.tex(f)); }).join('、') + '（相加為 ' + T(1) + '）。三片葉子依序是 ' + lf.map(function (f) { return T(Fr.tex(f)); }).join('、') + '，分母是三片相加 ' + T(Fr.tex(Py)) + '，分子是要的那一片。驗算：三個條件機率加起來必須是 ' + T(1) + '。',
             p: { ws: ws, rs: rs.map(fp), i1: i1, i2: i2, ans: [fp(A1), fp(A2), fp(A3)] } };
  };

  /* ── §4 貝氏與列聯表：先換成人數 ── */
  L1.bayesTable = function (r) {
    var sc = r.pick(SCR), N, pv, s, u, n1, n2, t = 0;
    do {
      N = r.pick([1000, 2000, 4000, 5000, 10000]);
      pv = F(r.pick([5, 10, 15, 20, 25, 30, 40]), 100);
      s = F(r.pick([70, 75, 80, 85, 90, 95]), 100); u = F(r.pick([5, 10, 15, 20, 25]), 100);
      n1 = N * pv.n / pv.d; n2 = N - n1; t++;
    } while (((n1 * s.n) % s.d !== 0 || (n2 * u.n) % u.d !== 0 || n1 < 50) && t < 400);
    if ((n1 * s.n) % s.d !== 0 || (n2 * u.n) % u.d !== 0) { N = 10000; pv = F(1, 5); s = F(4, 5); u = F(1, 10); n1 = 2000; n2 = 8000; }
    var a = n1 * s.n / s.d, b = n1 - a, c = n2 * u.n / u.d, d = n2 - c;
    var pos = a + c, neg = b + d;
    var A1 = F(pos, N), A2 = F(a, pos), A3 = F(b, neg);
    return { q: '共 ' + T(N) + ' 位' + sc.pop + '。已知「' + sc.d + '」的比例為 ' + T(pc(pv)) + '；' + sc.d + '的人「' + sc.y + '」的機率為 ' + T(Fr.tex(s)) + '；' + sc.nd + '的人「' + sc.y + '」的機率為 ' + T(Fr.tex(u)) + '。' + no(1) + '求「' + sc.d + '且' + sc.y + '」「' + sc.d + '且' + sc.n + '」「' + sc.nd + '且' + sc.y + '」「' + sc.nd + '且' + sc.n + '」四類的人數。' + no(2) + '求 ' + T(PTx(tx(sc.y))) + '。' + no(3) + sc.one + '，已知「' + sc.y + '」，求他' + sc.d + '的機率。' + no(4) + '已知「' + sc.n + '」，求他' + sc.d + '的機率。',
             a: jo([no(1) + T(a) + '、' + T(b) + '、' + T(c) + '、' + T(d), no(2) + T(Fr.tex(A1)), no(3) + T(Fr.tex(A2)), no(4) + T(Fr.tex(A3))]),
             h: '全部換成整數人數最好算：' + sc.d + ' ' + T(N) + '×' + T(Fr.tex(pv)) + '＝' + T(n1) + ' 人、' + sc.nd + ' ' + T(n2) + ' 人；再各自乘上該列的比率 ' + T(Fr.tex(s)) + ' 與 ' + T(Fr.tex(u)) + '。橫加等於直加是最快的驗算（' + T(a + '+' + b + '=' + n1) + '、' + T(a + '+' + c + '=' + pos) + '）。' + no(3) + '的分母是「' + sc.y + '」的合計 ' + T(pos) + '，' + no(4) + '的分母是「' + sc.n + '」的合計 ' + T(neg) + '。',
             p: { N: N, pv: fp(pv), s: fp(s), u: fp(u), cells: [a, b, c, d], ans: [fp(A1), fp(A2), fp(A3)] } };
  };

  /* ── §5 條件機率與排列組合 ── */
  var CC_B = [
    { t: '三數都是偶數', f: function (s, n) { return s.every(function (x) { return x % 2 === 0; }); } },
    { t: '三數都是奇數', f: function (s, n) { return s.every(function (x) { return x % 2 === 1; }); } },
    { t: '三數之和為偶數', f: function (s, n) { return (s[0] + s[1] + s[2]) % 2 === 0; } },
    { t: '三數之積為偶數', f: function (s, n) { return (s[0] * s[1] * s[2]) % 2 === 0; } },
    { t: '三數之和為奇數', f: function (s, n) { return (s[0] + s[1] + s[2]) % 2 === 1; } }
  ];
  L1.condCombo = function (r) {
    var n = r.pick([8, 9, 10, 11, 12, 14, 15]), kind = r.int(0, 2), i, j, k, C = [];
    for (i = 1; i <= n; i++) for (j = i + 1; j <= n; j++) for (k = j + 1; k <= n; k++) C.push([i, j, k]);
    var bt, at, nB = 0, nAB = 0, t = 0, mx, mn;
    do {
      t++;
      if (kind === 0) { mx = r.int(4, n); bt = { t: '取出的三數中最大的是 ' + T(mx), f: function (s) { return s[2] === mx; } }; }
      else if (kind === 1) { mn = r.int(1, n - 4); bt = { t: '取出的三數中最小的是 ' + T(mn), f: function (s) { return s[0] === mn; } }; }
      else bt = r.pick(CC_B);
      var aKind = r.int(0, 3), av, ax;
      if (aKind === 0) { av = r.int(2, n); at = { t: '其中含有 ' + T(av), f: function (s) { return s.indexOf(av) >= 0; } }; }
      else if (aKind === 1) { ax = r.int(3, n - 1); at = { t: '除了最大的數以外，另外兩數都小於 ' + T(ax), f: function (s) { return s[0] < ax && s[1] < ax; } }; }
      else if (aKind === 2) { ax = r.int(2, n - 2); at = { t: '除了最小的數以外，另外兩數都大於 ' + T(ax), f: function (s) { return s[1] > ax && s[2] > ax; } }; }
      else { at = r.pick(CC_B); }
      nB = 0; nAB = 0;
      for (i = 0; i < C.length; i++) if (bt.f(C[i])) { nB++; if (at.f(C[i])) nAB++; }
    } while ((nB < 4 || nAB === 0 || nAB === nB || at.t === bt.t) && t < 300);
    var an = F(nAB, nB);
    return { q: '從 ' + T('1,2,\\ldots,' + n) + ' 這 ' + T(n) + ' 個數字中任取三個相異數。已知' + bt.t + '，求' + at.t + ' 的機率。',
             a: T(Fr.tex(an)),
             h: '用 ' + T(PTx('A\\mid B') + '=\\dfrac{n(A\\cap B)}{n(B)}') + '，關鍵是把 ' + T('n(B)') + ' 數對：全部取法有 ' + T(CT(n, 3) + '=' + nCr(n, 3)) + ' 種，滿足「' + bt.t + '」的有 ' + T(nB) + ' 種（這就是新的分母），其中同時滿足「' + at.t + '」的有 ' + T(nAB) + ' 種。分子分母要用同一種算法，不能一個排列一個組合。',
             p: { n: n, bt: bt.t, at: at.t, nB: nB, nAB: nAB, ans: fp(an) } };
  };

  /* ── §5 題型辨識 ── */
  L1.typeIdent = function (r) {
    var tb = r.pick(TB), N, fr, c0, M, t = 0;
    do {
      N = r.pick([40, 50, 60, 80, 100, 120, 150, 200]);
      fr = r.pick([F(1, 2), F(2, 5), F(3, 5), F(1, 4), F(3, 4), F(3, 8), F(1, 5), F(7, 10), F(3, 10), F(5, 8)]);
      t++;
    } while ((N % fr.d !== 0 || N * fr.n / fr.d < 14 || N - N * fr.n / fr.d < 14) && t < 300);
    if (N % fr.d !== 0 || N * fr.n / fr.d < 14 || N - N * fr.n / fr.d < 14) { N = 200; fr = F(2, 5); }
    c0 = N * fr.n / fr.d;
    M = [[r.int(5, c0 - 5), 0], [0, 0]];
    M[1][0] = c0 - M[0][0];
    M[0][1] = r.int(5, N - c0 - 5); M[1][1] = N - c0 - M[0][1];
    var ri = r.int(0, 1), ci = 0, k = r.int(2, 4);
    var A1 = fr, A2 = F(M[ri][ci], rowSum(M, ri)), A3 = F(M[ri][ci], colSum(M, ci)), A4 = Fr.pow(A1, k), A5 = Fr.cp(A4);
    return { q: tabHead(tb, M) + '請先判斷各小題屬於哪一類（普通機率／條件機率／獨立重複），再求值：' + no(1) + tb.one + '，求他是「' + tb.c[ci] + '」的機率。' + no(2) + '已知他是「' + tb.r[ri] + '」，求他是「' + tb.c[ci] + '」的機率。' + no(3) + '已知他是「' + tb.c[ci] + '」，求他是「' + tb.r[ri] + '」的機率。' + no(4) + '連續 ' + T(k) + ' 次隨機抽一' + tb.u + '（每次記錄後放回），求 ' + T(k) + ' 次都抽到「' + tb.c[ci] + '」的機率。' + no(5) + '承 ' + no(4) + '，求 ' + T(k) + ' 次中至少一次抽到「' + tb.c[ci] + '」的機率。',
             a: jo([no(1) + T(Fr.tex(A1)), no(2) + T(Fr.tex(A2)), no(3) + T(Fr.tex(A3)), no(4) + T(Fr.tex(A4)), no(5) + T(Fr.tex(A5))]),
             h: no(1) + '是普通機率，分母是總數 ' + T(N) + '；' + no(2) + '是條件機率，分母換成「' + tb.r[ri] + '」的合計 ' + T(rowSum(M, ri)) + '；' + no(3) + '方向相反，分母換成「' + tb.c[ci] + '」的合計 ' + T(colSum(M, ci)) + '，兩題分子都是同一格的 ' + T(M[ri][ci]) + '。' + no(4) + '放回 ⟹ 每次都獨立、機率都是 ' + T(Fr.tex(A1)) + '，直接乘 ' + T(k) + ' 次；' + no(5) + '用餘事件 ' + T('1-' + pw(Fr.tex(A1), k)) + '。',
             p: { M: M, ri: ri, ci: ci, k: k, ans: [fp(A1), fp(A2), fp(A3), fp(A4), fp(A5)] } };
  };

  /* ═══════════════════════ L2 ═══════════════════════ */
  var L2 = {};

  /* ── §2 條件機率：由聯集與條件機率反求 ── */
  L2.condUnknown = function (r) {
    var m = randM(r), useDec = r() < 0.4;
    var giv = r.pick([['A\\cup B', 'A\\mid B', 'B\\mid A'], ['A', 'B\\mid A', 'A\\cup B'], ['B', "A'\\cap B'", 'A\\mid B'], ['A\\cup B', 'A\\cap B', 'B\\mid A']]);
    var tg = r.shuffle(['A', 'B', 'A\\cap B', "A\\mid B'", "A'\\cap B'", "B\\mid A'", 'A\\cup B']).filter(function (e) { return giv.indexOf(e) < 0; }).slice(0, 4);
    var gv = giv.map(function (e) { return evalTarget(e, m); });
    var av = tg.map(function (e) { return evalTarget(e, m); });
    return { q: '設 ' + T('A') + '、' + T('B') + ' 為樣本空間中的兩事件（機率皆不為 ' + T(0) + '），已知 ' + giv.map(function (e, i) { return factLine(e, gv[i], useDec); }).join('、') + '。求 ' + tg.map(function (e, i) { return no(i + 1) + T(PTx(e)); }).join('　') + '。',
             a: jo(tg.map(function (e, i) { return no(i + 1) + ansEq(PTx(e), av[i]); })),
             h: '把樣本空間拆成四塊未知數 ' + T(PTx('A\\cap B')) + '、' + T(PTx("A\\cap B'")) + '、' + T(PTx("A'\\cap B")) + '、' + T(PTx("A'\\cap B'")) + '，四塊和為 ' + T(1) + '；每一個已知條件都是一條一次方程式（例如 ' + T(PTx('X\\mid Y') + '=k') + ' 就是 ' + T(PTx('X\\cap Y') + '=k\\,' + PTx('Y')) + '）。本題解出來依序是 ' + T(Fr.tex(m[0])) + '、' + T(Fr.tex(m[1])) + '、' + T(Fr.tex(m[2])) + '、' + T(Fr.tex(m[3])) + '，要哪一個就把對應的塊加起來再相除。',
             p: { m: m.map(fp), giv: giv, tg: tg, ans: av.map(fp) } };
  };

  /* ── §2 兩顆骰子的條件機率與獨立性 ── */
  L2.condDice2 = function (r) {
    var eA, eB, nA, nB, nAB, a, b, t = 0;
    do {
      eA = dieEv2(r); eB = dieEv2(r); nA = 0; nB = 0; nAB = 0;
      for (a = 1; a <= 6; a++) for (b = 1; b <= 6; b++) {
        if (eA.f(a, b)) nA++; if (eB.f(a, b)) nB++; if (eA.f(a, b) && eB.f(a, b)) nAB++;
      }
      t++;
    } while ((eA.t === eB.t || nA < 2 || nB < 3 || nAB === 0 || nAB === nB || nA === 36 || nB === 36) && t < 400);
    var pA = F(nA, 36), pB = F(nB, 36), pAB = F(nAB, 36);
    var c1 = F(nAB, nB), c2 = F(nAB, nA), ok = Fr.eq(pAB, Fr.mul(pA, pB));
    return { q: '擲兩顆公正骰子（視為可分辨的兩顆），設 ' + T('A') + ' 表「' + eA.t + '」、' + T('B') + ' 表「' + eB.t + '」。' + no(1) + '求 ' + T(PTx('A')) + ' 與 ' + T(PTx('B')) + '　' + no(2) + '求 ' + T(PTx('A\\mid B')) + '　' + no(3) + '求 ' + T(PTx('B\\mid A')) + '　' + no(4) + '判斷 ' + T('A') + '、' + T('B') + ' 是否獨立。',
             a: jo([no(1) + T(Fr.tex(pA)) + '、' + T(Fr.tex(pB)), no(2) + T(Fr.tex(c1)), no(3) + T(Fr.tex(c2)), no(4) + (ok ? '獨立' : '不獨立') + '，' + ansEq(PTx('A\\cap B'), pAB) + '、' + ansEq(PTx('A') + PTx('B'), Fr.mul(pA, pB))]),
             h: '全部 ' + T(36) + ' 種有序結果中，' + T('A') + ' 有 ' + T(nA) + ' 種、' + T('B') + ' 有 ' + T(nB) + ' 種、' + T('A\\cap B') + ' 有 ' + T(nAB) + ' 種。' + no(2) + '的分母換成 ' + T(nB) + '、' + no(3) + '的分母換成 ' + T(nA) + '，分子都是 ' + T(nAB) + '——' + T(PTx('A\\mid B')) + ' 與 ' + T(PTx('B\\mid A')) + ' 通常不相等。' + no(4) + '比 ' + T(Fr.tex(pAB)) + ' 與 ' + T(prodF([pA, pB])) + '。',
             p: { eA: eA.t, eB: eB.t, nA: nA, nB: nB, nAB: nAB, indep: ok ? 1 : 0, ans: [fp(pA), fp(pB), fp(c1), fp(c2)] } };
  };

  /* ── §5 條件機率與組合（取 3 或 4 個） ── */
  L2.condComb2 = function (r) {
    var n = r.pick([9, 10, 11, 12, 13, 14]), rr = r.pick([3, 3, 4]), C = [], i, j, k, l, t = 0;
    if (rr === 3) { for (i = 1; i <= n; i++) for (j = i + 1; j <= n; j++) for (k = j + 1; k <= n; k++) C.push([i, j, k]); }
    else { for (i = 1; i <= n; i++) for (j = i + 1; j <= n; j++) for (k = j + 1; k <= n; k++) for (l = k + 1; l <= n; l++) C.push([i, j, k, l]); }
    var md = r.pick([2, 3, 4]);
    var BP = [
      { t: '取出的數之積為偶數', f: function (s) { return s.some(function (x) { return x % 2 === 0; }); } },
      { t: '取出的數之和為偶數', f: function (s) { return s.reduce(function (u, v) { return u + v; }, 0) % 2 === 0; } },
      { t: '取出的數之和為奇數', f: function (s) { return s.reduce(function (u, v) { return u + v; }, 0) % 2 === 1; } },
      { t: '取出的數中至少有一個是 ' + T(md) + ' 的倍數', f: function (s) { return s.some(function (x) { return x % md === 0; }); } },
      { t: '取出的數全都大於 ' + T(3), f: function (s) { return s.every(function (x) { return x > 3; }); } }
    ];
    var AP = [
      { t: '恰有一個奇數', f: function (s) { return s.filter(function (x) { return x % 2 === 1; }).length === 1; } },
      { t: '恰有兩個偶數', f: function (s) { return s.filter(function (x) { return x % 2 === 0; }).length === 2; } },
      { t: '全部都是偶數', f: function (s) { return s.every(function (x) { return x % 2 === 0; }); } },
      { t: '含有數字 ' + T(1), f: function (s) { return s.indexOf(1) >= 0; } },
      { t: '最大的數是 ' + T(n), f: function (s) { return s[s.length - 1] === n; } },
      { t: '最小的數不小於 ' + T(3), f: function (s) { return s[0] >= 3; } }
    ];
    var bt, at, nB, nAB;
    do {
      bt = r.pick(BP); at = r.pick(AP); nB = 0; nAB = 0;
      for (i = 0; i < C.length; i++) if (bt.f(C[i])) { nB++; if (at.f(C[i])) nAB++; }
      t++;
    } while ((nB < 6 || nAB === 0 || nAB === nB) && t < 300);
    var an = F(nAB, nB), tot = C.length;
    return { q: '從 ' + T('1,2,\\ldots,' + n) + ' 這 ' + T(n) + ' 個數字中任取 ' + T(rr) + ' 個相異數。已知' + bt.t + '，求這 ' + T(rr) + ' 個數' + at.t + ' 的機率。',
             a: T(Fr.tex(an)),
             h: '條件機率 ' + T('\\dfrac{n(A\\cap B)}{n(B)}') + '：全部取法 ' + T(CT(n, rr) + '=' + tot) + ' 種。先把 ' + T('n(B)') + ' 數對——像「積為偶數」「至少含一個倍數」走餘事件最快——本題 ' + T('n(B)=' + nB) + '；再數同時符合所求的有 ' + T('n(A\\cap B)=' + nAB) + ' 種。分子分母要用同一種算法。',
             p: { n: n, rr: rr, bt: bt.t, at: at.t, nB: nB, nAB: nAB, ans: fp(an) } };
  };

  /* ── §2 不放回連抽三次（含反問） ── */
  L2.drawThree = function (r) {
    var bg = r.pick(BAG), a = r.int(3, 6), b = r.int(2, 5), n = a + b;
    var c1 = bg.c[0], c2 = bg.c[1];
    var P3 = F(a, n);                                                    /* 第三次是 c1 */
    var Prev = F(a - 1, n - 1);                                          /* 已知第二次 c1，第一次也 c1 */
    var Pall = Fr.mul(F(a, n), Fr.mul(F(a - 1, n - 1), F(a - 2, n - 2)));
    /* 已知三次中恰有兩次 c1，求第一次是 c1 */
    var w2 = Fr.mul(F(3), Fr.mul(F(a, n), Fr.mul(F(a - 1, n - 1), F(b, n - 2))));
    var w2f = Fr.mul(F(2), Fr.mul(F(a, n), Fr.mul(F(a - 1, n - 1), F(b, n - 2))));
    var Pc = Fr.div(w2f, w2);
    return { q: bg.b + '中有 ' + T(a) + ' 顆' + c1 + bg.o + '與 ' + T(b) + ' 顆' + c2 + bg.o + '，不放回依序抽三次。求' + no(1) + '第三次是' + c1 + bg.o + '　' + no(2) + '三次都是' + c1 + bg.o + '　' + no(3) + '已知第二次是' + c1 + bg.o + '，第一次也是' + c1 + bg.o + '　' + no(4) + '已知三次中恰有兩次是' + c1 + bg.o + '，第一次是' + c1 + bg.o + ' 的機率。',
             a: jo([no(1) + T(Fr.tex(P3)), no(2) + T(Fr.tex(Pall)), no(3) + T(Fr.tex(Prev)), no(4) + T(Fr.tex(Pc))]),
             h: no(1) + '把 ' + T(n) + ' 顆球排成一列，每一顆排到第三個位置的機會都一樣 ⟹ 答案就是 ' + T(Fr.tex(F(a, n))) + '。' + no(3) + '是「反過來問」：由對稱性，兩次抽出的是一組無序的兩顆球，已知其中指定的一顆是' + c1 + '，另一顆是' + c1 + '的機率為 ' + T('\\dfrac{' + (a - 1) + '}{' + (n - 1) + '}') + '。' + no(4) + '分母是「恰兩次' + c1 + '」的三種順序合計 ' + T(Fr.tex(w2)) + '，分子只留第一次就是' + c1 + '的兩種 ' + T(Fr.tex(w2f)) + '。',
             p: { a: a, b: b, ans: [fp(P3), fp(Pall), fp(Prev), fp(Pc)] } };
  };

  /* ── §2 抽籤的公平性（對稱性） ── */
  L2.symDraw = function (r) {
    var w = r.int(2, 4), l = r.int(3, 6), n = w + l, k = r.int(2, Math.min(4, n - 1));
    var ctx = r.pick([{ o: '籤', y: '中獎', x: '沒有中獎', c: '籤筒', u: '張' }, { o: '球', y: '紅球', x: '白球', c: '袋子', u: '顆' }, { o: '卡片', y: '有獎', x: '沒有獎', c: '卡堆', u: '張' }]);
    var A1 = F(w, n), A2 = F(w - 1, n - 1), A3 = F(w - 1, n - 1), A4 = Fr.mul(F(l, n), F(l - 1, n - 1));
    return { q: ctx.c + '中有 ' + T(w) + ' ' + ctx.u + '「' + ctx.y + '」與 ' + T(l) + ' ' + ctx.u + '「' + ctx.x + '」的' + ctx.o + '，' + T(n) + ' 人依序各抽一' + ctx.u + '且抽後不放回。求' + no(1) + '第 ' + T(k) + ' 位抽到「' + ctx.y + '」　' + no(2) + '已知第 ' + T(1) + ' 位抽到「' + ctx.y + '」，第 ' + T(k) + ' 位也抽到「' + ctx.y + '」　' + no(3) + '已知第 ' + T(k) + ' 位抽到「' + ctx.y + '」，第 ' + T(1) + ' 位也抽到「' + ctx.y + '」　' + no(4) + '前兩位都沒抽到「' + ctx.y + '」的機率。',
             a: jo([no(1) + T(Fr.tex(A1)), no(2) + T(Fr.tex(A2)), no(3) + T(Fr.tex(A3)), no(4) + T(Fr.tex(A4))]),
             h: '把 ' + T(n) + ' ' + ctx.u + ctx.o + '排成一列，「' + ctx.y + '」落在任一個位置的機會都相同 ⟹ ' + no(1) + '與第一位一樣是 ' + T(Fr.tex(F(w, n))) + '，先抽後抽一樣公平。' + no(2) + '已知第 ' + T(1) + ' 位抽走一' + ctx.u + '「' + ctx.y + '」，剩 ' + T(n - 1) + ' ' + ctx.u + '中有 ' + T(w - 1) + ' ' + ctx.u + '「' + ctx.y + '」。' + no(3) + '的答案和 ' + no(2) + '相同——分子都是 ' + T(PTx('\\text{兩位都中}')) + '，而 ' + no(2) + no(3) + '的分母都是 ' + T(Fr.tex(F(w, n))) + '。',
             p: { w: w, l: l, k: k, ans: [fp(A1), fp(A2), fp(A3), fp(A4)] } };
  };

  /* ── §1 列聯表補完（給比例與一格） ── */
  L2.tableFill = function (r) {
    var sc = r.pick(SCR), N, pv, s, n1, n2, a, b, c, d, t = 0;
    do {
      N = r.pick([1000, 2000, 4000, 5000, 10000]);
      pv = F(r.pick([5, 10, 15, 20, 25, 30]), 100);
      s = F(r.pick([70, 75, 80, 85, 90]), 100);
      n1 = N * pv.n / pv.d; n2 = N - n1; t++;
      a = n1 * s.n / s.d; b = n1 - a;
      d = Math.round(n2 * (0.5 + 0.045 * r.int(0, 10))); c = n2 - d;
    } while (((n1 * s.n) % s.d !== 0 || n1 < 50 || c < 10 || d < 10) && t < 400);
    if ((n1 * s.n) % s.d !== 0 || c < 10 || d < 10) { N = 10000; pv = F(1, 10); s = F(9, 10); n1 = 1000; n2 = 9000; a = 900; b = 100; d = 8550; c = 450; }
    var w = F(d, N), pos = a + c, neg = b + d;
    var A1 = F(pos, N), A2 = F(a, pos), A3 = F(d, neg);
    return { q: '某次調查共 ' + T(N) + ' 位' + sc.pop + '。已知「' + sc.d + '」的比例為 ' + T(pc(pv)) + '；「' + sc.nd + '且' + sc.n + '」的人數佔全部的 ' + T(Fr.tex(w)) + '；' + sc.d + '的人中「' + sc.y + '」的比例為 ' + T(Fr.tex(s)) + '。' + no(1) + '求「' + sc.d + '且' + sc.y + '」「' + sc.d + '且' + sc.n + '」「' + sc.nd + '且' + sc.y + '」三類的人數。' + no(2) + '求 ' + T(PTx(tx(sc.y))) + '。' + no(3) + '已知某人「' + sc.y + '」，求他' + sc.d + '的機率。' + no(4) + '已知某人「' + sc.n + '」，求他' + sc.nd + '的機率。',
             a: jo([no(1) + T(a) + '、' + T(b) + '、' + T(c), no(2) + T(Fr.tex(A1)), no(3) + T(Fr.tex(A2)), no(4) + T(Fr.tex(A3))]),
             h: '先填「一定填得出來」的格子再用合計逼出其餘：' + sc.d + ' ' + T(n1) + ' 人、' + sc.nd + ' ' + T(N) + '-' + T(n1) + '=' + T(n2) + ' 人；' + sc.d + '且「' + sc.y + '」' + T(n1) + '×' + T(Fr.tex(s)) + '=' + T(a) + ' 人 ⟹ 同一列剩下 ' + T(b) + ' 人；「' + sc.nd + '且' + sc.n + '」' + T(d) + ' 人 ⟹ 同一列剩下 ' + T(c) + ' 人。橫加＝直加是最快的驗算（' + T(a + '+' + c + '=' + pos) + '）。',
             p: { N: N, pv: fp(pv), s: fp(s), w: fp(w), cells: [a, b, c, d], ans: [fp(A1), fp(A2), fp(A3)] } };
  };

  /* ── §3 列聯表：要多少人才會獨立 ── */
  L2.tableIndepFix = function (r) {
    var tb = r.pick(TB), N, R, C, x, t = 0;
    do {
      N = r.pick([200, 240, 300, 360, 400, 480, 500, 600]);
      R = r.int(2, 8) * (N / 10); C = r.int(2, 8) * (N / 10);
      t++;
    } while ((R >= N || C >= N || (R * C) % N !== 0 || R < 20 || C < 20) && t < 300);
    if (R >= N || C >= N || (R * C) % N !== 0) { N = 400; R = 160; C = 100; }
    var need = R * C / N, lo = Math.max(1, R + C - N + 1), hi = Math.min(R, C) - 1, dd = r.shuffle([-40, -30, -20, -15, -10, 10, 15, 20, 30, 40]), ii;
    x = 0;
    for (ii = 0; ii < dd.length; ii++) { if (need + dd[ii] >= lo && need + dd[ii] <= hi) { x = need + dd[ii]; break; } }
    if (!x) x = (need + 1 <= hi) ? need + 1 : need - 1;
    var Mx = [[x, R - x], [C - x, N - R - C + x]];
    var pc1 = F(C, N), pcr = F(x, R);
    return { q: tb.h + '共 ' + T(N) + ' ' + tb.u + '，其中「' + tb.r[0] + '」有 ' + T(R) + ' ' + tb.u + '、「' + tb.c[0] + '」有 ' + T(C) + ' ' + tb.u + '。' + no(1) + '若「' + tb.r[0] + '」與「' + tb.c[0] + '」這兩個事件獨立，求「' + tb.r[0] + '且' + tb.c[0] + '」應有多少 ' + tb.u + '。' + no(2) + '求此時的 ' + T(PTx(tx(tb.c[0]) + '\\mid' + tx(tb.r[0]))) + '。' + no(3) + '若實際上「' + tb.r[0] + '且' + tb.c[0] + '」有 ' + T(x) + ' ' + tb.u + '，判斷兩者是否獨立，並求此時的 ' + T(PTx(tx(tb.c[0]) + '\\mid' + tx(tb.r[0]))) + '。',
             a: jo([no(1) + T(need) + ' ' + tb.u, no(2) + T(Fr.tex(pc1)), no(3) + '不獨立，' + T(Fr.tex(pcr))]),
             h: '獨立 ⟺ ' + T(PTx('A\\cap B') + '=' + PTx('A') + PTx('B')) + '，換成人數就是 ' + T('\\dfrac{n(A\\cap B)}{' + N + '}=\\dfrac{' + R + '}{' + N + '}\\cdot\\dfrac{' + C + '}{' + N + '}') + ' ⟹ ' + T('n(A\\cap B)=\\dfrac{' + R + '\\times' + C + '}{' + N + '}=' + need) + '。' + no(2) + '獨立時條件機率等於邊際機率 ' + T(PTx(tx(tb.c[0])) + '=' + Fr.tex(pc1)) + '。' + no(3) + '實際是 ' + T(x) + ' ' + tb.u + '，' + T(x + '\\ne' + need) + ' ⟹ 不獨立，條件機率改成 ' + T('\\dfrac{' + x + '}{' + R + '}') + '。',
             p: { N: N, R: R, C: C, x: x, M: Mx, ans: [need, fp(pc1), fp(pcr)] } };
  };

  /* ── §3 三人獨立的綜合（含條件機率） ── */
  L2.indepThreePeople = function (r) {
    var nm = r.pick([['甲', '乙', '丙'], ['小文', '阿遠', '小美'], ['第一位', '第二位', '第三位']]);
    var act = r.pick([{ v: '各射擊一次', y: '命中' }, { v: '各解一道題', y: '解出' }, { v: '各抽一次獎', y: '抽中' }, { v: '各投籃一次', y: '投進' }]);
    var cand = [F(1, 2), F(1, 3), F(2, 3), F(1, 4), F(3, 4), F(2, 5), F(3, 5), F(1, 5), F(4, 5), F(1, 6), F(5, 6)];
    var ps = [], used = {}, f;
    while (ps.length < 3) { f = r.pick(cand); if (used[f.n + '/' + f.d]) continue; used[f.n + '/' + f.d] = 1; ps.push(f); }
    var qs = ps.map(Fr.cp);
    var none = Fr.mul(qs[0], Fr.mul(qs[1], qs[2])), atl = Fr.cp(none);
    var all = Fr.mul(ps[0], Fr.mul(ps[1], ps[2]));
    var one = Fr.add(Fr.mul(ps[0], Fr.mul(qs[1], qs[2])), Fr.add(Fr.mul(qs[0], Fr.mul(ps[1], qs[2])), Fr.mul(qs[0], Fr.mul(qs[1], ps[2]))));
    var A3 = Fr.div(all, atl), A4 = Fr.div(one, atl);
    return { q: nm.join('、') + ' 三人' + act.v + '，' + act.y + '的機率分別為 ' + ps.map(function (f2) { return T(Fr.tex(f2)); }).join('、') + '，且三人互相獨立。求' + no(1) + '至少有一人' + act.y + '　' + no(2) + '恰有一人' + act.y + '　' + no(3) + '已知至少有一人' + act.y + '，三人都' + act.y + '　' + no(4) + '已知至少有一人' + act.y + '，恰有一人' + act.y + ' 的機率。',
             a: jo([no(1) + T(Fr.tex(atl)), no(2) + T(Fr.tex(one)), no(3) + T(Fr.tex(A3)), no(4) + T(Fr.tex(A4))]),
             h: '「至少一人」先寫反面：沒有人' + act.y + '是 ' + T(prodF(qs) + '=' + Fr.tex(none)) + ' ⟹ ' + no(1) + T('1-' + Fr.tex(none) + '=' + Fr.tex(atl)) + '。' + no(3) + no(4) + '都是條件機率，分母同樣是 ' + T(Fr.tex(atl)) + '；分子分別是「三人都' + act.y + '」' + T(prodF(ps) + '=' + Fr.tex(all)) + ' 與「恰一人」' + T(Fr.tex(one)) + '。',
             p: { ps: ps.map(fp), ans: [fp(atl), fp(one), fp(A3), fp(A4)] } };
  };

  /* ── §3 由「至少一次」反求機率 ── */
  L2.solveP = function (r) {
    var nm = r.pick([['小文', '阿遠'], ['甲', '乙'], ['第一位', '第二位']]);
    var act = r.pick([{ v: '各抽一次獎', y: '抽中' }, { v: '各射擊一次', y: '命中' }, { v: '各投籃一次', y: '投進' }, { v: '各解一道題', y: '解出' }]);
    var den = r.pick([3, 4, 5, 6, 7, 8, 9, 10]), num = r.int(1, den - 1);
    var q0 = F(num, den), p0 = Fr.cp(q0);                     /* q0 = 1-p */
    var atl = Fr.cp(Fr.mul(q0, q0));
    var all = Fr.mul(p0, p0), one = Fr.mul(F(2), Fr.mul(p0, q0));
    var A3 = Fr.div(all, atl), A4 = Fr.div(one, atl);
    return { q: nm.join('與') + ' ' + act.v + '，兩人是否' + act.y + '互相獨立，且兩人' + act.y + '的機率相同，設為 ' + T('p') + '。已知兩人之中至少有一人' + act.y + '的機率為 ' + T(Fr.tex(atl)) + '。求' + no(1) + T('p') + '　' + no(2) + '兩人都' + act.y + '　' + no(3) + '已知至少有一人' + act.y + '，兩人都' + act.y + '　' + no(4) + '已知至少有一人' + act.y + '，恰有一人' + act.y + ' 的機率。',
             a: jo([no(1) + ansEq('p', p0), no(2) + T(Fr.tex(all)), no(3) + T(Fr.tex(A3)), no(4) + T(Fr.tex(A4))]),
             h: '由 ' + T('1-(1-p)^2=' + Fr.tex(atl)) + ' 得 ' + T('(1-p)^2=' + Fr.tex(Fr.mul(q0, q0))) + '，開方取正根（因為 ' + T('0\\le p\\le1') + '）得 ' + T('1-p=' + Fr.tex(q0)) + ' ⟹ ' + T('p=' + Fr.tex(p0)) + '。' + no(3) + no(4) + '的分母都是 ' + T(Fr.tex(atl)) + '；「至少一人」底下只有「恰一人」與「兩人都」兩種情形，所以 ' + no(3) + '與 ' + no(4) + '相加必為 ' + T(1) + '——這是最好的驗算。',
             p: { q0: fp(q0), ans: [fp(p0), fp(all), fp(A3), fp(A4)] } };
  };

  /* ── §3 重複試驗與條件機率 ── */
  L2.repeatCond = function (r) {
    var sc = r.pick(RT), p = r.pick([F(1, 2), F(1, 3), F(2, 3), F(1, 4), F(3, 4), F(2, 5), F(3, 5), F(1, 5), F(5, 6)]);
    var n = r.int(5, 7), k = r.int(2, n - 1), m = r.int(1, Math.min(k - 1, n - 2));
    var A1 = binP(n, k, p), A2 = F(0), i;
    for (i = k; i <= n; i++) A2 = Fr.add(A2, binP(n, i, p));
    var A3 = binP(n - m, k - m, p);
    var A4 = Fr.cp(Fr.pow(Fr.cp(p), n));
    return { q: sc.s + '「' + sc.y + '」的機率為 ' + T(Fr.tex(p)) + '，各次互相獨立，共' + sc.vb + ' ' + T(n) + ' ' + sc.u + '。求' + no(1) + '恰好 ' + T(k) + ' ' + sc.u + '「' + sc.y + '」　' + no(2) + '至少 ' + T(k) + ' ' + sc.u + '「' + sc.y + '」　' + no(3) + '已知前 ' + T(m) + ' ' + sc.u + '都「' + sc.y + '」，求 ' + T(n) + ' ' + sc.u + '中恰好 ' + T(k) + ' ' + sc.u + '「' + sc.y + '」　' + no(4) + '至少一' + sc.u + '「' + sc.y + '」的機率。',
             a: jo([no(1) + T(Fr.tex(A1)), no(2) + T(Fr.tex(A2)), no(3) + T(Fr.tex(A3)), no(4) + T(Fr.tex(A4))]),
             h: no(1) + '先挑「哪 ' + T(k) + ' ' + sc.u + '成功」共 ' + T(CT(n, k) + '=' + nCr(n, k)) + ' 種 ⟹ ' + T(binTex(n, k, Fr.tex(p), Fr.tex(Fr.cp(p)))) + '。' + no(2) + '把 ' + T(k) + ' 到 ' + T(n) + ' 各項加起來。' + no(3) + '是本題的重點：前 ' + T(m) + ' ' + sc.u + '已經固定，因為各次獨立，問題只剩「後 ' + T(n - m) + ' ' + sc.u + '中恰 ' + T(k - m) + ' ' + sc.u + '成功」⟹ ' + T(binTex(n - m, k - m, Fr.tex(p), Fr.tex(Fr.cp(p)))) + '。' + no(4) + '走餘事件 ' + T('1-' + pw(Fr.tex(Fr.cp(p)), n)) + '。',
             p: { n: n, k: k, m: m, p: fp(p), ans: [fp(A1), fp(A2), fp(A3), fp(A4)] } };
  };

  /* ── §3 要試幾次才夠（兩種成功機率） ── */
  L2.needTrialsAdv = function (r) {
    var sc = r.pick(RT), QS = [F(1, 2), F(2, 3), F(3, 4), F(4, 5), F(5, 6), F(9, 10), F(3, 5), F(8, 9), F(5, 8), F(4, 9), F(2, 5), F(1, 3)];
    var TH = [F(1, 10), F(1, 100), F(1, 2), F(1, 5), F(1, 4), F(1, 20), F(3, 10), F(2, 5), F(1, 8), F(1, 1000), F(1, 50)];
    var qa, qb, th, na, nb, ok = false, t = 0;
    while (t++ < 600 && !ok) {
      qa = r.pick(QS); qb = r.pick(QS); th = r.pick(TH);
      if (Fr.eq(qa, qb)) continue;
      var xa = Math.log(Fr.num(th)) / Math.log(Fr.num(qa)), xb = Math.log(Fr.num(th)) / Math.log(Fr.num(qb));
      if (Math.abs(xa - Math.round(xa)) < 0.08 || Math.abs(xb - Math.round(xb)) < 0.08) continue;
      na = Math.floor(xa) + 1; nb = Math.floor(xb) + 1;
      if (na < 2 || nb < 2 || na > 45 || nb > 45 || na === nb) continue;
      var la = lg(qa), lb = lg(qb), lt = lg(th);
      if (la === null || lb === null || lt === null) continue;
      if (Math.floor(lt / la) + 1 !== na || Math.floor(lt / lb) + 1 !== nb) continue;
      ok = true;
    }
    if (!ok) { qa = F(5, 6); qb = F(9, 10); th = F(1, 10); na = 13; nb = 22; }
    var u1 = need23(qa), u2 = need23(qb), u3 = need23(th), logs = [];
    if (u1[0] || u2[0] || u3[0]) logs.push(T('\\log2\\approx' + LOG2.toFixed(4)));
    if (u1[1] || u2[1] || u3[1]) logs.push(T('\\log3\\approx' + LOG3.toFixed(4)));
    var pa = Fr.cp(qa), pb = Fr.cp(qb), K = Fr.cp(th);
    return { q: sc.s + '「' + sc.y + '」的機率為 ' + T(Fr.tex(pa)) + '，各次互相獨立。' + no(1) + '至少要' + sc.vb + '幾' + sc.u + '，才能使「至少有一' + sc.u + sc.y + '」的機率大於 ' + T(Fr.tex(K)) + '？' + no(2) + '若把每次「' + sc.y + '」的機率改成 ' + T(Fr.tex(pb)) + '（其他不變），答案會變成幾' + sc.u + '？（' + logs.join('、') + '）',
             a: jo([no(1) + T(na) + ' ' + sc.u, no(2) + T(nb) + ' ' + sc.u]),
             h: '列式 ' + T('1-' + pw(Fr.tex(qa), 'n') + '\\gt ' + Fr.tex(K)) + ' ⟺ ' + T(par(Fr.tex(qa)) + '^n\\lt ' + Fr.tex(th)) + '。取常用對數後因為 ' + T('\\log' + par(Fr.tex(qa)) + '\\lt 0') + '，除過去要變號 ⟹ ' + T('n\\gt\\dfrac{\\log' + par(Fr.tex(th)) + '}{\\log' + par(Fr.tex(qa)) + '}') + '，再取大於它的最小整數。' + no(2) + '只是把底換成 ' + T(Fr.tex(qb)) + '；兩小題算完都要把 ' + T(na) + '、' + T(na - 1) + '（與 ' + T(nb) + '、' + T(nb - 1) + '）代回原式確認。',
             p: { qa: fp(qa), qb: fp(qb), th: fp(th), ans: [na, nb] } };
  };

  /* ── §4 多分支：由總機率反推未知比率 ── */
  L2.totalPath2 = function (r) {
    var sc = r.pick(CS3), ws = [r.int(1, 5), r.int(1, 5), r.int(1, 5)], S = ws[0] + ws[1] + ws[2];
    var cand = [1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20];
    var r1 = F(r.pick(cand), 100), r2 = F(r.pick(cand), 100), r3 = F(r.pick(cand), 100);
    var tz = 0;
    while ((Fr.eq(r1, r2) || Fr.eq(r2, r3) || Fr.eq(r1, r3)) && tz++ < 80) { r2 = F(r.pick(cand), 100); r3 = F(r.pick(cand), 100); }
    if (Fr.eq(r1, r2) || Fr.eq(r2, r3) || Fr.eq(r1, r3)) { r1 = F(1, 100); r2 = F(3, 100); r3 = F(6, 100); }
    var W = [F(ws[0], S), F(ws[1], S), F(ws[2], S)], rs = [r1, r2, r3];
    var Py = Fr.add(Fr.mul(W[0], r1), Fr.add(Fr.mul(W[1], r2), Fr.mul(W[2], r3)));
    var A2 = Fr.div(Fr.mul(W[2], r3), Py), A3 = Fr.div(Fr.mul(W[0], r1), Py);
    return { q: sc.a.join('、') + ' 三者的' + sc.w + '比為 ' + T(ws.join(':')) + '。已知' + sc.a[0] + '與' + sc.a[1] + '產生「' + sc.y + '」的比率分別為 ' + T(pc(r1)) + '、' + T(pc(r2)) + '，且' + sc.pick + '為「' + sc.y + '」的機率為 ' + T(Fr.tex(Py)) + '。' + no(1) + '求' + sc.a[2] + '產生「' + sc.y + '」的比率。' + no(2) + '已知是「' + sc.y + '」，求它來自' + sc.a[2] + '的機率。' + no(3) + '已知是「' + sc.y + '」，求它來自' + sc.a[0] + '的機率。',
             a: jo([no(1) + T(Fr.tex(r3)), no(2) + T(Fr.tex(A2)), no(3) + T(Fr.tex(A3))]),
             h: '先把比化成機率 ' + W.map(function (f) { return T(Fr.tex(f)); }).join('、') + '。把三條路徑加起來：' + T(prodF([W[0], r1]) + '+' + prodF([W[1], r2]) + '+' + Fr.tex(W[2]) + 'x=' + Fr.tex(Py)) + '，解出 ' + T('x=' + Fr.tex(r3)) + '。' + no(2) + no(3) + '是「要的那一片 ÷ 三片之和 ' + T(Fr.tex(Py)) + '」；三個分支的條件機率加起來必須是 ' + T(1) + '。',
             p: { ws: ws, r1: fp(r1), r2: fp(r2), Py: fp(Py), ans: [fp(r3), fp(A2), fp(A3)] } };
  };

  /* ── §4 兩階段：先從甲袋移一顆到乙袋 ── */
  L2.bayesTransfer = function (r) {
    var bg = r.pick(BAG), a1 = r.int(2, 5), b1 = r.int(1, 4), a2 = r.int(1, 4), b2 = r.int(1, 5);
    var c1 = bg.c[0], c2 = bg.c[1], n1 = a1 + b1, n2 = a2 + b2 + 1;
    var wA = F(a1, n1), wB = F(b1, n1);
    var qA = F(a2 + 1, n2), qB = F(a2, n2);
    var LA = Fr.mul(wA, qA), LB = Fr.mul(wB, qB), Pr = Fr.add(LA, LB);
    var LA2 = Fr.mul(wA, Fr.cp(qA)), LB2 = Fr.mul(wB, Fr.cp(qB)), Pw = Fr.add(LA2, LB2);
    var A2 = Fr.div(LA, Pr), A3 = Fr.div(LA2, Pw);
    return { q: '甲' + bg.b + '有 ' + T(a1) + ' 顆' + c1 + bg.o + '與 ' + T(b1) + ' 顆' + c2 + bg.o + '，乙' + bg.b + '有 ' + T(a2) + ' 顆' + c1 + bg.o + '與 ' + T(b2) + ' 顆' + c2 + bg.o + '。先從甲' + bg.b + '隨機取一顆放入乙' + bg.b + '，再從乙' + bg.b + '隨機取一顆。' + no(1) + '求從乙' + bg.b + '取出' + c1 + bg.o + '的機率。' + no(2) + '已知從乙' + bg.b + '取出的是' + c1 + bg.o + '，求先前移過去的也是' + c1 + bg.o + '的機率。' + no(3) + '已知從乙' + bg.b + '取出的是' + c2 + bg.o + '，求先前移過去的是' + c1 + bg.o + '的機率。',
             a: jo([no(1) + T(Fr.tex(Pr)), no(2) + T(Fr.tex(A2)), no(3) + T(Fr.tex(A3))]),
             h: '第一層是「移過去的是' + c1 + '還是' + c2 + '」：機率 ' + T(Fr.tex(wA)) + ' 與 ' + T(Fr.tex(wB)) + '。第二層的乙' + bg.b + '已經變成 ' + T(n2) + ' 顆——移' + c1 + '過去就是 ' + T(a2 + 1) + ' 顆' + c1 + '、移' + c2 + '過去就是 ' + T(a2) + ' 顆' + c1 + '。兩片葉子 ' + T(prodF([wA, qA]) + '=' + Fr.tex(LA)) + ' 與 ' + T(prodF([wB, qB]) + '=' + Fr.tex(LB)) + '，' + no(1) + '是相加、' + no(2) + '是第一片除以和。注意 ' + no(2) + '與 ' + no(3) + '的條件不同，兩者相加不會是 ' + T(1) + '。',
             p: { a1: a1, b1: b1, a2: a2, b2: b2, ans: [fp(Pr), fp(A2), fp(A3)] } };
  };

  /* ── §4 複檢：連續兩次都是同一個結果 ── */
  L2.bayesRetest = function (r) {
    var sc = r.pick(SCR), pv = F(r.pick([5, 10, 15, 20, 25, 30, 40, 50]), 100);
    var s = F(r.pick([70, 75, 80, 85, 90, 95]), 100), u = F(r.pick([5, 10, 15, 20, 25, 30]), 100);
    var d1 = Fr.mul(pv, s), n1 = Fr.mul(Fr.cp(pv), u), P1 = Fr.add(d1, n1);
    var d2 = Fr.mul(pv, Fr.mul(s, s)), n2 = Fr.mul(Fr.cp(pv), Fr.mul(u, u)), P2 = Fr.add(d2, n2);
    var A1 = P1, A2 = Fr.div(d1, P1), A3 = Fr.div(d2, P2);
    return { q: '某地區「' + sc.d + '」的比例為 ' + T(pc(pv)) + '。某檢驗：' + sc.d + '的人「' + sc.y + '」的機率為 ' + T(Fr.tex(s)) + '，' + sc.nd + '的人「' + sc.y + '」的機率為 ' + T(Fr.tex(u)) + '。' + no(1) + '求' + sc.one + '「' + sc.y + '」的機率。' + no(2) + '已知某人「' + sc.y + '」，求他' + sc.d + '的機率。' + no(3) + '對「' + sc.y + '」的人再做一次同樣的檢驗（在「是否' + sc.d + '」已知的條件下兩次檢驗互相獨立），若第二次仍「' + sc.y + '」，求他' + sc.d + '的機率。',
             a: jo([no(1) + T(Fr.tex(A1)), no(2) + T(Fr.tex(A2)), no(3) + T(Fr.tex(A3))]),
             h: no(1) + '兩條路加起來 ' + T(prodF([pv, s]) + '+' + prodF([Fr.cp(pv), u]) + '=' + Fr.tex(P1)) + '；' + no(2) + '是 ' + T('\\dfrac{' + Fr.tex(d1) + '}{' + Fr.tex(P1) + '}') + '。' + no(3) + '把 ' + no(2) + '的答案當成新的「比例」再算一次，或直接寫分子 ' + T(Fr.tex(pv) + pw(Fr.tex(s), 2) + '=' + Fr.tex(d2)) + '、分母 ' + T(Fr.tex(d2) + '+' + Fr.tex(Fr.cp(pv)) + pw(Fr.tex(u), 2) + '=' + Fr.tex(P2)) + '，兩種做法答案相同。',
             p: { pv: fp(pv), s: fp(s), u: fp(u), ans: [fp(A1), fp(A2), fp(A3)] } };
  };

  /* ── §4 盛行率改變的影響 ── */
  L2.bayesParamP = function (r) {
    var sc = r.pick(SCR), s = F(r.pick([80, 85, 90, 95, 96, 99]), 100), u = F(r.pick([1, 2, 4, 5, 10, 15, 20]), 100);
    var p1 = F(r.pick([1, 2, 5, 10]), 100), p2 = F(r.pick([20, 25, 40, 50]), 100);
    var k = r.pick([F(1, 2), F(3, 5), F(3, 4), F(9, 10), F(4, 5), F(2, 3)]);
    var f = function (p) { return Fr.div(Fr.mul(s, p), Fr.add(Fr.mul(s, p), Fr.mul(u, Fr.cp(p)))); };
    var A1 = f(p1), A2 = f(p2);
    /* s p /(s p + u(1-p)) >= k ⟺ p >= k u / (s(1-k) + k u) */
    var A3 = Fr.div(Fr.mul(k, u), Fr.add(Fr.mul(s, Fr.cp(k)), Fr.mul(k, u)));
    return { q: '某檢驗的準確度固定：' + sc.d + '的人「' + sc.y + '」的機率為 ' + T(Fr.tex(s)) + '，' + sc.nd + '的人「' + sc.y + '」的機率為 ' + T(Fr.tex(u)) + '。設某地區「' + sc.d + '」的比例為 ' + T('p') + '（' + T('0\\lt p\\lt1') + '）。' + no(1) + '當 ' + T('p=' + Fr.tex(p1)) + ' 時，求已知「' + sc.y + '」的人' + sc.d + '的機率。' + no(2) + '當 ' + T('p=' + Fr.tex(p2)) + ' 時，求同一個機率。' + no(3) + '若要使這個機率至少為 ' + T(Fr.tex(k)) + '，求 ' + T('p') + ' 的最小值。',
             a: jo([no(1) + T(Fr.tex(A1)), no(2) + T(Fr.tex(A2)), no(3) + ansEq('p', A3)]),
             h: '分子 ' + T(Fr.tex(s) + 'p') + '、分母 ' + T(Fr.tex(s) + 'p+' + Fr.tex(u) + '(1-p)') + '，上下同乘 ' + T(100) + ' 可以先把小數化掉。' + no(3) + '解 ' + T('\\dfrac{' + Fr.tex(s) + 'p}{' + Fr.tex(s) + 'p+' + Fr.tex(u) + '(1-p)}\\ge' + Fr.tex(k)) + '；分母恆為正，可以直接兩邊乘過去不必分情況，整理得 ' + T('p\\ge' + Fr.tex(A3)) + '。同一個檢驗，' + no(1) + '與 ' + no(2) + '的答案差很多——這就是盛行率的威力。',
             p: { s: fp(s), u: fp(u), p1: fp(p1), p2: fp(p2), k: fp(k), ans: [fp(A1), fp(A2), fp(A3)] } };
  };

  /* ── §4 硬幣與貝氏 ── */
  L2.bayesCoin = function (r) {
    var kk = r.int(2, 9), jj = r.pick([1, 1, 2, 3]), tot = kk + jj, m = r.int(1, 4);
    var wF = F(kk, tot), wB = F(jj, tot);
    var pf = Fr.pow(F(1, 2), m);
    var P1 = Fr.add(Fr.mul(wF, pf), wB);
    var A2 = Fr.div(wB, P1);
    var pf2 = Fr.pow(F(1, 2), m + 1), P2 = Fr.add(Fr.mul(wF, pf2), wB), A3 = Fr.div(wB, P2);
    var side = r.pick([['正面', '反面'], ['人頭', '字']]);
    return { q: '袋中有 ' + T(kk) + ' 枚公正硬幣（出現' + side[0] + '的機率 ' + T('\\dfrac12') + '）與 ' + T(jj) + ' 枚兩面都是' + side[0] + '的假硬幣。隨機取出一枚投擲 ' + T(m) + ' 次。' + no(1) + '求 ' + T(m) + ' 次都出現' + side[0] + '的機率。' + no(2) + '已知 ' + T(m) + ' 次都出現' + side[0] + '，求取到的是假硬幣的機率。' + no(3) + '承 ' + no(2) + '，若再投擲一次仍是' + side[0] + '（共 ' + T(m + 1) + ' 次都是' + side[0] + '），求取到的是假硬幣的機率。',
             a: jo([no(1) + T(Fr.tex(P1)), no(2) + T(Fr.tex(A2)), no(3) + T(Fr.tex(A3))]),
             h: '第一層是「取到公正硬幣」' + T(Fr.tex(wF)) + ' 與「取到假硬幣」' + T(Fr.tex(wB)) + '。兩片葉子：公正硬幣連出 ' + T(m) + ' 次' + side[0] + ' 是 ' + T(prodF([wF]) + pw('\\dfrac12', m) + '=' + Fr.tex(Fr.mul(wF, pf))) + '，假硬幣一定是' + side[0] + ' ⟹ 那一片就是 ' + T(Fr.tex(wB)) + '。' + no(2) + '是 ' + T('\\dfrac{' + Fr.tex(wB) + '}{' + Fr.tex(P1) + '}') + '；' + no(3) + '只是把指數從 ' + T(m) + ' 換成 ' + T(m + 1) + '，證據越多越偏向假硬幣。',
             p: { kk: kk, jj: jj, m: m, ans: [fp(P1), fp(A2), fp(A3)] } };
  };

  /* ══════════════════════════════════════════════════════════ */
  /* ══════════════════════════════════════════════════════════
     L1 解題步驟（s：每步一段 HTML）與第一層提示（h1：只講「這是哪一型、第一步做什麼」，不帶數字）
     全部由 p（與 o.q、o.a）重算，所以與題目、答案一定一致；答案由頁面另行附在步驟後。
     用法：用 splice_all_11b3.py 插在 META（var META_L1 = [）之前，並把 wrapAll(L1) 換成 wrapAll(L1, L1_SOL, L1_H1)。
     自己加的小工具一律加前綴 sx；產生器的通用工具（F／Fr／T／prod／prodF／CT／nCr／binTex／binP／lg…）可直接用。
     課綱界線（HANDOUT_SPEC §4）：不出現隨機變數／二項分布／期望值／變異數；
     不用「全機率公式」這個名詞（說「把所有路徑加起來」）；
     不用偽陽性／偽陰性／敏感度／特異度（一律用中文描述）。
     ══════════════════════════════════════════════════════════ */
  function sxF(t) { return F(t[0], t[1]); }                       /* p 裡的 [n,d] 還原成分數 */
  function sxFin(o) { return '答案：' + o.a + '。'; }
  function sxEq(raw, red) { return raw === red ? raw : raw + '=' + red; }   /* 代入式已是最簡就不再寫一次 */
  function sxFr(n, d) { return sxEq('\\dfrac{' + n + '}{' + d + '}', Fr.tex(F(n, d))); }
  function sxSet(a) { return '\\{' + a.join(',') + '\\}'; }
  function sxPlus(list, tot) { return sxEq(list.join('+'), String(tot)); }
  function sxAddF(list) { return sxEq(list.map(function (f) { return Fr.tex(f); }).join('+'), Fr.tex(sumF(list))); }
  function sxDiv(x, y, v) { return Fr.tex(x) + '\\div' + Fr.tex(y) + '=' + Fr.tex(v); }
  function sxM(q, re, d) { var m = q.match(re); return m ? m[1] : d; }
  function sxQ(q) { var m = q.match(/「[^」]*」/g) || [], i, o = []; for (i = 0; i < m.length; i++) o.push(m[i].slice(1, -1)); return o; }
  /* 百分之一為單位的整數 → 小數字串（0.45、1、1.05） */
  function sxDec(c) {
    var sg = c < 0 ? '-' : '', i, f, s;
    c = Math.abs(c); i = Math.floor(c / 100); f = c % 100; s = String(i);
    if (f) s += '.' + (f < 10 ? '0' + f : String(f)).replace(/0$/, '');
    return sg + s;
  }
  /* 一顆骰子的事件敘述 → 點數清單（認不出來回傳 null） */
  function sxDieL(t) {
    var m = t.match(/\$(\d+)\$/), k = m ? parseInt(m[1], 10) : 0, out = [], n, ok;
    for (n = 1; n <= 6; n++) {
      if (t.indexOf('奇數') >= 0) ok = n % 2 === 1;
      else if (t.indexOf('倍數') >= 0) ok = k > 0 && n % k === 0;
      else if (t.indexOf('偶數') >= 0) ok = n % 2 === 0;
      else if (t.indexOf('質數') >= 0) ok = (n === 2 || n === 3 || n === 5);
      else if (t.indexOf('至少為') >= 0) ok = n >= k;
      else if (t.indexOf('不超過') >= 0) ok = n <= k;
      else if (t.indexOf('大於') >= 0) ok = n > k;
      else if (t.indexOf('小於') >= 0) ok = n < k;
      else return null;
      if (ok) out.push(n);
    }
    return out;
  }
  /* 兩顆骰子的事件敘述 → 有序對清單 */
  function sxDie2L(t) {
    var m = t.match(/\$(\d+)\$/), k = m ? parseInt(m[1], 10) : 0, out = [], a, b, ok;
    for (a = 1; a <= 6; a++) for (b = 1; b <= 6; b++) {
      if (t.indexOf('和為偶數') >= 0) ok = (a + b) % 2 === 0;
      else if (t.indexOf('和大於') >= 0) ok = a + b > k;
      else if (t.indexOf('和為') >= 0) ok = a + b === k;
      else if (t.indexOf('至少有一顆') >= 0) ok = (a === k || b === k);
      else if (t.indexOf('點數相同') >= 0) ok = a === b;
      else if (t.indexOf('點數相異') >= 0) ok = a !== b;
      else if (t.indexOf('差為') >= 0) ok = Math.abs(a - b) === k;
      else if (t.indexOf('乘積為') >= 0) ok = a * b === k;
      else return null;
      if (ok) out.push([a, b]);
    }
    return out;
  }
  function sxPairs(L) { return '\\{' + L.map(function (e) { return '(' + e[0] + ',' + e[1] + ')'; }).join(',') + '\\}'; }
  function sxIn(L, e) { var i; for (i = 0; i < L.length; i++) if (L[i][0] === e[0] && L[i][1] === e[1]) return true; return false; }
  /* 撲克牌事件敘述 → [花色,點數] 清單（花色 0 紅心 1 方塊 2 黑桃 3 梅花） */
  function sxCardL(t) {
    var m = t.match(/\$(\d+)\$/), k = m ? parseInt(m[1], 10) : 0, out = [], s, v, ok;
    for (s = 0; s < 4; s++) for (v = 1; v <= 13; v++) {
      if (t.indexOf('不是花牌') >= 0) ok = v < 11;
      else if (t.indexOf('花牌') >= 0) ok = v >= 11;
      else if (t.indexOf('紅心或黑桃') >= 0) ok = (s === 0 || s === 2);
      else if (t.indexOf('紅心') >= 0) ok = s === 0;
      else if (t.indexOf('黑桃') >= 0) ok = s === 2;
      else if (t.indexOf('梅花') >= 0) ok = s === 3;
      else if (t.indexOf('紅色') >= 0) ok = s < 2;
      else if (t.indexOf('黑色') >= 0) ok = s >= 2;
      else if (t.indexOf('倍數') >= 0) ok = k > 0 && v % k === 0;
      else if (t.indexOf('偶數') >= 0) ok = v % 2 === 0;
      else if (t.indexOf('不超過') >= 0) ok = v <= k;
      else if (t.indexOf('大於') >= 0) ok = v > k;
      else if (t.indexOf('小於') >= 0) ok = v < k;
      else if (t.indexOf('是 K') >= 0) ok = v === 13;
      else if (t.indexOf('是 A') >= 0) ok = v === 1;
      else return null;
      if (ok) out.push([s, v]);
    }
    return out;
  }
  /* 牌數的來源說明：只看點數 ⟹ 4 張一組；只看花色 ⟹ 13 張一組 */
  function sxCardWhy(L) {
    var vs = {}, ss = {}, i, nv = 0, ns = 0, k;
    for (i = 0; i < L.length; i++) { vs[L[i][1]] = (vs[L[i][1]] || 0) + 1; ss[L[i][0]] = (ss[L[i][0]] || 0) + 1; }
    for (k in vs) if (vs[k] === 4) nv++;
    for (k in ss) if (ss[k] === 13) ns++;
    if (nv * 4 === L.length) return nv === 1 ? '（同一種點數有 ' + T('4') + ' 張）' : '（' + T(String(nv)) + ' 種點數各 ' + T('4') + ' 張，' + T('4\\times' + nv + '=' + L.length) + '）';
    if (ns * 13 === L.length) return ns === 1 ? '（一種花色有 ' + T('13') + ' 張）' : '（' + T(String(ns)) + ' 種花色各 ' + T('13') + ' 張，' + T('13\\times' + ns + '=' + L.length) + '）';
    return '';
  }
  /* 列聯表題幹 → 列標籤、欄標籤與單位 */
  function sxTab(q) {
    var m = q.match(/「([^」]+)」且「([^」]+)」/g) || [], r = [], c = [], i, mm;
    for (i = 0; i < m.length; i++) { mm = m[i].match(/「([^」]+)」且「([^」]+)」/); r.push(mm[1]); c.push(mm[2]); }
    return { r: [r[0], r[2]], c: [c[0], c[1]], u: sxM(q, /」有 \$\d+\$ (\S)/, '') };
  }
  /* 抽象事件：把樣本空間切成四塊 [A∩B, A∩B', A'∩B, A'∩B'] */
  var SX_S = { 'A': [1, 1, 0, 0], "A'": [0, 0, 1, 1], 'B': [1, 0, 1, 0], "B'": [0, 1, 0, 1] };
  function sxMask(e) {
    var ps = e.split(/\\cap|\\cup/), u = e.indexOf('\\cup') >= 0, v = SX_S[ps[0].trim()].slice(), i, k, w;
    for (k = 1; k < ps.length; k++) {
      w = SX_S[ps[k].trim()];
      for (i = 0; i < 4; i++) v[i] = u ? ((v[i] || w[i]) ? 1 : 0) : ((v[i] && w[i]) ? 1 : 0);
    }
    return v;
  }
  function sxBlkVal(mk, m) { var s = F(0), i; for (i = 0; i < 4; i++) if (mk[i]) s = Fr.add(s, m[i]); return s; }
  function sxBlkTex(mk, m) { var t = [], i; for (i = 0; i < 4; i++) if (mk[i]) t.push(Fr.tex(m[i])); return t.join('+'); }
  /* 一個目標式（集合式或條件式）→ 'P(…)=…=值' */
  function sxLine(e, m) {
    var k = e.indexOf('\\mid'), L, R, num, den;
    if (k < 0) { return PTx(e) + '=' + sxEq(sxBlkTex(sxMask(e), m), Fr.tex(sxBlkVal(sxMask(e), m))); }
    L = e.slice(0, k).trim(); R = e.slice(k + 4).trim();
    num = sxBlkVal(sxMask(L + '\\cap' + R), m); den = sxBlkVal(sxMask(R), m);
    return PTx(e) + '=' + sxDiv(num, den, Fr.div(num, den));
  }
  /* 四塊機率的推導：先求交集，再用減法補完 */
  function sxBlk1(m, g2) {
    var a = Fr.add(m[0], m[1]), b = Fr.add(m[0], m[2]), u = Fr.add(Fr.add(m[0], m[1]), m[2]);
    if (g2 === 'A\\cap B') return '已知直接給了 ' + T(PTx('A\\cap B') + '=' + Fr.tex(m[0])) + '。';
    if (g2 === 'A\\cup B') return '由 ' + T(PTx('A\\cap B') + '=' + PTx('A') + '+' + PTx('B') + '-' + PTx('A\\cup B') + '=' + Fr.tex(a) + '+' + Fr.tex(b) + '-' + Fr.tex(u) + '=' + Fr.tex(m[0])) + '。';
    if (g2 === "A'\\cap B'") return '先由 ' + T(PTx('A\\cup B') + '=1-' + PTx("A'\\cap B'") + '=1-' + Fr.tex(m[3]) + '=' + Fr.tex(u)) + '，再 ' + T(PTx('A\\cap B') + '=' + Fr.tex(a) + '+' + Fr.tex(b) + '-' + Fr.tex(u) + '=' + Fr.tex(m[0])) + '。';
    return '由 ' + T(PTx('A\\cap B') + '=' + PTx('A') + '-' + PTx("A\\cap B'") + '=' + Fr.tex(a) + '-' + Fr.tex(m[1]) + '=' + Fr.tex(m[0])) + '。';
  }
  function sxBlk2(m) {
    var a = Fr.add(m[0], m[1]), b = Fr.add(m[0], m[2]), u = Fr.add(Fr.add(m[0], m[1]), m[2]);
    return '其餘三塊用減法補完：' + T(PTx("A\\cap B'") + '=' + Fr.tex(a) + '-' + Fr.tex(m[0]) + '=' + Fr.tex(m[1])) + '、'
      + T(PTx("A'\\cap B") + '=' + Fr.tex(b) + '-' + Fr.tex(m[0]) + '=' + Fr.tex(m[2])) + '、'
      + T(PTx("A'\\cap B'") + '=1-' + Fr.tex(u) + '=' + Fr.tex(m[3])) + '。';
  }
  function sxTgs(tg, m, lo, hi) {
    var t = [], i;
    for (i = lo; i <= hi && i < tg.length; i++) t.push(no(i + 1) + T(sxLine(tg[i], m)));
    return t.join('　');
  }

  var L1_H1 = {
    freqTable: '這是「從次數表得到客觀機率」：客觀機率就是相對次數，分母一律是總次數，先把符合事件的那幾類次數加起來當分子。',
    subjCheck: '這是「檢視主觀機率的合理性」：逐條對照三個性質——機率要落在零與一之間、互斥又窮盡的機率和要恰好是一、子事件的機率不能比包含它的事件大。',
    tableThree: '這是「列聯表的三種機率」：邊際與聯合的分母都是總數，只有條件機率要把分母換成「已知」那一類的合計。',
    probRules: '這是「機率的基本性質」：把樣本空間切成四塊互斥的區域，先解出兩事件同時發生的那一塊，其餘用減法補完，要哪一個就把對應的塊加起來。',
    condDice: '這是「條件機率：直接數縮小後的樣本空間」：「已知」只做一件事——把分母從原來的全部結果換成符合已知條件的那些結果。',
    condFormula: '這是「用公式算條件機率」：先把四塊機率補完，再記住直線後面的那個事件才是分母。',
    condTable: '這是「從列聯表讀條件機率」：兩個事件的順序一換，分母就從這一列的合計換成這一欄的合計，分子則是同一格。',
    multRule: '這是「乘法公式」：把條件機率的定義兩邊同乘條件事件的機率就得到交集的機率，再用減法補完其餘各塊。',
    condInverse: '這是「已知條件機率反求其他機率」：先用乘法版求出交集，再用除法版把另一個邊際機率反解出來。',
    drawBalls: '這是「放回與不放回」：放回時每次的狀況都一樣、兩次互相獨立；不放回時第二次的分母要少一顆，而且要看第一次抽走了什麼。',
    treeThree: '這是「三層樹狀圖」：沿著一條路徑把機率連乘就是那條路徑的機率，要問的事件包含幾條路徑就把它們加起來。',
    cardKids: '這是「直接數縮小後的樣本空間」：不必套公式，把符合已知條件的結果數出來當分母，其中又符合所求的當分子。',
    indepCheck: '這是「判斷兩事件是否獨立」：算出交集的機率與兩個機率的乘積，相等才叫獨立——看數字湊不湊得起來，不是看意義像不像有關。',
    indepVsExcl: '這是「獨立與互斥的辨析」：互斥是交集的機率為零、獨立是交集的機率等於兩個機率相乘，機率都不為零時兩者不可能同時成立。',
    indepTable: '這是「從列聯表判斷獨立」：兩列的內部比例一樣就是獨立，四格交叉相乘相等講的是同一件事。',
    repeatTrial: '這是「重複試驗恰有幾次成功」：先問「哪幾次成功」有幾種選法，再乘上成功與失敗各自的機率次方。',
    atLeastOne: '這是「至少一次」：看到「至少」先寫反面，用一減去「一次也沒有」的機率。',
    threeIndep: '這是「三個機率不同的獨立事件」：不能用同一個機率的次方，要各自取反面再連乘；「恰有一個」得把幾種情形分別算完再相加。',
    needTrials: '這是「要試幾次才夠」：先列出「一次也沒成功」的機率小於某個值的不等式，兩邊取常用對數，因為底數小於一，除過去時不等號要變向。',
    totalPath: '這是「把所有路徑加起來」：先把第一層的比例化成機率，再沿每條路徑相乘，最後把同一種結果的所有路徑加起來。',
    bayesTwo: '這是「兩分支的貝氏」：畫兩層樹狀圖算出每片葉子，分母是同一種結果的所有葉子之和，分子是指定來源的那一片。',
    bayesScreen: '這是「篩檢問題」：假設一個很大的整數人數，把四格人數填出來再讀表最快；分母是檢驗結果相同的那一整群人。',
    bayesThree: '這是「三分支的貝氏」：比先化成機率，三片葉子各自相乘，分母是三片相加、分子是要的那一片。',
    bayesTable: '這是「貝氏與列聯表」：先把比例全部換成整數人數填進四格，再用橫加等於直加驗算，最後兩小題只是換分母。',
    condCombo: '這是「條件機率與排列組合」：關鍵是把符合已知條件的取法數對，分子與分母要用同一種算法。',
    typeIdent: '這是「題型辨識」：先看分母該是總數、某一列的合計、還是某一欄的合計；放回抽取才是獨立重複。'
  };

  var L1_SOL = {};

  /* ── §1 客觀機率與機率的基本性質 ── */
  L1_SOL.freqTable = function (p, o) {
    var N = p.N, A = p.ans.map(sxF);
    if (p.kind === 0) {
      var f = p.f, LA = sxDieL(p.e1), LB = sxDieL(p.e2);
      var n1 = A[0].n * (N / A[0].d), n2 = A[1].n * (N / A[1].d), cnt = A[2].n * (6 / A[2].d);
      var lst = function (L) { return L ? T(sxSet(L)) : '題幹圈出的那幾點'; };
      var add = function (L, tot) {
        var ns, i, s = 0;
        if (!L) return T(String(tot));
        ns = L.map(function (v) { return f[v - 1]; });
        for (i = 0; i < ns.length; i++) s += ns[i];
        return T(s === tot ? sxPlus(ns, tot) : String(tot));
      };
      return ['客觀機率就是相對次數：分母固定是總次數 ' + T(String(N)) + '。符合「' + p.e1 + '」的點數是 ' + lst(LA) + '，把這幾點的次數加起來 ' + add(LA, n1) + '。',
        '所以 ' + no(1) + T(sxFr(n1, N)) + '；同法，符合「' + p.e2 + '」的點數是 ' + lst(LB) + '，次數合計 ' + add(LB, n2) + ' ⟹ ' + no(2) + T(sxFr(n2, N)) + '。',
        no(3) + '公正骰子每一點的機率都是 ' + T('\\dfrac{1}{6}') + '，而符合「' + p.e1 + '」的點數有 ' + T(String(cnt)) + ' 個 ⟹ 理論值 ' + T(sxFr(cnt, 6)) + '（和 ' + no(1) + '的實際相對次數不一定相等）。' + sxFin(o)];
    }
    var cs = p.cs, ks = p.ks, ask = p.ask;
    var c0 = cs[ks.indexOf(ask[0])], c1 = cs[ks.indexOf(ask[1])], c2 = cs[ks.indexOf(ask[2])];
    return ['客觀機率就是相對次數，分母一律是總數 ' + T(String(N)) + '。' + no(1) + '「' + ask[0] + '」的次數是 ' + T(String(c0)) + ' ⟹ ' + T(sxFr(c0, N)) + '。',
      no(2) + '「' + ask[0] + '」與「' + ask[1] + '」互斥，次數可以直接相加：' + T(c0 + '+' + c1 + '=' + (c0 + c1)) + ' ⟹ ' + T(sxFr(c0 + c1, N)) + '。',
      no(3) + '「不是' + ask[2] + '」走餘事件最快：' + T(N + '-' + c2 + '=' + (N - c2)) + ' ⟹ ' + T(sxFr(N - c2, N)) + '。' + sxFin(o)];
  };

  L1_SOL.subjCheck = function (p, o) {
    var its = o.q.split(/\(\d\) /).slice(1), out = [], i;
    for (i = 0; i < 3; i++) {
      var law = p.laws[i], ok = p.ans[i] === 1, txt = its[i] || '';
      var nums = (txt.match(/\$-?[\d.]+\$/g) || []).map(function (t) { return t.slice(1, -1); });
      var ev = sxQ(txt), line = no(i + 1);
      if (law === '①') {
        line += '只給一個機率 ' + T(nums[0]) + '：性質 ① 要求它落在 ' + T('0') + ' 與 ' + T('1') + ' 之間，'
          + (ok ? '確實在範圍內 ⟹ 合理。' : '它跑到範圍外 ⟹ 不合理，違反性質 ①。');
      } else if (law === '②') {
        var c = 0, j;
        for (j = 0; j < nums.length; j++) c += Math.round(parseFloat(nums[j]) * 100);
        line += '三種情形互斥又窮盡，性質 ② 要求機率和恰好是 ' + T('1') + '：' + T(nums.join('+') + '=' + sxDec(c)) + '，'
          + (ok ? '正好是 ' + T('1') + ' ⟹ 合理。' : '不是 ' + T('1') + ' ⟹ 不合理，違反性質 ②。');
      } else {
        line += '「' + (ev[1] || '後者') + '」包含於「' + (ev[0] || '前者') + '」，性質 ③ 要求子事件的機率不可以比較大：比 ' + T(nums[1]) + ' 與 ' + T(nums[0]) + '，'
          + (ok ? '子事件的比較小 ⟹ 合理。' : '子事件反而比較大 ⟹ 不合理，違反性質 ③。');
      }
      out.push(line);
    }
    out[2] += sxFin(o);
    return out;
  };

  L1_SOL.tableThree = function (p, o) {
    var M = p.M, ri = p.ri, ci = p.ci, N = rowSum(M, 0) + rowSum(M, 1), lb = sxTab(o.q);
    var R = rowSum(M, ri), C = colSum(M, ci), cell = M[ri][ci];
    return ['先把合計算出來：「' + lb.r[ri] + '」這一列 ' + T(M[ri][0] + '+' + M[ri][1] + '=' + R) + '，「' + lb.c[ci] + '」這一欄 ' + T(M[0][ci] + '+' + M[1][ci] + '=' + C) + '，全部共 ' + T(String(N)) + ' ' + lb.u + '。',
      no(1) + '邊際機率的分母是總數：' + T(sxFr(R, N)) + '；' + no(2) + '聯合機率的分子是同時符合兩個條件的那一格 ' + T(String(cell)) + '，分母一樣是總數：' + T(sxFr(cell, N)) + '。',
      no(3) + '條件機率要把分母換成「已知」那一類的合計：已知「' + lb.r[ri] + '」⟹ 分母改成 ' + T(String(R)) + '，' + T(sxFr(cell, R)) + '；' + no(4) + '已知「' + lb.c[ci] + '」⟹ 分母改成 ' + T(String(C)) + '，' + T(sxFr(cell, C)) + '（分子都是同一格）。' + sxFin(o)];
  };

  L1_SOL.probRules = function (p, o) {
    var m = p.m.map(sxF);
    return ['把樣本空間切成四塊互斥的區域 ' + T(PTx('A\\cap B')) + '、' + T(PTx("A\\cap B'")) + '、' + T(PTx("A'\\cap B")) + '、' + T(PTx("A'\\cap B'")) + '（四塊相加為 ' + T('1') + '）。' + sxBlk1(m, p.giv[2]),
      sxBlk2(m),
      '要哪一個值，就把對應的塊加起來：' + sxTgs(p.tg, m, 0, 2) + '。' + sxFin(o)];
  };

  /* ── §2 條件機率 ── */
  L1_SOL.condDice = function (p, o) {
    var nB = p.nB, nAB = p.nAB;
    if (p.kind === 0) {
      var LB = sxDieL(p.eB), LA = sxDieL(p.eA);
      var LAB = (LB && LA) ? LB.filter(function (v) { return LA.indexOf(v) >= 0; }) : null;
      var okB = !!(LB && LB.length === nB), okAB = !!(LAB && LAB.length === nAB);
      return ['「已知」只做一件事：把樣本空間換掉。原本是 ' + T(sxSet([1, 2, 3, 4, 5, 6])) + ' 共 ' + T('6') + ' 個結果；符合「' + p.eB + '」的' + (okB ? '是 ' + T(sxSet(LB)) + '，' : '') + '共 ' + T(String(nB)) + ' 個 ⟹ 新的分母是 ' + T(String(nB)) + ' 而不是 ' + T('6') + '。',
        '在這 ' + T(String(nB)) + ' 個結果裡，再挑出同時符合「' + p.eA + '」的：' + (okAB ? T(sxSet(LAB)) + '，' : '') + '共 ' + T(String(nAB)) + ' 個。',
        '所求 ' + T(PTx('A\\mid B') + '=\\dfrac{n(A\\cap B)}{n(B)}=' + sxFr(nAB, nB)) + '。' + sxFin(o)];
    }
    var PB = sxDie2L(p.eB), PA = sxDie2L(p.eA);
    var PAB = (PB && PA) ? PB.filter(function (e) { return sxIn(PA, e); }) : null;
    var sB = (PB && PB.length === nB && nB <= 12) ? '，也就是 ' + T(sxPairs(PB)) : '';
    var sAB = (PAB && PAB.length === nAB && nAB <= 12) ? T(sxPairs(PAB)) + '，' : '';
    return ['兩顆骰子可分辨 ⟹ 全部有 ' + T('6\\times6=36') + ' 種有序結果。符合「' + p.eB + '」的有 ' + T(String(nB)) + ' 種' + sB + '，這 ' + T(String(nB)) + ' 種就是縮小後的樣本空間。',
      '在這 ' + T(String(nB)) + ' 種裡，同時符合「' + p.eA + '」的有 ' + sAB + '共 ' + T(String(nAB)) + ' 種。',
      '所求 ' + T(PTx('A\\mid B') + '=\\dfrac{n(A\\cap B)}{n(B)}=' + sxFr(nAB, nB)) + '（分母不是 ' + T('36') + '）。' + sxFin(o)];
  };

  L1_SOL.condFormula = function (p, o) {
    var m = p.m.map(sxF);
    return ['先把四塊機率補完：' + sxBlk1(m, p.giv[2]) + sxBlk2(m),
      '條件機率 ' + T(PTx('X\\mid Y') + '=\\dfrac{' + PTx('X\\cap Y') + '}{' + PTx('Y') + '}') + '，直線後面的才是分母：' + sxTgs(p.tg, m, 0, 1) + '。',
      '同法算後兩個（注意 ' + T(PTx("A\\mid B'")) + ' 不能寫成 ' + T('1-' + PTx('A\\mid B')) + '）：' + sxTgs(p.tg, m, 2, 3) + '。' + sxFin(o)];
  };

  L1_SOL.condTable = function (p, o) {
    var M = p.M, ri = p.ri, ci = p.ci, lb = sxTab(o.q);
    var R = rowSum(M, ri), R2 = rowSum(M, 1 - ri), C = colSum(M, ci), cell = M[ri][ci], cell2 = M[1 - ri][ci];
    var a1 = F(cell, R), a3 = F(cell2, R2), a4 = Fr.div(a1, a3);
    return ['先算三個合計：「' + lb.r[ri] + '」' + T(M[ri][0] + '+' + M[ri][1] + '=' + R) + '、「' + lb.r[1 - ri] + '」' + T(M[1 - ri][0] + '+' + M[1 - ri][1] + '=' + R2) + '、「' + lb.c[ci] + '」' + T(M[0][ci] + '+' + M[1][ci] + '=' + C) + '。',
      no(1) + '已知「' + lb.r[ri] + '」⟹ 分母是這一列的合計：' + T(sxFr(cell, R)) + '；' + no(2) + '已知「' + lb.c[ci] + '」⟹ 分母換成這一欄的合計：' + T(sxFr(cell, C)) + '（分子都是同一格的 ' + T(String(cell)) + '，順序一換分母就不同）。',
      no(3) + '換成另一列：' + T(sxFr(cell2, R2)) + '；' + no(4) + '要比較兩群的風險就得比這兩個條件機率（不能拿 ' + T(String(cell)) + ' 與 ' + T(String(cell2)) + ' 直接比，因為兩列的合計 ' + T(String(R)) + ' 與 ' + T(String(R2)) + ' 不一樣）：' + T(sxDiv(a1, a3, a4)) + '。' + sxFin(o)];
  };

  L1_SOL.multRule = function (p, o) {
    var m = p.m.map(sxF), a = Fr.add(m[0], m[1]), b = Fr.add(m[0], m[2]), u = Fr.add(a, m[2]), cd = Fr.div(m[0], a);
    return ['乘法公式就是把 ' + T(PTx('B\\mid A') + '=\\dfrac{' + PTx('A\\cap B') + '}{' + PTx('A') + '}') + ' 兩邊同乘 ' + T(PTx('A')) + '：' + T(PTx('A\\cap B') + '=' + PTx('A') + PTx('B\\mid A') + '=' + prodF([a, cd]) + '=' + Fr.tex(m[0])) + '。',
      '再用減法補完四塊：' + T(PTx("A\\cap B'") + '=' + PTx('A') + '-' + PTx('A\\cap B') + '=' + Fr.tex(a) + '-' + Fr.tex(m[0]) + '=' + Fr.tex(m[1])) + '、' + T(PTx("A'\\cap B") + '=' + PTx('B') + '-' + PTx('A\\cap B') + '=' + Fr.tex(b) + '-' + Fr.tex(m[0]) + '=' + Fr.tex(m[2])) + '、' + T(PTx("A'\\cap B'") + '=1-' + Fr.tex(u) + '=' + Fr.tex(m[3])) + '。',
      '四塊到齊，要哪一個就把對應的塊加起來（條件機率則是相除）：' + sxTgs(p.tg, m, 0, 2) + '。' + sxFin(o)];
  };

  L1_SOL.condInverse = function (p, o) {
    var m = p.m.map(sxF), giv = p.giv, a = Fr.add(m[0], m[1]), b = Fr.add(m[0], m[2]);
    var X = giv[0], Y = X === 'A' ? 'B' : 'A';
    var PX = X === 'A' ? a : b, PY = X === 'A' ? b : a;
    var mulE = Y + '\\mid ' + X, divE = X + '\\mid ' + Y;
    var mulV = Fr.div(m[0], PX), divV = Fr.div(m[0], PY);
    return ['先用乘法版求交集：' + T(PTx(X + '\\cap ' + Y) + '=' + PTx(X) + PTx(mulE) + '=' + prodF([PX, mulV]) + '=' + Fr.tex(m[0])) + '。',
      '再用除法版把另一個邊際機率反解出來：' + T(PTx(divE) + '=\\dfrac{' + PTx('A\\cap B') + '}{' + PTx(Y) + '}') + ' ⟹ ' + T(PTx(Y) + '=' + sxDiv(m[0], divV, PY)) + '。',
      '四塊依序是 ' + T(Fr.tex(m[0])) + '、' + T(Fr.tex(m[1])) + '、' + T(Fr.tex(m[2])) + '、' + T(Fr.tex(m[3])) + '（相加為 ' + T('1') + '），要哪一個就把對應的塊加起來：' + sxTgs(p.tg, m, 0, 2) + '。' + sxFin(o)];
  };

  L1_SOL.drawBalls = function (p, o) {
    var a = p.a, b = p.b, n = a + b, A = p.ans.map(sxF), c1 = sxM(o.q, /顆([^顆與]+)與/, '指定顏色的球');
    var p1 = F(a, n);
    if (p.back) {
      return ['每次抽完都放回 ⟹ ' + T(String(n)) + ' 顆球的組成完全沒變，兩次互相獨立，每一次抽到' + c1 + '的機率都是 ' + T(sxFr(a, n)) + '。',
        no(1) + '兩次都要：' + T(prodF([p1, p1]) + '=' + Fr.tex(A[0])) + '；' + no(2) + '「恰有一次」有「先' + c1 + '後不是」與「先不是後' + c1 + '」兩種順序，各算一次再相加 ⟹ ' + T(prodF([p1, F(b, n)]) + '+' + prodF([F(b, n), p1]) + '=' + Fr.tex(A[1])) + '。',
        no(3) + '第二次抽的時候球的組成還是一樣 ⟹ ' + T(Fr.tex(A[2])) + '；' + no(4) + '放回表示第一次的結果完全不影響第二次，所以條件機率就等於 ' + no(3) + '的 ' + T(Fr.tex(A[3])) + '。' + sxFin(o)];
    }
    return ['不放回 ⟹ 第一次是從 ' + T(String(n)) + ' 顆裡抽，第二次只剩 ' + T(String(n - 1)) + ' 顆，而且要看第一次抽走了什麼。第一次抽到' + c1 + '的機率是 ' + T(sxFr(a, n)) + '。',
      no(1) + '兩次都是' + c1 + '：第一次後' + c1 + '只剩 ' + T(String(a - 1)) + ' 顆 ⟹ ' + T(prodF([p1, F(a - 1, n - 1)]) + '=' + Fr.tex(A[0])) + '；' + no(2) + '「恰有一次」把兩種順序加起來 ' + T(prodF([p1, F(b, n - 1)]) + '+' + prodF([F(b, n), F(a, n - 1)]) + '=' + Fr.tex(A[1])) + '。',
      no(3) + '第二次是' + c1 + '要把「第一次也是」與「第一次不是」兩條路加起來：' + T(prodF([p1, F(a - 1, n - 1)]) + '+' + prodF([F(b, n), F(a, n - 1)]) + '=' + Fr.tex(A[2])) + '（和第一次一樣公平）；' + no(4) + '已知第一次是' + c1 + '，剩下的 ' + T(String(n - 1)) + ' 顆裡有 ' + T(String(a - 1)) + ' 顆' + c1 + ' ⟹ ' + T(sxFr(a - 1, n - 1)) + '。' + sxFin(o)];
  };

  L1_SOL.treeThree = function (p, o) {
    var w = p.w, l = p.l, n = w + l, A = p.ans.map(sxF), y = sxQ(o.q)[0] || '要的那一種';
    var w1 = F(w, n), l1 = F(l, n), pth = [prodF([w1, F(l, n - 1), F(l - 1, n - 2)])];
    return ['全部 ' + T(String(n)) + ' 個之中「' + y + '」有 ' + T(String(w)) + ' 個。不放回 ⟹ 每抽走一個，總數就少一個：第一位面對 ' + T(String(n)) + ' 個、第二位 ' + T(String(n - 1)) + ' 個、第三位 ' + T(String(n - 2)) + ' 個。',
      no(1) + '沿著「第一位中、第二位沒中、第三位沒中」這一條路徑連乘：' + T(pth[0] + '=' + Fr.tex(A[0])) + '。',
      no(2) + '抽到「' + y + '」的可以是三人中任一位，三條路徑的機率完全相同 ⟹ ' + T('3\\times' + par(Fr.tex(A[0])) + '=' + Fr.tex(A[1])) + '。',
      no(3) + '第二位要把「第一位也中」與「第一位沒中」兩條路加起來：' + T(prodF([w1, F(w - 1, n - 1)]) + '+' + prodF([l1, F(w, n - 1)]) + '=' + Fr.tex(A[2])) + '（結果和第一位一樣，先抽後抽一樣公平）；' + no(4) + '三人都中：' + (w < 3 ? '「' + y + '」一共只有 ' + T(String(w)) + ' 個，不夠三個人分 ⟹ ' + T('0') : T(prodF([w1, F(w - 1, n - 1), F(w - 2, n - 2)]) + '=' + Fr.tex(A[3]))) + '。' + sxFin(o)];
  };

  L1_SOL.cardKids = function (p, o) {
    if (p.kind === 0) {
      var nB = p.nB, nAB = p.nAB, LB = sxCardL(p.eB), LA = sxCardL(p.eA);
      var LAB = (LB && LA) ? LB.filter(function (e) { return sxIn(LA, e); }) : null;
      var wB = (LB && LB.length === nB) ? sxCardWhy(LB) : '';
      var wAB = (LAB && LAB.length === nAB) ? sxCardWhy(LAB) : '';
      return ['一副牌有 ' + T('52') + ' 張。已知' + p.eB + ' ⟹ 樣本空間縮小成符合它的 ' + T(String(nB)) + ' 張' + wB + '，這 ' + T(String(nB)) + ' 張就是新的分母。',
        '在這 ' + T(String(nB)) + ' 張裡，再數出同時符合「' + p.eA + '」的有 ' + T(String(nAB)) + ' 張' + wAB + '。',
        '所求 ' + T('\\dfrac{n(A\\cap B)}{n(B)}=' + sxFr(nAB, nB)) + '。' + sxFin(o)];
    }
    var k = p.k, least = p.least, tot = Math.pow(2, k), g = sxM(o.q, /個是([^，]+)，/, '指定的性別');
    var cs = [], ns = [], i, nb = 0, nab = p.allSame ? 1 : nCr(k, least);
    for (i = least; i <= k; i++) { cs.push(T(CT(k, i) + '=' + nCr(k, i))); ns.push(nCr(k, i)); nb += nCr(k, i); }
    return ['把 ' + T(String(k)) + ' 個小孩的性別依出生順序排成一列，樣本空間有 ' + T('2^' + k + '=' + tot) + ' 種（同樣是一個' + g + '，排在第幾個要算成不同的結果）。',
      '「至少 ' + T(String(least)) + ' 個' + g + '」要把恰好 ' + T(String(least)) + ' 個一直到 ' + T(String(k)) + ' 個的種數加起來：' + cs.join('、') + ' ⟹ ' + T(sxPlus(ns, nb)) + ' 種，分母不再是 ' + T(String(tot)) + '。',
      '其中' + (p.allSame ? T(String(k)) + ' 個都是' + g + '的只有 ' + T(String(nab)) + ' 種' : '恰有 ' + T(String(least)) + ' 個' + g + '的有 ' + T(CT(k, least) + '=' + nab) + ' 種') + ' ⟹ ' + T(sxFr(nab, nb)) + '。' + sxFin(o)];
  };

  /* ── §3 獨立性與重複試驗 ── */
  L1_SOL.indepCheck = function (p, o) {
    var A = p.ans.map(sxF);
    if (p.kind === 2) {
      var LA = sxDieL(p.eA), LB = sxDieL(p.eB);
      var LAB = (LA && LB) ? LA.filter(function (v) { return LB.indexOf(v) >= 0; }) : null;
      var nA = A[0].n * (6 / A[0].d), nB = A[1].n * (6 / A[1].d), nAB = A[2].n * (6 / A[2].d);
      var sA = (LA && LA.length === nA) ? T(sxSet(LA)) + '，' : '', sB = (LB && LB.length === nB) ? T(sxSet(LB)) + '，' : '';
      var sAB = nAB === 0 ? '兩個事件沒有共同的點數，' : '兩個同時成立的點數是 ' + ((LAB && LAB.length === nAB) ? T(sxSet(LAB)) + '，' : '');
      return ['先各自數點數：' + T('A') + ' 是 ' + sA + '共 ' + T(String(nA)) + ' 個 ⟹ ' + T(PTx('A') + '=' + sxFr(nA, 6)) + '；' + T('B') + ' 是 ' + sB + '共 ' + T(String(nB)) + ' 個 ⟹ ' + T(PTx('B') + '=' + sxFr(nB, 6)) + '。',
        sAB + '共 ' + T(String(nAB)) + ' 個 ⟹ ' + T(PTx('A\\cap B') + '=' + sxFr(nAB, 6)) + '；另一邊 ' + T(PTx('A') + PTx('B') + '=' + prodF([A[0], A[1]]) + '=' + Fr.tex(A[3])) + '。',
        '獨立的定義是 ' + T(PTx('A\\cap B') + '=' + PTx('A') + PTx('B')) + '：本題 ' + T(Fr.tex(A[2])) + ' 與 ' + T(Fr.tex(A[3])) + (p.indep ? ' 相等 ⟹ 獨立' : ' 不相等 ⟹ 不獨立') + '（看數字湊不湊得起來，不是看意義像不像有關）。' + sxFin(o)];
    }
    var m = p.m.map(sxF), a = Fr.add(m[0], m[1]), b = Fr.add(m[0], m[2]), u = Fr.add(a, m[2]);
    var first = p.kind === 0 ? '已知直接給了 ' + T(PTx('A\\cap B') + '=' + Fr.tex(m[0])) + '。'
      : '先由 ' + T(PTx('A\\cap B') + '=' + PTx('A') + '+' + PTx('B') + '-' + PTx('A\\cup B') + '=' + Fr.tex(a) + '+' + Fr.tex(b) + '-' + Fr.tex(u) + '=' + Fr.tex(m[0])) + '。';
    return [no(1) + first,
      no(2) + '再算另一邊：' + T(PTx('A') + PTx('B') + '=' + prodF([a, b]) + '=' + Fr.tex(A[1])) + '。',
      '獨立的定義是 ' + T(PTx('A\\cap B') + '=' + PTx('A') + PTx('B')) + '：' + T(Fr.tex(A[0])) + ' 與 ' + T(Fr.tex(A[1])) + (p.indep ? ' 相等 ⟹ 獨立' : ' 不相等 ⟹ 不獨立') + '。' + sxFin(o)];
  };

  function sxStmt(id, a, b, v, ok) {
    var ab = Fr.mul(a, b), s = Fr.add(a, b), u = Fr.sub(s, ab), na = Fr.cp(a), nb = Fr.cp(b);
    var tf = ok ? '真。' : '假。';
    switch (id) {
      case 0: return '互斥要求 ' + T(PTx('A') + '+' + PTx('B') + '\\le1') + '，本題 ' + T(Fr.tex(a) + '+' + Fr.tex(b) + '=' + Fr.tex(s)) + (ok ? ' 沒有超過 ' + T('1') + ' ⟹ 有可能互斥，' : ' 已經超過 ' + T('1') + ' ⟹ 不可能互斥，') + tf;
      case 1: return '只要交集的機率剛好是 ' + T(PTx('A') + PTx('B') + '=' + Fr.tex(ab)) + ' 就獨立，而這個值比 ' + T(Fr.tex(a)) + '、' + T(Fr.tex(b)) + ' 都小，不會和任何條件衝突 ⟹ ' + tf;
      case 2: return '兩個機率都不為 ' + T('0') + '：互斥給 ' + T(PTx('A\\cap B') + '=0') + '，獨立卻要 ' + T(PTx('A\\cap B') + '=' + Fr.tex(ab)) + '，兩者不可能同時成立 ⟹ ' + tf;
      case 3: return '獨立時 ' + T(PTx('A\\cup B') + '=' + Fr.tex(a) + '+' + Fr.tex(b) + '-' + Fr.tex(ab) + '=' + Fr.tex(u)) + '，敘述寫的是 ' + T(Fr.tex(v)) + ' ⟹ ' + tf;
      case 4: return '互斥時 ' + T(PTx('A\\cup B') + '=' + Fr.tex(a) + '+' + Fr.tex(b) + '=' + Fr.tex(s)) + '，敘述寫的是 ' + T(Fr.tex(v)) + ' ⟹ ' + tf;
      case 5: return '獨立時 ' + T(PTx('A\\mid B') + '=' + PTx('A') + '=' + Fr.tex(a)) + '（已知 ' + T('B') + ' 完全不影響 ' + T('A') + '），敘述寫的是 ' + T(Fr.tex(v)) + ' ⟹ ' + tf;
      case 6: return '互斥時 ' + T(PTx('A\\cap B') + '=0') + '，所以 ' + T(PTx('A\\mid B') + '=0') + '，敘述寫的是 ' + T(Fr.tex(v)) + ' ⟹ ' + tf;
      case 7: return '獨立會傳給餘事件：' + T(PTx("A'\\cap B'") + '=1-' + Fr.tex(a) + '-' + Fr.tex(b) + '+' + Fr.tex(ab) + '=' + Fr.tex(Fr.add(Fr.sub(F(1), s), ab))) + '，而 ' + T(PTx("A'") + PTx("B'") + '=' + prodF([na, nb]) + '=' + Fr.tex(Fr.mul(na, nb))) + '，兩者相等 ⟹ ' + tf;
      case 8: return '獨立的定義就是 ' + T(PTx('A\\cap B') + '=' + PTx('A') + PTx('B') + '=' + prodF([a, b]) + '=' + Fr.tex(ab)) + '，敘述寫的是 ' + T(Fr.tex(v)) + ' ⟹ ' + tf;
      default: return '獨立時 ' + T(PTx('A\\mid B') + '=' + PTx('A') + '=' + Fr.tex(a)) + '、' + T(PTx('B\\mid A') + '=' + PTx('B') + '=' + Fr.tex(b)) + '，本題兩者' + (ok ? '相等 ⟹ ' : '不相等 ⟹ ') + tf;
    }
  }
  L1_SOL.indepVsExcl = function (p, o) {
    var a = sxF(p.a), b = sxF(p.b), ab = Fr.mul(a, b), s = Fr.add(a, b), u = Fr.sub(s, ab);
    var one = function (i) { return no(i + 1) + sxStmt(p.ids[i], a, b, sxF(p.vs[i]), p.ans[i] === 1); };
    return ['先把會用到的數字一次算好：' + T(PTx('A') + '+' + PTx('B') + '=' + Fr.tex(s)) + '（' + (Fr.cmp(s, F(1)) <= 0 ? '沒有超過 ' + T('1') + '，所以互斥是有可能的' : '超過 ' + T('1') + '，所以不可能互斥') + '）、' + T(PTx('A') + PTx('B') + '=' + prodF([a, b]) + '=' + Fr.tex(ab)) + '；獨立時 ' + T(PTx('A\\cup B') + '=' + Fr.tex(u)) + '、' + T(PTx('A\\mid B') + '=' + Fr.tex(a)) + '，互斥時 ' + T(PTx('A\\cup B') + '=' + Fr.tex(s)) + '、' + T(PTx('A\\mid B') + '=0') + '。',
      one(0) + one(1),
      one(2) + one(3) + sxFin(o)];
  };

  L1_SOL.indepTable = function (p, o) {
    var M = p.M, ri = p.ri, ci = p.ci, lb = sxTab(o.q);
    var R = rowSum(M, ri), R2 = rowSum(M, 1 - ri), ad = M[0][0] * M[1][1], bc = M[0][1] * M[1][0];
    return ['兩列各自的合計：「' + lb.r[ri] + '」' + T(M[ri][0] + '+' + M[ri][1] + '=' + R) + '、「' + lb.r[1 - ri] + '」' + T(M[1 - ri][0] + '+' + M[1 - ri][1] + '=' + R2) + '。',
      no(1) + '兩個條件機率的分母就是各自那一列的合計：' + T(sxFr(M[ri][ci], R)) + '、' + T(sxFr(M[1 - ri][ci], R2)) + '——兩列的內部比例' + (p.indep ? '一樣' : '不一樣') + '。',
      no(2) + '四格寫成 ' + T('\\begin{matrix}a&b\\\\c&d\\end{matrix}') + ' 時，獨立的充要條件是 ' + T('ad=bc') + '：' + T(M[0][0] + '\\times' + M[1][1] + '=' + ad) + '、' + T(M[0][1] + '\\times' + M[1][0] + '=' + bc) + '，兩者' + (p.indep ? '相等 ⟹ 獨立' : '不相等 ⟹ 不獨立') + '。' + sxFin(o)];
  };

  L1_SOL.repeatTrial = function (p, o) {
    var n = p.n, k = p.k, pr = sxF(p.p), q = Fr.cp(pr), A = p.ans.map(sxF);
    var pt = Fr.tex(pr), qt = Fr.tex(q);
    return ['每次成功的機率 ' + T(pt) + '、失敗 ' + T(qt) + '，各次互相獨立。恰好成功 ' + T('j') + ' 次的機率＝「挑哪 ' + T('j') + ' 次成功」的方法數 ' + T(CT(n, 'j')) + ' 乘上 ' + T(par(pt) + sup('j') + par(qt) + '^{' + n + '-j}') + '。',
      no(1) + '全部都成功只有一種排法：' + T(pw(pt, n) + '=' + Fr.tex(A[0])) + '；' + no(2) + '恰好 ' + T(String(k)) + ' 次：' + T(binTex(n, k, pt, qt) + '=' + Fr.tex(A[1])) + '，其中 ' + T(CT(n, k) + '=' + nCr(n, k)) + ' 是「挑哪 ' + T(String(k)) + ' 次成功」的方法數。',
      no(3) + '「至少 ' + T(String(n - 1)) + ' 次」＝恰 ' + T(String(n)) + ' 次加上恰 ' + T(String(n - 1)) + ' 次：' + T(Fr.tex(A[0]) + '+' + binTex(n, n - 1, pt, qt) + '=' + Fr.tex(A[0]) + '+' + Fr.tex(binP(n, n - 1, pr)) + '=' + Fr.tex(A[2])) + '。',
      no(4) + '「至多 ' + T('1') + ' 次」＝恰 ' + T('0') + ' 次加上恰 ' + T('1') + ' 次：' + T(binTex(n, 0, pt, qt) + '+' + binTex(n, 1, pt, qt) + '=' + Fr.tex(binP(n, 0, pr)) + '+' + Fr.tex(binP(n, 1, pr)) + '=' + Fr.tex(A[3])) + '。' + sxFin(o)];
  };

  L1_SOL.atLeastOne = function (p, o) {
    var n = p.n, pr = sxF(p.p), q = Fr.cp(pr), A = p.ans.map(sxF);
    var pt = Fr.tex(pr), qt = Fr.tex(q), b1 = binP(n, 1, pr);
    return ['一次「成功」的機率是 ' + T(pt) + '，所以一次「沒有成功」的機率是 ' + T('1-' + pt + '=' + qt) + '；各次獨立 ⟹ ' + no(1) + T(pw(qt, n) + '=' + Fr.tex(A[0])) + '。',
      no(2) + '「至少一次」的反面正好是' + no(1) + '的「一次也沒有」：' + T('1-' + Fr.tex(A[0]) + '=' + Fr.tex(A[1])) + '。',
      no(3) + '「至少兩次」的反面是「' + T('0') + ' 次」或「恰 ' + T('1') + ' 次」，恰 ' + T('1') + ' 次是 ' + T(binTex(n, 1, pt, qt) + '=' + Fr.tex(b1)) + ' ⟹ ' + T('1-' + Fr.tex(A[0]) + '-' + Fr.tex(b1) + '=' + Fr.tex(A[2])) + '。' + sxFin(o)];
  };

  L1_SOL.threeIndep = function (p, o) {
    var ps = p.ps.map(sxF), qs = ps.map(Fr.cp), A = p.ans.map(sxF);
    var t1 = Fr.mul(ps[0], Fr.mul(qs[1], qs[2])), t2 = Fr.mul(qs[0], Fr.mul(ps[1], qs[2])), t3 = Fr.mul(qs[0], Fr.mul(qs[1], ps[2]));
    return ['三個人的機率不一樣，只能各自取反面：沒有成功的機率分別是 ' + T('1-' + Fr.tex(ps[0]) + '=' + Fr.tex(qs[0])) + '、' + T(Fr.tex(qs[1])) + '、' + T(Fr.tex(qs[2])) + '。',
      no(1) + '三者都成功就三個機率連乘：' + T(prodF(ps) + '=' + Fr.tex(A[0])) + '；' + no(2) + '都沒成功就三個反面連乘：' + T(prodF(qs) + '=' + Fr.tex(A[1])) + '。',
      no(3) + '「至少一個」的反面就是' + no(2) + '算出來的 ' + T(Fr.tex(A[1])) + '：' + T('1-' + Fr.tex(A[1]) + '=' + Fr.tex(A[2])) + '。',
      no(4) + '「恰有一個」要分三種情形（成功的是第一個、第二個或第三個）各算一次再相加，' + T(CT(3, 1)) + ' 只在三人機率相同時才能用：' + T(prodF([ps[0], qs[1], qs[2]]) + '+' + prodF([qs[0], ps[1], qs[2]]) + '+' + prodF([qs[0], qs[1], ps[2]]) + '=' + Fr.tex(t1) + '+' + Fr.tex(t2) + '+' + Fr.tex(t3) + '=' + Fr.tex(A[3])) + '。' + sxFin(o)];
  };

  L1_SOL.needTrials = function (p, o) {
    var q1 = sxF(p.q1), th1 = sxF(p.th1), th2 = sxF(p.th2), n1 = p.ans[0], n2 = p.ans[1];
    var lq = lg(q1), l1 = lg(th1), l2 = lg(th2), qt = Fr.tex(q1);
    var v1 = l1 / lq, v2 = l2 / lq;
    var ineq = function (th) { return pw(qt, 'n') + '\\lt ' + Fr.tex(th); };
    var solve = function (th, lv, v, nn) {
      return T('n\\gt\\dfrac{\\log' + par(Fr.tex(th)) + '}{\\log' + par(qt) + '}=\\dfrac{' + dec(lv, 4) + '}{' + dec(lq, 4) + '}\\approx' + dec(v, 2)) + ' ⟹ 最小的整數是 ' + T(String(nn));
    };
    return ['每一次「沒有成功」的機率是 ' + T('1-' + Fr.tex(Fr.cp(q1)) + '=' + qt) + '，各次獨立 ⟹ ' + T('n') + ' 次都沒成功是 ' + T(pw(qt, 'n')) + '。要「至少一次成功」的機率大於 ' + T(Fr.tex(Fr.cp(th1))) + '，就是要 ' + T(ineq(th1)) + '。',
      no(1) + '兩邊取常用對數。因為 ' + T('\\log' + par(qt) + '\\approx' + dec(lq, 4) + '\\lt 0') + '，除過去時不等號要變向：' + solve(th1, l1, v1, n1) + '。',
      no(2) + '同一個式子換成 ' + T(ineq(th2)) + '：' + solve(th2, l2, v2, n2) + '。把 ' + T(String(n2)) + ' 與 ' + T(String(n2 - 1)) + ' 各代回原式確認一次最保險。' + sxFin(o)];
  };

  /* ── §4 把所有路徑加起來、貝氏 ── */
  L1_SOL.totalPath = function (p, o) {
    var A = p.ans.map(sxF), h = F(1, 2);
    if (p.kind === 0) {
      var m = p.m, n = p.n, r1 = sxF(p.r1), r2 = sxF(p.r2);
      var w1 = F(m, m + n), w2 = F(n, m + n);
      var na = sxM(o.q, /某工廠的(.+?)與/, '甲'), nb = sxM(o.q, /與(.+?)(?:產量|供貨量|件數)比為/, '乙'), y = sxQ(o.q)[0] || '該結果';
      return ['比 ' + T(m + ':' + n) + ' 要先化成機率：' + T(PTx(tx(na)) + '=' + sxFr(m, m + n)) + '、' + T(PTx(tx(nb)) + '=' + sxFr(n, m + n)) + '（兩者相加為 ' + T('1') + '）。',
        no(1) + '走到「' + y + '」有兩條路徑，各自相乘再加起來：' + T(prodF([w1, r1]) + '+' + prodF([w2, r2]) + '=' + Fr.tex(Fr.mul(w1, r1)) + '+' + Fr.tex(Fr.mul(w2, r2)) + '=' + Fr.tex(A[0])) + '（合理性檢查：它一定落在 ' + T(Fr.tex(r1)) + ' 與 ' + T(Fr.tex(r2)) + ' 之間）。',
        no(2) + '比改成 ' + T('1:1') + ' 就是把兩條路徑的權重都換成 ' + T('\\dfrac{1}{2}') + '：' + T(prodF([h, r1]) + '+' + prodF([h, r2]) + '=' + Fr.tex(Fr.mul(h, r1)) + '+' + Fr.tex(Fr.mul(h, r2)) + '=' + Fr.tex(A[1])) + '。' + sxFin(o)];
    }
    var k = p.k, wA = F(6 - k, 6), wB = F(k, 6), q1 = F(p.a1, p.a1 + p.b1), q2 = F(p.a2, p.a2 + p.b2);
    var bx = sxM(o.q, /^甲(.)有/, '袋'), c1 = sxM(o.q, /顆([^顆與]+)與/, '指定顏色的球');
    var s6 = F(1, 6), s5 = F(5, 6);
    return ['先算第一層：點數大於 ' + T(String(k)) + ' 有 ' + T(String(6 - k)) + ' 種 ⟹ ' + T(PTx(tx('甲' + bx)) + '=' + sxFr(6 - k, 6)) + '、' + T(PTx(tx('乙' + bx)) + '=' + sxFr(k, 6)) + '。第二層是各' + bx + '裡' + c1 + '的比例 ' + T(sxFr(p.a1, p.a1 + p.b1)) + ' 與 ' + T(sxFr(p.a2, p.a2 + p.b2)) + '。',
      no(1) + '兩條路徑各自相乘再加起來：' + T(prodF([wA, q1]) + '+' + prodF([wB, q2]) + '=' + Fr.tex(Fr.mul(wA, q1)) + '+' + Fr.tex(Fr.mul(wB, q2)) + '=' + Fr.tex(A[0])) + '。',
      no(2) + '改成「點數為 ' + T('6') + ' 才用甲' + bx + '」⟹ 第一層的權重換成 ' + T('\\dfrac{1}{6}') + ' 與 ' + T('\\dfrac{5}{6}') + '：' + T(prodF([s6, q1]) + '+' + prodF([s5, q2]) + '=' + Fr.tex(Fr.mul(s6, q1)) + '+' + Fr.tex(Fr.mul(s5, q2)) + '=' + Fr.tex(A[1])) + '。' + sxFin(o)];
  };

  L1_SOL.bayesTwo = function (p, o) {
    var w1 = sxF(p.w1), w2 = Fr.cp(w1), r1 = sxF(p.r1), r2 = sxF(p.r2), A = p.ans.map(sxF);
    var L1p = Fr.mul(w1, r1), L2p = Fr.mul(w2, r2), G1 = Fr.mul(w1, Fr.cp(r1)), G2 = Fr.mul(w2, Fr.cp(r2));
    var Pn = Fr.add(G1, G2), qs = sxQ(o.q), y = qs[0] || '該結果', nn = qs[qs.length - 1] || '另一種結果';
    var na = sxM(o.q, /某工廠的(.+?)佔/, '甲'), nb = sxM(o.q, /；(.+?)佔/, '乙');
    return ['畫兩層樹狀圖：第一層是來源 ' + T(PTx(tx(na)) + '=' + Fr.tex(w1)) + '、' + T(PTx(tx(nb)) + '=' + Fr.tex(w2)) + '，第二層是各自產生「' + y + '」的比率 ' + T(Fr.tex(r1)) + ' 與 ' + T(Fr.tex(r2)) + '。',
      no(1) + '「' + y + '」有兩片葉子：' + T(prodF([w1, r1]) + '=' + Fr.tex(L1p)) + '（來自' + na + '）與 ' + T(prodF([w2, r2]) + '=' + Fr.tex(L2p)) + '（來自' + nb + '），把兩條路徑加起來 ' + T(sxAddF([L1p, L2p])) + '。',
      no(2) + '已知結果是「' + y + '」⟹ 分母換成剛才的 ' + T(Fr.tex(A[0])) + '，分子是要的那一片：' + T(sxDiv(L1p, A[0], A[1])) + '。',
      no(3) + '換成「' + nn + '」的兩片葉子：' + T(prodF([w1, Fr.cp(r1)]) + '=' + Fr.tex(G1)) + '、' + T(prodF([w2, Fr.cp(r2)]) + '=' + Fr.tex(G2)) + '，合計 ' + T(sxAddF([G1, G2])) + ' ⟹ ' + T(sxDiv(G1, Pn, A[2])) + '。' + sxFin(o)];
  };

  L1_SOL.bayesScreen = function (p, o) {
    var pv = sxF(p.pv), s = sxF(p.s), t = sxF(p.t), N = p.N, A = p.ans.map(sxF);
    var qs = sxQ(o.q), d = qs[0] || '有狀況', y = qs[1] || '陽性', nn = qs[qs.length - 1] || '另一種結果';
    var nd = sxM(o.q, /；(.+?)的人「/, '沒有' + d);
    var n1 = Math.round(Fr.num(pv) * N), n2 = N - n1;
    var a = Math.round(Fr.num(Fr.mul(pv, s)) * N), b = n1 - a;
    var c = Math.round(Fr.num(Fr.mul(Fr.cp(pv), Fr.cp(t))) * N), dd = n2 - c;
    var pos = a + c, neg = b + dd;
    return ['機率題換成人數最好算：假設共 ' + T(String(N)) + ' 人，「' + d + '」的有 ' + T(String(N) + '\\times' + Fr.tex(pv) + '=' + n1) + ' 人，' + nd + '的有 ' + T(N + '-' + n1 + '=' + n2) + ' 人。',
      '再各自乘上該群的比率：' + d + '的人裡「' + y + '」有 ' + T(n1 + '\\times' + Fr.tex(s) + '=' + a) + ' 人、「' + nn + '」有 ' + T(n1 + '-' + a + '=' + b) + ' 人；' + nd + '的人裡「' + nn + '」有 ' + T(n2 + '\\times' + Fr.tex(t) + '=' + dd) + ' 人，所以' + nd + '卻「' + y + '」的有 ' + T(n2 + '-' + dd + '=' + c) + ' 人。',
      no(1) + '「' + y + '」的合計是兩格相加 ' + T(a + '+' + c + '=' + pos) + ' 人 ⟹ ' + T(sxFr(pos, N)) + '。',
      no(2) + '已知「' + y + '」⟹ 分母換成 ' + T(String(pos)) + '：' + T(sxFr(a, pos)) + '（' + nd + '的人本來就佔絕大多數，即使判錯的比例很小，人數也可能和真正' + d + '的一樣多）；' + no(3) + '「' + nn + '」的合計是 ' + T(b + '+' + dd + '=' + neg) + ' ⟹ ' + T(sxFr(b, neg)) + '。' + sxFin(o)];
  };

  L1_SOL.bayesThree = function (p, o) {
    var ws = p.ws, S = ws[0] + ws[1] + ws[2], rs = p.rs.map(sxF), A = p.ans.map(sxF), i;
    var W = [], lf = [];
    for (i = 0; i < 3; i++) { W.push(F(ws[i], S)); lf.push(Fr.mul(W[i], rs[i])); }
    var nm = (sxM(o.q, /^(.+?) 三者的/, '甲、乙、丙') || '').split('、'), y = sxQ(o.q)[0] || '該結果';
    var g = function (i2) { return nm[i2] || '第' + (i2 + 1) + '個'; };
    return ['比 ' + T(ws.join(':')) + ' 要先化成機率：' + T(sxFr(ws[0], S)) + '、' + T(sxFr(ws[1], S)) + '、' + T(sxFr(ws[2], S)) + '（三者相加為 ' + T('1') + '）。',
      '三片「' + y + '」的葉子依序是 ' + T(prodF([W[0], rs[0]]) + '=' + Fr.tex(lf[0])) + '、' + T(prodF([W[1], rs[1]]) + '=' + Fr.tex(lf[1])) + '、' + T(prodF([W[2], rs[2]]) + '=' + Fr.tex(lf[2])) + '。',
      no(1) + '把三條路徑加起來：' + T(sxAddF(lf)) + '。',
      no(2) + '已知是「' + y + '」⟹ 分母換成 ' + T(Fr.tex(A[0])) + '，分子是' + g(p.i1) + '那一片：' + T(sxDiv(lf[p.i1], A[0], A[1])) + '；' + no(3) + '換成' + g(p.i2) + '那一片：' + T(sxDiv(lf[p.i2], A[0], A[2])) + '（驗算：三個條件機率加起來必須是 ' + T('1') + '）。' + sxFin(o)];
  };

  L1_SOL.bayesTable = function (p, o) {
    var N = p.N, pv = sxF(p.pv), s = sxF(p.s), u = sxF(p.u), C = p.cells, A = p.ans.map(sxF);
    var n1 = C[0] + C[1], n2 = C[2] + C[3], pos = C[0] + C[2], neg = C[1] + C[3];
    var qs = sxQ(o.q), d = qs[0] || '有狀況', y = qs[1] || '陽性', nn = qs[qs.length - 1] || '另一種結果';
    var mm = o.q.match(/；[^；]*?的人「/g) || [];
    var nd = mm.length ? mm[mm.length - 1].slice(1, -3) : '沒有' + d;
    return ['先把比例全部換成整數人數：「' + d + '」有 ' + T(String(N) + '\\times' + Fr.tex(pv) + '=' + n1) + ' 人，' + nd + '有 ' + T(N + '-' + n1 + '=' + n2) + ' 人。',
      no(1) + '再各自乘上該列的比率：' + T(n1 + '\\times' + Fr.tex(s) + '=' + C[0]) + '、' + T(n1 + '-' + C[0] + '=' + C[1]) + '、' + T(n2 + '\\times' + Fr.tex(u) + '=' + C[2]) + '、' + T(n2 + '-' + C[2] + '=' + C[3]) + '（橫加等於直加是最快的驗算：' + T(C[0] + '+' + C[1] + '=' + n1) + '）。',
      no(2) + '「' + y + '」的合計 ' + T(C[0] + '+' + C[2] + '=' + pos) + ' ⟹ ' + T(sxFr(pos, N)) + '。',
      no(3) + '已知「' + y + '」⟹ 分母換成 ' + T(String(pos)) + '：' + T(sxFr(C[0], pos)) + '；' + no(4) + '「' + nn + '」的合計 ' + T(C[1] + '+' + C[3] + '=' + neg) + ' ⟹ ' + T(sxFr(C[1], neg)) + '。' + sxFin(o)];
  };

  /* ── §5 綜合 ── */
  L1_SOL.condCombo = function (p, o) {
    var n = p.n, nB = p.nB, nAB = p.nAB, bt = p.bt, why = '';
    var mx = bt.indexOf('最大的是') >= 0 ? parseInt((bt.match(/\$(\d+)\$/) || [0, 0])[1], 10) : 0;
    var mn = bt.indexOf('最小的是') >= 0 ? parseInt((bt.match(/\$(\d+)\$/) || [0, 0])[1], 10) : 0;
    var od = Math.ceil(n / 2), ev = n - od, par2 = '';
    if (bt.indexOf('都是奇數') >= 0 && nCr(od, 3) === nB) par2 = T('1') + ' 到 ' + T(String(n)) + ' 裡奇數有 ' + T(String(od)) + ' 個，三個都從裡面挑 ⟹ ' + T(CT(od, 3) + '=' + nB);
    else if (bt.indexOf('都是偶數') >= 0 && nCr(ev, 3) === nB) par2 = T('1') + ' 到 ' + T(String(n)) + ' 裡偶數有 ' + T(String(ev)) + ' 個，三個都從裡面挑 ⟹ ' + T(CT(ev, 3) + '=' + nB);
    else if (bt.indexOf('和為偶數') >= 0 && nCr(ev, 3) + ev * nCr(od, 2) === nB) par2 = '奇數 ' + T(String(od)) + ' 個、偶數 ' + T(String(ev)) + ' 個；和是偶數就是「三個都偶」或「一偶兩奇」⟹ ' + T(CT(ev, 3) + '+' + CT(ev, 1) + '\\times ' + CT(od, 2) + '=' + nCr(ev, 3) + '+' + (ev * nCr(od, 2)) + '=' + nB);
    else if (bt.indexOf('和為奇數') >= 0 && nCr(od, 3) + od * nCr(ev, 2) === nB) par2 = '奇數 ' + T(String(od)) + ' 個、偶數 ' + T(String(ev)) + ' 個；和是奇數就是「三個都奇」或「兩偶一奇」⟹ ' + T(CT(od, 3) + '+' + CT(od, 1) + '\\times ' + CT(ev, 2) + '=' + nCr(od, 3) + '+' + (od * nCr(ev, 2)) + '=' + nB);
    else if (bt.indexOf('積為偶數') >= 0 && nCr(n, 3) - nCr(od, 3) === nB) par2 = '積是偶數的反面是「三個都是奇數」，奇數有 ' + T(String(od)) + ' 個 ⟹ ' + T(CT(n, 3) + '-' + CT(od, 3) + '=' + nCr(n, 3) + '-' + nCr(od, 3) + '=' + nB);
    if (mx && nCr(mx - 1, 2) === nB) why = '（另外兩個數只能從比它小的 ' + T(sxSet([1, 2, '\\ldots', mx - 1])) + ' 中挑兩個 ⟹ ' + T(CT(mx - 1, 2) + '=' + nB) + '）';
    else if (mn && nCr(n - mn, 2) === nB) why = '（另外兩個數只能從比它大的 ' + T(sxSet([mn + 1, '\\ldots', n])) + ' 共 ' + T(String(n - mn)) + ' 個裡挑兩個 ⟹ ' + T(CT(n - mn, 2) + '=' + nB) + '）';
    else if (par2) why = '（' + par2 + '）';
    return ['先把總數看清楚：' + T('1,2,\\ldots,' + n) + ' 取三個相異數共 ' + T(CT(n, 3) + '=' + nCr(n, 3)) + ' 種，但「已知」會把樣本空間縮小。',
      '已知「' + bt + '」的取法有 ' + T(String(nB)) + ' 種' + why + '，這 ' + T(String(nB)) + ' 種就是新的分母。',
      '在這 ' + T(String(nB)) + ' 種裡再挑出符合「' + p.at + '」的，有 ' + T(String(nAB)) + ' 種（分子與分母都用組合去數，不能一個排列一個組合）⟹ ' + T('\\dfrac{n(A\\cap B)}{n(B)}=' + sxFr(nAB, nB)) + '。' + sxFin(o)];
  };

  L1_SOL.typeIdent = function (p, o) {
    var M = p.M, ri = p.ri, ci = p.ci, k = p.k, A = p.ans.map(sxF), lb = sxTab(o.q);
    var N = rowSum(M, 0) + rowSum(M, 1), R = rowSum(M, ri), C = colSum(M, ci), cell = M[ri][ci];
    return ['先算合計：全部 ' + T(String(N)) + ' ' + lb.u + '、「' + lb.r[ri] + '」這一列 ' + T(M[ri][0] + '+' + M[ri][1] + '=' + R) + '、「' + lb.c[ci] + '」這一欄 ' + T(M[0][ci] + '+' + M[1][ci] + '=' + C) + '。',
      no(1) + '沒有任何「已知」⟹ 普通機率，分母是總數：' + T(sxFr(C, N)) + '；' + no(2) + '有「已知」⟹ 條件機率，分母換成「' + lb.r[ri] + '」的合計：' + T(sxFr(cell, R)) + '。',
      no(3) + '方向相反，分母換成「' + lb.c[ci] + '」的合計：' + T(sxFr(cell, C)) + '（分子都是同一格的 ' + T(String(cell)) + '，但分母不同）。',
      no(4) + '每次記錄後放回 ⟹ 每次都獨立、機率都是' + no(1) + '的 ' + T(Fr.tex(A[0])) + '，連乘 ' + T(String(k)) + ' 次：' + T(pw(Fr.tex(A[0]), k) + '=' + Fr.tex(A[3])) + '；' + no(5) + '「至少一次」走餘事件：' + T('1-' + Fr.tex(A[3]) + '=' + Fr.tex(A[4])) + '。' + sxFin(o)];
  };
  var META_L1 = [
      ['freqTable', '§1 從次數表得到客觀機率'], ['subjCheck', '§1 檢視主觀機率的合理性'], ['tableThree', '§1 列聯表：三種機率'], ['probRules', '§1 機率的基本性質'],
      ['condDice', '§2 條件機率：骰子'], ['condFormula', '§2 用公式算條件機率'], ['condTable', '§2 從列聯表讀條件機率'], ['multRule', '§2 乘法公式'], ['condInverse', '§2 已知條件機率反求'], ['drawBalls', '§2 放回與不放回'], ['treeThree', '§2 三層樹狀圖'], ['cardKids', '§2 直接數縮小後的樣本空間'],
      ['indepCheck', '§3 判斷兩事件是否獨立'], ['indepVsExcl', '§3 獨立與互斥的辨析'], ['indepTable', '§3 從列聯表判斷獨立'], ['repeatTrial', '§3 重複試驗：恰有幾次成功'], ['atLeastOne', '§3 至少一次'], ['threeIndep', '§3 三個獨立事件'], ['needTrials', '§3 要試幾次才夠'],
      ['totalPath', '§4 把所有路徑加起來'], ['bayesTwo', '§4 兩分支的貝氏'], ['bayesScreen', '§4 篩檢問題'], ['bayesThree', '§4 三分支的貝氏'], ['bayesTable', '§4 貝氏與列聯表'],
      ['condCombo', '§5 條件機率與排列組合'], ['typeIdent', '§5 題型辨識']
  ];
  var META_L2 = [
      ['condUnknown', '§2 條件機率：反求未知'], ['condDice2', '§2 兩顆骰子的條件機率與獨立'], ['condComb2', '§5 條件機率與組合'], ['drawThree', '§2 不放回連抽三次'], ['symDraw', '§2 抽籤的公平性'],
      ['tableFill', '§1 列聯表補完'], ['tableIndepFix', '§3 列聯表：要多少才獨立'],
      ['indepThreePeople', '§3 三人獨立的綜合'], ['solveP', '§3 由至少一次反求機率'], ['repeatCond', '§3 重複試驗與條件機率'], ['needTrialsAdv', '§3 要試幾次才夠（進階）'],
      ['totalPath2', '§4 多分支：反推未知比率'], ['bayesTransfer', '§4 兩階段的貝氏'], ['bayesRetest', '§4 複檢兩次'], ['bayesParamP', '§4 盛行率改變的影響'], ['bayesCoin', '§4 硬幣與貝氏']
  ];
  /* ══════════════════════════════════════════════════════════
     L3　中上（15 型）：每型對應固定題 L3-1～L3-15 的「類似題」
     ─────────────────────────────────────────────────────────
     同題型換數字／情境，答案一律精確：最簡分數（Fr.tex）或純選項字串。
     課綱界線（HANDOUT_SPEC §4）：答案永遠是一個機率值（或由機率反求的一個數）；
       不出現隨機變數、二項分布記號、期望值、變異數；
       不用「全機率公式」這個名詞（說「把所有路徑加起來」）；
       偽陽性／偽陰性／敏感度／特異度／先驗／後驗一律不用，改用中文敘述。
       重複試驗用高一下的組合硬乘 C^n_k p^k (1-p)^{n-k}。
     p 只放輸入參數與旗標（答案另放 p.ans，驗算器不讀）。
     每型開頭先丟掉一次 r()：連號種子的 LCG 首值幾乎相同，變體旗標不能靠它。
     ══════════════════════════════════════════════════════════ */
  var L3 = {};

  /* ── 小工具（名稱一律加 l3 前綴） ── */
  function l3P(e) { return 'P(' + e + ')'; }
  function l3no(i) { return '(' + i + ') '; }
  function l3jo(a) { return a.join('　'); }
  function l3fp(f) { return [f.n, f.d]; }
  function l3pct(n) { return n + '\\%'; }
  function l3opt(list) { var s = '', i; for (i = 0; i < list.length; i++) s += '(' + list[i] + ')'; return s; }
  /* 組合數與冪次的排版（自備一份，不依賴產生器裡可能改名的內部函式） */
  function l3nCr(n, k) { if (k < 0 || k > n) return 0; var t = 1, i; for (i = 1; i <= k; i++) t = t * (n - k + i) / i; return Math.round(t); }
  function l3CT(n, k) { return 'C^' + (n < 10 ? n : '{' + n + '}') + '_' + (k < 10 ? k : '{' + k + '}'); }
  function l3par(s) { s = String(s); return s.indexOf('\\') >= 0 ? '\\left(' + s + '\\right)' : '(' + s + ')'; }
  function l3pw(b, k) { if (k === 0) return ''; if (k === 1) return l3par(b); return l3par(b) + (k < 10 ? '^' + k : '^{' + k + '}'); }
  /* C^n_k p^k (1-p)^{n-k}（高一下的組合硬乘，不用二項分布記號） */
  function l3binP(n, k, p) { return Fr.mul(F(l3nCr(n, k)), Fr.mul(Fr.pow(p, k), Fr.pow(Fr.cp(p), n - k))); }
  /* 四塊機率 c=[A∩B, A∩B', A'∩B, A'∩B']（F 物件）上求任一集合運算式／條件機率 */
  var L3SET = { 'A': [1, 1, 0, 0], "A'": [0, 0, 1, 1], 'B': [1, 0, 1, 0], "B'": [0, 1, 0, 1] };
  function l3set(e, c) {
    var ps = e.split(/\\cap|\\cup/), op = e.indexOf('\\cup') >= 0 ? 'u' : 'i';
    var v = L3SET[ps[0].replace(/\s/g, '')].slice(), i, k, w, s;
    for (k = 1; k < ps.length; k++) {
      w = L3SET[ps[k].replace(/\s/g, '')];
      for (i = 0; i < 4; i++) v[i] = (op === 'u') ? ((v[i] || w[i]) ? 1 : 0) : ((v[i] && w[i]) ? 1 : 0);
    }
    s = F(0);
    for (i = 0; i < 4; i++) if (v[i]) s = Fr.add(s, c[i]);
    return s;
  }
  function l3ev(e, c) {
    var k = e.indexOf('\\mid');
    if (k < 0) return l3set(e, c);
    return Fr.div(l3set(e.slice(0, k) + '\\cap' + e.slice(k + 4), c), l3set(e.slice(k + 4), c));
  }

  /* ══ L3-1　骰子兩事件的雙向條件機率：分子同一個 n(A∩B)，只有分母換 ══ */
  function l3die2(r) {
    var k;
    switch (r.int(0, 9)) {
      case 0: k = r.int(4, 10); return { t: '兩次的點數和為 ' + T(k), f: function (a, b) { return a + b === k; } };
      case 1: k = r.int(5, 9); return { t: '兩次的點數和大於 ' + T(k), f: function (a, b) { return a + b > k; } };
      case 2: return { t: '兩次的點數和為偶數', f: function (a, b) { return (a + b) % 2 === 0; } };
      case 3: return { t: '兩次的點數和為奇數', f: function (a, b) { return (a + b) % 2 === 1; } };
      case 4: k = r.int(1, 6); return { t: '至少有一次出現 ' + T(k) + ' 點', f: function (a, b) { return a === k || b === k; } };
      case 5: return { t: '第一次的點數不小於第二次的點數', f: function (a, b) { return a >= b; } };
      case 6: return { t: '兩次的點數相同', f: function (a, b) { return a === b; } };
      case 7: k = r.int(1, 4); return { t: '兩次的點數差為 ' + T(k), f: function (a, b) { return Math.abs(a - b) === k; } };
      case 8: k = r.pick([4, 6, 8, 10, 12, 18, 24]); return { t: '兩次的點數乘積為 ' + T(k), f: function (a, b) { return a * b === k; } };
      default: k = r.int(2, 5); return { t: '兩次的點數都不超過 ' + T(k), f: function (a, b) { return a <= k && b <= k; } };
    }
  }
  L3.diceBothWays = function (r) {
    r();
    var eA, eB, nA = 0, nB = 0, nAB = 0, a, b, tr = 0;
    do {
      eA = l3die2(r); eB = l3die2(r); nA = 0; nB = 0; nAB = 0;
      for (a = 1; a <= 6; a++) for (b = 1; b <= 6; b++) {
        if (eA.f(a, b)) nA++;
        if (eB.f(a, b)) nB++;
        if (eA.f(a, b) && eB.f(a, b)) nAB++;
      }
      tr++;
    } while ((eA.t === eB.t || nA < 3 || nB < 3 || nA > 33 || nB > 33 || nAB === 0 || nAB === nA || nAB === nB
              || nAB * nA + nAB * nB === nA * nB) && tr < 500);   /* 兩個條件機率相加剛好是 1 也算退化 */
    var v = r.int(0, 2);
    var pAB = F(nAB, nB), pBA = F(nAB, nA), sm = Fr.add(pAB, pBA), it = F(nAB, 36);
    var setup = '擲一顆公正骰子兩次（兩次分得出先後）。設 ' + T('A') + ' 為「' + eA.t + '」的事件，' + T('B') + ' 為「' + eB.t + '」的事件。';
    var hb = '樣本空間就是 ' + T('6\\times6=36') + ' 個有序對，只要數出三個數字：' + T('n(A)=' + nA) + '、' + T('n(B)=' + nB) + '、' + T('n(A\\cap B)=' + nAB) + '。'
           + T(l3P('A\\mid B')) + ' 與 ' + T(l3P('B\\mid A')) + ' 的分子都是同一個 ' + T(nAB) + '，只有分母換成 ' + T(nB) + ' 或 ' + T(nA) + '。'
           + '（兩個條件機率相加大於 ' + T(1) + ' 一點也不奇怪——它們不是同一個樣本空間裡的互補事件。）';
    if (v === 1)
      return { q: setup + '求 ' + l3no(1) + T(l3P('A\\mid B')) + '　' + l3no(2) + T(l3P('B\\mid A')) + '。',
               a: l3jo([l3no(1) + T(Fr.tex(pAB)), l3no(2) + T(Fr.tex(pBA))]), h: hb,
               p: { eA: eA.t, eB: eB.t, nA: nA, nB: nB, nAB: nAB, v: 1, ans: [l3fp(pAB), l3fp(pBA)] } };
    if (v === 2)
      return { q: setup + '求 ' + l3no(1) + T(l3P('A\\cap B')) + '　' + l3no(2) + T(l3P('A\\mid B') + '+' + l3P('B\\mid A')) + '。',
               a: l3jo([l3no(1) + T(Fr.tex(it)), l3no(2) + T(Fr.tex(sm))]), h: hb,
               p: { eA: eA.t, eB: eB.t, nA: nA, nB: nB, nAB: nAB, v: 2, ans: [l3fp(it), l3fp(sm)] } };
    return { q: setup + '求 ' + T(l3P('A\\mid B') + '+' + l3P('B\\mid A')) + ' 之值。',
             a: T(Fr.tex(sm)), h: hb,
             p: { eA: eA.t, eB: eB.t, nA: nA, nB: nB, nAB: nAB, v: 0, ans: l3fp(sm) } };
  };

  /* ══ L3-2　由 P(A'∩B') 補齊四塊，再算條件機率 ══ */
  L3.compCellCond = function (r) {
    r();
    var D = r.pick([8, 10, 12, 15, 16, 20, 24, 25, 30, 40, 48, 60, 100]);
    var c4, tr = 0;
    do { c4 = [r.int(1, D - 3), r.int(1, D - 3), r.int(1, D - 3), 0]; c4[3] = D - c4[0] - c4[1] - c4[2]; tr++; }
    while (c4[3] <= 0 && tr < 400);
    if (c4[3] <= 0) c4 = [D - 3, 1, 1, 1];
    var c = [F(c4[0], D), F(c4[1], D), F(c4[2], D), F(c4[3], D)];
    var v = r.int(0, 2);
    var tg = r.pick(["B\\mid A'", "A\\mid B'", "B'\\mid A'", "A'\\mid B'"]);
    var cond = tg.slice(tg.indexOf('\\mid') + 4).replace(/\s/g, '');
    var val = l3ev(tg, c), pc0 = l3set(cond, c);
    var PA = l3set('A', c), PB = l3set('B', c), PW = c[3], PU = Fr.sub(F(1), PW), PI = c[0];
    var setup = '設 ' + T('A') + '、' + T('B') + ' 為樣本空間 ' + T('S') + ' 中的兩事件，已知 '
              + T(l3P('A') + '=' + Fr.tex(PA)) + '、' + T(l3P('B') + '=' + Fr.tex(PB)) + '、' + T(l3P("A'\\cap B'") + '=' + Fr.tex(PW)) + '。';
    var hb = '把樣本空間切成四塊。已知的 ' + T(l3P("A'\\cap B'") + '=' + Fr.tex(PW)) + ' 就是「兩件都不發生」那一塊 ⟹ '
           + T(l3P('A\\cup B') + '=1-' + Fr.tex(PW) + '=' + Fr.tex(PU)) + '，再由加法定理 ' + T(l3P('A\\cap B') + '=' + l3P('A') + '+' + l3P('B') + '-' + l3P('A\\cup B')) + ' 得 ' + T(Fr.tex(PI)) + '。'
           + '四塊依序是 ' + T(l3P('A\\cap B') + '=' + Fr.tex(c[0])) + '、' + T(l3P("A\\cap B'") + '=' + Fr.tex(c[1])) + '、' + T(l3P("A'\\cap B") + '=' + Fr.tex(c[2])) + '、' + T(l3P("A'\\cap B'") + '=' + Fr.tex(c[3])) + '。'
           + '條件機率的分母固定是 ' + T(l3P(cond) + '=' + Fr.tex(pc0)) + '，分子只留同時成立的那一塊——只有「條件不動、事件取反」才可以用 ' + T(1) + ' 減。';
    if (v === 1)
      return { q: setup + '求 ' + l3no(1) + T(l3P(cond)) + '　' + l3no(2) + T(l3P(tg)) + '。',
               a: l3jo([l3no(1) + T(Fr.tex(pc0)), l3no(2) + T(Fr.tex(val))]), h: hb,
               p: { D: D, c: c4, tg: tg, v: 1, ans: [l3fp(pc0), l3fp(val)] } };
    if (v === 2)
      return { q: setup + '求 ' + l3no(1) + T(l3P('A\\cap B')) + '　' + l3no(2) + T(l3P(tg)) + '。',
               a: l3jo([l3no(1) + T(Fr.tex(PI)), l3no(2) + T(Fr.tex(val))]), h: hb,
               p: { D: D, c: c4, tg: tg, v: 2, ans: [l3fp(PI), l3fp(val)] } };
    return { q: setup + '求 ' + T(l3P(tg)) + '。', a: T(Fr.tex(val)), h: hb,
             p: { D: D, c: c4, tg: tg, v: 0, ans: l3fp(val) } };
  };

  /* ══ L3-3　獨立＋一條含 P(A∪B) 的等式 ⟹ 只剩一個未知數的一次方程式 ══ */
  var L33T = (function () {
    var AA = [F(1, 2), F(1, 3), F(2, 3), F(1, 4), F(3, 4), F(1, 5), F(2, 5), F(3, 5), F(4, 5), F(1, 6), F(5, 6),
              F(1, 8), F(3, 8), F(5, 8), F(1, 10), F(3, 10), F(7, 10), F(2, 7), F(3, 7), F(1, 9), F(2, 9), F(4, 9)];
    var out = [], i, j, m, n, a, b, cc;
    for (i = 0; i < AA.length; i++) {
      a = AA[i];
      for (m = 2; m <= 3; m++) for (n = 1; n <= 2; n++) {
        b = Fr.div(Fr.mul(a, F(1 + n)), Fr.add(F(m - 1), a));
        if (b.n <= 0 || b.n >= b.d || b.d > 60) continue;
        if (Fr.eq(b, a)) continue;
        out.push({ a: a, b: b, form: 0, m: m, n: n });
      }
      for (j = 0; j < AA.length; j++) {
        b = AA[j];
        if (Fr.eq(b, a)) continue;
        cc = Fr.sub(Fr.add(a, b), Fr.mul(a, b));
        if (cc.d > 45) continue;
        out.push({ a: a, b: b, form: 1, c: cc });
      }
    }
    return out;
  })();
  L3.indepEquation = function (r) {
    r();
    var e = r.pick(L33T), a = e.a, b = e.b, v = r.int(0, 2);
    var c = [Fr.mul(a, b), Fr.mul(a, Fr.cp(b)), Fr.mul(Fr.cp(a), b), Fr.mul(Fr.cp(a), Fr.cp(b))];
    var tg = r.pick(v === 1 ? ["B'\\mid A", "A'\\cap B'", 'A\\cap B', 'A\\cup B']
                  : v === 2 ? ["B'\\mid A", 'A\\mid B', "A'\\cap B'", "A'\\mid B'", 'A\\cup B']
                            : ["B'\\mid A", "A'\\cap B'", "B\\mid A'", "A'\\mid B'", 'A\\cap B']);
    var val = l3ev(tg, c);
    var eqt = e.form === 0
      ? l3P('A\\cup B') + '=' + e.m + l3P('B') + '-' + (e.n === 1 ? '' : e.n) + l3P('A')
      : l3P('A\\cup B') + '=' + Fr.tex(e.c);
    var setup = '設樣本空間 ' + T('S') + ' 中的兩事件 ' + T('A') + '、' + T('B') + ' 互相獨立，且 ' + T(l3P('A') + '=' + Fr.tex(a)) + '、' + T(eqt) + '。';
    var hb = '令 ' + T(l3P('B') + '=b') + '。獨立 ⟹ ' + T(l3P('A\\cap B') + '=' + Fr.tex(a) + 'b') + '，代進加法定理 '
           + T(l3P('A\\cup B') + '=' + l3P('A') + '+' + l3P('B') + '-' + l3P('A\\cap B') + '=' + Fr.tex(a) + '+' + Fr.tex(Fr.cp(a)) + 'b')
           + '，再與題目給的 ' + T(eqt) + ' 相等，整條式子只剩 ' + T('b') + ' 一個未知數，解出 ' + T('b=' + Fr.tex(b)) + '。'
           + '接著記住「' + T('A') + '、' + T('B') + ' 獨立 ⟹ ' + T('A') + ' 與 ' + T("B'") + ' 也獨立」（由 ' + T(l3P("A\\cap B'") + '=' + l3P('A') + '-' + l3P('A\\cap B') + '=' + l3P('A') + l3P("B'")) + ' 推得），'
           + '四塊依序是 ' + T(Fr.tex(c[0])) + '、' + T(Fr.tex(c[1])) + '、' + T(Fr.tex(c[2])) + '、' + T(Fr.tex(c[3])) + '。';
    if (v === 1)
      return { q: setup + '求 ' + l3no(1) + T(l3P('B')) + '　' + l3no(2) + T(l3P(tg)) + '。',
               a: l3jo([l3no(1) + T(Fr.tex(b)), l3no(2) + T(Fr.tex(val))]), h: hb,
               p: { a: l3fp(a), form: e.form, tg: tg, v: 1, ans: [l3fp(b), l3fp(val)] } };
    if (v === 2)
      return { q: setup + '求 ' + l3no(1) + T(l3P('A\\cap B')) + '　' + l3no(2) + T(l3P(tg)) + '。',
               a: l3jo([l3no(1) + T(Fr.tex(c[0])), l3no(2) + T(Fr.tex(val))]), h: hb,
               p: { a: l3fp(a), form: e.form, tg: tg, v: 2, ans: [l3fp(c[0]), l3fp(val)] } };
    return { q: setup + '求 ' + T(l3P(tg)) + '。', a: T(Fr.tex(val)), h: hb,
             p: { a: l3fp(a), form: e.form, tg: tg, v: 0, ans: l3fp(val) } };
  };

  /* ══ L3-4　條件機率的最大最小：分母是定值，只要看 P(A∩B) 能多大、能多小 ══ */
  L3.condRange = function (r) {
    r();
    var D, na, nb, tr = 0;
    do {
      D = r.pick([4, 5, 6, 7, 8, 9, 10, 12, 15, 16, 20, 25]);
      na = r.int(1, D - 1); nb = r.int(1, D - 1); tr++;
    } while ((na >= nb || na + nb <= D) && tr < 600);
    if (na >= nb || na + nb <= D) { D = 5; na = 2; nb = 4; }
    var a = F(na, D), b = F(nb, D), v = r.int(0, 2);
    var M = Fr.div(a, b), mm = Fr.div(Fr.sub(Fr.add(a, b), F(1)), b);
    var Mi = a, mi = Fr.sub(Fr.add(a, b), F(1));
    var Mc = Fr.sub(F(1), mm), mc = Fr.sub(F(1), M);
    var setup = '設 ' + T('A') + '、' + T('B') + ' 為樣本空間中的兩事件，' + T(l3P('A') + '=' + Fr.tex(a)) + '、' + T(l3P('B') + '=' + Fr.tex(b)) + '。';
    var hb = T(l3P('A\\mid B') + '=\\dfrac{' + l3P('A\\cap B') + '}{' + l3P('B') + '}') + ' 的分母是定值 ' + T(Fr.tex(b)) + ' ⟹ 只要把 ' + T(l3P('A\\cap B')) + ' 的範圍找出來。'
           + '上界：' + T('A\\cap B\\subseteq A') + ' 且 ' + T('A\\cap B\\subseteq B') + ' ⟹ ' + T(l3P('A\\cap B') + '\\le\\min\\left(' + Fr.tex(a) + ',' + Fr.tex(b) + '\\right)=' + Fr.tex(Mi)) + '（此時 ' + T('A\\subseteq B') + '）。'
           + '下界：' + T(l3P('A\\cup B') + '\\le1') + ' ⟹ ' + T(l3P('A\\cap B') + '\\ge ' + l3P('A') + '+' + l3P('B') + '-1=' + Fr.tex(mi)) + '（此時 ' + T('A\\cup B=S') + '）。'
           + '兩個端點都畫得出文氏圖，所以是最大值與最小值而不只是上下界。';
    if (v === 1)
      return { q: setup + '求 ' + l3no(1) + T(l3P('A\\cap B')) + ' 的最大值與最小值　' + l3no(2) + T(l3P('A\\mid B')) + ' 的最大值。',
               a: l3jo([l3no(1) + '最大值 ' + T(Fr.tex(Mi)) + '、最小值 ' + T(Fr.tex(mi)), l3no(2) + T(Fr.tex(M))]), h: hb,
               p: { a: l3fp(a), b: l3fp(b), v: 1, ans: [l3fp(Mi), l3fp(mi), l3fp(M)] } };
    if (v === 2)
      return { q: setup + '求 ' + l3no(1) + T(l3P('A\\mid B')) + ' 的最大值　' + l3no(2) + T(l3P("A'\\mid B")) + ' 的最大值。',
               a: l3jo([l3no(1) + T(Fr.tex(M)), l3no(2) + T(Fr.tex(Mc))]), h: hb,
               p: { a: l3fp(a), b: l3fp(b), v: 2, ans: [l3fp(M), l3fp(Mc)] } };
    return { q: setup + '若 ' + T(l3P('A\\mid B')) + ' 的最大值為 ' + T('M') + '、最小值為 ' + T('m') + '，求 ' + T('M') + ' 與 ' + T('m') + '。',
             a: T('M=' + Fr.tex(M)) + '、' + T('m=' + Fr.tex(mm)), h: hb,
             p: { a: l3fp(a), b: l3fp(b), v: 0, ans: [l3fp(M), l3fp(mm)] } };
  };

  /* ══ L3-5　條件機率等於 1（或 0）的判讀：看包含關係，不必算分數 ══ */
  function l3die1(r) {
    var k, j;
    switch (r.int(0, 8)) {
      case 0: k = r.int(1, 6); return { t: '點數為 ' + T(k), f: function (n) { return n === k; } };
      case 1: return { t: '點數為奇數', f: function (n) { return n % 2 === 1; } };
      case 2: return { t: '點數為偶數', f: function (n) { return n % 2 === 0; } };
      case 3: return { t: '點數為質數', f: function (n) { return n === 2 || n === 3 || n === 5; } };
      case 4: k = r.int(2, 5); return { t: '點數小於 ' + T(k), f: function (n) { return n < k; } };
      case 5: k = r.int(2, 5); return { t: '點數大於 ' + T(k), f: function (n) { return n > k; } };
      case 6: k = r.int(2, 5); return { t: '點數不超過 ' + T(k), f: function (n) { return n <= k; } };
      case 7: k = r.pick([2, 3]); return { t: '點數為 ' + T(k) + ' 的倍數', f: function (n) { return n % k === 0; } };
      default: k = r.int(1, 5); j = r.int(k + 1, 6); return { t: '點數為 ' + T(k) + ' 或 ' + T(j), f: function (n) { return n === k || n === j; } };
    }
  }
  L3.condOneZero = function (r) {
    r();
    var eA, eB, SA, SB, i, tr = 0, ok = false;
    do {
      eA = l3die1(r); eB = l3die1(r); SA = []; SB = [];
      for (i = 1; i <= 6; i++) { if (eA.f(i)) SA.push(i); if (eB.f(i)) SB.push(i); }
      ok = SA.length >= 1 && SB.length > SA.length && SB.length <= 5 && eA.t !== eB.t;
      if (ok) for (i = 0; i < SA.length; i++) if (SB.indexOf(SA[i]) < 0) ok = false;
      tr++;
    } while (!ok && tr < 600);
    if (!ok) { eA = { t: '點數為 ' + T(1) }; eB = { t: '點數為奇數' }; SA = [1]; SB = [1, 3, 5]; }
    var nA = SA.length, nB = SB.length;
    var c = [F(nA, 6), F(0, 6), F(nB - nA, 6), F(6 - nB, 6)];
    var ones = r.shuffle(["B\\mid A", "A'\\mid B'"]), zeros = r.shuffle(["A\\mid B'", "B'\\mid A"]);
    var rest = r.shuffle(['A\\mid B', "A'\\mid B", "B\\mid A'", "B'\\mid A'"]);
    var v = r.int(0, 2);
    var setup = '擲一顆公正骰子一次。設 ' + T('A') + ' 為「' + eA.t + '」的事件、' + T('B') + ' 為「' + eB.t + '」的事件。';
    var hb = T('A=\\{' + SA.join(',') + '\\}') + '、' + T("A'=\\{" + [1, 2, 3, 4, 5, 6].filter(function (x) { return SA.indexOf(x) < 0; }).join(',') + '\\}') + '、'
           + T('B=\\{' + SB.join(',') + '\\}') + '、' + T("B'=\\{" + [1, 2, 3, 4, 5, 6].filter(function (x) { return SB.indexOf(x) < 0; }).join(',') + '\\}') + '。'
           + T(l3P('X\\mid Y') + '=1') + ' ⟺ ' + T('Y\\subseteq X') + '；' + T(l3P('X\\mid Y') + '=0') + ' ⟺ ' + T('X') + ' 與 ' + T('Y') + ' 互斥。'
           + '本題 ' + T('A\\subseteq B') + '（' + T(nA) + ' 個元素裝在 ' + T(nB) + ' 個元素裡面）⟹ 一頭一尾兩個極端值都用集合關係一眼看出，比代公式快得多。';
    if (v === 2) {
      var sel3 = r.shuffle([ones[0], zeros[0], rest[0]]);
      return { q: setup + '求下列三個值：' + sel3.map(function (x, i2) { return l3no(i2 + 1) + T(l3P(x)); }).join('　') + '。',
               a: l3jo(sel3.map(function (x, i2) { return l3no(i2 + 1) + T(Fr.tex(l3ev(x, c))); })), h: hb,
               p: { eA: eA.t, eB: eB.t, sel: sel3, v: 2, ans: sel3.map(function (x) { return l3fp(l3ev(x, c)); }) } };
    }
    var n1 = r.int(1, 2), n0 = r.int(1, 2);
    var sel = r.shuffle(ones.slice(0, n1).concat(zeros.slice(0, n0)).concat(rest.slice(0, 5 - n1 - n0)));
    var want = v === 0 ? F(1) : F(0), hit = [];
    for (i = 0; i < 5; i++) if (Fr.eq(l3ev(sel[i], c), want)) hit.push(i + 1);
    return { q: setup + '在下列五個值之中：' + sel.map(function (x, i2) { return l3no(i2 + 1) + T(l3P(x)); }).join('　')
                + '，哪幾個的值等於 ' + T(v === 0 ? 1 : 0) + '？（把編號全部寫出來）',
             a: l3opt(hit), h: hb,
             p: { eA: eA.t, eB: eB.t, sel: sel, want: v === 0 ? 1 : 0, v: v, ans: hit } };
  };

  /* ══ L3-6　列聯表＋「兩屬性獨立」：每一列都照總比例切開，等價判準是 ad=bc ══ */
  var L36C = [
    { g: ['理組', '文組'], y: '喜歡', n: '不喜歡', u: '位', who: '同學', ask: '詢問是否喜歡某項活動' },
    { g: ['男生', '女生'], y: '有參加社團', n: '沒有參加社團', u: '位', who: '學生', ask: '調查是否參加社團' },
    { g: ['住校生', '通勤生'], y: '有近視', n: '沒有近視', u: '位', who: '學生', ask: '檢查視力' },
    { g: ['甲廠', '乙廠'], y: '通過檢驗', n: '沒有通過檢驗', u: '件', who: '產品', ask: '逐件檢驗' },
    { g: ['有補習', '沒有補習'], y: '英文及格', n: '英文不及格', u: '位', who: '考生', ask: '統計英文成績' },
    { g: ['一年級', '二年級'], y: '有訂閱', n: '沒有訂閱', u: '位', who: '學生', ask: '調查訂閱情形' },
    { g: ['有運動習慣', '沒有運動習慣'], y: '血壓正常', n: '血壓偏高', u: '位', who: '受檢者', ask: '量血壓' }
  ];
  L3.tableIndepPick = function (r) {
    r();
    var ct = r.pick(L36C), N, n1, n2, M, a, b, cc, d, tr = 0, ok = false;
    do {
      N = r.pick([40, 50, 60, 80, 100, 120, 150, 200, 240, 300]);
      n1 = r.int(1, 9) * (N / 10); n2 = N - n1;
      M = r.int(1, 9) * (N / 10);
      ok = n1 >= 10 && n2 >= 10 && M >= 10 && M <= N - 10 && (M * n1) % N === 0;
      if (ok) { a = M * n1 / N; b = M * n2 / N; cc = n1 - a; d = n2 - b; ok = a >= 2 && b >= 2 && cc >= 2 && d >= 2; }
      tr++;
    } while (!ok && tr < 800);
    if (!ok) { N = 100; n1 = 60; n2 = 40; M = 50; a = 30; b = 20; cc = 30; d = 20; }
    var v = r.int(0, 2);
    var head = '隨機抽出' + ct.g[0] + ' ' + T(n1) + ' ' + ct.u + '、' + ct.g[1] + ' ' + T(n2) + ' ' + ct.u + ct.who + '（共 ' + T(N) + ' ' + ct.u + '），' + ct.ask + '。'
             + '設' + ct.g[0] + '之中' + ct.y + '的有 ' + T('a') + ' ' + ct.u + '、' + ct.n + '的有 ' + T('c') + ' ' + ct.u + '；'
             + ct.g[1] + '之中' + ct.y + '的有 ' + T('b') + ' ' + ct.u + '、' + ct.n + '的有 ' + T('d') + ' ' + ct.u + '。'
             + '已知全部 ' + T(N) + ' ' + ct.u + '之中共有 ' + T(M) + ' ' + ct.u + ct.y + '，且「組別」與「' + ct.y + '與否」為互相獨立的兩事件。';
    var rt = F(M, N);
    var hb = '獨立 ⟹ ' + T(l3P(tx(ct.y) + '\\mid' + tx(ct.g[0])) + '=' + l3P(tx(ct.y) + '\\mid' + tx(ct.g[1])) + '=' + l3P(tx(ct.y)) + '=\\dfrac{' + M + '}{' + N + '}=' + Fr.tex(rt))
           + ' ⟹ 每一列都照同一個比例切開：' + T('a=' + n1 + '\\times' + Fr.tex(rt) + '=' + a) + '、' + T('c=' + n1 + '-' + a + '=' + cc) + '、'
           + T('b=' + n2 + '\\times' + Fr.tex(rt) + '=' + b) + '、' + T('d=' + n2 + '-' + b + '=' + d) + '。'
           + '順帶一提，' + T('ad=bc') + ' 本身就是「兩屬性獨立」的等價條件（由 ' + T('\\dfrac{a}{a+c}=\\dfrac{b}{b+d}') + ' 交叉相乘整理即得），看到列聯表問獨立先算交叉乘積最快。';
    if (v === 1)
      return { q: head + '求 ' + l3no(1) + T('a') + ' 的值　' + l3no(2) + T(l3P(tx(ct.g[0]) + '\\mid' + tx(ct.y))) + '。',
               a: l3jo([l3no(1) + T(a) + ' ' + ct.u, l3no(2) + T(Fr.tex(F(a, M)))]), h: hb,
               p: { N: N, n1: n1, n2: n2, M: M, v: 1, ans: [a, l3fp(F(a, M))] } };
    if (v === 2)
      return { q: head + '求 ' + l3no(1) + T('d') + ' 的值　' + l3no(2) + T(l3P(tx(ct.n) + '\\mid' + tx(ct.g[1]))) + '。',
               a: l3jo([l3no(1) + T(d) + ' ' + ct.u, l3no(2) + T(Fr.tex(F(d, n2)))]), h: hb,
               p: { N: N, n1: n1, n2: n2, M: M, v: 2, ans: [d, l3fp(F(d, n2))] } };
    var forms = r.shuffle(['a', 'b', 'c', 'd', 'a+d', 'b+c', 'a+b', 'c+d']).slice(0, 4);
    var real = { a: a, b: b, c: cc, d: d, 'a+d': a + d, 'b+c': b + cc, 'a+b': a + b, 'c+d': cc + d };
    var stm = [], tw, dd, i;
    for (i = 0; i < 4; i++) {
      dd = r.pick([-3, -2, -1, 0, 0, 1, 2, 3]);
      tw = real[forms[i]] + dd;
      if (tw <= 0) tw = real[forms[i]] + 1;
      stm.push(forms[i] + '=' + tw);
    }
    stm = r.shuffle(stm.concat(['ad=bc']));
    var hit2 = [];
    for (i = 0; i < 5; i++) {
      if (stm[i] === 'ad=bc') { hit2.push(i + 1); continue; }
      var kk = stm[i].split('='); if (real[kk[0]] === parseInt(kk[1], 10)) hit2.push(i + 1);
    }
    return { q: head + '試選出所有正確的選項：' + stm.map(function (x, i2) { return l3no(i2 + 1) + T(x); }).join('　') + '。（把編號全部寫出來）',
             a: l3opt(hit2), h: hb,
             p: { N: N, n1: n1, n2: n2, M: M, stm: stm, v: 0, ans: hit2 } };
  };

  /* ══ L3-7　不放回、問「第 k 次取到某色」：排成一列，每個位置機會都一樣 ══ */
  var L37K = ['紅', '白', '黃', '藍', '綠', '黑', '紫', '橙'];
  L3.kthDrawColor = function (r) {
    r();
    var v = r.int(0, 2), cols, cnt, N, i, tar, k, tr = 0, ok = false;
    do {
      cols = r.shuffle(L37K).slice(0, r.int(3, 5));
      cnt = []; N = 0;
      for (i = 0; i < cols.length; i++) { cnt.push(r.int(1, 8)); N += cnt[i]; }
      tar = r.int(0, cols.length - 1);
      k = r.int(2, 5);
      ok = N >= 10 && N <= 22 && cnt[tar] >= 1 && cnt[tar] < N && k <= N - 1;
      if (ok && v === 1) ok = (N - cnt[tar] >= k - 1) && cnt[tar] < N - k + 1;
      if (ok && v === 2) ok = cnt[tar] >= 2 && cnt[tar] - 1 < N - 1;
      tr++;
    } while (!ok && tr < 800);
    if (!ok) { cols = ['紅', '白', '黃']; cnt = [3, 5, 4]; N = 12; tar = 0; k = 3; }
    var cname = cols[tar], nT = cnt[tar];
    var lst = cols.map(function (cl, i2) { return T(cnt[i2]) + ' 顆' + cl + '球'; }).join('、');
    var A1 = F(nT, N), A2 = F(nT, N - k + 1), A3 = F(nT - 1, N - 1);
    var setup = '袋中有 ' + lst + '，共 ' + T(N) + ' 顆。每次從袋中取出一球且不放回。';
    var hb = '不放回一顆一顆取出，等於把 ' + T(N) + ' 顆球隨機排成一列；每一顆球排到第 ' + T(k) + ' 個位置的機會都相同 ⟹ 第 ' + T(k)
           + ' 次取到' + cname + '球的機率就是 ' + T('\\dfrac{' + nT + '}{' + N + '}' + (gcd(nT, N) > 1 ? '=' + Fr.tex(A1) : '')) + '，和 ' + T(k) + ' 完全無關。'
           + '但只要題目多給了一個「已知」，樣本空間就縮小了：例如已知前 ' + T(k - 1) + ' 次都沒取到' + cname + '球，袋中只剩 ' + T(N - k + 1) + ' 顆而' + cname + '球還是 ' + T(nT) + ' 顆；'
           + '已知第 ' + T(1) + ' 次取到' + cname + '球，則剩下 ' + T(N - 1) + ' 顆中' + cname + '球只有 ' + T(nT - 1) + ' 顆。';
    if (v === 1)
      return { q: setup + '求 ' + l3no(1) + '第 ' + T(k) + ' 次取到' + cname + '球的機率　' + l3no(2) + '已知前 ' + T(k - 1) + ' 次都沒有取到' + cname + '球，第 ' + T(k) + ' 次取到' + cname + '球的機率。',
               a: l3jo([l3no(1) + T(Fr.tex(A1)), l3no(2) + T(Fr.tex(A2))]), h: hb,
               p: { cols: cols, cnt: cnt, tar: tar, k: k, v: 1, ans: [l3fp(A1), l3fp(A2)] } };
    if (v === 2)
      return { q: setup + '求 ' + l3no(1) + '第 ' + T(k) + ' 次取到' + cname + '球的機率　' + l3no(2) + '已知第 ' + T(1) + ' 次取到' + cname + '球，第 ' + T(k) + ' 次也取到' + cname + '球的機率。',
               a: l3jo([l3no(1) + T(Fr.tex(A1)), l3no(2) + T(Fr.tex(A3))]), h: hb,
               p: { cols: cols, cnt: cnt, tar: tar, k: k, v: 2, ans: [l3fp(A1), l3fp(A3)] } };
    return { q: setup + '求第 ' + T(k) + ' 次取到' + cname + '球的機率。', a: T(Fr.tex(A1)), h: hb,
             p: { cols: cols, cnt: cnt, tar: tar, k: k, v: 0, ans: l3fp(A1) } };
  };

  /* ══ L3-8　互相獨立、重複 n 次、問「至少 k 次成功」：走反面 ══ */
  var L38C = [
    { x: '射手', v: '射擊', y: '命中目標', u: '次' }, { x: '人', v: '投籃', y: '投進', u: '次' },
    { x: '考生', v: '作答', y: '答對', u: '題' }, { x: '球隊', v: '比賽', y: '獲勝', u: '場' },
    { x: '機器', v: '檢測', y: '故障', u: '次' }, { x: '玩家', v: '抽卡', y: '抽中稀有卡', u: '次' }
  ];
  var L38P = [F(1, 2), F(1, 3), F(2, 3), F(1, 4), F(3, 4), F(1, 5), F(2, 5), F(3, 5), F(4, 5), F(1, 6), F(5, 6), F(3, 8), F(2, 7), F(3, 10), F(7, 10)];
  L3.atLeastTwoTrials = function (r) {
    r();
    var ct = r.pick(L38C), p = r.pick(L38P), n = r.int(4, 6), v = r.int(0, 2);
    if (v === 2 && n < 5) n = 5;
    var k = v === 2 ? 3 : 2, i;
    var less = F(0);
    for (i = 0; i < k; i++) less = Fr.add(less, l3binP(n, i, p));
    var atl = Fr.sub(F(1), less), one = l3binP(n, 1, p);
    var q0 = Fr.cp(p);
    var setup = '某' + ct.x + '每次' + ct.v + '「' + ct.y + '」的機率均為 ' + T(Fr.tex(p)) + '，且各次互相獨立。今共' + ct.v + ' ' + T(n) + ' ' + ct.u + '。';
    var hb = '「至少 ' + T(k) + ' ' + ct.u + '」的反面只有 ' + T(k) + ' 種情形（' + (k === 2 ? T(0) + '、' + T(1) : T(0) + '、' + T(1) + '、' + T(2)) + ' ' + ct.u + '），比正面列舉少好幾項 ⟹ 走反面。'
           + '沒有任何一' + ct.u + '「' + ct.y + '」是 ' + T(l3pw(Fr.tex(q0), n) + '=' + Fr.tex(l3binP(n, 0, p))) + '；'
           + '恰有一' + ct.u + '要先選「是哪一' + ct.u + '成功」共 ' + T(l3CT(n, 1) + '=' + n) + ' 種，再乘 ' + T(l3pw(Fr.tex(p), 1) + l3pw(Fr.tex(q0), n - 1)) + ' ⟹ ' + T(Fr.tex(one)) + '。'
           + '那個 ' + T(l3CT(n, k)) + ' 數的是「哪幾' + ct.u + '成功」的選法，不是機率的一部分。';
    if (v === 1)
      return { q: setup + '求 ' + l3no(1) + '恰有 ' + T(1) + ' ' + ct.u + '「' + ct.y + '」　' + l3no(2) + '至少有 ' + T(2) + ' ' + ct.u + '「' + ct.y + '」的機率。',
               a: l3jo([l3no(1) + T(Fr.tex(one)), l3no(2) + T(Fr.tex(atl))]), h: hb,
               p: { n: n, k: 2, p: l3fp(p), v: 1, ans: [l3fp(one), l3fp(atl)] } };
    return { q: setup + '求至少有 ' + T(k) + ' ' + ct.u + '「' + ct.y + '」的機率。', a: T(Fr.tex(atl)), h: hb,
             p: { n: n, k: k, p: l3fp(p), v: v, ans: l3fp(atl) } };
  };

  /* ══ L3-9　「在恰有一人成功的條件下，是甲成功」：分母兩（三）條路徑，分子只留一條 ══ */
  var L39C = [
    { v: '朝同一目標各射擊一次', y: '命中目標', s: '命中' }, { v: '各投籃一次', y: '投進', s: '投進' },
    { v: '各解一道題', y: '解出', s: '解出' }, { v: '各抽一次獎', y: '抽中', s: '抽中' },
    { v: '各射擊一次', y: '命中', s: '命中' }
  ];
  var L39P = [F(1, 2), F(1, 3), F(2, 3), F(1, 4), F(3, 4), F(1, 5), F(2, 5), F(3, 5), F(4, 5), F(1, 6), F(5, 6), F(3, 8), F(2, 7), F(3, 10)];
  L3.exactlyOneHit = function (r) {
    r();
    var v = r.int(0, 2), m = v === 2 ? 3 : 2;
    var nm = r.pick([['甲', '乙', '丙'], ['小文', '阿遠', '小美'], ['第一位', '第二位', '第三位']]).slice(0, m);
    var ct = r.pick(L39C), ps = [], used = {}, f, i, j;
    while (ps.length < m) { f = r.pick(L39P); if (used[f.n + '/' + f.d]) continue; used[f.n + '/' + f.d] = 1; ps.push(f); }
    var qs = ps.map(Fr.cp), one = F(0), first = F(0);
    for (i = 0; i < m; i++) {
      var w = F(1);
      for (j = 0; j < m; j++) w = Fr.mul(w, i === j ? ps[j] : qs[j]);
      one = Fr.add(one, w);
      if (i === 0) first = w;
    }
    var A = Fr.div(first, one);
    var setup = nm.join('、') + (m === 2 ? '兩' : '三') + '人' + ct.v + '，' + ct.y + '的機率分別為 ' + ps.map(function (x) { return T(Fr.tex(x)); }).join('、') + '，且各人是否' + ct.s + '互不影響。';
    var hb = '「恰有一人' + ct.s + '」拆成 ' + T(m) + ' 條互斥的路徑，每條路徑就是 ' + T(m) + ' 個數字連乘：'
           + nm.map(function (x, i2) { return '只有' + x + ct.s + '的機率是 ' + T(Fr.tex((function () { var w2 = F(1), j2; for (j2 = 0; j2 < m; j2++) w2 = Fr.mul(w2, i2 === j2 ? ps[j2] : qs[j2]); return w2; })())); }).join('、') + '。'
           + '分母是這 ' + T(m) + ' 條相加 ' + T(Fr.tex(one)) + '，分子只留' + nm[0] + '那一條——條件機率本質上就是把幾條路徑的權重拿來比。';
    if (v === 1)
      return { q: setup + '求 ' + l3no(1) + '恰有一人' + ct.s + '的機率　' + l3no(2) + '在「恰有一人' + ct.s + '」的條件下，是' + nm[0] + ct.s + '的機率。',
               a: l3jo([l3no(1) + T(Fr.tex(one)), l3no(2) + T(Fr.tex(A))]), h: hb,
               p: { ps: ps.map(l3fp), v: 1, ans: [l3fp(one), l3fp(A)] } };
    return { q: setup + '在「恰有一人' + ct.s + '」的條件下，求是' + nm[0] + ct.s + '的機率。',
             a: T(Fr.tex(A)), h: hb,
             p: { ps: ps.map(l3fp), v: v, ans: l3fp(A) } };
  };

  /* ══ L3-10　兩分支貝氏：先把通往結果的每一條路徑乘出來當分母 ══ */
  var L310C = [
    { o: '產品', unit: '件', b: ['甲生產線', '乙生產線'], Y: '不良品' },
    { o: '零件', unit: '個', b: ['甲供應商', '乙供應商'], Y: '瑕疵品' },
    { o: '水果', unit: '顆', b: ['甲農場', '乙農場'], Y: '特級果' },
    { o: '訂單', unit: '筆', b: ['白天班', '夜間班'], Y: '延遲到貨的訂單' },
    { o: '成品', unit: '件', b: ['甲機器', '乙機器'], Y: '不合格品' },
    { o: '考卷', unit: '份', b: ['甲考場', '乙考場'], Y: '滿分卷' }
  ];
  L3.bayesTwoBranch = function (r) {
    r();
    var ct = r.pick(L310C), v = r.int(0, 2), w1, r1, r2, tr = 0;
    do { w1 = r.int(1, 19) * 5; r1 = r.int(1, 18) * 5; r2 = r.int(1, 18) * 5; tr++; }
    while ((r1 === r2 || w1 === 100 || w1 === 0) && tr < 400);
    var w2 = 100 - w1;
    var P1 = Fr.mul(F(w1, 100), F(r1, 100)), P2 = Fr.mul(F(w2, 100), F(r2, 100));
    var Q1 = Fr.mul(F(w1, 100), F(100 - r1, 100)), Q2 = Fr.mul(F(w2, 100), F(100 - r2, 100));
    var PY = Fr.add(P1, P2), PN = Fr.add(Q1, Q2);
    var A0 = Fr.div(P2, PY), A2 = Fr.div(Q1, PN);
    var head = '某批' + ct.o + '之中有 ' + T(l3pct(w1)) + ' 來自' + ct.b[0] + '、' + T(l3pct(w2)) + ' 來自' + ct.b[1] + '；'
             + ct.b[0] + '的' + ct.o + '之中「' + ct.Y + '」佔 ' + T(l3pct(r1)) + '、' + ct.b[1] + '的' + ct.o + '之中「' + ct.Y + '」佔 ' + T(l3pct(r2)) + '。今任取一' + ct.unit + ct.o + '，';
    var hb = '畫兩層樹狀圖：第一層是「來自' + ct.b[0] + '／' + ct.b[1] + '」，第二層是「是不是' + ct.Y + '」。通往「是' + ct.Y + '」的葉子有兩片：'
           + T(Fr.tex(F(w1, 100)) + '\\times' + Fr.tex(F(r1, 100)) + '=' + Fr.tex(P1)) + ' 與 ' + T(Fr.tex(F(w2, 100)) + '\\times' + Fr.tex(F(r2, 100)) + '=' + Fr.tex(P2)) + '，'
           + '把這兩條路徑加起來就是分母 ' + T(Fr.tex(PY)) + '；通往「不是' + ct.Y + '」的兩片則是 ' + T(Fr.tex(Q1)) + ' 與 ' + T(Fr.tex(Q2)) + '。'
           + '要問哪一個來源，分子就只留哪一條路徑——先確認分母是「已知的那件事」，可以擋掉分子分母寫反的錯。';
    if (v === 1)
      return { q: head + '求 ' + l3no(1) + '它是「' + ct.Y + '」的機率　' + l3no(2) + '已知它是「' + ct.Y + '」，求它來自' + ct.b[1] + '的機率。',
               a: l3jo([l3no(1) + T(Fr.tex(PY)), l3no(2) + T(Fr.tex(A0))]), h: hb,
               p: { w1: w1, r1: r1, r2: r2, v: 1, ans: [l3fp(PY), l3fp(A0)] } };
    if (v === 2)
      return { q: head + '已知它不是「' + ct.Y + '」，求它來自' + ct.b[0] + '的機率。', a: T(Fr.tex(A2)), h: hb,
               p: { w1: w1, r1: r1, r2: r2, v: 2, ans: l3fp(A2) } };
    return { q: head + '已知它是「' + ct.Y + '」，求它來自' + ct.b[1] + '的機率。', a: T(Fr.tex(A0)), h: hb,
             p: { w1: w1, r1: r1, r2: r2, v: 0, ans: l3fp(A0) } };
  };

  /* ══ L3-11　貝氏反過來問：設未知的那個比率為 p，列一元一次方程式 ══ */
  var L311W = [[F(1, 3), F(1, 2), F(1, 6)], [F(1, 2), F(1, 4), F(1, 4)], [F(2, 5), F(2, 5), F(1, 5)], [F(1, 4), F(1, 2), F(1, 4)],
               [F(3, 10), F(1, 2), F(1, 5)], [F(1, 6), F(1, 3), F(1, 2)], [F(2, 5), F(1, 2), F(1, 10)], [F(1, 5), F(1, 2), F(3, 10)],
               [F(1, 3), F(1, 3), F(1, 3)], [F(1, 2), F(3, 10), F(1, 5)], [F(2, 5), F(3, 10), F(3, 10)], [F(1, 6), F(1, 2), F(1, 3)],
               [F(1, 5), F(3, 5), F(1, 5)], [F(3, 8), F(1, 2), F(1, 8)], [F(1, 4), F(5, 12), F(1, 3)]];
  var L311Q = [F(1, 4), F(1, 5), F(1, 3), F(3, 10), F(2, 5), F(1, 2), F(1, 10), F(1, 6), F(1, 8), F(3, 8), F(1, 20), F(3, 20), F(2, 5)];
  var L311T = (function () {
    var out = [], i, u, r1, r2, j, w, ks, kn, x, pct;
    for (i = 0; i < L311W.length; i++) for (u = 0; u < 3; u++) {
      w = L311W[i]; ks = [0, 1, 2]; ks.splice(u, 1);
      for (r1 = 1; r1 <= 9; r1++) for (r2 = 1; r2 <= 9; r2++) {
        if (r1 === r2) continue;
        for (j = 0; j < L311Q.length; j++) {
          kn = Fr.add(Fr.mul(w[ks[0]], F(r1, 100)), Fr.mul(w[ks[1]], F(r2, 100)));
          x = Fr.div(Fr.mul(L311Q[j], kn), Fr.mul(w[u], Fr.sub(F(1), L311Q[j])));
          pct = Fr.mul(x, F(100));
          if (pct.d !== 1 || pct.n < 1 || pct.n > 20) continue;
          if (pct.n === r1 || pct.n === r2) continue;
          out.push([i, u, r1, r2, j, pct.n]);
        }
      }
    }
    return out;
  })();
  var L311C = [{ m: '機器', o: '產品', bad: '不良品', rate: '不良率', nm: ['甲', '乙', '丙'], head: '某工廠有甲、乙、丙三部機器' },
               { m: '生產線', o: '產品', bad: '瑕疵品', rate: '瑕疵率', nm: ['甲', '乙', '丙'], head: '某工廠有甲、乙、丙三條生產線' },
               { m: '供應商', o: '零件', bad: '不良品', rate: '不良率', nm: ['甲', '乙', '丙'], head: '某公司向甲、乙、丙三家供應商進貨' }];
  L3.bayesUnknownRate = function (r) {
    r();
    var e = r.pick(L311T), ct = r.pick(L311C), v = r.int(0, 2);
    var w = L311W[e[0]], u = e[1], r1 = e[2], r2 = e[3], t = L311Q[e[4]], xp = e[5];
    var ks = [0, 1, 2]; ks.splice(u, 1);
    var rate = [0, 0, 0]; rate[ks[0]] = r1; rate[ks[1]] = r2; rate[u] = xp;
    var x = F(xp, 100);
    var tot = Fr.add(Fr.add(Fr.mul(w[0], F(rate[0], 100)), Fr.mul(w[1], F(rate[1], 100))), Fr.mul(w[2], F(rate[2], 100)));
    var back = Fr.div(Fr.mul(w[ks[0]], F(r1, 100)), tot);
    var tT = (Fr.mul(t, F(100)).d === 1) ? l3pct(Fr.mul(t, F(100)).n) : Fr.tex(t);
    var head = ct.head + '，產量分別佔總產量的 ' + w.map(function (f) { return T(Fr.tex(f)); }).join('、') + '。'
             + '已知' + ct.nm[ks[0]] + ct.m + '的' + ct.rate + '為 ' + T(l3pct(r1)) + '、' + ct.nm[ks[1]] + ct.m + '的' + ct.rate + '為 ' + T(l3pct(r2)) + '。'
             + '若所有' + ct.bad + '之中，產自' + ct.nm[u] + ct.m + '者佔 ' + T(tT) + '，';
    var hb = '設' + ct.nm[u] + ct.m + '的' + ct.rate + '為 ' + T('p') + '。三條「' + ct.bad + '」的路徑分別是 '
           + T(Fr.tex(w[ks[0]]) + '\\times' + Fr.tex(F(r1, 100)) + '=' + Fr.tex(Fr.mul(w[ks[0]], F(r1, 100)))) + '、'
           + T(Fr.tex(w[ks[1]]) + '\\times' + Fr.tex(F(r2, 100)) + '=' + Fr.tex(Fr.mul(w[ks[1]], F(r2, 100)))) + '、'
           + T(Fr.tex(w[u]) + 'p') + '，把三條加起來就是全部的' + ct.rate + '。'
           + '「' + ct.nm[u] + '那一條除以總和等於 ' + T(tT) + '」列成一元一次方程式即可；'
           + '也可以直接改寫成「' + ct.nm[u] + '那一條 : 其餘兩條 ' + T('=' + t.n + ':' + (t.d - t.n)) + '」，一行就解完。';
    if (v === 1)
      return { q: head + '求 ' + l3no(1) + ct.nm[u] + ct.m + ct.o + '的' + ct.rate + '　' + l3no(2) + '全部' + ct.o + '的' + ct.rate + '。',
               a: l3jo([l3no(1) + T(Fr.tex(x)), l3no(2) + T(Fr.tex(tot))]), h: hb,
               p: { wi: e[0], u: u, r1: r1, r2: r2, ti: e[4], v: 1, ans: [l3fp(x), l3fp(tot)] } };
    if (v === 2)
      return { q: head + '求 ' + l3no(1) + ct.nm[u] + ct.m + ct.o + '的' + ct.rate + '　' + l3no(2) + '已知取到一' + (ct.o === '零件' ? '個' : '件') + ct.bad + '，它產自' + ct.nm[ks[0]] + ct.m + '的機率。',
               a: l3jo([l3no(1) + T(Fr.tex(x)), l3no(2) + T(Fr.tex(back))]), h: hb,
               p: { wi: e[0], u: u, r1: r1, r2: r2, ti: e[4], v: 2, ans: [l3fp(x), l3fp(back)] } };
    return { q: head + '求' + ct.nm[u] + ct.m + ct.o + '的' + ct.rate + '。', a: T(Fr.tex(x)), h: hb,
             p: { wi: e[0], u: u, r1: r1, r2: r2, ti: e[4], v: 0, ans: l3fp(x) } };
  };

  /* ══ L3-12　先選容器、再從容器取球：各袋球數不同，不能把總數直接相除 ══ */
  var L312K = ['紅', '白', '藍', '黃', '綠', '黑'];
  L3.bayesThreeBags = function (r) {
    r();
    var v = r.int(0, 2), nb = v === 2 ? 2 : 3;
    var bagNm = ['甲', '乙', '丙'].slice(0, nb);
    var cols, M, tot, i, j, tr = 0, ok = false;
    do {
      cols = r.shuffle(L312K).slice(0, 3);
      M = []; tot = [];
      for (i = 0; i < nb; i++) { M.push([r.int(1, 6), r.int(1, 6), r.int(1, 6)]); tot.push(M[i][0] + M[i][1] + M[i][2]); }
      ok = true;
      for (i = 0; i < nb; i++) if (tot[i] < 6 || tot[i] > 14) ok = false;
      if (ok) { ok = false; for (i = 0; i < nb; i++) for (j = i + 1; j < nb; j++) if (tot[i] !== tot[j]) ok = true; }
      tr++;
    } while (!ok && tr < 600);
    if (!ok) { cols = ['紅', '白', '藍']; M = [[2, 5, 3], [4, 2, 2], [3, 3, 4]].slice(0, nb); tot = M.map(function (x) { return x[0] + x[1] + x[2]; }); }
    var ci = r.int(0, 2), cname = cols[ci];
    var wt = [];
    if (nb === 2) { var k1 = r.int(1, 4), dn = r.pick([5, 6, 7, 8, 9, 10]); if (k1 >= dn) k1 = 1; wt = [F(k1, dn), F(dn - k1, dn)]; }
    else wt = [F(1, 3), F(1, 3), F(1, 3)];
    var paths = [], PY = F(0);
    for (i = 0; i < nb; i++) { paths.push(Fr.mul(wt[i], F(M[i][ci], tot[i]))); PY = Fr.add(PY, paths[i]); }
    var bi = r.int(0, nb - 1), A = Fr.div(paths[bi], PY);
    var desc = bagNm.map(function (bn, i2) { return bn + '袋有 ' + cols.map(function (cl, j2) { return T(M[i2][j2]) + ' 顆' + cl + '球'; }).join('、'); }).join('；');
    var pickTxt = nb === 3 ? '今隨機選一袋（三袋被選中的機會均等），再從該袋中任取一球。'
                           : '今選中甲袋的機率為 ' + T(Fr.tex(wt[0])) + '、選中乙袋的機率為 ' + T(Fr.tex(wt[1])) + '，選定後再從該袋中任取一球。';
    var hb = (nb === 3 ? '三袋的球數分別是 ' + tot.map(function (x) { return T(x); }).join('、') + '——不一樣！所以不能把' + cname + '球的總數除以全部球數，'
                       : '兩袋的球數是 ' + tot.map(function (x) { return T(x); }).join('、') + '，而且選袋的機會也不相等，')
           + '一定要先乘選中該袋的機率再乘各袋自己的比例：'
           + bagNm.map(function (bn, i2) { return T(Fr.tex(wt[i2]) + '\\times' + Fr.tex(F(M[i2][ci], tot[i2])) + '=' + Fr.tex(paths[i2])); }).join('、') + '。'
           + '把這 ' + T(nb) + ' 條路徑加起來就是取到' + cname + '球的機率 ' + T(Fr.tex(PY)) + '（也就是第二小題的分母），分子只留指定的那一袋。';
    if (v === 1)
      return { q: desc + '。' + pickTxt + '已知取到的是' + cname + '球，求它取自' + bagNm[bi] + '袋的機率。',
               a: T(Fr.tex(A)), h: hb,
               p: { M: M, cols: cols, ci: ci, bi: bi, wt: wt.map(l3fp), v: 1, ans: l3fp(A) } };
    return { q: desc + '。' + pickTxt + '求 ' + l3no(1) + '取到' + cname + '球的機率　' + l3no(2) + '已知取到的是' + cname + '球，它取自' + bagNm[bi] + '袋的機率。',
             a: l3jo([l3no(1) + T(Fr.tex(PY)), l3no(2) + T(Fr.tex(A))]), h: hb,
             p: { M: M, cols: cols, ci: ci, bi: bi, wt: wt.map(l3fp), v: v, ans: [l3fp(PY), l3fp(A)] } };
  };

  /* ══ L3-13　不盡相異物排列的條件機率：把「已知」那一格釘死，剩下的格子重新看一次 ══ */
  var L313W = [['好', '讀', '書'], ['春', '夏', '秋'], ['東', '西', '南'], ['天', '地', '人'], ['金', '木', '水'], ['甲', '乙', '丙']];
  L3.permMultiCond = function (r) {
    r();
    var v = r.int(0, 2), ws, cn, N, i, xi, yi, tr = 0, ok = false;
    do {
      ws = r.pick(L313W); cn = [r.int(1, 4), r.int(1, 4), r.int(1, 4)];
      N = cn[0] + cn[1] + cn[2];
      xi = r.int(0, 2); yi = r.int(0, 2);
      ok = N >= 6 && N <= 9;
      if (ok && v === 1) ok = (yi !== xi) && cn[yi] >= 1;
      else if (ok) ok = cn[xi] >= 2;
      tr++;
    } while (!ok && tr < 800);
    if (!ok) { ws = ['好', '讀', '書']; cn = [3, 3, 3]; N = 9; xi = 0; yi = 1; }
    var X = ws[xi], Y = ws[yi];
    var A0 = F(cn[xi] - 1, N - 1), A1 = F(cn[yi], N - 1), A2 = F(cn[xi], N);
    var head = '將 ' + cn.map(function (c2, i2) { return T(c2) + ' 個「' + ws[i2] + '」'; }).join('、') + '（共 ' + T(N) + ' 個字）隨機排成一列。';
    var hbA = '走法一（排列數）：末格為「' + X + '」的排法有 ' + T('\\dfrac{' + (N - 1) + '!}{' + (cn[xi] - 1) + '!\\,' + cn[(xi + 1) % 3] + '!\\,' + cn[(xi + 2) % 3] + '!}') + ' 種，'
            + '首末兩格都是「' + X + '」的排法有 ' + T('\\dfrac{' + (N - 2) + '!}{' + (cn[xi] - 2) + '!\\,' + cn[(xi + 1) % 3] + '!\\,' + cn[(xi + 2) % 3] + '!}') + ' 種，兩者相除。'
            + '走法二（縮小樣本空間）：把末格先釘死成「' + X + '」，剩下 ' + T(N - 1) + ' 格由「' + X + '」' + T(cn[xi] - 1) + ' 個與其餘 ' + T(N - cn[xi]) + ' 個字填滿，每個字排到第一格的機會均等 ⟹ 直接用 ' + T('\\dfrac{' + (cn[xi] - 1) + '}{' + (N - 1) + '}' + (gcd(cn[xi] - 1, N - 1) > 1 ? '=' + Fr.tex(A0) : '')) + '。'
            + '走法二快得多，但要說得出「為什麼剩下 ' + T(N - 1) + ' 個字排到第一格的機會均等」——因為原本的排列完全隨機，固定一格之後其餘各格仍然是完全隨機的排列。';
    if (v === 1) {
      var hbB = '把第一格先釘死成「' + X + '」，剩下 ' + T(N - 1) + ' 格由「' + X + '」' + T(cn[xi] - 1) + ' 個、「' + Y + '」' + T(cn[yi]) + ' 個與另一種字 ' + T(N - cn[xi] - cn[yi]) + ' 個填滿；'
              + '每個字排到最後一格的機會均等 ⟹ 機率就是 ' + T('\\dfrac{' + cn[yi] + '}{' + (N - 1) + '}' + (gcd(cn[yi], N - 1) > 1 ? '=' + Fr.tex(A1) : '')) + '。'
              + '硬算也可以：末字為「' + Y + '」且首字為「' + X + '」的排法除以首字為「' + X + '」的排法，中間 ' + T(N - 2) + ' 格用不盡相異物排列數各算一次。';
      return { q: head + '已知第一個字是「' + X + '」，求最後一個字是「' + Y + '」的機率。', a: T(Fr.tex(A1)), h: hbB,
               p: { cn: cn, xi: xi, yi: yi, v: 1, ans: l3fp(A1) } };
    }
    if (v === 2)
      return { q: head + '求 ' + l3no(1) + '最後一個字是「' + X + '」的機率　' + l3no(2) + '已知最後一個字是「' + X + '」，第一個字也是「' + X + '」的機率。',
               a: l3jo([l3no(1) + T(Fr.tex(A2)), l3no(2) + T(Fr.tex(A0))]), h: hbA,
               p: { cn: cn, xi: xi, v: 2, ans: [l3fp(A2), l3fp(A0)] } };
    return { q: head + '已知最後一個字是「' + X + '」，求第一個字也是「' + X + '」的機率。', a: T(Fr.tex(A0)), h: hbA,
             p: { cn: cn, xi: xi, v: 0, ans: l3fp(A0) } };
  };

  /* ══ L3-14　比賽打到一半問「最後誰贏」：只看還沒打的局 ══ */
  function l3win(a, b, p) {
    if (a <= 0) return F(1);
    if (b <= 0) return F(0);
    return Fr.add(Fr.mul(p, l3win(a - 1, b, p)), Fr.mul(Fr.cp(p), l3win(a, b - 1, p)));
  }
  var L314P = [F(1, 2), F(1, 3), F(2, 3), F(1, 4), F(3, 4), F(2, 5), F(3, 5), F(1, 5), F(4, 5), F(1, 6), F(5, 6), F(3, 10), F(7, 10)];
  L3.matchRemain = function (r) {
    r();
    var W = r.pick([3, 3, 4]), p = r.pick(L314P), v = r.int(0, 2);
    var x, y, tr = 0;
    /* v=2 要問「條件下全勝」⟹ 對手還需 ≥2 勝，否則那個條件機率恆為 1 */
    do { x = r.int(0, W - 1); y = r.int(0, W - 1); tr++; } while ((x + y < 1 || (W - x) + (W - y) > 6 || (v === 2 && y > W - 2)) && tr < 300);
    if (x + y < 1 || (v === 2 && y > W - 2)) { x = W - 1; y = 0; }
    var nm = r.pick([['小成', '小功'], ['甲', '乙'], ['小文', '阿遠'], ['紅隊', '藍隊']]);
    var a = W - x, b = W - y;
    var PA = l3win(a, b, p), PB = Fr.sub(F(1), PA), sweep = Fr.pow(p, a), cond = Fr.div(sweep, PA);
    var done = (x + y === 1)
      ? '已知第 ' + T(1) + ' 局由' + (x === 0 ? nm[1] : nm[0]) + '獲勝'
      : (x === 0 || y === 0)
        ? '已知前 ' + T(x + y) + ' 局都由' + (x === 0 ? nm[1] : nm[0]) + '獲勝'
        : '已知前 ' + T(x + y) + ' 局中' + nm[0] + '勝 ' + T(x) + ' 局、' + nm[1] + '勝 ' + T(y) + ' 局';
    var setup = nm[0] + '與' + nm[1] + '比賽，先勝 ' + T(W) + ' 局者獲勝。各局勝負互相獨立，且' + nm[0] + '每一局獲勝的機率為 ' + T(Fr.tex(p)) + '。' + done + '。';
    var hb = '已經打完的局完全不影響後面——各局獨立就是這個意思，千萬不要把前 ' + T(x + y) + ' 局的機率也乘進去。'
           + '接下來只看「還沒打的局」：' + nm[0] + '還要再勝 ' + T(a) + ' 局、' + nm[1] + '還要再勝 ' + T(b) + ' 局，'
           + '誰先達成誰獲勝，最多再打 ' + T(a + b - 1) + ' 局就一定分出勝負。'
           + (a === 1 ? '這裡' + nm[0] + '只差 ' + T(1) + ' 局，走反面最快：' + nm[1] + '要翻盤必須連贏 ' + T(b) + ' 局，機率 ' + T(l3pw(Fr.tex(Fr.cp(p)), b) + '=' + Fr.tex(Fr.pow(Fr.cp(p), b))) + '。'
                      : b === 1 ? '這裡' + nm[1] + '只差 ' + T(1) + ' 局，走反面比較快：' + nm[0] + '要獲勝就得把接下來的 ' + T(a) + ' 局全部拿下，機率 ' + T(l3pw(Fr.tex(p), a) + '=' + Fr.tex(Fr.pow(p, a))) + '。'
                                : '把「' + nm[0] + '再勝 ' + T(a) + ' 局」依「第幾局結束」拆成互斥的幾條路徑，或用遞迴一層一層往回算。');
    if (v === 1)
      return { q: setup + '求 ' + l3no(1) + '最後由' + nm[1] + '獲勝的機率　' + l3no(2) + '最後由' + nm[0] + '獲勝的機率。',
               a: l3jo([l3no(1) + T(Fr.tex(PB)), l3no(2) + T(Fr.tex(PA))]), h: hb,
               p: { W: W, x: x, y: y, p: l3fp(p), v: 1, ans: [l3fp(PB), l3fp(PA)] } };
    if (v === 2)
      return { q: setup + '求 ' + l3no(1) + '最後由' + nm[0] + '獲勝的機率　' + l3no(2) + '在「最後由' + nm[0] + '獲勝」的條件下，接下來 ' + T(a) + ' 局' + nm[0] + '全勝的機率。',
               a: l3jo([l3no(1) + T(Fr.tex(PA)), l3no(2) + T(Fr.tex(cond))]), h: hb,
               p: { W: W, x: x, y: y, p: l3fp(p), v: 2, ans: [l3fp(PA), l3fp(cond)] } };
    return { q: setup + '求最後由' + nm[0] + '獲勝的機率。', a: T(Fr.tex(PA)), h: hb,
             p: { W: W, x: x, y: y, p: l3fp(p), v: 0, ans: l3fp(PA) } };
  };

  /* ══ L3-15　兩階段關卡：把失敗拆成互斥的兩條路徑 ══ */
  var L315C = [
    { h: '某大學某學系的申請入學必須先通過初試，再進行複試', s1: '初試', s2: '複試', ok: '錄取', who: '小明' },
    { h: '某公司的徵才必須先通過筆試，再進行面試', s1: '筆試', s2: '面試', ok: '錄取', who: '小華' },
    { h: '某遊戲必須先通過第一關，才能挑戰第二關', s1: '第一關', s2: '第二關', ok: '破關', who: '小美' },
    { h: '某證照考試必須先通過學科測驗，再進行術科測驗', s1: '學科測驗', s2: '術科測驗', ok: '取得證照', who: '阿遠' },
    { h: '某社團的徵選必須先通過書面審查，再進行面談', s1: '書面審查', s2: '面談', ok: '入選', who: '小文' }
  ];
  var L315P = [F(1, 2), F(1, 3), F(2, 3), F(1, 4), F(3, 4), F(1, 5), F(2, 5), F(3, 5), F(4, 5), F(1, 6), F(5, 6), F(1, 8), F(3, 8), F(1, 7), F(2, 7), F(3, 10), F(7, 10), F(1, 9)];
  L3.twoStageFail = function (r) {
    r();
    var ct = r.pick(L315C), p1 = r.pick(L315P), p2 = r.pick(L315P), v = r.int(0, 2);
    var pass = Fr.mul(p1, p2), fail = Fr.sub(F(1), pass);
    var f2 = Fr.mul(p1, Fr.cp(p2)), f1 = Fr.cp(p1);
    var A2 = Fr.div(f2, fail), A1 = Fr.div(f1, fail);
    var setup = ct.h + '。已知' + ct.s1 + '的通過率為 ' + T(Fr.tex(p1)) + '，通過' + ct.s1 + '者的' + ct.s2 + '通過率為 ' + T(Fr.tex(p2)) + '。';
    var hb = '只有「' + ct.s1 + '過且' + ct.s2 + '也過」才叫' + ct.ok + '：' + T(Fr.tex(p1) + '\\times' + Fr.tex(p2) + '=' + Fr.tex(pass)) + ' ⟹ 沒有' + ct.ok + '的機率是 ' + T('1-' + Fr.tex(pass) + '=' + Fr.tex(fail)) + '。'
           + '沒有' + ct.ok + '可以拆成互斥的兩條路徑：「' + ct.s1 + '就沒過」' + T(Fr.tex(f1)) + ' 與「' + ct.s1 + '過了但' + ct.s2 + '沒過」' + T(Fr.tex(p1) + '\\times' + Fr.tex(Fr.cp(p2)) + '=' + Fr.tex(f2)) + '——'
           + ct.s1 + '就沒過的人根本沒進' + ct.s2 + '，不能算在' + ct.s2 + '失敗裡面。兩條路徑相加 ' + T(Fr.tex(f1) + '+' + Fr.tex(f2) + '=' + Fr.tex(fail)) + ' 剛好是全部的失敗，這就是最好的驗算。';
    if (v === 1)
      return { q: setup + '求 ' + l3no(1) + ct.who + ct.ok + '的機率　' + l3no(2) + '已知' + ct.who + '沒有' + ct.ok + '，' + ct.who + '是在' + ct.s2 + '失敗的機率。（化為最簡分數）',
               a: l3jo([l3no(1) + T(Fr.tex(pass)), l3no(2) + T(Fr.tex(A2))]), h: hb,
               p: { p1: l3fp(p1), p2: l3fp(p2), v: 1, ans: [l3fp(pass), l3fp(A2)] } };
    if (v === 2)
      return { q: setup + '已知' + ct.who + '沒有' + ct.ok + '，求' + ct.who + '是在' + ct.s1 + '就失敗的機率。（化為最簡分數）',
               a: T(Fr.tex(A1)), h: hb,
               p: { p1: l3fp(p1), p2: l3fp(p2), v: 2, ans: l3fp(A1) } };
    return { q: setup + '已知' + ct.who + '沒有' + ct.ok + '，求' + ct.who + '是在' + ct.s2 + '失敗的機率。（化為最簡分數）',
             a: T(Fr.tex(A2)), h: hb,
             p: { p1: l3fp(p1), p2: l3fp(p2), v: 0, ans: l3fp(A2) } };
  };

  var META_L3 = [['diceBothWays', '§2 骰子兩事件的雙向條件機率'], ['compCellCond', '§2 由 P(A′∩B′) 補格求條件機率'], ['indepEquation', '§3 獨立＋加法定理解方程'],
                 ['condRange', '§2 條件機率的最大最小'], ['condOneZero', '§2 條件機率等於 1 的判讀'], ['tableIndepPick', '§3 列聯表判獨立'],
                 ['kthDrawColor', '§2 不放回：第 k 次取到某色'], ['atLeastTwoTrials', '§3 重複試驗：至少兩次成功'], ['exactlyOneHit', '§3 獨立＋恰一人成功'],
                 ['bayesTwoBranch', '§4 兩分支的貝氏'], ['bayesUnknownRate', '§4 貝氏反求未知的不良率'], ['bayesThreeBags', '§4 三袋（先選容器再取球）'],
                 ['permMultiCond', '§5 不盡相異物排列的條件機率'], ['matchRemain', '§3 比賽剩餘局數'], ['twoStageFail', '§4 兩階段關卡']];
  /* 固定題 L3-n 對應的類似題型 */
  var L3_FIX = { 'L3-1': 'diceBothWays', 'L3-2': 'compCellCond', 'L3-3': 'indepEquation', 'L3-4': 'condRange', 'L3-5': 'condOneZero',
                 'L3-6': 'tableIndepPick', 'L3-7': 'kthDrawColor', 'L3-8': 'atLeastTwoTrials', 'L3-9': 'exactlyOneHit', 'L3-10': 'bayesTwoBranch',
                 'L3-11': 'bayesUnknownRate', 'L3-12': 'bayesThreeBags', 'L3-13': 'permMultiCond', 'L3-14': 'matchRemain', 'L3-15': 'twoStageFail' };

  /* ══════════════════════════════════════════════════════════
     L0　章首先備診斷（5 型）：古典機率（兩顆骰子）、組合數取球、餘事件「至少一個」、和事件的加法（以上高一下 ch2）、從兩類人數讀比例（國中）
     ══════════════════════════════════════════════════════════ */
  var L0 = {};
  function l0C(n, k) { if (k < 0 || k > n) return 0; var v = 1; for (var i = 1; i <= k; i++) v = v * (n - k + i) / i; return Math.round(v); }
  function l0fr(n, d) { return Fr.tex(F(n, d)); }
  function l0a(f) { return [f.n, f.d]; }
  L0.diceSum = function (r) {
    r();
    var v = r.int(0, 6), s, cnt = 0, i, j, what, why;
    if (v === 0) { s = r.int(3, 11); for (i = 1; i <= 6; i++) for (j = 1; j <= 6; j++) if (i + j === s) cnt++; what = '點數和為 ' + T(String(s)); why = '和為 $' + s + '$ 的有序數對'; }
    else if (v === 1) { s = r.int(8, 11); for (i = 1; i <= 6; i++) for (j = 1; j <= 6; j++) if (i + j >= s) cnt++; what = '點數和不小於 ' + T(String(s)); why = '和為 $' + s + '$ 到 $12$ 的有序數對'; }
    else if (v === 3) { s = r.int(2, 6); for (i = 1; i <= 6; i++) for (j = 1; j <= 6; j++) if (Math.max(i, j) === s) cnt++; what = '兩顆點數中較大的是 ' + T(String(s)) + '（兩顆相同時就是那個點數）'; why = '兩顆都不超過 $' + s + '$、而且至少一顆是 $' + s + '$ 的有序數對'; }
    else if (v === 4) { s = r.int(2, 6); for (i = 1; i <= 6; i++) for (j = 1; j <= 6; j++) if ((i * j) % s === 0) cnt++; what = '點數乘積是 ' + T(String(s)) + ' 的倍數'; why = '乘積是 $' + s + '$ 的倍數的有序數對（或改數「不是倍數」的再用 $36$ 去減）'; }
    else if (v === 5) { s = r.int(3, 6); for (i = 1; i <= 6; i++) for (j = 1; j <= 6; j++) if (i + j <= s) cnt++; what = '點數和不大於 ' + T(String(s)); why = '和為 $2$ 到 $' + s + '$ 的有序數對'; }
    else if (v === 6) { s = r.int(1, 6); for (i = 1; i <= 6; i++) for (j = 1; j <= 6; j++) if (i === s || j === s) cnt++; what = '至少有一顆出現 ' + T(String(s)) + ' 點'; why = '含有 $' + s + '$ 點的有序數對（$(' + s + ',' + s + ')$ 只能算一次；或用「兩顆都不是 $' + s + '$ 點」的 $5\\times5$ 格去減）'; }
    else { s = r.int(1, 4); for (i = 1; i <= 6; i++) for (j = 1; j <= 6; j++) if (Math.abs(i - j) === s) cnt++; what = '兩顆點數相差 ' + T(String(s)); why = '差為 $' + s + '$ 的有序數對（$(a,b)$ 與 $(b,a)$ 是不同的結果）'; }
    return { q: '同時擲兩顆公正骰子，求' + what + ' 的機率。', a: T(l0fr(cnt, 36)),
             h: '樣本空間是 $6\\times6=36$ 個<b>有序</b>數對，每個機率相同；把' + why + '一個一個列出來，數完再除以 $36$ 並約分。這一章的「已知…的條件下」只是把這 $36$ 格先劃掉一部分再數。',
             p: { v: v, s: s, ans: l0a(F(cnt, 36)) } };
  };
  L0.drawComb = function (r) {
    r();
    var a = r.int(2, 6), b = r.int(2, 6), k = r.int(2, 3), j = r.int(1, Math.min(k, a));
    if (k - j > b) j = k - b;
    var num = l0C(a, j) * l0C(b, k - j), den = l0C(a + b, k);
    return { q: '袋中有 ' + T(String(a)) + ' 顆紅球、' + T(String(b)) + ' 顆白球，一次取出 ' + T(String(k)) + ' 顆。求恰有 ' + T(String(j)) + ' 顆紅球的機率。', a: T(l0fr(num, den)),
             h: '分母是從 $' + (a + b) + '$ 顆取 $' + k + '$ 顆的取法 $C^{' + (a + b) + '}_{' + k + '}=' + den + '$；分子是「紅球取 $' + j + '$ 顆」乘以「白球取 $' + (k - j) + '$ 顆」：$C^{' + a + '}_{' + j + '}\\times C^{' + b + '}_{' + (k - j) + '}$。這一章的「不放回連抽」會用乘法公式一顆一顆算，兩種算法答案一定相同。',
             p: { a: a, b: b, k: k, j: j, ans: l0a(F(num, den)) } };
  };
  L0.atLeastOne = function (r) {
    r();
    var v = r.int(0, 1);
    if (v === 0) { var n = r.int(2, 6), den0 = Math.pow(2, n);
      return { q: '同時擲 ' + T(String(n)) + ' 枚公正硬幣，求至少出現一個正面的機率。', a: T(l0fr(den0 - 1, den0)),
               h: '「至少一個」先算反面：全部都是反面只有 $1$ 種，樣本空間共 $2^{' + n + '}=' + den0 + '$ 種 ⟹ 用 $1$ 去減。這一章的「至少命中一次」也是同一招：$1-(\\text{每次都沒中})$。',
               p: { v: v, n: n, ans: l0a(F(den0 - 1, den0)) } }; }
    var a = r.int(2, 5), b = r.int(3, 6), k = r.int(2, 3), den = l0C(a + b, k), none = l0C(b, k);
    return { q: '袋中有 ' + T(String(a)) + ' 顆紅球、' + T(String(b)) + ' 顆白球，一次取出 ' + T(String(k)) + ' 顆。求至少取到一顆紅球的機率。', a: T(l0fr(den - none, den)),
             h: '「至少一顆紅球」的反面是「全部是白球」：$\\dfrac{C^{' + b + '}_{' + k + '}}{C^{' + (a + b) + '}_{' + k + '}}=\\dfrac{' + none + '}{' + den + '}' + (gcd(none, den) > 1 ? '=' + l0fr(none, den) : '') + '$，再用 $1$ 去減。這一章的「至少命中一次」也是同一招。',
             p: { v: v, a: a, b: b, k: k, ans: l0a(F(den - none, den)) } };
  };
  L0.unionAdd = function (r) {
    r();
    var N = r.pick([10, 12, 15, 20, 24, 30]), nAB = r.int(1, Math.floor(N / 5)), nA = nAB + r.int(1, Math.floor(N / 3)), nB = nAB + r.int(1, Math.floor(N / 3));
    while (nA + nB - nAB >= N) nB--;
    if (nB <= nAB) nB = nAB + 1;
    var nU = nA + nB - nAB;
    return { q: '設 ' + T('P(A)=' + l0fr(nA, N)) + '、' + T('P(B)=' + l0fr(nB, N)) + '、' + T('P(A\\cap B)=' + l0fr(nAB, N)) + '。求 (1) ' + T('P(A\\cup B)') + '　(2) ' + T('A') + '、' + T('B') + ' 都不發生的機率。',
             a: '(1) ' + T(l0fr(nU, N)) + '　(2) ' + T(l0fr(N - nU, N)),
             h: '(1) $P(A\\cup B)=P(A)+P(B)-P(A\\cap B)$，重疊的部分被加了兩次要扣掉一次：通分成分母 $' + N + '$ 後是 $\\dfrac{' + nA + '+' + nB + '-' + nAB + '}{' + N + '}$。(2)「都不發生」是「至少一個發生」的反面：$1-P(A\\cup B)$。這一章的條件機率 $P(A\\mid B)=\\dfrac{P(A\\cap B)}{P(B)}$ 用的就是這張文氏圖。',
             p: { N: N, nA: nA, nB: nB, nAB: nAB, ans: [l0a(F(nU, N)), l0a(F(N - nU, N))] } };
  };
  L0.tableRead = function (r) {
    r();
    var boys = r.int(12, 24), girls = r.int(12, 24), bl = r.int(3, boys - 3), gl = r.int(3, girls - 3);
    var sub = r.pick([['喜歡數學', '數學'], ['戴眼鏡', '眼鏡'], ['搭公車上學', '公車'], ['參加社團', '社團']]);
    return { q: '某班男生 ' + T(String(boys)) + ' 人中有 ' + T(String(bl)) + ' 人' + sub[0] + '，女生 ' + T(String(girls)) + ' 人中有 ' + T(String(gl)) + ' 人' + sub[0] + '。求 (1) 全班' + sub[0] + '的比例　(2) ' + sub[0] + '的人當中，男生所占的比例。',
             a: '(1) ' + T(l0fr(bl + gl, boys + girls)) + '　(2) ' + T(l0fr(bl, bl + gl)),
             h: '兩個比例的<b>分母不同</b>：(1) 的分母是全班 $' + boys + '+' + girls + '$ 人；(2) 的分母換成「' + sub[0] + '的 $' + bl + '+' + gl + '$ 人」，分子是其中的男生。這一章的條件機率，就是這種「分母換成已知的那一群」的比例。',
             p: { boys: boys, girls: girls, bl: bl, gl: gl, ans: [l0a(F(bl + gl, boys + girls)), l0a(F(bl, bl + gl))] } };
  };
  var META_L0 = [['diceSum', '兩顆骰子的古典機率'], ['drawComb', '組合數：取球的機率'], ['atLeastOne', '餘事件：至少一個'], ['unionAdd', '和事件的加法'], ['tableRead', '從兩類人數讀比例']];
  /* 先備題型 → 該去哪裡複習 */
  var PREREQ = {
    diceSum: { txt: '古典機率：樣本空間與有序數對（高一下第二章 排列組合與機率）——條件機率只是把樣本空間先縮小再數', link: '../g10b-ch02/practice.html#L1' },
    drawComb: { txt: '用組合數算取球的機率（高一下第二章 排列組合與機率）——不放回連抽可以用它來核對乘法公式', link: '../g10b-ch02/practice.html#L1' },
    atLeastOne: { txt: '餘事件與「至少一個」（高一下第二章 排列組合與機率）——本章「至少命中一次」是同一招', link: '../g10b-ch02/practice.html#L1' },
    unionAdd: { txt: '和事件的加法與文氏圖（高一下第二章 排列組合與機率）——條件機率公式的分子、分母都從文氏圖讀', link: '../g10b-ch02/practice.html#L1' },
    tableRead: { txt: '從分類人數讀比例（國中的統計圖表）——「分母換成已知的那一群」就是條件機率', link: null }
  };
  /* ══════════════════════════════════════════════════════════
     對照題：同一型抽兩題，只差一個關鍵特徵（f 由 p 算出；keep 的欄位要相同）
     ══════════════════════════════════════════════════════════ */
  var CONTRAST = {
    'L1.drawBalls': { f: function (p) { return p.back; }, keep: ['a', 'b'], why: '同一箱球，<b>放回</b>時每次抽的分母、分子都不變，兩次互相獨立，所以「已知第一次是某色」對第二次沒有影響；<b>不放回</b>時第二次的分母少 $1$、同色球也少 $1$，條件機率就變了。但不管放不放回，「第二次抽到某色」的機率都和第一次一樣（對稱性）——比較兩題的第 (3) 小題就看得出來。' },
    'L1.indepCheck': { f: function (p) { return p.indep; }, why: '判斷獨立只有一個標準：把 $P(A\\cap B)$ 與 $P(A)\\,P(B)$ <b>都算出來比</b>。相等 ⟹ 獨立；不相等 ⟹ 不獨立。不要用感覺判斷，也不要和「互斥」（$P(A\\cap B)=0$）混在一起：兩個機率都不為 $0$ 的互斥事件，$P(A)P(B)\\gt0=P(A\\cap B)$，一定不獨立。' },
    'L1.indepTable': { f: function (p) { return p.indep; }, why: '列聯表判獨立：看兩列的條件機率是否相同，等價於<b>交叉相乘是否相等</b>（$ad=bc$）。相等 ⟹「知道是哪一列」不會改變落在哪一行的機率 ⟹ 獨立；差一點點也是不獨立。' },
    'L2.condDice2': { f: function (p) { return p.indep; }, why: '兩顆骰子的兩個事件獨不獨立，<b>和事件「看起來有沒有關係」無關</b>，只看 $P(A\\cap B)$ 是否等於 $P(A)P(B)$。在 $6\\times6$ 的表格上把 $A$、$B$ 各圈出來，數三個格子數 $n(A)$、$n(B)$、$n(A\\cap B)$，檢查 $36\\,n(A\\cap B)=n(A)\\,n(B)$ 就好。' },
    'L1.atLeastOne': { f: function (p) { return p.n; }, keep: ['p'], why: '同樣的成功機率，<b>試的次數越多，「一次都沒成功」$(1-p)^n$ 就越小</b>，所以「至少一次」$1-(1-p)^n$ 越大、越接近 $1$（但永遠到不了 $1$）。下一步就是反過來問：要試幾次，這個機率才會超過某個門檻？' },
    'L1.bayesTwo': { f: function (p) { return String(p.w1); }, keep: ['r1', 'r2'], why: '兩題裡甲、乙兩台機器各自的不合格率都一樣，只有<b>產量比例</b>不同。貝氏定理的分子是「產量比例 $\\times$ 不合格率」這條路徑——產量佔得多的機器，即使不合格率較低，不合格品也可能多半來自它。所以反推原因時，<b>一開始的比例和條件機率一樣重要</b>。' },
    'L1.bayesScreen': { f: function (p) { return String(p.pv); }, keep: ['s', 't'], why: '同一種檢驗（兩個準確率都一樣），只是<b>一開始的比例</b>不同。比例越低，「沒有的人」就越多，他們當中被誤判的人數會蓋過真正有的人 ⟹ 「被驗出來的人裡真正有的比例」就越低。<b>檢驗結果要怎麼解讀，取決於一開始的比例</b>——這是本章最反直覺的結論。' },
    'L1.bayesTable': { f: function (p) { return String(p.pv); }, keep: ['s', 'u'], why: '把機率換成人數填進四格表：檢驗的兩個比率不變，<b>一開始的比例一改，四格的人數就整個重新分配</b>。比例低時「沒有卻被驗出來」那一格的人數會比「有且被驗出來」還多，第 (3) 小題的答案就掉下來了。' },
    'L2.bayesRetest': { f: function (p) { return String(p.pv); }, keep: ['s', 'u'], why: '複檢就是把第一次算出來的機率當成第二次的起點，再做一次同樣的計算。<b>一開始的比例越低，第一次驗出來之後的機率也越低，就越需要第二次檢驗</b>；連續兩次都被驗出來，機率才會明顯拉高。' },
    'L2.symDraw': { f: function (p) { return p.k; }, keep: ['w', 'l'], why: '同一袋球，<b>不論排第幾位抽，抽到的機率都一樣</b>（第 (1) 小題兩題答案相同）：把所有球隨機排成一列，每個位置是某色的機率都是那個顏色所佔的比例。順序只有在「已經知道前面的人抽到什麼」之後才有影響。' },
    'L2.repeatCond': { f: function (p) { return p.m; }, keep: ['n', 'p'], why: '「已知前 $m$ 次都成功」之後，前 $m$ 次就不再是隨機的了：問題變成<b>剩下的 $n-m$ 次裡要恰好再成功 $k-m$ 次</b>（因為各次獨立，前面的結果不影響後面）。已知的次數不同，剩下要算的重複試驗就不同。' }
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

  return { makeRng: makeRng, L0: L0, L1: L1, L2: L2, L3: L3, L3_FIX: L3_FIX, META: META, PREREQ: PREREQ, CONTRAST: CONTRAST, contrastPair: contrastPair, _util: { gcd: gcd, F: F, Fr: Fr, nCr: nCr, binP: binP, evalTarget: evalTarget } };
}));
