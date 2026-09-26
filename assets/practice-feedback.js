/* 分級練習本 — 學生回報（詳解看不懂／題目有問題）（2026-09-26 起）
 *
 * 掛在 assets/reflex-cloud.js 之後、頁面自己的產生器腳本（<script> 內建 .gcard／.fx 卡片）之後。
 * 14 本練習本共用同一個檔：只認兩種卡片，不改頁面既有的任何按鈕／邏輯。
 *   .gcard[data-key]  產生器題（L1／L2）：key 就是 data-key，例如 "L2.distPtLine"；
 *                      note 前綴帶上卡片目前的種子，例如 "[L2.distPtLine seed=12345]"，
 *                      老師靠 key+seed 就能重算出學生當時看到的那一題。
 *   .fx[id]           固定題與 L3 的類似題（L3～L5）：key 就是 fx 的 id，例如 "L3-6"、"L4-9"。
 *
 * 送出 { page:"practice/<章>", id, kind:"unclear"|"wrong", note? } 給 ReflexCloud.feedback()。
 * 沒有 ReflexCloud、雲端未設定、或送出失敗都只顯示友善訊息，不丟例外、不影響頁面其他功能。
 * 節流：同一頁 30 秒內最多送一次；同一題同一種只送一次（這次載入頁面期間）。
 */
(function () {
  "use strict";

  var C = window.ReflexCloud;
  if (!C) return;
  var m = (location.pathname.match(/(g\d\d[ab]-ch\d\d)/) || [])[1];
  if (!m) return;
  var PAGE = "practice/" + m;
  var SENT = {};          /* "id|kind" -> 1，只記這次載入頁面期間 */
  var lastSendAt = 0;

  function injectStyle() {
    if (document.getElementById("pf-style")) return;
    var css = ".pf-row{margin-top:8px;display:flex;gap:6px;flex-wrap:wrap;align-items:center}"
      + ".pf-row button{opacity:.85}"
      + ".pf-box{margin-top:6px;padding:8px 10px;border-radius:8px;font-size:.86rem;background:#fdf6ec;border:1px dashed #d8b56a;max-width:100%;box-sizing:border-box}"
      + ".pf-box .pf-lbl{margin-bottom:4px}"
      + ".pf-box input.pf-note{width:100%;max-width:320px;box-sizing:border-box;font:inherit;font-size:.85rem;padding:5px 8px;border:1px solid #cfcfcf;border-radius:6px;margin:2px 0 6px;display:block}"
      + ".pf-box .pf-btns{display:flex;gap:6px;flex-wrap:wrap;align-items:center}"
      + ".pf-done{color:#2e7d4f;font-weight:700}"
      + ".pf-err{color:#b3261e;font-size:.82rem}";
    var s = document.createElement("style"); s.id = "pf-style"; s.textContent = css;
    document.head.appendChild(s);
  }

  function clampNote(s, n) { s = String(s || ""); return s.length > n ? s.slice(0, n) : s; }

  /* 幫一張卡片（container）掛上「題目有問題」／「詳解看不懂」兩顆按鈕與展開的回報框 */
  function attachFeedback(container, id, getPrefix) {
    var row = document.createElement("div"); row.className = "pf-row";
    var wrongBtn = document.createElement("button"); wrongBtn.type = "button"; wrongBtn.textContent = "🚩 題目有問題";
    var unclearBtn = document.createElement("button"); unclearBtn.type = "button"; unclearBtn.textContent = "❓ 詳解看不懂"; unclearBtn.hidden = true;
    row.appendChild(wrongBtn); row.appendChild(unclearBtn);
    var box = document.createElement("div"); box.className = "pf-box"; box.hidden = true;
    container.appendChild(row); container.appendChild(box);

    function renderDone() {
      box.textContent = ""; box.hidden = false;
      var d = document.createElement("span"); d.className = "pf-done"; d.textContent = "✓ 已收到，謝謝！老師會看到這則回報。";
      box.appendChild(d);
    }

    function openBox(kind) {
      var sentKey = id + "|" + kind;
      if (SENT[sentKey]) { renderDone(); return; }
      box.textContent = ""; box.hidden = false;
      var lbl = document.createElement("div"); lbl.className = "pf-lbl";
      lbl.textContent = (kind === "unclear" ? "詳解看不懂" : "題目有問題") + "，想多說一句的話寫在這裡（可以不填）：";
      var inp = document.createElement("input"); inp.type = "text"; inp.className = "pf-note"; inp.maxLength = 200;
      inp.placeholder = kind === "unclear" ? "例：第二步怎麼來的？" : "例：選項好像打錯了";
      var btns = document.createElement("div"); btns.className = "pf-btns";
      var send = document.createElement("button"); send.type = "button"; send.textContent = "送出";
      var cancel = document.createElement("button"); cancel.type = "button"; cancel.textContent = "取消";
      var st = document.createElement("span"); st.className = "pf-err";
      btns.appendChild(send); btns.appendChild(cancel); btns.appendChild(st);
      box.appendChild(lbl); box.appendChild(inp); box.appendChild(btns);
      inp.focus();

      cancel.onclick = function () { box.hidden = true; };
      send.onclick = function () {
        if (!C.feedback) { st.textContent = "雲端還沒準備好，稍後再試。"; return; }
        var now = Date.now();
        if (now - lastSendAt < 30000) { st.textContent = "送出太頻繁了，請等一下再試。"; return; }
        send.disabled = true; cancel.disabled = true; st.textContent = "送出中…";
        var note = clampNote((inp.value || "").trim(), 200);
        var prefix = getPrefix ? getPrefix() : "";
        var full = prefix ? (note ? prefix + " " + note : prefix) : note;
        full = clampNote(full, 500);
        var doc = { page: PAGE, id: id, kind: kind };
        if (full) doc.note = full;
        C.feedback(doc).then(function () {
          lastSendAt = Date.now();
          SENT[sentKey] = 1;
          renderDone();
        }).catch(function (e) {
          send.disabled = false; cancel.disabled = false;
          st.textContent = "⚠ 送出失敗：" + ((e && e.message) || "請稍後再試");
        });
      };
    }

    wrongBtn.onclick = function () { openBox("wrong"); };
    unclearBtn.onclick = function () { openBox("unclear"); };
    return { reveal: function () { unclearBtn.hidden = false; } };
  }

  function wireGcards() {
    document.querySelectorAll(".gcard[data-key]").forEach(function (card) {
      var key = card.getAttribute("data-key"); if (!key) return;
      var ctrl = attachFeedback(card, key, function () {
        var seedEl = card.querySelector(".seed");
        var seed = seedEl ? seedEl.textContent.replace("#", "").trim() : "";
        return "[" + key + (seed ? " seed=" + seed : "") + "]";
      });
      var ans = card.querySelector(".ans"), steps = card.querySelector(".steps");
      if (ans) ans.addEventListener("click", function () { ctrl.reveal(); });
      if (steps) steps.addEventListener("click", function () { ctrl.reveal(); });
    });
  }

  function wireFx() {
    document.querySelectorAll(".fx[id]").forEach(function (fx) {
      var id = fx.id; if (!id) return;
      var ctrl = attachFeedback(fx, id, function () { return ""; });
      fx.querySelectorAll("button[data-t]").forEach(function (b) {
        b.addEventListener("click", function () { ctrl.reveal(); });
      });
    });
  }

  injectStyle();
  wireGcards();
  wireFx();
})();
