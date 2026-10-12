/* 會員限定練習本的閘門（2026-10-08）
 *
 * 付費章的 practice.html 在公開站只剩一個殼：載入這支腳本，它會
 *   1. 用 Email 連結登入（同一個 Firebase 專案 niufutzu-jh，和道場、錯題本同帳號）
 *   2. 讀 entitlements/{email}.products.member 看有沒有授權（規則只放行本人）
 *   3. 有授權就讀 content/member/practice/{章} 的 { html, js }，把整頁換成真正的練習本
 *   沒授權的人連原始碼都拿不到（內容在 Firestore，規則在 Google 伺服器端檢查）。
 * 用法：<script src="../../assets/member-gate.js" data-ch="g10a-ch02" data-name="第二章 直線與圓"></script>
 */
(function () {
  "use strict";
  var SDK = "https://www.gstatic.com/firebasejs/11.6.0/";
  var EMAIL_KEY = "jhmath.reflex.email";
  /* LINE、Facebook 等 App 內瀏覽器：Google 不准在裡面登入 */
  var INAPP = /Line\/|FBAN|FBAV|Instagram|MicroMessenger/i.test(navigator.userAgent || "");
  var PRICING = "https://wrongbook.niufutzu.com/pricing";
  var me = document.currentScript, ch = me.getAttribute("data-ch"), name = me.getAttribute("data-name") || ch;
  var cfg = window.FIREBASE_CONFIG;

  function $(id) { return document.getElementById(id); }
  function esc(s) { return String(s == null ? "" : s).replace(/[&<>"']/g, function (c) { return { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]; }); }
  function box(html) { var g = $("gate"); if (g) g.innerHTML = html; }
  function friendly(e) {
    var m = (e && e.code) || (e && e.message) || String(e);
    if (/unauthorized-domain/.test(m)) return "這個網域還沒加進 Firebase 的已授權網域。";
    if (/permission-denied/.test(m)) return "沒有權限（授權可能已到期）。";
    if (/popup-closed-by-user|cancelled-popup-request/.test(m)) return "登入視窗被關掉了，再按一次就好。";
    if (/account-exists-with-different-credential/.test(m)) return "這個 Email 之前用「寄登入連結」登入過，請先用登入連結登入一次（之後兩種都能用）。";
    if (/network|Failed to fetch/.test(m)) return "網路連不上。";
    return m;
  }

  function run() {
    if (!cfg || !cfg.apiKey) { box('<div class="mg-card">這個網站沒有開啟雲端，無法載入會員內容。</div>'); return; }
    Promise.all([import(SDK + "firebase-app.js"), import(SDK + "firebase-auth.js"), import(SDK + "firebase-firestore.js")]).then(function (m) {
      var A = m[1], F = m[2], app = m[0].initializeApp(cfg), auth = A.getAuth(app), fs = F.getFirestore(app);
      A.setPersistence(auth, A.browserLocalPersistence).catch(function () {});

      function loginUI(msg) {
        var remembered = ""; try { remembered = localStorage.getItem(EMAIL_KEY) || ""; } catch (e) {}
        box('<div class="mg-card"><h2>🔒 ' + esc(name) + ' 練習本是會員內容</h2>' +
          '<p>已經是會員的話，用 Google 帳號或 Email 登入就能打開（不用密碼）。還不是會員？<a href="' + PRICING + '" target="_blank" rel="noopener">看方案</a>。</p>' +
          '<div class="mg-row"><input type="email" id="mgEmail" placeholder="你的 Email" value="' + esc(remembered) + '" autocomplete="email"><button type="button" id="mgSend">寄登入連結給我</button></div>' +
          (INAPP ? '<div class="mg-note">💡 要用 Google 登入，請點右上角「⋯」選「用瀏覽器開啟」（LINE／FB 裡面不能用 Google 登入）。</div>'
                 : '<div class="mg-row"><button type="button" id="mgGoogle">🔵 用 Google 帳號登入</button></div>') +
          '<div class="mg-note" id="mgMsg">' + esc(msg || "跟直覺道場、錯題本是同一個帳號。") + '</div></div>');
        if ($("mgGoogle")) $("mgGoogle").addEventListener("click", function () {
          var p = new A.GoogleAuthProvider(); p.setCustomParameters({ prompt: "select_account" });
          $("mgGoogle").disabled = true;
          A.signInWithPopup(auth, p).catch(function (e) {
            if (/popup-blocked|operation-not-supported-in-this-environment/.test((e && e.code) || "")) return A.signInWithRedirect(auth, p);
            $("mgGoogle").disabled = false; $("mgMsg").textContent = "Google 登入失敗：" + friendly(e);
          });
        });
        $("mgSend").addEventListener("click", function () {
          var email = ($("mgEmail").value || "").trim().toLowerCase();
          if (!/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(email)) { $("mgMsg").textContent = "Email 格式不對。"; return; }
          try { localStorage.setItem(EMAIL_KEY, email); } catch (e) {}
          $("mgSend").disabled = true; $("mgMsg").textContent = "寄送中…";
          A.sendSignInLinkToEmail(auth, email, { url: location.origin + location.pathname, handleCodeInApp: true })
            .then(function () { $("mgMsg").innerHTML = "📨 已寄到 <b>" + esc(email) + "</b>，打開那封信、點連結就會回到這頁並打開練習本。"; })
            .catch(function (e) { $("mgSend").disabled = false; $("mgMsg").textContent = "寄送失敗：" + friendly(e); });
        });
      }
      function noAccess(u, until) {
        box('<div class="mg-card"><h2>🔒 ' + esc(name) + ' 練習本是會員內容</h2>' +
          '<p>已登入 <b>' + esc(u.email) + '</b>，但這個帳號' + (until ? "的會員已於 " + esc(until) + " 到期" : "還不是會員") + '。</p>' +
          '<p><a class="mg-btn" href="' + PRICING + '" target="_blank" rel="noopener">看方案與付款方式</a> <button type="button" class="mg-ghost" id="mgOut">登出</button></p>' +
          '<div class="mg-note">開通後重新整理這頁即可；已付款但還沒開通，請聯絡老師。</div></div>');
        $("mgOut").addEventListener("click", function () { A.signOut(auth).then(function () { loginUI(); }); });
      }
      function render(doc) {
        var html = doc.html || "";
        if (doc.js) html = html.replace(/<script src="practice-gen\.js[^"]*"><\/script>/, function () { return "<script>" + doc.js.replace(/<\/script/gi, "<\\/script") + "</script>"; });
        document.open(); document.write(html); document.close();
      }
      function load(u) {
        box('<div class="mg-card">⏳ 載入會員內容…</div>');
        var email = (u.email || "").toLowerCase();
        F.getDoc(F.doc(fs, "entitlements", email)).then(function (s) {
          var mem = s.exists() ? ((s.data().products || {}).member || null) : null;
          var until = mem && mem.until && mem.until.toMillis ? mem.until.toMillis() : 0;
          if (!(until > Date.now())) { noAccess(u, until ? new Date(until).toLocaleDateString("zh-TW") : ""); return; }
          return F.getDoc(F.doc(fs, "content", "member", "practice", ch)).then(function (d) {
            if (!d.exists()) { box('<div class="mg-card">這一章的會員內容還沒上架，請聯絡老師。</div>'); return; }
            render(d.data());
          });
        }).catch(function (e) { box('<div class="mg-card">讀取失敗：' + esc(friendly(e)) + ' <button type="button" class="mg-ghost" onclick="location.reload()">重試</button></div>'); });
      }

      var pending = A.isSignInWithEmailLink(auth, location.href);
      if (pending) {
        var email = ""; try { email = localStorage.getItem(EMAIL_KEY) || ""; } catch (e) {}
        if (!email) email = prompt("請輸入你收到登入連結的那個 Email：") || "";
        email = email.trim().toLowerCase();
        A.signInWithEmailLink(auth, email, location.href).then(function () {
          try { localStorage.setItem(EMAIL_KEY, email); } catch (e) {}
          history.replaceState(null, "", location.origin + location.pathname);
        }).catch(function (e) { loginUI("登入失敗：" + friendly(e) + "（連結可能已過期，請重寄）"); });
      }
      A.onAuthStateChanged(auth, function (u) { if (u) load(u); else if (!pending) loginUI(); });
    }).catch(function (e) { box('<div class="mg-card">雲端啟動失敗：' + esc(e.message) + "</div>"); });
  }
  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", run); else run();
})();
