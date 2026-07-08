/* Melvin demo frontend.  Plain JS, no build step.
 *
 * Talks to the demo server's JSON API (/api/examples, /api/verify, /api/run).
 * Permalinks encode the program into the URL fragment (#code=…), deflated via
 * the native CompressionStream when available, plain base64url otherwise.
 */
(function () {
  "use strict";

  var $ = function (sel) { return document.querySelector(sel); };

  // ------------------------------------------------------------- state

  var editor = null;          // CodeMirror instance
  var currentName = "untitled.mml";
  var modified = false;
  var busy = false;
  var marks = [];             // active squiggle marks
  var lastBoogie = "";
  var statusTimer = null;

  // ------------------------------------------------------------- theme

  function preferredTheme() {
    var saved = localStorage.getItem("melvin-theme");
    if (saved) return saved;
    return window.matchMedia("(prefers-color-scheme: dark)").matches ? "dark" : "light";
  }

  function applyTheme(theme) {
    document.documentElement.setAttribute("data-theme", theme);
    if (editor) editor.setOption("theme", theme === "dark" ? "material-darker" : "default");
    localStorage.setItem("melvin-theme", theme);
  }

  // ------------------------------------------------------------- editor

  function initEditor() {
    editor = CodeMirror.fromTextArea($("#editor"), {
      mode: "mml",
      lineNumbers: true,
      matchBrackets: true,
      indentUnit: 2,
      tabSize: 2,
      gutters: ["CodeMirror-linenumbers", "melvin-movers", "melvin-errors"],
    });
    editor.setOption("theme",
      document.documentElement.getAttribute("data-theme") === "dark"
        ? "material-darker" : "default");
    var savedFont = localStorage.getItem("melvin-font");
    if (savedFont) setFontSize(savedFont);
    editor.on("change", function () {
      if (!modified) { modified = true; $("#modified-dot").hidden = false; }
      clearAnnotations();
    });
  }

  function setFontSize(px) {
    document.querySelector(".CodeMirror").style.fontSize = px;
    localStorage.setItem("melvin-font", px);
    editor.refresh();
  }

  function clearAnnotations() {
    marks.forEach(function (m) { m.clear(); });
    marks = [];
    editor.clearGutter("melvin-errors");
    editor.clearGutter("melvin-movers");
  }

  var MOVER_NAMES = {
    B: "both-mover", R: "right-mover", L: "left-mover",
    N: "non-mover", Y: "yield", E: "error (no mover applies)",
  };

  function annotateMovers(movers) {
    editor.clearGutter("melvin-movers");
    (movers || []).forEach(function (m) {
      var chip = document.createElement("div");
      chip.className = "mover-chip mover-" + m.effect;
      chip.textContent = m.effect;
      chip.title = MOVER_NAMES[m.effect] || m.effect;
      editor.setGutterMarker(m.line - 1, "melvin-movers", chip);
    });
  }

  function annotate(diags) {
    clearAnnotations();
    diags.forEach(function (d) {
      if (d.line == null) return;
      var from = { line: d.line - 1, ch: Math.max(0, (d.col || 1) - 1) };
      var to = { line: (d.end_line || d.line) - 1, ch: (d.end_col || (d.col || 1) + 1) - 1 };
      if (to.line === from.line && to.ch <= from.ch) {
        var text = editor.getLine(from.line) || "";
        to.ch = Math.min(text.length, from.ch + 1);
        if (to.ch <= from.ch) { from.ch = Math.max(0, text.length - 1); to.ch = text.length; }
      }
      marks.push(editor.markText(from, to, { className: "mml-squiggle", title: d.message }));
      var marker = document.createElement("div");
      marker.className = "gutter-error";
      marker.title = d.message;
      marker.textContent = "●";
      editor.setGutterMarker(d.line - 1, "melvin-errors", marker);
    });
  }

  function jumpTo(d) {
    if (d.line == null) return;
    editor.setCursor({ line: d.line - 1, ch: Math.max(0, (d.col || 1) - 1) });
    editor.scrollIntoView(null, 120);
    editor.focus();
  }

  // ------------------------------------------------------------- menus

  function initMenus() {
    document.querySelectorAll(".menu-btn").forEach(function (btn) {
      btn.addEventListener("click", function (e) {
        e.stopPropagation();
        var menu = btn.parentElement;
        var wasOpen = menu.classList.contains("open");
        closeMenus();
        if (!wasOpen) menu.classList.add("open");
      });
    });
    document.addEventListener("click", closeMenus);
    document.querySelectorAll("[data-font]").forEach(function (b) {
      b.addEventListener("click", function () { setFontSize(b.dataset.font); });
    });
    $("#theme-toggle").addEventListener("click", function () {
      var cur = document.documentElement.getAttribute("data-theme");
      applyTheme(cur === "dark" ? "light" : "dark");
    });
  }

  function closeMenus() {
    document.querySelectorAll(".menu.open").forEach(function (m) {
      m.classList.remove("open");
    });
  }

  // ------------------------------------------------------------- examples

  function loadExamplesMenu() {
    fetch("api/examples").then(function (r) { return r.json(); }).then(function (list) {
      var menu = $("#examples-menu");
      menu.innerHTML = "";
      var lastGroup = null;
      list.forEach(function (ex) {
        if (ex.group !== lastGroup) {
          lastGroup = ex.group;
          var g = document.createElement("div");
          g.className = "menu-group";
          g.textContent = ex.group;
          menu.appendChild(g);
        }
        var b = document.createElement("button");
        b.className = "menu-item menu-example";
        b.innerHTML = "<b></b><small></small>";
        b.querySelector("b").textContent = ex.title;
        b.querySelector("small").textContent = ex.blurb;
        b.addEventListener("click", function () { loadExample(ex.name); });
        menu.appendChild(b);
      });
    }).catch(function () {
      $("#examples-menu").innerHTML = "<span class='menu-loading'>could not load examples</span>";
    });
  }

  function loadExample(name) {
    fetch("api/examples/" + encodeURIComponent(name))
      .then(function (r) {
        if (!r.ok) throw new Error("could not load " + name);
        return r.json();
      })
      .then(function (ex) {
        editor.setValue(ex.source);
        setFileName(ex.name);
        history.replaceState(null, "", "#example=" + encodeURIComponent(ex.name));
        resetOutput();
      })
      .catch(function (err) { showTransientStatus(String(err.message || err)); });
  }

  function setFileName(name) {
    currentName = name;
    $("#file-name").textContent = name;
    modified = false;
    $("#modified-dot").hidden = true;
  }

  function resetOutput() {
    clearAnnotations();
    $("#tab-output").innerHTML =
      "<div class='placeholder'>Press <b>Verify</b> to check this program, or <b>Run</b> to execute it.</div>";
    $("#boogie-text").textContent = "Verify a program to see the Boogie it generates.";
    $("#btn-download-bpl").disabled = true;
    lastBoogie = "";
    setStatus("");
  }

  // ------------------------------------------------------------- tabs

  function initTabs() {
    document.querySelectorAll(".tab").forEach(function (t) {
      t.addEventListener("click", function () { selectTab(t.dataset.tab); });
    });
  }

  function selectTab(name) {
    document.querySelectorAll(".tab").forEach(function (t) {
      t.classList.toggle("active", t.dataset.tab === name);
    });
    document.querySelectorAll(".tab-panel").forEach(function (p) {
      p.classList.toggle("active", p.id === "tab-" + name);
    });
  }

  // ------------------------------------------------------------- status

  function setStatus(html, spinning) {
    var el = $("#status");
    el.innerHTML = "";
    if (spinning) {
      var s = document.createElement("span");
      s.className = "spinner";
      el.appendChild(s);
    }
    var t = document.createElement("span");
    t.innerHTML = html;
    el.appendChild(t);
  }

  function startBusy(label) {
    busy = true;
    $("#btn-verify").disabled = true;
    $("#btn-run").disabled = true;
    var t0 = Date.now();
    setStatus(label + "&hellip;", true);
    statusTimer = setInterval(function () {
      setStatus(label + "&hellip; " + ((Date.now() - t0) / 1000).toFixed(1) + "s", true);
    }, 100);
  }

  function endBusy(badgeClass, badgeText) {
    busy = false;
    $("#btn-verify").disabled = false;
    $("#btn-run").disabled = false;
    clearInterval(statusTimer);
    setStatus(badgeText ? "<span class='badge " + badgeClass + "'>" + badgeText + "</span>" : "");
  }

  function showTransientStatus(msg) {
    setStatus(msg);
    setTimeout(function () { if (!busy) setStatus(""); }, 4000);
  }

  // ------------------------------------------------------------- verify

  function postJSON(path, body) {
    return fetch(path, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify(body),
    }).then(function (r) {
      return r.json().then(function (data) {
        if (!r.ok) {
          var msg = (data && data.detail) ? data.detail : ("server error (" + r.status + ")");
          throw new Error(msg);
        }
        return data;
      });
    });
  }

  function verify() {
    if (busy) return;
    startBusy("verifying");
    selectTab("output");
    postJSON("api/verify", { source: editor.getValue() })
      .then(renderVerify)
      .catch(function (err) {
        endBusy("bad", "error");
        renderFailure(String(err.message || err));
      });
  }

  function renderVerify(res) {
    var out = $("#tab-output");
    out.innerHTML = "";
    clearAnnotations();
    var secs = (res.elapsed_ms / 1000).toFixed(1) + "s" + (res.cached ? " (cached)" : "");

    lastBoogie = res.boogie || "";
    $("#boogie-text").textContent = lastBoogie || "(no Boogie was generated — the program failed in the front end)";
    $("#btn-download-bpl").disabled = !lastBoogie;

    var banner = document.createElement("div");
    if (res.status === "verified") {
      endBusy("ok", "verified");
      banner.className = "result-banner ok";
      banner.innerHTML = "&#10003; verified — " + res.verified +
        " Boogie proof obligation(s) discharged <small>" + secs + "</small>";
      out.appendChild(banner);
    } else if (res.status === "timeout") {
      endBusy("warn", "timeout");
      banner.className = "result-banner warn";
      banner.innerHTML = "&#9203; verification timed out <small>The demo server limits " +
        "each query; install Melvin locally for longer runs.</small>";
      out.appendChild(banner);
    } else {
      endBusy("bad", "rejected");
      banner.className = "result-banner bad";
      var n = res.diagnostics.length;
      banner.innerHTML = "&#10007; rejected — " + n + " diagnostic" + (n === 1 ? "" : "s") +
        " <small>" + secs + "</small>";
      out.appendChild(banner);
      out.appendChild(diagListEl(res.diagnostics));
      annotate(res.diagnostics);
    }
    annotateMovers(res.movers);
  }

  function diagListEl(diags) {
    var ul = document.createElement("ul");
    ul.className = "diag-list";
    diags.forEach(function (d) {
      var li = document.createElement("li");
      li.className = "diag";
      var loc = document.createElement("div");
      loc.className = "diag-loc";
      loc.textContent = d.line != null ? ("line " + d.line + ":" + d.col) : "program";
      var msg = document.createElement("div");
      msg.className = "diag-msg";
      msg.textContent = d.message;
      li.appendChild(loc);
      li.appendChild(msg);
      li.addEventListener("click", function () { jumpTo(d); });
      ul.appendChild(li);
    });
    return ul;
  }

  function renderFailure(message) {
    var out = $("#tab-output");
    out.innerHTML = "";
    var banner = document.createElement("div");
    banner.className = "result-banner bad";
    banner.textContent = message;
    out.appendChild(banner);
  }

  // ------------------------------------------------------------- run

  function run() {
    if (busy) return;
    startBusy("running");
    selectTab("trace");
    postJSON("api/run", { source: editor.getValue() })
      .then(renderRun)
      .catch(function (err) {
        endBusy("bad", "error");
        selectTab("output");
        renderFailure(String(err.message || err));
      });
  }

  function renderRun(res) {
    var out = $("#tab-trace");
    out.innerHTML = "";
    var banner = document.createElement("div");
    var secs = res.elapsed_ms != null ? ((res.elapsed_ms / 1000).toFixed(1) + "s") : "";

    if (res.status === "safe") {
      endBusy("ok", "safe");
      banner.className = "result-banner ok";
      banner.innerHTML = "&#10003; SAFE — no interleaving reaches <code>wrong</code> " +
        "<small>explored " + res.states + " states, exhaustive &middot; " + secs + "</small>";
      out.appendChild(banner);
    } else if (res.status === "unsafe") {
      endBusy("bad", "unsafe");
      banner.className = "result-banner bad";
      banner.innerHTML = "&#10007; UNSAFE — some interleaving reaches <code>wrong</code> " +
        "<small>explored " + res.states + " states &middot; " + secs + "</small>";
      out.appendChild(banner);
      if (res.trace) {
        var label = document.createElement("div");
        label.textContent = "One such interleaving:";
        out.appendChild(label);
        var ol = document.createElement("ol");
        ol.className = "trace-list";
        res.trace.forEach(function (step) {
          var li = document.createElement("li");
          if (step && typeof step === "object") {
            li.textContent = "t" + step.tid + "  line " + step.line + ":  " + step.source;
            li.dataset.line = step.line;
          } else {
            li.textContent = String(step);
          }
          ol.appendChild(li);
        });
        out.appendChild(ol);
      }
    } else if (res.status === "unknown") {
      endBusy("warn", "unknown");
      banner.className = "result-banner warn";
      banner.innerHTML = "&#8230; UNKNOWN — " +
        (res.message || "the search hit the demo's state/time bound");
      out.appendChild(banner);
    } else {
      endBusy("bad", "error");
      banner.className = "result-banner bad";
      banner.textContent = (res.diagnostics && res.diagnostics[0] && res.diagnostics[0].message) ||
        res.message || "the program could not be run";
      out.appendChild(banner);
      if (res.diagnostics && res.diagnostics.length) {
        out.appendChild(diagListEl(res.diagnostics));
        annotate(res.diagnostics);
      }
    }
  }

  // ------------------------------------------------------------- share

  function b64urlEncode(bytes) {
    var bin = "";
    for (var i = 0; i < bytes.length; i++) bin += String.fromCharCode(bytes[i]);
    return btoa(bin).replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/, "");
  }

  function b64urlDecode(str) {
    var b64 = str.replace(/-/g, "+").replace(/_/g, "/");
    while (b64.length % 4) b64 += "=";
    var bin = atob(b64);
    var bytes = new Uint8Array(bin.length);
    for (var i = 0; i < bin.length; i++) bytes[i] = bin.charCodeAt(i);
    return bytes;
  }

  function encodeSource(text) {
    var bytes = new TextEncoder().encode(text);
    if (typeof CompressionStream === "undefined") {
      return Promise.resolve("p" + b64urlEncode(bytes));
    }
    var stream = new Blob([bytes]).stream().pipeThrough(new CompressionStream("deflate-raw"));
    return new Response(stream).arrayBuffer().then(function (buf) {
      return "c" + b64urlEncode(new Uint8Array(buf));
    });
  }

  function decodeSource(enc) {
    var kind = enc[0];
    var data = b64urlDecode(enc.slice(1));
    if (kind === "c") {
      var stream = new Blob([data]).stream().pipeThrough(new DecompressionStream("deflate-raw"));
      return new Response(stream).text();
    }
    return Promise.resolve(new TextDecoder().decode(data));
  }

  function share() {
    encodeSource(editor.getValue()).then(function (enc) {
      var url = location.origin + location.pathname + "#code=" + enc;
      history.replaceState(null, "", "#code=" + enc);
      return navigator.clipboard.writeText(url);
    }).then(function () {
      showTransientStatus("link copied to clipboard");
    }).catch(function () {
      showTransientStatus("could not copy — the URL bar now holds the link");
    });
  }

  // ------------------------------------------------------------- boot

  function loadFromHash() {
    var h = location.hash.slice(1);
    if (h.indexOf("code=") === 0) {
      decodeSource(h.slice(5)).then(function (text) {
        editor.setValue(text);
        setFileName("shared.mml");
        resetOutput();
      }).catch(function () { loadExample("counter.mml"); });
      return;
    }
    if (h.indexOf("example=") === 0) {
      loadExample(decodeURIComponent(h.slice(8)));
      return;
    }
    loadExample("counter.mml");
  }

  function initSplitter() {
    var divider = $("#divider");
    var mainEl = $("#main");
    var dragging = false;
    divider.addEventListener("mousedown", function (e) {
      dragging = true;
      e.preventDefault();
      document.body.style.cursor = "col-resize";
    });
    window.addEventListener("mousemove", function (e) {
      if (!dragging) return;
      var rect = mainEl.getBoundingClientRect();
      var horizontal = window.innerWidth > 800;
      var frac = horizontal
        ? (e.clientX - rect.left) / rect.width
        : (e.clientY - rect.top) / rect.height;
      frac = Math.min(0.85, Math.max(0.15, frac));
      $("#editor-pane").style.flex = "0 0 " + (frac * 100) + "%";
      editor.refresh();
    });
    window.addEventListener("mouseup", function () {
      dragging = false;
      document.body.style.cursor = "";
    });
  }

  function initKeys() {
    document.addEventListener("keydown", function (e) {
      if ((e.metaKey || e.ctrlKey) && e.key === "Enter") {
        e.preventDefault();
        verify();
      }
    });
  }

  applyTheme(preferredTheme());
  initEditor();
  initMenus();
  initTabs();
  initSplitter();
  initKeys();
  loadExamplesMenu();
  loadFromHash();

  $("#btn-verify").addEventListener("click", verify);
  $("#btn-run").addEventListener("click", run);
  $("#btn-share").addEventListener("click", share);
  $("#btn-download-bpl").addEventListener("click", function () {
    var blob = new Blob([lastBoogie], { type: "text/plain" });
    var a = document.createElement("a");
    a.href = URL.createObjectURL(blob);
    a.download = currentName.replace(/\.mml$/, "") + ".bpl";
    a.click();
    URL.revokeObjectURL(a.href);
  });
})();
