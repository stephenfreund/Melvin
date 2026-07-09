/* Snapshot: renders a store-JSON value
 *   { globals: {x: v, ...}, threads: {"1": {t: v, ...}}, objects: [...] }
 * as a DOM element.  Scalars become small tables; heap objects
 * ({id: "#1", class: "C", fields: {...}}) become Anchor-style box-and-arrow
 * diagrams, laid out with the vendored dagre and drawn in plain SVG.
 * Reference-valued fields are strings like "#2" (drawn as arrows) or "null".
 */
var Snapshot = (function () {
  "use strict";

  var ROW_H = 18, PAD = 6, CHAR_W = 7.2, TITLE_H = 20;

  function el(tag, cls, text) {
    var e = document.createElement(tag);
    if (cls) e.className = cls;
    if (text != null) e.textContent = text;
    return e;
  }

  function kvTable(title, kv) {
    var wrap = el("div", "snap-table");
    if (title) wrap.appendChild(el("div", "snap-table-title", title));
    var t = el("table");
    Object.keys(kv).forEach(function (k) {
      var tr = el("tr");
      tr.appendChild(el("td", "snap-k", k));
      tr.appendChild(el("td", "snap-v", String(kv[k])));
      t.appendChild(tr);
    });
    wrap.appendChild(t);
    return wrap;
  }

  function svgEl(tag, attrs) {
    var e = document.createElementNS("http://www.w3.org/2000/svg", tag);
    Object.keys(attrs || {}).forEach(function (k) { e.setAttribute(k, attrs[k]); });
    return e;
  }

  function objectDiagram(objects) {
    var g = new dagre.graphlib.Graph();
    g.setGraph({ rankdir: "LR", nodesep: 24, ranksep: 40, marginx: 8, marginy: 8 });
    g.setDefaultEdgeLabel(function () { return {}; });

    var byId = {};
    objects.forEach(function (o) { byId[o.id] = o; });

    objects.forEach(function (o) {
      var fields = Object.keys(o.fields || {});
      var widest = (o.class + " " + o.id).length;
      fields.forEach(function (f) {
        widest = Math.max(widest, (f + " = " + o.fields[f]).length);
      });
      g.setNode(o.id, {
        width: Math.max(90, widest * CHAR_W + 2 * PAD),
        height: TITLE_H + fields.length * ROW_H + PAD,
      });
    });
    objects.forEach(function (o) {
      Object.keys(o.fields || {}).forEach(function (f) {
        var v = String(o.fields[f]);
        if (v.charAt(0) === "#" && byId[v]) g.setEdge(o.id, v, { field: f });
      });
    });

    dagre.layout(g);

    var gr = g.graph();
    var svg = svgEl("svg", {
      class: "snap-heap",
      width: Math.ceil(gr.width || 10), height: Math.ceil(gr.height || 10),
      viewBox: "0 0 " + Math.ceil(gr.width || 10) + " " + Math.ceil(gr.height || 10),
    });
    var defs = svgEl("defs", {});
    var marker = svgEl("marker", {
      id: "snap-arrow", viewBox: "0 0 8 8", refX: 7, refY: 4,
      markerWidth: 7, markerHeight: 7, orient: "auto",
    });
    marker.appendChild(svgEl("path", { d: "M0,0 L8,4 L0,8 z", class: "snap-arrowhead" }));
    defs.appendChild(marker);
    svg.appendChild(defs);

    // edges under the boxes
    g.edges().forEach(function (e) {
      var pts = g.edge(e).points;
      var d = pts.map(function (p, i) {
        return (i === 0 ? "M" : "L") + p.x.toFixed(1) + "," + p.y.toFixed(1);
      }).join(" ");
      svg.appendChild(svgEl("path", {
        d: d, class: "snap-edge", "marker-end": "url(#snap-arrow)",
      }));
      var lbl = g.edge(e).field;
      if (lbl && pts.length) {
        var mid = pts[Math.floor(pts.length / 2)];
        var t = svgEl("text", { x: mid.x, y: mid.y - 3, class: "snap-edge-label" });
        t.textContent = lbl;
        svg.appendChild(t);
      }
    });

    objects.forEach(function (o) {
      var n = g.node(o.id);
      var x = n.x - n.width / 2, y = n.y - n.height / 2;
      var grp = svgEl("g", {});
      grp.appendChild(svgEl("rect", {
        x: x, y: y, width: n.width, height: n.height, rx: 4, class: "snap-box",
      }));
      grp.appendChild(svgEl("rect", {
        x: x, y: y, width: n.width, height: TITLE_H, rx: 4, class: "snap-box-title-bg",
      }));
      var title = svgEl("text", {
        x: x + PAD, y: y + TITLE_H - 6, class: "snap-box-title",
      });
      title.textContent = o.class + "  " + o.id;
      grp.appendChild(title);
      Object.keys(o.fields || {}).forEach(function (f, i) {
        var v = String(o.fields[f]);
        var row = svgEl("text", {
          x: x + PAD, y: y + TITLE_H + (i + 1) * ROW_H - 5, class: "snap-field",
        });
        row.textContent = (v.charAt(0) === "#" && byId[v]) ? f + " •" : f + " = " + v;
        grp.appendChild(row);
      });
      svg.appendChild(grp);
    });
    return svg;
  }

  /* store: store-JSON; opts.title: optional heading */
  function render(store, opts) {
    opts = opts || {};
    var root = el("div", "snapshot");
    if (opts.title) root.appendChild(el("div", "snap-title", opts.title));
    var scalars = el("div", "snap-scalars");
    var globals = (store && store.globals) || {};
    if (Object.keys(globals).length) scalars.appendChild(kvTable("globals", globals));
    var threads = (store && store.threads) || {};
    Object.keys(threads).sort().forEach(function (t) {
      if (Object.keys(threads[t]).length)
        scalars.appendChild(kvTable("t" + t + " locals", threads[t]));
    });
    if (scalars.childNodes.length) root.appendChild(scalars);
    var objects = (store && store.objects) || [];
    if (objects.length && typeof dagre !== "undefined") {
      root.appendChild(objectDiagram(objects));
    } else if (objects.length) {
      // dagre missing: fall back to tables
      objects.forEach(function (o) {
        root.appendChild(kvTable(o.class + " " + o.id, o.fields || {}));
      });
    }
    if (!root.childNodes.length ||
        (root.childNodes.length === 1 && opts.title)) {
      root.appendChild(el("div", "snap-empty", "(empty store)"));
    }
    return root;
  }

  return { render: render };
})();
