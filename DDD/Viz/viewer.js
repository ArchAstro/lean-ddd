/* DDD.Viz viewer: a class diagram of any domain DDD.Viz.emit describes, and an object
 * diagram of its scenarios, built from the real state after every step. No build step. */
(() => {
  "use strict";
  const { useState, useEffect, useMemo, useRef, useCallback } = React;
  const html = htm.bind(React.createElement);
  const SITE = window.DDD_SITE || { mode: "catalog", domains: [] };
  const NHUES = 8;
  const HEAD = 44, ROW = 19, PADB = 9, MAXROWS = 14, MINW = 156, MAXW = 360;
  const OHEAD = HEAD - 12;
  const reduced = () => window.matchMedia && matchMedia("(prefers-reduced-motion: reduce)").matches;

  /* ================= text ================= */
  const escHtml = (s) => s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
  function md(s) {
    if (!s) return "";
    return escHtml(s).split(/\n\s*\n/).map((p) => "<p>" + p.replace(/\n/g, " ")
      .replace(/\*\*(.+?)\*\*/g, "<b>$1</b>").replace(/`([^`]+)`/g, "<code>$1</code>") + "</p>").join("");
  }
  const plural = (n, w) => `${n} ${w}${n === 1 ? "" : "s"}`;
  function pretty(s, ns) {
    if (s == null) return "";
    let t = String(s).replace(/\s*\n\s*/g, " ");
    for (let i = 0; i < 3; i++) t = t.replace(/\{ (\w+) := ("(?:[^"\\]|\\.)*"|-?\d+) \}/g, "$2");
    if (ns) t = t.split(ns + ".").join("");
    return t.replace(/\bDDD\./g, "");
  }
  /** Split `f a "b c" [x, y] (g z)` into its head and its top-level arguments. */
  function splitArgs(s) {
    const out = []; let cur = "", depth = 0, q = false;
    for (let i = 0; i < s.length; i++) {
      const ch = s[i];
      if (q) { cur += ch; if (ch === "\\") cur += s[++i] || ""; else if (ch === '"') q = false; continue; }
      if (ch === '"') { q = true; cur += ch; continue; }
      if ("([{".includes(ch)) depth++;
      if (")]}".includes(ch)) depth--;
      if (ch === " " && depth === 0) { if (cur) out.push(cur); cur = ""; continue; }
      cur += ch;
    }
    if (cur) out.push(cur);
    return out;
  }
  const words = (s) => s.replace(/([a-z0-9])([A-Z])/g, "$1 $2").toLowerCase();
  /** Lean's `repr` of a value, as a person would write it. */
  const human = (t) => String(t).replace(/\b(?:[A-Z]\w*\.)+(\w+)/g, "$1").replace(/ := /g, ": ").replace(/\{ /g, "{").replace(/ \}/g, "}");
  const argName = (n) => n.replace(/_$/, "");
  /** Why a command was refused, in a sentence. */
  function reason(err, ns, M, targets) {
    const p = pretty(err, ns);
    if (!p || p.startsWith("Refused")) return "";
    if (/^Rejection\.policy/.test(p)) {
      const blocked = [...p.matchAll(/Disposition\.blocked "([^"]+)" \(?(?:OverrideClass\.)?(\w+)/g)].map((m) => `${m[1]} (${words(m[2])} may override)`);
      const facts = [...p.matchAll(/Disposition\.needsFact "([^"]+)" "([^"]+)"/g)].map((m) => `${m[1]} needs to know ${m[2]}`);
      return blocked.length ? `Blocked by policy: ${blocked.join("; ")}` : facts.length ? `Policy can't decide: ${facts.join("; ")}` : "Blocked by policy";
    }
    const imp = p.match(/^Rejection\.impossible \(?((?:\w+\.)*\w+)(.*?)\)?$/);
    if (imp && M) {
      const nm = imp[1].split(".").pop();
      for (const t of targets || []) { const a = M.agg(t), c = a && a.err && M.ctor(a.err, nm); if (c && c.doc) return plain(c.doc); }
    }
    if (imp) { const rest = human(imp[2]).trim(); return `The aggregate refuses: ${words(imp[1].split(".").pop())}${rest ? " (" + rest + ")" : ""}`; }
    const st = p.match(/^Rejection\.stale (\d+) (\d+)/);
    if (st) return `Stale: written against version ${st[1]}, but the log is at ${st[2]}`;
    return human(p);
  }
  /** The first sentence of a doc comment: its definition. */
  const first = (t) => { t = (t || "").replace(/\s+/g, " ").trim(); const m = t.match(/^.*?[.!?](?=\s|$)/); return m ? m[0] : t; };
  const plain = (t) => first(t).replace(/`([^`]*)`/g, "$1").replace(/\*\*?([^*]*)\*\*?/g, "$1");
  const unparen = (s) => (s.startsWith("(") && s.endsWith(")") ? s.slice(1, -1) : s);
  function Doc({ text, className }) {
    if (!text) return null;
    return html`<div className=${className || "doc"} dangerouslySetInnerHTML=${{ __html: md(text) }} />`;
  }

  /* ================= measuring ================= */
  const ctx2d = document.createElement("canvas").getContext("2d");
  const F_HEAD = '600 14px "Schibsted Grotesk", system-ui, sans-serif';
  const F_ROW = '11.5px "IBM Plex Mono", ui-monospace, monospace';
  const F_STEREO = '11.5px "Schibsted Grotesk", system-ui, sans-serif';
  const tw = (text, font) => { ctx2d.font = font; return ctx2d.measureText(text).width; };
  function clip(text, font, maxW) {
    text = String(text);
    if (tw(text, font) <= maxW) return text;
    let lo = 0, hi = text.length;
    while (lo < hi) { const m = (lo + hi + 1) >> 1; if (tw(text.slice(0, m) + "…", font) <= maxW) lo = m; else hi = m - 1; }
    return text.slice(0, lo) + "…";
  }

  /* ================= the model ================= */
  function indexModel(d) {
    const types = new Map(d.types.map((t) => [t.id, t]));
    const aggs = d.aggregates;
    const aggIdx = new Map(aggs.map((a, i) => [a.id, i]));
    const hue = (id) => (aggIdx.has(id) ? `var(--h${aggIdx.get(id) % NHUES})` : "var(--muted)");
    const contexts = d.contexts || [];
    const ctxOf = new Map();
    for (const c of contexts) for (const a of c.aggregates) ctxOf.set(a, c.id);
    const role = new Map();
    for (const a of aggs) {
      role.set(a.state, { agg: a.id, role: "root" }); role.set(a.cmd, { agg: a.id, role: "cmd" });
      role.set(a.evt, { agg: a.id, role: "evt" }); if (a.err) role.set(a.err, { agg: a.id, role: "err" });
    }
    /* Where each type lives: inside one aggregate, inside one bounded context, or shared. */
    const place = new Map();
    for (const t of d.types) {
      const r = role.get(t.id);
      if (r) { place.set(t.id, { level: "agg", id: r.agg }); continue; }
      if (t.kind === "dto") { place.set(t.id, { level: "sys", id: t.system || "" }); continue; }
      const owners = t.owners || [];
      if (owners.length === 1) { place.set(t.id, { level: "agg", id: owners[0] }); continue; }
      const cs = new Set(owners.map((o) => ctxOf.get(o) || "solo:" + o));
      const only = [...cs][0];
      if (owners.length > 1 && cs.size === 1 && !only.startsWith("solo:")) place.set(t.id, { level: "ctx", id: only });
      else place.set(t.id, { level: "shared" });
    }
    const kind = (t) => {
      if (role.get(t.id) && role.get(t.id).role === "root") return "aggregate";
      if (t.kind === "value" && fields(t).some((f) => f.name === "id")) return "entity";
      return t.kind;
    };
    /* Fields, with a parent structure's fields in place of `toParent`. */
    const effCache = new Map();
    function fields(t) {
      if (!t || !t.fields) return [];
      if (effCache.has(t.id)) return effCache.get(t.id);
      effCache.set(t.id, []);
      const ext = new Map((t.edges || []).filter((e) => e.kind === "extends").map((e) => [e.label, e.to]));
      const out = [];
      for (const f of t.fields) {
        if (ext.has(f.name) && types.has(ext.get(f.name))) out.push(...fields(types.get(ext.get(f.name))).map((x) => ({ ...x, from: types.get(ext.get(f.name)).name })));
        else out.push(f);
      }
      effCache.set(t.id, out);
      return out;
    }
    /** The one domain type a field holds (`T`, `Option T`, `List T`), if it holds one. */
    function target(f) {
      let s = (f.type || "").trim(), many = false, opt = false;
      for (;;) {
        s = unparen(s.trim());
        const m = s.match(/^(List|Array|Option)\s+(.*)$/);
        if (!m) break;
        if (m[1] === "Option") opt = true; else many = true;
        s = m[2];
      }
      const t = (f.refs || []).map((r) => types.get(r)).find((x) => x && x.name === s);
      return t ? { id: t.id, many, opt } : null;
    }
    /* An identifier type names the entity whose `id` it is. */
    const identifies = new Map();
    for (const t of d.types) for (const f of fields(t)) if (f.name === "id") {
      const g = target(f);
      if (g && types.get(g.id).kind === "identifier" && !identifies.has(g.id)) identifies.set(g.id, t.id);
    }
    const typeHue = (t) => { const p = t && place.get(t.id); return p && p.level === "agg" ? hue(p.id) : "var(--muted)"; };
    const kindOfId = (id) => (types.has(id) ? kind(types.get(id)) : null);
    const byPrefix = (raw, key) => {
      let best = null;
      for (const a of aggs) if (raw.startsWith(a[key] + ".") && (!best || a[key].length > best[key].length)) best = a;
      return best;
    };
    const ctor = (typeId, name) => ((types.get(typeId) || {}).ctors || []).find((c) => c.name === name);
    const systems = d.systems || [], ports = d.ports || [], services = d.services || [];
    return { systems, ports, services, system: (id) => systems.find((x) => x.id === id), port: (id) => ports.find((x) => x.id === id),
      service: (id) => services.find((x) => x.id === id), kindOfId, d, ns: d.ns, types, aggs, contexts, ctxOf, hue, typeHue, place, role, kind, fields, target, identifies, byPrefix, ctor,
      agg: (id) => aggs.find((a) => a.id === id), proc: (id) => d.processes.find((p) => p.id === id) };
  }

  const KIND_N = { aggregate: ["aggregate root", "aggregate roots"], entity: ["entity", "entities"], value: ["value object", "value objects"],
    identifier: ["identifier", "identifiers"], enum: ["enumeration", "enumerations"], choice: ["choice type", "choice types"],
    command: ["command type", "command types"], event: ["event type", "event types"], rejection: ["rejection type", "rejection types"], dto: ["DTO", "DTOs"] };
  const STEREO = { aggregate: "aggregate root", entity: "entity", value: "value object", identifier: "identifier", enum: "enumeration",
    choice: "choice", command: "commands", event: "events", rejection: "rejections", process: "process", dto: "DTO", service: "application service", acl: "anti-corruption layer", system: "external system" };

  /* ================= frames ================= */
  /** Bounded contexts holding aggregate boundaries; a shared kernel; the processes. */
  function containers(M, withProcs) {
    const cs = [];
    for (const c of M.contexts) cs.push({ id: "ctx:" + c.id, parent: null, kind: "context", label: c.title, sub: "bounded context" });
    for (const a of M.aggs) cs.push({ id: "agg:" + a.id, parent: M.ctxOf.has(a.id) ? "ctx:" + M.ctxOf.get(a.id) : null, kind: "aggregate", label: a.name, sub: "aggregate", agg: a.id, hue: M.hue(a.id) });
    cs.push({ id: "shared", parent: null, kind: "shared", label: "Shared kernel", sub: "used across contexts" });
    if (withProcs) cs.push({ id: "procs", parent: null, kind: "procs", label: "Processes", sub: "change several aggregates, all or nothing" });
    if (M.services.length || M.ports.length) cs.push({ id: "app", parent: null, kind: "app", label: "Application layer", sub: "use cases, and the ports they call" });
    for (const x of M.systems) cs.push({ id: "sys:" + x.id, parent: null, kind: "system", label: x.name, sub: "external" + (x.kind ? " " + x.kind : "") });
    cs.push({ id: "sys:", parent: null, kind: "system", label: "Outside", sub: "types the ports use" });
    return cs;
  }
  const containerOfType = (M, id) => {
    const p = M.place.get(id);
    if (!p || p.level === "shared") return "shared";
    if (p.level === "sys") return "sys:" + p.id;
    return p.level === "agg" ? "agg:" + p.id : "ctx:" + p.id;
  };

  /* ================= the class diagram ================= */
  const argText = (a) => (a.name.includes("✝") || /^a\d*$/.test(a.name) ? a.type : `${a.name}: ${a.type}`);
  const classRowText = (r) => (r.args ? (r.args.length || r.ret ? `${r.name}(${r.args.join(", ")})` : r.name) + (r.ret ? " → " + r.ret : "") : `${r.name}: ${r.type}`);
  /** What a port fronts, in words: one API, several, or the whole system. */
  function fronts(M, p) {
    const sys = p.system && M.system(p.system);
    if (!sys) return "";
    if (!p.apis.length) return `all of ${sys.name}`;
    const name = (a) => a;
    return `${sys.name}: ${p.apis.map(name).join(", ")} API${p.apis.length > 1 ? "s" : ""}`;
  }
  /** `f (a : A) (b : B) : R` as the argument types and `R`. */
  function sigParts(sig) {
    const i = sig.lastIndexOf(") : "), ret = i >= 0 ? sig.slice(i + 4) : (sig.split(" : ").slice(1).join(" : "));
    const args = [...sig.matchAll(/\(([^():]+?) : ([^()]+(?:\([^()]*\)[^()]*)*)\)/g)].map((m) => m[2].trim());
    return { args, ret };
  }
  function classGraph(M) {
    const nodes = [], edges = [];
    const resolve = (tid) => {
      const t = M.types.get(tid);
      return t && t.kind === "identifier" && M.identifies.has(tid) ? { to: M.identifies.get(tid), ref: true } : { to: tid, ref: false };
    };
    const kindFor = (from, to) => {
      const r = resolve(to);
      if (r.ref) return ["ref", r.to];
      if (M.types.get(to).kind === "identifier") return ["uses", to];
      return [containerOfType(M, to) === containerOfType(M, from) ? "has" : "uses", to];
    };
    for (const t of M.d.types) {
      const k = M.kind(t);
      const rows = [];
      if (t.fields) {
        M.fields(t).forEach((f, i) => {
          rows.push({ name: f.name, type: f.type, hueRef: (f.refs || [])[0], from: f.from, doc: f.doc });
          const g = M.target(f);
          if (!g) return;
          const [ek, to] = kindFor(t.id, g.id);
          edges.push({ from: t.id, row: i, to, kind: ek, card: g.many ? "*" : g.opt ? "0..1" : "1" });
        });
      } else if (t.ctors) {
        t.ctors.forEach((c, i) => {
          rows.push({ name: c.name, args: (c.args || []).map(argText), doc: c.doc });
          for (const a of c.args || []) {
            const g = M.target(a);
            if (!g) continue;
            let [ek, to] = kindFor(t.id, g.id);
            if (["command", "event", "rejection"].includes(k)) ek = "arg";
            edges.push({ from: t.id, row: i, to, kind: ek, card: g.many ? "*" : g.opt ? "0..1" : "1" });
          }
        });
      }
      for (const e of t.edges || []) if (e.kind === "extends" && M.types.has(e.to)) edges.push({ from: t.id, to: e.to, kind: "extends" });
      const agg = M.aggs.find((a) => a.state === t.id);
      nodes.push({ id: t.id, kind: k, title: t.name, doc: t.doc, stereo: STEREO[k] || k, rows, container: containerOfType(M, t.id), hue: M.typeHue(t), seals: agg ? agg.invariants.length : 0 });
    }
    for (const [idt, ent] of M.identifies) edges.push({ from: idt, to: ent, kind: "identifies" });
    for (const a of M.aggs) {
      edges.push({ from: a.cmd, to: a.state, kind: "msg" });
      edges.push({ from: a.state, to: a.evt, kind: "msg" });
      if (a.err) edges.push({ from: a.state, to: a.err, kind: "refuse" });
    }
    for (const p of M.d.processes) {
      nodes.push({ id: "proc:" + p.id, kind: "process", title: p.name, stereo: "process", rows: p.touches.map((t) => ({ name: "changes", type: (M.agg(t) || {}).name || t, hueAgg: t })), container: "procs", hue: "var(--focus)" });
      p.touches.forEach((t, i) => M.agg(t) && edges.push({ from: "proc:" + p.id, row: i, to: M.agg(t).state, kind: "proc" }));
    }
    appGraph(M, nodes, edges);
    const ids = new Set(nodes.map((n) => n.id));
    return { nodes: sizeNodes(nodes), edges: edges.filter((e) => ids.has(e.from) && ids.has(e.to)) };
  }
  /** Application services, ports, their anti-corruption layers, and the systems behind them. */
  function appGraph(M, nodes, edges) {
    const short = (n) => n.split(".").pop();
    for (const x of M.systems)
      nodes.push({ id: "sysnode:" + x.id, kind: "system", title: x.name, doc: x.doc, stereo: x.kind || "external system",
        rows: x.apis.length ? x.apis.map((a) => ({ name: a.id, type: a.doc || "API", doc: a.doc })) : [{ name: "one API", type: "" }],
        container: "sys:" + x.id, hue: "var(--muted)" });
    for (const p of M.ports) {
      const sys = p.system && M.system(p.system);
      nodes.push({ id: "port:" + p.id, kind: "port", title: short(p.name), doc: p.doc, stereo: "port" + (sys ? " → " + (p.apis.length ? p.apis.join(", ") + " API" + (p.apis.length > 1 ? "s" : "") : "all of " + sys.name) : ""), maxW: 560,
        rows: p.ops.map((o) => ({ name: o.name, args: o.args.map(argText), ret: o.returns, doc: o.doc })), container: "app", hue: "var(--port)" });
      p.ops.forEach((o, i) => { for (const r of o.refs) edges.push({ from: "port:" + p.id, row: i, to: r, kind: "dto" }); });
      if (sys) {
        if (p.apis.length) p.apis.forEach((a) => edges.push({ from: "port:" + p.id, to: "sysnode:" + sys.id, toRow: sys.apis.findIndex((x) => x.id === a), kind: "fronts" }));
        else edges.push({ from: "port:" + p.id, to: "sysnode:" + sys.id, kind: "fronts" });
      }
      if (p.acl.length) {
        nodes.push({ id: "acl:" + p.id, kind: "acl", title: short(p.name) + " translator", stereo: "anti-corruption layer",
          doc: "Turns what " + (sys ? sys.name : "the outside") + " answers into the domain's terms, or says why it can't.",
          maxW: 520, rows: p.acl.map((f) => { const sp = sigParts(f.signature); return { name: short(f.name), args: sp.args, ret: sp.ret, doc: f.doc }; }), container: "app", hue: "var(--port)" });
        edges.push({ from: "port:" + p.id, to: "acl:" + p.id, kind: "acl" });
        p.acl.forEach((f, i) => { for (const r of f.from) edges.push({ from: "acl:" + p.id, row: i, to: r, kind: "acl" }); for (const r of f.to) edges.push({ from: "acl:" + p.id, row: i, to: r, kind: "uses" }); });
      }
    }
    for (const sv of M.services) {
      nodes.push({ id: "svc:" + sv.id, kind: "service", title: sv.name, doc: sv.doc, stereo: "application service",
        rows: sv.useCases.map((u) => ({ name: u.id, type: u.asks.length ? "asks " + u.asks.join(", ") : "asks no one", doc: u.doc })), container: "app", hue: "var(--port)" });
      sv.useCases.forEach((u, i) => {
        for (const pid of u.asks) edges.push({ from: "svc:" + sv.id, row: i, to: "port:" + pid, kind: "asks" });
        for (const a of u.changes) { const g = M.agg(a); if (g) edges.push({ from: "svc:" + sv.id, row: i, to: g.state, kind: "changes" }); }
      });
    }
  }
  function sizeNodes(nodes) {
    for (const n of nodes) {
      const shown = n.rows.length > MAXROWS ? n.rows.slice(0, MAXROWS - 1) : n.rows;
      n.more = n.rows.length - shown.length;
      n.shown = shown;
      let w = Math.max(tw(n.title, F_HEAD) + 44 + (n.seals ? 40 : 0), tw("«" + n.stereo + "»", F_STEREO) + 30);
      for (const r of shown) w = Math.max(w, tw(classRowText(r), F_ROW) + 30);
      n.w = Math.round(Math.min(n.maxW || MAXW, Math.max(MINW, w)));
      n.h = HEAD + Math.max(1, shown.length + (n.more ? 1 : 0)) * ROW + PADB;
    }
    return nodes;
  }
  const rowIndex = (n, row) => (row === undefined || !n.shown ? row : row < n.shown.length ? row : n.shown.length);

  /* ================= layout ================= */
  /* Two levels: ELK lays out what is inside each frame; frames are then packed in rows. */
  const PAD = { context: [60, 26], aggregate: [48, 16], shared: [48, 16], procs: [48, 16], app: [52, 20], system: [48, 16] };
  function shelf(items, aspect, gap) {
    if (!items.length) return { w: 0, h: 0, at: {} };
    const area = items.reduce((s, b) => s + (b.w + gap) * (b.h + gap), 0);
    const target = Math.max(...items.map((b) => b.w), Math.sqrt(area * aspect));
    const at = {}; let x = 0, y = 0, rowH = 0, W = 0;
    for (const b of items) {
      if (x > 0 && x + b.w > target) { x = 0; y += rowH + gap; rowH = 0; }
      at[b.id] = { x, y }; x += b.w + gap; rowH = Math.max(rowH, b.h); W = Math.max(W, x - gap);
    }
    return { w: W, h: y + rowH, at };
  }
  async function elkBlock(id, ns, edges, opts) {
    if (!ns.length) return { w: 0, h: 0, at: {} };
    const ids = new Set(ns.map((n) => n.id)), seen = new Set();
    const es = [];
    edges.forEach((e, i) => {
      if (!ids.has(e.from) || !ids.has(e.to) || e.from === e.to || (opts.layoutKinds && !opts.layoutKinds.includes(e.kind))) return;
      const k = e.from + ">" + e.to; if (seen.has(k)) return; seen.add(k);
      es.push({ id: id + "e" + i, sources: [e.from], targets: [e.to] });
    });
    try {
      const out = await new ELK().layout({ id, children: ns.map((n) => ({ id: n.id, width: n.w, height: n.h })), edges: es, layoutOptions: {
        "elk.algorithm": "layered", "elk.direction": "RIGHT", "elk.spacing.nodeNode": "24", "elk.layered.spacing.nodeNodeBetweenLayers": "56",
        "elk.spacing.componentComponent": "36", "elk.layered.nodePlacement.strategy": "BRANDES_KOEPF",
        "elk.layered.considerModelOrder.strategy": "NODES_AND_EDGES", "elk.aspectRatio": String(opts.inner || 1.4), "elk.padding": "[top=0,left=0,bottom=0,right=0]" } });
      const at = {};
      for (const c of out.children) at[c.id] = { x: c.x, y: c.y };
      const b = bboxOf(ns.map((n) => ({ x: at[n.id].x, y: at[n.id].y, w: n.w, h: n.h })));
      for (const k in at) { at[k].x -= b.x; at[k].y -= b.y; }
      return { w: b.w, h: b.h, at };
    } catch (err) {
      console.warn("ELK layout failed; packing in rows", err);
      return shelf(ns, 1.4, 24);
    }
  }
  async function layout(nodes, edges, conts, opts = {}) {
    const pos = {};
    const inside = (cid, top) => { for (let c = cid; c; c = (conts.find((x) => x.id === c) || {}).parent) if (c === top) return true; return false; };
    const kidsOf = (id) => conts.filter((c) => c.parent === id);
    const own = (id) => nodes.filter((n) => n.container === id);
    // returns a box {id, w, h, place(ox, oy)} for a container, or null if empty
    async function build(c) {
      const [top, side] = PAD[c.kind];
      const inner = await elkBlock(c.id, own(c.id), edges, opts);
      const kids = (await Promise.all(kidsOf(c.id).map(build))).filter(Boolean);
      if (!kids.length && !inner.w) return null;
      const items = [...kids];
      if (inner.w) items.push({ id: c.id + "#own", w: inner.w, h: inner.h, place: (ox, oy) => { for (const k in inner.at) pos[k] = { x: ox + inner.at[k].x, y: oy + inner.at[k].y }; } });
      const packed = shelf(items, opts.aspect || 1.7, 34);
      return { id: c.id, w: packed.w + 2 * side, h: packed.h + top + side,
        place: (ox, oy) => { for (const it of items) it.place(ox + side + packed.at[it.id].x, oy + top + packed.at[it.id].y); } };
    }
    const tops = (await Promise.all(conts.filter((c) => !c.parent || !conts.some((p) => p.id === c.parent)).map(build))).filter(Boolean);
    const loose = nodes.filter((n) => !conts.some((c) => c.id === n.container));
    if (loose.length) { const b = await elkBlock("loose", loose, edges, opts); tops.push({ id: "loose", w: b.w, h: b.h, place: (ox, oy) => { for (const k in b.at) pos[k] = { x: ox + b.at[k].x, y: oy + b.at[k].y }; } }); }
    if (opts.lead && tops.length > 1) {
      // A story: the context it starts in on top, the others in a row beneath it, in the order
      // they came in. The newest objects of the lead context arrive at its bottom edge, next to
      // the others; when it grows, the row beneath moves down as one.
      const rank = (t) => { if (inside("agg:" + opts.lead, t.id)) return -1; const i = nodes.findIndex((n) => inside(n.container, t.id)); return i < 0 ? 1e9 : i; };
      const sorted = [...tops].sort((a, b) => rank(a) - rank(b));
      const [lead, ...rest] = sorted;
      const row = shelf(rest, 1e3, 70);
      lead.place(0, 0);
      for (const t of rest) t.place(row.at[t.id].x, lead.h + 70 + row.at[t.id].y);
      return pos;
    }
    const all = shelf(tops, opts.aspect || 1.7, 70);
    for (const t of tops) t.place(all.at[t.id].x, all.at[t.id].y);
    return pos;
  }

  /** Frame rectangles, from where their members are now. */
  function frames(conts, nodes, pos) {
        const boxes = new Map();
    const box = (c) => {
      if (boxes.has(c.id)) return boxes.get(c.id);
      let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
      for (const n of nodes) if (n.container === c.id && pos[n.id]) { const p = pos[n.id]; x0 = Math.min(x0, p.x); y0 = Math.min(y0, p.y); x1 = Math.max(x1, p.x + n.w); y1 = Math.max(y1, p.y + n.h); }
      for (const k of conts) if (k.parent === c.id) { const b = box(k); if (b) { x0 = Math.min(x0, b.x); y0 = Math.min(y0, b.y); x1 = Math.max(x1, b.x + b.w); y1 = Math.max(y1, b.y + b.h); } }
      if (x0 === Infinity) { boxes.set(c.id, null); return null; }
      const [top, side] = PAD[c.kind];
      const b = { ...c, x: x0 - side, y: y0 - top, w: x1 - x0 + 2 * side, h: y1 - y0 + top + side };
      boxes.set(c.id, b);
      return b;
    };
    conts.forEach(box);
    return conts.map((c) => boxes.get(c.id)).filter(Boolean);
  }
  function members(conts, nodes, id) {
    const ids = new Set([id]);
    let grew = true;
    while (grew) { grew = false; for (const c of conts) if (c.parent && ids.has(c.parent) && !ids.has(c.id)) { ids.add(c.id); grew = true; } }
    return nodes.filter((n) => ids.has(n.container)).map((n) => n.id);
  }
  function bboxOf(list) {
    let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
    for (const b of list) if (b) { x0 = Math.min(x0, b.x); y0 = Math.min(y0, b.y); x1 = Math.max(x1, b.x + b.w); y1 = Math.max(y1, b.y + b.h); }
    return x0 === Infinity ? null : { x: x0, y: y0, w: x1 - x0, h: y1 - y0 };
  }

  /* ================= edges ================= */
  function edgePath(a, ay, b, by) {
    const sx0 = a.x, sx1 = a.x + a.w, tx0 = b.x, tx1 = b.x + b.w;
    let sx, ex, d1, d2;
    if (tx0 >= sx1 + 12) { sx = sx1; ex = tx0; d1 = 1; d2 = -1; }
    else if (tx1 <= sx0 - 12) { sx = sx0; ex = tx1; d1 = -1; d2 = 1; }
    else { sx = sx1; ex = tx1; d1 = 1; d2 = 1; }
    const dx = Math.max(42, Math.abs(ex - sx) * 0.45);
    const loop = Math.max(sx, ex) + 56;
    const c1 = d1 === d2 ? loop : sx + d1 * dx, c2 = d1 === d2 ? loop : ex + d2 * dx;
    return { d: `M${sx},${ay} C${c1},${ay} ${c2},${by} ${ex},${by}`, ex, ey: by, d2 };
  }
  function selfLoop(a, ay) {
    const x = a.x + a.w, y2 = a.y + 20;
    return { d: `M${x},${ay} C${x + 56},${ay} ${x + 56},${y2} ${x},${y2}`, ex: x, ey: y2, d2: 1 };
  }

  /* ================= canvas: pan, zoom, drag ================= */
  function useView() {
    const [view, setView] = useState({ k: 1, x: 0, y: 0 });
    const cur = useRef(view);
    cur.current = view;
    const anim = useRef(null);
    const tween = useCallback((to, ms = 420) => {
      cancelAnimationFrame(anim.current);
      if (reduced() || ms === 0) { setView(to); return; }
      const from = cur.current, t0 = performance.now();
      const step = (now) => {
        const t = Math.min(1, (now - t0) / ms), e = 1 - Math.pow(1 - t, 3);
        setView({ k: from.k + (to.k - from.k) * e, x: from.x + (to.x - from.x) * e, y: from.y + (to.y - from.y) * e });
        if (t < 1) anim.current = requestAnimationFrame(step);
      };
      anim.current = requestAnimationFrame(step);
    }, []);
    return [view, setView, tween];
  }
  /** Fit it all if that stays readable; otherwise open readable, at its top left. */
  function openView(box, size) {
    const f = fitView(box, size);
    if (!box || f.k >= 0.5) return f;
    const k = 0.6;
    return { k, x: 30 - box.x * k, y: 24 - box.y * k };
  }
  function fitView(box, size, maxK = 1.1, pad = 40) {
    if (!box || !size.w) return { k: 1, x: 0, y: 0 };
    const k = Math.max(0.12, Math.min(maxK, (size.w - 2 * pad) / box.w, (size.h - 2 * pad) / box.h));
    return { k, x: size.w / 2 - (box.x + box.w / 2) * k, y: size.h / 2 - (box.y + box.h / 2) * k };
  }

  function Canvas({ nodes, conts, pos, setPos, view, setView, onSize, onBackground, onNodeClick, onFrameClick, label, nodeLayer, edgeLayer, overlay, map = true }) {
    const ref = useRef(null);
    const drag = useRef(null);
    const [dragging, setDragging] = useState(false);
    useEffect(() => {
      const el = ref.current;
      const measure = () => { const r = el.getBoundingClientRect(); onSize({ w: r.width, h: r.height }); };
      measure();
      const raf = requestAnimationFrame(measure);
      const ro = new ResizeObserver(measure);
      ro.observe(el);
      addEventListener("resize", measure);
      const wheel = (e) => {
        e.preventDefault();
        const r = el.getBoundingClientRect(), mx = e.clientX - r.left, my = e.clientY - r.top;
        const zoom = e.ctrlKey || e.metaKey || e.deltaMode === 1 || (Math.abs(e.deltaY) >= 50 && e.deltaX === 0 && Number.isInteger(e.deltaY));
        if (zoom) setView((v) => { const k = Math.max(0.12, Math.min(2.6, v.k * Math.exp(-e.deltaY * (e.ctrlKey ? 0.01 : 0.002)))); return { k, x: mx - ((mx - v.x) * k) / v.k, y: my - ((my - v.y) * k) / v.k }; });
        else setView((v) => ({ ...v, x: v.x - e.deltaX, y: v.y - e.deltaY }));
      };
      el.addEventListener("wheel", wheel, { passive: false });
      return () => { cancelAnimationFrame(raf); ro.disconnect(); removeEventListener("resize", measure); el.removeEventListener("wheel", wheel); };
    }, []);
    const start = (e, what) => {
      if (e.button !== 0) return;
      e.stopPropagation();
      const ids = what.kind === "node" ? [what.id] : what.kind === "frame" ? members(conts, nodes, what.id) : [];
      drag.current = { ...what, sx: e.clientX, sy: e.clientY, moved: false, orig: Object.fromEntries(ids.map((id) => [id, pos[id]])), view0: view, k: view.k };
      ref.current.setPointerCapture(e.pointerId);
    };
    const move = (e) => {
      const g = drag.current; if (!g) return;
      if (!g.moved && Math.hypot(e.clientX - g.sx, e.clientY - g.sy) < 4) return;
      if (!g.moved) { g.moved = true; setDragging(true); }
      if (g.kind === "pan") { setView({ ...g.view0, x: g.view0.x + e.clientX - g.sx, y: g.view0.y + e.clientY - g.sy }); return; }
      const dx = (e.clientX - g.sx) / g.k, dy = (e.clientY - g.sy) / g.k;
      setPos((p) => { const q = { ...p }; for (const id in g.orig) if (g.orig[id]) q[id] = { x: g.orig[id].x + dx, y: g.orig[id].y + dy }; return q; });
    };
    const end = () => {
      const g = drag.current; drag.current = null; setDragging(false);
      if (!g || g.moved) return;
      if (g.kind === "node") onNodeClick(g.id);
      else if (g.kind === "frame") onFrameClick && onFrameClick(g.id);
      else onBackground && onBackground();
    };
    const fr = frames(conts, nodes, pos);
    const [vs, setVs] = useState({ w: 0, h: 0 });
    const [mm, setMm] = useState(() => map && innerWidth > 1000);
    useEffect(() => { const el = ref.current; const r = el.getBoundingClientRect(); if (r.width !== vs.w || r.height !== vs.h) setVs({ w: r.width, h: r.height }); });
    return html`<${React.Fragment}><svg ref=${ref} className=${"canvas" + (dragging ? " dragging" : "")} role="application" aria-label=${label}
        onPointerDown=${(e) => start(e, { kind: "pan" })} onPointerMove=${move} onPointerUp=${end} onPointerCancel=${() => { drag.current = null; setDragging(false); }}
        onKeyDown=${(e) => { if (e.key !== "Enter" && e.key !== " ") return; const g = e.target.closest && e.target.closest("[data-id]"); if (g) { e.preventDefault(); onNodeClick(g.getAttribute("data-id")); } }}>
      <defs>
        <pattern id="dots" width="22" height="22" patternUnits="userSpaceOnUse" patternTransform=${`translate(${view.x} ${view.y}) scale(${view.k})`}><circle className="grid-dot" cx="1" cy="1" r="1" /></pattern>
        <marker id="end-extends" viewBox="0 0 12 12" refX="11" refY="6" markerWidth="13" markerHeight="13" markerUnits="userSpaceOnUse" orient="auto-start-reverse"><path d="M1,1 L11,6 L1,11 z" className="mk mk-extends" /></marker>
        ${["has", "ref", "uses", "msg", "proc", "arg", "identifies", "refuse", "cmd", "evt", "link", "flow", "asks", "changes", "dto", "acl", "fronts", "call"].map((k) => html`<marker key=${k} id=${"end-" + k} viewBox="0 0 10 10" refX="9" refY="5" markerWidth="8" markerHeight="8" markerUnits="userSpaceOnUse" orient="auto-start-reverse">
          ${k === "ref" || k === "identifies" || k === "link" ? html`<path d="M1,1 L9,5 L1,9" className=${"mk mk-open mk-" + k} />` : html`<path d="M0,0 L10,5 L0,10 z" className=${"mk mk-" + k} />`}</marker>`)}
        <marker id="start-has" viewBox="0 0 16 10" refX="1" refY="5" markerWidth="15" markerHeight="9" markerUnits="userSpaceOnUse" orient="auto-start-reverse"><path d="M1,5 L8,1 L15,5 L8,9 z" className="mk mk-has" /></marker>
      </defs>
      <rect className="bg" width="100%" height="100%" fill="url(#dots)" />
      <g transform=${`translate(${view.x} ${view.y}) scale(${view.k})`}>
        ${fr.filter((f) => f.kind !== "aggregate").map((f) => html`<${Frame} key=${f.id} f=${f} start=${start} k=${view.k} />`)}
        ${fr.filter((f) => f.kind === "aggregate").map((f) => html`<${Frame} key=${f.id} f=${f} start=${start} k=${view.k} />`)}
        ${edgeLayer}
        ${nodeLayer(start)}
        ${overlay}
      </g>
    </svg>
    <button className="mm-toggle" onClick=${() => setMm(!mm)} aria-pressed=${mm}>${mm ? "Hide map" : "Map"}</button>
    ${mm && html`<${Minimap} frames=${fr} nodes=${nodes} pos=${pos} view=${view} setView=${setView} size=${vs} />`}</${React.Fragment}>`;
  }
  function Minimap({ frames: fr, nodes, pos, view, setView, size }) {
    const world = bboxOf([...fr, ...nodes.map((n) => pos[n.id] && { x: pos[n.id].x, y: pos[n.id].y, w: n.w, h: n.h })]);
    const drag = useRef(false);
    if (!world || !size.w) return null;
    const vw = { x: -view.x / view.k, y: -view.y / view.k, w: size.w / view.k, h: size.h / view.k };
    if (vw.x <= world.x && vw.y <= world.y && vw.x + vw.w >= world.x + world.w && vw.y + vw.h >= world.y + world.h) return null;
    const W = 210, s = W / world.w, H = Math.min(170, world.h * s);
    const s2 = Math.min(s, H / world.h);
    const go = (e) => {
      const r = e.currentTarget.getBoundingClientRect();
      const wx = world.x + (e.clientX - r.left) / s2, wy = world.y + (e.clientY - r.top) / s2;
      setView((v) => ({ ...v, x: size.w / 2 - wx * v.k, y: size.h / 2 - wy * v.k }));
    };
    return html`<svg className="minimap" width=${world.w * s2} height=${world.h * s2} aria-label="Overview: click or drag to move around"
        onPointerDown=${(e) => { drag.current = true; e.currentTarget.setPointerCapture(e.pointerId); go(e); }}
        onPointerMove=${(e) => drag.current && go(e)} onPointerUp=${() => (drag.current = false)}>
      <g transform=${`scale(${s2}) translate(${-world.x} ${-world.y})`}>
        ${fr.map((f) => html`<rect key=${f.id} className=${"mm-frame mm-" + f.kind} style=${{ "--h": f.hue || "var(--faint)" }} x=${f.x} y=${f.y} width=${f.w} height=${f.h} rx="20" />`)}
        ${nodes.map((n) => pos[n.id] && html`<rect key=${n.id} className="mm-node" style=${{ "--h": n.hue || "var(--muted)" }} x=${pos[n.id].x} y=${pos[n.id].y} width=${n.w} height=${n.h} />`)}
        <rect className="mm-view" x=${vw.x} y=${vw.y} width=${vw.w} height=${vw.h} style=${{ strokeWidth: 2 / s2 }} />
      </g>
    </svg>`;
  }
  function Frame({ f, start, k = 1 }) {
    const big = f.kind === "context";
    const base = big ? 18 : 14, font = (z) => `${big ? 700 : 600} ${z}px "Schibsted Grotesk"`;
    // titles grow as you zoom out so they stay readable, but never wider than their frame
    let fs = Math.min(base * 4, Math.max(base, (big ? 22 : 16) / k));
    fs = Math.max(base, Math.min(fs, (f.w - 40) / Math.max(1, tw(f.label, font(1)))));
    const far = fs > base * 1.3;
    const labelW = tw(f.label, font(fs));
    const x = f.x + (big ? 22 : 16), y = far ? (big ? f.y - fs * 0.35 : f.y + fs + 6) : f.y + (big ? 34 : 28);
    return html`<g className=${"frame frame-" + f.kind} style=${{ "--h": f.hue || "var(--muted)" }}>
      <rect className="frame-box" x=${f.x} y=${f.y} width=${f.w} height=${f.h} rx=${big ? 20 : 13} />
      <g className="frame-handle" onPointerDown=${(e) => start(e, { kind: "frame", id: f.id })}>
        <title>Drag to move everything inside; click to zoom to it</title>
        <rect x=${f.x} y=${f.y} width=${Math.min(f.w, labelW + tw(f.sub, F_STEREO) * fs / base + 50)} height=${(big ? 50 : 40) + fs - base} fill="transparent" />
        <text className="frame-label" x=${x} y=${y} style=${{ fontSize: fs + "px" }}>${f.label}</text>
        ${!far && html`<text className="frame-sub" x=${x + labelW + 10} y=${y}>${f.sub}</text>`}
      </g>
    </g>`;
  }
  function ZoomBar({ setView, size, fit, tidy }) {
    const zoomBy = (f) => setView((v) => { const k = Math.max(0.12, Math.min(2.6, v.k * f)); return { k, x: size.w / 2 - ((size.w / 2 - v.x) * k) / v.k, y: size.h / 2 - ((size.h / 2 - v.y) * k) / v.k }; });
    return html`<div className="zoom" role="group" aria-label="View">
      <button onClick=${() => zoomBy(1.25)} aria-label="Zoom in">+</button>
      <button onClick=${() => zoomBy(0.8)} aria-label="Zoom out">−</button>
      <button onClick=${fit}>Fit</button>
      <button onClick=${tidy} title="Lay everything out again, forgetting where you moved things">Tidy</button>
    </div>`;
  }

  /* ================= class diagram view ================= */
  const LAYERS = [["has", "Composition", true], ["extends", "Extends", true], ["ref", "Reference by id", true], ["msg", "Commands and events", true], ["refuse", "Rejections", true],
    ["proc", "Processes", true], ["identifies", "Identifier of", true], ["asks", "Use case asks a port", true], ["changes", "Use case changes an aggregate", true],
    ["dto", "Port operations' DTOs", true], ["acl", "Anti-corruption layer", true], ["fronts", "Port fronts an API", true], ["uses", "Uses a shared value", false], ["arg", "Command and event arguments", false]];
  const loadPos = (key) => { try { const s = localStorage.getItem(key); return s ? JSON.parse(s) : null; } catch (e) { return null; } };
  const savePos = (key, p) => { try { localStorage.setItem(key, JSON.stringify(p)); } catch (e) { /* private mode */ } };
  const forget = (key) => { try { localStorage.removeItem(key); } catch (e) { /* private mode */ } };

  function ClassNode({ n, M, sel, hot, dim, start, k }) {
    const p = n.p;
    const cls = `node k-${n.kind}${sel ? " sel" : ""}${hot ? " hot" : ""}${dim ? " dim" : ""}`;
    if (k < 0.42) {
      // far away: the type's name, large enough to read, over a sketch of its rows
      const sc = Math.min(13 / k / 14, (n.w - 24) / Math.max(1, tw(n.title, F_HEAD)));
      return html`<g className=${cls + " far"} transform=${`translate(${p.x} ${p.y})`} style=${{ "--h": n.hue }} tabIndex="0" role="button" aria-label=${`${n.stereo} ${n.title}`}
          onPointerDown=${(e) => start(e, { kind: "node", id: n.id })} data-id=${n.id}>
        <rect className="n-body" width=${n.w} height=${n.h} rx="9" />
        <path className="n-head" d=${`M0,9 a9,9 0 0 1 9,-9 h${n.w - 18} a9,9 0 0 1 9,9 v${Math.max(HEAD, 14 * sc + 22) - 9} h${-n.w} z`} />
        <text className="n-title" x="12" y=${14 * sc + 6} style=${{ fontSize: 14 * sc + "px" }}>${n.title}</text>
        ${n.shown.map((r, i) => { const y = Math.max(HEAD, 14 * sc + 22) + i * ROW + 6; return y + 8 < n.h && html`<rect key=${i} className="n-skel" x="13" y=${y} width=${(n.w - 26) * (0.35 + 0.5 * (((i * 37 + n.title.length * 11) % 10) / 10))} height="7" rx="3" />`; })}
      </g>`;
    }
    return html`<g className=${cls} transform=${`translate(${p.x} ${p.y})`} style=${{ "--h": n.hue }} tabIndex="0" role="button" aria-label=${`${n.stereo} ${n.title}`}
        onPointerDown=${(e) => start(e, { kind: "node", id: n.id })} data-id=${n.id}>
      <rect className="n-body" width=${n.w} height=${n.h} rx="9" />
      <path className="n-head" d=${`M0,9 a9,9 0 0 1 9,-9 h${n.w - 18} a9,9 0 0 1 9,9 v${HEAD - 9} h${-n.w} z`} />
      <text className="n-stereo" x="14" y="17">«${n.stereo}»</text>
      <text className="n-title" x="14" y="35">${n.doc && html`<title>${n.title}: ${plain(n.doc)}</title>`}${clip(n.title, F_HEAD, n.w - 28 - (n.seals ? 40 : 0))}</text>
      ${n.seals > 0 && html`<text className="n-seal" x=${n.w - 14} y="35" textAnchor="end"><title>${plural(n.seals, "invariant")} proved in Lean</title>∎ ${n.seals}</text>`}
      ${n.shown.map((r, i) => {
        const y = HEAD + i * ROW + 14;
        if (r.args) {
          const t = clip(classRowText(r), F_ROW, n.w - 26), cut = t.indexOf("(");
          return html`<text key=${i} className="n-row" x="13" y=${y}>${r.doc && html`<title>${r.name}: ${plain(r.doc)}</title>`}<tspan className="n-ctor">${cut < 0 ? t : t.slice(0, cut)}</tspan>${cut >= 0 ? html`<tspan className="n-ty">${t.slice(cut)}</tspan>` : null}</text>`;
        }
        const name = r.name + ": ", ty = clip(r.type, F_ROW, n.w - 26 - tw(name, F_ROW));
        const rt = r.hueRef && M.types.get(r.hueRef);
        const fill = r.hueAgg ? M.hue(r.hueAgg) : rt && rt.kind !== "identifier" ? M.typeHue(rt) : null;
        return html`<text key=${i} className="n-row" x="13" y=${y}>${r.doc && html`<title>${r.name}: ${plain(r.doc)}</title>`}<tspan className=${r.from ? "n-inh" : ""}>${name}</tspan><tspan className="n-ty" style=${fill ? { fill } : null}>${ty}</tspan></text>`;
      })}
      ${n.more > 0 && html`<text className="n-more" x="13" y=${HEAD + n.shown.length * ROW + 14}>+${n.more} more, select to see all</text>`}
      ${!n.rows.length && html`<text className="n-more" x="13" y=${HEAD + 14}>no fields</text>`}
    </g>`;
  }

  function EdgeLayer({ edges, byId, focus, centre, layers, far, frs }) {
    const once = new Set();
    if (far) {
      // one line per pair of frames, as thick as the number of connections it stands for
      const fb = new Map(frs.map((f) => [f.id, f]));
      const bundles = new Map(), local = [];
      for (const e of edges) {
        const a = byId.get(e.from), b = byId.get(e.to);
        if (!a || !b || !a.p || !b.p || !layers[e.kind] && !(centre && (e.from === centre || e.to === centre))) continue;
        if (a.container === b.container) { local.push(e); continue; }
        const key = a.container + ">" + b.container;
        if (!bundles.has(key)) bundles.set(key, { from: a.container, to: b.container, n: 0, kinds: new Set(), hot: false });
        const bu = bundles.get(key); bu.n++; bu.kinds.add(e.kind); if (centre && (e.from === centre || e.to === centre)) bu.hot = true;
      }
      return html`<g className="edges">
        ${local.map((e, i) => { const a = byId.get(e.from), b = byId.get(e.to); const g = e.from === e.to ? selfLoop({ x: a.p.x, y: a.p.y, w: a.w, h: a.h }, a.p.y + HEAD / 2) : edgePath({ x: a.p.x, y: a.p.y, w: a.w, h: a.h }, a.p.y + HEAD / 2, { x: b.p.x, y: b.p.y, w: b.w, h: b.h }, b.p.y + HEAD / 2);
          return html`<g key=${"l" + i} className=${`edge e-${e.kind}${focus && !(e.from === centre || e.to === centre) ? " dim" : ""}`}><path d=${g.d} markerEnd=${e.kind === "has" ? null : `url(#end-${e.kind})`} markerStart=${e.kind === "has" ? "url(#start-has)" : null} /></g>`; })}
        ${[...bundles.values()].map((bu, i) => {
          const A = fb.get(bu.from), B = fb.get(bu.to);
          if (!A || !B) return null;
          const g = edgePath(A, A.y + Math.min(A.h / 2, 120), B, B.y + Math.min(B.h / 2, 120));
          const kind = bu.kinds.has("ref") ? "ref" : [...bu.kinds][0];
          const mx = (A.x + A.w / 2 + B.x + B.w / 2) / 2, my = (A.y + Math.min(A.h / 2, 120) + B.y + Math.min(B.h / 2, 120)) / 2;
          return html`<g key=${"b" + i} className=${`edge bundle e-${kind}${bu.hot ? " hot" : ""}${focus && !bu.hot ? " dim" : ""}`}>
            <path d=${g.d} style=${{ strokeWidth: 2 + Math.log2(bu.n) * 2 }} markerEnd=${`url(#end-${kind === "has" ? "uses" : kind})`} />
            <text className="bundle-n" x=${mx} y=${my} textAnchor="middle" style=${{ fontSize: Math.min(48, 12 / Math.max(0.12, frs.k || 0.3)) + "px" }}>${bu.n}</text></g>`;
        })}</g>`;
    }
    return html`<g className="edges">${edges.map((e, i) => {
      if ((e.kind === "ref" || e.kind === "uses" || e.kind === "arg") && !(centre && (e.from === centre || e.to === centre))) {
        const k = e.kind + e.from + ">" + e.to; if (once.has(k)) return null; once.add(k);
      }
      const a = byId.get(e.from), b = byId.get(e.to);
      if (!a || !b || !a.p || !b.p) return null;
      const touching = !!centre && (e.from === centre || e.to === centre);
      if (!layers[e.kind] && !touching) return null;
      const ra = rowIndex(a, e.row);
      const ay = ra === undefined ? a.p.y + HEAD / 2 : a.p.y + HEAD + ra * ROW + ROW / 2 - 1;
      const rb = e.toRow === undefined || e.toRow < 0 ? undefined : rowIndex(b, e.toRow);
      const by = rb === undefined ? b.p.y + HEAD / 2 : b.p.y + HEAD + rb * ROW + ROW / 2 - 1;
      const A = { x: a.p.x, y: a.p.y, w: a.w, h: a.h }, B = { x: b.p.x, y: b.p.y, w: b.w, h: b.h };
      const g = e.from === e.to ? selfLoop(A, ay) : edgePath(A, ay, B, by);
      return html`<g key=${i} className=${`edge e-${e.kind}${touching ? " hot" : ""}${focus && !touching ? " dim" : ""}`}>
        <path d=${g.d} markerEnd=${e.kind === "has" ? null : `url(#end-${e.kind})`} markerStart=${e.kind === "has" ? "url(#start-has)" : null} />
        ${e.card && e.card !== "1" && html`<text className="e-card" x=${g.ex + (g.d2 === -1 ? -8 : 8)} y=${g.ey - 7} textAnchor=${g.d2 === -1 ? "end" : "start"}>${e.card}</text>`}
      </g>`;
    })}</g>`;
  }

  function ClassView({ M, sel, setSel, layers }) {
    const G = useMemo(() => classGraph(M), [M]);
    const conts = useMemo(() => containers(M, M.d.processes.length > 0), [M]);
    const key = `ddd-viz:${M.d.id}:classes:v3`;
    const [pos, setPos] = useState(null);
    const [view, setView, tween] = useView();
    const [size, setSize] = useState({ w: 0, h: 0 });
    const [hover, setHover] = useState(null);
    const fitted = useRef(false);
    const relayout = useCallback(async () => {
      const p = await layout(G.nodes, G.edges, conts, { layoutKinds: ["has", "extends", "msg", "refuse", "proc", "identifies", "asks", "dto", "acl", "fronts"] });
      fitted.current = false; setPos(p);
    }, [G]);
    useEffect(() => {
      const saved = loadPos(key);
      if (saved && G.nodes.every((n) => saved[n.id])) setPos(saved); else relayout();
    }, [G]);
    useEffect(() => { if (pos) { const t = setTimeout(() => savePos(key, pos), 300); return () => clearTimeout(t); } }, [pos]);
    const nodes = useMemo(() => (pos ? G.nodes.map((n) => ({ ...n, p: pos[n.id] })) : []), [G, pos]);
    const byId = useMemo(() => new Map(nodes.map((n) => [n.id, n])), [nodes]);
    const all = () => bboxOf([...frames(conts, nodes, pos || {}), ...nodes.map((n) => n.p && { x: n.p.x, y: n.p.y, w: n.w, h: n.h })]);
    useEffect(() => { if (pos && size.w && !fitted.current) { fitted.current = true; setView(openView(all(), size)); } }, [pos, size.w]);
    const centre = sel || hover;
    const focus = useMemo(() => {
      if (!centre || !byId.has(centre)) return null;
      const s = new Set([centre]);
      for (const e of G.edges) { if (e.from === centre) s.add(e.to); if (e.to === centre) s.add(e.from); }
      return s;
    }, [centre, G, byId]);
    // bring a node chosen elsewhere (search, a link) into view
    useEffect(() => {
      if (!sel || !byId.has(sel) || !size.w) return;
      const n = byId.get(sel), k = Math.max(view.k, 0.85);
      const sx = n.p.x * view.k + view.x, sy = n.p.y * view.k + view.y;
      if (sx < 0 || sy < 0 || sx + n.w * view.k > size.w || sy + Math.min(n.h, 300) * view.k > size.h)
        tween({ k, x: size.w / 2 - (n.p.x + n.w / 2) * k, y: size.h / 3 - n.p.y * k });
    }, [sel, pos && 1]);
    if (!pos) return html`<div className="loading">Laying out ${plural(G.nodes.length, "type")}…</div>`;
    return html`<div className="stage" onPointerOver=${(e) => { const g = e.target.closest && e.target.closest("[data-id]"); setHover(g ? g.getAttribute("data-id") : null); }} onPointerLeave=${() => setHover(null)}>
      <${Canvas} nodes=${nodes} conts=${conts} pos=${pos} setPos=${setPos} view=${view} setView=${setView} onSize=${setSize}
        label=${`Class diagram of ${M.d.title}`}
        onBackground=${() => setSel(null)} onNodeClick=${(id) => setSel(id)}
        onFrameClick=${(id) => { const f = frames(conts, nodes, pos).find((x) => x.id === id); if (f) tween(fitView(f, size, 1.2)); }}
        edgeLayer=${html`<${EdgeLayer} edges=${G.edges} byId=${byId} focus=${focus} centre=${centre} layers=${layers} far=${view.k < 0.42} frs=${Object.assign(frames(conts, nodes, pos), { k: view.k })} />`}
        nodeLayer=${(start) => nodes.map((n) => html`<${ClassNode} key=${n.id} n=${n} M=${M} k=${view.k} sel=${sel === n.id} hot=${focus && focus.has(n.id)} dim=${focus && !focus.has(n.id)} start=${start} />`)} />
      <${ZoomBar} setView=${setView} size=${size} fit=${() => tween(fitView(all(), size))} tidy=${() => { forget(key); relayout(); }} />
    </div>`;
  }

  /* ================= objects: the state, instantiated ================= */
  function fmtVal(v, depth = 0) {
    if (v === null || v === undefined) return "—";
    if (typeof v === "string") return v;
    if (typeof v !== "object") return String(v);
    if (Array.isArray(v)) {
      if (!v.length) return "[]";
      const xs = depth === 0 && v.length > 4 ? v.slice(0, 3).map((x) => fmtVal(x, depth + 1)).concat([`+${v.length - 3}`]) : v.map((x) => fmtVal(x, depth + 1));
      return depth > 0 && v.length === 2 && !Array.isArray(v[0]) && typeof v[1] !== "object" ? `(${xs.join(", ")})` : `[${xs.join(", ")}]`;
    }
    const ks = Object.keys(v);
    if (ks.length === 1) {
      const x = v[ks[0]];
      if (x === null || typeof x !== "object") return ["raw", "code"].includes(ks[0]) ? fmtVal(x, depth) : `${ks[0]}(${fmtVal(x, depth + 1)})`;
      if (!Array.isArray(x)) {
        const inner = Object.keys(x);
        if (inner.length === 1 && ["raw", "code"].includes(inner[0])) return `${ks[0]}(${fmtVal(x, depth + 1)})`;
        return `${ks[0]}(${inner.map((k) => fmtVal(x[k], depth + 1)).join(", ")})`;
      }
      return `${ks[0]}(${x.map((y) => fmtVal(y, depth + 1)).join(", ")})`;
    }
    if (depth > 1) return "{…}";
    return `{${ks.slice(0, 3).map((k) => `${k}: ${fmtVal(v[k], depth + 1)}`).join(", ")}${ks.length > 3 ? ", …" : ""}}`;
  }
  /** Money, when a field's own doc says it is counted in cents (or a currency's smallest unit). */
  const CENTS = /\b(in (its |the )?(minor unit|cents)|smallest unit|cents of)\b/i;
  const NO_MINOR = new Set(["JPY", "KRW", "VND", "CLP", "ISK"]);
  function money(n, cur) {
    const d = cur && NO_MINOR.has(cur) ? 0 : 2;
    const v = (n / 10 ** d).toLocaleString("en-US", { minimumFractionDigits: d, maximumFractionDigits: d });
    return cur ? `${v} ${cur}` : v;
  }
  const isObjType = (M, t) => t && t.fields && ["aggregate", "entity", "value"].includes(M.kind(t)) && M.fields(t).length > 1;
  const idText = (v) => (v == null ? null : fmtVal(v));

  /** Every object in a step's state: the aggregate roots and the entities and values inside them. */
  function objectsOf(M, frame) {
    const objs = new Map(), links = [];
    const walk = (v, typeId, key, agg) => {
      const t = M.types.get(typeId), fs = M.fields(t);
      const o = { key, typeId, agg, id: fs.some((f) => f.name === "id") ? idText(v.id) : null, rows: [], container: "agg:" + agg };
      objs.set(key, o);
      fs.forEach((f) => {
        const val = v[f.name], g = M.target(f), tt = g && M.types.get(g.id);
        if (g && isObjType(M, tt) && g.id !== typeId) {
          const arr = g.many ? val || [] : val == null ? [] : [val];
          const keys = arr.map((x, i) => {
            const cid = x && typeof x === "object" && "id" in x ? idText(x.id) : null;
            const ck = `${key}/${f.name}${g.many ? (cid !== null ? "#" + cid : `[${i}]`) : ""}`;
            walk(x, g.id, ck, agg);
            links.push({ from: key, row: o.rows.length, to: ck, kind: "has" });
            return ck;
          });
          o.rows.push({ name: f.name, doc: f.doc, raw: val, text: g.many ? (keys.length ? `◆ ${plural(keys.length, tt.name)}` : "[]") : val == null ? "—" : `◆ ${tt.name}`, children: keys });
        } else {
          let text = fmtVal(val);
          if (f.type === "String" && typeof val === "string") text = `"${val}"`;
          if (typeof val === "number" && CENTS.test(f.doc || "")) {
            const c = v.currency && (v.currency.code || (typeof v.currency === "string" ? v.currency : null));
            text = money(val, c);
          }
          const row = { name: f.name, text, doc: f.doc, raw: val };
          if (g && tt && tt.kind === "identifier" && M.identifies.has(g.id) && f.name !== "id")
            row.ref = { type: M.identifies.get(g.id), values: (g.many ? val || [] : val == null ? [] : [val]).map(idText) };
          o.rows.push(row);
        }
      });
    };
    for (const a of M.aggs) {
      const s = frame.state[a.id];
      if (s && s.exists !== false && s.raw && typeof s.raw === "object") walk(s.raw, a.state, a.id, a.id);
    }
    const byTypeId = new Map();
    for (const o of objs.values()) if (o.id !== null) byTypeId.set(o.typeId + "|" + o.id, o.key);
    for (const o of objs.values()) o.rows.forEach((r, i) => {
      if (!r.ref) return;
      for (const v of r.ref.values) { const k = byTypeId.get(r.ref.type + "|" + v); if (k && k !== o.key) links.push({ from: o.key, row: i, to: k, kind: "ref" }); }
    });
    return { objs, links };
  }
  const objLabel = (M, o) => {
    const ty = (M.types.get(o.typeId) || {}).name || "?";
    if (o.id !== null && o.id !== "—") return `${o.id} : ${ty}`;
    const seg = o.key.split("/").pop().replace(/#.*$/, "");
    return `${seg} : ${ty}`;
  };

  /** The objects worth drawing: whatever the scenario creates, changes or targets, what holds them,
   *  and what they refer to. The rest of each aggregate folds into one "+N more" box. */
  /** When each object comes onto the page. A story starts from a blank page: an object appears
   *  at the first step that creates, changes or targets it, or names it in a note or `show:`, and
   *  whatever holds it comes with it. Once on the page it stays where it is. */
  function revealSchedule(sc, per) {
    const at = new Map();
    const put = (k, i) => { const parts = k.split("/"); for (let j = 1; j <= parts.length; j++) { const p = parts.slice(0, j).join("/"); if (!at.has(p)) at.set(p, i); } };
    sc.frames.forEach((f, i) => {
      for (const k of [...(f.reveal || []), ...(f.notes || []).map((n) => n.at)]) put(k, i);
      if (i === 0) return;
      const a = per[i - 1].objs, b = per[i].objs;
      for (const t of f.targets || []) if (b.has(t)) put(t, i);
      for (const [k, o] of b) { const p = a.get(k); if (!p || o.rows.some((r, j) => !p.rows[j] || p.rows[j].text !== r.text)) put(k, i); }
    });
    return at;
  }
  function scenarioWorld(M, sc) {
    const per = sc.frames.map((f) => objectsOf(M, f));
    // A row that is empty at every step says nothing, and neither does one that holds a default
    // (zero, false) and never changes. Leave them out; the kept rows are the same at every step.
    const EMPTY = new Set(["[]", "—", '""', "{}"]);
    const DEFAULT = (t) => /^(0|0\.0+|false|none|0\.00 [A-Z]{3})$/.test(t);
    const said = new Map(), texts = new Map();
    for (const fr of per) for (const [k, o] of fr.objs) o.rows.forEach((r) => { const id = k + "\u0000" + r.name; if (!texts.has(id)) texts.set(id, new Set()); texts.get(id).add(r.text); });
    const speaks = (k, r) => { const ts = texts.get(k + "\u0000" + r.name); return [...ts].some((t) => !EMPTY.has(t)) && !(ts.size === 1 && DEFAULT(r.text)); };
    for (const fr of per) for (const [k, o] of fr.objs) o.rows.forEach((r) => { if (speaks(k, r)) { if (!said.has(k)) said.set(k, new Set()); said.get(k).add(r.name); } });
    for (const fr of per) {
      const remap = new Map();
      for (const [k, o] of fr.objs) {
        const keep = said.get(k) || new Set(), m = new Map(), rows = [];
        o.rows.forEach((r, j) => { if (keep.has(r.name)) { m.set(j, rows.length); rows.push(r); } });
        o.rows = rows; remap.set(k, m);
      }
      fr.links = fr.links.filter((l) => l.row == null || (remap.get(l.from) && remap.get(l.from).has(l.row)))
        .map((l) => (l.row == null ? l : { ...l, row: remap.get(l.from).get(l.row) }));
    }
    const at = revealSchedule(sc, per);
    per.forEach((fr, i) => { fr.byEvent = i > 0 ? eventChanges(M, sc.frames[i], per[i - 1], fr) : []; });
    for (const fr of per) {
      for (const k of [...fr.objs.keys()]) if (!at.has(k)) fr.objs.delete(k);
      fr.links = fr.links.filter((l) => fr.objs.has(l.from) && fr.objs.has(l.to));
      fr.more = new Map();
    }
    const union = new Map();
    for (const fr of per) for (const [agg, n] of fr.more) {
      const k = "more:" + agg, label = `+${n} more in ${(M.agg(agg) || {}).name}`;
      const w = Math.round(Math.max(176, tw(label, F_HEAD) + 36));
      if (!union.has(k)) union.set(k, { id: k, container: "agg:" + agg, w, h: OHEAD + ROW + PADB, agg, more: true });
      else union.get(k).w = Math.max(union.get(k).w, w);
    }
    for (const { objs } of per) for (const o of objs.values()) {
      let w = tw(objLabel(M, o), F_HEAD) + 36;
      for (const r of o.rows) w = Math.max(w, tw(`${r.name} = ${r.text}`, F_ROW) + 30);
      w = Math.round(Math.min(340, Math.max(176, w)));
      const h = OHEAD + o.rows.length * ROW + PADB;
      const u = union.get(o.key);
      if (!u) union.set(o.key, { id: o.key, container: o.container, w, h, agg: o.agg });
      else { u.w = Math.max(u.w, w); u.h = Math.max(u.h, h); }
    }
    const links = new Map();
    for (const { links: ls } of per) for (const l of ls) links.set(l.from + ">" + l.to, l);
    return { per, at, nodes: [...union.values()], layoutEdges: [...links.values()] };
  }

  /** What one state changed in the next, for the objects `keep` holds: `"born"`, or the names
   *  of the rows whose value changed. */
  function changesBetween(a, b, keep) {
    const out = new Map();
    for (const [k, o] of keep.objs) {
      const y = b.get(k); if (!y) continue;
      const x = a.get(k);
      if (!x) { out.set(k, "born"); continue; }
      const was = new Map(x.rows.map((r) => [r.name, r.text]));
      const names = new Set(o.rows.map((r) => r.name).filter((n) => { const r = y.rows.find((q) => q.name === n); return r && was.get(n) !== r.text; }));
      if (names.size) out.set(k, names);
    }
    return out;
  }
  /** For each event a step records, the objects it created or changed. Exact when the step
   *  carries the state after each event (`stages`); otherwise each change goes to the last event
   *  recorded by that object's aggregate. */
  function eventChanges(M, f, before, after) {
    const evs = f.ok ? f.events || [] : [];
    if (!evs.length) return [];
    if (evs.length === 1 || (f.stages && f.stages.length === evs.length - 1)) {
      const seq = [before.objs, ...(f.stages || []).map((st) => objectsOf(M, { state: st }).objs), after.objs];
      return evs.map((_, i) => changesBetween(seq[i], seq[i + 1], after));
    }
    const all = changesBetween(before.objs, after.objs, after), out = evs.map(() => new Map());
    const aggs = evs.map((e) => message(M, e, "evt").agg);
    for (const [k, v] of all) {
      const agg = k.split("/")[0], i = aggs.lastIndexOf(agg);
      if (i >= 0) out[i].set(k, v);
    }
    return out;
  }

  /** A command or event, with its arguments named from the model. */
  function message(M, raw, key) {
    const parts = splitArgs(pretty(raw, M.ns));
    const name = (parts[0] || "").split(".").pop();
    const a = M.byPrefix(raw, key);
    const c = a && M.ctor(a[key], name);
    const args = parts.slice(1).map((x, i) => {
      const meta = c && c.args && c.args[i];
      if (meta && /^\d+$/.test(x.trim()) && (meta.name === "cents" || CENTS.test(meta.doc || ""))) x = money(+x);
      return { doc: meta && meta.doc, name: meta && !meta.name.includes("✝") ? argName(meta.name) : c && c.args && c.args.length === 1 ? "value" : `arg ${i + 1}`, text: human(unparen(x)) };
    });
    return { name, agg: a && a.id, args, doc: c && c.doc };
  }

  function MoreNode({ n, count, M, start, open }) {
    const p = n.p;
    return html`<g className="node obj more" transform=${`translate(${p.x} ${p.y})`} style=${{ "--h": M.hue(n.agg) }} tabIndex="0" role="button"
        aria-label=${`Show ${count} more objects in ${(M.agg(n.agg) || {}).name}`}
        onPointerDown=${(e) => start(e, { kind: "node", id: n.id })} onDoubleClick=${open} data-id=${n.id}>
      <rect className="n-body" width=${n.w} height=${n.h} rx="8" />
      <text className="o-title" x="13" y="21">+${count} more in ${(M.agg(n.agg) || {}).name}</text>
      <text className="n-more" x="13" y=${OHEAD + 14}>unchanged in this scenario · click to show</text>
    </g>`;
  }
  function ObjNode({ o, n, M, sel, state, start, changedRows, prevRows, delay = 0 }) {
    const p = n.p, w = n.w, h = OHEAD + o.rows.length * ROW + PADB;
    return html`<g className=${`node obj${o.key === o.agg ? " root" : ""}${sel ? " sel" : ""} ${state || ""}`} transform=${`translate(${p.x} ${p.y})`}
        style=${{ "--h": M.hue(o.agg), "--d": delay + "ms" }} onPointerDown=${(e) => start(e, { kind: "node", id: o.key })} data-id=${o.key}
        tabIndex="0" role="button" aria-label=${objLabel(M, o) + (state === "born" ? ", new" : state === "changed" ? ", changed" : "")}>
      <rect className="n-body" width=${w} height=${h} rx="8" />
      ${o.key === o.agg && html`<path className="n-rootband" d=${`M0,8 a8,8 0 0 1 8,-8 h${w - 16} a8,8 0 0 1 8,8 v-3 h${-w} z`} />`}
      <text className="o-title" x="13" y="21">${(M.types.get(o.typeId) || {}).doc && html`<title>${plain(M.types.get(o.typeId).doc)}</title>`}${clip(objLabel(M, o), F_HEAD, w - 26)}</text>
      <line className="o-rule" x1="0" x2=${w} y1=${OHEAD} y2=${OHEAD} />
      ${o.rows.map((r, i) => {
        const y = OHEAD + i * ROW;
        const ch = changedRows && changedRows.has(r.name);
        const nm = r.name + " = ", val = clip(r.text, F_ROW, w - 26 - tw(nm, F_ROW));
        return html`<g key=${r.name}>
          ${ch && (() => { const wasT = "was " + String(prevRows && prevRows.get(r.name)); return tw(nm + val, F_ROW) + tw(wasT, F_ROW) + 40 < w && html`<text className="o-mark" x=${w - 10} y=${y + 14} textAnchor="end">${wasT}</text>`; })()}
          ${ch && html`<rect className="o-changed" x="3" y=${y + 1} width=${w - 6} height=${ROW - 1} rx="4"><title>was ${prevRows && prevRows.get(r.name)}</title></rect>`}
          <text className="n-row" x="13" y=${y + 14}>${r.doc && html`<title>${r.name}: ${plain(r.doc)}</title>`}<tspan className="o-name">${nm}</tspan><tspan className=${r.children ? "o-kids" : r.ref ? "o-ref" : "o-val"}>${val}</tspan></text></g>`;
      })}
    </g>`;
  }

  /** A process run: its arguments named from the last parameters of its signature. */
  /** A use case a story step calls: its name, its service, and the values it was given. */
  function useCaseMessage(M, frame) {
    const sv = M.service(frame.service.service), u = sv && sv.useCases.find((x) => x.id === frame.service.useCase);
    const vals = splitArgs(pretty(frame.command, M.ns)).slice(1);
    const names = u ? [...u.signature.matchAll(/\(([^():]+?)\s*:/g)].flatMap((m) => m[1].trim().split(/\s+/)) : [];
    const tail = names.slice(Math.max(0, names.length - vals.length));
    return { name: frame.service.useCase, kind: "use case", sub: sv ? sv.name : frame.service.service, doc: u && u.doc,
      args: vals.map((t, i) => ({ name: tail[i] ? argName(tail[i]) : `arg ${i + 1}`, text: human(unparen(t)) })) };
  }
  /** A port call's answer, in short: a DTO's fields as `name = value`, or the error. */
  function callAnswer(M, c) {
    const t = pretty(c.result, M.ns).trim();
    const m = t.match(/^\{(.*)\}$/s);
    if (!m) return [t.split(".").pop()];
    return splitArgs(m[1].replace(/,\s*/g, " , ")).join(" ").split(" , ").map((x) => x.replace(/\s*:=\s*/, " = ").trim()).filter(Boolean);
  }
  const failedOf = (frame) => (typeof frame.result === "string" && frame.result.startsWith("failed: ") ? frame.result.slice(8) : null);
  function procMessage(M, frame) {
    const vals = splitArgs(pretty(frame.command, M.ns)).slice(1);
    const p = M.d.processes.find((x) => x.name === frame.via || x.id === frame.via);
    const names = p ? [...p.signature.matchAll(/\(([^():]+?)\s*:/g)].flatMap((m) => m[1].trim().split(/\s+/)) : [];
    const tail = names.slice(Math.max(0, names.length - vals.length));
    return { name: frame.via, kind: "process", doc: p && p.doc,
      args: vals.map((t, i) => ({ name: tail[i] ? argName(tail[i]) : `arg ${i + 1}`, text: human(unparen(t)) })) };
  }
  function ObjectView({ M, sc, step, phase, playing, sel, setSel, speed, follow, goStep }) {
    const W = useMemo(() => scenarioWorld(M, sc), [M, sc]);
    const conts = useMemo(() => containers(M, false).filter((c) => c.kind !== "shared"), [M]);
    const [view, setView, tween] = useView();
    const [size, setSize] = useState({ w: 0, h: 0 });
    const [hover, setHover] = useState(null);
    const fitted = useRef(false), focusAgg = useRef(null);

    /* The layout grows with the story: each step is laid out with only the objects on the page by
       then, so they stay together instead of leaving room for what comes later. Objects are given
       to ELK in the order they arrived, which keeps each layout close to the one before. */
    const [layouts, setLayouts] = useState(null);
    const relayout = useCallback(async () => {
      const edges = W.layoutEdges.filter((l) => l.kind === "has");
      // the story is mostly about the aggregate its commands target most often
      const hits = new Map();
      for (const f of sc.frames) for (const t of f.targets || []) { const a = t.split("/")[0]; hits.set(a, (hits.get(a) || 0) + 1); }
      const lead = [...hits].sort((a, b) => b[1] - a[1])[0];
      const order = [...W.nodes].sort((a, b) => (W.at.get(a.id) ?? 1e9) - (W.at.get(b.id) ?? 1e9));
      const out = []; let sig = null, last = null;
      for (let i = 0; i < sc.frames.length; i++) {
        const ns = order.filter((n) => W.at.get(n.id) <= i && (W.per[i].objs.has(n.id) || (i > 0 && W.per[i - 1].objs.has(n.id))));
        const ws = ns.map((n) => n.id).join("|");
        // Inside a context, aggregates sit side by side; contexts are placed by `lead` (see layout).
        if (ws !== sig) { last = await layout(ns, edges, conts, { aspect: 60, lead: lead ? lead[0] : "" }); sig = ws; }
        out.push(last);
      }
      fitted.current = false; setLayouts(out);
    }, [W]);
    useEffect(() => { setLayouts(null); relayout(); }, [W]);
    /** Where things are going: this step's layout, or the last step's while the command arrives. */
    const tpos = layouts && layouts[phase === 0 && step > 0 ? step - 1 : step];
    /** Where things are drawn: gliding to `tpos`. */
    const [pos, setPos] = useState(null);
    const posRef = useRef(null); posRef.current = pos;
    useEffect(() => {
      if (!tpos) return;
      const from = posRef.current;
      if (!from || reduced()) { setPos(tpos); return; }
      const t0 = performance.now(), ms = 700 / speed; let raf;
      const tick = (now) => {
        const t = Math.min(1, (now - t0) / ms), e = t < .5 ? 4 * t * t * t : 1 - Math.pow(-2 * t + 2, 3) / 2;
        const p = {};
        for (const k in tpos) { const a = from[k], b = tpos[k]; p[k] = a ? { x: a.x + (b.x - a.x) * e, y: a.y + (b.y - a.y) * e } : b; }
        setPos(p);
        if (t < 1) raf = requestAnimationFrame(tick);
      };
      raf = requestAnimationFrame(tick);
      return () => cancelAnimationFrame(raf);
    }, [tpos]);

    const frame = sc.frames[step];
    const cur = W.per[step], before = step > 0 ? W.per[step - 1] : cur;
    const shown = phase === 0 && step > 0 ? before : cur;
    const nodeOf = useMemo(() => new Map(W.nodes.map((n) => [n.id, n])), [W]);
    const posNode = (k) => { const n = nodeOf.get(k); return n && pos && pos[k] ? { ...n, p: pos[k] } : null; };

    const diff = useMemo(() => {
      const born = new Set(), changed = new Map(), was = new Map();
      if (step === 0) return { born, changed, was, gone: [] };
      for (const [k, o] of cur.objs) {
        const p = before.objs.get(k);
        if (!p) { born.add(k); continue; }
        const pr = new Map(p.rows.map((r) => [r.name, r.text]));
        const ch = new Set(o.rows.filter((r) => pr.get(r.name) !== r.text).map((r) => r.name));
        if (ch.size) { changed.set(k, ch); was.set(k, pr); }
      }
      return { born, changed, was, gone: [...before.objs.keys()].filter((k) => !cur.objs.has(k)) };
    }, [W, step]);

    // the message lane, left of the objects
    const worldOf = (P) => P && bboxOf(W.nodes.map((n) => P[n.id] && { x: P[n.id].x, y: P[n.id].y, w: n.w, h: n.h }));
    const world = useMemo(() => worldOf(pos), [pos, W]);
    /** The command and its events, placed left of what it targets, for positions `P`. */
    const msgsFor = (P) => {
      const world = worldOf(P), pos = P;
      const posNode = (k) => { const n = nodeOf.get(k); return n && P && P[k] ? { ...n, p: P[k] } : null; };
      if (!world || !frame || frame.start) return null;
      const roots = frame.targets.map((t) => posNode(t)).filter(Boolean);
      const cy = roots.length ? Math.min(...roots.map((r) => r.p.y)) + 10 : world.y + 40;
      const tf = frames(conts, W.nodes.filter((n) => pos[n.id]).map((n) => ({ ...n, p: pos[n.id] })), pos).find((f) => roots[0] && f.id === "agg:" + roots[0].agg);
      const clock = frame.actor === "clock";
      const cmd = clock ? { name: frame.note, kind: "clock", args: [] }
        : frame.service ? useCaseMessage(M, frame)
        : frame.via ? procMessage(M, frame)
        : { ...message(M, frame.command, "cmd"), kind: "command" };
      const cw = Math.round(Math.min(360, Math.max(240, tw(cmd.name, F_HEAD) + 40, ...cmd.args.map((a) => tw(`${a.name} = ${a.text}`, F_ROW) + 30))));
      const ch = HEAD + Math.max(clock ? 0 : 1, cmd.args.length) * ROW + (clock ? 6 : 36);
      const x = (tf ? tf.x : world.x) - cw - 70;
      const cbox = { x, y: cy, w: cw, h: ch };
      let ey = cbox.y + ch + 34;
      const evts = (frame.ok ? frame.events : []).map((e) => {
        const m = message(M, e, "evt");
        const shownArgs = m.args.slice(0, 4);
        const w = cw; // the command's width: events stack under it, clear of the aggregate's frame
        const h = HEAD + shownArgs.length * ROW + PADB;
        const b = { ...m, shownArgs, x, y: ey, w, h };
        ey += h + 12;
        return b;
      });
      for (const e of evts) e.x = x;
      // A use case's calls through its ports: outside the domain, left of the use case.
      const CW = 300;
      let qy = cbox.y;
      const calls = (frame.calls || []).map((c, i) => {
        const p = M.port(c.port), sys = p && p.system && M.system(p.system);
        const rows = callAnswer(M, c).slice(0, 4);
        const h = HEAD + (rows.length + 1) * ROW + PADB;
        const b = { ...c, i, sys: sys ? sys.name : "", rows, x: x - CW - 60, y: qy, w: CW, h };
        qy += h + 12;
        return b;
      });
      const lane = bboxOf([cbox, ...calls]);
      // What came before stays in the lane, faded, newest nearest: click one to go back to it.
      const PAST = 10, older = Math.max(0, step - 1 - PAST);
      const past = [];
      let py = cbox.y - 18;
      for (let i = step - 1; i >= 1 && i > older; i--) {
        const f = sc.frames[i];
        const name = f.actor === "clock" ? f.note : f.service ? f.service.useCase : f.via || message(M, f.command, "cmd").name;
        const evNames = f.ok ? (f.events || []).map((e) => message(M, e, "evt").name) : [];
        const shownEv = evNames.slice(0, 3);
        const h = 26 + (shownEv.length + (evNames.length > 3 ? 1 : 0)) * 15 + (shownEv.length ? 4 : 0);
        py -= h;
        past.push({ i, name, ok: f.ok, clock: f.actor === "clock", evNames, shownEv, x, y: py, w: cw, h, agg: (f.targets || [])[0] });
        py -= 8;
      }
      return { cmd, cbox, lane, calls, roots, evts, clock, past, older, olderY: py - 22 };
    };
    const msgs = useMemo(() => msgsFor(pos), [world, W, step, pos]);

    /** Where the camera should be for this step: the command, its target and what changed, never smaller than readable. */
    /** The part of the canvas the story's caption leaves free. */
    const tellRef = useRef(null);
    const stage = () => { const t = tellRef.current; const top = t ? t.offsetTop + t.offsetHeight + 8 : 0; return { top, w: size.w, h: Math.max(200, size.h - top - 56) }; };
    const fitIn = (box, maxK, pad) => { const st = stage(); const f = fitView(box, { w: st.w, h: st.h }, maxK, pad); return { ...f, y: f.y + st.top }; };
    const shot = (P = tpos || pos) => {
      const msgs = msgsFor(P), pos = P;
      const posNode = (k) => { const n = nodeOf.get(k); return n && P && P[k] ? { ...n, p: P[k] } : null; };
      if (!msgs) {
        const vis = W.nodes.filter((n) => pos[n.id] && W.at.get(n.id) <= step && sc.frames[step] && W.per[step].objs.has(n.id)).map((n) => ({ x: pos[n.id].x, y: pos[n.id].y, w: n.w, h: n.h }));
        return vis.length ? fitIn(bboxOf(vis), 1, 80) : { k: 1, x: size.w / 2, y: stage().top + 80 };
      }
      const entered = W.nodes.filter((n) => W.at.get(n.id) === step).map((n) => n.id);
      const noted = (frame.notes || []).map((x) => x.at);
      if (noted.length) {
        // A story step: what the notes are about must be readable; the command comes along if it fits.
        const nb = noted.map(posNode).filter(Boolean).map((n) => ({ x: n.p.x, y: n.p.y, w: n.w + 300, h: Math.min(n.h, 240) }));
        const eb = entered.map(posNode).filter(Boolean).map((n) => ({ x: n.p.x, y: n.p.y, w: n.w, h: Math.min(n.h, 240) }));
        const rb = msgs.roots.map((r) => ({ x: r.p.x, y: r.p.y, w: r.w, h: Math.min(r.h, 200) }));
        for (const set of [[msgs.lane, ...rb, ...nb, ...eb], [msgs.lane, ...nb], [...rb, ...nb], nb]) {
          if (!set.length) continue;
          const f = fitIn(bboxOf(set), 1, 48);
          if (f.k >= 0.62) return f;
        }
        const first = posNode(noted[0]);
        if (first) {
          const fb = { x: first.p.x, y: first.p.y, w: first.w + 300, h: Math.min(first.h, 320) };
          for (const set of [[msgs.lane, fb], [fb]]) { const f = fitIn(bboxOf(set), 1, 48); if (f.k >= 0.62) return f; }
          const st = stage(), k = 0.75;
          return { k, x: st.w / 2 - (fb.x + fb.w / 2) * k, y: st.top + 40 - fb.y * k };
        }
      }
      const boxes = [msgs.lane, ...msgs.roots.map((r) => ({ x: r.p.x, y: r.p.y, w: r.w, h: Math.min(r.h, 260) })), ...msgs.evts.slice(0, 3)];
      for (const k of [...new Set([...noted, ...diff.born, ...diff.changed.keys(), ...entered])].slice(0, 8)) {
        const n = posNode(k); if (n) boxes.push({ x: n.p.x, y: n.p.y, w: n.w + (noted.includes(k) ? 300 / Math.max(view.k, 0.5) : 0), h: Math.min(n.h, 200) });
      }
      const b = bboxOf(boxes);
      const f = fitIn(b, 1, 56);
      if (f.k >= 0.72) return f;
      if (msgs.roots.length > 1) {
        // a process: all its aggregates in view matters more than reading every row
        const all = fitIn(bboxOf([msgs.lane, ...msgs.roots.map((r) => ({ x: r.p.x, y: r.p.y, w: r.w, h: Math.min(r.h, 160) }))]), 1, 56);
        if (all.k >= 0.42) return all;
      }
      const core = bboxOf(boxes.slice(0, 1 + msgs.roots.length));
      const k = Math.min(1, Math.max(0.72, fitIn(core, 1, 56).k));
      return { k, x: 48 - core.x * k, y: stage().top + 40 - core.y * k };
    };
    const inView = (b) => b.x * view.k + view.x >= 0 && b.y * view.k + view.y >= stage().top && (b.x + b.w) * view.k + view.x <= size.w && (b.y + b.h) * view.k + view.y <= size.h;
    useEffect(() => {
      if (!tpos || !size.w || fitted.current) return;
      fitted.current = true;
      setView(shot(tpos));
    }, [tpos, size.w]);
    useEffect(() => {
      if (!follow || !tpos || !size.w || !fitted.current) return;
      const m = msgsFor(tpos);
      if (m && phase === 0 && inView(bboxOf([m.lane, ...m.roots.map((r) => ({ x: r.p.x, y: r.p.y, w: r.w, h: Math.min(r.h, 200) }))]))) return;
      tween(shot(tpos), 700 / speed);
    }, [tpos, follow, step, phase]);

    const centre = hover || sel;
    const focus = useMemo(() => {
      if (!centre || !shown.objs.has(centre)) return null;
      const s = new Set([centre]);
      for (const l of shown.links) { if (l.from === centre) s.add(l.to); if (l.to === centre) s.add(l.from); }
      return s;
    }, [centre, shown]);

    // aggregates this step touches that are out of view: a pointer at the canvas edge for each
    const offscreen = useMemo(() => {
      if (!pos || !size.w || !frame || frame.start) return [];
      const touched = new Map();
      for (const t of frame.targets || []) touched.set(t, "");
      if (phase === 1) for (const k of [...diff.born, ...diff.changed.keys()]) { const a = k.split("/")[0]; touched.set(a, "changed"); }
      const out = [];
      for (const [agg, what] of touched) {
        const n = posNode(agg);
        if (!n) continue;
        const box = { x: n.p.x, y: n.p.y, w: n.w, h: Math.min(n.h, 240) };
        const sx = box.x * view.k + view.x, sy = box.y * view.k + view.y, sw = box.w * view.k, sh = box.h * view.k;
        if (sx + sw > 0 && sx < size.w && sy + sh > 0 && sy < size.h) continue;
        const cx = sx + sw / 2, cy = sy + sh / 2, dx = cx - size.w / 2, dy = cy - size.h / 2;
        const arrow = Math.abs(dx) > Math.abs(dy) ? (dx > 0 ? "→" : "←") : dy > 0 ? "↓" : "↑";
        const x = Math.max(16, Math.min(size.w - 200, cx - 70)), y = Math.max(stage().top + 8, Math.min(size.h - 110, cy - 14));
        out.push({ agg, name: (M.agg(agg) || {}).name || agg, what, arrow, x, y, box });
      }
      return out;
    }, [pos, size, view, step, phase]);

    if (!pos) return html`<div className="loading">Laying out the objects…</div>`;
    const upTo = phase === 0 && step > 0 ? step - 1 : step;
    const onPage = (k) => W.at.has(k) && W.at.get(k) <= upTo;
    const visible = W.nodes.filter((n) => shown.objs.has(n.id) && onPage(n.id) && pos[n.id]).map((n) => ({ ...n, p: pos[n.id] }));
    const open = () => {};
    const linkLayer = html`<g className="edges">${shown.links.map((l, i) => {
      const a = posNode(l.from), b = posNode(l.to);
      if (!a || !b || !onPage(l.from) || !onPage(l.to)) return null;
      const oa = shown.objs.get(l.from);
      const ay = a.p.y + OHEAD + l.row * ROW + ROW / 2 - 1;
      const g = edgePath({ x: a.p.x, y: a.p.y, w: a.w, h: a.h }, ay, { x: b.p.x, y: b.p.y, w: b.w, h: b.h }, b.p.y + 16);
      const hot = !!centre && (l.from === centre || l.to === centre);
      const fresh = phase === 1 && (diff.born.has(l.to) || (diff.changed.has(l.from) && diff.changed.get(l.from).has(oa.rows[l.row].name)));
      return html`<g key=${i} className=${`edge ${l.kind === "has" ? "e-has" : "e-link"}${hot ? " hot" : ""}${focus && !hot ? " dim" : ""}${fresh ? " fresh" : ""}`}>
        <path d=${g.d} pathLength="1" markerEnd=${l.kind === "has" ? null : "url(#end-link)"} markerStart=${l.kind === "has" ? "url(#start-has)" : null} /></g>`;
    })}</g>`;

    const flows = phase === 1 && msgs ? (cur.byEvent || []).flatMap((chg, i) => {
      const e = msgs.evts[i]; if (!e) return [];
      return [...chg].filter(([k]) => onPage(k)).slice(0, 8).map(([k, what]) => {
        const n = posNode(k); if (!n) return null;
        const o = cur.objs.get(k);
        const rows = what === "born" || !o ? [] : o.rows.map((r, j) => (what.has(r.name) ? j : -1)).filter((j) => j >= 0);
        const ty = rows.length ? n.p.y + OHEAD + rows[0] * ROW + ROW / 2 : n.p.y + 16;
        const g = edgePath({ x: e.x, y: e.y, w: e.w, h: e.h }, e.y + e.h / 2, { x: n.p.x, y: n.p.y, w: n.w, h: n.h }, ty);
        return { key: i + ">" + k, d: g.d, agg: e.agg, i, label: `${e.name} ${what === "born" ? "creates" : "changes"} ${objLabel(M, o || { key: k, typeId: "" })}${rows.length ? ": " + rows.map((j) => o.rows[j].name).join(", ") : ""}` };
      }).filter(Boolean);
    }) : [];
    const pastLayer = msgs && msgs.past.length > 0 && html`<g className="past">
      ${msgs.older > 0 && html`<text className="past-more" x=${msgs.cbox.x + 4} y=${msgs.olderY + 14}>+${plural(msgs.older, "earlier step")}</text>`}
      ${msgs.past.map((p) => html`<g key=${"p" + p.i} className=${"past-card" + (p.ok ? "" : " refused") + (p.clock ? " clock" : "")} transform=${`translate(${p.x} ${p.y})`}
          style=${{ "--h": M.hue(p.agg) }} role="button" tabIndex="0" aria-label=${`Go back to step ${p.i}: ${p.name}`}
          onPointerDown=${(e) => { e.stopPropagation(); goStep && goStep(p.i); }}
          onKeyDown=${(e) => { if (e.key === "Enter" || e.key === " ") { e.preventDefault(); e.stopPropagation(); goStep && goStep(p.i); } }}>
        <title>Step ${p.i}: ${p.name}${p.ok ? (p.evNames.length ? " → " + p.evNames.join(", ") : "") : " (refused)"}. Click to go back to it.</title>
        <rect className="n-body" width=${p.w} height=${p.h} rx="7" />
        <text className="past-head" x="10" y="17"><tspan className="past-n">${p.i}</tspan>  ${clip(p.name, F_ROW, p.w - 70)}<tspan className="past-mark">  ${p.clock ? "" : p.ok ? "✓" : "✕"}</tspan></text>
        ${p.shownEv.map((n, j) => html`<text key=${j} className="past-ev" x="22" y=${33 + j * 15}>→ ${clip(n, F_ROW, p.w - 40)}</text>`)}
        ${p.evNames.length > 3 && html`<text className="past-ev" x="22" y=${33 + 3 * 15}>+${p.evNames.length - 3} more</text>`}
      </g>`)}</g>`;
    const overlay = msgs && html`<g className="msgs" key=${sc.id + ":" + step}>
      ${pastLayer}
      ${flows.map((fl) => html`<path key=${"f" + fl.key} className="m-flow" d=${fl.d} pathLength="1" markerEnd="url(#end-flow)"
          style=${{ "--h": M.hue(fl.agg), animationDelay: (260 + fl.i * 90) / speed + "ms" }}><title>${fl.label}</title></path>`)}
      ${msgs.calls.map((c) => {
        const g = edgePath(msgs.cbox, msgs.cbox.y + 22 + c.i * 6, c, c.y + 22);
        return html`<g key=${"c" + c.i} className=${"call-card" + (c.ok ? "" : " bad")} style=${{ animationDelay: (120 + c.i * 140) / speed + "ms" }}>
          <path className="m-call" d=${g.d} pathLength="1" markerEnd="url(#end-call)" />
          <g transform=${`translate(${c.x} ${c.y})`}>
            <title>${c.port}.${c.op}(${c.args}) answered ${c.result}</title>
            <rect className="n-body" width=${c.w} height=${c.h} rx="9" />
            <text className="n-stereo" x="14" y="17">«port» ${c.port}${c.sys ? " → " + c.sys : ""}</text>
            <text className="n-title" x="14" y="35">${clip(`${c.op}(${c.args})`, F_HEAD, c.w - 28)}</text>
            <text className="n-row c-verdict" x="14" y=${HEAD + 14}>${c.ok ? "answered" : "✕ failed"}</text>
            ${c.rows.map((r, j) => html`<text key=${j} className="n-row" x="22" y=${HEAD + (j + 1) * ROW + 14}><tspan className="o-val">${clip(r, F_ROW, c.w - 36)}</tspan></text>`)}
          </g></g>`;
      })}
      ${!msgs.clock && !(phase === 1 && failedOf(frame)) && msgs.roots.map((r, i) => {
        const g = edgePath(msgs.cbox, msgs.cbox.y + 22, { x: r.p.x, y: r.p.y, w: r.w, h: r.h }, r.p.y + 16);
        return html`<path key=${"a" + i} className=${"m-arrow" + (phase === 1 && !frame.ok ? " bad" : "")} d=${g.d} pathLength="1"
          markerEnd=${`url(#end-${phase === 1 && !frame.ok ? "refuse" : "cmd"})`} style=${{ animationDuration: 560 / speed + "ms" }} />`;
      })}
      <g className=${"msg m-" + msgs.cmd.kind.replace(" ", "") + (phase === 1 && !frame.ok ? " refused" : "")} transform=${`translate(${msgs.cbox.x} ${msgs.cbox.y})`}>
        <rect className="n-body" width=${msgs.cbox.w} height=${msgs.cbox.h} rx="9" />
        <text className="n-stereo" x="14" y="17">«${msgs.cmd.kind}»${msgs.cmd.sub ? " of " + msgs.cmd.sub : ""}${frame.actor && !msgs.clock ? " from " + frame.actor : ""}</text>
        <text className="n-title" x="14" y="35">${clip(msgs.cmd.name, F_HEAD, msgs.cbox.w - 28)}</text>
        ${msgs.cmd.args.map((a, i) => html`<text key=${i} className="n-row" x="14" y=${HEAD + i * ROW + 14}>
          <tspan className="o-name">${a.name} = </tspan><tspan className="o-val">${clip(a.text, F_ROW, msgs.cbox.w - 28 - tw(a.name + " = ", F_ROW))}</tspan></text>`)}
        ${!msgs.cmd.args.length && !msgs.clock && html`<text className="n-more" x="14" y=${HEAD + 14}>no arguments</text>`}
        ${phase === 1 && !msgs.clock && html`<g className=${"verdict-chip " + (frame.ok ? "ok" : "bad")} transform=${`translate(8 ${msgs.cbox.h - 31})`}>
          <rect width=${msgs.cbox.w - 16} height="23" rx="6" />
          <text x="10" y="16">${frame.ok ? "✓ accepted" : failedOf(frame) ? "✕ failed" : "✕ refused"}${failedOf(frame) ? html`<tspan className="why">  ${clip(failedOf(frame), F_ROW, msgs.cbox.w - 110)}<title>Nothing was decided or saved: the domain was never asked.</title></tspan>` : null}${frame.ok && (frame.findings || []).length ? html`<tspan className="warn">  ⚠ ${plural(frame.findings.length, "warning")}</tspan>` : null}${!frame.ok && !failedOf(frame) && reason(frame.error, M.ns, M, frame.targets) ? html`<tspan className="why">  ${clip(reason(frame.error, M.ns, M, frame.targets), F_ROW, msgs.cbox.w - 120)}</tspan>` : null}</text></g>`}
      </g>
      ${phase === 1 && msgs.evts.map((e, i) => {
        const root = posNode(e.agg);
        const g = root && edgePath({ x: root.p.x, y: root.p.y, w: root.w, h: root.h }, root.p.y + 16, e, e.y + 22);
        return html`<g key=${"ev" + i} className="ev" style=${{ animationDelay: (i * 90) / speed + "ms", "--h": M.hue(e.agg) }}>
          ${g && html`<path className="m-evt" d=${g.d} pathLength="1" markerEnd="url(#end-evt)" />`}
          <g transform=${`translate(${e.x} ${e.y})`}>
            <rect className="n-body ev-body" width=${e.w} height=${e.h} rx="9" />
            <text className="n-stereo" x="14" y="17">«event» recorded by ${(M.agg(e.agg) || {}).name || "?"}</text>
            ${e.args.length > e.shownArgs.length && html`<text className="n-more" x="14" y=${e.h - 4}>+${e.args.length - e.shownArgs.length} more</text>`}
            <text className="n-title" x="14" y="35">${e.name}</text>
            ${e.shownArgs.map((a, j) => html`<text key=${j} className="n-row" x="14" y=${HEAD + j * ROW + 14}><tspan className="o-name">${a.name} = </tspan><tspan className="o-val">${clip(a.text, F_ROW, e.w - 28 - tw(a.name + " = ", F_ROW))}</tspan></text>`)}
          </g></g>`;
      })}
    </g>`;

    /** Where each note goes: beside its object where it covers nothing, otherwise docked under
     *  the caption (also when its object is off screen), or flagged when there is no such object. */
    const notes = (() => {
      if (!(phase === 1 || frame.start)) return [];
      const scr = (b) => ({ x: b.x * view.k + view.x, y: b.y * view.k + view.y, w: b.w * view.k, h: b.h * view.k });
      const taken = visible.map((n) => scr({ x: n.p.x, y: n.p.y, w: n.w, h: n.h }));
      if (msgs) taken.push(scr(msgs.cbox), ...msgs.calls.map(scr), ...msgs.evts.map(scr));
      const t = tellRef.current; if (t) taken.push({ x: t.offsetLeft, y: t.offsetTop, w: t.offsetWidth, h: t.offsetHeight });
      const hit = (r) => taken.some((o) => r.x < o.x + o.w && o.x < r.x + r.w && r.y < o.y + o.h && o.y < r.y + r.h);
      const inside = (r) => r.x >= 8 && r.y >= stage().top && r.x + r.w <= size.w - 8 && r.y + r.h <= size.h - 64;
      const W0 = 270, H0 = 88, G = 18;
      return (frame.notes || []).map((x, i) => {
        const n = posNode(x.at);
        if (!n) return { ...x, i, dock: true };
        if (!onPage(x.at)) return null;
        const o = W.per[step].objs.get(x.at);
        const base = { ...x, i, n, label: o ? objLabel(M, o) : x.at };
        const b = scr({ x: n.p.x, y: n.p.y, w: n.w, h: Math.min(n.h, 220) });
        if (b.x > size.w || b.y > size.h || b.x + b.w < 0 || b.y + b.h < 0 || b.y + 20 < stage().top) return { ...base, dock: true };
        const cands = [];
        for (let dy = 0; dy <= 2; dy++) cands.push({ side: "r", x: b.x + b.w + G, y: b.y + 6 + dy * (H0 + 10) }, { side: "l", x: b.x - G - W0, y: b.y + 6 + dy * (H0 + 10) });
        cands.push({ side: "b", x: b.x, y: b.y + b.h + G }, { side: "t", x: b.x, y: b.y - G - H0 });
        const pick = cands.map((c) => ({ ...c, w: W0, h: H0 })).find((c) => inside(c) && !hit(c));
        if (!pick) return { ...base, dock: true };
        taken.push(pick);
        return { ...base, pin: pick };
      }).filter(Boolean);
    })();
    return html`<div className="stage" onPointerOver=${(e) => { const g = e.target.closest && e.target.closest("[data-id]"); setHover(g ? g.getAttribute("data-id") : null); }} onPointerLeave=${() => setHover(null)}>
      <${Canvas} nodes=${visible} conts=${conts} pos=${pos} setPos=${setPos} view=${view} setView=${setView} onSize=${setSize}
        label=${`Object diagram: ${sc.title}, step ${step}`}
        onBackground=${() => setSel(null)} onNodeClick=${(id) => (id.startsWith("more:") ? open(id.slice(5)) : setSel(id))}
        onFrameClick=${(id) => { const f = frames(conts, visible, pos).find((x) => x.id === id); if (f) tween(fitView(f, size, 1.2)); }}
        edgeLayer=${linkLayer} overlay=${overlay} map=${false}
        nodeLayer=${(start) => [
          ...(phase === 1 ? diff.gone.filter(onPage).map((k) => { const n = posNode(k); return n && html`<${ObjNode} key=${"gone:" + k} o=${before.objs.get(k)} n=${n} M=${M} state="gone" start=${start} />`; }) : []),
          ...visible.map((n) => {
            if (n.more) return html`<${MoreNode} key=${n.id} n=${n} count=${shown.more.get(n.agg)} M=${M} start=${start} open=${() => open(n.agg)} />`;
            const o = shown.objs.get(n.id);
            const entering = phase === 1 && W.at.get(n.id) === step && step > 0;
            const st = (phase === 1 && diff.born.has(n.id) ? "born" : phase === 1 && diff.changed.has(n.id) ? "changed" : focus && !focus.has(n.id) ? "dim" : "") + (entering ? " enter" : "");
            // a new object fades in once the others have made room for it
            const glides = layouts && step > 0 && layouts[step] !== layouts[step - 1];
            return html`<${ObjNode} key=${n.id} o=${o} n=${n} M=${M} sel=${sel === n.id} state=${st} start=${start} delay=${entering && glides ? Math.round(620 / speed) : 0}
              changedRows=${phase === 1 ? diff.changed.get(n.id) : null} prevRows=${diff.was.get(n.id)} />`;
          })]} />
      <${ZoomBar} setView=${setView} size=${size} fit=${() => tween(fitView(bboxOf([world, msgs && msgs.lane, ...(msgs ? msgs.evts : [])]), size, 1))} tidy=${() => relayout()} />
      <div className="tell" ref=${tellRef}>
        <${WorldFacts} sc=${sc} step=${step} />
        <div className="caption" key=${sc.id + ":" + step}>
          <div className="cap-head">${frame.start ? sc.title : html`<span className="n">${step}</span>${frame.note}`}</div>
          ${(frame.say || (frame.start ? sc.doc : "")) && html`<${Doc} text=${frame.say || sc.doc} className="cap-say" />`}
          ${frame.start && !visible.length && !playing && html`<p className="cap-hint">Press → to start, or Play.</p>`}
          ${playing && step < sc.frames.length - 1 && html`<div className="cap-timer" key=${"t" + step} style=${{ animationDuration: dwell(frame) / speed + "ms" }} />`}
        </div>
        ${notes.filter((x) => x.dock).map((x) => x.n
          ? html`<button key=${"dock" + x.i} className="callout docked" style=${{ "--h": M.hue(x.n.agg), animationDelay: (180 + x.i * 140) / speed + "ms" }}
              onClick=${() => { const b = { x: x.n.p.x, y: x.n.p.y, w: x.n.w + 300, h: Math.min(x.n.h, 320) }; const f = fitIn(b, 1, 48); tween({ ...f, k: Math.max(0.72, f.k) }); }}>
              <span className="dock-at">↗ ${x.label}</span><${Doc} text=${x.text} className="callout-text" /></button>`
          : html`<div key=${"miss" + x.i} className="callout docked missing"><span className="dock-at">⚠ No object "${x.at}" at this step</span><${Doc} text=${x.text} className="callout-text" /></div>`)}
      </div>
      ${notes.filter((x) => x.pin).map((x) => html`<div key=${"note" + x.i} className=${"callout " + x.pin.side} style=${{ left: x.pin.x + "px", top: x.pin.y + "px", "--h": M.hue(x.n.agg), animationDelay: (180 + x.i * 140) / speed + "ms" }}>
            <${Doc} text=${x.text} className="callout-text" /></div>`)}
      ${offscreen.map((h) => html`<button key=${h.agg} className="offscreen" style=${{ left: h.x + "px", top: h.y + "px", "--h": M.hue(h.agg) }}
          onClick=${() => tween({ ...fitView(h.box, size, 1, 56), k: Math.max(0.72, Math.min(1, fitView(h.box, size, 1, 56).k)) })}
          aria-label=${`Show ${h.name}, off screen`}><span className="arrow">${h.arrow}</span> ${h.name}${h.what ? html`<span className="what"> · ${h.what}</span>` : null}</button>`)}
      <div className="legend"><span><svg width="30" height="10"><path d="M2,5 H28" className="edge e-has" markerStart="url(#start-has)" /></svg>contains</span>
        <span><svg width="30" height="10"><path d="M2,5 H26" className="edge e-link" markerEnd="url(#end-link)" /></svg>refers to, by id</span>
        <span><svg width="30" height="10"><path d="M2,5 H26" className="m-flow still" markerEnd="url(#end-flow)" /></svg>event changes</span>
        <span><i className="sw born" />new</span><span><i className="sw changed" />changed</span></div>
    </div>`;
  }

  /* ================= inspector ================= */
  /** A term's definition, from its doc comment; if there is none, where to write it. */
  function Def({ doc, decl, className }) {
    if (doc) return html`<${Doc} text=${doc} className=${className} />`;
    return html`<p className=${"nodef " + (className || "")}>No definition yet. Add a <code>/-- … -/</code> comment to <code>${decl}</code> in Lean.</p>`;
  }
  function TypeRef({ id, M, go }) {
    const t = M.types.get(id);
    if (!t) return null;
    return html`<button className="tref" style=${{ "--h": M.typeHue(t) }} onClick=${() => go.type(id)}>${t.name}</button>`;
  }
  function Theorem({ t, M }) {
    const h = t.about && t.about.length === 1 ? M.hue(t.about[0]) : "var(--focus)";
    return html`<div className="thm" style=${{ "--h": h }}>
      <div className="tn"><span className="q">∎</span>${t.name}</div>
      <${Doc} text=${t.doc} className="" />
      <pre className="sig">${t.signature}</pre></div>`;
  }
  function TypeDetail({ id, M, go }) {
    if (id && id.startsWith("proc:")) return html`<${ProcDetail} p=${M.proc(id.slice(5))} M=${M} />`;
    if (id && id.startsWith("svc:")) return html`<${ServiceDetail} sv=${M.service(id.slice(4))} M=${M} go=${go} />`;
    if (id && (id.startsWith("port:") || id.startsWith("acl:"))) return html`<${PortDetail} p=${M.port(id.slice(id.indexOf(":") + 1))} M=${M} go=${go} />`;
    if (id && id.startsWith("sysnode:")) return html`<${SystemDetail} x=${M.system(id.slice(8))} M=${M} go=${go} />`;
    const t = M.types.get(id);
    if (!t) return html`<p className="doc">Nothing selected.</p>`;
    const k = M.kind(t), a = M.aggs.find((x) => x.state === t.id);
    const used = M.d.types.filter((u) => u.id !== t.id && (u.edges || []).some((e) => e.to === t.id));
    const fs = M.fields(t);
    const thms = a ? M.d.theorems.filter((x) => x.about.includes(a.id)) : [];
    const plc = M.place.get(t.id) || { level: "shared" };
    const where = plc.level === "agg" ? `in the ${M.agg(plc.id).name} aggregate` : plc.level === "ctx" ? `in ${(M.contexts.find((c) => c.id === plc.id) || {}).title}` : "shared";
    return html`<div style=${{ "--h": M.typeHue(t) }}>
      <p className="kicker"><span className="swatch" />«${STEREO[k] || k}» ${where}</p>
      <h2 className="mono-title">${t.name}</h2>
      <${Def} doc=${t.doc || (a && a.doc)} decl=${t.id} />
      ${M.identifies.has(t.id) && html`<p className="doc">The identity of <${TypeRef} id=${M.identifies.get(t.id)} M=${M} go=${go} />. Other aggregates hold this id, never the entity itself.</p>`}
      ${a && a.invariants.length > 0 && html`<h3>Always true <span className="n">${a.invariants.length}</span></h3>${a.invariants.map((x) => html`<${Theorem} key=${x.name} t=${{ ...x, about: [a.id] }} M=${M} />`)}`}
      ${fs.length > 0 && html`<h3>Fields <span className="n">${fs.length}</span></h3>
        <div className="rows">${fs.map((f) => { const g = M.target(f); return html`<div className="row" key=${f.name}>
          <div className="head"><span className="name">${f.name}</span><span className="ty">${f.type}</span>
            ${g && M.types.has(M.identifies.get(g.id) || g.id) && html`<${TypeRef} id=${M.identifies.get(g.id) || g.id} M=${M} go=${go} />`}
            ${f.from && html`<span className="badge">from ${f.from}</span>`}</div>
          <${Def} doc=${f.doc} decl=${(f.from ? f.from : t.id) + "." + f.name} className="d" /></div>`; })}</div>`}
      ${t.ctors && html`<h3>${k === "command" ? "Commands" : k === "event" ? "Events" : k === "rejection" ? "Reasons" : "Cases"} <span className="n">${t.ctors.length}</span></h3>
        <div className="rows">${t.ctors.map((c) => html`<div className="row" key=${c.name}>
          <div className="head"><span className="name">${c.name}</span><span className="ty">${(c.args || []).map(argText).join(", ")}</span></div>
          <${Def} doc=${c.doc} decl=${t.id + "." + c.name} className="d" /></div>`)}</div>`}
      ${used.length > 0 && html`<h3>Used by <span className="n">${used.length}</span></h3><div className="pills">${used.map((u) => html`<${TypeRef} key=${u.id} id=${u.id} M=${M} go=${go} />`)}</div>`}
      ${thms.length > 0 && html`<h3>Theorems about it <span className="n">${thms.length}</span></h3>${thms.map((x) => html`<${Theorem} key=${x.name} t=${x} M=${M} />`)}`}
    </div>`;
  }
  function ProcDetail({ p, M }) {
    if (!p) return null;
    const thms = M.d.theorems.filter((t) => t.processes.includes(p.id));
    return html`<div>
      <p className="kicker">«process» changes ${p.touches.map((t) => (M.agg(t) || {}).name).join(" and ")} together, or nothing at all</p>
      <h2 className="mono-title">${p.name}</h2>
      <${Doc} text=${p.doc} />
      <h3>Signature</h3><pre className="sig" style=${{ maxHeight: "none" }}>${p.signature}</pre>
      ${thms.length > 0 && html`<h3>Proved about it <span className="n">${thms.length}</span></h3>${thms.map((t) => html`<${Theorem} key=${t.name} t=${t} M=${M} />`)}`}
    </div>`;
  }
  /** Every term of the model with its definition: the ubiquitous language, read from the doc comments. */
  function Glossary({ M, go }) {
    const [q, setQ] = useState("");
    const [open, setOpen] = useState(false);
    const terms = useMemo(() => M.d.types.filter((t) => !["command", "event", "rejection"].includes(M.kind(t)))
      .map((t) => ({ id: t.id, name: t.name, doc: t.doc, kind: M.kind(t), hue: M.typeHue(t) }))
      .sort((a, b) => a.name.localeCompare(b.name)), [M]);
    const done = terms.filter((t) => t.doc).length;
    const shown = terms.filter((t) => !q || (t.name + " " + (t.doc || "")).toLowerCase().includes(q.toLowerCase()));
    return html`<h3>Glossary <span className="n">${done} of ${terms.length} defined</span></h3>
      <input className="gl-q" placeholder="Find a term" value=${q} onInput=${(e) => { setQ(e.target.value); setOpen(true); }} />
      <dl className="glossary">${(open || q ? shown : shown.slice(0, 8)).map((t) => html`<div key=${t.id} style=${{ "--h": t.hue }}>
        <dt><button className="tref" onClick=${() => go.type(t.id)}>${t.name}</button><span className="gk">${STEREO[t.kind] || t.kind}</span></dt>
        <dd>${t.doc ? plain(t.doc) : html`<span className="nodef">No definition yet</span>`}</dd></div>`)}</dl>
      ${!open && !q && shown.length > 8 && html`<button className="pill" onClick=${() => setOpen(true)}>Show all ${shown.length} terms</button>`}`;
  }
  /** Type names in a signature, as links where they are types of the model. */
  function Linked({ text, M, go }) {
    const byName = new Map(M.d.types.map((t) => [t.name.split(".").pop(), t.id]));
    const parts = String(text).split(/([A-Za-z_][\w.]*)/);
    return html`<span>${parts.map((x, i) => (byName.has(x.split(".").pop()) && /^[A-Z]/.test(x)
      ? html`<button key=${i} className="tlink" onClick=${() => go.type(byName.get(x.split(".").pop()))}>${x}</button>` : x))}</span>`;
  }
  function PortRef({ id, M, go }) {
    const p = M.port(id);
    return html`<button className="tref port-ref" onClick=${() => go.type("port:" + id)}>${p ? p.name.split(".").pop() : id}</button>`;
  }
  function ServiceDetail({ sv, M, go }) {
    if (!sv) return null;
    return html`<div>
      <p className="kicker">«application service» ${plural(sv.useCases.length, "use case")}, each one transaction</p>
      <h2 className="mono-title">${sv.name}</h2>
      <${Doc} text=${sv.doc} />
      <h3>Ports <span className="n">${sv.ports.length}</span></h3>
      <div className="pills">${sv.ports.length ? sv.ports.map((p) => html`<${PortRef} key=${p} id=${p} M=${M} go=${go} />`) : html`<span className="doc small">It asks no one outside.</span>`}</div>
      <h3>Use cases <span className="n">${sv.useCases.length}</span></h3>
      ${sv.useCases.map((u) => html`<div key=${u.id} className="usecase">
        <div className="uc-head"><b className="mono">${u.id}</b>
          ${u.changes.map((a) => M.agg(a) && html`<${TypeRef} key=${a} id=${M.agg(a).state} M=${M} go=${go} />`)}</div>
        <${Doc} text=${u.doc} className="small" />
        <div className="uc-asks">${u.asks.length ? html`asks ${u.asks.map((p) => html`<${PortRef} key=${p} id=${p} M=${M} go=${go} />`)}` : "asks no one outside"}</div>
        <pre className="sig"><${Linked} text=${u.signature} M=${M} go=${go} /></pre>
      </div>`)}
    </div>`;
  }
  function PortDetail({ p, M, go }) {
    if (!p) return null;
    const sys = p.system && M.system(p.system);
    const users = M.services.flatMap((sv) => sv.useCases.filter((u) => u.asks.includes(p.id)).map((u) => [sv, u]));
    const siblings = M.ports.filter((q) => q.id !== p.id && q.system && q.system === p.system);
    return html`<div>
      <p className="kicker">«port» ${p.ops.length} operation${p.ops.length === 1 ? "" : "s"}, owned by the application</p>
      <h2 className="mono-title">${p.name.split(".").pop()}</h2>
      <${Doc} text=${p.doc} />
      ${sys && html`<div className="fronts">
        <b>Fronts</b> ${p.apis.length ? html`${p.apis.map((a) => html`<span key=${a} className="api">${a}</span>`)} of` : "all of"}
        <button className="tref" onClick=${() => go.type("sysnode:" + sys.id)}>${sys.name}</button>
        <p className="doc small">${p.apis.length
          ? `One port per API: ${sys.name} has ${plural(sys.apis.length, "API")}${siblings.length ? `; ${siblings.map((q) => q.name.split(".").pop()).join(", ")} front${siblings.length === 1 ? "s" : ""} the others` : ""}.`
          : `One port for the whole of ${sys.name}.`}</p></div>`}
      <h3>Operations <span className="n">${p.ops.length}</span></h3>
      ${p.ops.map((o) => html`<div key=${o.name} className="op">
        <pre className="sig"><b>${o.name}</b>(${o.args.map((a, i) => html`<span key=${i}>${i ? ", " : ""}${a.name}: <${Linked} text=${a.type} M=${M} go=${go} /></span>`)}) → <${Linked} text=${o.returns} M=${M} go=${go} /></pre>
        <${Doc} text=${o.doc} className="small" /></div>`)}
      ${p.acl.length > 0 && html`<h3>Anti-corruption layer <span className="n">${p.acl.length}</span></h3>
        <p className="doc small">No DTO gets past these: they turn ${sys ? sys.name + "'s" : "the outside"} answers into the domain's terms, or say why not.</p>
        ${p.acl.map((f) => html`<div key=${f.name} className="op"><pre className="sig"><${Linked} text=${f.signature} M=${M} go=${go} /></pre><${Doc} text=${f.doc} className="small" /></div>`)}`}
      <h3>Asked by <span className="n">${users.length}</span></h3>
      <div className="pills">${users.map(([sv, u]) => html`<button key=${sv.id + u.id} className="tref" onClick=${() => go.type("svc:" + sv.id)}>${sv.name}.${u.id}</button>`)}</div>
    </div>`;
  }
  function SystemDetail({ x, M, go }) {
    if (!x) return null;
    const ports = M.ports.filter((p) => p.system === x.id);
    const dtos = M.d.types.filter((t) => t.kind === "dto" && t.system === x.id);
    return html`<div>
      <p className="kicker">«external system» ${x.kind}</p>
      <h2>${x.name}</h2>
      <${Doc} text=${x.doc} />
      <h3>APIs <span className="n">${x.apis.length}</span></h3>
      ${x.apis.map((a) => { const by = ports.filter((p) => !p.apis.length || p.apis.includes(a.id));
        return html`<div key=${a.id} className="api-row"><span className="api">${a.id}</span> <span className="doc small">${a.doc}</span>
          <span className="pills">${by.length ? by.map((p) => html`<${PortRef} key=${p.id} id=${p.id} M=${M} go=${go} />`) : html`<span className="doc small">no port uses it</span>`}</span></div>`; })}
      <h3>Its model <span className="n">${dtos.length}</span></h3>
      <p className="doc small">DTOs: ${x.name}'s own types, which only the ports and their anti-corruption layers see.</p>
      <div className="pills">${dtos.map((t) => html`<${TypeRef} key=${t.id} id=${t.id} M=${M} go=${go} />`)}</div>
    </div>`;
  }
  function Overview({ M, go, layers, setLayers }) {
    const { d } = M;
    const count = (k) => d.types.filter((t) => M.kind(t) === k).length;
    return html`<div>
      <p className="kicker">Class diagram, read from the compiled Lean</p>
      <h2>${d.title}</h2>
      <${Doc} text=${d.doc} />
      <div className="kinds">${["aggregate", "entity", "value", "identifier", "enum", "choice", "command", "event", "rejection", "dto"].filter((k) => count(k)).map((k) => html`<span key=${k} className="kindcount"><b>${count(k)}</b> ${KIND_N[k][count(k) === 1 ? 0 : 1]}</span>`)}</div>
      <h3>Connections</h3>
      <div className="layers">${LAYERS.map(([k, label]) => html`<label key=${k} className="layer">
        <input type="checkbox" checked=${!!layers[k]} onChange=${(e) => setLayers({ ...layers, [k]: e.target.checked })} />
        <svg width="36" height="12" aria-hidden="true"><path d="M3,6 H31" className=${"edge e-" + k} markerEnd=${k === "has" ? null : `url(#end-${k})`} markerStart=${k === "has" ? "url(#start-has)" : null} /></svg>${label}</label>`)}</div>
      <p className="doc small">Hover over or select a box to see all its connections, whichever are switched off.</p>
      <${Glossary} M=${M} go=${go} />
      ${M.contexts.length > 0 && html`<h3>Bounded contexts <span className="n">${M.contexts.length}</span></h3>
        ${M.contexts.map((c) => html`<div key=${c.id} className="ctx-row"><b>${c.title}</b><span className="doc">${c.doc}</span>
          <div className="pills">${c.aggregates.map((a) => M.agg(a) && html`<${TypeRef} key=${a} id=${M.agg(a).state} M=${M} go=${go} />`)}</div></div>`)}`}
      ${d.processes.length > 0 && html`<h3>Processes <span className="n">${d.processes.length}</span></h3>
        <div className="pills">${d.processes.map((p) => html`<button key=${p.id} className="tref" onClick=${() => go.type("proc:" + p.id)}>${p.name}</button>`)}</div>`}
      ${M.services.length > 0 && html`<h3>Application services <span className="n">${M.services.length}</span></h3>
        <div className="pills">${M.services.map((sv) => html`<button key=${sv.id} className="tref" onClick=${() => go.type("svc:" + sv.id)}>${sv.name}</button>`)}</div>`}
      ${M.ports.length > 0 && html`<h3>Ports <span className="n">${M.ports.length}</span></h3>
        ${M.ports.map((p) => html`<div key=${p.id} className="ctx-row"><${PortRef} id=${p.id} M=${M} go=${go} /><span className="doc small">${fronts(M, p)}</span></div>`)}`}
      ${d.theorems.length > 0 && html`<h3>Theorems <span className="n">${d.theorems.length}</span></h3>${d.theorems.map((t) => html`<${Theorem} key=${t.name} t=${t} M=${M} />`)}`}
    </div>`;
  }

  /** Facts about the world a step runs in (the snapshot's `@world` entry), and which just changed. */
  function WorldFacts({ sc, step, className }) {
    const w = (sc.frames[step].state || {})["@world"], prev = step > 0 ? (sc.frames[step - 1].state || {})["@world"] : null;
    if (!w || typeof w !== "object") return null;
    return html`<div className=${"world " + (className || "")}>${Object.entries(w).map(([k, v]) => {
      const ch = prev && JSON.stringify(prev[k]) !== JSON.stringify(v);
      return html`<span key=${k} className=${"fact" + (ch ? " changed" : "")}><span className="k">${k}</span> ${String(fmtVal(v)).replace(/^"|"$/g, "")}</span>`;
    })}</div>`;
  }
  /** A value as an expandable tree: records and lists open on click, everything else inline. */
  function ValueTree({ v, depth = 0 }) {
    if (v === null || v === undefined || typeof v !== "object") return html`<span className="vt-leaf">${fmtVal(v)}</span>`;
    const entries = Array.isArray(v) ? v.map((x, i) => [String(i), x]) : Object.entries(v);
    if (!entries.length) return html`<span className="vt-leaf">${Array.isArray(v) ? "[]" : "{}"}</span>`;
    return html`<details className="vt" open=${depth === 0 && entries.length <= 4}>
      <summary><span className="vt-sum">${Array.isArray(v) ? plural(entries.length, "item") : fmtVal(v, 1)}</span></summary>
      <dl>${entries.map(([k, x]) => html`<div key=${k} className="vt-row"><dt>${k}</dt><dd><${ValueTree} v=${x} depth=${depth + 1} /></dd></div>`)}</dl></details>`;
  }
  /** One object through the whole scenario: what it holds now, and every step that created or
   *  changed it, with the event that did. */
  function ObjectInspector({ M, sc, step, k, o, go }) {
    const per = useMemo(() => sc.frames.map((f) => objectsOf(M, f)), [M, sc]);
    const history = useMemo(() => {
      const out = [];
      for (let j = 1; j < sc.frames.length; j++) {
        const a = per[j - 1].objs.get(k), b = per[j].objs.get(k), f = sc.frames[j];
        if (!b && !a) continue;
        const by = eventChanges(M, f, per[j - 1], per[j]);
        const evs = (f.ok ? f.events || [] : []).map((e, i) => ({ name: message(M, e, "evt").name, hit: by[i] && by[i].has(k) })).filter((e) => e.hit);
        if (!a) { out.push({ j, what: "created", evs, changes: [] }); continue; }
        if (!b) { out.push({ j, what: "removed", evs, changes: [] }); continue; }
        const was = new Map(a.rows.map((r) => [r.name, r.text]));
        const changes = b.rows.filter((r) => was.get(r.name) !== r.text).map((r) => ({ name: r.name, from: was.get(r.name), to: r.text }));
        if (changes.length) out.push({ j, what: "changed", evs, changes });
      }
      return out;
    }, [per, k]);
    return html`<div className="objdetail" style=${{ "--h": M.hue(o.agg) }}>
      <h3><span className="swatch" />Selected object</h3>
      <p className="mono-title u">${objLabel(M, o)}</p>
      <${Def} doc=${(M.types.get(o.typeId) || {}).doc} decl=${o.typeId} />
      <h3>Now, at step ${step} <span className="n">${o.rows.length}</span></h3>
      <div className="rows">${o.rows.map((r) => html`<div className="row" key=${r.name}>
        <div className="head"><span className="name">${r.name}</span>${r.raw === null || typeof r.raw !== "object" ? html`<span className="ty full">${r.text}</span>` : null}</div>
        ${r.raw !== null && typeof r.raw === "object" && html`<div className="vt-wrap"><${ValueTree} v=${r.raw} /></div>`}
        <${Def} doc=${r.doc} decl=${o.typeId + "." + r.name} className="d" /></div>`)}</div>
      <h3>History <span className="n">${plural(history.length, "step")}</span></h3>
      ${history.length ? html`<ol className="history">${history.map((h) => html`<li key=${h.j} className=${h.j === step ? "cur" : h.j > step ? "later" : ""}>
          <button className="h-step" onClick=${() => go.scenario(sc.id, h.j)} aria-label=${`Go to step ${h.j}`}>${h.j}</button>
          <div className="h-body">
            <div className="h-what">${h.what === "changed" ? "changed" : h.what}${h.evs.length ? html` by <code>${h.evs.map((e) => e.name).join(", ")}</code>` : null}</div>
            ${h.changes.map((c) => html`<div key=${c.name} className="h-chg"><span className="name">${c.name}</span> <span className="was">${c.from === undefined ? "—" : c.from}</span> → <b>${c.to}</b></div>`)}
          </div></li>`)}</ol>` : html`<p className="doc">Nothing in this scenario changes it.</p>`}
      <button className="pill" style=${{ marginTop: 10 }} onClick=${() => go.type(o.typeId)}>Open its class in the model</button></div>`;
  }
  const frame0 = (f) => (f.via ? `Running ${f.via} across ${f.targets.length} aggregates…` : "The aggregate checks its rules…");
  function StepPanel({ M, sc, step, phase, go, sel }) {
    const f = sc.frames[step];
    const [cur, before] = useMemo(() => f ? [objectsOf(M, f), step > 0 ? objectsOf(M, sc.frames[step - 1]) : null] : [null, null], [sc, step]);
    if (!f) return null;
    const changes = [];
    if (before) {
      for (const [k, o] of cur.objs) {
        const p = before.objs.get(k);
        if (!p) { changes.push({ k, agg: o.agg, label: objLabel(M, o), what: "created" }); continue; }
        const pr = new Map(p.rows.map((r) => [r.name, r.text]));
        for (const r of o.rows) if (pr.get(r.name) !== r.text) changes.push({ k, agg: o.agg, label: objLabel(M, o), what: r.name, from: pr.get(r.name), to: r.text });
      }
      for (const [k, o] of before.objs) if (!cur.objs.has(k)) changes.push({ k, agg: o.agg, label: objLabel(M, o), what: "removed" });
    }
    const cmd = f.via || f.service ? null : message(M, f.command, "cmd");
    const o = sel && cur.objs.get(sel);
    const uc = f.service && useCaseMessage(M, f), failed = failedOf(f);
    return html`<div>
      <p className="kicker">Step ${step} of ${sc.frames.length - 1}</p>
      <h2>${sc.title}</h2>
      ${step === 0 && html`<${Doc} text=${sc.doc} />`}
      <p className="note">${f.note}</p>
      ${f.say && html`<${Doc} text=${f.say} className="say" />`}
      <${WorldFacts} sc=${sc} step=${step} />
      ${f.start && !f.say && html`<p className="doc">Press → to send the first command.</p>`}
      ${!f.start && f.actor !== "clock" && html`
        <div className="who"><span className="badge">${f.actor || "system"}</span><span className="arrow">${f.service ? "calls" : f.via ? "runs the process" : "sends"}</span>
          <code>${f.service ? `${uc.sub}.${uc.name}` : f.via || (cmd && cmd.name)}</code><span className="arrow">${f.service ? "which changes" : "to"}</span>
          ${f.targets.map((t) => M.agg(t) && html`<span key=${t} className="pill static" style=${{ "--h": M.hue(t) }}><span className="swatch" />${M.agg(t).name}</span>`)}</div>
        ${cmd && cmd.doc && html`<p className="cmd-def"><code>${cmd.name}</code> ${plain(cmd.doc)}</p>`}
        ${f.via && M.proc(f.via) && M.proc(f.via).doc && html`<p className="cmd-def"><code>${f.via}</code> ${plain(M.proc(f.via).doc)}</p>`}
        ${uc && uc.doc && html`<p className="cmd-def"><code>${uc.name}</code> ${plain(uc.doc)}</p>`}
        ${(f.calls || []).length > 0 && html`<h3>Asked outside <span className="n">${f.calls.length}</span></h3>
          <div className="calls">${f.calls.map((c, i) => { const p = M.port(c.port), sys = p && p.system && M.system(p.system);
            return html`<button key=${i} className=${"call click" + (c.ok ? "" : " bad")} onClick=${() => go.type("port:" + c.port)} title="Open the port">
              <span className="c-op">${c.port}.${c.op}</span>(${c.args})${sys ? html` <span className="doc small">→ ${sys.name}</span>` : null}
              <span className="c-res">${c.ok ? "" : "✕ "}${callAnswer(M, c).join(", ")}</span></button>`; })}</div>`}
        ${phase === 1 ? html`<div className=${"verdict " + (f.ok ? "ok" : "bad")}><span className="mark">${f.ok ? "✓" : "✕"}</span>
          <span>${f.ok ? (f.events.length ? `Accepted: ${plural(f.events.length, "event")} recorded.` : "Accepted.") : failed ? "Failed before the domain was asked, so nothing was decided or saved." : "Refused, so nothing changed."}
          ${failed && html`<span className="why">${failed}</span>`}
          ${!f.ok && !failed && reason(f.error, M.ns, M, f.targets) && html`<span className="why">${reason(f.error, M.ns, M, f.targets)}</span>`}</span></div>` : html`<div className="verdict pending"><span className="mark">…</span><span>${frame0(f)}</span></div>`}`}
      ${phase === 1 && (f.expect || []).length > 0 && html`<p className="checked" title="The build fails if a step does anything other than what its story says">✓ Checked when the domain is built: the story says ${f.expect[0]}.</p>`}
      ${phase === 1 && f.ok && (f.findings || []).length > 0 && html`<div className="verdict warn"><span className="mark">⚠</span>
        <span>Accepted, with ${plural(f.findings.length, "policy warning")}:${f.findings.map((x, i) => html`<span key=${i} className="why">${x}</span>`)}</span></div>`}
      ${phase === 1 && f.ok && f.events.length > 0 && html`<h3>Recorded <span className="n">${f.events.length}</span></h3>
        <div className="rows">${f.events.map((e, i) => { const m = message(M, e, "evt"); return html`<div key=${i} className="row" style=${{ "--h": M.hue(m.agg) }}>
          <div className="head"><span className="swatch" /><span className="name">${m.name}</span><span className="ty">${(M.agg(m.agg) || {}).name}</span></div>
          <${Def} doc=${m.doc} decl=${((M.agg(m.agg) || {}).evt || "Evt") + "." + m.name} className="d" /></div>`; })}</div>`}
      ${phase === 1 && changes.length > 0 && html`<h3>What changed <span className="n">${changes.length}</span></h3>
        <div className="rows">${changes.slice(0, 40).map((c, i) => html`<button key=${i} className="row click" style=${{ "--h": M.hue(c.agg) }} onClick=${() => go.obj(c.k)}>
          <div className="head"><span className="swatch" /><span className="name">${c.label}</span><span className="ty">${c.what}</span></div>
          ${c.from !== undefined && html`<div className="d mono"><span className="was">${c.from}</span> → <b>${c.to}</b></div>`}</button>`)}</div>`}
      ${o && html`<${ObjectInspector} M=${M} sc=${sc} step=${step} k=${sel} o=${o} go=${go} />`}
      ${M.d.scenarios.length > 1 && html`<h3>Scenarios</h3>
        <div className="scen-list">${M.d.scenarios.map((s) => html`<button key=${s.id} className="scen" aria-current=${s.id === sc.id} onClick=${() => go.scenario(s.id, 0)}>
          <b>${s.title}</b><span className="ticks">${s.frames.slice(1).map((x, i) => html`<i key=${i} className=${x.ok ? "" : "bad"} />`)}</span></button>`)}</div>`}
    </div>`;
  }

  /** How long playback stays on a step: time to take in the diagram, plus time to read what the
   *  step says and its notes at about 240 words a minute. */
  function dwell(f) {
    const words = [f.say || f.note || "", ...(f.notes || []).map((n) => n.text)].join(" ").split(/\s+/).filter(Boolean).length;
    return 2500 + words * 250;
  }
  function Timeline({ sc, step, setStep, playing, setPlaying, speed, setSpeed, follow, setFollow }) {
    const n = sc.frames.length;
    return html`<div className="timeline">
      <button className="ctrl" onClick=${() => setStep(Math.max(0, step - 1))} disabled=${step === 0} aria-label="Previous step">←</button>
      <button className="ctrl primary" onClick=${() => { if (step >= n - 1) setStep(0); setPlaying(!playing); }}>${playing ? "Pause" : step >= n - 1 ? "Replay" : "Play"}</button>
      <button className="ctrl" onClick=${() => setStep(Math.min(n - 1, step + 1))} disabled=${step >= n - 1} aria-label="Next step">→</button>
      <div className="track" role="group" aria-label="Steps">
        ${sc.frames.map((f, i) => html`<button key=${i} className=${"tick" + (f.start ? " start" : f.ok ? "" : " bad") + (i < step ? " past" : "")}
          aria-current=${i === step} aria-label=${`Step ${i}: ${f.note}`} title=${`${i}. ${f.note}`} onClick=${() => { setPlaying(false); setStep(i); }} />`)}
      </div>
      <label className="follow"><input type="checkbox" checked=${follow} onChange=${(e) => setFollow(e.target.checked)} />Follow</label>
      <div className="speed" role="group" aria-label="Speed">${[0.5, 1, 2].map((s) => html`<button key=${s} aria-pressed=${speed === s} onClick=${() => setSpeed(s)}>${s}×</button>`)}</div>
    </div>`;
  }

  /* ================= routing, theme, search ================= */
  function parseHash() {
    const [tab, a, b] = location.hash.slice(1).split("/");
    if (tab === "scenarios") return { tab, sid: a ? decodeURIComponent(a) : null, step: Number(b) || 0 };
    return { tab: "model", sel: a ? decodeURIComponent(a) : null };
  }
  const toHash = (r) => (r.tab === "scenarios" ? `#scenarios/${encodeURIComponent(r.sid || "")}/${r.step || 0}` : "#model" + (r.sel ? "/" + encodeURIComponent(r.sel) : ""));
  function useTheme() {
    const read = () => { try { return localStorage.getItem("ddd-viz-theme") || "auto"; } catch (e) { return "auto"; } };
    const [theme, setTheme] = useState(read);
    useEffect(() => {
      if (theme === "auto") document.documentElement.removeAttribute("data-theme"); else document.documentElement.setAttribute("data-theme", theme);
      try { localStorage.setItem("ddd-viz-theme", theme); } catch (e) { /* private mode */ }
    }, [theme]);
    return [theme, () => setTheme({ auto: "light", light: "dark", dark: "auto" }[theme])];
  }
  const ThemeButton = ({ theme, cycle }) => html`<button className="theme" onClick=${cycle}>${{ auto: "Theme: system", light: "Theme: light", dark: "Theme: dark" }[theme]}</button>`;
  function Search({ M, go }) {
    const [q, setQ] = useState("");
    const hits = q ? M.d.types.filter((t) => t.name.toLowerCase().includes(q.toLowerCase())).slice(0, 8) : [];
    return html`<div className="search-wrap">
      <input className="search" type="search" placeholder="Find a type" value=${q} onInput=${(e) => setQ(e.target.value)} aria-label="Find a type"
        onKeyDown=${(e) => { if (e.key === "Enter" && hits[0]) { go.type(hits[0].id); setQ(""); } if (e.key === "Escape") setQ(""); }} />
      ${hits.length > 0 && html`<div className="hits">${hits.map((t) => html`<button key=${t.id} style=${{ "--h": M.typeHue(t) }} onClick=${() => { go.type(t.id); setQ(""); }}>
        <span className="swatch" />${t.name}<span className="k">${STEREO[M.kind(t)]}</span></button>`)}</div>`}
    </div>`;
  }

  /* ================= domain page ================= */
  function Domain({ d }) {
    const M = useMemo(() => indexModel(d), [d]);
    const [route, setRoute] = useState(parseHash);
    const [playing, setPlaying] = useState(false);
    const [speed, setSpeed] = useState(1);
    const [phase, setPhase] = useState(1);
    const [follow, setFollow] = useState(true);
    const [objSel, setObjSel] = useState(null);
    const [aside, setAside] = useState(true);
    const [layers, setLayers] = useState(() => Object.fromEntries(LAYERS.map(([k, , on]) => [k, on])));
    const [theme, cycle] = useTheme();
    const [ready, setReady] = useState(false);
    useEffect(() => { const t = setTimeout(() => setReady(true), 1500); (document.fonts ? document.fonts.ready : Promise.resolve()).then(() => setReady(true)); return () => clearTimeout(t); }, []);
    const nav = useCallback((r) => { setRoute(r); history.replaceState(null, "", toHash(r)); }, []);
    useEffect(() => { const h = () => setRoute(parseHash()); addEventListener("hashchange", h); return () => removeEventListener("hashchange", h); }, []);
    useEffect(() => { document.title = d.title + ": domain model"; }, [d]);
    const sc = route.tab === "scenarios" ? d.scenarios.find((s) => s.id === route.sid) || d.scenarios[0] : null;
    const step = sc ? Math.min(route.step || 0, sc.frames.length - 1) : 0;
    const setStep = (i) => nav({ tab: "scenarios", sid: sc.id, step: i });
    const go = {
      type: (id) => { setPlaying(false); nav({ tab: "model", sel: id }); },
      scenario: (sid, s) => { setPlaying(false); setObjSel(null); nav({ tab: "scenarios", sid, step: s }); },
      obj: (k) => { setObjSel(k); setAside(true); },
    };
    // each step: the command goes out (phase 0), then the new state lands (phase 1)
    useEffect(() => {
      if (!sc || step === 0 || reduced()) { setPhase(1); return; }
      setPhase(0);
      const t = setTimeout(() => setPhase(1), 650 / speed);
      return () => clearTimeout(t);
    }, [sc && sc.id, step]);
    useEffect(() => {
      if (!playing || !sc) return;
      if (step >= sc.frames.length - 1) { setPlaying(false); return; }
      const t = setTimeout(() => setStep(step + 1), dwell(sc.frames[step]) / speed);
      return () => clearTimeout(t);
    }, [playing, step, sc && sc.id, speed]);
    useEffect(() => {
      const k = (e) => {
        if (e.target.closest && e.target.closest("input, textarea")) return;
        if (sc && e.key === "ArrowRight") { e.preventDefault(); setPlaying(false); setStep(Math.min(sc.frames.length - 1, step + 1)); }
        else if (sc && e.key === "ArrowLeft") { e.preventDefault(); setPlaying(false); setStep(Math.max(0, step - 1)); }
        else if (sc && e.key === " " && !(e.target.closest && e.target.closest("button"))) { e.preventDefault(); if (step >= sc.frames.length - 1) setStep(0); setPlaying((p) => !p); }
        else if (e.key === "Escape") { setObjSel(null); if (!sc) nav({ tab: "model", sel: null }); }
      };
      addEventListener("keydown", k);
      return () => removeEventListener("keydown", k);
    }, [sc && sc.id, step]);

    return html`<div className=${"app" + (aside ? "" : " no-aside")}>
      <header className="top">
        <div className="brand"><span className="seal" aria-hidden="true">∎</span><h1>${d.title}</h1>${SITE.home && html`<a href=${SITE.home}>All domains</a>`}</div>
        <nav className="tabs" role="tablist">
          <button role="tab" className="tab" aria-selected=${!sc} onClick=${() => nav({ tab: "model", sel: null })}>Model<span className="n">${plural(d.types.length, "type")}</span></button>
          <button role="tab" className="tab" aria-selected=${!!sc} disabled=${!d.scenarios.length} onClick=${() => go.scenario((sc || d.scenarios[0]).id, 0)}>Scenarios<span className="n">${d.scenarios.length}</span></button>
        </nav>
        ${!sc && html`<${Search} M=${M} go=${go} />`}
        <span className="spacer" />
        <button className="theme" onClick=${() => setAside(!aside)} aria-pressed=${aside}>${aside ? "Hide details" : "Show details"}</button>
        <${ThemeButton} theme=${theme} cycle=${cycle} />
      </header>
      <div className="main">
        ${!ready ? html`<div className="loading">Loading…</div>` : sc
          ? html`<${ObjectView} key=${sc.id} M=${M} sc=${sc} step=${step} phase=${phase} playing=${playing} sel=${objSel} setSel=${(k) => { setObjSel(k); if (k) setAside(true); }} speed=${speed} follow=${follow} goStep=${(i) => { setPlaying(false); setStep(i); }} />`
          : html`<${ClassView} M=${M} sel=${route.sel} setSel=${(id) => nav({ tab: "model", sel: id })} layers=${layers} />`}
        ${aside && html`<aside className="aside"><div className="aside-inner">
          ${sc ? html`<${StepPanel} M=${M} sc=${sc} step=${step} phase=${phase} go=${go} sel=${objSel} />`
            : route.sel ? html`<${TypeDetail} key=${route.sel} id=${route.sel} M=${M} go=${go} />` : html`<${Overview} M=${M} go=${go} layers=${layers} setLayers=${setLayers} />`}
        </div></aside>`}
      </div>
      ${sc ? html`<${Timeline} sc=${sc} step=${step} setStep=${setStep} playing=${playing} setPlaying=${setPlaying} speed=${speed} setSpeed=${setSpeed} follow=${follow} setFollow=${setFollow} />` : null}
    </div>`;
  }

  /* ================= catalog ================= */
  function Catalog() {
    const [theme, cycle] = useTheme();
    const ds = SITE.domains || [];
    return html`<div className="catalog-page"><div className="catalog">
      <div style=${{ display: "flex", justifyContent: "flex-end" }}><${ThemeButton} theme=${theme} cycle=${cycle} /></div>
      <h1><span style=${{ color: "var(--focus)" }}>∎</span> Domain models</h1>
      <p>Each model is read from compiled Lean. Its class diagram shows the bounded contexts, the aggregates and every type inside them. Its scenarios send real commands and draw the objects that result, step by step.</p>
      ${ds.length ? html`<div className="domains">${ds.map((x) => html`<a key=${x.id} className="domain" href=${x.href}>
          <b>${x.title}</b><p>${x.doc}</p>
          <div className="counts">${plural(x.aggregates, "aggregate")}<br />${plural(x.types, "type")}<br />${plural(x.theorems, "theorem")}<br />${plural(x.scenarios, "scenario")}</div></a>`)}</div>`
        : html`<p>No domains yet. Add a script that calls <code>DDD.Viz.emit</code>, then run <code>lake exe ddd-viz</code>.</p>`}
    </div></div>`;
  }
  function Root() {
    if (SITE.mode === "domain") {
      const d = (window.DDD_VIZ || {})[SITE.domain];
      if (!d) return html`<div className="catalog"><h1>Nothing to show</h1><p>This page has no domain data. Run its Lean script again.</p></div>`;
      return html`<${Domain} d=${d} />`;
    }
    return html`<${Catalog} />`;
  }
  ReactDOM.createRoot(document.getElementById("root")).render(html`<${Root} />`);
})();
