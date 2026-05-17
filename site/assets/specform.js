// specform.js — schema-driven structured spec editor.
//
// The Construct and Logic workbenches used to demand hand-written JSON.
// This renders a real form, byte-exact to the engine's serde structs
// (build.rs / logic.rs), with a collapsible "raw JSON" disclosure that
// round-trips both ways. Forms are primary; raw is the escape hatch.
//
// Field types: text · num · bool · enum · slist (scalar chips) ·
// clist (constellation rows, live-validated) · tuples (typed rows,
// cells may be nullable) · objlist (rows of sub-objects) · taglist
// (tagged-union rows whose visible fields follow `kind`) · map · json.

const el = (n, cls, txt) => {
  const e = document.createElement(n);
  if (cls) e.className = cls;
  if (txt != null) e.textContent = txt;
  return e;
};
const dbl = (ms, fn) => { let t; return (...a) => { clearTimeout(t); t = setTimeout(() => fn(...a), ms); }; };

// ── The schema registry ───────────────────────────────────────────────────
// req: at least one entry expected.  help: inline gloss.  ref: Eng §.
const F = (k, t, o = {}) => ({ k, t, ...o });

const LINK_KINDS_MLL = {
  ax: ["left", "right"], cut: ["left", "right"],
  tensor: ["left", "right", "output"], par: ["left", "right", "output"],
};
const LINK_KINDS_M2 = {
  ...LINK_KINDS_MLL,
  etensor: ["left", "right", "output"], epar: ["left", "right", "output"],
  weakening: ["output"], dereliction: ["input", "output"],
  contraction: ["left", "right", "output"],
};

export const SCHEMA = {
  nfa: {
    title: "NFA — nondeterministic finite automaton", ref: "Eng §56",
    blurb: "States, an input alphabet, and a transition relation δ. The word is run; acceptance ⇒ a saturated diagram.",
    fields: [
      F("states", "slist", { help: "All state names." }),
      F("alphabet", "slist", { help: "Input symbols." }),
      F("initial", "slist", { help: "Initial state(s)." }),
      F("finals", "slist", { help: "Accepting state(s)." }),
      F("transitions", "tuples", {
        cols: [{ l: "from" }, { l: "on", nullable: true }, { l: "to" }],
        help: "δ rows: (state, symbol | ε, state). Leave the symbol blank for ε.",
      }),
      F("word", "slist", { help: "Input word, one symbol per token." }),
    ],
  },
  npda: {
    title: "NPDA — nondeterministic pushdown automaton", ref: "Eng §56",
    blurb: "A finite control with a stack. Each move may read input, pop, and push (any of which may be ε).",
    fields: [
      F("states", "slist"), F("alphabet", "slist"),
      F("stack_alphabet", "slist", { help: "Stack symbols." }),
      F("initial", "slist"), F("finals", "slist"),
      F("transitions", "tuples", {
        cols: [{ l: "from" }, { l: "read", nullable: true }, { l: "pop", nullable: true }, { l: "to" }, { l: "push", nullable: true }],
        help: "(state, read | ε, pop | ε, state, push | ε).",
      }),
      F("word", "slist"),
    ],
  },
  ntm: {
    title: "NTM — nondeterministic Turing machine", ref: "Eng §57",
    blurb: "Tape machine: δ rewrites the head cell and moves L/R/S.",
    fields: [
      F("states", "slist"),
      F("gamma", "slist", { help: "Tape alphabet (include the blank symbol)." }),
      F("delta", "tuples", {
        cols: [{ l: "from" }, { l: "read" }, { l: "to" }, { l: "write" }, { l: "dir", enum: ["L", "R", "S"] }],
        help: "(state, read, state, write, direction).",
      }),
      F("q0", "text", { help: "Initial state." }),
      F("q_accept", "text"), F("q_reject", "text"),
      F("input", "slist", { help: "Input word (symbols)." }),
    ],
  },
  atm: {
    title: "ATM — alternating Turing machine", ref: "Eng §57",
    blurb: "An NTM whose states are existential (E) or universal (U).",
    fields: [
      F("states", "slist"), F("gamma", "slist"),
      F("delta", "tuples", {
        cols: [{ l: "from" }, { l: "read" }, { l: "to" }, { l: "write" }, { l: "dir", enum: ["L", "R", "S"] }],
      }),
      F("q0", "text"), F("q_accept", "text"), F("q_reject", "text"),
      F("class", "map", { vEnum: ["E", "U"], help: "state → E (existential) | U (universal)." }),
      F("input", "slist"),
    ],
  },
  nfta: {
    title: "NFTA — nondeterministic finite tree automaton", ref: "Eng §57.7",
    blurb: "Bottom-up tree acceptance. Rules bundle a parent symbol with its children states.",
    fields: [
      F("states", "slist"), F("initial", "slist", { help: "Accepting root state(s)." }),
      F("rules", "objlist", {
        item: [F("state", "text"), F("symbol", "text"), F("successors", "slist")],
        help: "Each rule: state ← symbol(successors…).",
      }),
      F("leaf_states", "slist"),
      F("terminal_pairs", "tuples", { cols: [{ l: "state" }, { l: "symbol" }] }),
      F("tree", "tree", {
        help: 'The tree to accept. Each point is a leaf (a terminal symbol) or a node (a symbol with child subtrees).',
      }),
    ],
  },
  nfst: {
    title: "NFST — nondeterministic finite-state transducer", ref: "Eng §56",
    blurb: "Like an NFA but each move may emit an output symbol.",
    fields: [
      F("states", "slist"), F("alphabet", "slist"),
      F("output_alphabet", "slist"),
      F("initial", "slist"), F("finals", "slist"),
      F("transitions", "tuples", {
        cols: [{ l: "from" }, { l: "in", nullable: true }, { l: "to" }, { l: "out", nullable: true }],
        help: "(state, input | ε, state, output | ε).",
      }),
      F("word", "slist"),
    ],
  },
  circuit: {
    title: "Boolean circuit", ref: "Eng §58",
    blurb: "A DAG of gates over named wires; runs under Ex with the Boolean module. (Ψ is empty.)",
    fields: [
      F("gates", "objlist", {
        item: [
          F("label", "text", { help: "Gate label: a constant (0/1), ∧, ∨, ¬, or a wire pass." }),
          F("inputs", "slist"), F("outputs", "slist"),
          F("is_output", "bool", { help: "Mark a circuit output." }),
        ],
      }),
    ],
  },
  tiles: {
    title: "Tile assembly system", ref: "Eng §8 (Wang tiles)",
    blurb: "aTAM tiles with four glues and binding strengths; self-assembles under Ex at temperature τ.",
    fields: [
      F("tile_types", "objlist", {
        item: [
          F("label", "text"),
          F("glue_w", "text"), F("glue_e", "text"),
          F("glue_s", "text"), F("glue_n", "text"),
          F("strengths", "num4", { help: "Binding strengths [W, E, S, N]." }),
        ],
      }),
      F("tau", "num", { help: "Temperature τ (binding threshold)." }),
      F("seed", "num", { opt: true, help: "Optional seed tile index." }),
      F("positions", "slist", { help: "Lattice positions to populate." }),
    ],
  },
  mll: {
    title: "MLL proof structure", ref: "Eng §62",
    blurb: "Axiom / cut / ⊗ / ⅋ links over integer vertices. Builds Φ_comp; explore with Ex.",
    fields: [F("links", "taglist", { kinds: LINK_KINDS_MLL, num: true })],
  },
  mll2i: {
    title: "MLL2I proof structure", ref: "Eng §74",
    blurb: "MLL with exponentials: adds ⊗ₑ, ⅋ₑ, weakening, dereliction, contraction.",
    fields: [F("links", "taglist", { kinds: LINK_KINDS_M2, num: true })],
  },

  // ── Logic workbench ──────────────────────────────────────────────────────
  ortho: {
    title: "Orthogonality — Φ₁ ⊥ Φ₂", ref: "Eng §52, §61",
    blurb: "Tests whether two constellations are orthogonal under ⊥ᶠⁱⁿ / ⊥¹ / ⊥ᴿ.",
    fields: [
      F("phi1", "cstr", { help: "First constellation Φ₁." }),
      F("phi2", "cstr", { help: "Second constellation Φ₂." }),
    ],
  },
  proofnet: {
    title: "Proof net — correctness + Φ_comp", ref: "Eng §68, §75",
    blurb: "A proof structure; the engine reports the DR (MLL) or Girard (MLL2I) verdict and yields a runnable Φ_comp.",
    fields: [
      F("kind", "enum", { opts: ["mll", "mll2i"], help: "MLL or MLL2I (selects the link vocabulary)." }),
      F("links", "taglist", { num: true, kindsFor: (v) => (v && v.kind === "mll2i" ? LINK_KINDS_M2 : LINK_KINDS_MLL) }),
    ],
  },
  behaviour: {
    title: "Behaviour / type — A = A⊥⊥", ref: "Eng §61, §79",
    blurb: "A finite universe and a candidate set A; the engine computes A⊥, A⊥⊥ and whether A is bi-orthogonally closed.",
    fields: [
      F("members", "clist", { help: "Members of A (constellations)." }),
      F("universe", "clist", { help: "The finite universe to test against." }),
      F("orth", "enum", { opts: ["fin", "one", "roots"], help: "Orthogonality relation." }),
    ],
  },
  compare: {
    title: "Compare — same result? ω delta", ref: "Eng §51, §79",
    blurb: "Runs ΦA ⊢ ΨA and ΦB ⊢ ΨB under the exact engine; reports same-observable and Δω.",
    fields: [
      F("phiA", "cstr"), F("psiA", "cstr"),
      F("phiB", "cstr"), F("psiB", "cstr"),
    ],
  },
};

// ── The form ──────────────────────────────────────────────────────────────
export class SpecForm {
  constructor(host, { onChange, parseCheck } = {}) {
    this.host = host;
    this.onChange = onChange || (() => {});
    this.parseCheck = parseCheck || null;
    this.schemaKey = null;
    this.model = {};
    this._emit = dbl(180, () => this.onChange(this.value()));
  }

  setSchema(key, initial) {
    this.schemaKey = key;
    this.model = initial ? structuredClone(initial) : this._defaults(key);
    this._render();
    this.onChange(this.value());
  }

  _defaults(key) {
    const m = {};
    for (const f of SCHEMA[key].fields) {
      m[f.k] = f.t === "slist" || f.t === "clist" || f.t === "tuples" ||
        f.t === "objlist" || f.t === "taglist" ? []
        : f.t === "bool" ? false
        : f.t === "num" || f.t === "num4" ? (f.t === "num4" ? [1, 1, 1, 1] : 0)
        : f.t === "map" ? {}
        : f.t === "json" ? {}
        : f.t === "tree" ? { leaf: "" }
        : f.t === "enum" ? (f.opts || ["mll"])[0]
        : "";
    }
    return m;
  }

  // value() — the byte-exact object the engine expects.
  value() {
    const sc = SCHEMA[this.schemaKey];
    const out = {};
    for (const f of sc.fields) {
      const v = this.model[f.k];
      if (f.t === "num") {
        if (f.opt && (v === "" || v == null)) continue;
        out[f.k] = Number(v) || 0;
      } else if (f.t === "num4") {
        out[f.k] = (v || [0, 0, 0, 0]).map((x) => Number(x) || 0);
      } else if (f.t === "bool") out[f.k] = !!v;
      else if (f.t === "slist" || f.t === "clist") out[f.k] = (v || []).map((s) => s).filter((s) => s !== "");
      else if (f.t === "tuples") {
        out[f.k] = (v || []).map((row) =>
          f.cols.map((c, i) => (c.nullable && (row[i] === "" || row[i] == null)) ? null : (row[i] ?? "")));
      } else if (f.t === "objlist") {
        out[f.k] = (v || []).map((o) => {
          const r = {};
          for (const sf of f.item) {
            if (sf.t === "slist") r[sf.k] = (o[sf.k] || []).filter((s) => s !== "");
            else if (sf.t === "bool") r[sf.k] = !!o[sf.k];
            else if (sf.t === "num4") r[sf.k] = (o[sf.k] || [0, 0, 0, 0]).map((x) => Number(x) || 0);
            else r[sf.k] = o[sf.k] ?? "";
          }
          return r;
        });
      } else if (f.t === "taglist") {
        const kinds = f.kindsFor ? f.kindsFor(this.model) : f.kinds;
        out[f.k] = (v || []).map((row) => {
          const r = { kind: row.kind };
          for (const fld of (kinds[row.kind] || [])) r[fld] = Number(row[fld]) || 0;
          return r;
        });
      } else if (f.t === "map") {
        const o = {};
        for (const [kk, vv] of (v || [])) if (kk !== "") o[kk] = vv;
        out[f.k] = o;
      } else if (f.t === "json" || f.t === "tree") out[f.k] = v;
      else out[f.k] = v ?? "";
    }
    return out;
  }

  json() { return JSON.stringify(this.value(), null, 2); }

  // setRaw — parse a raw JSON string back into the model (round-trip).
  setRaw(text) {
    let obj;
    try { obj = JSON.parse(text); }
    catch (e) { return { ok: false, error: e.message }; }
    const sc = SCHEMA[this.schemaKey];
    const m = this._defaults(this.schemaKey);
    for (const f of sc.fields) {
      if (!(f.k in obj)) continue;
      const v = obj[f.k];
      if (f.t === "map") m[f.k] = Object.entries(v || {});
      else if (f.t === "num4") m[f.k] = (v || [1, 1, 1, 1]).slice(0, 4);
      else m[f.k] = v;
    }
    this.model = m;
    this._render();
    this.onChange(this.value());
    return { ok: true };
  }

  // ── rendering ────────────────────────────────────────────────────────────
  _render() {
    const sc = SCHEMA[this.schemaKey];
    this.host.textContent = "";
    const head = el("div", "sf-head");
    const tt = el("div", "sf-head__t");
    tt.appendChild(el("span", "sf-head__title", sc.title));
    if (sc.ref) tt.appendChild(el("span", "sf-head__ref", sc.ref));
    head.appendChild(tt);
    head.appendChild(el("p", "sf-head__blurb", sc.blurb));
    this.host.appendChild(head);

    const body = el("div", "sf-body");
    for (const f of sc.fields) body.appendChild(this._field(f));
    this.host.appendChild(body);

    // raw-JSON disclosure (round-trips)
    const det = el("details", "sf-raw");
    det.appendChild(el("summary", "sf-raw__sum", "Advanced · raw JSON"));
    const ta = el("textarea", "stx-ta sf-raw__ta");
    ta.spellcheck = false;
    ta.value = this.json();
    const rerr = el("span", "sf-raw__err");
    det.addEventListener("toggle", () => { if (det.open) ta.value = this.json(); });
    ta.addEventListener("input", () => {
      const r = this.setRaw(ta.value);
      rerr.textContent = r.ok ? "" : "JSON: " + r.error;
      // _render() rebuilt the form; keep the textarea the user is typing in.
      const live = this.host.querySelector(".sf-raw__ta");
      if (live && live !== ta) { live.value = ta.value; live.focus(); }
    });
    det.appendChild(ta);
    det.appendChild(rerr);
    this.host.appendChild(det);
  }

  _set(k, v) { this.model[k] = v; this._emit(); }

  _help(f) {
    if (!f.help) return null;
    const w = el("span", "sf-help");
    w.appendChild(el("span", "sf-help__i", "ⓘ"));
    w.appendChild(el("span", "sf-help__tip", f.help));
    return w;
  }

  _label(f, forId) {
    const l = el("label", "sf-lab");
    l.appendChild(el("span", "sf-lab__k", f.k));
    if (forId) l.htmlFor = forId;
    const h = this._help(f);
    if (h) l.appendChild(h);
    return l;
  }

  _field(f) {
    const row = el("div", "sf-row");
    row.appendChild(this._label(f));
    const ctl = el("div", "sf-ctl");
    const m = this.model;
    if (f.t === "text" || f.t === "num") {
      const i = el("input", "sf-in");
      i.type = f.t === "num" ? "number" : "text";
      i.value = m[f.k] ?? "";
      i.addEventListener("input", () => this._set(f.k, i.value));
      ctl.appendChild(i);
    } else if (f.t === "bool") {
      const i = el("input"); i.type = "checkbox"; i.className = "sf-chk";
      i.checked = !!m[f.k];
      i.addEventListener("change", () => this._set(f.k, i.checked));
      ctl.appendChild(i);
    } else if (f.t === "enum") {
      const s = el("select", "sf-sel");
      for (const o of f.opts) { const op = el("option", null, o); op.value = o; s.appendChild(op); }
      s.value = m[f.k] ?? f.opts[0];
      s.addEventListener("change", () => { this._set(f.k, s.value); this._render(); });
      ctl.appendChild(s);
    } else if (f.t === "slist") {
      ctl.appendChild(this._chips(f.k));
    } else if (f.t === "clist") {
      ctl.appendChild(this._clist(f.k));
    } else if (f.t === "cstr") {
      ctl.appendChild(this._cstr(f.k));
    } else if (f.t === "tuples") {
      ctl.appendChild(this._tuples(f));
    } else if (f.t === "objlist") {
      ctl.appendChild(this._objlist(f));
    } else if (f.t === "taglist") {
      ctl.appendChild(this._taglist(f));
    } else if (f.t === "map") {
      ctl.appendChild(this._map(f));
    } else if (f.t === "num4") {
      ctl.appendChild(this._num4(f.k));
    } else if (f.t === "tree") {
      ctl.appendChild(this._tree(f.k));
    } else if (f.t === "json") {
      const ta = el("textarea", "stx-ta sf-json");
      ta.spellcheck = false;
      ta.value = JSON.stringify(m[f.k] ?? {}, null, 2);
      const er = el("span", "sf-raw__err");
      ta.addEventListener("input", () => {
        try { this._set(f.k, JSON.parse(ta.value)); er.textContent = ""; }
        catch (e) { er.textContent = "JSON: " + e.message; }
      });
      ctl.appendChild(ta); ctl.appendChild(er);
    }
    row.appendChild(ctl);
    return row;
  }

  _chips(k) {
    const wrap = el("div", "sf-chips");
    const draw = () => {
      wrap.textContent = "";
      (this.model[k] || []).forEach((val, i) => {
        const c = el("span", "sf-chip");
        const inp = el("input", "sf-chip__in");
        inp.value = val; inp.size = Math.max(val.length, 2);
        inp.addEventListener("input", () => { this.model[k][i] = inp.value; inp.size = Math.max(inp.value.length, 2); this._emit(); });
        const x = el("button", "sf-chip__x", "✕"); x.type = "button";
        x.addEventListener("click", () => { this.model[k].splice(i, 1); draw(); this._emit(); });
        c.appendChild(inp); c.appendChild(x); wrap.appendChild(c);
      });
      const add = el("button", "sf-add", "+ add"); add.type = "button";
      add.addEventListener("click", () => {
        (this.model[k] = this.model[k] || []).push(""); draw(); this._emit();
        wrap.querySelectorAll(".sf-chip__in"); const ins = wrap.querySelectorAll(".sf-chip__in");
        ins[ins.length - 1]?.focus();
      });
      wrap.appendChild(add);
    };
    draw();
    return wrap;
  }

  _cstr(k) {
    const wrap = el("div", "sf-cstr");
    const i = el("input", "sf-in sf-in--mono");
    i.value = this.model[k] ?? "";
    i.spellcheck = false;
    const mark = el("span", "sf-cstr__v");
    const check = dbl(200, () => {
      const val = i.value.trim();
      if (!val || !this.parseCheck) { mark.textContent = ""; mark.className = "sf-cstr__v"; return; }
      const ok = this.parseCheck(val);
      mark.textContent = ok ? "✓" : "✗";
      mark.className = "sf-cstr__v " + (ok ? "is-ok" : "is-no");
    });
    i.addEventListener("input", () => { this._set(k, i.value); check(); });
    wrap.appendChild(i); wrap.appendChild(mark);
    check();
    return wrap;
  }

  _clist(k) {
    const wrap = el("div", "sf-clist");
    const draw = () => {
      wrap.textContent = "";
      (this.model[k] || []).forEach((val, idx) => {
        const r = el("div", "sf-clist__r");
        const i = el("input", "sf-in sf-in--mono");
        i.value = val; i.spellcheck = false;
        const mk = el("span", "sf-cstr__v");
        const ck = dbl(200, () => {
          const vv = i.value.trim();
          if (!vv || !this.parseCheck) { mk.textContent = ""; mk.className = "sf-cstr__v"; return; }
          const ok = this.parseCheck(vv);
          mk.textContent = ok ? "✓" : "✗"; mk.className = "sf-cstr__v " + (ok ? "is-ok" : "is-no");
        });
        i.addEventListener("input", () => { this.model[k][idx] = i.value; this._emit(); ck(); });
        const x = el("button", "sf-chip__x", "✕"); x.type = "button";
        x.addEventListener("click", () => { this.model[k].splice(idx, 1); draw(); this._emit(); });
        r.appendChild(i); r.appendChild(mk); r.appendChild(x); wrap.appendChild(r);
        ck();
      });
      const add = el("button", "sf-add", "+ add"); add.type = "button";
      add.addEventListener("click", () => { (this.model[k] = this.model[k] || []).push(""); draw(); this._emit(); });
      wrap.appendChild(add);
    };
    draw();
    return wrap;
  }

  _cell(val, col, on) {
    if (col.enum) {
      const s = el("select", "sf-sel sf-sel--sm");
      for (const o of col.enum) { const op = el("option", null, o); op.value = o; s.appendChild(op); }
      s.value = val || col.enum[0];
      s.addEventListener("change", () => on(s.value));
      return s;
    }
    const i = el("input", "sf-in sf-in--sm");
    i.value = val ?? "";
    if (col.nullable) i.placeholder = "ε";
    i.addEventListener("input", () => on(i.value));
    return i;
  }

  _tuples(f) {
    const wrap = el("div", "sf-rows");
    const draw = () => {
      wrap.textContent = "";
      const hdr = el("div", "sf-rows__h");
      f.cols.forEach((c) => hdr.appendChild(el("span", "sf-rows__hc", c.l + (c.nullable ? " ?" : ""))));
      hdr.appendChild(el("span", "sf-rows__hc", ""));
      wrap.appendChild(hdr);
      (this.model[f.k] || []).forEach((rowv, ri) => {
        const r = el("div", "sf-rows__r");
        f.cols.forEach((c, ci) => {
          r.appendChild(this._cell(rowv[ci], c, (nv) => { this.model[f.k][ri][ci] = nv; this._emit(); }));
        });
        const x = el("button", "sf-chip__x", "✕"); x.type = "button";
        x.addEventListener("click", () => { this.model[f.k].splice(ri, 1); draw(); this._emit(); });
        r.appendChild(x); wrap.appendChild(r);
      });
      const add = el("button", "sf-add", "+ add row"); add.type = "button";
      add.addEventListener("click", () => {
        (this.model[f.k] = this.model[f.k] || []).push(f.cols.map(() => "")); draw(); this._emit();
      });
      wrap.appendChild(add);
    };
    draw();
    return wrap;
  }

  _objlist(f) {
    const wrap = el("div", "sf-objs");
    const draw = () => {
      wrap.textContent = "";
      (this.model[f.k] || []).forEach((ov, oi) => {
        const card = el("div", "sf-obj");
        for (const sf of f.item) {
          const r = el("div", "sf-row sf-row--sub");
          r.appendChild(this._label(sf));
          const ctl = el("div", "sf-ctl");
          if (sf.t === "slist") {
            ov[sf.k] = ov[sf.k] || [];
            const saved = this.model; // reuse chip editor against the sub-array
            const chips = (() => {
              const w = el("div", "sf-chips");
              const d2 = () => {
                w.textContent = "";
                ov[sf.k].forEach((val, i) => {
                  const c = el("span", "sf-chip");
                  const inp = el("input", "sf-chip__in"); inp.value = val; inp.size = Math.max(val.length, 2);
                  inp.addEventListener("input", () => { ov[sf.k][i] = inp.value; inp.size = Math.max(inp.value.length, 2); this._emit(); });
                  const x = el("button", "sf-chip__x", "✕"); x.type = "button";
                  x.addEventListener("click", () => { ov[sf.k].splice(i, 1); d2(); this._emit(); });
                  c.appendChild(inp); c.appendChild(x); w.appendChild(c);
                });
                const a = el("button", "sf-add", "+ add"); a.type = "button";
                a.addEventListener("click", () => { ov[sf.k].push(""); d2(); this._emit(); });
                w.appendChild(a);
              };
              d2(); return w;
            })();
            ctl.appendChild(chips);
          } else if (sf.t === "bool") {
            const i = el("input"); i.type = "checkbox"; i.className = "sf-chk";
            i.checked = !!ov[sf.k];
            i.addEventListener("change", () => { ov[sf.k] = i.checked; this._emit(); });
            ctl.appendChild(i);
          } else if (sf.t === "num4") {
            ov[sf.k] = ov[sf.k] || [1, 1, 1, 1];
            ctl.appendChild(this._num4arr(ov[sf.k]));
          } else {
            const i = el("input", "sf-in");
            i.type = sf.t === "num" ? "number" : "text";
            i.value = ov[sf.k] ?? "";
            i.addEventListener("input", () => { ov[sf.k] = i.value; this._emit(); });
            ctl.appendChild(i);
          }
          r.appendChild(ctl);
          card.appendChild(r);
        }
        const x = el("button", "sf-obj__x", "✕ remove"); x.type = "button";
        x.addEventListener("click", () => { this.model[f.k].splice(oi, 1); draw(); this._emit(); });
        card.appendChild(x);
        wrap.appendChild(card);
      });
      const add = el("button", "sf-add", "+ add"); add.type = "button";
      add.addEventListener("click", () => {
        const blank = {};
        for (const sf of f.item) blank[sf.k] = sf.t === "slist" ? [] : sf.t === "bool" ? false : sf.t === "num4" ? [1, 1, 1, 1] : "";
        (this.model[f.k] = this.model[f.k] || []).push(blank); draw(); this._emit();
      });
      wrap.appendChild(add);
    };
    draw();
    return wrap;
  }

  _taglist(f) {
    const wrap = el("div", "sf-rows");
    const kinds = () => (f.kindsFor ? f.kindsFor(this.model) : f.kinds);
    const draw = () => {
      wrap.textContent = "";
      const K = kinds();
      (this.model[f.k] || []).forEach((row, ri) => {
        const r = el("div", "sf-rows__r sf-rows__r--tag");
        const ks = el("select", "sf-sel sf-sel--sm");
        for (const kk of Object.keys(K)) { const op = el("option", null, kk); op.value = kk; ks.appendChild(op); }
        if (!K[row.kind]) row.kind = Object.keys(K)[0];
        ks.value = row.kind;
        ks.addEventListener("change", () => { row.kind = ks.value; draw(); this._emit(); });
        r.appendChild(ks);
        for (const fld of K[row.kind]) {
          const i = el("input", "sf-in sf-in--sm"); i.type = "number";
          i.placeholder = fld; i.title = fld;
          i.value = row[fld] ?? 0;
          i.addEventListener("input", () => { row[fld] = i.value; this._emit(); });
          r.appendChild(i);
        }
        const x = el("button", "sf-chip__x", "✕"); x.type = "button";
        x.addEventListener("click", () => { this.model[f.k].splice(ri, 1); draw(); this._emit(); });
        r.appendChild(x);
        wrap.appendChild(r);
      });
      const add = el("button", "sf-add", "+ add link"); add.type = "button";
      add.addEventListener("click", () => {
        const k0 = Object.keys(kinds())[0];
        (this.model[f.k] = this.model[f.k] || []).push({ kind: k0 }); draw(); this._emit();
      });
      wrap.appendChild(add);
    };
    draw();
    return wrap;
  }

  _map(f) {
    const wrap = el("div", "sf-rows");
    const draw = () => {
      wrap.textContent = "";
      (this.model[f.k] || []).forEach((pair, i) => {
        const r = el("div", "sf-rows__r");
        const kI = el("input", "sf-in sf-in--sm"); kI.value = pair[0] ?? ""; kI.placeholder = "state";
        kI.addEventListener("input", () => { this.model[f.k][i][0] = kI.value; this._emit(); });
        r.appendChild(kI);
        const vS = el("select", "sf-sel sf-sel--sm");
        for (const o of (f.vEnum || [])) { const op = el("option", null, o); op.value = o; vS.appendChild(op); }
        vS.value = pair[1] ?? (f.vEnum || [""])[0];
        vS.addEventListener("change", () => { this.model[f.k][i][1] = vS.value; this._emit(); });
        r.appendChild(vS);
        const x = el("button", "sf-chip__x", "✕"); x.type = "button";
        x.addEventListener("click", () => { this.model[f.k].splice(i, 1); draw(); this._emit(); });
        r.appendChild(x); wrap.appendChild(r);
      });
      const add = el("button", "sf-add", "+ add"); add.type = "button";
      add.addEventListener("click", () => {
        (this.model[f.k] = this.model[f.k] || []).push(["", (f.vEnum || [""])[0]]); draw(); this._emit();
      });
      wrap.appendChild(add);
    };
    draw();
    return wrap;
  }

  // recursive TreeSpec editor: {leaf:"x"} | {node:[sym,[ <tree>… ]]}
  _tree(k) {
    const wrap = el("div", "sf-tree");
    const draw = () => {
      wrap.textContent = "";
      wrap.appendChild(this._treeNode(this.model[k] || { leaf: "" },
        (n) => { this.model[k] = n; draw(); this._emit(); }, 0));
    };
    draw();
    return wrap;
  }

  _treeNode(obj, setObj, depth) {
    const isLeaf = obj && "leaf" in obj && !("node" in obj);
    const card = el("div", "sf-tnode");
    if (depth) card.classList.add("sf-tnode--nested");
    const bar = el("div", "sf-tnode__bar");
    const sel = el("select", "sf-sel sf-sel--sm");
    for (const o of ["leaf", "node"]) { const op = el("option", null, o); op.value = o; sel.appendChild(op); }
    sel.value = isLeaf ? "leaf" : "node";
    sel.addEventListener("change", () =>
      setObj(sel.value === "leaf" ? { leaf: "" } : { node: ["", [{ leaf: "" }]] }));
    bar.appendChild(sel);
    if (isLeaf) {
      const i = el("input", "sf-in sf-in--sm");
      i.placeholder = "terminal"; i.value = obj.leaf ?? "";
      i.addEventListener("input", () => { obj.leaf = i.value; this._emit(); });
      bar.appendChild(i);
      card.appendChild(bar);
      return card;
    }
    if (!obj.node) obj.node = ["", []];
    const sym = el("input", "sf-in sf-in--sm");
    sym.placeholder = "symbol"; sym.value = obj.node[0] ?? "";
    sym.addEventListener("input", () => { obj.node[0] = sym.value; this._emit(); });
    bar.appendChild(sym);
    const kids = el("div", "sf-tkids");
    const rebuild = () => {
      kids.textContent = "";
      obj.node[1].forEach((child, ci) => {
        const row = el("div", "sf-tkid");
        row.appendChild(this._treeNode(child,
          (n) => { obj.node[1][ci] = n; rebuild(); this._emit(); }, depth + 1));
        const x = el("button", "sf-chip__x", "✕"); x.type = "button";
        x.addEventListener("click", () => { obj.node[1].splice(ci, 1); rebuild(); this._emit(); });
        row.appendChild(x);
        kids.appendChild(row);
      });
    };
    const add = el("button", "sf-add", "+ child"); add.type = "button";
    add.addEventListener("click", () => { obj.node[1].push({ leaf: "" }); rebuild(); this._emit(); });
    bar.appendChild(add);
    card.appendChild(bar);
    rebuild();
    card.appendChild(kids);
    return card;
  }

  _num4arr(arr) {
    const w = el("div", "sf-num4");
    ["W", "E", "S", "N"].forEach((lab, i) => {
      const c = el("label", "sf-num4__c");
      c.appendChild(el("span", "sf-num4__l", lab));
      const inp = el("input", "sf-in sf-in--sm"); inp.type = "number";
      inp.value = arr[i] ?? 0;
      inp.addEventListener("input", () => { arr[i] = Number(inp.value) || 0; this._emit(); });
      c.appendChild(inp); w.appendChild(c);
    });
    return w;
  }
  _num4(k) {
    this.model[k] = this.model[k] || [1, 1, 1, 1];
    return this._num4arr(this.model[k]);
  }
}
