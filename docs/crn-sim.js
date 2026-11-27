/* crn-sim.js — mass-action and stochastic simulations for the Homeostasis site and slides.
 *
 * window.CRN_NETS: the networks formalized in the Lean library, with the ACR / adaptation values
 * proved there. window.CRNPlot(el, sceneId, opts): an animated plot of one scene.
 * The deterministic scenes integrate the same mass-action ODE as `massActionField` (RK4);
 * the stochastic scene is a Gillespie simulation of the CME for the toy ACR network.
 */
(function () {
  "use strict";

  /* ---------------- networks ---------------- */
  // complexes as stoichiometry vectors, reactions as [source, target] complex indices
  const NETS = {
    toy: {
      name: "Toy ACR network", file: "Kernel/Homeostasis.lean, Sanity/CRNHomeostasis.lean",
      species: ["A", "B"],
      complexes: [[1, 1], [0, 2], [0, 1], [1, 0]],
      reactions: [[0, 1], [2, 3]],
      rates: ["κ₀", "κ₁"], k: [1, 2],
      acr: 0, acrLabel: "x_A = κ₁/κ₀",
      acrValue: k => k[1] / k[0],
      T: 12,
      scheme: "A + B →(κ₀) 2B,   B →(κ₁) A"
    },
    envzD: {
      name: "EnvZ–OmpR, ADP (Fig. 2D)", file: "Design/EnvZOmpR.lean",
      species: ["EnvZ-D", "EnvZ", "EnvZ-T", "EnvZ-P", "OmpR", "EnvZ-OmpR-P", "OmpR-P", "EnvZ-OmpR-D-P"],
      complexes: [[1,0,0,0,0,0,0,0],[0,1,0,0,0,0,0,0],[0,0,1,0,0,0,0,0],[0,0,0,1,0,0,0,0],[0,0,0,1,1,0,0,0],
        [0,0,0,0,0,1,0,0],[0,1,0,0,0,0,1,0],[1,0,0,0,0,0,1,0],[0,0,0,0,0,0,0,1],[1,0,0,0,1,0,0,0]],
      reactions: [[0,1],[1,0],[1,2],[2,1],[2,3],[4,5],[5,4],[5,6],[7,8],[8,7],[8,9]],
      rates: ["κ₁","κ₂","κ₃","κ₄","κ₅","κ₆","κ₇","κ₈","κ₉","κ₁₀","κ₁₁"],
      k: [1,1,1,1,1,1,1,1,1,1,1],
      acr: 6, acrLabel: "[OmpR-P] = κ₁κ₃κ₅(κ₁₀+κ₁₁)/(κ₂(κ₄+κ₅)κ₉κ₁₁)",
      acrValue: k => k[0]*k[2]*k[4]*(k[9]+k[10]) / (k[1]*(k[3]+k[4])*k[8]*k[10]),
      T: 40,
      scheme: "EnvZ-D ⇌ EnvZ ⇌ EnvZ-T → EnvZ-P\nEnvZ-P + OmpR ⇌ EnvZ-OmpR-P → EnvZ + OmpR-P\nEnvZ-D + OmpR-P ⇌ EnvZ-OmpR-D-P → EnvZ-D + OmpR"
    },
    atp: {
      name: "EnvZ–OmpR, ATP (Fig. 2B)", file: "Design/EnvZOmpRATP.lean",
      species: ["X", "XT", "Xp", "Y", "XpY", "Yp", "XTYp"],
      complexes: [[1,0,0,0,0,0,0],[0,1,0,0,0,0,0],[0,0,1,0,0,0,0],[0,0,1,1,0,0,0],[0,0,0,0,1,0,0],
        [1,0,0,0,0,1,0],[0,1,0,0,0,1,0],[0,0,0,0,0,0,1],[0,1,0,1,0,0,0]],
      reactions: [[0,1],[1,0],[1,2],[3,4],[4,3],[4,5],[6,7],[7,6],[7,8]],
      rates: ["κ₁","κ₂","κ₃","κ₄","κ₅","κ₆","κ₇","κ₈","κ₉"],
      k: [1,1,1,1,1,1,1,1,1],
      acr: 5, acrLabel: "[Yp] = κ₃(κ₈+κ₉)/(κ₇κ₉)",
      acrValue: k => k[2]*(k[7]+k[8]) / (k[6]*k[8]),
      T: 60,
      scheme: "X ⇌ XT → Xp\nXp + Y ⇌ XpY → X + Yp\nXT + Yp ⇌ XTYp → XT + Y"
    },
    idh: {
      name: "IDHKP–IDH (Fig. 3)", file: "Design/IDHKP.lean",
      species: ["E", "Ip", "EIp", "I", "EIpI"],
      complexes: [[1,1,0,0,0],[0,0,1,0,0],[1,0,0,1,0],[0,0,1,1,0],[0,0,0,0,1],[0,1,1,0,0]],
      reactions: [[0,1],[1,0],[1,2],[3,4],[4,3],[4,5]],
      rates: ["κ₁","κ₂","κ₃","κ₄","κ₅","κ₆"],
      k: [1,1,1,1,1,1],
      acr: 3, acrLabel: "[I] = κ₃(κ₅+κ₆)/(κ₄κ₆)",
      acrValue: k => k[2]*(k[4]+k[5]) / (k[3]*k[5]),
      T: 40,
      scheme: "E + Ip ⇌ EIp → E + I\nEIp + I ⇌ EIpI → EIp + Ip"
    },
    phos: {
      name: "Phosphatase variant of Fig. 2B", file: "Design/EnvZOmpRPhosphatase.lean",
      species: ["X", "XT", "Xp", "Y", "XpY", "Yp", "Z", "ZYp"],
      complexes: [[1,0,0,0,0,0,0,0],[0,1,0,0,0,0,0,0],[0,0,1,0,0,0,0,0],[0,0,1,1,0,0,0,0],[0,0,0,0,1,0,0,0],
        [1,0,0,0,0,1,0,0],[0,0,0,0,0,1,1,0],[0,0,0,0,0,0,0,1],[0,0,0,1,0,0,1,0]],
      reactions: [[0,1],[1,0],[1,2],[3,4],[4,3],[4,5],[6,7],[7,6],[7,8]],
      rates: ["κ₁","κ₂","κ₃","κ₄","κ₅","κ₆","κ₇","κ₈","κ₉"],
      k: [1,1,1,1,1,1,1,1,1],
      acr: 5, noACR: true, acrLabel: "no ACR",
      acrValue: k => NaN,
      T: 60,
      scheme: "X ⇌ XT → Xp\nXp + Y ⇌ XpY → X + Yp\nZ + Yp ⇌ ZYp → Z + Y"
    },
    motif: {
      name: "Antithetic integral feedback", file: "Design/AntitheticMotif.lean, Design/AntitheticStability.lean",
      species: ["Z₁", "Z₂", "X"],
      complexes: [[0,0,0],[1,0,0],[0,0,1],[0,1,1],[1,1,0],[1,0,1]],
      // ∅ → Z₁ (μ), X → X + Z₂ (θ), Z₁ + Z₂ → ∅ (η), Z₁ → Z₁ + X (a), X → ∅ (γ)
      reactions: [[0,1],[2,3],[4,0],[1,5],[2,0]],
      rates: ["μ","θ","η","a","γ"],
      k: [1,1,1,1,1],
      acr: 2, acrLabel: "x = μ/θ for every γ > 0",
      acrValue: k => k[0] / k[1],
      T: 40,
      family: true,   // curves vary the disturbance γ instead of the initial state
      scheme: "∅ →(μ) Z₁,  X →(θ) X + Z₂,  Z₁ + Z₂ →(η) ∅\nZ₁ →(a) Z₁ + X,  X →(γ) ∅"
    }
  };

  /* ---------------- integration ---------------- */
  function field(net, k, dil) {
    const n = net.species.length, C = net.complexes, R = net.reactions;
    return function (x, out) {
      for (let i = 0; i < n; i++) out[i] = -dil * x[i];
      for (let r = 0; r < R.length; r++) {
        const s = C[R[r][0]], t = C[R[r][1]];
        let rate = k[r];
        for (let j = 0; j < n; j++) if (s[j]) rate *= Math.pow(Math.max(x[j], 0), s[j]);
        for (let j = 0; j < n; j++) out[j] += rate * (t[j] - s[j]);
      }
    };
  }
  function integrate(f, x0, T, steps) {
    const n = x0.length, h = T / steps, xs = [x0.slice()];
    let x = x0.slice();
    const k1 = new Array(n), k2 = new Array(n), k3 = new Array(n), k4 = new Array(n), y = new Array(n);
    for (let s = 0; s < steps; s++) {
      f(x, k1); for (let i = 0; i < n; i++) y[i] = x[i] + 0.5 * h * k1[i];
      f(y, k2); for (let i = 0; i < n; i++) y[i] = x[i] + 0.5 * h * k2[i];
      f(y, k3); for (let i = 0; i < n; i++) y[i] = x[i] + h * k3[i];
      f(y, k4);
      for (let i = 0; i < n; i++) x[i] += h / 6 * (k1[i] + 2 * k2[i] + 2 * k3[i] + k4[i]);
      xs.push(x.slice());
    }
    return xs;
  }
  // a seeded generator, so that "new initial states" is reproducible within a page
  function rng(seed) {
    let s = seed >>> 0;
    return () => { s = (s * 1664525 + 1013904223) >>> 0; return s / 4294967296; };
  }
  function gillespie(N, k, T, rand) {
    // toy ACR network on the level set x_A + x_B = N, started at the deterministic steady state
    let b = Math.max(1, N - Math.round(k[1] / k[0])), t = 0;
    const pts = [[0, N - b]];
    while (t < T) {
      const a = N - b, r0 = k[0] * a * b, r1 = k[1] * b, R = r0 + r1;
      if (R <= 0) { pts.push([T, a]); break; }
      t += -Math.log(1 - rand()) / R;
      if (t > T) { pts.push([T, a]); break; }
      if (rand() * R < r0) b += 1; else b -= 1;
      pts.push([t, N - b]);
    }
    return pts;
  }

  /* ---------------- drawing ---------------- */
  const PALETTE = ["#66d9e8", "#ff8a4c", "#a9e34b", "#f783ac", "#ffd43b", "#b197fc", "#74c0fc", "#ffa94d"];
  function niceMax(v) {
    if (!(v > 0)) return 1;
    const e = Math.pow(10, Math.floor(Math.log10(v))), m = v / e;
    return (m <= 1 ? 1 : m <= 2 ? 2 : m <= 4 ? 4 : m <= 5 ? 5 : m <= 8 ? 8 : 10) * e;
  }
  function fmt(v) { return Math.abs(v) >= 100 || v === Math.round(v) ? String(Math.round(v)) : v.toFixed(2).replace(/0+$/, "").replace(/\.$/, ""); }

  function CRNPlot(el, sceneId, opts) {
    opts = opts || {};
    const stochastic = sceneId === "extinction";
    const net = stochastic ? NETS.toy : NETS[sceneId];
    const k = (opts.k || (stochastic ? [1, 4] : net.k)).slice();
    let dil = 0, gamma = 1, N = opts.N || 10, seed = 7, species = net.acr, curves = [], progress = 1;
    let raf = 0, active = false, playing = true, last = 0;

    el.classList.add("cs");
    el.innerHTML = "";
    const canvas = document.createElement("canvas"); canvas.className = "cs-canvas";
    const bar = document.createElement("div"); bar.className = "cs-bar";
    el.append(canvas, bar);
    const btn = (label, title, fn) => {
      const b = document.createElement("button"); b.className = "cs-btn"; b.textContent = label; b.title = title;
      b.onclick = fn; bar.append(b); return b;
    };
    const playB = btn("❚❚", "Play / pause", () => { playing = !playing; playB.textContent = playing ? "❚❚" : "▶"; if (playing && progress >= 1) progress = 0; loop(); });
    playB.classList.add("cs-play");
    btn("↻", "Replay", () => { progress = 0; playing = true; playB.textContent = "❚❚"; loop(); });
    btn(stochastic ? "New run" : (net.family ? "New states" : "New initial states"), "Draw new random initial states", () => { seed += 1; compute(); progress = 0; playing = true; playB.textContent = "❚❚"; loop(); });

    if (!stochastic && opts.speciesSelect !== false) {
      const sel = document.createElement("select"); sel.className = "cs-sel"; sel.title = "Species to plot";
      net.species.forEach((s, i) => sel.append(new Option(s + (i === net.acr && !net.noACR ? "  (ACR)" : ""), i)));
      sel.value = species; sel.onchange = () => { species = +sel.value; draw(); };
      bar.append(sel);
    }
    const sliders = document.createElement("div"); sliders.className = "cs-sliders";
    function slider(label, min, max, val, log, onchange) {
      const w = document.createElement("label"); w.className = "cs-slider";
      const span = document.createElement("span"); const inp = document.createElement("input");
      inp.type = "range"; inp.min = 0; inp.max = 1000;
      const toPos = v => log ? 1000 * Math.log(v / min) / Math.log(max / min) : 1000 * (v - min) / (max - min);
      const toVal = p => log ? min * Math.pow(max / min, p / 1000) : min + (max - min) * p / 1000;
      inp.value = toPos(val);
      const show = v => span.textContent = label + " = " + (v < 10 ? v.toFixed(2) : Math.round(v));
      show(val);
      inp.oninput = () => { const v = toVal(+inp.value); show(v); onchange(v); compute(); progress = 1; draw(); };
      w.append(span, inp); sliders.append(w);
    }
    if (stochastic) {
      slider("N", 4, 40, N, false, v => { N = Math.round(v); });
      slider("κ₁/κ₀", 0.5, 8, k[1] / k[0], true, v => { k[0] = 1; k[1] = v; });
    } else if (opts.rateSliders !== false) {
      const which = opts.sliders || net.rates.map((_, i) => i);
      for (const r of which) slider(net.rates[r], 0.2, 5, k[r], true, v => { k[r] = v; });
      if (net.family || opts.dilution) slider("dilution", 0, 0.5, 0, false, v => { dil = v; });
    }
    if (sliders.children.length) el.append(sliders);
    const info = document.createElement("div"); info.className = "cs-info"; el.append(info);

    function compute() {
      const rand = rng(seed * 7919 + 13);
      curves = [];
      if (stochastic) {
        const T = opts.T || 20;
        for (let c = 0; c < (opts.runs || 3); c++) curves.push({ pts: gillespie(N, k, T, rand), T, label: "run " + (c + 1) });
        return;
      }
      const n = net.species.length, T = opts.T || net.T, steps = 4000;
      if (net.family) {
        const gammas = [0.25, 0.5, 1, 2, 4];
        for (const g of gammas) {
          const kk = k.slice(); kk[4] = g;
          const x0 = [0.1 + rand(), 0.1 + rand(), 0.1 + 2 * rand()];
          curves.push({ xs: integrate(field(net, kk, dil), x0, T, steps), T, label: "γ = " + g });
        }
      } else {
        for (let c = 0; c < (opts.curves || 6); c++) {
          const scale = 1 + 2 * rand();
          const x0 = Array.from({ length: n }, () => scale * (0.3 + rand()));
          curves.push({ xs: integrate(field(net, k, dil), x0, T, steps), T, label: "class " + (c + 1) });
        }
      }
    }

    function size() {
      const r = canvas.getBoundingClientRect(), d = window.devicePixelRatio || 1;
      const w = Math.max(200, Math.round(r.width)), h = Math.max(160, Math.round(r.height));
      if (canvas.width !== w * d || canvas.height !== h * d) { canvas.width = w * d; canvas.height = h * d; }
      return { w, h, d };
    }
    function draw() {
      const { w, h, d } = size(), g = canvas.getContext("2d");
      g.setTransform(d, 0, 0, d, 0, 0);
      g.fillStyle = "#0b1220"; g.fillRect(0, 0, w, h);
      const L = 46, Rm = 14, Tm = 14, B = 30, pw = w - L - Rm, ph = h - Tm - B;
      const T = curves.length ? curves[0].T : 1;
      const ref = stochastic ? k[1] / k[0] : net.acrValue(k);
      const showRef = stochastic || (species === net.acr && !net.noACR);
      let ymax = 0;
      if (stochastic) ymax = N;
      else for (const c of curves) for (const x of c.xs) ymax = Math.max(ymax, x[species]);
      if (showRef) ymax = Math.max(ymax, ref * 1.15);
      ymax = niceMax(ymax * 1.05);
      const X = t => L + pw * t / T, Y = v => Tm + ph * (1 - v / ymax);
      // grid and axes
      g.strokeStyle = "#1f2b44"; g.lineWidth = 1; g.fillStyle = "#9aa6bd"; g.font = "12px 'Source Sans 3', sans-serif";
      for (let i = 0; i <= 4; i++) {
        const v = ymax * i / 4, y = Y(v);
        g.beginPath(); g.moveTo(L, y); g.lineTo(L + pw, y); g.stroke();
        g.textAlign = "right"; g.textBaseline = "middle"; g.fillText(fmt(v), L - 6, y);
      }
      for (let i = 0; i <= 4; i++) {
        const t = T * i / 4; g.textAlign = "center"; g.textBaseline = "top"; g.fillText("t = " + fmt(t), X(t), Tm + ph + 8);
      }
      // reference lines
      g.setLineDash([6, 5]); g.lineWidth = 1.5;
      if (showRef) {
        g.strokeStyle = "#e8edf6"; g.beginPath(); g.moveTo(L, Y(ref)); g.lineTo(L + pw, Y(ref)); g.stroke();
      }
      if (stochastic) {
        g.strokeStyle = "#ff6b6b"; g.beginPath(); g.moveTo(L, Y(N)); g.lineTo(L + pw, Y(N)); g.stroke();
      }
      g.setLineDash([]);
      // curves
      const tEnd = T * progress;
      curves.forEach((c, ci) => {
        g.strokeStyle = PALETTE[ci % PALETTE.length]; g.lineWidth = 2.2; g.beginPath();
        if (stochastic) {
          let prev = null;
          for (const [t, a] of c.pts) {
            if (t > tEnd) { if (prev) g.lineTo(X(tEnd), Y(prev)); break; }
            if (prev === null) g.moveTo(X(t), Y(a)); else { g.lineTo(X(t), Y(prev)); g.lineTo(X(t), Y(a)); }
            prev = a;
          }
          if (prev !== null && c.pts[c.pts.length - 1][0] <= tEnd) g.lineTo(X(Math.min(tEnd, T)), Y(prev));
        } else {
          const m = Math.max(1, Math.round((c.xs.length - 1) * progress));
          for (let i = 0; i <= m; i += 4) {
            const t = T * i / (c.xs.length - 1), v = c.xs[i][species];
            if (i === 0) g.moveTo(X(t), Y(v)); else g.lineTo(X(t), Y(v));
          }
        }
        g.stroke();
      });
      // labels
      g.textAlign = "left"; g.textBaseline = "bottom"; g.font = "600 13px 'Source Sans 3', sans-serif";
      if (showRef) { g.fillStyle = "#e8edf6"; g.fillText((stochastic ? "deterministic ACR value κ₁/κ₀ = " : "Lean value ") + fmt(ref), L + 8, Y(ref) - 4); }
      if (stochastic) { g.fillStyle = "#ff6b6b"; g.fillText("extinction: x_A = N = " + N, L + 8, Y(N) + 18); }
      g.fillStyle = "#9aa6bd"; g.textAlign = "right";
      g.fillText(stochastic ? "x_A (copy number)" : net.species[species], L + pw - 4, Tm + 16);
      // info line
      if (stochastic) info.textContent = "Gillespie runs of the CME on the level set x_A + x_B = " + N + ". Each run is eventually absorbed at x_B = 0 (Lean: acrNet_extinction).";
      else if (net.family) info.textContent = dil > 0
        ? "With dilution " + dil.toFixed(2) + " the outputs no longer meet at μ/θ (Lean: aifNet_dilution_breaks_setpoint)."
        : "Five disturbances γ; the output adapts to μ/θ = " + fmt(ref) + " for each (Lean: aifNet_hasPerfectAdaptation).";
      else if (net.noACR && species === net.acr) info.textContent = curves.length + " compatibility classes, " + curves.length + " different limits: with a separate phosphatase Z there is no ACR in Yp (Lean: phos_not_hasACR), although the deficiency is still one.";
      else info.textContent = species === net.acr
        ? curves.length + " compatibility classes; at every positive steady state " + net.acrLabel + ". A class whose total is too small has no positive steady state."
        : "A non-ACR species: its steady value depends on the compatibility class.";
    }

    function loop() {
      cancelAnimationFrame(raf);
      if (!active) return;
      const step = now => {
        const dt = last ? Math.min(0.05, (now - last) / 1000) : 0; last = now;
        if (playing && progress < 1) { progress = Math.min(1, progress + dt / (opts.duration || 4)); draw(); }
        if (progress >= 1) { playing = false; playB.textContent = "▶"; draw(); last = 0; return; }
        raf = requestAnimationFrame(step);
      };
      last = 0; raf = requestAnimationFrame(step);
    }

    compute(); progress = 0;
    if ("ResizeObserver" in window) new ResizeObserver(() => draw()).observe(canvas);
    return {
      setActive(on) {
        active = on;
        if (on) { progress = 0; playing = true; playB.textContent = "❚❚"; draw(); loop(); }
        else cancelAnimationFrame(raf);
      },
      redraw: draw
    };
  }

  window.CRN_NETS = NETS;
  window.CRNPlot = CRNPlot;
})();
