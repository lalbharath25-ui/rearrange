/* Pixel rearrangement engine — pure, no DOM, runs in the browser (window.Engine) and in node.
   State holds a permutation: assign[t] = the source pixel sitting at target cell t.
   Pixels are only ever moved, never recoloured, so every result is an exact rearrangement
   of the input. Cost is squared distance in a luma-weighted colour space, plus an optional
   "stay near home" term on how far each pixel travels. Source pixels may come from a grid of
   a different shape (same count); opts.srcX/srcY give their home positions in target cells. */
(function (root, factory) {
  if (typeof module === 'object' && module.exports) module.exports = factory();
  else root.Engine = factory();
})(typeof self !== 'undefined' ? self : this, function () {
  'use strict';

  var K_LUMA = 1.0;       // luminance carries the structure of the portrait
  var K_CHROMA = 0.5;     // hue matters, but less
  var HOME_SCALE = 65025; // home=1: a full-height trip costs as much as a 255-level colour error

  function features(rgba, n) {
    var f = new Float32Array(n * 3);
    for (var i = 0; i < n; i++) {
      var r = rgba[i * 4], g = rgba[i * 4 + 1], b = rgba[i * 4 + 2];
      f[i * 3] = (0.299 * r + 0.587 * g + 0.114 * b) * K_LUMA;
      f[i * 3 + 1] = (r - g) * K_CHROMA;
      f[i * 3 + 2] = ((r + g) * 0.5 - b) * K_CHROMA;
    }
    return f;
  }

  function lumaOrder(f, n) {
    var idx = new Array(n);
    for (var i = 0; i < n; i++) idx[i] = i;
    idx.sort(function (a, b) { return (f[a * 3] - f[b * 3]) || (a - b); });
    return Int32Array.from(idx);
  }

  // Start from a brightness-rank match (exact histogram specification), then refine().
  function create(srcRGBA, tgtRGBA, W, H, opts) {
    opts = opts || {};
    var n = W * H;
    var S = features(srcRGBA, n), T = features(tgtRGBA, n);
    var cx = new Float32Array(n), cy = new Float32Array(n), sx = new Float32Array(n), sy = new Float32Array(n);
    for (var i = 0; i < n; i++) {
      cx[i] = (i % W) / H; cy[i] = ((i / W) | 0) / H;
      sx[i] = opts.srcX ? opts.srcX[i] / H : cx[i];
      sy[i] = opts.srcY ? opts.srcY[i] / H : cy[i];
    }
    var sOrd = lumaOrder(S, n), tOrd = lumaOrder(T, n);
    var assign = new Int32Array(n), posOf = new Int32Array(n), tRank = new Int32Array(n);
    for (var r = 0; r < n; r++) {
      assign[tOrd[r]] = sOrd[r];
      posOf[sOrd[r]] = tOrd[r];
      tRank[tOrd[r]] = r;
    }
    var st = {
      W: W, H: H, n: n, S: S, T: T, cx: cx, cy: cy, sx: sx, sy: sy,
      assign: assign, posOf: posOf, tOrd: tOrd, tRank: tRank,
      win: Math.max(8, Math.round(n * 0.01)),
      home: 0, homeW: 0, cost: 0, tried: 0, accepted: 0,
      seed: (opts.seed >>> 0) || 0x9e3779b9
    };
    setHome(st, opts.home || 0);
    return st;
  }

  function setHome(st, home) {
    st.home = home;
    st.homeW = home * home * HOME_SCALE;
    st.cost = totalCost(st);
  }

  function cellCost(st, s, t) {
    var S = st.S, T = st.T, s3 = s * 3, t3 = t * 3;
    var d0 = S[s3] - T[t3], d1 = S[s3 + 1] - T[t3 + 1], d2 = S[s3 + 2] - T[t3 + 2];
    var dx = st.sx[s] - st.cx[t], dy = st.sy[s] - st.cy[t];
    return d0 * d0 + d1 * d1 + d2 * d2 + st.homeW * (dx * dx + dy * dy);
  }

  function totalCost(st) {
    var c = 0;
    for (var t = 0; t < st.n; t++) c += cellCost(st, st.assign[t], t);
    return c;
  }

  // Greedy pair swaps. For squared distance, swapping the sources a,b at cells i,j lowers the
  // cost by exactly 2(a-b)·(j-i), so a trial is two short dot products. Three in four partners
  // are drawn from cells of similar target brightness, where useful trades concentrate.
  function refine(st, iters) {
    var n = st.n, S = st.S, T = st.T, cx = st.cx, cy = st.cy, sx = st.sx, sy = st.sy;
    var assign = st.assign, posOf = st.posOf, tOrd = st.tOrd, tRank = st.tRank;
    var win = st.win, span = 2 * win + 1, hw = st.homeW;
    var x = st.seed | 0, gained = 0, acc = 0;
    for (var k = 0; k < iters; k++) {
      x ^= x << 13; x ^= x >>> 17; x ^= x << 5;
      var i = (x >>> 0) % n, j;
      x ^= x << 13; x ^= x >>> 17; x ^= x << 5;
      var r = x >>> 0;
      if (r & 3) {
        var rk = tRank[i] + ((r >>> 2) % span) - win;
        if (rk < 0 || rk >= n) continue;
        j = tOrd[rk];
      } else {
        j = (r >>> 2) % n;
      }
      if (i === j) continue;
      var a = assign[i], b = assign[j];
      var a3 = a * 3, b3 = b * 3, i3 = i * 3, j3 = j * 3;
      var delta = (S[a3] - S[b3]) * (T[j3] - T[i3]) +
                  (S[a3 + 1] - S[b3 + 1]) * (T[j3 + 1] - T[i3 + 1]) +
                  (S[a3 + 2] - S[b3 + 2]) * (T[j3 + 2] - T[i3 + 2]);
      if (hw > 0) delta += hw * ((sx[a] - sx[b]) * (cx[j] - cx[i]) + (sy[a] - sy[b]) * (cy[j] - cy[i]));
      if (delta > 0) {
        assign[i] = b; assign[j] = a; posOf[a] = j; posOf[b] = i;
        gained += 2 * delta; acc++;
      }
    }
    st.seed = x; st.cost -= gained; st.tried += iters; st.accepted += acc;
    return acc;
  }

  // RGBA of the rearranged picture (target grid), built only from source pixels.
  function arrange(st, srcRGBA, out) {
    out = out || new Uint8ClampedArray(st.n * 4);
    for (var t = 0; t < st.n; t++) {
      var s = st.assign[t] * 4, o = t * 4;
      out[o] = srcRGBA[s]; out[o + 1] = srcRGBA[s + 1]; out[o + 2] = srcRGBA[s + 2]; out[o + 3] = 255;
    }
    return out;
  }

  // 100 × (1 − RGB RMSE / 255) between the rearranged picture and the target.
  function matchPct(st, srcRGBA, tgtRGBA) {
    var se = 0;
    for (var t = 0; t < st.n; t++) {
      var s = st.assign[t] * 4, o = t * 4;
      var dr = srcRGBA[s] - tgtRGBA[o], dg = srcRGBA[s + 1] - tgtRGBA[o + 1], db = srcRGBA[s + 2] - tgtRGBA[o + 2];
      se += dr * dr + dg * dg + db * db;
    }
    return 100 * (1 - Math.sqrt(se / (3 * st.n)) / 255);
  }

  // Brightness correlation (Pearson, %) between the rearranged picture and the target:
  // how recognisable the portrait is, independent of the source's palette.
  function likeness(st) {
    var n = st.n, S = st.S, T = st.T, a = 0, b = 0, aa = 0, bb = 0, ab = 0;
    for (var t = 0; t < n; t++) {
      var x = S[st.assign[t] * 3], y = T[t * 3];
      a += x; b += y; aa += x * x; bb += y * y; ab += x * y;
    }
    a /= n; b /= n;
    var va = aa / n - a * a, vb = bb / n - b * b;
    if (va < 1e-6 || vb < 1e-6) return 0;
    return Math.max(0, 100 * (ab / n - a * b) / Math.sqrt(va * vb));
  }

  // Factor pair (sw × sh = n) whose shape best fits the given aspect (w/h); null if none within tol.
  function bestGrid(n, aspect) {
    var best = null, ideal = Math.sqrt(n * aspect);
    for (var sw = Math.max(1, Math.floor(ideal * 0.7)); sw <= Math.ceil(ideal * 1.4); sw++) {
      if (n % sw) continue;
      var err = Math.abs(Math.log((sw / (n / sw)) / aspect));
      if (!best || err < best.err) best = { sw: sw, sh: n / sw, err: err };
    }
    return best;
  }

  return { create: create, refine: refine, setHome: setHome, totalCost: totalCost, arrange: arrange,
           matchPct: matchPct, likeness: likeness, bestGrid: bestGrid };
});
