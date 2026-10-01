/* Decoding for (almost) any image file a visitor can hand the page.
   Pipeline: sniff the magic bytes → let the browser's own decoder try → fall back to
   built-in decoders (PSD, camera-RAW previews, TGA, QOI, Netpbm, Radiance HDR) or to
   libraries fetched from jsDelivr only when that format turns up (HEIC/HEIF, TIFF, JPEG XL).
   The pure decoders take a Uint8Array and return {width, height, data: RGBA}, so node can
   test them; toCanvas() is the browser entry point. */
(function (root, factory) {
  if (typeof module === 'object' && module.exports) module.exports = factory();
  else root.Formats = factory();
})(typeof self !== 'undefined' ? self : this, function () {
  'use strict';

  const CDN = 'https://cdn.jsdelivr.net/npm/';
  const LIBS = {
    pako: { url: CDN + 'pako@2.1.0/dist/pako.min.js', sri: 'sha384-rNlaE5fs9dGIjmxWDALQh/RBAaGRYT5ChrzHo6tRfgrZ36iRFAiquP5g41Jsv+0j' },
    utif: { url: CDN + 'utif@3.1.0/UTIF.js', sri: 'sha384-RyBmXHdfZ/Uon+ud+/AqSyWpUWnKYt2tkRG/P4gWoRUGDU+qIAV3tGBPNlYTBZEF' },
    heic: { url: CDN + 'heic-to@1.6.5/dist/iife/heic-to.js', sri: 'sha384-pztinaMu47Qnun2X85+8CYi3nu+Sz1aLjadtPyHxdG2G9otfa3kLoI1w+HiCVEjK' },
    jxl: CDN + '@jsquash/jxl@1.3.0/decode.js'
  };
  const MAX_BYTES = 400e6, MAX_PIXELS = 150e6;

  const RAW_EXT = new Set(['dng', 'cr2', 'cr3', 'crw', 'nef', 'nrw', 'arw', 'srf', 'sr2', 'orf', 'rw2', 'raf',
    'pef', 'srw', 'x3f', '3fr', 'fff', 'erf', 'kdc', 'dcr', 'mrw', 'mos', 'rwl', 'iiq', 'raw', 'gpr']);
  const NAMES = { jpeg: 'JPEG', png: 'PNG', gif: 'GIF', webp: 'WebP', bmp: 'BMP', ico: 'icon', avif: 'AVIF',
    heif: 'HEIC', tiff: 'TIFF', raw: 'camera RAW', psd: 'Photoshop', jxl: 'JPEG XL', qoi: 'QOI', pnm: 'Netpbm',
    hdr: 'Radiance HDR', tga: 'TGA', svg: 'SVG', jp2: 'JPEG 2000' };
  const MIME = { jpeg: 'image/jpeg', png: 'image/png', gif: 'image/gif', webp: 'image/webp', bmp: 'image/bmp',
    ico: 'image/x-icon', avif: 'image/avif', heif: 'image/heic', tiff: 'image/tiff', jxl: 'image/jxl', jp2: 'image/jp2' };
  const UNSUPPORTED = {
    exr: 'OpenEXR files aren’t supported yet — export it as PNG or TIFF and try again.',
    pdf: 'That’s a PDF, not an image. Export the page as PNG or JPG first.'
  };
  const NEVER_NATIVE = new Set(['raw', 'psd', 'tga', 'qoi', 'pnm', 'hdr', 'svg']);

  // Extensions for desktop file pickers; phones keep plain image/* so their photo pickers still open.
  const ACCEPT = 'image/*,.heic,.heif,.avif,.jxl,.tif,.tiff,.psd,.psb,.tga,.qoi,.ppm,.pgm,.pbm,.pnm,.hdr,.svg,.ico,.cur,.bmp,.jp2,.j2k,' +
    [...RAW_EXT].map((e) => '.' + e).join(',');

  function fmtErr(msg) { const e = new Error(msg); e.friendly = msg; return e; }

  function ascii(u8, a, b) {
    let s = '';
    for (let i = a; i < Math.min(b, u8.length); i++) s += String.fromCharCode(u8[i]);
    return s;
  }
  function extOf(name) { const m = /\.([a-z0-9]+)$/i.exec(name || ''); return m ? m[1].toLowerCase() : ''; }

  function isSvg(u8) {
    const head = ascii(u8, 0, 2048).replace(/^﻿|^\xEF\xBB\xBF/, '').trimStart();
    return head[0] === '<' && /<svg[\s>]/i.test(head);
  }

  // ---------- sniffing ----------
  function sniff(u8, name) {
    const e = extOf(name), a4 = ascii(u8, 0, 4);
    if (u8[0] === 0xff && u8[1] === 0xd8 && u8[2] === 0xff) return 'jpeg';
    if (a4 === '\x89PNG') return 'png';
    if (a4 === 'GIF8') return 'gif';
    if (a4 === 'RIFF' && ascii(u8, 8, 12) === 'WEBP') return 'webp';
    if (ascii(u8, 4, 8) === 'ftyp') {
      const brand = ascii(u8, 8, 12), box = (u8[0] << 24 | u8[1] << 16 | u8[2] << 8 | u8[3]) >>> 0;
      const compat = ascii(u8, 16, Math.min(box, 64));
      if (brand === 'crx ') return 'raw';                                    // Canon CR3
      if (brand === 'avif' || brand === 'avis' || compat.includes('avif')) return 'avif';
      if (/^(heic|heix|hevc|hevx|heim|heis|mif1|mif2|msf1)$/.test(brand)) return 'heif';
      return 'unknown';
    }
    if (a4 === 'II*\0' || a4 === 'MM\0*') return RAW_EXT.has(e) ? 'raw' : 'tiff';
    if (a4 === 'IIRO' || a4 === 'IIRS' || a4 === 'MMOR' || a4 === 'IIU\0') return 'raw'; // Olympus, Panasonic
    if (ascii(u8, 0, 15) === 'FUJIFILMCCD-RAW') return 'raw';
    if (a4 === '8BPS') return 'psd';
    if ((u8[0] === 0xff && u8[1] === 0x0a) || ascii(u8, 4, 8) === 'JXL ') return 'jxl';
    if (a4 === 'qoif') return 'qoi';
    if (u8[0] === 0x50 && u8[1] >= 0x31 && u8[1] <= 0x36 && (u8[2] <= 32 || u8[2] === 35)) return 'pnm';
    if (ascii(u8, 0, 2) === '#?') return 'hdr';
    if (u8[0] === 0x76 && u8[1] === 0x2f && u8[2] === 0x31 && u8[3] === 0x01) return 'exr';
    if (a4 === '%PDF') return 'pdf';
    if (ascii(u8, 4, 8) === 'jP  ' || (u8[0] === 0xff && u8[1] === 0x4f && u8[2] === 0xff && u8[3] === 0x51)) return 'jp2';
    if (u8[0] === 0x42 && u8[1] === 0x4d && e !== 'tga') return 'bmp';
    // TGA has no magic, and its common header (00 00 02 00…) collides with .cur icons: trust the name first.
    if (e === 'tga' || e === 'icb' || e === 'vda' || e === 'vst' || ascii(u8, u8.length - 18, u8.length - 2) === 'TRUEVISION-XFILE') return 'tga';
    if (u8[0] === 0 && u8[1] === 0 && (u8[2] === 1 || u8[2] === 2) && u8[3] === 0) return 'ico';
    if (isSvg(u8)) return 'svg';
    if (RAW_EXT.has(e)) return 'raw';
    return 'unknown';
  }

  function checkSize(w, h, what) {
    if (!(w > 0 && h > 0)) throw fmtErr('This ' + what + ' file looks damaged.');
    if (w * h > MAX_PIXELS) throw fmtErr('That image is too large to open in a browser (' + Math.round(w * h / 1e6) + ' megapixels).');
  }

  // ---------- Netpbm: P1–P6 ----------
  function decodePNM(u8) {
    const type = u8[1] - 48;
    let p = 2;
    const skip = () => {
      for (;;) {
        while (p < u8.length && u8[p] <= 32) p++;
        if (u8[p] === 35) { while (p < u8.length && u8[p] !== 10 && u8[p] !== 13) p++; } else return;
      }
    };
    const num = () => {
      skip();
      let v = 0, any = false;
      while (p < u8.length && u8[p] >= 48 && u8[p] <= 57) { v = v * 10 + u8[p++] - 48; any = true; }
      if (!any) throw fmtErr('This Netpbm file looks damaged.');
      return v;
    };
    const w = num(), h = num(), max = (type === 1 || type === 4) ? 1 : num();
    checkSize(w, h, 'Netpbm');
    if (type >= 4) p++;                              // one whitespace byte ends a binary header
    const n = w * h, out = new Uint8ClampedArray(n * 4), k = 255 / max;
    const set = (i, r, g, b) => { const o = i * 4; out[o] = r; out[o + 1] = g; out[o + 2] = b; out[o + 3] = 255; };
    if (type === 1) {
      for (let i = 0; i < n; i++) {
        while (p < u8.length && u8[p] !== 48 && u8[p] !== 49) {
          if (u8[p] === 35) { while (p < u8.length && u8[p] !== 10) p++; } else p++;
        }
        const v = u8[p++] === 49 ? 0 : 255;
        set(i, v, v, v);
      }
    } else if (type === 4) {
      const rb = Math.ceil(w / 8);
      for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
        const v = (u8[p + y * rb + (x >> 3)] >> (7 - (x & 7))) & 1 ? 0 : 255;
        set(y * w + x, v, v, v);
      }
    } else {
      const ch = (type === 3 || type === 6) ? 3 : 1, wide = max > 255, c = [0, 0, 0];
      for (let i = 0; i < n; i++) {
        for (let j = 0; j < ch; j++) {
          let v;
          if (type <= 3) v = num();
          else if (wide) { v = (u8[p] << 8) | u8[p + 1]; p += 2; }
          else v = u8[p++];
          c[j] = v * k;
        }
        if (ch === 1) set(i, c[0], c[0], c[0]); else set(i, c[0], c[1], c[2]);
      }
    }
    return { width: w, height: h, data: out };
  }

  // ---------- TGA: colour-mapped / true-colour / grey, raw or RLE ----------
  function decodeTGA(u8) {
    const idLen = u8[0], cmType = u8[1], type = u8[2], base = type & 7, rle = type >= 9;
    const cmFirst = u8[3] | u8[4] << 8, cmLen = u8[5] | u8[6] << 8, cmBits = u8[7];
    const w = u8[12] | u8[13] << 8, h = u8[14] | u8[15] << 8, bpp = u8[16], desc = u8[17];
    if (base < 1 || base > 3 || (type & ~(8 | 7))) throw fmtErr('This TGA file uses a variant that isn’t supported.');
    checkSize(w, h, 'TGA');
    const alphaBits = desc & 15, bytes = Math.ceil(bpp / 8);
    let p = 18 + idLen;
    const color = (q, bits, dst, o) => {
      if (bits === 15 || bits === 16) {
        const v = u8[q] | u8[q + 1] << 8;
        dst[o] = (v >> 10 & 31) * 255 / 31; dst[o + 1] = (v >> 5 & 31) * 255 / 31; dst[o + 2] = (v & 31) * 255 / 31;
        dst[o + 3] = bits === 16 && alphaBits ? (v & 0x8000 ? 255 : 0) : 255;
      } else {
        dst[o] = u8[q + 2]; dst[o + 1] = u8[q + 1]; dst[o + 2] = u8[q];
        dst[o + 3] = bits === 32 && alphaBits ? u8[q + 3] : 255;
      }
    };
    let pal = null;
    if (cmType === 1) {
      const eb = Math.ceil(cmBits / 8);
      pal = new Uint8Array((cmFirst + cmLen) * 4);
      for (let i = 0; i < cmLen; i++, p += eb) color(p, cmBits, pal, (cmFirst + i) * 4);
    }
    const px = new Uint8Array(4);
    const read = (q) => {
      if (base === 1) {
        const idx = bytes === 2 ? u8[q] | u8[q + 1] << 8 : u8[q];
        if (pal && idx * 4 + 3 < pal.length) { px[0] = pal[idx * 4]; px[1] = pal[idx * 4 + 1]; px[2] = pal[idx * 4 + 2]; px[3] = pal[idx * 4 + 3]; }
        else { px[0] = px[1] = px[2] = 0; px[3] = 255; }
      } else if (base === 3) {
        px[0] = px[1] = px[2] = u8[q]; px[3] = bytes === 2 && alphaBits ? u8[q + 1] : 255;
      } else color(q, bpp, px, 0);
    };
    const n = w * h, out = new Uint8ClampedArray(n * 4), topDown = desc & 0x20, rtl = desc & 0x10;
    const put = (i) => {
      const x = i % w, y = (i / w) | 0;
      const o = ((topDown ? y : h - 1 - y) * w + (rtl ? w - 1 - x : x)) * 4;
      out[o] = px[0]; out[o + 1] = px[1]; out[o + 2] = px[2]; out[o + 3] = px[3];
    };
    if (!rle) {
      for (let i = 0; i < n && p + bytes <= u8.length; i++, p += bytes) { read(p); put(i); }
    } else {
      let i = 0;
      while (i < n && p < u8.length) {
        const hd = u8[p++], cnt = (hd & 127) + 1;
        if (hd & 128) { read(p); p += bytes; for (let k = 0; k < cnt && i < n; k++) put(i++); }
        else for (let k = 0; k < cnt && i < n; k++, p += bytes) { read(p); put(i++); }
      }
    }
    let anyAlpha = false;                            // alpha declared but never written = opaque
    for (let o = 3; o < out.length; o += 4) if (out[o]) { anyAlpha = true; break; }
    if (!anyAlpha) for (let o = 3; o < out.length; o += 4) out[o] = 255;
    return { width: w, height: h, data: out };
  }

  // ---------- QOI ----------
  function decodeQOI(u8) {
    const dv = new DataView(u8.buffer, u8.byteOffset, u8.byteLength);
    const w = dv.getUint32(4), h = dv.getUint32(8);
    checkSize(w, h, 'QOI');
    const n = w * h, out = new Uint8ClampedArray(n * 4), index = new Uint8Array(256);
    let r = 0, g = 0, b = 0, a = 255, run = 0, p = 14;
    for (let i = 0; i < n; i++) {
      if (run > 0) run--;
      else if (p < u8.length) {
        const b1 = u8[p++];
        if (b1 === 0xfe) { r = u8[p++]; g = u8[p++]; b = u8[p++]; }
        else if (b1 === 0xff) { r = u8[p++]; g = u8[p++]; b = u8[p++]; a = u8[p++]; }
        else if ((b1 & 0xc0) === 0x00) { const o = b1 * 4; r = index[o]; g = index[o + 1]; b = index[o + 2]; a = index[o + 3]; }
        else if ((b1 & 0xc0) === 0x40) {
          r = (r + ((b1 >> 4) & 3) - 2) & 255; g = (g + ((b1 >> 2) & 3) - 2) & 255; b = (b + (b1 & 3) - 2) & 255;
        } else if ((b1 & 0xc0) === 0x80) {
          const b2 = u8[p++], vg = (b1 & 0x3f) - 32;
          r = (r + vg - 8 + ((b2 >> 4) & 15)) & 255; g = (g + vg) & 255; b = (b + vg - 8 + (b2 & 15)) & 255;
        } else run = b1 & 0x3f;
        const o = ((r * 3 + g * 5 + b * 7 + a * 11) % 64) * 4;
        index[o] = r; index[o + 1] = g; index[o + 2] = b; index[o + 3] = a;
      }
      const o = i * 4;
      out[o] = r; out[o + 1] = g; out[o + 2] = b; out[o + 3] = a;
    }
    return { width: w, height: h, data: out };
  }

  // ---------- PSD / PSB: the flattened composite Photoshop stores after the layers ----------
  function unpackBits(src, p, len, dst, o, n) {
    const end = Math.min(p + len, src.length), stop = o + n;
    while (p < end && o < stop) {
      const hd = src[p++];
      if (hd > 128) { const v = src[p++]; for (let k = 257 - hd; k > 0 && o < stop; k--) dst[o++] = v; }
      else if (hd < 128) for (let k = 0; k <= hd && o < stop; k++) dst[o++] = src[p++];
    }
  }

  function labToRgb(L, a, b) {
    let y = (L + 16) / 116, x = a / 500 + y, z = y - b / 200;
    const f = (t) => t > 0.206893 ? t * t * t : (t - 16 / 116) / 7.787;
    x = 0.95047 * f(x); y = f(y); z = 1.08883 * f(z);
    const g = (c) => 255 * (c > 0.0031308 ? 1.055 * Math.pow(c, 1 / 2.4) - 0.055 : 12.92 * c);
    return [g(x * 3.2406 + y * -1.5372 + z * -0.4986), g(x * -0.9689 + y * 1.8758 + z * 0.0415), g(x * 0.0557 + y * -0.2040 + z * 1.0570)];
  }

  function decodePSD(u8) {
    const dv = new DataView(u8.buffer, u8.byteOffset, u8.byteLength);
    const ver = dv.getUint16(4), ch = dv.getUint16(12), h = dv.getUint32(14), w = dv.getUint32(18);
    const depth = dv.getUint16(22), mode = dv.getUint16(24);
    if (ver !== 1 && ver !== 2) throw fmtErr('This Photoshop file looks damaged.');
    checkSize(w, h, 'Photoshop');
    if (![1, 8, 16, 32].includes(depth)) throw fmtErr('This Photoshop file uses an unsupported bit depth.');
    let p = 26;
    const cmStart = p + 4;
    p = cmStart + dv.getUint32(p);                         // colour-mode data (indexed palette lives here)
    p += 4 + dv.getUint32(p);                              // image resources
    p += ver === 2 ? 8 + dv.getUint32(p) * 4294967296 + dv.getUint32(p + 4) : 4 + dv.getUint32(p);  // layers: skipped
    const comp = dv.getUint16(p); p += 2;
    const bpc = depth === 1 ? 0 : depth / 8, rowBytes = depth === 1 ? Math.ceil(w / 8) : w * bpc;
    const need = Math.min(ch, mode === 4 ? 4 : (mode === 3 || mode === 9) ? 3 : 1);
    const planes = [];
    if (comp === 0) {
      for (let c = 0; c < need; c++) planes.push(u8.subarray(p + c * rowBytes * h, p + (c + 1) * rowBytes * h));
    } else if (comp === 1) {
      const cb = ver === 2 ? 4 : 2;
      let dp = p + ch * h * cb;
      for (let c = 0; c < need; c++) {
        const plane = new Uint8Array(rowBytes * h);
        for (let y = 0; y < h; y++) {
          const ci = p + (c * h + y) * cb, len = cb === 2 ? dv.getUint16(ci) : dv.getUint32(ci);
          unpackBits(u8, dp, len, plane, y * rowBytes, rowBytes);
          dp += len;
        }
        planes.push(plane);
      }
    } else throw fmtErr('This Photoshop file stores its preview with ZIP compression. Re-save it with “Maximize compatibility” on.');
    if (planes.length < need || planes[need - 1].length < rowBytes * h) throw fmtErr('This Photoshop file looks truncated.');

    const s = depth === 8 ? (c, i) => planes[c][i]
      : depth === 16 ? (c, i) => planes[c][i * 2]          // big-endian: high byte first
      : depth === 32 ? (c, i) => { const q = planes[c], v = new DataView(q.buffer, q.byteOffset + i * 4, 4).getFloat32(0); return 255 * Math.pow(Math.min(1, Math.max(0, v)), 1 / 2.2); }
      : null;
    const n = w * h, out = new Uint8ClampedArray(n * 4);
    for (let i = 0; i < n; i++) {
      let r, g, b;
      if (mode === 0) { const x = i % w, y = (i / w) | 0; r = g = b = (planes[0][y * rowBytes + (x >> 3)] >> (7 - (x & 7))) & 1 ? 0 : 255; }
      else if (mode === 2) { const k = s(0, i); r = u8[cmStart + k]; g = u8[cmStart + 256 + k]; b = u8[cmStart + 512 + k]; }
      else if (mode === 3) { r = s(0, i); g = s(1, i); b = s(2, i); }
      else if (mode === 4) { const k = s(3, i) / 255; r = s(0, i) * k; g = s(1, i) * k; b = s(2, i) * k; }   // stored inverted
      else if (mode === 9) { [r, g, b] = labToRgb(s(0, i) * 100 / 255, s(1, i) - 128, s(2, i) - 128); }
      else { r = g = b = s(0, i); }                                                                           // grey, duotone, multichannel
      const o = i * 4;
      out[o] = r; out[o + 1] = g; out[o + 2] = b; out[o + 3] = 255;
    }
    return { width: w, height: h, data: out };
  }

  // ---------- Radiance HDR (RGBE), tone-mapped to 8-bit ----------
  function decodeHDR(u8) {
    let p = 0;
    const line = () => { let s = ''; while (p < u8.length && u8[p] !== 10) s += String.fromCharCode(u8[p++]); p++; return s; };
    const head = [];
    for (let s = line(); s !== ''; s = line()) { head.push(s); if (p >= u8.length || head.length > 200) throw fmtErr('This .hdr file looks damaged.'); }
    if (!/^#\?/.test(head[0])) throw fmtErr('This .hdr file looks damaged.');
    if (head.some((s) => /^FORMAT=32-bit_rle_xyze/.test(s))) throw fmtErr('XYZE-encoded .hdr files aren’t supported.');
    const m = /^-Y (\d+) \+X (\d+)$/.exec(line().trim());
    if (!m) throw fmtErr('This .hdr file uses an unusual orientation that isn’t supported.');
    const h = +m[1], w = +m[2];
    checkSize(w, h, 'HDR');
    const n = w * h, rgbe = new Uint8Array(n * 4), scan = new Uint8Array(w * 4);
    for (let y = 0; y < h && p < u8.length; y++) {
      if (w >= 8 && w < 32768 && u8[p] === 2 && u8[p + 1] === 2 && ((u8[p + 2] << 8) | u8[p + 3]) === w) {
        p += 4;
        for (let c = 0; c < 4; c++) {
          let x = 0;
          while (x < w && p < u8.length) {
            let cnt = u8[p++];
            if (cnt > 128) { cnt -= 128; const v = u8[p++]; while (cnt-- > 0 && x < w) scan[(x++) * 4 + c] = v; }
            else while (cnt-- > 0 && x < w) scan[(x++) * 4 + c] = u8[p++];
          }
        }
        rgbe.set(scan, y * w * 4);
      } else {
        rgbe.set(u8.subarray(p, p + w * 4), y * w * 4);
        p += w * 4;
      }
    }
    // Reinhard global operator keyed to the log-average luminance, then display gamma.
    const f = new Float32Array(n * 3), lum = new Float32Array(n);
    let logSum = 0;
    for (let i = 0; i < n; i++) {
      const e = rgbe[i * 4 + 3];
      if (e) {
        const k = Math.pow(2, e - 136);
        f[i * 3] = (rgbe[i * 4] + 0.5) * k; f[i * 3 + 1] = (rgbe[i * 4 + 1] + 0.5) * k; f[i * 3 + 2] = (rgbe[i * 4 + 2] + 0.5) * k;
      }
      lum[i] = 0.2126 * f[i * 3] + 0.7152 * f[i * 3 + 1] + 0.0722 * f[i * 3 + 2];
      logSum += Math.log(1e-6 + lum[i]);
    }
    const key = 0.18 / Math.exp(logSum / n), out = new Uint8ClampedArray(n * 4);
    for (let i = 0; i < n; i++) {
      const L = lum[i] * key, s = lum[i] > 0 ? (L / (1 + L)) / lum[i] : 0;
      for (let c = 0; c < 3; c++) out[i * 4 + c] = 255 * Math.pow(Math.min(1, f[i * 3 + c] * s), 1 / 2.2);
      out[i * 4 + 3] = 255;
    }
    return { width: w, height: h, data: out };
  }

  // ---------- camera RAW: the camera's own embedded JPEG preview ----------
  // Walks JPEG markers from an SOI so thumbnails nested inside EXIF are skipped, not mistaken for the end.
  function jpegExtent(u8, s) {
    let p = s + 2, w = 0, h = 0, sof = -1;
    while (p + 1 < u8.length) {
      if (u8[p] !== 0xff) return null;
      const m = u8[p + 1];
      if (m === 0xff) { p++; continue; }
      if (m === 0xd9) return { start: s, end: p + 2, width: w, height: h, sof };
      if ((m >= 0xd0 && m <= 0xd7) || m === 0x01) { p += 2; continue; }
      if (p + 3 >= u8.length) return null;
      const len = u8[p + 2] << 8 | u8[p + 3];
      if (len < 2) return null;
      if (m >= 0xc0 && m <= 0xcf && m !== 0xc4 && m !== 0xc8 && m !== 0xcc && p + 8 < u8.length) {
        sof = m - 0xc0; h = u8[p + 5] << 8 | u8[p + 6]; w = u8[p + 7] << 8 | u8[p + 8];
      }
      p += 2 + len;
      if (m === 0xda) {
        while (p + 1 < u8.length && !(u8[p] === 0xff && u8[p + 1] !== 0 && !(u8[p + 1] >= 0xd0 && u8[p + 1] <= 0xd7))) p++;
        if (p + 1 >= u8.length) return sof >= 0 ? { start: s, end: u8.length, width: w, height: h, sof } : null;
      }
    }
    return null;
  }

  // Browser-decodable (baseline / extended / progressive) JPEGs inside a file, biggest first.
  function findJpegs(u8) {
    const found = [];
    for (let i = 0; i + 2 < u8.length; i++) {
      if (u8[i] !== 0xff || u8[i + 1] !== 0xd8 || u8[i + 2] !== 0xff) continue;
      const j = jpegExtent(u8, i);
      if (!j) continue;
      if (j.sof >= 0 && j.sof <= 2 && j.width > 0 && j.height > 0) found.push(j);
      i = j.end - 1;
    }
    return found.sort((a, b) => b.width * b.height - a.width * a.height);
  }

  // EXIF orientation (1–8) from a TIFF structure (raw files, or a JPEG's APP1 payload).
  function tiffOrientation(u8) {
    const le = u8[0] === 0x49;
    if (!le && u8[0] !== 0x4d) return 1;
    try {
      const dv = new DataView(u8.buffer, u8.byteOffset, u8.byteLength), ifd = dv.getUint32(4, le), n = dv.getUint16(ifd, le);
      for (let i = 0; i < n; i++) {
        const e = ifd + 2 + i * 12;
        if (dv.getUint16(e, le) === 0x0112) { const v = dv.getUint16(e + 8, le); return v >= 1 && v <= 8 ? v : 1; }
      }
    } catch (err) { /* malformed: treat as upright */ }
    return 1;
  }

  function jpegOrientation(u8, j) {
    let p = j.start + 2;
    while (p + 4 < j.end && u8[p] === 0xff && u8[p + 1] !== 0xda) {
      const len = u8[p + 2] << 8 | u8[p + 3];
      if (u8[p + 1] === 0xe1 && ascii(u8, p + 4, p + 10) === 'Exif\0\0') return tiffOrientation(u8.subarray(p + 10, p + 2 + len));
      p += 2 + len;
    }
    return 1;
  }

  // ---------- high-bit-depth single-band TIFF (elevation models, scientific data) ----------
  function halfToFloat(h) {
    const s = h & 0x8000 ? -1 : 1, e = (h >> 10) & 31, f = h & 1023;
    return e === 0 ? s * Math.pow(2, -14) * (f / 1024) : e === 31 ? (f ? NaN : s * Infinity) : s * Math.pow(2, e - 15) * (1 + f / 1024);
  }

  // Values → grey with a 1–99 percentile stretch; nodata, NaN and absurd fill values become black.
  function stretchGray(get, n, nodata) {
    const bad = (v) => !isFinite(v) || v === nodata || Math.abs(v) > 1e30;
    const step = Math.max(1, Math.floor(n / 200000)), vals = [];
    for (let i = 0; i < n; i += step) { const v = get(i); if (!bad(v)) vals.push(v); }
    vals.sort((a, b) => a - b);
    const out = new Uint8ClampedArray(n * 4);
    const lo = vals.length ? vals[Math.floor(vals.length * 0.01)] : 0;
    let hi = vals.length ? vals[Math.min(vals.length - 1, Math.floor(vals.length * 0.99))] : 1;
    if (!(hi > lo)) hi = lo + 1;
    const k = 255 / (hi - lo);
    for (let i = 0; i < n; i++) {
      const v = get(i), g = bad(v) ? 0 : (v - lo) * k, o = i * 4;
      out[o] = out[o + 1] = out[o + 2] = g; out[o + 3] = 255;
    }
    return out;
  }

  // RGBA for a UTIF-decoded IFD. UTIF's own converter is fine for 8-bit and RGB, but shows
  // 16/32-bit single-band data (e.g. GeoTIFF DEMs) as black, so those get stretched here.
  function tiffToRGBA(ifd, toRGBA8) {
    const bps = ifd.t258 ? ifd.t258[0] : 1, spp = ifd.t277 ? ifd.t277[0] : 1;
    const fmt = ifd.t339 ? ifd.t339[0] : 1, photo = ifd.t262 ? ifd.t262[0] : 1;
    const nd = ifd.t42113 != null ? parseFloat(String(ifd.t42113)) : NaN;   // GDAL_NODATA
    if ((photo === 0 || photo === 1) && spp === 1 && (bps > 8 || fmt === 3)) {
      const d = ifd.data, n = ifd.width * ifd.height, b = bps / 8;
      if (!d || d.byteLength < n * b) throw fmtErr('This TIFF looks truncated.');
      const dv = new DataView(d.buffer, d.byteOffset, d.byteLength);
      const le = bps === 16 && !ifd.t33422 ? true : !!ifd.isLE;   // UTIF swaps 16-bit samples to little-endian (except DNG)
      const get = fmt === 3
        ? (b === 2 ? (i) => halfToFloat(dv.getUint16(i * 2, le)) : b === 4 ? (i) => dv.getFloat32(i * 4, le) : (i) => dv.getFloat64(i * 8, le))
        : fmt === 2
          ? (b === 2 ? (i) => dv.getInt16(i * 2, le) : (i) => dv.getInt32(i * 4, le))
          : (b === 2 ? (i) => dv.getUint16(i * 2, le) : (i) => dv.getUint32(i * 4, le));
      const out = stretchGray(get, n, nd);
      if (photo === 0) for (let o = 0; o < out.length; o += 4) { out[o] = out[o + 1] = out[o + 2] = 255 - out[o]; }
      return out;
    }
    const out = new Uint8ClampedArray(toRGBA8(ifd).buffer);
    if (spp === 1 && bps === 8 && nd >= 0 && nd <= 255 && ifd.data) {     // 8-bit GeoTIFFs: blank areas go black too
      for (let i = 0, n = ifd.width * ifd.height; i < n; i++) if (ifd.data[i] === nd) { const o = i * 4; out[o] = out[o + 1] = out[o + 2] = 0; }
    }
    return out;
  }

  // ============ browser side ============
  const loading = {};
  function loadLib(key) {
    const lib = LIBS[key];
    if (!loading[key]) loading[key] = new Promise((resolve, reject) => {
      const s = document.createElement('script');
      s.src = lib.url; s.async = true; s.crossOrigin = 'anonymous';
      if (!/^SRI_/.test(lib.sri)) s.integrity = lib.sri;
      s.onload = resolve;
      s.onerror = () => { delete loading[key]; s.remove(); reject(fmtErr('Couldn’t download the decoder for this format — check your internet connection.')); };
      document.head.append(s);
    });
    return loading[key];
  }

  const ORIENT = { 2: [-1, 0, 0, 1, 1, 0], 3: [-1, 0, 0, -1, 1, 1], 4: [1, 0, 0, -1, 0, 1], 5: [0, 1, 1, 0, 0, 0],
    6: [0, 1, -1, 0, 1, 0], 7: [0, -1, -1, 0, 1, 1], 8: [0, -1, 1, 0, 0, 1] };

  // Draw any drawable into a canvas no larger than maxSide, applying an EXIF orientation.
  function fit(src, maxSide, orientation) {
    const sw = src.naturalWidth || src.width, sh = src.naturalHeight || src.height;
    const k = Math.min(1, maxSide / Math.max(sw, sh)), w = Math.max(1, Math.round(sw * k)), h = Math.max(1, Math.round(sh * k));
    const t = ORIENT[orientation], swap = orientation >= 5;
    const c = document.createElement('canvas');
    c.width = swap ? h : w; c.height = swap ? w : h;
    const x = c.getContext('2d');
    x.imageSmoothingQuality = 'high';
    // translation terms in ORIENT are in units of the output canvas size
    if (t) x.setTransform(t[0], t[1], t[2], t[3], t[4] * c.width, t[5] * c.height);
    x.drawImage(src, 0, 0, w, h);
    return c;
  }

  // RGBA → canvas, box-averaging first when it is far bigger than needed.
  function rgbaCanvas(img, maxSide) {
    let { width: w, height: h, data } = img;
    const k = maxSide / Math.max(w, h);
    if (k < 0.5) {
      const tw = Math.max(1, Math.round(w * k)), th = Math.max(1, Math.round(h * k)), out = new Uint8ClampedArray(tw * th * 4);
      for (let ty = 0; ty < th; ty++) {
        const y0 = Math.floor(ty * h / th), y1 = Math.max(y0 + 1, Math.floor((ty + 1) * h / th));
        for (let tx = 0; tx < tw; tx++) {
          const x0 = Math.floor(tx * w / tw), x1 = Math.max(x0 + 1, Math.floor((tx + 1) * w / tw));
          let r = 0, g = 0, b = 0, a = 0;
          for (let y = y0; y < y1; y++) for (let x = x0, o = (y * w + x0) * 4; x < x1; x++, o += 4) { r += data[o]; g += data[o + 1]; b += data[o + 2]; a += data[o + 3]; }
          const cnt = (y1 - y0) * (x1 - x0), o = (ty * tw + tx) * 4;
          out[o] = r / cnt; out[o + 1] = g / cnt; out[o + 2] = b / cnt; out[o + 3] = a / cnt;
        }
      }
      w = tw; h = th; data = out;
    }
    const c = document.createElement('canvas');
    c.width = w; c.height = h;
    c.getContext('2d').putImageData(new ImageData(new Uint8ClampedArray(data.buffer, data.byteOffset, w * h * 4), w, h), 0, 0);
    return k < 1 ? fit(c, maxSide) : c;
  }

  async function viaImg(blob, maxSide, orientation) {
    const url = URL.createObjectURL(blob);
    try {
      const im = new Image();
      im.src = url;
      await im.decode();
      if (!im.naturalWidth || !im.naturalHeight) throw new Error('no size');
      return fit(im, maxSide, orientation);
    } finally {
      URL.revokeObjectURL(url);
    }
  }

  // SVGs without width/height decode at 0×0 (or a tiny default): give them a real size first.
  function svgBlob(u8, maxSide) {
    const doc = new DOMParser().parseFromString(new TextDecoder().decode(u8), 'image/svg+xml');
    const svg = doc.documentElement;
    if (!svg || svg.nodeName.toLowerCase() !== 'svg') throw fmtErr('This SVG file looks damaged.');
    const vb = (svg.getAttribute('viewBox') || '').trim().split(/[\s,]+/).map(Number);
    const len = (v) => (v && !/%/.test(v)) ? parseFloat(v) : NaN;
    let w = len(svg.getAttribute('width')), h = len(svg.getAttribute('height'));
    const vw = vb.length === 4 && vb[2] > 0 ? vb[2] : NaN, vh = vb.length === 4 && vb[3] > 0 ? vb[3] : NaN;
    if (!(w > 0) && !(h > 0)) { w = vw || 1024; h = vh || 1024; }
    else if (!(w > 0)) w = vw && vh ? h * vw / vh : h;
    else if (!(h > 0)) h = vw && vh ? w * vh / vw : w;
    const k = maxSide / Math.max(w, h);
    svg.setAttribute('width', String(w * k)); svg.setAttribute('height', String(h * k));
    return new Blob([new XMLSerializer().serializeToString(doc)], { type: 'image/svg+xml' });
  }

  async function previewCanvas(u8, maxSide) {
    const rawOrient = tiffOrientation(u8);
    for (const j of findJpegs(u8).slice(0, 4)) {
      if (j.width < 64) break;
      try {
        // a preview carrying its own EXIF orientation is already rotated by the browser
        const o = jpegOrientation(u8, j) !== 1 ? 1 : rawOrient;
        return await viaImg(new Blob([u8.subarray(j.start, j.end)], { type: 'image/jpeg' }), maxSide, o);
      } catch (err) { /* try the next candidate */ }
    }
    return null;
  }

  // UTIF's bundled (pdf.js) JPEG decoder guesses YCbCr for 3-component data, but a TIFF with
  // RGB photometric stores its JPEG strips as plain RGB. `B` is that decoder's colorTransform
  // field in the pinned utif@3.1.0 build (SRI-locked); 0 turns the conversion off.
  function patchUtifJpeg(UTIF) {
    if (UTIF._rgbJpegPatched) return;
    const J = UTIF.JpegDecoder, orig = UTIF.decode._decodeNewJPEG;
    UTIF.decode._decodeNewJPEG = function (img) {
      if (!(img.t262 && img.t262[0] === 2)) return orig.apply(this, arguments);
      UTIF.JpegDecoder = function () { const p = new J(); p.B = 0; return p; };
      try { return orig.apply(this, arguments); } finally { UTIF.JpegDecoder = J; }
    };
    UTIF._rgbJpegPatched = true;
  }

  async function tiffCanvas(buf, maxSide, say) {
    say('Loading the TIFF decoder (first time only)…');
    await loadLib('pako');
    await loadLib('utif');
    say('Reading TIFF…');
    const UTIF = self.UTIF;
    patchUtifJpeg(UTIF);
    const ifds = UTIF.decode(buf), all = [];
    const walk = (list) => list.forEach((d) => { all.push(d); if (d.subIFD) walk(d.subIFD); });
    walk(ifds);
    const area = (d) => (d.t256 ? d.t256[0] : 0) * (d.t257 ? d.t257[0] : 0);
    const cfa = (d) => d.t262 && (d.t262[0] === 32803 || d.t262[0] === 34892);   // raw sensor data, not a picture
    for (const d of all.filter((x) => area(x) > 0 && !cfa(x)).sort((a, b) => area(b) - area(a))) {
      checkSize(d.t256[0], d.t257[0], 'TIFF');
      try {
        UTIF.decodeImage(buf, d, ifds);
        if (!d.width || !d.data) continue;
        await new Promise((r) => setTimeout(r));      // let the status line paint before heavy work
        return rgbaCanvas({ width: d.width, height: d.height, data: tiffToRGBA(d, UTIF.toRGBA8) }, maxSide);
      } catch (err) { if (err.friendly) throw err; }
    }
    throw fmtErr('Couldn’t decode this TIFF — it may use an unusual compression.');
  }

  async function toCanvas(file, opts) {
    opts = opts || {};
    const maxSide = opts.maxSide || 1600, say = opts.onStatus || function () {};
    if (file.size > MAX_BYTES) throw fmtErr('That file is over 400 MB — too big to open in a browser.');
    const buf = await file.arrayBuffer(), u8 = new Uint8Array(buf), kind = sniff(u8, file.name);
    if (UNSUPPORTED[kind]) throw fmtErr(UNSUPPORTED[kind]);
    if (kind === 'svg') return viaImg(svgBlob(u8, maxSide), maxSide);
    if (!NEVER_NATIVE.has(kind)) {
      try { return await viaImg(new Blob([u8], { type: MIME[kind] || file.type || '' }), maxSide); }
      catch (err) { /* this browser can't: fall back below */ }
    }
    const pure = (fn) => rgbaCanvas(fn(u8), maxSide);
    switch (kind) {
      case 'heif': {
        say('Loading the HEIC decoder (first time only)…');
        await loadLib('heic');
        say('Converting HEIC…');
        let bmp;
        try { bmp = await self.HeicTo({ blob: new Blob([u8]), type: 'bitmap' }); }
        catch (err) { throw fmtErr('Couldn’t decode this HEIC photo.'); }
        try { return fit(bmp, maxSide); } finally { if (bmp.close) bmp.close(); }
      }
      case 'tiff':
        try { return await tiffCanvas(buf, maxSide, say); }
        catch (err) { const pv = await previewCanvas(u8, maxSide); if (pv) return pv; throw err; }
      case 'raw': {
        const pv = await previewCanvas(u8, maxSide);
        if (pv) return pv;
        if (ascii(u8, 0, 2) === 'II' || ascii(u8, 0, 2) === 'MM') return tiffCanvas(buf, maxSide, say);
        throw fmtErr('This camera RAW file has no preview image that can be read.');
      }
      case 'jxl': {
        say('Loading the JPEG XL decoder (first time only)…');
        let mod;
        try { mod = await import(LIBS.jxl); }
        catch (err) { throw fmtErr('Couldn’t download the decoder for this format — check your internet connection.'); }
        say('Decoding JPEG XL…');
        let img;
        try { img = await mod.default(buf); } catch (err) { throw fmtErr('Couldn’t decode this JPEG XL image.'); }
        return rgbaCanvas(img, maxSide);
      }
      case 'psd': return pure(decodePSD);
      case 'tga': return pure(decodeTGA);
      case 'qoi': return pure(decodeQOI);
      case 'pnm': return pure(decodePNM);
      case 'hdr': return pure(decodeHDR);
    }
    throw fmtErr(NAMES[kind] ? 'Your browser couldn’t open this ' + NAMES[kind] + ' file. Try exporting it as PNG or JPG.'
      : 'That file doesn’t look like an image this page can read.');
  }

  return { ACCEPT, sniff, decodePNM, decodeTGA, decodeQOI, decodePSD, decodeHDR, findJpegs, tiffOrientation,
    jpegOrientation, tiffToRGBA, stretchGray, halfToFloat, toCanvas };
});
