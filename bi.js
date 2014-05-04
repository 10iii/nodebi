/*
 ** Pure JavaScript Big Integer module for node.js
 ** Copyright (c)  2012  10iii
 ** All Rights Reserved.
 ** This module is released under a BSD license.
 **
 ** This module is modified from Tom Wu's jsbn library. Which is also under a BSD license.
 ** See http://www-cs-students.stanford.edu/~tjw/jsbn/
 **
 ** The main change from jsbn is using a buff array instead of hashset member to keep digits
 ** and estimate buff size when create a new BI object during calculating.
 ** For detail see https://github.com/10iii/nodebi
 **
 */
(function () {
  // Bits per digit
  var
    dbits = 28,
    BI_DB = dbits,
    BI_DM = ((1 << dbits) - 1),
    BI_DV = (1 << dbits),
    BI_FP = 52,
    BI_FV = Math.pow(2, BI_FP),
    BI_F1 = BI_FP - dbits,
    BI_F2 = 2 * dbits - BI_FP;

  // Digit conversions
  var BI_RM = "0123456789abcdefghijklmnopqrstuvwxyz";
  var BI_RC = new Array();
  var rr, vv;
  rr = "0".charCodeAt(0);
  for (vv = 0; vv <= 9; ++vv) BI_RC[rr++] = vv;
  rr = "a".charCodeAt(0);
  for (vv = 10; vv < 36; ++vv) BI_RC[rr++] = vv;
  rr = "A".charCodeAt(0);
  for (vv = 10; vv < 36; ++vv) BI_RC[rr++] = vv;

  // (public) Constructor
  function BigInteger(a, b, c, d) {
    if ('number' == typeof d && d > 0) {
      this.buf = new Array(d);
    } else {
      this.buf = new Array();
    }
    this.t = 0;
    this.s = 0;
    if ('number' == typeof a) {
      this.fromInt(a);
    } else if ('string' == typeof a) {
      ('number' == typeof b) ? this.fromString(a, b) : this.fromString(a, 256);
    }
  }

  // return new, unset BigInteger
  function nbi(max_digits) {
    return new BigInteger(null, null, null, max_digits);
  }

  // am: Compute w_j += (x*this_i), propagate carries,
  // c is initial carry, returns final carry.
  // c < 3*dvalue, x < 2*dvalue, this_i < dvalue
  // We need to select the fastest one that works in this environment.

  // am1: use a single mult and divide to get the high bits,
  // max digit bits should be 26 because
  // max internal value = 2*dvalue^2-2*dvalue (< 2^53)
  function am1(i, x, w, j, c, n) {
    var this_buf = this.buf;
    var w_buf = w.buf;
    while (--n >= 0) {
      var v = x * this_buf[i++] + w_buf[j] + c;
      c = Math.floor(v / 0x4000000);
      w_buf[j++] = v & 0x3ffffff;
    }
    return c;
  }

  // am2 avoids a big mult-and-extract completely.
  // Max digit bits should be <= 30 because we do bitwise ops
  // on values up to 2*hdvalue^2-hdvalue-1 (< 2^31)
  function am2(i, x, w, j, c, n) {
    var this_buf = this.buf;
    var w_buf = w.buf;
    var xl = x & 0x7fff,
      xh = x >> 15;
    while (--n >= 0) {
      var l = this_buf[i] & 0x7fff;
      var h = this_buf[i++] >> 15;
      var m = xh * l + h * xl;
      l = xl * l + ((m & 0x7fff) << 15) + w_buf[j] + (c & 0x3fffffff);
      c = (l >>> 30) + (m >>> 15) + xh * h + (c >>> 30);
      w_buf[j++] = l & 0x3fffffff;
    }
    return c;
  }

  // Alternately, set max digit bits to 28 since some
  // browsers slow down when dealing with 32-bit numbers.
  function am3(i, x, w, j, c, n) {
    var this_buf = this.buf;
    var w_buf = w.buf;

    var xl = x & 0x3fff,
      xh = x >> 14;
    while (--n >= 0) {
      var l = this_buf[i] & 0x3fff;
      var h = this_buf[i++] >> 14;
      var m = xh * l + h * xl;
      l = xl * l + ((m & 0x3fff) << 14) + w_buf[j] + c;
      c = (l >> 28) + (m >> 14) + xh * h;
      w_buf[j++] = l & 0xfffffff;
    }
    return c;
  }

  // This is tailored to VMs with 2-bit tagging. It makes sure
  // that all the computations stay within the 29 bits available.
  function am4(i, x, w, j, c, n) {
    var this_buf = this.buf;
    var w_buf = w.buf;

    var xl = x & 0x1fff,
      xh = x >> 13;
    while (--n >= 0) {
      var l = this_buf[i] & 0x1fff;
      var h = this_buf[i++] >> 13;
      var m = xh * l + h * xl;
      l = xl * l + ((m & 0x1fff) << 13) + w_buf[j] + c;
      c = (l >> 26) + (m >> 13) + xh * h;
      w_buf[j++] = l & 0x3ffffff;
    }
    return c;
  }

  // am3/28 is best for SM, Rhino, but am4/26 is best for v8.
  // Kestrel (Opera 9.5) gets its best result with am4/26.
  // IE7 does 9% better with am3/28 than with am4/26.
  // Firefox (SM) gets 10% faster with am3/28 than with am4/26.


  function int2char(n) {
    return BI_RM.charAt(n);
  }

  function intAt(s, i) {
    var c = BI_RC[s.charCodeAt(i)];
    return (c == null) ? -1 : c;
  }

  // (protected) copy this to r
  function bnpCopyTo(r) {
    var this_buf = this.buf;
    var r_buf = r.buf;

    for (var i = this.t - 1; i >= 0; --i) r_buf[i] = this_buf[i];
    r.t = this.t;
    r.s = this.s;
  }

  // (protected) set from integer value x, -DV <= x < DV
  function bnpFromInt(x) {
    var this_buf = this.buf;
    this.t = 1;
    this.s = (x < 0) ? -1 : 0;
    if (x > 0) this_buf[0] = x;
    else if (x < -1) this_buf[0] = x + BI_DV;
    else this.t = 0;
  }

  // return bigint initialized to value
  function nbv(i) {
    var r = nbi();
    r.fromInt(i);
    return r;
  }

  // return a new BigInteger object
  // bi(int) / bi(string) / bi (string, radix)
  function bi(a, b) {
    return new BigInteger(a, b, null, null);
  }


  // (protected) set from string and radix
  function bnpFromString(s, b) {
    var this_buf = this.buf;
    var k;
    if (b == 16) k = 4;
    else if (b == 8) k = 3;
    else if (b == 256) k = 8; // byte buf
    else if (b == 2) k = 1;
    else if (b == 32) k = 5;
    else if (b == 4) k = 2;
    else {
      this.fromRadix(s, b);
      return;
    }
    this.t = 0;
    this.s = 0;
    var i = s.length,
      mi = false,
      sh = 0;
    while (--i >= 0) {
      var x = (k == 8) ? s[i] & 0xff : intAt(s, i);
      if (x < 0) {
        if (s.charAt(i) == "-") mi = true;
        continue;
      }
      mi = false;
      if (sh == 0) this_buf[this.t++] = x;
      else if (sh + k > BI_DB) {
        this_buf[this.t - 1] |= (x & ((1 << (BI_DB - sh)) - 1)) << sh;
        this_buf[this.t++] = (x >> (BI_DB - sh));
      } else this_buf[this.t - 1] |= x << sh;
      sh += k;
      if (sh >= BI_DB) sh -= BI_DB;
    }
    if (k == 8 && (s[0] & 0x80) != 0) {
      this.s = -1;
      if (sh > 0) this_buf[this.t - 1] |= ((1 << (BI_DB - sh)) - 1) << sh;
    }
    this.clamp();
    if (mi) BigInteger.ZERO.subTo(this, this);
  }

  // (protected) clamp off excess high words
  function bnpClamp() {
    var this_buf = this.buf;
    var c = this.s & BI_DM;
    while (this.t > 0 && this_buf[this.t - 1] == c)--this.t;
  }

  // (public) return string representation in given radix
  function bnToString(b) {
    var this_buf = this.buf;
    if (this.s < 0) return "-" + this.negate().toString(b);
    var k;
    if (b == 16) k = 4;
    else if (b == 8) k = 3;
    else if (b == 2) k = 1;
    else if (b == 32) k = 5;
    else if (b == 4) k = 2;
    else return this.toRadix(b);
    var km = (1 << k) - 1,
      d, m = false,
      r = "",
      i = this.t;
    var p = BI_DB - (i * BI_DB) % k;
    if (i-- > 0) {
      if (p < BI_DB && (d = this_buf[i] >> p) > 0) {
        m = true;
        r = int2char(d);
      }
      while (i >= 0) {
        if (p < k) {
          d = (this_buf[i] & ((1 << p) - 1)) << (k - p);
          d |= this_buf[--i] >> (p += BI_DB - k);
        } else {
          d = (this_buf[i] >> (p -= k)) & km;
          if (p <= 0) {
            p += BI_DB;
            --i;
          }
        }
        if (d > 0) m = true;
        if (m) r += int2char(d);
      }
    }
    return m ? r : "0";
  }

  // (public) -this
  function bnNegate() {
    var r = nbi(this.t + 2);
    BigInteger.ZERO.subTo(this, r);
    return r;
  }

  // (public) |this|
  function bnAbs() {
    return (this.s < 0) ? this.negate() : this;
  }

  // (public) return + if this > a, - if this < a, 0 if equal
  function bnCompareTo(a) {
    var this_buf = this.buf;
    var a_buf = a.buf;

    var r = this.s - a.s;
    if (r != 0) return r;
    var i = this.t;
    r = i - a.t;
    if (r != 0) return (this.s < 0) ? -r : r;
    while (--i >= 0)
      if ((r = this_buf[i] - a_buf[i]) != 0) return r;
    return 0;
  }

  // returns bit length of the integer x
  function nbits(x) {
    var r = 1,
      t;
    if ((t = x >>> 16) != 0) {
      x = t;
      r += 16;
    }
    if ((t = x >> 8) != 0) {
      x = t;
      r += 8;
    }
    if ((t = x >> 4) != 0) {
      x = t;
      r += 4;
    }
    if ((t = x >> 2) != 0) {
      x = t;
      r += 2;
    }
    if ((t = x >> 1) != 0) {
      x = t;
      r += 1;
    }
    return r;
  }

  // (public) return the number of bits in "this"
  function bnBitLength() {
    var this_buf = this.buf;
    if (this.t <= 0) return 0;
    return BI_DB * (this.t - 1) + nbits(this_buf[this.t - 1] ^ (this.s & BI_DM));
  }

  // (protected) r = this << n*DB
  function bnpDLShiftTo(n, r) {
    var this_buf = this.buf;
    var r_buf = r.buf;
    var i;
    for (i = this.t - 1; i >= 0; --i) r_buf[i + n] = this_buf[i];
    for (i = n - 1; i >= 0; --i) r_buf[i] = 0;
    r.t = this.t + n;
    r.s = this.s;
  }

  // (protected) r = this >> n*DB
  function bnpDRShiftTo(n, r) {
    var this_buf = this.buf;
    var r_buf = r.buf;
    for (var i = n; i < this.t; ++i) r_buf[i - n] = this_buf[i];
    r.t = Math.max(this.t - n, 0);
    r.s = this.s;
  }

  // (protected) r = this << n
  function bnpLShiftTo(n, r) {
    var this_buf = this.buf;
    var r_buf = r.buf;
    var bs = n % BI_DB;
    var cbs = BI_DB - bs;
    var bm = (1 << cbs) - 1;
    var ds = Math.floor(n / BI_DB),
      c = (this.s << bs) & BI_DM,
      i;
    for (i = this.t - 1; i >= 0; --i) {
      r_buf[i + ds + 1] = (this_buf[i] >> cbs) | c;
      c = (this_buf[i] & bm) << bs;
    }
    for (i = ds - 1; i >= 0; --i) r_buf[i] = 0;
    r_buf[ds] = c;
    r.t = this.t + ds + 1;
    r.s = this.s;
    r.clamp();
  }

  // (protected) r = this >> n
  function bnpRShiftTo(n, r) {
    var this_buf = this.buf;
    var r_buf = r.buf;
    r.s = this.s;
    var ds = Math.floor(n / BI_DB);
    if (ds >= this.t) {
      r.t = 0;
      return;
    }
    var bs = n % BI_DB;
    var cbs = BI_DB - bs;
    var bm = (1 << bs) - 1;
    r_buf[0] = this_buf[ds] >> bs;
    for (var i = ds + 1; i < this.t; ++i) {
      r_buf[i - ds - 1] |= (this_buf[i] & bm) << cbs;
      r_buf[i - ds] = this_buf[i] >> bs;
    }
    if (bs > 0) r_buf[this.t - ds - 1] |= (this.s & bm) << cbs;
    r.t = this.t - ds;
    r.clamp();
  }

  // (protected) r = this - a
  function bnpSubTo(a, r) {
    var this_buf = this.buf;
    var r_buf = r.buf;
    var a_buf = a.buf;
    var i = 0,
      c = 0,
      m = Math.min(a.t, this.t);
    while (i < m) {
      c += this_buf[i] - a_buf[i];
      r_buf[i++] = c & BI_DM;
      c >>= BI_DB;
    }
    if (a.t < this.t) {
      c -= a.s;
      while (i < this.t) {
        c += this_buf[i];
        r_buf[i++] = c & BI_DM;
        c >>= BI_DB;
      }
      c += this.s;
    } else {
      c += this.s;
      while (i < a.t) {
        c -= a_buf[i];
        r_buf[i++] = c & BI_DM;
        c >>= BI_DB;
      }
      c -= a.s;
    }
    r.s = (c < 0) ? -1 : 0;
    if (c < -1) r_buf[i++] = BI_DV + c;
    else if (c > 0) r_buf[i++] = c;
    r.t = i;
    r.clamp();
  }

  // (protected) r = this * a, r != this,a (HAC 14.12)
  // "this" should be the larger one if appropriate.
  function bnpMultiplyTo(a, r) {
    var this_buf = this.buf;
    var r_buf = r.buf;
    var x = this.abs(),
      y = a.abs();
    var y_buf = y.buf;

    var i = x.t;
    r.t = i + y.t;
    while (--i >= 0) r_buf[i] = 0;
    for (i = 0; i < y.t; ++i) r_buf[i + x.t] = x.am(0, y_buf[i], r, i, 0, x.t);
    r.s = 0;
    r.clamp();
    if (this.s != a.s) BigInteger.ZERO.subTo(r, r);
  }

  // (protected) r = this^2, r != this (HAC 14.16)
  function bnpSquareTo(r) {
    var x = this.abs();
    var x_buf = x.buf;
    var r_buf = r.buf;

    var i = r.t = 2 * x.t;
    while (--i >= 0) r_buf[i] = 0;
    for (i = 0; i < x.t - 1; ++i) {
      var c = x.am(i, x_buf[i], r, 2 * i, 0, 1);
      if ((r_buf[i + x.t] += x.am(i + 1, 2 * x_buf[i], r, 2 * i + 1, c, x.t - i - 1)) >= BI_DV) {
        r_buf[i + x.t] -= BI_DV;
        r_buf[i + x.t + 1] = 1;
      }
    }
    if (r.t > 0) r_buf[r.t - 1] += x.am(i, x_buf[i], r, 2 * i, 0, 1);
    r.s = 0;
    r.clamp();
  }

  // (protected) divide this by m, quotient and remainder to q, r (HAC 14.20)
  // r != q, this != m.  q or r may be null.
  function bnpDivRemTo(m, q, r) {
    var pm = m.abs();
    if (pm.t <= 0) return;
    var pt = this.abs();
    if (pt.t < pm.t) {
      if (q != null) q.fromInt(0);
      if (r != null) this.copyTo(r);
      return;
    }
    if (r == null) r = nbi(this.t + 2);
    var y = nbi(this.t + 2),
      ts = this.s,
      ms = m.s;
    var pm_buf = pm.buf;
    var nsh = BI_DB - nbits(pm_buf[pm.t - 1]); // normalize modulus
    if (nsh > 0) {
      pm.lShiftTo(nsh, y);
      pt.lShiftTo(nsh, r);
    } else {
      pm.copyTo(y);
      pt.copyTo(r);
    }
    var ys = y.t;

    var y_buf = y.buf;
    var y0 = y_buf[ys - 1];
    if (y0 == 0) return;
    var yt = y0 * (1 << BI_F1) + ((ys > 1) ? y_buf[ys - 2] >> BI_F2 : 0);
    var d1 = BI_FV / yt,
      d2 = (1 << BI_F1) / yt,
      e = 1 << BI_F2;
    var i = r.t,
      j = i - ys,
      t = (q == null) ? nbi(this.t + 2) : q;
    y.dlShiftTo(j, t);

    var r_buf = r.buf;
    if (r.compareTo(t) >= 0) {
      r_buf[r.t++] = 1;
      r.subTo(t, r);
    }
    BigInteger.ONE.dlShiftTo(ys, t);
    t.subTo(y, y); // "negative" y so we can replace sub with am later
    while (y.t < ys) y_buf[y.t++] = 0;
    while (--j >= 0) {
      // Estimate quotient digit
      var qd = (r_buf[--i] == y0) ? BI_DM : Math.floor(r_buf[i] * d1 + (r_buf[i - 1] + e) * d2);
      if ((r_buf[i] += y.am(0, qd, r, j, 0, ys)) < qd) { // Try it out
        y.dlShiftTo(j, t);
        r.subTo(t, r);
        while (r_buf[i] < --qd) r.subTo(t, r);
      }
    }
    if (q != null) {
      r.drShiftTo(ys, q);
      if (ts != ms) BigInteger.ZERO.subTo(q, q);
    }
    r.t = ys;
    r.clamp();
    if (nsh > 0) r.rShiftTo(nsh, r); // Denormalize remainder
    if (ts < 0) BigInteger.ZERO.subTo(r, r);
  }

  // (public) this mod a
  function bnMod(a) {
    var r = nbi(this.t + 2);
    this.abs().divRemTo(a, null, r);
    if (this.s < 0 && r.compareTo(BigInteger.ZERO) > 0) a.subTo(r, r);
    return r;
  }

  // Modular reduction using "classic" algorithm
  function Classic(m) {
    this.m = m;
  }

  function cConvert(x) {
    if (x.s < 0 || x.compareTo(this.m) >= 0) return x.mod(this.m);
    else return x;
  }

  function cRevert(x) {
    return x;
  }

  function cReduce(x) {
    x.divRemTo(this.m, null, x);
  }

  function cMulTo(x, y, r) {
    x.multiplyTo(y, r);
    this.reduce(r);
  }

  function cSqrTo(x, r) {
    x.squareTo(r);
    this.reduce(r);
  }

  Classic.prototype.convert = cConvert;
  Classic.prototype.revert = cRevert;
  Classic.prototype.reduce = cReduce;
  Classic.prototype.mulTo = cMulTo;
  Classic.prototype.sqrTo = cSqrTo;

  // (protected) return "-1/this % 2^DB"; useful for Mont. reduction
  // justification:
  //         xy == 1 (mod m)
  //         xy =  1+km
  //   xy(2-xy) = (1+km)(1-km)
  // x[y(2-xy)] = 1-k^2m^2
  // x[y(2-xy)] == 1 (mod m^2)
  // if y is 1/x mod m, then y(2-xy) is 1/x mod m^2
  // should reduce x and y(2-xy) by m^2 at each step to keep size bounded.
  // JS multiply "overflows" differently from C/C++, so care is needed here.
  function bnpInvDigit() {
    var this_buf = this.buf;
    if (this.t < 1) return 0;
    var x = this_buf[0];
    if ((x & 1) == 0) return 0;
    var y = x & 3; // y == 1/x mod 2^2
    y = (y * (2 - (x & 0xf) * y)) & 0xf; // y == 1/x mod 2^4
    y = (y * (2 - (x & 0xff) * y)) & 0xff; // y == 1/x mod 2^8
    y = (y * (2 - (((x & 0xffff) * y) & 0xffff))) & 0xffff; // y == 1/x mod 2^16
    // last step - calculate inverse mod DV directly;
    // assumes 16 < DB <= 32 and assumes ability to handle 48-bit ints
    y = (y * (2 - x * y % BI_DV)) % BI_DV; // y == 1/x mod 2^dbits
    // we really want the negative inverse, and -DV < y < DV
    return (y > 0) ? BI_DV - y : -y;
  }

  // Montgomery reduction
  function Montgomery(m) {
    this.m = m;
    this.mp = m.invDigit();
    this.mpl = this.mp & 0x7fff;
    this.mph = this.mp >> 15;
    this.um = (1 << (BI_DB - 15)) - 1;
    this.mt2 = 2 * m.t;
  }

  // xR mod m
  function montConvert(x) {
    var r = nbi(this.m.t + 2);
    x.abs().dlShiftTo(this.m.t, r);
    r.divRemTo(this.m, null, r);
    if (x.s < 0 && r.compareTo(BigInteger.ZERO) > 0) this.m.subTo(r, r);
    return r;
  }

  // x/R mod m
  function montRevert(x) {
    var r = nbi(this.m.t + 2);
    x.copyTo(r);
    this.reduce(r);
    return r;
  }

  // x = x/R mod m (HAC 14.32)
  function montReduce(x) {
    var x_buf = x.buf;
    while (x.t <= this.mt2) // pad x so am has enough room later
      x_buf[x.t++] = 0;
    for (var i = 0; i < this.m.t; ++i) {
      // faster way of calculating u0 = x[i]*mp mod DV
      var j = x_buf[i] & 0x7fff;
      var u0 = (j * this.mpl + (((j * this.mph + (x_buf[i] >> 15) * this.mpl) & this.um) << 15)) & BI_DM;
      // use am to combine the multiply-shift-add into one call
      j = i + this.m.t;
      x_buf[j] += this.m.am(0, u0, x, i, 0, this.m.t);
      // propagate carry
      while (x_buf[j] >= BI_DV) {
        x_buf[j] -= BI_DV;
        x_buf[++j]++;
      }
    }
    x.clamp();
    x.drShiftTo(this.m.t, x);
    if (x.compareTo(this.m) >= 0) x.subTo(this.m, x);
  }

  // r = "x^2/R mod m"; x != r
  function montSqrTo(x, r) {
    x.squareTo(r);
    this.reduce(r);
  }

  // r = "xy/R mod m"; x,y != r
  function montMulTo(x, y, r) {
    x.multiplyTo(y, r);
    this.reduce(r);
  }

  Montgomery.prototype.convert = montConvert;
  Montgomery.prototype.revert = montRevert;
  Montgomery.prototype.reduce = montReduce;
  Montgomery.prototype.mulTo = montMulTo;
  Montgomery.prototype.sqrTo = montSqrTo;

  // (protected) true iff this is even
  function bnpIsEven() {
    var this_buf = this.buf;
    return ((this.t > 0) ? (this_buf[0] & 1) : this.s) == 0;
  }

  // (protected) this^e, e < 2^32, doing sqr and mul with "r" (HAC 14.79)
  function bnpExp(e, z) {
    if (e > 0xffffffff || e < 1) return BigInteger.ONE;
    var r = nbi(this.t + 2),
      r2 = nbi(this.t + 2),
      g = z.convert(this),
      i = nbits(e) - 1;
    g.copyTo(r);
    while (--i >= 0) {
      z.sqrTo(r, r2);
      if ((e & (1 << i)) > 0) z.mulTo(r2, g, r);
      else {
        var t = r;
        r = r2;
        r2 = t;
      }
    }
    return z.revert(r);
  }

  // (public) this^e % m, 0 <= e < 2^32
  function bnModPowInt(e, m) {
    var z;
    if (e < 256 || m.isEven()) z = new Classic(m);
    else z = new Montgomery(m);
    return this.exp(e, z);
  }

  // (public) return value as integer
  function bnIntValue() {
    var this_buf = this.buf;
    if (this.s < 0) {
      if (this.t == 1) return this_buf[0] - BI_DV;
      else if (this.t == 0) return -1;
    } else if (this.t == 1) return this_buf[0];
    else if (this.t == 0) return 0;
    // assumes 16 < DB < 32
    return ((this_buf[1] & ((1 << (32 - BI_DB)) - 1)) << BI_DB) | this_buf[0];
  }

  // (public) this << n
  function bnShiftLeft(n) {
    var r = nbi(this.t + n + 2);
    if (n < 0) this.rShiftTo(-n, r);
    else this.lShiftTo(n, r);
    return r;
  }
  // (protected) r = this + a
  function bnpAddTo(a, r) {
    var this_buf = this.buf;
    var a_buf = a.buf;
    var r_buf = r.buf;
    var i = 0,
      c = 0,
      m = Math.min(a.t, this.t);
    while (i < m) {
      c += this_buf[i] + a_buf[i];
      r_buf[i++] = c & BI_DM;
      c >>= BI_DB;
    }
    if (a.t < this.t) {
      c += a.s;
      while (i < this.t) {
        c += this_buf[i];
        r_buf[i++] = c & BI_DM;
        c >>= BI_DB;
      }
      c += this.s;
    } else {
      c += this.s;
      while (i < a.t) {
        c += a_buf[i];
        r_buf[i++] = c & BI_DM;
        c >>= BI_DB;
      }
      c += a.s;
    }
    r.s = (c < 0) ? -1 : 0;
    if (c > 0) r_buf[i++] = c;
    else if (c < -1) r_buf[i++] = BI_DV + c;
    r.t = i;
    r.clamp();
  }

  BigInteger.prototype.am = am3;
  // protected
  BigInteger.prototype.copyTo = bnpCopyTo;
  BigInteger.prototype.fromInt = bnpFromInt;
  BigInteger.prototype.fromString = bnpFromString;
  BigInteger.prototype.clamp = bnpClamp;
  BigInteger.prototype.dlShiftTo = bnpDLShiftTo;
  BigInteger.prototype.drShiftTo = bnpDRShiftTo;
  BigInteger.prototype.lShiftTo = bnpLShiftTo;
  BigInteger.prototype.rShiftTo = bnpRShiftTo;
  BigInteger.prototype.subTo = bnpSubTo;
  BigInteger.prototype.addTo = bnpAddTo;
  BigInteger.prototype.multiplyTo = bnpMultiplyTo;
  BigInteger.prototype.squareTo = bnpSquareTo;
  BigInteger.prototype.divRemTo = bnpDivRemTo;
  BigInteger.prototype.invDigit = bnpInvDigit;
  BigInteger.prototype.isEven = bnpIsEven;
  BigInteger.prototype.exp = bnpExp;
  BigInteger.prototype.bnShiftLeft = bnShiftLeft;
  BigInteger.prototype.bnIntValue = bnIntValue;

  //setupEngine(am3, 28);

  // public
  BigInteger.prototype.toString = bnToString;
  BigInteger.prototype.negate = bnNegate;
  BigInteger.prototype.abs = bnAbs;
  BigInteger.prototype.compareTo = bnCompareTo;
  BigInteger.prototype.bitLength = bnBitLength;
  BigInteger.prototype.mod = bnMod;
  BigInteger.prototype.modPowInt = bnModPowInt;

  // "constants"
  BigInteger.ZERO = nbv(0);
  BigInteger.ONE = nbv(1);


  BigInteger.prototype.clone = function () {
    var r = nbi(this.t + 2);
    this.copyTo(r);
    return r
  };
  BigInteger.prototype.multiply = function (a) {
    var r = nbi(this.t + a.t + 2);
    this.multiplyTo(a, r);
    return r
  };
  BigInteger.prototype.divide = function (a) {
    var r = nbi(this.t + 2);
    this.divRemTo(a, r, null);
    return r
  };
  BigInteger.prototype.add = function (a) {
    var r = nbi(Math.max(this.t, a.t) + 2);
    this.addTo(a, r);
    return r
  };
  BigInteger.prototype.sub = function (a) {
    var r = nbi(Math.max(this.t, a.t) + 2);
    o.subTo(a, r);
    return r
  };

  if (typeof module !== 'undefined' && module.exports) {
    module.exports = bi;
  }
}());
