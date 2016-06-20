"use strict";
// This object will hold all exports.
var Haste = {};
if(typeof window === 'undefined') window = global;

/* Constructor functions for small ADTs. */
function T0(t){this._=t;}
function T1(t,a){this._=t;this.a=a;}
function T2(t,a,b){this._=t;this.a=a;this.b=b;}
function T3(t,a,b,c){this._=t;this.a=a;this.b=b;this.c=c;}
function T4(t,a,b,c,d){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;}
function T5(t,a,b,c,d,e){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;}
function T6(t,a,b,c,d,e,f){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;this.f=f;}

/* Thunk
   Creates a thunk representing the given closure.
   If the non-updatable flag is undefined, the thunk is updatable.
*/
function T(f, nu) {
    this.f = f;
    if(nu === undefined) {
        this.x = __updatable;
    }
}

/* Hint to optimizer that an imported symbol is strict. */
function __strict(x) {return x}

// A tailcall.
function F(f) {
    this.f = f;
}

// A partially applied function. Invariant: members are never thunks.
function PAP(f, args) {
    this.f = f;
    this.args = args;
    this.arity = f.length - args.length;
}

// "Zero" object; used to avoid creating a whole bunch of new objects
// in the extremely common case of a nil-like data constructor.
var __Z = new T0(0);

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

// Indicates that a closure-creating tail loop isn't done.
var __continue = {};

/* Generic apply.
   Applies a function *or* a partial application object to a list of arguments.
   See https://ghc.haskell.org/trac/ghc/wiki/Commentary/Rts/HaskellExecution/FunctionCalls
   for more information.
*/
function A(f, args) {
    while(true) {
        f = E(f);
        if(f instanceof Function) {
            if(args.length === f.length) {
                return f.apply(null, args);
            } else if(args.length < f.length) {
                return new PAP(f, args);
            } else {
                var f2 = f.apply(null, args.slice(0, f.length));
                args = args.slice(f.length);
                f = B(f2);
            }
        } else if(f instanceof PAP) {
            if(args.length === f.arity) {
                return f.f.apply(null, f.args.concat(args));
            } else if(args.length < f.arity) {
                return new PAP(f.f, f.args.concat(args));
            } else {
                var f2 = f.f.apply(null, f.args.concat(args.slice(0, f.arity)));
                args = args.slice(f.arity);
                f = B(f2);
            }
        } else {
            return f;
        }
    }
}

function A1(f, x) {
    f = E(f);
    if(f instanceof Function) {
        return f.length === 1 ? f(x) : new PAP(f, [x]);
    } else if(f instanceof PAP) {
        return f.arity === 1 ? f.f.apply(null, f.args.concat([x]))
                             : new PAP(f.f, f.args.concat([x]));
    } else {
        return f;
    }
}

function A2(f, x, y) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 2:  return f(x, y);
        case 1:  return A1(B(f(x)), y);
        default: return new PAP(f, [x,y]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 2:  return f.f.apply(null, f.args.concat([x,y]));
        case 1:  return A1(B(f.f.apply(null, f.args.concat([x]))), y);
        default: return new PAP(f.f, f.args.concat([x,y]));
        }
    } else {
        return f;
    }
}

function A3(f, x, y, z) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 3:  return f(x, y, z);
        case 2:  return A1(B(f(x, y)), z);
        case 1:  return A2(B(f(x)), y, z);
        default: return new PAP(f, [x,y,z]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 3:  return f.f.apply(null, f.args.concat([x,y,z]));
        case 2:  return A1(B(f.f.apply(null, f.args.concat([x,y]))), z);
        case 1:  return A2(B(f.f.apply(null, f.args.concat([x]))), y, z);
        default: return new PAP(f.f, f.args.concat([x,y,z]));
        }
    } else {
        return f;
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            if(t.x === __updatable) {
                var f = t.f;
                t.f = __blackhole;
                t.x = f();
            } else {
                return t.f();
            }
        }
        if(t.x === __updatable) {
            throw 'Infinite loop!';
        } else {
            return t.x;
        }
    } else {
        return t;
    }
}

/* Tail call chain counter. */
var C = 0, Cs = [];

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    Cs.push(C);
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        C = 0;
        f = fun();
    }
    C = Cs.pop();
    return f;
}

// Export Haste, A, B and E. Haste because we need to preserve exports, A, B
// and E because they're handy for Haste.Foreign.
if(!window) {
    var window = {};
}
window['Haste'] = Haste;
window['A'] = A;
window['E'] = E;
window['B'] = B;


/* Throw an error.
   We need to be able to use throw as an exception so we wrap it in a function.
*/
function die(err) {
    throw E(err);
}

function quot(a, b) {
    return (a-a%b)/b;
}

function quotRemI(a, b) {
    return {_:0, a:(a-a%b)/b, b:a%b};
}

// 32 bit integer multiplication, with correct overflow behavior
// note that |0 or >>>0 needs to be applied to the result, for int and word
// respectively.
if(Math.imul) {
    var imul = Math.imul;
} else {
    var imul = function(a, b) {
        // ignore high a * high a as the result will always be truncated
        var lows = (a & 0xffff) * (b & 0xffff); // low a * low b
        var aB = (a & 0xffff) * (b & 0xffff0000); // low a * high b
        var bA = (a & 0xffff0000) * (b & 0xffff); // low b * high a
        return lows + aB + bA; // sum will not exceed 52 bits, so it's safe
    }
}

function addC(a, b) {
    var x = a+b;
    return {_:0, a:x & 0xffffffff, b:x > 0x7fffffff};
}

function subC(a, b) {
    var x = a-b;
    return {_:0, a:x & 0xffffffff, b:x < -2147483648};
}

function sinh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / 2;
}

function tanh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / (Math.exp(arg) + Math.exp(-arg));
}

function cosh (arg) {
    return (Math.exp(arg) + Math.exp(-arg)) / 2;
}

function isFloatFinite(x) {
    return isFinite(x);
}

function isDoubleFinite(x) {
    return isFinite(x);
}

function err(str) {
    die(toJSStr(str));
}

/* unpackCString#
   NOTE: update constructor tags if the code generator starts munging them.
*/
function unCStr(str) {return unAppCStr(str, __Z);}

function unFoldrCStr(str, f, z) {
    var acc = z;
    for(var i = str.length-1; i >= 0; --i) {
        acc = B(A(f, [str.charCodeAt(i), acc]));
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return {_:1,a:str.charCodeAt(i),b:new T(function() {
            return unAppCStr(str,chrs,i+1);
        })};
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str._ == 1; str = E(str.b)) {
        s += String.fromCharCode(E(str.a));
    }
    return s;
}

// newMutVar
function nMV(val) {
    return ({x: val});
}

// readMutVar
function rMV(mv) {
    return mv.x;
}

// writeMutVar
function wMV(mv, val) {
    mv.x = val;
}

// atomicModifyMutVar
function mMV(mv, f) {
    var x = B(A(f, [mv.x]));
    mv.x = x.a;
    return x.b;
}

function localeEncoding() {
    var le = newByteArr(5);
    le['v']['i8'][0] = 'U'.charCodeAt(0);
    le['v']['i8'][1] = 'T'.charCodeAt(0);
    le['v']['i8'][2] = 'F'.charCodeAt(0);
    le['v']['i8'][3] = '-'.charCodeAt(0);
    le['v']['i8'][4] = '8'.charCodeAt(0);
    return le;
}

var isDoubleNaN = isNaN;
var isFloatNaN = isNaN;

function isDoubleInfinite(d) {
    return (d === Infinity);
}
var isFloatInfinite = isDoubleInfinite;

function isDoubleNegativeZero(x) {
    return (x===0 && (1/x)===-Infinity);
}
var isFloatNegativeZero = isDoubleNegativeZero;

function strEq(a, b) {
    return a == b;
}

function strOrd(a, b) {
    if(a < b) {
        return 0;
    } else if(a == b) {
        return 1;
    }
    return 2;
}

/* Convert a JS exception into a Haskell JSException */
function __hsException(e) {
  e = e.toString();
  var x = new Long(2904464383, 3929545892, true);
  var y = new Long(3027541338, 3270546716, true);
  var t = new T5(0, x, y
                  , new T5(0, x, y
                            , unCStr("haste-prim")
                            , unCStr("Haste.Prim.Foreign")
                            , unCStr("JSException")), __Z, __Z);
  var show = function(x) {return unCStr(E(x).a);}
  var dispEx = function(x) {return unCStr("JavaScript exception: " + E(x).a);}
  var showList = function(_, s) {return unAppCStr(e, s);}
  var showsPrec = function(_, _p, s) {return unAppCStr(e, s);}
  var showDict = new T3(0, showsPrec, show, showList);
  var self;
  var fromEx = function(_) {return new T1(1, self);}
  var dict = new T5(0, t, showDict, null /* toException */, fromEx, dispEx);
  self = new T2(0, dict, new T1(0, e));
  return self;
}

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        if(typeof e._ === 'undefined') {
            e = __hsException(e);
        }
        return B(A(handler,[e, 0]));
    }
}

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Object) {
        return x._;
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round, rintDouble = jsRound, rintFloat = jsRound;
var jsTrunc = Math.trunc ? Math.trunc : function(x) {
    return x < 0 ? Math.ceil(x) : Math.floor(x);
};
function jsRoundW(n) {
    return Math.abs(jsTrunc(n));
}
var realWorld = undefined;
if(typeof _ == 'undefined') {
    var _ = undefined;
}

function popCnt64(i) {
    return popCnt(i.low) + popCnt(i.high);
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

function __clz(bits, x) {
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    } else {
        return bits - (1 + Math.floor(Math.log(x)/Math.LN2));
    }
}

// TODO: can probably be done much faster with arithmetic tricks like __clz
function __ctz(bits, x) {
    var y = 1;
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    }
    for(var i = 0; i < bits; ++i) {
        if(y & x) {
            return i;
        } else {
            y <<= 1;
        }
    }
    return 0;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    if(x === 0) {
        return __decodedZeroF;
    }
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return {_:0, a:sign*man, b:exp};
}

var __decodedZero = {_:0,a:1,b:0,c:0,d:0};
var __decodedZeroF = {_:0,a:1,b:0};

function decodeDouble(x) {
    if(x === 0) {
        // GHC 7.10+ *really* doesn't like 0 to be represented as anything
        // but zeroes all the way.
        return __decodedZero;
    }
    rts_scratchDouble[0] = x;
    var sign = x < 0 ? -1 : 1;
    var manHigh = rts_scratchW32[1] & 0xfffff;
    var manLow = rts_scratchW32[0];
    var exp = ((rts_scratchW32[1] >> 20) & 0x7ff) - 1075;
    if(exp === 0) {
        ++exp;
    } else {
        manHigh |= (1 << 20);
    }
    return {_:0, a:sign, b:manHigh, c:manLow, d:exp};
}

function isNull(obj) {
    return obj === null;
}

function jsRead(str) {
    return Number(str);
}

function jsShowI(val) {return val.toString();}
function jsShow(val) {
    var ret = val.toString();
    return val == Math.round(val) ? ret + '.0' : ret;
}

window['jsGetMouseCoords'] = function jsGetMouseCoords(e) {
    var posx = 0;
    var posy = 0;
    if (!e) var e = window.event;
    if (e.pageX || e.pageY) 	{
	posx = e.pageX;
	posy = e.pageY;
    }
    else if (e.clientX || e.clientY) 	{
	posx = e.clientX + document.body.scrollLeft
	    + document.documentElement.scrollLeft;
	posy = e.clientY + document.body.scrollTop
	    + document.documentElement.scrollTop;
    }
    return [posx - (e.currentTarget.offsetLeft || 0),
	    posy - (e.currentTarget.offsetTop || 0)];
}

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs._) {
        strs = E(strs);
        arr.push(E(strs.a));
        strs = E(strs.b);
    }
    return arr.join(sep);
}

// Parse a JSON message into a Haste.JSON.JSON value.
// As this pokes around inside Haskell values, it'll need to be updated if:
// * Haste.JSON.JSON changes;
// * E() starts to choke on non-thunks;
// * data constructor code generation changes; or
// * Just and Nothing change tags.
function jsParseJSON(str) {
    try {
        var js = JSON.parse(str);
        var hs = toHS(js);
    } catch(_) {
        return __Z;
    }
    return {_:1,a:hs};
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return {_:0, a:jsRead(obj)};
    case 'string':
        return {_:1, a:obj};
    case 'boolean':
        return {_:2, a:obj}; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return {_:3, a:arr2lst_json(obj, 0)};
        } else if (obj == null) {
            return {_:5};
        } else {
            // Object type but not array - it's a dictionary.
            // The RFC doesn't say anything about the ordering of keys, but
            // considering that lots of people rely on keys being "in order" as
            // defined by "the same way someone put them in at the other end,"
            // it's probably a good idea to put some cycles into meeting their
            // misguided expectations.
            var ks = [];
            for(var k in obj) {
                ks.unshift(k);
            }
            var xs = [0];
            for(var i = 0; i < ks.length; i++) {
                xs = {_:1, a:{_:0, a:ks[i], b:toHS(obj[ks[i]])}, b:xs};
            }
            return {_:4, a:xs};
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1, a:toHS(arr[elem]), b:new T(function() {return arr2lst_json(arr,elem+1);}),c:true}
}

/* gettimeofday(2) */
function gettimeofday(tv, _tz) {
    var t = new Date().getTime();
    writeOffAddr("i32", 4, tv, 0, (t/1000)|0);
    writeOffAddr("i32", 4, tv, 1, ((t%1000)*1000)|0);
    return 0;
}

// Create a little endian ArrayBuffer representation of something.
function toABHost(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    return a;
}

function toABSwap(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    var bs = new Uint8Array(a);
    for(var i = 0, j = n-1; i < j; ++i, --j) {
        var tmp = bs[i];
        bs[i] = bs[j];
        bs[j] = tmp;
    }
    return a;
}

window['toABle'] = toABHost;
window['toABbe'] = toABSwap;

// Swap byte order if host is not little endian.
var buffer = new ArrayBuffer(2);
new DataView(buffer).setInt16(0, 256, true);
if(new Int16Array(buffer)[0] !== 256) {
    window['toABle'] = toABSwap;
    window['toABbe'] = toABHost;
}

/* bn.js by Fedor Indutny, see doc/LICENSE.bn for license */
var __bn = {};
(function (module, exports) {
'use strict';

function BN(number, base, endian) {
  // May be `new BN(bn)` ?
  if (number !== null &&
      typeof number === 'object' &&
      Array.isArray(number.words)) {
    return number;
  }

  this.negative = 0;
  this.words = null;
  this.length = 0;

  if (base === 'le' || base === 'be') {
    endian = base;
    base = 10;
  }

  if (number !== null)
    this._init(number || 0, base || 10, endian || 'be');
}
if (typeof module === 'object')
  module.exports = BN;
else
  exports.BN = BN;

BN.BN = BN;
BN.wordSize = 26;

BN.max = function max(left, right) {
  if (left.cmp(right) > 0)
    return left;
  else
    return right;
};

BN.min = function min(left, right) {
  if (left.cmp(right) < 0)
    return left;
  else
    return right;
};

BN.prototype._init = function init(number, base, endian) {
  if (typeof number === 'number') {
    return this._initNumber(number, base, endian);
  } else if (typeof number === 'object') {
    return this._initArray(number, base, endian);
  }
  if (base === 'hex')
    base = 16;

  number = number.toString().replace(/\s+/g, '');
  var start = 0;
  if (number[0] === '-')
    start++;

  if (base === 16)
    this._parseHex(number, start);
  else
    this._parseBase(number, base, start);

  if (number[0] === '-')
    this.negative = 1;

  this.strip();

  if (endian !== 'le')
    return;

  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initNumber = function _initNumber(number, base, endian) {
  if (number < 0) {
    this.negative = 1;
    number = -number;
  }
  if (number < 0x4000000) {
    this.words = [ number & 0x3ffffff ];
    this.length = 1;
  } else if (number < 0x10000000000000) {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff
    ];
    this.length = 2;
  } else {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff,
      1
    ];
    this.length = 3;
  }

  if (endian !== 'le')
    return;

  // Reverse the bytes
  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initArray = function _initArray(number, base, endian) {
  if (number.length <= 0) {
    this.words = [ 0 ];
    this.length = 1;
    return this;
  }

  this.length = Math.ceil(number.length / 3);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  var off = 0;
  if (endian === 'be') {
    for (var i = number.length - 1, j = 0; i >= 0; i -= 3) {
      var w = number[i] | (number[i - 1] << 8) | (number[i - 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  } else if (endian === 'le') {
    for (var i = 0, j = 0; i < number.length; i += 3) {
      var w = number[i] | (number[i + 1] << 8) | (number[i + 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  }
  return this.strip();
};

function parseHex(str, start, end) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r <<= 4;

    // 'a' - 'f'
    if (c >= 49 && c <= 54)
      r |= c - 49 + 0xa;

    // 'A' - 'F'
    else if (c >= 17 && c <= 22)
      r |= c - 17 + 0xa;

    // '0' - '9'
    else
      r |= c & 0xf;
  }
  return r;
}

BN.prototype._parseHex = function _parseHex(number, start) {
  // Create possibly bigger array to ensure that it fits the number
  this.length = Math.ceil((number.length - start) / 6);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  // Scan 24-bit chunks and add them to the number
  var off = 0;
  for (var i = number.length - 6, j = 0; i >= start; i -= 6) {
    var w = parseHex(number, i, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
    off += 24;
    if (off >= 26) {
      off -= 26;
      j++;
    }
  }
  if (i + 6 !== start) {
    var w = parseHex(number, start, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
  }
  this.strip();
};

function parseBase(str, start, end, mul) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r *= mul;

    // 'a'
    if (c >= 49)
      r += c - 49 + 0xa;

    // 'A'
    else if (c >= 17)
      r += c - 17 + 0xa;

    // '0' - '9'
    else
      r += c;
  }
  return r;
}

BN.prototype._parseBase = function _parseBase(number, base, start) {
  // Initialize as zero
  this.words = [ 0 ];
  this.length = 1;

  // Find length of limb in base
  for (var limbLen = 0, limbPow = 1; limbPow <= 0x3ffffff; limbPow *= base)
    limbLen++;
  limbLen--;
  limbPow = (limbPow / base) | 0;

  var total = number.length - start;
  var mod = total % limbLen;
  var end = Math.min(total, total - mod) + start;

  var word = 0;
  for (var i = start; i < end; i += limbLen) {
    word = parseBase(number, i, i + limbLen, base);

    this.imuln(limbPow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }

  if (mod !== 0) {
    var pow = 1;
    var word = parseBase(number, i, number.length, base);

    for (var i = 0; i < mod; i++)
      pow *= base;
    this.imuln(pow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }
};

BN.prototype.copy = function copy(dest) {
  dest.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    dest.words[i] = this.words[i];
  dest.length = this.length;
  dest.negative = this.negative;
};

BN.prototype.clone = function clone() {
  var r = new BN(null);
  this.copy(r);
  return r;
};

// Remove leading `0` from `this`
BN.prototype.strip = function strip() {
  while (this.length > 1 && this.words[this.length - 1] === 0)
    this.length--;
  return this._normSign();
};

BN.prototype._normSign = function _normSign() {
  // -0 = 0
  if (this.length === 1 && this.words[0] === 0)
    this.negative = 0;
  return this;
};

var zeros = [
  '',
  '0',
  '00',
  '000',
  '0000',
  '00000',
  '000000',
  '0000000',
  '00000000',
  '000000000',
  '0000000000',
  '00000000000',
  '000000000000',
  '0000000000000',
  '00000000000000',
  '000000000000000',
  '0000000000000000',
  '00000000000000000',
  '000000000000000000',
  '0000000000000000000',
  '00000000000000000000',
  '000000000000000000000',
  '0000000000000000000000',
  '00000000000000000000000',
  '000000000000000000000000',
  '0000000000000000000000000'
];

var groupSizes = [
  0, 0,
  25, 16, 12, 11, 10, 9, 8,
  8, 7, 7, 7, 7, 6, 6,
  6, 6, 6, 6, 6, 5, 5,
  5, 5, 5, 5, 5, 5, 5,
  5, 5, 5, 5, 5, 5, 5
];

var groupBases = [
  0, 0,
  33554432, 43046721, 16777216, 48828125, 60466176, 40353607, 16777216,
  43046721, 10000000, 19487171, 35831808, 62748517, 7529536, 11390625,
  16777216, 24137569, 34012224, 47045881, 64000000, 4084101, 5153632,
  6436343, 7962624, 9765625, 11881376, 14348907, 17210368, 20511149,
  24300000, 28629151, 33554432, 39135393, 45435424, 52521875, 60466176
];

BN.prototype.toString = function toString(base, padding) {
  base = base || 10;
  var padding = padding | 0 || 1;
  if (base === 16 || base === 'hex') {
    var out = '';
    var off = 0;
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var w = this.words[i];
      var word = (((w << off) | carry) & 0xffffff).toString(16);
      carry = (w >>> (24 - off)) & 0xffffff;
      if (carry !== 0 || i !== this.length - 1)
        out = zeros[6 - word.length] + word + out;
      else
        out = word + out;
      off += 2;
      if (off >= 26) {
        off -= 26;
        i--;
      }
    }
    if (carry !== 0)
      out = carry.toString(16) + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else if (base === (base | 0) && base >= 2 && base <= 36) {
    var groupSize = groupSizes[base];
    var groupBase = groupBases[base];
    var out = '';
    var c = this.clone();
    c.negative = 0;
    while (c.cmpn(0) !== 0) {
      var r = c.modn(groupBase).toString(base);
      c = c.idivn(groupBase);

      if (c.cmpn(0) !== 0)
        out = zeros[groupSize - r.length] + r + out;
      else
        out = r + out;
    }
    if (this.cmpn(0) === 0)
      out = '0' + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else {
    throw 'Base should be between 2 and 36';
  }
};

BN.prototype.toJSON = function toJSON() {
  return this.toString(16);
};

BN.prototype.toArray = function toArray(endian, length) {
  this.strip();
  var littleEndian = endian === 'le';
  var res = new Array(this.byteLength());
  res[0] = 0;

  var q = this.clone();
  if (!littleEndian) {
    // Assume big-endian
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[res.length - i - 1] = b;
    }
  } else {
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[i] = b;
    }
  }

  if (length) {
    while (res.length < length) {
      if (littleEndian)
        res.push(0);
      else
        res.unshift(0);
    }
  }

  return res;
};

if (Math.clz32) {
  BN.prototype._countBits = function _countBits(w) {
    return 32 - Math.clz32(w);
  };
} else {
  BN.prototype._countBits = function _countBits(w) {
    var t = w;
    var r = 0;
    if (t >= 0x1000) {
      r += 13;
      t >>>= 13;
    }
    if (t >= 0x40) {
      r += 7;
      t >>>= 7;
    }
    if (t >= 0x8) {
      r += 4;
      t >>>= 4;
    }
    if (t >= 0x02) {
      r += 2;
      t >>>= 2;
    }
    return r + t;
  };
}

// Return number of used bits in a BN
BN.prototype.bitLength = function bitLength() {
  var hi = 0;
  var w = this.words[this.length - 1];
  var hi = this._countBits(w);
  return (this.length - 1) * 26 + hi;
};

BN.prototype.byteLength = function byteLength() {
  return Math.ceil(this.bitLength() / 8);
};

// Return negative clone of `this`
BN.prototype.neg = function neg() {
  if (this.cmpn(0) === 0)
    return this.clone();

  var r = this.clone();
  r.negative = this.negative ^ 1;
  return r;
};

BN.prototype.ineg = function ineg() {
  this.negative ^= 1;
  return this;
};

// Or `num` with `this` in-place
BN.prototype.iuor = function iuor(num) {
  while (this.length < num.length)
    this.words[this.length++] = 0;

  for (var i = 0; i < num.length; i++)
    this.words[i] = this.words[i] | num.words[i];

  return this.strip();
};

BN.prototype.ior = function ior(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuor(num);
};


// Or `num` with `this`
BN.prototype.or = function or(num) {
  if (this.length > num.length)
    return this.clone().ior(num);
  else
    return num.clone().ior(this);
};

BN.prototype.uor = function uor(num) {
  if (this.length > num.length)
    return this.clone().iuor(num);
  else
    return num.clone().iuor(this);
};


// And `num` with `this` in-place
BN.prototype.iuand = function iuand(num) {
  // b = min-length(num, this)
  var b;
  if (this.length > num.length)
    b = num;
  else
    b = this;

  for (var i = 0; i < b.length; i++)
    this.words[i] = this.words[i] & num.words[i];

  this.length = b.length;

  return this.strip();
};

BN.prototype.iand = function iand(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuand(num);
};


// And `num` with `this`
BN.prototype.and = function and(num) {
  if (this.length > num.length)
    return this.clone().iand(num);
  else
    return num.clone().iand(this);
};

BN.prototype.uand = function uand(num) {
  if (this.length > num.length)
    return this.clone().iuand(num);
  else
    return num.clone().iuand(this);
};


// Xor `num` with `this` in-place
BN.prototype.iuxor = function iuxor(num) {
  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  for (var i = 0; i < b.length; i++)
    this.words[i] = a.words[i] ^ b.words[i];

  if (this !== a)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];

  this.length = a.length;

  return this.strip();
};

BN.prototype.ixor = function ixor(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuxor(num);
};


// Xor `num` with `this`
BN.prototype.xor = function xor(num) {
  if (this.length > num.length)
    return this.clone().ixor(num);
  else
    return num.clone().ixor(this);
};

BN.prototype.uxor = function uxor(num) {
  if (this.length > num.length)
    return this.clone().iuxor(num);
  else
    return num.clone().iuxor(this);
};


// Add `num` to `this` in-place
BN.prototype.iadd = function iadd(num) {
  // negative + positive
  if (this.negative !== 0 && num.negative === 0) {
    this.negative = 0;
    var r = this.isub(num);
    this.negative ^= 1;
    return this._normSign();

  // positive + negative
  } else if (this.negative === 0 && num.negative !== 0) {
    num.negative = 0;
    var r = this.isub(num);
    num.negative = 1;
    return r._normSign();
  }

  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) + (b.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }

  this.length = a.length;
  if (carry !== 0) {
    this.words[this.length] = carry;
    this.length++;
  // Copy the rest of the words
  } else if (a !== this) {
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  }

  return this;
};

// Add `num` to `this`
BN.prototype.add = function add(num) {
  if (num.negative !== 0 && this.negative === 0) {
    num.negative = 0;
    var res = this.sub(num);
    num.negative ^= 1;
    return res;
  } else if (num.negative === 0 && this.negative !== 0) {
    this.negative = 0;
    var res = num.sub(this);
    this.negative = 1;
    return res;
  }

  if (this.length > num.length)
    return this.clone().iadd(num);
  else
    return num.clone().iadd(this);
};

// Subtract `num` from `this` in-place
BN.prototype.isub = function isub(num) {
  // this - (-num) = this + num
  if (num.negative !== 0) {
    num.negative = 0;
    var r = this.iadd(num);
    num.negative = 1;
    return r._normSign();

  // -this - num = -(this + num)
  } else if (this.negative !== 0) {
    this.negative = 0;
    this.iadd(num);
    this.negative = 1;
    return this._normSign();
  }

  // At this point both numbers are positive
  var cmp = this.cmp(num);

  // Optimization - zeroify
  if (cmp === 0) {
    this.negative = 0;
    this.length = 1;
    this.words[0] = 0;
    return this;
  }

  // a > b
  var a;
  var b;
  if (cmp > 0) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) - (b.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }

  // Copy rest of the words
  if (carry === 0 && i < a.length && a !== this)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  this.length = Math.max(this.length, i);

  if (a !== this)
    this.negative = 1;

  return this.strip();
};

// Subtract `num` from `this`
BN.prototype.sub = function sub(num) {
  return this.clone().isub(num);
};

function smallMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  var len = (self.length + num.length) | 0;
  out.length = len;
  len = (len - 1) | 0;

  // Peel one iteration (compiler can't do it, because of code complexity)
  var a = self.words[0] | 0;
  var b = num.words[0] | 0;
  var r = a * b;

  var lo = r & 0x3ffffff;
  var carry = (r / 0x4000000) | 0;
  out.words[0] = lo;

  for (var k = 1; k < len; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = carry >>> 26;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = (k - j) | 0;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;
    }
    out.words[k] = rword | 0;
    carry = ncarry | 0;
  }
  if (carry !== 0) {
    out.words[k] = carry | 0;
  } else {
    out.length--;
  }

  return out.strip();
}

function bigMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  out.length = self.length + num.length;

  var carry = 0;
  var hncarry = 0;
  for (var k = 0; k < out.length - 1; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = hncarry;
    hncarry = 0;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;

      hncarry += ncarry >>> 26;
      ncarry &= 0x3ffffff;
    }
    out.words[k] = rword;
    carry = ncarry;
    ncarry = hncarry;
  }
  if (carry !== 0) {
    out.words[k] = carry;
  } else {
    out.length--;
  }

  return out.strip();
}

BN.prototype.mulTo = function mulTo(num, out) {
  var res;
  if (this.length + num.length < 63)
    res = smallMulTo(this, num, out);
  else
    res = bigMulTo(this, num, out);
  return res;
};

// Multiply `this` by `num`
BN.prototype.mul = function mul(num) {
  var out = new BN(null);
  out.words = new Array(this.length + num.length);
  return this.mulTo(num, out);
};

// In-place Multiplication
BN.prototype.imul = function imul(num) {
  if (this.cmpn(0) === 0 || num.cmpn(0) === 0) {
    this.words[0] = 0;
    this.length = 1;
    return this;
  }

  var tlen = this.length;
  var nlen = num.length;

  this.negative = num.negative ^ this.negative;
  this.length = this.length + num.length;
  this.words[this.length - 1] = 0;

  for (var k = this.length - 2; k >= 0; k--) {
    // Sum all words with the same `i + j = k` and accumulate `carry`,
    // note that carry could be >= 0x3ffffff
    var carry = 0;
    var rword = 0;
    var maxJ = Math.min(k, nlen - 1);
    for (var j = Math.max(0, k - tlen + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = this.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      carry += (r / 0x4000000) | 0;
      lo += rword;
      rword = lo & 0x3ffffff;
      carry += lo >>> 26;
    }
    this.words[k] = rword;
    this.words[k + 1] += carry;
    carry = 0;
  }

  // Propagate overflows
  var carry = 0;
  for (var i = 1; i < this.length; i++) {
    var w = (this.words[i] | 0) + carry;
    this.words[i] = w & 0x3ffffff;
    carry = w >>> 26;
  }

  return this.strip();
};

BN.prototype.imuln = function imuln(num) {
  // Carry
  var carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = (this.words[i] | 0) * num;
    var lo = (w & 0x3ffffff) + (carry & 0x3ffffff);
    carry >>= 26;
    carry += (w / 0x4000000) | 0;
    // NOTE: lo is 27bit maximum
    carry += lo >>> 26;
    this.words[i] = lo & 0x3ffffff;
  }

  if (carry !== 0) {
    this.words[i] = carry;
    this.length++;
  }

  return this;
};

BN.prototype.muln = function muln(num) {
  return this.clone().imuln(num);
};

// `this` * `this`
BN.prototype.sqr = function sqr() {
  return this.mul(this);
};

// `this` * `this` in-place
BN.prototype.isqr = function isqr() {
  return this.mul(this);
};

// Shift-left in-place
BN.prototype.iushln = function iushln(bits) {
  var r = bits % 26;
  var s = (bits - r) / 26;
  var carryMask = (0x3ffffff >>> (26 - r)) << (26 - r);

  if (r !== 0) {
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var newCarry = this.words[i] & carryMask;
      var c = ((this.words[i] | 0) - newCarry) << r;
      this.words[i] = c | carry;
      carry = newCarry >>> (26 - r);
    }
    if (carry) {
      this.words[i] = carry;
      this.length++;
    }
  }

  if (s !== 0) {
    for (var i = this.length - 1; i >= 0; i--)
      this.words[i + s] = this.words[i];
    for (var i = 0; i < s; i++)
      this.words[i] = 0;
    this.length += s;
  }

  return this.strip();
};

BN.prototype.ishln = function ishln(bits) {
  return this.iushln(bits);
};

// Shift-right in-place
BN.prototype.iushrn = function iushrn(bits, hint, extended) {
  var h;
  if (hint)
    h = (hint - (hint % 26)) / 26;
  else
    h = 0;

  var r = bits % 26;
  var s = Math.min((bits - r) / 26, this.length);
  var mask = 0x3ffffff ^ ((0x3ffffff >>> r) << r);
  var maskedWords = extended;

  h -= s;
  h = Math.max(0, h);

  // Extended mode, copy masked part
  if (maskedWords) {
    for (var i = 0; i < s; i++)
      maskedWords.words[i] = this.words[i];
    maskedWords.length = s;
  }

  if (s === 0) {
    // No-op, we should not move anything at all
  } else if (this.length > s) {
    this.length -= s;
    for (var i = 0; i < this.length; i++)
      this.words[i] = this.words[i + s];
  } else {
    this.words[0] = 0;
    this.length = 1;
  }

  var carry = 0;
  for (var i = this.length - 1; i >= 0 && (carry !== 0 || i >= h); i--) {
    var word = this.words[i] | 0;
    this.words[i] = (carry << (26 - r)) | (word >>> r);
    carry = word & mask;
  }

  // Push carried bits as a mask
  if (maskedWords && carry !== 0)
    maskedWords.words[maskedWords.length++] = carry;

  if (this.length === 0) {
    this.words[0] = 0;
    this.length = 1;
  }

  this.strip();

  return this;
};

BN.prototype.ishrn = function ishrn(bits, hint, extended) {
  return this.iushrn(bits, hint, extended);
};

// Shift-left
BN.prototype.shln = function shln(bits) {
  var x = this.clone();
  var neg = x.negative;
  x.negative = false;
  x.ishln(bits);
  x.negative = neg;
  return x;
};

BN.prototype.ushln = function ushln(bits) {
  return this.clone().iushln(bits);
};

// Shift-right
BN.prototype.shrn = function shrn(bits) {
  var x = this.clone();
  if(x.negative) {
      x.negative = false;
      x.ishrn(bits);
      x.negative = true;
      return x.isubn(1);
  } else {
      return x.ishrn(bits);
  }
};

BN.prototype.ushrn = function ushrn(bits) {
  return this.clone().iushrn(bits);
};

// Test if n bit is set
BN.prototype.testn = function testn(bit) {
  var r = bit % 26;
  var s = (bit - r) / 26;
  var q = 1 << r;

  // Fast case: bit is much higher than all existing words
  if (this.length <= s) {
    return false;
  }

  // Check bit and return
  var w = this.words[s];

  return !!(w & q);
};

// Add plain number `num` to `this`
BN.prototype.iaddn = function iaddn(num) {
  if (num < 0)
    return this.isubn(-num);

  // Possible sign change
  if (this.negative !== 0) {
    if (this.length === 1 && (this.words[0] | 0) < num) {
      this.words[0] = num - (this.words[0] | 0);
      this.negative = 0;
      return this;
    }

    this.negative = 0;
    this.isubn(num);
    this.negative = 1;
    return this;
  }

  // Add without checks
  return this._iaddn(num);
};

BN.prototype._iaddn = function _iaddn(num) {
  this.words[0] += num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] >= 0x4000000; i++) {
    this.words[i] -= 0x4000000;
    if (i === this.length - 1)
      this.words[i + 1] = 1;
    else
      this.words[i + 1]++;
  }
  this.length = Math.max(this.length, i + 1);

  return this;
};

// Subtract plain number `num` from `this`
BN.prototype.isubn = function isubn(num) {
  if (num < 0)
    return this.iaddn(-num);

  if (this.negative !== 0) {
    this.negative = 0;
    this.iaddn(num);
    this.negative = 1;
    return this;
  }

  this.words[0] -= num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] < 0; i++) {
    this.words[i] += 0x4000000;
    this.words[i + 1] -= 1;
  }

  return this.strip();
};

BN.prototype.addn = function addn(num) {
  return this.clone().iaddn(num);
};

BN.prototype.subn = function subn(num) {
  return this.clone().isubn(num);
};

BN.prototype.iabs = function iabs() {
  this.negative = 0;

  return this;
};

BN.prototype.abs = function abs() {
  return this.clone().iabs();
};

BN.prototype._ishlnsubmul = function _ishlnsubmul(num, mul, shift) {
  // Bigger storage is needed
  var len = num.length + shift;
  var i;
  if (this.words.length < len) {
    var t = new Array(len);
    for (var i = 0; i < this.length; i++)
      t[i] = this.words[i];
    this.words = t;
  } else {
    i = this.length;
  }

  // Zeroify rest
  this.length = Math.max(this.length, len);
  for (; i < this.length; i++)
    this.words[i] = 0;

  var carry = 0;
  for (var i = 0; i < num.length; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    var right = (num.words[i] | 0) * mul;
    w -= right & 0x3ffffff;
    carry = (w >> 26) - ((right / 0x4000000) | 0);
    this.words[i + shift] = w & 0x3ffffff;
  }
  for (; i < this.length - shift; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    carry = w >> 26;
    this.words[i + shift] = w & 0x3ffffff;
  }

  if (carry === 0)
    return this.strip();

  carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = -(this.words[i] | 0) + carry;
    carry = w >> 26;
    this.words[i] = w & 0x3ffffff;
  }
  this.negative = 1;

  return this.strip();
};

BN.prototype._wordDiv = function _wordDiv(num, mode) {
  var shift = this.length - num.length;

  var a = this.clone();
  var b = num;

  // Normalize
  var bhi = b.words[b.length - 1] | 0;
  var bhiBits = this._countBits(bhi);
  shift = 26 - bhiBits;
  if (shift !== 0) {
    b = b.ushln(shift);
    a.iushln(shift);
    bhi = b.words[b.length - 1] | 0;
  }

  // Initialize quotient
  var m = a.length - b.length;
  var q;

  if (mode !== 'mod') {
    q = new BN(null);
    q.length = m + 1;
    q.words = new Array(q.length);
    for (var i = 0; i < q.length; i++)
      q.words[i] = 0;
  }

  var diff = a.clone()._ishlnsubmul(b, 1, m);
  if (diff.negative === 0) {
    a = diff;
    if (q)
      q.words[m] = 1;
  }

  for (var j = m - 1; j >= 0; j--) {
    var qj = (a.words[b.length + j] | 0) * 0x4000000 +
             (a.words[b.length + j - 1] | 0);

    // NOTE: (qj / bhi) is (0x3ffffff * 0x4000000 + 0x3ffffff) / 0x2000000 max
    // (0x7ffffff)
    qj = Math.min((qj / bhi) | 0, 0x3ffffff);

    a._ishlnsubmul(b, qj, j);
    while (a.negative !== 0) {
      qj--;
      a.negative = 0;
      a._ishlnsubmul(b, 1, j);
      if (a.cmpn(0) !== 0)
        a.negative ^= 1;
    }
    if (q)
      q.words[j] = qj;
  }
  if (q)
    q.strip();
  a.strip();

  // Denormalize
  if (mode !== 'div' && shift !== 0)
    a.iushrn(shift);
  return { div: q ? q : null, mod: a };
};

BN.prototype.divmod = function divmod(num, mode, positive) {
  if (this.negative !== 0 && num.negative === 0) {
    var res = this.neg().divmod(num, mode);
    var div;
    var mod;
    if (mode !== 'mod')
      div = res.div.neg();
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.add(num);
    }
    return {
      div: div,
      mod: mod
    };
  } else if (this.negative === 0 && num.negative !== 0) {
    var res = this.divmod(num.neg(), mode);
    var div;
    if (mode !== 'mod')
      div = res.div.neg();
    return { div: div, mod: res.mod };
  } else if ((this.negative & num.negative) !== 0) {
    var res = this.neg().divmod(num.neg(), mode);
    var mod;
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.isub(num);
    }
    return {
      div: res.div,
      mod: mod
    };
  }

  // Both numbers are positive at this point

  // Strip both numbers to approximate shift value
  if (num.length > this.length || this.cmp(num) < 0)
    return { div: new BN(0), mod: this };

  // Very short reduction
  if (num.length === 1) {
    if (mode === 'div')
      return { div: this.divn(num.words[0]), mod: null };
    else if (mode === 'mod')
      return { div: null, mod: new BN(this.modn(num.words[0])) };
    return {
      div: this.divn(num.words[0]),
      mod: new BN(this.modn(num.words[0]))
    };
  }

  return this._wordDiv(num, mode);
};

// Find `this` / `num`
BN.prototype.div = function div(num) {
  return this.divmod(num, 'div', false).div;
};

// Find `this` % `num`
BN.prototype.mod = function mod(num) {
  return this.divmod(num, 'mod', false).mod;
};

BN.prototype.umod = function umod(num) {
  return this.divmod(num, 'mod', true).mod;
};

// Find Round(`this` / `num`)
BN.prototype.divRound = function divRound(num) {
  var dm = this.divmod(num);

  // Fast case - exact division
  if (dm.mod.cmpn(0) === 0)
    return dm.div;

  var mod = dm.div.negative !== 0 ? dm.mod.isub(num) : dm.mod;

  var half = num.ushrn(1);
  var r2 = num.andln(1);
  var cmp = mod.cmp(half);

  // Round down
  if (cmp < 0 || r2 === 1 && cmp === 0)
    return dm.div;

  // Round up
  return dm.div.negative !== 0 ? dm.div.isubn(1) : dm.div.iaddn(1);
};

BN.prototype.modn = function modn(num) {
  var p = (1 << 26) % num;

  var acc = 0;
  for (var i = this.length - 1; i >= 0; i--)
    acc = (p * acc + (this.words[i] | 0)) % num;

  return acc;
};

// In-place division by number
BN.prototype.idivn = function idivn(num) {
  var carry = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var w = (this.words[i] | 0) + carry * 0x4000000;
    this.words[i] = (w / num) | 0;
    carry = w % num;
  }

  return this.strip();
};

BN.prototype.divn = function divn(num) {
  return this.clone().idivn(num);
};

BN.prototype.isEven = function isEven() {
  return (this.words[0] & 1) === 0;
};

BN.prototype.isOdd = function isOdd() {
  return (this.words[0] & 1) === 1;
};

// And first word and num
BN.prototype.andln = function andln(num) {
  return this.words[0] & num;
};

BN.prototype.cmpn = function cmpn(num) {
  var negative = num < 0;
  if (negative)
    num = -num;

  if (this.negative !== 0 && !negative)
    return -1;
  else if (this.negative === 0 && negative)
    return 1;

  num &= 0x3ffffff;
  this.strip();

  var res;
  if (this.length > 1) {
    res = 1;
  } else {
    var w = this.words[0] | 0;
    res = w === num ? 0 : w < num ? -1 : 1;
  }
  if (this.negative !== 0)
    res = -res;
  return res;
};

// Compare two numbers and return:
// 1 - if `this` > `num`
// 0 - if `this` == `num`
// -1 - if `this` < `num`
BN.prototype.cmp = function cmp(num) {
  if (this.negative !== 0 && num.negative === 0)
    return -1;
  else if (this.negative === 0 && num.negative !== 0)
    return 1;

  var res = this.ucmp(num);
  if (this.negative !== 0)
    return -res;
  else
    return res;
};

// Unsigned comparison
BN.prototype.ucmp = function ucmp(num) {
  // At this point both numbers have the same sign
  if (this.length > num.length)
    return 1;
  else if (this.length < num.length)
    return -1;

  var res = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var a = this.words[i] | 0;
    var b = num.words[i] | 0;

    if (a === b)
      continue;
    if (a < b)
      res = -1;
    else if (a > b)
      res = 1;
    break;
  }
  return res;
};
})(undefined, __bn);

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return {_:0, a:0, b:undefined};
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return {_:0, a:1, b:val};
    }
}

function takeMVar(mv) {
    if(mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to take empty MVar!");
    }
    var val = mv.x;
    mv.empty = true;
    mv.x = null;
    return val;
}

function putMVar(mv, val) {
    if(!mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to put full MVar!");
    }
    mv.empty = false;
    mv.x = val;
}

function tryPutMVar(mv, val) {
    if(!mv.empty) {
        return 0;
    } else {
        mv.empty = false;
        mv.x = val;
        return 1;
    }
}

function sameMVar(a, b) {
    return (a == b);
}

function isEmptyMVar(mv) {
    return mv.empty ? 1 : 0;
}

// Implementation of stable names.
// Unlike native GHC, the garbage collector isn't going to move data around
// in a way that we can detect, so each object could serve as its own stable
// name if it weren't for the fact we can't turn a JS reference into an
// integer.
// So instead, each object has a unique integer attached to it, which serves
// as its stable name.

var __next_stable_name = 1;
var __stable_table;

function makeStableName(x) {
    if(x instanceof Object) {
        if(!x.stableName) {
            x.stableName = __next_stable_name;
            __next_stable_name += 1;
        }
        return {type: 'obj', name: x.stableName};
    } else {
        return {type: 'prim', name: Number(x)};
    }
}

function eqStableName(x, y) {
    return (x.type == y.type && x.name == y.name) ? 1 : 0;
}

// TODO: inefficient compared to real fromInt?
__bn.Z = new __bn.BN(0);
__bn.ONE = new __bn.BN(1);
__bn.MOD32 = new __bn.BN(0x100000000); // 2^32
var I_fromNumber = function(x) {return new __bn.BN(x);}
var I_fromInt = I_fromNumber;
var I_fromBits = function(lo,hi) {
    var x = new __bn.BN(lo >>> 0);
    var y = new __bn.BN(hi >>> 0);
    y.ishln(32);
    x.iadd(y);
    return x;
}
var I_fromString = function(s) {return new __bn.BN(s);}
var I_toInt = function(x) {return I_toNumber(x.mod(__bn.MOD32));}
var I_toWord = function(x) {return I_toInt(x) >>> 0;};
// TODO: inefficient!
var I_toNumber = function(x) {return Number(x.toString());}
var I_equals = function(a,b) {return a.cmp(b) === 0;}
var I_compare = function(a,b) {return a.cmp(b);}
var I_compareInt = function(x,i) {return x.cmp(new __bn.BN(i));}
var I_negate = function(x) {return x.neg();}
var I_add = function(a,b) {return a.add(b);}
var I_sub = function(a,b) {return a.sub(b);}
var I_mul = function(a,b) {return a.mul(b);}
var I_mod = function(a,b) {return I_rem(I_add(b, I_rem(a, b)), b);}
var I_quotRem = function(a,b) {
    var qr = a.divmod(b);
    return {_:0, a:qr.div, b:qr.mod};
}
var I_div = function(a,b) {
    if((a.cmp(__bn.Z)>=0) != (a.cmp(__bn.Z)>=0)) {
        if(a.cmp(a.rem(b), __bn.Z) !== 0) {
            return a.div(b).sub(__bn.ONE);
        }
    }
    return a.div(b);
}
var I_divMod = function(a,b) {
    return {_:0, a:I_div(a,b), b:a.mod(b)};
}
var I_quot = function(a,b) {return a.div(b);}
var I_rem = function(a,b) {return a.mod(b);}
var I_and = function(a,b) {return a.and(b);}
var I_or = function(a,b) {return a.or(b);}
var I_xor = function(a,b) {return a.xor(b);}
var I_shiftLeft = function(a,b) {return a.shln(b);}
var I_shiftRight = function(a,b) {return a.shrn(b);}
var I_signum = function(x) {return x.cmp(new __bn.BN(0));}
var I_abs = function(x) {return x.abs();}
var I_decodeDouble = function(x) {
    var dec = decodeDouble(x);
    var mantissa = I_fromBits(dec.c, dec.b);
    if(dec.a < 0) {
        mantissa = I_negate(mantissa);
    }
    return {_:0, a:dec.d, b:mantissa};
}
var I_toString = function(x) {return x.toString();}
var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    if(x.isNegative()) {
        return I_negate(I_fromInt64(x.negate()));
    } else {
        return I_fromBits(x.low, x.high);
    }
}

function I_toInt64(x) {
    if(x.negative) {
        return I_toInt64(I_negate(x)).negate();
    } else {
        return new Long(I_toInt(x), I_toInt(I_shiftRight(x,32)));
    }
}

function I_fromWord64(x) {
    return I_fromBits(x.toInt(), x.shru(32).toInt());
}

function I_toWord64(x) {
    var w = I_toInt64(x);
    w.unsigned = true;
    return w;
}

/**
 * @license long.js (c) 2013 Daniel Wirtz <dcode@dcode.io>
 * Released under the Apache License, Version 2.0
 * see: https://github.com/dcodeIO/long.js for details
 */
function Long(low, high, unsigned) {
    this.low = low | 0;
    this.high = high | 0;
    this.unsigned = !!unsigned;
}

var INT_CACHE = {};
var UINT_CACHE = {};
function cacheable(x, u) {
    return u ? 0 <= (x >>>= 0) && x < 256 : -128 <= (x |= 0) && x < 128;
}

function __fromInt(value, unsigned) {
    var obj, cachedObj, cache;
    if (unsigned) {
        if (cache = cacheable(value >>>= 0, true)) {
            cachedObj = UINT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, (value | 0) < 0 ? -1 : 0, true);
        if (cache)
            UINT_CACHE[value] = obj;
        return obj;
    } else {
        if (cache = cacheable(value |= 0, false)) {
            cachedObj = INT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, value < 0 ? -1 : 0, false);
        if (cache)
            INT_CACHE[value] = obj;
        return obj;
    }
}

function __fromNumber(value, unsigned) {
    if (isNaN(value) || !isFinite(value))
        return unsigned ? UZERO : ZERO;
    if (unsigned) {
        if (value < 0)
            return UZERO;
        if (value >= TWO_PWR_64_DBL)
            return MAX_UNSIGNED_VALUE;
    } else {
        if (value <= -TWO_PWR_63_DBL)
            return MIN_VALUE;
        if (value + 1 >= TWO_PWR_63_DBL)
            return MAX_VALUE;
    }
    if (value < 0)
        return __fromNumber(-value, unsigned).neg();
    return new Long((value % TWO_PWR_32_DBL) | 0, (value / TWO_PWR_32_DBL) | 0, unsigned);
}
var pow_dbl = Math.pow;
var TWO_PWR_16_DBL = 1 << 16;
var TWO_PWR_24_DBL = 1 << 24;
var TWO_PWR_32_DBL = TWO_PWR_16_DBL * TWO_PWR_16_DBL;
var TWO_PWR_64_DBL = TWO_PWR_32_DBL * TWO_PWR_32_DBL;
var TWO_PWR_63_DBL = TWO_PWR_64_DBL / 2;
var TWO_PWR_24 = __fromInt(TWO_PWR_24_DBL);
var ZERO = __fromInt(0);
Long.ZERO = ZERO;
var UZERO = __fromInt(0, true);
Long.UZERO = UZERO;
var ONE = __fromInt(1);
Long.ONE = ONE;
var UONE = __fromInt(1, true);
Long.UONE = UONE;
var NEG_ONE = __fromInt(-1);
Long.NEG_ONE = NEG_ONE;
var MAX_VALUE = new Long(0xFFFFFFFF|0, 0x7FFFFFFF|0, false);
Long.MAX_VALUE = MAX_VALUE;
var MAX_UNSIGNED_VALUE = new Long(0xFFFFFFFF|0, 0xFFFFFFFF|0, true);
Long.MAX_UNSIGNED_VALUE = MAX_UNSIGNED_VALUE;
var MIN_VALUE = new Long(0, 0x80000000|0, false);
Long.MIN_VALUE = MIN_VALUE;
var __lp = Long.prototype;
__lp.toInt = function() {return this.unsigned ? this.low >>> 0 : this.low;};
__lp.toNumber = function() {
    if (this.unsigned)
        return ((this.high >>> 0) * TWO_PWR_32_DBL) + (this.low >>> 0);
    return this.high * TWO_PWR_32_DBL + (this.low >>> 0);
};
__lp.isZero = function() {return this.high === 0 && this.low === 0;};
__lp.isNegative = function() {return !this.unsigned && this.high < 0;};
__lp.isOdd = function() {return (this.low & 1) === 1;};
__lp.eq = function(other) {
    if (this.unsigned !== other.unsigned && (this.high >>> 31) === 1 && (other.high >>> 31) === 1)
        return false;
    return this.high === other.high && this.low === other.low;
};
__lp.neq = function(other) {return !this.eq(other);};
__lp.lt = function(other) {return this.comp(other) < 0;};
__lp.lte = function(other) {return this.comp(other) <= 0;};
__lp.gt = function(other) {return this.comp(other) > 0;};
__lp.gte = function(other) {return this.comp(other) >= 0;};
__lp.compare = function(other) {
    if (this.eq(other))
        return 0;
    var thisNeg = this.isNegative(),
        otherNeg = other.isNegative();
    if (thisNeg && !otherNeg)
        return -1;
    if (!thisNeg && otherNeg)
        return 1;
    if (!this.unsigned)
        return this.sub(other).isNegative() ? -1 : 1;
    return (other.high >>> 0) > (this.high >>> 0) || (other.high === this.high && (other.low >>> 0) > (this.low >>> 0)) ? -1 : 1;
};
__lp.comp = __lp.compare;
__lp.negate = function() {
    if (!this.unsigned && this.eq(MIN_VALUE))
        return MIN_VALUE;
    return this.not().add(ONE);
};
__lp.neg = __lp.negate;
__lp.add = function(addend) {
    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = addend.high >>> 16;
    var b32 = addend.high & 0xFFFF;
    var b16 = addend.low >>> 16;
    var b00 = addend.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 + b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 + b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 + b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 + b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.subtract = function(subtrahend) {return this.add(subtrahend.neg());};
__lp.sub = __lp.subtract;
__lp.multiply = function(multiplier) {
    if (this.isZero())
        return ZERO;
    if (multiplier.isZero())
        return ZERO;
    if (this.eq(MIN_VALUE))
        return multiplier.isOdd() ? MIN_VALUE : ZERO;
    if (multiplier.eq(MIN_VALUE))
        return this.isOdd() ? MIN_VALUE : ZERO;

    if (this.isNegative()) {
        if (multiplier.isNegative())
            return this.neg().mul(multiplier.neg());
        else
            return this.neg().mul(multiplier).neg();
    } else if (multiplier.isNegative())
        return this.mul(multiplier.neg()).neg();

    if (this.lt(TWO_PWR_24) && multiplier.lt(TWO_PWR_24))
        return __fromNumber(this.toNumber() * multiplier.toNumber(), this.unsigned);

    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = multiplier.high >>> 16;
    var b32 = multiplier.high & 0xFFFF;
    var b16 = multiplier.low >>> 16;
    var b00 = multiplier.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 * b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 * b00;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c16 += a00 * b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 * b00;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a16 * b16;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a00 * b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.mul = __lp.multiply;
__lp.divide = function(divisor) {
    if (divisor.isZero())
        throw Error('division by zero');
    if (this.isZero())
        return this.unsigned ? UZERO : ZERO;
    var approx, rem, res;
    if (this.eq(MIN_VALUE)) {
        if (divisor.eq(ONE) || divisor.eq(NEG_ONE))
            return MIN_VALUE;
        else if (divisor.eq(MIN_VALUE))
            return ONE;
        else {
            var halfThis = this.shr(1);
            approx = halfThis.div(divisor).shl(1);
            if (approx.eq(ZERO)) {
                return divisor.isNegative() ? ONE : NEG_ONE;
            } else {
                rem = this.sub(divisor.mul(approx));
                res = approx.add(rem.div(divisor));
                return res;
            }
        }
    } else if (divisor.eq(MIN_VALUE))
        return this.unsigned ? UZERO : ZERO;
    if (this.isNegative()) {
        if (divisor.isNegative())
            return this.neg().div(divisor.neg());
        return this.neg().div(divisor).neg();
    } else if (divisor.isNegative())
        return this.div(divisor.neg()).neg();

    res = ZERO;
    rem = this;
    while (rem.gte(divisor)) {
        approx = Math.max(1, Math.floor(rem.toNumber() / divisor.toNumber()));
        var log2 = Math.ceil(Math.log(approx) / Math.LN2),
            delta = (log2 <= 48) ? 1 : pow_dbl(2, log2 - 48),
            approxRes = __fromNumber(approx),
            approxRem = approxRes.mul(divisor);
        while (approxRem.isNegative() || approxRem.gt(rem)) {
            approx -= delta;
            approxRes = __fromNumber(approx, this.unsigned);
            approxRem = approxRes.mul(divisor);
        }
        if (approxRes.isZero())
            approxRes = ONE;

        res = res.add(approxRes);
        rem = rem.sub(approxRem);
    }
    return res;
};
__lp.div = __lp.divide;
__lp.modulo = function(divisor) {return this.sub(this.div(divisor).mul(divisor));};
__lp.mod = __lp.modulo;
__lp.not = function not() {return new Long(~this.low, ~this.high, this.unsigned);};
__lp.and = function(other) {return new Long(this.low & other.low, this.high & other.high, this.unsigned);};
__lp.or = function(other) {return new Long(this.low | other.low, this.high | other.high, this.unsigned);};
__lp.xor = function(other) {return new Long(this.low ^ other.low, this.high ^ other.high, this.unsigned);};

__lp.shl = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long(this.low << numBits, (this.high << numBits) | (this.low >>> (32 - numBits)), this.unsigned);
    else
        return new Long(0, this.low << (numBits - 32), this.unsigned);
};

__lp.shr = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long((this.low >>> numBits) | (this.high << (32 - numBits)), this.high >> numBits, this.unsigned);
    else
        return new Long(this.high >> (numBits - 32), this.high >= 0 ? 0 : -1, this.unsigned);
};

__lp.shru = function(numBits) {
    numBits &= 63;
    if (numBits === 0)
        return this;
    else {
        var high = this.high;
        if (numBits < 32) {
            var low = this.low;
            return new Long((low >>> numBits) | (high << (32 - numBits)), high >>> numBits, this.unsigned);
        } else if (numBits === 32)
            return new Long(high, 0, this.unsigned);
        else
            return new Long(high >>> (numBits - 32), 0, this.unsigned);
    }
};

__lp.toSigned = function() {return this.unsigned ? new Long(this.low, this.high, false) : this;};
__lp.toUnsigned = function() {return this.unsigned ? this : new Long(this.low, this.high, true);};

// Int64
function hs_eqInt64(x, y) {return x.eq(y);}
function hs_neInt64(x, y) {return x.neq(y);}
function hs_ltInt64(x, y) {return x.lt(y);}
function hs_leInt64(x, y) {return x.lte(y);}
function hs_gtInt64(x, y) {return x.gt(y);}
function hs_geInt64(x, y) {return x.gte(y);}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {return x.shl(bits);}
function hs_uncheckedIShiftRA64(x, bits) {return x.shr(bits);}
function hs_uncheckedIShiftRL64(x, bits) {return x.shru(bits);}
function hs_int64ToInt(x) {return x.toInt();}
var hs_intToInt64 = __fromInt;

// Word64
function hs_wordToWord64(x) {return __fromInt(x, true);}
function hs_word64ToWord(x) {return x.toInt(x);}
function hs_mkWord64(low, high) {return new Long(low,high,true);}
function hs_and64(a,b) {return a.and(b);};
function hs_or64(a,b) {return a.or(b);};
function hs_xor64(a,b) {return a.xor(b);};
function hs_not64(x) {return x.not();}
var hs_eqWord64 = hs_eqInt64;
var hs_neWord64 = hs_neInt64;
var hs_ltWord64 = hs_ltInt64;
var hs_leWord64 = hs_leInt64;
var hs_gtWord64 = hs_gtInt64;
var hs_geWord64 = hs_geInt64;
var hs_quotWord64 = hs_quotInt64;
var hs_remWord64 = hs_remInt64;
var hs_uncheckedShiftL64 = hs_uncheckedIShiftL64;
var hs_uncheckedShiftRL64 = hs_uncheckedIShiftRL64;
function hs_int64ToWord64(x) {return x.toUnsigned();}
function hs_word64ToInt64(x) {return x.toSigned();}

// Joseph Myers' MD5 implementation, ported to work on typed arrays.
// Used under the BSD license.
function md5cycle(x, k) {
    var a = x[0], b = x[1], c = x[2], d = x[3];

    a = ff(a, b, c, d, k[0], 7, -680876936);
    d = ff(d, a, b, c, k[1], 12, -389564586);
    c = ff(c, d, a, b, k[2], 17,  606105819);
    b = ff(b, c, d, a, k[3], 22, -1044525330);
    a = ff(a, b, c, d, k[4], 7, -176418897);
    d = ff(d, a, b, c, k[5], 12,  1200080426);
    c = ff(c, d, a, b, k[6], 17, -1473231341);
    b = ff(b, c, d, a, k[7], 22, -45705983);
    a = ff(a, b, c, d, k[8], 7,  1770035416);
    d = ff(d, a, b, c, k[9], 12, -1958414417);
    c = ff(c, d, a, b, k[10], 17, -42063);
    b = ff(b, c, d, a, k[11], 22, -1990404162);
    a = ff(a, b, c, d, k[12], 7,  1804603682);
    d = ff(d, a, b, c, k[13], 12, -40341101);
    c = ff(c, d, a, b, k[14], 17, -1502002290);
    b = ff(b, c, d, a, k[15], 22,  1236535329);

    a = gg(a, b, c, d, k[1], 5, -165796510);
    d = gg(d, a, b, c, k[6], 9, -1069501632);
    c = gg(c, d, a, b, k[11], 14,  643717713);
    b = gg(b, c, d, a, k[0], 20, -373897302);
    a = gg(a, b, c, d, k[5], 5, -701558691);
    d = gg(d, a, b, c, k[10], 9,  38016083);
    c = gg(c, d, a, b, k[15], 14, -660478335);
    b = gg(b, c, d, a, k[4], 20, -405537848);
    a = gg(a, b, c, d, k[9], 5,  568446438);
    d = gg(d, a, b, c, k[14], 9, -1019803690);
    c = gg(c, d, a, b, k[3], 14, -187363961);
    b = gg(b, c, d, a, k[8], 20,  1163531501);
    a = gg(a, b, c, d, k[13], 5, -1444681467);
    d = gg(d, a, b, c, k[2], 9, -51403784);
    c = gg(c, d, a, b, k[7], 14,  1735328473);
    b = gg(b, c, d, a, k[12], 20, -1926607734);

    a = hh(a, b, c, d, k[5], 4, -378558);
    d = hh(d, a, b, c, k[8], 11, -2022574463);
    c = hh(c, d, a, b, k[11], 16,  1839030562);
    b = hh(b, c, d, a, k[14], 23, -35309556);
    a = hh(a, b, c, d, k[1], 4, -1530992060);
    d = hh(d, a, b, c, k[4], 11,  1272893353);
    c = hh(c, d, a, b, k[7], 16, -155497632);
    b = hh(b, c, d, a, k[10], 23, -1094730640);
    a = hh(a, b, c, d, k[13], 4,  681279174);
    d = hh(d, a, b, c, k[0], 11, -358537222);
    c = hh(c, d, a, b, k[3], 16, -722521979);
    b = hh(b, c, d, a, k[6], 23,  76029189);
    a = hh(a, b, c, d, k[9], 4, -640364487);
    d = hh(d, a, b, c, k[12], 11, -421815835);
    c = hh(c, d, a, b, k[15], 16,  530742520);
    b = hh(b, c, d, a, k[2], 23, -995338651);

    a = ii(a, b, c, d, k[0], 6, -198630844);
    d = ii(d, a, b, c, k[7], 10,  1126891415);
    c = ii(c, d, a, b, k[14], 15, -1416354905);
    b = ii(b, c, d, a, k[5], 21, -57434055);
    a = ii(a, b, c, d, k[12], 6,  1700485571);
    d = ii(d, a, b, c, k[3], 10, -1894986606);
    c = ii(c, d, a, b, k[10], 15, -1051523);
    b = ii(b, c, d, a, k[1], 21, -2054922799);
    a = ii(a, b, c, d, k[8], 6,  1873313359);
    d = ii(d, a, b, c, k[15], 10, -30611744);
    c = ii(c, d, a, b, k[6], 15, -1560198380);
    b = ii(b, c, d, a, k[13], 21,  1309151649);
    a = ii(a, b, c, d, k[4], 6, -145523070);
    d = ii(d, a, b, c, k[11], 10, -1120210379);
    c = ii(c, d, a, b, k[2], 15,  718787259);
    b = ii(b, c, d, a, k[9], 21, -343485551);

    x[0] = add32(a, x[0]);
    x[1] = add32(b, x[1]);
    x[2] = add32(c, x[2]);
    x[3] = add32(d, x[3]);

}

function cmn(q, a, b, x, s, t) {
    a = add32(add32(a, q), add32(x, t));
    return add32((a << s) | (a >>> (32 - s)), b);
}

function ff(a, b, c, d, x, s, t) {
    return cmn((b & c) | ((~b) & d), a, b, x, s, t);
}

function gg(a, b, c, d, x, s, t) {
    return cmn((b & d) | (c & (~d)), a, b, x, s, t);
}

function hh(a, b, c, d, x, s, t) {
    return cmn(b ^ c ^ d, a, b, x, s, t);
}

function ii(a, b, c, d, x, s, t) {
    return cmn(c ^ (b | (~d)), a, b, x, s, t);
}

function md51(s, n) {
    var a = s['v']['w8'];
    var orig_n = n,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=n; i+=64) {
        md5cycle(state, md5blk(a.subarray(i-64, i)));
    }
    a = a.subarray(i-64);
    n = n < (i-64) ? 0 : n-(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<n; i++)
        tail[i>>2] |= a[i] << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = orig_n*8;
    md5cycle(state, tail);
    return state;
}
window['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s[i]
            + (s[i+1] << 8)
            + (s[i+2] << 16)
            + (s[i+3] << 24);
    }
    return md5blks;
}

var hex_chr = '0123456789abcdef'.split('');

function rhex(n)
{
    var s='', j=0;
    for(; j<4; j++)
        s += hex_chr[(n >> (j * 8 + 4)) & 0x0F]
        + hex_chr[(n >> (j * 8)) & 0x0F];
    return s;
}

function hex(x) {
    for (var i=0; i<x.length; i++)
        x[i] = rhex(x[i]);
    return x.join('');
}

function md5(s, n) {
    return hex(md51(s, n));
}

window['md5'] = md5;

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

function __hsbase_MD5Init(ctx) {}
// Note that this is a one time "update", since that's all that's used by
// GHC.Fingerprint.
function __hsbase_MD5Update(ctx, s, n) {
    ctx.md5 = md51(s, n);
}
function __hsbase_MD5Final(out, ctx) {
    var a = out['v']['i32'];
    a[0] = ctx.md5[0];
    a[1] = ctx.md5[1];
    a[2] = ctx.md5[2];
    a[3] = ctx.md5[3];
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = new Array(n);
    for(var i = 0; i < n; ++i) {
        arr[i] = x;
    }
    return arr;
}

// Create all views at once; perhaps it's wasteful, but it's better than having
// to check for the right view at each read or write.
function newByteArr(n) {
    // Pad the thing to multiples of 8.
    var padding = 8 - n % 8;
    if(padding < 8) {
        n += padding;
    }
    return new ByteArray(new ArrayBuffer(n));
}

// Wrap a JS ArrayBuffer into a ByteArray. Truncates the array length to the
// closest multiple of 8 bytes.
function wrapByteArr(buffer) {
    var diff = buffer.byteLength % 8;
    if(diff != 0) {
        var buffer = buffer.slice(0, buffer.byteLength-diff);
    }
    return new ByteArray(buffer);
}

function ByteArray(buffer) {
    var views =
        { 'i8' : new Int8Array(buffer)
        , 'i16': new Int16Array(buffer)
        , 'i32': new Int32Array(buffer)
        , 'w8' : new Uint8Array(buffer)
        , 'w16': new Uint16Array(buffer)
        , 'w32': new Uint32Array(buffer)
        , 'f32': new Float32Array(buffer)
        , 'f64': new Float64Array(buffer)
        };
    this['b'] = buffer;
    this['v'] = views;
    this['off'] = 0;
}
window['newArr'] = newArr;
window['newByteArr'] = newByteArr;
window['wrapByteArr'] = wrapByteArr;
window['ByteArray'] = ByteArray;

// An attempt at emulating pointers enough for ByteString and Text to be
// usable without patching the hell out of them.
// The general idea is that Addr# is a byte array with an associated offset.

function plusAddr(addr, off) {
    var newaddr = {};
    newaddr['off'] = addr['off'] + off;
    newaddr['b']   = addr['b'];
    newaddr['v']   = addr['v'];
    return newaddr;
}

function writeOffAddr(type, elemsize, addr, off, x) {
    addr['v'][type][addr.off/elemsize + off] = x;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

// Two addresses are equal if they point to the same buffer and have the same
// offset. For other comparisons, just use the offsets - nobody in their right
// mind would check if one pointer is less than another, completely unrelated,
// pointer and then act on that information anyway.
function addrEq(a, b) {
    if(a == b) {
        return true;
    }
    return a && b && a['b'] == b['b'] && a['off'] == b['off'];
}

function addrLT(a, b) {
    if(a) {
        return b && a['off'] < b['off'];
    } else {
        return (b != 0); 
    }
}

function addrGT(a, b) {
    if(b) {
        return a && a['off'] > b['off'];
    } else {
        return (a != 0);
    }
}

function withChar(f, charCode) {
    return f(String.fromCharCode(charCode)).charCodeAt(0);
}

function u_towlower(charCode) {
    return withChar(function(c) {return c.toLowerCase()}, charCode);
}

function u_towupper(charCode) {
    return withChar(function(c) {return c.toUpperCase()}, charCode);
}

var u_towtitle = u_towupper;

function u_iswupper(charCode) {
    var c = String.fromCharCode(charCode);
    return c == c.toUpperCase() && c != c.toLowerCase();
}

function u_iswlower(charCode) {
    var c = String.fromCharCode(charCode);
    return  c == c.toLowerCase() && c != c.toUpperCase();
}

function u_iswdigit(charCode) {
    return charCode >= 48 && charCode <= 57;
}

function u_iswcntrl(charCode) {
    return charCode <= 0x1f || charCode == 0x7f;
}

function u_iswspace(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(/\s/g,'') != c;
}

function u_iswalpha(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(__hs_alphare, '') != c;
}

function u_iswalnum(charCode) {
    return u_iswdigit(charCode) || u_iswalpha(charCode);
}

function u_iswprint(charCode) {
    return !u_iswcntrl(charCode);
}

function u_gencat(c) {
    throw 'u_gencat is only supported with --full-unicode.';
}

// Regex that matches any alphabetic character in any language. Horrible thing.
var __hs_alphare = /[\u0041-\u005A\u0061-\u007A\u00AA\u00B5\u00BA\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u0527\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0\u08A2-\u08AC\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0977\u0979-\u097F\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C33\u0C35-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191C\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2119-\u211D\u2124\u2126\u2128\u212A-\u212D\u212F-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2183\u2184\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2E2F\u3005\u3006\u3031-\u3035\u303B\u303C\u3041-\u3096\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA697\uA6A0-\uA6E5\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA793\uA7A0-\uA7AA\uA7F8-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA80-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]/g;

// Simulate handles.
// When implementing new handles, remember that passed strings may be thunks,
// and so need to be evaluated before use.

function jsNewHandle(init, read, write, flush, close, seek, tell) {
    var h = {
        read: read || function() {},
        write: write || function() {},
        seek: seek || function() {},
        tell: tell || function() {},
        close: close || function() {},
        flush: flush || function() {}
    };
    init.call(h);
    return h;
}

function jsReadHandle(h, len) {return h.read(len);}
function jsWriteHandle(h, str) {return h.write(str);}
function jsFlushHandle(h) {return h.flush();}
function jsCloseHandle(h) {return h.close();}

function jsMkConWriter(op) {
    return function(str) {
        str = E(str);
        var lines = (this.buf + str).split('\n');
        for(var i = 0; i < lines.length-1; ++i) {
            op.call(console, lines[i]);
        }
        this.buf = lines[lines.length-1];
    }
}

function jsMkStdout() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.log),
        function() {console.log(this.buf); this.buf = '';}
    );
}

function jsMkStderr() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.warn),
        function() {console.warn(this.buf); this.buf = '';}
    );
}

function jsMkStdin() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(len) {
            while(this.buf.length < len) {
                this.buf += prompt('[stdin]') + '\n';
            }
            var ret = this.buf.substr(0, len);
            this.buf = this.buf.substr(len);
            return ret;
        }
    );
}

// "Weak Pointers". Mostly useless implementation since
// JS does its own GC.

function mkWeak(key, val, fin) {
    fin = !fin? function() {}: fin;
    return {key: key, val: val, fin: fin};
}

function derefWeak(w) {
    return {_:0, a:1, b:E(w).val};
}

function finalizeWeak(w) {
    return {_:0, a:B(A1(E(w).fin, __Z))};
}

/* For foreign import ccall "wrapper" */
function createAdjustor(args, f, a, b) {
    return function(){
        var x = f.apply(null, arguments);
        while(x instanceof F) {x = x.f();}
        return x;
    };
}

var __apply = function(f,as) {
    var arr = [];
    for(; as._ === 1; as = as.b) {
        arr.push(as.a);
    }
    arr.reverse();
    return f.apply(null, arr);
}
var __app0 = function(f) {return f();}
var __app1 = function(f,a) {return f(a);}
var __app2 = function(f,a,b) {return f(a,b);}
var __app3 = function(f,a,b,c) {return f(a,b,c);}
var __app4 = function(f,a,b,c,d) {return f(a,b,c,d);}
var __app5 = function(f,a,b,c,d,e) {return f(a,b,c,d,e);}
var __jsNull = function() {return null;}
var __eq = function(a,b) {return a===b;}
var __createJSFunc = function(arity, f){
    if(f instanceof Function && arity === f.length) {
        return (function() {
            var x = f.apply(null,arguments);
            if(x instanceof T) {
                if(x.f !== __blackhole) {
                    var ff = x.f;
                    x.f = __blackhole;
                    return x.x = ff();
                }
                return x.x;
            } else {
                while(x instanceof F) {
                    x = x.f();
                }
                return E(x);
            }
        });
    } else {
        return (function(){
            var as = Array.prototype.slice.call(arguments);
            as.push(0);
            return E(B(A(f,as)));
        });
    }
}


function __arr2lst(elem,arr) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1,
            a:arr[elem],
            b:new T(function(){return __arr2lst(elem+1,arr);})};
}

function __lst2arr(xs) {
    var arr = [];
    xs = E(xs);
    for(;xs._ === 1; xs = E(xs.b)) {
        arr.push(E(xs.a));
    }
    return arr;
}

var __new = function() {return ({});}
var __set = function(o,k,v) {o[k]=v;}
var __get = function(o,k) {return o[k];}
var __has = function(o,k) {return o[k]!==undefined;}

var _0=function(_1,_2,_){var _3=B(A1(_1,_)),_4=B(A1(_2,_));return new T(function(){return B(A1(_3,_4));});},_5=function(_6,_7,_){var _8=B(A1(_7,_));return new T(function(){return B(A1(_6,_8));});},_9=function(_a,_){return _a;},_b=function(_c,_d,_){var _e=B(A1(_c,_));return C > 19 ? new F(function(){return A1(_d,_);}) : (++C,A1(_d,_));},_f=new T(function(){return unCStr("base");}),_g=new T(function(){return unCStr("GHC.IO.Exception");}),_h=new T(function(){return unCStr("IOException");}),_i=function(_j){return E(new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_f,_g,_h),__Z,__Z));},_k=function(_l){return E(E(_l).a);},_m=function(_n,_o,_p){var _q=B(A1(_n,_)),_r=B(A1(_o,_)),_s=hs_eqWord64(_q.a,_r.a);if(!_s){return __Z;}else{var _t=hs_eqWord64(_q.b,_r.b);return (!_t)?__Z:new T1(1,_p);}},_u=new T(function(){return unCStr(": ");}),_v=new T(function(){return unCStr(")");}),_w=new T(function(){return unCStr(" (");}),_x=function(_y,_z){var _A=E(_y);return (_A._==0)?E(_z):new T2(1,_A.a,new T(function(){return _x(_A.b,_z);}));},_B=new T(function(){return unCStr("interrupted");}),_C=new T(function(){return unCStr("system error");}),_D=new T(function(){return unCStr("unsatisified constraints");}),_E=new T(function(){return unCStr("user error");}),_F=new T(function(){return unCStr("permission denied");}),_G=new T(function(){return unCStr("illegal operation");}),_H=new T(function(){return unCStr("end of file");}),_I=new T(function(){return unCStr("resource exhausted");}),_J=new T(function(){return unCStr("resource busy");}),_K=new T(function(){return unCStr("does not exist");}),_L=new T(function(){return unCStr("already exists");}),_M=new T(function(){return unCStr("resource vanished");}),_N=new T(function(){return unCStr("timeout");}),_O=new T(function(){return unCStr("unsupported operation");}),_P=new T(function(){return unCStr("hardware fault");}),_Q=new T(function(){return unCStr("inappropriate type");}),_R=new T(function(){return unCStr("invalid argument");}),_S=new T(function(){return unCStr("failed");}),_T=new T(function(){return unCStr("protocol error");}),_U=function(_V,_W){switch(E(_V)){case 0:return _x(_L,_W);case 1:return _x(_K,_W);case 2:return _x(_J,_W);case 3:return _x(_I,_W);case 4:return _x(_H,_W);case 5:return _x(_G,_W);case 6:return _x(_F,_W);case 7:return _x(_E,_W);case 8:return _x(_D,_W);case 9:return _x(_C,_W);case 10:return _x(_T,_W);case 11:return _x(_S,_W);case 12:return _x(_R,_W);case 13:return _x(_Q,_W);case 14:return _x(_P,_W);case 15:return _x(_O,_W);case 16:return _x(_N,_W);case 17:return _x(_M,_W);default:return _x(_B,_W);}},_X=new T(function(){return unCStr("}");}),_Y=new T(function(){return unCStr("{handle: ");}),_Z=function(_10,_11,_12,_13,_14,_15){var _16=new T(function(){var _17=new T(function(){var _18=new T(function(){var _19=E(_13);if(!_19._){return E(_15);}else{var _1a=new T(function(){return _x(_19,new T(function(){return _x(_v,_15);},1));},1);return _x(_w,_1a);}},1);return _U(_11,_18);}),_1b=E(_12);if(!_1b._){return E(_17);}else{return _x(_1b,new T(function(){return _x(_u,_17);},1));}}),_1c=E(_14);if(!_1c._){var _1d=E(_10);if(!_1d._){return E(_16);}else{var _1e=E(_1d.a);if(!_1e._){var _1f=new T(function(){var _1g=new T(function(){return _x(_X,new T(function(){return _x(_u,_16);},1));},1);return _x(_1e.a,_1g);},1);return _x(_Y,_1f);}else{var _1h=new T(function(){var _1i=new T(function(){return _x(_X,new T(function(){return _x(_u,_16);},1));},1);return _x(_1e.a,_1i);},1);return _x(_Y,_1h);}}}else{return _x(_1c.a,new T(function(){return _x(_u,_16);},1));}},_1j=function(_1k){var _1l=E(_1k);return _Z(_1l.a,_1l.b,_1l.c,_1l.d,_1l.f,__Z);},_1m=function(_1n,_1o){var _1p=E(_1n);return _Z(_1p.a,_1p.b,_1p.c,_1p.d,_1p.f,_1o);},_1q=function(_1r,_1s,_1t){var _1u=E(_1s);if(!_1u._){return unAppCStr("[]",_1t);}else{var _1v=new T(function(){var _1w=new T(function(){var _1x=function(_1y){var _1z=E(_1y);if(!_1z._){return E(new T2(1,93,_1t));}else{var _1A=new T(function(){return B(A2(_1r,_1z.a,new T(function(){return _1x(_1z.b);})));});return new T2(1,44,_1A);}};return _1x(_1u.b);});return B(A2(_1r,_1u.a,_1w));});return new T2(1,91,_1v);}},_1B=new T(function(){return new T5(0,_i,new T3(0,function(_1C,_1D,_1E){var _1F=E(_1D);return _Z(_1F.a,_1F.b,_1F.c,_1F.d,_1F.f,_1E);},_1j,function(_1G,_1H){return _1q(_1m,_1G,_1H);}),function(_1I){return new T2(0,_1B,_1I);},function(_1J){var _1K=E(_1J);return _m(_k(_1K.a),_i,_1K.b);},_1j);}),_1L=new T(function(){return E(_1B);}),_1M=function(_1N){return E(E(_1N).c);},_1O=function(_1P){return new T6(0,__Z,7,__Z,_1P,__Z,__Z);},_1Q=function(_1R,_){var _1S=new T(function(){return B(A2(_1M,_1L,new T(function(){return B(A1(_1O,_1R));})));});return die(_1S);},_1T=function(_1U,_){return _1Q(_1U,_);},_1V=function(_1W){return E(_1W);},_1X=new T2(0,new T5(0,new T5(0,new T2(0,_5,function(_1Y,_1Z,_){var _20=B(A1(_1Z,_));return _1Y;}),_9,_0,_b,function(_21,_22,_){var _23=B(A1(_21,_)),_24=B(A1(_22,_));return _23;}),function(_25,_26,_){var _27=B(A1(_25,_));return C > 19 ? new F(function(){return A2(_26,_27,_);}) : (++C,A2(_26,_27,_));},_b,_9,function(_28){return C > 19 ? new F(function(){return A1(_1T,_28);}) : (++C,A1(_1T,_28));}),_1V),_29=function(_){return 0;},_2a=new T2(0,function(_2b){switch(E(_2b)){case 0:return "load";case 1:return "unload";case 2:return "change";case 3:return "focus";case 4:return "blur";case 5:return "submit";default:return "scroll";}},function(_2c,_2d,_){return _29(_);}),_2e=function(_2f,_){var _2g=_2f["keyCode"],_2h=_2f["ctrlKey"],_2i=_2f["altKey"],_2j=_2f["shiftKey"],_2k=_2f["metaKey"];return new T(function(){var _2l=Number(_2g),_2m=jsTrunc(_2l);return new T5(0,_2m,E(_2h),E(_2i),E(_2j),E(_2k));});},_2n=new T2(0,function(_2o){switch(E(_2o)){case 0:return "keypress";case 1:return "keyup";default:return "keydown";}},function(_2p,_2q,_){return _2e(E(_2q),_);}),_2r=function(_){return 0;},_2s=new T2(0,_1V,function(_2t,_){return new T1(1,_2t);}),_2u=new T2(0,_1X,_9),_2v=(function(e,p){var x = e[p];return typeof x === 'undefined' ? '' : x.toString();}),_2w=function(_2x,_2y){while(1){var _2z=E(_2x);if(!_2z._){return E(_2y);}else{var _2A=new T2(1,_2z.a,_2y);_2x=_2z.b;_2y=_2A;continue;}}},_2B=function(_2C){return _2w(_2C,__Z);},_2D=function(_2E,_2F,_2G){while(1){var _2H=(function(_2I,_2J,_2K){var _2L=E(_2I);if(!_2L._){return new T2(0,new T(function(){return _2B(_2J);}),new T(function(){return _2B(_2K);}));}else{var _2M=_2J,_2N=new T2(1,_2L.a,_2K);_2E=_2L.b;_2F=_2M;_2G=_2N;return __continue;}})(_2E,_2F,_2G);if(_2H!=__continue){return _2H;}}},_2O=function(_2P,_2Q,_2R){while(1){var _2S=(function(_2T,_2U,_2V){var _2W=E(_2T);if(!_2W._){return new T2(0,new T(function(){return _2B(_2U);}),new T(function(){return _2B(_2V);}));}else{var _2X=_2W.b,_2Y=E(_2W.a);if(_2Y==46){return _2D(_2X,_2U,__Z);}else{var _2Z=new T2(1,_2Y,_2U),_30=_2V;_2P=_2X;_2Q=_2Z;_2R=_30;return __continue;}}})(_2P,_2Q,_2R);if(_2S!=__continue){return _2S;}}},_31=function(_32,_33){var _34=E(_33);if(!_34._){return __Z;}else{var _35=_34.a,_36=E(_32);return (_36==1)?new T2(1,_35,__Z):new T2(1,_35,new T(function(){return _31(_36-1|0,_34.b);}));}},_37=function(_38){var _39=I_decodeDouble(_38);return new T2(0,new T1(1,_39.b),_39.a);},_3a=function(_3b){var _3c=E(_3b);if(!_3c._){return _3c.a;}else{return I_toNumber(_3c.a);}},_3d=function(_3e){return new T1(0,_3e);},_3f=function(_3g){var _3h=hs_intToInt64(2147483647),_3i=hs_leInt64(_3g,_3h);if(!_3i){return new T1(1,I_fromInt64(_3g));}else{var _3j=hs_intToInt64(-2147483648),_3k=hs_geInt64(_3g,_3j);if(!_3k){return new T1(1,I_fromInt64(_3g));}else{var _3l=hs_int64ToInt(_3g);return _3d(_3l);}}},_3m=function(_3n){var _3o=hs_intToInt64(_3n);return E(_3o);},_3p=function(_3q){var _3r=E(_3q);if(!_3r._){return _3m(_3r.a);}else{return I_toInt64(_3r.a);}},_3s=function(_3t,_3u){while(1){var _3v=E(_3t);if(!_3v._){_3t=new T1(1,I_fromInt(_3v.a));continue;}else{return new T1(1,I_shiftLeft(_3v.a,_3u));}}},_3w=function(_3x,_3y){var _3z=Math.pow(10,_3x),_3A=rintDouble(_3y*_3z),_3B=_37(_3A),_3C=_3B.a,_3D=_3B.b,_3E=function(_3F,_3G){var _3H=new T(function(){return unAppCStr(".",new T(function(){if(0>=_3x){return __Z;}else{return _31(_3x,_3G);}}));},1);return _x(_3F,_3H);};if(_3D>=0){var _3I=jsShow(_3a(_3s(_3C,_3D))/_3z),_3J=_2O(fromJSStr(_3I),__Z,__Z);return _3E(_3J.a,_3J.b);}else{var _3K=hs_uncheckedIShiftRA64(_3p(_3C), -_3D),_3L=jsShow(_3a(_3f(_3K))/_3z),_3M=_2O(fromJSStr(_3L),__Z,__Z);return _3E(_3M.a,_3M.b);}},_3N=new T(function(){return unCStr("<br>");}),_3O=function(_3P,_3Q){var _3R=new T(function(){return unAppCStr(": ",new T(function(){return _x(_3w(4,E(_3Q)),_3N);}));},1);return _x(_3P,_3R);},_3S=function(_3T){var _3U=E(_3T);if(!_3U._){return __Z;}else{var _3V=E(_3U.a);return _x(_3O(_3V.a,_3V.b),new T(function(){return _3S(_3U.b);},1));}},_3W=function(_3X){var _3Y=E(_3X);if(!_3Y._){return __Z;}else{var _3Z=E(_3Y.a);return _x(_3O(_3Z.a,_3Z.b),new T(function(){return _3W(_3Y.b);},1));}},_40=(function(e,p,v){e[p] = v;}),_41=new T(function(){return unCStr("base");}),_42=new T(function(){return unCStr("Control.Exception.Base");}),_43=new T(function(){return unCStr("PatternMatchFail");}),_44=function(_45){return E(new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_41,_42,_43),__Z,__Z));},_46=function(_47){return E(E(_47).a);},_48=function(_49,_4a){return _x(E(_49).a,_4a);},_4b=new T(function(){return new T5(0,_44,new T3(0,function(_4c,_4d,_4e){return _x(E(_4d).a,_4e);},_46,function(_4f,_4g){return _1q(_48,_4f,_4g);}),function(_4h){return new T2(0,_4b,_4h);},function(_4i){var _4j=E(_4i);return _m(_k(_4j.a),_44,_4j.b);},_46);}),_4k=new T(function(){return unCStr("Non-exhaustive patterns in");}),_4l=function(_4m,_4n){return die(new T(function(){return B(A2(_1M,_4n,_4m));}));},_4o=function(_4p,_4q){return _4l(_4p,_4q);},_4r=function(_4s,_4t){var _4u=E(_4t);if(!_4u._){return new T2(0,__Z,__Z);}else{var _4v=_4u.a;if(!B(A1(_4s,_4v))){return new T2(0,__Z,_4u);}else{var _4w=new T(function(){var _4x=_4r(_4s,_4u.b);return new T2(0,_4x.a,_4x.b);});return new T2(0,new T2(1,_4v,new T(function(){return E(E(_4w).a);})),new T(function(){return E(E(_4w).b);}));}}},_4y=new T(function(){return unCStr("\n");}),_4z=function(_4A){return (E(_4A)==124)?false:true;},_4B=function(_4C,_4D){var _4E=_4r(_4z,unCStr(_4C)),_4F=_4E.a,_4G=function(_4H,_4I){var _4J=new T(function(){var _4K=new T(function(){return _x(_4D,new T(function(){return _x(_4I,_4y);},1));});return unAppCStr(": ",_4K);},1);return _x(_4H,_4J);},_4L=E(_4E.b);if(!_4L._){return _4G(_4F,__Z);}else{if(E(_4L.a)==124){return _4G(_4F,new T2(1,32,_4L.b));}else{return _4G(_4F,__Z);}}},_4M=function(_4N){return _4o(new T1(0,new T(function(){return _4B(_4N,_4k);})),_4b);},_4O=new T(function(){return B((function(_4P){return C > 19 ? new F(function(){return _4M("calculator.hs:(13,1)-(30,39)|function calculator");}) : (++C,_4M("calculator.hs:(13,1)-(30,39)|function calculator"));})(_));}),_4Q=new T(function(){return unCStr("innerHTML");}),_4R=function(_4S){return E(E(_4S).a);},_4T=function(_4U){return E(E(_4U).a);},_4V=function(_4W){return E(E(_4W).b);},_4X=function(_4Y){return E(E(_4Y).a);},_4Z=function(_50){return E(E(_50).b);},_51=function(_52){return E(E(_52).a);},_53=function(_54){var _55=B(A1(_54,_));return E(_55);},_56=new T(function(){return _53(function(_){return nMV(__Z);});}),_57=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_58=new T(function(){return _53(function(_){return __jsNull();});}),_59=function(_5a){return E(E(_5a).b);},_5b=function(_5c){return E(E(_5c).b);},_5d=function(_5e){return E(E(_5e).d);},_5f=function(_5g,_5h,_5i,_5j,_5k,_5l){var _5m=_4R(_5g),_5n=_4T(_5m),_5o=new T(function(){return _59(_5m);}),_5p=new T(function(){return _5d(_5n);}),_5q=new T(function(){return B(A2(_4X,_5h,_5j));}),_5r=new T(function(){return B(A2(_51,_5i,_5k));}),_5s=function(_5t){return C > 19 ? new F(function(){return A1(_5p,new T3(0,_5r,_5q,_5t));}) : (++C,A1(_5p,new T3(0,_5r,_5q,_5t)));},_5u=function(_5v){var _5w=new T(function(){var _5x=new T(function(){var _5y=__createJSFunc(2,function(_5z,_){var _5A=B(A2(E(_5v),_5z,_));return _58;}),_5B=_5y;return function(_){return _57(E(_5q),E(_5r),_5B);};});return B(A1(_5o,_5x));});return C > 19 ? new F(function(){return A3(_4V,_5n,_5w,_5s);}) : (++C,A3(_4V,_5n,_5w,_5s));},_5C=new T(function(){var _5D=new T(function(){return _59(_5m);}),_5E=function(_5F){var _5G=new T(function(){return B(A1(_5D,function(_){var _=wMV(E(_56),new T1(1,_5F));return C > 19 ? new F(function(){return A(_4Z,[_5i,_5k,_5F,_]);}) : (++C,A(_4Z,[_5i,_5k,_5F,_]));}));});return C > 19 ? new F(function(){return A3(_4V,_5n,_5G,_5l);}) : (++C,A3(_4V,_5n,_5G,_5l));};return B(A2(_5b,_5g,_5E));});return C > 19 ? new F(function(){return A3(_4V,_5n,_5C,_5u);}) : (++C,A3(_4V,_5n,_5C,_5u));},_5H=new T(function(){return unCStr("CHF");}),_5I=function(_5J,_5K){var _5L=E(_5K);return (_5L._==0)?__Z:new T2(1,_5J,new T(function(){return _5I(_5L.a,_5L.b);}));},_5M=new T(function(){return unCStr(": empty list");}),_5N=new T(function(){return unCStr("Prelude.");}),_5O=function(_5P){return err(_x(_5N,new T(function(){return _x(_5P,_5M);},1)));},_5Q=new T(function(){return _5O(new T(function(){return unCStr("init");}));}),_5R=function(_5S){var _5T=E(_5S);if(!_5T._){return E(_5Q);}else{return _5I(_5T.a,_5T.b);}},_5U=new T(function(){return _5O(new T(function(){return unCStr("last");}));}),_5V=function(_5W){while(1){var _5X=(function(_5Y){var _5Z=E(_5Y);if(!_5Z._){return __Z;}else{var _60=_5Z.b,_61=E(_5Z.a);if(!E(_61.b)._){return new T2(1,_61.a,new T(function(){return _5V(_60);}));}else{_5W=_60;return __continue;}}})(_5W);if(_5X!=__continue){return _5X;}}},_62=function(_63,_64){while(1){var _65=(function(_66,_67){var _68=E(_66);switch(_68._){case 0:var _69=E(_67);if(!_69._){return __Z;}else{_63=B(A1(_68.a,_69.a));_64=_69.b;return __continue;}break;case 1:var _6a=B(A1(_68.a,_67)),_6b=_67;_63=_6a;_64=_6b;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_68.a,_67),new T(function(){return _62(_68.b,_67);}));default:return E(_68.a);}})(_63,_64);if(_65!=__continue){return _65;}}},_6c=new T(function(){return err(new T(function(){return unCStr("Prelude.read: ambiguous parse");}));}),_6d=new T(function(){return err(new T(function(){return unCStr("Prelude.read: no parse");}));}),_6e=new T(function(){return B(_4M("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_6f=function(_6g,_6h){var _6i=function(_6j){var _6k=E(_6h);if(_6k._==3){return new T2(3,_6k.a,new T(function(){return _6f(_6g,_6k.b);}));}else{var _6l=E(_6g);if(_6l._==2){return _6k;}else{if(_6k._==2){return _6l;}else{var _6m=function(_6n){if(_6k._==4){var _6o=function(_6p){return new T1(4,new T(function(){return _x(_62(_6l,_6p),_6k.a);}));};return new T1(1,_6o);}else{if(_6l._==1){var _6q=_6l.a;if(!_6k._){return new T1(1,function(_6r){return _6f(B(A1(_6q,_6r)),_6k);});}else{var _6s=function(_6t){return _6f(B(A1(_6q,_6t)),new T(function(){return B(A1(_6k.a,_6t));}));};return new T1(1,_6s);}}else{if(!_6k._){return E(_6e);}else{var _6u=function(_6v){return _6f(_6l,new T(function(){return B(A1(_6k.a,_6v));}));};return new T1(1,_6u);}}}};switch(_6l._){case 1:if(_6k._==4){var _6w=function(_6x){return new T1(4,new T(function(){return _x(_62(B(A1(_6l.a,_6x)),_6x),_6k.a);}));};return new T1(1,_6w);}else{return _6m(_);}break;case 4:var _6y=_6l.a;switch(_6k._){case 0:var _6z=function(_6A){var _6B=new T(function(){return _x(_6y,new T(function(){return _62(_6k,_6A);},1));});return new T1(4,_6B);};return new T1(1,_6z);case 1:var _6C=function(_6D){var _6E=new T(function(){return _x(_6y,new T(function(){return _62(B(A1(_6k.a,_6D)),_6D);},1));});return new T1(4,_6E);};return new T1(1,_6C);default:return new T1(4,new T(function(){return _x(_6y,_6k.a);}));}break;default:return _6m(_);}}}}},_6F=E(_6g);switch(_6F._){case 0:var _6G=E(_6h);if(!_6G._){var _6H=function(_6I){return _6f(B(A1(_6F.a,_6I)),new T(function(){return B(A1(_6G.a,_6I));}));};return new T1(0,_6H);}else{return _6i(_);}break;case 3:return new T2(3,_6F.a,new T(function(){return _6f(_6F.b,_6h);}));default:return _6i(_);}},_6J=new T(function(){return unCStr("(");}),_6K=new T(function(){return unCStr(")");}),_6L=function(_6M,_6N){while(1){var _6O=E(_6M);if(!_6O._){return (E(_6N)._==0)?true:false;}else{var _6P=E(_6N);if(!_6P._){return false;}else{if(E(_6O.a)!=E(_6P.a)){return false;}else{_6M=_6O.b;_6N=_6P.b;continue;}}}}},_6Q=new T2(0,function(_6R,_6S){return E(_6R)==E(_6S);},function(_6T,_6U){return E(_6T)!=E(_6U);}),_6V=function(_6W,_6X){while(1){var _6Y=E(_6W);if(!_6Y._){return (E(_6X)._==0)?true:false;}else{var _6Z=E(_6X);if(!_6Z._){return false;}else{if(E(_6Y.a)!=E(_6Z.a)){return false;}else{_6W=_6Y.b;_6X=_6Z.b;continue;}}}}},_70=function(_71,_72){return (!_6V(_71,_72))?true:false;},_73=function(_74,_75){var _76=E(_74);switch(_76._){case 0:return new T1(0,function(_77){return C > 19 ? new F(function(){return _73(B(A1(_76.a,_77)),_75);}) : (++C,_73(B(A1(_76.a,_77)),_75));});case 1:return new T1(1,function(_78){return C > 19 ? new F(function(){return _73(B(A1(_76.a,_78)),_75);}) : (++C,_73(B(A1(_76.a,_78)),_75));});case 2:return new T0(2);case 3:return _6f(B(A1(_75,_76.a)),new T(function(){return B(_73(_76.b,_75));}));default:var _79=function(_7a){var _7b=E(_7a);if(!_7b._){return __Z;}else{var _7c=E(_7b.a);return _x(_62(B(A1(_75,_7c.a)),_7c.b),new T(function(){return _79(_7b.b);},1));}},_7d=_79(_76.a);return (_7d._==0)?new T0(2):new T1(4,_7d);}},_7e=new T0(2),_7f=function(_7g){return new T2(3,_7g,_7e);},_7h=function(_7i,_7j){var _7k=E(_7i);if(!_7k){return C > 19 ? new F(function(){return A1(_7j,0);}) : (++C,A1(_7j,0));}else{var _7l=new T(function(){return B(_7h(_7k-1|0,_7j));});return new T1(0,function(_7m){return E(_7l);});}},_7n=function(_7o,_7p,_7q){var _7r=new T(function(){return B(A1(_7o,_7f));}),_7s=function(_7t,_7u,_7v,_7w){while(1){var _7x=B((function(_7y,_7z,_7A,_7B){var _7C=E(_7y);switch(_7C._){case 0:var _7D=E(_7z);if(!_7D._){return C > 19 ? new F(function(){return A1(_7p,_7B);}) : (++C,A1(_7p,_7B));}else{var _7E=_7A+1|0,_7F=_7B;_7t=B(A1(_7C.a,_7D.a));_7u=_7D.b;_7v=_7E;_7w=_7F;return __continue;}break;case 1:var _7G=B(A1(_7C.a,_7z)),_7H=_7z,_7E=_7A,_7F=_7B;_7t=_7G;_7u=_7H;_7v=_7E;_7w=_7F;return __continue;case 2:return C > 19 ? new F(function(){return A1(_7p,_7B);}) : (++C,A1(_7p,_7B));break;case 3:var _7I=new T(function(){return B(_73(_7C,_7B));});return C > 19 ? new F(function(){return _7h(_7A,function(_7J){return E(_7I);});}) : (++C,_7h(_7A,function(_7J){return E(_7I);}));break;default:return C > 19 ? new F(function(){return _73(_7C,_7B);}) : (++C,_73(_7C,_7B));}})(_7t,_7u,_7v,_7w));if(_7x!=__continue){return _7x;}}};return function(_7K){return _7s(_7r,_7K,0,_7q);};},_7L=function(_7M){return C > 19 ? new F(function(){return A1(_7M,__Z);}) : (++C,A1(_7M,__Z));},_7N=function(_7O,_7P){var _7Q=function(_7R){var _7S=E(_7R);if(!_7S._){return _7L;}else{var _7T=_7S.a;if(!B(A1(_7O,_7T))){return _7L;}else{var _7U=new T(function(){return _7Q(_7S.b);}),_7V=function(_7W){var _7X=new T(function(){return B(A1(_7U,function(_7Y){return C > 19 ? new F(function(){return A1(_7W,new T2(1,_7T,_7Y));}) : (++C,A1(_7W,new T2(1,_7T,_7Y)));}));});return new T1(0,function(_7Z){return E(_7X);});};return _7V;}}};return function(_80){return C > 19 ? new F(function(){return A2(_7Q,_80,_7P);}) : (++C,A2(_7Q,_80,_7P));};},_81=new T(function(){return err(new T(function(){return unCStr("valDig: Bad base");}));}),_82=function(_83,_84){var _85=function(_86,_87){var _88=E(_86);if(!_88._){var _89=new T(function(){return B(A1(_87,__Z));});return function(_8a){return C > 19 ? new F(function(){return A1(_8a,_89);}) : (++C,A1(_8a,_89));};}else{var _8b=E(_88.a),_8c=function(_8d){var _8e=new T(function(){return _85(_88.b,function(_8f){return C > 19 ? new F(function(){return A1(_87,new T2(1,_8d,_8f));}) : (++C,A1(_87,new T2(1,_8d,_8f)));});}),_8g=function(_8h){var _8i=new T(function(){return B(A1(_8e,_8h));});return new T1(0,function(_8j){return E(_8i);});};return _8g;};switch(E(_83)){case 8:if(48>_8b){var _8k=new T(function(){return B(A1(_87,__Z));});return function(_8l){return C > 19 ? new F(function(){return A1(_8l,_8k);}) : (++C,A1(_8l,_8k));};}else{if(_8b>55){var _8m=new T(function(){return B(A1(_87,__Z));});return function(_8n){return C > 19 ? new F(function(){return A1(_8n,_8m);}) : (++C,A1(_8n,_8m));};}else{return _8c(_8b-48|0);}}break;case 10:if(48>_8b){var _8o=new T(function(){return B(A1(_87,__Z));});return function(_8p){return C > 19 ? new F(function(){return A1(_8p,_8o);}) : (++C,A1(_8p,_8o));};}else{if(_8b>57){var _8q=new T(function(){return B(A1(_87,__Z));});return function(_8r){return C > 19 ? new F(function(){return A1(_8r,_8q);}) : (++C,A1(_8r,_8q));};}else{return _8c(_8b-48|0);}}break;case 16:if(48>_8b){if(97>_8b){if(65>_8b){var _8s=new T(function(){return B(A1(_87,__Z));});return function(_8t){return C > 19 ? new F(function(){return A1(_8t,_8s);}) : (++C,A1(_8t,_8s));};}else{if(_8b>70){var _8u=new T(function(){return B(A1(_87,__Z));});return function(_8v){return C > 19 ? new F(function(){return A1(_8v,_8u);}) : (++C,A1(_8v,_8u));};}else{return _8c((_8b-65|0)+10|0);}}}else{if(_8b>102){if(65>_8b){var _8w=new T(function(){return B(A1(_87,__Z));});return function(_8x){return C > 19 ? new F(function(){return A1(_8x,_8w);}) : (++C,A1(_8x,_8w));};}else{if(_8b>70){var _8y=new T(function(){return B(A1(_87,__Z));});return function(_8z){return C > 19 ? new F(function(){return A1(_8z,_8y);}) : (++C,A1(_8z,_8y));};}else{return _8c((_8b-65|0)+10|0);}}}else{return _8c((_8b-97|0)+10|0);}}}else{if(_8b>57){if(97>_8b){if(65>_8b){var _8A=new T(function(){return B(A1(_87,__Z));});return function(_8B){return C > 19 ? new F(function(){return A1(_8B,_8A);}) : (++C,A1(_8B,_8A));};}else{if(_8b>70){var _8C=new T(function(){return B(A1(_87,__Z));});return function(_8D){return C > 19 ? new F(function(){return A1(_8D,_8C);}) : (++C,A1(_8D,_8C));};}else{return _8c((_8b-65|0)+10|0);}}}else{if(_8b>102){if(65>_8b){var _8E=new T(function(){return B(A1(_87,__Z));});return function(_8F){return C > 19 ? new F(function(){return A1(_8F,_8E);}) : (++C,A1(_8F,_8E));};}else{if(_8b>70){var _8G=new T(function(){return B(A1(_87,__Z));});return function(_8H){return C > 19 ? new F(function(){return A1(_8H,_8G);}) : (++C,A1(_8H,_8G));};}else{return _8c((_8b-65|0)+10|0);}}}else{return _8c((_8b-97|0)+10|0);}}}else{return _8c(_8b-48|0);}}break;default:return E(_81);}}},_8I=function(_8J){var _8K=E(_8J);if(!_8K._){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_84,_8K);}) : (++C,A1(_84,_8K));}};return function(_8L){return C > 19 ? new F(function(){return A3(_85,_8L,_1V,_8I);}) : (++C,A3(_85,_8L,_1V,_8I));};},_8M=function(_8N){var _8O=function(_8P){return C > 19 ? new F(function(){return A1(_8N,new T1(5,new T2(0,8,_8P)));}) : (++C,A1(_8N,new T1(5,new T2(0,8,_8P))));},_8Q=function(_8R){return C > 19 ? new F(function(){return A1(_8N,new T1(5,new T2(0,16,_8R)));}) : (++C,A1(_8N,new T1(5,new T2(0,16,_8R))));},_8S=function(_8T){switch(E(_8T)){case 79:return new T1(1,_82(8,_8O));case 88:return new T1(1,_82(16,_8Q));case 111:return new T1(1,_82(8,_8O));case 120:return new T1(1,_82(16,_8Q));default:return new T0(2);}};return function(_8U){return (E(_8U)==48)?E(new T1(0,_8S)):new T0(2);};},_8V=function(_8W){return new T1(0,_8M(_8W));},_8X=function(_8Y){return C > 19 ? new F(function(){return A1(_8Y,__Z);}) : (++C,A1(_8Y,__Z));},_8Z=function(_90){return C > 19 ? new F(function(){return A1(_90,__Z);}) : (++C,A1(_90,__Z));},_91=new T1(0,1),_92=function(_93,_94){while(1){var _95=E(_93);if(!_95._){var _96=_95.a,_97=E(_94);if(!_97._){var _98=_97.a,_99=addC(_96,_98);if(!E(_99.b)){return new T1(0,_99.a);}else{_93=new T1(1,I_fromInt(_96));_94=new T1(1,I_fromInt(_98));continue;}}else{_93=new T1(1,I_fromInt(_96));_94=_97;continue;}}else{var _9a=E(_94);if(!_9a._){_93=_95;_94=new T1(1,I_fromInt(_9a.a));continue;}else{return new T1(1,I_add(_95.a,_9a.a));}}}},_9b=new T(function(){return _92(new T1(0,2147483647),_91);}),_9c=function(_9d){var _9e=E(_9d);if(!_9e._){var _9f=E(_9e.a);return (_9f==(-2147483648))?E(_9b):new T1(0, -_9f);}else{return new T1(1,I_negate(_9e.a));}},_9g=new T1(0,10),_9h=function(_9i,_9j){while(1){var _9k=E(_9i);if(!_9k._){return E(_9j);}else{var _9l=_9j+1|0;_9i=_9k.b;_9j=_9l;continue;}}},_9m=function(_9n,_9o){var _9p=E(_9o);return (_9p._==0)?__Z:new T2(1,new T(function(){return B(A1(_9n,_9p.a));}),new T(function(){return _9m(_9n,_9p.b);}));},_9q=function(_9r){return _3d(E(_9r));},_9s=new T(function(){return err(new T(function(){return unCStr("this should not happen");}));}),_9t=function(_9u,_9v){while(1){var _9w=E(_9u);if(!_9w._){var _9x=_9w.a,_9y=E(_9v);if(!_9y._){var _9z=_9y.a;if(!(imul(_9x,_9z)|0)){return new T1(0,imul(_9x,_9z)|0);}else{_9u=new T1(1,I_fromInt(_9x));_9v=new T1(1,I_fromInt(_9z));continue;}}else{_9u=new T1(1,I_fromInt(_9x));_9v=_9y;continue;}}else{var _9A=E(_9v);if(!_9A._){_9u=_9w;_9v=new T1(1,I_fromInt(_9A.a));continue;}else{return new T1(1,I_mul(_9w.a,_9A.a));}}}},_9B=function(_9C,_9D){var _9E=E(_9D);if(!_9E._){return __Z;}else{var _9F=E(_9E.b);return (_9F._==0)?E(_9s):new T2(1,_92(_9t(_9E.a,_9C),_9F.a),new T(function(){return _9B(_9C,_9F.b);}));}},_9G=new T1(0,0),_9H=function(_9I,_9J,_9K){while(1){var _9L=(function(_9M,_9N,_9O){var _9P=E(_9O);if(!_9P._){return E(_9G);}else{if(!E(_9P.b)._){return E(_9P.a);}else{var _9Q=E(_9N);if(_9Q<=40){var _9R=function(_9S,_9T){while(1){var _9U=E(_9T);if(!_9U._){return E(_9S);}else{var _9V=_92(_9t(_9S,_9M),_9U.a);_9S=_9V;_9T=_9U.b;continue;}}};return _9R(_9G,_9P);}else{var _9W=_9t(_9M,_9M);if(!(_9Q%2)){var _9X=_9B(_9M,_9P);_9I=_9W;_9J=quot(_9Q+1|0,2);_9K=_9X;return __continue;}else{var _9X=_9B(_9M,new T2(1,_9G,_9P));_9I=_9W;_9J=quot(_9Q+1|0,2);_9K=_9X;return __continue;}}}}})(_9I,_9J,_9K);if(_9L!=__continue){return _9L;}}},_9Y=function(_9Z,_a0){return _9H(_9Z,new T(function(){return _9h(_a0,0);},1),_9m(_9q,_a0));},_a1=function(_a2){var _a3=new T(function(){var _a4=new T(function(){var _a5=function(_a6){return C > 19 ? new F(function(){return A1(_a2,new T1(1,new T(function(){return _9Y(_9g,_a6);})));}) : (++C,A1(_a2,new T1(1,new T(function(){return _9Y(_9g,_a6);}))));};return new T1(1,_82(10,_a5));}),_a7=function(_a8){if(E(_a8)==43){var _a9=function(_aa){return C > 19 ? new F(function(){return A1(_a2,new T1(1,new T(function(){return _9Y(_9g,_aa);})));}) : (++C,A1(_a2,new T1(1,new T(function(){return _9Y(_9g,_aa);}))));};return new T1(1,_82(10,_a9));}else{return new T0(2);}},_ab=function(_ac){if(E(_ac)==45){var _ad=function(_ae){return C > 19 ? new F(function(){return A1(_a2,new T1(1,new T(function(){return _9c(_9Y(_9g,_ae));})));}) : (++C,A1(_a2,new T1(1,new T(function(){return _9c(_9Y(_9g,_ae));}))));};return new T1(1,_82(10,_ad));}else{return new T0(2);}};return _6f(_6f(new T1(0,_ab),new T1(0,_a7)),_a4);});return _6f(new T1(0,function(_af){return (E(_af)==101)?E(_a3):new T0(2);}),new T1(0,function(_ag){return (E(_ag)==69)?E(_a3):new T0(2);}));},_ah=function(_ai){var _aj=function(_ak){return C > 19 ? new F(function(){return A1(_ai,new T1(1,_ak));}) : (++C,A1(_ai,new T1(1,_ak)));};return function(_al){return (E(_al)==46)?new T1(1,_82(10,_aj)):new T0(2);};},_am=function(_an){return new T1(0,_ah(_an));},_ao=function(_ap){var _aq=function(_ar){var _as=function(_at){return new T1(1,_7n(_a1,_8X,function(_au){return C > 19 ? new F(function(){return A1(_ap,new T1(5,new T3(1,_ar,_at,_au)));}) : (++C,A1(_ap,new T1(5,new T3(1,_ar,_at,_au))));}));};return new T1(1,_7n(_am,_8Z,_as));};return _82(10,_aq);},_av=function(_aw){return new T1(1,_ao(_aw));},_ax=function(_ay){return E(E(_ay).a);},_az=function(_aA,_aB,_aC){while(1){var _aD=E(_aC);if(!_aD._){return false;}else{if(!B(A3(_ax,_aA,_aB,_aD.a))){_aC=_aD.b;continue;}else{return true;}}}},_aE=new T(function(){return unCStr("!@#$%&*+./<=>?\\^|:-~");}),_aF=function(_aG){return _az(_6Q,_aG,_aE);},_aH=function(_aI){var _aJ=new T(function(){return B(A1(_aI,8));}),_aK=new T(function(){return B(A1(_aI,16));});return function(_aL){switch(E(_aL)){case 79:return E(_aJ);case 88:return E(_aK);case 111:return E(_aJ);case 120:return E(_aK);default:return new T0(2);}};},_aM=function(_aN){return new T1(0,_aH(_aN));},_aO=function(_aP){return C > 19 ? new F(function(){return A1(_aP,10);}) : (++C,A1(_aP,10));},_aQ=function(_aR,_aS){var _aT=jsShowI(_aR);return _x(fromJSStr(_aT),_aS);},_aU=function(_aV,_aW,_aX){if(_aW>=0){return _aQ(_aW,_aX);}else{if(_aV<=6){return _aQ(_aW,_aX);}else{return new T2(1,40,new T(function(){var _aY=jsShowI(_aW);return _x(fromJSStr(_aY),new T2(1,41,_aX));}));}}},_aZ=function(_b0){return err(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return _aU(9,_b0,__Z);})));},_b1=function(_b2){var _b3=E(_b2);if(!_b3._){return E(_b3.a);}else{return I_toInt(_b3.a);}},_b4=function(_b5,_b6){var _b7=E(_b5);if(!_b7._){var _b8=_b7.a,_b9=E(_b6);return (_b9._==0)?_b8<=_b9.a:I_compareInt(_b9.a,_b8)>=0;}else{var _ba=_b7.a,_bb=E(_b6);return (_bb._==0)?I_compareInt(_ba,_bb.a)<=0:I_compare(_ba,_bb.a)<=0;}},_bc=function(_bd){return new T0(2);},_be=function(_bf){var _bg=E(_bf);if(!_bg._){return _bc;}else{var _bh=_bg.a,_bi=E(_bg.b);if(!_bi._){return E(_bh);}else{var _bj=new T(function(){return _be(_bi);}),_bk=function(_bl){return _6f(B(A1(_bh,_bl)),new T(function(){return B(A1(_bj,_bl));}));};return _bk;}}},_bm=function(_bn,_bo){var _bp=function(_bq,_br,_bs){var _bt=E(_bq);if(!_bt._){return C > 19 ? new F(function(){return A1(_bs,_bn);}) : (++C,A1(_bs,_bn));}else{var _bu=E(_br);if(!_bu._){return new T0(2);}else{if(E(_bt.a)!=E(_bu.a)){return new T0(2);}else{var _bv=new T(function(){return B(_bp(_bt.b,_bu.b,_bs));});return new T1(0,function(_bw){return E(_bv);});}}}};return function(_bx){return C > 19 ? new F(function(){return _bp(_bn,_bx,_bo);}) : (++C,_bp(_bn,_bx,_bo));};},_by=new T(function(){return unCStr("SO");}),_bz=function(_bA){var _bB=new T(function(){return B(A1(_bA,14));});return new T1(1,_bm(_by,function(_bC){return E(_bB);}));},_bD=new T(function(){return unCStr("SOH");}),_bE=function(_bF){var _bG=new T(function(){return B(A1(_bF,1));});return new T1(1,_bm(_bD,function(_bH){return E(_bG);}));},_bI=new T(function(){return unCStr("NUL");}),_bJ=function(_bK){var _bL=new T(function(){return B(A1(_bK,0));});return new T1(1,_bm(_bI,function(_bM){return E(_bL);}));},_bN=new T(function(){return unCStr("STX");}),_bO=function(_bP){var _bQ=new T(function(){return B(A1(_bP,2));});return new T1(1,_bm(_bN,function(_bR){return E(_bQ);}));},_bS=new T(function(){return unCStr("ETX");}),_bT=function(_bU){var _bV=new T(function(){return B(A1(_bU,3));});return new T1(1,_bm(_bS,function(_bW){return E(_bV);}));},_bX=new T(function(){return unCStr("EOT");}),_bY=function(_bZ){var _c0=new T(function(){return B(A1(_bZ,4));});return new T1(1,_bm(_bX,function(_c1){return E(_c0);}));},_c2=new T(function(){return unCStr("ENQ");}),_c3=function(_c4){var _c5=new T(function(){return B(A1(_c4,5));});return new T1(1,_bm(_c2,function(_c6){return E(_c5);}));},_c7=new T(function(){return unCStr("ACK");}),_c8=function(_c9){var _ca=new T(function(){return B(A1(_c9,6));});return new T1(1,_bm(_c7,function(_cb){return E(_ca);}));},_cc=new T(function(){return unCStr("BEL");}),_cd=function(_ce){var _cf=new T(function(){return B(A1(_ce,7));});return new T1(1,_bm(_cc,function(_cg){return E(_cf);}));},_ch=new T(function(){return unCStr("BS");}),_ci=function(_cj){var _ck=new T(function(){return B(A1(_cj,8));});return new T1(1,_bm(_ch,function(_cl){return E(_ck);}));},_cm=new T(function(){return unCStr("HT");}),_cn=function(_co){var _cp=new T(function(){return B(A1(_co,9));});return new T1(1,_bm(_cm,function(_cq){return E(_cp);}));},_cr=new T(function(){return unCStr("LF");}),_cs=function(_ct){var _cu=new T(function(){return B(A1(_ct,10));});return new T1(1,_bm(_cr,function(_cv){return E(_cu);}));},_cw=new T(function(){return unCStr("VT");}),_cx=function(_cy){var _cz=new T(function(){return B(A1(_cy,11));});return new T1(1,_bm(_cw,function(_cA){return E(_cz);}));},_cB=new T(function(){return unCStr("FF");}),_cC=function(_cD){var _cE=new T(function(){return B(A1(_cD,12));});return new T1(1,_bm(_cB,function(_cF){return E(_cE);}));},_cG=new T(function(){return unCStr("CR");}),_cH=function(_cI){var _cJ=new T(function(){return B(A1(_cI,13));});return new T1(1,_bm(_cG,function(_cK){return E(_cJ);}));},_cL=new T(function(){return unCStr("SI");}),_cM=function(_cN){var _cO=new T(function(){return B(A1(_cN,15));});return new T1(1,_bm(_cL,function(_cP){return E(_cO);}));},_cQ=new T(function(){return unCStr("DLE");}),_cR=function(_cS){var _cT=new T(function(){return B(A1(_cS,16));});return new T1(1,_bm(_cQ,function(_cU){return E(_cT);}));},_cV=new T(function(){return unCStr("DC1");}),_cW=function(_cX){var _cY=new T(function(){return B(A1(_cX,17));});return new T1(1,_bm(_cV,function(_cZ){return E(_cY);}));},_d0=new T(function(){return unCStr("DC2");}),_d1=function(_d2){var _d3=new T(function(){return B(A1(_d2,18));});return new T1(1,_bm(_d0,function(_d4){return E(_d3);}));},_d5=new T(function(){return unCStr("DC3");}),_d6=function(_d7){var _d8=new T(function(){return B(A1(_d7,19));});return new T1(1,_bm(_d5,function(_d9){return E(_d8);}));},_da=new T(function(){return unCStr("DC4");}),_db=function(_dc){var _dd=new T(function(){return B(A1(_dc,20));});return new T1(1,_bm(_da,function(_de){return E(_dd);}));},_df=new T(function(){return unCStr("NAK");}),_dg=function(_dh){var _di=new T(function(){return B(A1(_dh,21));});return new T1(1,_bm(_df,function(_dj){return E(_di);}));},_dk=new T(function(){return unCStr("SYN");}),_dl=function(_dm){var _dn=new T(function(){return B(A1(_dm,22));});return new T1(1,_bm(_dk,function(_do){return E(_dn);}));},_dp=new T(function(){return unCStr("ETB");}),_dq=function(_dr){var _ds=new T(function(){return B(A1(_dr,23));});return new T1(1,_bm(_dp,function(_dt){return E(_ds);}));},_du=new T(function(){return unCStr("CAN");}),_dv=function(_dw){var _dx=new T(function(){return B(A1(_dw,24));});return new T1(1,_bm(_du,function(_dy){return E(_dx);}));},_dz=new T(function(){return unCStr("EM");}),_dA=function(_dB){var _dC=new T(function(){return B(A1(_dB,25));});return new T1(1,_bm(_dz,function(_dD){return E(_dC);}));},_dE=new T(function(){return unCStr("SUB");}),_dF=function(_dG){var _dH=new T(function(){return B(A1(_dG,26));});return new T1(1,_bm(_dE,function(_dI){return E(_dH);}));},_dJ=new T(function(){return unCStr("ESC");}),_dK=function(_dL){var _dM=new T(function(){return B(A1(_dL,27));});return new T1(1,_bm(_dJ,function(_dN){return E(_dM);}));},_dO=new T(function(){return unCStr("FS");}),_dP=function(_dQ){var _dR=new T(function(){return B(A1(_dQ,28));});return new T1(1,_bm(_dO,function(_dS){return E(_dR);}));},_dT=new T(function(){return unCStr("GS");}),_dU=function(_dV){var _dW=new T(function(){return B(A1(_dV,29));});return new T1(1,_bm(_dT,function(_dX){return E(_dW);}));},_dY=new T(function(){return unCStr("RS");}),_dZ=function(_e0){var _e1=new T(function(){return B(A1(_e0,30));});return new T1(1,_bm(_dY,function(_e2){return E(_e1);}));},_e3=new T(function(){return unCStr("US");}),_e4=function(_e5){var _e6=new T(function(){return B(A1(_e5,31));});return new T1(1,_bm(_e3,function(_e7){return E(_e6);}));},_e8=new T(function(){return unCStr("SP");}),_e9=function(_ea){var _eb=new T(function(){return B(A1(_ea,32));});return new T1(1,_bm(_e8,function(_ec){return E(_eb);}));},_ed=new T(function(){return unCStr("DEL");}),_ee=function(_ef){var _eg=new T(function(){return B(A1(_ef,127));});return new T1(1,_bm(_ed,function(_eh){return E(_eg);}));},_ei=new T(function(){return _be(new T2(1,function(_ej){return new T1(1,_7n(_bE,_bz,_ej));},new T2(1,_bJ,new T2(1,_bO,new T2(1,_bT,new T2(1,_bY,new T2(1,_c3,new T2(1,_c8,new T2(1,_cd,new T2(1,_ci,new T2(1,_cn,new T2(1,_cs,new T2(1,_cx,new T2(1,_cC,new T2(1,_cH,new T2(1,_cM,new T2(1,_cR,new T2(1,_cW,new T2(1,_d1,new T2(1,_d6,new T2(1,_db,new T2(1,_dg,new T2(1,_dl,new T2(1,_dq,new T2(1,_dv,new T2(1,_dA,new T2(1,_dF,new T2(1,_dK,new T2(1,_dP,new T2(1,_dU,new T2(1,_dZ,new T2(1,_e4,new T2(1,_e9,new T2(1,_ee,__Z))))))))))))))))))))))))))))))))));}),_ek=function(_el){var _em=new T(function(){return B(A1(_el,7));}),_en=new T(function(){return B(A1(_el,8));}),_eo=new T(function(){return B(A1(_el,9));}),_ep=new T(function(){return B(A1(_el,10));}),_eq=new T(function(){return B(A1(_el,11));}),_er=new T(function(){return B(A1(_el,12));}),_es=new T(function(){return B(A1(_el,13));}),_et=new T(function(){return B(A1(_el,92));}),_eu=new T(function(){return B(A1(_el,39));}),_ev=new T(function(){return B(A1(_el,34));}),_ew=new T(function(){var _ex=function(_ey){var _ez=new T(function(){return _3d(E(_ey));}),_eA=function(_eB){var _eC=_9Y(_ez,_eB);if(!_b4(_eC,new T1(0,1114111))){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_el,new T(function(){var _eD=_b1(_eC);if(_eD>>>0>1114111){return _aZ(_eD);}else{return _eD;}}));}) : (++C,A1(_el,new T(function(){var _eD=_b1(_eC);if(_eD>>>0>1114111){return _aZ(_eD);}else{return _eD;}})));}};return new T1(1,_82(_ey,_eA));},_eE=new T(function(){var _eF=new T(function(){return B(A1(_el,31));}),_eG=new T(function(){return B(A1(_el,30));}),_eH=new T(function(){return B(A1(_el,29));}),_eI=new T(function(){return B(A1(_el,28));}),_eJ=new T(function(){return B(A1(_el,27));}),_eK=new T(function(){return B(A1(_el,26));}),_eL=new T(function(){return B(A1(_el,25));}),_eM=new T(function(){return B(A1(_el,24));}),_eN=new T(function(){return B(A1(_el,23));}),_eO=new T(function(){return B(A1(_el,22));}),_eP=new T(function(){return B(A1(_el,21));}),_eQ=new T(function(){return B(A1(_el,20));}),_eR=new T(function(){return B(A1(_el,19));}),_eS=new T(function(){return B(A1(_el,18));}),_eT=new T(function(){return B(A1(_el,17));}),_eU=new T(function(){return B(A1(_el,16));}),_eV=new T(function(){return B(A1(_el,15));}),_eW=new T(function(){return B(A1(_el,14));}),_eX=new T(function(){return B(A1(_el,6));}),_eY=new T(function(){return B(A1(_el,5));}),_eZ=new T(function(){return B(A1(_el,4));}),_f0=new T(function(){return B(A1(_el,3));}),_f1=new T(function(){return B(A1(_el,2));}),_f2=new T(function(){return B(A1(_el,1));}),_f3=new T(function(){return B(A1(_el,0));}),_f4=function(_f5){switch(E(_f5)){case 64:return E(_f3);case 65:return E(_f2);case 66:return E(_f1);case 67:return E(_f0);case 68:return E(_eZ);case 69:return E(_eY);case 70:return E(_eX);case 71:return E(_em);case 72:return E(_en);case 73:return E(_eo);case 74:return E(_ep);case 75:return E(_eq);case 76:return E(_er);case 77:return E(_es);case 78:return E(_eW);case 79:return E(_eV);case 80:return E(_eU);case 81:return E(_eT);case 82:return E(_eS);case 83:return E(_eR);case 84:return E(_eQ);case 85:return E(_eP);case 86:return E(_eO);case 87:return E(_eN);case 88:return E(_eM);case 89:return E(_eL);case 90:return E(_eK);case 91:return E(_eJ);case 92:return E(_eI);case 93:return E(_eH);case 94:return E(_eG);case 95:return E(_eF);default:return new T0(2);}};return _6f(new T1(0,function(_f6){return (E(_f6)==94)?E(new T1(0,_f4)):new T0(2);}),new T(function(){return B(A1(_ei,_el));}));});return _6f(new T1(1,_7n(_aM,_aO,_ex)),_eE);});return _6f(new T1(0,function(_f7){switch(E(_f7)){case 34:return E(_ev);case 39:return E(_eu);case 92:return E(_et);case 97:return E(_em);case 98:return E(_en);case 102:return E(_er);case 110:return E(_ep);case 114:return E(_es);case 116:return E(_eo);case 118:return E(_eq);default:return new T0(2);}}),_ew);},_f8=function(_f9){return C > 19 ? new F(function(){return A1(_f9,0);}) : (++C,A1(_f9,0));},_fa=function(_fb){var _fc=E(_fb);if(!_fc._){return _f8;}else{var _fd=E(_fc.a),_fe=_fd>>>0,_ff=new T(function(){return _fa(_fc.b);});if(_fe>887){var _fg=u_iswspace(_fd);if(!E(_fg)){return _f8;}else{var _fh=function(_fi){var _fj=new T(function(){return B(A1(_ff,_fi));});return new T1(0,function(_fk){return E(_fj);});};return _fh;}}else{if(_fe==32){var _fl=function(_fm){var _fn=new T(function(){return B(A1(_ff,_fm));});return new T1(0,function(_fo){return E(_fn);});};return _fl;}else{if(_fe-9>>>0>4){if(_fe==160){var _fp=function(_fq){var _fr=new T(function(){return B(A1(_ff,_fq));});return new T1(0,function(_fs){return E(_fr);});};return _fp;}else{return _f8;}}else{var _ft=function(_fu){var _fv=new T(function(){return B(A1(_ff,_fu));});return new T1(0,function(_fw){return E(_fv);});};return _ft;}}}}},_fx=function(_fy){var _fz=new T(function(){return B(_fx(_fy));}),_fA=function(_fB){return (E(_fB)==92)?E(_fz):new T0(2);},_fC=function(_fD){return E(new T1(0,_fA));},_fE=new T1(1,function(_fF){return C > 19 ? new F(function(){return A2(_fa,_fF,_fC);}) : (++C,A2(_fa,_fF,_fC));}),_fG=new T(function(){return B(_ek(function(_fH){return C > 19 ? new F(function(){return A1(_fy,new T2(0,_fH,true));}) : (++C,A1(_fy,new T2(0,_fH,true)));}));}),_fI=function(_fJ){var _fK=E(_fJ);if(_fK==38){return E(_fz);}else{var _fL=_fK>>>0;if(_fL>887){var _fM=u_iswspace(_fK);return (E(_fM)==0)?new T0(2):E(_fE);}else{return (_fL==32)?E(_fE):(_fL-9>>>0>4)?(_fL==160)?E(_fE):new T0(2):E(_fE);}}};return _6f(new T1(0,function(_fN){return (E(_fN)==92)?E(new T1(0,_fI)):new T0(2);}),new T1(0,function(_fO){var _fP=E(_fO);if(_fP==92){return E(_fG);}else{return C > 19 ? new F(function(){return A1(_fy,new T2(0,_fP,false));}) : (++C,A1(_fy,new T2(0,_fP,false)));}}));},_fQ=function(_fR,_fS){var _fT=new T(function(){return B(A1(_fS,new T1(1,new T(function(){return B(A1(_fR,__Z));}))));}),_fU=function(_fV){var _fW=E(_fV),_fX=E(_fW.a);if(_fX==34){if(!E(_fW.b)){return E(_fT);}else{return C > 19 ? new F(function(){return _fQ(function(_fY){return C > 19 ? new F(function(){return A1(_fR,new T2(1,_fX,_fY));}) : (++C,A1(_fR,new T2(1,_fX,_fY)));},_fS);}) : (++C,_fQ(function(_fY){return C > 19 ? new F(function(){return A1(_fR,new T2(1,_fX,_fY));}) : (++C,A1(_fR,new T2(1,_fX,_fY)));},_fS));}}else{return C > 19 ? new F(function(){return _fQ(function(_fZ){return C > 19 ? new F(function(){return A1(_fR,new T2(1,_fX,_fZ));}) : (++C,A1(_fR,new T2(1,_fX,_fZ)));},_fS);}) : (++C,_fQ(function(_fZ){return C > 19 ? new F(function(){return A1(_fR,new T2(1,_fX,_fZ));}) : (++C,A1(_fR,new T2(1,_fX,_fZ)));},_fS));}};return C > 19 ? new F(function(){return _fx(_fU);}) : (++C,_fx(_fU));},_g0=new T(function(){return unCStr("_\'");}),_g1=function(_g2){var _g3=u_iswalnum(_g2);if(!E(_g3)){return _az(_6Q,_g2,_g0);}else{return true;}},_g4=function(_g5){return _g1(E(_g5));},_g6=new T(function(){return unCStr(",;()[]{}`");}),_g7=new T(function(){return unCStr("=>");}),_g8=new T(function(){return unCStr("~");}),_g9=new T(function(){return unCStr("@");}),_ga=new T(function(){return unCStr("->");}),_gb=new T(function(){return unCStr("<-");}),_gc=new T(function(){return unCStr("|");}),_gd=new T(function(){return unCStr("\\");}),_ge=new T(function(){return unCStr("=");}),_gf=new T(function(){return unCStr("::");}),_gg=new T(function(){return unCStr("..");}),_gh=function(_gi){var _gj=new T(function(){return B(A1(_gi,new T0(6)));}),_gk=new T(function(){var _gl=new T(function(){var _gm=function(_gn){var _go=new T(function(){return B(A1(_gi,new T1(0,_gn)));});return new T1(0,function(_gp){return (E(_gp)==39)?E(_go):new T0(2);});};return B(_ek(_gm));}),_gq=function(_gr){var _gs=E(_gr);switch(_gs){case 39:return new T0(2);case 92:return E(_gl);default:var _gt=new T(function(){return B(A1(_gi,new T1(0,_gs)));});return new T1(0,function(_gu){return (E(_gu)==39)?E(_gt):new T0(2);});}},_gv=new T(function(){var _gw=new T(function(){return B(_fQ(_1V,_gi));}),_gx=new T(function(){var _gy=new T(function(){var _gz=new T(function(){var _gA=function(_gB){var _gC=E(_gB),_gD=u_iswalpha(_gC);return (E(_gD)==0)?(_gC==95)?new T1(1,_7N(_g4,function(_gE){return C > 19 ? new F(function(){return A1(_gi,new T1(3,new T2(1,_gC,_gE)));}) : (++C,A1(_gi,new T1(3,new T2(1,_gC,_gE))));})):new T0(2):new T1(1,_7N(_g4,function(_gF){return C > 19 ? new F(function(){return A1(_gi,new T1(3,new T2(1,_gC,_gF)));}) : (++C,A1(_gi,new T1(3,new T2(1,_gC,_gF))));}));};return _6f(new T1(0,_gA),new T(function(){return new T1(1,_7n(_8V,_av,_gi));}));}),_gG=function(_gH){return (!_az(_6Q,_gH,_aE))?new T0(2):new T1(1,_7N(_aF,function(_gI){var _gJ=new T2(1,_gH,_gI);if(!_az(new T2(0,_6V,_70),_gJ,new T2(1,_gg,new T2(1,_gf,new T2(1,_ge,new T2(1,_gd,new T2(1,_gc,new T2(1,_gb,new T2(1,_ga,new T2(1,_g9,new T2(1,_g8,new T2(1,_g7,__Z)))))))))))){return C > 19 ? new F(function(){return A1(_gi,new T1(4,_gJ));}) : (++C,A1(_gi,new T1(4,_gJ)));}else{return C > 19 ? new F(function(){return A1(_gi,new T1(2,_gJ));}) : (++C,A1(_gi,new T1(2,_gJ)));}}));};return _6f(new T1(0,_gG),_gz);});return _6f(new T1(0,function(_gK){if(!_az(_6Q,_gK,_g6)){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_gi,new T1(2,new T2(1,_gK,__Z)));}) : (++C,A1(_gi,new T1(2,new T2(1,_gK,__Z))));}}),_gy);});return _6f(new T1(0,function(_gL){return (E(_gL)==34)?E(_gw):new T0(2);}),_gx);});return _6f(new T1(0,function(_gM){return (E(_gM)==39)?E(new T1(0,_gq)):new T0(2);}),_gv);});return _6f(new T1(1,function(_gN){return (E(_gN)._==0)?E(_gj):new T0(2);}),_gk);},_gO=function(_gP,_gQ){var _gR=new T(function(){var _gS=new T(function(){var _gT=function(_gU){var _gV=new T(function(){var _gW=new T(function(){return B(A1(_gQ,_gU));});return B(_gh(function(_gX){var _gY=E(_gX);return (_gY._==2)?(!_6L(_gY.a,_6K))?new T0(2):E(_gW):new T0(2);}));}),_gZ=function(_h0){return E(_gV);};return new T1(1,function(_h1){return C > 19 ? new F(function(){return A2(_fa,_h1,_gZ);}) : (++C,A2(_fa,_h1,_gZ));});};return B(A2(_gP,0,_gT));});return B(_gh(function(_h2){var _h3=E(_h2);return (_h3._==2)?(!_6L(_h3.a,_6J))?new T0(2):E(_gS):new T0(2);}));}),_h4=function(_h5){return E(_gR);};return function(_h6){return C > 19 ? new F(function(){return A2(_fa,_h6,_h4);}) : (++C,A2(_fa,_h6,_h4));};},_h7=function(_h8,_h9){var _ha=function(_hb){var _hc=new T(function(){return B(A1(_h8,_hb));}),_hd=function(_he){return _6f(B(A1(_hc,_he)),new T(function(){return new T1(1,_gO(_ha,_he));}));};return _hd;},_hf=new T(function(){return B(A1(_h8,_h9));}),_hg=function(_hh){return _6f(B(A1(_hf,_hh)),new T(function(){return new T1(1,_gO(_ha,_hh));}));};return _hg;},_hi=function(_hj,_hk){var _hl=function(_hm,_hn){var _ho=function(_hp){return C > 19 ? new F(function(){return A1(_hn,new T(function(){return  -E(_hp);}));}) : (++C,A1(_hn,new T(function(){return  -E(_hp);})));},_hq=new T(function(){return B(_gh(function(_hr){return C > 19 ? new F(function(){return A3(_hj,_hr,_hm,_ho);}) : (++C,A3(_hj,_hr,_hm,_ho));}));}),_hs=function(_ht){return E(_hq);},_hu=function(_hv){return C > 19 ? new F(function(){return A2(_fa,_hv,_hs);}) : (++C,A2(_fa,_hv,_hs));},_hw=new T(function(){return B(_gh(function(_hx){var _hy=E(_hx);if(_hy._==4){var _hz=E(_hy.a);if(!_hz._){return C > 19 ? new F(function(){return A3(_hj,_hy,_hm,_hn);}) : (++C,A3(_hj,_hy,_hm,_hn));}else{if(E(_hz.a)==45){if(!E(_hz.b)._){return E(new T1(1,_hu));}else{return C > 19 ? new F(function(){return A3(_hj,_hy,_hm,_hn);}) : (++C,A3(_hj,_hy,_hm,_hn));}}else{return C > 19 ? new F(function(){return A3(_hj,_hy,_hm,_hn);}) : (++C,A3(_hj,_hy,_hm,_hn));}}}else{return C > 19 ? new F(function(){return A3(_hj,_hy,_hm,_hn);}) : (++C,A3(_hj,_hy,_hm,_hn));}}));}),_hA=function(_hB){return E(_hw);};return new T1(1,function(_hC){return C > 19 ? new F(function(){return A2(_fa,_hC,_hA);}) : (++C,A2(_fa,_hC,_hA));});};return _h7(_hl,_hk);},_hD=new T(function(){return 1/0;}),_hE=function(_hF,_hG){return C > 19 ? new F(function(){return A1(_hG,_hD);}) : (++C,A1(_hG,_hD));},_hH=new T(function(){return 0/0;}),_hI=function(_hJ,_hK){return C > 19 ? new F(function(){return A1(_hK,_hH);}) : (++C,A1(_hK,_hH));},_hL=new T(function(){return unCStr("NaN");}),_hM=new T(function(){return unCStr("Infinity");}),_hN=new T(function(){return unCStr("base");}),_hO=new T(function(){return unCStr("GHC.Exception");}),_hP=new T(function(){return unCStr("ArithException");}),_hQ=function(_hR){return E(new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_hN,_hO,_hP),__Z,__Z));},_hS=new T(function(){return unCStr("Ratio has zero denominator");}),_hT=new T(function(){return unCStr("denormal");}),_hU=new T(function(){return unCStr("divide by zero");}),_hV=new T(function(){return unCStr("loss of precision");}),_hW=new T(function(){return unCStr("arithmetic underflow");}),_hX=new T(function(){return unCStr("arithmetic overflow");}),_hY=function(_hZ,_i0){switch(E(_hZ)){case 0:return _x(_hX,_i0);case 1:return _x(_hW,_i0);case 2:return _x(_hV,_i0);case 3:return _x(_hU,_i0);case 4:return _x(_hT,_i0);default:return _x(_hS,_i0);}},_i1=function(_i2){return _hY(_i2,__Z);},_i3=new T(function(){return new T5(0,_hQ,new T3(0,function(_i4,_i5,_i6){return _hY(_i5,_i6);},_i1,function(_i7,_i8){return _1q(_hY,_i7,_i8);}),_i9,function(_ia){var _ib=E(_ia);return _m(_k(_ib.a),_hQ,_ib.b);},_i1);}),_i9=function(_4q){return new T2(0,_i3,_4q);},_ic=new T(function(){return die(new T(function(){return _i9(3);}));}),_id=function(_ie,_if){var _ig=E(_ie);if(!_ig._){var _ih=_ig.a,_ii=E(_if);return (_ii._==0)?_ih==_ii.a:(I_compareInt(_ii.a,_ih)==0)?true:false;}else{var _ij=_ig.a,_ik=E(_if);return (_ik._==0)?(I_compareInt(_ij,_ik.a)==0)?true:false:(I_compare(_ij,_ik.a)==0)?true:false;}},_il=new T1(0,0),_im=function(_in,_io){while(1){var _ip=E(_in);if(!_ip._){var _iq=E(_ip.a);if(_iq==(-2147483648)){_in=new T1(1,I_fromInt(-2147483648));continue;}else{var _ir=E(_io);if(!_ir._){return new T1(0,_iq%_ir.a);}else{_in=new T1(1,I_fromInt(_iq));_io=_ir;continue;}}}else{var _is=_ip.a,_it=E(_io);return (_it._==0)?new T1(1,I_rem(_is,I_fromInt(_it.a))):new T1(1,I_rem(_is,_it.a));}}},_iu=function(_iv,_iw){if(!_id(_iw,_il)){return _im(_iv,_iw);}else{return E(_ic);}},_ix=function(_iy,_iz){while(1){if(!_id(_iz,_il)){var _iA=_iz,_iB=_iu(_iy,_iz);_iy=_iA;_iz=_iB;continue;}else{return E(_iy);}}},_iC=function(_iD){var _iE=E(_iD);if(!_iE._){var _iF=E(_iE.a);return (_iF==(-2147483648))?E(_9b):(_iF<0)?new T1(0, -_iF):_iE;}else{var _iG=_iE.a;return (I_compareInt(_iG,0)>=0)?_iE:new T1(1,I_negate(_iG));}},_iH=function(_iI,_iJ){while(1){var _iK=E(_iI);if(!_iK._){var _iL=E(_iK.a);if(_iL==(-2147483648)){_iI=new T1(1,I_fromInt(-2147483648));continue;}else{var _iM=E(_iJ);if(!_iM._){return new T1(0,quot(_iL,_iM.a));}else{_iI=new T1(1,I_fromInt(_iL));_iJ=_iM;continue;}}}else{var _iN=_iK.a,_iO=E(_iJ);return (_iO._==0)?new T1(0,I_toInt(I_quot(_iN,I_fromInt(_iO.a)))):new T1(1,I_quot(_iN,_iO.a));}}},_iP=new T(function(){return die(new T(function(){return _i9(5);}));}),_iQ=function(_iR,_iS){if(!_id(_iS,_il)){var _iT=_ix(_iC(_iR),_iC(_iS));return (!_id(_iT,_il))?new T2(0,_iH(_iR,_iT),_iH(_iS,_iT)):E(_ic);}else{return E(_iP);}},_iU=new T1(0,1),_iV=new T(function(){return err(new T(function(){return unCStr("Negative exponent");}));}),_iW=new T1(0,2),_iX=new T(function(){return _id(_iW,_il);}),_iY=function(_iZ,_j0){while(1){var _j1=E(_iZ);if(!_j1._){var _j2=_j1.a,_j3=E(_j0);if(!_j3._){var _j4=_j3.a,_j5=subC(_j2,_j4);if(!E(_j5.b)){return new T1(0,_j5.a);}else{_iZ=new T1(1,I_fromInt(_j2));_j0=new T1(1,I_fromInt(_j4));continue;}}else{_iZ=new T1(1,I_fromInt(_j2));_j0=_j3;continue;}}else{var _j6=E(_j0);if(!_j6._){_iZ=_j1;_j0=new T1(1,I_fromInt(_j6.a));continue;}else{return new T1(1,I_sub(_j1.a,_j6.a));}}}},_j7=function(_j8,_j9,_ja){while(1){if(!E(_iX)){if(!_id(_im(_j9,_iW),_il)){if(!_id(_j9,_iU)){var _jb=_9t(_j8,_j8),_jc=_iH(_iY(_j9,_iU),_iW),_jd=_9t(_j8,_ja);_j8=_jb;_j9=_jc;_ja=_jd;continue;}else{return _9t(_j8,_ja);}}else{var _jb=_9t(_j8,_j8),_jc=_iH(_j9,_iW);_j8=_jb;_j9=_jc;continue;}}else{return E(_ic);}}},_je=function(_jf,_jg){while(1){if(!E(_iX)){if(!_id(_im(_jg,_iW),_il)){if(!_id(_jg,_iU)){return _j7(_9t(_jf,_jf),_iH(_iY(_jg,_iU),_iW),_jf);}else{return E(_jf);}}else{var _jh=_9t(_jf,_jf),_ji=_iH(_jg,_iW);_jf=_jh;_jg=_ji;continue;}}else{return E(_ic);}}},_jj=function(_jk,_jl){var _jm=E(_jk);if(!_jm._){var _jn=_jm.a,_jo=E(_jl);return (_jo._==0)?_jn<_jo.a:I_compareInt(_jo.a,_jn)>0;}else{var _jp=_jm.a,_jq=E(_jl);return (_jq._==0)?I_compareInt(_jp,_jq.a)<0:I_compare(_jp,_jq.a)<0;}},_jr=function(_js,_jt){if(!_jj(_jt,_il)){if(!_id(_jt,_il)){return _je(_js,_jt);}else{return E(_iU);}}else{return E(_iV);}},_ju=new T1(0,1),_jv=new T1(0,0),_jw=new T1(0,-1),_jx=function(_jy){var _jz=E(_jy);if(!_jz._){var _jA=_jz.a;return (_jA>=0)?(E(_jA)==0)?E(_jv):E(_91):E(_jw);}else{var _jB=I_compareInt(_jz.a,0);return (_jB<=0)?(E(_jB)==0)?E(_jv):E(_jw):E(_91);}},_jC=function(_jD,_jE,_jF){while(1){var _jG=E(_jF);if(!_jG._){if(!_jj(_jD,_9G)){return new T2(0,_9t(_jE,B(_jr(_9g,_jD))),_iU);}else{var _jH=B(_jr(_9g,_9c(_jD)));return _iQ(_9t(_jE,_jx(_jH)),_iC(_jH));}}else{var _jI=_iY(_jD,_ju),_jJ=_92(_9t(_jE,_9g),_3d(E(_jG.a)));_jD=_jI;_jE=_jJ;_jF=_jG.b;continue;}}},_jK=function(_jL,_jM){var _jN=E(_jL);if(!_jN._){var _jO=_jN.a,_jP=E(_jM);return (_jP._==0)?_jO>=_jP.a:I_compareInt(_jP.a,_jO)<=0;}else{var _jQ=_jN.a,_jR=E(_jM);return (_jR._==0)?I_compareInt(_jQ,_jR.a)>=0:I_compare(_jQ,_jR.a)>=0;}},_jS=function(_jT){var _jU=E(_jT);if(!_jU._){var _jV=_jU.b;return _iQ(_9t(_9H(new T(function(){return _3d(E(_jU.a));}),new T(function(){return _9h(_jV,0);},1),_9m(_9q,_jV)),_ju),_ju);}else{var _jW=_jU.a,_jX=_jU.c,_jY=E(_jU.b);if(!_jY._){var _jZ=E(_jX);if(!_jZ._){return _iQ(_9t(_9Y(_9g,_jW),_ju),_ju);}else{var _k0=_jZ.a;if(!_jK(_k0,_9G)){var _k1=B(_jr(_9g,_9c(_k0)));return _iQ(_9t(_9Y(_9g,_jW),_jx(_k1)),_iC(_k1));}else{return _iQ(_9t(_9t(_9Y(_9g,_jW),B(_jr(_9g,_k0))),_ju),_ju);}}}else{var _k2=_jY.a,_k3=E(_jX);if(!_k3._){return _jC(_9G,_9Y(_9g,_jW),_k2);}else{return _jC(_k3.a,_9Y(_9g,_jW),_k2);}}}},_k4=function(_k5,_k6){while(1){var _k7=E(_k6);if(!_k7._){return __Z;}else{if(!B(A1(_k5,_k7.a))){return _k7;}else{_k6=_k7.b;continue;}}}},_k8=function(_k9,_ka){var _kb=E(_k9);if(!_kb._){var _kc=_kb.a,_kd=E(_ka);return (_kd._==0)?_kc>_kd.a:I_compareInt(_kd.a,_kc)<0;}else{var _ke=_kb.a,_kf=E(_ka);return (_kf._==0)?I_compareInt(_ke,_kf.a)>0:I_compare(_ke,_kf.a)>0;}},_kg=function(_kh,_ki){return E(_kh)==E(_ki);},_kj=function(_kk){return _kg(0,_kk);},_kl=new T1(1,new T2(0,E(_9G),E(_iU))),_km=function(_kn,_ko,_kp){var _kq=E(_kp);if(!_kq._){return new T1(1,new T(function(){var _kr=_jS(_kq);return new T2(0,E(_kr.a),E(_kr.b));}));}else{var _ks=E(_kq.c);if(!_ks._){return new T1(1,new T(function(){var _kt=_jS(_kq);return new T2(0,E(_kt.a),E(_kt.b));}));}else{var _ku=_ks.a;if(!_k8(_ku,new T1(0,2147483647))){if(!_jj(_ku,new T1(0,-2147483648))){var _kv=function(_kw){var _kx=_kw+_b1(_ku)|0;return (_kx<=(E(_ko)+3|0))?(_kx>=(E(_kn)-3|0))?new T1(1,new T(function(){var _ky=_jS(_kq);return new T2(0,E(_ky.a),E(_ky.b));})):E(_kl):__Z;},_kz=_k4(_kj,_kq.a);if(!_kz._){var _kA=E(_kq.b);if(!_kA._){return E(_kl);}else{var _kB=_4r(_kj,_kA.a);if(!E(_kB.b)._){return E(_kl);}else{return _kv( -_9h(_kB.a,0));}}}else{return _kv(_9h(_kz,0));}}else{return __Z;}}else{return __Z;}}}},_kC=function(_kD,_kE){return new T0(2);},_kF=new T1(0,1),_kG=function(_kH,_kI){var _kJ=E(_kH);if(!_kJ._){var _kK=_kJ.a,_kL=E(_kI);if(!_kL._){var _kM=_kL.a;return (_kK!=_kM)?(_kK>_kM)?2:0:1;}else{var _kN=I_compareInt(_kL.a,_kK);return (_kN<=0)?(_kN>=0)?1:2:0;}}else{var _kO=_kJ.a,_kP=E(_kI);if(!_kP._){var _kQ=I_compareInt(_kO,_kP.a);return (_kQ>=0)?(_kQ<=0)?1:2:0;}else{var _kR=I_compare(_kO,_kP.a);return (_kR>=0)?(_kR<=0)?1:2:0;}}},_kS=function(_kT,_kU){var _kV=E(_kT);return (_kV._==0)?_kV.a*Math.pow(2,_kU):I_toNumber(_kV.a)*Math.pow(2,_kU);},_kW=function(_kX,_kY){while(1){var _kZ=E(_kX);if(!_kZ._){var _l0=E(_kZ.a);if(_l0==(-2147483648)){_kX=new T1(1,I_fromInt(-2147483648));continue;}else{var _l1=E(_kY);if(!_l1._){var _l2=_l1.a;return new T2(0,new T1(0,quot(_l0,_l2)),new T1(0,_l0%_l2));}else{_kX=new T1(1,I_fromInt(_l0));_kY=_l1;continue;}}}else{var _l3=E(_kY);if(!_l3._){_kX=_kZ;_kY=new T1(1,I_fromInt(_l3.a));continue;}else{var _l4=I_quotRem(_kZ.a,_l3.a);return new T2(0,new T1(1,_l4.a),new T1(1,_l4.b));}}}},_l5=new T1(0,0),_l6=function(_l7,_l8,_l9){if(!_id(_l9,_l5)){var _la=_kW(_l8,_l9),_lb=_la.a;switch(_kG(_3s(_la.b,1),_l9)){case 0:return _kS(_lb,_l7);case 1:if(!(_b1(_lb)&1)){return _kS(_lb,_l7);}else{return _kS(_92(_lb,_kF),_l7);}break;default:return _kS(_92(_lb,_kF),_l7);}}else{return E(_ic);}},_lc=function(_ld){var _le=function(_lf,_lg){while(1){if(!_jj(_lf,_ld)){if(!_k8(_lf,_ld)){if(!_id(_lf,_ld)){return C > 19 ? new F(function(){return _4M("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2");}) : (++C,_4M("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2"));}else{return E(_lg);}}else{return _lg-1|0;}}else{var _lh=_3s(_lf,1),_li=_lg+1|0;_lf=_lh;_lg=_li;continue;}}};return C > 19 ? new F(function(){return _le(_91,0);}) : (++C,_le(_91,0));},_lj=function(_lk){var _ll=E(_lk);if(!_ll._){var _lm=_ll.a>>>0;if(!_lm){return -1;}else{var _ln=function(_lo,_lp){while(1){if(_lo>=_lm){if(_lo<=_lm){if(_lo!=_lm){return C > 19 ? new F(function(){return _4M("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");}) : (++C,_4M("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2"));}else{return E(_lp);}}else{return _lp-1|0;}}else{var _lq=imul(_lo,2)>>>0,_lr=_lp+1|0;_lo=_lq;_lp=_lr;continue;}}};return C > 19 ? new F(function(){return _ln(1,0);}) : (++C,_ln(1,0));}}else{return C > 19 ? new F(function(){return _lc(_ll);}) : (++C,_lc(_ll));}},_ls=function(_lt){var _lu=E(_lt);if(!_lu._){var _lv=_lu.a>>>0;if(!_lv){return new T2(0,-1,0);}else{var _lw=function(_lx,_ly){while(1){if(_lx>=_lv){if(_lx<=_lv){if(_lx!=_lv){return C > 19 ? new F(function(){return _4M("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");}) : (++C,_4M("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2"));}else{return E(_ly);}}else{return _ly-1|0;}}else{var _lz=imul(_lx,2)>>>0,_lA=_ly+1|0;_lx=_lz;_ly=_lA;continue;}}};return new T2(0,B(_lw(1,0)),(_lv&_lv-1>>>0)>>>0&4294967295);}}else{var _lB=_lu.a;return new T2(0,B(_lj(_lu)),I_compareInt(I_and(_lB,I_sub(_lB,I_fromInt(1))),0));}},_lC=function(_lD,_lE){while(1){var _lF=E(_lD);if(!_lF._){var _lG=_lF.a,_lH=E(_lE);if(!_lH._){return new T1(0,(_lG>>>0&_lH.a>>>0)>>>0&4294967295);}else{_lD=new T1(1,I_fromInt(_lG));_lE=_lH;continue;}}else{var _lI=E(_lE);if(!_lI._){_lD=_lF;_lE=new T1(1,I_fromInt(_lI.a));continue;}else{return new T1(1,I_and(_lF.a,_lI.a));}}}},_lJ=function(_lK,_lL){var _lM=E(_lK);if(!_lM._){var _lN=(_lM.a>>>0&(2<<_lL>>>0)-1>>>0)>>>0,_lO=1<<_lL>>>0;return (_lO<=_lN)?(_lO>=_lN)?1:2:0;}else{var _lP=_lC(_lM,_iY(_3s(new T1(0,2),_lL),_91)),_lQ=_3s(_91,_lL);return (!_k8(_lQ,_lP))?(!_jj(_lQ,_lP))?1:2:0;}},_lR=function(_lS,_lT){while(1){var _lU=E(_lS);if(!_lU._){_lS=new T1(1,I_fromInt(_lU.a));continue;}else{return new T1(1,I_shiftRight(_lU.a,_lT));}}},_lV=function(_lW,_lX,_lY,_lZ){var _m0=_ls(_lZ),_m1=_m0.a;if(!E(_m0.b)){var _m2=B(_lj(_lY));if(_m2<((_m1+_lW|0)-1|0)){var _m3=_m1+(_lW-_lX|0)|0;if(_m3>0){if(_m3>_m2){if(_m3<=(_m2+1|0)){if(!E(_ls(_lY).b)){return 0;}else{return _kS(_kF,_lW-_lX|0);}}else{return 0;}}else{var _m4=_lR(_lY,_m3);switch(_lJ(_lY,_m3-1|0)){case 0:return _kS(_m4,_lW-_lX|0);case 1:if(!(_b1(_m4)&1)){return _kS(_m4,_lW-_lX|0);}else{return _kS(_92(_m4,_kF),_lW-_lX|0);}break;default:return _kS(_92(_m4,_kF),_lW-_lX|0);}}}else{return _kS(_lY,(_lW-_lX|0)-_m3|0);}}else{if(_m2>=_lX){var _m5=_lR(_lY,(_m2+1|0)-_lX|0);switch(_lJ(_lY,_m2-_lX|0)){case 0:return _kS(_m5,((_m2-_m1|0)+1|0)-_lX|0);case 2:return _kS(_92(_m5,_kF),((_m2-_m1|0)+1|0)-_lX|0);default:if(!(_b1(_m5)&1)){return _kS(_m5,((_m2-_m1|0)+1|0)-_lX|0);}else{return _kS(_92(_m5,_kF),((_m2-_m1|0)+1|0)-_lX|0);}}}else{return _kS(_lY, -_m1);}}}else{var _m6=B(_lj(_lY))-_m1|0,_m7=function(_m8){var _m9=function(_ma,_mb){if(!_b4(_3s(_mb,_lX),_ma)){return _l6(_m8-_lX|0,_ma,_mb);}else{return _l6((_m8-_lX|0)+1|0,_ma,_3s(_mb,1));}};if(_m8>=_lX){if(_m8!=_lX){return _m9(_lY,new T(function(){return _3s(_lZ,_m8-_lX|0);}));}else{return _m9(_lY,_lZ);}}else{return _m9(new T(function(){return _3s(_lY,_lX-_m8|0);}),_lZ);}};if(_lW>_m6){return C > 19 ? new F(function(){return _m7(_lW);}) : (++C,_m7(_lW));}else{return C > 19 ? new F(function(){return _m7(_m6);}) : (++C,_m7(_m6));}}},_mc=new T(function(){return 0/0;}),_md=new T(function(){return -1/0;}),_me=new T(function(){return 1/0;}),_mf=function(_mg,_mh){if(!_id(_mh,_l5)){if(!_id(_mg,_l5)){if(!_jj(_mg,_l5)){return C > 19 ? new F(function(){return _lV(-1021,53,_mg,_mh);}) : (++C,_lV(-1021,53,_mg,_mh));}else{return  -B(_lV(-1021,53,_9c(_mg),_mh));}}else{return 0;}}else{return (!_id(_mg,_l5))?(!_jj(_mg,_l5))?E(_me):E(_md):E(_mc);}},_mi=function(_mj){var _mk=E(_mj);switch(_mk._){case 3:var _ml=_mk.a;return (!_6L(_ml,_hM))?(!_6L(_ml,_hL))?_kC:_hI:_hE;case 5:var _mm=_km(-1021,1024,_mk.a);if(!_mm._){return _hE;}else{var _mn=new T(function(){var _mo=E(_mm.a);return B(_mf(_mo.a,_mo.b));});return function(_mp,_mq){return C > 19 ? new F(function(){return A1(_mq,_mn);}) : (++C,A1(_mq,_mn));};}break;default:return _kC;}},_mr=function(_ms){var _mt=function(_mu){return E(new T2(3,_ms,_7e));};return new T1(1,function(_mv){return C > 19 ? new F(function(){return A2(_fa,_mv,_mt);}) : (++C,A2(_fa,_mv,_mt));});},_mw=new T(function(){return B(A3(_hi,_mi,0,_mr));}),_mx=function(_my,_mz){while(1){var _mA=E(_my);if(!_mA._){return E(_mz);}else{_my=_mA.b;_mz=_mA.a;continue;}}},_mB=function(_mC){var _mD=E(_mC);if(!_mD._){return __Z;}else{var _mE=_mD.a,_mF=new T(function(){if(E(_mx(_mE,_5U))==37){var _mG=_5V(_62(_mw,new T(function(){return _5R(_mE);})));if(!_mG._){return E(_6d);}else{if(!E(_mG.b)._){return E(_mG.a)/100;}else{return E(_6c);}}}else{var _mH=_5V(_62(_mw,_mE));if(!_mH._){return E(_6d);}else{if(!E(_mH.b)._){return E(_mH.a);}else{return E(_6c);}}}});return new T1(1,_mF);}},_mI=function(_mJ){if(_mJ!=0){if(_mJ<=0){var _mK=1/(1+0.5* -_mJ),_mL=_mK*_mK,_mM=_mL*_mK,_mN=_mM*_mK,_mO=_mN*_mK,_mP=_mO*_mK,_mQ=_mP*_mK,_mR=_mQ*_mK;return (_mJ<0)?_mK*Math.exp( -(_mJ*_mJ)-1.26551223+1.00002368*_mK+0.37409196*_mL+9.678418e-2*_mM-0.18628806*_mN+0.27886807*_mO-1.13520398*_mP+1.48851587*_mQ-0.82215223*_mR+0.17087277*_mR*_mK)-1:1-_mK*Math.exp( -(_mJ*_mJ)-1.26551223+1.00002368*_mK+0.37409196*_mL+9.678418e-2*_mM-0.18628806*_mN+0.27886807*_mO-1.13520398*_mP+1.48851587*_mQ-0.82215223*_mR+0.17087277*_mR*_mK);}else{var _mS=1/(1+0.5*_mJ),_mT=_mS*_mS,_mU=_mT*_mS,_mV=_mU*_mS,_mW=_mV*_mS,_mX=_mW*_mS,_mY=_mX*_mS,_mZ=_mY*_mS;return (_mJ<0)?_mS*Math.exp( -(_mJ*_mJ)-1.26551223+1.00002368*_mS+0.37409196*_mT+9.678418e-2*_mU-0.18628806*_mV+0.27886807*_mW-1.13520398*_mX+1.48851587*_mY-0.82215223*_mZ+0.17087277*_mZ*_mS)-1:1-_mS*Math.exp( -(_mJ*_mJ)-1.26551223+1.00002368*_mS+0.37409196*_mT+9.678418e-2*_mU-0.18628806*_mV+0.27886807*_mW-1.13520398*_mX+1.48851587*_mY-0.82215223*_mZ+0.17087277*_mZ*_mS);}}else{return (_mJ<0)?Math.exp( -(_mJ*_mJ)-1.26551223+1.00002368+0.37409196+9.678418e-2-0.18628806+0.27886807-1.13520398+1.48851587-0.82215223+0.17087277)-1:1-Math.exp( -(_mJ*_mJ)-1.26551223+1.00002368+0.37409196+9.678418e-2-0.18628806+0.27886807-1.13520398+1.48851587-0.82215223+0.17087277);}},_n0=new T(function(){return unCStr("price");}),_n1=new T(function(){return unCStr("rho");}),_n2=new T(function(){return unCStr("vega");}),_n3=new T(function(){return unCStr("theta");}),_n4=new T(function(){return unCStr("gamma");}),_n5=new T(function(){return unCStr("delta");}),_n6=function(_n7,_n8){var _n9=E(_n7);if(!_n9._){return __Z;}else{var _na=E(_n8);return (_na._==0)?__Z:new T2(1,new T2(0,_n9.a,_na.a),new T(function(){return _n6(_n9.b,_na.b);}));}},_nb=function(_nc){var _nd=new T(function(){return E(E(_nc).d);}),_ne=new T(function(){return E(E(_nc).c);}),_nf=new T(function(){return Math.exp( -E(_ne)*E(_nd));}),_ng=new T(function(){return E(E(_nc).e);}),_nh=new T(function(){return E(E(E(_nc).b).b);}),_ni=new T(function(){return E(E(E(_nc).a).b);}),_nj=new T(function(){var _nk=E(_ng),_nl=E(_nd);return (Math.log(E(_nh)/E(_ni))+(E(_ne)+_nk*_nk/2)*_nl)/_nk/Math.sqrt(_nl);}),_nm=new T(function(){if(!E(E(_nc).g)){return 1;}else{return -1;}}),_nn=new T(function(){return 0.5*(1-_mI( -(E(_nm)*(E(_nj)-E(_ng)*Math.sqrt(E(_nd))))*0.7071067811865475));}),_no=new T(function(){return Math.sqrt(E(_nd));}),_np=new T(function(){var _nq=E(_nj);return Math.exp( -(_nq*_nq/2))/2.5066282746350725;});return _n6(new T2(1,_n0,new T2(1,_n5,new T2(1,_n4,new T2(1,_n3,new T2(1,_n2,new T2(1,_n1,__Z)))))),new T2(1,new T(function(){var _nr=E(_nm);return (_nr*E(_nh)*0.5*(1-_mI( -(_nr*E(_nj))*0.7071067811865475))-_nr*E(_ni)*E(_nf)*E(_nn))*E(E(_nc).f);}),new T2(1,new T(function(){if(!E(E(_nc).g)){return 0.5*(1-_mI( -E(_nj)*0.7071067811865475));}else{return 0.5*(1-_mI( -E(_nj)*0.7071067811865475))-1;}}),new T2(1,new T(function(){return E(_np)/E(_nh)/E(_ng)/E(_no);}),new T2(1,new T(function(){return ( -E(_nh)*E(_np)*E(_ng)/2/E(_no)-E(_nm)*E(_ne)*E(_ni)*E(_nf)*E(_nn))/365;}),new T2(1,new T(function(){return E(_nh)*E(_no)*E(_np);}),new T2(1,new T(function(){return E(_nm)*E(_ni)*E(_nd)*E(_nf)*E(_nn);}),__Z)))))));},_ns=function(_nt,_){var _nu=E(_nt);if(!_nu._){return E(_4O);}else{var _nv=_nu.a,_nw=E(_nu.b);if(!_nw._){return E(_4O);}else{var _nx=_nw.a,_ny=E(_nw.b);if(!_ny._){return E(_4O);}else{var _nz=_ny.a,_nA=E(_ny.b);if(!_nA._){return E(_4O);}else{var _nB=_nA.a,_nC=E(_nA.b);if(!_nC._){return E(_4O);}else{var _nD=_nC.a,_nE=E(_nC.b);if(!_nE._){return E(_4O);}else{var _nF=E(_nE.b);if(!_nF._){return E(_4O);}else{if(!E(_nF.b)._){var _nG=function(_){var _nH=_2v(E(_nv),"value"),_nI=_2v(E(_nx),"value"),_nJ=_2v(E(_nz),"value"),_nK=_2v(E(_nB),"value"),_nL=_2v(E(_nD),"value"),_nM=_mB(new T1(1,new T(function(){var _nN=String(_nH);return fromJSStr(_nN);})));if(!_nM._){return 0;}else{var _nO=_nM.a,_nP=_mB(new T1(1,new T(function(){var _nQ=String(_nI);return fromJSStr(_nQ);})));if(!_nP._){return 0;}else{var _nR=_nP.a,_nS=_mB(new T1(1,new T(function(){var _nT=String(_nJ);return fromJSStr(_nT);})));if(!_nS._){return 0;}else{var _nU=_nS.a,_nV=_mB(new T1(1,new T(function(){var _nW=String(_nK);return fromJSStr(_nW);})));if(!_nV._){return 0;}else{var _nX=_nV.a,_nY=_mB(new T1(1,new T(function(){var _nZ=String(_nL);return fromJSStr(_nZ);})));if(!_nY._){return 0;}else{var _o0=_nY.a,_o1=toJSStr(E(_4Q)),_o2=_40(E(_nE.a),_o1,toJSStr(_3S(_nb({_:0,a:new T2(0,_5H,_nR),b:new T2(0,_5H,_nO),c:_nU,d:_nX,e:_o0,f:1,g:false})))),_o3=_40(E(_nF.a),_o1,toJSStr(_3W(_nb({_:0,a:new T2(0,_5H,_nR),b:new T2(0,_5H,_nO),c:_nU,d:_nX,e:_o0,f:1,g:true}))));return _2r(_);}}}}}},_o4=B(A(_5f,[_2u,_2s,_2n,_nv,1,function(_o5,_){return _nG(_);},_])),_o6=B(A(_5f,[_2u,_2s,_2n,_nx,1,function(_o7,_){return _nG(_);},_])),_o8=B(A(_5f,[_2u,_2s,_2a,_nz,2,function(_o9,_){return _nG(_);},_])),_oa=B(A(_5f,[_2u,_2s,_2a,_nB,2,function(_ob,_){return _nG(_);},_]));return C > 19 ? new F(function(){return A(_5f,[_2u,_2s,_2a,_nD,2,function(_oc,_){return _nG(_);},_]);}) : (++C,A(_5f,[_2u,_2s,_2a,_nD,2,function(_oc,_){return _nG(_);},_]));}else{return E(_4O);}}}}}}}}},_od=(function(id){return document.getElementById(id);}),_oe=new T(function(){return err(new T(function(){return unCStr("Maybe.fromJust: Nothing");}));}),_of=function(_og){var _oh=E(_og);return (_oh._==0)?E(_oe):E(_oh.a);},_oi=function(_oj,_ok){while(1){var _ol=(function(_om,_on){var _oo=E(_om);if(!_oo._){return __Z;}else{var _op=_oo.b,_oq=E(_on);if(!_oq._){return __Z;}else{var _or=_oq.b;if(!E(_oq.a)._){return new T2(1,_oo.a,new T(function(){return _oi(_op,_or);}));}else{_oj=_op;_ok=_or;return __continue;}}}})(_oj,_ok);if(_ol!=__continue){return _ol;}}},_os=new T(function(){return unAppCStr("[]",__Z);}),_ot=function(_ou){var _ov=E(_ou);if(!_ov._){return E(new T2(1,93,__Z));}else{var _ow=new T(function(){return _x(fromJSStr(E(_ov.a)),new T(function(){return _ot(_ov.b);},1));});return new T2(1,44,_ow);}},_ox=function(_oy,_oz){var _oA=new T(function(){var _oB=_oi(_oy,_oz);if(!_oB._){return E(_os);}else{var _oC=new T(function(){return _x(fromJSStr(E(_oB.a)),new T(function(){return _ot(_oB.b);},1));});return new T2(1,91,_oC);}});return err(unAppCStr("Elements with the following IDs could not be found: ",_oA));},_oD=function(_oE){while(1){var _oF=E(_oE);if(!_oF._){return false;}else{if(!E(_oF.a)._){return true;}else{_oE=_oF.b;continue;}}}},_oG=function(_oH,_oI,_oJ){var _oK=_4T(_oH),_oL=function(_oM){if(!_oD(_oM)){return C > 19 ? new F(function(){return A1(_oJ,new T(function(){return _9m(_of,_oM);}));}) : (++C,A1(_oJ,new T(function(){return _9m(_of,_oM);})));}else{return _ox(_oI,_oM);}},_oN=new T(function(){var _oO=new T(function(){return B(A2(_5d,_oK,__Z));}),_oP=function(_oQ){var _oR=E(_oQ);if(!_oR._){return E(_oO);}else{var _oS=new T(function(){return B(_oP(_oR.b));}),_oT=function(_oU){return C > 19 ? new F(function(){return A3(_4V,_oK,_oS,function(_oV){return C > 19 ? new F(function(){return A2(_5d,_oK,new T2(1,_oU,_oV));}) : (++C,A2(_5d,_oK,new T2(1,_oU,_oV)));});}) : (++C,A3(_4V,_oK,_oS,function(_oV){return C > 19 ? new F(function(){return A2(_5d,_oK,new T2(1,_oU,_oV));}) : (++C,A2(_5d,_oK,new T2(1,_oU,_oV)));}));},_oW=new T(function(){return B(A2(_59,_oH,function(_){var _oX=_od(E(_oR.a)),_oY=__eq(_oX,E(_58));return (E(_oY)==0)?new T1(1,_oX):__Z;}));});return C > 19 ? new F(function(){return A3(_4V,_oK,_oW,_oT);}) : (++C,A3(_4V,_oK,_oW,_oT));}};return B(_oP(_oI));});return C > 19 ? new F(function(){return A3(_4V,_oK,_oN,_oL);}) : (++C,A3(_4V,_oK,_oN,_oL));},_oZ=new T(function(){return B(_oG(_1X,new T(function(){return _9m(function(_p0){return toJSStr(E(_p0));},new T2(1,new T(function(){return unCStr("s");}),new T2(1,new T(function(){return unCStr("k");}),new T2(1,new T(function(){return unCStr("r");}),new T2(1,new T(function(){return unCStr("t");}),new T2(1,new T(function(){return unCStr("sigma");}),new T2(1,new T(function(){return unCStr("resultC");}),new T2(1,new T(function(){return unCStr("resultP");}),__Z))))))));}),_ns));});
var hasteMain = function() {B(A(_oZ, [0]));};window.onload = hasteMain;