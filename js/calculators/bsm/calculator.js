"use strict";
var __haste_prog_id = '68fb8dc67f59aa9165464672d7d467bcb03d8003aa51685b65ba07a9f00cc84c';
var __haste_script_elem = document.currentScript;
// This object will hold all exports.
var Haste = {};
if(typeof window === 'undefined' && typeof global !== 'undefined') window = global;

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

function writeOffAddr64(addr, off, x) {
    addr['v']['w32'][addr.off/8 + off*2] = x.low;
    addr['v']['w32'][addr.off/8 + off*2 + 1] = x.high;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

function readOffAddr64(signed, addr, off) {
    var w64 = hs_mkWord64( addr['v']['w32'][addr.off/8 + off*2]
                         , addr['v']['w32'][addr.off/8 + off*2 + 1]);
    return signed ? hs_word64ToInt64(w64) : w64;
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
var __isUndef = function(x) {return typeof x == 'undefined';}
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

/* Code for creating and querying the static pointer table. */
window.__hs_spt = [];

function __spt_insert(ptr) {
    ptr = E(B(ptr));
    var ks = [ (ptr.a.a.low>>>0).toString(16)
             , (ptr.a.a.high>>>0).toString(16)
             , (ptr.a.b.low>>>0).toString(16)
             , (ptr.a.b.high>>>0).toString(16)
             ]
    var key = ks.join();
    window.__hs_spt[key] = ptr;
}

function hs_spt_lookup(k) {
    var ks = [ k['v']['w32'][0].toString(16)
             , k['v']['w32'][1].toString(16)
             , k['v']['w32'][2].toString(16)
             , k['v']['w32'][3].toString(16)
             ]
    var key = ks.join();
    return window.__hs_spt[key];
}

var _0=function(_1,_2,_){var _3=B(A1(_1,_)),_4=B(A1(_2,_));return new T(function(){return B(A1(_3,_4));});},_5=function(_6,_7,_){var _8=B(A1(_7,_));return new T(function(){return B(A1(_6,_8));});},_9=function(_a,_){return _a;},_b=function(_c,_d,_){var _e=B(A1(_c,_));return C > 19 ? new F(function(){return A1(_d,_);}) : (++C,A1(_d,_));},_f=new T(function(){return unCStr("base");}),_g=new T(function(){return unCStr("GHC.IO.Exception");}),_h=new T(function(){return unCStr("IOException");}),_i=function(_j){return E(new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_f,_g,_h),__Z,__Z));},_k=function(_l){return E(E(_l).a);},_m=function(_n,_o,_p){var _q=B(A1(_n,_)),_r=B(A1(_o,_)),_s=hs_eqWord64(_q.a,_r.a);if(!_s){return __Z;}else{var _t=hs_eqWord64(_q.b,_r.b);return (!_t)?__Z:new T1(1,_p);}},_u=new T(function(){return unCStr(": ");}),_v=new T(function(){return unCStr(")");}),_w=new T(function(){return unCStr(" (");}),_x=function(_y,_z){var _A=E(_y);return (_A._==0)?E(_z):new T2(1,_A.a,new T(function(){return _x(_A.b,_z);}));},_B=new T(function(){return unCStr("interrupted");}),_C=new T(function(){return unCStr("system error");}),_D=new T(function(){return unCStr("unsatisified constraints");}),_E=new T(function(){return unCStr("user error");}),_F=new T(function(){return unCStr("permission denied");}),_G=new T(function(){return unCStr("illegal operation");}),_H=new T(function(){return unCStr("end of file");}),_I=new T(function(){return unCStr("resource exhausted");}),_J=new T(function(){return unCStr("resource busy");}),_K=new T(function(){return unCStr("does not exist");}),_L=new T(function(){return unCStr("already exists");}),_M=new T(function(){return unCStr("resource vanished");}),_N=new T(function(){return unCStr("timeout");}),_O=new T(function(){return unCStr("unsupported operation");}),_P=new T(function(){return unCStr("hardware fault");}),_Q=new T(function(){return unCStr("inappropriate type");}),_R=new T(function(){return unCStr("invalid argument");}),_S=new T(function(){return unCStr("failed");}),_T=new T(function(){return unCStr("protocol error");}),_U=function(_V,_W){switch(E(_V)){case 0:return _x(_L,_W);case 1:return _x(_K,_W);case 2:return _x(_J,_W);case 3:return _x(_I,_W);case 4:return _x(_H,_W);case 5:return _x(_G,_W);case 6:return _x(_F,_W);case 7:return _x(_E,_W);case 8:return _x(_D,_W);case 9:return _x(_C,_W);case 10:return _x(_T,_W);case 11:return _x(_S,_W);case 12:return _x(_R,_W);case 13:return _x(_Q,_W);case 14:return _x(_P,_W);case 15:return _x(_O,_W);case 16:return _x(_N,_W);case 17:return _x(_M,_W);default:return _x(_B,_W);}},_X=new T(function(){return unCStr("}");}),_Y=new T(function(){return unCStr("{handle: ");}),_Z=function(_10,_11,_12,_13,_14,_15){var _16=new T(function(){var _17=new T(function(){var _18=new T(function(){var _19=E(_13);if(!_19._){return E(_15);}else{var _1a=new T(function(){return _x(_19,new T(function(){return _x(_v,_15);},1));},1);return _x(_w,_1a);}},1);return _U(_11,_18);}),_1b=E(_12);if(!_1b._){return E(_17);}else{return _x(_1b,new T(function(){return _x(_u,_17);},1));}}),_1c=E(_14);if(!_1c._){var _1d=E(_10);if(!_1d._){return E(_16);}else{var _1e=E(_1d.a);if(!_1e._){var _1f=new T(function(){var _1g=new T(function(){return _x(_X,new T(function(){return _x(_u,_16);},1));},1);return _x(_1e.a,_1g);},1);return _x(_Y,_1f);}else{var _1h=new T(function(){var _1i=new T(function(){return _x(_X,new T(function(){return _x(_u,_16);},1));},1);return _x(_1e.a,_1i);},1);return _x(_Y,_1h);}}}else{return _x(_1c.a,new T(function(){return _x(_u,_16);},1));}},_1j=function(_1k){var _1l=E(_1k);return _Z(_1l.a,_1l.b,_1l.c,_1l.d,_1l.f,__Z);},_1m=function(_1n,_1o){var _1p=E(_1n);return _Z(_1p.a,_1p.b,_1p.c,_1p.d,_1p.f,_1o);},_1q=function(_1r,_1s,_1t){var _1u=E(_1s);if(!_1u._){return unAppCStr("[]",_1t);}else{var _1v=new T(function(){var _1w=new T(function(){var _1x=function(_1y){var _1z=E(_1y);if(!_1z._){return E(new T2(1,93,_1t));}else{var _1A=new T(function(){return B(A2(_1r,_1z.a,new T(function(){return _1x(_1z.b);})));});return new T2(1,44,_1A);}};return _1x(_1u.b);});return B(A2(_1r,_1u.a,_1w));});return new T2(1,91,_1v);}},_1B=new T(function(){return new T5(0,_i,new T3(0,function(_1C,_1D,_1E){var _1F=E(_1D);return _Z(_1F.a,_1F.b,_1F.c,_1F.d,_1F.f,_1E);},_1j,function(_1G,_1H){return _1q(_1m,_1G,_1H);}),function(_1I){return new T2(0,_1B,_1I);},function(_1J){var _1K=E(_1J);return _m(_k(_1K.a),_i,_1K.b);},_1j);}),_1L=new T(function(){return E(_1B);}),_1M=function(_1N){return E(E(_1N).c);},_1O=function(_1P){return new T6(0,__Z,7,__Z,_1P,__Z,__Z);},_1Q=function(_1R,_){var _1S=new T(function(){return B(A2(_1M,_1L,new T(function(){return B(A1(_1O,_1R));})));});return die(_1S);},_1T=function(_1U,_){return _1Q(_1U,_);},_1V=function(_1W){return E(_1W);},_1X=new T2(0,new T5(0,new T5(0,new T2(0,_5,function(_1Y,_1Z,_){var _20=B(A1(_1Z,_));return _1Y;}),_9,_0,_b,function(_21,_22,_){var _23=B(A1(_21,_)),_24=B(A1(_22,_));return _23;}),function(_25,_26,_){var _27=B(A1(_25,_));return C > 19 ? new F(function(){return A2(_26,_27,_);}) : (++C,A2(_26,_27,_));},_b,_9,function(_28){return C > 19 ? new F(function(){return A1(_1T,_28);}) : (++C,A1(_1T,_28));}),_1V),_29=function(_){return 0;},_2a=new T2(0,function(_2b){switch(E(_2b)){case 0:return "load";case 1:return "unload";case 2:return "change";case 3:return "focus";case 4:return "blur";case 5:return "submit";default:return "scroll";}},function(_2c,_2d,_){return _29(_);}),_2e=function(_2f,_){var _2g=_2f["keyCode"],_2h=_2f["ctrlKey"],_2i=_2f["altKey"],_2j=_2f["shiftKey"],_2k=_2f["metaKey"];return new T(function(){var _2l=Number(_2g),_2m=jsTrunc(_2l);return new T5(0,_2m,E(_2h),E(_2i),E(_2j),E(_2k));});},_2n=new T2(0,function(_2o){switch(E(_2o)){case 0:return "keypress";case 1:return "keyup";default:return "keydown";}},function(_2p,_2q,_){return _2e(E(_2q),_);}),_2r=function(_){return 0;},_2s=new T2(0,_1V,function(_2t,_){return new T1(1,_2t);}),_2u=new T2(0,_1X,_9),_2v=(function(e,p){var x = e[p];return typeof x === 'undefined' ? '' : x.toString();}),_2w=(function(e,p,v){e[p] = v;}),_2x=new T(function(){return unCStr("base");}),_2y=new T(function(){return unCStr("Control.Exception.Base");}),_2z=new T(function(){return unCStr("PatternMatchFail");}),_2A=function(_2B){return E(new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_2x,_2y,_2z),__Z,__Z));},_2C=function(_2D){return E(E(_2D).a);},_2E=function(_2F,_2G){return _x(E(_2F).a,_2G);},_2H=new T(function(){return new T5(0,_2A,new T3(0,function(_2I,_2J,_2K){return _x(E(_2J).a,_2K);},_2C,function(_2L,_2M){return _1q(_2E,_2L,_2M);}),function(_2N){return new T2(0,_2H,_2N);},function(_2O){var _2P=E(_2O);return _m(_k(_2P.a),_2A,_2P.b);},_2C);}),_2Q=new T(function(){return unCStr("Non-exhaustive patterns in");}),_2R=function(_2S,_2T){return die(new T(function(){return B(A2(_1M,_2T,_2S));}));},_2U=function(_2V,_2W){return _2R(_2V,_2W);},_2X=function(_2Y,_2Z){var _30=E(_2Z);if(!_30._){return new T2(0,__Z,__Z);}else{var _31=_30.a;if(!B(A1(_2Y,_31))){return new T2(0,__Z,_30);}else{var _32=new T(function(){var _33=_2X(_2Y,_30.b);return new T2(0,_33.a,_33.b);});return new T2(0,new T2(1,_31,new T(function(){return E(E(_32).a);})),new T(function(){return E(E(_32).b);}));}}},_34=new T(function(){return unCStr("\n");}),_35=function(_36){return (E(_36)==124)?false:true;},_37=function(_38,_39){var _3a=_2X(_35,unCStr(_38)),_3b=_3a.a,_3c=function(_3d,_3e){var _3f=new T(function(){var _3g=new T(function(){return _x(_39,new T(function(){return _x(_3e,_34);},1));});return unAppCStr(": ",_3g);},1);return _x(_3d,_3f);},_3h=E(_3a.b);if(!_3h._){return _3c(_3b,__Z);}else{if(E(_3h.a)==124){return _3c(_3b,new T2(1,32,_3h.b));}else{return _3c(_3b,__Z);}}},_3i=function(_3j){return _2U(new T1(0,new T(function(){return _37(_3j,_2Q);})),_2H);},_3k=new T(function(){return B((function(_3l){return C > 19 ? new F(function(){return _3i("calculator.hs:(13,1)-(30,39)|function calculator");}) : (++C,_3i("calculator.hs:(13,1)-(30,39)|function calculator"));})(_));}),_3m=new T(function(){return unCStr("innerHTML");}),_3n=function(_3o){return E(E(_3o).a);},_3p=function(_3q){return E(E(_3q).a);},_3r=function(_3s){return E(E(_3s).b);},_3t=function(_3u){return E(E(_3u).a);},_3v=function(_3w){return E(E(_3w).b);},_3x=function(_3y){return E(E(_3y).a);},_3z=function(_3A){var _3B=B(A1(_3A,_));return E(_3B);},_3C=new T(function(){return _3z(function(_){return nMV(__Z);});}),_3D=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_3E=new T(function(){return _3z(function(_){return __jsNull();});}),_3F=function(_3G){return E(E(_3G).b);},_3H=function(_3I){return E(E(_3I).b);},_3J=function(_3K){return E(E(_3K).d);},_3L=function(_3M,_3N,_3O,_3P,_3Q,_3R){var _3S=_3n(_3M),_3T=_3p(_3S),_3U=new T(function(){return _3F(_3S);}),_3V=new T(function(){return _3J(_3T);}),_3W=new T(function(){return B(A2(_3t,_3N,_3P));}),_3X=new T(function(){return B(A2(_3x,_3O,_3Q));}),_3Y=function(_3Z){return C > 19 ? new F(function(){return A1(_3V,new T3(0,_3X,_3W,_3Z));}) : (++C,A1(_3V,new T3(0,_3X,_3W,_3Z)));},_40=function(_41){var _42=new T(function(){var _43=new T(function(){var _44=__createJSFunc(2,function(_45,_){var _46=B(A2(E(_41),_45,_));return _3E;}),_47=_44;return function(_){return _3D(E(_3W),E(_3X),_47);};});return B(A1(_3U,_43));});return C > 19 ? new F(function(){return A3(_3r,_3T,_42,_3Y);}) : (++C,A3(_3r,_3T,_42,_3Y));},_48=new T(function(){var _49=new T(function(){return _3F(_3S);}),_4a=function(_4b){var _4c=new T(function(){return B(A1(_49,function(_){var _=wMV(E(_3C),new T1(1,_4b));return C > 19 ? new F(function(){return A(_3v,[_3O,_3Q,_4b,_]);}) : (++C,A(_3v,[_3O,_3Q,_4b,_]));}));});return C > 19 ? new F(function(){return A3(_3r,_3T,_4c,_3R);}) : (++C,A3(_3r,_3T,_4c,_3R));};return B(A2(_3H,_3M,_4a));});return C > 19 ? new F(function(){return A3(_3r,_3T,_48,_40);}) : (++C,A3(_3r,_3T,_48,_40));},_4d=new T(function(){return unCStr("CHF");}),_4e=function(_4f,_4g){while(1){var _4h=E(_4f);if(!_4h._){return E(_4g);}else{var _4i=new T2(1,_4h.a,_4g);_4f=_4h.b;_4g=_4i;continue;}}},_4j=function(_4k){return _4e(_4k,__Z);},_4l=function(_4m,_4n,_4o){while(1){var _4p=(function(_4q,_4r,_4s){var _4t=E(_4q);if(!_4t._){return new T2(0,new T(function(){return _4j(_4r);}),new T(function(){return _4j(_4s);}));}else{var _4u=_4r,_4v=new T2(1,_4t.a,_4s);_4m=_4t.b;_4n=_4u;_4o=_4v;return __continue;}})(_4m,_4n,_4o);if(_4p!=__continue){return _4p;}}},_4w=function(_4x,_4y,_4z){while(1){var _4A=(function(_4B,_4C,_4D){var _4E=E(_4B);if(!_4E._){return new T2(0,new T(function(){return _4j(_4C);}),new T(function(){return _4j(_4D);}));}else{var _4F=_4E.b,_4G=E(_4E.a);if(_4G==46){return _4l(_4F,_4C,__Z);}else{var _4H=new T2(1,_4G,_4C),_4I=_4D;_4x=_4F;_4y=_4H;_4z=_4I;return __continue;}}})(_4x,_4y,_4z);if(_4A!=__continue){return _4A;}}},_4J=function(_4K,_4L){var _4M=E(_4L);if(!_4M._){return __Z;}else{var _4N=_4M.a,_4O=E(_4K);return (_4O==1)?new T2(1,_4N,__Z):new T2(1,_4N,new T(function(){return _4J(_4O-1|0,_4M.b);}));}},_4P=function(_4Q){var _4R=I_decodeDouble(_4Q);return new T2(0,new T1(1,_4R.b),_4R.a);},_4S=function(_4T){var _4U=E(_4T);if(!_4U._){return _4U.a;}else{return I_toNumber(_4U.a);}},_4V=function(_4W){return new T1(0,_4W);},_4X=function(_4Y){var _4Z=hs_intToInt64(2147483647),_50=hs_leInt64(_4Y,_4Z);if(!_50){return new T1(1,I_fromInt64(_4Y));}else{var _51=hs_intToInt64(-2147483648),_52=hs_geInt64(_4Y,_51);if(!_52){return new T1(1,I_fromInt64(_4Y));}else{var _53=hs_int64ToInt(_4Y);return _4V(_53);}}},_54=function(_55){var _56=hs_intToInt64(_55);return E(_56);},_57=function(_58){var _59=E(_58);if(!_59._){return _54(_59.a);}else{return I_toInt64(_59.a);}},_5a=function(_5b,_5c){while(1){var _5d=E(_5b);if(!_5d._){_5b=new T1(1,I_fromInt(_5d.a));continue;}else{return new T1(1,I_shiftLeft(_5d.a,_5c));}}},_5e=function(_5f,_5g){var _5h=Math.pow(10,_5f),_5i=rintDouble(_5g*_5h),_5j=_4P(_5i),_5k=_5j.a,_5l=_5j.b,_5m=function(_5n,_5o){var _5p=new T(function(){return unAppCStr(".",new T(function(){if(0>=_5f){return __Z;}else{return _4J(_5f,_5o);}}));},1);return _x(_5n,_5p);};if(_5l>=0){var _5q=jsShow(_4S(_5a(_5k,_5l))/_5h),_5r=_4w(fromJSStr(_5q),__Z,__Z);return _5m(_5r.a,_5r.b);}else{var _5s=hs_uncheckedIShiftRA64(_57(_5k), -_5l),_5t=jsShow(_4S(_4X(_5s))/_5h),_5u=_4w(fromJSStr(_5t),__Z,__Z);return _5m(_5u.a,_5u.b);}},_5v=new T(function(){return unCStr("<br>");}),_5w=new T(function(){return unCStr(" ");}),_5x=function(_5y){var _5z=E(_5y);if(!_5z._){return __Z;}else{var _5A=new T(function(){var _5B=E(_5z.a),_5C=new T(function(){return unAppCStr(": ",new T(function(){return _x(_5e(4,E(_5B.b)),_5w);}));},1);return _x(_x(_5B.a,_5C),new T(function(){return _5x(_5z.b);},1));},1);return _x(_5v,_5A);}},_5D=function(_5E,_5F){var _5G=E(_5F);return (_5G._==0)?__Z:new T2(1,_5E,new T(function(){return _5D(_5G.a,_5G.b);}));},_5H=new T(function(){return unCStr(": empty list");}),_5I=new T(function(){return unCStr("Prelude.");}),_5J=function(_5K){return err(_x(_5I,new T(function(){return _x(_5K,_5H);},1)));},_5L=new T(function(){return _5J(new T(function(){return unCStr("init");}));}),_5M=function(_5N){var _5O=E(_5N);if(!_5O._){return E(_5L);}else{return _5D(_5O.a,_5O.b);}},_5P=new T(function(){return _5J(new T(function(){return unCStr("last");}));}),_5Q=function(_5R){while(1){var _5S=(function(_5T){var _5U=E(_5T);if(!_5U._){return __Z;}else{var _5V=_5U.b,_5W=E(_5U.a);if(!E(_5W.b)._){return new T2(1,_5W.a,new T(function(){return _5Q(_5V);}));}else{_5R=_5V;return __continue;}}})(_5R);if(_5S!=__continue){return _5S;}}},_5X=function(_5Y,_5Z){while(1){var _60=(function(_61,_62){var _63=E(_61);switch(_63._){case 0:var _64=E(_62);if(!_64._){return __Z;}else{_5Y=B(A1(_63.a,_64.a));_5Z=_64.b;return __continue;}break;case 1:var _65=B(A1(_63.a,_62)),_66=_62;_5Y=_65;_5Z=_66;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_63.a,_62),new T(function(){return _5X(_63.b,_62);}));default:return E(_63.a);}})(_5Y,_5Z);if(_60!=__continue){return _60;}}},_67=new T(function(){return err(new T(function(){return unCStr("Prelude.read: ambiguous parse");}));}),_68=new T(function(){return err(new T(function(){return unCStr("Prelude.read: no parse");}));}),_69=new T(function(){return B(_3i("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_6a=function(_6b,_6c){var _6d=function(_6e){var _6f=E(_6c);if(_6f._==3){return new T2(3,_6f.a,new T(function(){return _6a(_6b,_6f.b);}));}else{var _6g=E(_6b);if(_6g._==2){return _6f;}else{if(_6f._==2){return _6g;}else{var _6h=function(_6i){if(_6f._==4){var _6j=function(_6k){return new T1(4,new T(function(){return _x(_5X(_6g,_6k),_6f.a);}));};return new T1(1,_6j);}else{if(_6g._==1){var _6l=_6g.a;if(!_6f._){return new T1(1,function(_6m){return _6a(B(A1(_6l,_6m)),_6f);});}else{var _6n=function(_6o){return _6a(B(A1(_6l,_6o)),new T(function(){return B(A1(_6f.a,_6o));}));};return new T1(1,_6n);}}else{if(!_6f._){return E(_69);}else{var _6p=function(_6q){return _6a(_6g,new T(function(){return B(A1(_6f.a,_6q));}));};return new T1(1,_6p);}}}};switch(_6g._){case 1:if(_6f._==4){var _6r=function(_6s){return new T1(4,new T(function(){return _x(_5X(B(A1(_6g.a,_6s)),_6s),_6f.a);}));};return new T1(1,_6r);}else{return _6h(_);}break;case 4:var _6t=_6g.a;switch(_6f._){case 0:var _6u=function(_6v){var _6w=new T(function(){return _x(_6t,new T(function(){return _5X(_6f,_6v);},1));});return new T1(4,_6w);};return new T1(1,_6u);case 1:var _6x=function(_6y){var _6z=new T(function(){return _x(_6t,new T(function(){return _5X(B(A1(_6f.a,_6y)),_6y);},1));});return new T1(4,_6z);};return new T1(1,_6x);default:return new T1(4,new T(function(){return _x(_6t,_6f.a);}));}break;default:return _6h(_);}}}}},_6A=E(_6b);switch(_6A._){case 0:var _6B=E(_6c);if(!_6B._){var _6C=function(_6D){return _6a(B(A1(_6A.a,_6D)),new T(function(){return B(A1(_6B.a,_6D));}));};return new T1(0,_6C);}else{return _6d(_);}break;case 3:return new T2(3,_6A.a,new T(function(){return _6a(_6A.b,_6c);}));default:return _6d(_);}},_6E=new T(function(){return unCStr("(");}),_6F=new T(function(){return unCStr(")");}),_6G=function(_6H,_6I){while(1){var _6J=E(_6H);if(!_6J._){return (E(_6I)._==0)?true:false;}else{var _6K=E(_6I);if(!_6K._){return false;}else{if(E(_6J.a)!=E(_6K.a)){return false;}else{_6H=_6J.b;_6I=_6K.b;continue;}}}}},_6L=new T2(0,function(_6M,_6N){return E(_6M)==E(_6N);},function(_6O,_6P){return E(_6O)!=E(_6P);}),_6Q=function(_6R,_6S){while(1){var _6T=E(_6R);if(!_6T._){return (E(_6S)._==0)?true:false;}else{var _6U=E(_6S);if(!_6U._){return false;}else{if(E(_6T.a)!=E(_6U.a)){return false;}else{_6R=_6T.b;_6S=_6U.b;continue;}}}}},_6V=function(_6W,_6X){return (!_6Q(_6W,_6X))?true:false;},_6Y=function(_6Z,_70){var _71=E(_6Z);switch(_71._){case 0:return new T1(0,function(_72){return C > 19 ? new F(function(){return _6Y(B(A1(_71.a,_72)),_70);}) : (++C,_6Y(B(A1(_71.a,_72)),_70));});case 1:return new T1(1,function(_73){return C > 19 ? new F(function(){return _6Y(B(A1(_71.a,_73)),_70);}) : (++C,_6Y(B(A1(_71.a,_73)),_70));});case 2:return new T0(2);case 3:return _6a(B(A1(_70,_71.a)),new T(function(){return B(_6Y(_71.b,_70));}));default:var _74=function(_75){var _76=E(_75);if(!_76._){return __Z;}else{var _77=E(_76.a);return _x(_5X(B(A1(_70,_77.a)),_77.b),new T(function(){return _74(_76.b);},1));}},_78=_74(_71.a);return (_78._==0)?new T0(2):new T1(4,_78);}},_79=new T0(2),_7a=function(_7b){return new T2(3,_7b,_79);},_7c=function(_7d,_7e){var _7f=E(_7d);if(!_7f){return C > 19 ? new F(function(){return A1(_7e,0);}) : (++C,A1(_7e,0));}else{var _7g=new T(function(){return B(_7c(_7f-1|0,_7e));});return new T1(0,function(_7h){return E(_7g);});}},_7i=function(_7j,_7k,_7l){var _7m=new T(function(){return B(A1(_7j,_7a));}),_7n=function(_7o,_7p,_7q,_7r){while(1){var _7s=B((function(_7t,_7u,_7v,_7w){var _7x=E(_7t);switch(_7x._){case 0:var _7y=E(_7u);if(!_7y._){return C > 19 ? new F(function(){return A1(_7k,_7w);}) : (++C,A1(_7k,_7w));}else{var _7z=_7v+1|0,_7A=_7w;_7o=B(A1(_7x.a,_7y.a));_7p=_7y.b;_7q=_7z;_7r=_7A;return __continue;}break;case 1:var _7B=B(A1(_7x.a,_7u)),_7C=_7u,_7z=_7v,_7A=_7w;_7o=_7B;_7p=_7C;_7q=_7z;_7r=_7A;return __continue;case 2:return C > 19 ? new F(function(){return A1(_7k,_7w);}) : (++C,A1(_7k,_7w));break;case 3:var _7D=new T(function(){return B(_6Y(_7x,_7w));});return C > 19 ? new F(function(){return _7c(_7v,function(_7E){return E(_7D);});}) : (++C,_7c(_7v,function(_7E){return E(_7D);}));break;default:return C > 19 ? new F(function(){return _6Y(_7x,_7w);}) : (++C,_6Y(_7x,_7w));}})(_7o,_7p,_7q,_7r));if(_7s!=__continue){return _7s;}}};return function(_7F){return _7n(_7m,_7F,0,_7l);};},_7G=function(_7H){return C > 19 ? new F(function(){return A1(_7H,__Z);}) : (++C,A1(_7H,__Z));},_7I=function(_7J,_7K){var _7L=function(_7M){var _7N=E(_7M);if(!_7N._){return _7G;}else{var _7O=_7N.a;if(!B(A1(_7J,_7O))){return _7G;}else{var _7P=new T(function(){return _7L(_7N.b);}),_7Q=function(_7R){var _7S=new T(function(){return B(A1(_7P,function(_7T){return C > 19 ? new F(function(){return A1(_7R,new T2(1,_7O,_7T));}) : (++C,A1(_7R,new T2(1,_7O,_7T)));}));});return new T1(0,function(_7U){return E(_7S);});};return _7Q;}}};return function(_7V){return C > 19 ? new F(function(){return A2(_7L,_7V,_7K);}) : (++C,A2(_7L,_7V,_7K));};},_7W=new T(function(){return err(new T(function(){return unCStr("valDig: Bad base");}));}),_7X=function(_7Y,_7Z){var _80=function(_81,_82){var _83=E(_81);if(!_83._){var _84=new T(function(){return B(A1(_82,__Z));});return function(_85){return C > 19 ? new F(function(){return A1(_85,_84);}) : (++C,A1(_85,_84));};}else{var _86=E(_83.a),_87=function(_88){var _89=new T(function(){return _80(_83.b,function(_8a){return C > 19 ? new F(function(){return A1(_82,new T2(1,_88,_8a));}) : (++C,A1(_82,new T2(1,_88,_8a)));});}),_8b=function(_8c){var _8d=new T(function(){return B(A1(_89,_8c));});return new T1(0,function(_8e){return E(_8d);});};return _8b;};switch(E(_7Y)){case 8:if(48>_86){var _8f=new T(function(){return B(A1(_82,__Z));});return function(_8g){return C > 19 ? new F(function(){return A1(_8g,_8f);}) : (++C,A1(_8g,_8f));};}else{if(_86>55){var _8h=new T(function(){return B(A1(_82,__Z));});return function(_8i){return C > 19 ? new F(function(){return A1(_8i,_8h);}) : (++C,A1(_8i,_8h));};}else{return _87(_86-48|0);}}break;case 10:if(48>_86){var _8j=new T(function(){return B(A1(_82,__Z));});return function(_8k){return C > 19 ? new F(function(){return A1(_8k,_8j);}) : (++C,A1(_8k,_8j));};}else{if(_86>57){var _8l=new T(function(){return B(A1(_82,__Z));});return function(_8m){return C > 19 ? new F(function(){return A1(_8m,_8l);}) : (++C,A1(_8m,_8l));};}else{return _87(_86-48|0);}}break;case 16:if(48>_86){if(97>_86){if(65>_86){var _8n=new T(function(){return B(A1(_82,__Z));});return function(_8o){return C > 19 ? new F(function(){return A1(_8o,_8n);}) : (++C,A1(_8o,_8n));};}else{if(_86>70){var _8p=new T(function(){return B(A1(_82,__Z));});return function(_8q){return C > 19 ? new F(function(){return A1(_8q,_8p);}) : (++C,A1(_8q,_8p));};}else{return _87((_86-65|0)+10|0);}}}else{if(_86>102){if(65>_86){var _8r=new T(function(){return B(A1(_82,__Z));});return function(_8s){return C > 19 ? new F(function(){return A1(_8s,_8r);}) : (++C,A1(_8s,_8r));};}else{if(_86>70){var _8t=new T(function(){return B(A1(_82,__Z));});return function(_8u){return C > 19 ? new F(function(){return A1(_8u,_8t);}) : (++C,A1(_8u,_8t));};}else{return _87((_86-65|0)+10|0);}}}else{return _87((_86-97|0)+10|0);}}}else{if(_86>57){if(97>_86){if(65>_86){var _8v=new T(function(){return B(A1(_82,__Z));});return function(_8w){return C > 19 ? new F(function(){return A1(_8w,_8v);}) : (++C,A1(_8w,_8v));};}else{if(_86>70){var _8x=new T(function(){return B(A1(_82,__Z));});return function(_8y){return C > 19 ? new F(function(){return A1(_8y,_8x);}) : (++C,A1(_8y,_8x));};}else{return _87((_86-65|0)+10|0);}}}else{if(_86>102){if(65>_86){var _8z=new T(function(){return B(A1(_82,__Z));});return function(_8A){return C > 19 ? new F(function(){return A1(_8A,_8z);}) : (++C,A1(_8A,_8z));};}else{if(_86>70){var _8B=new T(function(){return B(A1(_82,__Z));});return function(_8C){return C > 19 ? new F(function(){return A1(_8C,_8B);}) : (++C,A1(_8C,_8B));};}else{return _87((_86-65|0)+10|0);}}}else{return _87((_86-97|0)+10|0);}}}else{return _87(_86-48|0);}}break;default:return E(_7W);}}},_8D=function(_8E){var _8F=E(_8E);if(!_8F._){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_7Z,_8F);}) : (++C,A1(_7Z,_8F));}};return function(_8G){return C > 19 ? new F(function(){return A3(_80,_8G,_1V,_8D);}) : (++C,A3(_80,_8G,_1V,_8D));};},_8H=function(_8I){var _8J=function(_8K){return C > 19 ? new F(function(){return A1(_8I,new T1(5,new T2(0,8,_8K)));}) : (++C,A1(_8I,new T1(5,new T2(0,8,_8K))));},_8L=function(_8M){return C > 19 ? new F(function(){return A1(_8I,new T1(5,new T2(0,16,_8M)));}) : (++C,A1(_8I,new T1(5,new T2(0,16,_8M))));},_8N=function(_8O){switch(E(_8O)){case 79:return new T1(1,_7X(8,_8J));case 88:return new T1(1,_7X(16,_8L));case 111:return new T1(1,_7X(8,_8J));case 120:return new T1(1,_7X(16,_8L));default:return new T0(2);}};return function(_8P){return (E(_8P)==48)?E(new T1(0,_8N)):new T0(2);};},_8Q=function(_8R){return new T1(0,_8H(_8R));},_8S=function(_8T){return C > 19 ? new F(function(){return A1(_8T,__Z);}) : (++C,A1(_8T,__Z));},_8U=function(_8V){return C > 19 ? new F(function(){return A1(_8V,__Z);}) : (++C,A1(_8V,__Z));},_8W=new T1(0,1),_8X=function(_8Y,_8Z){while(1){var _90=E(_8Y);if(!_90._){var _91=_90.a,_92=E(_8Z);if(!_92._){var _93=_92.a,_94=addC(_91,_93);if(!E(_94.b)){return new T1(0,_94.a);}else{_8Y=new T1(1,I_fromInt(_91));_8Z=new T1(1,I_fromInt(_93));continue;}}else{_8Y=new T1(1,I_fromInt(_91));_8Z=_92;continue;}}else{var _95=E(_8Z);if(!_95._){_8Y=_90;_8Z=new T1(1,I_fromInt(_95.a));continue;}else{return new T1(1,I_add(_90.a,_95.a));}}}},_96=new T(function(){return _8X(new T1(0,2147483647),_8W);}),_97=function(_98){var _99=E(_98);if(!_99._){var _9a=E(_99.a);return (_9a==(-2147483648))?E(_96):new T1(0, -_9a);}else{return new T1(1,I_negate(_99.a));}},_9b=new T1(0,10),_9c=function(_9d,_9e){while(1){var _9f=E(_9d);if(!_9f._){return E(_9e);}else{var _9g=_9e+1|0;_9d=_9f.b;_9e=_9g;continue;}}},_9h=function(_9i,_9j){var _9k=E(_9j);return (_9k._==0)?__Z:new T2(1,new T(function(){return B(A1(_9i,_9k.a));}),new T(function(){return _9h(_9i,_9k.b);}));},_9l=function(_9m){return _4V(E(_9m));},_9n=new T(function(){return err(new T(function(){return unCStr("this should not happen");}));}),_9o=function(_9p,_9q){while(1){var _9r=E(_9p);if(!_9r._){var _9s=_9r.a,_9t=E(_9q);if(!_9t._){var _9u=_9t.a;if(!(imul(_9s,_9u)|0)){return new T1(0,imul(_9s,_9u)|0);}else{_9p=new T1(1,I_fromInt(_9s));_9q=new T1(1,I_fromInt(_9u));continue;}}else{_9p=new T1(1,I_fromInt(_9s));_9q=_9t;continue;}}else{var _9v=E(_9q);if(!_9v._){_9p=_9r;_9q=new T1(1,I_fromInt(_9v.a));continue;}else{return new T1(1,I_mul(_9r.a,_9v.a));}}}},_9w=function(_9x,_9y){var _9z=E(_9y);if(!_9z._){return __Z;}else{var _9A=E(_9z.b);return (_9A._==0)?E(_9n):new T2(1,_8X(_9o(_9z.a,_9x),_9A.a),new T(function(){return _9w(_9x,_9A.b);}));}},_9B=new T1(0,0),_9C=function(_9D,_9E,_9F){while(1){var _9G=(function(_9H,_9I,_9J){var _9K=E(_9J);if(!_9K._){return E(_9B);}else{if(!E(_9K.b)._){return E(_9K.a);}else{var _9L=E(_9I);if(_9L<=40){var _9M=function(_9N,_9O){while(1){var _9P=E(_9O);if(!_9P._){return E(_9N);}else{var _9Q=_8X(_9o(_9N,_9H),_9P.a);_9N=_9Q;_9O=_9P.b;continue;}}};return _9M(_9B,_9K);}else{var _9R=_9o(_9H,_9H);if(!(_9L%2)){var _9S=_9w(_9H,_9K);_9D=_9R;_9E=quot(_9L+1|0,2);_9F=_9S;return __continue;}else{var _9S=_9w(_9H,new T2(1,_9B,_9K));_9D=_9R;_9E=quot(_9L+1|0,2);_9F=_9S;return __continue;}}}}})(_9D,_9E,_9F);if(_9G!=__continue){return _9G;}}},_9T=function(_9U,_9V){return _9C(_9U,new T(function(){return _9c(_9V,0);},1),_9h(_9l,_9V));},_9W=function(_9X){var _9Y=new T(function(){var _9Z=new T(function(){var _a0=function(_a1){return C > 19 ? new F(function(){return A1(_9X,new T1(1,new T(function(){return _9T(_9b,_a1);})));}) : (++C,A1(_9X,new T1(1,new T(function(){return _9T(_9b,_a1);}))));};return new T1(1,_7X(10,_a0));}),_a2=function(_a3){if(E(_a3)==43){var _a4=function(_a5){return C > 19 ? new F(function(){return A1(_9X,new T1(1,new T(function(){return _9T(_9b,_a5);})));}) : (++C,A1(_9X,new T1(1,new T(function(){return _9T(_9b,_a5);}))));};return new T1(1,_7X(10,_a4));}else{return new T0(2);}},_a6=function(_a7){if(E(_a7)==45){var _a8=function(_a9){return C > 19 ? new F(function(){return A1(_9X,new T1(1,new T(function(){return _97(_9T(_9b,_a9));})));}) : (++C,A1(_9X,new T1(1,new T(function(){return _97(_9T(_9b,_a9));}))));};return new T1(1,_7X(10,_a8));}else{return new T0(2);}};return _6a(_6a(new T1(0,_a6),new T1(0,_a2)),_9Z);});return _6a(new T1(0,function(_aa){return (E(_aa)==101)?E(_9Y):new T0(2);}),new T1(0,function(_ab){return (E(_ab)==69)?E(_9Y):new T0(2);}));},_ac=function(_ad){var _ae=function(_af){return C > 19 ? new F(function(){return A1(_ad,new T1(1,_af));}) : (++C,A1(_ad,new T1(1,_af)));};return function(_ag){return (E(_ag)==46)?new T1(1,_7X(10,_ae)):new T0(2);};},_ah=function(_ai){return new T1(0,_ac(_ai));},_aj=function(_ak){var _al=function(_am){var _an=function(_ao){return new T1(1,_7i(_9W,_8S,function(_ap){return C > 19 ? new F(function(){return A1(_ak,new T1(5,new T3(1,_am,_ao,_ap)));}) : (++C,A1(_ak,new T1(5,new T3(1,_am,_ao,_ap))));}));};return new T1(1,_7i(_ah,_8U,_an));};return _7X(10,_al);},_aq=function(_ar){return new T1(1,_aj(_ar));},_as=function(_at){return E(E(_at).a);},_au=function(_av,_aw,_ax){while(1){var _ay=E(_ax);if(!_ay._){return false;}else{if(!B(A3(_as,_av,_aw,_ay.a))){_ax=_ay.b;continue;}else{return true;}}}},_az=new T(function(){return unCStr("!@#$%&*+./<=>?\\^|:-~");}),_aA=function(_aB){return _au(_6L,_aB,_az);},_aC=function(_aD){var _aE=new T(function(){return B(A1(_aD,8));}),_aF=new T(function(){return B(A1(_aD,16));});return function(_aG){switch(E(_aG)){case 79:return E(_aE);case 88:return E(_aF);case 111:return E(_aE);case 120:return E(_aF);default:return new T0(2);}};},_aH=function(_aI){return new T1(0,_aC(_aI));},_aJ=function(_aK){return C > 19 ? new F(function(){return A1(_aK,10);}) : (++C,A1(_aK,10));},_aL=function(_aM,_aN){var _aO=jsShowI(_aM);return _x(fromJSStr(_aO),_aN);},_aP=function(_aQ,_aR,_aS){if(_aR>=0){return _aL(_aR,_aS);}else{if(_aQ<=6){return _aL(_aR,_aS);}else{return new T2(1,40,new T(function(){var _aT=jsShowI(_aR);return _x(fromJSStr(_aT),new T2(1,41,_aS));}));}}},_aU=function(_aV){return err(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return _aP(9,_aV,__Z);})));},_aW=function(_aX){var _aY=E(_aX);if(!_aY._){return E(_aY.a);}else{return I_toInt(_aY.a);}},_aZ=function(_b0,_b1){var _b2=E(_b0);if(!_b2._){var _b3=_b2.a,_b4=E(_b1);return (_b4._==0)?_b3<=_b4.a:I_compareInt(_b4.a,_b3)>=0;}else{var _b5=_b2.a,_b6=E(_b1);return (_b6._==0)?I_compareInt(_b5,_b6.a)<=0:I_compare(_b5,_b6.a)<=0;}},_b7=function(_b8){return new T0(2);},_b9=function(_ba){var _bb=E(_ba);if(!_bb._){return _b7;}else{var _bc=_bb.a,_bd=E(_bb.b);if(!_bd._){return E(_bc);}else{var _be=new T(function(){return _b9(_bd);}),_bf=function(_bg){return _6a(B(A1(_bc,_bg)),new T(function(){return B(A1(_be,_bg));}));};return _bf;}}},_bh=function(_bi,_bj){var _bk=function(_bl,_bm,_bn){var _bo=E(_bl);if(!_bo._){return C > 19 ? new F(function(){return A1(_bn,_bi);}) : (++C,A1(_bn,_bi));}else{var _bp=E(_bm);if(!_bp._){return new T0(2);}else{if(E(_bo.a)!=E(_bp.a)){return new T0(2);}else{var _bq=new T(function(){return B(_bk(_bo.b,_bp.b,_bn));});return new T1(0,function(_br){return E(_bq);});}}}};return function(_bs){return C > 19 ? new F(function(){return _bk(_bi,_bs,_bj);}) : (++C,_bk(_bi,_bs,_bj));};},_bt=new T(function(){return unCStr("SO");}),_bu=function(_bv){var _bw=new T(function(){return B(A1(_bv,14));});return new T1(1,_bh(_bt,function(_bx){return E(_bw);}));},_by=new T(function(){return unCStr("SOH");}),_bz=function(_bA){var _bB=new T(function(){return B(A1(_bA,1));});return new T1(1,_bh(_by,function(_bC){return E(_bB);}));},_bD=new T(function(){return unCStr("NUL");}),_bE=function(_bF){var _bG=new T(function(){return B(A1(_bF,0));});return new T1(1,_bh(_bD,function(_bH){return E(_bG);}));},_bI=new T(function(){return unCStr("STX");}),_bJ=function(_bK){var _bL=new T(function(){return B(A1(_bK,2));});return new T1(1,_bh(_bI,function(_bM){return E(_bL);}));},_bN=new T(function(){return unCStr("ETX");}),_bO=function(_bP){var _bQ=new T(function(){return B(A1(_bP,3));});return new T1(1,_bh(_bN,function(_bR){return E(_bQ);}));},_bS=new T(function(){return unCStr("EOT");}),_bT=function(_bU){var _bV=new T(function(){return B(A1(_bU,4));});return new T1(1,_bh(_bS,function(_bW){return E(_bV);}));},_bX=new T(function(){return unCStr("ENQ");}),_bY=function(_bZ){var _c0=new T(function(){return B(A1(_bZ,5));});return new T1(1,_bh(_bX,function(_c1){return E(_c0);}));},_c2=new T(function(){return unCStr("ACK");}),_c3=function(_c4){var _c5=new T(function(){return B(A1(_c4,6));});return new T1(1,_bh(_c2,function(_c6){return E(_c5);}));},_c7=new T(function(){return unCStr("BEL");}),_c8=function(_c9){var _ca=new T(function(){return B(A1(_c9,7));});return new T1(1,_bh(_c7,function(_cb){return E(_ca);}));},_cc=new T(function(){return unCStr("BS");}),_cd=function(_ce){var _cf=new T(function(){return B(A1(_ce,8));});return new T1(1,_bh(_cc,function(_cg){return E(_cf);}));},_ch=new T(function(){return unCStr("HT");}),_ci=function(_cj){var _ck=new T(function(){return B(A1(_cj,9));});return new T1(1,_bh(_ch,function(_cl){return E(_ck);}));},_cm=new T(function(){return unCStr("LF");}),_cn=function(_co){var _cp=new T(function(){return B(A1(_co,10));});return new T1(1,_bh(_cm,function(_cq){return E(_cp);}));},_cr=new T(function(){return unCStr("VT");}),_cs=function(_ct){var _cu=new T(function(){return B(A1(_ct,11));});return new T1(1,_bh(_cr,function(_cv){return E(_cu);}));},_cw=new T(function(){return unCStr("FF");}),_cx=function(_cy){var _cz=new T(function(){return B(A1(_cy,12));});return new T1(1,_bh(_cw,function(_cA){return E(_cz);}));},_cB=new T(function(){return unCStr("CR");}),_cC=function(_cD){var _cE=new T(function(){return B(A1(_cD,13));});return new T1(1,_bh(_cB,function(_cF){return E(_cE);}));},_cG=new T(function(){return unCStr("SI");}),_cH=function(_cI){var _cJ=new T(function(){return B(A1(_cI,15));});return new T1(1,_bh(_cG,function(_cK){return E(_cJ);}));},_cL=new T(function(){return unCStr("DLE");}),_cM=function(_cN){var _cO=new T(function(){return B(A1(_cN,16));});return new T1(1,_bh(_cL,function(_cP){return E(_cO);}));},_cQ=new T(function(){return unCStr("DC1");}),_cR=function(_cS){var _cT=new T(function(){return B(A1(_cS,17));});return new T1(1,_bh(_cQ,function(_cU){return E(_cT);}));},_cV=new T(function(){return unCStr("DC2");}),_cW=function(_cX){var _cY=new T(function(){return B(A1(_cX,18));});return new T1(1,_bh(_cV,function(_cZ){return E(_cY);}));},_d0=new T(function(){return unCStr("DC3");}),_d1=function(_d2){var _d3=new T(function(){return B(A1(_d2,19));});return new T1(1,_bh(_d0,function(_d4){return E(_d3);}));},_d5=new T(function(){return unCStr("DC4");}),_d6=function(_d7){var _d8=new T(function(){return B(A1(_d7,20));});return new T1(1,_bh(_d5,function(_d9){return E(_d8);}));},_da=new T(function(){return unCStr("NAK");}),_db=function(_dc){var _dd=new T(function(){return B(A1(_dc,21));});return new T1(1,_bh(_da,function(_de){return E(_dd);}));},_df=new T(function(){return unCStr("SYN");}),_dg=function(_dh){var _di=new T(function(){return B(A1(_dh,22));});return new T1(1,_bh(_df,function(_dj){return E(_di);}));},_dk=new T(function(){return unCStr("ETB");}),_dl=function(_dm){var _dn=new T(function(){return B(A1(_dm,23));});return new T1(1,_bh(_dk,function(_do){return E(_dn);}));},_dp=new T(function(){return unCStr("CAN");}),_dq=function(_dr){var _ds=new T(function(){return B(A1(_dr,24));});return new T1(1,_bh(_dp,function(_dt){return E(_ds);}));},_du=new T(function(){return unCStr("EM");}),_dv=function(_dw){var _dx=new T(function(){return B(A1(_dw,25));});return new T1(1,_bh(_du,function(_dy){return E(_dx);}));},_dz=new T(function(){return unCStr("SUB");}),_dA=function(_dB){var _dC=new T(function(){return B(A1(_dB,26));});return new T1(1,_bh(_dz,function(_dD){return E(_dC);}));},_dE=new T(function(){return unCStr("ESC");}),_dF=function(_dG){var _dH=new T(function(){return B(A1(_dG,27));});return new T1(1,_bh(_dE,function(_dI){return E(_dH);}));},_dJ=new T(function(){return unCStr("FS");}),_dK=function(_dL){var _dM=new T(function(){return B(A1(_dL,28));});return new T1(1,_bh(_dJ,function(_dN){return E(_dM);}));},_dO=new T(function(){return unCStr("GS");}),_dP=function(_dQ){var _dR=new T(function(){return B(A1(_dQ,29));});return new T1(1,_bh(_dO,function(_dS){return E(_dR);}));},_dT=new T(function(){return unCStr("RS");}),_dU=function(_dV){var _dW=new T(function(){return B(A1(_dV,30));});return new T1(1,_bh(_dT,function(_dX){return E(_dW);}));},_dY=new T(function(){return unCStr("US");}),_dZ=function(_e0){var _e1=new T(function(){return B(A1(_e0,31));});return new T1(1,_bh(_dY,function(_e2){return E(_e1);}));},_e3=new T(function(){return unCStr("SP");}),_e4=function(_e5){var _e6=new T(function(){return B(A1(_e5,32));});return new T1(1,_bh(_e3,function(_e7){return E(_e6);}));},_e8=new T(function(){return unCStr("DEL");}),_e9=function(_ea){var _eb=new T(function(){return B(A1(_ea,127));});return new T1(1,_bh(_e8,function(_ec){return E(_eb);}));},_ed=new T(function(){return _b9(new T2(1,function(_ee){return new T1(1,_7i(_bz,_bu,_ee));},new T2(1,_bE,new T2(1,_bJ,new T2(1,_bO,new T2(1,_bT,new T2(1,_bY,new T2(1,_c3,new T2(1,_c8,new T2(1,_cd,new T2(1,_ci,new T2(1,_cn,new T2(1,_cs,new T2(1,_cx,new T2(1,_cC,new T2(1,_cH,new T2(1,_cM,new T2(1,_cR,new T2(1,_cW,new T2(1,_d1,new T2(1,_d6,new T2(1,_db,new T2(1,_dg,new T2(1,_dl,new T2(1,_dq,new T2(1,_dv,new T2(1,_dA,new T2(1,_dF,new T2(1,_dK,new T2(1,_dP,new T2(1,_dU,new T2(1,_dZ,new T2(1,_e4,new T2(1,_e9,__Z))))))))))))))))))))))))))))))))));}),_ef=function(_eg){var _eh=new T(function(){return B(A1(_eg,7));}),_ei=new T(function(){return B(A1(_eg,8));}),_ej=new T(function(){return B(A1(_eg,9));}),_ek=new T(function(){return B(A1(_eg,10));}),_el=new T(function(){return B(A1(_eg,11));}),_em=new T(function(){return B(A1(_eg,12));}),_en=new T(function(){return B(A1(_eg,13));}),_eo=new T(function(){return B(A1(_eg,92));}),_ep=new T(function(){return B(A1(_eg,39));}),_eq=new T(function(){return B(A1(_eg,34));}),_er=new T(function(){var _es=function(_et){var _eu=new T(function(){return _4V(E(_et));}),_ev=function(_ew){var _ex=_9T(_eu,_ew);if(!_aZ(_ex,new T1(0,1114111))){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_eg,new T(function(){var _ey=_aW(_ex);if(_ey>>>0>1114111){return _aU(_ey);}else{return _ey;}}));}) : (++C,A1(_eg,new T(function(){var _ey=_aW(_ex);if(_ey>>>0>1114111){return _aU(_ey);}else{return _ey;}})));}};return new T1(1,_7X(_et,_ev));},_ez=new T(function(){var _eA=new T(function(){return B(A1(_eg,31));}),_eB=new T(function(){return B(A1(_eg,30));}),_eC=new T(function(){return B(A1(_eg,29));}),_eD=new T(function(){return B(A1(_eg,28));}),_eE=new T(function(){return B(A1(_eg,27));}),_eF=new T(function(){return B(A1(_eg,26));}),_eG=new T(function(){return B(A1(_eg,25));}),_eH=new T(function(){return B(A1(_eg,24));}),_eI=new T(function(){return B(A1(_eg,23));}),_eJ=new T(function(){return B(A1(_eg,22));}),_eK=new T(function(){return B(A1(_eg,21));}),_eL=new T(function(){return B(A1(_eg,20));}),_eM=new T(function(){return B(A1(_eg,19));}),_eN=new T(function(){return B(A1(_eg,18));}),_eO=new T(function(){return B(A1(_eg,17));}),_eP=new T(function(){return B(A1(_eg,16));}),_eQ=new T(function(){return B(A1(_eg,15));}),_eR=new T(function(){return B(A1(_eg,14));}),_eS=new T(function(){return B(A1(_eg,6));}),_eT=new T(function(){return B(A1(_eg,5));}),_eU=new T(function(){return B(A1(_eg,4));}),_eV=new T(function(){return B(A1(_eg,3));}),_eW=new T(function(){return B(A1(_eg,2));}),_eX=new T(function(){return B(A1(_eg,1));}),_eY=new T(function(){return B(A1(_eg,0));}),_eZ=function(_f0){switch(E(_f0)){case 64:return E(_eY);case 65:return E(_eX);case 66:return E(_eW);case 67:return E(_eV);case 68:return E(_eU);case 69:return E(_eT);case 70:return E(_eS);case 71:return E(_eh);case 72:return E(_ei);case 73:return E(_ej);case 74:return E(_ek);case 75:return E(_el);case 76:return E(_em);case 77:return E(_en);case 78:return E(_eR);case 79:return E(_eQ);case 80:return E(_eP);case 81:return E(_eO);case 82:return E(_eN);case 83:return E(_eM);case 84:return E(_eL);case 85:return E(_eK);case 86:return E(_eJ);case 87:return E(_eI);case 88:return E(_eH);case 89:return E(_eG);case 90:return E(_eF);case 91:return E(_eE);case 92:return E(_eD);case 93:return E(_eC);case 94:return E(_eB);case 95:return E(_eA);default:return new T0(2);}};return _6a(new T1(0,function(_f1){return (E(_f1)==94)?E(new T1(0,_eZ)):new T0(2);}),new T(function(){return B(A1(_ed,_eg));}));});return _6a(new T1(1,_7i(_aH,_aJ,_es)),_ez);});return _6a(new T1(0,function(_f2){switch(E(_f2)){case 34:return E(_eq);case 39:return E(_ep);case 92:return E(_eo);case 97:return E(_eh);case 98:return E(_ei);case 102:return E(_em);case 110:return E(_ek);case 114:return E(_en);case 116:return E(_ej);case 118:return E(_el);default:return new T0(2);}}),_er);},_f3=function(_f4){return C > 19 ? new F(function(){return A1(_f4,0);}) : (++C,A1(_f4,0));},_f5=function(_f6){var _f7=E(_f6);if(!_f7._){return _f3;}else{var _f8=E(_f7.a),_f9=_f8>>>0,_fa=new T(function(){return _f5(_f7.b);});if(_f9>887){var _fb=u_iswspace(_f8);if(!E(_fb)){return _f3;}else{var _fc=function(_fd){var _fe=new T(function(){return B(A1(_fa,_fd));});return new T1(0,function(_ff){return E(_fe);});};return _fc;}}else{if(_f9==32){var _fg=function(_fh){var _fi=new T(function(){return B(A1(_fa,_fh));});return new T1(0,function(_fj){return E(_fi);});};return _fg;}else{if(_f9-9>>>0>4){if(_f9==160){var _fk=function(_fl){var _fm=new T(function(){return B(A1(_fa,_fl));});return new T1(0,function(_fn){return E(_fm);});};return _fk;}else{return _f3;}}else{var _fo=function(_fp){var _fq=new T(function(){return B(A1(_fa,_fp));});return new T1(0,function(_fr){return E(_fq);});};return _fo;}}}}},_fs=function(_ft){var _fu=new T(function(){return B(_fs(_ft));}),_fv=function(_fw){return (E(_fw)==92)?E(_fu):new T0(2);},_fx=function(_fy){return E(new T1(0,_fv));},_fz=new T1(1,function(_fA){return C > 19 ? new F(function(){return A2(_f5,_fA,_fx);}) : (++C,A2(_f5,_fA,_fx));}),_fB=new T(function(){return B(_ef(function(_fC){return C > 19 ? new F(function(){return A1(_ft,new T2(0,_fC,true));}) : (++C,A1(_ft,new T2(0,_fC,true)));}));}),_fD=function(_fE){var _fF=E(_fE);if(_fF==38){return E(_fu);}else{var _fG=_fF>>>0;if(_fG>887){var _fH=u_iswspace(_fF);return (E(_fH)==0)?new T0(2):E(_fz);}else{return (_fG==32)?E(_fz):(_fG-9>>>0>4)?(_fG==160)?E(_fz):new T0(2):E(_fz);}}};return _6a(new T1(0,function(_fI){return (E(_fI)==92)?E(new T1(0,_fD)):new T0(2);}),new T1(0,function(_fJ){var _fK=E(_fJ);if(_fK==92){return E(_fB);}else{return C > 19 ? new F(function(){return A1(_ft,new T2(0,_fK,false));}) : (++C,A1(_ft,new T2(0,_fK,false)));}}));},_fL=function(_fM,_fN){var _fO=new T(function(){return B(A1(_fN,new T1(1,new T(function(){return B(A1(_fM,__Z));}))));}),_fP=function(_fQ){var _fR=E(_fQ),_fS=E(_fR.a);if(_fS==34){if(!E(_fR.b)){return E(_fO);}else{return C > 19 ? new F(function(){return _fL(function(_fT){return C > 19 ? new F(function(){return A1(_fM,new T2(1,_fS,_fT));}) : (++C,A1(_fM,new T2(1,_fS,_fT)));},_fN);}) : (++C,_fL(function(_fT){return C > 19 ? new F(function(){return A1(_fM,new T2(1,_fS,_fT));}) : (++C,A1(_fM,new T2(1,_fS,_fT)));},_fN));}}else{return C > 19 ? new F(function(){return _fL(function(_fU){return C > 19 ? new F(function(){return A1(_fM,new T2(1,_fS,_fU));}) : (++C,A1(_fM,new T2(1,_fS,_fU)));},_fN);}) : (++C,_fL(function(_fU){return C > 19 ? new F(function(){return A1(_fM,new T2(1,_fS,_fU));}) : (++C,A1(_fM,new T2(1,_fS,_fU)));},_fN));}};return C > 19 ? new F(function(){return _fs(_fP);}) : (++C,_fs(_fP));},_fV=new T(function(){return unCStr("_\'");}),_fW=function(_fX){var _fY=u_iswalnum(_fX);if(!E(_fY)){return _au(_6L,_fX,_fV);}else{return true;}},_fZ=function(_g0){return _fW(E(_g0));},_g1=new T(function(){return unCStr(",;()[]{}`");}),_g2=new T(function(){return unCStr("=>");}),_g3=new T(function(){return unCStr("~");}),_g4=new T(function(){return unCStr("@");}),_g5=new T(function(){return unCStr("->");}),_g6=new T(function(){return unCStr("<-");}),_g7=new T(function(){return unCStr("|");}),_g8=new T(function(){return unCStr("\\");}),_g9=new T(function(){return unCStr("=");}),_ga=new T(function(){return unCStr("::");}),_gb=new T(function(){return unCStr("..");}),_gc=function(_gd){var _ge=new T(function(){return B(A1(_gd,new T0(6)));}),_gf=new T(function(){var _gg=new T(function(){var _gh=function(_gi){var _gj=new T(function(){return B(A1(_gd,new T1(0,_gi)));});return new T1(0,function(_gk){return (E(_gk)==39)?E(_gj):new T0(2);});};return B(_ef(_gh));}),_gl=function(_gm){var _gn=E(_gm);switch(_gn){case 39:return new T0(2);case 92:return E(_gg);default:var _go=new T(function(){return B(A1(_gd,new T1(0,_gn)));});return new T1(0,function(_gp){return (E(_gp)==39)?E(_go):new T0(2);});}},_gq=new T(function(){var _gr=new T(function(){return B(_fL(_1V,_gd));}),_gs=new T(function(){var _gt=new T(function(){var _gu=new T(function(){var _gv=function(_gw){var _gx=E(_gw),_gy=u_iswalpha(_gx);return (E(_gy)==0)?(_gx==95)?new T1(1,_7I(_fZ,function(_gz){return C > 19 ? new F(function(){return A1(_gd,new T1(3,new T2(1,_gx,_gz)));}) : (++C,A1(_gd,new T1(3,new T2(1,_gx,_gz))));})):new T0(2):new T1(1,_7I(_fZ,function(_gA){return C > 19 ? new F(function(){return A1(_gd,new T1(3,new T2(1,_gx,_gA)));}) : (++C,A1(_gd,new T1(3,new T2(1,_gx,_gA))));}));};return _6a(new T1(0,_gv),new T(function(){return new T1(1,_7i(_8Q,_aq,_gd));}));}),_gB=function(_gC){return (!_au(_6L,_gC,_az))?new T0(2):new T1(1,_7I(_aA,function(_gD){var _gE=new T2(1,_gC,_gD);if(!_au(new T2(0,_6Q,_6V),_gE,new T2(1,_gb,new T2(1,_ga,new T2(1,_g9,new T2(1,_g8,new T2(1,_g7,new T2(1,_g6,new T2(1,_g5,new T2(1,_g4,new T2(1,_g3,new T2(1,_g2,__Z)))))))))))){return C > 19 ? new F(function(){return A1(_gd,new T1(4,_gE));}) : (++C,A1(_gd,new T1(4,_gE)));}else{return C > 19 ? new F(function(){return A1(_gd,new T1(2,_gE));}) : (++C,A1(_gd,new T1(2,_gE)));}}));};return _6a(new T1(0,_gB),_gu);});return _6a(new T1(0,function(_gF){if(!_au(_6L,_gF,_g1)){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_gd,new T1(2,new T2(1,_gF,__Z)));}) : (++C,A1(_gd,new T1(2,new T2(1,_gF,__Z))));}}),_gt);});return _6a(new T1(0,function(_gG){return (E(_gG)==34)?E(_gr):new T0(2);}),_gs);});return _6a(new T1(0,function(_gH){return (E(_gH)==39)?E(new T1(0,_gl)):new T0(2);}),_gq);});return _6a(new T1(1,function(_gI){return (E(_gI)._==0)?E(_ge):new T0(2);}),_gf);},_gJ=function(_gK,_gL){var _gM=new T(function(){var _gN=new T(function(){var _gO=function(_gP){var _gQ=new T(function(){var _gR=new T(function(){return B(A1(_gL,_gP));});return B(_gc(function(_gS){var _gT=E(_gS);return (_gT._==2)?(!_6G(_gT.a,_6F))?new T0(2):E(_gR):new T0(2);}));}),_gU=function(_gV){return E(_gQ);};return new T1(1,function(_gW){return C > 19 ? new F(function(){return A2(_f5,_gW,_gU);}) : (++C,A2(_f5,_gW,_gU));});};return B(A2(_gK,0,_gO));});return B(_gc(function(_gX){var _gY=E(_gX);return (_gY._==2)?(!_6G(_gY.a,_6E))?new T0(2):E(_gN):new T0(2);}));}),_gZ=function(_h0){return E(_gM);};return function(_h1){return C > 19 ? new F(function(){return A2(_f5,_h1,_gZ);}) : (++C,A2(_f5,_h1,_gZ));};},_h2=function(_h3,_h4){var _h5=function(_h6){var _h7=new T(function(){return B(A1(_h3,_h6));}),_h8=function(_h9){return _6a(B(A1(_h7,_h9)),new T(function(){return new T1(1,_gJ(_h5,_h9));}));};return _h8;},_ha=new T(function(){return B(A1(_h3,_h4));}),_hb=function(_hc){return _6a(B(A1(_ha,_hc)),new T(function(){return new T1(1,_gJ(_h5,_hc));}));};return _hb;},_hd=function(_he,_hf){var _hg=function(_hh,_hi){var _hj=function(_hk){return C > 19 ? new F(function(){return A1(_hi,new T(function(){return  -E(_hk);}));}) : (++C,A1(_hi,new T(function(){return  -E(_hk);})));},_hl=new T(function(){return B(_gc(function(_hm){return C > 19 ? new F(function(){return A3(_he,_hm,_hh,_hj);}) : (++C,A3(_he,_hm,_hh,_hj));}));}),_hn=function(_ho){return E(_hl);},_hp=function(_hq){return C > 19 ? new F(function(){return A2(_f5,_hq,_hn);}) : (++C,A2(_f5,_hq,_hn));},_hr=new T(function(){return B(_gc(function(_hs){var _ht=E(_hs);if(_ht._==4){var _hu=E(_ht.a);if(!_hu._){return C > 19 ? new F(function(){return A3(_he,_ht,_hh,_hi);}) : (++C,A3(_he,_ht,_hh,_hi));}else{if(E(_hu.a)==45){if(!E(_hu.b)._){return E(new T1(1,_hp));}else{return C > 19 ? new F(function(){return A3(_he,_ht,_hh,_hi);}) : (++C,A3(_he,_ht,_hh,_hi));}}else{return C > 19 ? new F(function(){return A3(_he,_ht,_hh,_hi);}) : (++C,A3(_he,_ht,_hh,_hi));}}}else{return C > 19 ? new F(function(){return A3(_he,_ht,_hh,_hi);}) : (++C,A3(_he,_ht,_hh,_hi));}}));}),_hv=function(_hw){return E(_hr);};return new T1(1,function(_hx){return C > 19 ? new F(function(){return A2(_f5,_hx,_hv);}) : (++C,A2(_f5,_hx,_hv));});};return _h2(_hg,_hf);},_hy=new T(function(){return 1/0;}),_hz=function(_hA,_hB){return C > 19 ? new F(function(){return A1(_hB,_hy);}) : (++C,A1(_hB,_hy));},_hC=new T(function(){return 0/0;}),_hD=function(_hE,_hF){return C > 19 ? new F(function(){return A1(_hF,_hC);}) : (++C,A1(_hF,_hC));},_hG=new T(function(){return unCStr("NaN");}),_hH=new T(function(){return unCStr("Infinity");}),_hI=new T(function(){return unCStr("base");}),_hJ=new T(function(){return unCStr("GHC.Exception");}),_hK=new T(function(){return unCStr("ArithException");}),_hL=function(_hM){return E(new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_hI,_hJ,_hK),__Z,__Z));},_hN=new T(function(){return unCStr("Ratio has zero denominator");}),_hO=new T(function(){return unCStr("denormal");}),_hP=new T(function(){return unCStr("divide by zero");}),_hQ=new T(function(){return unCStr("loss of precision");}),_hR=new T(function(){return unCStr("arithmetic underflow");}),_hS=new T(function(){return unCStr("arithmetic overflow");}),_hT=function(_hU,_hV){switch(E(_hU)){case 0:return _x(_hS,_hV);case 1:return _x(_hR,_hV);case 2:return _x(_hQ,_hV);case 3:return _x(_hP,_hV);case 4:return _x(_hO,_hV);default:return _x(_hN,_hV);}},_hW=function(_hX){return _hT(_hX,__Z);},_hY=new T(function(){return new T5(0,_hL,new T3(0,function(_hZ,_i0,_i1){return _hT(_i0,_i1);},_hW,function(_i2,_i3){return _1q(_hT,_i2,_i3);}),_i4,function(_i5){var _i6=E(_i5);return _m(_k(_i6.a),_hL,_i6.b);},_hW);}),_i4=function(_2W){return new T2(0,_hY,_2W);},_i7=new T(function(){return die(new T(function(){return _i4(3);}));}),_i8=function(_i9,_ia){var _ib=E(_i9);if(!_ib._){var _ic=_ib.a,_id=E(_ia);return (_id._==0)?_ic==_id.a:(I_compareInt(_id.a,_ic)==0)?true:false;}else{var _ie=_ib.a,_if=E(_ia);return (_if._==0)?(I_compareInt(_ie,_if.a)==0)?true:false:(I_compare(_ie,_if.a)==0)?true:false;}},_ig=new T1(0,0),_ih=function(_ii,_ij){while(1){var _ik=E(_ii);if(!_ik._){var _il=E(_ik.a);if(_il==(-2147483648)){_ii=new T1(1,I_fromInt(-2147483648));continue;}else{var _im=E(_ij);if(!_im._){return new T1(0,_il%_im.a);}else{_ii=new T1(1,I_fromInt(_il));_ij=_im;continue;}}}else{var _in=_ik.a,_io=E(_ij);return (_io._==0)?new T1(1,I_rem(_in,I_fromInt(_io.a))):new T1(1,I_rem(_in,_io.a));}}},_ip=function(_iq,_ir){if(!_i8(_ir,_ig)){return _ih(_iq,_ir);}else{return E(_i7);}},_is=function(_it,_iu){while(1){if(!_i8(_iu,_ig)){var _iv=_iu,_iw=_ip(_it,_iu);_it=_iv;_iu=_iw;continue;}else{return E(_it);}}},_ix=function(_iy){var _iz=E(_iy);if(!_iz._){var _iA=E(_iz.a);return (_iA==(-2147483648))?E(_96):(_iA<0)?new T1(0, -_iA):_iz;}else{var _iB=_iz.a;return (I_compareInt(_iB,0)>=0)?_iz:new T1(1,I_negate(_iB));}},_iC=function(_iD,_iE){while(1){var _iF=E(_iD);if(!_iF._){var _iG=E(_iF.a);if(_iG==(-2147483648)){_iD=new T1(1,I_fromInt(-2147483648));continue;}else{var _iH=E(_iE);if(!_iH._){return new T1(0,quot(_iG,_iH.a));}else{_iD=new T1(1,I_fromInt(_iG));_iE=_iH;continue;}}}else{var _iI=_iF.a,_iJ=E(_iE);return (_iJ._==0)?new T1(0,I_toInt(I_quot(_iI,I_fromInt(_iJ.a)))):new T1(1,I_quot(_iI,_iJ.a));}}},_iK=new T(function(){return die(new T(function(){return _i4(5);}));}),_iL=function(_iM,_iN){if(!_i8(_iN,_ig)){var _iO=_is(_ix(_iM),_ix(_iN));return (!_i8(_iO,_ig))?new T2(0,_iC(_iM,_iO),_iC(_iN,_iO)):E(_i7);}else{return E(_iK);}},_iP=new T1(0,1),_iQ=new T(function(){return err(new T(function(){return unCStr("Negative exponent");}));}),_iR=new T1(0,2),_iS=new T(function(){return _i8(_iR,_ig);}),_iT=function(_iU,_iV){while(1){var _iW=E(_iU);if(!_iW._){var _iX=_iW.a,_iY=E(_iV);if(!_iY._){var _iZ=_iY.a,_j0=subC(_iX,_iZ);if(!E(_j0.b)){return new T1(0,_j0.a);}else{_iU=new T1(1,I_fromInt(_iX));_iV=new T1(1,I_fromInt(_iZ));continue;}}else{_iU=new T1(1,I_fromInt(_iX));_iV=_iY;continue;}}else{var _j1=E(_iV);if(!_j1._){_iU=_iW;_iV=new T1(1,I_fromInt(_j1.a));continue;}else{return new T1(1,I_sub(_iW.a,_j1.a));}}}},_j2=function(_j3,_j4,_j5){while(1){if(!E(_iS)){if(!_i8(_ih(_j4,_iR),_ig)){if(!_i8(_j4,_iP)){var _j6=_9o(_j3,_j3),_j7=_iC(_iT(_j4,_iP),_iR),_j8=_9o(_j3,_j5);_j3=_j6;_j4=_j7;_j5=_j8;continue;}else{return _9o(_j3,_j5);}}else{var _j6=_9o(_j3,_j3),_j7=_iC(_j4,_iR);_j3=_j6;_j4=_j7;continue;}}else{return E(_i7);}}},_j9=function(_ja,_jb){while(1){if(!E(_iS)){if(!_i8(_ih(_jb,_iR),_ig)){if(!_i8(_jb,_iP)){return _j2(_9o(_ja,_ja),_iC(_iT(_jb,_iP),_iR),_ja);}else{return E(_ja);}}else{var _jc=_9o(_ja,_ja),_jd=_iC(_jb,_iR);_ja=_jc;_jb=_jd;continue;}}else{return E(_i7);}}},_je=function(_jf,_jg){var _jh=E(_jf);if(!_jh._){var _ji=_jh.a,_jj=E(_jg);return (_jj._==0)?_ji<_jj.a:I_compareInt(_jj.a,_ji)>0;}else{var _jk=_jh.a,_jl=E(_jg);return (_jl._==0)?I_compareInt(_jk,_jl.a)<0:I_compare(_jk,_jl.a)<0;}},_jm=function(_jn,_jo){if(!_je(_jo,_ig)){if(!_i8(_jo,_ig)){return _j9(_jn,_jo);}else{return E(_iP);}}else{return E(_iQ);}},_jp=new T1(0,1),_jq=new T1(0,0),_jr=new T1(0,-1),_js=function(_jt){var _ju=E(_jt);if(!_ju._){var _jv=_ju.a;return (_jv>=0)?(E(_jv)==0)?E(_jq):E(_8W):E(_jr);}else{var _jw=I_compareInt(_ju.a,0);return (_jw<=0)?(E(_jw)==0)?E(_jq):E(_jr):E(_8W);}},_jx=function(_jy,_jz,_jA){while(1){var _jB=E(_jA);if(!_jB._){if(!_je(_jy,_9B)){return new T2(0,_9o(_jz,B(_jm(_9b,_jy))),_iP);}else{var _jC=B(_jm(_9b,_97(_jy)));return _iL(_9o(_jz,_js(_jC)),_ix(_jC));}}else{var _jD=_iT(_jy,_jp),_jE=_8X(_9o(_jz,_9b),_4V(E(_jB.a)));_jy=_jD;_jz=_jE;_jA=_jB.b;continue;}}},_jF=function(_jG,_jH){var _jI=E(_jG);if(!_jI._){var _jJ=_jI.a,_jK=E(_jH);return (_jK._==0)?_jJ>=_jK.a:I_compareInt(_jK.a,_jJ)<=0;}else{var _jL=_jI.a,_jM=E(_jH);return (_jM._==0)?I_compareInt(_jL,_jM.a)>=0:I_compare(_jL,_jM.a)>=0;}},_jN=function(_jO){var _jP=E(_jO);if(!_jP._){var _jQ=_jP.b;return _iL(_9o(_9C(new T(function(){return _4V(E(_jP.a));}),new T(function(){return _9c(_jQ,0);},1),_9h(_9l,_jQ)),_jp),_jp);}else{var _jR=_jP.a,_jS=_jP.c,_jT=E(_jP.b);if(!_jT._){var _jU=E(_jS);if(!_jU._){return _iL(_9o(_9T(_9b,_jR),_jp),_jp);}else{var _jV=_jU.a;if(!_jF(_jV,_9B)){var _jW=B(_jm(_9b,_97(_jV)));return _iL(_9o(_9T(_9b,_jR),_js(_jW)),_ix(_jW));}else{return _iL(_9o(_9o(_9T(_9b,_jR),B(_jm(_9b,_jV))),_jp),_jp);}}}else{var _jX=_jT.a,_jY=E(_jS);if(!_jY._){return _jx(_9B,_9T(_9b,_jR),_jX);}else{return _jx(_jY.a,_9T(_9b,_jR),_jX);}}}},_jZ=function(_k0,_k1){while(1){var _k2=E(_k1);if(!_k2._){return __Z;}else{if(!B(A1(_k0,_k2.a))){return _k2;}else{_k1=_k2.b;continue;}}}},_k3=function(_k4,_k5){var _k6=E(_k4);if(!_k6._){var _k7=_k6.a,_k8=E(_k5);return (_k8._==0)?_k7>_k8.a:I_compareInt(_k8.a,_k7)<0;}else{var _k9=_k6.a,_ka=E(_k5);return (_ka._==0)?I_compareInt(_k9,_ka.a)>0:I_compare(_k9,_ka.a)>0;}},_kb=function(_kc,_kd){return E(_kc)==E(_kd);},_ke=function(_kf){return _kb(0,_kf);},_kg=new T1(1,new T2(0,E(_9B),E(_iP))),_kh=function(_ki,_kj,_kk){var _kl=E(_kk);if(!_kl._){return new T1(1,new T(function(){var _km=_jN(_kl);return new T2(0,E(_km.a),E(_km.b));}));}else{var _kn=E(_kl.c);if(!_kn._){return new T1(1,new T(function(){var _ko=_jN(_kl);return new T2(0,E(_ko.a),E(_ko.b));}));}else{var _kp=_kn.a;if(!_k3(_kp,new T1(0,2147483647))){if(!_je(_kp,new T1(0,-2147483648))){var _kq=function(_kr){var _ks=_kr+_aW(_kp)|0;return (_ks<=(E(_kj)+3|0))?(_ks>=(E(_ki)-3|0))?new T1(1,new T(function(){var _kt=_jN(_kl);return new T2(0,E(_kt.a),E(_kt.b));})):E(_kg):__Z;},_ku=_jZ(_ke,_kl.a);if(!_ku._){var _kv=E(_kl.b);if(!_kv._){return E(_kg);}else{var _kw=_2X(_ke,_kv.a);if(!E(_kw.b)._){return E(_kg);}else{return _kq( -_9c(_kw.a,0));}}}else{return _kq(_9c(_ku,0));}}else{return __Z;}}else{return __Z;}}}},_kx=function(_ky,_kz){return new T0(2);},_kA=new T1(0,1),_kB=function(_kC,_kD){var _kE=E(_kC);if(!_kE._){var _kF=_kE.a,_kG=E(_kD);if(!_kG._){var _kH=_kG.a;return (_kF!=_kH)?(_kF>_kH)?2:0:1;}else{var _kI=I_compareInt(_kG.a,_kF);return (_kI<=0)?(_kI>=0)?1:2:0;}}else{var _kJ=_kE.a,_kK=E(_kD);if(!_kK._){var _kL=I_compareInt(_kJ,_kK.a);return (_kL>=0)?(_kL<=0)?1:2:0;}else{var _kM=I_compare(_kJ,_kK.a);return (_kM>=0)?(_kM<=0)?1:2:0;}}},_kN=function(_kO,_kP){var _kQ=E(_kO);return (_kQ._==0)?_kQ.a*Math.pow(2,_kP):I_toNumber(_kQ.a)*Math.pow(2,_kP);},_kR=function(_kS,_kT){while(1){var _kU=E(_kS);if(!_kU._){var _kV=E(_kU.a);if(_kV==(-2147483648)){_kS=new T1(1,I_fromInt(-2147483648));continue;}else{var _kW=E(_kT);if(!_kW._){var _kX=_kW.a;return new T2(0,new T1(0,quot(_kV,_kX)),new T1(0,_kV%_kX));}else{_kS=new T1(1,I_fromInt(_kV));_kT=_kW;continue;}}}else{var _kY=E(_kT);if(!_kY._){_kS=_kU;_kT=new T1(1,I_fromInt(_kY.a));continue;}else{var _kZ=I_quotRem(_kU.a,_kY.a);return new T2(0,new T1(1,_kZ.a),new T1(1,_kZ.b));}}}},_l0=new T1(0,0),_l1=function(_l2,_l3,_l4){if(!_i8(_l4,_l0)){var _l5=_kR(_l3,_l4),_l6=_l5.a;switch(_kB(_5a(_l5.b,1),_l4)){case 0:return _kN(_l6,_l2);case 1:if(!(_aW(_l6)&1)){return _kN(_l6,_l2);}else{return _kN(_8X(_l6,_kA),_l2);}break;default:return _kN(_8X(_l6,_kA),_l2);}}else{return E(_i7);}},_l7=function(_l8){var _l9=function(_la,_lb){while(1){if(!_je(_la,_l8)){if(!_k3(_la,_l8)){if(!_i8(_la,_l8)){return C > 19 ? new F(function(){return _3i("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2");}) : (++C,_3i("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2"));}else{return E(_lb);}}else{return _lb-1|0;}}else{var _lc=_5a(_la,1),_ld=_lb+1|0;_la=_lc;_lb=_ld;continue;}}};return C > 19 ? new F(function(){return _l9(_8W,0);}) : (++C,_l9(_8W,0));},_le=function(_lf){var _lg=E(_lf);if(!_lg._){var _lh=_lg.a>>>0;if(!_lh){return -1;}else{var _li=function(_lj,_lk){while(1){if(_lj>=_lh){if(_lj<=_lh){if(_lj!=_lh){return C > 19 ? new F(function(){return _3i("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");}) : (++C,_3i("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2"));}else{return E(_lk);}}else{return _lk-1|0;}}else{var _ll=imul(_lj,2)>>>0,_lm=_lk+1|0;_lj=_ll;_lk=_lm;continue;}}};return C > 19 ? new F(function(){return _li(1,0);}) : (++C,_li(1,0));}}else{return C > 19 ? new F(function(){return _l7(_lg);}) : (++C,_l7(_lg));}},_ln=function(_lo){var _lp=E(_lo);if(!_lp._){var _lq=_lp.a>>>0;if(!_lq){return new T2(0,-1,0);}else{var _lr=function(_ls,_lt){while(1){if(_ls>=_lq){if(_ls<=_lq){if(_ls!=_lq){return C > 19 ? new F(function(){return _3i("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");}) : (++C,_3i("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2"));}else{return E(_lt);}}else{return _lt-1|0;}}else{var _lu=imul(_ls,2)>>>0,_lv=_lt+1|0;_ls=_lu;_lt=_lv;continue;}}};return new T2(0,B(_lr(1,0)),(_lq&_lq-1>>>0)>>>0&4294967295);}}else{var _lw=_lp.a;return new T2(0,B(_le(_lp)),I_compareInt(I_and(_lw,I_sub(_lw,I_fromInt(1))),0));}},_lx=function(_ly,_lz){while(1){var _lA=E(_ly);if(!_lA._){var _lB=_lA.a,_lC=E(_lz);if(!_lC._){return new T1(0,(_lB>>>0&_lC.a>>>0)>>>0&4294967295);}else{_ly=new T1(1,I_fromInt(_lB));_lz=_lC;continue;}}else{var _lD=E(_lz);if(!_lD._){_ly=_lA;_lz=new T1(1,I_fromInt(_lD.a));continue;}else{return new T1(1,I_and(_lA.a,_lD.a));}}}},_lE=function(_lF,_lG){var _lH=E(_lF);if(!_lH._){var _lI=(_lH.a>>>0&(2<<_lG>>>0)-1>>>0)>>>0,_lJ=1<<_lG>>>0;return (_lJ<=_lI)?(_lJ>=_lI)?1:2:0;}else{var _lK=_lx(_lH,_iT(_5a(new T1(0,2),_lG),_8W)),_lL=_5a(_8W,_lG);return (!_k3(_lL,_lK))?(!_je(_lL,_lK))?1:2:0;}},_lM=function(_lN,_lO){while(1){var _lP=E(_lN);if(!_lP._){_lN=new T1(1,I_fromInt(_lP.a));continue;}else{return new T1(1,I_shiftRight(_lP.a,_lO));}}},_lQ=function(_lR,_lS,_lT,_lU){var _lV=_ln(_lU),_lW=_lV.a;if(!E(_lV.b)){var _lX=B(_le(_lT));if(_lX<((_lW+_lR|0)-1|0)){var _lY=_lW+(_lR-_lS|0)|0;if(_lY>0){if(_lY>_lX){if(_lY<=(_lX+1|0)){if(!E(_ln(_lT).b)){return 0;}else{return _kN(_kA,_lR-_lS|0);}}else{return 0;}}else{var _lZ=_lM(_lT,_lY);switch(_lE(_lT,_lY-1|0)){case 0:return _kN(_lZ,_lR-_lS|0);case 1:if(!(_aW(_lZ)&1)){return _kN(_lZ,_lR-_lS|0);}else{return _kN(_8X(_lZ,_kA),_lR-_lS|0);}break;default:return _kN(_8X(_lZ,_kA),_lR-_lS|0);}}}else{return _kN(_lT,(_lR-_lS|0)-_lY|0);}}else{if(_lX>=_lS){var _m0=_lM(_lT,(_lX+1|0)-_lS|0);switch(_lE(_lT,_lX-_lS|0)){case 0:return _kN(_m0,((_lX-_lW|0)+1|0)-_lS|0);case 2:return _kN(_8X(_m0,_kA),((_lX-_lW|0)+1|0)-_lS|0);default:if(!(_aW(_m0)&1)){return _kN(_m0,((_lX-_lW|0)+1|0)-_lS|0);}else{return _kN(_8X(_m0,_kA),((_lX-_lW|0)+1|0)-_lS|0);}}}else{return _kN(_lT, -_lW);}}}else{var _m1=B(_le(_lT))-_lW|0,_m2=function(_m3){var _m4=function(_m5,_m6){if(!_aZ(_5a(_m6,_lS),_m5)){return _l1(_m3-_lS|0,_m5,_m6);}else{return _l1((_m3-_lS|0)+1|0,_m5,_5a(_m6,1));}};if(_m3>=_lS){if(_m3!=_lS){return _m4(_lT,new T(function(){return _5a(_lU,_m3-_lS|0);}));}else{return _m4(_lT,_lU);}}else{return _m4(new T(function(){return _5a(_lT,_lS-_m3|0);}),_lU);}};if(_lR>_m1){return C > 19 ? new F(function(){return _m2(_lR);}) : (++C,_m2(_lR));}else{return C > 19 ? new F(function(){return _m2(_m1);}) : (++C,_m2(_m1));}}},_m7=new T(function(){return 0/0;}),_m8=new T(function(){return -1/0;}),_m9=new T(function(){return 1/0;}),_ma=function(_mb,_mc){if(!_i8(_mc,_l0)){if(!_i8(_mb,_l0)){if(!_je(_mb,_l0)){return C > 19 ? new F(function(){return _lQ(-1021,53,_mb,_mc);}) : (++C,_lQ(-1021,53,_mb,_mc));}else{return  -B(_lQ(-1021,53,_97(_mb),_mc));}}else{return 0;}}else{return (!_i8(_mb,_l0))?(!_je(_mb,_l0))?E(_m9):E(_m8):E(_m7);}},_md=function(_me){var _mf=E(_me);switch(_mf._){case 3:var _mg=_mf.a;return (!_6G(_mg,_hH))?(!_6G(_mg,_hG))?_kx:_hD:_hz;case 5:var _mh=_kh(-1021,1024,_mf.a);if(!_mh._){return _hz;}else{var _mi=new T(function(){var _mj=E(_mh.a);return B(_ma(_mj.a,_mj.b));});return function(_mk,_ml){return C > 19 ? new F(function(){return A1(_ml,_mi);}) : (++C,A1(_ml,_mi));};}break;default:return _kx;}},_mm=function(_mn){var _mo=function(_mp){return E(new T2(3,_mn,_79));};return new T1(1,function(_mq){return C > 19 ? new F(function(){return A2(_f5,_mq,_mo);}) : (++C,A2(_f5,_mq,_mo));});},_mr=new T(function(){return B(A3(_hd,_md,0,_mm));}),_ms=function(_mt,_mu){while(1){var _mv=E(_mt);if(!_mv._){return E(_mu);}else{_mt=_mv.b;_mu=_mv.a;continue;}}},_mw=function(_mx){var _my=E(_mx);if(!_my._){return __Z;}else{var _mz=_my.a,_mA=new T(function(){if(E(_ms(_mz,_5P))==37){var _mB=_5Q(_5X(_mr,new T(function(){return _5M(_mz);})));if(!_mB._){return E(_68);}else{if(!E(_mB.b)._){return E(_mB.a)/100;}else{return E(_67);}}}else{var _mC=_5Q(_5X(_mr,_mz));if(!_mC._){return E(_68);}else{if(!E(_mC.b)._){return E(_mC.a);}else{return E(_67);}}}});return new T1(1,_mA);}},_mD=function(_mE){if(_mE!=0){if(_mE<=0){var _mF=1/(1+0.5* -_mE),_mG=_mF*_mF,_mH=_mG*_mF,_mI=_mH*_mF,_mJ=_mI*_mF,_mK=_mJ*_mF,_mL=_mK*_mF,_mM=_mL*_mF;return (_mE<0)?_mF*Math.exp( -(_mE*_mE)-1.26551223+1.00002368*_mF+0.37409196*_mG+9.678418e-2*_mH-0.18628806*_mI+0.27886807*_mJ-1.13520398*_mK+1.48851587*_mL-0.82215223*_mM+0.17087277*_mM*_mF)-1:1-_mF*Math.exp( -(_mE*_mE)-1.26551223+1.00002368*_mF+0.37409196*_mG+9.678418e-2*_mH-0.18628806*_mI+0.27886807*_mJ-1.13520398*_mK+1.48851587*_mL-0.82215223*_mM+0.17087277*_mM*_mF);}else{var _mN=1/(1+0.5*_mE),_mO=_mN*_mN,_mP=_mO*_mN,_mQ=_mP*_mN,_mR=_mQ*_mN,_mS=_mR*_mN,_mT=_mS*_mN,_mU=_mT*_mN;return (_mE<0)?_mN*Math.exp( -(_mE*_mE)-1.26551223+1.00002368*_mN+0.37409196*_mO+9.678418e-2*_mP-0.18628806*_mQ+0.27886807*_mR-1.13520398*_mS+1.48851587*_mT-0.82215223*_mU+0.17087277*_mU*_mN)-1:1-_mN*Math.exp( -(_mE*_mE)-1.26551223+1.00002368*_mN+0.37409196*_mO+9.678418e-2*_mP-0.18628806*_mQ+0.27886807*_mR-1.13520398*_mS+1.48851587*_mT-0.82215223*_mU+0.17087277*_mU*_mN);}}else{return (_mE<0)?Math.exp( -(_mE*_mE)-1.26551223+1.00002368+0.37409196+9.678418e-2-0.18628806+0.27886807-1.13520398+1.48851587-0.82215223+0.17087277)-1:1-Math.exp( -(_mE*_mE)-1.26551223+1.00002368+0.37409196+9.678418e-2-0.18628806+0.27886807-1.13520398+1.48851587-0.82215223+0.17087277);}},_mV=new T(function(){return unCStr("price");}),_mW=new T(function(){return unCStr("rho");}),_mX=new T(function(){return unCStr("vega");}),_mY=new T(function(){return unCStr("theta");}),_mZ=new T(function(){return unCStr("gamma");}),_n0=new T(function(){return unCStr("delta");}),_n1=function(_n2,_n3){var _n4=E(_n2);if(!_n4._){return __Z;}else{var _n5=E(_n3);return (_n5._==0)?__Z:new T2(1,new T2(0,_n4.a,_n5.a),new T(function(){return _n1(_n4.b,_n5.b);}));}},_n6=function(_n7){var _n8=new T(function(){return E(E(_n7).d);}),_n9=new T(function(){return E(E(_n7).c);}),_na=new T(function(){return Math.exp( -E(_n9)*E(_n8));}),_nb=new T(function(){return E(E(_n7).e);}),_nc=new T(function(){return E(E(E(_n7).b).b);}),_nd=new T(function(){return E(E(E(_n7).a).b);}),_ne=new T(function(){var _nf=E(_nb),_ng=E(_n8);return (Math.log(E(_nc)/E(_nd))+(E(_n9)+_nf*_nf/2)*_ng)/_nf/Math.sqrt(_ng);}),_nh=new T(function(){if(!E(E(_n7).g)){return 1;}else{return -1;}}),_ni=new T(function(){return 0.5*(1-_mD( -(E(_nh)*(E(_ne)-E(_nb)*Math.sqrt(E(_n8))))*0.7071067811865475));}),_nj=new T(function(){return Math.sqrt(E(_n8));}),_nk=new T(function(){var _nl=E(_ne);return Math.exp( -(_nl*_nl/2))/2.5066282746350725;});return _n1(new T2(1,_mV,new T2(1,_n0,new T2(1,_mZ,new T2(1,_mY,new T2(1,_mX,new T2(1,_mW,__Z)))))),new T2(1,new T(function(){var _nm=E(_nh);return (_nm*E(_nc)*0.5*(1-_mD( -(_nm*E(_ne))*0.7071067811865475))-_nm*E(_nd)*E(_na)*E(_ni))*E(E(_n7).f);}),new T2(1,new T(function(){if(!E(E(_n7).g)){return 0.5*(1-_mD( -E(_ne)*0.7071067811865475));}else{return 0.5*(1-_mD( -E(_ne)*0.7071067811865475))-1;}}),new T2(1,new T(function(){return E(_nk)/E(_nc)/E(_nb)/E(_nj);}),new T2(1,new T(function(){return ( -E(_nc)*E(_nk)*E(_nb)/2/E(_nj)-E(_nh)*E(_n9)*E(_nd)*E(_na)*E(_ni))/365;}),new T2(1,new T(function(){return E(_nc)*E(_nj)*E(_nk);}),new T2(1,new T(function(){return E(_nh)*E(_nd)*E(_n8)*E(_na)*E(_ni);}),__Z)))))));},_nn=function(_no,_){var _np=E(_no);if(!_np._){return E(_3k);}else{var _nq=_np.a,_nr=E(_np.b);if(!_nr._){return E(_3k);}else{var _ns=_nr.a,_nt=E(_nr.b);if(!_nt._){return E(_3k);}else{var _nu=_nt.a,_nv=E(_nt.b);if(!_nv._){return E(_3k);}else{var _nw=_nv.a,_nx=E(_nv.b);if(!_nx._){return E(_3k);}else{var _ny=_nx.a,_nz=E(_nx.b);if(!_nz._){return E(_3k);}else{var _nA=E(_nz.b);if(!_nA._){return E(_3k);}else{if(!E(_nA.b)._){var _nB=function(_){var _nC=_2v(E(_nq),"value"),_nD=_2v(E(_ns),"value"),_nE=_2v(E(_nu),"value"),_nF=_2v(E(_nw),"value"),_nG=_2v(E(_ny),"value"),_nH=_mw(new T1(1,new T(function(){var _nI=String(_nC);return fromJSStr(_nI);})));if(!_nH._){return 0;}else{var _nJ=_nH.a,_nK=_mw(new T1(1,new T(function(){var _nL=String(_nD);return fromJSStr(_nL);})));if(!_nK._){return 0;}else{var _nM=_nK.a,_nN=_mw(new T1(1,new T(function(){var _nO=String(_nE);return fromJSStr(_nO);})));if(!_nN._){return 0;}else{var _nP=_nN.a,_nQ=_mw(new T1(1,new T(function(){var _nR=String(_nF);return fromJSStr(_nR);})));if(!_nQ._){return 0;}else{var _nS=_nQ.a,_nT=_mw(new T1(1,new T(function(){var _nU=String(_nG);return fromJSStr(_nU);})));if(!_nT._){return 0;}else{var _nV=_nT.a,_nW=toJSStr(E(_3m)),_nX=_2w(E(_nz.a),_nW,toJSStr(_5x(_n6({_:0,a:new T2(0,_4d,_nM),b:new T2(0,_4d,_nJ),c:_nP,d:_nS,e:_nV,f:1,g:false})))),_nY=_2w(E(_nA.a),_nW,toJSStr(_5x(_n6({_:0,a:new T2(0,_4d,_nM),b:new T2(0,_4d,_nJ),c:_nP,d:_nS,e:_nV,f:1,g:true}))));return _2r(_);}}}}}},_nZ=B(A(_3L,[_2u,_2s,_2n,_nq,1,function(_o0,_){return _nB(_);},_])),_o1=B(A(_3L,[_2u,_2s,_2n,_ns,1,function(_o2,_){return _nB(_);},_])),_o3=B(A(_3L,[_2u,_2s,_2a,_nu,2,function(_o4,_){return _nB(_);},_])),_o5=B(A(_3L,[_2u,_2s,_2a,_nw,2,function(_o6,_){return _nB(_);},_]));return C > 19 ? new F(function(){return A(_3L,[_2u,_2s,_2a,_ny,2,function(_o7,_){return _nB(_);},_]);}) : (++C,A(_3L,[_2u,_2s,_2a,_ny,2,function(_o7,_){return _nB(_);},_]));}else{return E(_3k);}}}}}}}}},_o8=function(_o9,_){var _oa=E(_o9);if(!_oa._){return __Z;}else{var _ob=_o8(_oa.b,_);return new T2(1,_oa.a,_ob);}},_oc=function(_od,_){var _oe=__arr2lst(0,_od);return _o8(_oe,_);},_of=function(_og,_){return _oc(E(_og),_);},_oh=function(_oi,_){return _oi;},_oj=function(_ok){return E(E(_ok).a);},_ol=function(_om,_on,_){var _oo=__eq(_on,E(_3E));if(!E(_oo)){var _op=__isUndef(_on);if(!E(_op)){var _oq=B(A3(_oj,_om,_on,_));return new T1(1,_oq);}else{return __Z;}}else{return __Z;}},_or=(function(id){return document.getElementById(id);}),_os=new T(function(){return err(new T(function(){return unCStr("Maybe.fromJust: Nothing");}));}),_ot=function(_ou){var _ov=E(_ou);return (_ov._==0)?E(_os):E(_ov.a);},_ow=function(_ox,_oy){while(1){var _oz=(function(_oA,_oB){var _oC=E(_oA);if(!_oC._){return __Z;}else{var _oD=_oC.b,_oE=E(_oB);if(!_oE._){return __Z;}else{var _oF=_oE.b;if(!E(_oE.a)._){return new T2(1,_oC.a,new T(function(){return _ow(_oD,_oF);}));}else{_ox=_oD;_oy=_oF;return __continue;}}}})(_ox,_oy);if(_oz!=__continue){return _oz;}}},_oG=new T(function(){return unAppCStr("[]",__Z);}),_oH=function(_oI){var _oJ=E(_oI);if(!_oJ._){return E(new T2(1,93,__Z));}else{var _oK=new T(function(){return _x(fromJSStr(E(_oJ.a)),new T(function(){return _oH(_oJ.b);},1));});return new T2(1,44,_oK);}},_oL=function(_oM,_oN){var _oO=new T(function(){var _oP=_ow(_oM,_oN);if(!_oP._){return E(_oG);}else{var _oQ=new T(function(){return _x(fromJSStr(E(_oP.a)),new T(function(){return _oH(_oP.b);},1));});return new T2(1,91,_oQ);}});return err(unAppCStr("Elements with the following IDs could not be found: ",_oO));},_oR=function(_oS){while(1){var _oT=E(_oS);if(!_oT._){return false;}else{if(!E(_oT.a)._){return true;}else{_oS=_oT.b;continue;}}}},_oU=function(_oV,_oW,_oX){var _oY=_3p(_oV),_oZ=function(_p0){if(!_oR(_p0)){return C > 19 ? new F(function(){return A1(_oX,new T(function(){return _9h(_ot,_p0);}));}) : (++C,A1(_oX,new T(function(){return _9h(_ot,_p0);})));}else{return _oL(_oW,_p0);}},_p1=new T(function(){var _p2=new T(function(){return B(A2(_3J,_oY,__Z));}),_p3=function(_p4){var _p5=E(_p4);if(!_p5._){return E(_p2);}else{var _p6=new T(function(){return B(_p3(_p5.b));}),_p7=function(_p8){return C > 19 ? new F(function(){return A3(_3r,_oY,_p6,function(_p9){return C > 19 ? new F(function(){return A2(_3J,_oY,new T2(1,_p8,_p9));}) : (++C,A2(_3J,_oY,new T2(1,_p8,_p9)));});}) : (++C,A3(_3r,_oY,_p6,function(_p9){return C > 19 ? new F(function(){return A2(_3J,_oY,new T2(1,_p8,_p9));}) : (++C,A2(_3J,_oY,new T2(1,_p8,_p9)));}));},_pa=new T(function(){return B(A2(_3F,_oV,function(_){var _pb=_or(E(_p5.a));return _ol(new T2(0,_oh,_of),_pb,_);}));});return C > 19 ? new F(function(){return A3(_3r,_oY,_pa,_p7);}) : (++C,A3(_3r,_oY,_pa,_p7));}};return B(_p3(_oW));});return C > 19 ? new F(function(){return A3(_3r,_oY,_p1,_oZ);}) : (++C,A3(_3r,_oY,_p1,_oZ));},_pc=new T(function(){return B(_oU(_1X,new T(function(){return _9h(function(_pd){return toJSStr(E(_pd));},new T2(1,new T(function(){return unCStr("s");}),new T2(1,new T(function(){return unCStr("k");}),new T2(1,new T(function(){return unCStr("r");}),new T2(1,new T(function(){return unCStr("t");}),new T2(1,new T(function(){return unCStr("sigma");}),new T2(1,new T(function(){return unCStr("resultC");}),new T2(1,new T(function(){return unCStr("resultP");}),__Z))))))));}),_nn));});
var hasteMain = function() {B(A(_pc, [0]));};window.onload = hasteMain;