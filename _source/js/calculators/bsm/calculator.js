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

var _0=function(_1,_2,_){var _3=B(A1(_1,_)),_4=B(A1(_2,_));return new T(function(){return B(A1(_3,_4));});},_5=function(_6,_7,_){var _8=B(A1(_7,_));return new T(function(){return B(A1(_6,_8));});},_9=function(_a,_){return _a;},_b=function(_c,_d,_){var _e=B(A1(_c,_));return C > 19 ? new F(function(){return A1(_d,_);}) : (++C,A1(_d,_));},_f=new T(function(){return unCStr("base");}),_g=new T(function(){return unCStr("GHC.IO.Exception");}),_h=new T(function(){return unCStr("IOException");}),_i=function(_j){return E(new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_f,_g,_h),__Z,__Z));},_k=function(_l){return E(E(_l).a);},_m=function(_n,_o,_p){var _q=B(A1(_n,_)),_r=B(A1(_o,_)),_s=hs_eqWord64(_q.a,_r.a);if(!_s){return __Z;}else{var _t=hs_eqWord64(_q.b,_r.b);return (!_t)?__Z:new T1(1,_p);}},_u=new T(function(){return unCStr(": ");}),_v=new T(function(){return unCStr(")");}),_w=new T(function(){return unCStr(" (");}),_x=function(_y,_z){var _A=E(_y);return (_A._==0)?E(_z):new T2(1,_A.a,new T(function(){return _x(_A.b,_z);}));},_B=new T(function(){return unCStr("interrupted");}),_C=new T(function(){return unCStr("system error");}),_D=new T(function(){return unCStr("unsatisified constraints");}),_E=new T(function(){return unCStr("user error");}),_F=new T(function(){return unCStr("permission denied");}),_G=new T(function(){return unCStr("illegal operation");}),_H=new T(function(){return unCStr("end of file");}),_I=new T(function(){return unCStr("resource exhausted");}),_J=new T(function(){return unCStr("resource busy");}),_K=new T(function(){return unCStr("does not exist");}),_L=new T(function(){return unCStr("already exists");}),_M=new T(function(){return unCStr("resource vanished");}),_N=new T(function(){return unCStr("timeout");}),_O=new T(function(){return unCStr("unsupported operation");}),_P=new T(function(){return unCStr("hardware fault");}),_Q=new T(function(){return unCStr("inappropriate type");}),_R=new T(function(){return unCStr("invalid argument");}),_S=new T(function(){return unCStr("failed");}),_T=new T(function(){return unCStr("protocol error");}),_U=function(_V,_W){switch(E(_V)){case 0:return _x(_L,_W);case 1:return _x(_K,_W);case 2:return _x(_J,_W);case 3:return _x(_I,_W);case 4:return _x(_H,_W);case 5:return _x(_G,_W);case 6:return _x(_F,_W);case 7:return _x(_E,_W);case 8:return _x(_D,_W);case 9:return _x(_C,_W);case 10:return _x(_T,_W);case 11:return _x(_S,_W);case 12:return _x(_R,_W);case 13:return _x(_Q,_W);case 14:return _x(_P,_W);case 15:return _x(_O,_W);case 16:return _x(_N,_W);case 17:return _x(_M,_W);default:return _x(_B,_W);}},_X=new T(function(){return unCStr("}");}),_Y=new T(function(){return unCStr("{handle: ");}),_Z=function(_10,_11,_12,_13,_14,_15){var _16=new T(function(){var _17=new T(function(){var _18=new T(function(){var _19=E(_13);if(!_19._){return E(_15);}else{var _1a=new T(function(){return _x(_19,new T(function(){return _x(_v,_15);},1));},1);return _x(_w,_1a);}},1);return _U(_11,_18);}),_1b=E(_12);if(!_1b._){return E(_17);}else{return _x(_1b,new T(function(){return _x(_u,_17);},1));}}),_1c=E(_14);if(!_1c._){var _1d=E(_10);if(!_1d._){return E(_16);}else{var _1e=E(_1d.a);if(!_1e._){var _1f=new T(function(){var _1g=new T(function(){return _x(_X,new T(function(){return _x(_u,_16);},1));},1);return _x(_1e.a,_1g);},1);return _x(_Y,_1f);}else{var _1h=new T(function(){var _1i=new T(function(){return _x(_X,new T(function(){return _x(_u,_16);},1));},1);return _x(_1e.a,_1i);},1);return _x(_Y,_1h);}}}else{return _x(_1c.a,new T(function(){return _x(_u,_16);},1));}},_1j=function(_1k){var _1l=E(_1k);return _Z(_1l.a,_1l.b,_1l.c,_1l.d,_1l.f,__Z);},_1m=function(_1n,_1o){var _1p=E(_1n);return _Z(_1p.a,_1p.b,_1p.c,_1p.d,_1p.f,_1o);},_1q=function(_1r,_1s,_1t){var _1u=E(_1s);if(!_1u._){return unAppCStr("[]",_1t);}else{var _1v=new T(function(){var _1w=new T(function(){var _1x=function(_1y){var _1z=E(_1y);if(!_1z._){return E(new T2(1,93,_1t));}else{var _1A=new T(function(){return B(A2(_1r,_1z.a,new T(function(){return _1x(_1z.b);})));});return new T2(1,44,_1A);}};return _1x(_1u.b);});return B(A2(_1r,_1u.a,_1w));});return new T2(1,91,_1v);}},_1B=new T(function(){return new T5(0,_i,new T3(0,function(_1C,_1D,_1E){var _1F=E(_1D);return _Z(_1F.a,_1F.b,_1F.c,_1F.d,_1F.f,_1E);},_1j,function(_1G,_1H){return _1q(_1m,_1G,_1H);}),function(_1I){return new T2(0,_1B,_1I);},function(_1J){var _1K=E(_1J);return _m(_k(_1K.a),_i,_1K.b);},_1j);}),_1L=new T(function(){return E(_1B);}),_1M=function(_1N){return E(E(_1N).c);},_1O=function(_1P){return new T6(0,__Z,7,__Z,_1P,__Z,__Z);},_1Q=function(_1R,_){var _1S=new T(function(){return B(A2(_1M,_1L,new T(function(){return B(A1(_1O,_1R));})));});return die(_1S);},_1T=function(_1U,_){return _1Q(_1U,_);},_1V=function(_1W){return E(_1W);},_1X=new T2(0,new T5(0,new T5(0,new T2(0,_5,function(_1Y,_1Z,_){var _20=B(A1(_1Z,_));return _1Y;}),_9,_0,_b,function(_21,_22,_){var _23=B(A1(_21,_)),_24=B(A1(_22,_));return _23;}),function(_25,_26,_){var _27=B(A1(_25,_));return C > 19 ? new F(function(){return A2(_26,_27,_);}) : (++C,A2(_26,_27,_));},_b,_9,function(_28){return C > 19 ? new F(function(){return A1(_1T,_28);}) : (++C,A1(_1T,_28));}),_1V),_29=function(_){return 0;},_2a=new T2(0,function(_2b){switch(E(_2b)){case 0:return "load";case 1:return "unload";case 2:return "change";case 3:return "focus";case 4:return "blur";case 5:return "submit";default:return "scroll";}},function(_2c,_2d,_){return _29(_);}),_2e=function(_2f,_){var _2g=_2f["keyCode"],_2h=_2f["ctrlKey"],_2i=_2f["altKey"],_2j=_2f["shiftKey"],_2k=_2f["metaKey"];return new T(function(){var _2l=Number(_2g),_2m=jsTrunc(_2l);return new T5(0,_2m,E(_2h),E(_2i),E(_2j),E(_2k));});},_2n=new T2(0,function(_2o){switch(E(_2o)){case 0:return "keypress";case 1:return "keyup";default:return "keydown";}},function(_2p,_2q,_){return _2e(E(_2q),_);}),_2r=function(_){return 0;},_2s=new T2(0,_1V,function(_2t,_){return new T1(1,_2t);}),_2u=new T2(0,_1X,_9),_2v=function(_2w){if(_2w!=0){if(_2w<=0){var _2x=1/(1+0.5* -_2w),_2y=_2x*_2x,_2z=_2y*_2x,_2A=_2z*_2x,_2B=_2A*_2x,_2C=_2B*_2x,_2D=_2C*_2x,_2E=_2D*_2x;return (_2w<0)?_2x*Math.exp( -(_2w*_2w)-1.26551223+1.00002368*_2x+0.37409196*_2y+9.678418e-2*_2z-0.18628806*_2A+0.27886807*_2B-1.13520398*_2C+1.48851587*_2D-0.82215223*_2E+0.17087277*_2E*_2x)-1:1-_2x*Math.exp( -(_2w*_2w)-1.26551223+1.00002368*_2x+0.37409196*_2y+9.678418e-2*_2z-0.18628806*_2A+0.27886807*_2B-1.13520398*_2C+1.48851587*_2D-0.82215223*_2E+0.17087277*_2E*_2x);}else{var _2F=1/(1+0.5*_2w),_2G=_2F*_2F,_2H=_2G*_2F,_2I=_2H*_2F,_2J=_2I*_2F,_2K=_2J*_2F,_2L=_2K*_2F,_2M=_2L*_2F;return (_2w<0)?_2F*Math.exp( -(_2w*_2w)-1.26551223+1.00002368*_2F+0.37409196*_2G+9.678418e-2*_2H-0.18628806*_2I+0.27886807*_2J-1.13520398*_2K+1.48851587*_2L-0.82215223*_2M+0.17087277*_2M*_2F)-1:1-_2F*Math.exp( -(_2w*_2w)-1.26551223+1.00002368*_2F+0.37409196*_2G+9.678418e-2*_2H-0.18628806*_2I+0.27886807*_2J-1.13520398*_2K+1.48851587*_2L-0.82215223*_2M+0.17087277*_2M*_2F);}}else{return (_2w<0)?Math.exp( -(_2w*_2w)-1.26551223+1.00002368+0.37409196+9.678418e-2-0.18628806+0.27886807-1.13520398+1.48851587-0.82215223+0.17087277)-1:1-Math.exp( -(_2w*_2w)-1.26551223+1.00002368+0.37409196+9.678418e-2-0.18628806+0.27886807-1.13520398+1.48851587-0.82215223+0.17087277);}},_2N=function(_2O,_2P){while(1){var _2Q=E(_2O);if(!_2Q._){return E(_2P);}else{var _2R=new T2(1,_2Q.a,_2P);_2O=_2Q.b;_2P=_2R;continue;}}},_2S=function(_2T){return _2N(_2T,__Z);},_2U=function(_2V,_2W,_2X){while(1){var _2Y=(function(_2Z,_30,_31){var _32=E(_2Z);if(!_32._){return new T2(0,new T(function(){return _2S(_30);}),new T(function(){return _2S(_31);}));}else{var _33=_30,_34=new T2(1,_32.a,_31);_2V=_32.b;_2W=_33;_2X=_34;return __continue;}})(_2V,_2W,_2X);if(_2Y!=__continue){return _2Y;}}},_35=function(_36,_37,_38){while(1){var _39=(function(_3a,_3b,_3c){var _3d=E(_3a);if(!_3d._){return new T2(0,new T(function(){return _2S(_3b);}),new T(function(){return _2S(_3c);}));}else{var _3e=_3d.b,_3f=E(_3d.a);if(_3f==46){return _2U(_3e,_3b,__Z);}else{var _3g=new T2(1,_3f,_3b),_3h=_3c;_36=_3e;_37=_3g;_38=_3h;return __continue;}}})(_36,_37,_38);if(_39!=__continue){return _39;}}},_3i=function(_3j,_3k){var _3l=E(_3k);if(!_3l._){return __Z;}else{var _3m=_3l.a,_3n=E(_3j);return (_3n==1)?new T2(1,_3m,__Z):new T2(1,_3m,new T(function(){return _3i(_3n-1|0,_3l.b);}));}},_3o=function(_3p){var _3q=I_decodeDouble(_3p);return new T2(0,new T1(1,_3q.b),_3q.a);},_3r=function(_3s){var _3t=E(_3s);if(!_3t._){return _3t.a;}else{return I_toNumber(_3t.a);}},_3u=function(_3v){return new T1(0,_3v);},_3w=function(_3x){var _3y=hs_intToInt64(2147483647),_3z=hs_leInt64(_3x,_3y);if(!_3z){return new T1(1,I_fromInt64(_3x));}else{var _3A=hs_intToInt64(-2147483648),_3B=hs_geInt64(_3x,_3A);if(!_3B){return new T1(1,I_fromInt64(_3x));}else{var _3C=hs_int64ToInt(_3x);return _3u(_3C);}}},_3D=function(_3E){var _3F=hs_intToInt64(_3E);return E(_3F);},_3G=function(_3H){var _3I=E(_3H);if(!_3I._){return _3D(_3I.a);}else{return I_toInt64(_3I.a);}},_3J=function(_3K,_3L){while(1){var _3M=E(_3K);if(!_3M._){_3K=new T1(1,I_fromInt(_3M.a));continue;}else{return new T1(1,I_shiftLeft(_3M.a,_3L));}}},_3N=function(_3O,_3P){var _3Q=Math.pow(10,_3O),_3R=rintDouble(_3P*_3Q),_3S=_3o(_3R),_3T=_3S.a,_3U=_3S.b,_3V=function(_3W,_3X){var _3Y=new T(function(){return unAppCStr(".",new T(function(){if(0>=_3O){return __Z;}else{return _3i(_3O,_3X);}}));},1);return _x(_3W,_3Y);};if(_3U>=0){var _3Z=jsShow(_3r(_3J(_3T,_3U))/_3Q),_40=_35(fromJSStr(_3Z),__Z,__Z);return _3V(_40.a,_40.b);}else{var _41=hs_uncheckedIShiftRA64(_3G(_3T), -_3U),_42=jsShow(_3r(_3w(_41))/_3Q),_43=_35(fromJSStr(_42),__Z,__Z);return _3V(_43.a,_43.b);}},_44=(function(e,p){var x = e[p];return typeof x === 'undefined' ? '' : x.toString();}),_45=(function(e,p,v){e[p] = v;}),_46=new T(function(){return unCStr("base");}),_47=new T(function(){return unCStr("Control.Exception.Base");}),_48=new T(function(){return unCStr("PatternMatchFail");}),_49=function(_4a){return E(new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_46,_47,_48),__Z,__Z));},_4b=function(_4c){return E(E(_4c).a);},_4d=function(_4e,_4f){return _x(E(_4e).a,_4f);},_4g=new T(function(){return new T5(0,_49,new T3(0,function(_4h,_4i,_4j){return _x(E(_4i).a,_4j);},_4b,function(_4k,_4l){return _1q(_4d,_4k,_4l);}),function(_4m){return new T2(0,_4g,_4m);},function(_4n){var _4o=E(_4n);return _m(_k(_4o.a),_49,_4o.b);},_4b);}),_4p=new T(function(){return unCStr("Non-exhaustive patterns in");}),_4q=function(_4r,_4s){return die(new T(function(){return B(A2(_1M,_4s,_4r));}));},_4t=function(_4u,_4v){return _4q(_4u,_4v);},_4w=function(_4x,_4y){var _4z=E(_4y);if(!_4z._){return new T2(0,__Z,__Z);}else{var _4A=_4z.a;if(!B(A1(_4x,_4A))){return new T2(0,__Z,_4z);}else{var _4B=new T(function(){var _4C=_4w(_4x,_4z.b);return new T2(0,_4C.a,_4C.b);});return new T2(0,new T2(1,_4A,new T(function(){return E(E(_4B).a);})),new T(function(){return E(E(_4B).b);}));}}},_4D=new T(function(){return unCStr("\n");}),_4E=function(_4F){return (E(_4F)==124)?false:true;},_4G=function(_4H,_4I){var _4J=_4w(_4E,unCStr(_4H)),_4K=_4J.a,_4L=function(_4M,_4N){var _4O=new T(function(){var _4P=new T(function(){return _x(_4I,new T(function(){return _x(_4N,_4D);},1));});return unAppCStr(": ",_4P);},1);return _x(_4M,_4O);},_4Q=E(_4J.b);if(!_4Q._){return _4L(_4K,__Z);}else{if(E(_4Q.a)==124){return _4L(_4K,new T2(1,32,_4Q.b));}else{return _4L(_4K,__Z);}}},_4R=function(_4S){return _4t(new T1(0,new T(function(){return _4G(_4S,_4p);})),_4g);},_4T=new T(function(){return B((function(_4U){return C > 19 ? new F(function(){return _4R("calculator.hs:(11,1)-(28,39)|function calculator");}) : (++C,_4R("calculator.hs:(11,1)-(28,39)|function calculator"));})(_));}),_4V=new T(function(){return unCStr("innerHTML");}),_4W=function(_4X){return E(E(_4X).a);},_4Y=function(_4Z){return E(E(_4Z).a);},_50=function(_51){return E(E(_51).b);},_52=function(_53){return E(E(_53).a);},_54=function(_55){return E(E(_55).b);},_56=function(_57){return E(E(_57).a);},_58=function(_59){var _5a=B(A1(_59,_));return E(_5a);},_5b=new T(function(){return _58(function(_){return nMV(__Z);});}),_5c=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_5d=new T(function(){return _58(function(_){return __jsNull();});}),_5e=function(_5f){return E(E(_5f).b);},_5g=function(_5h){return E(E(_5h).b);},_5i=function(_5j){return E(E(_5j).d);},_5k=function(_5l,_5m,_5n,_5o,_5p,_5q){var _5r=_4W(_5l),_5s=_4Y(_5r),_5t=new T(function(){return _5e(_5r);}),_5u=new T(function(){return _5i(_5s);}),_5v=new T(function(){return B(A2(_52,_5m,_5o));}),_5w=new T(function(){return B(A2(_56,_5n,_5p));}),_5x=function(_5y){return C > 19 ? new F(function(){return A1(_5u,new T3(0,_5w,_5v,_5y));}) : (++C,A1(_5u,new T3(0,_5w,_5v,_5y)));},_5z=function(_5A){var _5B=new T(function(){var _5C=new T(function(){var _5D=__createJSFunc(2,function(_5E,_){var _5F=B(A2(E(_5A),_5E,_));return _5d;}),_5G=_5D;return function(_){return _5c(E(_5v),E(_5w),_5G);};});return B(A1(_5t,_5C));});return C > 19 ? new F(function(){return A3(_50,_5s,_5B,_5x);}) : (++C,A3(_50,_5s,_5B,_5x));},_5H=new T(function(){var _5I=new T(function(){return _5e(_5r);}),_5J=function(_5K){var _5L=new T(function(){return B(A1(_5I,function(_){var _=wMV(E(_5b),new T1(1,_5K));return C > 19 ? new F(function(){return A(_54,[_5n,_5p,_5K,_]);}) : (++C,A(_54,[_5n,_5p,_5K,_]));}));});return C > 19 ? new F(function(){return A3(_50,_5s,_5L,_5q);}) : (++C,A3(_50,_5s,_5L,_5q));};return B(A2(_5g,_5l,_5J));});return C > 19 ? new F(function(){return A3(_50,_5s,_5H,_5z);}) : (++C,A3(_50,_5s,_5H,_5z));},_5M=function(_5N,_5O){var _5P=E(_5O);return (_5P._==0)?__Z:new T2(1,_5N,new T(function(){return _5M(_5P.a,_5P.b);}));},_5Q=new T(function(){return unCStr(": empty list");}),_5R=new T(function(){return unCStr("Prelude.");}),_5S=function(_5T){return err(_x(_5R,new T(function(){return _x(_5T,_5Q);},1)));},_5U=new T(function(){return _5S(new T(function(){return unCStr("init");}));}),_5V=function(_5W){var _5X=E(_5W);if(!_5X._){return E(_5U);}else{return _5M(_5X.a,_5X.b);}},_5Y=new T(function(){return _5S(new T(function(){return unCStr("last");}));}),_5Z=function(_60){while(1){var _61=(function(_62){var _63=E(_62);if(!_63._){return __Z;}else{var _64=_63.b,_65=E(_63.a);if(!E(_65.b)._){return new T2(1,_65.a,new T(function(){return _5Z(_64);}));}else{_60=_64;return __continue;}}})(_60);if(_61!=__continue){return _61;}}},_66=function(_67,_68){while(1){var _69=(function(_6a,_6b){var _6c=E(_6a);switch(_6c._){case 0:var _6d=E(_6b);if(!_6d._){return __Z;}else{_67=B(A1(_6c.a,_6d.a));_68=_6d.b;return __continue;}break;case 1:var _6e=B(A1(_6c.a,_6b)),_6f=_6b;_67=_6e;_68=_6f;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_6c.a,_6b),new T(function(){return _66(_6c.b,_6b);}));default:return E(_6c.a);}})(_67,_68);if(_69!=__continue){return _69;}}},_6g=new T(function(){return err(new T(function(){return unCStr("Prelude.read: ambiguous parse");}));}),_6h=new T(function(){return err(new T(function(){return unCStr("Prelude.read: no parse");}));}),_6i=new T(function(){return B(_4R("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_6j=function(_6k,_6l){var _6m=function(_6n){var _6o=E(_6l);if(_6o._==3){return new T2(3,_6o.a,new T(function(){return _6j(_6k,_6o.b);}));}else{var _6p=E(_6k);if(_6p._==2){return _6o;}else{if(_6o._==2){return _6p;}else{var _6q=function(_6r){if(_6o._==4){var _6s=function(_6t){return new T1(4,new T(function(){return _x(_66(_6p,_6t),_6o.a);}));};return new T1(1,_6s);}else{if(_6p._==1){var _6u=_6p.a;if(!_6o._){return new T1(1,function(_6v){return _6j(B(A1(_6u,_6v)),_6o);});}else{var _6w=function(_6x){return _6j(B(A1(_6u,_6x)),new T(function(){return B(A1(_6o.a,_6x));}));};return new T1(1,_6w);}}else{if(!_6o._){return E(_6i);}else{var _6y=function(_6z){return _6j(_6p,new T(function(){return B(A1(_6o.a,_6z));}));};return new T1(1,_6y);}}}};switch(_6p._){case 1:if(_6o._==4){var _6A=function(_6B){return new T1(4,new T(function(){return _x(_66(B(A1(_6p.a,_6B)),_6B),_6o.a);}));};return new T1(1,_6A);}else{return _6q(_);}break;case 4:var _6C=_6p.a;switch(_6o._){case 0:var _6D=function(_6E){var _6F=new T(function(){return _x(_6C,new T(function(){return _66(_6o,_6E);},1));});return new T1(4,_6F);};return new T1(1,_6D);case 1:var _6G=function(_6H){var _6I=new T(function(){return _x(_6C,new T(function(){return _66(B(A1(_6o.a,_6H)),_6H);},1));});return new T1(4,_6I);};return new T1(1,_6G);default:return new T1(4,new T(function(){return _x(_6C,_6o.a);}));}break;default:return _6q(_);}}}}},_6J=E(_6k);switch(_6J._){case 0:var _6K=E(_6l);if(!_6K._){var _6L=function(_6M){return _6j(B(A1(_6J.a,_6M)),new T(function(){return B(A1(_6K.a,_6M));}));};return new T1(0,_6L);}else{return _6m(_);}break;case 3:return new T2(3,_6J.a,new T(function(){return _6j(_6J.b,_6l);}));default:return _6m(_);}},_6N=new T(function(){return unCStr("(");}),_6O=new T(function(){return unCStr(")");}),_6P=function(_6Q,_6R){while(1){var _6S=E(_6Q);if(!_6S._){return (E(_6R)._==0)?true:false;}else{var _6T=E(_6R);if(!_6T._){return false;}else{if(E(_6S.a)!=E(_6T.a)){return false;}else{_6Q=_6S.b;_6R=_6T.b;continue;}}}}},_6U=new T2(0,function(_6V,_6W){return E(_6V)==E(_6W);},function(_6X,_6Y){return E(_6X)!=E(_6Y);}),_6Z=function(_70,_71){while(1){var _72=E(_70);if(!_72._){return (E(_71)._==0)?true:false;}else{var _73=E(_71);if(!_73._){return false;}else{if(E(_72.a)!=E(_73.a)){return false;}else{_70=_72.b;_71=_73.b;continue;}}}}},_74=function(_75,_76){return (!_6Z(_75,_76))?true:false;},_77=function(_78,_79){var _7a=E(_78);switch(_7a._){case 0:return new T1(0,function(_7b){return C > 19 ? new F(function(){return _77(B(A1(_7a.a,_7b)),_79);}) : (++C,_77(B(A1(_7a.a,_7b)),_79));});case 1:return new T1(1,function(_7c){return C > 19 ? new F(function(){return _77(B(A1(_7a.a,_7c)),_79);}) : (++C,_77(B(A1(_7a.a,_7c)),_79));});case 2:return new T0(2);case 3:return _6j(B(A1(_79,_7a.a)),new T(function(){return B(_77(_7a.b,_79));}));default:var _7d=function(_7e){var _7f=E(_7e);if(!_7f._){return __Z;}else{var _7g=E(_7f.a);return _x(_66(B(A1(_79,_7g.a)),_7g.b),new T(function(){return _7d(_7f.b);},1));}},_7h=_7d(_7a.a);return (_7h._==0)?new T0(2):new T1(4,_7h);}},_7i=new T0(2),_7j=function(_7k){return new T2(3,_7k,_7i);},_7l=function(_7m,_7n){var _7o=E(_7m);if(!_7o){return C > 19 ? new F(function(){return A1(_7n,0);}) : (++C,A1(_7n,0));}else{var _7p=new T(function(){return B(_7l(_7o-1|0,_7n));});return new T1(0,function(_7q){return E(_7p);});}},_7r=function(_7s,_7t,_7u){var _7v=new T(function(){return B(A1(_7s,_7j));}),_7w=function(_7x,_7y,_7z,_7A){while(1){var _7B=B((function(_7C,_7D,_7E,_7F){var _7G=E(_7C);switch(_7G._){case 0:var _7H=E(_7D);if(!_7H._){return C > 19 ? new F(function(){return A1(_7t,_7F);}) : (++C,A1(_7t,_7F));}else{var _7I=_7E+1|0,_7J=_7F;_7x=B(A1(_7G.a,_7H.a));_7y=_7H.b;_7z=_7I;_7A=_7J;return __continue;}break;case 1:var _7K=B(A1(_7G.a,_7D)),_7L=_7D,_7I=_7E,_7J=_7F;_7x=_7K;_7y=_7L;_7z=_7I;_7A=_7J;return __continue;case 2:return C > 19 ? new F(function(){return A1(_7t,_7F);}) : (++C,A1(_7t,_7F));break;case 3:var _7M=new T(function(){return B(_77(_7G,_7F));});return C > 19 ? new F(function(){return _7l(_7E,function(_7N){return E(_7M);});}) : (++C,_7l(_7E,function(_7N){return E(_7M);}));break;default:return C > 19 ? new F(function(){return _77(_7G,_7F);}) : (++C,_77(_7G,_7F));}})(_7x,_7y,_7z,_7A));if(_7B!=__continue){return _7B;}}};return function(_7O){return _7w(_7v,_7O,0,_7u);};},_7P=function(_7Q){return C > 19 ? new F(function(){return A1(_7Q,__Z);}) : (++C,A1(_7Q,__Z));},_7R=function(_7S,_7T){var _7U=function(_7V){var _7W=E(_7V);if(!_7W._){return _7P;}else{var _7X=_7W.a;if(!B(A1(_7S,_7X))){return _7P;}else{var _7Y=new T(function(){return _7U(_7W.b);}),_7Z=function(_80){var _81=new T(function(){return B(A1(_7Y,function(_82){return C > 19 ? new F(function(){return A1(_80,new T2(1,_7X,_82));}) : (++C,A1(_80,new T2(1,_7X,_82)));}));});return new T1(0,function(_83){return E(_81);});};return _7Z;}}};return function(_84){return C > 19 ? new F(function(){return A2(_7U,_84,_7T);}) : (++C,A2(_7U,_84,_7T));};},_85=new T(function(){return err(new T(function(){return unCStr("valDig: Bad base");}));}),_86=function(_87,_88){var _89=function(_8a,_8b){var _8c=E(_8a);if(!_8c._){var _8d=new T(function(){return B(A1(_8b,__Z));});return function(_8e){return C > 19 ? new F(function(){return A1(_8e,_8d);}) : (++C,A1(_8e,_8d));};}else{var _8f=E(_8c.a),_8g=function(_8h){var _8i=new T(function(){return _89(_8c.b,function(_8j){return C > 19 ? new F(function(){return A1(_8b,new T2(1,_8h,_8j));}) : (++C,A1(_8b,new T2(1,_8h,_8j)));});}),_8k=function(_8l){var _8m=new T(function(){return B(A1(_8i,_8l));});return new T1(0,function(_8n){return E(_8m);});};return _8k;};switch(E(_87)){case 8:if(48>_8f){var _8o=new T(function(){return B(A1(_8b,__Z));});return function(_8p){return C > 19 ? new F(function(){return A1(_8p,_8o);}) : (++C,A1(_8p,_8o));};}else{if(_8f>55){var _8q=new T(function(){return B(A1(_8b,__Z));});return function(_8r){return C > 19 ? new F(function(){return A1(_8r,_8q);}) : (++C,A1(_8r,_8q));};}else{return _8g(_8f-48|0);}}break;case 10:if(48>_8f){var _8s=new T(function(){return B(A1(_8b,__Z));});return function(_8t){return C > 19 ? new F(function(){return A1(_8t,_8s);}) : (++C,A1(_8t,_8s));};}else{if(_8f>57){var _8u=new T(function(){return B(A1(_8b,__Z));});return function(_8v){return C > 19 ? new F(function(){return A1(_8v,_8u);}) : (++C,A1(_8v,_8u));};}else{return _8g(_8f-48|0);}}break;case 16:if(48>_8f){if(97>_8f){if(65>_8f){var _8w=new T(function(){return B(A1(_8b,__Z));});return function(_8x){return C > 19 ? new F(function(){return A1(_8x,_8w);}) : (++C,A1(_8x,_8w));};}else{if(_8f>70){var _8y=new T(function(){return B(A1(_8b,__Z));});return function(_8z){return C > 19 ? new F(function(){return A1(_8z,_8y);}) : (++C,A1(_8z,_8y));};}else{return _8g((_8f-65|0)+10|0);}}}else{if(_8f>102){if(65>_8f){var _8A=new T(function(){return B(A1(_8b,__Z));});return function(_8B){return C > 19 ? new F(function(){return A1(_8B,_8A);}) : (++C,A1(_8B,_8A));};}else{if(_8f>70){var _8C=new T(function(){return B(A1(_8b,__Z));});return function(_8D){return C > 19 ? new F(function(){return A1(_8D,_8C);}) : (++C,A1(_8D,_8C));};}else{return _8g((_8f-65|0)+10|0);}}}else{return _8g((_8f-97|0)+10|0);}}}else{if(_8f>57){if(97>_8f){if(65>_8f){var _8E=new T(function(){return B(A1(_8b,__Z));});return function(_8F){return C > 19 ? new F(function(){return A1(_8F,_8E);}) : (++C,A1(_8F,_8E));};}else{if(_8f>70){var _8G=new T(function(){return B(A1(_8b,__Z));});return function(_8H){return C > 19 ? new F(function(){return A1(_8H,_8G);}) : (++C,A1(_8H,_8G));};}else{return _8g((_8f-65|0)+10|0);}}}else{if(_8f>102){if(65>_8f){var _8I=new T(function(){return B(A1(_8b,__Z));});return function(_8J){return C > 19 ? new F(function(){return A1(_8J,_8I);}) : (++C,A1(_8J,_8I));};}else{if(_8f>70){var _8K=new T(function(){return B(A1(_8b,__Z));});return function(_8L){return C > 19 ? new F(function(){return A1(_8L,_8K);}) : (++C,A1(_8L,_8K));};}else{return _8g((_8f-65|0)+10|0);}}}else{return _8g((_8f-97|0)+10|0);}}}else{return _8g(_8f-48|0);}}break;default:return E(_85);}}},_8M=function(_8N){var _8O=E(_8N);if(!_8O._){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_88,_8O);}) : (++C,A1(_88,_8O));}};return function(_8P){return C > 19 ? new F(function(){return A3(_89,_8P,_1V,_8M);}) : (++C,A3(_89,_8P,_1V,_8M));};},_8Q=function(_8R){var _8S=function(_8T){return C > 19 ? new F(function(){return A1(_8R,new T1(5,new T2(0,8,_8T)));}) : (++C,A1(_8R,new T1(5,new T2(0,8,_8T))));},_8U=function(_8V){return C > 19 ? new F(function(){return A1(_8R,new T1(5,new T2(0,16,_8V)));}) : (++C,A1(_8R,new T1(5,new T2(0,16,_8V))));},_8W=function(_8X){switch(E(_8X)){case 79:return new T1(1,_86(8,_8S));case 88:return new T1(1,_86(16,_8U));case 111:return new T1(1,_86(8,_8S));case 120:return new T1(1,_86(16,_8U));default:return new T0(2);}};return function(_8Y){return (E(_8Y)==48)?E(new T1(0,_8W)):new T0(2);};},_8Z=function(_90){return new T1(0,_8Q(_90));},_91=function(_92){return C > 19 ? new F(function(){return A1(_92,__Z);}) : (++C,A1(_92,__Z));},_93=function(_94){return C > 19 ? new F(function(){return A1(_94,__Z);}) : (++C,A1(_94,__Z));},_95=new T1(0,1),_96=function(_97,_98){while(1){var _99=E(_97);if(!_99._){var _9a=_99.a,_9b=E(_98);if(!_9b._){var _9c=_9b.a,_9d=addC(_9a,_9c);if(!E(_9d.b)){return new T1(0,_9d.a);}else{_97=new T1(1,I_fromInt(_9a));_98=new T1(1,I_fromInt(_9c));continue;}}else{_97=new T1(1,I_fromInt(_9a));_98=_9b;continue;}}else{var _9e=E(_98);if(!_9e._){_97=_99;_98=new T1(1,I_fromInt(_9e.a));continue;}else{return new T1(1,I_add(_99.a,_9e.a));}}}},_9f=new T(function(){return _96(new T1(0,2147483647),_95);}),_9g=function(_9h){var _9i=E(_9h);if(!_9i._){var _9j=E(_9i.a);return (_9j==(-2147483648))?E(_9f):new T1(0, -_9j);}else{return new T1(1,I_negate(_9i.a));}},_9k=new T1(0,10),_9l=function(_9m,_9n){while(1){var _9o=E(_9m);if(!_9o._){return E(_9n);}else{var _9p=_9n+1|0;_9m=_9o.b;_9n=_9p;continue;}}},_9q=function(_9r,_9s){var _9t=E(_9s);return (_9t._==0)?__Z:new T2(1,new T(function(){return B(A1(_9r,_9t.a));}),new T(function(){return _9q(_9r,_9t.b);}));},_9u=function(_9v){return _3u(E(_9v));},_9w=new T(function(){return err(new T(function(){return unCStr("this should not happen");}));}),_9x=function(_9y,_9z){while(1){var _9A=E(_9y);if(!_9A._){var _9B=_9A.a,_9C=E(_9z);if(!_9C._){var _9D=_9C.a;if(!(imul(_9B,_9D)|0)){return new T1(0,imul(_9B,_9D)|0);}else{_9y=new T1(1,I_fromInt(_9B));_9z=new T1(1,I_fromInt(_9D));continue;}}else{_9y=new T1(1,I_fromInt(_9B));_9z=_9C;continue;}}else{var _9E=E(_9z);if(!_9E._){_9y=_9A;_9z=new T1(1,I_fromInt(_9E.a));continue;}else{return new T1(1,I_mul(_9A.a,_9E.a));}}}},_9F=function(_9G,_9H){var _9I=E(_9H);if(!_9I._){return __Z;}else{var _9J=E(_9I.b);return (_9J._==0)?E(_9w):new T2(1,_96(_9x(_9I.a,_9G),_9J.a),new T(function(){return _9F(_9G,_9J.b);}));}},_9K=new T1(0,0),_9L=function(_9M,_9N,_9O){while(1){var _9P=(function(_9Q,_9R,_9S){var _9T=E(_9S);if(!_9T._){return E(_9K);}else{if(!E(_9T.b)._){return E(_9T.a);}else{var _9U=E(_9R);if(_9U<=40){var _9V=function(_9W,_9X){while(1){var _9Y=E(_9X);if(!_9Y._){return E(_9W);}else{var _9Z=_96(_9x(_9W,_9Q),_9Y.a);_9W=_9Z;_9X=_9Y.b;continue;}}};return _9V(_9K,_9T);}else{var _a0=_9x(_9Q,_9Q);if(!(_9U%2)){var _a1=_9F(_9Q,_9T);_9M=_a0;_9N=quot(_9U+1|0,2);_9O=_a1;return __continue;}else{var _a1=_9F(_9Q,new T2(1,_9K,_9T));_9M=_a0;_9N=quot(_9U+1|0,2);_9O=_a1;return __continue;}}}}})(_9M,_9N,_9O);if(_9P!=__continue){return _9P;}}},_a2=function(_a3,_a4){return _9L(_a3,new T(function(){return _9l(_a4,0);},1),_9q(_9u,_a4));},_a5=function(_a6){var _a7=new T(function(){var _a8=new T(function(){var _a9=function(_aa){return C > 19 ? new F(function(){return A1(_a6,new T1(1,new T(function(){return _a2(_9k,_aa);})));}) : (++C,A1(_a6,new T1(1,new T(function(){return _a2(_9k,_aa);}))));};return new T1(1,_86(10,_a9));}),_ab=function(_ac){if(E(_ac)==43){var _ad=function(_ae){return C > 19 ? new F(function(){return A1(_a6,new T1(1,new T(function(){return _a2(_9k,_ae);})));}) : (++C,A1(_a6,new T1(1,new T(function(){return _a2(_9k,_ae);}))));};return new T1(1,_86(10,_ad));}else{return new T0(2);}},_af=function(_ag){if(E(_ag)==45){var _ah=function(_ai){return C > 19 ? new F(function(){return A1(_a6,new T1(1,new T(function(){return _9g(_a2(_9k,_ai));})));}) : (++C,A1(_a6,new T1(1,new T(function(){return _9g(_a2(_9k,_ai));}))));};return new T1(1,_86(10,_ah));}else{return new T0(2);}};return _6j(_6j(new T1(0,_af),new T1(0,_ab)),_a8);});return _6j(new T1(0,function(_aj){return (E(_aj)==101)?E(_a7):new T0(2);}),new T1(0,function(_ak){return (E(_ak)==69)?E(_a7):new T0(2);}));},_al=function(_am){var _an=function(_ao){return C > 19 ? new F(function(){return A1(_am,new T1(1,_ao));}) : (++C,A1(_am,new T1(1,_ao)));};return function(_ap){return (E(_ap)==46)?new T1(1,_86(10,_an)):new T0(2);};},_aq=function(_ar){return new T1(0,_al(_ar));},_as=function(_at){var _au=function(_av){var _aw=function(_ax){return new T1(1,_7r(_a5,_91,function(_ay){return C > 19 ? new F(function(){return A1(_at,new T1(5,new T3(1,_av,_ax,_ay)));}) : (++C,A1(_at,new T1(5,new T3(1,_av,_ax,_ay))));}));};return new T1(1,_7r(_aq,_93,_aw));};return _86(10,_au);},_az=function(_aA){return new T1(1,_as(_aA));},_aB=function(_aC){return E(E(_aC).a);},_aD=function(_aE,_aF,_aG){while(1){var _aH=E(_aG);if(!_aH._){return false;}else{if(!B(A3(_aB,_aE,_aF,_aH.a))){_aG=_aH.b;continue;}else{return true;}}}},_aI=new T(function(){return unCStr("!@#$%&*+./<=>?\\^|:-~");}),_aJ=function(_aK){return _aD(_6U,_aK,_aI);},_aL=function(_aM){var _aN=new T(function(){return B(A1(_aM,8));}),_aO=new T(function(){return B(A1(_aM,16));});return function(_aP){switch(E(_aP)){case 79:return E(_aN);case 88:return E(_aO);case 111:return E(_aN);case 120:return E(_aO);default:return new T0(2);}};},_aQ=function(_aR){return new T1(0,_aL(_aR));},_aS=function(_aT){return C > 19 ? new F(function(){return A1(_aT,10);}) : (++C,A1(_aT,10));},_aU=function(_aV,_aW){var _aX=jsShowI(_aV);return _x(fromJSStr(_aX),_aW);},_aY=function(_aZ,_b0,_b1){if(_b0>=0){return _aU(_b0,_b1);}else{if(_aZ<=6){return _aU(_b0,_b1);}else{return new T2(1,40,new T(function(){var _b2=jsShowI(_b0);return _x(fromJSStr(_b2),new T2(1,41,_b1));}));}}},_b3=function(_b4){return err(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return _aY(9,_b4,__Z);})));},_b5=function(_b6){var _b7=E(_b6);if(!_b7._){return E(_b7.a);}else{return I_toInt(_b7.a);}},_b8=function(_b9,_ba){var _bb=E(_b9);if(!_bb._){var _bc=_bb.a,_bd=E(_ba);return (_bd._==0)?_bc<=_bd.a:I_compareInt(_bd.a,_bc)>=0;}else{var _be=_bb.a,_bf=E(_ba);return (_bf._==0)?I_compareInt(_be,_bf.a)<=0:I_compare(_be,_bf.a)<=0;}},_bg=function(_bh){return new T0(2);},_bi=function(_bj){var _bk=E(_bj);if(!_bk._){return _bg;}else{var _bl=_bk.a,_bm=E(_bk.b);if(!_bm._){return E(_bl);}else{var _bn=new T(function(){return _bi(_bm);}),_bo=function(_bp){return _6j(B(A1(_bl,_bp)),new T(function(){return B(A1(_bn,_bp));}));};return _bo;}}},_bq=function(_br,_bs){var _bt=function(_bu,_bv,_bw){var _bx=E(_bu);if(!_bx._){return C > 19 ? new F(function(){return A1(_bw,_br);}) : (++C,A1(_bw,_br));}else{var _by=E(_bv);if(!_by._){return new T0(2);}else{if(E(_bx.a)!=E(_by.a)){return new T0(2);}else{var _bz=new T(function(){return B(_bt(_bx.b,_by.b,_bw));});return new T1(0,function(_bA){return E(_bz);});}}}};return function(_bB){return C > 19 ? new F(function(){return _bt(_br,_bB,_bs);}) : (++C,_bt(_br,_bB,_bs));};},_bC=new T(function(){return unCStr("SO");}),_bD=function(_bE){var _bF=new T(function(){return B(A1(_bE,14));});return new T1(1,_bq(_bC,function(_bG){return E(_bF);}));},_bH=new T(function(){return unCStr("SOH");}),_bI=function(_bJ){var _bK=new T(function(){return B(A1(_bJ,1));});return new T1(1,_bq(_bH,function(_bL){return E(_bK);}));},_bM=new T(function(){return unCStr("NUL");}),_bN=function(_bO){var _bP=new T(function(){return B(A1(_bO,0));});return new T1(1,_bq(_bM,function(_bQ){return E(_bP);}));},_bR=new T(function(){return unCStr("STX");}),_bS=function(_bT){var _bU=new T(function(){return B(A1(_bT,2));});return new T1(1,_bq(_bR,function(_bV){return E(_bU);}));},_bW=new T(function(){return unCStr("ETX");}),_bX=function(_bY){var _bZ=new T(function(){return B(A1(_bY,3));});return new T1(1,_bq(_bW,function(_c0){return E(_bZ);}));},_c1=new T(function(){return unCStr("EOT");}),_c2=function(_c3){var _c4=new T(function(){return B(A1(_c3,4));});return new T1(1,_bq(_c1,function(_c5){return E(_c4);}));},_c6=new T(function(){return unCStr("ENQ");}),_c7=function(_c8){var _c9=new T(function(){return B(A1(_c8,5));});return new T1(1,_bq(_c6,function(_ca){return E(_c9);}));},_cb=new T(function(){return unCStr("ACK");}),_cc=function(_cd){var _ce=new T(function(){return B(A1(_cd,6));});return new T1(1,_bq(_cb,function(_cf){return E(_ce);}));},_cg=new T(function(){return unCStr("BEL");}),_ch=function(_ci){var _cj=new T(function(){return B(A1(_ci,7));});return new T1(1,_bq(_cg,function(_ck){return E(_cj);}));},_cl=new T(function(){return unCStr("BS");}),_cm=function(_cn){var _co=new T(function(){return B(A1(_cn,8));});return new T1(1,_bq(_cl,function(_cp){return E(_co);}));},_cq=new T(function(){return unCStr("HT");}),_cr=function(_cs){var _ct=new T(function(){return B(A1(_cs,9));});return new T1(1,_bq(_cq,function(_cu){return E(_ct);}));},_cv=new T(function(){return unCStr("LF");}),_cw=function(_cx){var _cy=new T(function(){return B(A1(_cx,10));});return new T1(1,_bq(_cv,function(_cz){return E(_cy);}));},_cA=new T(function(){return unCStr("VT");}),_cB=function(_cC){var _cD=new T(function(){return B(A1(_cC,11));});return new T1(1,_bq(_cA,function(_cE){return E(_cD);}));},_cF=new T(function(){return unCStr("FF");}),_cG=function(_cH){var _cI=new T(function(){return B(A1(_cH,12));});return new T1(1,_bq(_cF,function(_cJ){return E(_cI);}));},_cK=new T(function(){return unCStr("CR");}),_cL=function(_cM){var _cN=new T(function(){return B(A1(_cM,13));});return new T1(1,_bq(_cK,function(_cO){return E(_cN);}));},_cP=new T(function(){return unCStr("SI");}),_cQ=function(_cR){var _cS=new T(function(){return B(A1(_cR,15));});return new T1(1,_bq(_cP,function(_cT){return E(_cS);}));},_cU=new T(function(){return unCStr("DLE");}),_cV=function(_cW){var _cX=new T(function(){return B(A1(_cW,16));});return new T1(1,_bq(_cU,function(_cY){return E(_cX);}));},_cZ=new T(function(){return unCStr("DC1");}),_d0=function(_d1){var _d2=new T(function(){return B(A1(_d1,17));});return new T1(1,_bq(_cZ,function(_d3){return E(_d2);}));},_d4=new T(function(){return unCStr("DC2");}),_d5=function(_d6){var _d7=new T(function(){return B(A1(_d6,18));});return new T1(1,_bq(_d4,function(_d8){return E(_d7);}));},_d9=new T(function(){return unCStr("DC3");}),_da=function(_db){var _dc=new T(function(){return B(A1(_db,19));});return new T1(1,_bq(_d9,function(_dd){return E(_dc);}));},_de=new T(function(){return unCStr("DC4");}),_df=function(_dg){var _dh=new T(function(){return B(A1(_dg,20));});return new T1(1,_bq(_de,function(_di){return E(_dh);}));},_dj=new T(function(){return unCStr("NAK");}),_dk=function(_dl){var _dm=new T(function(){return B(A1(_dl,21));});return new T1(1,_bq(_dj,function(_dn){return E(_dm);}));},_do=new T(function(){return unCStr("SYN");}),_dp=function(_dq){var _dr=new T(function(){return B(A1(_dq,22));});return new T1(1,_bq(_do,function(_ds){return E(_dr);}));},_dt=new T(function(){return unCStr("ETB");}),_du=function(_dv){var _dw=new T(function(){return B(A1(_dv,23));});return new T1(1,_bq(_dt,function(_dx){return E(_dw);}));},_dy=new T(function(){return unCStr("CAN");}),_dz=function(_dA){var _dB=new T(function(){return B(A1(_dA,24));});return new T1(1,_bq(_dy,function(_dC){return E(_dB);}));},_dD=new T(function(){return unCStr("EM");}),_dE=function(_dF){var _dG=new T(function(){return B(A1(_dF,25));});return new T1(1,_bq(_dD,function(_dH){return E(_dG);}));},_dI=new T(function(){return unCStr("SUB");}),_dJ=function(_dK){var _dL=new T(function(){return B(A1(_dK,26));});return new T1(1,_bq(_dI,function(_dM){return E(_dL);}));},_dN=new T(function(){return unCStr("ESC");}),_dO=function(_dP){var _dQ=new T(function(){return B(A1(_dP,27));});return new T1(1,_bq(_dN,function(_dR){return E(_dQ);}));},_dS=new T(function(){return unCStr("FS");}),_dT=function(_dU){var _dV=new T(function(){return B(A1(_dU,28));});return new T1(1,_bq(_dS,function(_dW){return E(_dV);}));},_dX=new T(function(){return unCStr("GS");}),_dY=function(_dZ){var _e0=new T(function(){return B(A1(_dZ,29));});return new T1(1,_bq(_dX,function(_e1){return E(_e0);}));},_e2=new T(function(){return unCStr("RS");}),_e3=function(_e4){var _e5=new T(function(){return B(A1(_e4,30));});return new T1(1,_bq(_e2,function(_e6){return E(_e5);}));},_e7=new T(function(){return unCStr("US");}),_e8=function(_e9){var _ea=new T(function(){return B(A1(_e9,31));});return new T1(1,_bq(_e7,function(_eb){return E(_ea);}));},_ec=new T(function(){return unCStr("SP");}),_ed=function(_ee){var _ef=new T(function(){return B(A1(_ee,32));});return new T1(1,_bq(_ec,function(_eg){return E(_ef);}));},_eh=new T(function(){return unCStr("DEL");}),_ei=function(_ej){var _ek=new T(function(){return B(A1(_ej,127));});return new T1(1,_bq(_eh,function(_el){return E(_ek);}));},_em=new T(function(){return _bi(new T2(1,function(_en){return new T1(1,_7r(_bI,_bD,_en));},new T2(1,_bN,new T2(1,_bS,new T2(1,_bX,new T2(1,_c2,new T2(1,_c7,new T2(1,_cc,new T2(1,_ch,new T2(1,_cm,new T2(1,_cr,new T2(1,_cw,new T2(1,_cB,new T2(1,_cG,new T2(1,_cL,new T2(1,_cQ,new T2(1,_cV,new T2(1,_d0,new T2(1,_d5,new T2(1,_da,new T2(1,_df,new T2(1,_dk,new T2(1,_dp,new T2(1,_du,new T2(1,_dz,new T2(1,_dE,new T2(1,_dJ,new T2(1,_dO,new T2(1,_dT,new T2(1,_dY,new T2(1,_e3,new T2(1,_e8,new T2(1,_ed,new T2(1,_ei,__Z))))))))))))))))))))))))))))))))));}),_eo=function(_ep){var _eq=new T(function(){return B(A1(_ep,7));}),_er=new T(function(){return B(A1(_ep,8));}),_es=new T(function(){return B(A1(_ep,9));}),_et=new T(function(){return B(A1(_ep,10));}),_eu=new T(function(){return B(A1(_ep,11));}),_ev=new T(function(){return B(A1(_ep,12));}),_ew=new T(function(){return B(A1(_ep,13));}),_ex=new T(function(){return B(A1(_ep,92));}),_ey=new T(function(){return B(A1(_ep,39));}),_ez=new T(function(){return B(A1(_ep,34));}),_eA=new T(function(){var _eB=function(_eC){var _eD=new T(function(){return _3u(E(_eC));}),_eE=function(_eF){var _eG=_a2(_eD,_eF);if(!_b8(_eG,new T1(0,1114111))){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_ep,new T(function(){var _eH=_b5(_eG);if(_eH>>>0>1114111){return _b3(_eH);}else{return _eH;}}));}) : (++C,A1(_ep,new T(function(){var _eH=_b5(_eG);if(_eH>>>0>1114111){return _b3(_eH);}else{return _eH;}})));}};return new T1(1,_86(_eC,_eE));},_eI=new T(function(){var _eJ=new T(function(){return B(A1(_ep,31));}),_eK=new T(function(){return B(A1(_ep,30));}),_eL=new T(function(){return B(A1(_ep,29));}),_eM=new T(function(){return B(A1(_ep,28));}),_eN=new T(function(){return B(A1(_ep,27));}),_eO=new T(function(){return B(A1(_ep,26));}),_eP=new T(function(){return B(A1(_ep,25));}),_eQ=new T(function(){return B(A1(_ep,24));}),_eR=new T(function(){return B(A1(_ep,23));}),_eS=new T(function(){return B(A1(_ep,22));}),_eT=new T(function(){return B(A1(_ep,21));}),_eU=new T(function(){return B(A1(_ep,20));}),_eV=new T(function(){return B(A1(_ep,19));}),_eW=new T(function(){return B(A1(_ep,18));}),_eX=new T(function(){return B(A1(_ep,17));}),_eY=new T(function(){return B(A1(_ep,16));}),_eZ=new T(function(){return B(A1(_ep,15));}),_f0=new T(function(){return B(A1(_ep,14));}),_f1=new T(function(){return B(A1(_ep,6));}),_f2=new T(function(){return B(A1(_ep,5));}),_f3=new T(function(){return B(A1(_ep,4));}),_f4=new T(function(){return B(A1(_ep,3));}),_f5=new T(function(){return B(A1(_ep,2));}),_f6=new T(function(){return B(A1(_ep,1));}),_f7=new T(function(){return B(A1(_ep,0));}),_f8=function(_f9){switch(E(_f9)){case 64:return E(_f7);case 65:return E(_f6);case 66:return E(_f5);case 67:return E(_f4);case 68:return E(_f3);case 69:return E(_f2);case 70:return E(_f1);case 71:return E(_eq);case 72:return E(_er);case 73:return E(_es);case 74:return E(_et);case 75:return E(_eu);case 76:return E(_ev);case 77:return E(_ew);case 78:return E(_f0);case 79:return E(_eZ);case 80:return E(_eY);case 81:return E(_eX);case 82:return E(_eW);case 83:return E(_eV);case 84:return E(_eU);case 85:return E(_eT);case 86:return E(_eS);case 87:return E(_eR);case 88:return E(_eQ);case 89:return E(_eP);case 90:return E(_eO);case 91:return E(_eN);case 92:return E(_eM);case 93:return E(_eL);case 94:return E(_eK);case 95:return E(_eJ);default:return new T0(2);}};return _6j(new T1(0,function(_fa){return (E(_fa)==94)?E(new T1(0,_f8)):new T0(2);}),new T(function(){return B(A1(_em,_ep));}));});return _6j(new T1(1,_7r(_aQ,_aS,_eB)),_eI);});return _6j(new T1(0,function(_fb){switch(E(_fb)){case 34:return E(_ez);case 39:return E(_ey);case 92:return E(_ex);case 97:return E(_eq);case 98:return E(_er);case 102:return E(_ev);case 110:return E(_et);case 114:return E(_ew);case 116:return E(_es);case 118:return E(_eu);default:return new T0(2);}}),_eA);},_fc=function(_fd){return C > 19 ? new F(function(){return A1(_fd,0);}) : (++C,A1(_fd,0));},_fe=function(_ff){var _fg=E(_ff);if(!_fg._){return _fc;}else{var _fh=E(_fg.a),_fi=_fh>>>0,_fj=new T(function(){return _fe(_fg.b);});if(_fi>887){var _fk=u_iswspace(_fh);if(!E(_fk)){return _fc;}else{var _fl=function(_fm){var _fn=new T(function(){return B(A1(_fj,_fm));});return new T1(0,function(_fo){return E(_fn);});};return _fl;}}else{if(_fi==32){var _fp=function(_fq){var _fr=new T(function(){return B(A1(_fj,_fq));});return new T1(0,function(_fs){return E(_fr);});};return _fp;}else{if(_fi-9>>>0>4){if(_fi==160){var _ft=function(_fu){var _fv=new T(function(){return B(A1(_fj,_fu));});return new T1(0,function(_fw){return E(_fv);});};return _ft;}else{return _fc;}}else{var _fx=function(_fy){var _fz=new T(function(){return B(A1(_fj,_fy));});return new T1(0,function(_fA){return E(_fz);});};return _fx;}}}}},_fB=function(_fC){var _fD=new T(function(){return B(_fB(_fC));}),_fE=function(_fF){return (E(_fF)==92)?E(_fD):new T0(2);},_fG=function(_fH){return E(new T1(0,_fE));},_fI=new T1(1,function(_fJ){return C > 19 ? new F(function(){return A2(_fe,_fJ,_fG);}) : (++C,A2(_fe,_fJ,_fG));}),_fK=new T(function(){return B(_eo(function(_fL){return C > 19 ? new F(function(){return A1(_fC,new T2(0,_fL,true));}) : (++C,A1(_fC,new T2(0,_fL,true)));}));}),_fM=function(_fN){var _fO=E(_fN);if(_fO==38){return E(_fD);}else{var _fP=_fO>>>0;if(_fP>887){var _fQ=u_iswspace(_fO);return (E(_fQ)==0)?new T0(2):E(_fI);}else{return (_fP==32)?E(_fI):(_fP-9>>>0>4)?(_fP==160)?E(_fI):new T0(2):E(_fI);}}};return _6j(new T1(0,function(_fR){return (E(_fR)==92)?E(new T1(0,_fM)):new T0(2);}),new T1(0,function(_fS){var _fT=E(_fS);if(_fT==92){return E(_fK);}else{return C > 19 ? new F(function(){return A1(_fC,new T2(0,_fT,false));}) : (++C,A1(_fC,new T2(0,_fT,false)));}}));},_fU=function(_fV,_fW){var _fX=new T(function(){return B(A1(_fW,new T1(1,new T(function(){return B(A1(_fV,__Z));}))));}),_fY=function(_fZ){var _g0=E(_fZ),_g1=E(_g0.a);if(_g1==34){if(!E(_g0.b)){return E(_fX);}else{return C > 19 ? new F(function(){return _fU(function(_g2){return C > 19 ? new F(function(){return A1(_fV,new T2(1,_g1,_g2));}) : (++C,A1(_fV,new T2(1,_g1,_g2)));},_fW);}) : (++C,_fU(function(_g2){return C > 19 ? new F(function(){return A1(_fV,new T2(1,_g1,_g2));}) : (++C,A1(_fV,new T2(1,_g1,_g2)));},_fW));}}else{return C > 19 ? new F(function(){return _fU(function(_g3){return C > 19 ? new F(function(){return A1(_fV,new T2(1,_g1,_g3));}) : (++C,A1(_fV,new T2(1,_g1,_g3)));},_fW);}) : (++C,_fU(function(_g3){return C > 19 ? new F(function(){return A1(_fV,new T2(1,_g1,_g3));}) : (++C,A1(_fV,new T2(1,_g1,_g3)));},_fW));}};return C > 19 ? new F(function(){return _fB(_fY);}) : (++C,_fB(_fY));},_g4=new T(function(){return unCStr("_\'");}),_g5=function(_g6){var _g7=u_iswalnum(_g6);if(!E(_g7)){return _aD(_6U,_g6,_g4);}else{return true;}},_g8=function(_g9){return _g5(E(_g9));},_ga=new T(function(){return unCStr(",;()[]{}`");}),_gb=new T(function(){return unCStr("=>");}),_gc=new T(function(){return unCStr("~");}),_gd=new T(function(){return unCStr("@");}),_ge=new T(function(){return unCStr("->");}),_gf=new T(function(){return unCStr("<-");}),_gg=new T(function(){return unCStr("|");}),_gh=new T(function(){return unCStr("\\");}),_gi=new T(function(){return unCStr("=");}),_gj=new T(function(){return unCStr("::");}),_gk=new T(function(){return unCStr("..");}),_gl=function(_gm){var _gn=new T(function(){return B(A1(_gm,new T0(6)));}),_go=new T(function(){var _gp=new T(function(){var _gq=function(_gr){var _gs=new T(function(){return B(A1(_gm,new T1(0,_gr)));});return new T1(0,function(_gt){return (E(_gt)==39)?E(_gs):new T0(2);});};return B(_eo(_gq));}),_gu=function(_gv){var _gw=E(_gv);switch(_gw){case 39:return new T0(2);case 92:return E(_gp);default:var _gx=new T(function(){return B(A1(_gm,new T1(0,_gw)));});return new T1(0,function(_gy){return (E(_gy)==39)?E(_gx):new T0(2);});}},_gz=new T(function(){var _gA=new T(function(){return B(_fU(_1V,_gm));}),_gB=new T(function(){var _gC=new T(function(){var _gD=new T(function(){var _gE=function(_gF){var _gG=E(_gF),_gH=u_iswalpha(_gG);return (E(_gH)==0)?(_gG==95)?new T1(1,_7R(_g8,function(_gI){return C > 19 ? new F(function(){return A1(_gm,new T1(3,new T2(1,_gG,_gI)));}) : (++C,A1(_gm,new T1(3,new T2(1,_gG,_gI))));})):new T0(2):new T1(1,_7R(_g8,function(_gJ){return C > 19 ? new F(function(){return A1(_gm,new T1(3,new T2(1,_gG,_gJ)));}) : (++C,A1(_gm,new T1(3,new T2(1,_gG,_gJ))));}));};return _6j(new T1(0,_gE),new T(function(){return new T1(1,_7r(_8Z,_az,_gm));}));}),_gK=function(_gL){return (!_aD(_6U,_gL,_aI))?new T0(2):new T1(1,_7R(_aJ,function(_gM){var _gN=new T2(1,_gL,_gM);if(!_aD(new T2(0,_6Z,_74),_gN,new T2(1,_gk,new T2(1,_gj,new T2(1,_gi,new T2(1,_gh,new T2(1,_gg,new T2(1,_gf,new T2(1,_ge,new T2(1,_gd,new T2(1,_gc,new T2(1,_gb,__Z)))))))))))){return C > 19 ? new F(function(){return A1(_gm,new T1(4,_gN));}) : (++C,A1(_gm,new T1(4,_gN)));}else{return C > 19 ? new F(function(){return A1(_gm,new T1(2,_gN));}) : (++C,A1(_gm,new T1(2,_gN)));}}));};return _6j(new T1(0,_gK),_gD);});return _6j(new T1(0,function(_gO){if(!_aD(_6U,_gO,_ga)){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_gm,new T1(2,new T2(1,_gO,__Z)));}) : (++C,A1(_gm,new T1(2,new T2(1,_gO,__Z))));}}),_gC);});return _6j(new T1(0,function(_gP){return (E(_gP)==34)?E(_gA):new T0(2);}),_gB);});return _6j(new T1(0,function(_gQ){return (E(_gQ)==39)?E(new T1(0,_gu)):new T0(2);}),_gz);});return _6j(new T1(1,function(_gR){return (E(_gR)._==0)?E(_gn):new T0(2);}),_go);},_gS=function(_gT,_gU){var _gV=new T(function(){var _gW=new T(function(){var _gX=function(_gY){var _gZ=new T(function(){var _h0=new T(function(){return B(A1(_gU,_gY));});return B(_gl(function(_h1){var _h2=E(_h1);return (_h2._==2)?(!_6P(_h2.a,_6O))?new T0(2):E(_h0):new T0(2);}));}),_h3=function(_h4){return E(_gZ);};return new T1(1,function(_h5){return C > 19 ? new F(function(){return A2(_fe,_h5,_h3);}) : (++C,A2(_fe,_h5,_h3));});};return B(A2(_gT,0,_gX));});return B(_gl(function(_h6){var _h7=E(_h6);return (_h7._==2)?(!_6P(_h7.a,_6N))?new T0(2):E(_gW):new T0(2);}));}),_h8=function(_h9){return E(_gV);};return function(_ha){return C > 19 ? new F(function(){return A2(_fe,_ha,_h8);}) : (++C,A2(_fe,_ha,_h8));};},_hb=function(_hc,_hd){var _he=function(_hf){var _hg=new T(function(){return B(A1(_hc,_hf));}),_hh=function(_hi){return _6j(B(A1(_hg,_hi)),new T(function(){return new T1(1,_gS(_he,_hi));}));};return _hh;},_hj=new T(function(){return B(A1(_hc,_hd));}),_hk=function(_hl){return _6j(B(A1(_hj,_hl)),new T(function(){return new T1(1,_gS(_he,_hl));}));};return _hk;},_hm=function(_hn,_ho){var _hp=function(_hq,_hr){var _hs=function(_ht){return C > 19 ? new F(function(){return A1(_hr,new T(function(){return  -E(_ht);}));}) : (++C,A1(_hr,new T(function(){return  -E(_ht);})));},_hu=new T(function(){return B(_gl(function(_hv){return C > 19 ? new F(function(){return A3(_hn,_hv,_hq,_hs);}) : (++C,A3(_hn,_hv,_hq,_hs));}));}),_hw=function(_hx){return E(_hu);},_hy=function(_hz){return C > 19 ? new F(function(){return A2(_fe,_hz,_hw);}) : (++C,A2(_fe,_hz,_hw));},_hA=new T(function(){return B(_gl(function(_hB){var _hC=E(_hB);if(_hC._==4){var _hD=E(_hC.a);if(!_hD._){return C > 19 ? new F(function(){return A3(_hn,_hC,_hq,_hr);}) : (++C,A3(_hn,_hC,_hq,_hr));}else{if(E(_hD.a)==45){if(!E(_hD.b)._){return E(new T1(1,_hy));}else{return C > 19 ? new F(function(){return A3(_hn,_hC,_hq,_hr);}) : (++C,A3(_hn,_hC,_hq,_hr));}}else{return C > 19 ? new F(function(){return A3(_hn,_hC,_hq,_hr);}) : (++C,A3(_hn,_hC,_hq,_hr));}}}else{return C > 19 ? new F(function(){return A3(_hn,_hC,_hq,_hr);}) : (++C,A3(_hn,_hC,_hq,_hr));}}));}),_hE=function(_hF){return E(_hA);};return new T1(1,function(_hG){return C > 19 ? new F(function(){return A2(_fe,_hG,_hE);}) : (++C,A2(_fe,_hG,_hE));});};return _hb(_hp,_ho);},_hH=new T(function(){return 1/0;}),_hI=function(_hJ,_hK){return C > 19 ? new F(function(){return A1(_hK,_hH);}) : (++C,A1(_hK,_hH));},_hL=new T(function(){return 0/0;}),_hM=function(_hN,_hO){return C > 19 ? new F(function(){return A1(_hO,_hL);}) : (++C,A1(_hO,_hL));},_hP=new T(function(){return unCStr("NaN");}),_hQ=new T(function(){return unCStr("Infinity");}),_hR=new T(function(){return unCStr("base");}),_hS=new T(function(){return unCStr("GHC.Exception");}),_hT=new T(function(){return unCStr("ArithException");}),_hU=function(_hV){return E(new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_hR,_hS,_hT),__Z,__Z));},_hW=new T(function(){return unCStr("Ratio has zero denominator");}),_hX=new T(function(){return unCStr("denormal");}),_hY=new T(function(){return unCStr("divide by zero");}),_hZ=new T(function(){return unCStr("loss of precision");}),_i0=new T(function(){return unCStr("arithmetic underflow");}),_i1=new T(function(){return unCStr("arithmetic overflow");}),_i2=function(_i3,_i4){switch(E(_i3)){case 0:return _x(_i1,_i4);case 1:return _x(_i0,_i4);case 2:return _x(_hZ,_i4);case 3:return _x(_hY,_i4);case 4:return _x(_hX,_i4);default:return _x(_hW,_i4);}},_i5=function(_i6){return _i2(_i6,__Z);},_i7=new T(function(){return new T5(0,_hU,new T3(0,function(_i8,_i9,_ia){return _i2(_i9,_ia);},_i5,function(_ib,_ic){return _1q(_i2,_ib,_ic);}),_id,function(_ie){var _if=E(_ie);return _m(_k(_if.a),_hU,_if.b);},_i5);}),_id=function(_4v){return new T2(0,_i7,_4v);},_ig=new T(function(){return die(new T(function(){return _id(3);}));}),_ih=function(_ii,_ij){var _ik=E(_ii);if(!_ik._){var _il=_ik.a,_im=E(_ij);return (_im._==0)?_il==_im.a:(I_compareInt(_im.a,_il)==0)?true:false;}else{var _in=_ik.a,_io=E(_ij);return (_io._==0)?(I_compareInt(_in,_io.a)==0)?true:false:(I_compare(_in,_io.a)==0)?true:false;}},_ip=new T1(0,0),_iq=function(_ir,_is){while(1){var _it=E(_ir);if(!_it._){var _iu=E(_it.a);if(_iu==(-2147483648)){_ir=new T1(1,I_fromInt(-2147483648));continue;}else{var _iv=E(_is);if(!_iv._){return new T1(0,_iu%_iv.a);}else{_ir=new T1(1,I_fromInt(_iu));_is=_iv;continue;}}}else{var _iw=_it.a,_ix=E(_is);return (_ix._==0)?new T1(1,I_rem(_iw,I_fromInt(_ix.a))):new T1(1,I_rem(_iw,_ix.a));}}},_iy=function(_iz,_iA){if(!_ih(_iA,_ip)){return _iq(_iz,_iA);}else{return E(_ig);}},_iB=function(_iC,_iD){while(1){if(!_ih(_iD,_ip)){var _iE=_iD,_iF=_iy(_iC,_iD);_iC=_iE;_iD=_iF;continue;}else{return E(_iC);}}},_iG=function(_iH){var _iI=E(_iH);if(!_iI._){var _iJ=E(_iI.a);return (_iJ==(-2147483648))?E(_9f):(_iJ<0)?new T1(0, -_iJ):_iI;}else{var _iK=_iI.a;return (I_compareInt(_iK,0)>=0)?_iI:new T1(1,I_negate(_iK));}},_iL=function(_iM,_iN){while(1){var _iO=E(_iM);if(!_iO._){var _iP=E(_iO.a);if(_iP==(-2147483648)){_iM=new T1(1,I_fromInt(-2147483648));continue;}else{var _iQ=E(_iN);if(!_iQ._){return new T1(0,quot(_iP,_iQ.a));}else{_iM=new T1(1,I_fromInt(_iP));_iN=_iQ;continue;}}}else{var _iR=_iO.a,_iS=E(_iN);return (_iS._==0)?new T1(0,I_toInt(I_quot(_iR,I_fromInt(_iS.a)))):new T1(1,I_quot(_iR,_iS.a));}}},_iT=new T(function(){return die(new T(function(){return _id(5);}));}),_iU=function(_iV,_iW){if(!_ih(_iW,_ip)){var _iX=_iB(_iG(_iV),_iG(_iW));return (!_ih(_iX,_ip))?new T2(0,_iL(_iV,_iX),_iL(_iW,_iX)):E(_ig);}else{return E(_iT);}},_iY=new T1(0,1),_iZ=new T(function(){return err(new T(function(){return unCStr("Negative exponent");}));}),_j0=new T1(0,2),_j1=new T(function(){return _ih(_j0,_ip);}),_j2=function(_j3,_j4){while(1){var _j5=E(_j3);if(!_j5._){var _j6=_j5.a,_j7=E(_j4);if(!_j7._){var _j8=_j7.a,_j9=subC(_j6,_j8);if(!E(_j9.b)){return new T1(0,_j9.a);}else{_j3=new T1(1,I_fromInt(_j6));_j4=new T1(1,I_fromInt(_j8));continue;}}else{_j3=new T1(1,I_fromInt(_j6));_j4=_j7;continue;}}else{var _ja=E(_j4);if(!_ja._){_j3=_j5;_j4=new T1(1,I_fromInt(_ja.a));continue;}else{return new T1(1,I_sub(_j5.a,_ja.a));}}}},_jb=function(_jc,_jd,_je){while(1){if(!E(_j1)){if(!_ih(_iq(_jd,_j0),_ip)){if(!_ih(_jd,_iY)){var _jf=_9x(_jc,_jc),_jg=_iL(_j2(_jd,_iY),_j0),_jh=_9x(_jc,_je);_jc=_jf;_jd=_jg;_je=_jh;continue;}else{return _9x(_jc,_je);}}else{var _jf=_9x(_jc,_jc),_jg=_iL(_jd,_j0);_jc=_jf;_jd=_jg;continue;}}else{return E(_ig);}}},_ji=function(_jj,_jk){while(1){if(!E(_j1)){if(!_ih(_iq(_jk,_j0),_ip)){if(!_ih(_jk,_iY)){return _jb(_9x(_jj,_jj),_iL(_j2(_jk,_iY),_j0),_jj);}else{return E(_jj);}}else{var _jl=_9x(_jj,_jj),_jm=_iL(_jk,_j0);_jj=_jl;_jk=_jm;continue;}}else{return E(_ig);}}},_jn=function(_jo,_jp){var _jq=E(_jo);if(!_jq._){var _jr=_jq.a,_js=E(_jp);return (_js._==0)?_jr<_js.a:I_compareInt(_js.a,_jr)>0;}else{var _jt=_jq.a,_ju=E(_jp);return (_ju._==0)?I_compareInt(_jt,_ju.a)<0:I_compare(_jt,_ju.a)<0;}},_jv=function(_jw,_jx){if(!_jn(_jx,_ip)){if(!_ih(_jx,_ip)){return _ji(_jw,_jx);}else{return E(_iY);}}else{return E(_iZ);}},_jy=new T1(0,1),_jz=new T1(0,0),_jA=new T1(0,-1),_jB=function(_jC){var _jD=E(_jC);if(!_jD._){var _jE=_jD.a;return (_jE>=0)?(E(_jE)==0)?E(_jz):E(_95):E(_jA);}else{var _jF=I_compareInt(_jD.a,0);return (_jF<=0)?(E(_jF)==0)?E(_jz):E(_jA):E(_95);}},_jG=function(_jH,_jI,_jJ){while(1){var _jK=E(_jJ);if(!_jK._){if(!_jn(_jH,_9K)){return new T2(0,_9x(_jI,B(_jv(_9k,_jH))),_iY);}else{var _jL=B(_jv(_9k,_9g(_jH)));return _iU(_9x(_jI,_jB(_jL)),_iG(_jL));}}else{var _jM=_j2(_jH,_jy),_jN=_96(_9x(_jI,_9k),_3u(E(_jK.a)));_jH=_jM;_jI=_jN;_jJ=_jK.b;continue;}}},_jO=function(_jP,_jQ){var _jR=E(_jP);if(!_jR._){var _jS=_jR.a,_jT=E(_jQ);return (_jT._==0)?_jS>=_jT.a:I_compareInt(_jT.a,_jS)<=0;}else{var _jU=_jR.a,_jV=E(_jQ);return (_jV._==0)?I_compareInt(_jU,_jV.a)>=0:I_compare(_jU,_jV.a)>=0;}},_jW=function(_jX){var _jY=E(_jX);if(!_jY._){var _jZ=_jY.b;return _iU(_9x(_9L(new T(function(){return _3u(E(_jY.a));}),new T(function(){return _9l(_jZ,0);},1),_9q(_9u,_jZ)),_jy),_jy);}else{var _k0=_jY.a,_k1=_jY.c,_k2=E(_jY.b);if(!_k2._){var _k3=E(_k1);if(!_k3._){return _iU(_9x(_a2(_9k,_k0),_jy),_jy);}else{var _k4=_k3.a;if(!_jO(_k4,_9K)){var _k5=B(_jv(_9k,_9g(_k4)));return _iU(_9x(_a2(_9k,_k0),_jB(_k5)),_iG(_k5));}else{return _iU(_9x(_9x(_a2(_9k,_k0),B(_jv(_9k,_k4))),_jy),_jy);}}}else{var _k6=_k2.a,_k7=E(_k1);if(!_k7._){return _jG(_9K,_a2(_9k,_k0),_k6);}else{return _jG(_k7.a,_a2(_9k,_k0),_k6);}}}},_k8=function(_k9,_ka){while(1){var _kb=E(_ka);if(!_kb._){return __Z;}else{if(!B(A1(_k9,_kb.a))){return _kb;}else{_ka=_kb.b;continue;}}}},_kc=function(_kd,_ke){var _kf=E(_kd);if(!_kf._){var _kg=_kf.a,_kh=E(_ke);return (_kh._==0)?_kg>_kh.a:I_compareInt(_kh.a,_kg)<0;}else{var _ki=_kf.a,_kj=E(_ke);return (_kj._==0)?I_compareInt(_ki,_kj.a)>0:I_compare(_ki,_kj.a)>0;}},_kk=function(_kl,_km){return E(_kl)==E(_km);},_kn=function(_ko){return _kk(0,_ko);},_kp=new T1(1,new T2(0,E(_9K),E(_iY))),_kq=function(_kr,_ks,_kt){var _ku=E(_kt);if(!_ku._){return new T1(1,new T(function(){var _kv=_jW(_ku);return new T2(0,E(_kv.a),E(_kv.b));}));}else{var _kw=E(_ku.c);if(!_kw._){return new T1(1,new T(function(){var _kx=_jW(_ku);return new T2(0,E(_kx.a),E(_kx.b));}));}else{var _ky=_kw.a;if(!_kc(_ky,new T1(0,2147483647))){if(!_jn(_ky,new T1(0,-2147483648))){var _kz=function(_kA){var _kB=_kA+_b5(_ky)|0;return (_kB<=(E(_ks)+3|0))?(_kB>=(E(_kr)-3|0))?new T1(1,new T(function(){var _kC=_jW(_ku);return new T2(0,E(_kC.a),E(_kC.b));})):E(_kp):__Z;},_kD=_k8(_kn,_ku.a);if(!_kD._){var _kE=E(_ku.b);if(!_kE._){return E(_kp);}else{var _kF=_4w(_kn,_kE.a);if(!E(_kF.b)._){return E(_kp);}else{return _kz( -_9l(_kF.a,0));}}}else{return _kz(_9l(_kD,0));}}else{return __Z;}}else{return __Z;}}}},_kG=function(_kH,_kI){return new T0(2);},_kJ=new T1(0,1),_kK=function(_kL,_kM){var _kN=E(_kL);if(!_kN._){var _kO=_kN.a,_kP=E(_kM);if(!_kP._){var _kQ=_kP.a;return (_kO!=_kQ)?(_kO>_kQ)?2:0:1;}else{var _kR=I_compareInt(_kP.a,_kO);return (_kR<=0)?(_kR>=0)?1:2:0;}}else{var _kS=_kN.a,_kT=E(_kM);if(!_kT._){var _kU=I_compareInt(_kS,_kT.a);return (_kU>=0)?(_kU<=0)?1:2:0;}else{var _kV=I_compare(_kS,_kT.a);return (_kV>=0)?(_kV<=0)?1:2:0;}}},_kW=function(_kX,_kY){var _kZ=E(_kX);return (_kZ._==0)?_kZ.a*Math.pow(2,_kY):I_toNumber(_kZ.a)*Math.pow(2,_kY);},_l0=function(_l1,_l2){while(1){var _l3=E(_l1);if(!_l3._){var _l4=E(_l3.a);if(_l4==(-2147483648)){_l1=new T1(1,I_fromInt(-2147483648));continue;}else{var _l5=E(_l2);if(!_l5._){var _l6=_l5.a;return new T2(0,new T1(0,quot(_l4,_l6)),new T1(0,_l4%_l6));}else{_l1=new T1(1,I_fromInt(_l4));_l2=_l5;continue;}}}else{var _l7=E(_l2);if(!_l7._){_l1=_l3;_l2=new T1(1,I_fromInt(_l7.a));continue;}else{var _l8=I_quotRem(_l3.a,_l7.a);return new T2(0,new T1(1,_l8.a),new T1(1,_l8.b));}}}},_l9=new T1(0,0),_la=function(_lb,_lc,_ld){if(!_ih(_ld,_l9)){var _le=_l0(_lc,_ld),_lf=_le.a;switch(_kK(_3J(_le.b,1),_ld)){case 0:return _kW(_lf,_lb);case 1:if(!(_b5(_lf)&1)){return _kW(_lf,_lb);}else{return _kW(_96(_lf,_kJ),_lb);}break;default:return _kW(_96(_lf,_kJ),_lb);}}else{return E(_ig);}},_lg=function(_lh){var _li=function(_lj,_lk){while(1){if(!_jn(_lj,_lh)){if(!_kc(_lj,_lh)){if(!_ih(_lj,_lh)){return C > 19 ? new F(function(){return _4R("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2");}) : (++C,_4R("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2"));}else{return E(_lk);}}else{return _lk-1|0;}}else{var _ll=_3J(_lj,1),_lm=_lk+1|0;_lj=_ll;_lk=_lm;continue;}}};return C > 19 ? new F(function(){return _li(_95,0);}) : (++C,_li(_95,0));},_ln=function(_lo){var _lp=E(_lo);if(!_lp._){var _lq=_lp.a>>>0;if(!_lq){return -1;}else{var _lr=function(_ls,_lt){while(1){if(_ls>=_lq){if(_ls<=_lq){if(_ls!=_lq){return C > 19 ? new F(function(){return _4R("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");}) : (++C,_4R("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2"));}else{return E(_lt);}}else{return _lt-1|0;}}else{var _lu=imul(_ls,2)>>>0,_lv=_lt+1|0;_ls=_lu;_lt=_lv;continue;}}};return C > 19 ? new F(function(){return _lr(1,0);}) : (++C,_lr(1,0));}}else{return C > 19 ? new F(function(){return _lg(_lp);}) : (++C,_lg(_lp));}},_lw=function(_lx){var _ly=E(_lx);if(!_ly._){var _lz=_ly.a>>>0;if(!_lz){return new T2(0,-1,0);}else{var _lA=function(_lB,_lC){while(1){if(_lB>=_lz){if(_lB<=_lz){if(_lB!=_lz){return C > 19 ? new F(function(){return _4R("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");}) : (++C,_4R("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2"));}else{return E(_lC);}}else{return _lC-1|0;}}else{var _lD=imul(_lB,2)>>>0,_lE=_lC+1|0;_lB=_lD;_lC=_lE;continue;}}};return new T2(0,B(_lA(1,0)),(_lz&_lz-1>>>0)>>>0&4294967295);}}else{var _lF=_ly.a;return new T2(0,B(_ln(_ly)),I_compareInt(I_and(_lF,I_sub(_lF,I_fromInt(1))),0));}},_lG=function(_lH,_lI){while(1){var _lJ=E(_lH);if(!_lJ._){var _lK=_lJ.a,_lL=E(_lI);if(!_lL._){return new T1(0,(_lK>>>0&_lL.a>>>0)>>>0&4294967295);}else{_lH=new T1(1,I_fromInt(_lK));_lI=_lL;continue;}}else{var _lM=E(_lI);if(!_lM._){_lH=_lJ;_lI=new T1(1,I_fromInt(_lM.a));continue;}else{return new T1(1,I_and(_lJ.a,_lM.a));}}}},_lN=function(_lO,_lP){var _lQ=E(_lO);if(!_lQ._){var _lR=(_lQ.a>>>0&(2<<_lP>>>0)-1>>>0)>>>0,_lS=1<<_lP>>>0;return (_lS<=_lR)?(_lS>=_lR)?1:2:0;}else{var _lT=_lG(_lQ,_j2(_3J(new T1(0,2),_lP),_95)),_lU=_3J(_95,_lP);return (!_kc(_lU,_lT))?(!_jn(_lU,_lT))?1:2:0;}},_lV=function(_lW,_lX){while(1){var _lY=E(_lW);if(!_lY._){_lW=new T1(1,I_fromInt(_lY.a));continue;}else{return new T1(1,I_shiftRight(_lY.a,_lX));}}},_lZ=function(_m0,_m1,_m2,_m3){var _m4=_lw(_m3),_m5=_m4.a;if(!E(_m4.b)){var _m6=B(_ln(_m2));if(_m6<((_m5+_m0|0)-1|0)){var _m7=_m5+(_m0-_m1|0)|0;if(_m7>0){if(_m7>_m6){if(_m7<=(_m6+1|0)){if(!E(_lw(_m2).b)){return 0;}else{return _kW(_kJ,_m0-_m1|0);}}else{return 0;}}else{var _m8=_lV(_m2,_m7);switch(_lN(_m2,_m7-1|0)){case 0:return _kW(_m8,_m0-_m1|0);case 1:if(!(_b5(_m8)&1)){return _kW(_m8,_m0-_m1|0);}else{return _kW(_96(_m8,_kJ),_m0-_m1|0);}break;default:return _kW(_96(_m8,_kJ),_m0-_m1|0);}}}else{return _kW(_m2,(_m0-_m1|0)-_m7|0);}}else{if(_m6>=_m1){var _m9=_lV(_m2,(_m6+1|0)-_m1|0);switch(_lN(_m2,_m6-_m1|0)){case 0:return _kW(_m9,((_m6-_m5|0)+1|0)-_m1|0);case 2:return _kW(_96(_m9,_kJ),((_m6-_m5|0)+1|0)-_m1|0);default:if(!(_b5(_m9)&1)){return _kW(_m9,((_m6-_m5|0)+1|0)-_m1|0);}else{return _kW(_96(_m9,_kJ),((_m6-_m5|0)+1|0)-_m1|0);}}}else{return _kW(_m2, -_m5);}}}else{var _ma=B(_ln(_m2))-_m5|0,_mb=function(_mc){var _md=function(_me,_mf){if(!_b8(_3J(_mf,_m1),_me)){return _la(_mc-_m1|0,_me,_mf);}else{return _la((_mc-_m1|0)+1|0,_me,_3J(_mf,1));}};if(_mc>=_m1){if(_mc!=_m1){return _md(_m2,new T(function(){return _3J(_m3,_mc-_m1|0);}));}else{return _md(_m2,_m3);}}else{return _md(new T(function(){return _3J(_m2,_m1-_mc|0);}),_m3);}};if(_m0>_ma){return C > 19 ? new F(function(){return _mb(_m0);}) : (++C,_mb(_m0));}else{return C > 19 ? new F(function(){return _mb(_ma);}) : (++C,_mb(_ma));}}},_mg=new T(function(){return 0/0;}),_mh=new T(function(){return -1/0;}),_mi=new T(function(){return 1/0;}),_mj=function(_mk,_ml){if(!_ih(_ml,_l9)){if(!_ih(_mk,_l9)){if(!_jn(_mk,_l9)){return C > 19 ? new F(function(){return _lZ(-1021,53,_mk,_ml);}) : (++C,_lZ(-1021,53,_mk,_ml));}else{return  -B(_lZ(-1021,53,_9g(_mk),_ml));}}else{return 0;}}else{return (!_ih(_mk,_l9))?(!_jn(_mk,_l9))?E(_mi):E(_mh):E(_mg);}},_mm=function(_mn){var _mo=E(_mn);switch(_mo._){case 3:var _mp=_mo.a;return (!_6P(_mp,_hQ))?(!_6P(_mp,_hP))?_kG:_hM:_hI;case 5:var _mq=_kq(-1021,1024,_mo.a);if(!_mq._){return _hI;}else{var _mr=new T(function(){var _ms=E(_mq.a);return B(_mj(_ms.a,_ms.b));});return function(_mt,_mu){return C > 19 ? new F(function(){return A1(_mu,_mr);}) : (++C,A1(_mu,_mr));};}break;default:return _kG;}},_mv=function(_mw){var _mx=function(_my){return E(new T2(3,_mw,_7i));};return new T1(1,function(_mz){return C > 19 ? new F(function(){return A2(_fe,_mz,_mx);}) : (++C,A2(_fe,_mz,_mx));});},_mA=new T(function(){return B(A3(_hm,_mm,0,_mv));}),_mB=function(_mC,_mD){while(1){var _mE=E(_mC);if(!_mE._){return E(_mD);}else{_mC=_mE.b;_mD=_mE.a;continue;}}},_mF=function(_mG){var _mH=E(_mG);if(!_mH._){return __Z;}else{var _mI=_mH.a,_mJ=new T(function(){if(E(_mB(_mI,_5Y))==37){var _mK=_5Z(_66(_mA,new T(function(){return _5V(_mI);})));if(!_mK._){return E(_6h);}else{if(!E(_mK.b)._){return E(_mK.a)/100;}else{return E(_6g);}}}else{var _mL=_5Z(_66(_mA,_mI));if(!_mL._){return E(_6h);}else{if(!E(_mL.b)._){return E(_mL.a);}else{return E(_6g);}}}});return new T1(1,_mJ);}},_mM=function(_mN,_){var _mO=E(_mN);if(!_mO._){return E(_4T);}else{var _mP=_mO.a,_mQ=E(_mO.b);if(!_mQ._){return E(_4T);}else{var _mR=_mQ.a,_mS=E(_mQ.b);if(!_mS._){return E(_4T);}else{var _mT=_mS.a,_mU=E(_mS.b);if(!_mU._){return E(_4T);}else{var _mV=_mU.a,_mW=E(_mU.b);if(!_mW._){return E(_4T);}else{var _mX=_mW.a,_mY=E(_mW.b);if(!_mY._){return E(_4T);}else{var _mZ=E(_mY.b);if(!_mZ._){return E(_4T);}else{if(!E(_mZ.b)._){var _n0=function(_){var _n1=_44(E(_mP),"value"),_n2=_44(E(_mR),"value"),_n3=_44(E(_mT),"value"),_n4=_44(E(_mV),"value"),_n5=_44(E(_mX),"value"),_n6=_mF(new T1(1,new T(function(){var _n7=String(_n1);return fromJSStr(_n7);})));if(!_n6._){return 0;}else{var _n8=_mF(new T1(1,new T(function(){var _n9=String(_n2);return fromJSStr(_n9);})));if(!_n8._){return 0;}else{var _na=_mF(new T1(1,new T(function(){var _nb=String(_n3);return fromJSStr(_nb);})));if(!_na._){return 0;}else{var _nc=_mF(new T1(1,new T(function(){var _nd=String(_n4);return fromJSStr(_nd);})));if(!_nc._){return 0;}else{var _ne=_mF(new T1(1,new T(function(){var _nf=String(_n5);return fromJSStr(_nf);})));if(!_ne._){return 0;}else{var _ng=toJSStr(E(_4V)),_nh=E(_n6.a),_ni=E(_n8.a),_nj=E(_na.a),_nk=E(_nc.a),_nl=E(_ne.a),_nm=_nl*_nl/2,_nn=Math.log(_ni/_nh),_no=( -_nn+_nk*(_nj+_nm))/_nl/Math.sqrt(_nk),_np=( -_nn+_nk*(_nj+ -_nm))/_nl/Math.sqrt(_nk),_nq=_45(E(_mY.a),_ng,toJSStr(_3N(2,_nh*0.5*(1-_2v( -_no*0.7071067811865475))-_ni*Math.exp( -_nj*_nk)*0.5*(1-_2v( -_np*0.7071067811865475))))),_nr=_45(E(_mZ.a),_ng,toJSStr(_3N(2,_ni*Math.exp( -_nj*_nk)*0.5*(1-_2v(_np*0.7071067811865475))-_nh*0.5*(1-_2v(_no*0.7071067811865475)))));return _2r(_);}}}}}},_ns=B(A(_5k,[_2u,_2s,_2n,_mP,1,function(_nt,_){return _n0(_);},_])),_nu=B(A(_5k,[_2u,_2s,_2n,_mR,1,function(_nv,_){return _n0(_);},_])),_nw=B(A(_5k,[_2u,_2s,_2a,_mT,2,function(_nx,_){return _n0(_);},_])),_ny=B(A(_5k,[_2u,_2s,_2a,_mV,2,function(_nz,_){return _n0(_);},_]));return C > 19 ? new F(function(){return A(_5k,[_2u,_2s,_2a,_mX,2,function(_nA,_){return _n0(_);},_]);}) : (++C,A(_5k,[_2u,_2s,_2a,_mX,2,function(_nA,_){return _n0(_);},_]));}else{return E(_4T);}}}}}}}}},_nB=(function(id){return document.getElementById(id);}),_nC=new T(function(){return err(new T(function(){return unCStr("Maybe.fromJust: Nothing");}));}),_nD=function(_nE){var _nF=E(_nE);return (_nF._==0)?E(_nC):E(_nF.a);},_nG=function(_nH,_nI){while(1){var _nJ=(function(_nK,_nL){var _nM=E(_nK);if(!_nM._){return __Z;}else{var _nN=_nM.b,_nO=E(_nL);if(!_nO._){return __Z;}else{var _nP=_nO.b;if(!E(_nO.a)._){return new T2(1,_nM.a,new T(function(){return _nG(_nN,_nP);}));}else{_nH=_nN;_nI=_nP;return __continue;}}}})(_nH,_nI);if(_nJ!=__continue){return _nJ;}}},_nQ=new T(function(){return unAppCStr("[]",__Z);}),_nR=function(_nS){var _nT=E(_nS);if(!_nT._){return E(new T2(1,93,__Z));}else{var _nU=new T(function(){return _x(fromJSStr(E(_nT.a)),new T(function(){return _nR(_nT.b);},1));});return new T2(1,44,_nU);}},_nV=function(_nW,_nX){var _nY=new T(function(){var _nZ=_nG(_nW,_nX);if(!_nZ._){return E(_nQ);}else{var _o0=new T(function(){return _x(fromJSStr(E(_nZ.a)),new T(function(){return _nR(_nZ.b);},1));});return new T2(1,91,_o0);}});return err(unAppCStr("Elements with the following IDs could not be found: ",_nY));},_o1=function(_o2){while(1){var _o3=E(_o2);if(!_o3._){return false;}else{if(!E(_o3.a)._){return true;}else{_o2=_o3.b;continue;}}}},_o4=function(_o5,_o6,_o7){var _o8=_4Y(_o5),_o9=function(_oa){if(!_o1(_oa)){return C > 19 ? new F(function(){return A1(_o7,new T(function(){return _9q(_nD,_oa);}));}) : (++C,A1(_o7,new T(function(){return _9q(_nD,_oa);})));}else{return _nV(_o6,_oa);}},_ob=new T(function(){var _oc=new T(function(){return B(A2(_5i,_o8,__Z));}),_od=function(_oe){var _of=E(_oe);if(!_of._){return E(_oc);}else{var _og=new T(function(){return B(_od(_of.b));}),_oh=function(_oi){return C > 19 ? new F(function(){return A3(_50,_o8,_og,function(_oj){return C > 19 ? new F(function(){return A2(_5i,_o8,new T2(1,_oi,_oj));}) : (++C,A2(_5i,_o8,new T2(1,_oi,_oj)));});}) : (++C,A3(_50,_o8,_og,function(_oj){return C > 19 ? new F(function(){return A2(_5i,_o8,new T2(1,_oi,_oj));}) : (++C,A2(_5i,_o8,new T2(1,_oi,_oj)));}));},_ok=new T(function(){return B(A2(_5e,_o5,function(_){var _ol=_nB(E(_of.a)),_om=__eq(_ol,E(_5d));return (E(_om)==0)?new T1(1,_ol):__Z;}));});return C > 19 ? new F(function(){return A3(_50,_o8,_ok,_oh);}) : (++C,A3(_50,_o8,_ok,_oh));}};return B(_od(_o6));});return C > 19 ? new F(function(){return A3(_50,_o8,_ob,_o9);}) : (++C,A3(_50,_o8,_ob,_o9));},_on=new T(function(){return B(_o4(_1X,new T(function(){return _9q(function(_oo){return toJSStr(E(_oo));},new T2(1,new T(function(){return unCStr("s");}),new T2(1,new T(function(){return unCStr("k");}),new T2(1,new T(function(){return unCStr("r");}),new T2(1,new T(function(){return unCStr("t");}),new T2(1,new T(function(){return unCStr("sigma");}),new T2(1,new T(function(){return unCStr("resultC");}),new T2(1,new T(function(){return unCStr("resultP");}),__Z))))))));}),_mM));});
var hasteMain = function() {B(A(_on, [0]));};window.onload = hasteMain;