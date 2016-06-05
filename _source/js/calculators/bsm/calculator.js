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

var _0=function(_1,_2,_){var _3=B(A1(_1,_)),_4=B(A1(_2,_));return _3;},_5=function(_6,_7,_){var _8=B(A1(_6,_)),_9=B(A1(_7,_));return new T(function(){return B(A1(_8,_9));});},_a=function(_b,_c,_){var _d=B(A1(_c,_));return _b;},_e=function(_f,_g,_){var _h=B(A1(_g,_));return new T(function(){return B(A1(_f,_h));});},_i=new T2(0,_e,_a),_j=function(_k,_){return _k;},_l=function(_m,_n,_){var _o=B(A1(_m,_));return new F(function(){return A1(_n,_);});},_p=new T5(0,_i,_j,_5,_l,_0),_q=new T(function(){return B(unCStr("base"));}),_r=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_s=new T(function(){return B(unCStr("IOException"));}),_t=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_q,_r,_s),_u=__Z,_v=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_t,_u,_u),_w=function(_x){return E(_v);},_y=function(_z){return E(E(_z).a);},_A=function(_B,_C,_D){var _E=B(A1(_B,_)),_F=B(A1(_C,_)),_G=hs_eqWord64(_E.a,_F.a);if(!_G){return __Z;}else{var _H=hs_eqWord64(_E.b,_F.b);return (!_H)?__Z:new T1(1,_D);}},_I=function(_J){var _K=E(_J);return new F(function(){return _A(B(_y(_K.a)),_w,_K.b);});},_L=new T(function(){return B(unCStr(": "));}),_M=new T(function(){return B(unCStr(")"));}),_N=new T(function(){return B(unCStr(" ("));}),_O=function(_P,_Q){var _R=E(_P);return (_R._==0)?E(_Q):new T2(1,_R.a,new T(function(){return B(_O(_R.b,_Q));}));},_S=new T(function(){return B(unCStr("interrupted"));}),_T=new T(function(){return B(unCStr("system error"));}),_U=new T(function(){return B(unCStr("unsatisified constraints"));}),_V=new T(function(){return B(unCStr("user error"));}),_W=new T(function(){return B(unCStr("permission denied"));}),_X=new T(function(){return B(unCStr("illegal operation"));}),_Y=new T(function(){return B(unCStr("end of file"));}),_Z=new T(function(){return B(unCStr("resource exhausted"));}),_10=new T(function(){return B(unCStr("resource busy"));}),_11=new T(function(){return B(unCStr("does not exist"));}),_12=new T(function(){return B(unCStr("already exists"));}),_13=new T(function(){return B(unCStr("resource vanished"));}),_14=new T(function(){return B(unCStr("timeout"));}),_15=new T(function(){return B(unCStr("unsupported operation"));}),_16=new T(function(){return B(unCStr("hardware fault"));}),_17=new T(function(){return B(unCStr("inappropriate type"));}),_18=new T(function(){return B(unCStr("invalid argument"));}),_19=new T(function(){return B(unCStr("failed"));}),_1a=new T(function(){return B(unCStr("protocol error"));}),_1b=function(_1c,_1d){switch(E(_1c)){case 0:return new F(function(){return _O(_12,_1d);});break;case 1:return new F(function(){return _O(_11,_1d);});break;case 2:return new F(function(){return _O(_10,_1d);});break;case 3:return new F(function(){return _O(_Z,_1d);});break;case 4:return new F(function(){return _O(_Y,_1d);});break;case 5:return new F(function(){return _O(_X,_1d);});break;case 6:return new F(function(){return _O(_W,_1d);});break;case 7:return new F(function(){return _O(_V,_1d);});break;case 8:return new F(function(){return _O(_U,_1d);});break;case 9:return new F(function(){return _O(_T,_1d);});break;case 10:return new F(function(){return _O(_1a,_1d);});break;case 11:return new F(function(){return _O(_19,_1d);});break;case 12:return new F(function(){return _O(_18,_1d);});break;case 13:return new F(function(){return _O(_17,_1d);});break;case 14:return new F(function(){return _O(_16,_1d);});break;case 15:return new F(function(){return _O(_15,_1d);});break;case 16:return new F(function(){return _O(_14,_1d);});break;case 17:return new F(function(){return _O(_13,_1d);});break;default:return new F(function(){return _O(_S,_1d);});}},_1e=new T(function(){return B(unCStr("}"));}),_1f=new T(function(){return B(unCStr("{handle: "));}),_1g=function(_1h,_1i,_1j,_1k,_1l,_1m){var _1n=new T(function(){var _1o=new T(function(){var _1p=new T(function(){var _1q=E(_1k);if(!_1q._){return E(_1m);}else{var _1r=new T(function(){return B(_O(_1q,new T(function(){return B(_O(_M,_1m));},1)));},1);return B(_O(_N,_1r));}},1);return B(_1b(_1i,_1p));}),_1s=E(_1j);if(!_1s._){return E(_1o);}else{return B(_O(_1s,new T(function(){return B(_O(_L,_1o));},1)));}}),_1t=E(_1l);if(!_1t._){var _1u=E(_1h);if(!_1u._){return E(_1n);}else{var _1v=E(_1u.a);if(!_1v._){var _1w=new T(function(){var _1x=new T(function(){return B(_O(_1e,new T(function(){return B(_O(_L,_1n));},1)));},1);return B(_O(_1v.a,_1x));},1);return new F(function(){return _O(_1f,_1w);});}else{var _1y=new T(function(){var _1z=new T(function(){return B(_O(_1e,new T(function(){return B(_O(_L,_1n));},1)));},1);return B(_O(_1v.a,_1z));},1);return new F(function(){return _O(_1f,_1y);});}}}else{return new F(function(){return _O(_1t.a,new T(function(){return B(_O(_L,_1n));},1));});}},_1A=function(_1B){var _1C=E(_1B);return new F(function(){return _1g(_1C.a,_1C.b,_1C.c,_1C.d,_1C.f,_u);});},_1D=function(_1E){return new T2(0,_1F,_1E);},_1G=function(_1H,_1I,_1J){var _1K=E(_1I);return new F(function(){return _1g(_1K.a,_1K.b,_1K.c,_1K.d,_1K.f,_1J);});},_1L=function(_1M,_1N){var _1O=E(_1M);return new F(function(){return _1g(_1O.a,_1O.b,_1O.c,_1O.d,_1O.f,_1N);});},_1P=44,_1Q=93,_1R=91,_1S=function(_1T,_1U,_1V){var _1W=E(_1U);if(!_1W._){return new F(function(){return unAppCStr("[]",_1V);});}else{var _1X=new T(function(){var _1Y=new T(function(){var _1Z=function(_20){var _21=E(_20);if(!_21._){return E(new T2(1,_1Q,_1V));}else{var _22=new T(function(){return B(A2(_1T,_21.a,new T(function(){return B(_1Z(_21.b));})));});return new T2(1,_1P,_22);}};return B(_1Z(_1W.b));});return B(A2(_1T,_1W.a,_1Y));});return new T2(1,_1R,_1X);}},_23=function(_24,_25){return new F(function(){return _1S(_1L,_24,_25);});},_26=new T3(0,_1G,_1A,_23),_1F=new T(function(){return new T5(0,_w,_26,_1D,_I,_1A);}),_27=new T(function(){return E(_1F);}),_28=function(_29){return E(E(_29).c);},_2a=__Z,_2b=7,_2c=function(_2d){return new T6(0,_2a,_2b,_u,_2d,_2a,_2a);},_2e=function(_2f,_){var _2g=new T(function(){return B(A2(_28,_27,new T(function(){return B(A1(_2c,_2f));})));});return new F(function(){return die(_2g);});},_2h=function(_2i,_){return new F(function(){return _2e(_2i,_);});},_2j=function(_2k){return new F(function(){return A1(_2h,_2k);});},_2l=function(_2m,_2n,_){var _2o=B(A1(_2m,_));return new F(function(){return A2(_2n,_2o,_);});},_2p=new T5(0,_p,_2l,_l,_j,_2j),_2q=function(_2r){return E(_2r);},_2s=new T2(0,_2p,_2q),_2t=0,_2u=function(_){return _2t;},_2v=function(_2w,_2x,_){return new F(function(){return _2u(_);});},_2y="scroll",_2z="submit",_2A="blur",_2B="focus",_2C="change",_2D="unload",_2E="load",_2F=function(_2G){switch(E(_2G)){case 0:return E(_2E);case 1:return E(_2D);case 2:return E(_2C);case 3:return E(_2B);case 4:return E(_2A);case 5:return E(_2z);default:return E(_2y);}},_2H=new T2(0,_2F,_2v),_2I="metaKey",_2J="shiftKey",_2K="altKey",_2L="ctrlKey",_2M="keyCode",_2N=function(_2O,_){var _2P=__get(_2O,E(_2M)),_2Q=__get(_2O,E(_2L)),_2R=__get(_2O,E(_2K)),_2S=__get(_2O,E(_2J)),_2T=__get(_2O,E(_2I));return new T(function(){var _2U=Number(_2P),_2V=jsTrunc(_2U);return new T5(0,_2V,E(_2Q),E(_2R),E(_2S),E(_2T));});},_2W=function(_2X,_2Y,_){return new F(function(){return _2N(E(_2Y),_);});},_2Z="keydown",_30="keyup",_31="keypress",_32=function(_33){switch(E(_33)){case 0:return E(_31);case 1:return E(_30);default:return E(_2Z);}},_34=new T2(0,_32,_2W),_35=function(_){return _2t;},_36=function(_37,_){return new T1(1,_37);},_38=new T2(0,_2q,_36),_39=new T2(0,_2s,_j),_3a=function(_3b){if(_3b!=0){if(_3b<=0){var _3c=1/(1+0.5* -_3b),_3d=_3c*_3c,_3e=_3d*_3c,_3f=_3e*_3c,_3g=_3f*_3c,_3h=_3g*_3c,_3i=_3h*_3c,_3j=_3i*_3c;return (_3b<0)?_3c*Math.exp( -(_3b*_3b)-1.26551223+1.00002368*_3c+0.37409196*_3d+9.678418e-2*_3e-0.18628806*_3f+0.27886807*_3g-1.13520398*_3h+1.48851587*_3i-0.82215223*_3j+0.17087277*_3j*_3c)-1:1-_3c*Math.exp( -(_3b*_3b)-1.26551223+1.00002368*_3c+0.37409196*_3d+9.678418e-2*_3e-0.18628806*_3f+0.27886807*_3g-1.13520398*_3h+1.48851587*_3i-0.82215223*_3j+0.17087277*_3j*_3c);}else{var _3k=1/(1+0.5*_3b),_3l=_3k*_3k,_3m=_3l*_3k,_3n=_3m*_3k,_3o=_3n*_3k,_3p=_3o*_3k,_3q=_3p*_3k,_3r=_3q*_3k;return (_3b<0)?_3k*Math.exp( -(_3b*_3b)-1.26551223+1.00002368*_3k+0.37409196*_3l+9.678418e-2*_3m-0.18628806*_3n+0.27886807*_3o-1.13520398*_3p+1.48851587*_3q-0.82215223*_3r+0.17087277*_3r*_3k)-1:1-_3k*Math.exp( -(_3b*_3b)-1.26551223+1.00002368*_3k+0.37409196*_3l+9.678418e-2*_3m-0.18628806*_3n+0.27886807*_3o-1.13520398*_3p+1.48851587*_3q-0.82215223*_3r+0.17087277*_3r*_3k);}}else{return (_3b<0)?Math.exp( -(_3b*_3b)-1.26551223+1.00002368+0.37409196+9.678418e-2-0.18628806+0.27886807-1.13520398+1.48851587-0.82215223+0.17087277)-1:1-Math.exp( -(_3b*_3b)-1.26551223+1.00002368+0.37409196+9.678418e-2-0.18628806+0.27886807-1.13520398+1.48851587-0.82215223+0.17087277);}},_3s=function(_3t,_3u){while(1){var _3v=E(_3t);if(!_3v._){return E(_3u);}else{var _3w=new T2(1,_3v.a,_3u);_3t=_3v.b;_3u=_3w;continue;}}},_3x=function(_3y){return new F(function(){return _3s(_3y,_u);});},_3z=function(_3A,_3B,_3C){while(1){var _3D=B((function(_3E,_3F,_3G){var _3H=E(_3E);if(!_3H._){return new T2(0,new T(function(){return B(_3x(_3F));}),new T(function(){return B(_3x(_3G));}));}else{var _3I=_3F,_3J=new T2(1,_3H.a,_3G);_3A=_3H.b;_3B=_3I;_3C=_3J;return __continue;}})(_3A,_3B,_3C));if(_3D!=__continue){return _3D;}}},_3K=function(_3L,_3M,_3N){while(1){var _3O=B((function(_3P,_3Q,_3R){var _3S=E(_3P);if(!_3S._){return new T2(0,new T(function(){return B(_3x(_3Q));}),new T(function(){return B(_3x(_3R));}));}else{var _3T=_3S.b,_3U=E(_3S.a);if(E(_3U)==46){return new F(function(){return _3z(_3T,_3Q,_u);});}else{var _3V=new T2(1,_3U,_3Q),_3W=_3R;_3L=_3T;_3M=_3V;_3N=_3W;return __continue;}}})(_3L,_3M,_3N));if(_3O!=__continue){return _3O;}}},_3X=function(_3Y,_3Z){var _40=E(_3Z);if(!_40._){return __Z;}else{var _41=_40.a,_42=E(_3Y);return (_42==1)?new T2(1,_41,_u):new T2(1,_41,new T(function(){return B(_3X(_42-1|0,_40.b));}));}},_43=function(_44){var _45=I_decodeDouble(_44);return new T2(0,new T1(1,_45.b),_45.a);},_46=function(_47){var _48=E(_47);if(!_48._){return _48.a;}else{return new F(function(){return I_toNumber(_48.a);});}},_49=function(_4a){return new T1(0,_4a);},_4b=function(_4c){var _4d=hs_intToInt64(2147483647),_4e=hs_leInt64(_4c,_4d);if(!_4e){return new T1(1,I_fromInt64(_4c));}else{var _4f=hs_intToInt64(-2147483648),_4g=hs_geInt64(_4c,_4f);if(!_4g){return new T1(1,I_fromInt64(_4c));}else{var _4h=hs_int64ToInt(_4c);return new F(function(){return _49(_4h);});}}},_4i=function(_4j){var _4k=hs_intToInt64(_4j);return E(_4k);},_4l=function(_4m){var _4n=E(_4m);if(!_4n._){return new F(function(){return _4i(_4n.a);});}else{return new F(function(){return I_toInt64(_4n.a);});}},_4o=function(_4p,_4q){while(1){var _4r=E(_4p);if(!_4r._){_4p=new T1(1,I_fromInt(_4r.a));continue;}else{return new T1(1,I_shiftLeft(_4r.a,_4q));}}},_4s=function(_4t,_4u){var _4v=Math.pow(10,_4t),_4w=rintDouble(_4u*_4v),_4x=B(_43(_4w)),_4y=_4x.a,_4z=_4x.b,_4A=function(_4B,_4C){var _4D=new T(function(){return B(unAppCStr(".",new T(function(){if(0>=_4t){return __Z;}else{return B(_3X(_4t,_4C));}})));},1);return new F(function(){return _O(_4B,_4D);});};if(_4z>=0){var _4E=jsShow(B(_46(B(_4o(_4y,_4z))))/_4v),_4F=B(_3K(fromJSStr(_4E),_u,_u));return new F(function(){return _4A(_4F.a,_4F.b);});}else{var _4G=hs_uncheckedIShiftRA64(B(_4l(_4y)), -_4z),_4H=jsShow(B(_46(B(_4b(_4G))))/_4v),_4I=B(_3K(fromJSStr(_4H),_u,_u));return new F(function(){return _4A(_4I.a,_4I.b);});}},_4J=2,_4K=1,_4L="value",_4M=new T(function(){return eval("(function(e,p){var x = e[p];return typeof x === \'undefined\' ? \'\' : x.toString();})");}),_4N=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_4O=new T(function(){return B(unCStr("base"));}),_4P=new T(function(){return B(unCStr("Control.Exception.Base"));}),_4Q=new T(function(){return B(unCStr("PatternMatchFail"));}),_4R=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_4O,_4P,_4Q),_4S=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_4R,_u,_u),_4T=function(_4U){return E(_4S);},_4V=function(_4W){var _4X=E(_4W);return new F(function(){return _A(B(_y(_4X.a)),_4T,_4X.b);});},_4Y=function(_4Z){return E(E(_4Z).a);},_50=function(_51){return new T2(0,_52,_51);},_53=function(_54,_55){return new F(function(){return _O(E(_54).a,_55);});},_56=function(_57,_58){return new F(function(){return _1S(_53,_57,_58);});},_59=function(_5a,_5b,_5c){return new F(function(){return _O(E(_5b).a,_5c);});},_5d=new T3(0,_59,_4Y,_56),_52=new T(function(){return new T5(0,_4T,_5d,_50,_4V,_4Y);}),_5e=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_5f=function(_5g,_5h){return new F(function(){return die(new T(function(){return B(A2(_28,_5h,_5g));}));});},_5i=function(_5j,_5k){return new F(function(){return _5f(_5j,_5k);});},_5l=function(_5m,_5n){var _5o=E(_5n);if(!_5o._){return new T2(0,_u,_u);}else{var _5p=_5o.a;if(!B(A1(_5m,_5p))){return new T2(0,_u,_5o);}else{var _5q=new T(function(){var _5r=B(_5l(_5m,_5o.b));return new T2(0,_5r.a,_5r.b);});return new T2(0,new T2(1,_5p,new T(function(){return E(E(_5q).a);})),new T(function(){return E(E(_5q).b);}));}}},_5s=32,_5t=new T(function(){return B(unCStr("\n"));}),_5u=function(_5v){return (E(_5v)==124)?false:true;},_5w=function(_5x,_5y){var _5z=B(_5l(_5u,B(unCStr(_5x)))),_5A=_5z.a,_5B=function(_5C,_5D){var _5E=new T(function(){var _5F=new T(function(){return B(_O(_5y,new T(function(){return B(_O(_5D,_5t));},1)));});return B(unAppCStr(": ",_5F));},1);return new F(function(){return _O(_5C,_5E);});},_5G=E(_5z.b);if(!_5G._){return new F(function(){return _5B(_5A,_u);});}else{if(E(_5G.a)==124){return new F(function(){return _5B(_5A,new T2(1,_5s,_5G.b));});}else{return new F(function(){return _5B(_5A,_u);});}}},_5H=function(_5I){return new F(function(){return _5i(new T1(0,new T(function(){return B(_5w(_5I,_5e));})),_52);});},_5J=function(_5K){return new F(function(){return _5H("calculator.hs:(11,1)-(28,39)|function calculator");});},_5L=new T(function(){return B(_5J(_));}),_5M=new T(function(){return B(unCStr("innerHTML"));}),_5N=function(_5O){return E(E(_5O).a);},_5P=function(_5Q){return E(E(_5Q).a);},_5R=function(_5S){return E(E(_5S).b);},_5T=function(_5U){return E(E(_5U).a);},_5V=function(_5W){return E(E(_5W).b);},_5X=function(_5Y){return E(E(_5Y).a);},_5Z=function(_){return new F(function(){return nMV(_2a);});},_60=function(_61){var _62=B(A1(_61,_));return E(_62);},_63=new T(function(){return B(_60(_5Z));}),_64=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_65=function(_){return new F(function(){return __jsNull();});},_66=new T(function(){return B(_60(_65));}),_67=new T(function(){return E(_66);}),_68=function(_69){return E(E(_69).b);},_6a=function(_6b){return E(E(_6b).b);},_6c=function(_6d){return E(E(_6d).d);},_6e=function(_6f,_6g,_6h,_6i,_6j,_6k){var _6l=B(_5N(_6f)),_6m=B(_5P(_6l)),_6n=new T(function(){return B(_68(_6l));}),_6o=new T(function(){return B(_6c(_6m));}),_6p=new T(function(){return B(A2(_5T,_6g,_6i));}),_6q=new T(function(){return B(A2(_5X,_6h,_6j));}),_6r=function(_6s){return new F(function(){return A1(_6o,new T3(0,_6q,_6p,_6s));});},_6t=function(_6u){var _6v=new T(function(){var _6w=new T(function(){var _6x=__createJSFunc(2,function(_6y,_){var _6z=B(A2(E(_6u),_6y,_));return _67;}),_6A=_6x;return function(_){return new F(function(){return __app3(E(_64),E(_6p),E(_6q),_6A);});};});return B(A1(_6n,_6w));});return new F(function(){return A3(_5R,_6m,_6v,_6r);});},_6B=new T(function(){var _6C=new T(function(){return B(_68(_6l));}),_6D=function(_6E){var _6F=new T(function(){return B(A1(_6C,function(_){var _=wMV(E(_63),new T1(1,_6E));return new F(function(){return A(_5V,[_6h,_6j,_6E,_]);});}));});return new F(function(){return A3(_5R,_6m,_6F,_6k);});};return B(A2(_6a,_6f,_6D));});return new F(function(){return A3(_5R,_6m,_6B,_6t);});},_6G=function(_6H,_6I){var _6J=E(_6I);return (_6J._==0)?__Z:new T2(1,_6H,new T(function(){return B(_6G(_6J.a,_6J.b));}));},_6K=new T(function(){return B(unCStr(": empty list"));}),_6L=new T(function(){return B(unCStr("Prelude."));}),_6M=function(_6N){return new F(function(){return err(B(_O(_6L,new T(function(){return B(_O(_6N,_6K));},1))));});},_6O=new T(function(){return B(unCStr("init"));}),_6P=new T(function(){return B(_6M(_6O));}),_6Q=function(_6R){var _6S=E(_6R);if(!_6S._){return E(_6P);}else{return new F(function(){return _6G(_6S.a,_6S.b);});}},_6T=new T(function(){return B(unCStr("last"));}),_6U=new T(function(){return B(_6M(_6T));}),_6V=function(_6W){while(1){var _6X=B((function(_6Y){var _6Z=E(_6Y);if(!_6Z._){return __Z;}else{var _70=_6Z.b,_71=E(_6Z.a);if(!E(_71.b)._){return new T2(1,_71.a,new T(function(){return B(_6V(_70));}));}else{_6W=_70;return __continue;}}})(_6W));if(_6X!=__continue){return _6X;}}},_72=function(_73,_74){while(1){var _75=B((function(_76,_77){var _78=E(_76);switch(_78._){case 0:var _79=E(_77);if(!_79._){return __Z;}else{_73=B(A1(_78.a,_79.a));_74=_79.b;return __continue;}break;case 1:var _7a=B(A1(_78.a,_77)),_7b=_77;_73=_7a;_74=_7b;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_78.a,_77),new T(function(){return B(_72(_78.b,_77));}));default:return E(_78.a);}})(_73,_74));if(_75!=__continue){return _75;}}},_7c=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_7d=new T(function(){return B(err(_7c));}),_7e=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_7f=new T(function(){return B(err(_7e));}),_7g=new T(function(){return B(_5H("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_7h=function(_7i,_7j){var _7k=function(_7l){var _7m=E(_7j);if(_7m._==3){return new T2(3,_7m.a,new T(function(){return B(_7h(_7i,_7m.b));}));}else{var _7n=E(_7i);if(_7n._==2){return E(_7m);}else{var _7o=E(_7m);if(_7o._==2){return E(_7n);}else{var _7p=function(_7q){var _7r=E(_7o);if(_7r._==4){var _7s=function(_7t){return new T1(4,new T(function(){return B(_O(B(_72(_7n,_7t)),_7r.a));}));};return new T1(1,_7s);}else{var _7u=E(_7n);if(_7u._==1){var _7v=_7u.a,_7w=E(_7r);if(!_7w._){return new T1(1,function(_7x){return new F(function(){return _7h(B(A1(_7v,_7x)),_7w);});});}else{var _7y=function(_7z){return new F(function(){return _7h(B(A1(_7v,_7z)),new T(function(){return B(A1(_7w.a,_7z));}));});};return new T1(1,_7y);}}else{var _7A=E(_7r);if(!_7A._){return E(_7g);}else{var _7B=function(_7C){return new F(function(){return _7h(_7u,new T(function(){return B(A1(_7A.a,_7C));}));});};return new T1(1,_7B);}}}},_7D=E(_7n);switch(_7D._){case 1:var _7E=E(_7o);if(_7E._==4){var _7F=function(_7G){return new T1(4,new T(function(){return B(_O(B(_72(B(A1(_7D.a,_7G)),_7G)),_7E.a));}));};return new T1(1,_7F);}else{return new F(function(){return _7p(_);});}break;case 4:var _7H=_7D.a,_7I=E(_7o);switch(_7I._){case 0:var _7J=function(_7K){var _7L=new T(function(){return B(_O(_7H,new T(function(){return B(_72(_7I,_7K));},1)));});return new T1(4,_7L);};return new T1(1,_7J);case 1:var _7M=function(_7N){var _7O=new T(function(){return B(_O(_7H,new T(function(){return B(_72(B(A1(_7I.a,_7N)),_7N));},1)));});return new T1(4,_7O);};return new T1(1,_7M);default:return new T1(4,new T(function(){return B(_O(_7H,_7I.a));}));}break;default:return new F(function(){return _7p(_);});}}}}},_7P=E(_7i);switch(_7P._){case 0:var _7Q=E(_7j);if(!_7Q._){var _7R=function(_7S){return new F(function(){return _7h(B(A1(_7P.a,_7S)),new T(function(){return B(A1(_7Q.a,_7S));}));});};return new T1(0,_7R);}else{return new F(function(){return _7k(_);});}break;case 3:return new T2(3,_7P.a,new T(function(){return B(_7h(_7P.b,_7j));}));default:return new F(function(){return _7k(_);});}},_7T=new T(function(){return B(unCStr("("));}),_7U=new T(function(){return B(unCStr(")"));}),_7V=function(_7W,_7X){while(1){var _7Y=E(_7W);if(!_7Y._){return (E(_7X)._==0)?true:false;}else{var _7Z=E(_7X);if(!_7Z._){return false;}else{if(E(_7Y.a)!=E(_7Z.a)){return false;}else{_7W=_7Y.b;_7X=_7Z.b;continue;}}}}},_80=function(_81,_82){return E(_81)!=E(_82);},_83=function(_84,_85){return E(_84)==E(_85);},_86=new T2(0,_83,_80),_87=function(_88,_89){while(1){var _8a=E(_88);if(!_8a._){return (E(_89)._==0)?true:false;}else{var _8b=E(_89);if(!_8b._){return false;}else{if(E(_8a.a)!=E(_8b.a)){return false;}else{_88=_8a.b;_89=_8b.b;continue;}}}}},_8c=function(_8d,_8e){return (!B(_87(_8d,_8e)))?true:false;},_8f=new T2(0,_87,_8c),_8g=function(_8h,_8i){var _8j=E(_8h);switch(_8j._){case 0:return new T1(0,function(_8k){return new F(function(){return _8g(B(A1(_8j.a,_8k)),_8i);});});case 1:return new T1(1,function(_8l){return new F(function(){return _8g(B(A1(_8j.a,_8l)),_8i);});});case 2:return new T0(2);case 3:return new F(function(){return _7h(B(A1(_8i,_8j.a)),new T(function(){return B(_8g(_8j.b,_8i));}));});break;default:var _8m=function(_8n){var _8o=E(_8n);if(!_8o._){return __Z;}else{var _8p=E(_8o.a);return new F(function(){return _O(B(_72(B(A1(_8i,_8p.a)),_8p.b)),new T(function(){return B(_8m(_8o.b));},1));});}},_8q=B(_8m(_8j.a));return (_8q._==0)?new T0(2):new T1(4,_8q);}},_8r=new T0(2),_8s=function(_8t){return new T2(3,_8t,_8r);},_8u=function(_8v,_8w){var _8x=E(_8v);if(!_8x){return new F(function(){return A1(_8w,_2t);});}else{var _8y=new T(function(){return B(_8u(_8x-1|0,_8w));});return new T1(0,function(_8z){return E(_8y);});}},_8A=function(_8B,_8C,_8D){var _8E=new T(function(){return B(A1(_8B,_8s));}),_8F=function(_8G,_8H,_8I,_8J){while(1){var _8K=B((function(_8L,_8M,_8N,_8O){var _8P=E(_8L);switch(_8P._){case 0:var _8Q=E(_8M);if(!_8Q._){return new F(function(){return A1(_8C,_8O);});}else{var _8R=_8N+1|0,_8S=_8O;_8G=B(A1(_8P.a,_8Q.a));_8H=_8Q.b;_8I=_8R;_8J=_8S;return __continue;}break;case 1:var _8T=B(A1(_8P.a,_8M)),_8U=_8M,_8R=_8N,_8S=_8O;_8G=_8T;_8H=_8U;_8I=_8R;_8J=_8S;return __continue;case 2:return new F(function(){return A1(_8C,_8O);});break;case 3:var _8V=new T(function(){return B(_8g(_8P,_8O));});return new F(function(){return _8u(_8N,function(_8W){return E(_8V);});});break;default:return new F(function(){return _8g(_8P,_8O);});}})(_8G,_8H,_8I,_8J));if(_8K!=__continue){return _8K;}}};return function(_8X){return new F(function(){return _8F(_8E,_8X,0,_8D);});};},_8Y=function(_8Z){return new F(function(){return A1(_8Z,_u);});},_90=function(_91,_92){var _93=function(_94){var _95=E(_94);if(!_95._){return E(_8Y);}else{var _96=_95.a;if(!B(A1(_91,_96))){return E(_8Y);}else{var _97=new T(function(){return B(_93(_95.b));}),_98=function(_99){var _9a=new T(function(){return B(A1(_97,function(_9b){return new F(function(){return A1(_99,new T2(1,_96,_9b));});}));});return new T1(0,function(_9c){return E(_9a);});};return E(_98);}}};return function(_9d){return new F(function(){return A2(_93,_9d,_92);});};},_9e=new T0(6),_9f=new T(function(){return B(unCStr("valDig: Bad base"));}),_9g=new T(function(){return B(err(_9f));}),_9h=function(_9i,_9j){var _9k=function(_9l,_9m){var _9n=E(_9l);if(!_9n._){var _9o=new T(function(){return B(A1(_9m,_u));});return function(_9p){return new F(function(){return A1(_9p,_9o);});};}else{var _9q=E(_9n.a),_9r=function(_9s){var _9t=new T(function(){return B(_9k(_9n.b,function(_9u){return new F(function(){return A1(_9m,new T2(1,_9s,_9u));});}));}),_9v=function(_9w){var _9x=new T(function(){return B(A1(_9t,_9w));});return new T1(0,function(_9y){return E(_9x);});};return E(_9v);};switch(E(_9i)){case 8:if(48>_9q){var _9z=new T(function(){return B(A1(_9m,_u));});return function(_9A){return new F(function(){return A1(_9A,_9z);});};}else{if(_9q>55){var _9B=new T(function(){return B(A1(_9m,_u));});return function(_9C){return new F(function(){return A1(_9C,_9B);});};}else{return new F(function(){return _9r(_9q-48|0);});}}break;case 10:if(48>_9q){var _9D=new T(function(){return B(A1(_9m,_u));});return function(_9E){return new F(function(){return A1(_9E,_9D);});};}else{if(_9q>57){var _9F=new T(function(){return B(A1(_9m,_u));});return function(_9G){return new F(function(){return A1(_9G,_9F);});};}else{return new F(function(){return _9r(_9q-48|0);});}}break;case 16:if(48>_9q){if(97>_9q){if(65>_9q){var _9H=new T(function(){return B(A1(_9m,_u));});return function(_9I){return new F(function(){return A1(_9I,_9H);});};}else{if(_9q>70){var _9J=new T(function(){return B(A1(_9m,_u));});return function(_9K){return new F(function(){return A1(_9K,_9J);});};}else{return new F(function(){return _9r((_9q-65|0)+10|0);});}}}else{if(_9q>102){if(65>_9q){var _9L=new T(function(){return B(A1(_9m,_u));});return function(_9M){return new F(function(){return A1(_9M,_9L);});};}else{if(_9q>70){var _9N=new T(function(){return B(A1(_9m,_u));});return function(_9O){return new F(function(){return A1(_9O,_9N);});};}else{return new F(function(){return _9r((_9q-65|0)+10|0);});}}}else{return new F(function(){return _9r((_9q-97|0)+10|0);});}}}else{if(_9q>57){if(97>_9q){if(65>_9q){var _9P=new T(function(){return B(A1(_9m,_u));});return function(_9Q){return new F(function(){return A1(_9Q,_9P);});};}else{if(_9q>70){var _9R=new T(function(){return B(A1(_9m,_u));});return function(_9S){return new F(function(){return A1(_9S,_9R);});};}else{return new F(function(){return _9r((_9q-65|0)+10|0);});}}}else{if(_9q>102){if(65>_9q){var _9T=new T(function(){return B(A1(_9m,_u));});return function(_9U){return new F(function(){return A1(_9U,_9T);});};}else{if(_9q>70){var _9V=new T(function(){return B(A1(_9m,_u));});return function(_9W){return new F(function(){return A1(_9W,_9V);});};}else{return new F(function(){return _9r((_9q-65|0)+10|0);});}}}else{return new F(function(){return _9r((_9q-97|0)+10|0);});}}}else{return new F(function(){return _9r(_9q-48|0);});}}break;default:return E(_9g);}}},_9X=function(_9Y){var _9Z=E(_9Y);if(!_9Z._){return new T0(2);}else{return new F(function(){return A1(_9j,_9Z);});}};return function(_a0){return new F(function(){return A3(_9k,_a0,_2q,_9X);});};},_a1=16,_a2=8,_a3=function(_a4){var _a5=function(_a6){return new F(function(){return A1(_a4,new T1(5,new T2(0,_a2,_a6)));});},_a7=function(_a8){return new F(function(){return A1(_a4,new T1(5,new T2(0,_a1,_a8)));});},_a9=function(_aa){switch(E(_aa)){case 79:return new T1(1,B(_9h(_a2,_a5)));case 88:return new T1(1,B(_9h(_a1,_a7)));case 111:return new T1(1,B(_9h(_a2,_a5)));case 120:return new T1(1,B(_9h(_a1,_a7)));default:return new T0(2);}};return function(_ab){return (E(_ab)==48)?E(new T1(0,_a9)):new T0(2);};},_ac=function(_ad){return new T1(0,B(_a3(_ad)));},_ae=function(_af){return new F(function(){return A1(_af,_2a);});},_ag=function(_ah){return new F(function(){return A1(_ah,_2a);});},_ai=10,_aj=new T1(0,1),_ak=new T1(0,2147483647),_al=function(_am,_an){while(1){var _ao=E(_am);if(!_ao._){var _ap=_ao.a,_aq=E(_an);if(!_aq._){var _ar=_aq.a,_as=addC(_ap,_ar);if(!E(_as.b)){return new T1(0,_as.a);}else{_am=new T1(1,I_fromInt(_ap));_an=new T1(1,I_fromInt(_ar));continue;}}else{_am=new T1(1,I_fromInt(_ap));_an=_aq;continue;}}else{var _at=E(_an);if(!_at._){_am=_ao;_an=new T1(1,I_fromInt(_at.a));continue;}else{return new T1(1,I_add(_ao.a,_at.a));}}}},_au=new T(function(){return B(_al(_ak,_aj));}),_av=function(_aw){var _ax=E(_aw);if(!_ax._){var _ay=E(_ax.a);return (_ay==(-2147483648))?E(_au):new T1(0, -_ay);}else{return new T1(1,I_negate(_ax.a));}},_az=new T1(0,10),_aA=function(_aB,_aC){while(1){var _aD=E(_aB);if(!_aD._){return E(_aC);}else{var _aE=_aC+1|0;_aB=_aD.b;_aC=_aE;continue;}}},_aF=function(_aG,_aH){var _aI=E(_aH);return (_aI._==0)?__Z:new T2(1,new T(function(){return B(A1(_aG,_aI.a));}),new T(function(){return B(_aF(_aG,_aI.b));}));},_aJ=function(_aK){return new F(function(){return _49(E(_aK));});},_aL=new T(function(){return B(unCStr("this should not happen"));}),_aM=new T(function(){return B(err(_aL));}),_aN=function(_aO,_aP){while(1){var _aQ=E(_aO);if(!_aQ._){var _aR=_aQ.a,_aS=E(_aP);if(!_aS._){var _aT=_aS.a;if(!(imul(_aR,_aT)|0)){return new T1(0,imul(_aR,_aT)|0);}else{_aO=new T1(1,I_fromInt(_aR));_aP=new T1(1,I_fromInt(_aT));continue;}}else{_aO=new T1(1,I_fromInt(_aR));_aP=_aS;continue;}}else{var _aU=E(_aP);if(!_aU._){_aO=_aQ;_aP=new T1(1,I_fromInt(_aU.a));continue;}else{return new T1(1,I_mul(_aQ.a,_aU.a));}}}},_aV=function(_aW,_aX){var _aY=E(_aX);if(!_aY._){return __Z;}else{var _aZ=E(_aY.b);return (_aZ._==0)?E(_aM):new T2(1,B(_al(B(_aN(_aY.a,_aW)),_aZ.a)),new T(function(){return B(_aV(_aW,_aZ.b));}));}},_b0=new T1(0,0),_b1=function(_b2,_b3,_b4){while(1){var _b5=B((function(_b6,_b7,_b8){var _b9=E(_b8);if(!_b9._){return E(_b0);}else{if(!E(_b9.b)._){return E(_b9.a);}else{var _ba=E(_b7);if(_ba<=40){var _bb=function(_bc,_bd){while(1){var _be=E(_bd);if(!_be._){return E(_bc);}else{var _bf=B(_al(B(_aN(_bc,_b6)),_be.a));_bc=_bf;_bd=_be.b;continue;}}};return new F(function(){return _bb(_b0,_b9);});}else{var _bg=B(_aN(_b6,_b6));if(!(_ba%2)){var _bh=B(_aV(_b6,_b9));_b2=_bg;_b3=quot(_ba+1|0,2);_b4=_bh;return __continue;}else{var _bh=B(_aV(_b6,new T2(1,_b0,_b9)));_b2=_bg;_b3=quot(_ba+1|0,2);_b4=_bh;return __continue;}}}}})(_b2,_b3,_b4));if(_b5!=__continue){return _b5;}}},_bi=function(_bj,_bk){return new F(function(){return _b1(_bj,new T(function(){return B(_aA(_bk,0));},1),B(_aF(_aJ,_bk)));});},_bl=function(_bm){var _bn=new T(function(){var _bo=new T(function(){var _bp=function(_bq){return new F(function(){return A1(_bm,new T1(1,new T(function(){return B(_bi(_az,_bq));})));});};return new T1(1,B(_9h(_ai,_bp)));}),_br=function(_bs){if(E(_bs)==43){var _bt=function(_bu){return new F(function(){return A1(_bm,new T1(1,new T(function(){return B(_bi(_az,_bu));})));});};return new T1(1,B(_9h(_ai,_bt)));}else{return new T0(2);}},_bv=function(_bw){if(E(_bw)==45){var _bx=function(_by){return new F(function(){return A1(_bm,new T1(1,new T(function(){return B(_av(B(_bi(_az,_by))));})));});};return new T1(1,B(_9h(_ai,_bx)));}else{return new T0(2);}};return B(_7h(B(_7h(new T1(0,_bv),new T1(0,_br))),_bo));});return new F(function(){return _7h(new T1(0,function(_bz){return (E(_bz)==101)?E(_bn):new T0(2);}),new T1(0,function(_bA){return (E(_bA)==69)?E(_bn):new T0(2);}));});},_bB=function(_bC){var _bD=function(_bE){return new F(function(){return A1(_bC,new T1(1,_bE));});};return function(_bF){return (E(_bF)==46)?new T1(1,B(_9h(_ai,_bD))):new T0(2);};},_bG=function(_bH){return new T1(0,B(_bB(_bH)));},_bI=function(_bJ){var _bK=function(_bL){var _bM=function(_bN){return new T1(1,B(_8A(_bl,_ae,function(_bO){return new F(function(){return A1(_bJ,new T1(5,new T3(1,_bL,_bN,_bO)));});})));};return new T1(1,B(_8A(_bG,_ag,_bM)));};return new F(function(){return _9h(_ai,_bK);});},_bP=function(_bQ){return new T1(1,B(_bI(_bQ)));},_bR=function(_bS){return E(E(_bS).a);},_bT=function(_bU,_bV,_bW){while(1){var _bX=E(_bW);if(!_bX._){return false;}else{if(!B(A3(_bR,_bU,_bV,_bX.a))){_bW=_bX.b;continue;}else{return true;}}}},_bY=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_bZ=function(_c0){return new F(function(){return _bT(_86,_c0,_bY);});},_c1=false,_c2=true,_c3=function(_c4){var _c5=new T(function(){return B(A1(_c4,_a2));}),_c6=new T(function(){return B(A1(_c4,_a1));});return function(_c7){switch(E(_c7)){case 79:return E(_c5);case 88:return E(_c6);case 111:return E(_c5);case 120:return E(_c6);default:return new T0(2);}};},_c8=function(_c9){return new T1(0,B(_c3(_c9)));},_ca=function(_cb){return new F(function(){return A1(_cb,_ai);});},_cc=function(_cd,_ce){var _cf=jsShowI(_cd);return new F(function(){return _O(fromJSStr(_cf),_ce);});},_cg=41,_ch=40,_ci=function(_cj,_ck,_cl){if(_ck>=0){return new F(function(){return _cc(_ck,_cl);});}else{if(_cj<=6){return new F(function(){return _cc(_ck,_cl);});}else{return new T2(1,_ch,new T(function(){var _cm=jsShowI(_ck);return B(_O(fromJSStr(_cm),new T2(1,_cg,_cl)));}));}}},_cn=function(_co){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_ci(9,_co,_u));}))));});},_cp=function(_cq){var _cr=E(_cq);if(!_cr._){return E(_cr.a);}else{return new F(function(){return I_toInt(_cr.a);});}},_cs=function(_ct,_cu){var _cv=E(_ct);if(!_cv._){var _cw=_cv.a,_cx=E(_cu);return (_cx._==0)?_cw<=_cx.a:I_compareInt(_cx.a,_cw)>=0;}else{var _cy=_cv.a,_cz=E(_cu);return (_cz._==0)?I_compareInt(_cy,_cz.a)<=0:I_compare(_cy,_cz.a)<=0;}},_cA=function(_cB){return new T0(2);},_cC=function(_cD){var _cE=E(_cD);if(!_cE._){return E(_cA);}else{var _cF=_cE.a,_cG=E(_cE.b);if(!_cG._){return E(_cF);}else{var _cH=new T(function(){return B(_cC(_cG));}),_cI=function(_cJ){return new F(function(){return _7h(B(A1(_cF,_cJ)),new T(function(){return B(A1(_cH,_cJ));}));});};return E(_cI);}}},_cK=function(_cL,_cM){var _cN=function(_cO,_cP,_cQ){var _cR=E(_cO);if(!_cR._){return new F(function(){return A1(_cQ,_cL);});}else{var _cS=E(_cP);if(!_cS._){return new T0(2);}else{if(E(_cR.a)!=E(_cS.a)){return new T0(2);}else{var _cT=new T(function(){return B(_cN(_cR.b,_cS.b,_cQ));});return new T1(0,function(_cU){return E(_cT);});}}}};return function(_cV){return new F(function(){return _cN(_cL,_cV,_cM);});};},_cW=new T(function(){return B(unCStr("SO"));}),_cX=14,_cY=function(_cZ){var _d0=new T(function(){return B(A1(_cZ,_cX));});return new T1(1,B(_cK(_cW,function(_d1){return E(_d0);})));},_d2=new T(function(){return B(unCStr("SOH"));}),_d3=1,_d4=function(_d5){var _d6=new T(function(){return B(A1(_d5,_d3));});return new T1(1,B(_cK(_d2,function(_d7){return E(_d6);})));},_d8=function(_d9){return new T1(1,B(_8A(_d4,_cY,_d9)));},_da=new T(function(){return B(unCStr("NUL"));}),_db=0,_dc=function(_dd){var _de=new T(function(){return B(A1(_dd,_db));});return new T1(1,B(_cK(_da,function(_df){return E(_de);})));},_dg=new T(function(){return B(unCStr("STX"));}),_dh=2,_di=function(_dj){var _dk=new T(function(){return B(A1(_dj,_dh));});return new T1(1,B(_cK(_dg,function(_dl){return E(_dk);})));},_dm=new T(function(){return B(unCStr("ETX"));}),_dn=3,_do=function(_dp){var _dq=new T(function(){return B(A1(_dp,_dn));});return new T1(1,B(_cK(_dm,function(_dr){return E(_dq);})));},_ds=new T(function(){return B(unCStr("EOT"));}),_dt=4,_du=function(_dv){var _dw=new T(function(){return B(A1(_dv,_dt));});return new T1(1,B(_cK(_ds,function(_dx){return E(_dw);})));},_dy=new T(function(){return B(unCStr("ENQ"));}),_dz=5,_dA=function(_dB){var _dC=new T(function(){return B(A1(_dB,_dz));});return new T1(1,B(_cK(_dy,function(_dD){return E(_dC);})));},_dE=new T(function(){return B(unCStr("ACK"));}),_dF=6,_dG=function(_dH){var _dI=new T(function(){return B(A1(_dH,_dF));});return new T1(1,B(_cK(_dE,function(_dJ){return E(_dI);})));},_dK=new T(function(){return B(unCStr("BEL"));}),_dL=7,_dM=function(_dN){var _dO=new T(function(){return B(A1(_dN,_dL));});return new T1(1,B(_cK(_dK,function(_dP){return E(_dO);})));},_dQ=new T(function(){return B(unCStr("BS"));}),_dR=8,_dS=function(_dT){var _dU=new T(function(){return B(A1(_dT,_dR));});return new T1(1,B(_cK(_dQ,function(_dV){return E(_dU);})));},_dW=new T(function(){return B(unCStr("HT"));}),_dX=9,_dY=function(_dZ){var _e0=new T(function(){return B(A1(_dZ,_dX));});return new T1(1,B(_cK(_dW,function(_e1){return E(_e0);})));},_e2=new T(function(){return B(unCStr("LF"));}),_e3=10,_e4=function(_e5){var _e6=new T(function(){return B(A1(_e5,_e3));});return new T1(1,B(_cK(_e2,function(_e7){return E(_e6);})));},_e8=new T(function(){return B(unCStr("VT"));}),_e9=11,_ea=function(_eb){var _ec=new T(function(){return B(A1(_eb,_e9));});return new T1(1,B(_cK(_e8,function(_ed){return E(_ec);})));},_ee=new T(function(){return B(unCStr("FF"));}),_ef=12,_eg=function(_eh){var _ei=new T(function(){return B(A1(_eh,_ef));});return new T1(1,B(_cK(_ee,function(_ej){return E(_ei);})));},_ek=new T(function(){return B(unCStr("CR"));}),_el=13,_em=function(_en){var _eo=new T(function(){return B(A1(_en,_el));});return new T1(1,B(_cK(_ek,function(_ep){return E(_eo);})));},_eq=new T(function(){return B(unCStr("SI"));}),_er=15,_es=function(_et){var _eu=new T(function(){return B(A1(_et,_er));});return new T1(1,B(_cK(_eq,function(_ev){return E(_eu);})));},_ew=new T(function(){return B(unCStr("DLE"));}),_ex=16,_ey=function(_ez){var _eA=new T(function(){return B(A1(_ez,_ex));});return new T1(1,B(_cK(_ew,function(_eB){return E(_eA);})));},_eC=new T(function(){return B(unCStr("DC1"));}),_eD=17,_eE=function(_eF){var _eG=new T(function(){return B(A1(_eF,_eD));});return new T1(1,B(_cK(_eC,function(_eH){return E(_eG);})));},_eI=new T(function(){return B(unCStr("DC2"));}),_eJ=18,_eK=function(_eL){var _eM=new T(function(){return B(A1(_eL,_eJ));});return new T1(1,B(_cK(_eI,function(_eN){return E(_eM);})));},_eO=new T(function(){return B(unCStr("DC3"));}),_eP=19,_eQ=function(_eR){var _eS=new T(function(){return B(A1(_eR,_eP));});return new T1(1,B(_cK(_eO,function(_eT){return E(_eS);})));},_eU=new T(function(){return B(unCStr("DC4"));}),_eV=20,_eW=function(_eX){var _eY=new T(function(){return B(A1(_eX,_eV));});return new T1(1,B(_cK(_eU,function(_eZ){return E(_eY);})));},_f0=new T(function(){return B(unCStr("NAK"));}),_f1=21,_f2=function(_f3){var _f4=new T(function(){return B(A1(_f3,_f1));});return new T1(1,B(_cK(_f0,function(_f5){return E(_f4);})));},_f6=new T(function(){return B(unCStr("SYN"));}),_f7=22,_f8=function(_f9){var _fa=new T(function(){return B(A1(_f9,_f7));});return new T1(1,B(_cK(_f6,function(_fb){return E(_fa);})));},_fc=new T(function(){return B(unCStr("ETB"));}),_fd=23,_fe=function(_ff){var _fg=new T(function(){return B(A1(_ff,_fd));});return new T1(1,B(_cK(_fc,function(_fh){return E(_fg);})));},_fi=new T(function(){return B(unCStr("CAN"));}),_fj=24,_fk=function(_fl){var _fm=new T(function(){return B(A1(_fl,_fj));});return new T1(1,B(_cK(_fi,function(_fn){return E(_fm);})));},_fo=new T(function(){return B(unCStr("EM"));}),_fp=25,_fq=function(_fr){var _fs=new T(function(){return B(A1(_fr,_fp));});return new T1(1,B(_cK(_fo,function(_ft){return E(_fs);})));},_fu=new T(function(){return B(unCStr("SUB"));}),_fv=26,_fw=function(_fx){var _fy=new T(function(){return B(A1(_fx,_fv));});return new T1(1,B(_cK(_fu,function(_fz){return E(_fy);})));},_fA=new T(function(){return B(unCStr("ESC"));}),_fB=27,_fC=function(_fD){var _fE=new T(function(){return B(A1(_fD,_fB));});return new T1(1,B(_cK(_fA,function(_fF){return E(_fE);})));},_fG=new T(function(){return B(unCStr("FS"));}),_fH=28,_fI=function(_fJ){var _fK=new T(function(){return B(A1(_fJ,_fH));});return new T1(1,B(_cK(_fG,function(_fL){return E(_fK);})));},_fM=new T(function(){return B(unCStr("GS"));}),_fN=29,_fO=function(_fP){var _fQ=new T(function(){return B(A1(_fP,_fN));});return new T1(1,B(_cK(_fM,function(_fR){return E(_fQ);})));},_fS=new T(function(){return B(unCStr("RS"));}),_fT=30,_fU=function(_fV){var _fW=new T(function(){return B(A1(_fV,_fT));});return new T1(1,B(_cK(_fS,function(_fX){return E(_fW);})));},_fY=new T(function(){return B(unCStr("US"));}),_fZ=31,_g0=function(_g1){var _g2=new T(function(){return B(A1(_g1,_fZ));});return new T1(1,B(_cK(_fY,function(_g3){return E(_g2);})));},_g4=new T(function(){return B(unCStr("SP"));}),_g5=32,_g6=function(_g7){var _g8=new T(function(){return B(A1(_g7,_g5));});return new T1(1,B(_cK(_g4,function(_g9){return E(_g8);})));},_ga=new T(function(){return B(unCStr("DEL"));}),_gb=127,_gc=function(_gd){var _ge=new T(function(){return B(A1(_gd,_gb));});return new T1(1,B(_cK(_ga,function(_gf){return E(_ge);})));},_gg=new T2(1,_gc,_u),_gh=new T2(1,_g6,_gg),_gi=new T2(1,_g0,_gh),_gj=new T2(1,_fU,_gi),_gk=new T2(1,_fO,_gj),_gl=new T2(1,_fI,_gk),_gm=new T2(1,_fC,_gl),_gn=new T2(1,_fw,_gm),_go=new T2(1,_fq,_gn),_gp=new T2(1,_fk,_go),_gq=new T2(1,_fe,_gp),_gr=new T2(1,_f8,_gq),_gs=new T2(1,_f2,_gr),_gt=new T2(1,_eW,_gs),_gu=new T2(1,_eQ,_gt),_gv=new T2(1,_eK,_gu),_gw=new T2(1,_eE,_gv),_gx=new T2(1,_ey,_gw),_gy=new T2(1,_es,_gx),_gz=new T2(1,_em,_gy),_gA=new T2(1,_eg,_gz),_gB=new T2(1,_ea,_gA),_gC=new T2(1,_e4,_gB),_gD=new T2(1,_dY,_gC),_gE=new T2(1,_dS,_gD),_gF=new T2(1,_dM,_gE),_gG=new T2(1,_dG,_gF),_gH=new T2(1,_dA,_gG),_gI=new T2(1,_du,_gH),_gJ=new T2(1,_do,_gI),_gK=new T2(1,_di,_gJ),_gL=new T2(1,_dc,_gK),_gM=new T2(1,_d8,_gL),_gN=new T(function(){return B(_cC(_gM));}),_gO=34,_gP=new T1(0,1114111),_gQ=92,_gR=39,_gS=function(_gT){var _gU=new T(function(){return B(A1(_gT,_dL));}),_gV=new T(function(){return B(A1(_gT,_dR));}),_gW=new T(function(){return B(A1(_gT,_dX));}),_gX=new T(function(){return B(A1(_gT,_e3));}),_gY=new T(function(){return B(A1(_gT,_e9));}),_gZ=new T(function(){return B(A1(_gT,_ef));}),_h0=new T(function(){return B(A1(_gT,_el));}),_h1=new T(function(){return B(A1(_gT,_gQ));}),_h2=new T(function(){return B(A1(_gT,_gR));}),_h3=new T(function(){return B(A1(_gT,_gO));}),_h4=new T(function(){var _h5=function(_h6){var _h7=new T(function(){return B(_49(E(_h6)));}),_h8=function(_h9){var _ha=B(_bi(_h7,_h9));if(!B(_cs(_ha,_gP))){return new T0(2);}else{return new F(function(){return A1(_gT,new T(function(){var _hb=B(_cp(_ha));if(_hb>>>0>1114111){return B(_cn(_hb));}else{return _hb;}}));});}};return new T1(1,B(_9h(_h6,_h8)));},_hc=new T(function(){var _hd=new T(function(){return B(A1(_gT,_fZ));}),_he=new T(function(){return B(A1(_gT,_fT));}),_hf=new T(function(){return B(A1(_gT,_fN));}),_hg=new T(function(){return B(A1(_gT,_fH));}),_hh=new T(function(){return B(A1(_gT,_fB));}),_hi=new T(function(){return B(A1(_gT,_fv));}),_hj=new T(function(){return B(A1(_gT,_fp));}),_hk=new T(function(){return B(A1(_gT,_fj));}),_hl=new T(function(){return B(A1(_gT,_fd));}),_hm=new T(function(){return B(A1(_gT,_f7));}),_hn=new T(function(){return B(A1(_gT,_f1));}),_ho=new T(function(){return B(A1(_gT,_eV));}),_hp=new T(function(){return B(A1(_gT,_eP));}),_hq=new T(function(){return B(A1(_gT,_eJ));}),_hr=new T(function(){return B(A1(_gT,_eD));}),_hs=new T(function(){return B(A1(_gT,_ex));}),_ht=new T(function(){return B(A1(_gT,_er));}),_hu=new T(function(){return B(A1(_gT,_cX));}),_hv=new T(function(){return B(A1(_gT,_dF));}),_hw=new T(function(){return B(A1(_gT,_dz));}),_hx=new T(function(){return B(A1(_gT,_dt));}),_hy=new T(function(){return B(A1(_gT,_dn));}),_hz=new T(function(){return B(A1(_gT,_dh));}),_hA=new T(function(){return B(A1(_gT,_d3));}),_hB=new T(function(){return B(A1(_gT,_db));}),_hC=function(_hD){switch(E(_hD)){case 64:return E(_hB);case 65:return E(_hA);case 66:return E(_hz);case 67:return E(_hy);case 68:return E(_hx);case 69:return E(_hw);case 70:return E(_hv);case 71:return E(_gU);case 72:return E(_gV);case 73:return E(_gW);case 74:return E(_gX);case 75:return E(_gY);case 76:return E(_gZ);case 77:return E(_h0);case 78:return E(_hu);case 79:return E(_ht);case 80:return E(_hs);case 81:return E(_hr);case 82:return E(_hq);case 83:return E(_hp);case 84:return E(_ho);case 85:return E(_hn);case 86:return E(_hm);case 87:return E(_hl);case 88:return E(_hk);case 89:return E(_hj);case 90:return E(_hi);case 91:return E(_hh);case 92:return E(_hg);case 93:return E(_hf);case 94:return E(_he);case 95:return E(_hd);default:return new T0(2);}};return B(_7h(new T1(0,function(_hE){return (E(_hE)==94)?E(new T1(0,_hC)):new T0(2);}),new T(function(){return B(A1(_gN,_gT));})));});return B(_7h(new T1(1,B(_8A(_c8,_ca,_h5))),_hc));});return new F(function(){return _7h(new T1(0,function(_hF){switch(E(_hF)){case 34:return E(_h3);case 39:return E(_h2);case 92:return E(_h1);case 97:return E(_gU);case 98:return E(_gV);case 102:return E(_gZ);case 110:return E(_gX);case 114:return E(_h0);case 116:return E(_gW);case 118:return E(_gY);default:return new T0(2);}}),_h4);});},_hG=function(_hH){return new F(function(){return A1(_hH,_2t);});},_hI=function(_hJ){var _hK=E(_hJ);if(!_hK._){return E(_hG);}else{var _hL=E(_hK.a),_hM=_hL>>>0,_hN=new T(function(){return B(_hI(_hK.b));});if(_hM>887){var _hO=u_iswspace(_hL);if(!E(_hO)){return E(_hG);}else{var _hP=function(_hQ){var _hR=new T(function(){return B(A1(_hN,_hQ));});return new T1(0,function(_hS){return E(_hR);});};return E(_hP);}}else{var _hT=E(_hM);if(_hT==32){var _hU=function(_hV){var _hW=new T(function(){return B(A1(_hN,_hV));});return new T1(0,function(_hX){return E(_hW);});};return E(_hU);}else{if(_hT-9>>>0>4){if(E(_hT)==160){var _hY=function(_hZ){var _i0=new T(function(){return B(A1(_hN,_hZ));});return new T1(0,function(_i1){return E(_i0);});};return E(_hY);}else{return E(_hG);}}else{var _i2=function(_i3){var _i4=new T(function(){return B(A1(_hN,_i3));});return new T1(0,function(_i5){return E(_i4);});};return E(_i2);}}}}},_i6=function(_i7){var _i8=new T(function(){return B(_i6(_i7));}),_i9=function(_ia){return (E(_ia)==92)?E(_i8):new T0(2);},_ib=function(_ic){return E(new T1(0,_i9));},_id=new T1(1,function(_ie){return new F(function(){return A2(_hI,_ie,_ib);});}),_if=new T(function(){return B(_gS(function(_ig){return new F(function(){return A1(_i7,new T2(0,_ig,_c2));});}));}),_ih=function(_ii){var _ij=E(_ii);if(_ij==38){return E(_i8);}else{var _ik=_ij>>>0;if(_ik>887){var _il=u_iswspace(_ij);return (E(_il)==0)?new T0(2):E(_id);}else{var _im=E(_ik);return (_im==32)?E(_id):(_im-9>>>0>4)?(E(_im)==160)?E(_id):new T0(2):E(_id);}}};return new F(function(){return _7h(new T1(0,function(_in){return (E(_in)==92)?E(new T1(0,_ih)):new T0(2);}),new T1(0,function(_io){var _ip=E(_io);if(E(_ip)==92){return E(_if);}else{return new F(function(){return A1(_i7,new T2(0,_ip,_c1));});}}));});},_iq=function(_ir,_is){var _it=new T(function(){return B(A1(_is,new T1(1,new T(function(){return B(A1(_ir,_u));}))));}),_iu=function(_iv){var _iw=E(_iv),_ix=E(_iw.a);if(E(_ix)==34){if(!E(_iw.b)){return E(_it);}else{return new F(function(){return _iq(function(_iy){return new F(function(){return A1(_ir,new T2(1,_ix,_iy));});},_is);});}}else{return new F(function(){return _iq(function(_iz){return new F(function(){return A1(_ir,new T2(1,_ix,_iz));});},_is);});}};return new F(function(){return _i6(_iu);});},_iA=new T(function(){return B(unCStr("_\'"));}),_iB=function(_iC){var _iD=u_iswalnum(_iC);if(!E(_iD)){return new F(function(){return _bT(_86,_iC,_iA);});}else{return true;}},_iE=function(_iF){return new F(function(){return _iB(E(_iF));});},_iG=new T(function(){return B(unCStr(",;()[]{}`"));}),_iH=new T(function(){return B(unCStr("=>"));}),_iI=new T2(1,_iH,_u),_iJ=new T(function(){return B(unCStr("~"));}),_iK=new T2(1,_iJ,_iI),_iL=new T(function(){return B(unCStr("@"));}),_iM=new T2(1,_iL,_iK),_iN=new T(function(){return B(unCStr("->"));}),_iO=new T2(1,_iN,_iM),_iP=new T(function(){return B(unCStr("<-"));}),_iQ=new T2(1,_iP,_iO),_iR=new T(function(){return B(unCStr("|"));}),_iS=new T2(1,_iR,_iQ),_iT=new T(function(){return B(unCStr("\\"));}),_iU=new T2(1,_iT,_iS),_iV=new T(function(){return B(unCStr("="));}),_iW=new T2(1,_iV,_iU),_iX=new T(function(){return B(unCStr("::"));}),_iY=new T2(1,_iX,_iW),_iZ=new T(function(){return B(unCStr(".."));}),_j0=new T2(1,_iZ,_iY),_j1=function(_j2){var _j3=new T(function(){return B(A1(_j2,_9e));}),_j4=new T(function(){var _j5=new T(function(){var _j6=function(_j7){var _j8=new T(function(){return B(A1(_j2,new T1(0,_j7)));});return new T1(0,function(_j9){return (E(_j9)==39)?E(_j8):new T0(2);});};return B(_gS(_j6));}),_ja=function(_jb){var _jc=E(_jb);switch(E(_jc)){case 39:return new T0(2);case 92:return E(_j5);default:var _jd=new T(function(){return B(A1(_j2,new T1(0,_jc)));});return new T1(0,function(_je){return (E(_je)==39)?E(_jd):new T0(2);});}},_jf=new T(function(){var _jg=new T(function(){return B(_iq(_2q,_j2));}),_jh=new T(function(){var _ji=new T(function(){var _jj=new T(function(){var _jk=function(_jl){var _jm=E(_jl),_jn=u_iswalpha(_jm);return (E(_jn)==0)?(E(_jm)==95)?new T1(1,B(_90(_iE,function(_jo){return new F(function(){return A1(_j2,new T1(3,new T2(1,_jm,_jo)));});}))):new T0(2):new T1(1,B(_90(_iE,function(_jp){return new F(function(){return A1(_j2,new T1(3,new T2(1,_jm,_jp)));});})));};return B(_7h(new T1(0,_jk),new T(function(){return new T1(1,B(_8A(_ac,_bP,_j2)));})));}),_jq=function(_jr){return (!B(_bT(_86,_jr,_bY)))?new T0(2):new T1(1,B(_90(_bZ,function(_js){var _jt=new T2(1,_jr,_js);if(!B(_bT(_8f,_jt,_j0))){return new F(function(){return A1(_j2,new T1(4,_jt));});}else{return new F(function(){return A1(_j2,new T1(2,_jt));});}})));};return B(_7h(new T1(0,_jq),_jj));});return B(_7h(new T1(0,function(_ju){if(!B(_bT(_86,_ju,_iG))){return new T0(2);}else{return new F(function(){return A1(_j2,new T1(2,new T2(1,_ju,_u)));});}}),_ji));});return B(_7h(new T1(0,function(_jv){return (E(_jv)==34)?E(_jg):new T0(2);}),_jh));});return B(_7h(new T1(0,function(_jw){return (E(_jw)==39)?E(new T1(0,_ja)):new T0(2);}),_jf));});return new F(function(){return _7h(new T1(1,function(_jx){return (E(_jx)._==0)?E(_j3):new T0(2);}),_j4);});},_jy=0,_jz=function(_jA,_jB){var _jC=new T(function(){var _jD=new T(function(){var _jE=function(_jF){var _jG=new T(function(){var _jH=new T(function(){return B(A1(_jB,_jF));});return B(_j1(function(_jI){var _jJ=E(_jI);return (_jJ._==2)?(!B(_7V(_jJ.a,_7U)))?new T0(2):E(_jH):new T0(2);}));}),_jK=function(_jL){return E(_jG);};return new T1(1,function(_jM){return new F(function(){return A2(_hI,_jM,_jK);});});};return B(A2(_jA,_jy,_jE));});return B(_j1(function(_jN){var _jO=E(_jN);return (_jO._==2)?(!B(_7V(_jO.a,_7T)))?new T0(2):E(_jD):new T0(2);}));}),_jP=function(_jQ){return E(_jC);};return function(_jR){return new F(function(){return A2(_hI,_jR,_jP);});};},_jS=function(_jT,_jU){var _jV=function(_jW){var _jX=new T(function(){return B(A1(_jT,_jW));}),_jY=function(_jZ){return new F(function(){return _7h(B(A1(_jX,_jZ)),new T(function(){return new T1(1,B(_jz(_jV,_jZ)));}));});};return E(_jY);},_k0=new T(function(){return B(A1(_jT,_jU));}),_k1=function(_k2){return new F(function(){return _7h(B(A1(_k0,_k2)),new T(function(){return new T1(1,B(_jz(_jV,_k2)));}));});};return E(_k1);},_k3=function(_k4,_k5){var _k6=function(_k7,_k8){var _k9=function(_ka){return new F(function(){return A1(_k8,new T(function(){return  -E(_ka);}));});},_kb=new T(function(){return B(_j1(function(_kc){return new F(function(){return A3(_k4,_kc,_k7,_k9);});}));}),_kd=function(_ke){return E(_kb);},_kf=function(_kg){return new F(function(){return A2(_hI,_kg,_kd);});},_kh=new T(function(){return B(_j1(function(_ki){var _kj=E(_ki);if(_kj._==4){var _kk=E(_kj.a);if(!_kk._){return new F(function(){return A3(_k4,_kj,_k7,_k8);});}else{if(E(_kk.a)==45){if(!E(_kk.b)._){return E(new T1(1,_kf));}else{return new F(function(){return A3(_k4,_kj,_k7,_k8);});}}else{return new F(function(){return A3(_k4,_kj,_k7,_k8);});}}}else{return new F(function(){return A3(_k4,_kj,_k7,_k8);});}}));}),_kl=function(_km){return E(_kh);};return new T1(1,function(_kn){return new F(function(){return A2(_hI,_kn,_kl);});});};return new F(function(){return _jS(_k6,_k5);});},_ko=new T(function(){return 1/0;}),_kp=function(_kq,_kr){return new F(function(){return A1(_kr,_ko);});},_ks=new T(function(){return 0/0;}),_kt=function(_ku,_kv){return new F(function(){return A1(_kv,_ks);});},_kw=new T(function(){return B(unCStr("NaN"));}),_kx=new T(function(){return B(unCStr("Infinity"));}),_ky=1024,_kz=-1021,_kA=new T(function(){return B(unCStr("base"));}),_kB=new T(function(){return B(unCStr("GHC.Exception"));}),_kC=new T(function(){return B(unCStr("ArithException"));}),_kD=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_kA,_kB,_kC),_kE=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_kD,_u,_u),_kF=function(_kG){return E(_kE);},_kH=function(_kI){var _kJ=E(_kI);return new F(function(){return _A(B(_y(_kJ.a)),_kF,_kJ.b);});},_kK=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_kL=new T(function(){return B(unCStr("denormal"));}),_kM=new T(function(){return B(unCStr("divide by zero"));}),_kN=new T(function(){return B(unCStr("loss of precision"));}),_kO=new T(function(){return B(unCStr("arithmetic underflow"));}),_kP=new T(function(){return B(unCStr("arithmetic overflow"));}),_kQ=function(_kR,_kS){switch(E(_kR)){case 0:return new F(function(){return _O(_kP,_kS);});break;case 1:return new F(function(){return _O(_kO,_kS);});break;case 2:return new F(function(){return _O(_kN,_kS);});break;case 3:return new F(function(){return _O(_kM,_kS);});break;case 4:return new F(function(){return _O(_kL,_kS);});break;default:return new F(function(){return _O(_kK,_kS);});}},_kT=function(_kU){return new F(function(){return _kQ(_kU,_u);});},_kV=function(_kW,_kX,_kY){return new F(function(){return _kQ(_kX,_kY);});},_kZ=function(_l0,_l1){return new F(function(){return _1S(_kQ,_l0,_l1);});},_l2=new T3(0,_kV,_kT,_kZ),_l3=new T(function(){return new T5(0,_kF,_l2,_l4,_kH,_kT);}),_l4=function(_5k){return new T2(0,_l3,_5k);},_l5=3,_l6=new T(function(){return B(_l4(_l5));}),_l7=new T(function(){return die(_l6);}),_l8=function(_l9,_la){var _lb=E(_l9);if(!_lb._){var _lc=_lb.a,_ld=E(_la);return (_ld._==0)?_lc==_ld.a:(I_compareInt(_ld.a,_lc)==0)?true:false;}else{var _le=_lb.a,_lf=E(_la);return (_lf._==0)?(I_compareInt(_le,_lf.a)==0)?true:false:(I_compare(_le,_lf.a)==0)?true:false;}},_lg=new T1(0,0),_lh=function(_li,_lj){while(1){var _lk=E(_li);if(!_lk._){var _ll=E(_lk.a);if(_ll==(-2147483648)){_li=new T1(1,I_fromInt(-2147483648));continue;}else{var _lm=E(_lj);if(!_lm._){return new T1(0,_ll%_lm.a);}else{_li=new T1(1,I_fromInt(_ll));_lj=_lm;continue;}}}else{var _ln=_lk.a,_lo=E(_lj);return (_lo._==0)?new T1(1,I_rem(_ln,I_fromInt(_lo.a))):new T1(1,I_rem(_ln,_lo.a));}}},_lp=function(_lq,_lr){if(!B(_l8(_lr,_lg))){return new F(function(){return _lh(_lq,_lr);});}else{return E(_l7);}},_ls=function(_lt,_lu){while(1){if(!B(_l8(_lu,_lg))){var _lv=_lu,_lw=B(_lp(_lt,_lu));_lt=_lv;_lu=_lw;continue;}else{return E(_lt);}}},_lx=function(_ly){var _lz=E(_ly);if(!_lz._){var _lA=E(_lz.a);return (_lA==(-2147483648))?E(_au):(_lA<0)?new T1(0, -_lA):E(_lz);}else{var _lB=_lz.a;return (I_compareInt(_lB,0)>=0)?E(_lz):new T1(1,I_negate(_lB));}},_lC=function(_lD,_lE){while(1){var _lF=E(_lD);if(!_lF._){var _lG=E(_lF.a);if(_lG==(-2147483648)){_lD=new T1(1,I_fromInt(-2147483648));continue;}else{var _lH=E(_lE);if(!_lH._){return new T1(0,quot(_lG,_lH.a));}else{_lD=new T1(1,I_fromInt(_lG));_lE=_lH;continue;}}}else{var _lI=_lF.a,_lJ=E(_lE);return (_lJ._==0)?new T1(0,I_toInt(I_quot(_lI,I_fromInt(_lJ.a)))):new T1(1,I_quot(_lI,_lJ.a));}}},_lK=5,_lL=new T(function(){return B(_l4(_lK));}),_lM=new T(function(){return die(_lL);}),_lN=function(_lO,_lP){if(!B(_l8(_lP,_lg))){var _lQ=B(_ls(B(_lx(_lO)),B(_lx(_lP))));return (!B(_l8(_lQ,_lg)))?new T2(0,B(_lC(_lO,_lQ)),B(_lC(_lP,_lQ))):E(_l7);}else{return E(_lM);}},_lR=new T1(0,1),_lS=new T(function(){return B(unCStr("Negative exponent"));}),_lT=new T(function(){return B(err(_lS));}),_lU=new T1(0,2),_lV=new T(function(){return B(_l8(_lU,_lg));}),_lW=function(_lX,_lY){while(1){var _lZ=E(_lX);if(!_lZ._){var _m0=_lZ.a,_m1=E(_lY);if(!_m1._){var _m2=_m1.a,_m3=subC(_m0,_m2);if(!E(_m3.b)){return new T1(0,_m3.a);}else{_lX=new T1(1,I_fromInt(_m0));_lY=new T1(1,I_fromInt(_m2));continue;}}else{_lX=new T1(1,I_fromInt(_m0));_lY=_m1;continue;}}else{var _m4=E(_lY);if(!_m4._){_lX=_lZ;_lY=new T1(1,I_fromInt(_m4.a));continue;}else{return new T1(1,I_sub(_lZ.a,_m4.a));}}}},_m5=function(_m6,_m7,_m8){while(1){if(!E(_lV)){if(!B(_l8(B(_lh(_m7,_lU)),_lg))){if(!B(_l8(_m7,_lR))){var _m9=B(_aN(_m6,_m6)),_ma=B(_lC(B(_lW(_m7,_lR)),_lU)),_mb=B(_aN(_m6,_m8));_m6=_m9;_m7=_ma;_m8=_mb;continue;}else{return new F(function(){return _aN(_m6,_m8);});}}else{var _m9=B(_aN(_m6,_m6)),_ma=B(_lC(_m7,_lU));_m6=_m9;_m7=_ma;continue;}}else{return E(_l7);}}},_mc=function(_md,_me){while(1){if(!E(_lV)){if(!B(_l8(B(_lh(_me,_lU)),_lg))){if(!B(_l8(_me,_lR))){return new F(function(){return _m5(B(_aN(_md,_md)),B(_lC(B(_lW(_me,_lR)),_lU)),_md);});}else{return E(_md);}}else{var _mf=B(_aN(_md,_md)),_mg=B(_lC(_me,_lU));_md=_mf;_me=_mg;continue;}}else{return E(_l7);}}},_mh=function(_mi,_mj){var _mk=E(_mi);if(!_mk._){var _ml=_mk.a,_mm=E(_mj);return (_mm._==0)?_ml<_mm.a:I_compareInt(_mm.a,_ml)>0;}else{var _mn=_mk.a,_mo=E(_mj);return (_mo._==0)?I_compareInt(_mn,_mo.a)<0:I_compare(_mn,_mo.a)<0;}},_mp=function(_mq,_mr){if(!B(_mh(_mr,_lg))){if(!B(_l8(_mr,_lg))){return new F(function(){return _mc(_mq,_mr);});}else{return E(_lR);}}else{return E(_lT);}},_ms=new T1(0,1),_mt=new T1(0,0),_mu=new T1(0,-1),_mv=function(_mw){var _mx=E(_mw);if(!_mx._){var _my=_mx.a;return (_my>=0)?(E(_my)==0)?E(_mt):E(_aj):E(_mu);}else{var _mz=I_compareInt(_mx.a,0);return (_mz<=0)?(E(_mz)==0)?E(_mt):E(_mu):E(_aj);}},_mA=function(_mB,_mC,_mD){while(1){var _mE=E(_mD);if(!_mE._){if(!B(_mh(_mB,_b0))){return new T2(0,B(_aN(_mC,B(_mp(_az,_mB)))),_lR);}else{var _mF=B(_mp(_az,B(_av(_mB))));return new F(function(){return _lN(B(_aN(_mC,B(_mv(_mF)))),B(_lx(_mF)));});}}else{var _mG=B(_lW(_mB,_ms)),_mH=B(_al(B(_aN(_mC,_az)),B(_49(E(_mE.a)))));_mB=_mG;_mC=_mH;_mD=_mE.b;continue;}}},_mI=function(_mJ,_mK){var _mL=E(_mJ);if(!_mL._){var _mM=_mL.a,_mN=E(_mK);return (_mN._==0)?_mM>=_mN.a:I_compareInt(_mN.a,_mM)<=0;}else{var _mO=_mL.a,_mP=E(_mK);return (_mP._==0)?I_compareInt(_mO,_mP.a)>=0:I_compare(_mO,_mP.a)>=0;}},_mQ=function(_mR){var _mS=E(_mR);if(!_mS._){var _mT=_mS.b;return new F(function(){return _lN(B(_aN(B(_b1(new T(function(){return B(_49(E(_mS.a)));}),new T(function(){return B(_aA(_mT,0));},1),B(_aF(_aJ,_mT)))),_ms)),_ms);});}else{var _mU=_mS.a,_mV=_mS.c,_mW=E(_mS.b);if(!_mW._){var _mX=E(_mV);if(!_mX._){return new F(function(){return _lN(B(_aN(B(_bi(_az,_mU)),_ms)),_ms);});}else{var _mY=_mX.a;if(!B(_mI(_mY,_b0))){var _mZ=B(_mp(_az,B(_av(_mY))));return new F(function(){return _lN(B(_aN(B(_bi(_az,_mU)),B(_mv(_mZ)))),B(_lx(_mZ)));});}else{return new F(function(){return _lN(B(_aN(B(_aN(B(_bi(_az,_mU)),B(_mp(_az,_mY)))),_ms)),_ms);});}}}else{var _n0=_mW.a,_n1=E(_mV);if(!_n1._){return new F(function(){return _mA(_b0,B(_bi(_az,_mU)),_n0);});}else{return new F(function(){return _mA(_n1.a,B(_bi(_az,_mU)),_n0);});}}}},_n2=function(_n3,_n4){while(1){var _n5=E(_n4);if(!_n5._){return __Z;}else{if(!B(A1(_n3,_n5.a))){return E(_n5);}else{_n4=_n5.b;continue;}}}},_n6=function(_n7,_n8){var _n9=E(_n7);if(!_n9._){var _na=_n9.a,_nb=E(_n8);return (_nb._==0)?_na>_nb.a:I_compareInt(_nb.a,_na)<0;}else{var _nc=_n9.a,_nd=E(_n8);return (_nd._==0)?I_compareInt(_nc,_nd.a)>0:I_compare(_nc,_nd.a)>0;}},_ne=0,_nf=function(_ng,_nh){return E(_ng)==E(_nh);},_ni=function(_nj){return new F(function(){return _nf(_ne,_nj);});},_nk=new T2(0,E(_b0),E(_lR)),_nl=new T1(1,_nk),_nm=new T1(0,-2147483648),_nn=new T1(0,2147483647),_no=function(_np,_nq,_nr){var _ns=E(_nr);if(!_ns._){return new T1(1,new T(function(){var _nt=B(_mQ(_ns));return new T2(0,E(_nt.a),E(_nt.b));}));}else{var _nu=E(_ns.c);if(!_nu._){return new T1(1,new T(function(){var _nv=B(_mQ(_ns));return new T2(0,E(_nv.a),E(_nv.b));}));}else{var _nw=_nu.a;if(!B(_n6(_nw,_nn))){if(!B(_mh(_nw,_nm))){var _nx=function(_ny){var _nz=_ny+B(_cp(_nw))|0;return (_nz<=(E(_nq)+3|0))?(_nz>=(E(_np)-3|0))?new T1(1,new T(function(){var _nA=B(_mQ(_ns));return new T2(0,E(_nA.a),E(_nA.b));})):E(_nl):__Z;},_nB=B(_n2(_ni,_ns.a));if(!_nB._){var _nC=E(_ns.b);if(!_nC._){return E(_nl);}else{var _nD=B(_5l(_ni,_nC.a));if(!E(_nD.b)._){return E(_nl);}else{return new F(function(){return _nx( -B(_aA(_nD.a,0)));});}}}else{return new F(function(){return _nx(B(_aA(_nB,0)));});}}else{return __Z;}}else{return __Z;}}}},_nE=function(_nF,_nG){return new T0(2);},_nH=new T1(0,1),_nI=function(_nJ,_nK){var _nL=E(_nJ);if(!_nL._){var _nM=_nL.a,_nN=E(_nK);if(!_nN._){var _nO=_nN.a;return (_nM!=_nO)?(_nM>_nO)?2:0:1;}else{var _nP=I_compareInt(_nN.a,_nM);return (_nP<=0)?(_nP>=0)?1:2:0;}}else{var _nQ=_nL.a,_nR=E(_nK);if(!_nR._){var _nS=I_compareInt(_nQ,_nR.a);return (_nS>=0)?(_nS<=0)?1:2:0;}else{var _nT=I_compare(_nQ,_nR.a);return (_nT>=0)?(_nT<=0)?1:2:0;}}},_nU=function(_nV,_nW){var _nX=E(_nV);return (_nX._==0)?_nX.a*Math.pow(2,_nW):I_toNumber(_nX.a)*Math.pow(2,_nW);},_nY=function(_nZ,_o0){while(1){var _o1=E(_nZ);if(!_o1._){var _o2=E(_o1.a);if(_o2==(-2147483648)){_nZ=new T1(1,I_fromInt(-2147483648));continue;}else{var _o3=E(_o0);if(!_o3._){var _o4=_o3.a;return new T2(0,new T1(0,quot(_o2,_o4)),new T1(0,_o2%_o4));}else{_nZ=new T1(1,I_fromInt(_o2));_o0=_o3;continue;}}}else{var _o5=E(_o0);if(!_o5._){_nZ=_o1;_o0=new T1(1,I_fromInt(_o5.a));continue;}else{var _o6=I_quotRem(_o1.a,_o5.a);return new T2(0,new T1(1,_o6.a),new T1(1,_o6.b));}}}},_o7=new T1(0,0),_o8=function(_o9,_oa,_ob){if(!B(_l8(_ob,_o7))){var _oc=B(_nY(_oa,_ob)),_od=_oc.a;switch(B(_nI(B(_4o(_oc.b,1)),_ob))){case 0:return new F(function(){return _nU(_od,_o9);});break;case 1:if(!(B(_cp(_od))&1)){return new F(function(){return _nU(_od,_o9);});}else{return new F(function(){return _nU(B(_al(_od,_nH)),_o9);});}break;default:return new F(function(){return _nU(B(_al(_od,_nH)),_o9);});}}else{return E(_l7);}},_oe=function(_of){var _og=function(_oh,_oi){while(1){if(!B(_mh(_oh,_of))){if(!B(_n6(_oh,_of))){if(!B(_l8(_oh,_of))){return new F(function(){return _5H("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2");});}else{return E(_oi);}}else{return _oi-1|0;}}else{var _oj=B(_4o(_oh,1)),_ok=_oi+1|0;_oh=_oj;_oi=_ok;continue;}}};return new F(function(){return _og(_aj,0);});},_ol=function(_om){var _on=E(_om);if(!_on._){var _oo=_on.a>>>0;if(!_oo){return -1;}else{var _op=function(_oq,_or){while(1){if(_oq>=_oo){if(_oq<=_oo){if(_oq!=_oo){return new F(function(){return _5H("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_or);}}else{return _or-1|0;}}else{var _os=imul(_oq,2)>>>0,_ot=_or+1|0;_oq=_os;_or=_ot;continue;}}};return new F(function(){return _op(1,0);});}}else{return new F(function(){return _oe(_on);});}},_ou=function(_ov){var _ow=E(_ov);if(!_ow._){var _ox=_ow.a>>>0;if(!_ox){return new T2(0,-1,0);}else{var _oy=function(_oz,_oA){while(1){if(_oz>=_ox){if(_oz<=_ox){if(_oz!=_ox){return new F(function(){return _5H("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_oA);}}else{return _oA-1|0;}}else{var _oB=imul(_oz,2)>>>0,_oC=_oA+1|0;_oz=_oB;_oA=_oC;continue;}}};return new T2(0,B(_oy(1,0)),(_ox&_ox-1>>>0)>>>0&4294967295);}}else{var _oD=_ow.a;return new T2(0,B(_ol(_ow)),I_compareInt(I_and(_oD,I_sub(_oD,I_fromInt(1))),0));}},_oE=function(_oF,_oG){while(1){var _oH=E(_oF);if(!_oH._){var _oI=_oH.a,_oJ=E(_oG);if(!_oJ._){return new T1(0,(_oI>>>0&_oJ.a>>>0)>>>0&4294967295);}else{_oF=new T1(1,I_fromInt(_oI));_oG=_oJ;continue;}}else{var _oK=E(_oG);if(!_oK._){_oF=_oH;_oG=new T1(1,I_fromInt(_oK.a));continue;}else{return new T1(1,I_and(_oH.a,_oK.a));}}}},_oL=new T1(0,2),_oM=function(_oN,_oO){var _oP=E(_oN);if(!_oP._){var _oQ=(_oP.a>>>0&(2<<_oO>>>0)-1>>>0)>>>0,_oR=1<<_oO>>>0;return (_oR<=_oQ)?(_oR>=_oQ)?1:2:0;}else{var _oS=B(_oE(_oP,B(_lW(B(_4o(_oL,_oO)),_aj)))),_oT=B(_4o(_aj,_oO));return (!B(_n6(_oT,_oS)))?(!B(_mh(_oT,_oS)))?1:2:0;}},_oU=function(_oV,_oW){while(1){var _oX=E(_oV);if(!_oX._){_oV=new T1(1,I_fromInt(_oX.a));continue;}else{return new T1(1,I_shiftRight(_oX.a,_oW));}}},_oY=function(_oZ,_p0,_p1,_p2){var _p3=B(_ou(_p2)),_p4=_p3.a;if(!E(_p3.b)){var _p5=B(_ol(_p1));if(_p5<((_p4+_oZ|0)-1|0)){var _p6=_p4+(_oZ-_p0|0)|0;if(_p6>0){if(_p6>_p5){if(_p6<=(_p5+1|0)){if(!E(B(_ou(_p1)).b)){return 0;}else{return new F(function(){return _nU(_nH,_oZ-_p0|0);});}}else{return 0;}}else{var _p7=B(_oU(_p1,_p6));switch(B(_oM(_p1,_p6-1|0))){case 0:return new F(function(){return _nU(_p7,_oZ-_p0|0);});break;case 1:if(!(B(_cp(_p7))&1)){return new F(function(){return _nU(_p7,_oZ-_p0|0);});}else{return new F(function(){return _nU(B(_al(_p7,_nH)),_oZ-_p0|0);});}break;default:return new F(function(){return _nU(B(_al(_p7,_nH)),_oZ-_p0|0);});}}}else{return new F(function(){return _nU(_p1,(_oZ-_p0|0)-_p6|0);});}}else{if(_p5>=_p0){var _p8=B(_oU(_p1,(_p5+1|0)-_p0|0));switch(B(_oM(_p1,_p5-_p0|0))){case 0:return new F(function(){return _nU(_p8,((_p5-_p4|0)+1|0)-_p0|0);});break;case 2:return new F(function(){return _nU(B(_al(_p8,_nH)),((_p5-_p4|0)+1|0)-_p0|0);});break;default:if(!(B(_cp(_p8))&1)){return new F(function(){return _nU(_p8,((_p5-_p4|0)+1|0)-_p0|0);});}else{return new F(function(){return _nU(B(_al(_p8,_nH)),((_p5-_p4|0)+1|0)-_p0|0);});}}}else{return new F(function(){return _nU(_p1, -_p4);});}}}else{var _p9=B(_ol(_p1))-_p4|0,_pa=function(_pb){var _pc=function(_pd,_pe){if(!B(_cs(B(_4o(_pe,_p0)),_pd))){return new F(function(){return _o8(_pb-_p0|0,_pd,_pe);});}else{return new F(function(){return _o8((_pb-_p0|0)+1|0,_pd,B(_4o(_pe,1)));});}};if(_pb>=_p0){if(_pb!=_p0){return new F(function(){return _pc(_p1,new T(function(){return B(_4o(_p2,_pb-_p0|0));}));});}else{return new F(function(){return _pc(_p1,_p2);});}}else{return new F(function(){return _pc(new T(function(){return B(_4o(_p1,_p0-_pb|0));}),_p2);});}};if(_oZ>_p9){return new F(function(){return _pa(_oZ);});}else{return new F(function(){return _pa(_p9);});}}},_pf=new T(function(){return 0/0;}),_pg=new T(function(){return -1/0;}),_ph=new T(function(){return 1/0;}),_pi=0,_pj=function(_pk,_pl){if(!B(_l8(_pl,_o7))){if(!B(_l8(_pk,_o7))){if(!B(_mh(_pk,_o7))){return new F(function(){return _oY(-1021,53,_pk,_pl);});}else{return  -B(_oY(-1021,53,B(_av(_pk)),_pl));}}else{return E(_pi);}}else{return (!B(_l8(_pk,_o7)))?(!B(_mh(_pk,_o7)))?E(_ph):E(_pg):E(_pf);}},_pm=function(_pn){var _po=E(_pn);switch(_po._){case 3:var _pp=_po.a;return (!B(_7V(_pp,_kx)))?(!B(_7V(_pp,_kw)))?E(_nE):E(_kt):E(_kp);case 5:var _pq=B(_no(_kz,_ky,_po.a));if(!_pq._){return E(_kp);}else{var _pr=new T(function(){var _ps=E(_pq.a);return B(_pj(_ps.a,_ps.b));});return function(_pt,_pu){return new F(function(){return A1(_pu,_pr);});};}break;default:return E(_nE);}},_pv=function(_pw){var _px=function(_py){return E(new T2(3,_pw,_8r));};return new T1(1,function(_pz){return new F(function(){return A2(_hI,_pz,_px);});});},_pA=new T(function(){return B(A3(_k3,_pm,_jy,_pv));}),_pB=function(_pC,_pD){while(1){var _pE=E(_pC);if(!_pE._){return E(_pD);}else{_pC=_pE.b;_pD=_pE.a;continue;}}},_pF=function(_pG){var _pH=E(_pG);if(!_pH._){return __Z;}else{var _pI=_pH.a,_pJ=new T(function(){if(E(B(_pB(_pI,_6U)))==37){var _pK=B(_6V(B(_72(_pA,new T(function(){return B(_6Q(_pI));})))));if(!_pK._){return E(_7f);}else{if(!E(_pK.b)._){return E(_pK.a)/100;}else{return E(_7d);}}}else{var _pL=B(_6V(B(_72(_pA,_pI))));if(!_pL._){return E(_7f);}else{if(!E(_pL.b)._){return E(_pL.a);}else{return E(_7d);}}}});return new T1(1,_pJ);}},_pM=function(_pN,_){var _pO=E(_pN);if(!_pO._){return E(_5L);}else{var _pP=_pO.a,_pQ=E(_pO.b);if(!_pQ._){return E(_5L);}else{var _pR=_pQ.a,_pS=E(_pQ.b);if(!_pS._){return E(_5L);}else{var _pT=_pS.a,_pU=E(_pS.b);if(!_pU._){return E(_5L);}else{var _pV=_pU.a,_pW=E(_pU.b);if(!_pW._){return E(_5L);}else{var _pX=_pW.a,_pY=E(_pW.b);if(!_pY._){return E(_5L);}else{var _pZ=E(_pY.b);if(!_pZ._){return E(_5L);}else{if(!E(_pZ.b)._){var _q0=function(_){var _q1=E(_4L),_q2=E(_4M),_q3=__app2(_q2,E(_pP),_q1),_q4=__app2(_q2,E(_pR),_q1),_q5=__app2(_q2,E(_pT),_q1),_q6=__app2(_q2,E(_pV),_q1),_q7=__app2(_q2,E(_pX),_q1),_q8=B(_pF(new T1(1,new T(function(){var _q9=String(_q3);return fromJSStr(_q9);}))));if(!_q8._){return _2t;}else{var _qa=B(_pF(new T1(1,new T(function(){var _qb=String(_q4);return fromJSStr(_qb);}))));if(!_qa._){return _2t;}else{var _qc=B(_pF(new T1(1,new T(function(){var _qd=String(_q5);return fromJSStr(_qd);}))));if(!_qc._){return _2t;}else{var _qe=B(_pF(new T1(1,new T(function(){var _qf=String(_q6);return fromJSStr(_qf);}))));if(!_qe._){return _2t;}else{var _qg=B(_pF(new T1(1,new T(function(){var _qh=String(_q7);return fromJSStr(_qh);}))));if(!_qg._){return _2t;}else{var _qi=toJSStr(E(_5M)),_qj=E(_q8.a),_qk=E(_qa.a),_ql=E(_qc.a),_qm=E(_qe.a),_qn=E(_qg.a),_qo=_qn*_qn/2,_qp=Math.log(_qk/_qj),_qq=( -_qp+_qm*(_ql+_qo))/_qn/Math.sqrt(_qm),_qr=( -_qp+_qm*(_ql+ -_qo))/_qn/Math.sqrt(_qm),_qs=E(_4N),_qt=__app3(_qs,E(_pY.a),_qi,toJSStr(B(_4s(2,_qj*0.5*(1-B(_3a( -_qq*0.7071067811865475)))-_qk*Math.exp( -_ql*_qm)*0.5*(1-B(_3a( -_qr*0.7071067811865475))))))),_qu=__app3(_qs,E(_pZ.a),_qi,toJSStr(B(_4s(2,_qk*Math.exp( -_ql*_qm)*0.5*(1-B(_3a(_qr*0.7071067811865475)))-_qj*0.5*(1-B(_3a(_qq*0.7071067811865475)))))));return new F(function(){return _35(_);});}}}}}},_qv=B(A(_6e,[_39,_38,_34,_pP,_4K,function(_qw,_){return new F(function(){return _q0(_);});},_])),_qx=B(A(_6e,[_39,_38,_34,_pR,_4K,function(_qy,_){return new F(function(){return _q0(_);});},_])),_qz=B(A(_6e,[_39,_38,_2H,_pT,_4J,function(_qA,_){return new F(function(){return _q0(_);});},_])),_qB=B(A(_6e,[_39,_38,_2H,_pV,_4J,function(_qC,_){return new F(function(){return _q0(_);});},_]));return new F(function(){return A(_6e,[_39,_38,_2H,_pX,_4J,function(_qD,_){return new F(function(){return _q0(_);});},_]);});}else{return E(_5L);}}}}}}}}},_qE=new T(function(){return B(unCStr("s"));}),_qF=new T(function(){return B(unCStr("k"));}),_qG=new T(function(){return B(unCStr("r"));}),_qH=new T(function(){return B(unCStr("t"));}),_qI=new T(function(){return B(unCStr("sigma"));}),_qJ=new T(function(){return B(unCStr("resultC"));}),_qK=new T(function(){return B(unCStr("resultP"));}),_qL=new T2(1,_qK,_u),_qM=new T2(1,_qJ,_qL),_qN=new T2(1,_qI,_qM),_qO=new T2(1,_qH,_qN),_qP=new T2(1,_qG,_qO),_qQ=new T2(1,_qF,_qP),_qR=new T2(1,_qE,_qQ),_qS=function(_qT){return new F(function(){return toJSStr(E(_qT));});},_qU=new T(function(){return B(_aF(_qS,_qR));}),_qV=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_qW=new T(function(){return B(unCStr("Maybe.fromJust: Nothing"));}),_qX=new T(function(){return B(err(_qW));}),_qY=function(_qZ){var _r0=E(_qZ);return (_r0._==0)?E(_qX):E(_r0.a);},_r1=function(_r2,_r3){while(1){var _r4=B((function(_r5,_r6){var _r7=E(_r5);if(!_r7._){return __Z;}else{var _r8=_r7.b,_r9=E(_r6);if(!_r9._){return __Z;}else{var _ra=_r9.b;if(!E(_r9.a)._){return new T2(1,_r7.a,new T(function(){return B(_r1(_r8,_ra));}));}else{_r2=_r8;_r3=_ra;return __continue;}}}})(_r2,_r3));if(_r4!=__continue){return _r4;}}},_rb=new T(function(){return B(unAppCStr("[]",_u));}),_rc=new T2(1,_1Q,_u),_rd=function(_re){var _rf=E(_re);if(!_rf._){return E(_rc);}else{var _rg=new T(function(){return B(_O(fromJSStr(E(_rf.a)),new T(function(){return B(_rd(_rf.b));},1)));});return new T2(1,_1P,_rg);}},_rh=function(_ri,_rj){var _rk=new T(function(){var _rl=B(_r1(_ri,_rj));if(!_rl._){return E(_rb);}else{var _rm=new T(function(){return B(_O(fromJSStr(E(_rl.a)),new T(function(){return B(_rd(_rl.b));},1)));});return new T2(1,_1R,_rm);}});return new F(function(){return err(B(unAppCStr("Elements with the following IDs could not be found: ",_rk)));});},_rn=function(_ro){while(1){var _rp=E(_ro);if(!_rp._){return false;}else{if(!E(_rp.a)._){return true;}else{_ro=_rp.b;continue;}}}},_rq=function(_rr,_rs,_rt){var _ru=B(_5P(_rr)),_rv=function(_rw){if(!B(_rn(_rw))){return new F(function(){return A1(_rt,new T(function(){return B(_aF(_qY,_rw));}));});}else{return new F(function(){return _rh(_rs,_rw);});}},_rx=new T(function(){var _ry=new T(function(){return B(A2(_6c,_ru,_u));}),_rz=function(_rA){var _rB=E(_rA);if(!_rB._){return E(_ry);}else{var _rC=new T(function(){return B(_rz(_rB.b));}),_rD=function(_rE){return new F(function(){return A3(_5R,_ru,_rC,function(_rF){return new F(function(){return A2(_6c,_ru,new T2(1,_rE,_rF));});});});},_rG=new T(function(){var _rH=function(_){var _rI=__app1(E(_qV),E(_rB.a)),_rJ=__eq(_rI,E(_67));return (E(_rJ)==0)?new T1(1,_rI):_2a;};return B(A2(_68,_rr,_rH));});return new F(function(){return A3(_5R,_ru,_rG,_rD);});}};return B(_rz(_rs));});return new F(function(){return A3(_5R,_ru,_rx,_rv);});},_rK=new T(function(){return B(_rq(_2s,_qU,_pM));});
var hasteMain = function() {B(A(_rK, [0]));};window.onload = hasteMain;