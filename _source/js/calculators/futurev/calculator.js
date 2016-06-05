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

var _0=function(_1,_2,_){var _3=B(A1(_1,_)),_4=B(A1(_2,_));return new T(function(){return B(A1(_3,_4));});},_5=function(_6,_7,_){var _8=B(A1(_7,_));return new T(function(){return B(A1(_6,_8));});},_9=function(_a,_){return _a;},_b=function(_c,_d,_){var _e=B(A1(_c,_));return C > 19 ? new F(function(){return A1(_d,_);}) : (++C,A1(_d,_));},_f=new T(function(){return unCStr("base");}),_g=new T(function(){return unCStr("GHC.IO.Exception");}),_h=new T(function(){return unCStr("IOException");}),_i=function(_j){return E(new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_f,_g,_h),__Z,__Z));},_k=function(_l){return E(E(_l).a);},_m=function(_n,_o,_p){var _q=B(A1(_n,_)),_r=B(A1(_o,_)),_s=hs_eqWord64(_q.a,_r.a);if(!_s){return __Z;}else{var _t=hs_eqWord64(_q.b,_r.b);return (!_t)?__Z:new T1(1,_p);}},_u=new T(function(){return unCStr(": ");}),_v=new T(function(){return unCStr(")");}),_w=new T(function(){return unCStr(" (");}),_x=function(_y,_z){var _A=E(_y);return (_A._==0)?E(_z):new T2(1,_A.a,new T(function(){return _x(_A.b,_z);}));},_B=new T(function(){return unCStr("interrupted");}),_C=new T(function(){return unCStr("system error");}),_D=new T(function(){return unCStr("unsatisified constraints");}),_E=new T(function(){return unCStr("user error");}),_F=new T(function(){return unCStr("permission denied");}),_G=new T(function(){return unCStr("illegal operation");}),_H=new T(function(){return unCStr("end of file");}),_I=new T(function(){return unCStr("resource exhausted");}),_J=new T(function(){return unCStr("resource busy");}),_K=new T(function(){return unCStr("does not exist");}),_L=new T(function(){return unCStr("already exists");}),_M=new T(function(){return unCStr("resource vanished");}),_N=new T(function(){return unCStr("timeout");}),_O=new T(function(){return unCStr("unsupported operation");}),_P=new T(function(){return unCStr("hardware fault");}),_Q=new T(function(){return unCStr("inappropriate type");}),_R=new T(function(){return unCStr("invalid argument");}),_S=new T(function(){return unCStr("failed");}),_T=new T(function(){return unCStr("protocol error");}),_U=function(_V,_W){switch(E(_V)){case 0:return _x(_L,_W);case 1:return _x(_K,_W);case 2:return _x(_J,_W);case 3:return _x(_I,_W);case 4:return _x(_H,_W);case 5:return _x(_G,_W);case 6:return _x(_F,_W);case 7:return _x(_E,_W);case 8:return _x(_D,_W);case 9:return _x(_C,_W);case 10:return _x(_T,_W);case 11:return _x(_S,_W);case 12:return _x(_R,_W);case 13:return _x(_Q,_W);case 14:return _x(_P,_W);case 15:return _x(_O,_W);case 16:return _x(_N,_W);case 17:return _x(_M,_W);default:return _x(_B,_W);}},_X=new T(function(){return unCStr("}");}),_Y=new T(function(){return unCStr("{handle: ");}),_Z=function(_10,_11,_12,_13,_14,_15){var _16=new T(function(){var _17=new T(function(){var _18=new T(function(){var _19=E(_13);if(!_19._){return E(_15);}else{var _1a=new T(function(){return _x(_19,new T(function(){return _x(_v,_15);},1));},1);return _x(_w,_1a);}},1);return _U(_11,_18);}),_1b=E(_12);if(!_1b._){return E(_17);}else{return _x(_1b,new T(function(){return _x(_u,_17);},1));}}),_1c=E(_14);if(!_1c._){var _1d=E(_10);if(!_1d._){return E(_16);}else{var _1e=E(_1d.a);if(!_1e._){var _1f=new T(function(){var _1g=new T(function(){return _x(_X,new T(function(){return _x(_u,_16);},1));},1);return _x(_1e.a,_1g);},1);return _x(_Y,_1f);}else{var _1h=new T(function(){var _1i=new T(function(){return _x(_X,new T(function(){return _x(_u,_16);},1));},1);return _x(_1e.a,_1i);},1);return _x(_Y,_1h);}}}else{return _x(_1c.a,new T(function(){return _x(_u,_16);},1));}},_1j=function(_1k){var _1l=E(_1k);return _Z(_1l.a,_1l.b,_1l.c,_1l.d,_1l.f,__Z);},_1m=function(_1n,_1o){var _1p=E(_1n);return _Z(_1p.a,_1p.b,_1p.c,_1p.d,_1p.f,_1o);},_1q=function(_1r,_1s,_1t){var _1u=E(_1s);if(!_1u._){return unAppCStr("[]",_1t);}else{var _1v=new T(function(){var _1w=new T(function(){var _1x=function(_1y){var _1z=E(_1y);if(!_1z._){return E(new T2(1,93,_1t));}else{var _1A=new T(function(){return B(A2(_1r,_1z.a,new T(function(){return _1x(_1z.b);})));});return new T2(1,44,_1A);}};return _1x(_1u.b);});return B(A2(_1r,_1u.a,_1w));});return new T2(1,91,_1v);}},_1B=new T(function(){return new T5(0,_i,new T3(0,function(_1C,_1D,_1E){var _1F=E(_1D);return _Z(_1F.a,_1F.b,_1F.c,_1F.d,_1F.f,_1E);},_1j,function(_1G,_1H){return _1q(_1m,_1G,_1H);}),function(_1I){return new T2(0,_1B,_1I);},function(_1J){var _1K=E(_1J);return _m(_k(_1K.a),_i,_1K.b);},_1j);}),_1L=new T(function(){return E(_1B);}),_1M=function(_1N){return E(E(_1N).c);},_1O=function(_1P){return new T6(0,__Z,7,__Z,_1P,__Z,__Z);},_1Q=function(_1R,_){var _1S=new T(function(){return B(A2(_1M,_1L,new T(function(){return B(A1(_1O,_1R));})));});return die(_1S);},_1T=function(_1U,_){return _1Q(_1U,_);},_1V=function(_1W){return E(_1W);},_1X=new T2(0,new T5(0,new T5(0,new T2(0,_5,function(_1Y,_1Z,_){var _20=B(A1(_1Z,_));return _1Y;}),_9,_0,_b,function(_21,_22,_){var _23=B(A1(_21,_)),_24=B(A1(_22,_));return _23;}),function(_25,_26,_){var _27=B(A1(_25,_));return C > 19 ? new F(function(){return A2(_26,_27,_);}) : (++C,A2(_26,_27,_));},_b,_9,function(_28){return C > 19 ? new F(function(){return A1(_1T,_28);}) : (++C,A1(_1T,_28));}),_1V),_29=function(_){return 0;},_2a=function(_2b,_2c,_){return _29(_);},_2d=function(_2e){switch(E(_2e)){case 0:return "load";case 1:return "unload";case 2:return "change";case 3:return "focus";case 4:return "blur";case 5:return "submit";default:return "scroll";}},_2f=function(_2g,_){var _2h=_2g["keyCode"],_2i=_2g["ctrlKey"],_2j=_2g["altKey"],_2k=_2g["shiftKey"],_2l=_2g["metaKey"];return new T(function(){var _2m=Number(_2h),_2n=jsTrunc(_2m);return new T5(0,_2n,E(_2i),E(_2j),E(_2k),E(_2l));});},_2o=new T2(0,function(_2p){switch(E(_2p)){case 0:return "keypress";case 1:return "keyup";default:return "keydown";}},function(_2q,_2r,_){return _2f(E(_2r),_);}),_2s=function(_){return 0;},_2t=new T2(0,_1V,function(_2u,_){return new T1(1,_2u);}),_2v=new T2(0,_1X,_9),_2w=function(_2x,_2y){while(1){var _2z=E(_2x);if(!_2z._){return E(_2y);}else{var _2A=new T2(1,_2z.a,_2y);_2x=_2z.b;_2y=_2A;continue;}}},_2B=function(_2C){return _2w(_2C,__Z);},_2D=function(_2E,_2F,_2G){while(1){var _2H=(function(_2I,_2J,_2K){var _2L=E(_2I);if(!_2L._){return new T2(0,new T(function(){return _2B(_2J);}),new T(function(){return _2B(_2K);}));}else{var _2M=_2J,_2N=new T2(1,_2L.a,_2K);_2E=_2L.b;_2F=_2M;_2G=_2N;return __continue;}})(_2E,_2F,_2G);if(_2H!=__continue){return _2H;}}},_2O=function(_2P,_2Q,_2R){while(1){var _2S=(function(_2T,_2U,_2V){var _2W=E(_2T);if(!_2W._){return new T2(0,new T(function(){return _2B(_2U);}),new T(function(){return _2B(_2V);}));}else{var _2X=_2W.b,_2Y=E(_2W.a);if(_2Y==46){return _2D(_2X,_2U,__Z);}else{var _2Z=new T2(1,_2Y,_2U),_30=_2V;_2P=_2X;_2Q=_2Z;_2R=_30;return __continue;}}})(_2P,_2Q,_2R);if(_2S!=__continue){return _2S;}}},_31=function(_32,_33){var _34=E(_33);if(!_34._){return __Z;}else{var _35=_34.a,_36=E(_32);return (_36==1)?new T2(1,_35,__Z):new T2(1,_35,new T(function(){return _31(_36-1|0,_34.b);}));}},_37=function(_38){var _39=I_decodeDouble(_38);return new T2(0,new T1(1,_39.b),_39.a);},_3a=function(_3b){var _3c=E(_3b);if(!_3c._){return _3c.a;}else{return I_toNumber(_3c.a);}},_3d=function(_3e){return new T1(0,_3e);},_3f=function(_3g){var _3h=hs_intToInt64(2147483647),_3i=hs_leInt64(_3g,_3h);if(!_3i){return new T1(1,I_fromInt64(_3g));}else{var _3j=hs_intToInt64(-2147483648),_3k=hs_geInt64(_3g,_3j);if(!_3k){return new T1(1,I_fromInt64(_3g));}else{var _3l=hs_int64ToInt(_3g);return _3d(_3l);}}},_3m=function(_3n){var _3o=hs_intToInt64(_3n);return E(_3o);},_3p=function(_3q){var _3r=E(_3q);if(!_3r._){return _3m(_3r.a);}else{return I_toInt64(_3r.a);}},_3s=function(_3t,_3u){while(1){var _3v=E(_3t);if(!_3v._){_3t=new T1(1,I_fromInt(_3v.a));continue;}else{return new T1(1,I_shiftLeft(_3v.a,_3u));}}},_3w=function(_3x,_3y){var _3z=Math.pow(10,_3x),_3A=rintDouble(_3y*_3z),_3B=_37(_3A),_3C=_3B.a,_3D=_3B.b,_3E=function(_3F,_3G){var _3H=new T(function(){return unAppCStr(".",new T(function(){if(0>=_3x){return __Z;}else{return _31(_3x,_3G);}}));},1);return _x(_3F,_3H);};if(_3D>=0){var _3I=jsShow(_3a(_3s(_3C,_3D))/_3z),_3J=_2O(fromJSStr(_3I),__Z,__Z);return _3E(_3J.a,_3J.b);}else{var _3K=hs_uncheckedIShiftRA64(_3p(_3C), -_3D),_3L=jsShow(_3a(_3f(_3K))/_3z),_3M=_2O(fromJSStr(_3L),__Z,__Z);return _3E(_3M.a,_3M.b);}},_3N=(function(e,p){var x = e[p];return typeof x === 'undefined' ? '' : x.toString();}),_3O=(function(e,p,v){e[p] = v;}),_3P=new T(function(){return unCStr("base");}),_3Q=new T(function(){return unCStr("Control.Exception.Base");}),_3R=new T(function(){return unCStr("PatternMatchFail");}),_3S=function(_3T){return E(new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_3P,_3Q,_3R),__Z,__Z));},_3U=function(_3V){return E(E(_3V).a);},_3W=function(_3X,_3Y){return _x(E(_3X).a,_3Y);},_3Z=new T(function(){return new T5(0,_3S,new T3(0,function(_40,_41,_42){return _x(E(_41).a,_42);},_3U,function(_43,_44){return _1q(_3W,_43,_44);}),function(_45){return new T2(0,_3Z,_45);},function(_46){var _47=E(_46);return _m(_k(_47.a),_3S,_47.b);},_3U);}),_48=new T(function(){return unCStr("Non-exhaustive patterns in");}),_49=function(_4a,_4b){return die(new T(function(){return B(A2(_1M,_4b,_4a));}));},_4c=function(_4d,_4e){return _49(_4d,_4e);},_4f=function(_4g,_4h){var _4i=E(_4h);if(!_4i._){return new T2(0,__Z,__Z);}else{var _4j=_4i.a;if(!B(A1(_4g,_4j))){return new T2(0,__Z,_4i);}else{var _4k=new T(function(){var _4l=_4f(_4g,_4i.b);return new T2(0,_4l.a,_4l.b);});return new T2(0,new T2(1,_4j,new T(function(){return E(E(_4k).a);})),new T(function(){return E(E(_4k).b);}));}}},_4m=new T(function(){return unCStr("\n");}),_4n=function(_4o){return (E(_4o)==124)?false:true;},_4p=function(_4q,_4r){var _4s=_4f(_4n,unCStr(_4q)),_4t=_4s.a,_4u=function(_4v,_4w){var _4x=new T(function(){var _4y=new T(function(){return _x(_4r,new T(function(){return _x(_4w,_4m);},1));});return unAppCStr(": ",_4y);},1);return _x(_4v,_4x);},_4z=E(_4s.b);if(!_4z._){return _4u(_4t,__Z);}else{if(E(_4z.a)==124){return _4u(_4t,new T2(1,32,_4z.b));}else{return _4u(_4t,__Z);}}},_4A=function(_4B){return _4c(new T1(0,new T(function(){return _4p(_4B,_48);})),_3Z);},_4C=new T(function(){return B((function(_4D){return C > 19 ? new F(function(){return _4A("calculator.hs:(10,1)-(24,37)|function calculator");}) : (++C,_4A("calculator.hs:(10,1)-(24,37)|function calculator"));})(_));}),_4E=new T(function(){return unCStr("innerHTML");}),_4F=function(_4G){return E(E(_4G).a);},_4H=function(_4I){return E(E(_4I).a);},_4J=function(_4K){return E(E(_4K).b);},_4L=function(_4M){return E(E(_4M).a);},_4N=function(_4O){return E(E(_4O).b);},_4P=function(_4Q){return E(E(_4Q).a);},_4R=function(_4S){var _4T=B(A1(_4S,_));return E(_4T);},_4U=new T(function(){return _4R(function(_){return nMV(__Z);});}),_4V=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_4W=new T(function(){return _4R(function(_){return __jsNull();});}),_4X=function(_4Y){return E(E(_4Y).b);},_4Z=function(_50){return E(E(_50).b);},_51=function(_52){return E(E(_52).d);},_53=function(_54,_55,_56,_57,_58,_59){var _5a=_4F(_54),_5b=_4H(_5a),_5c=new T(function(){return _4X(_5a);}),_5d=new T(function(){return _51(_5b);}),_5e=new T(function(){return B(A2(_4L,_55,_57));}),_5f=new T(function(){return B(A2(_4P,_56,_58));}),_5g=function(_5h){return C > 19 ? new F(function(){return A1(_5d,new T3(0,_5f,_5e,_5h));}) : (++C,A1(_5d,new T3(0,_5f,_5e,_5h)));},_5i=function(_5j){var _5k=new T(function(){var _5l=new T(function(){var _5m=__createJSFunc(2,function(_5n,_){var _5o=B(A2(E(_5j),_5n,_));return _4W;}),_5p=_5m;return function(_){return _4V(E(_5e),E(_5f),_5p);};});return B(A1(_5c,_5l));});return C > 19 ? new F(function(){return A3(_4J,_5b,_5k,_5g);}) : (++C,A3(_4J,_5b,_5k,_5g));},_5q=new T(function(){var _5r=new T(function(){return _4X(_5a);}),_5s=function(_5t){var _5u=new T(function(){return B(A1(_5r,function(_){var _=wMV(E(_4U),new T1(1,_5t));return C > 19 ? new F(function(){return A(_4N,[_56,_58,_5t,_]);}) : (++C,A(_4N,[_56,_58,_5t,_]));}));});return C > 19 ? new F(function(){return A3(_4J,_5b,_5u,_59);}) : (++C,A3(_4J,_5b,_5u,_59));};return B(A2(_4Z,_54,_5s));});return C > 19 ? new F(function(){return A3(_4J,_5b,_5q,_5i);}) : (++C,A3(_4J,_5b,_5q,_5i));},_5v=function(_5w,_5x){var _5y=E(_5x);return (_5y._==0)?__Z:new T2(1,_5w,new T(function(){return _5v(_5y.a,_5y.b);}));},_5z=new T(function(){return unCStr(": empty list");}),_5A=new T(function(){return unCStr("Prelude.");}),_5B=function(_5C){return err(_x(_5A,new T(function(){return _x(_5C,_5z);},1)));},_5D=new T(function(){return _5B(new T(function(){return unCStr("init");}));}),_5E=function(_5F){var _5G=E(_5F);if(!_5G._){return E(_5D);}else{return _5v(_5G.a,_5G.b);}},_5H=new T(function(){return _5B(new T(function(){return unCStr("last");}));}),_5I=function(_5J){while(1){var _5K=(function(_5L){var _5M=E(_5L);if(!_5M._){return __Z;}else{var _5N=_5M.b,_5O=E(_5M.a);if(!E(_5O.b)._){return new T2(1,_5O.a,new T(function(){return _5I(_5N);}));}else{_5J=_5N;return __continue;}}})(_5J);if(_5K!=__continue){return _5K;}}},_5P=function(_5Q,_5R){while(1){var _5S=(function(_5T,_5U){var _5V=E(_5T);switch(_5V._){case 0:var _5W=E(_5U);if(!_5W._){return __Z;}else{_5Q=B(A1(_5V.a,_5W.a));_5R=_5W.b;return __continue;}break;case 1:var _5X=B(A1(_5V.a,_5U)),_5Y=_5U;_5Q=_5X;_5R=_5Y;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_5V.a,_5U),new T(function(){return _5P(_5V.b,_5U);}));default:return E(_5V.a);}})(_5Q,_5R);if(_5S!=__continue){return _5S;}}},_5Z=new T(function(){return err(new T(function(){return unCStr("Prelude.read: ambiguous parse");}));}),_60=new T(function(){return err(new T(function(){return unCStr("Prelude.read: no parse");}));}),_61=new T(function(){return B(_4A("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_62=function(_63,_64){var _65=function(_66){var _67=E(_64);if(_67._==3){return new T2(3,_67.a,new T(function(){return _62(_63,_67.b);}));}else{var _68=E(_63);if(_68._==2){return _67;}else{if(_67._==2){return _68;}else{var _69=function(_6a){if(_67._==4){var _6b=function(_6c){return new T1(4,new T(function(){return _x(_5P(_68,_6c),_67.a);}));};return new T1(1,_6b);}else{if(_68._==1){var _6d=_68.a;if(!_67._){return new T1(1,function(_6e){return _62(B(A1(_6d,_6e)),_67);});}else{var _6f=function(_6g){return _62(B(A1(_6d,_6g)),new T(function(){return B(A1(_67.a,_6g));}));};return new T1(1,_6f);}}else{if(!_67._){return E(_61);}else{var _6h=function(_6i){return _62(_68,new T(function(){return B(A1(_67.a,_6i));}));};return new T1(1,_6h);}}}};switch(_68._){case 1:if(_67._==4){var _6j=function(_6k){return new T1(4,new T(function(){return _x(_5P(B(A1(_68.a,_6k)),_6k),_67.a);}));};return new T1(1,_6j);}else{return _69(_);}break;case 4:var _6l=_68.a;switch(_67._){case 0:var _6m=function(_6n){var _6o=new T(function(){return _x(_6l,new T(function(){return _5P(_67,_6n);},1));});return new T1(4,_6o);};return new T1(1,_6m);case 1:var _6p=function(_6q){var _6r=new T(function(){return _x(_6l,new T(function(){return _5P(B(A1(_67.a,_6q)),_6q);},1));});return new T1(4,_6r);};return new T1(1,_6p);default:return new T1(4,new T(function(){return _x(_6l,_67.a);}));}break;default:return _69(_);}}}}},_6s=E(_63);switch(_6s._){case 0:var _6t=E(_64);if(!_6t._){var _6u=function(_6v){return _62(B(A1(_6s.a,_6v)),new T(function(){return B(A1(_6t.a,_6v));}));};return new T1(0,_6u);}else{return _65(_);}break;case 3:return new T2(3,_6s.a,new T(function(){return _62(_6s.b,_64);}));default:return _65(_);}},_6w=new T(function(){return unCStr("(");}),_6x=new T(function(){return unCStr(")");}),_6y=function(_6z,_6A){while(1){var _6B=E(_6z);if(!_6B._){return (E(_6A)._==0)?true:false;}else{var _6C=E(_6A);if(!_6C._){return false;}else{if(E(_6B.a)!=E(_6C.a)){return false;}else{_6z=_6B.b;_6A=_6C.b;continue;}}}}},_6D=new T2(0,function(_6E,_6F){return E(_6E)==E(_6F);},function(_6G,_6H){return E(_6G)!=E(_6H);}),_6I=function(_6J,_6K){while(1){var _6L=E(_6J);if(!_6L._){return (E(_6K)._==0)?true:false;}else{var _6M=E(_6K);if(!_6M._){return false;}else{if(E(_6L.a)!=E(_6M.a)){return false;}else{_6J=_6L.b;_6K=_6M.b;continue;}}}}},_6N=function(_6O,_6P){return (!_6I(_6O,_6P))?true:false;},_6Q=function(_6R,_6S){var _6T=E(_6R);switch(_6T._){case 0:return new T1(0,function(_6U){return C > 19 ? new F(function(){return _6Q(B(A1(_6T.a,_6U)),_6S);}) : (++C,_6Q(B(A1(_6T.a,_6U)),_6S));});case 1:return new T1(1,function(_6V){return C > 19 ? new F(function(){return _6Q(B(A1(_6T.a,_6V)),_6S);}) : (++C,_6Q(B(A1(_6T.a,_6V)),_6S));});case 2:return new T0(2);case 3:return _62(B(A1(_6S,_6T.a)),new T(function(){return B(_6Q(_6T.b,_6S));}));default:var _6W=function(_6X){var _6Y=E(_6X);if(!_6Y._){return __Z;}else{var _6Z=E(_6Y.a);return _x(_5P(B(A1(_6S,_6Z.a)),_6Z.b),new T(function(){return _6W(_6Y.b);},1));}},_70=_6W(_6T.a);return (_70._==0)?new T0(2):new T1(4,_70);}},_71=new T0(2),_72=function(_73){return new T2(3,_73,_71);},_74=function(_75,_76){var _77=E(_75);if(!_77){return C > 19 ? new F(function(){return A1(_76,0);}) : (++C,A1(_76,0));}else{var _78=new T(function(){return B(_74(_77-1|0,_76));});return new T1(0,function(_79){return E(_78);});}},_7a=function(_7b,_7c,_7d){var _7e=new T(function(){return B(A1(_7b,_72));}),_7f=function(_7g,_7h,_7i,_7j){while(1){var _7k=B((function(_7l,_7m,_7n,_7o){var _7p=E(_7l);switch(_7p._){case 0:var _7q=E(_7m);if(!_7q._){return C > 19 ? new F(function(){return A1(_7c,_7o);}) : (++C,A1(_7c,_7o));}else{var _7r=_7n+1|0,_7s=_7o;_7g=B(A1(_7p.a,_7q.a));_7h=_7q.b;_7i=_7r;_7j=_7s;return __continue;}break;case 1:var _7t=B(A1(_7p.a,_7m)),_7u=_7m,_7r=_7n,_7s=_7o;_7g=_7t;_7h=_7u;_7i=_7r;_7j=_7s;return __continue;case 2:return C > 19 ? new F(function(){return A1(_7c,_7o);}) : (++C,A1(_7c,_7o));break;case 3:var _7v=new T(function(){return B(_6Q(_7p,_7o));});return C > 19 ? new F(function(){return _74(_7n,function(_7w){return E(_7v);});}) : (++C,_74(_7n,function(_7w){return E(_7v);}));break;default:return C > 19 ? new F(function(){return _6Q(_7p,_7o);}) : (++C,_6Q(_7p,_7o));}})(_7g,_7h,_7i,_7j));if(_7k!=__continue){return _7k;}}};return function(_7x){return _7f(_7e,_7x,0,_7d);};},_7y=function(_7z){return C > 19 ? new F(function(){return A1(_7z,__Z);}) : (++C,A1(_7z,__Z));},_7A=function(_7B,_7C){var _7D=function(_7E){var _7F=E(_7E);if(!_7F._){return _7y;}else{var _7G=_7F.a;if(!B(A1(_7B,_7G))){return _7y;}else{var _7H=new T(function(){return _7D(_7F.b);}),_7I=function(_7J){var _7K=new T(function(){return B(A1(_7H,function(_7L){return C > 19 ? new F(function(){return A1(_7J,new T2(1,_7G,_7L));}) : (++C,A1(_7J,new T2(1,_7G,_7L)));}));});return new T1(0,function(_7M){return E(_7K);});};return _7I;}}};return function(_7N){return C > 19 ? new F(function(){return A2(_7D,_7N,_7C);}) : (++C,A2(_7D,_7N,_7C));};},_7O=new T(function(){return err(new T(function(){return unCStr("valDig: Bad base");}));}),_7P=function(_7Q,_7R){var _7S=function(_7T,_7U){var _7V=E(_7T);if(!_7V._){var _7W=new T(function(){return B(A1(_7U,__Z));});return function(_7X){return C > 19 ? new F(function(){return A1(_7X,_7W);}) : (++C,A1(_7X,_7W));};}else{var _7Y=E(_7V.a),_7Z=function(_80){var _81=new T(function(){return _7S(_7V.b,function(_82){return C > 19 ? new F(function(){return A1(_7U,new T2(1,_80,_82));}) : (++C,A1(_7U,new T2(1,_80,_82)));});}),_83=function(_84){var _85=new T(function(){return B(A1(_81,_84));});return new T1(0,function(_86){return E(_85);});};return _83;};switch(E(_7Q)){case 8:if(48>_7Y){var _87=new T(function(){return B(A1(_7U,__Z));});return function(_88){return C > 19 ? new F(function(){return A1(_88,_87);}) : (++C,A1(_88,_87));};}else{if(_7Y>55){var _89=new T(function(){return B(A1(_7U,__Z));});return function(_8a){return C > 19 ? new F(function(){return A1(_8a,_89);}) : (++C,A1(_8a,_89));};}else{return _7Z(_7Y-48|0);}}break;case 10:if(48>_7Y){var _8b=new T(function(){return B(A1(_7U,__Z));});return function(_8c){return C > 19 ? new F(function(){return A1(_8c,_8b);}) : (++C,A1(_8c,_8b));};}else{if(_7Y>57){var _8d=new T(function(){return B(A1(_7U,__Z));});return function(_8e){return C > 19 ? new F(function(){return A1(_8e,_8d);}) : (++C,A1(_8e,_8d));};}else{return _7Z(_7Y-48|0);}}break;case 16:if(48>_7Y){if(97>_7Y){if(65>_7Y){var _8f=new T(function(){return B(A1(_7U,__Z));});return function(_8g){return C > 19 ? new F(function(){return A1(_8g,_8f);}) : (++C,A1(_8g,_8f));};}else{if(_7Y>70){var _8h=new T(function(){return B(A1(_7U,__Z));});return function(_8i){return C > 19 ? new F(function(){return A1(_8i,_8h);}) : (++C,A1(_8i,_8h));};}else{return _7Z((_7Y-65|0)+10|0);}}}else{if(_7Y>102){if(65>_7Y){var _8j=new T(function(){return B(A1(_7U,__Z));});return function(_8k){return C > 19 ? new F(function(){return A1(_8k,_8j);}) : (++C,A1(_8k,_8j));};}else{if(_7Y>70){var _8l=new T(function(){return B(A1(_7U,__Z));});return function(_8m){return C > 19 ? new F(function(){return A1(_8m,_8l);}) : (++C,A1(_8m,_8l));};}else{return _7Z((_7Y-65|0)+10|0);}}}else{return _7Z((_7Y-97|0)+10|0);}}}else{if(_7Y>57){if(97>_7Y){if(65>_7Y){var _8n=new T(function(){return B(A1(_7U,__Z));});return function(_8o){return C > 19 ? new F(function(){return A1(_8o,_8n);}) : (++C,A1(_8o,_8n));};}else{if(_7Y>70){var _8p=new T(function(){return B(A1(_7U,__Z));});return function(_8q){return C > 19 ? new F(function(){return A1(_8q,_8p);}) : (++C,A1(_8q,_8p));};}else{return _7Z((_7Y-65|0)+10|0);}}}else{if(_7Y>102){if(65>_7Y){var _8r=new T(function(){return B(A1(_7U,__Z));});return function(_8s){return C > 19 ? new F(function(){return A1(_8s,_8r);}) : (++C,A1(_8s,_8r));};}else{if(_7Y>70){var _8t=new T(function(){return B(A1(_7U,__Z));});return function(_8u){return C > 19 ? new F(function(){return A1(_8u,_8t);}) : (++C,A1(_8u,_8t));};}else{return _7Z((_7Y-65|0)+10|0);}}}else{return _7Z((_7Y-97|0)+10|0);}}}else{return _7Z(_7Y-48|0);}}break;default:return E(_7O);}}},_8v=function(_8w){var _8x=E(_8w);if(!_8x._){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_7R,_8x);}) : (++C,A1(_7R,_8x));}};return function(_8y){return C > 19 ? new F(function(){return A3(_7S,_8y,_1V,_8v);}) : (++C,A3(_7S,_8y,_1V,_8v));};},_8z=function(_8A){var _8B=function(_8C){return C > 19 ? new F(function(){return A1(_8A,new T1(5,new T2(0,8,_8C)));}) : (++C,A1(_8A,new T1(5,new T2(0,8,_8C))));},_8D=function(_8E){return C > 19 ? new F(function(){return A1(_8A,new T1(5,new T2(0,16,_8E)));}) : (++C,A1(_8A,new T1(5,new T2(0,16,_8E))));},_8F=function(_8G){switch(E(_8G)){case 79:return new T1(1,_7P(8,_8B));case 88:return new T1(1,_7P(16,_8D));case 111:return new T1(1,_7P(8,_8B));case 120:return new T1(1,_7P(16,_8D));default:return new T0(2);}};return function(_8H){return (E(_8H)==48)?E(new T1(0,_8F)):new T0(2);};},_8I=function(_8J){return new T1(0,_8z(_8J));},_8K=function(_8L){return C > 19 ? new F(function(){return A1(_8L,__Z);}) : (++C,A1(_8L,__Z));},_8M=function(_8N){return C > 19 ? new F(function(){return A1(_8N,__Z);}) : (++C,A1(_8N,__Z));},_8O=new T1(0,1),_8P=function(_8Q,_8R){while(1){var _8S=E(_8Q);if(!_8S._){var _8T=_8S.a,_8U=E(_8R);if(!_8U._){var _8V=_8U.a,_8W=addC(_8T,_8V);if(!E(_8W.b)){return new T1(0,_8W.a);}else{_8Q=new T1(1,I_fromInt(_8T));_8R=new T1(1,I_fromInt(_8V));continue;}}else{_8Q=new T1(1,I_fromInt(_8T));_8R=_8U;continue;}}else{var _8X=E(_8R);if(!_8X._){_8Q=_8S;_8R=new T1(1,I_fromInt(_8X.a));continue;}else{return new T1(1,I_add(_8S.a,_8X.a));}}}},_8Y=new T(function(){return _8P(new T1(0,2147483647),_8O);}),_8Z=function(_90){var _91=E(_90);if(!_91._){var _92=E(_91.a);return (_92==(-2147483648))?E(_8Y):new T1(0, -_92);}else{return new T1(1,I_negate(_91.a));}},_93=new T1(0,10),_94=function(_95,_96){while(1){var _97=E(_95);if(!_97._){return E(_96);}else{var _98=_96+1|0;_95=_97.b;_96=_98;continue;}}},_99=function(_9a,_9b){var _9c=E(_9b);return (_9c._==0)?__Z:new T2(1,new T(function(){return B(A1(_9a,_9c.a));}),new T(function(){return _99(_9a,_9c.b);}));},_9d=function(_9e){return _3d(E(_9e));},_9f=new T(function(){return err(new T(function(){return unCStr("this should not happen");}));}),_9g=function(_9h,_9i){while(1){var _9j=E(_9h);if(!_9j._){var _9k=_9j.a,_9l=E(_9i);if(!_9l._){var _9m=_9l.a;if(!(imul(_9k,_9m)|0)){return new T1(0,imul(_9k,_9m)|0);}else{_9h=new T1(1,I_fromInt(_9k));_9i=new T1(1,I_fromInt(_9m));continue;}}else{_9h=new T1(1,I_fromInt(_9k));_9i=_9l;continue;}}else{var _9n=E(_9i);if(!_9n._){_9h=_9j;_9i=new T1(1,I_fromInt(_9n.a));continue;}else{return new T1(1,I_mul(_9j.a,_9n.a));}}}},_9o=function(_9p,_9q){var _9r=E(_9q);if(!_9r._){return __Z;}else{var _9s=E(_9r.b);return (_9s._==0)?E(_9f):new T2(1,_8P(_9g(_9r.a,_9p),_9s.a),new T(function(){return _9o(_9p,_9s.b);}));}},_9t=new T1(0,0),_9u=function(_9v,_9w,_9x){while(1){var _9y=(function(_9z,_9A,_9B){var _9C=E(_9B);if(!_9C._){return E(_9t);}else{if(!E(_9C.b)._){return E(_9C.a);}else{var _9D=E(_9A);if(_9D<=40){var _9E=function(_9F,_9G){while(1){var _9H=E(_9G);if(!_9H._){return E(_9F);}else{var _9I=_8P(_9g(_9F,_9z),_9H.a);_9F=_9I;_9G=_9H.b;continue;}}};return _9E(_9t,_9C);}else{var _9J=_9g(_9z,_9z);if(!(_9D%2)){var _9K=_9o(_9z,_9C);_9v=_9J;_9w=quot(_9D+1|0,2);_9x=_9K;return __continue;}else{var _9K=_9o(_9z,new T2(1,_9t,_9C));_9v=_9J;_9w=quot(_9D+1|0,2);_9x=_9K;return __continue;}}}}})(_9v,_9w,_9x);if(_9y!=__continue){return _9y;}}},_9L=function(_9M,_9N){return _9u(_9M,new T(function(){return _94(_9N,0);},1),_99(_9d,_9N));},_9O=function(_9P){var _9Q=new T(function(){var _9R=new T(function(){var _9S=function(_9T){return C > 19 ? new F(function(){return A1(_9P,new T1(1,new T(function(){return _9L(_93,_9T);})));}) : (++C,A1(_9P,new T1(1,new T(function(){return _9L(_93,_9T);}))));};return new T1(1,_7P(10,_9S));}),_9U=function(_9V){if(E(_9V)==43){var _9W=function(_9X){return C > 19 ? new F(function(){return A1(_9P,new T1(1,new T(function(){return _9L(_93,_9X);})));}) : (++C,A1(_9P,new T1(1,new T(function(){return _9L(_93,_9X);}))));};return new T1(1,_7P(10,_9W));}else{return new T0(2);}},_9Y=function(_9Z){if(E(_9Z)==45){var _a0=function(_a1){return C > 19 ? new F(function(){return A1(_9P,new T1(1,new T(function(){return _8Z(_9L(_93,_a1));})));}) : (++C,A1(_9P,new T1(1,new T(function(){return _8Z(_9L(_93,_a1));}))));};return new T1(1,_7P(10,_a0));}else{return new T0(2);}};return _62(_62(new T1(0,_9Y),new T1(0,_9U)),_9R);});return _62(new T1(0,function(_a2){return (E(_a2)==101)?E(_9Q):new T0(2);}),new T1(0,function(_a3){return (E(_a3)==69)?E(_9Q):new T0(2);}));},_a4=function(_a5){var _a6=function(_a7){return C > 19 ? new F(function(){return A1(_a5,new T1(1,_a7));}) : (++C,A1(_a5,new T1(1,_a7)));};return function(_a8){return (E(_a8)==46)?new T1(1,_7P(10,_a6)):new T0(2);};},_a9=function(_aa){return new T1(0,_a4(_aa));},_ab=function(_ac){var _ad=function(_ae){var _af=function(_ag){return new T1(1,_7a(_9O,_8K,function(_ah){return C > 19 ? new F(function(){return A1(_ac,new T1(5,new T3(1,_ae,_ag,_ah)));}) : (++C,A1(_ac,new T1(5,new T3(1,_ae,_ag,_ah))));}));};return new T1(1,_7a(_a9,_8M,_af));};return _7P(10,_ad);},_ai=function(_aj){return new T1(1,_ab(_aj));},_ak=function(_al){return E(E(_al).a);},_am=function(_an,_ao,_ap){while(1){var _aq=E(_ap);if(!_aq._){return false;}else{if(!B(A3(_ak,_an,_ao,_aq.a))){_ap=_aq.b;continue;}else{return true;}}}},_ar=new T(function(){return unCStr("!@#$%&*+./<=>?\\^|:-~");}),_as=function(_at){return _am(_6D,_at,_ar);},_au=function(_av){var _aw=new T(function(){return B(A1(_av,8));}),_ax=new T(function(){return B(A1(_av,16));});return function(_ay){switch(E(_ay)){case 79:return E(_aw);case 88:return E(_ax);case 111:return E(_aw);case 120:return E(_ax);default:return new T0(2);}};},_az=function(_aA){return new T1(0,_au(_aA));},_aB=function(_aC){return C > 19 ? new F(function(){return A1(_aC,10);}) : (++C,A1(_aC,10));},_aD=function(_aE,_aF){var _aG=jsShowI(_aE);return _x(fromJSStr(_aG),_aF);},_aH=function(_aI,_aJ,_aK){if(_aJ>=0){return _aD(_aJ,_aK);}else{if(_aI<=6){return _aD(_aJ,_aK);}else{return new T2(1,40,new T(function(){var _aL=jsShowI(_aJ);return _x(fromJSStr(_aL),new T2(1,41,_aK));}));}}},_aM=function(_aN){return err(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return _aH(9,_aN,__Z);})));},_aO=function(_aP){var _aQ=E(_aP);if(!_aQ._){return E(_aQ.a);}else{return I_toInt(_aQ.a);}},_aR=function(_aS,_aT){var _aU=E(_aS);if(!_aU._){var _aV=_aU.a,_aW=E(_aT);return (_aW._==0)?_aV<=_aW.a:I_compareInt(_aW.a,_aV)>=0;}else{var _aX=_aU.a,_aY=E(_aT);return (_aY._==0)?I_compareInt(_aX,_aY.a)<=0:I_compare(_aX,_aY.a)<=0;}},_aZ=function(_b0){return new T0(2);},_b1=function(_b2){var _b3=E(_b2);if(!_b3._){return _aZ;}else{var _b4=_b3.a,_b5=E(_b3.b);if(!_b5._){return E(_b4);}else{var _b6=new T(function(){return _b1(_b5);}),_b7=function(_b8){return _62(B(A1(_b4,_b8)),new T(function(){return B(A1(_b6,_b8));}));};return _b7;}}},_b9=function(_ba,_bb){var _bc=function(_bd,_be,_bf){var _bg=E(_bd);if(!_bg._){return C > 19 ? new F(function(){return A1(_bf,_ba);}) : (++C,A1(_bf,_ba));}else{var _bh=E(_be);if(!_bh._){return new T0(2);}else{if(E(_bg.a)!=E(_bh.a)){return new T0(2);}else{var _bi=new T(function(){return B(_bc(_bg.b,_bh.b,_bf));});return new T1(0,function(_bj){return E(_bi);});}}}};return function(_bk){return C > 19 ? new F(function(){return _bc(_ba,_bk,_bb);}) : (++C,_bc(_ba,_bk,_bb));};},_bl=new T(function(){return unCStr("SO");}),_bm=function(_bn){var _bo=new T(function(){return B(A1(_bn,14));});return new T1(1,_b9(_bl,function(_bp){return E(_bo);}));},_bq=new T(function(){return unCStr("SOH");}),_br=function(_bs){var _bt=new T(function(){return B(A1(_bs,1));});return new T1(1,_b9(_bq,function(_bu){return E(_bt);}));},_bv=new T(function(){return unCStr("NUL");}),_bw=function(_bx){var _by=new T(function(){return B(A1(_bx,0));});return new T1(1,_b9(_bv,function(_bz){return E(_by);}));},_bA=new T(function(){return unCStr("STX");}),_bB=function(_bC){var _bD=new T(function(){return B(A1(_bC,2));});return new T1(1,_b9(_bA,function(_bE){return E(_bD);}));},_bF=new T(function(){return unCStr("ETX");}),_bG=function(_bH){var _bI=new T(function(){return B(A1(_bH,3));});return new T1(1,_b9(_bF,function(_bJ){return E(_bI);}));},_bK=new T(function(){return unCStr("EOT");}),_bL=function(_bM){var _bN=new T(function(){return B(A1(_bM,4));});return new T1(1,_b9(_bK,function(_bO){return E(_bN);}));},_bP=new T(function(){return unCStr("ENQ");}),_bQ=function(_bR){var _bS=new T(function(){return B(A1(_bR,5));});return new T1(1,_b9(_bP,function(_bT){return E(_bS);}));},_bU=new T(function(){return unCStr("ACK");}),_bV=function(_bW){var _bX=new T(function(){return B(A1(_bW,6));});return new T1(1,_b9(_bU,function(_bY){return E(_bX);}));},_bZ=new T(function(){return unCStr("BEL");}),_c0=function(_c1){var _c2=new T(function(){return B(A1(_c1,7));});return new T1(1,_b9(_bZ,function(_c3){return E(_c2);}));},_c4=new T(function(){return unCStr("BS");}),_c5=function(_c6){var _c7=new T(function(){return B(A1(_c6,8));});return new T1(1,_b9(_c4,function(_c8){return E(_c7);}));},_c9=new T(function(){return unCStr("HT");}),_ca=function(_cb){var _cc=new T(function(){return B(A1(_cb,9));});return new T1(1,_b9(_c9,function(_cd){return E(_cc);}));},_ce=new T(function(){return unCStr("LF");}),_cf=function(_cg){var _ch=new T(function(){return B(A1(_cg,10));});return new T1(1,_b9(_ce,function(_ci){return E(_ch);}));},_cj=new T(function(){return unCStr("VT");}),_ck=function(_cl){var _cm=new T(function(){return B(A1(_cl,11));});return new T1(1,_b9(_cj,function(_cn){return E(_cm);}));},_co=new T(function(){return unCStr("FF");}),_cp=function(_cq){var _cr=new T(function(){return B(A1(_cq,12));});return new T1(1,_b9(_co,function(_cs){return E(_cr);}));},_ct=new T(function(){return unCStr("CR");}),_cu=function(_cv){var _cw=new T(function(){return B(A1(_cv,13));});return new T1(1,_b9(_ct,function(_cx){return E(_cw);}));},_cy=new T(function(){return unCStr("SI");}),_cz=function(_cA){var _cB=new T(function(){return B(A1(_cA,15));});return new T1(1,_b9(_cy,function(_cC){return E(_cB);}));},_cD=new T(function(){return unCStr("DLE");}),_cE=function(_cF){var _cG=new T(function(){return B(A1(_cF,16));});return new T1(1,_b9(_cD,function(_cH){return E(_cG);}));},_cI=new T(function(){return unCStr("DC1");}),_cJ=function(_cK){var _cL=new T(function(){return B(A1(_cK,17));});return new T1(1,_b9(_cI,function(_cM){return E(_cL);}));},_cN=new T(function(){return unCStr("DC2");}),_cO=function(_cP){var _cQ=new T(function(){return B(A1(_cP,18));});return new T1(1,_b9(_cN,function(_cR){return E(_cQ);}));},_cS=new T(function(){return unCStr("DC3");}),_cT=function(_cU){var _cV=new T(function(){return B(A1(_cU,19));});return new T1(1,_b9(_cS,function(_cW){return E(_cV);}));},_cX=new T(function(){return unCStr("DC4");}),_cY=function(_cZ){var _d0=new T(function(){return B(A1(_cZ,20));});return new T1(1,_b9(_cX,function(_d1){return E(_d0);}));},_d2=new T(function(){return unCStr("NAK");}),_d3=function(_d4){var _d5=new T(function(){return B(A1(_d4,21));});return new T1(1,_b9(_d2,function(_d6){return E(_d5);}));},_d7=new T(function(){return unCStr("SYN");}),_d8=function(_d9){var _da=new T(function(){return B(A1(_d9,22));});return new T1(1,_b9(_d7,function(_db){return E(_da);}));},_dc=new T(function(){return unCStr("ETB");}),_dd=function(_de){var _df=new T(function(){return B(A1(_de,23));});return new T1(1,_b9(_dc,function(_dg){return E(_df);}));},_dh=new T(function(){return unCStr("CAN");}),_di=function(_dj){var _dk=new T(function(){return B(A1(_dj,24));});return new T1(1,_b9(_dh,function(_dl){return E(_dk);}));},_dm=new T(function(){return unCStr("EM");}),_dn=function(_do){var _dp=new T(function(){return B(A1(_do,25));});return new T1(1,_b9(_dm,function(_dq){return E(_dp);}));},_dr=new T(function(){return unCStr("SUB");}),_ds=function(_dt){var _du=new T(function(){return B(A1(_dt,26));});return new T1(1,_b9(_dr,function(_dv){return E(_du);}));},_dw=new T(function(){return unCStr("ESC");}),_dx=function(_dy){var _dz=new T(function(){return B(A1(_dy,27));});return new T1(1,_b9(_dw,function(_dA){return E(_dz);}));},_dB=new T(function(){return unCStr("FS");}),_dC=function(_dD){var _dE=new T(function(){return B(A1(_dD,28));});return new T1(1,_b9(_dB,function(_dF){return E(_dE);}));},_dG=new T(function(){return unCStr("GS");}),_dH=function(_dI){var _dJ=new T(function(){return B(A1(_dI,29));});return new T1(1,_b9(_dG,function(_dK){return E(_dJ);}));},_dL=new T(function(){return unCStr("RS");}),_dM=function(_dN){var _dO=new T(function(){return B(A1(_dN,30));});return new T1(1,_b9(_dL,function(_dP){return E(_dO);}));},_dQ=new T(function(){return unCStr("US");}),_dR=function(_dS){var _dT=new T(function(){return B(A1(_dS,31));});return new T1(1,_b9(_dQ,function(_dU){return E(_dT);}));},_dV=new T(function(){return unCStr("SP");}),_dW=function(_dX){var _dY=new T(function(){return B(A1(_dX,32));});return new T1(1,_b9(_dV,function(_dZ){return E(_dY);}));},_e0=new T(function(){return unCStr("DEL");}),_e1=function(_e2){var _e3=new T(function(){return B(A1(_e2,127));});return new T1(1,_b9(_e0,function(_e4){return E(_e3);}));},_e5=new T(function(){return _b1(new T2(1,function(_e6){return new T1(1,_7a(_br,_bm,_e6));},new T2(1,_bw,new T2(1,_bB,new T2(1,_bG,new T2(1,_bL,new T2(1,_bQ,new T2(1,_bV,new T2(1,_c0,new T2(1,_c5,new T2(1,_ca,new T2(1,_cf,new T2(1,_ck,new T2(1,_cp,new T2(1,_cu,new T2(1,_cz,new T2(1,_cE,new T2(1,_cJ,new T2(1,_cO,new T2(1,_cT,new T2(1,_cY,new T2(1,_d3,new T2(1,_d8,new T2(1,_dd,new T2(1,_di,new T2(1,_dn,new T2(1,_ds,new T2(1,_dx,new T2(1,_dC,new T2(1,_dH,new T2(1,_dM,new T2(1,_dR,new T2(1,_dW,new T2(1,_e1,__Z))))))))))))))))))))))))))))))))));}),_e7=function(_e8){var _e9=new T(function(){return B(A1(_e8,7));}),_ea=new T(function(){return B(A1(_e8,8));}),_eb=new T(function(){return B(A1(_e8,9));}),_ec=new T(function(){return B(A1(_e8,10));}),_ed=new T(function(){return B(A1(_e8,11));}),_ee=new T(function(){return B(A1(_e8,12));}),_ef=new T(function(){return B(A1(_e8,13));}),_eg=new T(function(){return B(A1(_e8,92));}),_eh=new T(function(){return B(A1(_e8,39));}),_ei=new T(function(){return B(A1(_e8,34));}),_ej=new T(function(){var _ek=function(_el){var _em=new T(function(){return _3d(E(_el));}),_en=function(_eo){var _ep=_9L(_em,_eo);if(!_aR(_ep,new T1(0,1114111))){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_e8,new T(function(){var _eq=_aO(_ep);if(_eq>>>0>1114111){return _aM(_eq);}else{return _eq;}}));}) : (++C,A1(_e8,new T(function(){var _eq=_aO(_ep);if(_eq>>>0>1114111){return _aM(_eq);}else{return _eq;}})));}};return new T1(1,_7P(_el,_en));},_er=new T(function(){var _es=new T(function(){return B(A1(_e8,31));}),_et=new T(function(){return B(A1(_e8,30));}),_eu=new T(function(){return B(A1(_e8,29));}),_ev=new T(function(){return B(A1(_e8,28));}),_ew=new T(function(){return B(A1(_e8,27));}),_ex=new T(function(){return B(A1(_e8,26));}),_ey=new T(function(){return B(A1(_e8,25));}),_ez=new T(function(){return B(A1(_e8,24));}),_eA=new T(function(){return B(A1(_e8,23));}),_eB=new T(function(){return B(A1(_e8,22));}),_eC=new T(function(){return B(A1(_e8,21));}),_eD=new T(function(){return B(A1(_e8,20));}),_eE=new T(function(){return B(A1(_e8,19));}),_eF=new T(function(){return B(A1(_e8,18));}),_eG=new T(function(){return B(A1(_e8,17));}),_eH=new T(function(){return B(A1(_e8,16));}),_eI=new T(function(){return B(A1(_e8,15));}),_eJ=new T(function(){return B(A1(_e8,14));}),_eK=new T(function(){return B(A1(_e8,6));}),_eL=new T(function(){return B(A1(_e8,5));}),_eM=new T(function(){return B(A1(_e8,4));}),_eN=new T(function(){return B(A1(_e8,3));}),_eO=new T(function(){return B(A1(_e8,2));}),_eP=new T(function(){return B(A1(_e8,1));}),_eQ=new T(function(){return B(A1(_e8,0));}),_eR=function(_eS){switch(E(_eS)){case 64:return E(_eQ);case 65:return E(_eP);case 66:return E(_eO);case 67:return E(_eN);case 68:return E(_eM);case 69:return E(_eL);case 70:return E(_eK);case 71:return E(_e9);case 72:return E(_ea);case 73:return E(_eb);case 74:return E(_ec);case 75:return E(_ed);case 76:return E(_ee);case 77:return E(_ef);case 78:return E(_eJ);case 79:return E(_eI);case 80:return E(_eH);case 81:return E(_eG);case 82:return E(_eF);case 83:return E(_eE);case 84:return E(_eD);case 85:return E(_eC);case 86:return E(_eB);case 87:return E(_eA);case 88:return E(_ez);case 89:return E(_ey);case 90:return E(_ex);case 91:return E(_ew);case 92:return E(_ev);case 93:return E(_eu);case 94:return E(_et);case 95:return E(_es);default:return new T0(2);}};return _62(new T1(0,function(_eT){return (E(_eT)==94)?E(new T1(0,_eR)):new T0(2);}),new T(function(){return B(A1(_e5,_e8));}));});return _62(new T1(1,_7a(_az,_aB,_ek)),_er);});return _62(new T1(0,function(_eU){switch(E(_eU)){case 34:return E(_ei);case 39:return E(_eh);case 92:return E(_eg);case 97:return E(_e9);case 98:return E(_ea);case 102:return E(_ee);case 110:return E(_ec);case 114:return E(_ef);case 116:return E(_eb);case 118:return E(_ed);default:return new T0(2);}}),_ej);},_eV=function(_eW){return C > 19 ? new F(function(){return A1(_eW,0);}) : (++C,A1(_eW,0));},_eX=function(_eY){var _eZ=E(_eY);if(!_eZ._){return _eV;}else{var _f0=E(_eZ.a),_f1=_f0>>>0,_f2=new T(function(){return _eX(_eZ.b);});if(_f1>887){var _f3=u_iswspace(_f0);if(!E(_f3)){return _eV;}else{var _f4=function(_f5){var _f6=new T(function(){return B(A1(_f2,_f5));});return new T1(0,function(_f7){return E(_f6);});};return _f4;}}else{if(_f1==32){var _f8=function(_f9){var _fa=new T(function(){return B(A1(_f2,_f9));});return new T1(0,function(_fb){return E(_fa);});};return _f8;}else{if(_f1-9>>>0>4){if(_f1==160){var _fc=function(_fd){var _fe=new T(function(){return B(A1(_f2,_fd));});return new T1(0,function(_ff){return E(_fe);});};return _fc;}else{return _eV;}}else{var _fg=function(_fh){var _fi=new T(function(){return B(A1(_f2,_fh));});return new T1(0,function(_fj){return E(_fi);});};return _fg;}}}}},_fk=function(_fl){var _fm=new T(function(){return B(_fk(_fl));}),_fn=function(_fo){return (E(_fo)==92)?E(_fm):new T0(2);},_fp=function(_fq){return E(new T1(0,_fn));},_fr=new T1(1,function(_fs){return C > 19 ? new F(function(){return A2(_eX,_fs,_fp);}) : (++C,A2(_eX,_fs,_fp));}),_ft=new T(function(){return B(_e7(function(_fu){return C > 19 ? new F(function(){return A1(_fl,new T2(0,_fu,true));}) : (++C,A1(_fl,new T2(0,_fu,true)));}));}),_fv=function(_fw){var _fx=E(_fw);if(_fx==38){return E(_fm);}else{var _fy=_fx>>>0;if(_fy>887){var _fz=u_iswspace(_fx);return (E(_fz)==0)?new T0(2):E(_fr);}else{return (_fy==32)?E(_fr):(_fy-9>>>0>4)?(_fy==160)?E(_fr):new T0(2):E(_fr);}}};return _62(new T1(0,function(_fA){return (E(_fA)==92)?E(new T1(0,_fv)):new T0(2);}),new T1(0,function(_fB){var _fC=E(_fB);if(_fC==92){return E(_ft);}else{return C > 19 ? new F(function(){return A1(_fl,new T2(0,_fC,false));}) : (++C,A1(_fl,new T2(0,_fC,false)));}}));},_fD=function(_fE,_fF){var _fG=new T(function(){return B(A1(_fF,new T1(1,new T(function(){return B(A1(_fE,__Z));}))));}),_fH=function(_fI){var _fJ=E(_fI),_fK=E(_fJ.a);if(_fK==34){if(!E(_fJ.b)){return E(_fG);}else{return C > 19 ? new F(function(){return _fD(function(_fL){return C > 19 ? new F(function(){return A1(_fE,new T2(1,_fK,_fL));}) : (++C,A1(_fE,new T2(1,_fK,_fL)));},_fF);}) : (++C,_fD(function(_fL){return C > 19 ? new F(function(){return A1(_fE,new T2(1,_fK,_fL));}) : (++C,A1(_fE,new T2(1,_fK,_fL)));},_fF));}}else{return C > 19 ? new F(function(){return _fD(function(_fM){return C > 19 ? new F(function(){return A1(_fE,new T2(1,_fK,_fM));}) : (++C,A1(_fE,new T2(1,_fK,_fM)));},_fF);}) : (++C,_fD(function(_fM){return C > 19 ? new F(function(){return A1(_fE,new T2(1,_fK,_fM));}) : (++C,A1(_fE,new T2(1,_fK,_fM)));},_fF));}};return C > 19 ? new F(function(){return _fk(_fH);}) : (++C,_fk(_fH));},_fN=new T(function(){return unCStr("_\'");}),_fO=function(_fP){var _fQ=u_iswalnum(_fP);if(!E(_fQ)){return _am(_6D,_fP,_fN);}else{return true;}},_fR=function(_fS){return _fO(E(_fS));},_fT=new T(function(){return unCStr(",;()[]{}`");}),_fU=new T(function(){return unCStr("=>");}),_fV=new T(function(){return unCStr("~");}),_fW=new T(function(){return unCStr("@");}),_fX=new T(function(){return unCStr("->");}),_fY=new T(function(){return unCStr("<-");}),_fZ=new T(function(){return unCStr("|");}),_g0=new T(function(){return unCStr("\\");}),_g1=new T(function(){return unCStr("=");}),_g2=new T(function(){return unCStr("::");}),_g3=new T(function(){return unCStr("..");}),_g4=function(_g5){var _g6=new T(function(){return B(A1(_g5,new T0(6)));}),_g7=new T(function(){var _g8=new T(function(){var _g9=function(_ga){var _gb=new T(function(){return B(A1(_g5,new T1(0,_ga)));});return new T1(0,function(_gc){return (E(_gc)==39)?E(_gb):new T0(2);});};return B(_e7(_g9));}),_gd=function(_ge){var _gf=E(_ge);switch(_gf){case 39:return new T0(2);case 92:return E(_g8);default:var _gg=new T(function(){return B(A1(_g5,new T1(0,_gf)));});return new T1(0,function(_gh){return (E(_gh)==39)?E(_gg):new T0(2);});}},_gi=new T(function(){var _gj=new T(function(){return B(_fD(_1V,_g5));}),_gk=new T(function(){var _gl=new T(function(){var _gm=new T(function(){var _gn=function(_go){var _gp=E(_go),_gq=u_iswalpha(_gp);return (E(_gq)==0)?(_gp==95)?new T1(1,_7A(_fR,function(_gr){return C > 19 ? new F(function(){return A1(_g5,new T1(3,new T2(1,_gp,_gr)));}) : (++C,A1(_g5,new T1(3,new T2(1,_gp,_gr))));})):new T0(2):new T1(1,_7A(_fR,function(_gs){return C > 19 ? new F(function(){return A1(_g5,new T1(3,new T2(1,_gp,_gs)));}) : (++C,A1(_g5,new T1(3,new T2(1,_gp,_gs))));}));};return _62(new T1(0,_gn),new T(function(){return new T1(1,_7a(_8I,_ai,_g5));}));}),_gt=function(_gu){return (!_am(_6D,_gu,_ar))?new T0(2):new T1(1,_7A(_as,function(_gv){var _gw=new T2(1,_gu,_gv);if(!_am(new T2(0,_6I,_6N),_gw,new T2(1,_g3,new T2(1,_g2,new T2(1,_g1,new T2(1,_g0,new T2(1,_fZ,new T2(1,_fY,new T2(1,_fX,new T2(1,_fW,new T2(1,_fV,new T2(1,_fU,__Z)))))))))))){return C > 19 ? new F(function(){return A1(_g5,new T1(4,_gw));}) : (++C,A1(_g5,new T1(4,_gw)));}else{return C > 19 ? new F(function(){return A1(_g5,new T1(2,_gw));}) : (++C,A1(_g5,new T1(2,_gw)));}}));};return _62(new T1(0,_gt),_gm);});return _62(new T1(0,function(_gx){if(!_am(_6D,_gx,_fT)){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_g5,new T1(2,new T2(1,_gx,__Z)));}) : (++C,A1(_g5,new T1(2,new T2(1,_gx,__Z))));}}),_gl);});return _62(new T1(0,function(_gy){return (E(_gy)==34)?E(_gj):new T0(2);}),_gk);});return _62(new T1(0,function(_gz){return (E(_gz)==39)?E(new T1(0,_gd)):new T0(2);}),_gi);});return _62(new T1(1,function(_gA){return (E(_gA)._==0)?E(_g6):new T0(2);}),_g7);},_gB=function(_gC,_gD){var _gE=new T(function(){var _gF=new T(function(){var _gG=function(_gH){var _gI=new T(function(){var _gJ=new T(function(){return B(A1(_gD,_gH));});return B(_g4(function(_gK){var _gL=E(_gK);return (_gL._==2)?(!_6y(_gL.a,_6x))?new T0(2):E(_gJ):new T0(2);}));}),_gM=function(_gN){return E(_gI);};return new T1(1,function(_gO){return C > 19 ? new F(function(){return A2(_eX,_gO,_gM);}) : (++C,A2(_eX,_gO,_gM));});};return B(A2(_gC,0,_gG));});return B(_g4(function(_gP){var _gQ=E(_gP);return (_gQ._==2)?(!_6y(_gQ.a,_6w))?new T0(2):E(_gF):new T0(2);}));}),_gR=function(_gS){return E(_gE);};return function(_gT){return C > 19 ? new F(function(){return A2(_eX,_gT,_gR);}) : (++C,A2(_eX,_gT,_gR));};},_gU=function(_gV,_gW){var _gX=function(_gY){var _gZ=new T(function(){return B(A1(_gV,_gY));}),_h0=function(_h1){return _62(B(A1(_gZ,_h1)),new T(function(){return new T1(1,_gB(_gX,_h1));}));};return _h0;},_h2=new T(function(){return B(A1(_gV,_gW));}),_h3=function(_h4){return _62(B(A1(_h2,_h4)),new T(function(){return new T1(1,_gB(_gX,_h4));}));};return _h3;},_h5=function(_h6,_h7){var _h8=function(_h9,_ha){var _hb=function(_hc){return C > 19 ? new F(function(){return A1(_ha,new T(function(){return  -E(_hc);}));}) : (++C,A1(_ha,new T(function(){return  -E(_hc);})));},_hd=new T(function(){return B(_g4(function(_he){return C > 19 ? new F(function(){return A3(_h6,_he,_h9,_hb);}) : (++C,A3(_h6,_he,_h9,_hb));}));}),_hf=function(_hg){return E(_hd);},_hh=function(_hi){return C > 19 ? new F(function(){return A2(_eX,_hi,_hf);}) : (++C,A2(_eX,_hi,_hf));},_hj=new T(function(){return B(_g4(function(_hk){var _hl=E(_hk);if(_hl._==4){var _hm=E(_hl.a);if(!_hm._){return C > 19 ? new F(function(){return A3(_h6,_hl,_h9,_ha);}) : (++C,A3(_h6,_hl,_h9,_ha));}else{if(E(_hm.a)==45){if(!E(_hm.b)._){return E(new T1(1,_hh));}else{return C > 19 ? new F(function(){return A3(_h6,_hl,_h9,_ha);}) : (++C,A3(_h6,_hl,_h9,_ha));}}else{return C > 19 ? new F(function(){return A3(_h6,_hl,_h9,_ha);}) : (++C,A3(_h6,_hl,_h9,_ha));}}}else{return C > 19 ? new F(function(){return A3(_h6,_hl,_h9,_ha);}) : (++C,A3(_h6,_hl,_h9,_ha));}}));}),_hn=function(_ho){return E(_hj);};return new T1(1,function(_hp){return C > 19 ? new F(function(){return A2(_eX,_hp,_hn);}) : (++C,A2(_eX,_hp,_hn));});};return _gU(_h8,_h7);},_hq=new T(function(){return 1/0;}),_hr=function(_hs,_ht){return C > 19 ? new F(function(){return A1(_ht,_hq);}) : (++C,A1(_ht,_hq));},_hu=new T(function(){return 0/0;}),_hv=function(_hw,_hx){return C > 19 ? new F(function(){return A1(_hx,_hu);}) : (++C,A1(_hx,_hu));},_hy=new T(function(){return unCStr("NaN");}),_hz=new T(function(){return unCStr("Infinity");}),_hA=new T(function(){return unCStr("base");}),_hB=new T(function(){return unCStr("GHC.Exception");}),_hC=new T(function(){return unCStr("ArithException");}),_hD=function(_hE){return E(new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_hA,_hB,_hC),__Z,__Z));},_hF=new T(function(){return unCStr("Ratio has zero denominator");}),_hG=new T(function(){return unCStr("denormal");}),_hH=new T(function(){return unCStr("divide by zero");}),_hI=new T(function(){return unCStr("loss of precision");}),_hJ=new T(function(){return unCStr("arithmetic underflow");}),_hK=new T(function(){return unCStr("arithmetic overflow");}),_hL=function(_hM,_hN){switch(E(_hM)){case 0:return _x(_hK,_hN);case 1:return _x(_hJ,_hN);case 2:return _x(_hI,_hN);case 3:return _x(_hH,_hN);case 4:return _x(_hG,_hN);default:return _x(_hF,_hN);}},_hO=function(_hP){return _hL(_hP,__Z);},_hQ=new T(function(){return new T5(0,_hD,new T3(0,function(_hR,_hS,_hT){return _hL(_hS,_hT);},_hO,function(_hU,_hV){return _1q(_hL,_hU,_hV);}),_hW,function(_hX){var _hY=E(_hX);return _m(_k(_hY.a),_hD,_hY.b);},_hO);}),_hW=function(_4e){return new T2(0,_hQ,_4e);},_hZ=new T(function(){return die(new T(function(){return _hW(3);}));}),_i0=function(_i1,_i2){var _i3=E(_i1);if(!_i3._){var _i4=_i3.a,_i5=E(_i2);return (_i5._==0)?_i4==_i5.a:(I_compareInt(_i5.a,_i4)==0)?true:false;}else{var _i6=_i3.a,_i7=E(_i2);return (_i7._==0)?(I_compareInt(_i6,_i7.a)==0)?true:false:(I_compare(_i6,_i7.a)==0)?true:false;}},_i8=new T1(0,0),_i9=function(_ia,_ib){while(1){var _ic=E(_ia);if(!_ic._){var _id=E(_ic.a);if(_id==(-2147483648)){_ia=new T1(1,I_fromInt(-2147483648));continue;}else{var _ie=E(_ib);if(!_ie._){return new T1(0,_id%_ie.a);}else{_ia=new T1(1,I_fromInt(_id));_ib=_ie;continue;}}}else{var _if=_ic.a,_ig=E(_ib);return (_ig._==0)?new T1(1,I_rem(_if,I_fromInt(_ig.a))):new T1(1,I_rem(_if,_ig.a));}}},_ih=function(_ii,_ij){if(!_i0(_ij,_i8)){return _i9(_ii,_ij);}else{return E(_hZ);}},_ik=function(_il,_im){while(1){if(!_i0(_im,_i8)){var _in=_im,_io=_ih(_il,_im);_il=_in;_im=_io;continue;}else{return E(_il);}}},_ip=function(_iq){var _ir=E(_iq);if(!_ir._){var _is=E(_ir.a);return (_is==(-2147483648))?E(_8Y):(_is<0)?new T1(0, -_is):_ir;}else{var _it=_ir.a;return (I_compareInt(_it,0)>=0)?_ir:new T1(1,I_negate(_it));}},_iu=function(_iv,_iw){while(1){var _ix=E(_iv);if(!_ix._){var _iy=E(_ix.a);if(_iy==(-2147483648)){_iv=new T1(1,I_fromInt(-2147483648));continue;}else{var _iz=E(_iw);if(!_iz._){return new T1(0,quot(_iy,_iz.a));}else{_iv=new T1(1,I_fromInt(_iy));_iw=_iz;continue;}}}else{var _iA=_ix.a,_iB=E(_iw);return (_iB._==0)?new T1(0,I_toInt(I_quot(_iA,I_fromInt(_iB.a)))):new T1(1,I_quot(_iA,_iB.a));}}},_iC=new T(function(){return die(new T(function(){return _hW(5);}));}),_iD=function(_iE,_iF){if(!_i0(_iF,_i8)){var _iG=_ik(_ip(_iE),_ip(_iF));return (!_i0(_iG,_i8))?new T2(0,_iu(_iE,_iG),_iu(_iF,_iG)):E(_hZ);}else{return E(_iC);}},_iH=new T1(0,1),_iI=new T(function(){return err(new T(function(){return unCStr("Negative exponent");}));}),_iJ=new T1(0,2),_iK=new T(function(){return _i0(_iJ,_i8);}),_iL=function(_iM,_iN){while(1){var _iO=E(_iM);if(!_iO._){var _iP=_iO.a,_iQ=E(_iN);if(!_iQ._){var _iR=_iQ.a,_iS=subC(_iP,_iR);if(!E(_iS.b)){return new T1(0,_iS.a);}else{_iM=new T1(1,I_fromInt(_iP));_iN=new T1(1,I_fromInt(_iR));continue;}}else{_iM=new T1(1,I_fromInt(_iP));_iN=_iQ;continue;}}else{var _iT=E(_iN);if(!_iT._){_iM=_iO;_iN=new T1(1,I_fromInt(_iT.a));continue;}else{return new T1(1,I_sub(_iO.a,_iT.a));}}}},_iU=function(_iV,_iW,_iX){while(1){if(!E(_iK)){if(!_i0(_i9(_iW,_iJ),_i8)){if(!_i0(_iW,_iH)){var _iY=_9g(_iV,_iV),_iZ=_iu(_iL(_iW,_iH),_iJ),_j0=_9g(_iV,_iX);_iV=_iY;_iW=_iZ;_iX=_j0;continue;}else{return _9g(_iV,_iX);}}else{var _iY=_9g(_iV,_iV),_iZ=_iu(_iW,_iJ);_iV=_iY;_iW=_iZ;continue;}}else{return E(_hZ);}}},_j1=function(_j2,_j3){while(1){if(!E(_iK)){if(!_i0(_i9(_j3,_iJ),_i8)){if(!_i0(_j3,_iH)){return _iU(_9g(_j2,_j2),_iu(_iL(_j3,_iH),_iJ),_j2);}else{return E(_j2);}}else{var _j4=_9g(_j2,_j2),_j5=_iu(_j3,_iJ);_j2=_j4;_j3=_j5;continue;}}else{return E(_hZ);}}},_j6=function(_j7,_j8){var _j9=E(_j7);if(!_j9._){var _ja=_j9.a,_jb=E(_j8);return (_jb._==0)?_ja<_jb.a:I_compareInt(_jb.a,_ja)>0;}else{var _jc=_j9.a,_jd=E(_j8);return (_jd._==0)?I_compareInt(_jc,_jd.a)<0:I_compare(_jc,_jd.a)<0;}},_je=function(_jf,_jg){if(!_j6(_jg,_i8)){if(!_i0(_jg,_i8)){return _j1(_jf,_jg);}else{return E(_iH);}}else{return E(_iI);}},_jh=new T1(0,1),_ji=new T1(0,0),_jj=new T1(0,-1),_jk=function(_jl){var _jm=E(_jl);if(!_jm._){var _jn=_jm.a;return (_jn>=0)?(E(_jn)==0)?E(_ji):E(_8O):E(_jj);}else{var _jo=I_compareInt(_jm.a,0);return (_jo<=0)?(E(_jo)==0)?E(_ji):E(_jj):E(_8O);}},_jp=function(_jq,_jr,_js){while(1){var _jt=E(_js);if(!_jt._){if(!_j6(_jq,_9t)){return new T2(0,_9g(_jr,B(_je(_93,_jq))),_iH);}else{var _ju=B(_je(_93,_8Z(_jq)));return _iD(_9g(_jr,_jk(_ju)),_ip(_ju));}}else{var _jv=_iL(_jq,_jh),_jw=_8P(_9g(_jr,_93),_3d(E(_jt.a)));_jq=_jv;_jr=_jw;_js=_jt.b;continue;}}},_jx=function(_jy,_jz){var _jA=E(_jy);if(!_jA._){var _jB=_jA.a,_jC=E(_jz);return (_jC._==0)?_jB>=_jC.a:I_compareInt(_jC.a,_jB)<=0;}else{var _jD=_jA.a,_jE=E(_jz);return (_jE._==0)?I_compareInt(_jD,_jE.a)>=0:I_compare(_jD,_jE.a)>=0;}},_jF=function(_jG){var _jH=E(_jG);if(!_jH._){var _jI=_jH.b;return _iD(_9g(_9u(new T(function(){return _3d(E(_jH.a));}),new T(function(){return _94(_jI,0);},1),_99(_9d,_jI)),_jh),_jh);}else{var _jJ=_jH.a,_jK=_jH.c,_jL=E(_jH.b);if(!_jL._){var _jM=E(_jK);if(!_jM._){return _iD(_9g(_9L(_93,_jJ),_jh),_jh);}else{var _jN=_jM.a;if(!_jx(_jN,_9t)){var _jO=B(_je(_93,_8Z(_jN)));return _iD(_9g(_9L(_93,_jJ),_jk(_jO)),_ip(_jO));}else{return _iD(_9g(_9g(_9L(_93,_jJ),B(_je(_93,_jN))),_jh),_jh);}}}else{var _jP=_jL.a,_jQ=E(_jK);if(!_jQ._){return _jp(_9t,_9L(_93,_jJ),_jP);}else{return _jp(_jQ.a,_9L(_93,_jJ),_jP);}}}},_jR=function(_jS,_jT){while(1){var _jU=E(_jT);if(!_jU._){return __Z;}else{if(!B(A1(_jS,_jU.a))){return _jU;}else{_jT=_jU.b;continue;}}}},_jV=function(_jW,_jX){var _jY=E(_jW);if(!_jY._){var _jZ=_jY.a,_k0=E(_jX);return (_k0._==0)?_jZ>_k0.a:I_compareInt(_k0.a,_jZ)<0;}else{var _k1=_jY.a,_k2=E(_jX);return (_k2._==0)?I_compareInt(_k1,_k2.a)>0:I_compare(_k1,_k2.a)>0;}},_k3=function(_k4,_k5){return E(_k4)==E(_k5);},_k6=function(_k7){return _k3(0,_k7);},_k8=new T1(1,new T2(0,E(_9t),E(_iH))),_k9=function(_ka,_kb,_kc){var _kd=E(_kc);if(!_kd._){return new T1(1,new T(function(){var _ke=_jF(_kd);return new T2(0,E(_ke.a),E(_ke.b));}));}else{var _kf=E(_kd.c);if(!_kf._){return new T1(1,new T(function(){var _kg=_jF(_kd);return new T2(0,E(_kg.a),E(_kg.b));}));}else{var _kh=_kf.a;if(!_jV(_kh,new T1(0,2147483647))){if(!_j6(_kh,new T1(0,-2147483648))){var _ki=function(_kj){var _kk=_kj+_aO(_kh)|0;return (_kk<=(E(_kb)+3|0))?(_kk>=(E(_ka)-3|0))?new T1(1,new T(function(){var _kl=_jF(_kd);return new T2(0,E(_kl.a),E(_kl.b));})):E(_k8):__Z;},_km=_jR(_k6,_kd.a);if(!_km._){var _kn=E(_kd.b);if(!_kn._){return E(_k8);}else{var _ko=_4f(_k6,_kn.a);if(!E(_ko.b)._){return E(_k8);}else{return _ki( -_94(_ko.a,0));}}}else{return _ki(_94(_km,0));}}else{return __Z;}}else{return __Z;}}}},_kp=function(_kq,_kr){return new T0(2);},_ks=new T1(0,1),_kt=function(_ku,_kv){var _kw=E(_ku);if(!_kw._){var _kx=_kw.a,_ky=E(_kv);if(!_ky._){var _kz=_ky.a;return (_kx!=_kz)?(_kx>_kz)?2:0:1;}else{var _kA=I_compareInt(_ky.a,_kx);return (_kA<=0)?(_kA>=0)?1:2:0;}}else{var _kB=_kw.a,_kC=E(_kv);if(!_kC._){var _kD=I_compareInt(_kB,_kC.a);return (_kD>=0)?(_kD<=0)?1:2:0;}else{var _kE=I_compare(_kB,_kC.a);return (_kE>=0)?(_kE<=0)?1:2:0;}}},_kF=function(_kG,_kH){var _kI=E(_kG);return (_kI._==0)?_kI.a*Math.pow(2,_kH):I_toNumber(_kI.a)*Math.pow(2,_kH);},_kJ=function(_kK,_kL){while(1){var _kM=E(_kK);if(!_kM._){var _kN=E(_kM.a);if(_kN==(-2147483648)){_kK=new T1(1,I_fromInt(-2147483648));continue;}else{var _kO=E(_kL);if(!_kO._){var _kP=_kO.a;return new T2(0,new T1(0,quot(_kN,_kP)),new T1(0,_kN%_kP));}else{_kK=new T1(1,I_fromInt(_kN));_kL=_kO;continue;}}}else{var _kQ=E(_kL);if(!_kQ._){_kK=_kM;_kL=new T1(1,I_fromInt(_kQ.a));continue;}else{var _kR=I_quotRem(_kM.a,_kQ.a);return new T2(0,new T1(1,_kR.a),new T1(1,_kR.b));}}}},_kS=new T1(0,0),_kT=function(_kU,_kV,_kW){if(!_i0(_kW,_kS)){var _kX=_kJ(_kV,_kW),_kY=_kX.a;switch(_kt(_3s(_kX.b,1),_kW)){case 0:return _kF(_kY,_kU);case 1:if(!(_aO(_kY)&1)){return _kF(_kY,_kU);}else{return _kF(_8P(_kY,_ks),_kU);}break;default:return _kF(_8P(_kY,_ks),_kU);}}else{return E(_hZ);}},_kZ=function(_l0){var _l1=function(_l2,_l3){while(1){if(!_j6(_l2,_l0)){if(!_jV(_l2,_l0)){if(!_i0(_l2,_l0)){return C > 19 ? new F(function(){return _4A("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2");}) : (++C,_4A("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2"));}else{return E(_l3);}}else{return _l3-1|0;}}else{var _l4=_3s(_l2,1),_l5=_l3+1|0;_l2=_l4;_l3=_l5;continue;}}};return C > 19 ? new F(function(){return _l1(_8O,0);}) : (++C,_l1(_8O,0));},_l6=function(_l7){var _l8=E(_l7);if(!_l8._){var _l9=_l8.a>>>0;if(!_l9){return -1;}else{var _la=function(_lb,_lc){while(1){if(_lb>=_l9){if(_lb<=_l9){if(_lb!=_l9){return C > 19 ? new F(function(){return _4A("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");}) : (++C,_4A("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2"));}else{return E(_lc);}}else{return _lc-1|0;}}else{var _ld=imul(_lb,2)>>>0,_le=_lc+1|0;_lb=_ld;_lc=_le;continue;}}};return C > 19 ? new F(function(){return _la(1,0);}) : (++C,_la(1,0));}}else{return C > 19 ? new F(function(){return _kZ(_l8);}) : (++C,_kZ(_l8));}},_lf=function(_lg){var _lh=E(_lg);if(!_lh._){var _li=_lh.a>>>0;if(!_li){return new T2(0,-1,0);}else{var _lj=function(_lk,_ll){while(1){if(_lk>=_li){if(_lk<=_li){if(_lk!=_li){return C > 19 ? new F(function(){return _4A("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");}) : (++C,_4A("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2"));}else{return E(_ll);}}else{return _ll-1|0;}}else{var _lm=imul(_lk,2)>>>0,_ln=_ll+1|0;_lk=_lm;_ll=_ln;continue;}}};return new T2(0,B(_lj(1,0)),(_li&_li-1>>>0)>>>0&4294967295);}}else{var _lo=_lh.a;return new T2(0,B(_l6(_lh)),I_compareInt(I_and(_lo,I_sub(_lo,I_fromInt(1))),0));}},_lp=function(_lq,_lr){while(1){var _ls=E(_lq);if(!_ls._){var _lt=_ls.a,_lu=E(_lr);if(!_lu._){return new T1(0,(_lt>>>0&_lu.a>>>0)>>>0&4294967295);}else{_lq=new T1(1,I_fromInt(_lt));_lr=_lu;continue;}}else{var _lv=E(_lr);if(!_lv._){_lq=_ls;_lr=new T1(1,I_fromInt(_lv.a));continue;}else{return new T1(1,I_and(_ls.a,_lv.a));}}}},_lw=function(_lx,_ly){var _lz=E(_lx);if(!_lz._){var _lA=(_lz.a>>>0&(2<<_ly>>>0)-1>>>0)>>>0,_lB=1<<_ly>>>0;return (_lB<=_lA)?(_lB>=_lA)?1:2:0;}else{var _lC=_lp(_lz,_iL(_3s(new T1(0,2),_ly),_8O)),_lD=_3s(_8O,_ly);return (!_jV(_lD,_lC))?(!_j6(_lD,_lC))?1:2:0;}},_lE=function(_lF,_lG){while(1){var _lH=E(_lF);if(!_lH._){_lF=new T1(1,I_fromInt(_lH.a));continue;}else{return new T1(1,I_shiftRight(_lH.a,_lG));}}},_lI=function(_lJ,_lK,_lL,_lM){var _lN=_lf(_lM),_lO=_lN.a;if(!E(_lN.b)){var _lP=B(_l6(_lL));if(_lP<((_lO+_lJ|0)-1|0)){var _lQ=_lO+(_lJ-_lK|0)|0;if(_lQ>0){if(_lQ>_lP){if(_lQ<=(_lP+1|0)){if(!E(_lf(_lL).b)){return 0;}else{return _kF(_ks,_lJ-_lK|0);}}else{return 0;}}else{var _lR=_lE(_lL,_lQ);switch(_lw(_lL,_lQ-1|0)){case 0:return _kF(_lR,_lJ-_lK|0);case 1:if(!(_aO(_lR)&1)){return _kF(_lR,_lJ-_lK|0);}else{return _kF(_8P(_lR,_ks),_lJ-_lK|0);}break;default:return _kF(_8P(_lR,_ks),_lJ-_lK|0);}}}else{return _kF(_lL,(_lJ-_lK|0)-_lQ|0);}}else{if(_lP>=_lK){var _lS=_lE(_lL,(_lP+1|0)-_lK|0);switch(_lw(_lL,_lP-_lK|0)){case 0:return _kF(_lS,((_lP-_lO|0)+1|0)-_lK|0);case 2:return _kF(_8P(_lS,_ks),((_lP-_lO|0)+1|0)-_lK|0);default:if(!(_aO(_lS)&1)){return _kF(_lS,((_lP-_lO|0)+1|0)-_lK|0);}else{return _kF(_8P(_lS,_ks),((_lP-_lO|0)+1|0)-_lK|0);}}}else{return _kF(_lL, -_lO);}}}else{var _lT=B(_l6(_lL))-_lO|0,_lU=function(_lV){var _lW=function(_lX,_lY){if(!_aR(_3s(_lY,_lK),_lX)){return _kT(_lV-_lK|0,_lX,_lY);}else{return _kT((_lV-_lK|0)+1|0,_lX,_3s(_lY,1));}};if(_lV>=_lK){if(_lV!=_lK){return _lW(_lL,new T(function(){return _3s(_lM,_lV-_lK|0);}));}else{return _lW(_lL,_lM);}}else{return _lW(new T(function(){return _3s(_lL,_lK-_lV|0);}),_lM);}};if(_lJ>_lT){return C > 19 ? new F(function(){return _lU(_lJ);}) : (++C,_lU(_lJ));}else{return C > 19 ? new F(function(){return _lU(_lT);}) : (++C,_lU(_lT));}}},_lZ=new T(function(){return 0/0;}),_m0=new T(function(){return -1/0;}),_m1=new T(function(){return 1/0;}),_m2=function(_m3,_m4){if(!_i0(_m4,_kS)){if(!_i0(_m3,_kS)){if(!_j6(_m3,_kS)){return C > 19 ? new F(function(){return _lI(-1021,53,_m3,_m4);}) : (++C,_lI(-1021,53,_m3,_m4));}else{return  -B(_lI(-1021,53,_8Z(_m3),_m4));}}else{return 0;}}else{return (!_i0(_m3,_kS))?(!_j6(_m3,_kS))?E(_m1):E(_m0):E(_lZ);}},_m5=function(_m6){var _m7=E(_m6);switch(_m7._){case 3:var _m8=_m7.a;return (!_6y(_m8,_hz))?(!_6y(_m8,_hy))?_kp:_hv:_hr;case 5:var _m9=_k9(-1021,1024,_m7.a);if(!_m9._){return _hr;}else{var _ma=new T(function(){var _mb=E(_m9.a);return B(_m2(_mb.a,_mb.b));});return function(_mc,_md){return C > 19 ? new F(function(){return A1(_md,_ma);}) : (++C,A1(_md,_ma));};}break;default:return _kp;}},_me=function(_mf){var _mg=function(_mh){return E(new T2(3,_mf,_71));};return new T1(1,function(_mi){return C > 19 ? new F(function(){return A2(_eX,_mi,_mg);}) : (++C,A2(_eX,_mi,_mg));});},_mj=new T(function(){return B(A3(_h5,_m5,0,_me));}),_mk=function(_ml,_mm){while(1){var _mn=E(_ml);if(!_mn._){return E(_mm);}else{_ml=_mn.b;_mm=_mn.a;continue;}}},_mo=function(_mp){var _mq=E(_mp);if(!_mq._){return __Z;}else{var _mr=_mq.a,_ms=new T(function(){if(E(_mk(_mr,_5H))==37){var _mt=_5I(_5P(_mj,new T(function(){return _5E(_mr);})));if(!_mt._){return E(_60);}else{if(!E(_mt.b)._){return E(_mt.a)/100;}else{return E(_5Z);}}}else{var _mu=_5I(_5P(_mj,_mr));if(!_mu._){return E(_60);}else{if(!E(_mu.b)._){return E(_mu.a);}else{return E(_5Z);}}}});return new T1(1,_ms);}},_mv=function(_mw,_){var _mx=E(_mw);if(!_mx._){return E(_4C);}else{var _my=_mx.a,_mz=E(_mx.b);if(!_mz._){return E(_4C);}else{var _mA=_mz.a,_mB=E(_mz.b);if(!_mB._){return E(_4C);}else{var _mC=_mB.a,_mD=E(_mB.b);if(!_mD._){return E(_4C);}else{if(!E(_mD.b)._){var _mE=function(_){var _mF=_3N(E(_my),"value"),_mG=_3N(E(_mA),"value"),_mH=_3N(E(_mC),"value"),_mI=_mo(new T1(1,new T(function(){var _mJ=String(_mF);return fromJSStr(_mJ);})));if(!_mI._){return 0;}else{var _mK=_mo(new T1(1,new T(function(){var _mL=String(_mG);return fromJSStr(_mL);})));if(!_mK._){return 0;}else{var _mM=_mo(new T1(1,new T(function(){var _mN=String(_mH);return fromJSStr(_mN);})));if(!_mM._){return 0;}else{var _mO=_3O(E(_mD.a),toJSStr(E(_4E)),toJSStr(_3w(2,E(_mI.a)*Math.pow(1+E(_mM.a),E(_mK.a)))));return _2s(_);}}}},_mP=B(A(_53,[_2v,_2t,_2o,_my,1,function(_mQ,_){return _mE(_);},_])),_mR=B(A(_53,[_2v,_2t,_2o,_mA,1,function(_mS,_){return _mE(_);},_]));return C > 19 ? new F(function(){return A(_53,[_2v,_2t,new T2(0,_2d,_2a),_mC,2,function(_mT,_){return _mE(_);},_]);}) : (++C,A(_53,[_2v,_2t,new T2(0,_2d,_2a),_mC,2,function(_mT,_){return _mE(_);},_]));}else{return E(_4C);}}}}}},_mU=(function(id){return document.getElementById(id);}),_mV=new T(function(){return err(new T(function(){return unCStr("Maybe.fromJust: Nothing");}));}),_mW=function(_mX){var _mY=E(_mX);return (_mY._==0)?E(_mV):E(_mY.a);},_mZ=function(_n0,_n1){while(1){var _n2=(function(_n3,_n4){var _n5=E(_n3);if(!_n5._){return __Z;}else{var _n6=_n5.b,_n7=E(_n4);if(!_n7._){return __Z;}else{var _n8=_n7.b;if(!E(_n7.a)._){return new T2(1,_n5.a,new T(function(){return _mZ(_n6,_n8);}));}else{_n0=_n6;_n1=_n8;return __continue;}}}})(_n0,_n1);if(_n2!=__continue){return _n2;}}},_n9=new T(function(){return unAppCStr("[]",__Z);}),_na=function(_nb){var _nc=E(_nb);if(!_nc._){return E(new T2(1,93,__Z));}else{var _nd=new T(function(){return _x(fromJSStr(E(_nc.a)),new T(function(){return _na(_nc.b);},1));});return new T2(1,44,_nd);}},_ne=function(_nf,_ng){var _nh=new T(function(){var _ni=_mZ(_nf,_ng);if(!_ni._){return E(_n9);}else{var _nj=new T(function(){return _x(fromJSStr(E(_ni.a)),new T(function(){return _na(_ni.b);},1));});return new T2(1,91,_nj);}});return err(unAppCStr("Elements with the following IDs could not be found: ",_nh));},_nk=function(_nl){while(1){var _nm=E(_nl);if(!_nm._){return false;}else{if(!E(_nm.a)._){return true;}else{_nl=_nm.b;continue;}}}},_nn=function(_no,_np,_nq){var _nr=_4H(_no),_ns=function(_nt){if(!_nk(_nt)){return C > 19 ? new F(function(){return A1(_nq,new T(function(){return _99(_mW,_nt);}));}) : (++C,A1(_nq,new T(function(){return _99(_mW,_nt);})));}else{return _ne(_np,_nt);}},_nu=new T(function(){var _nv=new T(function(){return B(A2(_51,_nr,__Z));}),_nw=function(_nx){var _ny=E(_nx);if(!_ny._){return E(_nv);}else{var _nz=new T(function(){return B(_nw(_ny.b));}),_nA=function(_nB){return C > 19 ? new F(function(){return A3(_4J,_nr,_nz,function(_nC){return C > 19 ? new F(function(){return A2(_51,_nr,new T2(1,_nB,_nC));}) : (++C,A2(_51,_nr,new T2(1,_nB,_nC)));});}) : (++C,A3(_4J,_nr,_nz,function(_nC){return C > 19 ? new F(function(){return A2(_51,_nr,new T2(1,_nB,_nC));}) : (++C,A2(_51,_nr,new T2(1,_nB,_nC)));}));},_nD=new T(function(){return B(A2(_4X,_no,function(_){var _nE=_mU(E(_ny.a)),_nF=__eq(_nE,E(_4W));return (E(_nF)==0)?new T1(1,_nE):__Z;}));});return C > 19 ? new F(function(){return A3(_4J,_nr,_nD,_nA);}) : (++C,A3(_4J,_nr,_nD,_nA));}};return B(_nw(_np));});return C > 19 ? new F(function(){return A3(_4J,_nr,_nu,_ns);}) : (++C,A3(_4J,_nr,_nu,_ns));},_nG=new T(function(){return B(_nn(_1X,new T(function(){return _99(function(_nH){return toJSStr(E(_nH));},new T2(1,new T(function(){return unCStr("pv");}),new T2(1,new T(function(){return unCStr("ty");}),new T2(1,new T(function(){return unCStr("r");}),new T2(1,new T(function(){return unCStr("result");}),__Z)))));}),_mv));});
var hasteMain = function() {B(A(_nG, [0]));};window.onload = hasteMain;