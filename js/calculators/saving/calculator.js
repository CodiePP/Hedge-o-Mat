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

var _0=function(_1,_2,_){var _3=B(A1(_1,_)),_4=B(A1(_2,_));return _3;},_5=function(_6,_7,_){var _8=B(A1(_6,_)),_9=B(A1(_7,_));return new T(function(){return B(A1(_8,_9));});},_a=function(_b,_c,_){var _d=B(A1(_c,_));return _b;},_e=function(_f,_g,_){var _h=B(A1(_g,_));return new T(function(){return B(A1(_f,_h));});},_i=new T2(0,_e,_a),_j=function(_k,_){return _k;},_l=function(_m,_n,_){var _o=B(A1(_m,_));return new F(function(){return A1(_n,_);});},_p=new T5(0,_i,_j,_5,_l,_0),_q=new T(function(){return B(unCStr("base"));}),_r=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_s=new T(function(){return B(unCStr("IOException"));}),_t=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_q,_r,_s),_u=__Z,_v=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_t,_u,_u),_w=function(_x){return E(_v);},_y=function(_z){return E(E(_z).a);},_A=function(_B,_C,_D){var _E=B(A1(_B,_)),_F=B(A1(_C,_)),_G=hs_eqWord64(_E.a,_F.a);if(!_G){return __Z;}else{var _H=hs_eqWord64(_E.b,_F.b);return (!_H)?__Z:new T1(1,_D);}},_I=function(_J){var _K=E(_J);return new F(function(){return _A(B(_y(_K.a)),_w,_K.b);});},_L=new T(function(){return B(unCStr(": "));}),_M=new T(function(){return B(unCStr(")"));}),_N=new T(function(){return B(unCStr(" ("));}),_O=function(_P,_Q){var _R=E(_P);return (_R._==0)?E(_Q):new T2(1,_R.a,new T(function(){return B(_O(_R.b,_Q));}));},_S=new T(function(){return B(unCStr("interrupted"));}),_T=new T(function(){return B(unCStr("system error"));}),_U=new T(function(){return B(unCStr("unsatisified constraints"));}),_V=new T(function(){return B(unCStr("user error"));}),_W=new T(function(){return B(unCStr("permission denied"));}),_X=new T(function(){return B(unCStr("illegal operation"));}),_Y=new T(function(){return B(unCStr("end of file"));}),_Z=new T(function(){return B(unCStr("resource exhausted"));}),_10=new T(function(){return B(unCStr("resource busy"));}),_11=new T(function(){return B(unCStr("does not exist"));}),_12=new T(function(){return B(unCStr("already exists"));}),_13=new T(function(){return B(unCStr("resource vanished"));}),_14=new T(function(){return B(unCStr("timeout"));}),_15=new T(function(){return B(unCStr("unsupported operation"));}),_16=new T(function(){return B(unCStr("hardware fault"));}),_17=new T(function(){return B(unCStr("inappropriate type"));}),_18=new T(function(){return B(unCStr("invalid argument"));}),_19=new T(function(){return B(unCStr("failed"));}),_1a=new T(function(){return B(unCStr("protocol error"));}),_1b=function(_1c,_1d){switch(E(_1c)){case 0:return new F(function(){return _O(_12,_1d);});break;case 1:return new F(function(){return _O(_11,_1d);});break;case 2:return new F(function(){return _O(_10,_1d);});break;case 3:return new F(function(){return _O(_Z,_1d);});break;case 4:return new F(function(){return _O(_Y,_1d);});break;case 5:return new F(function(){return _O(_X,_1d);});break;case 6:return new F(function(){return _O(_W,_1d);});break;case 7:return new F(function(){return _O(_V,_1d);});break;case 8:return new F(function(){return _O(_U,_1d);});break;case 9:return new F(function(){return _O(_T,_1d);});break;case 10:return new F(function(){return _O(_1a,_1d);});break;case 11:return new F(function(){return _O(_19,_1d);});break;case 12:return new F(function(){return _O(_18,_1d);});break;case 13:return new F(function(){return _O(_17,_1d);});break;case 14:return new F(function(){return _O(_16,_1d);});break;case 15:return new F(function(){return _O(_15,_1d);});break;case 16:return new F(function(){return _O(_14,_1d);});break;case 17:return new F(function(){return _O(_13,_1d);});break;default:return new F(function(){return _O(_S,_1d);});}},_1e=new T(function(){return B(unCStr("}"));}),_1f=new T(function(){return B(unCStr("{handle: "));}),_1g=function(_1h,_1i,_1j,_1k,_1l,_1m){var _1n=new T(function(){var _1o=new T(function(){var _1p=new T(function(){var _1q=E(_1k);if(!_1q._){return E(_1m);}else{var _1r=new T(function(){return B(_O(_1q,new T(function(){return B(_O(_M,_1m));},1)));},1);return B(_O(_N,_1r));}},1);return B(_1b(_1i,_1p));}),_1s=E(_1j);if(!_1s._){return E(_1o);}else{return B(_O(_1s,new T(function(){return B(_O(_L,_1o));},1)));}}),_1t=E(_1l);if(!_1t._){var _1u=E(_1h);if(!_1u._){return E(_1n);}else{var _1v=E(_1u.a);if(!_1v._){var _1w=new T(function(){var _1x=new T(function(){return B(_O(_1e,new T(function(){return B(_O(_L,_1n));},1)));},1);return B(_O(_1v.a,_1x));},1);return new F(function(){return _O(_1f,_1w);});}else{var _1y=new T(function(){var _1z=new T(function(){return B(_O(_1e,new T(function(){return B(_O(_L,_1n));},1)));},1);return B(_O(_1v.a,_1z));},1);return new F(function(){return _O(_1f,_1y);});}}}else{return new F(function(){return _O(_1t.a,new T(function(){return B(_O(_L,_1n));},1));});}},_1A=function(_1B){var _1C=E(_1B);return new F(function(){return _1g(_1C.a,_1C.b,_1C.c,_1C.d,_1C.f,_u);});},_1D=function(_1E){return new T2(0,_1F,_1E);},_1G=function(_1H,_1I,_1J){var _1K=E(_1I);return new F(function(){return _1g(_1K.a,_1K.b,_1K.c,_1K.d,_1K.f,_1J);});},_1L=function(_1M,_1N){var _1O=E(_1M);return new F(function(){return _1g(_1O.a,_1O.b,_1O.c,_1O.d,_1O.f,_1N);});},_1P=44,_1Q=93,_1R=91,_1S=function(_1T,_1U,_1V){var _1W=E(_1U);if(!_1W._){return new F(function(){return unAppCStr("[]",_1V);});}else{var _1X=new T(function(){var _1Y=new T(function(){var _1Z=function(_20){var _21=E(_20);if(!_21._){return E(new T2(1,_1Q,_1V));}else{var _22=new T(function(){return B(A2(_1T,_21.a,new T(function(){return B(_1Z(_21.b));})));});return new T2(1,_1P,_22);}};return B(_1Z(_1W.b));});return B(A2(_1T,_1W.a,_1Y));});return new T2(1,_1R,_1X);}},_23=function(_24,_25){return new F(function(){return _1S(_1L,_24,_25);});},_26=new T3(0,_1G,_1A,_23),_1F=new T(function(){return new T5(0,_w,_26,_1D,_I,_1A);}),_27=new T(function(){return E(_1F);}),_28=function(_29){return E(E(_29).c);},_2a=__Z,_2b=7,_2c=function(_2d){return new T6(0,_2a,_2b,_u,_2d,_2a,_2a);},_2e=function(_2f,_){var _2g=new T(function(){return B(A2(_28,_27,new T(function(){return B(A1(_2c,_2f));})));});return new F(function(){return die(_2g);});},_2h=function(_2i,_){return new F(function(){return _2e(_2i,_);});},_2j=function(_2k){return new F(function(){return A1(_2h,_2k);});},_2l=function(_2m,_2n,_){var _2o=B(A1(_2m,_));return new F(function(){return A2(_2n,_2o,_);});},_2p=new T5(0,_p,_2l,_l,_j,_2j),_2q=function(_2r){return E(_2r);},_2s=new T2(0,_2p,_2q),_2t=0,_2u=function(_){return _2t;},_2v=function(_2w,_2x,_){return new F(function(){return _2u(_);});},_2y="scroll",_2z="submit",_2A="blur",_2B="focus",_2C="change",_2D="unload",_2E="load",_2F=function(_2G){switch(E(_2G)){case 0:return E(_2E);case 1:return E(_2D);case 2:return E(_2C);case 3:return E(_2B);case 4:return E(_2A);case 5:return E(_2z);default:return E(_2y);}},_2H=new T2(0,_2F,_2v),_2I="metaKey",_2J="shiftKey",_2K="altKey",_2L="ctrlKey",_2M="keyCode",_2N=function(_2O,_){var _2P=__get(_2O,E(_2M)),_2Q=__get(_2O,E(_2L)),_2R=__get(_2O,E(_2K)),_2S=__get(_2O,E(_2J)),_2T=__get(_2O,E(_2I));return new T(function(){var _2U=Number(_2P),_2V=jsTrunc(_2U);return new T5(0,_2V,E(_2Q),E(_2R),E(_2S),E(_2T));});},_2W=function(_2X,_2Y,_){return new F(function(){return _2N(E(_2Y),_);});},_2Z="keydown",_30="keyup",_31="keypress",_32=function(_33){switch(E(_33)){case 0:return E(_31);case 1:return E(_30);default:return E(_2Z);}},_34=new T2(0,_32,_2W),_35=function(_){return _2t;},_36=function(_37,_){return new T1(1,_37);},_38=new T2(0,_2q,_36),_39=new T2(0,_2s,_j),_3a=function(_3b,_3c){while(1){var _3d=E(_3b);if(!_3d._){return E(_3c);}else{var _3e=new T2(1,_3d.a,_3c);_3b=_3d.b;_3c=_3e;continue;}}},_3f=function(_3g){return new F(function(){return _3a(_3g,_u);});},_3h=function(_3i,_3j,_3k){while(1){var _3l=B((function(_3m,_3n,_3o){var _3p=E(_3m);if(!_3p._){return new T2(0,new T(function(){return B(_3f(_3n));}),new T(function(){return B(_3f(_3o));}));}else{var _3q=_3n,_3r=new T2(1,_3p.a,_3o);_3i=_3p.b;_3j=_3q;_3k=_3r;return __continue;}})(_3i,_3j,_3k));if(_3l!=__continue){return _3l;}}},_3s=function(_3t,_3u,_3v){while(1){var _3w=B((function(_3x,_3y,_3z){var _3A=E(_3x);if(!_3A._){return new T2(0,new T(function(){return B(_3f(_3y));}),new T(function(){return B(_3f(_3z));}));}else{var _3B=_3A.b,_3C=E(_3A.a);if(E(_3C)==46){return new F(function(){return _3h(_3B,_3y,_u);});}else{var _3D=new T2(1,_3C,_3y),_3E=_3z;_3t=_3B;_3u=_3D;_3v=_3E;return __continue;}}})(_3t,_3u,_3v));if(_3w!=__continue){return _3w;}}},_3F=function(_3G,_3H){var _3I=E(_3H);if(!_3I._){return __Z;}else{var _3J=_3I.a,_3K=E(_3G);return (_3K==1)?new T2(1,_3J,_u):new T2(1,_3J,new T(function(){return B(_3F(_3K-1|0,_3I.b));}));}},_3L=function(_3M){var _3N=I_decodeDouble(_3M);return new T2(0,new T1(1,_3N.b),_3N.a);},_3O=function(_3P){var _3Q=E(_3P);if(!_3Q._){return _3Q.a;}else{return new F(function(){return I_toNumber(_3Q.a);});}},_3R=function(_3S){return new T1(0,_3S);},_3T=function(_3U){var _3V=hs_intToInt64(2147483647),_3W=hs_leInt64(_3U,_3V);if(!_3W){return new T1(1,I_fromInt64(_3U));}else{var _3X=hs_intToInt64(-2147483648),_3Y=hs_geInt64(_3U,_3X);if(!_3Y){return new T1(1,I_fromInt64(_3U));}else{var _3Z=hs_int64ToInt(_3U);return new F(function(){return _3R(_3Z);});}}},_40=function(_41){var _42=hs_intToInt64(_41);return E(_42);},_43=function(_44){var _45=E(_44);if(!_45._){return new F(function(){return _40(_45.a);});}else{return new F(function(){return I_toInt64(_45.a);});}},_46=function(_47,_48){while(1){var _49=E(_47);if(!_49._){_47=new T1(1,I_fromInt(_49.a));continue;}else{return new T1(1,I_shiftLeft(_49.a,_48));}}},_4a=function(_4b,_4c){var _4d=Math.pow(10,_4b),_4e=rintDouble(_4c*_4d),_4f=B(_3L(_4e)),_4g=_4f.a,_4h=_4f.b,_4i=function(_4j,_4k){var _4l=new T(function(){return B(unAppCStr(".",new T(function(){if(0>=_4b){return __Z;}else{return B(_3F(_4b,_4k));}})));},1);return new F(function(){return _O(_4j,_4l);});};if(_4h>=0){var _4m=jsShow(B(_3O(B(_46(_4g,_4h))))/_4d),_4n=B(_3s(fromJSStr(_4m),_u,_u));return new F(function(){return _4i(_4n.a,_4n.b);});}else{var _4o=hs_uncheckedIShiftRA64(B(_43(_4g)), -_4h),_4p=jsShow(B(_3O(B(_3T(_4o))))/_4d),_4q=B(_3s(fromJSStr(_4p),_u,_u));return new F(function(){return _4i(_4q.a,_4q.b);});}},_4r=2,_4s=1,_4t="value",_4u=new T(function(){return eval("(function(e,p){var x = e[p];return typeof x === \'undefined\' ? \'\' : x.toString();})");}),_4v=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_4w=new T(function(){return B(unCStr("base"));}),_4x=new T(function(){return B(unCStr("Control.Exception.Base"));}),_4y=new T(function(){return B(unCStr("PatternMatchFail"));}),_4z=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_4w,_4x,_4y),_4A=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_4z,_u,_u),_4B=function(_4C){return E(_4A);},_4D=function(_4E){var _4F=E(_4E);return new F(function(){return _A(B(_y(_4F.a)),_4B,_4F.b);});},_4G=function(_4H){return E(E(_4H).a);},_4I=function(_4J){return new T2(0,_4K,_4J);},_4L=function(_4M,_4N){return new F(function(){return _O(E(_4M).a,_4N);});},_4O=function(_4P,_4Q){return new F(function(){return _1S(_4L,_4P,_4Q);});},_4R=function(_4S,_4T,_4U){return new F(function(){return _O(E(_4T).a,_4U);});},_4V=new T3(0,_4R,_4G,_4O),_4K=new T(function(){return new T5(0,_4B,_4V,_4I,_4D,_4G);}),_4W=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_4X=function(_4Y,_4Z){return new F(function(){return die(new T(function(){return B(A2(_28,_4Z,_4Y));}));});},_50=function(_51,_52){return new F(function(){return _4X(_51,_52);});},_53=function(_54,_55){var _56=E(_55);if(!_56._){return new T2(0,_u,_u);}else{var _57=_56.a;if(!B(A1(_54,_57))){return new T2(0,_u,_56);}else{var _58=new T(function(){var _59=B(_53(_54,_56.b));return new T2(0,_59.a,_59.b);});return new T2(0,new T2(1,_57,new T(function(){return E(E(_58).a);})),new T(function(){return E(E(_58).b);}));}}},_5a=32,_5b=new T(function(){return B(unCStr("\n"));}),_5c=function(_5d){return (E(_5d)==124)?false:true;},_5e=function(_5f,_5g){var _5h=B(_53(_5c,B(unCStr(_5f)))),_5i=_5h.a,_5j=function(_5k,_5l){var _5m=new T(function(){var _5n=new T(function(){return B(_O(_5g,new T(function(){return B(_O(_5l,_5b));},1)));});return B(unAppCStr(": ",_5n));},1);return new F(function(){return _O(_5k,_5m);});},_5o=E(_5h.b);if(!_5o._){return new F(function(){return _5j(_5i,_u);});}else{if(E(_5o.a)==124){return new F(function(){return _5j(_5i,new T2(1,_5a,_5o.b));});}else{return new F(function(){return _5j(_5i,_u);});}}},_5p=function(_5q){return new F(function(){return _50(new T1(0,new T(function(){return B(_5e(_5q,_4W));})),_4K);});},_5r=function(_5s){return new F(function(){return _5p("calculator.hs:(10,1)-(24,42)|function calculator");});},_5t=new T(function(){return B(_5r(_));}),_5u=new T(function(){return B(unCStr("innerHTML"));}),_5v=function(_5w){return E(E(_5w).a);},_5x=function(_5y){return E(E(_5y).a);},_5z=function(_5A){return E(E(_5A).b);},_5B=function(_5C){return E(E(_5C).a);},_5D=function(_5E){return E(E(_5E).b);},_5F=function(_5G){return E(E(_5G).a);},_5H=function(_){return new F(function(){return nMV(_2a);});},_5I=function(_5J){var _5K=B(A1(_5J,_));return E(_5K);},_5L=new T(function(){return B(_5I(_5H));}),_5M=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_5N=function(_){return new F(function(){return __jsNull();});},_5O=new T(function(){return B(_5I(_5N));}),_5P=new T(function(){return E(_5O);}),_5Q=function(_5R){return E(E(_5R).b);},_5S=function(_5T){return E(E(_5T).b);},_5U=function(_5V){return E(E(_5V).d);},_5W=function(_5X,_5Y,_5Z,_60,_61,_62){var _63=B(_5v(_5X)),_64=B(_5x(_63)),_65=new T(function(){return B(_5Q(_63));}),_66=new T(function(){return B(_5U(_64));}),_67=new T(function(){return B(A2(_5B,_5Y,_60));}),_68=new T(function(){return B(A2(_5F,_5Z,_61));}),_69=function(_6a){return new F(function(){return A1(_66,new T3(0,_68,_67,_6a));});},_6b=function(_6c){var _6d=new T(function(){var _6e=new T(function(){var _6f=__createJSFunc(2,function(_6g,_){var _6h=B(A2(E(_6c),_6g,_));return _5P;}),_6i=_6f;return function(_){return new F(function(){return __app3(E(_5M),E(_67),E(_68),_6i);});};});return B(A1(_65,_6e));});return new F(function(){return A3(_5z,_64,_6d,_69);});},_6j=new T(function(){var _6k=new T(function(){return B(_5Q(_63));}),_6l=function(_6m){var _6n=new T(function(){return B(A1(_6k,function(_){var _=wMV(E(_5L),new T1(1,_6m));return new F(function(){return A(_5D,[_5Z,_61,_6m,_]);});}));});return new F(function(){return A3(_5z,_64,_6n,_62);});};return B(A2(_5S,_5X,_6l));});return new F(function(){return A3(_5z,_64,_6j,_6b);});},_6o=function(_6p,_6q){var _6r=E(_6q);return (_6r._==0)?__Z:new T2(1,_6p,new T(function(){return B(_6o(_6r.a,_6r.b));}));},_6s=new T(function(){return B(unCStr(": empty list"));}),_6t=new T(function(){return B(unCStr("Prelude."));}),_6u=function(_6v){return new F(function(){return err(B(_O(_6t,new T(function(){return B(_O(_6v,_6s));},1))));});},_6w=new T(function(){return B(unCStr("init"));}),_6x=new T(function(){return B(_6u(_6w));}),_6y=function(_6z){var _6A=E(_6z);if(!_6A._){return E(_6x);}else{return new F(function(){return _6o(_6A.a,_6A.b);});}},_6B=new T(function(){return B(unCStr("last"));}),_6C=new T(function(){return B(_6u(_6B));}),_6D=function(_6E){while(1){var _6F=B((function(_6G){var _6H=E(_6G);if(!_6H._){return __Z;}else{var _6I=_6H.b,_6J=E(_6H.a);if(!E(_6J.b)._){return new T2(1,_6J.a,new T(function(){return B(_6D(_6I));}));}else{_6E=_6I;return __continue;}}})(_6E));if(_6F!=__continue){return _6F;}}},_6K=function(_6L,_6M){while(1){var _6N=B((function(_6O,_6P){var _6Q=E(_6O);switch(_6Q._){case 0:var _6R=E(_6P);if(!_6R._){return __Z;}else{_6L=B(A1(_6Q.a,_6R.a));_6M=_6R.b;return __continue;}break;case 1:var _6S=B(A1(_6Q.a,_6P)),_6T=_6P;_6L=_6S;_6M=_6T;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_6Q.a,_6P),new T(function(){return B(_6K(_6Q.b,_6P));}));default:return E(_6Q.a);}})(_6L,_6M));if(_6N!=__continue){return _6N;}}},_6U=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_6V=new T(function(){return B(err(_6U));}),_6W=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_6X=new T(function(){return B(err(_6W));}),_6Y=new T(function(){return B(_5p("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_6Z=function(_70,_71){var _72=function(_73){var _74=E(_71);if(_74._==3){return new T2(3,_74.a,new T(function(){return B(_6Z(_70,_74.b));}));}else{var _75=E(_70);if(_75._==2){return E(_74);}else{var _76=E(_74);if(_76._==2){return E(_75);}else{var _77=function(_78){var _79=E(_76);if(_79._==4){var _7a=function(_7b){return new T1(4,new T(function(){return B(_O(B(_6K(_75,_7b)),_79.a));}));};return new T1(1,_7a);}else{var _7c=E(_75);if(_7c._==1){var _7d=_7c.a,_7e=E(_79);if(!_7e._){return new T1(1,function(_7f){return new F(function(){return _6Z(B(A1(_7d,_7f)),_7e);});});}else{var _7g=function(_7h){return new F(function(){return _6Z(B(A1(_7d,_7h)),new T(function(){return B(A1(_7e.a,_7h));}));});};return new T1(1,_7g);}}else{var _7i=E(_79);if(!_7i._){return E(_6Y);}else{var _7j=function(_7k){return new F(function(){return _6Z(_7c,new T(function(){return B(A1(_7i.a,_7k));}));});};return new T1(1,_7j);}}}},_7l=E(_75);switch(_7l._){case 1:var _7m=E(_76);if(_7m._==4){var _7n=function(_7o){return new T1(4,new T(function(){return B(_O(B(_6K(B(A1(_7l.a,_7o)),_7o)),_7m.a));}));};return new T1(1,_7n);}else{return new F(function(){return _77(_);});}break;case 4:var _7p=_7l.a,_7q=E(_76);switch(_7q._){case 0:var _7r=function(_7s){var _7t=new T(function(){return B(_O(_7p,new T(function(){return B(_6K(_7q,_7s));},1)));});return new T1(4,_7t);};return new T1(1,_7r);case 1:var _7u=function(_7v){var _7w=new T(function(){return B(_O(_7p,new T(function(){return B(_6K(B(A1(_7q.a,_7v)),_7v));},1)));});return new T1(4,_7w);};return new T1(1,_7u);default:return new T1(4,new T(function(){return B(_O(_7p,_7q.a));}));}break;default:return new F(function(){return _77(_);});}}}}},_7x=E(_70);switch(_7x._){case 0:var _7y=E(_71);if(!_7y._){var _7z=function(_7A){return new F(function(){return _6Z(B(A1(_7x.a,_7A)),new T(function(){return B(A1(_7y.a,_7A));}));});};return new T1(0,_7z);}else{return new F(function(){return _72(_);});}break;case 3:return new T2(3,_7x.a,new T(function(){return B(_6Z(_7x.b,_71));}));default:return new F(function(){return _72(_);});}},_7B=new T(function(){return B(unCStr("("));}),_7C=new T(function(){return B(unCStr(")"));}),_7D=function(_7E,_7F){while(1){var _7G=E(_7E);if(!_7G._){return (E(_7F)._==0)?true:false;}else{var _7H=E(_7F);if(!_7H._){return false;}else{if(E(_7G.a)!=E(_7H.a)){return false;}else{_7E=_7G.b;_7F=_7H.b;continue;}}}}},_7I=function(_7J,_7K){return E(_7J)!=E(_7K);},_7L=function(_7M,_7N){return E(_7M)==E(_7N);},_7O=new T2(0,_7L,_7I),_7P=function(_7Q,_7R){while(1){var _7S=E(_7Q);if(!_7S._){return (E(_7R)._==0)?true:false;}else{var _7T=E(_7R);if(!_7T._){return false;}else{if(E(_7S.a)!=E(_7T.a)){return false;}else{_7Q=_7S.b;_7R=_7T.b;continue;}}}}},_7U=function(_7V,_7W){return (!B(_7P(_7V,_7W)))?true:false;},_7X=new T2(0,_7P,_7U),_7Y=function(_7Z,_80){var _81=E(_7Z);switch(_81._){case 0:return new T1(0,function(_82){return new F(function(){return _7Y(B(A1(_81.a,_82)),_80);});});case 1:return new T1(1,function(_83){return new F(function(){return _7Y(B(A1(_81.a,_83)),_80);});});case 2:return new T0(2);case 3:return new F(function(){return _6Z(B(A1(_80,_81.a)),new T(function(){return B(_7Y(_81.b,_80));}));});break;default:var _84=function(_85){var _86=E(_85);if(!_86._){return __Z;}else{var _87=E(_86.a);return new F(function(){return _O(B(_6K(B(A1(_80,_87.a)),_87.b)),new T(function(){return B(_84(_86.b));},1));});}},_88=B(_84(_81.a));return (_88._==0)?new T0(2):new T1(4,_88);}},_89=new T0(2),_8a=function(_8b){return new T2(3,_8b,_89);},_8c=function(_8d,_8e){var _8f=E(_8d);if(!_8f){return new F(function(){return A1(_8e,_2t);});}else{var _8g=new T(function(){return B(_8c(_8f-1|0,_8e));});return new T1(0,function(_8h){return E(_8g);});}},_8i=function(_8j,_8k,_8l){var _8m=new T(function(){return B(A1(_8j,_8a));}),_8n=function(_8o,_8p,_8q,_8r){while(1){var _8s=B((function(_8t,_8u,_8v,_8w){var _8x=E(_8t);switch(_8x._){case 0:var _8y=E(_8u);if(!_8y._){return new F(function(){return A1(_8k,_8w);});}else{var _8z=_8v+1|0,_8A=_8w;_8o=B(A1(_8x.a,_8y.a));_8p=_8y.b;_8q=_8z;_8r=_8A;return __continue;}break;case 1:var _8B=B(A1(_8x.a,_8u)),_8C=_8u,_8z=_8v,_8A=_8w;_8o=_8B;_8p=_8C;_8q=_8z;_8r=_8A;return __continue;case 2:return new F(function(){return A1(_8k,_8w);});break;case 3:var _8D=new T(function(){return B(_7Y(_8x,_8w));});return new F(function(){return _8c(_8v,function(_8E){return E(_8D);});});break;default:return new F(function(){return _7Y(_8x,_8w);});}})(_8o,_8p,_8q,_8r));if(_8s!=__continue){return _8s;}}};return function(_8F){return new F(function(){return _8n(_8m,_8F,0,_8l);});};},_8G=function(_8H){return new F(function(){return A1(_8H,_u);});},_8I=function(_8J,_8K){var _8L=function(_8M){var _8N=E(_8M);if(!_8N._){return E(_8G);}else{var _8O=_8N.a;if(!B(A1(_8J,_8O))){return E(_8G);}else{var _8P=new T(function(){return B(_8L(_8N.b));}),_8Q=function(_8R){var _8S=new T(function(){return B(A1(_8P,function(_8T){return new F(function(){return A1(_8R,new T2(1,_8O,_8T));});}));});return new T1(0,function(_8U){return E(_8S);});};return E(_8Q);}}};return function(_8V){return new F(function(){return A2(_8L,_8V,_8K);});};},_8W=new T0(6),_8X=new T(function(){return B(unCStr("valDig: Bad base"));}),_8Y=new T(function(){return B(err(_8X));}),_8Z=function(_90,_91){var _92=function(_93,_94){var _95=E(_93);if(!_95._){var _96=new T(function(){return B(A1(_94,_u));});return function(_97){return new F(function(){return A1(_97,_96);});};}else{var _98=E(_95.a),_99=function(_9a){var _9b=new T(function(){return B(_92(_95.b,function(_9c){return new F(function(){return A1(_94,new T2(1,_9a,_9c));});}));}),_9d=function(_9e){var _9f=new T(function(){return B(A1(_9b,_9e));});return new T1(0,function(_9g){return E(_9f);});};return E(_9d);};switch(E(_90)){case 8:if(48>_98){var _9h=new T(function(){return B(A1(_94,_u));});return function(_9i){return new F(function(){return A1(_9i,_9h);});};}else{if(_98>55){var _9j=new T(function(){return B(A1(_94,_u));});return function(_9k){return new F(function(){return A1(_9k,_9j);});};}else{return new F(function(){return _99(_98-48|0);});}}break;case 10:if(48>_98){var _9l=new T(function(){return B(A1(_94,_u));});return function(_9m){return new F(function(){return A1(_9m,_9l);});};}else{if(_98>57){var _9n=new T(function(){return B(A1(_94,_u));});return function(_9o){return new F(function(){return A1(_9o,_9n);});};}else{return new F(function(){return _99(_98-48|0);});}}break;case 16:if(48>_98){if(97>_98){if(65>_98){var _9p=new T(function(){return B(A1(_94,_u));});return function(_9q){return new F(function(){return A1(_9q,_9p);});};}else{if(_98>70){var _9r=new T(function(){return B(A1(_94,_u));});return function(_9s){return new F(function(){return A1(_9s,_9r);});};}else{return new F(function(){return _99((_98-65|0)+10|0);});}}}else{if(_98>102){if(65>_98){var _9t=new T(function(){return B(A1(_94,_u));});return function(_9u){return new F(function(){return A1(_9u,_9t);});};}else{if(_98>70){var _9v=new T(function(){return B(A1(_94,_u));});return function(_9w){return new F(function(){return A1(_9w,_9v);});};}else{return new F(function(){return _99((_98-65|0)+10|0);});}}}else{return new F(function(){return _99((_98-97|0)+10|0);});}}}else{if(_98>57){if(97>_98){if(65>_98){var _9x=new T(function(){return B(A1(_94,_u));});return function(_9y){return new F(function(){return A1(_9y,_9x);});};}else{if(_98>70){var _9z=new T(function(){return B(A1(_94,_u));});return function(_9A){return new F(function(){return A1(_9A,_9z);});};}else{return new F(function(){return _99((_98-65|0)+10|0);});}}}else{if(_98>102){if(65>_98){var _9B=new T(function(){return B(A1(_94,_u));});return function(_9C){return new F(function(){return A1(_9C,_9B);});};}else{if(_98>70){var _9D=new T(function(){return B(A1(_94,_u));});return function(_9E){return new F(function(){return A1(_9E,_9D);});};}else{return new F(function(){return _99((_98-65|0)+10|0);});}}}else{return new F(function(){return _99((_98-97|0)+10|0);});}}}else{return new F(function(){return _99(_98-48|0);});}}break;default:return E(_8Y);}}},_9F=function(_9G){var _9H=E(_9G);if(!_9H._){return new T0(2);}else{return new F(function(){return A1(_91,_9H);});}};return function(_9I){return new F(function(){return A3(_92,_9I,_2q,_9F);});};},_9J=16,_9K=8,_9L=function(_9M){var _9N=function(_9O){return new F(function(){return A1(_9M,new T1(5,new T2(0,_9K,_9O)));});},_9P=function(_9Q){return new F(function(){return A1(_9M,new T1(5,new T2(0,_9J,_9Q)));});},_9R=function(_9S){switch(E(_9S)){case 79:return new T1(1,B(_8Z(_9K,_9N)));case 88:return new T1(1,B(_8Z(_9J,_9P)));case 111:return new T1(1,B(_8Z(_9K,_9N)));case 120:return new T1(1,B(_8Z(_9J,_9P)));default:return new T0(2);}};return function(_9T){return (E(_9T)==48)?E(new T1(0,_9R)):new T0(2);};},_9U=function(_9V){return new T1(0,B(_9L(_9V)));},_9W=function(_9X){return new F(function(){return A1(_9X,_2a);});},_9Y=function(_9Z){return new F(function(){return A1(_9Z,_2a);});},_a0=10,_a1=new T1(0,1),_a2=new T1(0,2147483647),_a3=function(_a4,_a5){while(1){var _a6=E(_a4);if(!_a6._){var _a7=_a6.a,_a8=E(_a5);if(!_a8._){var _a9=_a8.a,_aa=addC(_a7,_a9);if(!E(_aa.b)){return new T1(0,_aa.a);}else{_a4=new T1(1,I_fromInt(_a7));_a5=new T1(1,I_fromInt(_a9));continue;}}else{_a4=new T1(1,I_fromInt(_a7));_a5=_a8;continue;}}else{var _ab=E(_a5);if(!_ab._){_a4=_a6;_a5=new T1(1,I_fromInt(_ab.a));continue;}else{return new T1(1,I_add(_a6.a,_ab.a));}}}},_ac=new T(function(){return B(_a3(_a2,_a1));}),_ad=function(_ae){var _af=E(_ae);if(!_af._){var _ag=E(_af.a);return (_ag==(-2147483648))?E(_ac):new T1(0, -_ag);}else{return new T1(1,I_negate(_af.a));}},_ah=new T1(0,10),_ai=function(_aj,_ak){while(1){var _al=E(_aj);if(!_al._){return E(_ak);}else{var _am=_ak+1|0;_aj=_al.b;_ak=_am;continue;}}},_an=function(_ao,_ap){var _aq=E(_ap);return (_aq._==0)?__Z:new T2(1,new T(function(){return B(A1(_ao,_aq.a));}),new T(function(){return B(_an(_ao,_aq.b));}));},_ar=function(_as){return new F(function(){return _3R(E(_as));});},_at=new T(function(){return B(unCStr("this should not happen"));}),_au=new T(function(){return B(err(_at));}),_av=function(_aw,_ax){while(1){var _ay=E(_aw);if(!_ay._){var _az=_ay.a,_aA=E(_ax);if(!_aA._){var _aB=_aA.a;if(!(imul(_az,_aB)|0)){return new T1(0,imul(_az,_aB)|0);}else{_aw=new T1(1,I_fromInt(_az));_ax=new T1(1,I_fromInt(_aB));continue;}}else{_aw=new T1(1,I_fromInt(_az));_ax=_aA;continue;}}else{var _aC=E(_ax);if(!_aC._){_aw=_ay;_ax=new T1(1,I_fromInt(_aC.a));continue;}else{return new T1(1,I_mul(_ay.a,_aC.a));}}}},_aD=function(_aE,_aF){var _aG=E(_aF);if(!_aG._){return __Z;}else{var _aH=E(_aG.b);return (_aH._==0)?E(_au):new T2(1,B(_a3(B(_av(_aG.a,_aE)),_aH.a)),new T(function(){return B(_aD(_aE,_aH.b));}));}},_aI=new T1(0,0),_aJ=function(_aK,_aL,_aM){while(1){var _aN=B((function(_aO,_aP,_aQ){var _aR=E(_aQ);if(!_aR._){return E(_aI);}else{if(!E(_aR.b)._){return E(_aR.a);}else{var _aS=E(_aP);if(_aS<=40){var _aT=function(_aU,_aV){while(1){var _aW=E(_aV);if(!_aW._){return E(_aU);}else{var _aX=B(_a3(B(_av(_aU,_aO)),_aW.a));_aU=_aX;_aV=_aW.b;continue;}}};return new F(function(){return _aT(_aI,_aR);});}else{var _aY=B(_av(_aO,_aO));if(!(_aS%2)){var _aZ=B(_aD(_aO,_aR));_aK=_aY;_aL=quot(_aS+1|0,2);_aM=_aZ;return __continue;}else{var _aZ=B(_aD(_aO,new T2(1,_aI,_aR)));_aK=_aY;_aL=quot(_aS+1|0,2);_aM=_aZ;return __continue;}}}}})(_aK,_aL,_aM));if(_aN!=__continue){return _aN;}}},_b0=function(_b1,_b2){return new F(function(){return _aJ(_b1,new T(function(){return B(_ai(_b2,0));},1),B(_an(_ar,_b2)));});},_b3=function(_b4){var _b5=new T(function(){var _b6=new T(function(){var _b7=function(_b8){return new F(function(){return A1(_b4,new T1(1,new T(function(){return B(_b0(_ah,_b8));})));});};return new T1(1,B(_8Z(_a0,_b7)));}),_b9=function(_ba){if(E(_ba)==43){var _bb=function(_bc){return new F(function(){return A1(_b4,new T1(1,new T(function(){return B(_b0(_ah,_bc));})));});};return new T1(1,B(_8Z(_a0,_bb)));}else{return new T0(2);}},_bd=function(_be){if(E(_be)==45){var _bf=function(_bg){return new F(function(){return A1(_b4,new T1(1,new T(function(){return B(_ad(B(_b0(_ah,_bg))));})));});};return new T1(1,B(_8Z(_a0,_bf)));}else{return new T0(2);}};return B(_6Z(B(_6Z(new T1(0,_bd),new T1(0,_b9))),_b6));});return new F(function(){return _6Z(new T1(0,function(_bh){return (E(_bh)==101)?E(_b5):new T0(2);}),new T1(0,function(_bi){return (E(_bi)==69)?E(_b5):new T0(2);}));});},_bj=function(_bk){var _bl=function(_bm){return new F(function(){return A1(_bk,new T1(1,_bm));});};return function(_bn){return (E(_bn)==46)?new T1(1,B(_8Z(_a0,_bl))):new T0(2);};},_bo=function(_bp){return new T1(0,B(_bj(_bp)));},_bq=function(_br){var _bs=function(_bt){var _bu=function(_bv){return new T1(1,B(_8i(_b3,_9W,function(_bw){return new F(function(){return A1(_br,new T1(5,new T3(1,_bt,_bv,_bw)));});})));};return new T1(1,B(_8i(_bo,_9Y,_bu)));};return new F(function(){return _8Z(_a0,_bs);});},_bx=function(_by){return new T1(1,B(_bq(_by)));},_bz=function(_bA){return E(E(_bA).a);},_bB=function(_bC,_bD,_bE){while(1){var _bF=E(_bE);if(!_bF._){return false;}else{if(!B(A3(_bz,_bC,_bD,_bF.a))){_bE=_bF.b;continue;}else{return true;}}}},_bG=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_bH=function(_bI){return new F(function(){return _bB(_7O,_bI,_bG);});},_bJ=false,_bK=true,_bL=function(_bM){var _bN=new T(function(){return B(A1(_bM,_9K));}),_bO=new T(function(){return B(A1(_bM,_9J));});return function(_bP){switch(E(_bP)){case 79:return E(_bN);case 88:return E(_bO);case 111:return E(_bN);case 120:return E(_bO);default:return new T0(2);}};},_bQ=function(_bR){return new T1(0,B(_bL(_bR)));},_bS=function(_bT){return new F(function(){return A1(_bT,_a0);});},_bU=function(_bV,_bW){var _bX=jsShowI(_bV);return new F(function(){return _O(fromJSStr(_bX),_bW);});},_bY=41,_bZ=40,_c0=function(_c1,_c2,_c3){if(_c2>=0){return new F(function(){return _bU(_c2,_c3);});}else{if(_c1<=6){return new F(function(){return _bU(_c2,_c3);});}else{return new T2(1,_bZ,new T(function(){var _c4=jsShowI(_c2);return B(_O(fromJSStr(_c4),new T2(1,_bY,_c3)));}));}}},_c5=function(_c6){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_c0(9,_c6,_u));}))));});},_c7=function(_c8){var _c9=E(_c8);if(!_c9._){return E(_c9.a);}else{return new F(function(){return I_toInt(_c9.a);});}},_ca=function(_cb,_cc){var _cd=E(_cb);if(!_cd._){var _ce=_cd.a,_cf=E(_cc);return (_cf._==0)?_ce<=_cf.a:I_compareInt(_cf.a,_ce)>=0;}else{var _cg=_cd.a,_ch=E(_cc);return (_ch._==0)?I_compareInt(_cg,_ch.a)<=0:I_compare(_cg,_ch.a)<=0;}},_ci=function(_cj){return new T0(2);},_ck=function(_cl){var _cm=E(_cl);if(!_cm._){return E(_ci);}else{var _cn=_cm.a,_co=E(_cm.b);if(!_co._){return E(_cn);}else{var _cp=new T(function(){return B(_ck(_co));}),_cq=function(_cr){return new F(function(){return _6Z(B(A1(_cn,_cr)),new T(function(){return B(A1(_cp,_cr));}));});};return E(_cq);}}},_cs=function(_ct,_cu){var _cv=function(_cw,_cx,_cy){var _cz=E(_cw);if(!_cz._){return new F(function(){return A1(_cy,_ct);});}else{var _cA=E(_cx);if(!_cA._){return new T0(2);}else{if(E(_cz.a)!=E(_cA.a)){return new T0(2);}else{var _cB=new T(function(){return B(_cv(_cz.b,_cA.b,_cy));});return new T1(0,function(_cC){return E(_cB);});}}}};return function(_cD){return new F(function(){return _cv(_ct,_cD,_cu);});};},_cE=new T(function(){return B(unCStr("SO"));}),_cF=14,_cG=function(_cH){var _cI=new T(function(){return B(A1(_cH,_cF));});return new T1(1,B(_cs(_cE,function(_cJ){return E(_cI);})));},_cK=new T(function(){return B(unCStr("SOH"));}),_cL=1,_cM=function(_cN){var _cO=new T(function(){return B(A1(_cN,_cL));});return new T1(1,B(_cs(_cK,function(_cP){return E(_cO);})));},_cQ=function(_cR){return new T1(1,B(_8i(_cM,_cG,_cR)));},_cS=new T(function(){return B(unCStr("NUL"));}),_cT=0,_cU=function(_cV){var _cW=new T(function(){return B(A1(_cV,_cT));});return new T1(1,B(_cs(_cS,function(_cX){return E(_cW);})));},_cY=new T(function(){return B(unCStr("STX"));}),_cZ=2,_d0=function(_d1){var _d2=new T(function(){return B(A1(_d1,_cZ));});return new T1(1,B(_cs(_cY,function(_d3){return E(_d2);})));},_d4=new T(function(){return B(unCStr("ETX"));}),_d5=3,_d6=function(_d7){var _d8=new T(function(){return B(A1(_d7,_d5));});return new T1(1,B(_cs(_d4,function(_d9){return E(_d8);})));},_da=new T(function(){return B(unCStr("EOT"));}),_db=4,_dc=function(_dd){var _de=new T(function(){return B(A1(_dd,_db));});return new T1(1,B(_cs(_da,function(_df){return E(_de);})));},_dg=new T(function(){return B(unCStr("ENQ"));}),_dh=5,_di=function(_dj){var _dk=new T(function(){return B(A1(_dj,_dh));});return new T1(1,B(_cs(_dg,function(_dl){return E(_dk);})));},_dm=new T(function(){return B(unCStr("ACK"));}),_dn=6,_do=function(_dp){var _dq=new T(function(){return B(A1(_dp,_dn));});return new T1(1,B(_cs(_dm,function(_dr){return E(_dq);})));},_ds=new T(function(){return B(unCStr("BEL"));}),_dt=7,_du=function(_dv){var _dw=new T(function(){return B(A1(_dv,_dt));});return new T1(1,B(_cs(_ds,function(_dx){return E(_dw);})));},_dy=new T(function(){return B(unCStr("BS"));}),_dz=8,_dA=function(_dB){var _dC=new T(function(){return B(A1(_dB,_dz));});return new T1(1,B(_cs(_dy,function(_dD){return E(_dC);})));},_dE=new T(function(){return B(unCStr("HT"));}),_dF=9,_dG=function(_dH){var _dI=new T(function(){return B(A1(_dH,_dF));});return new T1(1,B(_cs(_dE,function(_dJ){return E(_dI);})));},_dK=new T(function(){return B(unCStr("LF"));}),_dL=10,_dM=function(_dN){var _dO=new T(function(){return B(A1(_dN,_dL));});return new T1(1,B(_cs(_dK,function(_dP){return E(_dO);})));},_dQ=new T(function(){return B(unCStr("VT"));}),_dR=11,_dS=function(_dT){var _dU=new T(function(){return B(A1(_dT,_dR));});return new T1(1,B(_cs(_dQ,function(_dV){return E(_dU);})));},_dW=new T(function(){return B(unCStr("FF"));}),_dX=12,_dY=function(_dZ){var _e0=new T(function(){return B(A1(_dZ,_dX));});return new T1(1,B(_cs(_dW,function(_e1){return E(_e0);})));},_e2=new T(function(){return B(unCStr("CR"));}),_e3=13,_e4=function(_e5){var _e6=new T(function(){return B(A1(_e5,_e3));});return new T1(1,B(_cs(_e2,function(_e7){return E(_e6);})));},_e8=new T(function(){return B(unCStr("SI"));}),_e9=15,_ea=function(_eb){var _ec=new T(function(){return B(A1(_eb,_e9));});return new T1(1,B(_cs(_e8,function(_ed){return E(_ec);})));},_ee=new T(function(){return B(unCStr("DLE"));}),_ef=16,_eg=function(_eh){var _ei=new T(function(){return B(A1(_eh,_ef));});return new T1(1,B(_cs(_ee,function(_ej){return E(_ei);})));},_ek=new T(function(){return B(unCStr("DC1"));}),_el=17,_em=function(_en){var _eo=new T(function(){return B(A1(_en,_el));});return new T1(1,B(_cs(_ek,function(_ep){return E(_eo);})));},_eq=new T(function(){return B(unCStr("DC2"));}),_er=18,_es=function(_et){var _eu=new T(function(){return B(A1(_et,_er));});return new T1(1,B(_cs(_eq,function(_ev){return E(_eu);})));},_ew=new T(function(){return B(unCStr("DC3"));}),_ex=19,_ey=function(_ez){var _eA=new T(function(){return B(A1(_ez,_ex));});return new T1(1,B(_cs(_ew,function(_eB){return E(_eA);})));},_eC=new T(function(){return B(unCStr("DC4"));}),_eD=20,_eE=function(_eF){var _eG=new T(function(){return B(A1(_eF,_eD));});return new T1(1,B(_cs(_eC,function(_eH){return E(_eG);})));},_eI=new T(function(){return B(unCStr("NAK"));}),_eJ=21,_eK=function(_eL){var _eM=new T(function(){return B(A1(_eL,_eJ));});return new T1(1,B(_cs(_eI,function(_eN){return E(_eM);})));},_eO=new T(function(){return B(unCStr("SYN"));}),_eP=22,_eQ=function(_eR){var _eS=new T(function(){return B(A1(_eR,_eP));});return new T1(1,B(_cs(_eO,function(_eT){return E(_eS);})));},_eU=new T(function(){return B(unCStr("ETB"));}),_eV=23,_eW=function(_eX){var _eY=new T(function(){return B(A1(_eX,_eV));});return new T1(1,B(_cs(_eU,function(_eZ){return E(_eY);})));},_f0=new T(function(){return B(unCStr("CAN"));}),_f1=24,_f2=function(_f3){var _f4=new T(function(){return B(A1(_f3,_f1));});return new T1(1,B(_cs(_f0,function(_f5){return E(_f4);})));},_f6=new T(function(){return B(unCStr("EM"));}),_f7=25,_f8=function(_f9){var _fa=new T(function(){return B(A1(_f9,_f7));});return new T1(1,B(_cs(_f6,function(_fb){return E(_fa);})));},_fc=new T(function(){return B(unCStr("SUB"));}),_fd=26,_fe=function(_ff){var _fg=new T(function(){return B(A1(_ff,_fd));});return new T1(1,B(_cs(_fc,function(_fh){return E(_fg);})));},_fi=new T(function(){return B(unCStr("ESC"));}),_fj=27,_fk=function(_fl){var _fm=new T(function(){return B(A1(_fl,_fj));});return new T1(1,B(_cs(_fi,function(_fn){return E(_fm);})));},_fo=new T(function(){return B(unCStr("FS"));}),_fp=28,_fq=function(_fr){var _fs=new T(function(){return B(A1(_fr,_fp));});return new T1(1,B(_cs(_fo,function(_ft){return E(_fs);})));},_fu=new T(function(){return B(unCStr("GS"));}),_fv=29,_fw=function(_fx){var _fy=new T(function(){return B(A1(_fx,_fv));});return new T1(1,B(_cs(_fu,function(_fz){return E(_fy);})));},_fA=new T(function(){return B(unCStr("RS"));}),_fB=30,_fC=function(_fD){var _fE=new T(function(){return B(A1(_fD,_fB));});return new T1(1,B(_cs(_fA,function(_fF){return E(_fE);})));},_fG=new T(function(){return B(unCStr("US"));}),_fH=31,_fI=function(_fJ){var _fK=new T(function(){return B(A1(_fJ,_fH));});return new T1(1,B(_cs(_fG,function(_fL){return E(_fK);})));},_fM=new T(function(){return B(unCStr("SP"));}),_fN=32,_fO=function(_fP){var _fQ=new T(function(){return B(A1(_fP,_fN));});return new T1(1,B(_cs(_fM,function(_fR){return E(_fQ);})));},_fS=new T(function(){return B(unCStr("DEL"));}),_fT=127,_fU=function(_fV){var _fW=new T(function(){return B(A1(_fV,_fT));});return new T1(1,B(_cs(_fS,function(_fX){return E(_fW);})));},_fY=new T2(1,_fU,_u),_fZ=new T2(1,_fO,_fY),_g0=new T2(1,_fI,_fZ),_g1=new T2(1,_fC,_g0),_g2=new T2(1,_fw,_g1),_g3=new T2(1,_fq,_g2),_g4=new T2(1,_fk,_g3),_g5=new T2(1,_fe,_g4),_g6=new T2(1,_f8,_g5),_g7=new T2(1,_f2,_g6),_g8=new T2(1,_eW,_g7),_g9=new T2(1,_eQ,_g8),_ga=new T2(1,_eK,_g9),_gb=new T2(1,_eE,_ga),_gc=new T2(1,_ey,_gb),_gd=new T2(1,_es,_gc),_ge=new T2(1,_em,_gd),_gf=new T2(1,_eg,_ge),_gg=new T2(1,_ea,_gf),_gh=new T2(1,_e4,_gg),_gi=new T2(1,_dY,_gh),_gj=new T2(1,_dS,_gi),_gk=new T2(1,_dM,_gj),_gl=new T2(1,_dG,_gk),_gm=new T2(1,_dA,_gl),_gn=new T2(1,_du,_gm),_go=new T2(1,_do,_gn),_gp=new T2(1,_di,_go),_gq=new T2(1,_dc,_gp),_gr=new T2(1,_d6,_gq),_gs=new T2(1,_d0,_gr),_gt=new T2(1,_cU,_gs),_gu=new T2(1,_cQ,_gt),_gv=new T(function(){return B(_ck(_gu));}),_gw=34,_gx=new T1(0,1114111),_gy=92,_gz=39,_gA=function(_gB){var _gC=new T(function(){return B(A1(_gB,_dt));}),_gD=new T(function(){return B(A1(_gB,_dz));}),_gE=new T(function(){return B(A1(_gB,_dF));}),_gF=new T(function(){return B(A1(_gB,_dL));}),_gG=new T(function(){return B(A1(_gB,_dR));}),_gH=new T(function(){return B(A1(_gB,_dX));}),_gI=new T(function(){return B(A1(_gB,_e3));}),_gJ=new T(function(){return B(A1(_gB,_gy));}),_gK=new T(function(){return B(A1(_gB,_gz));}),_gL=new T(function(){return B(A1(_gB,_gw));}),_gM=new T(function(){var _gN=function(_gO){var _gP=new T(function(){return B(_3R(E(_gO)));}),_gQ=function(_gR){var _gS=B(_b0(_gP,_gR));if(!B(_ca(_gS,_gx))){return new T0(2);}else{return new F(function(){return A1(_gB,new T(function(){var _gT=B(_c7(_gS));if(_gT>>>0>1114111){return B(_c5(_gT));}else{return _gT;}}));});}};return new T1(1,B(_8Z(_gO,_gQ)));},_gU=new T(function(){var _gV=new T(function(){return B(A1(_gB,_fH));}),_gW=new T(function(){return B(A1(_gB,_fB));}),_gX=new T(function(){return B(A1(_gB,_fv));}),_gY=new T(function(){return B(A1(_gB,_fp));}),_gZ=new T(function(){return B(A1(_gB,_fj));}),_h0=new T(function(){return B(A1(_gB,_fd));}),_h1=new T(function(){return B(A1(_gB,_f7));}),_h2=new T(function(){return B(A1(_gB,_f1));}),_h3=new T(function(){return B(A1(_gB,_eV));}),_h4=new T(function(){return B(A1(_gB,_eP));}),_h5=new T(function(){return B(A1(_gB,_eJ));}),_h6=new T(function(){return B(A1(_gB,_eD));}),_h7=new T(function(){return B(A1(_gB,_ex));}),_h8=new T(function(){return B(A1(_gB,_er));}),_h9=new T(function(){return B(A1(_gB,_el));}),_ha=new T(function(){return B(A1(_gB,_ef));}),_hb=new T(function(){return B(A1(_gB,_e9));}),_hc=new T(function(){return B(A1(_gB,_cF));}),_hd=new T(function(){return B(A1(_gB,_dn));}),_he=new T(function(){return B(A1(_gB,_dh));}),_hf=new T(function(){return B(A1(_gB,_db));}),_hg=new T(function(){return B(A1(_gB,_d5));}),_hh=new T(function(){return B(A1(_gB,_cZ));}),_hi=new T(function(){return B(A1(_gB,_cL));}),_hj=new T(function(){return B(A1(_gB,_cT));}),_hk=function(_hl){switch(E(_hl)){case 64:return E(_hj);case 65:return E(_hi);case 66:return E(_hh);case 67:return E(_hg);case 68:return E(_hf);case 69:return E(_he);case 70:return E(_hd);case 71:return E(_gC);case 72:return E(_gD);case 73:return E(_gE);case 74:return E(_gF);case 75:return E(_gG);case 76:return E(_gH);case 77:return E(_gI);case 78:return E(_hc);case 79:return E(_hb);case 80:return E(_ha);case 81:return E(_h9);case 82:return E(_h8);case 83:return E(_h7);case 84:return E(_h6);case 85:return E(_h5);case 86:return E(_h4);case 87:return E(_h3);case 88:return E(_h2);case 89:return E(_h1);case 90:return E(_h0);case 91:return E(_gZ);case 92:return E(_gY);case 93:return E(_gX);case 94:return E(_gW);case 95:return E(_gV);default:return new T0(2);}};return B(_6Z(new T1(0,function(_hm){return (E(_hm)==94)?E(new T1(0,_hk)):new T0(2);}),new T(function(){return B(A1(_gv,_gB));})));});return B(_6Z(new T1(1,B(_8i(_bQ,_bS,_gN))),_gU));});return new F(function(){return _6Z(new T1(0,function(_hn){switch(E(_hn)){case 34:return E(_gL);case 39:return E(_gK);case 92:return E(_gJ);case 97:return E(_gC);case 98:return E(_gD);case 102:return E(_gH);case 110:return E(_gF);case 114:return E(_gI);case 116:return E(_gE);case 118:return E(_gG);default:return new T0(2);}}),_gM);});},_ho=function(_hp){return new F(function(){return A1(_hp,_2t);});},_hq=function(_hr){var _hs=E(_hr);if(!_hs._){return E(_ho);}else{var _ht=E(_hs.a),_hu=_ht>>>0,_hv=new T(function(){return B(_hq(_hs.b));});if(_hu>887){var _hw=u_iswspace(_ht);if(!E(_hw)){return E(_ho);}else{var _hx=function(_hy){var _hz=new T(function(){return B(A1(_hv,_hy));});return new T1(0,function(_hA){return E(_hz);});};return E(_hx);}}else{var _hB=E(_hu);if(_hB==32){var _hC=function(_hD){var _hE=new T(function(){return B(A1(_hv,_hD));});return new T1(0,function(_hF){return E(_hE);});};return E(_hC);}else{if(_hB-9>>>0>4){if(E(_hB)==160){var _hG=function(_hH){var _hI=new T(function(){return B(A1(_hv,_hH));});return new T1(0,function(_hJ){return E(_hI);});};return E(_hG);}else{return E(_ho);}}else{var _hK=function(_hL){var _hM=new T(function(){return B(A1(_hv,_hL));});return new T1(0,function(_hN){return E(_hM);});};return E(_hK);}}}}},_hO=function(_hP){var _hQ=new T(function(){return B(_hO(_hP));}),_hR=function(_hS){return (E(_hS)==92)?E(_hQ):new T0(2);},_hT=function(_hU){return E(new T1(0,_hR));},_hV=new T1(1,function(_hW){return new F(function(){return A2(_hq,_hW,_hT);});}),_hX=new T(function(){return B(_gA(function(_hY){return new F(function(){return A1(_hP,new T2(0,_hY,_bK));});}));}),_hZ=function(_i0){var _i1=E(_i0);if(_i1==38){return E(_hQ);}else{var _i2=_i1>>>0;if(_i2>887){var _i3=u_iswspace(_i1);return (E(_i3)==0)?new T0(2):E(_hV);}else{var _i4=E(_i2);return (_i4==32)?E(_hV):(_i4-9>>>0>4)?(E(_i4)==160)?E(_hV):new T0(2):E(_hV);}}};return new F(function(){return _6Z(new T1(0,function(_i5){return (E(_i5)==92)?E(new T1(0,_hZ)):new T0(2);}),new T1(0,function(_i6){var _i7=E(_i6);if(E(_i7)==92){return E(_hX);}else{return new F(function(){return A1(_hP,new T2(0,_i7,_bJ));});}}));});},_i8=function(_i9,_ia){var _ib=new T(function(){return B(A1(_ia,new T1(1,new T(function(){return B(A1(_i9,_u));}))));}),_ic=function(_id){var _ie=E(_id),_if=E(_ie.a);if(E(_if)==34){if(!E(_ie.b)){return E(_ib);}else{return new F(function(){return _i8(function(_ig){return new F(function(){return A1(_i9,new T2(1,_if,_ig));});},_ia);});}}else{return new F(function(){return _i8(function(_ih){return new F(function(){return A1(_i9,new T2(1,_if,_ih));});},_ia);});}};return new F(function(){return _hO(_ic);});},_ii=new T(function(){return B(unCStr("_\'"));}),_ij=function(_ik){var _il=u_iswalnum(_ik);if(!E(_il)){return new F(function(){return _bB(_7O,_ik,_ii);});}else{return true;}},_im=function(_in){return new F(function(){return _ij(E(_in));});},_io=new T(function(){return B(unCStr(",;()[]{}`"));}),_ip=new T(function(){return B(unCStr("=>"));}),_iq=new T2(1,_ip,_u),_ir=new T(function(){return B(unCStr("~"));}),_is=new T2(1,_ir,_iq),_it=new T(function(){return B(unCStr("@"));}),_iu=new T2(1,_it,_is),_iv=new T(function(){return B(unCStr("->"));}),_iw=new T2(1,_iv,_iu),_ix=new T(function(){return B(unCStr("<-"));}),_iy=new T2(1,_ix,_iw),_iz=new T(function(){return B(unCStr("|"));}),_iA=new T2(1,_iz,_iy),_iB=new T(function(){return B(unCStr("\\"));}),_iC=new T2(1,_iB,_iA),_iD=new T(function(){return B(unCStr("="));}),_iE=new T2(1,_iD,_iC),_iF=new T(function(){return B(unCStr("::"));}),_iG=new T2(1,_iF,_iE),_iH=new T(function(){return B(unCStr(".."));}),_iI=new T2(1,_iH,_iG),_iJ=function(_iK){var _iL=new T(function(){return B(A1(_iK,_8W));}),_iM=new T(function(){var _iN=new T(function(){var _iO=function(_iP){var _iQ=new T(function(){return B(A1(_iK,new T1(0,_iP)));});return new T1(0,function(_iR){return (E(_iR)==39)?E(_iQ):new T0(2);});};return B(_gA(_iO));}),_iS=function(_iT){var _iU=E(_iT);switch(E(_iU)){case 39:return new T0(2);case 92:return E(_iN);default:var _iV=new T(function(){return B(A1(_iK,new T1(0,_iU)));});return new T1(0,function(_iW){return (E(_iW)==39)?E(_iV):new T0(2);});}},_iX=new T(function(){var _iY=new T(function(){return B(_i8(_2q,_iK));}),_iZ=new T(function(){var _j0=new T(function(){var _j1=new T(function(){var _j2=function(_j3){var _j4=E(_j3),_j5=u_iswalpha(_j4);return (E(_j5)==0)?(E(_j4)==95)?new T1(1,B(_8I(_im,function(_j6){return new F(function(){return A1(_iK,new T1(3,new T2(1,_j4,_j6)));});}))):new T0(2):new T1(1,B(_8I(_im,function(_j7){return new F(function(){return A1(_iK,new T1(3,new T2(1,_j4,_j7)));});})));};return B(_6Z(new T1(0,_j2),new T(function(){return new T1(1,B(_8i(_9U,_bx,_iK)));})));}),_j8=function(_j9){return (!B(_bB(_7O,_j9,_bG)))?new T0(2):new T1(1,B(_8I(_bH,function(_ja){var _jb=new T2(1,_j9,_ja);if(!B(_bB(_7X,_jb,_iI))){return new F(function(){return A1(_iK,new T1(4,_jb));});}else{return new F(function(){return A1(_iK,new T1(2,_jb));});}})));};return B(_6Z(new T1(0,_j8),_j1));});return B(_6Z(new T1(0,function(_jc){if(!B(_bB(_7O,_jc,_io))){return new T0(2);}else{return new F(function(){return A1(_iK,new T1(2,new T2(1,_jc,_u)));});}}),_j0));});return B(_6Z(new T1(0,function(_jd){return (E(_jd)==34)?E(_iY):new T0(2);}),_iZ));});return B(_6Z(new T1(0,function(_je){return (E(_je)==39)?E(new T1(0,_iS)):new T0(2);}),_iX));});return new F(function(){return _6Z(new T1(1,function(_jf){return (E(_jf)._==0)?E(_iL):new T0(2);}),_iM);});},_jg=0,_jh=function(_ji,_jj){var _jk=new T(function(){var _jl=new T(function(){var _jm=function(_jn){var _jo=new T(function(){var _jp=new T(function(){return B(A1(_jj,_jn));});return B(_iJ(function(_jq){var _jr=E(_jq);return (_jr._==2)?(!B(_7D(_jr.a,_7C)))?new T0(2):E(_jp):new T0(2);}));}),_js=function(_jt){return E(_jo);};return new T1(1,function(_ju){return new F(function(){return A2(_hq,_ju,_js);});});};return B(A2(_ji,_jg,_jm));});return B(_iJ(function(_jv){var _jw=E(_jv);return (_jw._==2)?(!B(_7D(_jw.a,_7B)))?new T0(2):E(_jl):new T0(2);}));}),_jx=function(_jy){return E(_jk);};return function(_jz){return new F(function(){return A2(_hq,_jz,_jx);});};},_jA=function(_jB,_jC){var _jD=function(_jE){var _jF=new T(function(){return B(A1(_jB,_jE));}),_jG=function(_jH){return new F(function(){return _6Z(B(A1(_jF,_jH)),new T(function(){return new T1(1,B(_jh(_jD,_jH)));}));});};return E(_jG);},_jI=new T(function(){return B(A1(_jB,_jC));}),_jJ=function(_jK){return new F(function(){return _6Z(B(A1(_jI,_jK)),new T(function(){return new T1(1,B(_jh(_jD,_jK)));}));});};return E(_jJ);},_jL=function(_jM,_jN){var _jO=function(_jP,_jQ){var _jR=function(_jS){return new F(function(){return A1(_jQ,new T(function(){return  -E(_jS);}));});},_jT=new T(function(){return B(_iJ(function(_jU){return new F(function(){return A3(_jM,_jU,_jP,_jR);});}));}),_jV=function(_jW){return E(_jT);},_jX=function(_jY){return new F(function(){return A2(_hq,_jY,_jV);});},_jZ=new T(function(){return B(_iJ(function(_k0){var _k1=E(_k0);if(_k1._==4){var _k2=E(_k1.a);if(!_k2._){return new F(function(){return A3(_jM,_k1,_jP,_jQ);});}else{if(E(_k2.a)==45){if(!E(_k2.b)._){return E(new T1(1,_jX));}else{return new F(function(){return A3(_jM,_k1,_jP,_jQ);});}}else{return new F(function(){return A3(_jM,_k1,_jP,_jQ);});}}}else{return new F(function(){return A3(_jM,_k1,_jP,_jQ);});}}));}),_k3=function(_k4){return E(_jZ);};return new T1(1,function(_k5){return new F(function(){return A2(_hq,_k5,_k3);});});};return new F(function(){return _jA(_jO,_jN);});},_k6=new T(function(){return 1/0;}),_k7=function(_k8,_k9){return new F(function(){return A1(_k9,_k6);});},_ka=new T(function(){return 0/0;}),_kb=function(_kc,_kd){return new F(function(){return A1(_kd,_ka);});},_ke=new T(function(){return B(unCStr("NaN"));}),_kf=new T(function(){return B(unCStr("Infinity"));}),_kg=1024,_kh=-1021,_ki=new T(function(){return B(unCStr("base"));}),_kj=new T(function(){return B(unCStr("GHC.Exception"));}),_kk=new T(function(){return B(unCStr("ArithException"));}),_kl=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_ki,_kj,_kk),_km=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_kl,_u,_u),_kn=function(_ko){return E(_km);},_kp=function(_kq){var _kr=E(_kq);return new F(function(){return _A(B(_y(_kr.a)),_kn,_kr.b);});},_ks=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_kt=new T(function(){return B(unCStr("denormal"));}),_ku=new T(function(){return B(unCStr("divide by zero"));}),_kv=new T(function(){return B(unCStr("loss of precision"));}),_kw=new T(function(){return B(unCStr("arithmetic underflow"));}),_kx=new T(function(){return B(unCStr("arithmetic overflow"));}),_ky=function(_kz,_kA){switch(E(_kz)){case 0:return new F(function(){return _O(_kx,_kA);});break;case 1:return new F(function(){return _O(_kw,_kA);});break;case 2:return new F(function(){return _O(_kv,_kA);});break;case 3:return new F(function(){return _O(_ku,_kA);});break;case 4:return new F(function(){return _O(_kt,_kA);});break;default:return new F(function(){return _O(_ks,_kA);});}},_kB=function(_kC){return new F(function(){return _ky(_kC,_u);});},_kD=function(_kE,_kF,_kG){return new F(function(){return _ky(_kF,_kG);});},_kH=function(_kI,_kJ){return new F(function(){return _1S(_ky,_kI,_kJ);});},_kK=new T3(0,_kD,_kB,_kH),_kL=new T(function(){return new T5(0,_kn,_kK,_kM,_kp,_kB);}),_kM=function(_52){return new T2(0,_kL,_52);},_kN=3,_kO=new T(function(){return B(_kM(_kN));}),_kP=new T(function(){return die(_kO);}),_kQ=function(_kR,_kS){var _kT=E(_kR);if(!_kT._){var _kU=_kT.a,_kV=E(_kS);return (_kV._==0)?_kU==_kV.a:(I_compareInt(_kV.a,_kU)==0)?true:false;}else{var _kW=_kT.a,_kX=E(_kS);return (_kX._==0)?(I_compareInt(_kW,_kX.a)==0)?true:false:(I_compare(_kW,_kX.a)==0)?true:false;}},_kY=new T1(0,0),_kZ=function(_l0,_l1){while(1){var _l2=E(_l0);if(!_l2._){var _l3=E(_l2.a);if(_l3==(-2147483648)){_l0=new T1(1,I_fromInt(-2147483648));continue;}else{var _l4=E(_l1);if(!_l4._){return new T1(0,_l3%_l4.a);}else{_l0=new T1(1,I_fromInt(_l3));_l1=_l4;continue;}}}else{var _l5=_l2.a,_l6=E(_l1);return (_l6._==0)?new T1(1,I_rem(_l5,I_fromInt(_l6.a))):new T1(1,I_rem(_l5,_l6.a));}}},_l7=function(_l8,_l9){if(!B(_kQ(_l9,_kY))){return new F(function(){return _kZ(_l8,_l9);});}else{return E(_kP);}},_la=function(_lb,_lc){while(1){if(!B(_kQ(_lc,_kY))){var _ld=_lc,_le=B(_l7(_lb,_lc));_lb=_ld;_lc=_le;continue;}else{return E(_lb);}}},_lf=function(_lg){var _lh=E(_lg);if(!_lh._){var _li=E(_lh.a);return (_li==(-2147483648))?E(_ac):(_li<0)?new T1(0, -_li):E(_lh);}else{var _lj=_lh.a;return (I_compareInt(_lj,0)>=0)?E(_lh):new T1(1,I_negate(_lj));}},_lk=function(_ll,_lm){while(1){var _ln=E(_ll);if(!_ln._){var _lo=E(_ln.a);if(_lo==(-2147483648)){_ll=new T1(1,I_fromInt(-2147483648));continue;}else{var _lp=E(_lm);if(!_lp._){return new T1(0,quot(_lo,_lp.a));}else{_ll=new T1(1,I_fromInt(_lo));_lm=_lp;continue;}}}else{var _lq=_ln.a,_lr=E(_lm);return (_lr._==0)?new T1(0,I_toInt(I_quot(_lq,I_fromInt(_lr.a)))):new T1(1,I_quot(_lq,_lr.a));}}},_ls=5,_lt=new T(function(){return B(_kM(_ls));}),_lu=new T(function(){return die(_lt);}),_lv=function(_lw,_lx){if(!B(_kQ(_lx,_kY))){var _ly=B(_la(B(_lf(_lw)),B(_lf(_lx))));return (!B(_kQ(_ly,_kY)))?new T2(0,B(_lk(_lw,_ly)),B(_lk(_lx,_ly))):E(_kP);}else{return E(_lu);}},_lz=new T1(0,1),_lA=new T(function(){return B(unCStr("Negative exponent"));}),_lB=new T(function(){return B(err(_lA));}),_lC=new T1(0,2),_lD=new T(function(){return B(_kQ(_lC,_kY));}),_lE=function(_lF,_lG){while(1){var _lH=E(_lF);if(!_lH._){var _lI=_lH.a,_lJ=E(_lG);if(!_lJ._){var _lK=_lJ.a,_lL=subC(_lI,_lK);if(!E(_lL.b)){return new T1(0,_lL.a);}else{_lF=new T1(1,I_fromInt(_lI));_lG=new T1(1,I_fromInt(_lK));continue;}}else{_lF=new T1(1,I_fromInt(_lI));_lG=_lJ;continue;}}else{var _lM=E(_lG);if(!_lM._){_lF=_lH;_lG=new T1(1,I_fromInt(_lM.a));continue;}else{return new T1(1,I_sub(_lH.a,_lM.a));}}}},_lN=function(_lO,_lP,_lQ){while(1){if(!E(_lD)){if(!B(_kQ(B(_kZ(_lP,_lC)),_kY))){if(!B(_kQ(_lP,_lz))){var _lR=B(_av(_lO,_lO)),_lS=B(_lk(B(_lE(_lP,_lz)),_lC)),_lT=B(_av(_lO,_lQ));_lO=_lR;_lP=_lS;_lQ=_lT;continue;}else{return new F(function(){return _av(_lO,_lQ);});}}else{var _lR=B(_av(_lO,_lO)),_lS=B(_lk(_lP,_lC));_lO=_lR;_lP=_lS;continue;}}else{return E(_kP);}}},_lU=function(_lV,_lW){while(1){if(!E(_lD)){if(!B(_kQ(B(_kZ(_lW,_lC)),_kY))){if(!B(_kQ(_lW,_lz))){return new F(function(){return _lN(B(_av(_lV,_lV)),B(_lk(B(_lE(_lW,_lz)),_lC)),_lV);});}else{return E(_lV);}}else{var _lX=B(_av(_lV,_lV)),_lY=B(_lk(_lW,_lC));_lV=_lX;_lW=_lY;continue;}}else{return E(_kP);}}},_lZ=function(_m0,_m1){var _m2=E(_m0);if(!_m2._){var _m3=_m2.a,_m4=E(_m1);return (_m4._==0)?_m3<_m4.a:I_compareInt(_m4.a,_m3)>0;}else{var _m5=_m2.a,_m6=E(_m1);return (_m6._==0)?I_compareInt(_m5,_m6.a)<0:I_compare(_m5,_m6.a)<0;}},_m7=function(_m8,_m9){if(!B(_lZ(_m9,_kY))){if(!B(_kQ(_m9,_kY))){return new F(function(){return _lU(_m8,_m9);});}else{return E(_lz);}}else{return E(_lB);}},_ma=new T1(0,1),_mb=new T1(0,0),_mc=new T1(0,-1),_md=function(_me){var _mf=E(_me);if(!_mf._){var _mg=_mf.a;return (_mg>=0)?(E(_mg)==0)?E(_mb):E(_a1):E(_mc);}else{var _mh=I_compareInt(_mf.a,0);return (_mh<=0)?(E(_mh)==0)?E(_mb):E(_mc):E(_a1);}},_mi=function(_mj,_mk,_ml){while(1){var _mm=E(_ml);if(!_mm._){if(!B(_lZ(_mj,_aI))){return new T2(0,B(_av(_mk,B(_m7(_ah,_mj)))),_lz);}else{var _mn=B(_m7(_ah,B(_ad(_mj))));return new F(function(){return _lv(B(_av(_mk,B(_md(_mn)))),B(_lf(_mn)));});}}else{var _mo=B(_lE(_mj,_ma)),_mp=B(_a3(B(_av(_mk,_ah)),B(_3R(E(_mm.a)))));_mj=_mo;_mk=_mp;_ml=_mm.b;continue;}}},_mq=function(_mr,_ms){var _mt=E(_mr);if(!_mt._){var _mu=_mt.a,_mv=E(_ms);return (_mv._==0)?_mu>=_mv.a:I_compareInt(_mv.a,_mu)<=0;}else{var _mw=_mt.a,_mx=E(_ms);return (_mx._==0)?I_compareInt(_mw,_mx.a)>=0:I_compare(_mw,_mx.a)>=0;}},_my=function(_mz){var _mA=E(_mz);if(!_mA._){var _mB=_mA.b;return new F(function(){return _lv(B(_av(B(_aJ(new T(function(){return B(_3R(E(_mA.a)));}),new T(function(){return B(_ai(_mB,0));},1),B(_an(_ar,_mB)))),_ma)),_ma);});}else{var _mC=_mA.a,_mD=_mA.c,_mE=E(_mA.b);if(!_mE._){var _mF=E(_mD);if(!_mF._){return new F(function(){return _lv(B(_av(B(_b0(_ah,_mC)),_ma)),_ma);});}else{var _mG=_mF.a;if(!B(_mq(_mG,_aI))){var _mH=B(_m7(_ah,B(_ad(_mG))));return new F(function(){return _lv(B(_av(B(_b0(_ah,_mC)),B(_md(_mH)))),B(_lf(_mH)));});}else{return new F(function(){return _lv(B(_av(B(_av(B(_b0(_ah,_mC)),B(_m7(_ah,_mG)))),_ma)),_ma);});}}}else{var _mI=_mE.a,_mJ=E(_mD);if(!_mJ._){return new F(function(){return _mi(_aI,B(_b0(_ah,_mC)),_mI);});}else{return new F(function(){return _mi(_mJ.a,B(_b0(_ah,_mC)),_mI);});}}}},_mK=function(_mL,_mM){while(1){var _mN=E(_mM);if(!_mN._){return __Z;}else{if(!B(A1(_mL,_mN.a))){return E(_mN);}else{_mM=_mN.b;continue;}}}},_mO=function(_mP,_mQ){var _mR=E(_mP);if(!_mR._){var _mS=_mR.a,_mT=E(_mQ);return (_mT._==0)?_mS>_mT.a:I_compareInt(_mT.a,_mS)<0;}else{var _mU=_mR.a,_mV=E(_mQ);return (_mV._==0)?I_compareInt(_mU,_mV.a)>0:I_compare(_mU,_mV.a)>0;}},_mW=0,_mX=function(_mY,_mZ){return E(_mY)==E(_mZ);},_n0=function(_n1){return new F(function(){return _mX(_mW,_n1);});},_n2=new T2(0,E(_aI),E(_lz)),_n3=new T1(1,_n2),_n4=new T1(0,-2147483648),_n5=new T1(0,2147483647),_n6=function(_n7,_n8,_n9){var _na=E(_n9);if(!_na._){return new T1(1,new T(function(){var _nb=B(_my(_na));return new T2(0,E(_nb.a),E(_nb.b));}));}else{var _nc=E(_na.c);if(!_nc._){return new T1(1,new T(function(){var _nd=B(_my(_na));return new T2(0,E(_nd.a),E(_nd.b));}));}else{var _ne=_nc.a;if(!B(_mO(_ne,_n5))){if(!B(_lZ(_ne,_n4))){var _nf=function(_ng){var _nh=_ng+B(_c7(_ne))|0;return (_nh<=(E(_n8)+3|0))?(_nh>=(E(_n7)-3|0))?new T1(1,new T(function(){var _ni=B(_my(_na));return new T2(0,E(_ni.a),E(_ni.b));})):E(_n3):__Z;},_nj=B(_mK(_n0,_na.a));if(!_nj._){var _nk=E(_na.b);if(!_nk._){return E(_n3);}else{var _nl=B(_53(_n0,_nk.a));if(!E(_nl.b)._){return E(_n3);}else{return new F(function(){return _nf( -B(_ai(_nl.a,0)));});}}}else{return new F(function(){return _nf(B(_ai(_nj,0)));});}}else{return __Z;}}else{return __Z;}}}},_nm=function(_nn,_no){return new T0(2);},_np=new T1(0,1),_nq=function(_nr,_ns){var _nt=E(_nr);if(!_nt._){var _nu=_nt.a,_nv=E(_ns);if(!_nv._){var _nw=_nv.a;return (_nu!=_nw)?(_nu>_nw)?2:0:1;}else{var _nx=I_compareInt(_nv.a,_nu);return (_nx<=0)?(_nx>=0)?1:2:0;}}else{var _ny=_nt.a,_nz=E(_ns);if(!_nz._){var _nA=I_compareInt(_ny,_nz.a);return (_nA>=0)?(_nA<=0)?1:2:0;}else{var _nB=I_compare(_ny,_nz.a);return (_nB>=0)?(_nB<=0)?1:2:0;}}},_nC=function(_nD,_nE){var _nF=E(_nD);return (_nF._==0)?_nF.a*Math.pow(2,_nE):I_toNumber(_nF.a)*Math.pow(2,_nE);},_nG=function(_nH,_nI){while(1){var _nJ=E(_nH);if(!_nJ._){var _nK=E(_nJ.a);if(_nK==(-2147483648)){_nH=new T1(1,I_fromInt(-2147483648));continue;}else{var _nL=E(_nI);if(!_nL._){var _nM=_nL.a;return new T2(0,new T1(0,quot(_nK,_nM)),new T1(0,_nK%_nM));}else{_nH=new T1(1,I_fromInt(_nK));_nI=_nL;continue;}}}else{var _nN=E(_nI);if(!_nN._){_nH=_nJ;_nI=new T1(1,I_fromInt(_nN.a));continue;}else{var _nO=I_quotRem(_nJ.a,_nN.a);return new T2(0,new T1(1,_nO.a),new T1(1,_nO.b));}}}},_nP=new T1(0,0),_nQ=function(_nR,_nS,_nT){if(!B(_kQ(_nT,_nP))){var _nU=B(_nG(_nS,_nT)),_nV=_nU.a;switch(B(_nq(B(_46(_nU.b,1)),_nT))){case 0:return new F(function(){return _nC(_nV,_nR);});break;case 1:if(!(B(_c7(_nV))&1)){return new F(function(){return _nC(_nV,_nR);});}else{return new F(function(){return _nC(B(_a3(_nV,_np)),_nR);});}break;default:return new F(function(){return _nC(B(_a3(_nV,_np)),_nR);});}}else{return E(_kP);}},_nW=function(_nX){var _nY=function(_nZ,_o0){while(1){if(!B(_lZ(_nZ,_nX))){if(!B(_mO(_nZ,_nX))){if(!B(_kQ(_nZ,_nX))){return new F(function(){return _5p("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2");});}else{return E(_o0);}}else{return _o0-1|0;}}else{var _o1=B(_46(_nZ,1)),_o2=_o0+1|0;_nZ=_o1;_o0=_o2;continue;}}};return new F(function(){return _nY(_a1,0);});},_o3=function(_o4){var _o5=E(_o4);if(!_o5._){var _o6=_o5.a>>>0;if(!_o6){return -1;}else{var _o7=function(_o8,_o9){while(1){if(_o8>=_o6){if(_o8<=_o6){if(_o8!=_o6){return new F(function(){return _5p("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_o9);}}else{return _o9-1|0;}}else{var _oa=imul(_o8,2)>>>0,_ob=_o9+1|0;_o8=_oa;_o9=_ob;continue;}}};return new F(function(){return _o7(1,0);});}}else{return new F(function(){return _nW(_o5);});}},_oc=function(_od){var _oe=E(_od);if(!_oe._){var _of=_oe.a>>>0;if(!_of){return new T2(0,-1,0);}else{var _og=function(_oh,_oi){while(1){if(_oh>=_of){if(_oh<=_of){if(_oh!=_of){return new F(function(){return _5p("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_oi);}}else{return _oi-1|0;}}else{var _oj=imul(_oh,2)>>>0,_ok=_oi+1|0;_oh=_oj;_oi=_ok;continue;}}};return new T2(0,B(_og(1,0)),(_of&_of-1>>>0)>>>0&4294967295);}}else{var _ol=_oe.a;return new T2(0,B(_o3(_oe)),I_compareInt(I_and(_ol,I_sub(_ol,I_fromInt(1))),0));}},_om=function(_on,_oo){while(1){var _op=E(_on);if(!_op._){var _oq=_op.a,_or=E(_oo);if(!_or._){return new T1(0,(_oq>>>0&_or.a>>>0)>>>0&4294967295);}else{_on=new T1(1,I_fromInt(_oq));_oo=_or;continue;}}else{var _os=E(_oo);if(!_os._){_on=_op;_oo=new T1(1,I_fromInt(_os.a));continue;}else{return new T1(1,I_and(_op.a,_os.a));}}}},_ot=new T1(0,2),_ou=function(_ov,_ow){var _ox=E(_ov);if(!_ox._){var _oy=(_ox.a>>>0&(2<<_ow>>>0)-1>>>0)>>>0,_oz=1<<_ow>>>0;return (_oz<=_oy)?(_oz>=_oy)?1:2:0;}else{var _oA=B(_om(_ox,B(_lE(B(_46(_ot,_ow)),_a1)))),_oB=B(_46(_a1,_ow));return (!B(_mO(_oB,_oA)))?(!B(_lZ(_oB,_oA)))?1:2:0;}},_oC=function(_oD,_oE){while(1){var _oF=E(_oD);if(!_oF._){_oD=new T1(1,I_fromInt(_oF.a));continue;}else{return new T1(1,I_shiftRight(_oF.a,_oE));}}},_oG=function(_oH,_oI,_oJ,_oK){var _oL=B(_oc(_oK)),_oM=_oL.a;if(!E(_oL.b)){var _oN=B(_o3(_oJ));if(_oN<((_oM+_oH|0)-1|0)){var _oO=_oM+(_oH-_oI|0)|0;if(_oO>0){if(_oO>_oN){if(_oO<=(_oN+1|0)){if(!E(B(_oc(_oJ)).b)){return 0;}else{return new F(function(){return _nC(_np,_oH-_oI|0);});}}else{return 0;}}else{var _oP=B(_oC(_oJ,_oO));switch(B(_ou(_oJ,_oO-1|0))){case 0:return new F(function(){return _nC(_oP,_oH-_oI|0);});break;case 1:if(!(B(_c7(_oP))&1)){return new F(function(){return _nC(_oP,_oH-_oI|0);});}else{return new F(function(){return _nC(B(_a3(_oP,_np)),_oH-_oI|0);});}break;default:return new F(function(){return _nC(B(_a3(_oP,_np)),_oH-_oI|0);});}}}else{return new F(function(){return _nC(_oJ,(_oH-_oI|0)-_oO|0);});}}else{if(_oN>=_oI){var _oQ=B(_oC(_oJ,(_oN+1|0)-_oI|0));switch(B(_ou(_oJ,_oN-_oI|0))){case 0:return new F(function(){return _nC(_oQ,((_oN-_oM|0)+1|0)-_oI|0);});break;case 2:return new F(function(){return _nC(B(_a3(_oQ,_np)),((_oN-_oM|0)+1|0)-_oI|0);});break;default:if(!(B(_c7(_oQ))&1)){return new F(function(){return _nC(_oQ,((_oN-_oM|0)+1|0)-_oI|0);});}else{return new F(function(){return _nC(B(_a3(_oQ,_np)),((_oN-_oM|0)+1|0)-_oI|0);});}}}else{return new F(function(){return _nC(_oJ, -_oM);});}}}else{var _oR=B(_o3(_oJ))-_oM|0,_oS=function(_oT){var _oU=function(_oV,_oW){if(!B(_ca(B(_46(_oW,_oI)),_oV))){return new F(function(){return _nQ(_oT-_oI|0,_oV,_oW);});}else{return new F(function(){return _nQ((_oT-_oI|0)+1|0,_oV,B(_46(_oW,1)));});}};if(_oT>=_oI){if(_oT!=_oI){return new F(function(){return _oU(_oJ,new T(function(){return B(_46(_oK,_oT-_oI|0));}));});}else{return new F(function(){return _oU(_oJ,_oK);});}}else{return new F(function(){return _oU(new T(function(){return B(_46(_oJ,_oI-_oT|0));}),_oK);});}};if(_oH>_oR){return new F(function(){return _oS(_oH);});}else{return new F(function(){return _oS(_oR);});}}},_oX=new T(function(){return 0/0;}),_oY=new T(function(){return -1/0;}),_oZ=new T(function(){return 1/0;}),_p0=0,_p1=function(_p2,_p3){if(!B(_kQ(_p3,_nP))){if(!B(_kQ(_p2,_nP))){if(!B(_lZ(_p2,_nP))){return new F(function(){return _oG(-1021,53,_p2,_p3);});}else{return  -B(_oG(-1021,53,B(_ad(_p2)),_p3));}}else{return E(_p0);}}else{return (!B(_kQ(_p2,_nP)))?(!B(_lZ(_p2,_nP)))?E(_oZ):E(_oY):E(_oX);}},_p4=function(_p5){var _p6=E(_p5);switch(_p6._){case 3:var _p7=_p6.a;return (!B(_7D(_p7,_kf)))?(!B(_7D(_p7,_ke)))?E(_nm):E(_kb):E(_k7);case 5:var _p8=B(_n6(_kh,_kg,_p6.a));if(!_p8._){return E(_k7);}else{var _p9=new T(function(){var _pa=E(_p8.a);return B(_p1(_pa.a,_pa.b));});return function(_pb,_pc){return new F(function(){return A1(_pc,_p9);});};}break;default:return E(_nm);}},_pd=function(_pe){var _pf=function(_pg){return E(new T2(3,_pe,_89));};return new T1(1,function(_ph){return new F(function(){return A2(_hq,_ph,_pf);});});},_pi=new T(function(){return B(A3(_jL,_p4,_jg,_pd));}),_pj=function(_pk,_pl){while(1){var _pm=E(_pk);if(!_pm._){return E(_pl);}else{_pk=_pm.b;_pl=_pm.a;continue;}}},_pn=function(_po){var _pp=E(_po);if(!_pp._){return __Z;}else{var _pq=_pp.a,_pr=new T(function(){if(E(B(_pj(_pq,_6C)))==37){var _ps=B(_6D(B(_6K(_pi,new T(function(){return B(_6y(_pq));})))));if(!_ps._){return E(_6X);}else{if(!E(_ps.b)._){return E(_ps.a)/100;}else{return E(_6V);}}}else{var _pt=B(_6D(B(_6K(_pi,_pq))));if(!_pt._){return E(_6X);}else{if(!E(_pt.b)._){return E(_pt.a);}else{return E(_6V);}}}});return new T1(1,_pr);}},_pu=function(_pv,_){var _pw=E(_pv);if(!_pw._){return E(_5t);}else{var _px=_pw.a,_py=E(_pw.b);if(!_py._){return E(_5t);}else{var _pz=_py.a,_pA=E(_py.b);if(!_pA._){return E(_5t);}else{var _pB=_pA.a,_pC=E(_pA.b);if(!_pC._){return E(_5t);}else{if(!E(_pC.b)._){var _pD=function(_){var _pE=E(_4t),_pF=E(_4u),_pG=__app2(_pF,E(_px),_pE),_pH=__app2(_pF,E(_pz),_pE),_pI=__app2(_pF,E(_pB),_pE),_pJ=B(_pn(new T1(1,new T(function(){var _pK=String(_pG);return fromJSStr(_pK);}))));if(!_pJ._){return _2t;}else{var _pL=B(_pn(new T1(1,new T(function(){var _pM=String(_pH);return fromJSStr(_pM);}))));if(!_pL._){return _2t;}else{var _pN=B(_pn(new T1(1,new T(function(){var _pO=String(_pI);return fromJSStr(_pO);}))));if(!_pN._){return _2t;}else{var _pP=__app3(E(_4v),E(_pC.a),toJSStr(E(_5u)),toJSStr(B(_4a(2,Math.log(E(_pJ.a)/E(_pL.a))/Math.log(1+E(_pN.a))))));return new F(function(){return _35(_);});}}}},_pQ=B(A(_5W,[_39,_38,_34,_px,_4s,function(_pR,_){return new F(function(){return _pD(_);});},_])),_pS=B(A(_5W,[_39,_38,_34,_pz,_4s,function(_pT,_){return new F(function(){return _pD(_);});},_]));return new F(function(){return A(_5W,[_39,_38,_2H,_pB,_4r,function(_pU,_){return new F(function(){return _pD(_);});},_]);});}else{return E(_5t);}}}}}},_pV=new T(function(){return B(unCStr("result"));}),_pW=new T2(1,_pV,_u),_pX=new T(function(){return B(unCStr("r"));}),_pY=new T2(1,_pX,_pW),_pZ=new T(function(){return B(unCStr("y"));}),_q0=new T2(1,_pZ,_pY),_q1=new T(function(){return B(unCStr("x"));}),_q2=new T2(1,_q1,_q0),_q3=function(_q4){return new F(function(){return toJSStr(E(_q4));});},_q5=new T(function(){return B(_an(_q3,_q2));}),_q6=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_q7=new T(function(){return B(unCStr("Maybe.fromJust: Nothing"));}),_q8=new T(function(){return B(err(_q7));}),_q9=function(_qa){var _qb=E(_qa);return (_qb._==0)?E(_q8):E(_qb.a);},_qc=function(_qd,_qe){while(1){var _qf=B((function(_qg,_qh){var _qi=E(_qg);if(!_qi._){return __Z;}else{var _qj=_qi.b,_qk=E(_qh);if(!_qk._){return __Z;}else{var _ql=_qk.b;if(!E(_qk.a)._){return new T2(1,_qi.a,new T(function(){return B(_qc(_qj,_ql));}));}else{_qd=_qj;_qe=_ql;return __continue;}}}})(_qd,_qe));if(_qf!=__continue){return _qf;}}},_qm=new T(function(){return B(unAppCStr("[]",_u));}),_qn=new T2(1,_1Q,_u),_qo=function(_qp){var _qq=E(_qp);if(!_qq._){return E(_qn);}else{var _qr=new T(function(){return B(_O(fromJSStr(E(_qq.a)),new T(function(){return B(_qo(_qq.b));},1)));});return new T2(1,_1P,_qr);}},_qs=function(_qt,_qu){var _qv=new T(function(){var _qw=B(_qc(_qt,_qu));if(!_qw._){return E(_qm);}else{var _qx=new T(function(){return B(_O(fromJSStr(E(_qw.a)),new T(function(){return B(_qo(_qw.b));},1)));});return new T2(1,_1R,_qx);}});return new F(function(){return err(B(unAppCStr("Elements with the following IDs could not be found: ",_qv)));});},_qy=function(_qz){while(1){var _qA=E(_qz);if(!_qA._){return false;}else{if(!E(_qA.a)._){return true;}else{_qz=_qA.b;continue;}}}},_qB=function(_qC,_qD,_qE){var _qF=B(_5x(_qC)),_qG=function(_qH){if(!B(_qy(_qH))){return new F(function(){return A1(_qE,new T(function(){return B(_an(_q9,_qH));}));});}else{return new F(function(){return _qs(_qD,_qH);});}},_qI=new T(function(){var _qJ=new T(function(){return B(A2(_5U,_qF,_u));}),_qK=function(_qL){var _qM=E(_qL);if(!_qM._){return E(_qJ);}else{var _qN=new T(function(){return B(_qK(_qM.b));}),_qO=function(_qP){return new F(function(){return A3(_5z,_qF,_qN,function(_qQ){return new F(function(){return A2(_5U,_qF,new T2(1,_qP,_qQ));});});});},_qR=new T(function(){var _qS=function(_){var _qT=__app1(E(_q6),E(_qM.a)),_qU=__eq(_qT,E(_5P));return (E(_qU)==0)?new T1(1,_qT):_2a;};return B(A2(_5Q,_qC,_qS));});return new F(function(){return A3(_5z,_qF,_qR,_qO);});}};return B(_qK(_qD));});return new F(function(){return A3(_5z,_qF,_qI,_qG);});},_qV=new T(function(){return B(_qB(_2s,_q5,_pu));});
var hasteMain = function() {B(A(_qV, [0]));};window.onload = hasteMain;