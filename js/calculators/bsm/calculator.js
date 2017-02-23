"use strict";
var __haste_prog_id = '33733583e85e36bf01354248eb47bc92f4a534cb1155626b943472a43ab0c019';
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

var _0=function(_1,_2,_){var _3=B(A1(_1,_)),_4=B(A1(_2,_));return new T(function(){return B(A1(_3,_4));});},_5=function(_6,_7,_){var _8=B(A1(_7,_));return new T(function(){return B(A1(_6,_8));});},_9=function(_a,_){return _a;},_b=function(_c,_d,_){var _e=B(A1(_c,_));return C > 19 ? new F(function(){return A1(_d,_);}) : (++C,A1(_d,_));},_f=new T(function(){return unCStr("base");}),_g=new T(function(){return unCStr("GHC.IO.Exception");}),_h=new T(function(){return unCStr("IOException");}),_i=function(_j){return E(new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_f,_g,_h),__Z,__Z));},_k=function(_l){return E(E(_l).a);},_m=function(_n,_o,_p){var _q=B(A1(_n,_)),_r=B(A1(_o,_)),_s=hs_eqWord64(_q.a,_r.a);if(!_s){return __Z;}else{var _t=hs_eqWord64(_q.b,_r.b);return (!_t)?__Z:new T1(1,_p);}},_u=new T(function(){return unCStr(": ");}),_v=new T(function(){return unCStr(")");}),_w=new T(function(){return unCStr(" (");}),_x=function(_y,_z){var _A=E(_y);return (_A._==0)?E(_z):new T2(1,_A.a,new T(function(){return _x(_A.b,_z);}));},_B=new T(function(){return unCStr("interrupted");}),_C=new T(function(){return unCStr("system error");}),_D=new T(function(){return unCStr("unsatisified constraints");}),_E=new T(function(){return unCStr("user error");}),_F=new T(function(){return unCStr("permission denied");}),_G=new T(function(){return unCStr("illegal operation");}),_H=new T(function(){return unCStr("end of file");}),_I=new T(function(){return unCStr("resource exhausted");}),_J=new T(function(){return unCStr("resource busy");}),_K=new T(function(){return unCStr("does not exist");}),_L=new T(function(){return unCStr("already exists");}),_M=new T(function(){return unCStr("resource vanished");}),_N=new T(function(){return unCStr("timeout");}),_O=new T(function(){return unCStr("unsupported operation");}),_P=new T(function(){return unCStr("hardware fault");}),_Q=new T(function(){return unCStr("inappropriate type");}),_R=new T(function(){return unCStr("invalid argument");}),_S=new T(function(){return unCStr("failed");}),_T=new T(function(){return unCStr("protocol error");}),_U=function(_V,_W){switch(E(_V)){case 0:return _x(_L,_W);case 1:return _x(_K,_W);case 2:return _x(_J,_W);case 3:return _x(_I,_W);case 4:return _x(_H,_W);case 5:return _x(_G,_W);case 6:return _x(_F,_W);case 7:return _x(_E,_W);case 8:return _x(_D,_W);case 9:return _x(_C,_W);case 10:return _x(_T,_W);case 11:return _x(_S,_W);case 12:return _x(_R,_W);case 13:return _x(_Q,_W);case 14:return _x(_P,_W);case 15:return _x(_O,_W);case 16:return _x(_N,_W);case 17:return _x(_M,_W);default:return _x(_B,_W);}},_X=new T(function(){return unCStr("}");}),_Y=new T(function(){return unCStr("{handle: ");}),_Z=function(_10,_11,_12,_13,_14,_15){var _16=new T(function(){var _17=new T(function(){var _18=new T(function(){var _19=E(_13);if(!_19._){return E(_15);}else{var _1a=new T(function(){return _x(_19,new T(function(){return _x(_v,_15);},1));},1);return _x(_w,_1a);}},1);return _U(_11,_18);}),_1b=E(_12);if(!_1b._){return E(_17);}else{return _x(_1b,new T(function(){return _x(_u,_17);},1));}}),_1c=E(_14);if(!_1c._){var _1d=E(_10);if(!_1d._){return E(_16);}else{var _1e=E(_1d.a);if(!_1e._){var _1f=new T(function(){var _1g=new T(function(){return _x(_X,new T(function(){return _x(_u,_16);},1));},1);return _x(_1e.a,_1g);},1);return _x(_Y,_1f);}else{var _1h=new T(function(){var _1i=new T(function(){return _x(_X,new T(function(){return _x(_u,_16);},1));},1);return _x(_1e.a,_1i);},1);return _x(_Y,_1h);}}}else{return _x(_1c.a,new T(function(){return _x(_u,_16);},1));}},_1j=function(_1k){var _1l=E(_1k);return _Z(_1l.a,_1l.b,_1l.c,_1l.d,_1l.f,__Z);},_1m=function(_1n,_1o){var _1p=E(_1n);return _Z(_1p.a,_1p.b,_1p.c,_1p.d,_1p.f,_1o);},_1q=function(_1r,_1s,_1t){var _1u=E(_1s);if(!_1u._){return unAppCStr("[]",_1t);}else{var _1v=new T(function(){var _1w=new T(function(){var _1x=function(_1y){var _1z=E(_1y);if(!_1z._){return E(new T2(1,93,_1t));}else{var _1A=new T(function(){return B(A2(_1r,_1z.a,new T(function(){return _1x(_1z.b);})));});return new T2(1,44,_1A);}};return _1x(_1u.b);});return B(A2(_1r,_1u.a,_1w));});return new T2(1,91,_1v);}},_1B=new T(function(){return new T5(0,_i,new T3(0,function(_1C,_1D,_1E){var _1F=E(_1D);return _Z(_1F.a,_1F.b,_1F.c,_1F.d,_1F.f,_1E);},_1j,function(_1G,_1H){return _1q(_1m,_1G,_1H);}),function(_1I){return new T2(0,_1B,_1I);},function(_1J){var _1K=E(_1J);return _m(_k(_1K.a),_i,_1K.b);},_1j);}),_1L=new T(function(){return E(_1B);}),_1M=function(_1N){return E(E(_1N).c);},_1O=function(_1P){return new T6(0,__Z,7,__Z,_1P,__Z,__Z);},_1Q=function(_1R,_){var _1S=new T(function(){return B(A2(_1M,_1L,new T(function(){return B(A1(_1O,_1R));})));});return die(_1S);},_1T=function(_1U,_){return _1Q(_1U,_);},_1V=function(_1W){return E(_1W);},_1X=new T2(0,new T5(0,new T5(0,new T2(0,_5,function(_1Y,_1Z,_){var _20=B(A1(_1Z,_));return _1Y;}),_9,_0,_b,function(_21,_22,_){var _23=B(A1(_21,_)),_24=B(A1(_22,_));return _23;}),function(_25,_26,_){var _27=B(A1(_25,_));return C > 19 ? new F(function(){return A2(_26,_27,_);}) : (++C,A2(_26,_27,_));},_b,_9,function(_28){return C > 19 ? new F(function(){return A1(_1T,_28);}) : (++C,A1(_1T,_28));}),_1V),_29=function(_){return 0;},_2a=new T2(0,function(_2b){switch(E(_2b)){case 0:return "load";case 1:return "unload";case 2:return "change";case 3:return "focus";case 4:return "blur";case 5:return "submit";default:return "scroll";}},function(_2c,_2d,_){return _29(_);}),_2e=function(_2f,_){var _2g=_2f["keyCode"],_2h=_2f["ctrlKey"],_2i=_2f["altKey"],_2j=_2f["shiftKey"],_2k=_2f["metaKey"];return new T(function(){var _2l=Number(_2g),_2m=jsTrunc(_2l);return new T5(0,_2m,E(_2h),E(_2i),E(_2j),E(_2k));});},_2n=new T2(0,function(_2o){switch(E(_2o)){case 0:return "keypress";case 1:return "keyup";default:return "keydown";}},function(_2p,_2q,_){return _2e(E(_2q),_);}),_2r=function(_){return 0;},_2s=new T2(0,_1V,function(_2t,_){return new T1(1,_2t);}),_2u=new T2(0,_1X,_9),_2v=(function(e,p){var x = e[p];return typeof x === 'undefined' ? '' : x.toString();}),_2w=function(_2x,_2y){while(1){var _2z=E(_2x);if(!_2z._){return E(_2y);}else{var _2A=new T2(1,_2z.a,_2y);_2x=_2z.b;_2y=_2A;continue;}}},_2B=function(_2C){return _2w(_2C,__Z);},_2D=function(_2E,_2F,_2G){while(1){var _2H=(function(_2I,_2J,_2K){var _2L=E(_2I);if(!_2L._){return new T2(0,new T(function(){return _2B(_2J);}),new T(function(){return _2B(_2K);}));}else{var _2M=_2J,_2N=new T2(1,_2L.a,_2K);_2E=_2L.b;_2F=_2M;_2G=_2N;return __continue;}})(_2E,_2F,_2G);if(_2H!=__continue){return _2H;}}},_2O=function(_2P,_2Q,_2R){while(1){var _2S=(function(_2T,_2U,_2V){var _2W=E(_2T);if(!_2W._){return new T2(0,new T(function(){return _2B(_2U);}),new T(function(){return _2B(_2V);}));}else{var _2X=_2W.b,_2Y=E(_2W.a);if(_2Y==46){return _2D(_2X,_2U,__Z);}else{var _2Z=new T2(1,_2Y,_2U),_30=_2V;_2P=_2X;_2Q=_2Z;_2R=_30;return __continue;}}})(_2P,_2Q,_2R);if(_2S!=__continue){return _2S;}}},_31=function(_32,_33){var _34=E(_33);if(!_34._){return __Z;}else{var _35=_34.a,_36=E(_32);return (_36==1)?new T2(1,_35,__Z):new T2(1,_35,new T(function(){return _31(_36-1|0,_34.b);}));}},_37=function(_38){var _39=I_decodeDouble(_38);return new T2(0,new T1(1,_39.b),_39.a);},_3a=function(_3b){var _3c=E(_3b);if(!_3c._){return _3c.a;}else{return I_toNumber(_3c.a);}},_3d=function(_3e){return new T1(0,_3e);},_3f=function(_3g){var _3h=hs_intToInt64(2147483647),_3i=hs_leInt64(_3g,_3h);if(!_3i){return new T1(1,I_fromInt64(_3g));}else{var _3j=hs_intToInt64(-2147483648),_3k=hs_geInt64(_3g,_3j);if(!_3k){return new T1(1,I_fromInt64(_3g));}else{var _3l=hs_int64ToInt(_3g);return _3d(_3l);}}},_3m=function(_3n){var _3o=hs_intToInt64(_3n);return E(_3o);},_3p=function(_3q){var _3r=E(_3q);if(!_3r._){return _3m(_3r.a);}else{return I_toInt64(_3r.a);}},_3s=function(_3t,_3u){while(1){var _3v=E(_3t);if(!_3v._){_3t=new T1(1,I_fromInt(_3v.a));continue;}else{return new T1(1,I_shiftLeft(_3v.a,_3u));}}},_3w=function(_3x,_3y){var _3z=Math.pow(10,_3x),_3A=rintDouble(_3y*_3z),_3B=_37(_3A),_3C=_3B.a,_3D=_3B.b,_3E=function(_3F,_3G){var _3H=new T(function(){return unAppCStr(".",new T(function(){if(0>=_3x){return __Z;}else{return _31(_3x,_3G);}}));},1);return _x(_3F,_3H);};if(_3D>=0){var _3I=jsShow(_3a(_3s(_3C,_3D))/_3z),_3J=_2O(fromJSStr(_3I),__Z,__Z);return _3E(_3J.a,_3J.b);}else{var _3K=hs_uncheckedIShiftRA64(_3p(_3C), -_3D),_3L=jsShow(_3a(_3f(_3K))/_3z),_3M=_2O(fromJSStr(_3L),__Z,__Z);return _3E(_3M.a,_3M.b);}},_3N=new T(function(){return unCStr("</td></tr> ");}),_3O=function(_3P,_3Q){var _3R=new T(function(){var _3S=new T(function(){return unAppCStr(":</td><td>",new T(function(){return _x(_3w(4,E(_3Q)),_3N);}));},1);return _x(_3P,_3S);});return unAppCStr("<tr><td>",_3R);},_3T=function(_3U){var _3V=E(_3U);if(!_3V._){return __Z;}else{var _3W=E(_3V.a);return _x(_3O(_3W.a,_3W.b),new T(function(){return _3T(_3V.b);},1));}},_3X=function(_3Y){var _3Z=E(_3Y);if(!_3Z._){return __Z;}else{var _40=E(_3Z.a);return _x(_3O(_40.a,_40.b),new T(function(){return _3X(_3Z.b);},1));}},_41=(function(e,p,v){e[p] = v;}),_42=new T(function(){return unCStr("base");}),_43=new T(function(){return unCStr("Control.Exception.Base");}),_44=new T(function(){return unCStr("PatternMatchFail");}),_45=function(_46){return E(new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_42,_43,_44),__Z,__Z));},_47=function(_48){return E(E(_48).a);},_49=function(_4a,_4b){return _x(E(_4a).a,_4b);},_4c=new T(function(){return new T5(0,_45,new T3(0,function(_4d,_4e,_4f){return _x(E(_4e).a,_4f);},_47,function(_4g,_4h){return _1q(_49,_4g,_4h);}),function(_4i){return new T2(0,_4c,_4i);},function(_4j){var _4k=E(_4j);return _m(_k(_4k.a),_45,_4k.b);},_47);}),_4l=new T(function(){return unCStr("Non-exhaustive patterns in");}),_4m=function(_4n,_4o){return die(new T(function(){return B(A2(_1M,_4o,_4n));}));},_4p=function(_4q,_4r){return _4m(_4q,_4r);},_4s=function(_4t,_4u){var _4v=E(_4u);if(!_4v._){return new T2(0,__Z,__Z);}else{var _4w=_4v.a;if(!B(A1(_4t,_4w))){return new T2(0,__Z,_4v);}else{var _4x=new T(function(){var _4y=_4s(_4t,_4v.b);return new T2(0,_4y.a,_4y.b);});return new T2(0,new T2(1,_4w,new T(function(){return E(E(_4x).a);})),new T(function(){return E(E(_4x).b);}));}}},_4z=new T(function(){return unCStr("\n");}),_4A=function(_4B){return (E(_4B)==124)?false:true;},_4C=function(_4D,_4E){var _4F=_4s(_4A,unCStr(_4D)),_4G=_4F.a,_4H=function(_4I,_4J){var _4K=new T(function(){var _4L=new T(function(){return _x(_4E,new T(function(){return _x(_4J,_4z);},1));});return unAppCStr(": ",_4L);},1);return _x(_4I,_4K);},_4M=E(_4F.b);if(!_4M._){return _4H(_4G,__Z);}else{if(E(_4M.a)==124){return _4H(_4G,new T2(1,32,_4M.b));}else{return _4H(_4G,__Z);}}},_4N=function(_4O){return _4p(new T1(0,new T(function(){return _4C(_4O,_4l);})),_4c);},_4P=new T(function(){return B((function(_4Q){return C > 19 ? new F(function(){return _4N("calculator.hs:(13,1)-(30,39)|function calculator");}) : (++C,_4N("calculator.hs:(13,1)-(30,39)|function calculator"));})(_));}),_4R=new T(function(){return unCStr("innerHTML");}),_4S=function(_4T){return E(E(_4T).a);},_4U=function(_4V){return E(E(_4V).a);},_4W=function(_4X){return E(E(_4X).b);},_4Y=function(_4Z){return E(E(_4Z).a);},_50=function(_51){return E(E(_51).b);},_52=function(_53){return E(E(_53).a);},_54=function(_55){var _56=B(A1(_55,_));return E(_56);},_57=new T(function(){return _54(function(_){return nMV(__Z);});}),_58=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_59=new T(function(){return _54(function(_){return __jsNull();});}),_5a=function(_5b){return E(E(_5b).b);},_5c=function(_5d){return E(E(_5d).b);},_5e=function(_5f){return E(E(_5f).d);},_5g=function(_5h,_5i,_5j,_5k,_5l,_5m){var _5n=_4S(_5h),_5o=_4U(_5n),_5p=new T(function(){return _5a(_5n);}),_5q=new T(function(){return _5e(_5o);}),_5r=new T(function(){return B(A2(_4Y,_5i,_5k));}),_5s=new T(function(){return B(A2(_52,_5j,_5l));}),_5t=function(_5u){return C > 19 ? new F(function(){return A1(_5q,new T3(0,_5s,_5r,_5u));}) : (++C,A1(_5q,new T3(0,_5s,_5r,_5u)));},_5v=function(_5w){var _5x=new T(function(){var _5y=new T(function(){var _5z=__createJSFunc(2,function(_5A,_){var _5B=B(A2(E(_5w),_5A,_));return _59;}),_5C=_5z;return function(_){return _58(E(_5r),E(_5s),_5C);};});return B(A1(_5p,_5y));});return C > 19 ? new F(function(){return A3(_4W,_5o,_5x,_5t);}) : (++C,A3(_4W,_5o,_5x,_5t));},_5D=new T(function(){var _5E=new T(function(){return _5a(_5n);}),_5F=function(_5G){var _5H=new T(function(){return B(A1(_5E,function(_){var _=wMV(E(_57),new T1(1,_5G));return C > 19 ? new F(function(){return A(_50,[_5j,_5l,_5G,_]);}) : (++C,A(_50,[_5j,_5l,_5G,_]));}));});return C > 19 ? new F(function(){return A3(_4W,_5o,_5H,_5m);}) : (++C,A3(_4W,_5o,_5H,_5m));};return B(A2(_5c,_5h,_5F));});return C > 19 ? new F(function(){return A3(_4W,_5o,_5D,_5v);}) : (++C,A3(_4W,_5o,_5D,_5v));},_5I=new T(function(){return unCStr("CHF");}),_5J=function(_5K,_5L){var _5M=E(_5L);return (_5M._==0)?__Z:new T2(1,_5K,new T(function(){return _5J(_5M.a,_5M.b);}));},_5N=new T(function(){return unCStr(": empty list");}),_5O=new T(function(){return unCStr("Prelude.");}),_5P=function(_5Q){return err(_x(_5O,new T(function(){return _x(_5Q,_5N);},1)));},_5R=new T(function(){return _5P(new T(function(){return unCStr("init");}));}),_5S=function(_5T){var _5U=E(_5T);if(!_5U._){return E(_5R);}else{return _5J(_5U.a,_5U.b);}},_5V=new T(function(){return _5P(new T(function(){return unCStr("last");}));}),_5W=function(_5X){while(1){var _5Y=(function(_5Z){var _60=E(_5Z);if(!_60._){return __Z;}else{var _61=_60.b,_62=E(_60.a);if(!E(_62.b)._){return new T2(1,_62.a,new T(function(){return _5W(_61);}));}else{_5X=_61;return __continue;}}})(_5X);if(_5Y!=__continue){return _5Y;}}},_63=function(_64,_65){while(1){var _66=(function(_67,_68){var _69=E(_67);switch(_69._){case 0:var _6a=E(_68);if(!_6a._){return __Z;}else{_64=B(A1(_69.a,_6a.a));_65=_6a.b;return __continue;}break;case 1:var _6b=B(A1(_69.a,_68)),_6c=_68;_64=_6b;_65=_6c;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_69.a,_68),new T(function(){return _63(_69.b,_68);}));default:return E(_69.a);}})(_64,_65);if(_66!=__continue){return _66;}}},_6d=new T(function(){return err(new T(function(){return unCStr("Prelude.read: ambiguous parse");}));}),_6e=new T(function(){return err(new T(function(){return unCStr("Prelude.read: no parse");}));}),_6f=new T(function(){return B(_4N("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_6g=function(_6h,_6i){var _6j=function(_6k){var _6l=E(_6i);if(_6l._==3){return new T2(3,_6l.a,new T(function(){return _6g(_6h,_6l.b);}));}else{var _6m=E(_6h);if(_6m._==2){return _6l;}else{if(_6l._==2){return _6m;}else{var _6n=function(_6o){if(_6l._==4){var _6p=function(_6q){return new T1(4,new T(function(){return _x(_63(_6m,_6q),_6l.a);}));};return new T1(1,_6p);}else{if(_6m._==1){var _6r=_6m.a;if(!_6l._){return new T1(1,function(_6s){return _6g(B(A1(_6r,_6s)),_6l);});}else{var _6t=function(_6u){return _6g(B(A1(_6r,_6u)),new T(function(){return B(A1(_6l.a,_6u));}));};return new T1(1,_6t);}}else{if(!_6l._){return E(_6f);}else{var _6v=function(_6w){return _6g(_6m,new T(function(){return B(A1(_6l.a,_6w));}));};return new T1(1,_6v);}}}};switch(_6m._){case 1:if(_6l._==4){var _6x=function(_6y){return new T1(4,new T(function(){return _x(_63(B(A1(_6m.a,_6y)),_6y),_6l.a);}));};return new T1(1,_6x);}else{return _6n(_);}break;case 4:var _6z=_6m.a;switch(_6l._){case 0:var _6A=function(_6B){var _6C=new T(function(){return _x(_6z,new T(function(){return _63(_6l,_6B);},1));});return new T1(4,_6C);};return new T1(1,_6A);case 1:var _6D=function(_6E){var _6F=new T(function(){return _x(_6z,new T(function(){return _63(B(A1(_6l.a,_6E)),_6E);},1));});return new T1(4,_6F);};return new T1(1,_6D);default:return new T1(4,new T(function(){return _x(_6z,_6l.a);}));}break;default:return _6n(_);}}}}},_6G=E(_6h);switch(_6G._){case 0:var _6H=E(_6i);if(!_6H._){var _6I=function(_6J){return _6g(B(A1(_6G.a,_6J)),new T(function(){return B(A1(_6H.a,_6J));}));};return new T1(0,_6I);}else{return _6j(_);}break;case 3:return new T2(3,_6G.a,new T(function(){return _6g(_6G.b,_6i);}));default:return _6j(_);}},_6K=new T(function(){return unCStr("(");}),_6L=new T(function(){return unCStr(")");}),_6M=function(_6N,_6O){while(1){var _6P=E(_6N);if(!_6P._){return (E(_6O)._==0)?true:false;}else{var _6Q=E(_6O);if(!_6Q._){return false;}else{if(E(_6P.a)!=E(_6Q.a)){return false;}else{_6N=_6P.b;_6O=_6Q.b;continue;}}}}},_6R=new T2(0,function(_6S,_6T){return E(_6S)==E(_6T);},function(_6U,_6V){return E(_6U)!=E(_6V);}),_6W=function(_6X,_6Y){while(1){var _6Z=E(_6X);if(!_6Z._){return (E(_6Y)._==0)?true:false;}else{var _70=E(_6Y);if(!_70._){return false;}else{if(E(_6Z.a)!=E(_70.a)){return false;}else{_6X=_6Z.b;_6Y=_70.b;continue;}}}}},_71=function(_72,_73){return (!_6W(_72,_73))?true:false;},_74=function(_75,_76){var _77=E(_75);switch(_77._){case 0:return new T1(0,function(_78){return C > 19 ? new F(function(){return _74(B(A1(_77.a,_78)),_76);}) : (++C,_74(B(A1(_77.a,_78)),_76));});case 1:return new T1(1,function(_79){return C > 19 ? new F(function(){return _74(B(A1(_77.a,_79)),_76);}) : (++C,_74(B(A1(_77.a,_79)),_76));});case 2:return new T0(2);case 3:return _6g(B(A1(_76,_77.a)),new T(function(){return B(_74(_77.b,_76));}));default:var _7a=function(_7b){var _7c=E(_7b);if(!_7c._){return __Z;}else{var _7d=E(_7c.a);return _x(_63(B(A1(_76,_7d.a)),_7d.b),new T(function(){return _7a(_7c.b);},1));}},_7e=_7a(_77.a);return (_7e._==0)?new T0(2):new T1(4,_7e);}},_7f=new T0(2),_7g=function(_7h){return new T2(3,_7h,_7f);},_7i=function(_7j,_7k){var _7l=E(_7j);if(!_7l){return C > 19 ? new F(function(){return A1(_7k,0);}) : (++C,A1(_7k,0));}else{var _7m=new T(function(){return B(_7i(_7l-1|0,_7k));});return new T1(0,function(_7n){return E(_7m);});}},_7o=function(_7p,_7q,_7r){var _7s=new T(function(){return B(A1(_7p,_7g));}),_7t=function(_7u,_7v,_7w,_7x){while(1){var _7y=B((function(_7z,_7A,_7B,_7C){var _7D=E(_7z);switch(_7D._){case 0:var _7E=E(_7A);if(!_7E._){return C > 19 ? new F(function(){return A1(_7q,_7C);}) : (++C,A1(_7q,_7C));}else{var _7F=_7B+1|0,_7G=_7C;_7u=B(A1(_7D.a,_7E.a));_7v=_7E.b;_7w=_7F;_7x=_7G;return __continue;}break;case 1:var _7H=B(A1(_7D.a,_7A)),_7I=_7A,_7F=_7B,_7G=_7C;_7u=_7H;_7v=_7I;_7w=_7F;_7x=_7G;return __continue;case 2:return C > 19 ? new F(function(){return A1(_7q,_7C);}) : (++C,A1(_7q,_7C));break;case 3:var _7J=new T(function(){return B(_74(_7D,_7C));});return C > 19 ? new F(function(){return _7i(_7B,function(_7K){return E(_7J);});}) : (++C,_7i(_7B,function(_7K){return E(_7J);}));break;default:return C > 19 ? new F(function(){return _74(_7D,_7C);}) : (++C,_74(_7D,_7C));}})(_7u,_7v,_7w,_7x));if(_7y!=__continue){return _7y;}}};return function(_7L){return _7t(_7s,_7L,0,_7r);};},_7M=function(_7N){return C > 19 ? new F(function(){return A1(_7N,__Z);}) : (++C,A1(_7N,__Z));},_7O=function(_7P,_7Q){var _7R=function(_7S){var _7T=E(_7S);if(!_7T._){return _7M;}else{var _7U=_7T.a;if(!B(A1(_7P,_7U))){return _7M;}else{var _7V=new T(function(){return _7R(_7T.b);}),_7W=function(_7X){var _7Y=new T(function(){return B(A1(_7V,function(_7Z){return C > 19 ? new F(function(){return A1(_7X,new T2(1,_7U,_7Z));}) : (++C,A1(_7X,new T2(1,_7U,_7Z)));}));});return new T1(0,function(_80){return E(_7Y);});};return _7W;}}};return function(_81){return C > 19 ? new F(function(){return A2(_7R,_81,_7Q);}) : (++C,A2(_7R,_81,_7Q));};},_82=new T(function(){return err(new T(function(){return unCStr("valDig: Bad base");}));}),_83=function(_84,_85){var _86=function(_87,_88){var _89=E(_87);if(!_89._){var _8a=new T(function(){return B(A1(_88,__Z));});return function(_8b){return C > 19 ? new F(function(){return A1(_8b,_8a);}) : (++C,A1(_8b,_8a));};}else{var _8c=E(_89.a),_8d=function(_8e){var _8f=new T(function(){return _86(_89.b,function(_8g){return C > 19 ? new F(function(){return A1(_88,new T2(1,_8e,_8g));}) : (++C,A1(_88,new T2(1,_8e,_8g)));});}),_8h=function(_8i){var _8j=new T(function(){return B(A1(_8f,_8i));});return new T1(0,function(_8k){return E(_8j);});};return _8h;};switch(E(_84)){case 8:if(48>_8c){var _8l=new T(function(){return B(A1(_88,__Z));});return function(_8m){return C > 19 ? new F(function(){return A1(_8m,_8l);}) : (++C,A1(_8m,_8l));};}else{if(_8c>55){var _8n=new T(function(){return B(A1(_88,__Z));});return function(_8o){return C > 19 ? new F(function(){return A1(_8o,_8n);}) : (++C,A1(_8o,_8n));};}else{return _8d(_8c-48|0);}}break;case 10:if(48>_8c){var _8p=new T(function(){return B(A1(_88,__Z));});return function(_8q){return C > 19 ? new F(function(){return A1(_8q,_8p);}) : (++C,A1(_8q,_8p));};}else{if(_8c>57){var _8r=new T(function(){return B(A1(_88,__Z));});return function(_8s){return C > 19 ? new F(function(){return A1(_8s,_8r);}) : (++C,A1(_8s,_8r));};}else{return _8d(_8c-48|0);}}break;case 16:if(48>_8c){if(97>_8c){if(65>_8c){var _8t=new T(function(){return B(A1(_88,__Z));});return function(_8u){return C > 19 ? new F(function(){return A1(_8u,_8t);}) : (++C,A1(_8u,_8t));};}else{if(_8c>70){var _8v=new T(function(){return B(A1(_88,__Z));});return function(_8w){return C > 19 ? new F(function(){return A1(_8w,_8v);}) : (++C,A1(_8w,_8v));};}else{return _8d((_8c-65|0)+10|0);}}}else{if(_8c>102){if(65>_8c){var _8x=new T(function(){return B(A1(_88,__Z));});return function(_8y){return C > 19 ? new F(function(){return A1(_8y,_8x);}) : (++C,A1(_8y,_8x));};}else{if(_8c>70){var _8z=new T(function(){return B(A1(_88,__Z));});return function(_8A){return C > 19 ? new F(function(){return A1(_8A,_8z);}) : (++C,A1(_8A,_8z));};}else{return _8d((_8c-65|0)+10|0);}}}else{return _8d((_8c-97|0)+10|0);}}}else{if(_8c>57){if(97>_8c){if(65>_8c){var _8B=new T(function(){return B(A1(_88,__Z));});return function(_8C){return C > 19 ? new F(function(){return A1(_8C,_8B);}) : (++C,A1(_8C,_8B));};}else{if(_8c>70){var _8D=new T(function(){return B(A1(_88,__Z));});return function(_8E){return C > 19 ? new F(function(){return A1(_8E,_8D);}) : (++C,A1(_8E,_8D));};}else{return _8d((_8c-65|0)+10|0);}}}else{if(_8c>102){if(65>_8c){var _8F=new T(function(){return B(A1(_88,__Z));});return function(_8G){return C > 19 ? new F(function(){return A1(_8G,_8F);}) : (++C,A1(_8G,_8F));};}else{if(_8c>70){var _8H=new T(function(){return B(A1(_88,__Z));});return function(_8I){return C > 19 ? new F(function(){return A1(_8I,_8H);}) : (++C,A1(_8I,_8H));};}else{return _8d((_8c-65|0)+10|0);}}}else{return _8d((_8c-97|0)+10|0);}}}else{return _8d(_8c-48|0);}}break;default:return E(_82);}}},_8J=function(_8K){var _8L=E(_8K);if(!_8L._){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_85,_8L);}) : (++C,A1(_85,_8L));}};return function(_8M){return C > 19 ? new F(function(){return A3(_86,_8M,_1V,_8J);}) : (++C,A3(_86,_8M,_1V,_8J));};},_8N=function(_8O){var _8P=function(_8Q){return C > 19 ? new F(function(){return A1(_8O,new T1(5,new T2(0,8,_8Q)));}) : (++C,A1(_8O,new T1(5,new T2(0,8,_8Q))));},_8R=function(_8S){return C > 19 ? new F(function(){return A1(_8O,new T1(5,new T2(0,16,_8S)));}) : (++C,A1(_8O,new T1(5,new T2(0,16,_8S))));},_8T=function(_8U){switch(E(_8U)){case 79:return new T1(1,_83(8,_8P));case 88:return new T1(1,_83(16,_8R));case 111:return new T1(1,_83(8,_8P));case 120:return new T1(1,_83(16,_8R));default:return new T0(2);}};return function(_8V){return (E(_8V)==48)?E(new T1(0,_8T)):new T0(2);};},_8W=function(_8X){return new T1(0,_8N(_8X));},_8Y=function(_8Z){return C > 19 ? new F(function(){return A1(_8Z,__Z);}) : (++C,A1(_8Z,__Z));},_90=function(_91){return C > 19 ? new F(function(){return A1(_91,__Z);}) : (++C,A1(_91,__Z));},_92=new T1(0,1),_93=function(_94,_95){while(1){var _96=E(_94);if(!_96._){var _97=_96.a,_98=E(_95);if(!_98._){var _99=_98.a,_9a=addC(_97,_99);if(!E(_9a.b)){return new T1(0,_9a.a);}else{_94=new T1(1,I_fromInt(_97));_95=new T1(1,I_fromInt(_99));continue;}}else{_94=new T1(1,I_fromInt(_97));_95=_98;continue;}}else{var _9b=E(_95);if(!_9b._){_94=_96;_95=new T1(1,I_fromInt(_9b.a));continue;}else{return new T1(1,I_add(_96.a,_9b.a));}}}},_9c=new T(function(){return _93(new T1(0,2147483647),_92);}),_9d=function(_9e){var _9f=E(_9e);if(!_9f._){var _9g=E(_9f.a);return (_9g==(-2147483648))?E(_9c):new T1(0, -_9g);}else{return new T1(1,I_negate(_9f.a));}},_9h=new T1(0,10),_9i=function(_9j,_9k){while(1){var _9l=E(_9j);if(!_9l._){return E(_9k);}else{var _9m=_9k+1|0;_9j=_9l.b;_9k=_9m;continue;}}},_9n=function(_9o,_9p){var _9q=E(_9p);return (_9q._==0)?__Z:new T2(1,new T(function(){return B(A1(_9o,_9q.a));}),new T(function(){return _9n(_9o,_9q.b);}));},_9r=function(_9s){return _3d(E(_9s));},_9t=new T(function(){return err(new T(function(){return unCStr("this should not happen");}));}),_9u=function(_9v,_9w){while(1){var _9x=E(_9v);if(!_9x._){var _9y=_9x.a,_9z=E(_9w);if(!_9z._){var _9A=_9z.a;if(!(imul(_9y,_9A)|0)){return new T1(0,imul(_9y,_9A)|0);}else{_9v=new T1(1,I_fromInt(_9y));_9w=new T1(1,I_fromInt(_9A));continue;}}else{_9v=new T1(1,I_fromInt(_9y));_9w=_9z;continue;}}else{var _9B=E(_9w);if(!_9B._){_9v=_9x;_9w=new T1(1,I_fromInt(_9B.a));continue;}else{return new T1(1,I_mul(_9x.a,_9B.a));}}}},_9C=function(_9D,_9E){var _9F=E(_9E);if(!_9F._){return __Z;}else{var _9G=E(_9F.b);return (_9G._==0)?E(_9t):new T2(1,_93(_9u(_9F.a,_9D),_9G.a),new T(function(){return _9C(_9D,_9G.b);}));}},_9H=new T1(0,0),_9I=function(_9J,_9K,_9L){while(1){var _9M=(function(_9N,_9O,_9P){var _9Q=E(_9P);if(!_9Q._){return E(_9H);}else{if(!E(_9Q.b)._){return E(_9Q.a);}else{var _9R=E(_9O);if(_9R<=40){var _9S=function(_9T,_9U){while(1){var _9V=E(_9U);if(!_9V._){return E(_9T);}else{var _9W=_93(_9u(_9T,_9N),_9V.a);_9T=_9W;_9U=_9V.b;continue;}}};return _9S(_9H,_9Q);}else{var _9X=_9u(_9N,_9N);if(!(_9R%2)){var _9Y=_9C(_9N,_9Q);_9J=_9X;_9K=quot(_9R+1|0,2);_9L=_9Y;return __continue;}else{var _9Y=_9C(_9N,new T2(1,_9H,_9Q));_9J=_9X;_9K=quot(_9R+1|0,2);_9L=_9Y;return __continue;}}}}})(_9J,_9K,_9L);if(_9M!=__continue){return _9M;}}},_9Z=function(_a0,_a1){return _9I(_a0,new T(function(){return _9i(_a1,0);},1),_9n(_9r,_a1));},_a2=function(_a3){var _a4=new T(function(){var _a5=new T(function(){var _a6=function(_a7){return C > 19 ? new F(function(){return A1(_a3,new T1(1,new T(function(){return _9Z(_9h,_a7);})));}) : (++C,A1(_a3,new T1(1,new T(function(){return _9Z(_9h,_a7);}))));};return new T1(1,_83(10,_a6));}),_a8=function(_a9){if(E(_a9)==43){var _aa=function(_ab){return C > 19 ? new F(function(){return A1(_a3,new T1(1,new T(function(){return _9Z(_9h,_ab);})));}) : (++C,A1(_a3,new T1(1,new T(function(){return _9Z(_9h,_ab);}))));};return new T1(1,_83(10,_aa));}else{return new T0(2);}},_ac=function(_ad){if(E(_ad)==45){var _ae=function(_af){return C > 19 ? new F(function(){return A1(_a3,new T1(1,new T(function(){return _9d(_9Z(_9h,_af));})));}) : (++C,A1(_a3,new T1(1,new T(function(){return _9d(_9Z(_9h,_af));}))));};return new T1(1,_83(10,_ae));}else{return new T0(2);}};return _6g(_6g(new T1(0,_ac),new T1(0,_a8)),_a5);});return _6g(new T1(0,function(_ag){return (E(_ag)==101)?E(_a4):new T0(2);}),new T1(0,function(_ah){return (E(_ah)==69)?E(_a4):new T0(2);}));},_ai=function(_aj){var _ak=function(_al){return C > 19 ? new F(function(){return A1(_aj,new T1(1,_al));}) : (++C,A1(_aj,new T1(1,_al)));};return function(_am){return (E(_am)==46)?new T1(1,_83(10,_ak)):new T0(2);};},_an=function(_ao){return new T1(0,_ai(_ao));},_ap=function(_aq){var _ar=function(_as){var _at=function(_au){return new T1(1,_7o(_a2,_8Y,function(_av){return C > 19 ? new F(function(){return A1(_aq,new T1(5,new T3(1,_as,_au,_av)));}) : (++C,A1(_aq,new T1(5,new T3(1,_as,_au,_av))));}));};return new T1(1,_7o(_an,_90,_at));};return _83(10,_ar);},_aw=function(_ax){return new T1(1,_ap(_ax));},_ay=function(_az){return E(E(_az).a);},_aA=function(_aB,_aC,_aD){while(1){var _aE=E(_aD);if(!_aE._){return false;}else{if(!B(A3(_ay,_aB,_aC,_aE.a))){_aD=_aE.b;continue;}else{return true;}}}},_aF=new T(function(){return unCStr("!@#$%&*+./<=>?\\^|:-~");}),_aG=function(_aH){return _aA(_6R,_aH,_aF);},_aI=function(_aJ){var _aK=new T(function(){return B(A1(_aJ,8));}),_aL=new T(function(){return B(A1(_aJ,16));});return function(_aM){switch(E(_aM)){case 79:return E(_aK);case 88:return E(_aL);case 111:return E(_aK);case 120:return E(_aL);default:return new T0(2);}};},_aN=function(_aO){return new T1(0,_aI(_aO));},_aP=function(_aQ){return C > 19 ? new F(function(){return A1(_aQ,10);}) : (++C,A1(_aQ,10));},_aR=function(_aS,_aT){var _aU=jsShowI(_aS);return _x(fromJSStr(_aU),_aT);},_aV=function(_aW,_aX,_aY){if(_aX>=0){return _aR(_aX,_aY);}else{if(_aW<=6){return _aR(_aX,_aY);}else{return new T2(1,40,new T(function(){var _aZ=jsShowI(_aX);return _x(fromJSStr(_aZ),new T2(1,41,_aY));}));}}},_b0=function(_b1){return err(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return _aV(9,_b1,__Z);})));},_b2=function(_b3){var _b4=E(_b3);if(!_b4._){return E(_b4.a);}else{return I_toInt(_b4.a);}},_b5=function(_b6,_b7){var _b8=E(_b6);if(!_b8._){var _b9=_b8.a,_ba=E(_b7);return (_ba._==0)?_b9<=_ba.a:I_compareInt(_ba.a,_b9)>=0;}else{var _bb=_b8.a,_bc=E(_b7);return (_bc._==0)?I_compareInt(_bb,_bc.a)<=0:I_compare(_bb,_bc.a)<=0;}},_bd=function(_be){return new T0(2);},_bf=function(_bg){var _bh=E(_bg);if(!_bh._){return _bd;}else{var _bi=_bh.a,_bj=E(_bh.b);if(!_bj._){return E(_bi);}else{var _bk=new T(function(){return _bf(_bj);}),_bl=function(_bm){return _6g(B(A1(_bi,_bm)),new T(function(){return B(A1(_bk,_bm));}));};return _bl;}}},_bn=function(_bo,_bp){var _bq=function(_br,_bs,_bt){var _bu=E(_br);if(!_bu._){return C > 19 ? new F(function(){return A1(_bt,_bo);}) : (++C,A1(_bt,_bo));}else{var _bv=E(_bs);if(!_bv._){return new T0(2);}else{if(E(_bu.a)!=E(_bv.a)){return new T0(2);}else{var _bw=new T(function(){return B(_bq(_bu.b,_bv.b,_bt));});return new T1(0,function(_bx){return E(_bw);});}}}};return function(_by){return C > 19 ? new F(function(){return _bq(_bo,_by,_bp);}) : (++C,_bq(_bo,_by,_bp));};},_bz=new T(function(){return unCStr("SO");}),_bA=function(_bB){var _bC=new T(function(){return B(A1(_bB,14));});return new T1(1,_bn(_bz,function(_bD){return E(_bC);}));},_bE=new T(function(){return unCStr("SOH");}),_bF=function(_bG){var _bH=new T(function(){return B(A1(_bG,1));});return new T1(1,_bn(_bE,function(_bI){return E(_bH);}));},_bJ=new T(function(){return unCStr("NUL");}),_bK=function(_bL){var _bM=new T(function(){return B(A1(_bL,0));});return new T1(1,_bn(_bJ,function(_bN){return E(_bM);}));},_bO=new T(function(){return unCStr("STX");}),_bP=function(_bQ){var _bR=new T(function(){return B(A1(_bQ,2));});return new T1(1,_bn(_bO,function(_bS){return E(_bR);}));},_bT=new T(function(){return unCStr("ETX");}),_bU=function(_bV){var _bW=new T(function(){return B(A1(_bV,3));});return new T1(1,_bn(_bT,function(_bX){return E(_bW);}));},_bY=new T(function(){return unCStr("EOT");}),_bZ=function(_c0){var _c1=new T(function(){return B(A1(_c0,4));});return new T1(1,_bn(_bY,function(_c2){return E(_c1);}));},_c3=new T(function(){return unCStr("ENQ");}),_c4=function(_c5){var _c6=new T(function(){return B(A1(_c5,5));});return new T1(1,_bn(_c3,function(_c7){return E(_c6);}));},_c8=new T(function(){return unCStr("ACK");}),_c9=function(_ca){var _cb=new T(function(){return B(A1(_ca,6));});return new T1(1,_bn(_c8,function(_cc){return E(_cb);}));},_cd=new T(function(){return unCStr("BEL");}),_ce=function(_cf){var _cg=new T(function(){return B(A1(_cf,7));});return new T1(1,_bn(_cd,function(_ch){return E(_cg);}));},_ci=new T(function(){return unCStr("BS");}),_cj=function(_ck){var _cl=new T(function(){return B(A1(_ck,8));});return new T1(1,_bn(_ci,function(_cm){return E(_cl);}));},_cn=new T(function(){return unCStr("HT");}),_co=function(_cp){var _cq=new T(function(){return B(A1(_cp,9));});return new T1(1,_bn(_cn,function(_cr){return E(_cq);}));},_cs=new T(function(){return unCStr("LF");}),_ct=function(_cu){var _cv=new T(function(){return B(A1(_cu,10));});return new T1(1,_bn(_cs,function(_cw){return E(_cv);}));},_cx=new T(function(){return unCStr("VT");}),_cy=function(_cz){var _cA=new T(function(){return B(A1(_cz,11));});return new T1(1,_bn(_cx,function(_cB){return E(_cA);}));},_cC=new T(function(){return unCStr("FF");}),_cD=function(_cE){var _cF=new T(function(){return B(A1(_cE,12));});return new T1(1,_bn(_cC,function(_cG){return E(_cF);}));},_cH=new T(function(){return unCStr("CR");}),_cI=function(_cJ){var _cK=new T(function(){return B(A1(_cJ,13));});return new T1(1,_bn(_cH,function(_cL){return E(_cK);}));},_cM=new T(function(){return unCStr("SI");}),_cN=function(_cO){var _cP=new T(function(){return B(A1(_cO,15));});return new T1(1,_bn(_cM,function(_cQ){return E(_cP);}));},_cR=new T(function(){return unCStr("DLE");}),_cS=function(_cT){var _cU=new T(function(){return B(A1(_cT,16));});return new T1(1,_bn(_cR,function(_cV){return E(_cU);}));},_cW=new T(function(){return unCStr("DC1");}),_cX=function(_cY){var _cZ=new T(function(){return B(A1(_cY,17));});return new T1(1,_bn(_cW,function(_d0){return E(_cZ);}));},_d1=new T(function(){return unCStr("DC2");}),_d2=function(_d3){var _d4=new T(function(){return B(A1(_d3,18));});return new T1(1,_bn(_d1,function(_d5){return E(_d4);}));},_d6=new T(function(){return unCStr("DC3");}),_d7=function(_d8){var _d9=new T(function(){return B(A1(_d8,19));});return new T1(1,_bn(_d6,function(_da){return E(_d9);}));},_db=new T(function(){return unCStr("DC4");}),_dc=function(_dd){var _de=new T(function(){return B(A1(_dd,20));});return new T1(1,_bn(_db,function(_df){return E(_de);}));},_dg=new T(function(){return unCStr("NAK");}),_dh=function(_di){var _dj=new T(function(){return B(A1(_di,21));});return new T1(1,_bn(_dg,function(_dk){return E(_dj);}));},_dl=new T(function(){return unCStr("SYN");}),_dm=function(_dn){var _do=new T(function(){return B(A1(_dn,22));});return new T1(1,_bn(_dl,function(_dp){return E(_do);}));},_dq=new T(function(){return unCStr("ETB");}),_dr=function(_ds){var _dt=new T(function(){return B(A1(_ds,23));});return new T1(1,_bn(_dq,function(_du){return E(_dt);}));},_dv=new T(function(){return unCStr("CAN");}),_dw=function(_dx){var _dy=new T(function(){return B(A1(_dx,24));});return new T1(1,_bn(_dv,function(_dz){return E(_dy);}));},_dA=new T(function(){return unCStr("EM");}),_dB=function(_dC){var _dD=new T(function(){return B(A1(_dC,25));});return new T1(1,_bn(_dA,function(_dE){return E(_dD);}));},_dF=new T(function(){return unCStr("SUB");}),_dG=function(_dH){var _dI=new T(function(){return B(A1(_dH,26));});return new T1(1,_bn(_dF,function(_dJ){return E(_dI);}));},_dK=new T(function(){return unCStr("ESC");}),_dL=function(_dM){var _dN=new T(function(){return B(A1(_dM,27));});return new T1(1,_bn(_dK,function(_dO){return E(_dN);}));},_dP=new T(function(){return unCStr("FS");}),_dQ=function(_dR){var _dS=new T(function(){return B(A1(_dR,28));});return new T1(1,_bn(_dP,function(_dT){return E(_dS);}));},_dU=new T(function(){return unCStr("GS");}),_dV=function(_dW){var _dX=new T(function(){return B(A1(_dW,29));});return new T1(1,_bn(_dU,function(_dY){return E(_dX);}));},_dZ=new T(function(){return unCStr("RS");}),_e0=function(_e1){var _e2=new T(function(){return B(A1(_e1,30));});return new T1(1,_bn(_dZ,function(_e3){return E(_e2);}));},_e4=new T(function(){return unCStr("US");}),_e5=function(_e6){var _e7=new T(function(){return B(A1(_e6,31));});return new T1(1,_bn(_e4,function(_e8){return E(_e7);}));},_e9=new T(function(){return unCStr("SP");}),_ea=function(_eb){var _ec=new T(function(){return B(A1(_eb,32));});return new T1(1,_bn(_e9,function(_ed){return E(_ec);}));},_ee=new T(function(){return unCStr("DEL");}),_ef=function(_eg){var _eh=new T(function(){return B(A1(_eg,127));});return new T1(1,_bn(_ee,function(_ei){return E(_eh);}));},_ej=new T(function(){return _bf(new T2(1,function(_ek){return new T1(1,_7o(_bF,_bA,_ek));},new T2(1,_bK,new T2(1,_bP,new T2(1,_bU,new T2(1,_bZ,new T2(1,_c4,new T2(1,_c9,new T2(1,_ce,new T2(1,_cj,new T2(1,_co,new T2(1,_ct,new T2(1,_cy,new T2(1,_cD,new T2(1,_cI,new T2(1,_cN,new T2(1,_cS,new T2(1,_cX,new T2(1,_d2,new T2(1,_d7,new T2(1,_dc,new T2(1,_dh,new T2(1,_dm,new T2(1,_dr,new T2(1,_dw,new T2(1,_dB,new T2(1,_dG,new T2(1,_dL,new T2(1,_dQ,new T2(1,_dV,new T2(1,_e0,new T2(1,_e5,new T2(1,_ea,new T2(1,_ef,__Z))))))))))))))))))))))))))))))))));}),_el=function(_em){var _en=new T(function(){return B(A1(_em,7));}),_eo=new T(function(){return B(A1(_em,8));}),_ep=new T(function(){return B(A1(_em,9));}),_eq=new T(function(){return B(A1(_em,10));}),_er=new T(function(){return B(A1(_em,11));}),_es=new T(function(){return B(A1(_em,12));}),_et=new T(function(){return B(A1(_em,13));}),_eu=new T(function(){return B(A1(_em,92));}),_ev=new T(function(){return B(A1(_em,39));}),_ew=new T(function(){return B(A1(_em,34));}),_ex=new T(function(){var _ey=function(_ez){var _eA=new T(function(){return _3d(E(_ez));}),_eB=function(_eC){var _eD=_9Z(_eA,_eC);if(!_b5(_eD,new T1(0,1114111))){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_em,new T(function(){var _eE=_b2(_eD);if(_eE>>>0>1114111){return _b0(_eE);}else{return _eE;}}));}) : (++C,A1(_em,new T(function(){var _eE=_b2(_eD);if(_eE>>>0>1114111){return _b0(_eE);}else{return _eE;}})));}};return new T1(1,_83(_ez,_eB));},_eF=new T(function(){var _eG=new T(function(){return B(A1(_em,31));}),_eH=new T(function(){return B(A1(_em,30));}),_eI=new T(function(){return B(A1(_em,29));}),_eJ=new T(function(){return B(A1(_em,28));}),_eK=new T(function(){return B(A1(_em,27));}),_eL=new T(function(){return B(A1(_em,26));}),_eM=new T(function(){return B(A1(_em,25));}),_eN=new T(function(){return B(A1(_em,24));}),_eO=new T(function(){return B(A1(_em,23));}),_eP=new T(function(){return B(A1(_em,22));}),_eQ=new T(function(){return B(A1(_em,21));}),_eR=new T(function(){return B(A1(_em,20));}),_eS=new T(function(){return B(A1(_em,19));}),_eT=new T(function(){return B(A1(_em,18));}),_eU=new T(function(){return B(A1(_em,17));}),_eV=new T(function(){return B(A1(_em,16));}),_eW=new T(function(){return B(A1(_em,15));}),_eX=new T(function(){return B(A1(_em,14));}),_eY=new T(function(){return B(A1(_em,6));}),_eZ=new T(function(){return B(A1(_em,5));}),_f0=new T(function(){return B(A1(_em,4));}),_f1=new T(function(){return B(A1(_em,3));}),_f2=new T(function(){return B(A1(_em,2));}),_f3=new T(function(){return B(A1(_em,1));}),_f4=new T(function(){return B(A1(_em,0));}),_f5=function(_f6){switch(E(_f6)){case 64:return E(_f4);case 65:return E(_f3);case 66:return E(_f2);case 67:return E(_f1);case 68:return E(_f0);case 69:return E(_eZ);case 70:return E(_eY);case 71:return E(_en);case 72:return E(_eo);case 73:return E(_ep);case 74:return E(_eq);case 75:return E(_er);case 76:return E(_es);case 77:return E(_et);case 78:return E(_eX);case 79:return E(_eW);case 80:return E(_eV);case 81:return E(_eU);case 82:return E(_eT);case 83:return E(_eS);case 84:return E(_eR);case 85:return E(_eQ);case 86:return E(_eP);case 87:return E(_eO);case 88:return E(_eN);case 89:return E(_eM);case 90:return E(_eL);case 91:return E(_eK);case 92:return E(_eJ);case 93:return E(_eI);case 94:return E(_eH);case 95:return E(_eG);default:return new T0(2);}};return _6g(new T1(0,function(_f7){return (E(_f7)==94)?E(new T1(0,_f5)):new T0(2);}),new T(function(){return B(A1(_ej,_em));}));});return _6g(new T1(1,_7o(_aN,_aP,_ey)),_eF);});return _6g(new T1(0,function(_f8){switch(E(_f8)){case 34:return E(_ew);case 39:return E(_ev);case 92:return E(_eu);case 97:return E(_en);case 98:return E(_eo);case 102:return E(_es);case 110:return E(_eq);case 114:return E(_et);case 116:return E(_ep);case 118:return E(_er);default:return new T0(2);}}),_ex);},_f9=function(_fa){return C > 19 ? new F(function(){return A1(_fa,0);}) : (++C,A1(_fa,0));},_fb=function(_fc){var _fd=E(_fc);if(!_fd._){return _f9;}else{var _fe=E(_fd.a),_ff=_fe>>>0,_fg=new T(function(){return _fb(_fd.b);});if(_ff>887){var _fh=u_iswspace(_fe);if(!E(_fh)){return _f9;}else{var _fi=function(_fj){var _fk=new T(function(){return B(A1(_fg,_fj));});return new T1(0,function(_fl){return E(_fk);});};return _fi;}}else{if(_ff==32){var _fm=function(_fn){var _fo=new T(function(){return B(A1(_fg,_fn));});return new T1(0,function(_fp){return E(_fo);});};return _fm;}else{if(_ff-9>>>0>4){if(_ff==160){var _fq=function(_fr){var _fs=new T(function(){return B(A1(_fg,_fr));});return new T1(0,function(_ft){return E(_fs);});};return _fq;}else{return _f9;}}else{var _fu=function(_fv){var _fw=new T(function(){return B(A1(_fg,_fv));});return new T1(0,function(_fx){return E(_fw);});};return _fu;}}}}},_fy=function(_fz){var _fA=new T(function(){return B(_fy(_fz));}),_fB=function(_fC){return (E(_fC)==92)?E(_fA):new T0(2);},_fD=function(_fE){return E(new T1(0,_fB));},_fF=new T1(1,function(_fG){return C > 19 ? new F(function(){return A2(_fb,_fG,_fD);}) : (++C,A2(_fb,_fG,_fD));}),_fH=new T(function(){return B(_el(function(_fI){return C > 19 ? new F(function(){return A1(_fz,new T2(0,_fI,true));}) : (++C,A1(_fz,new T2(0,_fI,true)));}));}),_fJ=function(_fK){var _fL=E(_fK);if(_fL==38){return E(_fA);}else{var _fM=_fL>>>0;if(_fM>887){var _fN=u_iswspace(_fL);return (E(_fN)==0)?new T0(2):E(_fF);}else{return (_fM==32)?E(_fF):(_fM-9>>>0>4)?(_fM==160)?E(_fF):new T0(2):E(_fF);}}};return _6g(new T1(0,function(_fO){return (E(_fO)==92)?E(new T1(0,_fJ)):new T0(2);}),new T1(0,function(_fP){var _fQ=E(_fP);if(_fQ==92){return E(_fH);}else{return C > 19 ? new F(function(){return A1(_fz,new T2(0,_fQ,false));}) : (++C,A1(_fz,new T2(0,_fQ,false)));}}));},_fR=function(_fS,_fT){var _fU=new T(function(){return B(A1(_fT,new T1(1,new T(function(){return B(A1(_fS,__Z));}))));}),_fV=function(_fW){var _fX=E(_fW),_fY=E(_fX.a);if(_fY==34){if(!E(_fX.b)){return E(_fU);}else{return C > 19 ? new F(function(){return _fR(function(_fZ){return C > 19 ? new F(function(){return A1(_fS,new T2(1,_fY,_fZ));}) : (++C,A1(_fS,new T2(1,_fY,_fZ)));},_fT);}) : (++C,_fR(function(_fZ){return C > 19 ? new F(function(){return A1(_fS,new T2(1,_fY,_fZ));}) : (++C,A1(_fS,new T2(1,_fY,_fZ)));},_fT));}}else{return C > 19 ? new F(function(){return _fR(function(_g0){return C > 19 ? new F(function(){return A1(_fS,new T2(1,_fY,_g0));}) : (++C,A1(_fS,new T2(1,_fY,_g0)));},_fT);}) : (++C,_fR(function(_g0){return C > 19 ? new F(function(){return A1(_fS,new T2(1,_fY,_g0));}) : (++C,A1(_fS,new T2(1,_fY,_g0)));},_fT));}};return C > 19 ? new F(function(){return _fy(_fV);}) : (++C,_fy(_fV));},_g1=new T(function(){return unCStr("_\'");}),_g2=function(_g3){var _g4=u_iswalnum(_g3);if(!E(_g4)){return _aA(_6R,_g3,_g1);}else{return true;}},_g5=function(_g6){return _g2(E(_g6));},_g7=new T(function(){return unCStr(",;()[]{}`");}),_g8=new T(function(){return unCStr("=>");}),_g9=new T(function(){return unCStr("~");}),_ga=new T(function(){return unCStr("@");}),_gb=new T(function(){return unCStr("->");}),_gc=new T(function(){return unCStr("<-");}),_gd=new T(function(){return unCStr("|");}),_ge=new T(function(){return unCStr("\\");}),_gf=new T(function(){return unCStr("=");}),_gg=new T(function(){return unCStr("::");}),_gh=new T(function(){return unCStr("..");}),_gi=function(_gj){var _gk=new T(function(){return B(A1(_gj,new T0(6)));}),_gl=new T(function(){var _gm=new T(function(){var _gn=function(_go){var _gp=new T(function(){return B(A1(_gj,new T1(0,_go)));});return new T1(0,function(_gq){return (E(_gq)==39)?E(_gp):new T0(2);});};return B(_el(_gn));}),_gr=function(_gs){var _gt=E(_gs);switch(_gt){case 39:return new T0(2);case 92:return E(_gm);default:var _gu=new T(function(){return B(A1(_gj,new T1(0,_gt)));});return new T1(0,function(_gv){return (E(_gv)==39)?E(_gu):new T0(2);});}},_gw=new T(function(){var _gx=new T(function(){return B(_fR(_1V,_gj));}),_gy=new T(function(){var _gz=new T(function(){var _gA=new T(function(){var _gB=function(_gC){var _gD=E(_gC),_gE=u_iswalpha(_gD);return (E(_gE)==0)?(_gD==95)?new T1(1,_7O(_g5,function(_gF){return C > 19 ? new F(function(){return A1(_gj,new T1(3,new T2(1,_gD,_gF)));}) : (++C,A1(_gj,new T1(3,new T2(1,_gD,_gF))));})):new T0(2):new T1(1,_7O(_g5,function(_gG){return C > 19 ? new F(function(){return A1(_gj,new T1(3,new T2(1,_gD,_gG)));}) : (++C,A1(_gj,new T1(3,new T2(1,_gD,_gG))));}));};return _6g(new T1(0,_gB),new T(function(){return new T1(1,_7o(_8W,_aw,_gj));}));}),_gH=function(_gI){return (!_aA(_6R,_gI,_aF))?new T0(2):new T1(1,_7O(_aG,function(_gJ){var _gK=new T2(1,_gI,_gJ);if(!_aA(new T2(0,_6W,_71),_gK,new T2(1,_gh,new T2(1,_gg,new T2(1,_gf,new T2(1,_ge,new T2(1,_gd,new T2(1,_gc,new T2(1,_gb,new T2(1,_ga,new T2(1,_g9,new T2(1,_g8,__Z)))))))))))){return C > 19 ? new F(function(){return A1(_gj,new T1(4,_gK));}) : (++C,A1(_gj,new T1(4,_gK)));}else{return C > 19 ? new F(function(){return A1(_gj,new T1(2,_gK));}) : (++C,A1(_gj,new T1(2,_gK)));}}));};return _6g(new T1(0,_gH),_gA);});return _6g(new T1(0,function(_gL){if(!_aA(_6R,_gL,_g7)){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_gj,new T1(2,new T2(1,_gL,__Z)));}) : (++C,A1(_gj,new T1(2,new T2(1,_gL,__Z))));}}),_gz);});return _6g(new T1(0,function(_gM){return (E(_gM)==34)?E(_gx):new T0(2);}),_gy);});return _6g(new T1(0,function(_gN){return (E(_gN)==39)?E(new T1(0,_gr)):new T0(2);}),_gw);});return _6g(new T1(1,function(_gO){return (E(_gO)._==0)?E(_gk):new T0(2);}),_gl);},_gP=function(_gQ,_gR){var _gS=new T(function(){var _gT=new T(function(){var _gU=function(_gV){var _gW=new T(function(){var _gX=new T(function(){return B(A1(_gR,_gV));});return B(_gi(function(_gY){var _gZ=E(_gY);return (_gZ._==2)?(!_6M(_gZ.a,_6L))?new T0(2):E(_gX):new T0(2);}));}),_h0=function(_h1){return E(_gW);};return new T1(1,function(_h2){return C > 19 ? new F(function(){return A2(_fb,_h2,_h0);}) : (++C,A2(_fb,_h2,_h0));});};return B(A2(_gQ,0,_gU));});return B(_gi(function(_h3){var _h4=E(_h3);return (_h4._==2)?(!_6M(_h4.a,_6K))?new T0(2):E(_gT):new T0(2);}));}),_h5=function(_h6){return E(_gS);};return function(_h7){return C > 19 ? new F(function(){return A2(_fb,_h7,_h5);}) : (++C,A2(_fb,_h7,_h5));};},_h8=function(_h9,_ha){var _hb=function(_hc){var _hd=new T(function(){return B(A1(_h9,_hc));}),_he=function(_hf){return _6g(B(A1(_hd,_hf)),new T(function(){return new T1(1,_gP(_hb,_hf));}));};return _he;},_hg=new T(function(){return B(A1(_h9,_ha));}),_hh=function(_hi){return _6g(B(A1(_hg,_hi)),new T(function(){return new T1(1,_gP(_hb,_hi));}));};return _hh;},_hj=function(_hk,_hl){var _hm=function(_hn,_ho){var _hp=function(_hq){return C > 19 ? new F(function(){return A1(_ho,new T(function(){return  -E(_hq);}));}) : (++C,A1(_ho,new T(function(){return  -E(_hq);})));},_hr=new T(function(){return B(_gi(function(_hs){return C > 19 ? new F(function(){return A3(_hk,_hs,_hn,_hp);}) : (++C,A3(_hk,_hs,_hn,_hp));}));}),_ht=function(_hu){return E(_hr);},_hv=function(_hw){return C > 19 ? new F(function(){return A2(_fb,_hw,_ht);}) : (++C,A2(_fb,_hw,_ht));},_hx=new T(function(){return B(_gi(function(_hy){var _hz=E(_hy);if(_hz._==4){var _hA=E(_hz.a);if(!_hA._){return C > 19 ? new F(function(){return A3(_hk,_hz,_hn,_ho);}) : (++C,A3(_hk,_hz,_hn,_ho));}else{if(E(_hA.a)==45){if(!E(_hA.b)._){return E(new T1(1,_hv));}else{return C > 19 ? new F(function(){return A3(_hk,_hz,_hn,_ho);}) : (++C,A3(_hk,_hz,_hn,_ho));}}else{return C > 19 ? new F(function(){return A3(_hk,_hz,_hn,_ho);}) : (++C,A3(_hk,_hz,_hn,_ho));}}}else{return C > 19 ? new F(function(){return A3(_hk,_hz,_hn,_ho);}) : (++C,A3(_hk,_hz,_hn,_ho));}}));}),_hB=function(_hC){return E(_hx);};return new T1(1,function(_hD){return C > 19 ? new F(function(){return A2(_fb,_hD,_hB);}) : (++C,A2(_fb,_hD,_hB));});};return _h8(_hm,_hl);},_hE=new T(function(){return 1/0;}),_hF=function(_hG,_hH){return C > 19 ? new F(function(){return A1(_hH,_hE);}) : (++C,A1(_hH,_hE));},_hI=new T(function(){return 0/0;}),_hJ=function(_hK,_hL){return C > 19 ? new F(function(){return A1(_hL,_hI);}) : (++C,A1(_hL,_hI));},_hM=new T(function(){return unCStr("NaN");}),_hN=new T(function(){return unCStr("Infinity");}),_hO=new T(function(){return unCStr("base");}),_hP=new T(function(){return unCStr("GHC.Exception");}),_hQ=new T(function(){return unCStr("ArithException");}),_hR=function(_hS){return E(new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_hO,_hP,_hQ),__Z,__Z));},_hT=new T(function(){return unCStr("Ratio has zero denominator");}),_hU=new T(function(){return unCStr("denormal");}),_hV=new T(function(){return unCStr("divide by zero");}),_hW=new T(function(){return unCStr("loss of precision");}),_hX=new T(function(){return unCStr("arithmetic underflow");}),_hY=new T(function(){return unCStr("arithmetic overflow");}),_hZ=function(_i0,_i1){switch(E(_i0)){case 0:return _x(_hY,_i1);case 1:return _x(_hX,_i1);case 2:return _x(_hW,_i1);case 3:return _x(_hV,_i1);case 4:return _x(_hU,_i1);default:return _x(_hT,_i1);}},_i2=function(_i3){return _hZ(_i3,__Z);},_i4=new T(function(){return new T5(0,_hR,new T3(0,function(_i5,_i6,_i7){return _hZ(_i6,_i7);},_i2,function(_i8,_i9){return _1q(_hZ,_i8,_i9);}),_ia,function(_ib){var _ic=E(_ib);return _m(_k(_ic.a),_hR,_ic.b);},_i2);}),_ia=function(_4r){return new T2(0,_i4,_4r);},_id=new T(function(){return die(new T(function(){return _ia(3);}));}),_ie=function(_if,_ig){var _ih=E(_if);if(!_ih._){var _ii=_ih.a,_ij=E(_ig);return (_ij._==0)?_ii==_ij.a:(I_compareInt(_ij.a,_ii)==0)?true:false;}else{var _ik=_ih.a,_il=E(_ig);return (_il._==0)?(I_compareInt(_ik,_il.a)==0)?true:false:(I_compare(_ik,_il.a)==0)?true:false;}},_im=new T1(0,0),_in=function(_io,_ip){while(1){var _iq=E(_io);if(!_iq._){var _ir=E(_iq.a);if(_ir==(-2147483648)){_io=new T1(1,I_fromInt(-2147483648));continue;}else{var _is=E(_ip);if(!_is._){return new T1(0,_ir%_is.a);}else{_io=new T1(1,I_fromInt(_ir));_ip=_is;continue;}}}else{var _it=_iq.a,_iu=E(_ip);return (_iu._==0)?new T1(1,I_rem(_it,I_fromInt(_iu.a))):new T1(1,I_rem(_it,_iu.a));}}},_iv=function(_iw,_ix){if(!_ie(_ix,_im)){return _in(_iw,_ix);}else{return E(_id);}},_iy=function(_iz,_iA){while(1){if(!_ie(_iA,_im)){var _iB=_iA,_iC=_iv(_iz,_iA);_iz=_iB;_iA=_iC;continue;}else{return E(_iz);}}},_iD=function(_iE){var _iF=E(_iE);if(!_iF._){var _iG=E(_iF.a);return (_iG==(-2147483648))?E(_9c):(_iG<0)?new T1(0, -_iG):_iF;}else{var _iH=_iF.a;return (I_compareInt(_iH,0)>=0)?_iF:new T1(1,I_negate(_iH));}},_iI=function(_iJ,_iK){while(1){var _iL=E(_iJ);if(!_iL._){var _iM=E(_iL.a);if(_iM==(-2147483648)){_iJ=new T1(1,I_fromInt(-2147483648));continue;}else{var _iN=E(_iK);if(!_iN._){return new T1(0,quot(_iM,_iN.a));}else{_iJ=new T1(1,I_fromInt(_iM));_iK=_iN;continue;}}}else{var _iO=_iL.a,_iP=E(_iK);return (_iP._==0)?new T1(0,I_toInt(I_quot(_iO,I_fromInt(_iP.a)))):new T1(1,I_quot(_iO,_iP.a));}}},_iQ=new T(function(){return die(new T(function(){return _ia(5);}));}),_iR=function(_iS,_iT){if(!_ie(_iT,_im)){var _iU=_iy(_iD(_iS),_iD(_iT));return (!_ie(_iU,_im))?new T2(0,_iI(_iS,_iU),_iI(_iT,_iU)):E(_id);}else{return E(_iQ);}},_iV=new T1(0,1),_iW=new T(function(){return err(new T(function(){return unCStr("Negative exponent");}));}),_iX=new T1(0,2),_iY=new T(function(){return _ie(_iX,_im);}),_iZ=function(_j0,_j1){while(1){var _j2=E(_j0);if(!_j2._){var _j3=_j2.a,_j4=E(_j1);if(!_j4._){var _j5=_j4.a,_j6=subC(_j3,_j5);if(!E(_j6.b)){return new T1(0,_j6.a);}else{_j0=new T1(1,I_fromInt(_j3));_j1=new T1(1,I_fromInt(_j5));continue;}}else{_j0=new T1(1,I_fromInt(_j3));_j1=_j4;continue;}}else{var _j7=E(_j1);if(!_j7._){_j0=_j2;_j1=new T1(1,I_fromInt(_j7.a));continue;}else{return new T1(1,I_sub(_j2.a,_j7.a));}}}},_j8=function(_j9,_ja,_jb){while(1){if(!E(_iY)){if(!_ie(_in(_ja,_iX),_im)){if(!_ie(_ja,_iV)){var _jc=_9u(_j9,_j9),_jd=_iI(_iZ(_ja,_iV),_iX),_je=_9u(_j9,_jb);_j9=_jc;_ja=_jd;_jb=_je;continue;}else{return _9u(_j9,_jb);}}else{var _jc=_9u(_j9,_j9),_jd=_iI(_ja,_iX);_j9=_jc;_ja=_jd;continue;}}else{return E(_id);}}},_jf=function(_jg,_jh){while(1){if(!E(_iY)){if(!_ie(_in(_jh,_iX),_im)){if(!_ie(_jh,_iV)){return _j8(_9u(_jg,_jg),_iI(_iZ(_jh,_iV),_iX),_jg);}else{return E(_jg);}}else{var _ji=_9u(_jg,_jg),_jj=_iI(_jh,_iX);_jg=_ji;_jh=_jj;continue;}}else{return E(_id);}}},_jk=function(_jl,_jm){var _jn=E(_jl);if(!_jn._){var _jo=_jn.a,_jp=E(_jm);return (_jp._==0)?_jo<_jp.a:I_compareInt(_jp.a,_jo)>0;}else{var _jq=_jn.a,_jr=E(_jm);return (_jr._==0)?I_compareInt(_jq,_jr.a)<0:I_compare(_jq,_jr.a)<0;}},_js=function(_jt,_ju){if(!_jk(_ju,_im)){if(!_ie(_ju,_im)){return _jf(_jt,_ju);}else{return E(_iV);}}else{return E(_iW);}},_jv=new T1(0,1),_jw=new T1(0,0),_jx=new T1(0,-1),_jy=function(_jz){var _jA=E(_jz);if(!_jA._){var _jB=_jA.a;return (_jB>=0)?(E(_jB)==0)?E(_jw):E(_92):E(_jx);}else{var _jC=I_compareInt(_jA.a,0);return (_jC<=0)?(E(_jC)==0)?E(_jw):E(_jx):E(_92);}},_jD=function(_jE,_jF,_jG){while(1){var _jH=E(_jG);if(!_jH._){if(!_jk(_jE,_9H)){return new T2(0,_9u(_jF,B(_js(_9h,_jE))),_iV);}else{var _jI=B(_js(_9h,_9d(_jE)));return _iR(_9u(_jF,_jy(_jI)),_iD(_jI));}}else{var _jJ=_iZ(_jE,_jv),_jK=_93(_9u(_jF,_9h),_3d(E(_jH.a)));_jE=_jJ;_jF=_jK;_jG=_jH.b;continue;}}},_jL=function(_jM,_jN){var _jO=E(_jM);if(!_jO._){var _jP=_jO.a,_jQ=E(_jN);return (_jQ._==0)?_jP>=_jQ.a:I_compareInt(_jQ.a,_jP)<=0;}else{var _jR=_jO.a,_jS=E(_jN);return (_jS._==0)?I_compareInt(_jR,_jS.a)>=0:I_compare(_jR,_jS.a)>=0;}},_jT=function(_jU){var _jV=E(_jU);if(!_jV._){var _jW=_jV.b;return _iR(_9u(_9I(new T(function(){return _3d(E(_jV.a));}),new T(function(){return _9i(_jW,0);},1),_9n(_9r,_jW)),_jv),_jv);}else{var _jX=_jV.a,_jY=_jV.c,_jZ=E(_jV.b);if(!_jZ._){var _k0=E(_jY);if(!_k0._){return _iR(_9u(_9Z(_9h,_jX),_jv),_jv);}else{var _k1=_k0.a;if(!_jL(_k1,_9H)){var _k2=B(_js(_9h,_9d(_k1)));return _iR(_9u(_9Z(_9h,_jX),_jy(_k2)),_iD(_k2));}else{return _iR(_9u(_9u(_9Z(_9h,_jX),B(_js(_9h,_k1))),_jv),_jv);}}}else{var _k3=_jZ.a,_k4=E(_jY);if(!_k4._){return _jD(_9H,_9Z(_9h,_jX),_k3);}else{return _jD(_k4.a,_9Z(_9h,_jX),_k3);}}}},_k5=function(_k6,_k7){while(1){var _k8=E(_k7);if(!_k8._){return __Z;}else{if(!B(A1(_k6,_k8.a))){return _k8;}else{_k7=_k8.b;continue;}}}},_k9=function(_ka,_kb){var _kc=E(_ka);if(!_kc._){var _kd=_kc.a,_ke=E(_kb);return (_ke._==0)?_kd>_ke.a:I_compareInt(_ke.a,_kd)<0;}else{var _kf=_kc.a,_kg=E(_kb);return (_kg._==0)?I_compareInt(_kf,_kg.a)>0:I_compare(_kf,_kg.a)>0;}},_kh=function(_ki,_kj){return E(_ki)==E(_kj);},_kk=function(_kl){return _kh(0,_kl);},_km=new T1(1,new T2(0,E(_9H),E(_iV))),_kn=function(_ko,_kp,_kq){var _kr=E(_kq);if(!_kr._){return new T1(1,new T(function(){var _ks=_jT(_kr);return new T2(0,E(_ks.a),E(_ks.b));}));}else{var _kt=E(_kr.c);if(!_kt._){return new T1(1,new T(function(){var _ku=_jT(_kr);return new T2(0,E(_ku.a),E(_ku.b));}));}else{var _kv=_kt.a;if(!_k9(_kv,new T1(0,2147483647))){if(!_jk(_kv,new T1(0,-2147483648))){var _kw=function(_kx){var _ky=_kx+_b2(_kv)|0;return (_ky<=(E(_kp)+3|0))?(_ky>=(E(_ko)-3|0))?new T1(1,new T(function(){var _kz=_jT(_kr);return new T2(0,E(_kz.a),E(_kz.b));})):E(_km):__Z;},_kA=_k5(_kk,_kr.a);if(!_kA._){var _kB=E(_kr.b);if(!_kB._){return E(_km);}else{var _kC=_4s(_kk,_kB.a);if(!E(_kC.b)._){return E(_km);}else{return _kw( -_9i(_kC.a,0));}}}else{return _kw(_9i(_kA,0));}}else{return __Z;}}else{return __Z;}}}},_kD=function(_kE,_kF){return new T0(2);},_kG=new T1(0,1),_kH=function(_kI,_kJ){var _kK=E(_kI);if(!_kK._){var _kL=_kK.a,_kM=E(_kJ);if(!_kM._){var _kN=_kM.a;return (_kL!=_kN)?(_kL>_kN)?2:0:1;}else{var _kO=I_compareInt(_kM.a,_kL);return (_kO<=0)?(_kO>=0)?1:2:0;}}else{var _kP=_kK.a,_kQ=E(_kJ);if(!_kQ._){var _kR=I_compareInt(_kP,_kQ.a);return (_kR>=0)?(_kR<=0)?1:2:0;}else{var _kS=I_compare(_kP,_kQ.a);return (_kS>=0)?(_kS<=0)?1:2:0;}}},_kT=function(_kU,_kV){var _kW=E(_kU);return (_kW._==0)?_kW.a*Math.pow(2,_kV):I_toNumber(_kW.a)*Math.pow(2,_kV);},_kX=function(_kY,_kZ){while(1){var _l0=E(_kY);if(!_l0._){var _l1=E(_l0.a);if(_l1==(-2147483648)){_kY=new T1(1,I_fromInt(-2147483648));continue;}else{var _l2=E(_kZ);if(!_l2._){var _l3=_l2.a;return new T2(0,new T1(0,quot(_l1,_l3)),new T1(0,_l1%_l3));}else{_kY=new T1(1,I_fromInt(_l1));_kZ=_l2;continue;}}}else{var _l4=E(_kZ);if(!_l4._){_kY=_l0;_kZ=new T1(1,I_fromInt(_l4.a));continue;}else{var _l5=I_quotRem(_l0.a,_l4.a);return new T2(0,new T1(1,_l5.a),new T1(1,_l5.b));}}}},_l6=new T1(0,0),_l7=function(_l8,_l9,_la){if(!_ie(_la,_l6)){var _lb=_kX(_l9,_la),_lc=_lb.a;switch(_kH(_3s(_lb.b,1),_la)){case 0:return _kT(_lc,_l8);case 1:if(!(_b2(_lc)&1)){return _kT(_lc,_l8);}else{return _kT(_93(_lc,_kG),_l8);}break;default:return _kT(_93(_lc,_kG),_l8);}}else{return E(_id);}},_ld=function(_le){var _lf=function(_lg,_lh){while(1){if(!_jk(_lg,_le)){if(!_k9(_lg,_le)){if(!_ie(_lg,_le)){return C > 19 ? new F(function(){return _4N("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2");}) : (++C,_4N("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2"));}else{return E(_lh);}}else{return _lh-1|0;}}else{var _li=_3s(_lg,1),_lj=_lh+1|0;_lg=_li;_lh=_lj;continue;}}};return C > 19 ? new F(function(){return _lf(_92,0);}) : (++C,_lf(_92,0));},_lk=function(_ll){var _lm=E(_ll);if(!_lm._){var _ln=_lm.a>>>0;if(!_ln){return -1;}else{var _lo=function(_lp,_lq){while(1){if(_lp>=_ln){if(_lp<=_ln){if(_lp!=_ln){return C > 19 ? new F(function(){return _4N("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");}) : (++C,_4N("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2"));}else{return E(_lq);}}else{return _lq-1|0;}}else{var _lr=imul(_lp,2)>>>0,_ls=_lq+1|0;_lp=_lr;_lq=_ls;continue;}}};return C > 19 ? new F(function(){return _lo(1,0);}) : (++C,_lo(1,0));}}else{return C > 19 ? new F(function(){return _ld(_lm);}) : (++C,_ld(_lm));}},_lt=function(_lu){var _lv=E(_lu);if(!_lv._){var _lw=_lv.a>>>0;if(!_lw){return new T2(0,-1,0);}else{var _lx=function(_ly,_lz){while(1){if(_ly>=_lw){if(_ly<=_lw){if(_ly!=_lw){return C > 19 ? new F(function(){return _4N("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");}) : (++C,_4N("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2"));}else{return E(_lz);}}else{return _lz-1|0;}}else{var _lA=imul(_ly,2)>>>0,_lB=_lz+1|0;_ly=_lA;_lz=_lB;continue;}}};return new T2(0,B(_lx(1,0)),(_lw&_lw-1>>>0)>>>0&4294967295);}}else{var _lC=_lv.a;return new T2(0,B(_lk(_lv)),I_compareInt(I_and(_lC,I_sub(_lC,I_fromInt(1))),0));}},_lD=function(_lE,_lF){while(1){var _lG=E(_lE);if(!_lG._){var _lH=_lG.a,_lI=E(_lF);if(!_lI._){return new T1(0,(_lH>>>0&_lI.a>>>0)>>>0&4294967295);}else{_lE=new T1(1,I_fromInt(_lH));_lF=_lI;continue;}}else{var _lJ=E(_lF);if(!_lJ._){_lE=_lG;_lF=new T1(1,I_fromInt(_lJ.a));continue;}else{return new T1(1,I_and(_lG.a,_lJ.a));}}}},_lK=function(_lL,_lM){var _lN=E(_lL);if(!_lN._){var _lO=(_lN.a>>>0&(2<<_lM>>>0)-1>>>0)>>>0,_lP=1<<_lM>>>0;return (_lP<=_lO)?(_lP>=_lO)?1:2:0;}else{var _lQ=_lD(_lN,_iZ(_3s(new T1(0,2),_lM),_92)),_lR=_3s(_92,_lM);return (!_k9(_lR,_lQ))?(!_jk(_lR,_lQ))?1:2:0;}},_lS=function(_lT,_lU){while(1){var _lV=E(_lT);if(!_lV._){_lT=new T1(1,I_fromInt(_lV.a));continue;}else{return new T1(1,I_shiftRight(_lV.a,_lU));}}},_lW=function(_lX,_lY,_lZ,_m0){var _m1=_lt(_m0),_m2=_m1.a;if(!E(_m1.b)){var _m3=B(_lk(_lZ));if(_m3<((_m2+_lX|0)-1|0)){var _m4=_m2+(_lX-_lY|0)|0;if(_m4>0){if(_m4>_m3){if(_m4<=(_m3+1|0)){if(!E(_lt(_lZ).b)){return 0;}else{return _kT(_kG,_lX-_lY|0);}}else{return 0;}}else{var _m5=_lS(_lZ,_m4);switch(_lK(_lZ,_m4-1|0)){case 0:return _kT(_m5,_lX-_lY|0);case 1:if(!(_b2(_m5)&1)){return _kT(_m5,_lX-_lY|0);}else{return _kT(_93(_m5,_kG),_lX-_lY|0);}break;default:return _kT(_93(_m5,_kG),_lX-_lY|0);}}}else{return _kT(_lZ,(_lX-_lY|0)-_m4|0);}}else{if(_m3>=_lY){var _m6=_lS(_lZ,(_m3+1|0)-_lY|0);switch(_lK(_lZ,_m3-_lY|0)){case 0:return _kT(_m6,((_m3-_m2|0)+1|0)-_lY|0);case 2:return _kT(_93(_m6,_kG),((_m3-_m2|0)+1|0)-_lY|0);default:if(!(_b2(_m6)&1)){return _kT(_m6,((_m3-_m2|0)+1|0)-_lY|0);}else{return _kT(_93(_m6,_kG),((_m3-_m2|0)+1|0)-_lY|0);}}}else{return _kT(_lZ, -_m2);}}}else{var _m7=B(_lk(_lZ))-_m2|0,_m8=function(_m9){var _ma=function(_mb,_mc){if(!_b5(_3s(_mc,_lY),_mb)){return _l7(_m9-_lY|0,_mb,_mc);}else{return _l7((_m9-_lY|0)+1|0,_mb,_3s(_mc,1));}};if(_m9>=_lY){if(_m9!=_lY){return _ma(_lZ,new T(function(){return _3s(_m0,_m9-_lY|0);}));}else{return _ma(_lZ,_m0);}}else{return _ma(new T(function(){return _3s(_lZ,_lY-_m9|0);}),_m0);}};if(_lX>_m7){return C > 19 ? new F(function(){return _m8(_lX);}) : (++C,_m8(_lX));}else{return C > 19 ? new F(function(){return _m8(_m7);}) : (++C,_m8(_m7));}}},_md=new T(function(){return 0/0;}),_me=new T(function(){return -1/0;}),_mf=new T(function(){return 1/0;}),_mg=function(_mh,_mi){if(!_ie(_mi,_l6)){if(!_ie(_mh,_l6)){if(!_jk(_mh,_l6)){return C > 19 ? new F(function(){return _lW(-1021,53,_mh,_mi);}) : (++C,_lW(-1021,53,_mh,_mi));}else{return  -B(_lW(-1021,53,_9d(_mh),_mi));}}else{return 0;}}else{return (!_ie(_mh,_l6))?(!_jk(_mh,_l6))?E(_mf):E(_me):E(_md);}},_mj=function(_mk){var _ml=E(_mk);switch(_ml._){case 3:var _mm=_ml.a;return (!_6M(_mm,_hN))?(!_6M(_mm,_hM))?_kD:_hJ:_hF;case 5:var _mn=_kn(-1021,1024,_ml.a);if(!_mn._){return _hF;}else{var _mo=new T(function(){var _mp=E(_mn.a);return B(_mg(_mp.a,_mp.b));});return function(_mq,_mr){return C > 19 ? new F(function(){return A1(_mr,_mo);}) : (++C,A1(_mr,_mo));};}break;default:return _kD;}},_ms=function(_mt){var _mu=function(_mv){return E(new T2(3,_mt,_7f));};return new T1(1,function(_mw){return C > 19 ? new F(function(){return A2(_fb,_mw,_mu);}) : (++C,A2(_fb,_mw,_mu));});},_mx=new T(function(){return B(A3(_hj,_mj,0,_ms));}),_my=function(_mz,_mA){while(1){var _mB=E(_mz);if(!_mB._){return E(_mA);}else{_mz=_mB.b;_mA=_mB.a;continue;}}},_mC=function(_mD){var _mE=E(_mD);if(!_mE._){return __Z;}else{var _mF=_mE.a,_mG=new T(function(){if(E(_my(_mF,_5V))==37){var _mH=_5W(_63(_mx,new T(function(){return _5S(_mF);})));if(!_mH._){return E(_6e);}else{if(!E(_mH.b)._){return E(_mH.a)/100;}else{return E(_6d);}}}else{var _mI=_5W(_63(_mx,_mF));if(!_mI._){return E(_6e);}else{if(!E(_mI.b)._){return E(_mI.a);}else{return E(_6d);}}}});return new T1(1,_mG);}},_mJ=function(_mK){if(_mK!=0){if(_mK<=0){var _mL=1/(1+0.5* -_mK),_mM=_mL*_mL,_mN=_mM*_mL,_mO=_mN*_mL,_mP=_mO*_mL,_mQ=_mP*_mL,_mR=_mQ*_mL,_mS=_mR*_mL;return (_mK<0)?_mL*Math.exp( -(_mK*_mK)-1.26551223+1.00002368*_mL+0.37409196*_mM+9.678418e-2*_mN-0.18628806*_mO+0.27886807*_mP-1.13520398*_mQ+1.48851587*_mR-0.82215223*_mS+0.17087277*_mS*_mL)-1:1-_mL*Math.exp( -(_mK*_mK)-1.26551223+1.00002368*_mL+0.37409196*_mM+9.678418e-2*_mN-0.18628806*_mO+0.27886807*_mP-1.13520398*_mQ+1.48851587*_mR-0.82215223*_mS+0.17087277*_mS*_mL);}else{var _mT=1/(1+0.5*_mK),_mU=_mT*_mT,_mV=_mU*_mT,_mW=_mV*_mT,_mX=_mW*_mT,_mY=_mX*_mT,_mZ=_mY*_mT,_n0=_mZ*_mT;return (_mK<0)?_mT*Math.exp( -(_mK*_mK)-1.26551223+1.00002368*_mT+0.37409196*_mU+9.678418e-2*_mV-0.18628806*_mW+0.27886807*_mX-1.13520398*_mY+1.48851587*_mZ-0.82215223*_n0+0.17087277*_n0*_mT)-1:1-_mT*Math.exp( -(_mK*_mK)-1.26551223+1.00002368*_mT+0.37409196*_mU+9.678418e-2*_mV-0.18628806*_mW+0.27886807*_mX-1.13520398*_mY+1.48851587*_mZ-0.82215223*_n0+0.17087277*_n0*_mT);}}else{return (_mK<0)?Math.exp( -(_mK*_mK)-1.26551223+1.00002368+0.37409196+9.678418e-2-0.18628806+0.27886807-1.13520398+1.48851587-0.82215223+0.17087277)-1:1-Math.exp( -(_mK*_mK)-1.26551223+1.00002368+0.37409196+9.678418e-2-0.18628806+0.27886807-1.13520398+1.48851587-0.82215223+0.17087277);}},_n1=new T(function(){return unCStr("price");}),_n2=new T(function(){return unCStr("rho");}),_n3=new T(function(){return unCStr("vega");}),_n4=new T(function(){return unCStr("theta");}),_n5=new T(function(){return unCStr("gamma");}),_n6=new T(function(){return unCStr("delta");}),_n7=function(_n8,_n9){var _na=E(_n8);if(!_na._){return __Z;}else{var _nb=E(_n9);return (_nb._==0)?__Z:new T2(1,new T2(0,_na.a,_nb.a),new T(function(){return _n7(_na.b,_nb.b);}));}},_nc=function(_nd){var _ne=new T(function(){return E(E(_nd).d);}),_nf=new T(function(){return E(E(_nd).c);}),_ng=new T(function(){return Math.exp( -E(_nf)*E(_ne));}),_nh=new T(function(){return E(E(_nd).e);}),_ni=new T(function(){return E(E(E(_nd).b).b);}),_nj=new T(function(){return E(E(E(_nd).a).b);}),_nk=new T(function(){var _nl=E(_nh),_nm=E(_ne);return (Math.log(E(_ni)/E(_nj))+(E(_nf)+_nl*_nl/2)*_nm)/_nl/Math.sqrt(_nm);}),_nn=new T(function(){if(!E(E(_nd).g)){return 1;}else{return -1;}}),_no=new T(function(){return 0.5*(1-_mJ( -(E(_nn)*(E(_nk)-E(_nh)*Math.sqrt(E(_ne))))*0.7071067811865475));}),_np=new T(function(){return Math.sqrt(E(_ne));}),_nq=new T(function(){var _nr=E(_nk);return Math.exp( -(_nr*_nr/2))/2.5066282746350725;});return _n7(new T2(1,_n1,new T2(1,_n6,new T2(1,_n5,new T2(1,_n4,new T2(1,_n3,new T2(1,_n2,__Z)))))),new T2(1,new T(function(){var _ns=E(_nn);return (_ns*E(_ni)*0.5*(1-_mJ( -(_ns*E(_nk))*0.7071067811865475))-_ns*E(_nj)*E(_ng)*E(_no))*E(E(_nd).f);}),new T2(1,new T(function(){if(!E(E(_nd).g)){return 0.5*(1-_mJ( -E(_nk)*0.7071067811865475));}else{return 0.5*(1-_mJ( -E(_nk)*0.7071067811865475))-1;}}),new T2(1,new T(function(){return E(_nq)/E(_ni)/E(_nh)/E(_np);}),new T2(1,new T(function(){return ( -E(_ni)*E(_nq)*E(_nh)/2/E(_np)-E(_nn)*E(_nf)*E(_nj)*E(_ng)*E(_no))/365;}),new T2(1,new T(function(){return E(_ni)*E(_np)*E(_nq);}),new T2(1,new T(function(){return E(_nn)*E(_nj)*E(_ne)*E(_ng)*E(_no);}),__Z)))))));},_nt=function(_nu,_){var _nv=E(_nu);if(!_nv._){return E(_4P);}else{var _nw=_nv.a,_nx=E(_nv.b);if(!_nx._){return E(_4P);}else{var _ny=_nx.a,_nz=E(_nx.b);if(!_nz._){return E(_4P);}else{var _nA=_nz.a,_nB=E(_nz.b);if(!_nB._){return E(_4P);}else{var _nC=_nB.a,_nD=E(_nB.b);if(!_nD._){return E(_4P);}else{var _nE=_nD.a,_nF=E(_nD.b);if(!_nF._){return E(_4P);}else{var _nG=E(_nF.b);if(!_nG._){return E(_4P);}else{if(!E(_nG.b)._){var _nH=function(_){var _nI=_2v(E(_nw),"value"),_nJ=_2v(E(_ny),"value"),_nK=_2v(E(_nA),"value"),_nL=_2v(E(_nC),"value"),_nM=_2v(E(_nE),"value"),_nN=_mC(new T1(1,new T(function(){var _nO=String(_nI);return fromJSStr(_nO);})));if(!_nN._){return 0;}else{var _nP=_nN.a,_nQ=_mC(new T1(1,new T(function(){var _nR=String(_nJ);return fromJSStr(_nR);})));if(!_nQ._){return 0;}else{var _nS=_nQ.a,_nT=_mC(new T1(1,new T(function(){var _nU=String(_nK);return fromJSStr(_nU);})));if(!_nT._){return 0;}else{var _nV=_nT.a,_nW=_mC(new T1(1,new T(function(){var _nX=String(_nL);return fromJSStr(_nX);})));if(!_nW._){return 0;}else{var _nY=_nW.a,_nZ=_mC(new T1(1,new T(function(){var _o0=String(_nM);return fromJSStr(_o0);})));if(!_nZ._){return 0;}else{var _o1=_nZ.a,_o2=toJSStr(E(_4R)),_o3=_41(E(_nF.a),_o2,toJSStr(_3T(_nc({_:0,a:new T2(0,_5I,_nS),b:new T2(0,_5I,_nP),c:_nV,d:_nY,e:_o1,f:1,g:false})))),_o4=_41(E(_nG.a),_o2,toJSStr(_3X(_nc({_:0,a:new T2(0,_5I,_nS),b:new T2(0,_5I,_nP),c:_nV,d:_nY,e:_o1,f:1,g:true}))));return _2r(_);}}}}}},_o5=B(A(_5g,[_2u,_2s,_2n,_nw,1,function(_o6,_){return _nH(_);},_])),_o7=B(A(_5g,[_2u,_2s,_2n,_ny,1,function(_o8,_){return _nH(_);},_])),_o9=B(A(_5g,[_2u,_2s,_2a,_nA,2,function(_oa,_){return _nH(_);},_])),_ob=B(A(_5g,[_2u,_2s,_2a,_nC,2,function(_oc,_){return _nH(_);},_]));return C > 19 ? new F(function(){return A(_5g,[_2u,_2s,_2a,_nE,2,function(_od,_){return _nH(_);},_]);}) : (++C,A(_5g,[_2u,_2s,_2a,_nE,2,function(_od,_){return _nH(_);},_]));}else{return E(_4P);}}}}}}}}},_oe=function(_of,_){var _og=E(_of);if(!_og._){return __Z;}else{var _oh=_oe(_og.b,_);return new T2(1,_og.a,_oh);}},_oi=function(_oj,_){var _ok=__arr2lst(0,_oj);return _oe(_ok,_);},_ol=function(_om,_){return _oi(E(_om),_);},_on=function(_oo,_){return _oo;},_op=function(_oq){return E(E(_oq).a);},_or=function(_os,_ot,_){var _ou=__eq(_ot,E(_59));if(!E(_ou)){var _ov=__isUndef(_ot);if(!E(_ov)){var _ow=B(A3(_op,_os,_ot,_));return new T1(1,_ow);}else{return __Z;}}else{return __Z;}},_ox=(function(id){return document.getElementById(id);}),_oy=new T(function(){return err(new T(function(){return unCStr("Maybe.fromJust: Nothing");}));}),_oz=function(_oA){var _oB=E(_oA);return (_oB._==0)?E(_oy):E(_oB.a);},_oC=function(_oD,_oE){while(1){var _oF=(function(_oG,_oH){var _oI=E(_oG);if(!_oI._){return __Z;}else{var _oJ=_oI.b,_oK=E(_oH);if(!_oK._){return __Z;}else{var _oL=_oK.b;if(!E(_oK.a)._){return new T2(1,_oI.a,new T(function(){return _oC(_oJ,_oL);}));}else{_oD=_oJ;_oE=_oL;return __continue;}}}})(_oD,_oE);if(_oF!=__continue){return _oF;}}},_oM=new T(function(){return unAppCStr("[]",__Z);}),_oN=function(_oO){var _oP=E(_oO);if(!_oP._){return E(new T2(1,93,__Z));}else{var _oQ=new T(function(){return _x(fromJSStr(E(_oP.a)),new T(function(){return _oN(_oP.b);},1));});return new T2(1,44,_oQ);}},_oR=function(_oS,_oT){var _oU=new T(function(){var _oV=_oC(_oS,_oT);if(!_oV._){return E(_oM);}else{var _oW=new T(function(){return _x(fromJSStr(E(_oV.a)),new T(function(){return _oN(_oV.b);},1));});return new T2(1,91,_oW);}});return err(unAppCStr("Elements with the following IDs could not be found: ",_oU));},_oX=function(_oY){while(1){var _oZ=E(_oY);if(!_oZ._){return false;}else{if(!E(_oZ.a)._){return true;}else{_oY=_oZ.b;continue;}}}},_p0=function(_p1,_p2,_p3){var _p4=_4U(_p1),_p5=function(_p6){if(!_oX(_p6)){return C > 19 ? new F(function(){return A1(_p3,new T(function(){return _9n(_oz,_p6);}));}) : (++C,A1(_p3,new T(function(){return _9n(_oz,_p6);})));}else{return _oR(_p2,_p6);}},_p7=new T(function(){var _p8=new T(function(){return B(A2(_5e,_p4,__Z));}),_p9=function(_pa){var _pb=E(_pa);if(!_pb._){return E(_p8);}else{var _pc=new T(function(){return B(_p9(_pb.b));}),_pd=function(_pe){return C > 19 ? new F(function(){return A3(_4W,_p4,_pc,function(_pf){return C > 19 ? new F(function(){return A2(_5e,_p4,new T2(1,_pe,_pf));}) : (++C,A2(_5e,_p4,new T2(1,_pe,_pf)));});}) : (++C,A3(_4W,_p4,_pc,function(_pf){return C > 19 ? new F(function(){return A2(_5e,_p4,new T2(1,_pe,_pf));}) : (++C,A2(_5e,_p4,new T2(1,_pe,_pf)));}));},_pg=new T(function(){return B(A2(_5a,_p1,function(_){var _ph=_ox(E(_pb.a));return _or(new T2(0,_on,_ol),_ph,_);}));});return C > 19 ? new F(function(){return A3(_4W,_p4,_pg,_pd);}) : (++C,A3(_4W,_p4,_pg,_pd));}};return B(_p9(_p2));});return C > 19 ? new F(function(){return A3(_4W,_p4,_p7,_p5);}) : (++C,A3(_4W,_p4,_p7,_p5));},_pi=new T(function(){return B(_p0(_1X,new T(function(){return _9n(function(_pj){return toJSStr(E(_pj));},new T2(1,new T(function(){return unCStr("s");}),new T2(1,new T(function(){return unCStr("k");}),new T2(1,new T(function(){return unCStr("r");}),new T2(1,new T(function(){return unCStr("t");}),new T2(1,new T(function(){return unCStr("sigma");}),new T2(1,new T(function(){return unCStr("resultC");}),new T2(1,new T(function(){return unCStr("resultP");}),__Z))))))));}),_nt));});
var hasteMain = function() {B(A(_pi, [0]));};window.onload = hasteMain;