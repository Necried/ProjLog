"use strict";
var __haste_prog_id = 'bdcff07bf336e8c88bb5237c3bf1830b371fe167cc11948987998e81a576775c';
var __haste_script_elem = typeof document == 'object' ? document.currentScript : null;
// This object will hold all exports.
var Haste = {};
if(typeof window === 'undefined' && typeof global !== 'undefined') window = global;
window['__haste_crypto'] = window.crypto || window.msCrypto;
if(window['__haste_crypto'] && !window['__haste_crypto'].subtle && window.crypto.webkitSubtle) {
    window['__haste_crypto'].subtle = window.crypto.webkitSubtle;
}

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
  var x = new Long(738919189, 2683596561, true)
  var y = new Long(3648966346, 573393410, true);
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
    var len = buffer.byteLength;
    var views =
        { 'i8' : new Int8Array(buffer)
        , 'i16': len % 2 ? null : new Int16Array(buffer)
        , 'i32': len % 4 ? null : new Int32Array(buffer)
        , 'w8' : new Uint8Array(buffer)
        , 'w16': len % 2 ? null : new Uint16Array(buffer)
        , 'w32': len % 4 ? null : new Uint32Array(buffer)
        , 'f32': len % 4 ? null : new Float32Array(buffer)
        , 'f64': len % 8 ? null : new Float64Array(buffer)
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

var _0=new T(function(){return B(unCStr("expression only available on native nodes"));}),_1=new T(function(){return B(err(_0));}),_2=new T2(0,new Long(3391483696,672714196,true),new Long(1946106450,3710973492,true)),_3=16,_4=15,_5=new T2(0,_4,_3),_6=new T(function(){return B(unCStr("sptEntry:1"));}),_7=new T(function(){return B(unCStr("Main"));}),_8=new T(function(){return B(unCStr("main"));}),_9=new T4(0,_8,_7,_6,_5),_a=new T3(0,_2,_9,_1),_b=new T2(0,new Long(4017620647,2174824019,true),new Long(3502511348,2739385215,true)),_c="]",_d="}",_e=":",_f=",",_g=new T(function(){return eval("JSON.stringify");}),_h="false",_i="null",_j="[",_k="{",_l="\"",_m="true",_n=function(_o,_p){var _q=E(_p);switch(_q._){case 0:return new T2(0,new T(function(){return jsShow(_q.a);}),_o);case 1:return new T2(0,new T(function(){var _r=__app1(E(_g),_q.a);return String(_r);}),_o);case 2:return (!E(_q.a))?new T2(0,_h,_o):new T2(0,_m,_o);case 3:var _s=E(_q.a);if(!_s._){return new T2(0,_j,new T2(1,_c,_o));}else{var _t=new T(function(){var _u=new T(function(){var _v=function(_w){var _x=E(_w);if(!_x._){return E(new T2(1,_c,_o));}else{var _y=new T(function(){var _z=B(_n(new T(function(){return B(_v(_x.b));}),_x.a));return new T2(1,_z.a,_z.b);});return new T2(1,_f,_y);}};return B(_v(_s.b));}),_A=B(_n(_u,_s.a));return new T2(1,_A.a,_A.b);});return new T2(0,_j,_t);}break;case 4:var _B=E(_q.a);if(!_B._){return new T2(0,_k,new T2(1,_d,_o));}else{var _C=E(_B.a),_D=new T(function(){var _E=new T(function(){var _F=function(_G){var _H=E(_G);if(!_H._){return E(new T2(1,_d,_o));}else{var _I=E(_H.a),_J=new T(function(){var _K=B(_n(new T(function(){return B(_F(_H.b));}),_I.b));return new T2(1,_K.a,_K.b);});return new T2(1,_f,new T2(1,_l,new T2(1,_I.a,new T2(1,_l,new T2(1,_e,_J)))));}};return B(_F(_B.b));}),_L=B(_n(_E,_C.b));return new T2(1,_L.a,_L.b);});return new T2(0,_k,new T2(1,new T(function(){var _M=__app1(E(_g),E(_C.a));return String(_M);}),new T2(1,_e,_D)));}break;default:return new T2(0,_i,_o);}},_N=__Z,_O=new T(function(){return toJSStr(_N);}),_P=function(_Q){var _R=B(_n(_N,_Q)),_S=jsCat(new T2(1,_R.a,_R.b),E(_O));return new F(function(){return fromJSStr(_S);});},_T=function(_U){return new F(function(){return err(B(unAppCStr("JSON decoding failed: ",new T(function(){return B(_P(_U));}))));});},_V=new T(function(){return B(unCStr("impossible: too few arguments"));}),_W=new T(function(){return B(err(_V));}),_X=function(_Y){return new T1(1,toJSStr(E(_Y)));},_Z=function(_10,_11){var _12=E(_11);return (_12._==0)?__Z:new T2(1,new T(function(){return B(A1(_10,_12.a));}),new T(function(){return B(_Z(_10,_12.b));}));},_13=function(_14){return new T1(3,E(B(_Z(_X,_14))));},_15=function(_16,_17){while(1){var _18=B((function(_19,_1a){var _1b=E(_1a);if(!_1b._){return __Z;}else{var _1c=_1b.a,_1d=_1b.b;if(!B(A1(_19,_1c))){var _1e=_19;_16=_1e;_17=_1d;return __continue;}else{return new T2(1,_1c,new T(function(){return B(_15(_19,_1d));}));}}})(_16,_17));if(_18!=__continue){return _18;}}},_1f=function(_1g,_1h){var _1i=E(_1g);return (_1i._==0)?E(_1h):new T2(1,_1i.a,new T(function(){return B(_1f(_1i.b,_1h));}));},_1j=function(_1k){return (E(_1k)==( -1))?true:false;},_1l=new T(function(){return B(unCStr("closeDirStream"));}),_1m=function(_1n){return E(_1n);},_1o=0,_1p=function(_1q,_1r,_){var _=writeOffAddr("w32",4,E(_1q),0,E(_1r));return _1o;},_1s=function(_1t,_){return new F(function(){return readOffAddr("w32",4,E(_1t),0);});},_1u=function(_1v,_1w,_1x,_){var _=writeOffAddr("w32",4,plusAddr(E(_1v),E(_1w)),0,E(_1x));return _1o;},_1y=function(_1z,_1A,_){return new F(function(){return readOffAddr("w32",4,plusAddr(E(_1z),E(_1A)),0);});},_1B=4,_1C=function(_1D){return E(_1B);},_1E=function(_1F,_1G,_){return new F(function(){return readOffAddr("w32",4,E(_1F),E(_1G));});},_1H=function(_1I,_1J,_1K,_){var _=writeOffAddr("w32",4,E(_1I),E(_1J),E(_1K));return _1o;},_1L={_:0,a:_1C,b:_1C,c:_1E,d:_1H,e:_1y,f:_1u,g:_1s,h:_1p},_1M=0,_1N=function(_1O){return E(E(_1O).c);},_1P=function(_1Q,_1R,_1S,_){if(_1R>0){var _1T=function(_1U,_1V,_){while(1){var _1W=E(_1U);if(!_1W){var _1X=B(A(_1N,[_1Q,_1S,_1M,_]));return new T2(1,_1X,_1V);}else{var _1Y=B(A(_1N,[_1Q,_1S,_1W,_])),_1Z=new T2(1,_1Y,_1V);_1U=_1W-1|0;_1V=_1Z;continue;}}};return new F(function(){return _1T(_1R-1|0,_N,_);});}else{return _N;}},_20=__Z,_21=0,_22=1,_23=function(_24,_25,_26,_){switch(E(0)){case 0:var _27=function(_){var _28=B(A1(_24,_)),_29=_28,_2a=new T(function(){return B(A1(_26,_29));}),_2b=jsCatch(function(_){return new F(function(){return _2a();});},function(_2c,_){var _2d=B(A2(_25,_29,_));return new F(function(){return die(_2c);});}),_2e=B(A2(_25,_29,_));return _2b;};return new F(function(){return _27();});break;case 1:var _2f=B(A1(_24,_)),_2g=_2f,_2h=jsCatch(new T(function(){return B(A1(_26,_2g));}),function(_2i,_){var _2j=B(A2(_25,_2g,_));return new F(function(){return die(_2i);});}),_2k=B(A2(_25,_2g,_));return _2h;default:var _2l=B(A1(_24,_)),_2m=_2l,_2n=jsCatch(new T(function(){return B(A1(_26,_2m));}),function(_2o,_){var _2p=B(A2(_25,_2m,_));return new F(function(){return die(_2o);});}),_2q=B(A2(_25,_2m,_));return _2n;}},_2r=function(_2s){return E(E(_2s).c);},_2t=new T(function(){return B(unCStr("mallocForeignPtrBytes: size must be >= 0"));}),_2u=new T(function(){return B(err(_2t));}),_2v=function(_2w,_2x,_){var _2y=function(_2z,_){while(1){var _2A=readOffAddr("i8",1,_2x,_2z);if(!E(_2A)){return _2z;}else{var _2B=_2z+1|0;_2z=_2B;continue;}}},_2C=B(_2y(0,_)),_2D=_2C,_2E=function(_2F,_){var _2G=nMV(_20),_2H=_2G,_2I=E(_2D),_2J=function(_2K){var _2L=imul(_2K,4)|0;if(_2L>=0){var _2M=nMV(_20),_2N=_2M,_2O=newByteArr(_2L),_2P=_2O,_2Q=function(_2R,_){var _2S=E(_2F),_2T=B(A3(_2S.a,_2R,new T6(0,_2P,new T2(1,_2P,_2N),_22,_2K,0,0),_)),_2U=E(_2T),_2V=_2U.c,_2W=E(_2U.b);if(_2W.e!=_2W.f){if(E(_2U.a)==1){var _2X=E(_2V),_2Y=_2X.b,_2Z=B(_1P(_1L,_2X.f-_2X.e|0,_2X.a,_)),_30=B(_2Q(_2W,0));return new T(function(){return B(_1f(_2Z,_30));});}else{var _31=B(A3(_2S.b,_2W,_2V,_)),_32=E(_31),_33=E(_32.b),_34=_33.b,_35=B(_1P(_1L,_33.f-_33.e|0,_33.a,_)),_36=B(_2Q(_32.a,0));return new T(function(){return B(_1f(_35,_36));});}}else{var _37=E(_2V),_38=_37.b,_39=B(_1P(_1L,_37.f-_37.e|0,_37.a,_));return _39;}};return new F(function(){return _2Q(new T6(0,_2x,new T1(0,_2H),_21,_2I,0,_2I),_);});}else{return E(_2u);}};if(_2I>1){return new F(function(){return _2J(_2I);});}else{return new F(function(){return _2J(1);});}};return new F(function(){return _23(E(_2w).b,_2r,_2E,_);});},_3a=3,_3b=function(_3c,_3d){while(1){var _3e=E(_3c);if(!_3e._){return (E(_3d)._==0)?true:false;}else{var _3f=E(_3d);if(!_3f._){return false;}else{if(E(_3e.a)!=E(_3f.a)){return false;}else{_3c=_3e.b;_3d=_3f.b;continue;}}}}},_3g=new T(function(){return B(unCStr("UTF16LE"));}),_3h=new T(function(){return B(unCStr("UTF16BE"));}),_3i=new T(function(){return B(unCStr("UTF16"));}),_3j=new T(function(){return B(unCStr("UTF8"));}),_3k=new T(function(){return B(unCStr("UTF32LE"));}),_3l=new T(function(){return B(unCStr("UTF32BE"));}),_3m=new T(function(){return B(unCStr("UTF32"));}),_3n=function(_3o,_3p){var _3q=jsShowI(_3o);return new F(function(){return _1f(fromJSStr(_3q),_3p);});},_3r=41,_3s=40,_3t=function(_3u,_3v,_3w){if(_3v>=0){return new F(function(){return _3n(_3v,_3w);});}else{if(_3u<=6){return new F(function(){return _3n(_3v,_3w);});}else{return new T2(1,_3s,new T(function(){var _3x=jsShowI(_3v);return B(_1f(fromJSStr(_3x),new T2(1,_3r,_3w)));}));}}},_3y=function(_3z){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_3t(9,_3z,_N));}))));});},_3A=function(_3B){while(1){var _3C=B((function(_3D){var _3E=E(_3D);if(!_3E._){return __Z;}else{var _3F=_3E.b,_3G=E(_3E.a);if(_3G==45){_3B=_3F;return __continue;}else{return new T2(1,new T(function(){var _3H=u_towupper(_3G);if(_3H>>>0>1114111){return B(_3y(_3H));}else{return _3H;}}),new T(function(){return B(_3A(_3F));}));}}})(_3B));if(_3C!=__continue){return _3C;}}},_3I=function(_3J,_3K){var _3L=E(_3K);if(!_3L._){return new T2(0,_N,_N);}else{var _3M=_3L.a;if(!B(A1(_3J,_3M))){return new T2(0,_N,_3L);}else{var _3N=new T(function(){var _3O=B(_3I(_3J,_3L.b));return new T2(0,_3O.a,_3O.b);});return new T2(0,new T2(1,_3M,new T(function(){return E(E(_3N).a);})),new T(function(){return E(E(_3N).b);}));}}},_3P=new T(function(){return B(unCStr("UTF-32LE"));}),_3Q=function(_3R){return (E(_3R)==47)?false:true;},_3S=0,_3T=1,_3U=0,_3V=new T(function(){return B(unCStr("iconvRecoder"));}),_3W= -1,_3X=new T(function(){return B(unCStr("base"));}),_3Y=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_3Z=new T(function(){return B(unCStr("IOException"));}),_40=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_3X,_3Y,_3Z),_41=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_40,_N,_N),_42=function(_43){return E(_41);},_44=function(_45){return E(E(_45).a);},_46=function(_47,_48,_49){var _4a=B(A1(_47,_)),_4b=B(A1(_48,_)),_4c=hs_eqWord64(_4a.a,_4b.a);if(!_4c){return __Z;}else{var _4d=hs_eqWord64(_4a.b,_4b.b);return (!_4d)?__Z:new T1(1,_49);}},_4e=function(_4f){var _4g=E(_4f);return new F(function(){return _46(B(_44(_4g.a)),_42,_4g.b);});},_4h=new T(function(){return B(unCStr(": "));}),_4i=new T(function(){return B(unCStr(")"));}),_4j=new T(function(){return B(unCStr(" ("));}),_4k=new T(function(){return B(unCStr("interrupted"));}),_4l=new T(function(){return B(unCStr("system error"));}),_4m=new T(function(){return B(unCStr("unsatisified constraints"));}),_4n=new T(function(){return B(unCStr("user error"));}),_4o=new T(function(){return B(unCStr("permission denied"));}),_4p=new T(function(){return B(unCStr("illegal operation"));}),_4q=new T(function(){return B(unCStr("end of file"));}),_4r=new T(function(){return B(unCStr("resource exhausted"));}),_4s=new T(function(){return B(unCStr("resource busy"));}),_4t=new T(function(){return B(unCStr("does not exist"));}),_4u=new T(function(){return B(unCStr("already exists"));}),_4v=new T(function(){return B(unCStr("resource vanished"));}),_4w=new T(function(){return B(unCStr("timeout"));}),_4x=new T(function(){return B(unCStr("unsupported operation"));}),_4y=new T(function(){return B(unCStr("hardware fault"));}),_4z=new T(function(){return B(unCStr("inappropriate type"));}),_4A=new T(function(){return B(unCStr("invalid argument"));}),_4B=new T(function(){return B(unCStr("failed"));}),_4C=new T(function(){return B(unCStr("protocol error"));}),_4D=function(_4E,_4F){switch(E(_4E)){case 0:return new F(function(){return _1f(_4u,_4F);});break;case 1:return new F(function(){return _1f(_4t,_4F);});break;case 2:return new F(function(){return _1f(_4s,_4F);});break;case 3:return new F(function(){return _1f(_4r,_4F);});break;case 4:return new F(function(){return _1f(_4q,_4F);});break;case 5:return new F(function(){return _1f(_4p,_4F);});break;case 6:return new F(function(){return _1f(_4o,_4F);});break;case 7:return new F(function(){return _1f(_4n,_4F);});break;case 8:return new F(function(){return _1f(_4m,_4F);});break;case 9:return new F(function(){return _1f(_4l,_4F);});break;case 10:return new F(function(){return _1f(_4C,_4F);});break;case 11:return new F(function(){return _1f(_4B,_4F);});break;case 12:return new F(function(){return _1f(_4A,_4F);});break;case 13:return new F(function(){return _1f(_4z,_4F);});break;case 14:return new F(function(){return _1f(_4y,_4F);});break;case 15:return new F(function(){return _1f(_4x,_4F);});break;case 16:return new F(function(){return _1f(_4w,_4F);});break;case 17:return new F(function(){return _1f(_4v,_4F);});break;default:return new F(function(){return _1f(_4k,_4F);});}},_4G=new T(function(){return B(unCStr("}"));}),_4H=new T(function(){return B(unCStr("{handle: "));}),_4I=function(_4J,_4K,_4L,_4M,_4N,_4O){var _4P=new T(function(){var _4Q=new T(function(){var _4R=new T(function(){var _4S=E(_4M);if(!_4S._){return E(_4O);}else{var _4T=new T(function(){return B(_1f(_4S,new T(function(){return B(_1f(_4i,_4O));},1)));},1);return B(_1f(_4j,_4T));}},1);return B(_4D(_4K,_4R));}),_4U=E(_4L);if(!_4U._){return E(_4Q);}else{return B(_1f(_4U,new T(function(){return B(_1f(_4h,_4Q));},1)));}}),_4V=E(_4N);if(!_4V._){var _4W=E(_4J);if(!_4W._){return E(_4P);}else{var _4X=E(_4W.a);if(!_4X._){var _4Y=new T(function(){var _4Z=new T(function(){return B(_1f(_4G,new T(function(){return B(_1f(_4h,_4P));},1)));},1);return B(_1f(_4X.a,_4Z));},1);return new F(function(){return _1f(_4H,_4Y);});}else{var _50=new T(function(){var _51=new T(function(){return B(_1f(_4G,new T(function(){return B(_1f(_4h,_4P));},1)));},1);return B(_1f(_4X.a,_51));},1);return new F(function(){return _1f(_4H,_50);});}}}else{return new F(function(){return _1f(_4V.a,new T(function(){return B(_1f(_4h,_4P));},1));});}},_52=function(_53){var _54=E(_53);return new F(function(){return _4I(_54.a,_54.b,_54.c,_54.d,_54.f,_N);});},_55=function(_56,_57,_58){var _59=E(_57);return new F(function(){return _4I(_59.a,_59.b,_59.c,_59.d,_59.f,_58);});},_5a=function(_5b,_5c){var _5d=E(_5b);return new F(function(){return _4I(_5d.a,_5d.b,_5d.c,_5d.d,_5d.f,_5c);});},_5e=44,_5f=93,_5g=91,_5h=function(_5i,_5j,_5k){var _5l=E(_5j);if(!_5l._){return new F(function(){return unAppCStr("[]",_5k);});}else{var _5m=new T(function(){var _5n=new T(function(){var _5o=function(_5p){var _5q=E(_5p);if(!_5q._){return E(new T2(1,_5f,_5k));}else{var _5r=new T(function(){return B(A2(_5i,_5q.a,new T(function(){return B(_5o(_5q.b));})));});return new T2(1,_5e,_5r);}};return B(_5o(_5l.b));});return B(A2(_5i,_5l.a,_5n));});return new T2(1,_5g,_5m);}},_5s=function(_5t,_5u){return new F(function(){return _5h(_5a,_5t,_5u);});},_5v=new T3(0,_55,_52,_5s),_5w=new T(function(){return new T5(0,_42,_5v,_5x,_4e,_52);}),_5x=function(_5y){return new T2(0,_5w,_5y);},_5z=__Z,_5A=1,_5B=function(_5C,_){var _5D=function(_5E,_){while(1){var _5F=readOffAddr("i8",1,_5C,_5E);if(!E(_5F)){return _5E;}else{var _5G=_5E+1|0;_5E=_5G;continue;}}},_5H=B(_5D(0,_)),_5I=E(_5H);if(_5I>0){var _5J=function(_5K,_5L,_){while(1){var _5M=readOffAddr("i8",1,_5C,_5L);if(_5L>0){var _5N=new T2(1,_5M>>>0&255&4294967295,_5K),_5O=_5L-1|0;_5K=_5N;_5L=_5O;continue;}else{return new T2(1,_5M>>>0&255&4294967295,_5K);}}};return new F(function(){return _5J(_N,_5I-1|0,_);});}else{return _N;}},_5P=function(_){var _5Q=localeEncoding();return new F(function(){return _5B(_5Q,0);});},_5R=function(_5S){var _5T=B(A1(_5S,_));return E(_5T);},_5U=new T(function(){return B(_5R(_5P));}),_5V=function(_){return new F(function(){return _5W(_5A,_5U,0);});},_5X=new T(function(){return B(_5R(_5V));}),_5Y=function(_){var _5Z=nMV(_5X),_60=_5Z;return new T2(0,function(_){return new F(function(){return rMV(_60);});},function(_61,_){var _=wMV(_60,_61);return _1o;});},_62=new T(function(){return B(_5R(_5Y));}),_63=new T(function(){return E(E(_62).a);}),_64=function(_65,_66,_67,_68){var _69=function(_){var _6a=E(_66),_6b=strerror(_6a),_6c=B(A1(_63,0)),_6d=B(_2v(_6c,_6b,0));return new T6(0,_67,new T(function(){switch(E(_6a)){case 1:return 6;break;case 2:return 1;break;case 3:return 1;break;case 4:return 18;break;case 5:return 14;break;case 6:return 1;break;case 7:return 3;break;case 8:return 12;break;case 9:return 12;break;case 10:return 1;break;case 11:return 3;break;case 12:return 3;break;case 13:return 6;break;case 15:return 12;break;case 16:return 2;break;case 17:return 0;break;case 18:return 15;break;case 19:return 15;break;case 20:return 13;break;case 21:return 13;break;case 22:return 12;break;case 23:return 3;break;case 24:return 3;break;case 25:return 5;break;case 26:return 2;break;case 27:return 6;break;case 28:return 3;break;case 29:return 15;break;case 30:return 6;break;case 31:return 3;break;case 32:return 17;break;case 33:return 12;break;case 34:return 15;break;case 35:return 2;break;case 36:return 12;break;case 37:return 3;break;case 38:return 15;break;case 39:return 8;break;case 40:return 12;break;case 42:return 1;break;case 43:return 17;break;case 60:return 12;break;case 61:return 1;break;case 62:return 16;break;case 63:return 3;break;case 64:return 1;break;case 66:return 5;break;case 67:return 17;break;case 69:return 8;break;case 70:return 17;break;case 71:return 10;break;case 72:return 15;break;case 74:return 13;break;case 78:return 17;break;case 84:return 12;break;case 87:return 3;break;case 88:return 12;break;case 89:return 12;break;case 90:return 3;break;case 91:return 10;break;case 92:return 15;break;case 93:return 10;break;case 94:return 15;break;case 95:return 15;break;case 96:return 15;break;case 97:return 15;break;case 98:return 2;break;case 99:return 15;break;case 100:return 17;break;case 101:return 1;break;case 102:return 17;break;case 104:return 17;break;case 105:return 3;break;case 106:return 0;break;case 107:return 12;break;case 108:return 5;break;case 109:return 3;break;case 110:return 16;break;case 111:return 1;break;case 112:return 1;break;case 113:return 1;break;case 114:return 0;break;case 115:return 0;break;case 116:return 17;break;case 122:return 6;break;default:return 11;}}),_65,_6d,new T1(1,_6a),_68);};return new F(function(){return _5R(_69);});},_6e=function(_6f,_){var _6g=__hscore_get_errno(),_6h=new T(function(){return B(_5x(new T(function(){return B(_64(_6f,_6g,_5z,_5z));})));});return new F(function(){return die(_6h);});},_6i=function(_6j,_6k,_6l,_6m,_6n,_6o,_6p,_6q,_6r,_6s,_6t,_6u,_6v,_6w,_6x,_){var _6y=newByteArr(4),_6z=_6y,_6A=E(_6q),_6B=function(_6C){var _6D=plusAddr(_6k,_6C),_=die("Unsupported PrimOp: writeAddrOffAddr#"),_6E=newByteArr(4),_6F=_6E,_6G=E(_6x),_6H=function(_6I){var _6J=plusAddr(_6r,_6I),_=die("Unsupported PrimOp: writeAddrOffAddr#"),_6K=newByteArr(4),_6L=_6K,_6M=function(_6N){var _=writeOffAddr("w32",4,_6L,0,_6N),_6O=newByteArr(4),_6P=_6O,_6Q=function(_6R){var _=writeOffAddr("w32",4,_6P,0,_6R),_6S=hs_iconv(E(_6j),_6z,_6L,_6F,_6P),_6T=readOffAddr("w32",4,_6L,0),_6U=readOffAddr("w32",4,_6P,0),_6V=new T(function(){if(_6G<32){return (_6U&4294967295)>>_6G;}else{if((_6U&4294967295)>=0){return E(_3U);}else{return E(_3W);}}}),_6W=new T(function(){var _6X=E(_6T);if(!_6X){return new T6(0,_6k,_6l,_6m,_6n,0,0);}else{if(_6A<32){return new T6(0,_6k,_6l,_6m,_6n,_6p-((_6X&4294967295)>>_6A)|0,_6p);}else{if((_6X&4294967295)>=0){return new T6(0,_6k,_6l,_6m,_6n,_6p,_6p);}else{return new T6(0,_6k,_6l,_6m,_6n,_6p+1|0,_6p);}}}});if(E(_6S)==4294967295){var _6Y=__hscore_get_errno();switch(E(_6Y)){case  -1:var _6Z=B(_6e(_3V,_));return _6Z;case 7:return new T3(0,_3T,_6W,new T(function(){return new T6(0,_6r,_6s,_6t,_6u,_6v,_6u-E(_6V)|0);}));case 22:return new T3(0,_3S,_6W,new T(function(){return new T6(0,_6r,_6s,_6t,_6u,_6v,_6u-E(_6V)|0);}));case 84:return new T3(0,new T(function(){if(!E(_6V)){return 1;}else{return 2;}}),_6W,new T(function(){return new T6(0,_6r,_6s,_6t,_6u,_6v,_6u-E(_6V)|0);}));default:var _70=B(_6e(_3V,_));return _70;}}else{return new T3(0,_3S,_6W,new T(function(){return new T6(0,_6r,_6s,_6t,_6u,_6v,_6u-E(_6V)|0);}));}};if(_6G<32){return new F(function(){return _6Q((_6u-_6w|0)<<_6G>>>0);});}else{return new F(function(){return _6Q(0);});}};if(_6A<32){return new F(function(){return _6M((_6p-_6o|0)<<_6A>>>0);});}else{return new F(function(){return _6M(0);});}};if(_6G<32){return new F(function(){return _6H(_6w<<_6G);});}else{return new F(function(){return _6H(0);});}};if(_6A<32){return new F(function(){return _6B(_6o<<_6A);});}else{return new F(function(){return _6B(0);});}},_71=2,_72=function(_73,_74,_75,_){var _76=E(_74),_77=E(_75);return new F(function(){return _6i(_73,_76.a,_76.b,_76.c,_76.d,_76.e,_76.f,_71,_77.a,_77.b,_77.c,_77.d,_77.e,_77.f,_3U,_);});},_78=function(_79,_7a,_7b,_){var _7c=E(_7a),_7d=E(_7b);return new F(function(){return _6i(_79,_7c.a,_7c.b,_7c.c,_7c.d,_7c.e,_7c.f,_3U,_7d.a,_7d.b,_7d.c,_7d.d,_7d.e,_7d.f,_71,_);});},_7e=function(_){return _1o;},_7f=function(_7g,_){return new F(function(){return _7e(_);});},_7h=new T(function(){return B(unCStr("mkTextEncoding"));}),_7i=new T(function(){return B(unCStr("Iconv.close"));}),_7j=function(_7k,_7l){while(1){var _7m=E(_7k);if(!_7m._){return E(_7l);}else{var _7n=_7l+1|0;_7k=_7m.b;_7l=_7n;continue;}}},_7o=function(_7p,_7q,_){var _7r=newByteArr(B(_7j(_7p,0))+1|0),_7s=_7r,_7t=function(_7u,_7v,_){while(1){var _7w=E(_7u);if(!_7w._){var _=writeOffAddr("i8",1,_7s,_7v,0);return _1o;}else{var _=writeOffAddr("i8",1,_7s,_7v,E(_7w.a)&255),_7x=_7v+1|0;_7u=_7w.b;_7v=_7x;continue;}}},_7y=B(_7t(_7p,0,_)),_7z=B(A2(_7q,_7s,_));return _7z;},_7A=function(_7B,_7C,_7D,_7E,_){var _7F=function(_7G,_){var _7H=function(_7I,_){var _7J=hs_iconv_open(E(_7I),E(_7G)),_7K=E(_7J);if(_7K==( -1)){var _7L=B(_6e(_7h,_)),_7M=_7L;return new T5(0,new T(function(){return B(A1(_7E,_7M));}),_7D,function(_){var _7N=hs_iconv_close(E(_7M));if(E(_7N)==( -1)){var _7O=B(_6e(_7i,_));return _1o;}else{return _1o;}},_7e,_7f);}else{return new T5(0,new T(function(){return B(A1(_7E,_7K));}),_7D,function(_){var _7P=hs_iconv_close(_7K);if(E(_7P)==( -1)){var _7Q=B(_6e(_7i,_));return _1o;}else{return _1o;}},_7e,_7f);}};return new F(function(){return _7o(_7C,_7H,_);});};return new F(function(){return _7o(_7B,_7F,_);});},_7R=12,_7S=new T(function(){return B(unCStr("invalid byte sequence"));}),_7T=new T(function(){return B(unCStr("recoverDecode"));}),_7U=new T6(0,_5z,_7R,_7T,_7S,_5z,_5z),_7V=new T(function(){return B(_5x(_7U));}),_7W=function(_7X,_7Y,_7Z,_80,_81,_82,_83,_84,_85,_86,_87,_88,_89,_){switch(E(_7X)){case 0:return new F(function(){return die(_7V);});break;case 1:return new T2(0,new T6(0,_7Y,_7Z,_80,_81,_82+1|0,_83),new T6(0,_84,_85,_86,_87,_88,_89));case 2:var _=writeOffAddr("w32",4,_84,_89,65533);return new T2(0,new T6(0,_7Y,_7Z,_80,_81,_82+1|0,_83),new T6(0,_84,_85,_86,_87,_88,_89+1|0));default:var _8a=readOffAddr("w8",1,plusAddr(_7Y,_82),0);if(_8a>=128){var _8b=56320+(_8a&4294967295)|0;if(_8b>>>0>1114111){return new F(function(){return _3y(_8b);});}else{var _=writeOffAddr("w32",4,_84,_89,_8b);return new T2(0,new T6(0,_7Y,_7Z,_80,_81,_82+1|0,_83),new T6(0,_84,_85,_86,_87,_88,_89+1|0));}}else{var _8c=_8a&4294967295;if(_8c>>>0>1114111){return new F(function(){return _3y(_8c);});}else{var _=writeOffAddr("w32",4,_84,_89,_8c);return new T2(0,new T6(0,_7Y,_7Z,_80,_81,_82+1|0,_83),new T6(0,_84,_85,_86,_87,_88,_89+1|0));}}}},_8d=function(_8e,_8f,_8g,_){var _8h=E(_8f),_8i=E(_8g);return new F(function(){return _7W(_8e,_8h.a,_8h.b,_8h.c,_8h.d,_8h.e,_8h.f,_8i.a,_8i.b,_8i.c,_8i.d,_8i.e,_8i.f,_);});},_8j=new T(function(){return B(unCStr("recoverEncode"));}),_8k=new T(function(){return B(unCStr("invalid character"));}),_8l=new T6(0,_5z,_7R,_8j,_8k,_5z,_5z),_8m=new T(function(){return B(_5x(_8l));}),_8n=function(_){return new F(function(){return die(_8m);});},_8o=function(_8p,_8q,_8r,_8s,_8t,_8u,_8v,_8w,_8x,_8y,_8z,_8A,_8B,_){var _8C=readOffAddr("w32",4,_8q,_8u);switch(E(_8p)){case 0:return new F(function(){return _8n(0);});break;case 1:return new T2(0,new T6(0,_8q,_8r,_8s,_8t,_8u+1|0,_8v),new T6(0,_8w,_8x,_8y,_8z,_8A,_8B));case 2:if(E(_8C)==63){return new T2(0,new T6(0,_8q,_8r,_8s,_8t,_8u+1|0,_8v),new T6(0,_8w,_8x,_8y,_8z,_8A,_8B));}else{var _=writeOffAddr("w32",4,_8q,_8u,63);return new T2(0,new T6(0,_8q,_8r,_8s,_8t,_8u,_8v),new T6(0,_8w,_8x,_8y,_8z,_8A,_8B));}break;default:if(56448>_8C){return new F(function(){return _8n(0);});}else{if(_8C>=56576){return new F(function(){return _8n(0);});}else{var _=writeOffAddr("w8",1,plusAddr(_8w,_8B),0,_8C>>>0&255);return new T2(0,new T6(0,_8q,_8r,_8s,_8t,_8u+1|0,_8v),new T6(0,_8w,_8x,_8y,_8z,_8A,_8B+1|0));}}}},_8D=function(_8E,_8F,_8G,_){var _8H=E(_8F),_8I=E(_8G);return new F(function(){return _8o(_8E,_8H.a,_8H.b,_8H.c,_8H.d,_8H.e,_8H.f,_8I.a,_8I.b,_8I.c,_8I.d,_8I.e,_8I.f,_);});},_8J=function(_8K,_8L,_){var _8M=function(_8N,_8O,_){return new F(function(){return _8D(_8K,_8N,_8O,_);});},_8P=new T(function(){var _8Q=B(_3I(_3Q,_8L));return new T2(0,_8Q.a,_8Q.b);}),_8R=function(_8N,_8O,_){return new F(function(){return _8d(_8K,_8N,_8O,_);});},_8S=new T(function(){return B(_1f(_3P,new T(function(){return E(E(_8P).b);},1)));}),_8T=new T(function(){return E(E(_8P).a);});return new T3(0,_8L,function(_){return new F(function(){return _7A(_8T,_8S,_8R,_78,_);});},function(_){return new F(function(){return _7A(_3P,_8L,_8M,_72,_);});});},_8U=2,_8V=function(_8W,_8X,_8Y,_8Z,_90,_91,_92,_93,_94,_95,_96,_97,_){var _98=new T6(0,_8W,_8X,_8Y,_8Z,0,0),_99=function(_9a,_9b,_){while(1){var _9c=B((function(_9d,_9e,_){if(_9d<_91){if((_95-_9e|0)>=2){var _9f=readOffAddr("w32",4,_8W,_9d),_9g=_9f;if(_9g>=65536){if((_95-_9e|0)>=4){var _9h=_9g-65536|0,_=writeOffAddr("w8",1,plusAddr(_92,_9e),0,((_9h>>18)+216|0)>>>0&255),_=writeOffAddr("w8",1,plusAddr(_92,_9e+1|0),0,_9h>>10>>>0&255),_9i=_9h&1023,_=writeOffAddr("w8",1,plusAddr(_92,_9e+2|0),0,((_9i>>8)+220|0)>>>0&255),_=writeOffAddr("w8",1,plusAddr(_92,_9e+3|0),0,_9i>>>0&255),_9j=_9d+1|0,_9k=_9e+4|0;_9a=_9j;_9b=_9k;_=0;return __continue;}else{return new T3(0,_3T,new T(function(){if(_9d!=_91){return new T6(0,_8W,_8X,_8Y,_8Z,_9d,_91);}else{return E(_98);}}),new T6(0,_92,_93,_94,_95,_96,_9e));}}else{var _9l=function(_9m){if(56320>_9g){var _=writeOffAddr("w8",1,plusAddr(_92,_9e),0,_9g>>8>>>0&255),_=writeOffAddr("w8",1,plusAddr(_92,_9e+1|0),0,_9g>>>0&255);return new F(function(){return _99(_9d+1|0,_9e+2|0,0);});}else{if(_9g>57343){var _=writeOffAddr("w8",1,plusAddr(_92,_9e),0,_9g>>8>>>0&255),_=writeOffAddr("w8",1,plusAddr(_92,_9e+1|0),0,_9g>>>0&255);return new F(function(){return _99(_9d+1|0,_9e+2|0,0);});}else{return new T3(0,_8U,new T(function(){if(_9d!=_91){return new T6(0,_8W,_8X,_8Y,_8Z,_9d,_91);}else{return E(_98);}}),new T6(0,_92,_93,_94,_95,_96,_9e));}}};if(55296>_9g){return new F(function(){return _9l(0);});}else{if(_9g>56319){return new F(function(){return _9l(0);});}else{return new T3(0,_8U,new T(function(){if(_9d!=_91){return new T6(0,_8W,_8X,_8Y,_8Z,_9d,_91);}else{return E(_98);}}),new T6(0,_92,_93,_94,_95,_96,_9e));}}}}else{return new T3(0,_3T,new T(function(){if(_9d!=_91){return new T6(0,_8W,_8X,_8Y,_8Z,_9d,_91);}else{return E(_98);}}),new T6(0,_92,_93,_94,_95,_96,_9e));}}else{return new T3(0,_3S,new T(function(){if(_9d!=_91){return new T6(0,_8W,_8X,_8Y,_8Z,_9d,_91);}else{return E(_98);}}),new T6(0,_92,_93,_94,_95,_96,_9e));}})(_9a,_9b,_));if(_9c!=__continue){return _9c;}}};return new F(function(){return _99(_90,_97,_);});},_9n=true,_9o=function(_9p,_9q,_9r,_9s,_9t,_9u,_9v,_9w,_){var _9x=rMV(_9p);if(!E(_9x)){if((_9u-_9w|0)>=2){var _=wMV(_9p,_9n),_=writeOffAddr("w8",1,plusAddr(_9r,_9w),0,254),_=writeOffAddr("w8",1,plusAddr(_9r,_9w+1|0),0,255),_9y=E(_9q);return new F(function(){return _8V(_9y.a,_9y.b,_9y.c,_9y.d,_9y.e,_9y.f,_9r,_9s,_9t,_9u,_9v,_9w+2|0,0);});}else{return new T3(0,_3T,_9q,new T6(0,_9r,_9s,_9t,_9u,_9v,_9w));}}else{var _9z=E(_9q);return new F(function(){return _8V(_9z.a,_9z.b,_9z.c,_9z.d,_9z.e,_9z.f,_9r,_9s,_9t,_9u,_9v,_9w,_);});}},_9A=function(_9B,_9C,_9D,_9E,_9F,_9G,_9H,_9I,_9J,_9K,_9L,_9M,_){var _9N=new T6(0,_9B,_9C,_9D,_9E,0,0),_9O=function(_9P,_9Q,_){while(1){var _9R=B((function(_9S,_9T,_){if(_9T<_9K){if(_9S<_9G){if((_9S+1|0)!=_9G){var _9U=readOffAddr("w8",1,plusAddr(_9B,_9S),0),_9V=readOffAddr("w8",1,plusAddr(_9B,_9S+1|0),0),_9W=(_9U<<8>>>0&65535)+_9V>>>0&65535;if(_9W>=55296){if(_9W<=57343){if((_9G-_9S|0)>=4){var _9X=readOffAddr("w8",1,plusAddr(_9B,_9S+2|0),0),_9Y=readOffAddr("w8",1,plusAddr(_9B,_9S+3|0),0);if(_9W<55296){return new T3(0,_8U,new T(function(){if(_9S!=_9G){return new T6(0,_9B,_9C,_9D,_9E,_9S,_9G);}else{return E(_9N);}}),new T6(0,_9H,_9I,_9J,_9K,_9L,_9T));}else{if(_9W>56319){return new T3(0,_8U,new T(function(){if(_9S!=_9G){return new T6(0,_9B,_9C,_9D,_9E,_9S,_9G);}else{return E(_9N);}}),new T6(0,_9H,_9I,_9J,_9K,_9L,_9T));}else{var _9Z=(_9X<<8>>>0&65535)+_9Y>>>0&65535;if(_9Z<56320){return new T3(0,_8U,new T(function(){if(_9S!=_9G){return new T6(0,_9B,_9C,_9D,_9E,_9S,_9G);}else{return E(_9N);}}),new T6(0,_9H,_9I,_9J,_9K,_9L,_9T));}else{if(_9Z>57343){return new T3(0,_8U,new T(function(){if(_9S!=_9G){return new T6(0,_9B,_9C,_9D,_9E,_9S,_9G);}else{return E(_9N);}}),new T6(0,_9H,_9I,_9J,_9K,_9L,_9T));}else{var _=writeOffAddr("w32",4,_9H,_9T,((((_9W&4294967295)-55296|0)<<10)+((_9Z&4294967295)-56320|0)|0)+65536|0),_a0=_9S+4|0,_a1=_9T+1|0;_9P=_a0;_9Q=_a1;_=0;return __continue;}}}}}else{return new T3(0,_3S,new T(function(){if(_9S!=_9G){return new T6(0,_9B,_9C,_9D,_9E,_9S,_9G);}else{return E(_9N);}}),new T6(0,_9H,_9I,_9J,_9K,_9L,_9T));}}else{var _=writeOffAddr("w32",4,_9H,_9T,_9W&4294967295),_a0=_9S+2|0,_a1=_9T+1|0;_9P=_a0;_9Q=_a1;_=0;return __continue;}}else{var _=writeOffAddr("w32",4,_9H,_9T,_9W&4294967295),_a0=_9S+2|0,_a1=_9T+1|0;_9P=_a0;_9Q=_a1;_=0;return __continue;}}else{return new T3(0,_3S,new T(function(){if(_9S!=_9G){return new T6(0,_9B,_9C,_9D,_9E,_9S,_9G);}else{return E(_9N);}}),new T6(0,_9H,_9I,_9J,_9K,_9L,_9T));}}else{return new T3(0,_3S,new T(function(){if(_9S!=_9G){return new T6(0,_9B,_9C,_9D,_9E,_9S,_9G);}else{return E(_9N);}}),new T6(0,_9H,_9I,_9J,_9K,_9L,_9T));}}else{return new T3(0,_3T,new T(function(){if(_9S!=_9G){return new T6(0,_9B,_9C,_9D,_9E,_9S,_9G);}else{return E(_9N);}}),new T6(0,_9H,_9I,_9J,_9K,_9L,_9T));}})(_9P,_9Q,_));if(_9R!=__continue){return _9R;}}};return new F(function(){return _9O(_9F,_9M,_);});},_a2=function(_a3,_a4,_a5,_a6,_a7,_a8,_a9,_aa,_ab,_ac,_ad,_ae,_){var _af=new T6(0,_a3,_a4,_a5,_a6,0,0),_ag=function(_ah,_ai,_){while(1){var _aj=B((function(_ak,_al,_){if(_al<_ac){if(_ak<_a8){if((_ak+1|0)!=_a8){var _am=readOffAddr("w8",1,plusAddr(_a3,_ak),0),_an=readOffAddr("w8",1,plusAddr(_a3,_ak+1|0),0),_ao=(_an<<8>>>0&65535)+_am>>>0&65535;if(_ao>=55296){if(_ao<=57343){if((_a8-_ak|0)>=4){var _ap=readOffAddr("w8",1,plusAddr(_a3,_ak+2|0),0),_aq=readOffAddr("w8",1,plusAddr(_a3,_ak+3|0),0);if(_ao<55296){return new T3(0,_8U,new T(function(){if(_ak!=_a8){return new T6(0,_a3,_a4,_a5,_a6,_ak,_a8);}else{return E(_af);}}),new T6(0,_a9,_aa,_ab,_ac,_ad,_al));}else{if(_ao>56319){return new T3(0,_8U,new T(function(){if(_ak!=_a8){return new T6(0,_a3,_a4,_a5,_a6,_ak,_a8);}else{return E(_af);}}),new T6(0,_a9,_aa,_ab,_ac,_ad,_al));}else{var _ar=(_aq<<8>>>0&65535)+_ap>>>0&65535;if(_ar<56320){return new T3(0,_8U,new T(function(){if(_ak!=_a8){return new T6(0,_a3,_a4,_a5,_a6,_ak,_a8);}else{return E(_af);}}),new T6(0,_a9,_aa,_ab,_ac,_ad,_al));}else{if(_ar>57343){return new T3(0,_8U,new T(function(){if(_ak!=_a8){return new T6(0,_a3,_a4,_a5,_a6,_ak,_a8);}else{return E(_af);}}),new T6(0,_a9,_aa,_ab,_ac,_ad,_al));}else{var _=writeOffAddr("w32",4,_a9,_al,((((_ao&4294967295)-55296|0)<<10)+((_ar&4294967295)-56320|0)|0)+65536|0),_as=_ak+4|0,_at=_al+1|0;_ah=_as;_ai=_at;_=0;return __continue;}}}}}else{return new T3(0,_3S,new T(function(){if(_ak!=_a8){return new T6(0,_a3,_a4,_a5,_a6,_ak,_a8);}else{return E(_af);}}),new T6(0,_a9,_aa,_ab,_ac,_ad,_al));}}else{var _=writeOffAddr("w32",4,_a9,_al,_ao&4294967295),_as=_ak+2|0,_at=_al+1|0;_ah=_as;_ai=_at;_=0;return __continue;}}else{var _=writeOffAddr("w32",4,_a9,_al,_ao&4294967295),_as=_ak+2|0,_at=_al+1|0;_ah=_as;_ai=_at;_=0;return __continue;}}else{return new T3(0,_3S,new T(function(){if(_ak!=_a8){return new T6(0,_a3,_a4,_a5,_a6,_ak,_a8);}else{return E(_af);}}),new T6(0,_a9,_aa,_ab,_ac,_ad,_al));}}else{return new T3(0,_3S,new T(function(){if(_ak!=_a8){return new T6(0,_a3,_a4,_a5,_a6,_ak,_a8);}else{return E(_af);}}),new T6(0,_a9,_aa,_ab,_ac,_ad,_al));}}else{return new T3(0,_3T,new T(function(){if(_ak!=_a8){return new T6(0,_a3,_a4,_a5,_a6,_ak,_a8);}else{return E(_af);}}),new T6(0,_a9,_aa,_ab,_ac,_ad,_al));}})(_ah,_ai,_));if(_aj!=__continue){return _aj;}}};return new F(function(){return _ag(_a7,_ae,_);});},_au=function(_av,_aw,_){var _ax=E(_av),_ay=E(_aw);return new F(function(){return _9A(_ax.a,_ax.b,_ax.c,_ax.d,_ax.e,_ax.f,_ay.a,_ay.b,_ay.c,_ay.d,_ay.e,_ay.f,_);});},_az=new T1(1,_au),_aA=function(_aB,_aC,_){var _aD=E(_aB),_aE=E(_aC);return new F(function(){return _a2(_aD.a,_aD.b,_aD.c,_aD.d,_aD.e,_aD.f,_aE.a,_aE.b,_aE.c,_aE.d,_aE.e,_aE.f,_);});},_aF=new T1(1,_aA),_aG=function(_aH,_aI,_aJ,_aK,_aL,_aM,_aN,_aO,_){var _aP=rMV(_aH),_aQ=E(_aP);if(!_aQ._){if((_aN-_aM|0)>=2){var _aR=readOffAddr("w8",1,plusAddr(_aI,_aM),0),_aS=_aR,_aT=readOffAddr("w8",1,plusAddr(_aI,_aM+1|0),0),_aU=_aT,_aV=function(_aW){if(E(_aS)==255){if(E(_aU)==254){var _=wMV(_aH,_aF),_aX=E(_aO);return new F(function(){return _a2(_aI,_aJ,_aK,_aL,_aM+2|0,_aN,_aX.a,_aX.b,_aX.c,_aX.d,_aX.e,_aX.f,0);});}else{var _=wMV(_aH,_az),_aY=E(_aO);return new F(function(){return _9A(_aI,_aJ,_aK,_aL,_aM,_aN,_aY.a,_aY.b,_aY.c,_aY.d,_aY.e,_aY.f,0);});}}else{var _=wMV(_aH,_az),_aZ=E(_aO);return new F(function(){return _9A(_aI,_aJ,_aK,_aL,_aM,_aN,_aZ.a,_aZ.b,_aZ.c,_aZ.d,_aZ.e,_aZ.f,0);});}};if(E(_aS)==254){if(E(_aU)==255){var _=wMV(_aH,_az),_b0=E(_aO);return new F(function(){return _9A(_aI,_aJ,_aK,_aL,_aM+2|0,_aN,_b0.a,_b0.b,_b0.c,_b0.d,_b0.e,_b0.f,0);});}else{return new F(function(){return _aV(0);});}}else{return new F(function(){return _aV(0);});}}else{return new T3(0,_3S,new T6(0,_aI,_aJ,_aK,_aL,_aM,_aN),_aO);}}else{return new F(function(){return A3(_aQ.a,new T6(0,_aI,_aJ,_aK,_aL,_aM,_aN),_aO,_);});}},_b1=false,_b2=function(_){return _1o;},_b3=new T(function(){return B(unCStr("UTF-16"));}),_b4=function(_b5){var _b6=function(_){var _b7=nMV(_b1),_b8=_b7;return new T5(0,function(_b9,_ba,_){var _bb=E(_ba);return new F(function(){return _9o(_b8,_b9,_bb.a,_bb.b,_bb.c,_bb.d,_bb.e,_bb.f,_);});},function(_bc,_bd,_){return new F(function(){return _8D(_b5,_bc,_bd,_);});},_b2,function(_){return new F(function(){return rMV(_b8);});},function(_be,_){var _=wMV(_b8,_be);return _1o;});},_bf=function(_){var _bg=nMV(_5z),_bh=_bg;return new T5(0,function(_bi,_bj,_){var _bk=E(_bi);return new F(function(){return _aG(_bh,_bk.a,_bk.b,_bk.c,_bk.d,_bk.e,_bk.f,_bj,_);});},function(_bc,_bd,_){return new F(function(){return _8d(_b5,_bc,_bd,_);});},_b2,function(_){return new F(function(){return rMV(_bh);});},function(_bl,_){var _=wMV(_bh,_bl);return _1o;});};return new T3(0,_b3,_bf,_b6);},_bm=function(_bn,_bo,_){var _bp=E(_bn),_bq=E(_bo);return new F(function(){return _8V(_bp.a,_bp.b,_bp.c,_bp.d,_bp.e,_bp.f,_bq.a,_bq.b,_bq.c,_bq.d,_bq.e,_bq.f,_);});},_br=function(_bs,_){return new F(function(){return _b2(_);});},_bt=new T(function(){return B(unCStr("UTF-16BE"));}),_bu=function(_bv){var _bw=function(_){return new T5(0,_bm,function(_bc,_bd,_){return new F(function(){return _8D(_bv,_bc,_bd,_);});},_b2,_b2,_br);},_bx=function(_){return new T5(0,_au,function(_bc,_bd,_){return new F(function(){return _8d(_bv,_bc,_bd,_);});},_b2,_b2,_br);};return new T3(0,_bt,_bx,_bw);},_by=function(_bz,_bA,_bB,_bC,_bD,_bE,_bF,_bG,_bH,_bI,_bJ,_bK,_){var _bL=new T6(0,_bz,_bA,_bB,_bC,0,0),_bM=function(_bN,_bO,_){while(1){var _bP=B((function(_bQ,_bR,_){if(_bQ<_bE){if((_bI-_bR|0)>=2){var _bS=readOffAddr("w32",4,_bz,_bQ),_bT=_bS;if(_bT>=65536){if((_bI-_bR|0)>=4){var _bU=_bT-65536|0,_=writeOffAddr("w8",1,plusAddr(_bF,_bR),0,_bU>>10>>>0&255),_=writeOffAddr("w8",1,plusAddr(_bF,_bR+1|0),0,((_bU>>18)+216|0)>>>0&255),_bV=_bU&1023,_=writeOffAddr("w8",1,plusAddr(_bF,_bR+2|0),0,_bV>>>0&255),_=writeOffAddr("w8",1,plusAddr(_bF,_bR+3|0),0,((_bV>>8)+220|0)>>>0&255),_bW=_bQ+1|0,_bX=_bR+4|0;_bN=_bW;_bO=_bX;_=0;return __continue;}else{return new T3(0,_3T,new T(function(){if(_bQ!=_bE){return new T6(0,_bz,_bA,_bB,_bC,_bQ,_bE);}else{return E(_bL);}}),new T6(0,_bF,_bG,_bH,_bI,_bJ,_bR));}}else{var _bY=function(_bZ){if(56320>_bT){var _=writeOffAddr("w8",1,plusAddr(_bF,_bR),0,_bT>>>0&255),_=writeOffAddr("w8",1,plusAddr(_bF,_bR+1|0),0,_bT>>8>>>0&255);return new F(function(){return _bM(_bQ+1|0,_bR+2|0,0);});}else{if(_bT>57343){var _=writeOffAddr("w8",1,plusAddr(_bF,_bR),0,_bT>>>0&255),_=writeOffAddr("w8",1,plusAddr(_bF,_bR+1|0),0,_bT>>8>>>0&255);return new F(function(){return _bM(_bQ+1|0,_bR+2|0,0);});}else{return new T3(0,_8U,new T(function(){if(_bQ!=_bE){return new T6(0,_bz,_bA,_bB,_bC,_bQ,_bE);}else{return E(_bL);}}),new T6(0,_bF,_bG,_bH,_bI,_bJ,_bR));}}};if(55296>_bT){return new F(function(){return _bY(0);});}else{if(_bT>56319){return new F(function(){return _bY(0);});}else{return new T3(0,_8U,new T(function(){if(_bQ!=_bE){return new T6(0,_bz,_bA,_bB,_bC,_bQ,_bE);}else{return E(_bL);}}),new T6(0,_bF,_bG,_bH,_bI,_bJ,_bR));}}}}else{return new T3(0,_3T,new T(function(){if(_bQ!=_bE){return new T6(0,_bz,_bA,_bB,_bC,_bQ,_bE);}else{return E(_bL);}}),new T6(0,_bF,_bG,_bH,_bI,_bJ,_bR));}}else{return new T3(0,_3S,new T(function(){if(_bQ!=_bE){return new T6(0,_bz,_bA,_bB,_bC,_bQ,_bE);}else{return E(_bL);}}),new T6(0,_bF,_bG,_bH,_bI,_bJ,_bR));}})(_bN,_bO,_));if(_bP!=__continue){return _bP;}}};return new F(function(){return _bM(_bD,_bK,_);});},_c0=function(_c1,_c2,_){var _c3=E(_c1),_c4=E(_c2);return new F(function(){return _by(_c3.a,_c3.b,_c3.c,_c3.d,_c3.e,_c3.f,_c4.a,_c4.b,_c4.c,_c4.d,_c4.e,_c4.f,_);});},_c5=new T(function(){return B(unCStr("UTF16-LE"));}),_c6=function(_c7){var _c8=function(_){return new T5(0,_c0,function(_bc,_bd,_){return new F(function(){return _8D(_c7,_bc,_bd,_);});},_b2,_b2,_br);},_c9=function(_){return new T5(0,_aA,function(_bc,_bd,_){return new F(function(){return _8d(_c7,_bc,_bd,_);});},_b2,_b2,_br);};return new T3(0,_c5,_c9,_c8);},_ca=function(_cb,_cc,_cd,_ce,_cf,_cg,_ch,_ci,_cj,_ck,_cl,_cm,_){var _cn=new T6(0,_cb,_cc,_cd,_ce,0,0),_co=function(_cp,_cq,_){if(_cp<_cg){if((_ck-_cq|0)>=4){var _cr=readOffAddr("w32",4,_cb,_cp),_cs=_cr,_ct=function(_cu){if(56320>_cs){var _=writeOffAddr("w8",1,plusAddr(_ch,_cq),0,_cs>>24>>>0&255),_=writeOffAddr("w8",1,plusAddr(_ch,_cq+1|0),0,_cs>>16>>>0&255),_=writeOffAddr("w8",1,plusAddr(_ch,_cq+2|0),0,_cs>>8>>>0&255),_=writeOffAddr("w8",1,plusAddr(_ch,_cq+3|0),0,_cs>>>0&255);return new F(function(){return _co(_cp+1|0,_cq+4|0,0);});}else{if(_cs>57343){var _=writeOffAddr("w8",1,plusAddr(_ch,_cq),0,_cs>>24>>>0&255),_=writeOffAddr("w8",1,plusAddr(_ch,_cq+1|0),0,_cs>>16>>>0&255),_=writeOffAddr("w8",1,plusAddr(_ch,_cq+2|0),0,_cs>>8>>>0&255),_=writeOffAddr("w8",1,plusAddr(_ch,_cq+3|0),0,_cs>>>0&255);return new F(function(){return _co(_cp+1|0,_cq+4|0,0);});}else{return new T3(0,_8U,new T(function(){if(_cp!=_cg){return new T6(0,_cb,_cc,_cd,_ce,_cp,_cg);}else{return E(_cn);}}),new T6(0,_ch,_ci,_cj,_ck,_cl,_cq));}}};if(55296>_cs){return new F(function(){return _ct(0);});}else{if(_cs>56319){return new F(function(){return _ct(0);});}else{return new T3(0,_8U,new T(function(){if(_cp!=_cg){return new T6(0,_cb,_cc,_cd,_ce,_cp,_cg);}else{return E(_cn);}}),new T6(0,_ch,_ci,_cj,_ck,_cl,_cq));}}}else{return new T3(0,_3T,new T(function(){if(_cp!=_cg){return new T6(0,_cb,_cc,_cd,_ce,_cp,_cg);}else{return E(_cn);}}),new T6(0,_ch,_ci,_cj,_ck,_cl,_cq));}}else{return new T3(0,_3S,new T(function(){if(_cp!=_cg){return new T6(0,_cb,_cc,_cd,_ce,_cp,_cg);}else{return E(_cn);}}),new T6(0,_ch,_ci,_cj,_ck,_cl,_cq));}};return new F(function(){return _co(_cf,_cm,_);});},_cv=function(_cw,_cx,_cy,_cz,_cA,_cB,_cC,_cD,_){var _cE=rMV(_cw);if(!E(_cE)){if((_cB-_cD|0)>=4){var _=wMV(_cw,_9n),_=writeOffAddr("w8",1,plusAddr(_cy,_cD),0,0),_=writeOffAddr("w8",1,plusAddr(_cy,_cD+1|0),0,0),_=writeOffAddr("w8",1,plusAddr(_cy,_cD+2|0),0,254),_=writeOffAddr("w8",1,plusAddr(_cy,_cD+3|0),0,255),_cF=E(_cx);return new F(function(){return _ca(_cF.a,_cF.b,_cF.c,_cF.d,_cF.e,_cF.f,_cy,_cz,_cA,_cB,_cC,_cD+4|0,0);});}else{return new T3(0,_3T,_cx,new T6(0,_cy,_cz,_cA,_cB,_cC,_cD));}}else{var _cG=E(_cx);return new F(function(){return _ca(_cG.a,_cG.b,_cG.c,_cG.d,_cG.e,_cG.f,_cy,_cz,_cA,_cB,_cC,_cD,_);});}},_cH=function(_cI,_cJ,_cK,_cL,_cM,_cN,_cO,_cP,_cQ,_cR,_cS,_cT,_){var _cU=new T6(0,_cI,_cJ,_cK,_cL,0,0),_cV=function(_cW,_cX,_){while(1){var _cY=B((function(_cZ,_d0,_){if(_d0<_cR){if((_cN-_cZ|0)>=4){var _d1=readOffAddr("w8",1,plusAddr(_cI,_cZ),0),_d2=readOffAddr("w8",1,plusAddr(_cI,_cZ+1|0),0),_d3=readOffAddr("w8",1,plusAddr(_cI,_cZ+2|0),0),_d4=readOffAddr("w8",1,plusAddr(_cI,_cZ+3|0),0),_d5=((((_d1&4294967295)<<24)+((_d2&4294967295)<<16)|0)+((_d3&4294967295)<<8)|0)+(_d4&4294967295)|0,_d6=function(_d7){if(_d5<=57343){return new T3(0,_8U,new T(function(){if(_cZ!=_cN){return new T6(0,_cI,_cJ,_cK,_cL,_cZ,_cN);}else{return E(_cU);}}),new T6(0,_cO,_cP,_cQ,_cR,_cS,_d0));}else{if(_d5>1114111){return new T3(0,_8U,new T(function(){if(_cZ!=_cN){return new T6(0,_cI,_cJ,_cK,_cL,_cZ,_cN);}else{return E(_cU);}}),new T6(0,_cO,_cP,_cQ,_cR,_cS,_d0));}else{var _=writeOffAddr("w32",4,_cO,_d0,_d5);return new F(function(){return _cV(_cZ+4|0,_d0+1|0,0);});}}};if(_d5<0){return new F(function(){return _d6(0);});}else{if(_d5>=55296){return new F(function(){return _d6(0);});}else{var _=writeOffAddr("w32",4,_cO,_d0,_d5),_d8=_cZ+4|0,_d9=_d0+1|0;_cW=_d8;_cX=_d9;_=0;return __continue;}}}else{return new T3(0,_3S,new T(function(){if(_cZ!=_cN){return new T6(0,_cI,_cJ,_cK,_cL,_cZ,_cN);}else{return E(_cU);}}),new T6(0,_cO,_cP,_cQ,_cR,_cS,_d0));}}else{return new T3(0,_3T,new T(function(){if(_cZ!=_cN){return new T6(0,_cI,_cJ,_cK,_cL,_cZ,_cN);}else{return E(_cU);}}),new T6(0,_cO,_cP,_cQ,_cR,_cS,_d0));}})(_cW,_cX,_));if(_cY!=__continue){return _cY;}}};return new F(function(){return _cV(_cM,_cT,_);});},_da=function(_db,_dc,_dd,_de,_df,_dg,_dh,_di,_dj,_dk,_dl,_dm,_){var _dn=new T6(0,_db,_dc,_dd,_de,0,0),_do=function(_dp,_dq,_){while(1){var _dr=B((function(_ds,_dt,_){if(_dt<_dk){if((_dg-_ds|0)>=4){var _du=readOffAddr("w8",1,plusAddr(_db,_ds),0),_dv=readOffAddr("w8",1,plusAddr(_db,_ds+1|0),0),_dw=readOffAddr("w8",1,plusAddr(_db,_ds+2|0),0),_dx=readOffAddr("w8",1,plusAddr(_db,_ds+3|0),0),_dy=((((_dx&4294967295)<<24)+((_dw&4294967295)<<16)|0)+((_dv&4294967295)<<8)|0)+(_du&4294967295)|0,_dz=function(_dA){if(_dy<=57343){return new T3(0,_8U,new T(function(){if(_ds!=_dg){return new T6(0,_db,_dc,_dd,_de,_ds,_dg);}else{return E(_dn);}}),new T6(0,_dh,_di,_dj,_dk,_dl,_dt));}else{if(_dy>1114111){return new T3(0,_8U,new T(function(){if(_ds!=_dg){return new T6(0,_db,_dc,_dd,_de,_ds,_dg);}else{return E(_dn);}}),new T6(0,_dh,_di,_dj,_dk,_dl,_dt));}else{var _=writeOffAddr("w32",4,_dh,_dt,_dy);return new F(function(){return _do(_ds+4|0,_dt+1|0,0);});}}};if(_dy<0){return new F(function(){return _dz(0);});}else{if(_dy>=55296){return new F(function(){return _dz(0);});}else{var _=writeOffAddr("w32",4,_dh,_dt,_dy),_dB=_ds+4|0,_dC=_dt+1|0;_dp=_dB;_dq=_dC;_=0;return __continue;}}}else{return new T3(0,_3S,new T(function(){if(_ds!=_dg){return new T6(0,_db,_dc,_dd,_de,_ds,_dg);}else{return E(_dn);}}),new T6(0,_dh,_di,_dj,_dk,_dl,_dt));}}else{return new T3(0,_3T,new T(function(){if(_ds!=_dg){return new T6(0,_db,_dc,_dd,_de,_ds,_dg);}else{return E(_dn);}}),new T6(0,_dh,_di,_dj,_dk,_dl,_dt));}})(_dp,_dq,_));if(_dr!=__continue){return _dr;}}};return new F(function(){return _do(_df,_dm,_);});},_dD=function(_dE,_dF,_){var _dG=E(_dE),_dH=E(_dF);return new F(function(){return _cH(_dG.a,_dG.b,_dG.c,_dG.d,_dG.e,_dG.f,_dH.a,_dH.b,_dH.c,_dH.d,_dH.e,_dH.f,_);});},_dI=new T1(1,_dD),_dJ=function(_dK,_dL,_){var _dM=E(_dK),_dN=E(_dL);return new F(function(){return _da(_dM.a,_dM.b,_dM.c,_dM.d,_dM.e,_dM.f,_dN.a,_dN.b,_dN.c,_dN.d,_dN.e,_dN.f,_);});},_dO=new T1(1,_dJ),_dP=function(_dQ,_dR,_dS,_dT,_dU,_dV,_dW,_dX,_){var _dY=rMV(_dQ),_dZ=E(_dY);if(!_dZ._){if((_dW-_dV|0)>=4){var _e0=readOffAddr("w8",1,plusAddr(_dR,_dV),0),_e1=_e0,_e2=readOffAddr("w8",1,plusAddr(_dR,_dV+1|0),0),_e3=_e2,_e4=readOffAddr("w8",1,plusAddr(_dR,_dV+2|0),0),_e5=_e4,_e6=readOffAddr("w8",1,plusAddr(_dR,_dV+3|0),0),_e7=_e6,_e8=function(_e9){if(E(_e1)==255){if(E(_e3)==254){if(!E(_e5)){if(!E(_e7)){var _=wMV(_dQ,_dO),_ea=E(_dX);return new F(function(){return _da(_dR,_dS,_dT,_dU,_dV+4|0,_dW,_ea.a,_ea.b,_ea.c,_ea.d,_ea.e,_ea.f,0);});}else{var _=wMV(_dQ,_dI),_eb=E(_dX);return new F(function(){return _cH(_dR,_dS,_dT,_dU,_dV,_dW,_eb.a,_eb.b,_eb.c,_eb.d,_eb.e,_eb.f,0);});}}else{var _=wMV(_dQ,_dI),_ec=E(_dX);return new F(function(){return _cH(_dR,_dS,_dT,_dU,_dV,_dW,_ec.a,_ec.b,_ec.c,_ec.d,_ec.e,_ec.f,0);});}}else{var _=wMV(_dQ,_dI),_ed=E(_dX);return new F(function(){return _cH(_dR,_dS,_dT,_dU,_dV,_dW,_ed.a,_ed.b,_ed.c,_ed.d,_ed.e,_ed.f,0);});}}else{var _=wMV(_dQ,_dI),_ee=E(_dX);return new F(function(){return _cH(_dR,_dS,_dT,_dU,_dV,_dW,_ee.a,_ee.b,_ee.c,_ee.d,_ee.e,_ee.f,0);});}};if(!E(_e1)){if(!E(_e3)){if(E(_e5)==254){if(E(_e7)==255){var _=wMV(_dQ,_dI),_ef=E(_dX);return new F(function(){return _cH(_dR,_dS,_dT,_dU,_dV+4|0,_dW,_ef.a,_ef.b,_ef.c,_ef.d,_ef.e,_ef.f,0);});}else{return new F(function(){return _e8(0);});}}else{return new F(function(){return _e8(0);});}}else{return new F(function(){return _e8(0);});}}else{return new F(function(){return _e8(0);});}}else{return new T3(0,_3S,new T6(0,_dR,_dS,_dT,_dU,_dV,_dW),_dX);}}else{return new F(function(){return A3(_dZ.a,new T6(0,_dR,_dS,_dT,_dU,_dV,_dW),_dX,_);});}},_eg=function(_){return _1o;},_eh=new T(function(){return B(unCStr("UTF-32"));}),_ei=function(_ej){var _ek=function(_){var _el=nMV(_b1),_em=_el;return new T5(0,function(_en,_eo,_){var _ep=E(_eo);return new F(function(){return _cv(_em,_en,_ep.a,_ep.b,_ep.c,_ep.d,_ep.e,_ep.f,_);});},function(_eq,_er,_){return new F(function(){return _8D(_ej,_eq,_er,_);});},_eg,function(_){return new F(function(){return rMV(_em);});},function(_es,_){var _=wMV(_em,_es);return _1o;});},_et=function(_){var _eu=nMV(_5z),_ev=_eu;return new T5(0,function(_ew,_ex,_){var _ey=E(_ew);return new F(function(){return _dP(_ev,_ey.a,_ey.b,_ey.c,_ey.d,_ey.e,_ey.f,_ex,_);});},function(_eq,_er,_){return new F(function(){return _8d(_ej,_eq,_er,_);});},_eg,function(_){return new F(function(){return rMV(_ev);});},function(_ez,_){var _=wMV(_ev,_ez);return _1o;});};return new T3(0,_eh,_et,_ek);},_eA=function(_eB,_eC,_){var _eD=E(_eB),_eE=E(_eC);return new F(function(){return _ca(_eD.a,_eD.b,_eD.c,_eD.d,_eD.e,_eD.f,_eE.a,_eE.b,_eE.c,_eE.d,_eE.e,_eE.f,_);});},_eF=function(_eG,_){return new F(function(){return _eg(_);});},_eH=new T(function(){return B(unCStr("UTF-32BE"));}),_eI=function(_eJ){var _eK=function(_){return new T5(0,_eA,function(_eq,_er,_){return new F(function(){return _8D(_eJ,_eq,_er,_);});},_eg,_eg,_eF);},_eL=function(_){return new T5(0,_dD,function(_eq,_er,_){return new F(function(){return _8d(_eJ,_eq,_er,_);});},_eg,_eg,_eF);};return new T3(0,_eH,_eL,_eK);},_eM=function(_eN,_eO,_eP,_eQ,_eR,_eS,_eT,_eU,_eV,_eW,_eX,_eY,_){var _eZ=new T6(0,_eN,_eO,_eP,_eQ,0,0),_f0=function(_f1,_f2,_){if(_f1<_eS){if((_eW-_f2|0)>=4){var _f3=readOffAddr("w32",4,_eN,_f1),_f4=_f3,_f5=function(_f6){if(56320>_f4){var _=writeOffAddr("w8",1,plusAddr(_eT,_f2),0,_f4>>>0&255),_=writeOffAddr("w8",1,plusAddr(_eT,_f2+1|0),0,_f4>>8>>>0&255),_=writeOffAddr("w8",1,plusAddr(_eT,_f2+2|0),0,_f4>>16>>>0&255),_=writeOffAddr("w8",1,plusAddr(_eT,_f2+3|0),0,_f4>>24>>>0&255);return new F(function(){return _f0(_f1+1|0,_f2+4|0,0);});}else{if(_f4>57343){var _=writeOffAddr("w8",1,plusAddr(_eT,_f2),0,_f4>>>0&255),_=writeOffAddr("w8",1,plusAddr(_eT,_f2+1|0),0,_f4>>8>>>0&255),_=writeOffAddr("w8",1,plusAddr(_eT,_f2+2|0),0,_f4>>16>>>0&255),_=writeOffAddr("w8",1,plusAddr(_eT,_f2+3|0),0,_f4>>24>>>0&255);return new F(function(){return _f0(_f1+1|0,_f2+4|0,0);});}else{return new T3(0,_8U,new T(function(){if(_f1!=_eS){return new T6(0,_eN,_eO,_eP,_eQ,_f1,_eS);}else{return E(_eZ);}}),new T6(0,_eT,_eU,_eV,_eW,_eX,_f2));}}};if(55296>_f4){return new F(function(){return _f5(0);});}else{if(_f4>56319){return new F(function(){return _f5(0);});}else{return new T3(0,_8U,new T(function(){if(_f1!=_eS){return new T6(0,_eN,_eO,_eP,_eQ,_f1,_eS);}else{return E(_eZ);}}),new T6(0,_eT,_eU,_eV,_eW,_eX,_f2));}}}else{return new T3(0,_3T,new T(function(){if(_f1!=_eS){return new T6(0,_eN,_eO,_eP,_eQ,_f1,_eS);}else{return E(_eZ);}}),new T6(0,_eT,_eU,_eV,_eW,_eX,_f2));}}else{return new T3(0,_3S,new T(function(){if(_f1!=_eS){return new T6(0,_eN,_eO,_eP,_eQ,_f1,_eS);}else{return E(_eZ);}}),new T6(0,_eT,_eU,_eV,_eW,_eX,_f2));}};return new F(function(){return _f0(_eR,_eY,_);});},_f7=function(_f8,_f9,_){var _fa=E(_f8),_fb=E(_f9);return new F(function(){return _eM(_fa.a,_fa.b,_fa.c,_fa.d,_fa.e,_fa.f,_fb.a,_fb.b,_fb.c,_fb.d,_fb.e,_fb.f,_);});},_fc=new T(function(){return B(unCStr("UTF-32LE"));}),_fd=function(_fe){var _ff=function(_){return new T5(0,_f7,function(_eq,_er,_){return new F(function(){return _8D(_fe,_eq,_er,_);});},_eg,_eg,_eF);},_fg=function(_){return new T5(0,_dJ,function(_eq,_er,_){return new F(function(){return _8d(_fe,_eq,_er,_);});},_eg,_eg,_eF);};return new T3(0,_fc,_fg,_ff);},_fh=function(_fi,_fj,_fk,_fl,_fm,_fn,_fo,_fp,_fq,_fr,_fs,_ft,_){var _fu=new T6(0,_fi,_fj,_fk,_fl,0,0),_fv=function(_fw,_fx,_){while(1){var _fy=B((function(_fz,_fA,_){if(_fA<_fr){if(_fz<_fn){var _fB=readOffAddr("w32",4,_fi,_fz),_fC=_fB;if(_fC>127){if(_fC>2047){if(_fC>65535){if((_fr-_fA|0)>=4){var _=writeOffAddr("w8",1,plusAddr(_fo,_fA),0,((_fC>>18)+240|0)>>>0&255),_=writeOffAddr("w8",1,plusAddr(_fo,_fA+1|0),0,((_fC>>12&63)+128|0)>>>0&255),_=writeOffAddr("w8",1,plusAddr(_fo,_fA+2|0),0,((_fC>>6&63)+128|0)>>>0&255),_=writeOffAddr("w8",1,plusAddr(_fo,_fA+3|0),0,((_fC&63)+128|0)>>>0&255),_fD=_fz+1|0,_fE=_fA+4|0;_fw=_fD;_fx=_fE;_=0;return __continue;}else{return new T3(0,_3T,new T(function(){if(_fz!=_fn){return new T6(0,_fi,_fj,_fk,_fl,_fz,_fn);}else{return E(_fu);}}),new T6(0,_fo,_fp,_fq,_fr,_fs,_fA));}}else{var _fF=function(_fG){var _fH=function(_fI){if((_fr-_fA|0)>=3){var _=writeOffAddr("w8",1,plusAddr(_fo,_fA),0,((_fC>>12)+224|0)>>>0&255),_=writeOffAddr("w8",1,plusAddr(_fo,_fA+1|0),0,((_fC>>6&63)+128|0)>>>0&255),_=writeOffAddr("w8",1,plusAddr(_fo,_fA+2|0),0,((_fC&63)+128|0)>>>0&255);return new F(function(){return _fv(_fz+1|0,_fA+3|0,0);});}else{return new T3(0,_3T,new T(function(){if(_fz!=_fn){return new T6(0,_fi,_fj,_fk,_fl,_fz,_fn);}else{return E(_fu);}}),new T6(0,_fo,_fp,_fq,_fr,_fs,_fA));}};if(56320>_fC){return new F(function(){return _fH(0);});}else{if(_fC>57343){return new F(function(){return _fH(0);});}else{return new T3(0,_8U,new T(function(){if(_fz!=_fn){return new T6(0,_fi,_fj,_fk,_fl,_fz,_fn);}else{return E(_fu);}}),new T6(0,_fo,_fp,_fq,_fr,_fs,_fA));}}};if(55296>_fC){return new F(function(){return _fF(0);});}else{if(_fC>56319){return new F(function(){return _fF(0);});}else{return new T3(0,_8U,new T(function(){if(_fz!=_fn){return new T6(0,_fi,_fj,_fk,_fl,_fz,_fn);}else{return E(_fu);}}),new T6(0,_fo,_fp,_fq,_fr,_fs,_fA));}}}}else{if((_fr-_fA|0)>=2){var _=writeOffAddr("w8",1,plusAddr(_fo,_fA),0,((_fC>>6)+192|0)>>>0&255),_=writeOffAddr("w8",1,plusAddr(_fo,_fA+1|0),0,((_fC&63)+128|0)>>>0&255),_fD=_fz+1|0,_fE=_fA+2|0;_fw=_fD;_fx=_fE;_=0;return __continue;}else{return new T3(0,_3T,new T(function(){if(_fz!=_fn){return new T6(0,_fi,_fj,_fk,_fl,_fz,_fn);}else{return E(_fu);}}),new T6(0,_fo,_fp,_fq,_fr,_fs,_fA));}}}else{var _=writeOffAddr("w8",1,plusAddr(_fo,_fA),0,_fC>>>0&255),_fD=_fz+1|0,_fE=_fA+1|0;_fw=_fD;_fx=_fE;_=0;return __continue;}}else{return new T3(0,_3S,new T(function(){if(_fz!=_fn){return new T6(0,_fi,_fj,_fk,_fl,_fz,_fn);}else{return E(_fu);}}),new T6(0,_fo,_fp,_fq,_fr,_fs,_fA));}}else{return new T3(0,_3T,new T(function(){if(_fz!=_fn){return new T6(0,_fi,_fj,_fk,_fl,_fz,_fn);}else{return E(_fu);}}),new T6(0,_fo,_fp,_fq,_fr,_fs,_fA));}})(_fw,_fx,_));if(_fy!=__continue){return _fy;}}};return new F(function(){return _fv(_fm,_ft,_);});},_fJ=function(_fK,_fL,_){var _fM=E(_fK),_fN=E(_fL);return new F(function(){return _fh(_fM.a,_fM.b,_fM.c,_fM.d,_fM.e,_fM.f,_fN.a,_fN.b,_fN.c,_fN.d,_fN.e,_fN.f,_);});},_fO=function(_){return _1o;},_fP=function(_fQ,_){return new F(function(){return _fO(_);});},_fR=function(_fS,_fT,_fU,_fV,_fW,_fX,_fY,_fZ,_g0,_g1,_g2,_g3,_){var _g4=new T6(0,_fS,_fT,_fU,_fV,0,0),_g5=function(_g6,_g7,_){while(1){var _g8=B((function(_g9,_ga,_){if(_ga<_g1){if(_g9<_fX){var _gb=readOffAddr("w8",1,plusAddr(_fS,_g9),0),_gc=_gb;if(_gc>127){var _gd=function(_ge){var _gf=function(_gg){var _gh=function(_gi){if(_gc<240){return new T3(0,_8U,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga));}else{switch(_fX-_g9|0){case 1:return new T3(0,_3S,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga));case 2:var _gj=readOffAddr("w8",1,plusAddr(_fS,_g9+1|0),0),_gk=_gj,_gl=function(_gm){var _gn=function(_go){return (E(_gc)==244)?(_gk<128)?new T3(0,_8U,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga)):(_gk>143)?new T3(0,_8U,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga)):new T3(0,_3S,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga)):new T3(0,_8U,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga));};if(_gc<241){return new F(function(){return _gn(0);});}else{if(_gc>243){return new F(function(){return _gn(0);});}else{if(_gk<128){return new F(function(){return _gn(0);});}else{if(_gk>191){return new F(function(){return _gn(0);});}else{return new T3(0,_3S,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga));}}}}};if(E(_gc)==240){if(_gk<144){return new F(function(){return _gl(0);});}else{if(_gk>191){return new F(function(){return _gl(0);});}else{return new T3(0,_3S,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga));}}}else{return new F(function(){return _gl(0);});}break;case 3:var _gp=readOffAddr("w8",1,plusAddr(_fS,_g9+1|0),0),_gq=_gp,_gr=readOffAddr("w8",1,plusAddr(_fS,_g9+2|0),0),_gs=_gr,_gt=function(_gu){var _gv=function(_gw){return (E(_gc)==244)?(_gq<128)?new T3(0,_8U,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga)):(_gq>143)?new T3(0,_8U,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga)):(_gs<128)?new T3(0,_8U,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga)):(_gs>191)?new T3(0,_8U,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga)):new T3(0,_3S,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga)):new T3(0,_8U,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga));};if(_gc<241){return new F(function(){return _gv(0);});}else{if(_gc>243){return new F(function(){return _gv(0);});}else{if(_gq<128){return new F(function(){return _gv(0);});}else{if(_gq>191){return new F(function(){return _gv(0);});}else{if(_gs<128){return new F(function(){return _gv(0);});}else{if(_gs>191){return new F(function(){return _gv(0);});}else{return new T3(0,_3S,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga));}}}}}}};if(E(_gc)==240){if(_gq<144){return new F(function(){return _gt(0);});}else{if(_gq>191){return new F(function(){return _gt(0);});}else{if(_gs<128){return new F(function(){return _gt(0);});}else{if(_gs>191){return new F(function(){return _gt(0);});}else{return new T3(0,_3S,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga));}}}}}else{return new F(function(){return _gt(0);});}break;default:var _gx=readOffAddr("w8",1,plusAddr(_fS,_g9+1|0),0),_gy=_gx,_gz=readOffAddr("w8",1,plusAddr(_fS,_g9+2|0),0),_gA=_gz,_gB=readOffAddr("w8",1,plusAddr(_fS,_g9+3|0),0),_gC=_gB,_gD=function(_gE){var _gF=function(_gG){if(E(_gc)==244){if(_gy<128){return new T3(0,_8U,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga));}else{if(_gy>143){return new T3(0,_8U,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga));}else{if(_gA<128){return new T3(0,_8U,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga));}else{if(_gA>191){return new T3(0,_8U,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga));}else{if(_gC<128){return new T3(0,_8U,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga));}else{if(_gC>191){return new T3(0,_8U,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga));}else{var _=writeOffAddr("w32",4,_fY,_ga,((1048576+(((_gy&4294967295)-128|0)<<12)|0)+(((_gA&4294967295)-128|0)<<6)|0)+((_gC&4294967295)-128|0)|0);return new F(function(){return _g5(_g9+4|0,_ga+1|0,0);});}}}}}}}else{return new T3(0,_8U,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga));}};if(_gc<241){return new F(function(){return _gF(0);});}else{if(_gc>243){return new F(function(){return _gF(0);});}else{if(_gy<128){return new F(function(){return _gF(0);});}else{if(_gy>191){return new F(function(){return _gF(0);});}else{if(_gA<128){return new F(function(){return _gF(0);});}else{if(_gA>191){return new F(function(){return _gF(0);});}else{if(_gC<128){return new F(function(){return _gF(0);});}else{if(_gC>191){return new F(function(){return _gF(0);});}else{var _=writeOffAddr("w32",4,_fY,_ga,(((((_gc&4294967295)-240|0)<<18)+(((_gy&4294967295)-128|0)<<12)|0)+(((_gA&4294967295)-128|0)<<6)|0)+((_gC&4294967295)-128|0)|0);return new F(function(){return _g5(_g9+4|0,_ga+1|0,0);});}}}}}}}}};if(E(_gc)==240){if(_gy<144){return new F(function(){return _gD(0);});}else{if(_gy>191){return new F(function(){return _gD(0);});}else{if(_gA<128){return new F(function(){return _gD(0);});}else{if(_gA>191){return new F(function(){return _gD(0);});}else{if(_gC<128){return new F(function(){return _gD(0);});}else{if(_gC>191){return new F(function(){return _gD(0);});}else{var _=writeOffAddr("w32",4,_fY,_ga,((((_gy&4294967295)-128|0)<<12)+(((_gA&4294967295)-128|0)<<6)|0)+((_gC&4294967295)-128|0)|0);return new F(function(){return _g5(_g9+4|0,_ga+1|0,0);});}}}}}}}else{return new F(function(){return _gD(0);});}}}};if(_gc<224){return new F(function(){return _gh(0);});}else{if(_gc>239){return new F(function(){return _gh(0);});}else{switch(_fX-_g9|0){case 1:return new T3(0,_3S,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga));case 2:var _gH=readOffAddr("w8",1,plusAddr(_fS,_g9+1|0),0),_gI=_gH,_gJ=function(_gK){var _gL=function(_gM){var _gN=function(_gO){return (_gc<238)?new T3(0,_8U,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga)):(_gI<128)?new T3(0,_8U,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga)):(_gI>191)?new T3(0,_8U,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga)):new T3(0,_3S,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga));};if(E(_gc)==237){if(_gI<128){return new F(function(){return _gN(0);});}else{if(_gI>159){return new F(function(){return _gN(0);});}else{return new T3(0,_3S,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga));}}}else{return new F(function(){return _gN(0);});}};if(_gc<225){return new F(function(){return _gL(0);});}else{if(_gc>236){return new F(function(){return _gL(0);});}else{if(_gI<128){return new F(function(){return _gL(0);});}else{if(_gI>191){return new F(function(){return _gL(0);});}else{return new T3(0,_3S,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga));}}}}};if(E(_gc)==224){if(_gI<160){return new F(function(){return _gJ(0);});}else{if(_gI>191){return new F(function(){return _gJ(0);});}else{return new T3(0,_3S,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga));}}}else{return new F(function(){return _gJ(0);});}break;default:var _gP=readOffAddr("w8",1,plusAddr(_fS,_g9+1|0),0),_gQ=_gP,_gR=readOffAddr("w8",1,plusAddr(_fS,_g9+2|0),0),_gS=_gR,_gT=function(_gU){var _gV=function(_gW){var _gX=function(_gY){if(_gc<238){return new T3(0,_8U,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga));}else{if(_gQ<128){return new T3(0,_8U,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga));}else{if(_gQ>191){return new T3(0,_8U,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga));}else{if(_gS<128){return new T3(0,_8U,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga));}else{if(_gS>191){return new T3(0,_8U,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga));}else{var _=writeOffAddr("w32",4,_fY,_ga,((((_gc&4294967295)-224|0)<<12)+(((_gQ&4294967295)-128|0)<<6)|0)+((_gS&4294967295)-128|0)|0);return new F(function(){return _g5(_g9+3|0,_ga+1|0,0);});}}}}}};if(E(_gc)==237){if(_gQ<128){return new F(function(){return _gX(0);});}else{if(_gQ>159){return new F(function(){return _gX(0);});}else{if(_gS<128){return new F(function(){return _gX(0);});}else{if(_gS>191){return new F(function(){return _gX(0);});}else{var _=writeOffAddr("w32",4,_fY,_ga,(53248+(((_gQ&4294967295)-128|0)<<6)|0)+((_gS&4294967295)-128|0)|0);return new F(function(){return _g5(_g9+3|0,_ga+1|0,0);});}}}}}else{return new F(function(){return _gX(0);});}};if(_gc<225){return new F(function(){return _gV(0);});}else{if(_gc>236){return new F(function(){return _gV(0);});}else{if(_gQ<128){return new F(function(){return _gV(0);});}else{if(_gQ>191){return new F(function(){return _gV(0);});}else{if(_gS<128){return new F(function(){return _gV(0);});}else{if(_gS>191){return new F(function(){return _gV(0);});}else{var _=writeOffAddr("w32",4,_fY,_ga,((((_gc&4294967295)-224|0)<<12)+(((_gQ&4294967295)-128|0)<<6)|0)+((_gS&4294967295)-128|0)|0);return new F(function(){return _g5(_g9+3|0,_ga+1|0,0);});}}}}}}};if(E(_gc)==224){if(_gQ<160){return new F(function(){return _gT(0);});}else{if(_gQ>191){return new F(function(){return _gT(0);});}else{if(_gS<128){return new F(function(){return _gT(0);});}else{if(_gS>191){return new F(function(){return _gT(0);});}else{var _=writeOffAddr("w32",4,_fY,_ga,(((_gQ&4294967295)-128|0)<<6)+((_gS&4294967295)-128|0)|0);return new F(function(){return _g5(_g9+3|0,_ga+1|0,0);});}}}}}else{return new F(function(){return _gT(0);});}}}}};if(_gc<194){return new F(function(){return _gf(0);});}else{if(_gc>223){return new F(function(){return _gf(0);});}else{if((_fX-_g9|0)>=2){var _gZ=readOffAddr("w8",1,plusAddr(_fS,_g9+1|0),0);if(_gZ>=128){if(_gZ<192){var _=writeOffAddr("w32",4,_fY,_ga,(((_gc&4294967295)-192|0)<<6)+((_gZ&4294967295)-128|0)|0);return new F(function(){return _g5(_g9+2|0,_ga+1|0,0);});}else{return new T3(0,_8U,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga));}}else{return new T3(0,_8U,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga));}}else{return new T3(0,_3S,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga));}}}};if(_gc<192){return new F(function(){return _gd(0);});}else{if(_gc>193){return new F(function(){return _gd(0);});}else{return new T3(0,_8U,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga));}}}else{var _=writeOffAddr("w32",4,_fY,_ga,_gc&4294967295),_h0=_g9+1|0,_h1=_ga+1|0;_g6=_h0;_g7=_h1;_=0;return __continue;}}else{return new T3(0,_3S,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga));}}else{return new T3(0,_3T,new T(function(){if(_g9!=_fX){return new T6(0,_fS,_fT,_fU,_fV,_g9,_fX);}else{return E(_g4);}}),new T6(0,_fY,_fZ,_g0,_g1,_g2,_ga));}})(_g6,_g7,_));if(_g8!=__continue){return _g8;}}};return new F(function(){return _g5(_fW,_g3,_);});},_h2=function(_h3,_h4,_){var _h5=E(_h3),_h6=E(_h4);return new F(function(){return _fR(_h5.a,_h5.b,_h5.c,_h5.d,_h5.e,_h5.f,_h6.a,_h6.b,_h6.c,_h6.d,_h6.e,_h6.f,_);});},_h7=new T(function(){return B(unCStr("UTF-8"));}),_h8=function(_h9){var _ha=function(_){return new T5(0,_fJ,function(_hb,_hc,_){return new F(function(){return _8D(_h9,_hb,_hc,_);});},_fO,_fO,_fP);},_hd=function(_){return new T5(0,_h2,function(_hb,_hc,_){return new F(function(){return _8d(_h9,_hb,_hc,_);});},_fO,_fO,_fP);};return new T3(0,_h7,_hd,_ha);},_5W=function(_he,_hf,_){var _hg=B(_3A(_hf));if(!B(_3b(_hg,_3i))){if(!B(_3b(_hg,_3h))){if(!B(_3b(_hg,_3g))){if(!B(_3b(_hg,_3m))){if(!B(_3b(_hg,_3l))){if(!B(_3b(_hg,_3k))){if(!B(_3b(_hg,_3j))){return new F(function(){return _8J(_he,_hf,_);});}else{return new T(function(){return B(_h8(_he));});}}else{return new T(function(){return B(_fd(_he));});}}else{return new T(function(){return B(_eI(_he));});}}else{return new T(function(){return B(_ei(_he));});}}else{return new T(function(){return B(_c6(_he));});}}else{return new T(function(){return B(_bu(_he));});}}else{return new T(function(){return B(_b4(_he));});}},_hh=function(_){return new F(function(){return _5W(_3a,_5U,0);});},_hi=new T(function(){return B(_5R(_hh));}),_hj=function(_){var _hk=nMV(_hi),_hl=_hk;return new T2(0,function(_){return new F(function(){return rMV(_hl);});},function(_hm,_){var _=wMV(_hl,_hm);return _1o;});},_hn=new T(function(){return B(_5R(_hj));}),_ho=new T(function(){return B(unCStr("readDirStream"));}),_hp=function(_hq,_){var _hr=newByteArr(4),_hs=function(_ht,_){while(1){var _hu=__hscore_set_errno(0),_hv=__hscore_readdir(E(_hq),_ht);if(!E(_hv)){var _hw=die("Unsupported PrimOp: readAddrOffAddr#");if(!addrEq(_hw,0)){var _hx=__hscore_d_name(_hw),_hy=B(A1(E(_hn).a,_)),_hz=B(_2v(_hy,_hx,_)),_hA=__hscore_free_dirent(_hw);return _hz;}else{return _N;}}else{var _hB=__hscore_get_errno();switch(E(_hB)){case 0:return _N;case 4:continue;default:return new F(function(){return _6e(_ho,_);});}}}},_hC=B(_hs(_hr,_));return _hC;},_hD=function(_hE,_){var _hF=function(_hG,_){while(1){var _hH=B((function(_hI,_){var _hJ=B(_hp(_hE,_)),_hK=E(_hJ);if(!_hK._){return new T(function(){return B(A1(_hI,_N));});}else{_hG=function(_hL){return new F(function(){return A1(_hI,new T2(1,_hK,_hL));});};return __continue;}})(_hG,_));if(_hH!=__continue){return _hH;}}};return new F(function(){return _hF(_1m,_);});},_hM=new T(function(){return B(unCStr("getDirectoryContents"));}),_hN=new T(function(){return B(unCStr(":"));}),_hO=function(_hP,_hQ,_){var _hR=function(_hS,_){var _hT=E(_hS),_hU=B(A2(_44,_hT.a,_)),_hV=hs_eqWord64(_hU.a,new Long(4053623282,1685460941,true));if(!_hV){return new F(function(){return die(_hT);});}else{var _hW=hs_eqWord64(_hU.b,new Long(3693590983,2507416641,true));if(!_hW){return new F(function(){return die(_hT);});}else{var _hX=new T(function(){return B(_5x(new T(function(){return B(A1(_hP,_hT.b));})));});return new F(function(){return die(_hX);});}}};return new F(function(){return jsCatch(_hQ,_hR);});},_hY=function(_hZ,_){return new F(function(){return ghczuwrapperZC0ZCHMhPQD6hrJtKr0n8PDQlkkZCSystemziPosixziDirectoryZCopendir(E(_hZ));});},_i0=function(_i1,_){return new F(function(){return _hY(_i1,_);});},_i2=function(_i3,_i4,_i5,_i6,_i7,_i8,_){var _i9=nMV(_20),_ia=function(_ib,_ic,_){while(1){var _id=B((function(_ie,_if,_){var _ig=E(_i3),_ih=B(A3(_ig.a,_ie,_if,_)),_ii=E(_ih),_ij=_ii.c,_ik=E(_ii.b);if(_ik.e!=_ik.f){if(E(_ii.a)==1){return _5z;}else{var _il=B(A3(_ig.b,_ik,_ij,_)),_im=E(_il);_ib=_im.a;_ic=_im.b;return __continue;}}else{var _in=function(_io){var _ip=E(_ij),_iq=_ip.a,_ir=_ip.b,_is=_ip.e,_it=_ip.f;if(!E(_i4)){var _iu=B(A2(_i8,new T2(0,_iq,_it-_is|0),_));return new T1(1,_iu);}else{var _=writeOffAddr("w8",1,_iq,_it,0),_iv=B(A2(_i8,new T2(0,_iq,_it-_is|0),_));return new T1(1,_iv);}};if(!E(_i4)){return new F(function(){return _in(_);});}else{var _iw=E(_ij);if(!(_iw.d-_iw.f|0)){return _5z;}else{return new F(function(){return _in(_);});}}}})(_ib,_ic,_));if(_id!=__continue){return _id;}}};return new F(function(){return _ia(_i5,new T(function(){return new T6(0,_i6,new T1(0,_i9),_22,E(_i7),0,0);}),_);});},_ix=function(_iy){return E(E(_iy).d);},_iz=function(_iA,_iB,_iC,_){var _iD=function(_iE,_iF,_){while(1){var _iG=E(_iE);if(!_iG._){return _1o;}else{var _iH=B(A(_ix,[_iA,_iB,_iF,_iG.a,_])),_iI=_iF+1|0;_iE=_iG.b;_iF=_iI;continue;}}};return new F(function(){return _iD(_iC,0,_);});},_iJ=function(_iK,_iL,_iM,_){var _iN=function(_iO){return new F(function(){return A1(_iM,E(_iO).a);});},_iP=function(_iQ,_){var _iR=B(_7j(_iL,0)),_iS=newByteArr(imul(_iR,4)|0),_iT=_iS,_iU=B(_iz(_1L,_iT,_iL,_)),_iV=nMV(_20),_iW=_iV,_iX=function(_iY,_){var _iZ=newByteArr(_iY),_j0=B(_i2(_iQ,_9n,new T6(0,_iT,new T1(0,_iW),_21,_iR,0,_iR),_iZ,_iY,_iN,_)),_j1=E(_j0);if(!_j1._){var _j2=B(_iX(imul(_iY,2)|0,_));return _j2;}else{return _j1.a;}},_j3=B(_iX(_iR+1|0,_));return _j3;};return new F(function(){return _23(E(_iK).c,_2r,_iP,_);});},_j4=new T(function(){return B(unCStr("openDirStream"));}),_j5=function(_j6,_j7,_){var _j8=__hscore_get_errno(),_j9=new T(function(){return B(_5x(new T(function(){return B(_64(_j6,_j8,_5z,new T1(1,_j7)));})));});return new F(function(){return die(_j9);});},_ja=function(_jb,_jc,_jd,_je,_){while(1){var _jf=B(A1(_je,_));if(!B(A1(_jb,_jf))){return _jf;}else{var _jg=__hscore_get_errno();if(E(_jg)==4){continue;}else{return new F(function(){return _j5(_jc,_jd,_);});}}}},_jh=function(_ji){return new F(function(){return addrEq(E(_ji),0);});},_jj=function(_jk,_){var _jl=B(A1(E(_hn).a,_)),_jm=function(_jn,_){return new F(function(){return _ja(_jh,_j4,_jk,function(_){return new F(function(){return _i0(_jn,_);});},_);});};return new F(function(){return _iJ(_jl,_jk,_jm,_);});},_jo=function(_jp,_jq,_jr,_){while(1){var _js=B(A1(_jr,_));if(!B(A1(_jp,_js))){return _js;}else{var _jt=__hscore_get_errno();if(E(_jt)==4){continue;}else{return new F(function(){return _6e(_jq,_);});}}}},_ju=function(_jv,_){var _jw=function(_){if(!E(0)){var _jx=function(_){var _jy=B(_jj(_jv,_)),_jz=_jy,_jA=function(_jB,_){var _jC=B(_jo(_1j,_1l,function(_){return new F(function(){return closedir(E(_jz));});},_));return new F(function(){return die(_jB);});},_jD=function(_){return new F(function(){return _hD(_jz,_);});},_jE=jsCatch(function(_){return new F(function(){return _jD();});},_jA),_jF=B(_jo(_1j,_1l,function(_){return new F(function(){return closedir(E(_jz));});},_));return _jE;};return new F(function(){return _jx();});}else{var _jG=B(_jj(_jv,_)),_jH=_jG,_jI=function(_jJ,_){var _jK=B(_jo(_1j,_1l,function(_){return new F(function(){return closedir(E(_jH));});},_));return new F(function(){return die(_jJ);});},_jL=jsCatch(function(_){return new F(function(){return _hD(_jH,_);});},_jI),_jM=B(_jo(_1j,_1l,function(_){return new F(function(){return closedir(E(_jH));});},_));return _jL;}},_jN=function(_jO){var _jP=E(_jO),_jQ=new T(function(){return B(_1f(_hM,new T(function(){var _jR=E(_jP.c);if(!_jR._){return __Z;}else{return B(_1f(_hN,_jR));}},1)));});return new T6(0,_jP.a,_jP.b,_jQ,_jP.d,_jP.e,new T1(1,_jv));};return new F(function(){return _hO(_jN,_jw,_);});},_jS=function(_jT,_jU){while(1){var _jV=E(_jT);if(!_jV._){return (E(_jU)._==0)?true:false;}else{var _jW=E(_jU);if(!_jW._){return false;}else{if(E(_jV.a)!=E(_jW.a)){return false;}else{_jT=_jV.b;_jU=_jW.b;continue;}}}}},_jX=function(_jY,_jZ){return (!B(_jS(_jY,_jZ)))?true:false;},_k0=new T(function(){return B(unCStr(".."));}),_k1=new T(function(){return B(unCStr("."));}),_k2=function(_k3){if(!B(_jS(_k3,_k1))){return new F(function(){return _jX(_k3,_k0);});}else{return false;}},_k4=function(_k5){var _k6=new T(function(){var _k7=E(_k5);if(!_k7._){return E(_W);}else{var _k8=E(_k7.a);if(_k8._==1){var _k9=new T(function(){return fromJSStr(_k8.a);}),_ka=function(_kb){var _kc=function(_){var _kd=B(_ju(_k9,_));return new T(function(){return B(A1(_kb,new T(function(){return B(_15(_k2,_kd));})));});};return new T1(0,_kc);};return E(_ka);}else{return B(_T(_k8));}}}),_ke=function(_kf){var _kg=function(_kh){return new F(function(){return A1(_kf,new T(function(){return B(_13(_kh));}));});};return new F(function(){return A1(_k6,_kg);});};return E(_ke);},_ki=function(_kj,_kk){return new F(function(){return _k4(_kk);});},_kl=19,_km=new T2(0,_kl,_kl),_kn=new T(function(){return B(unCStr("sptEntry:0"));}),_ko=new T4(0,_8,_7,_kn,_km),_kp=new T3(0,_b,_ko,_ki),_kq=new T2(0,new Long(3059772246,3639684881,true),new Long(3998037628,3893224407,true)),_kr=new T(function(){return B(unCStr("GHC.Tuple"));}),_ks=new T(function(){return B(unCStr("ghc-prim"));}),_kt=new T(function(){return B(unCStr("()"));}),_ku=new T5(0,new Long(2170319554,3688774321,true),new Long(26914641,3196943984,true),_ks,_kr,_kt),_kv=new T5(0,new Long(2170319554,3688774321,true),new Long(26914641,3196943984,true),_ku,_N,_N),_kw=new T2(1,_kv,_N),_kx=new T(function(){return B(_1f(_N,_kw));}),_ky=function(_kz){var _kA=E(_kz);if(!_kA._){return __Z;}else{var _kB=E(_kA.a);return new T2(1,new T2(0,_kB.a,_kB.b),new T(function(){return B(_ky(_kA.b));}));}},_kC=new T(function(){return B(_ky(_kx));}),_kD=new T2(1,_kq,_kC),_kE=new T(function(){return B(unCStr("Haste.App.Server.Type"));}),_kF=new T(function(){return B(unCStr("6cKLJVuw5DJ4ZCG47q2sCl"));}),_kG=new T(function(){return B(unCStr("EnvServer"));}),_kH=new T5(0,new Long(3059772246,3639684881,true),new Long(3998037628,3893224407,true),_kF,_kE,_kG),_kI=function(_kJ,_kK){if(_kK<64){var _kL=hs_uncheckedShiftRL64(_kJ,_kK);return E(_kL);}else{var _kM=hs_wordToWord64(0);return E(_kM);}},_kN=function(_kO,_kP,_kQ,_){while(1){var _kR=B((function(_kS,_kT,_kU,_){var _kV=E(_kT);if(!_kV){return _1o;}else{var _kW=E(_kU),_kX=E(_kS),_kY=hs_word64ToWord(_kW),_=writeOffAddr("w8",1,_kX,_kV-1|0,_kY&255);_kO=_kX;_kP=_kV-1|0;_kQ=new T(function(){return B(_kI(_kW,8));},1);return __continue;}})(_kO,_kP,_kQ,_));if(_kR!=__continue){return _kR;}}},_kZ=function(_l0,_l1,_l2,_){var _l3=B(_kN(_l0,8,_l1,_));return new F(function(){return _kN(new T(function(){return plusAddr(E(_l0),8);},1),8,_l2,_);});},_l4=function(_l5,_l6,_){var _l7=E(_l6);return new F(function(){return _kZ(_l5,_l7.a,_l7.b,_);});},_l8=function(_l9,_la){return new T2(0,E(_l9),E(_la));},_lb=function(_lc,_ld){if(_ld<64){var _le=hs_uncheckedShiftL64(_lc,_ld);return E(_le);}else{var _lf=hs_wordToWord64(0);return E(_lf);}},_lg=function(_lh,_li,_lj,_){while(1){var _lk=E(_li);if(!_lk){return _lj;}else{var _ll=E(_lh),_lm=readOffAddr("w8",1,_ll,0),_ln=hs_wordToWord64(_lm),_lo=hs_or64(B(_lb(_lj,8)),_ln);_lh=plusAddr(_ll,1);_li=_lk-1|0;_lj=_lo;continue;}}},_lp=function(_lq,_){var _lr=B(_lg(_lq,8,new Long(0,0,true),_)),_ls=B(_lg(new T(function(){return plusAddr(E(_lq),8);},1),8,new Long(0,0,true),_));return new T(function(){return B(_l8(_lr,_ls));});},_lt=function(_lu,_lv,_lw,_){var _lx=E(_lw);return new F(function(){return _kZ(new T(function(){return plusAddr(E(_lu),E(_lv));}),_lx.a,_lx.b,_);});},_ly=function(_lz,_lA){return new F(function(){return plusAddr(E(_lz),E(_lA));});},_lB=function(_lC,_lD,_){return new F(function(){return _lp(new T(function(){return B(_ly(_lC,_lD));}),_);});},_lE=function(_lF,_lG,_lH,_){var _lI=E(_lH);return new F(function(){return _kZ(new T(function(){return plusAddr(E(_lF),imul(E(_lG),16)|0);}),_lI.a,_lI.b,_);});},_lJ=function(_lK,_lL,_){return new F(function(){return _lp(new T(function(){return plusAddr(E(_lK),imul(E(_lL),16)|0);}),_);});},_lM=8,_lN=function(_lO){return E(_lM);},_lP=16,_lQ=function(_lR){return E(_lP);},_lS={_:0,a:_lQ,b:_lN,c:_lJ,d:_lE,e:_lB,f:_lt,g:_lp,h:_l4},_lT=function(_lU,_lV,_){var _lW=newByteArr(88),_lX=__hsbase_MD5Init(_lW),_lY=__hsbase_MD5Update(_lW,E(_lU),E(_lV)),_lZ=newByteArr(16),_m0=__hsbase_MD5Final(_lZ,_lW),_m1=B(_lp(_lZ,_));return _m1;},_m2=function(_m3){return new F(function(){return _5R(function(_){var _m4=B(_7j(_m3,0)),_m5=newByteArr(imul(_m4,16)|0),_m6=B(_iz(_lS,_m5,_m3,_)),_m7=B(_lT(_m5,imul(_m4,16)|0,_));return _m7;});});},_m8=new T(function(){var _m9=E(_kx);if(!_m9._){return new T5(0,new Long(3059772246,3639684881,true),new Long(3998037628,3893224407,true),_kH,_N,_N);}else{var _ma=B(_m2(_kD));return new T5(0,_ma.a,_ma.b,_kH,_N,_m9);}}),_mb=10,_mc=function(_md,_me){var _mf=E(_me);if(!_mf._){return E(_1m);}else{var _mg=_mf.a,_mh=E(_mf.b);if(!_mh._){var _mi=E(_mg);return new F(function(){return _mj(_mb,_mi.c,_mi.d,_mi.e);});}else{var _mk=new T(function(){var _ml=E(_mg);return B(_mj(_mb,_ml.c,_ml.d,_ml.e));}),_mm=new T(function(){return B(_mc(_md,_mh));}),_mn=function(_mo){var _mp=new T(function(){return B(A1(_md,new T(function(){return B(A1(_mm,_mo));})));});return new F(function(){return A1(_mk,_mp);});};return E(_mn);}}},_mq=function(_mr,_ms,_mt,_mu,_mv,_mw,_mx){var _my=new T5(0,_mr,_ms,_mt,_mu,_mv),_mz=function(_mA){var _mB=new T(function(){var _mC=new T(function(){return B(_ky(_mx));}),_mD=function(_mE){var _mF=E(_mE);if(!_mF._){return E(_mC);}else{var _mG=E(_mF.a);return new T2(1,new T2(0,_mG.a,_mG.b),new T(function(){return B(_mD(_mF.b));}));}};return B(_mD(_mw));}),_mH=B(A1(_m2,new T2(1,new T2(0,_mr,_ms),_mB)));return new T5(0,_mH.a,_mH.b,_my,_mw,_mx);};if(!E(_mw)._){if(!E(_mx)._){return new T5(0,_mr,_ms,_my,_N,_N);}else{return new F(function(){return _mz(_);});}}else{return new F(function(){return _mz(_);});}},_mI=new T(function(){return B(unCStr("ghc-prim"));}),_mJ=new T(function(){return B(unCStr("()"));}),_mK=new T(function(){return B(unCStr("GHC.Tuple"));}),_mL=new T5(0,new Long(2170319554,3688774321,true),new Long(26914641,3196943984,true),_mI,_mK,_mJ),_mM=new T5(0,new Long(2170319554,3688774321,true),new Long(26914641,3196943984,true),_mL,_N,_N),_mN=new T2(1,_mM,_N),_mO=new T(function(){return B(_1f(_N,_mN));}),_mP=new T(function(){return B(unCStr("[]"));}),_mQ=new T(function(){return B(unCStr("GHC.Types"));}),_mR=new T(function(){return E(B(_mq(new Long(4033920485,4128112366,true),new Long(786266835,2297333520,true),_mI,_mQ,_mP,_N,_mO)).c);}),_mS=8,_mT=32,_mU=function(_mV){return new T2(1,_mT,_mV);},_mW=new T(function(){return B(unCStr(" -> "));}),_mX=9,_mY=93,_mZ=91,_n0=41,_n1=44,_n2=function(_mV){return new T2(1,_n1,_mV);},_n3=40,_n4=0,_mj=function(_n5,_n6,_n7,_n8){var _n9=E(_n8);if(!_n9._){return function(_na){return new F(function(){return _1f(E(_n6).e,_na);});};}else{var _nb=_n9.a,_nc=function(_nd){var _ne=E(_n6).e,_nf=function(_ng){var _nh=new T(function(){return B(_mc(_mU,B(_1f(_n7,_n9))));});if(E(_n5)<=9){var _ni=function(_nj){return new F(function(){return _1f(_ne,new T2(1,_mT,new T(function(){return B(A1(_nh,_nj));})));});};return E(_ni);}else{var _nk=function(_nl){var _nm=new T(function(){return B(_1f(_ne,new T2(1,_mT,new T(function(){return B(A1(_nh,new T2(1,_3r,_nl)));}))));});return new T2(1,_3s,_nm);};return E(_nk);}},_nn=E(_ne);if(!_nn._){return new F(function(){return _nf(_);});}else{if(E(_nn.a)==40){var _no=E(_nn.b);if(!_no._){return new F(function(){return _nf(_);});}else{if(E(_no.a)==44){var _np=new T(function(){return B(_mc(_n2,_n9));}),_nq=function(_nr){return new T2(1,_n3,new T(function(){return B(A1(_np,new T2(1,_n0,_nr)));}));};return E(_nq);}else{return new F(function(){return _nf(_);});}}}else{return new F(function(){return _nf(_);});}}},_ns=E(_n9.b);if(!_ns._){var _nt=E(_n6),_nu=E(_mR),_nv=hs_eqWord64(_nt.a,_nu.a);if(!_nv){return new F(function(){return _nc(_);});}else{var _nw=hs_eqWord64(_nt.b,_nu.b);if(!_nw){return new F(function(){return _nc(_);});}else{var _nx=new T(function(){var _ny=E(_nb);return B(_mj(_n4,_ny.c,_ny.d,_ny.e));}),_nz=function(_nA){return new T2(1,_mZ,new T(function(){return B(A1(_nx,new T2(1,_mY,_nA)));}));};return E(_nz);}}}else{if(!E(_ns.b)._){var _nB=E(_n6),_nC=hs_eqWord64(_nB.a,new Long(4173248105,3789542698,true));if(!_nC){return new F(function(){return _nc(_);});}else{var _nD=hs_eqWord64(_nB.b,new Long(4270398258,833198194,true));if(!_nD){return new F(function(){return _nc(_);});}else{var _nE=new T(function(){var _nF=E(_nb);return B(_mj(_mX,_nF.c,_nF.d,_nF.e));}),_nG=new T(function(){var _nH=E(_ns.a);return B(_mj(_mS,_nH.c,_nH.d,_nH.e));});if(E(_n5)<=8){var _nI=function(_nJ){var _nK=new T(function(){return B(_1f(_mW,new T(function(){return B(A1(_nG,_nJ));},1)));});return new F(function(){return A1(_nE,_nK);});};return E(_nI);}else{var _nL=function(_nM){var _nN=new T(function(){var _nO=new T(function(){return B(_1f(_mW,new T(function(){return B(A1(_nG,new T2(1,_3r,_nM)));},1)));});return B(A1(_nE,_nO));});return new T2(1,_3s,_nN);};return E(_nL);}}}}else{return new F(function(){return _nc(_);});}}}},_nP=function(_nQ,_nR){while(1){var _nS=E(_nR);if(!_nS._){return E(_nQ);}else{var _nT=(imul(_nQ,33)>>>0&65535)+(E(_nS.a)>>>0&65535)>>>0&65535;_nQ=_nT;_nR=_nS.b;continue;}}},_nU=new T(function(){return eval("(function(){return location.hostname;})");}),_nV=function(_){var _nW=__app0(E(_nU));return new T(function(){var _nX=String(_nW),_nY=fromJSStr(_nX);if(!B(_3b(_N,_nY))){var _nZ=E(_nY);}else{var _nZ=B(unCStr("localhost"));}var _o0=E(_m8);return new T2(0,E(_nZ),(B(_nP(5381,B(A(_mj,[_n4,_o0.c,_o0.d,_o0.e,_N]))))&4294967295)%64511+1024|0);});},_o1=new T(function(){return B(_5R(_nV));}),_o2=function(_o3){return new F(function(){return A1(_o3,_1o);});},_o4=new T(function(){return B(unCStr("Please start local nodes using `startLocal\'"));}),_o5=new T(function(){return B(err(_o4));}),_o6=new T(function(){if(!E(_o1)._){return E(_o2);}else{return E(_o5);}}),_o7=new T2(1,_o6,_N),_o8="deltaZ",_o9="deltaY",_oa="deltaX",_ob=new T(function(){return B(unCStr(")"));}),_oc=new T(function(){return B(_3t(0,2,_ob));}),_od=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_oc));}),_oe=function(_of){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_3t(0,_of,_od));}))));});},_og=function(_oh,_){return new T(function(){var _oi=Number(E(_oh)),_oj=jsTrunc(_oi);if(_oj<0){return B(_oe(_oj));}else{if(_oj>2){return B(_oe(_oj));}else{return _oj;}}});},_ok=0,_ol=new T3(0,_ok,_ok,_ok),_om="button",_on=new T(function(){return eval("jsGetMouseCoords");}),_oo=function(_op,_){var _oq=E(_op);if(!_oq._){return _N;}else{var _or=B(_oo(_oq.b,_));return new T2(1,new T(function(){var _os=Number(E(_oq.a));return jsTrunc(_os);}),_or);}},_ot=function(_ou,_){var _ov=__arr2lst(0,_ou);return new F(function(){return _oo(_ov,_);});},_ow=function(_ox,_){return new F(function(){return _ot(E(_ox),_);});},_oy=function(_oz,_){return new T(function(){var _oA=Number(E(_oz));return jsTrunc(_oA);});},_oB=new T2(0,_oy,_ow),_oC=function(_oD,_){var _oE=E(_oD);if(!_oE._){return _N;}else{var _oF=B(_oC(_oE.b,_));return new T2(1,_oE.a,_oF);}},_oG=7,_oH=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:268:5-9"));}),_oI=new T6(0,_5z,_oG,_N,_oH,_5z,_5z),_oJ=new T(function(){return B(_5x(_oI));}),_oK=function(_){return new F(function(){return die(_oJ);});},_oL=function(_oM){return E(E(_oM).a);},_oN=function(_oO,_oP,_oQ,_){var _oR=__arr2lst(0,_oQ),_oS=B(_oC(_oR,_)),_oT=E(_oS);if(!_oT._){return new F(function(){return _oK(_);});}else{var _oU=E(_oT.b);if(!_oU._){return new F(function(){return _oK(_);});}else{if(!E(_oU.b)._){var _oV=B(A3(_oL,_oO,_oT.a,_)),_oW=B(A3(_oL,_oP,_oU.a,_));return new T2(0,_oV,_oW);}else{return new F(function(){return _oK(_);});}}}},_oX=function(_){return new F(function(){return __jsNull();});},_oY=new T(function(){return B(_5R(_oX));}),_oZ=new T(function(){return E(_oY);}),_p0=function(_p1,_p2,_){if(E(_p1)==7){var _p3=__app1(E(_on),_p2),_p4=B(_oN(_oB,_oB,_p3,_)),_p5=__get(_p2,E(_oa)),_p6=__get(_p2,E(_o9)),_p7=__get(_p2,E(_o8));return new T(function(){return new T3(0,E(_p4),E(_5z),E(new T3(0,_p5,_p6,_p7)));});}else{var _p8=__app1(E(_on),_p2),_p9=B(_oN(_oB,_oB,_p8,_)),_pa=__get(_p2,E(_om)),_pb=__eq(_pa,E(_oZ));if(!E(_pb)){var _pc=__isUndef(_pa);if(!E(_pc)){var _pd=B(_og(_pa,_));return new T(function(){return new T3(0,E(_p9),E(new T1(1,_pd)),E(_ol));});}else{return new T(function(){return new T3(0,E(_p9),E(_5z),E(_ol));});}}else{return new T(function(){return new T3(0,E(_p9),E(_5z),E(_ol));});}}},_pe=function(_pf,_pg,_){return new F(function(){return _p0(_pf,E(_pg),_);});},_ph="mouseout",_pi="mouseover",_pj="mousemove",_pk="mouseup",_pl="mousedown",_pm="dblclick",_pn="click",_po="wheel",_pp=function(_pq){switch(E(_pq)){case 0:return E(_pn);case 1:return E(_pm);case 2:return E(_pl);case 3:return E(_pk);case 4:return E(_pj);case 5:return E(_pi);case 6:return E(_ph);default:return E(_po);}},_pr=new T2(0,_pp,_pe),_ps=function(_pt){return E(_pt);},_pu=function(_pv,_){while(1){var _pw=E(_pv);if(!_pw._){return _1o;}else{var _px=_pw.b,_py=E(_pw.a);switch(_py._){case 0:var _pz=B(A1(_py.a,_));_pv=B(_1f(_px,new T2(1,_pz,_N)));continue;case 1:_pv=B(_1f(_px,_py.a));continue;default:_pv=_px;continue;}}}},_pA=function(_pB,_pC,_){var _pD=E(_pB);switch(_pD._){case 0:var _pE=B(A1(_pD.a,_));return new F(function(){return _pu(B(_1f(_pC,new T2(1,_pE,_N))),_);});break;case 1:return new F(function(){return _pu(B(_1f(_pC,_pD.a)),_);});break;default:return new F(function(){return _pu(_pC,_);});}},_pF=function(_pG){var _pH=E(_pG);if(!_pH._){return new F(function(){return err(E(_pH.a).a);});}else{return new T0(2);}},_pI=function(_pJ,_pK){var _pL=function(_pM,_){return new F(function(){return _pA(new T(function(){return B(A2(_pJ,_pM,_pF));}),_N,_);});};return new F(function(){return A1(_pK,new T1(1,_pL));});},_pN=function(_pO,_pP,_pQ){var _pR=function(_pS){var _pT=E(_pS);if(!_pT._){return new F(function(){return A1(_pQ,_pT);});}else{var _pU=new T(function(){return B(A1(_pQ,_pT));});return new F(function(){return A1(_pP,function(_pV){var _pW=E(_pV);if(!_pW._){return new F(function(){return A1(_pQ,new T1(0,_pW.a));});}else{return E(_pU);}});});}};return new F(function(){return A1(_pO,_pR);});},_pX=function(_pY,_pZ,_q0){var _q1=new T(function(){return B(A1(_pZ,function(_q2){return new F(function(){return A1(_q0,E(_q2));});}));});return new F(function(){return A1(_pY,function(_q3){var _q4=E(_q3);if(!_q4._){return new F(function(){return A1(_q0,new T1(0,_q4.a));});}else{return E(_q1);}});});},_q5=function(_q6,_q7,_q8){var _q9=function(_qa){var _qb=E(_qa);if(!_qb._){return new F(function(){return A1(_q8,new T1(0,_qb.a));});}else{var _qc=function(_qd){var _qe=E(_qd);if(!_qe._){return new F(function(){return A1(_q8,new T1(0,_qe.a));});}else{return new F(function(){return A1(_q8,new T1(1,new T(function(){return B(A1(_qb.a,_qe.a));})));});}};return new F(function(){return A1(_q7,_qc);});}};return new F(function(){return A1(_q6,_q9);});},_qf=function(_qg,_qh){return new F(function(){return A1(_qh,new T1(1,_qg));});},_qi=function(_qj,_qk,_ql){var _qm=function(_qn){return new F(function(){return A1(_ql,new T(function(){var _qo=E(_qn);if(!_qo._){return new T1(0,_qo.a);}else{return E(new T1(1,_qj));}}));});};return new F(function(){return A1(_qk,_qm);});},_qp=function(_qq,_qr){var _qs=E(_qr);return (_qs._==0)?new T1(0,_qs.a):new T1(1,new T(function(){return B(A1(_qq,_qs.a));}));},_qt=function(_qu,_qv,_qw){var _qx=function(_qy){return new F(function(){return A1(_qw,new T(function(){return B(_qp(_qu,_qy));}));});};return new F(function(){return A1(_qv,_qx);});},_qz=new T2(0,_qt,_qi),_qA=new T5(0,_qz,_qf,_q5,_pX,_pN),_qB=function(_qC,_qD){return new F(function(){return A1(_qD,new T1(0,new T1(0,_qC)));});},_qE=function(_qF,_qG,_qH){return new F(function(){return A1(_qF,function(_qI){var _qJ=E(_qI);if(!_qJ._){return new F(function(){return A1(_qH,new T1(0,_qJ.a));});}else{return new F(function(){return A2(_qG,_qJ.a,_qH);});}});});},_qK=function(_qL,_qM,_qN){var _qO=new T(function(){return B(A1(_qM,_qN));});return new F(function(){return A1(_qL,function(_qP){var _qQ=E(_qP);if(!_qQ._){return new F(function(){return A1(_qN,new T1(0,_qQ.a));});}else{return E(_qO);}});});},_qR=function(_qS,_qT,_qU){return new F(function(){return _qK(_qS,_qT,_qU);});},_qV=new T5(0,_qA,_qE,_qR,_qf,_qB),_qW=function(_qX,_qY){var _qZ=function(_){var _r0=B(A1(_qX,_));return new T(function(){return B(A1(_qY,new T1(1,_r0)));});};return new T1(0,_qZ);},_r1=new T2(0,_qV,_qW),_r2=new T2(0,_r1,_pI),_r3=0,_r4=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_r5=new T(function(){return B(unCStr("Haste.App.Client.Type"));}),_r6=new T(function(){return B(unCStr("6cKLJVuw5DJ4ZCG47q2sCl"));}),_r7=new T(function(){return B(unCStr("Client"));}),_r8=new T5(0,new Long(3596631468,345261357,true),new Long(1580918728,149751875,true),_r6,_r5,_r7),_r9=new T5(0,new Long(3596631468,345261357,true),new Long(1580918728,149751875,true),_r8,_N,_N),_ra=function(_rb){return E(_r9);},_rc=function(_rd,_re,_rf){var _rg=function(_rh){var _ri=new T(function(){return B(A1(_rf,_rh));});return new F(function(){return A1(_re,function(_rj){return E(_ri);});});};return new F(function(){return A1(_rd,_rg);});},_rk=function(_rl,_rm,_rn){var _ro=new T(function(){return B(A1(_rm,function(_rp){return new F(function(){return A1(_rn,_rp);});}));});return new F(function(){return A1(_rl,function(_rq){return E(_ro);});});},_rr=function(_rs,_rt,_ru){var _rv=function(_rw){var _rx=function(_ry){return new F(function(){return A1(_ru,new T(function(){return B(A1(_rw,_ry));}));});};return new F(function(){return A1(_rt,_rx);});};return new F(function(){return A1(_rs,_rv);});},_rz=function(_rA,_rB){return new F(function(){return A1(_rB,_rA);});},_rC=function(_rD,_rE,_rF){var _rG=new T(function(){return B(A1(_rF,_rD));});return new F(function(){return A1(_rE,function(_rH){return E(_rG);});});},_rI=function(_rJ,_rK,_rL){var _rM=function(_rN){return new F(function(){return A1(_rL,new T(function(){return B(A1(_rJ,_rN));}));});};return new F(function(){return A1(_rK,_rM);});},_rO=new T2(0,_rI,_rC),_rP=new T5(0,_rO,_rz,_rr,_rk,_rc),_rQ=function(_rR,_rS,_rT){return new F(function(){return A1(_rR,function(_rU){return new F(function(){return A2(_rS,_rU,_rT);});});});},_rV=function(_rW){return E(E(_rW).b);},_rX=function(_rY,_rZ){return new F(function(){return A3(_rV,_s0,_rY,function(_s1){return E(_rZ);});});},_s2=function(_s3){return new F(function(){return err(_s3);});},_s0=new T(function(){return new T5(0,_rP,_rQ,_rX,_rz,_s2);}),_s4=function(_s5,_s6,_){var _s7=B(A1(_s6,_));return new T(function(){return B(A1(_s5,_s7));});},_s8=function(_s9,_sa){return new T1(0,function(_){return new F(function(){return _s4(_sa,_s9,_);});});},_sb=new T2(0,_s0,_s8),_sc=function(_sd){return new T0(2);},_se=function(_sf){var _sg=new T(function(){return B(A1(_sf,_sc));}),_sh=function(_si){return new T1(1,new T2(1,new T(function(){return B(A1(_si,_1o));}),new T2(1,_sg,_N)));};return E(_sh);},_sj=new T3(0,_sb,_1m,_se),_sk=function(_sl,_sm){return new T2(1,E(_sl),E(_sm));},_sn=function(_so,_sp){return new T2(0,E(_so),E(_sp));},_sq=function(_sr){return new T1(0,E(_sr));},_ss=function(_st){return new T1(3,E(B(_Z(_sq,_st))));},_su="The given Number can\'t be represented as an Int32",_sv=new T1(0,_su),_sw="Tried to deserialize a non-Number to an Int32",_sx=new T1(0,_sw),_sy=function(_sz){var _sA=E(_sz);if(!_sA._){var _sB=_sA.a;if(_sB>=4294967295){return E(_sv);}else{var _sC=_sB&4294967295;return (_sC!=_sB)?E(_sv):new T1(1,_sC);}}else{return E(_sx);}},_sD="Tried to deserialie a non-array to a list!",_sE=new T1(0,_sD),_sF=new T1(1,_N),_sG=new T1(0,_su),_sH=new T1(0,_sw),_sI=function(_sJ){var _sK=E(_sJ);if(!_sK._){return E(_sF);}else{var _sL=E(_sK.a);if(!_sL._){var _sM=_sL.a;if(_sM>=4294967295){return E(_sG);}else{var _sN=_sM&4294967295;if(_sN!=_sM){return E(_sG);}else{var _sO=B(_sI(_sK.b));return (_sO._==0)?new T1(0,_sO.a):new T1(1,new T2(1,_sN,_sO.a));}}}else{return E(_sH);}}},_sP=function(_sQ){var _sR=E(_sQ);if(_sR._==3){return new F(function(){return _sI(_sR.a);});}else{return E(_sE);}},_sS=new T4(0,_sq,_ss,_sy,_sP),_sT=function(_sU){return new T1(3,E(B(_Z(_1m,_sU))));},_sV=new T1(0,_sD),_sW=new T1(1,_N),_sX=function(_sY){var _sZ=E(_sY);if(!_sZ._){return E(_sW);}else{var _t0=B(_sX(_sZ.b));return (_t0._==0)?new T1(0,_t0.a):new T1(1,new T2(1,_sZ.a,_t0.a));}},_t1=function(_t2){var _t3=E(_t2);if(_t3._==3){return new F(function(){return _sX(_t3.a);});}else{return E(_sV);}},_t4=function(_t5){return new T1(1,_t5);},_t6=new T4(0,_1m,_sT,_t4,_t1),_t7=function(_t8){return new T1(1,E(_t8));},_t9=function(_ta){return new T1(3,E(B(_Z(_t7,_ta))));},_tb="Tried to deserialize a non-JSString to a JSString",_tc=new T1(0,_tb),_td=function(_te){var _tf=E(_te);return (_tf._==1)?new T1(1,_tf.a):E(_tc);},_tg=new T1(0,_sD),_th=new T1(1,_N),_ti=new T1(0,_tb),_tj=function(_tk){var _tl=E(_tk);if(!_tl._){return E(_th);}else{var _tm=E(_tl.a);if(_tm._==1){var _tn=B(_tj(_tl.b));return (_tn._==0)?new T1(0,_tn.a):new T1(1,new T2(1,_tm.a,_tn.a));}else{return E(_ti);}}},_to=function(_tp){var _tq=E(_tp);if(_tq._==3){return new F(function(){return _tj(_tq.a);});}else{return E(_tg);}},_tr=new T4(0,_t7,_t9,_td,_to),_ts="nonce",_tt=new T(function(){return B(unCStr("base"));}),_tu=new T(function(){return B(unCStr("Control.Exception.Base"));}),_tv=new T(function(){return B(unCStr("PatternMatchFail"));}),_tw=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_tt,_tu,_tv),_tx=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_tw,_N,_N),_ty=function(_tz){return E(_tx);},_tA=function(_tB){var _tC=E(_tB);return new F(function(){return _46(B(_44(_tC.a)),_ty,_tC.b);});},_tD=function(_tE){return E(E(_tE).a);},_tF=function(_tG){return new T2(0,_tH,_tG);},_tI=function(_tJ,_tK){return new F(function(){return _1f(E(_tJ).a,_tK);});},_tL=function(_tM,_tN){return new F(function(){return _5h(_tI,_tM,_tN);});},_tO=function(_tP,_tQ,_tR){return new F(function(){return _1f(E(_tQ).a,_tR);});},_tS=new T3(0,_tO,_tD,_tL),_tH=new T(function(){return new T5(0,_ty,_tS,_tF,_tA,_tD);}),_tT=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_tU=function(_tV){return E(E(_tV).c);},_tW=function(_tX,_tY){return new F(function(){return die(new T(function(){return B(A2(_tU,_tY,_tX));}));});},_tZ=function(_u0,_u1){return new F(function(){return _tW(_u0,_u1);});},_u2=32,_u3=new T(function(){return B(unCStr("\n"));}),_u4=function(_u5){return (E(_u5)==124)?false:true;},_u6=function(_u7,_u8){var _u9=B(_3I(_u4,B(unCStr(_u7)))),_ua=_u9.a,_ub=function(_uc,_ud){var _ue=new T(function(){var _uf=new T(function(){return B(_1f(_u8,new T(function(){return B(_1f(_ud,_u3));},1)));});return B(unAppCStr(": ",_uf));},1);return new F(function(){return _1f(_uc,_ue);});},_ug=E(_u9.b);if(!_ug._){return new F(function(){return _ub(_ua,_N);});}else{if(E(_ug.a)==124){return new F(function(){return _ub(_ua,new T2(1,_u2,_ug.b));});}else{return new F(function(){return _ub(_ua,_N);});}}},_uh=function(_ui){return new F(function(){return _tZ(new T1(0,new T(function(){return B(_u6(_ui,_tT));})),_tH);});},_uj=new T(function(){return B(_uh("src/Haste/App/Protocol.hs:(63,5)-(65,63)|case"));}),_uk="result",_ul="ok",_um="error",_un="status",_uo=new T1(0,_tb),_up=function(_uq){var _ur=E(_uq);return (_ur._==1)?new T1(1,new T(function(){return fromJSStr(_ur.a);})):E(_uo);},_us="Tried to deserialize long string to a Char",_ut=new T1(0,_us),_uu="Tried to deserialize a non-string to a Char",_uv=new T1(0,_uu),_uw=new T(function(){return eval("(function(s,i){return s.charCodeAt(i);})");}),_ux=new T(function(){return B(unCStr("Haste.JSString.head: empty JSString"));}),_uy=new T(function(){return B(err(_ux));}),_uz=function(_uA){var _uB=__app2(E(_uw),_uA,0),_uC=isDoubleNaN(_uB);return (E(_uC)==0)?E(_uB):E(_uy);},_uD=new T(function(){return eval("(function(s){return s.length;})");}),_uE=function(_uF){var _uG=__app1(E(_uD),_uF),_uH=Number(_uG),_uI=jsTrunc(_uH);return E(_uI);},_uJ=function(_uK){var _uL=E(_uK);if(_uL._==1){var _uM=_uL.a;return (B(_uE(_uM))<=1)?new T1(1,new T(function(){return B(_uz(_uM));})):E(_ut);}else{return E(_uv);}},_uN=function(_uO){return new T1(1,toJSStr(new T2(1,_uO,_N)));},_uP=new T4(0,_uN,_X,_uJ,_up),_uQ=new T1(1,_N),_uR=new T1(0,_sD),_uS=function(_uT){return E(E(_uT).d);},_uU=function(_uV,_uW){var _uX=E(_uW);if(_uX._==3){var _uY=new T(function(){return B(_uS(_uV));}),_uZ=function(_v0){var _v1=E(_v0);if(!_v1._){return E(_uQ);}else{var _v2=B(A1(_uY,_v1.a));if(!_v2._){return new T1(0,_v2.a);}else{var _v3=B(_uZ(_v1.b));return (_v3._==0)?new T1(0,_v3.a):new T1(1,new T2(1,_v2.a,_v3.a));}}};return new F(function(){return _uZ(_uX.a);});}else{return E(_uR);}},_v4=function(_v5){return new F(function(){return _uU(_uP,_v5);});},_v6=new T4(0,_X,_13,_up,_v4),_v7=function(_v8){return E(E(_v8).a);},_v9=function(_va,_vb){return (!B(A3(_v7,_vc,_va,_vb)))?true:false;},_vd=function(_ve,_vf){var _vg=strEq(E(_ve),E(_vf));return (E(_vg)==0)?false:true;},_vh=function(_vi,_vj){return new F(function(){return _vd(_vi,_vj);});},_vc=new T(function(){return new T2(0,_vh,_v9);}),_vk="Key not found: ",_vl="Tried to do lookup on non-object!",_vm=new T1(0,_vl),_vn=new T(function(){return toJSStr(_N);}),_vo=function(_vp,_vq,_vr){while(1){var _vs=E(_vr);if(!_vs._){return __Z;}else{var _vt=E(_vs.a);if(!B(A3(_v7,_vp,_vq,_vt.a))){_vr=_vs.b;continue;}else{return new T1(1,_vt.b);}}}},_vu=function(_vv){return E(E(_vv).c);},_vw=function(_vx,_vy,_vz){var _vA=E(_vy);if(_vA._==4){var _vB=B(_vo(_vc,_vz,_vA.a));if(!_vB._){return new T1(0,new T(function(){return jsCat(new T2(1,_vk,new T2(1,_vz,_N)),E(_vn));}));}else{return new F(function(){return A2(_vu,_vx,_vB.a);});}}else{return E(_vm);}},_vC=function(_vD){var _vE=B(_vw(_tr,_vD,_un));if(!_vE._){return new T1(0,_vE.a);}else{var _vF=E(_vE.a),_vG=E(_um),_vH=strEq(_vF,_vG);if(!E(_vH)){var _vI=strEq(_vF,E(_ul));if(!E(_vI)){return E(_uj);}else{var _vJ=B(_vw(_sS,_vD,_ts));if(!_vJ._){return new T1(0,_vJ.a);}else{var _vK=B(_vw(_t6,_vD,_uk));return (_vK._==0)?new T1(0,_vK.a):new T1(1,new T(function(){return B(_sn(_vJ.a,_vK.a));}));}}}else{var _vL=B(_vw(_sS,_vD,_ts));if(!_vL._){return new T1(0,_vL.a);}else{var _vM=B(_vw(_v6,_vD,_vG));return (_vM._==0)?new T1(0,_vM.a):new T1(1,new T(function(){return B(_sk(_vL.a,_vM.a));}));}}}},_vN=function(_vO){return E(E(_vO).a);},_vP=function(_vQ,_vR,_vS,_vT,_vU){var _vV=B(A2(_vN,_vQ,E(_vU)));return new F(function(){return A2(_vR,_vS,new T2(1,_vV,E(_vT)));});},_vW=function(_vX){return new F(function(){return __lst2arr(E(_vX));});},_vY=function(_vZ){return E(_vZ);},_w0=new T2(0,_vY,_vW),_w1=function(_w2,_){var _w3=E(_w2);if(!_w3._){return _N;}else{var _w4=B(_w1(_w3.b,_));return new T2(1,_1o,_w4);}},_w5=function(_w6,_){var _w7=__arr2lst(0,_w6);return new F(function(){return _w1(_w7,_);});},_w8=function(_w9,_){return new F(function(){return _w5(E(_w9),_);});},_wa=function(_){return _1o;},_wb=function(_wc,_){return new F(function(){return _wa(_);});},_wd=new T2(0,_wb,_w8),_we=function(_wf,_wg,_wh,_){var _wi=__apply(_wg,E(_wh));return new F(function(){return A3(_oL,_wf,_wi,_);});},_wj=function(_wk,_wl,_wm,_){return new F(function(){return _we(_wk,E(_wl),_wm,_);});},_wn=function(_wo,_wp,_wq,_){return new F(function(){return _wj(_wo,_wp,_wq,_);});},_wr=function(_ws,_wt,_){return new F(function(){return _wn(_wd,_ws,_wt,_);});},_wu=function(_wv){return E(_oZ);},_ww=function(_wx){return new F(function(){return __lst2arr(B(_Z(_wu,_wx)));});},_wy=new T2(0,_wu,_ww),_wz=function(_wA,_wB){var _wC=function(_){var _wD=B(A1(_wB,_));return new T(function(){return B(A2(_vN,_wA,_wD));});},_wE=__createJSFunc(0,E(_wC));return E(_wE);},_wF=function(_wG,_wH){return new F(function(){return _wz(_wG,_wH);});},_wI=function(_wJ,_wK){var _wL=__lst2arr(B(_Z(function(_wM){return new F(function(){return _wF(_wJ,_wM);});},_wK)));return E(_wL);},_wN=function(_wO){return new F(function(){return _wI(_wy,_wO);});},_wP=function(_wQ){return new F(function(){return __createJSFunc(0,function(_){var _wR=B(A1(_wQ,_));return _oZ;});});},_wS=new T2(0,_wP,_wN),_wT=function(_ws,_wt,_wU){return new F(function(){return _vP(_wS,_wr,_ws,_wt,_wU);});},_wV="wasClean",_wW="reason",_wX="code",_wY=function(_wZ,_){var _x0=__get(_wZ,E(_wX)),_x1=__get(_wZ,E(_wW)),_x2=__get(_wZ,E(_wV));return new T3(0,new T(function(){var _x3=Number(_x0);return jsTrunc(_x3);}),new T(function(){return String(_x1);}),_x2);},_x4=function(_x5,_){var _x6=E(_x5);if(!_x6._){return _N;}else{var _x7=B(_wY(E(_x6.a),_)),_x8=B(_x4(_x6.b,_));return new T2(1,_x7,_x8);}},_x9=function(_xa,_){var _xb=__arr2lst(0,_xa);return new F(function(){return _x4(_xb,_);});},_xc=function(_xd,_){return new F(function(){return _x9(E(_xd),_);});},_xe=function(_xf,_){return new F(function(){return _wY(E(_xf),_);});},_xg=new T2(0,_xe,_xc),_xh=1,_xi=function(_xj){return E(_xh);},_xk=function(_xl,_){var _xm=B(A1(_xl,_));return _oZ;},_xn=new T2(0,_xk,_xi),_xo=function(_xp){return E(E(_xp).a);},_xq=function(_xr,_xs,_xt,_xu){var _xv=new T(function(){return B(A1(_xt,new T(function(){var _xw=B(A3(_oL,_xr,_xu,_));return E(_xw);})));});return new F(function(){return A2(_xo,_xs,_xv);});},_xx=function(_xy){return E(E(_xy).b);},_xz=new T(function(){return B(unCStr("Prelude.undefined"));}),_xA=new T(function(){return B(err(_xz));}),_xB=function(_xC,_xD,_xE){var _xF=__createJSFunc(1+B(A2(_xx,_xD,new T(function(){return B(A1(_xE,_xA));})))|0,function(_xG){return new F(function(){return _xq(_xC,_xD,_xE,_xG);});});return E(_xF);},_xH=function(_xI){return new F(function(){return _xB(_xg,_xn,_xI);});},_xJ=function(_xK,_xL,_xM){return new F(function(){return _xB(_xK,_xL,_xM);});},_xN=function(_xO,_xP,_xQ){var _xR=__lst2arr(B(_Z(function(_wM){return new F(function(){return _xJ(_xO,_xP,_wM);});},_xQ)));return E(_xR);},_xS=function(_xT){return new F(function(){return _xN(_xg,_xn,_xT);});},_xU=new T2(0,_xH,_xS),_xV=function(_ws,_wt,_wU){return new F(function(){return _vP(_xU,_wT,_ws,_wt,_wU);});},_xW=function(_xX,_){var _xY=E(_xX);if(!_xY._){return _N;}else{var _xZ=B(_xW(_xY.b,_));return new T2(1,_xY.a,_xZ);}},_y0=function(_y1,_){var _y2=__arr2lst(0,_y1);return new F(function(){return _xW(_y2,_);});},_y3=function(_y4,_){return new F(function(){return _y0(E(_y4),_);});},_y5=function(_y6,_){return _y6;},_y7=new T2(0,_y5,_y3),_y8=function(_y9){return new F(function(){return _xB(_y7,_xn,_y9);});},_ya=function(_yb){return new F(function(){return _xN(_y7,_xn,_yb);});},_yc=new T2(0,_y8,_ya),_yd=function(_ws,_wt,_wU){return new F(function(){return _vP(_yc,_xV,_ws,_wt,_wU);});},_ye=2,_yf=function(_yg){return E(_ye);},_yh=function(_yi,_yj,_){var _yk=B(A2(_yi,new T(function(){return String(E(_yj));}),_));return _oZ;},_yl=new T2(0,_yh,_yf),_ym=function(_yn){return new F(function(){return _xB(_y7,_yl,_yn);});},_yo=function(_yp){return new F(function(){return _xN(_y7,_yl,_yp);});},_yq=new T2(0,_ym,_yo),_yr=function(_ws,_wt,_wU){return new F(function(){return _vP(_yq,_yd,_ws,_wt,_wU);});},_ys=new T(function(){return eval("(function(url, cb, f, close, err) {var ws = new WebSocket(url);ws.onmessage = function(e) {cb(ws,e.data);};ws.onopen = function(e) {f(ws);};ws.onclose = function(e) {close(e.data);};ws.error = function(e) {err();};return ws;})");}),_yt=function(_wU){return new F(function(){return _vP(_w0,_yr,_ys,_N,_wU);});},_yu=new T(function(){return eval("(function(s, msg) {if(s.readyState != 1) {return false;} else {s.send(msg); return true;}})");}),_yv="source",_yw="origin",_yx="data",_yy=function(_yz,_){var _yA=__get(_yz,E(_yx)),_yB=__get(_yz,E(_yw)),_yC=__get(_yz,E(_yv));return new T(function(){var _yD=String(_yB);return new T3(0,_yA,_yD,_yC);});},_yE=function(_yF,_yG,_){return new F(function(){return _yy(E(_yG),_);});},_yH="message",_yI=function(_yJ){var _yK=E(_yJ);return E(_yH);},_yL=new T2(0,_yI,_yE),_yM=function(_yN){return E(_yN);},_yO=function(_yP,_yQ){var _yR=function(_yS,_){return new F(function(){return _pA(new T(function(){return B(A2(_yP,_yS,_sc));}),_N,_);});};return new F(function(){return A1(_yQ,_yR);});},_yT=new T2(0,_sb,_yO),_yU=new T(function(){return eval("(function(w,m){w.postMessage(m,\'*\');})");}),_yV=0,_yW=new T(function(){return eval("(function(name){return window[\'__haste_app_sbx\'][name];})");}),_yX=function(_yY){return new F(function(){return err(B(unAppCStr("no such sandbox: ",_yY)));});},_yZ=new T1(1,_N),_z0=new T(function(){return B(_uh("src/Haste/App/Sandbox.hs:(109,1)-(126,16)|function callSandbox"));}),_z1=function(_z2){return E(E(_z2).a);},_z3=function(_z4){return E(E(_z4).a);},_z5=function(_z6){return E(E(_z6).b);},_z7=function(_z8){return E(E(_z8).a);},_z9=function(_){return new F(function(){return nMV(_5z);});},_za=new T(function(){return B(_5R(_z9));}),_zb=function(_zc){return E(E(_zc).b);},_zd=function(_ze){return E(E(_ze).b);},_zf=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_zg=function(_zh){return E(E(_zh).d);},_zi=function(_zj,_zk,_zl,_zm,_zn,_zo){var _zp=B(_z1(_zj)),_zq=B(_z3(_zp)),_zr=new T(function(){return B(_zb(_zp));}),_zs=new T(function(){return B(_zg(_zq));}),_zt=new T(function(){return B(A1(_zk,_zm));}),_zu=new T(function(){return B(A2(_z7,_zl,_zn));}),_zv=function(_zw){return new F(function(){return A1(_zs,new T3(0,_zu,_zt,_zw));});},_zx=function(_zy){var _zz=new T(function(){var _zA=new T(function(){var _zB=__createJSFunc(2,function(_zC,_){var _zD=B(A2(E(_zy),_zC,_));return _oZ;}),_zE=_zB;return function(_){return new F(function(){return __app3(E(_zf),E(_zt),E(_zu),_zE);});};});return B(A1(_zr,_zA));});return new F(function(){return A3(_rV,_zq,_zz,_zv);});},_zF=new T(function(){var _zG=new T(function(){return B(_zb(_zp));}),_zH=function(_zI){var _zJ=new T(function(){return B(A1(_zG,function(_){var _=wMV(E(_za),new T1(1,_zI));return new F(function(){return A(_z5,[_zl,_zn,_zI,_]);});}));});return new F(function(){return A3(_rV,_zq,_zJ,_zo);});};return B(A2(_zd,_zj,_zH));});return new F(function(){return A3(_rV,_zq,_zF,_zx);});},_zK=new T(function(){return eval("(function(e){if(e){e.preventDefault();}})");}),_zL=function(_){var _zM=rMV(E(_za)),_zN=E(_zM);if(!_zN._){var _zO=__app1(E(_zK),E(_oZ));return new F(function(){return _wa(_);});}else{var _zP=__app1(E(_zK),E(_zN.a));return new F(function(){return _wa(_);});}},_zQ=new T0(2),_zR=function(_zS){return E(E(_zS).b);},_zT=function(_zU,_zV,_zW){var _zX=function(_zY){var _zZ=function(_){var _A0=E(_zV),_A1=rMV(_A0),_A2=E(_A1);if(!_A2._){var _A3=new T(function(){var _A4=new T(function(){return B(A1(_zY,_1o));});return B(_1f(_A2.b,new T2(1,new T2(0,_zW,function(_A5){return E(_A4);}),_N)));}),_=wMV(_A0,new T2(0,_A2.a,_A3));return _zQ;}else{var _A6=E(_A2.a);if(!_A6._){var _=wMV(_A0,new T2(0,_zW,_N));return new T(function(){return B(A1(_zY,_1o));});}else{var _=wMV(_A0,new T1(1,_A6.b));return new T1(1,new T2(1,new T(function(){return B(A1(_zY,_1o));}),new T2(1,new T(function(){return B(A2(_A6.a,_zW,_sc));}),_N)));}}};return new T1(0,_zZ);};return new F(function(){return A2(_zR,_zU,_zX);});},_A7=new T1(1,_N),_A8=function(_A9,_Aa){var _Ab=function(_Ac){var _Ad=function(_){var _Ae=E(_Aa),_Af=rMV(_Ae),_Ag=E(_Af);if(!_Ag._){var _Ah=_Ag.a,_Ai=E(_Ag.b);if(!_Ai._){var _=wMV(_Ae,_A7);return new T(function(){return B(A1(_Ac,_Ah));});}else{var _Aj=E(_Ai.a),_=wMV(_Ae,new T2(0,_Aj.a,_Ai.b));return new T1(1,new T2(1,new T(function(){return B(A1(_Ac,_Ah));}),new T2(1,new T(function(){return B(A1(_Aj.b,_sc));}),_N)));}}else{var _Ak=new T(function(){var _Al=function(_Am){var _An=new T(function(){return B(A1(_Ac,_Am));});return function(_Ao){return E(_An);};};return B(_1f(_Ag.a,new T2(1,_Al,_N)));}),_=wMV(_Ae,new T1(1,_Ak));return _zQ;}};return new T1(0,_Ad);};return new F(function(){return A2(_zR,_A9,_Ab);});},_Ap=new T(function(){return eval("(function(e,name,f){e.removeEventListener(name,f[0]);})");}),_Aq=new T(function(){return eval("window");}),_Ar=function(_As,_At,_Au,_Av){var _Aw=E(_At);if(!_Aw._){return E(_z0);}else{var _Ax=_Aw.a;return function(_){var _Ay=__app1(E(_yW),toJSStr(_Ax)),_Az=__eq(_Ay,E(_oZ)),_AA=function(_,_AB){return new T(function(){var _AC=E(_AB);if(!_AC._){return B(_yX(_Ax));}else{var _AD=function(_){var _AE=nMV(_yZ),_AF=_AE;return new T(function(){var _AG=new T(function(){return B(_A8(_sj,_AF));}),_AH=function(_AI){var _AJ=function(_){var _AK=__app2(E(_yU),E(_AC.a),E(_Au));return new T(function(){var _AL=function(_AM){var _AN=E(_AI),_AO=function(_){var _AP=__app3(E(_Ap),E(_AN.b),E(_AN.a),E(_AN.c));return new T(function(){return B(A1(_Av,_AM));});};return new T1(0,_AO);};return B(A1(_AG,_AL));});};return new T1(0,_AJ);},_AQ=function(_AR,_AS){var _AT=function(_){return new T(function(){var _AU=String(E(_AR).a),_AV=jsParseJSON(_AU);if(!_AV._){return B(A1(_AS,_1o));}else{var _AW=B(_vC(_AV.a));if(!_AW._){return B(A1(_AS,_1o));}else{var _AX=E(_AW.a);if(!_AX._){if(E(_As)!=_AX.a){return B(A1(_AS,_1o));}else{var _AY=function(_){var _AZ=B(_zL(_));return new T(function(){return B(A(_zT,[_sj,_AF,_AX.b,_AS]));});};return new T1(0,_AY);}}else{return B(A1(_AS,_1o));}}}});};return new T1(0,_AT);};return B(A(_zi,[_yT,_yM,_yL,_Aq,_yV,_AQ,_AH]));});};return new T1(0,_AD);}});};if(!E(_Az)){var _B0=__isUndef(_Ay);if(!E(_B0)){return new F(function(){return _AA(_,new T1(1,_Ay));});}else{return new F(function(){return _AA(_,_5z);});}}else{return new F(function(){return _AA(_,_5z);});}};}},_B1=new T1(1,_N),_B2=function(_B3,_B4,_B5,_B6,_B7){return function(_){var _B8=nMV(_B1),_B9=_B8,_Ba=function(_){var _Bb=function(_){return new F(function(){return _pA(new T(function(){return B(A(_zT,[_sj,_B9,_5z,_sc]));}),_N,_);});},_Bc=function(_Bd,_){return new F(function(){return _pA(new T(function(){return B(A2(_B5,_Bd,_sc));}),_N,_);});},_Be=function(_Bf,_){return new F(function(){return _pA(new T(function(){return B(A(_zT,[_sj,_B9,new T1(1,_Bf),_sc]));}),_N,_);});},_Bg=function(_Bh,_Bi,_){return new F(function(){return _pA(new T(function(){return B(A3(_B6,_Bh,_Bi,_sc));}),_N,_);});},_Bj=B(A(_B3,[_B4,_Bg,_Be,_Bc,_Bb,_]));return new T(function(){return B(A3(_A8,_sj,_B9,_B7));});};return new T1(0,_Ba);};},_Bk=function(_Bl){return new F(function(){return fromJSStr(E(_Bl));});},_Bm=new T1(1,_N),_Bn=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/App/Client.hs:25:9-15"));}),_Bo=new T(function(){return B(err(_Bn));}),_Bp=new T(function(){return B(unCStr("RecConError"));}),_Bq=new T5(0,new Long(1508037083,2897215931,true),new Long(4082371724,351178574,true),_tt,_tu,_Bp),_Br=new T5(0,new Long(1508037083,2897215931,true),new Long(4082371724,351178574,true),_Bq,_N,_N),_Bs=function(_Bt){return E(_Br);},_Bu=function(_Bv){var _Bw=E(_Bv);return new F(function(){return _46(B(_44(_Bw.a)),_Bs,_Bw.b);});},_Bx=function(_By){return E(E(_By).a);},_Bz=function(_tG){return new T2(0,_BA,_tG);},_BB=function(_BC,_BD){return new F(function(){return _1f(E(_BC).a,_BD);});},_BE=function(_BF,_BG){return new F(function(){return _5h(_BB,_BF,_BG);});},_BH=function(_BI,_BJ,_BK){return new F(function(){return _1f(E(_BJ).a,_BK);});},_BL=new T3(0,_BH,_Bx,_BE),_BA=new T(function(){return new T5(0,_Bs,_BL,_Bz,_Bu,_Bx);}),_BM=new T(function(){return B(unCStr("Missing field in record construction"));}),_BN=function(_BO){return new F(function(){return _tZ(new T1(0,new T(function(){return B(_u6(_BO,_BM));})),_BA);});},_BP=new T(function(){return B(_BN("src/Haste/App/Client.hs:(37,20)-(40,11)|wsOnClose"));}),_BQ=":",_BR="ws://",_BS="Invalid JSON!",_BT=new T(function(){return fromJSStr(E(_BS));}),_BU=new T1(0,_BT),_BV=new T1(0,_BU),_BW=new T(function(){return eval("(function(ws){ws.onclose = ws.onerror = function(){}; ws.close();})");}),_BX=function(_BY,_BZ,_C0){var _C1=E(_BY);if(!_C1._){var _C2=new T(function(){return jsCat(new T2(1,_BR,new T2(1,new T(function(){return toJSStr(_C1.a);}),new T2(1,_BQ,new T2(1,new T(function(){return String(_C1.b);}),_N)))),E(_vn));}),_C3=function(_C4){var _C5=new T(function(){return B(A1(_C4,_BV));}),_C6=function(_){var _C7=nMV(_Bm),_C8=_C7;return new T(function(){var _C9=new T(function(){return B(_A8(_sj,_C8));}),_Ca=function(_Cb){var _Cc=E(_Cb);if(!_Cc._){return E(_Bo);}else{var _Cd=function(_){var _Ce=E(_Cc.a),_Cf=__app2(E(_yu),_Ce,E(_BZ));return new T(function(){var _Cg=function(_Ch){var _Ci=function(_){var _Cj=__app1(E(_BW),_Ce);return new T(function(){var _Ck=jsParseJSON(E(_Ch));if(!_Ck._){return E(_C5);}else{var _Cl=B(_vC(_Ck.a));if(!_Cl._){return B(A1(_C4,new T1(0,new T1(0,new T(function(){return B(_Bk(_Cl.a));})))));}else{var _Cm=E(_Cl.a);if(!_Cm._){return B(A1(_C4,new T1(1,_Cm.b)));}else{return B(A1(_C4,new T1(0,new T1(0,_Cm.b))));}}}});};return new T1(0,_Ci);};return B(A1(_C9,_Cg));});};return new T1(0,_Cd);}};return new T1(0,B(_B2(_yt,_C2,_BP,function(_Cn,_Co){return new F(function(){return _zT(_sj,_C8,_Co);});},_Ca)));});};return new T1(0,_C6);};return E(_C3);}else{var _Cp=function(_Cq){return new T1(0,B(_Ar(_C0,_C1,_BZ,function(_Cr){return new F(function(){return A1(_Cq,new T1(1,_Cr));});})));};return E(_Cp);}},_Cs=new T1(1,_1o),_Ct=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/App/Client/Type.hs:25:5-11"));}),_Cu=new T(function(){return B(err(_Ct));}),_Cv=function(_Cw){return (E(_Cw)._==0)?E(_Cu):new T0(2);},_Cx=function(_Cy){var _Cz=new T(function(){return B(A1(_Cy,_Cv));}),_CA=function(_CB){return new T1(1,new T2(1,new T(function(){return B(A1(_CB,_Cs));}),new T2(1,_Cz,_N)));};return E(_CA);},_CC=function(_CD,_CE){return new F(function(){return A1(_CD,function(_CF){return new F(function(){return A1(_CE,new T1(1,_CF));});});});},_CG=new T3(0,_r1,_CC,_Cx),_CH=new T3(0,_ra,_CG,_BX),_CI=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/App/Remote.hs:67:5-11"));}),_CJ=function(_CK){return E(E(_CK).a);},_CL=function(_CM){return E(E(_CM).a);},_CN=function(_CO){return E(E(_CO).a);},_CP=function(_CQ){return E(E(_CQ).b);},_CR="args",_CS="method",_CT="tag",_CU=new T(function(){return new T1(1,"call");}),_CV=new T2(0,_CT,_CU),_CW="hi",_CX="lo",_CY=function(_CZ){var _D0=E(_CZ);if(!_D0._){return _D0.a;}else{return new F(function(){return I_toNumber(_D0.a);});}},_D1=function(_D2){var _D3=hs_intToInt64(2147483647),_D4=hs_int64ToWord64(_D3),_D5=hs_leWord64(_D2,_D4);if(!_D5){return new T1(1,I_fromWord64(_D2));}else{var _D6=hs_word64ToInt64(_D2),_D7=hs_int64ToInt(_D6);return new T1(0,_D7);}},_D8=function(_D9){return new T2(1,new T2(0,_CX,new T(function(){var _Da=hs_and64(E(_D9),new Long(4294967295,0,true));return new T1(0,B(_CY(B(_D1(_Da)))));})),new T2(1,new T2(0,_CW,new T(function(){var _Db=hs_and64(B(_kI(E(_D9),32)),new Long(4294967295,0,true));return new T1(0,B(_CY(B(_D1(_Db)))));})),_N));},_Dc=function(_Dd,_De){return new T2(1,new T2(0,_CX,new T(function(){return new T1(4,E(B(_D8(_Dd))));})),new T2(1,new T2(0,_CW,new T(function(){return new T1(4,E(B(_D8(_De))));})),_N));},_Df=function(_Dg,_Dh,_Di,_Dj){return new T2(1,_CV,new T2(1,new T2(0,_ts,new T1(0,_Dg)),new T2(1,new T2(0,_CS,new T(function(){return new T1(4,E(B(_Dc(_Dh,_Di))));})),new T2(1,new T2(0,_CR,new T(function(){return new T1(3,E(B(_Z(_1m,_Dj))));})),_N))));},_Dk=function(_Dl){var _Dm=B(_n(_N,_Dl)),_Dn=jsCat(new T2(1,_Dm.a,_Dm.b),E(_O));return E(_Dn);},_Do=function(_Dp){var _Dq=E(_Dp);return new T2(0,_Dq+1|0,_Dq);},_Dr=0,_Ds=function(_){return new F(function(){return nMV(_Dr);});},_Dt=new T(function(){return B(_5R(_Ds));}),_Du=function(_){var _Dv=mMV(E(_Dt),_Do),_Dw=E(_Dv);return _Dv;},_Dx=function(_Dy){return E(E(_Dy).c);},_Dz=function(_DA,_DB,_DC,_DD){var _DE=B(_CN(B(_CP(_DA)))),_DF=function(_DG){return new F(function(){return A(_Dx,[_DA,_DB,new T(function(){var _DH=E(_DC);return B(_Dk(new T1(4,E(B(_Df(E(_DG),_DH.a,_DH.b,_DD))))));}),_DG]);});};return new F(function(){return A3(_rV,B(_z3(_DE)),new T(function(){return B(A2(_zb,_DE,_Du));}),_DF);});},_DI=function(_DJ){return E(E(_DJ).e);},_DK=function(_DL){return E(E(_DL).a);},_DM=function(_DN,_DO){while(1){var _DP=E(_DN);if(!_DP._){return E(_DO);}else{var _DQ=new T2(1,_DP.a,_DO);_DN=_DP.b;_DO=_DQ;continue;}}},_DR=function(_DS,_DT,_DU,_DV,_DW){var _DX=B(_z3(B(_CN(B(_CP(_DS)))))),_DY=new T(function(){return B(A2(_DI,_DX,_CI));}),_DZ=new T(function(){var _E0=new T(function(){return B(_Dz(_DS,_DU,_DV,new T(function(){return B(_DM(_DW,_N));})));});return B(A3(_DK,B(_CJ(B(_CL(_DX)))),function(_E1){return new F(function(){return A2(_vu,_DT,_E1);});},_E0));});return new F(function(){return A3(_rV,_DX,_DZ,function(_E2){var _E3=E(_E2);if(!_E3._){return E(_DY);}else{return new F(function(){return A2(_zg,_DX,_E3.a);});}});});},_E4=function(_E5){return new T1(3,E(B(_Z(_13,_E5))));},_E6=function(_E7){return new F(function(){return _uU(_v6,_E7);});},_E8=function(_E7){return new F(function(){return _uU(_uP,_E7);});},_E9=new T4(0,_13,_E4,_E8,_E6),_Ea=new T(function(){return new T1(1,"./data");}),_Eb=new T2(1,_Ea,_N),_Ec=new T(function(){return B(_DR(_CH,_E9,_o1,_b,_Eb));}),_Ed=new T(function(){return eval("alert");}),_Ee=new T(function(){return B(unCStr("ok"));}),_Ef=new T1(1,_1o),_Eg=function(_Eh){return function(_){var _Ei=__app1(E(_Ed),toJSStr(E(_Ee)));return new T(function(){return B(A1(_Eh,_Ef));});};},_Ej=function(_Ek){return new T1(0,B(_Eg(_Ek)));},_El=function(_Em,_E7){return new F(function(){return _Ej(_E7);});},_En="btn",_Eo=function(_Ep,_Eq){return new F(function(){return A2(_zg,B(_z3(_Ep)),new T1(1,_Eq));});},_Er=new T2(0,_1m,_Eo),_Es=function(_Et,_Eu){return new T2(0,E(_Et),toJSStr(E(_Eu)));},_Ev="list",_Ew=new T(function(){return eval("(function(c,p){p.appendChild(c);})");}),_Ex=function(_Ey,_Ez,_EA){var _EB=E(_Ez);if(!_EB._){return new F(function(){return A1(_EA,_Ef);});}else{var _EC=function(_){var _ED=E(_Ey),_EE=E(_Ew),_EF=__app2(_EE,E(_EB.a),_ED);return new T(function(){var _EG=function(_EH,_EI){var _EJ=E(_EH);if(!_EJ._){return new F(function(){return A1(_EI,_Ef);});}else{var _EK=function(_){var _EL=__app2(_EE,E(_EJ.a),_ED);return new T(function(){return B(_EG(_EJ.b,_EI));});};return new T1(0,_EK);}};return B(_EG(_EB.b,_EA));});};return new T1(0,_EC);}},_EM=new T(function(){return eval("(function(t){return document.createElement(t);})");}),_EN=new T(function(){return new T2(0,E(new T1(2,"name")),"Download");}),_EO=new T(function(){return new T2(0,E(new T1(2,"value")),"Download selected file");}),_EP=new T2(1,_EO,_N),_EQ=new T2(1,_EN,_EP),_ER=new T(function(){return new T2(0,E(new T1(2,"type")),"submit");}),_ES=new T2(1,_ER,_EQ),_ET=new T(function(){return B(unCStr("input"));}),_EU=function(_EV){var _EW=function(_){var _EX=__app1(E(_EM),toJSStr(E(_ET)));return new T(function(){return B(A1(_EV,new T1(1,_EX)));});};return new T1(0,_EW);},_EY=function(_EZ){return E(E(_EZ).c);},_F0=function(_F1){return E(E(_F1).a);},_F2=new T(function(){return eval("(function(e,p,v){e.setAttribute(p, v);})");}),_F3=new T(function(){return eval("(function(e,p,v){e.style[p] = v;})");}),_F4=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_F5=function(_F6,_F7,_F8,_F9){var _Fa=new T(function(){return B(A2(_F0,_F6,_F8));}),_Fb=function(_Fc,_){var _Fd=E(_Fc);if(!_Fd._){return _1o;}else{var _Fe=E(_Fa),_Ff=E(_Ew),_Fg=__app2(_Ff,E(_Fd.a),_Fe),_Fh=function(_Fi,_){while(1){var _Fj=E(_Fi);if(!_Fj._){return _1o;}else{var _Fk=__app2(_Ff,E(_Fj.a),_Fe);_Fi=_Fj.b;continue;}}};return new F(function(){return _Fh(_Fd.b,_);});}},_Fl=function(_Fm,_){while(1){var _Fn=B((function(_Fo,_){var _Fp=E(_Fo);if(!_Fp._){return _1o;}else{var _Fq=_Fp.b,_Fr=E(_Fp.a);if(!_Fr._){var _Fs=_Fr.b,_Ft=E(_Fr.a);switch(_Ft._){case 0:var _Fu=E(_Fa),_Fv=E(_F4),_Fw=__app3(_Fv,_Fu,_Ft.a,_Fs),_Fx=function(_Fy,_){while(1){var _Fz=E(_Fy);if(!_Fz._){return _1o;}else{var _FA=_Fz.b,_FB=E(_Fz.a);if(!_FB._){var _FC=_FB.b,_FD=E(_FB.a);switch(_FD._){case 0:var _FE=__app3(_Fv,_Fu,_FD.a,_FC);_Fy=_FA;continue;case 1:var _FF=__app3(E(_F3),_Fu,_FD.a,_FC);_Fy=_FA;continue;default:var _FG=__app3(E(_F2),_Fu,_FD.a,_FC);_Fy=_FA;continue;}}else{var _FH=B(_Fb(_FB.a,_));_Fy=_FA;continue;}}}};return new F(function(){return _Fx(_Fq,_);});break;case 1:var _FI=E(_Fa),_FJ=E(_F3),_FK=__app3(_FJ,_FI,_Ft.a,_Fs),_FL=function(_FM,_){while(1){var _FN=E(_FM);if(!_FN._){return _1o;}else{var _FO=_FN.b,_FP=E(_FN.a);if(!_FP._){var _FQ=_FP.b,_FR=E(_FP.a);switch(_FR._){case 0:var _FS=__app3(E(_F4),_FI,_FR.a,_FQ);_FM=_FO;continue;case 1:var _FT=__app3(_FJ,_FI,_FR.a,_FQ);_FM=_FO;continue;default:var _FU=__app3(E(_F2),_FI,_FR.a,_FQ);_FM=_FO;continue;}}else{var _FV=B(_Fb(_FP.a,_));_FM=_FO;continue;}}}};return new F(function(){return _FL(_Fq,_);});break;default:var _FW=E(_Fa),_FX=E(_F2),_FY=__app3(_FX,_FW,_Ft.a,_Fs),_FZ=function(_G0,_){while(1){var _G1=E(_G0);if(!_G1._){return _1o;}else{var _G2=_G1.b,_G3=E(_G1.a);if(!_G3._){var _G4=_G3.b,_G5=E(_G3.a);switch(_G5._){case 0:var _G6=__app3(E(_F4),_FW,_G5.a,_G4);_G0=_G2;continue;case 1:var _G7=__app3(E(_F3),_FW,_G5.a,_G4);_G0=_G2;continue;default:var _G8=__app3(_FX,_FW,_G5.a,_G4);_G0=_G2;continue;}}else{var _G9=B(_Fb(_G3.a,_));_G0=_G2;continue;}}}};return new F(function(){return _FZ(_Fq,_);});}}else{var _Ga=B(_Fb(_Fr.a,_));_Fm=_Fq;return __continue;}}})(_Fm,_));if(_Fn!=__continue){return _Fn;}}};return new F(function(){return A2(_zb,_F7,function(_){return new F(function(){return _Fl(_F9,_);});});});},_Gb=function(_Gc,_Gd,_Ge,_Gf){var _Gg=B(_z3(_Gd)),_Gh=function(_Gi){return new F(function(){return A3(_EY,_Gg,new T(function(){return B(_F5(_Gc,_Gd,_Gi,_Gf));}),new T(function(){return B(A2(_zg,_Gg,_Gi));}));});};return new F(function(){return A3(_rV,_Gg,_Ge,_Gh);});},_Gj=new T(function(){return B(_Gb(_Er,_r1,_EU,_ES));}),_Gk=new T(function(){return new T2(0,E(new T1(2,"name")),"Submit");}),_Gl=new T(function(){return new T2(0,E(new T1(2,"value")),"Edit selected file");}),_Gm=new T2(1,_Gl,_N),_Gn=new T2(1,_Gk,_Gm),_Go=new T2(1,_ER,_Gn),_Gp=new T(function(){return B(_Gb(_Er,_r1,_EU,_Go));}),_Gq=new T(function(){return B(unCStr("br"));}),_Gr=new T(function(){return B(unCStr(" found!"));}),_Gs=function(_Gt){return new F(function(){return err(B(unAppCStr("No element with ID ",new T(function(){return B(_1f(fromJSStr(E(_Gt)),_Gr));}))));});},_Gu=function(_Gv){return function(_){var _Gw=E(_Ev),_Gx=__app1(E(_r4),_Gw),_Gy=_Gx,_Gz=__eq(_Gy,E(_oZ));if(!E(_Gz)){var _GA=__isUndef(_Gy);return (E(_GA)==0)?new T(function(){var _GB=function(_GC){var _GD=E(_GC);if(!_GD._){return new F(function(){return A1(_Gv,new T1(0,_GD.a));});}else{var _GE=function(_GF){var _GG=E(_GF);if(!_GG._){return new F(function(){return A1(_Gv,new T1(0,_GG.a));});}else{var _GH=function(_){var _GI=__app1(E(_EM),toJSStr(E(_Gq)));return new T(function(){return B(_Ex(_Gy,new T2(1,_GI,new T2(1,_GD.a,new T2(1,_GG.a,_N))),_Gv));});};return new T1(0,_GH);}};return new F(function(){return A1(_Gj,_GE);});}};return B(A1(_Gp,_GB));}):new T(function(){return B(_Gs(_Gw));});}else{return new T(function(){return B(_Gs(_Gw));});}};},_GJ=function(_GK){return new T1(0,B(_Gu(_GK)));},_GL=new T(function(){return B(unCStr("span"));}),_GM=function(_GN){return function(_){var _GO=__app1(E(_EM),toJSStr(E(_GL)));return new T(function(){return B(A1(_GN,new T1(1,_GO)));});};},_GP=function(_GQ){return new T1(0,B(_GM(_GQ)));},_GR=function(_GS){return function(_){var _GT=__app1(E(_EM),toJSStr(E(_ET)));return new T(function(){return B(A1(_GS,new T1(1,_GT)));});};},_GU=function(_GV){return new T1(0,B(_GR(_GV)));},_GW=new T(function(){return new T1(0,"innerHTML");}),_GX=new T(function(){return new T2(0,E(new T1(2,"name")),"filetype");}),_GY=new T(function(){return new T1(2,"value");}),_GZ=new T(function(){return new T2(0,E(new T1(2,"type")),"radio");}),_H0=function(_H1){var _H2=E(_H1);if(!_H2._){return E(_GJ);}else{var _H3=_H2.a,_H4=new T(function(){return B(_Gb(_Er,_r1,_GP,new T2(1,new T(function(){return B(_Es(_GW,_H3));}),_N)));}),_H5=new T(function(){return B(_Gb(_Er,_r1,_GU,new T2(1,_GZ,new T2(1,new T(function(){return B(_Es(_GY,_H3));}),new T2(1,_GX,new T2(1,new T(function(){return B(_Es(_GW,_H3));}),_N))))));}),_H6=new T(function(){return B(_H0(_H2.b));}),_H7=function(_H8){var _H9=new T(function(){return B(A1(_H6,_H8));}),_Ha=function(_Hb){var _Hc=E(_Hb);if(!_Hc._){return new F(function(){return A1(_H8,_Hc);});}else{return E(_H9);}},_Hd=function(_){var _He=E(_Ev),_Hf=__app1(E(_r4),_He),_Hg=_Hf,_Hh=__eq(_Hg,E(_oZ));if(!E(_Hh)){var _Hi=__isUndef(_Hg);return (E(_Hi)==0)?new T(function(){var _Hj=function(_Hk){var _Hl=E(_Hk);if(!_Hl._){return new F(function(){return A1(_H8,new T1(0,_Hl.a));});}else{var _Hm=function(_Hn){var _Ho=E(_Hn);if(!_Ho._){return new F(function(){return A1(_H8,new T1(0,_Ho.a));});}else{var _Hp=function(_){var _Hq=__app1(E(_EM),toJSStr(E(_Gq)));return new T(function(){return B(_Ex(_Hg,new T2(1,_Ho.a,new T2(1,_Hl.a,new T2(1,_Hq,_N))),_Ha));});};return new T1(0,_Hp);}};return new F(function(){return A1(_H5,_Hm);});}};return B(A1(_H4,_Hj));}):new T(function(){return B(_Gs(_He));});}else{return new T(function(){return B(_Gs(_He));});}};return new T1(0,_Hd);};return E(_H7);}},_Hr=function(_Hs){var _Ht=new T(function(){return B(A1(_Hs,_Ef));}),_Hu=function(_){var _Hv=E(_En),_Hw=__app1(E(_r4),_Hv),_Hx=__eq(_Hw,E(_oZ));if(!E(_Hx)){var _Hy=__isUndef(_Hw);return (E(_Hy)==0)?new T(function(){return B(A(_zi,[_r2,_ps,_pr,_Hw,_r3,_El,function(_Hz){var _HA=E(_Hz);if(!_HA._){return new F(function(){return A1(_Hs,new T1(0,_HA.a));});}else{return E(_Ht);}}]));}):new T(function(){return B(_Gs(_Hv));});}else{return new T(function(){return B(_Gs(_Hv));});}},_HB=function(_HC){var _HD=E(_HC);if(!_HD._){return new F(function(){return A1(_Hs,_HD);});}else{return E(new T1(0,_Hu));}};return new F(function(){return A1(_Ec,function(_HE){var _HF=E(_HE);if(!_HF._){return new F(function(){return A1(_Hs,new T1(0,_HF.a));});}else{return new F(function(){return A2(_H0,_HF.a,_HB);});}});});},_HG=new T(function(){return eval("(function(){return self[\'__haste_program_is_sandboxed\'];})");}),_HH=function(_HI,_HJ){var _HK=E(_HI);if(!_HK._){return new F(function(){return A1(_HJ,_1o);});}else{var _HL=new T(function(){return B(_HH(_HK.b,_HJ));});return new F(function(){return A1(_HK.a,function(_HM){return E(_HL);});});}},_HN=function(_HO){var _HP=E(_HO);if(!_HP._){return new F(function(){return err(E(_HP.a).a);});}else{return new T0(2);}},_HQ=function(_HR,_HS,_){var _HT=__app0(E(_HG)),_HU=_HT,_HV=new T(function(){var _HW=new T(function(){return B(A1(_HS,_HN));});return B(_HH(_HR,function(_HX){return (!_HU)?E(_HW):new T0(2);}));});return new F(function(){return _pA(_HV,_N,_);});},_HY=function(_){return new F(function(){return _HQ(_o7,_Hr,_);});},_HZ=function(_){return new F(function(){return _HY(_);});};__spt_insert(_kp);
__spt_insert(_a);

var hasteMain = function() {B(A(_HZ, [0]));};window.onload = hasteMain;