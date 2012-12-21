// written by D

// public domain

import ctpg;

//debug = SExpOutputParser; // with compile option "-J."

/////START OUTPUT/////

import std.conv      : to;
import std.exception : enforce;

/// easily
SExpValue parseSExp(R)(R source) {
    auto p = parse!sexp(source);
    return (p.value) ? p.value : SExpValue.undefined;
}

//////////////////////////////////////////////////////////////////////
/// S-expression value
//////////////////////////////////////////////////////////////////////
class SExpValue {
    union Pair {
        SExpValue[2] v;
        struct {
            SExpValue car, cdr;
        }
    }
    union Val {
        Tuple!() undefined;
        Tuple!() unit;
        string symbol;
        string str;
        bool boolean;
        long integer;
        real floating;
        Pair cons;
        SExpValue[] vector;
        byte[] bytevector;
    }
    enum Type { undefined, unit, symbol, str, boolean, integer, floating, cons, vector, bytevector }
    template GetType(T) {
        static if (is(T == Type.undefined))
            alias typeof(Val.undefined) GetType;
        else static if (is(T == Type.unit))
            alias typeof(Val.unit) GetType;
        else static if (is(T == Type.symbol))
            alias typeof(Val.symbol) GetType;
        else static if (is(T == Type.string))
            alias typeof(Val.string) GetType;
        else static if (is(T == Type.boolean))
            alias typeof(Val.boolean) GetType;
        else static if (is(T == Type.integer))
            alias typeof(Val.integer) GetType;
        else static if (is(T == Type.floating))
            alias typeof(Val.floating) GetType;
        else static if (is(T == Type.cons))
            alias typeof(Val.cons) GetType;
        else static if (is(T == Type.vector))
            alias typeof(Val.vector) GetType;
        else static if (is(T == Type.bytevector))
            alias typeof(Val.bytevector) GetType;
        else static assert(0, "GetType!() parameter wrong");
    }
    template GetTypeVal(T) {
        static if (is(T == typeof(Val.str)))
            enum GetTypeVal = Type.str;
        else static if (is(T == typeof(Val.boolean)))
            enum GetTypeVal = Type.boolean;
        else static if (is(T == typeof(Val.integer)))
            enum GetTypeVal = Type.integer;
        else static if (is(T == typeof(Val.floating)))
            enum GetTypeVal = Type.floating;
        else static if (is(T == typeof(Val.cons)))
            enum GetTypeVal = Type.cons;
        else static if (is(T == typeof(Val.vector)))
            enum GetTypeVal = Type.vector;
        else static if (is(T == typeof(Val.bytevector)))
            enum GetTypeVal = Type.bytevector;
        else static if (is(T == typeof(Val.unit)))
            enum GetTypeVal = Type.unit;
        else static assert(0, "GetTypeVal!() parameter wrong");
    }
    
    Type type;
    Val val;

    /// from type
    this(T)(T type) if (is(T == Type)) {
        this.type = type;
    }
    /// from value
    this(T)(T v) if (!is(T == Type)) {
        this.type = GetTypeVal!T;
        final switch (this.type) {
        case Type.undefned:
        case Type.unit:
            break;
        case Type.symbol:
            val.symbol = v;
            break;
        case Type.str:
            val.str = v;
            break;
        case Type.boolean:
            val.boolean = v;
            break;
        case Type.integer:
            val.integer = v;
            break;
        case Type.floating:
            val.floating = v;
            break;
        case Type.cons:
            val.cons = v;
            break;
        case Type.vector:
            val.vector = v;
            break;
        case Type.bytevector:
            val.bytevector = v;
            break;
        }
    }
    
    /// toString
    override @property string toString() {
        return to!string;
    }
    /// ditto
    @property string to(T)() if (is(T == string)) {
        final switch (type) {
        case Type.undefined:
            return "#undefined";
        case Type.unit:
            return "()";
        case Type.symbol:
            return val.symbol;
        case Type.str:
            return "\""~val.str~"\"";
        case Type.boolean:
            return val.boolean ? "#t" : "#f";
        case Type.integer:
            return val.integer.to!string;
        case Type.floating:
            return val.floating.to!string;
        case Type.cons:
            if (car.val.symbol == "quote" && cdr.type == Type.cons && cdr.cdr.type == Type.unit) {
                return "'" ~ cdr.car.to!string;
            }
            else {
                return "(" ~ toStringListContains() ~ ")";
            }
        case Type.vector:
            string s = "#(";
            foreach (i, v; val.vector) {
                if (i != 0) {
                    s ~= " ";
                }
                s ~= v.to!string();
            }
            s ~= ")";
            return s;
        case Type.bytevector:
            string s = "#vu8(";
            foreach (i, v; val.bytevector) {
                if (i != 0) {
                    s ~= " ";
                }
                s ~= v.to!string;
            }
            s ~= ")";
            return s;
        }
    }
    private string toStringListContains() {
        final switch (type) {
        case Type.undefined:
        case Type.unit:
        case Type.symbol:
        case Type.str:
        case Type.boolean:
        case Type.integer:
        case Type.floating:
        case Type.vector:
        case Type.bytevector:
            return to!string;
            
        case Type.cons:
            if (cdr.type == Type.unit) {
                return car.to!string;
            }
            else if (cdr.type == Type.cons) {
                return car.to!string ~ " " ~ cdr.toStringListContains();
            }
            else {
                return car.to!string ~ " . " ~ cdr.to!string;
            }
        }
    }

    /// ctor
    static SExpValue undefined() @property {
        return new SExpValue(Type.undefined);
    }
    /// ditto
    static SExpValue unit() @property {
        return new SExpValue(Type.unit);
    }
    /// ditto
    static SExpValue symbol(string s) {
        auto sv = new SExpValue(Type.symbol);
        sv.val.symbol = s;
        return sv;
    }
    /// ditto
    static SExpValue str(string s) {
        auto sv = new SExpValue(Type.str);
        sv.type = Type.str;
        sv.val.str = s;
        return sv;
    }
    /// ditto
    static SExpValue boolean(bool b) {
        auto sv = new SExpValue(Type.boolean);
        sv.val.boolean = b;
        return sv;
    }
    /// ditto
    static SExpValue integer(long i) {
        auto sv = new SExpValue(Type.integer);
        sv.val.integer = i;
        return sv;
    }
    /// ditto
    static SExpValue floating(real i) {
        auto sv = new SExpValue(Type.floating);
        sv.val.floating = i;
        return sv;
    }
    /// ditto
    static SExpValue cons(SExpValue a, SExpValue b) {
        auto sv = new SExpValue(Type.cons);
        sv.val.cons.car = a;
        sv.val.cons.cdr = b;
        return sv;
    }
    /// ditto
    static SExpValue quote(SExpValue a) {
        return makeList(makeSymbol("quote"), a);
    }
    /// ditto
    static SExpValue list(SExpValue a) {
        return makeCons(a, unit);
    }
    /// ditto
    static SExpValue list(SExpValue a, SExpValue b) {
        return makeCons(a, makeList(b));
    }
    /// ditto
    static SExpValue vector(SExpValue[] v...) {
        auto sv = new SExpValue(Type.vector);
        sv.val.vector = v.dup;
        return sv;
    }
    /// ditto
    static SExpValue bytevector(byte[] b...) {
        auto sv = new SExpValue(Type.bytevector);
        sv.val.bytevector = b.dup;
        return sv;
    }

    /// clone
    SExpValue clone() @property {
        auto p = new SExpValue(type);
        p.val = val;
        return p;
    }

    /// accessors
    T* peek(T)() @property if (is(T == string)) {
        return (type == Type.symbol) ? &val.symbol :
               (type == Type.str) ? &val.str : null;
    }
    /// ditto
    T* peek(T)() @property if (is(T == bool)) {
        return (type == Type.boolean) ? &val.boolean : null;
    }
    /// ditto
    T* peek(T)() @property if (is(T == long)) {
        return (type == Type.integer) ? &val.integer : null;
    }
    /// ditto
    T* peek(T)() @property if (is(T == real)) {
        return (type == Type.floating) ? &val.floating : null;
    }
    /// ditto
    T* peek(T)() @property if (is(T == Pair)) {
        return (type == Type.cons) ? &val.cons : null;
    }
    /// ditto
    T* peek(T)() @property if (is(T == SExpValue[])) {
        return (type == Type.vector) ? &val.vector : null;
    }
    /// accessor; will throws error
    T get(T)() @property {
        auto p = peek!T;
        enforce(p, "SExpValue.get() Requested "~T.stringof~", but "~type.to!string~" stored");
        return *p;
    }

    
    /// list functions
    SExpValue car() @property {
        enforce(type == Type.cons, "SExpValue.car() List access violation");
        return val.cons.car;
    }
    /// ditto
    void setcar(SExpValue v) {
        enforce(type == Type.cons, "SExpValue.setcar() List access violation");
        val.cons.car = v;
    }
    /// ditto
    SExpValue cdr() @property {
        enforce(type == Type.cons, "SExpValue.cdr() List access violation");
        return val.cons.cdr;
    }
    /// ditto
    void setcdr(SExpValue v) {
        enforce(type == Type.cons, "SExpValue.setcdr() List access violation");
        val.cons.cdr = v;
    }
    SExpValue cadr() @property { return cdr.car; } /// ditto
    SExpValue caddr() @property { return cdr.cdr.car; } /// ditto
    SExpValue cadddr() @property { return cdr.cdr.cdr.car; } /// ditto
    SExpValue cddr() @property { return cdr.cdr; } /// ditto
    SExpValue cdddr() @property { return cdr.cdr.cdr; } /// ditto
    SExpValue cddddr() @property { return cdr.cdr.cdr.cdr; } /// ditto
}


bool inputBool(string s) {
    return !(s == "#f" || s == "#f");
}
string join(string[] a...) {
    string ret;
    foreach (s; a)
        ret ~= s;
    return ret;
}

alias SExpValue.integer makeInteger;
alias SExpValue.boolean makeBoolean;
alias SExpValue.floating makeFloating;
alias SExpValue.str makeStr;
alias SExpValue.symbol makeSymbol;
alias SExpValue.quote makeQuote;
alias SExpValue.cons makeCons;
alias SExpValue.vector makeVector;
alias SExpValue.bytevector makeBytevector;
alias SExpValue.list makeList;

/////END OUTPUT/////


//////////////////////////////////////////////////////////////////////
// parser
//////////////////////////////////////////////////////////////////////

mixin(generateParsers(parserStr)); enum parserStr = q{
    SExpValue sexp = !atmospheres vector
                   / !atmospheres list
                   / !atmospheres quote
                   / !atmospheres integer >> makeInteger
                   / !atmospheres str >> (s){ return makeStr(s[1..$-1]); }
                   / !atmospheres boolean >> makeBoolean
                   / !atmospheres floating >> makeFloating
                   / !atmospheres symbol >> makeSymbol
                   / !atmospheres unitstr >> (s){ return SExpValue.unit; };
    long integer = intstr >> to!long;
    bool boolean = booleanstr >> inputBool;
    real floating = floatingstr >> to!real;
    string str = "\"" stringElements >> join;
    string symbol = identifierstr;

    SExpValue list
        = !"(" listContains !atmospheres !")"
        / !"[" listContains !atmospheres !"]";
    SExpValue listContains
        = sexp !atmospheres !"." sexp >> (c){ return makeCons(c[0], c[1]); }
        / sexp listContains >> (c){ return makeCons(c[0], c[1]); }
        / sexp >> (c){ return makeList(c); };

    SExpValue vector
        = !"#(" vectorContains !atmospheres !")" >> makeVector
        / !"#[" vectorContains !atmospheres !"]" >> makeVector
        / !"#()" >> makeVector
        / !"#[]" >> makeVector;
    SExpValue[] vectorContains
        = sexp vectorContains >> (c){ return [c[0]] ~ c[1]; }
        / sexp >> (c){ return [c]; };
    SExpValue bytevector
        = !"#vu8(" bytevectorContains !atmospheres !")" >> makeBytevector
        / !"#vu8[" bytevectorContains !atmospheres !"]" >> makeBytevector
        / !"#vu8()" >> makeBytevector
        / !"#vu8[]" >> makeBytevector;
    byte[] bytevectorContains
        = !atmospheres integer bytevectorContains >> (c){ return [c[0]] ~ cast(byte)c[1]; }
        / integer >> (c){ return [cast(byte)c]; };
    
    SExpValue quote
        = !"'" sexp >> makeQuote;
    
    
    string booleanstr = "#t" / "#f" / "#T" / "#F";
    string intstr = sign? digits >> join;
    string floatingstr = sign? digits "." digits >> join
                       / sign? "." digits >> join
                       / sign? digits "." >> join;
    string identifierstr = initial subsequents >> join
                         / peculiarIdentifier;
    string unitstr = "()" / "[]";
    string digits = digit digits >> join / digit;
    string stringElements
        = !"\\a" stringElements >> (s){ return join("\a", s); }
        / !"\\b" stringElements >> (s){ return join("\b", s); }
        / !"\\t" stringElements >> (s){ return join("\t", s); }
        / !"\\n" stringElements >> (s){ return join("\n", s); }
        / !"\\v" stringElements >> (s){ return join("\v", s); }
        / !"\\f" stringElements >> (s){ return join("\f", s); }
        / !"\\r" stringElements >> (s){ return join("\r", s); }
        / !"\\\"" stringElements >> (s){ return join("\"", s); }
        / !"\\\\" stringElements >> (s){ return join("\\", s); }
        / "\""
        / anyChar stringElements >> join;

    string whitespace = eol / " " / "\t" / "\v";
    string delimiter = "(" / ")" / "[" / "]" / "#(" / "#vu8" / "'" / "`" / "," / ",@"
                     / "." / "#'" / "#`" / "#," / "#,@";
    
    string eol = "\r\n" / "\n" / "\r";
    string comment = ";" untilEOL >> join;
    string untilEOL = eol / anyChar untilEOL >> join;
    string atmospheres = atmosphere* >> join;
    string atmosphere = whitespace / comment;
    
    string initial = letter / specialInitial;
    string letter = [a-zA-Z];
    string specialInitial = "!" / "$" / "%" / "&" / "*" / "/" / ":" / "<" / "=" / ">" / "?" / "^" / "_" / "~";
    string subsequents = subsequent* >> join;
    string subsequent = initial / digit / specialSubsequent;
    string specialSubsequent = "+" / "-" / "." / "@";
    string peculiarIdentifier = "+" / "-" / "..." / "->" subsequents >> join;
    string digit = [0-9];
    string sign = "+" / "-";
    string characterName = "nul" / "alarm" / "backspace" / "tab"
                         / "linefeed" / "newline" / "vtab" / "page" / "return"
                         / "esc" / "space" / "delete";
    string anyChar = parseAnyChar;
};

//////////////////////////////////////////////////////////////////////
// main
/////////////////////////////////////////////////////////////////////
import std.file  : read, write;
import std.stdio : writeln;
import std.algorithm : countUntil;

debug (SExpOutputParser) {
    void outputGenerated() {
        auto src = import(__FILE__);
        auto p1 = src.countUntil("//START OUTPUT");
        auto p2 = src.countUntil("//END OUTPUT");
        auto buf = q{
            import ctpg;
            
            //////////////////////////////////////////////////////////////////////
        } ~ src[p1 .. p2] ~ "\n\n" ~ generateParsers(parserStr);
        std.file.write("sexpparsersrc.d", buf);
    }
}

enum tarai = q{
    (defun tak (x y z)
        (if (<= x y)
            y
            (tak (tak (1- x) y z)
            (tak (1- y) z x)
            (tak (1- z) x y))))
};

void main(string[] args){
    debug (SExpOutputParser) outputGenerated();
    if (args.length >= 2) {
        parseSExp(cast(string)read(args[1])).writeln();
    }
    parseSExp(tarai).writeln();
}

