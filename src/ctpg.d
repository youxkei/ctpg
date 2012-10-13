// Written in the D programming language.
/++
This module implements a compile time parser generator.
+/
/*          Copyright youkei 2010 - 2012.
 * Distributed under the Boost Software License, Version 1.0.
 *    (See accompanying file LICENSE_1_0.txt or copy at
 *          http://www.boost.org/LICENSE_1_0.txt)
 */

module ctpg;

import std.array:       save, empty, join;
import std.conv:        to, text;
import std.range:       isInputRange, isForwardRange, ElementType;
import std.traits:      CommonType, isCallable, ReturnType, isSomeChar, isSomeString, Unqual, isAssignable, isArray;
import std.typetuple:   staticMap, TypeTuple;
import std.metastrings: toStringNow;

import std.utf: decode;

public import std.typecons: Tuple, isTuple, tuple;

alias Tuple!() None;

version = Issue_8038_Fixed;
//debug = ctpg;
debug(ctpg){
    debug = ctpg_compile_time;
}

private:

import std.stdio;

debug(ctpg) void main(){
    "unittest passed".writeln();
}

version(unittest){
    import std.stdio: writeln;
    template TestParser(T){
        alias T ResultType;
        ParseResult!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
            return typeof(return)();
        }
    }

    struct TestRange(T){
        static assert(isForwardRange!(typeof(this)));
        immutable(T)[] source;

        const pure @safe nothrow @property
        T front(){ return source[0]; }

        pure @safe nothrow @property
        void popFront(){ source = source[1..$]; }

        const pure @safe nothrow @property
        bool empty(){ return source.length == 0; }

        const pure @safe nothrow @property
        typeof(this) save(){ return this; }

        const pure @safe nothrow
        bool opEquals(in TestRange rhs){
            return source == rhs.source;
        }
    }

    TestRange!(T) testRange(T)(immutable(T)[] source){
        return TestRange!T(source);
    }
}

template ParserType(alias parser){
    static if(is(parser.ResultType)){
        alias parser.ResultType ParserType;
    }else{
        static assert(false);
    }
}

unittest{
    static assert(is(ParserType!(TestParser!string) == string));
    static assert(is(ParserType!(TestParser!int) == int));
    static assert(is(ParserType!(TestParser!long) == long));
}

template isCharRange(R){
    enum isCharRange = isInputRange!R && isSomeChar!(ElementType!R);
}

unittest{
    static assert(isCharRange!(TestRange! char));
    static assert(isCharRange!(TestRange!wchar));
    static assert(isCharRange!(TestRange!dchar));
    static assert(!isCharRange!int);
}

public:

final class CallerInfo{
    this(size_t line, string file){
        _line = line;
        _file = file;
    }

    pure @safe nothrow const @property
    size_t line(){
        return _line;
    }

    pure @safe nothrow const @property
    string file(){
        return _file;
    }

    private{
        size_t _line;
        string _file;
    }
}

// struct Option
    struct Option(T){
        public{
            bool some;
            T value;

            alias value this;
        }
    }

    Option!T makeOption(T)(bool some, T value){
        return Option!T(some, value);
    }

alias Tuple!(string, string) StateType;

// struct Context
    struct Context(Range){
        Range input;
        size_t position;
        size_t line = 1;
        StateType state;

        unittest{
            static assert(isForwardRange!Range);
        }

        invariant(){
            assert(line >= 1);
        }

        @property
        Context save(){
            return Context(input.save, position, line, state);
        }

        @property
        bool empty(){
            return input.empty;
        }

        equals_t opEquals(Context rhs){
            return input == rhs.input && position == rhs.position && line == rhs.line && state == rhs.state;
        }
    }

    Context!Range makeContext(Range)(Range range, size_t position = 0, size_t line = 1, StateType state = StateType.init){
        return Context!Range(range, position, line, state);
    }

// struct ParseResult
    struct ParseResult(Range, T){
        bool match;
        T value;
        Context!Range next;
        Error error;

        void opAssign(U)(ParseResult!(Range, U) rhs)if(isAssignable!(T, U)){
            match = rhs.match;
            value = rhs.value;
            next = rhs.next;
            error = rhs.error;
        }

        equals_t opEquals(ParseResult lhs){
            return match == lhs.match && value == lhs.value && next == lhs.next && error == lhs.error;
        }
    }

    ParseResult!(Range, T) makeParseResult(Range, T)(bool match, T value, Context!Range next, Error error = Error.init){
        return ParseResult!(Range, T)(match, value, next, error);
    }

// struct Error
    struct Error{
        invariant(){
            assert(line >= 1);
        }

        string need;
        size_t position;
        size_t line = 1;

        pure @safe nothrow const
        bool opEquals(in Error rhs){
            return need == rhs.need && position == rhs.position && line == rhs.line;
        }
    }

// function flat
    string flat(Arg)(Arg arg){
        static if(is(Arg == Tuple!(string, string[]))){
            string result = arg[0];
            foreach(elem; arg[1]){
                result ~= elem;
            }
            return result;
        }else{
            string result;
            static if(isTuple!Arg || isArray!Arg){
                if(arg.length){
                    foreach(elem; arg){
                        result ~= flat(elem);
                    }
                }
            }else{
                result = arg.to!string();
            }
            return result;
        }
    }

    unittest{
        enum dg = {
            assert(flat(tuple(1, "hello", tuple(2, "world"))) == "1hello2world");
            assert(flat(tuple([0, 1, 2], "hello", tuple([3, 4, 5], ["wor", "ld!!"]), ["!", "!"])) == "012hello345world!!!!");
            assert(flat(tuple('表', 'が', '怖', 'い', '噂', 'の', 'ソ', 'フ', 'ト')) == "表が怖い噂のソフト");
            assert(flat(tuple("A", [""][0..0])) == "A");
            return true;
        };
        debug(ctpg_compile_time) static assert(dg());
        dg();
    }

// parsers
    // success
        template success(){
            alias None ResultType;
            static ParseResult!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                return makeParseResult(true, None.init, input, Error.init);
            }
        }

    // failure
        template failure(){
            alias None ResultType;
            static ParseResult!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                return makeParseResult(false, None.init, Context!R.init, Error("", input.position, input.line));
            }
        }

    // parseString
        template staticConvertString(string str, T){
            static if(is(T == string)){
                alias str staticConvertString;
            }else static if(is(T == wstring)){
                enum staticConvertString = str.to!wstring();
            }else static if(is(T == dstring)){
                enum staticConvertString = str.to!dstring();
            }else static if(isCharRange!T){
                static if(is(Unqual!(ElementType!T) == char)){
                    alias str staticConvertString;
                }else static if(is(Unqual!(ElementType!T) == wchar)){
                    enum staticConvertString = str.to!wstring();
                }else static if(is(Unqual!(ElementType!T) == dchar)){
                    enum staticConvertString = str.to!dstring();
                }else{
                    static assert(false);
                }
            }else{
                static assert(false);
            }
        }

        unittest{
            static assert(staticConvertString!("foobar", string) == "foobar");
            static assert(staticConvertString!("foobar", wstring) == "foobar"w);
            static assert(staticConvertString!("foobar", dstring) == "foobar"d);
            static assert(staticConvertString!("foobar", TestRange!char) == "foobar");
            static assert(staticConvertString!("foobar", TestRange!wchar) == "foobar"w);
            static assert(staticConvertString!("foobar", TestRange!dchar) == "foobar"d);
        }

        size_t countLines(string str){
            typeof(return) lines;
            foreach(c; str){
                if(c == '\n'){
                    ++lines;
                }
            }
            return lines;
        }

        unittest{
            enum dg = {
                assert(countLines("これ\nとこれ") == 1);
                assert(countLines("これ\nとこれ\nとさらにこれ") == 2);
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

        template parseString(string str){
            static assert(str.length);
            alias string ResultType;
            static ParseResult!(R, ResultType) parse(R)(Context!R _input, in CallerInfo info){
                auto input = _input; // Somehow this parser doesn't work well without this line.
                enum lines = str.countLines();
                typeof(return) result;
                static if(isSomeString!R){
                    enum convertedString = staticConvertString!(str, R);
                    if(input.input.length >= convertedString.length && convertedString == input.input[0..convertedString.length]){
                        result.match = true;
                        result.value = str;
                        result.next.input = input.input[convertedString.length..$];
                        result.next.line = input.line + lines;
                        result.next.position = input.position + convertedString.length;
                        result.next.state = input.state;
                        return result;
                    }
                    result.error = Error('"' ~ str ~ '"', input.position, input.line);
                }else static if(isCharRange!R){
                    enum convertedString = staticConvertString!(str, R);
                    foreach(c; convertedString){
                        if(input.input.empty || c != input.input.front){
                            goto Lerror;
                        }else{
                            input.input.popFront;
                        }
                    }
                    result.match = true;
                    result.value = str;
                    result.next.input = input.input;
                    result.next.line = input.line + lines;
                    result.next.position = input.position + convertedString.length;
                    result.next.state = input.state;
                    return result;

                    Lerror:

                    result.error = Error('"' ~ str ~ '"', input.position, input.line);
                }else{
                    throw new Exception("");
                }
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(parseString!"hello".parse(makeContext("hello world"             ), new CallerInfo(0, "")) == makeParseResult(true, "hello", makeContext(" world"             , 5)));
                assert(parseString!"hello".parse(makeContext("hello world"w            ), new CallerInfo(0, "")) == makeParseResult(true, "hello", makeContext(" world"w            , 5)));
                assert(parseString!"hello".parse(makeContext("hello world"d            ), new CallerInfo(0, "")) == makeParseResult(true, "hello", makeContext(" world"d            , 5)));
                assert(parseString!"hello".parse(makeContext("hello world" .testRange()), new CallerInfo(0, "")) == makeParseResult(true, "hello", makeContext(" world" .testRange(), 5)));
                assert(parseString!"hello".parse(makeContext("hello world"w.testRange()), new CallerInfo(0, "")) == makeParseResult(true, "hello", makeContext(" world"w.testRange(), 5)));
                assert(parseString!"hello".parse(makeContext("hello world"d.testRange()), new CallerInfo(0, "")) == makeParseResult(true, "hello", makeContext(" world"d.testRange(), 5)));

                assert(parseString!"hello".parse(makeContext("hello"             ), new CallerInfo(0, "")) == makeParseResult(true, "hello", makeContext(""             , 5)));
                assert(parseString!"hello".parse(makeContext("hello"w            ), new CallerInfo(0, "")) == makeParseResult(true, "hello", makeContext(""w            , 5)));
                assert(parseString!"hello".parse(makeContext("hello"d            ), new CallerInfo(0, "")) == makeParseResult(true, "hello", makeContext(""d            , 5)));
                assert(parseString!"hello".parse(makeContext("hello" .testRange()), new CallerInfo(0, "")) == makeParseResult(true, "hello", makeContext("" .testRange(), 5)));
                assert(parseString!"hello".parse(makeContext("hello"w.testRange()), new CallerInfo(0, "")) == makeParseResult(true, "hello", makeContext(""w.testRange(), 5)));
                assert(parseString!"hello".parse(makeContext("hello"d.testRange()), new CallerInfo(0, "")) == makeParseResult(true, "hello", makeContext(""d.testRange(), 5)));


                assert(parseString!"表が怖い".parse(makeContext("表が怖い噂のソフト"             ), new CallerInfo(0, "")) == makeParseResult(true, "表が怖い", makeContext("噂のソフト"             , 12)));
                assert(parseString!"表が怖い".parse(makeContext("表が怖い噂のソフト"w            ), new CallerInfo(0, "")) == makeParseResult(true, "表が怖い", makeContext("噂のソフト"w            ,  4)));
                assert(parseString!"表が怖い".parse(makeContext("表が怖い噂のソフト"d            ), new CallerInfo(0, "")) == makeParseResult(true, "表が怖い", makeContext("噂のソフト"d            ,  4)));
                assert(parseString!"表が怖い".parse(makeContext("表が怖い噂のソフト" .testRange()), new CallerInfo(0, "")) == makeParseResult(true, "表が怖い", makeContext("噂のソフト" .testRange(), 12)));
                assert(parseString!"表が怖い".parse(makeContext("表が怖い噂のソフト"w.testRange()), new CallerInfo(0, "")) == makeParseResult(true, "表が怖い", makeContext("噂のソフト"w.testRange(),  4)));
                assert(parseString!"表が怖い".parse(makeContext("表が怖い噂のソフト"d.testRange()), new CallerInfo(0, "")) == makeParseResult(true, "表が怖い", makeContext("噂のソフト"d.testRange(),  4)));

                assert(parseString!"hello".parse(makeContext("hllo world"             ), new CallerInfo(0, "")) == makeParseResult(false, "", makeContext(""             ), Error(q{"hello"}, 0)));
                assert(parseString!"hello".parse(makeContext("hllo world"w            ), new CallerInfo(0, "")) == makeParseResult(false, "", makeContext(""w            ), Error(q{"hello"}, 0)));
                assert(parseString!"hello".parse(makeContext("hllo world"d            ), new CallerInfo(0, "")) == makeParseResult(false, "", makeContext(""d            ), Error(q{"hello"}, 0)));
                assert(parseString!"hello".parse(makeContext("hllo world" .testRange()), new CallerInfo(0, "")) == makeParseResult(false, "", makeContext("" .testRange()), Error(q{"hello"}, 0)));
                assert(parseString!"hello".parse(makeContext("hllo world"w.testRange()), new CallerInfo(0, "")) == makeParseResult(false, "", makeContext(""w.testRange()), Error(q{"hello"}, 0)));
                assert(parseString!"hello".parse(makeContext("hllo world"d.testRange()), new CallerInfo(0, "")) == makeParseResult(false, "", makeContext(""d.testRange()), Error(q{"hello"}, 0)));

                try{
                    scope(success) assert(false);
                    auto result = parseString!"hello".parse(makeContext([0, 0]), new CallerInfo(0, ""));
                }catch(Exception ex){}
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // parseCharRange
        dchar decodeRange(R)(auto ref R range, auto ref size_t advance){
            dchar result;
            static if(is(Unqual!(ElementType!R) == char)){
                if(!(range.front & 0b_1000_0000)){
                    result = range.front;
                    range.popFront;
                    advance = 1;
                    return result;
                }else if(!(range.front & 0b_0010_0000)){
                    result = range.front & 0b_0001_1111;
                    result <<= 6;
                    range.popFront;
                    result |= range.front & 0b_0011_1111;
                    range.popFront;
                    advance = 2;
                    return result;
                }else if(!(range.front & 0b_0001_0000)){
                    result = range.front & 0b_0000_1111;
                    result <<= 6;
                    range.popFront;
                    result |= range.front & 0b_0011_1111;
                    result <<= 6;
                    range.popFront;
                    result |= range.front & 0b_0011_1111;
                    range.popFront;
                    advance = 3;
                    return result;
                }else{
                    result = range.front & 0b_0000_0111;
                    result <<= 6;
                    range.popFront;
                    result |= range.front & 0b_0011_1111;
                    result <<= 6;
                    range.popFront;
                    result |= range.front & 0b_0011_1111;
                    result <<= 6;
                    range.popFront;
                    result |= range.front & 0b_0011_1111;
                    range.popFront;
                    advance = 4;
                    return result;
                }
            }else static if(is(Unqual!(ElementType!R) == wchar)){
                if(range.front <= 0xD7FF || (0xE000 <= range.front && range.front < 0xFFFF)){
                    result = range.front;
                    range.popFront;
                    advance = 1;
                    return result;
                }else{
                    result = (range.front & 0b_0000_0011_1111_1111) * 0x400;
                    range.popFront;
                    result += (range.front & 0b_0000_0011_1111_1111) + 0x10000;
                    range.popFront;
                    advance = 2;
                    return result;
                }
            }else static if(is(Unqual!(ElementType!R) == dchar)){
                result = range.front;
                range.popFront;
                advance = 1;
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(decodeRange(testRange("\u0001"), 0) == '\u0001');
                assert(decodeRange(testRange("\u0081"), 0) == '\u0081');
                assert(decodeRange(testRange("\u0801"), 0) == '\u0801');
                assert(decodeRange(testRange("\U00012345"), 0) == '\U00012345');
                assert(decodeRange(testRange("\u0001"w), 0) == '\u0001');
                assert(decodeRange(testRange("\uE001"w), 0) == '\uE001');
                assert(decodeRange(testRange("\U00012345"w), 0) == '\U00012345');
                assert(decodeRange(testRange("\U0010FFFE"), 0) == '\U0010FFFE');
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

        template parseCharRange(dchar low, dchar high){
            static assert(low <= high);

            alias string ResultType;
            static ParseResult!(R, ResultType) parse(R)(Context!R _input, in CallerInfo info){
                auto input = _input; // Somehow this parser doesn't work well without this line.
                typeof(return) result;
                static if(isSomeString!R){
                    if(input.input.length){
                        size_t idx;
                        dchar c = decode(input.input, idx);
                        if(low <= c && c <= high){
                            result.match = true;
                            static if(is(R == string)){
                                result.value = input.input[0..idx];
                            }else{
                                result.value = c.to!string();
                            }
                            result.next.input = input.input[idx..$];
                            result.next.line = c == '\n' ? input.line + 1 : input.line;
                            result.next.position = input.position + idx;
                            result.next.state = input.state;
                            return result;
                        }
                    }
                    if(low == dchar.min && high == dchar.max){
                        result.error = Error("any char", input.position, input.line);
                    }else{
                        result.error = Error("c: '" ~ low.to!string() ~ "' <= c <= '" ~ high.to!string() ~ "'", input.position, input.line);
                    }
                }else static if(isCharRange!R){
                    if(!input.input.empty){
                        size_t advance;
                        dchar c = decodeRange(input.input, advance);
                        if(low <= c && c <= high){
                            result.match = true;
                            result.value = c.to!string();
                            result.next.input = input.input;
                            result.next.line = c == '\n' ? input.line + 1 : input.line;
                            result.next.position = input.position + advance;
                            result.next.state = input.state;
                            return result;
                        }
                    }
                    if(low == dchar.min && high == dchar.max){
                        result.error = Error("any char", input.position, input.line);
                    }else{
                        result.error = Error("c: '" ~ low.to!string() ~ "' <= c <= '" ~ high.to!string() ~ "'", input.position, input.line);
                    }
                }else{
                    throw new Exception("");
                }
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(parseCharRange!('a', 'z').parse(makeContext("hoge"             ), new CallerInfo(0, "")) == makeParseResult(true, "h", makeContext("oge"             , 1)));
                assert(parseCharRange!('a', 'z').parse(makeContext("hoge"w            ), new CallerInfo(0, "")) == makeParseResult(true, "h", makeContext("oge"w            , 1)));
                assert(parseCharRange!('a', 'z').parse(makeContext("hoge"d            ), new CallerInfo(0, "")) == makeParseResult(true, "h", makeContext("oge"d            , 1)));
                assert(parseCharRange!('a', 'z').parse(makeContext("hoge" .testRange()), new CallerInfo(0, "")) == makeParseResult(true, "h", makeContext("oge" .testRange(), 1)));
                assert(parseCharRange!('a', 'z').parse(makeContext("hoge"w.testRange()), new CallerInfo(0, "")) == makeParseResult(true, "h", makeContext("oge"w.testRange(), 1)));
                assert(parseCharRange!('a', 'z').parse(makeContext("hoge"d.testRange()), new CallerInfo(0, "")) == makeParseResult(true, "h", makeContext("oge"d.testRange(), 1)));

                assert(parseCharRange!('\u0100', '\U0010FFFF').parse(makeContext("\U00012345hoge"             ), new CallerInfo(0, "")) == makeParseResult(true, "\U00012345", makeContext("hoge"             , 4)));
                assert(parseCharRange!('\u0100', '\U0010FFFF').parse(makeContext("\U00012345hoge"w            ), new CallerInfo(0, "")) == makeParseResult(true, "\U00012345", makeContext("hoge"w            , 2)));
                assert(parseCharRange!('\u0100', '\U0010FFFF').parse(makeContext("\U00012345hoge"d            ), new CallerInfo(0, "")) == makeParseResult(true, "\U00012345", makeContext("hoge"d            , 1)));
                assert(parseCharRange!('\u0100', '\U0010FFFF').parse(makeContext("\U00012345hoge" .testRange()), new CallerInfo(0, "")) == makeParseResult(true, "\U00012345", makeContext("hoge" .testRange(), 4)));
                assert(parseCharRange!('\u0100', '\U0010FFFF').parse(makeContext("\U00012345hoge"w.testRange()), new CallerInfo(0, "")) == makeParseResult(true, "\U00012345", makeContext("hoge"w.testRange(), 2)));
                assert(parseCharRange!('\u0100', '\U0010FFFF').parse(makeContext("\U00012345hoge"d.testRange()), new CallerInfo(0, "")) == makeParseResult(true, "\U00012345", makeContext("hoge"d.testRange(), 1)));

                assert(parseCharRange!('\u0100', '\U0010FFFF').parse(makeContext("hello world"             ), new CallerInfo(0, "")) == makeParseResult(false, "", makeContext(""             ), Error("c: '\u0100' <= c <= '\U0010FFFF'")));
                assert(parseCharRange!('\u0100', '\U0010FFFF').parse(makeContext("hello world"w            ), new CallerInfo(0, "")) == makeParseResult(false, "", makeContext(""w            ), Error("c: '\u0100' <= c <= '\U0010FFFF'")));
                assert(parseCharRange!('\u0100', '\U0010FFFF').parse(makeContext("hello world"d            ), new CallerInfo(0, "")) == makeParseResult(false, "", makeContext(""d            ), Error("c: '\u0100' <= c <= '\U0010FFFF'")));
                assert(parseCharRange!('\u0100', '\U0010FFFF').parse(makeContext("hello world" .testRange()), new CallerInfo(0, "")) == makeParseResult(false, "", makeContext("" .testRange()), Error("c: '\u0100' <= c <= '\U0010FFFF'")));
                assert(parseCharRange!('\u0100', '\U0010FFFF').parse(makeContext("hello world"w.testRange()), new CallerInfo(0, "")) == makeParseResult(false, "", makeContext(""w.testRange()), Error("c: '\u0100' <= c <= '\U0010FFFF'")));
                assert(parseCharRange!('\u0100', '\U0010FFFF').parse(makeContext("hello world"d.testRange()), new CallerInfo(0, "")) == makeParseResult(false, "", makeContext(""d.testRange()), Error("c: '\u0100' <= c <= '\U0010FFFF'")));

                try{
                    scope(success) assert(false);
                    auto result = parseCharRange!('\u0100', '\U0010FFFF').parse(makeContext([0, 0]), new CallerInfo(0, ""));
                }catch(Exception ex){}
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // parseEscapeSequence
        template parseEscapeSequence(){
            alias string ResultType;
            static ParseResult!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                typeof(return) result;
                static if(isSomeString!R){
                    if(input.input[0] == '\\'){
                        switch(input.input[1]){
                            case 'u':{
                                result.match = true;
                                result.value = input.input[0..6].to!string();
                                result.next.input = input.input[6..$];
                                result.next.line = input.line;
                                result.next.position = input.position + 1;
                                result.next.state = input.state;
                                return result;
                            }
                            case 'U':{
                                result.match = true;
                                result.value = input.input[0..10].to!string();
                                result.next.input = input.input[10..$];
                                result.next.line = input.line;
                                result.next.position = input.position + 1;
                                result.next.state = input.state;
                                return result;
                            }
                            case '\'': case '"': case '?': case '\\': case 'a': case 'b': case 'f': case 'n': case 'r': case 't': case 'v':{
                                result.match = true;
                                result.value = input.input[0..2].to!string();
                                result.next.input = input.input[2..$];
                                result.next.line = input.line;
                                result.next.position = input.position + 1;
                                result.next.state = input.state;
                                return result;
                            }
                            default:{
                            }
                        }
                    }
                    result.error = Error("escape sequence", input.position, input.line);
                }else static if(isCharRange!R){
                    auto c1 = input.input.front;
                    if(c1 == '\\'){
                        input.input.popFront;
                        auto c2 = input.input.front;
                        switch(c2){
                            case 'u':{
                                result.match = true;
                                input.input.popFront;
                                char[6] data;
                                data[0..2] = "\\u";
                                foreach(idx; 2..6){
                                    data[idx] = cast(char)input.input.front;
                                    input.input.popFront;
                                }
                                result.value = to!string(data);
                                result.next.input = input.input;
                                result.next.line = input.line;
                                result.next.position = input.position + 1;
                                result.next.state = input.state;
                                return result;
                            }
                            case 'U':{
                                result.match = true;
                                input.input.popFront;
                                char[10] data;
                                data[0..2] = "\\U";
                                foreach(idx; 2..10){
                                    data[idx] = cast(char)input.input.front;
                                    input.input.popFront;
                                }
                                result.value = to!string(data);
                                result.next.input = input.input;
                                result.next.line = input.line;
                                result.next.position = input.position + 1;
                                result.next.state = input.state;
                                return result;
                            }
                            case '\'': case '"': case '?': case '\\': case 'a': case 'b': case 'f': case 'n': case 'r': case 't': case 'v':{
                                result.match = true;
                                input.input.popFront;
                                result.value = "\\" ~ to!string(c2);
                                result.next.input = input.input;
                                result.next.line = input.line;
                                result.next.position = input.position + 1;
                                result.next.state = input.state;
                                return result;
                            }
                            default:{
                            }
                        }
                    }
                    result.error = Error("escape sequence", input.position, input.line);
                }else{
                    throw new Exception("");
                }
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(parseEscapeSequence!().parse(makeContext(`\"hoge`             ), new CallerInfo(0, "")) == makeParseResult(true, `\"`, makeContext("hoge"             , 1)));
                assert(parseEscapeSequence!().parse(makeContext(`\"hoge`w            ), new CallerInfo(0, "")) == makeParseResult(true, `\"`, makeContext("hoge"w            , 1)));
                assert(parseEscapeSequence!().parse(makeContext(`\"hoge`d            ), new CallerInfo(0, "")) == makeParseResult(true, `\"`, makeContext("hoge"d            , 1)));
                assert(parseEscapeSequence!().parse(makeContext(`\"hoge` .testRange()), new CallerInfo(0, "")) == makeParseResult(true, `\"`, makeContext("hoge" .testRange(), 1)));
                assert(parseEscapeSequence!().parse(makeContext(`\"hoge`w.testRange()), new CallerInfo(0, "")) == makeParseResult(true, `\"`, makeContext("hoge"w.testRange(), 1)));
                assert(parseEscapeSequence!().parse(makeContext(`\"hoge`d.testRange()), new CallerInfo(0, "")) == makeParseResult(true, `\"`, makeContext("hoge"d.testRange(), 1)));

                assert(parseEscapeSequence!().parse(makeContext(`\U0010FFFFhoge`             ), new CallerInfo(0, "")) == makeParseResult(true, `\U0010FFFF`, makeContext("hoge"             , 1)));
                assert(parseEscapeSequence!().parse(makeContext(`\U0010FFFFhoge`w            ), new CallerInfo(0, "")) == makeParseResult(true, `\U0010FFFF`, makeContext("hoge"w            , 1)));
                assert(parseEscapeSequence!().parse(makeContext(`\U0010FFFFhoge`d            ), new CallerInfo(0, "")) == makeParseResult(true, `\U0010FFFF`, makeContext("hoge"d            , 1)));
                assert(parseEscapeSequence!().parse(makeContext(`\U0010FFFFhoge` .testRange()), new CallerInfo(0, "")) == makeParseResult(true, `\U0010FFFF`, makeContext("hoge" .testRange(), 1)));
                assert(parseEscapeSequence!().parse(makeContext(`\U0010FFFFhoge`w.testRange()), new CallerInfo(0, "")) == makeParseResult(true, `\U0010FFFF`, makeContext("hoge"w.testRange(), 1)));
                assert(parseEscapeSequence!().parse(makeContext(`\U0010FFFFhoge`d.testRange()), new CallerInfo(0, "")) == makeParseResult(true, `\U0010FFFF`, makeContext("hoge"d.testRange(), 1)));

                assert(parseEscapeSequence!().parse(makeContext(`\u10FFhoge`             ), new CallerInfo(0, "")) == makeParseResult(true, `\u10FF`, makeContext("hoge"             , 1)));
                assert(parseEscapeSequence!().parse(makeContext(`\u10FFhoge`w            ), new CallerInfo(0, "")) == makeParseResult(true, `\u10FF`, makeContext("hoge"w            , 1)));
                assert(parseEscapeSequence!().parse(makeContext(`\u10FFhoge`d            ), new CallerInfo(0, "")) == makeParseResult(true, `\u10FF`, makeContext("hoge"d            , 1)));
                assert(parseEscapeSequence!().parse(makeContext(`\u10FFhoge` .testRange()), new CallerInfo(0, "")) == makeParseResult(true, `\u10FF`, makeContext("hoge" .testRange(), 1)));
                assert(parseEscapeSequence!().parse(makeContext(`\u10FFhoge`w.testRange()), new CallerInfo(0, "")) == makeParseResult(true, `\u10FF`, makeContext("hoge"w.testRange(), 1)));
                assert(parseEscapeSequence!().parse(makeContext(`\u10FFhoge`d.testRange()), new CallerInfo(0, "")) == makeParseResult(true, `\u10FF`, makeContext("hoge"d.testRange(), 1)));

                assert(parseEscapeSequence!().parse(makeContext(`\nhoge`             ), new CallerInfo(0, "")) == makeParseResult(true, `\n`, makeContext("hoge"             , 1)));
                assert(parseEscapeSequence!().parse(makeContext(`\nhoge`w            ), new CallerInfo(0, "")) == makeParseResult(true, `\n`, makeContext("hoge"w            , 1)));
                assert(parseEscapeSequence!().parse(makeContext(`\nhoge`d            ), new CallerInfo(0, "")) == makeParseResult(true, `\n`, makeContext("hoge"d            , 1)));
                assert(parseEscapeSequence!().parse(makeContext(`\nhoge` .testRange()), new CallerInfo(0, "")) == makeParseResult(true, `\n`, makeContext("hoge" .testRange(), 1)));
                assert(parseEscapeSequence!().parse(makeContext(`\nhoge`w.testRange()), new CallerInfo(0, "")) == makeParseResult(true, `\n`, makeContext("hoge"w.testRange(), 1)));
                assert(parseEscapeSequence!().parse(makeContext(`\nhoge`d.testRange()), new CallerInfo(0, "")) == makeParseResult(true, `\n`, makeContext("hoge"d.testRange(), 1)));

                assert(parseEscapeSequence!().parse(makeContext("鬱hoge"             ), new CallerInfo(0, "")) == makeParseResult(false, "", makeContext(""             ), Error("escape sequence")));
                assert(parseEscapeSequence!().parse(makeContext("鬱hoge"w            ), new CallerInfo(0, "")) == makeParseResult(false, "", makeContext(""w            ), Error("escape sequence")));
                assert(parseEscapeSequence!().parse(makeContext("鬱hoge"d            ), new CallerInfo(0, "")) == makeParseResult(false, "", makeContext(""d            ), Error("escape sequence")));
                assert(parseEscapeSequence!().parse(makeContext("鬱hoge" .testRange()), new CallerInfo(0, "")) == makeParseResult(false, "", makeContext("" .testRange()), Error("escape sequence")));
                assert(parseEscapeSequence!().parse(makeContext("鬱hoge"w.testRange()), new CallerInfo(0, "")) == makeParseResult(false, "", makeContext(""w.testRange()), Error("escape sequence")));
                assert(parseEscapeSequence!().parse(makeContext("鬱hoge"d.testRange()), new CallerInfo(0, "")) == makeParseResult(false, "", makeContext(""d.testRange()), Error("escape sequence")));

                try{
                    scope(success) assert(false);
                    auto result = parseEscapeSequence!().parse(makeContext([0, 0][]), new CallerInfo(0, ""));
                }catch(Exception ex){}
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // parseSpace
        template parseSpace(){
            alias string ResultType;
            static ParseResult!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                typeof(return) result;
                static if(isSomeString!R){
                    if(input.input.length > 0 && (input.input[0] == ' ' || input.input[0] == '\n' || input.input[0] == '\t' || input.input[0] == '\r' || input.input[0] == '\f')){
                        result.match = true;
                        result.value = input.input[0..1].to!string();
                        result.next.input = input.input[1..$];
                        result.next.line = (input.input[0] == '\n' ? input.line + 1 : input.line);
                        result.next.position = input.position + 1;
                        result.next.state = input.state;
                        return result;
                    }
                    result.error = Error("space", input.position, input.line);
                }else static if(isCharRange!R){
                    if(!input.input.empty){
                        Unqual!(ElementType!R) c = input.input.front;
                        if(c == ' ' || c == '\n' || c == '\t' || c == '\r' || c == '\f'){
                            result.match = true;
                            result.value = c.to!string();
                            input.input.popFront;
                            result.next.input = input.input;
                            result.next.line = (c == '\n' ? input.line + 1 : input.line);
                            result.next.position = input.position + 1;
                            result.next.state = input.state;
                            return result;
                        }
                    }
                    result.error = Error("space", input.position, input.line);
                }else{
                    throw new Exception("");
                }
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(parseSpace!().parse(makeContext("\thoge"             ), new CallerInfo(0, "")) == makeParseResult(true, "\t", makeContext("hoge"             , 1)));
                assert(parseSpace!().parse(makeContext("\thoge"w            ), new CallerInfo(0, "")) == makeParseResult(true, "\t", makeContext("hoge"w            , 1)));
                assert(parseSpace!().parse(makeContext("\thoge"d            ), new CallerInfo(0, "")) == makeParseResult(true, "\t", makeContext("hoge"d            , 1)));
                assert(parseSpace!().parse(makeContext("\thoge" .testRange()), new CallerInfo(0, "")) == makeParseResult(true, "\t", makeContext("hoge" .testRange(), 1)));
                assert(parseSpace!().parse(makeContext("\thoge"w.testRange()), new CallerInfo(0, "")) == makeParseResult(true, "\t", makeContext("hoge"w.testRange(), 1)));
                assert(parseSpace!().parse(makeContext("\thoge"d.testRange()), new CallerInfo(0, "")) == makeParseResult(true, "\t", makeContext("hoge"d.testRange(), 1)));

                assert(parseSpace!().parse(makeContext("hoge"             ), new CallerInfo(0, "")) == makeParseResult(false, "", makeContext(""             ), Error("space")));
                assert(parseSpace!().parse(makeContext("hoge"w            ), new CallerInfo(0, "")) == makeParseResult(false, "", makeContext(""w            ), Error("space")));
                assert(parseSpace!().parse(makeContext("hoge"d            ), new CallerInfo(0, "")) == makeParseResult(false, "", makeContext(""d            ), Error("space")));
                assert(parseSpace!().parse(makeContext("hoge" .testRange()), new CallerInfo(0, "")) == makeParseResult(false, "", makeContext("" .testRange()), Error("space")));
                assert(parseSpace!().parse(makeContext("hoge"w.testRange()), new CallerInfo(0, "")) == makeParseResult(false, "", makeContext(""w.testRange()), Error("space")));
                assert(parseSpace!().parse(makeContext("hoge"d.testRange()), new CallerInfo(0, "")) == makeParseResult(false, "", makeContext(""d.testRange()), Error("space")));

                try{
                    scope(success) assert(false);
                    auto result = parseSpace!().parse(makeContext([0, 0]), new CallerInfo(0, ""));
                }catch(Exception ex){}
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // parseEOF
        template parseEOF(){
            alias None ResultType;
            static ParseResult!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                typeof(return) result;
                if(input.input.empty){
                    result.match = true;
                    result.next.input = input.input;
                    result.next.line = input.line;
                    result.next.position = input.position;
                    result.next.state = input.state;
                }else{
                    result.error = Error("EOF", input.position, input.line);
                }
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(parseEOF!().parse(makeContext(""             ), new CallerInfo(0, "")) == makeParseResult(true, None.init, makeContext(""             , 0)));
                assert(parseEOF!().parse(makeContext(""w            ), new CallerInfo(0, "")) == makeParseResult(true, None.init, makeContext(""w            , 0)));
                assert(parseEOF!().parse(makeContext(""d            ), new CallerInfo(0, "")) == makeParseResult(true, None.init, makeContext(""d            , 0)));
                assert(parseEOF!().parse(makeContext("" .testRange()), new CallerInfo(0, "")) == makeParseResult(true, None.init, makeContext("" .testRange(), 0)));
                assert(parseEOF!().parse(makeContext(""w.testRange()), new CallerInfo(0, "")) == makeParseResult(true, None.init, makeContext(""w.testRange(), 0)));
                assert(parseEOF!().parse(makeContext(""d.testRange()), new CallerInfo(0, "")) == makeParseResult(true, None.init, makeContext(""d.testRange(), 0)));

                assert(parseEOF!().parse(makeContext("hoge"             ), new CallerInfo(0, "")) == makeParseResult(false, None.init, makeContext(""             ), Error("EOF")));
                assert(parseEOF!().parse(makeContext("hoge"w            ), new CallerInfo(0, "")) == makeParseResult(false, None.init, makeContext(""w            ), Error("EOF")));
                assert(parseEOF!().parse(makeContext("hoge"d            ), new CallerInfo(0, "")) == makeParseResult(false, None.init, makeContext(""d            ), Error("EOF")));
                assert(parseEOF!().parse(makeContext("hoge" .testRange()), new CallerInfo(0, "")) == makeParseResult(false, None.init, makeContext("" .testRange()), Error("EOF")));
                assert(parseEOF!().parse(makeContext("hoge"w.testRange()), new CallerInfo(0, "")) == makeParseResult(false, None.init, makeContext(""w.testRange()), Error("EOF")));
                assert(parseEOF!().parse(makeContext("hoge"d.testRange()), new CallerInfo(0, "")) == makeParseResult(false, None.init, makeContext(""d.testRange()), Error("EOF")));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

// combinators
    // combinateSkip
        template combinateSkip(alias parser, alias skip){
            alias ParserType!parser ResultType;
            static ParseResult!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                auto r = parser.parse(input.save, info);
                if(!r.match){
                    auto skipped = skip.parse(input, info);
                    if(skipped.match){
                        return parser.parse(skipped.next, info);
                    }else{
                        return r;
                    }
                }else{
                    return r;
                }
            }
        }

        unittest{
            enum dg = {
                assert(combinateSkip!(parseString!"foo", parseString!" ").parse(makeContext(" foo"), new CallerInfo(0, "")) == makeParseResult(true, "foo", makeContext("", 4)));
                assert(combinateSkip!(parseString!"foo", parseString!" ").parse(makeContext("foo"), new CallerInfo(0, "")) == makeParseResult(true, "foo", makeContext("", 3)));
                assert(combinateSkip!(parseString!"foo", parseString!"foo").parse(makeContext("foo"), new CallerInfo(0, "")) == makeParseResult(true, "foo", makeContext("", 3)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // combinateUnTuple
        template combinateUnTuple(alias parser){
            static if(isTuple!(ParserType!parser) && ParserType!parser.Types.length == 1){
                alias ParserType!parser.Types[0] ResultType;
                static ParseResult!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                    typeof(return) result;
                    auto r = parser.parse(input, info);
                    result.match = r.match;
                    result.value = r.value[0];
                    result.next = r.next;
                    result.error = r.error;
                    return result;
                }
            }else{
                alias parser combinateUnTuple;
            }
        }

        unittest{
            enum dg = {
                assert(combinateUnTuple!(TestParser!int).parse(makeContext(""), new CallerInfo(0, "")) == makeParseResult(false, 0, makeContext("")));
                assert(combinateUnTuple!(TestParser!long).parse(makeContext(""), new CallerInfo(0, "")) == makeParseResult(false, 0L, makeContext("")));
                assert(combinateUnTuple!(TestParser!string).parse(makeContext(""), new CallerInfo(0, "")) == makeParseResult(false, "", makeContext("")));
                assert(combinateUnTuple!(TestParser!wstring).parse(makeContext(""), new CallerInfo(0, "")) == makeParseResult(false, ""w, makeContext("")));
                assert(combinateUnTuple!(TestParser!dstring).parse(makeContext(""), new CallerInfo(0, "")) == makeParseResult(false, ""d, makeContext("")));
                assert(combinateUnTuple!(TestParser!(Tuple!int)).parse(makeContext(""), new CallerInfo(0, "")) == makeParseResult(false, 0, makeContext("")));
                assert(combinateUnTuple!(TestParser!(Tuple!(int, int))).parse(makeContext(""), new CallerInfo(0, "")) == makeParseResult(false, tuple(0, 0), makeContext("")));
                assert(combinateUnTuple!(TestParser!(Tuple!(Tuple!int))).parse(makeContext(""), new CallerInfo(0, "")) == makeParseResult(false, tuple(0), makeContext("")));
                assert(combinateUnTuple!(TestParser!(Tuple!(Tuple!(int, int)))).parse(makeContext(""), new CallerInfo(0, "")) == makeParseResult(false, tuple(0, 0), makeContext("")));
                assert(combinateUnTuple!(TestParser!(Tuple!(Tuple!(int, int), int))).parse(makeContext(""), new CallerInfo(0, "")) == makeParseResult(false, tuple(tuple(0, 0), 0), makeContext("")));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // combinateSequence
        template flatTuple(T){
            static if(isTuple!T){
                alias T.Types flatTuple;
            }else{
                alias T flatTuple;
            }
        }

        unittest{
            static assert(is(flatTuple!(string) == string));
            static assert(is(flatTuple!(Tuple!(string)) == TypeTuple!string));
            static assert(is(flatTuple!(Tuple!(Tuple!(string))) == TypeTuple!(Tuple!string)));
        }

        template CombinateSequenceImplType(parsers...){
            alias Tuple!(staticMap!(flatTuple, staticMap!(ParserType, parsers))) CombinateSequenceImplType;
        }

        unittest{
            static assert(is(CombinateSequenceImplType!(TestParser!string, TestParser!string) == Tuple!(string, string)));
            static assert(is(CombinateSequenceImplType!(TestParser!int, TestParser!long) == Tuple!(int, long)));
            static assert(is(CombinateSequenceImplType!(TestParser!(Tuple!(int, long)), TestParser!uint) == Tuple!(int, long, uint)));
            static assert(is(CombinateSequenceImplType!(TestParser!(Tuple!(int, long)), TestParser!(Tuple!(uint, ulong))) == Tuple!(int, long, uint, ulong)));
            static assert(is(CombinateSequenceImplType!(TestParser!(Tuple!(Tuple!(byte, short), long)), TestParser!(Tuple!(uint, ulong))) == Tuple!(Tuple!(byte, short), long, uint, ulong)));
        }

        template combinateSequence(parsers...){
            alias combinateUnTuple!(combinateSequenceImpl!(parsers)) combinateSequence;
        }

        template combinateSequenceImpl(parsers...){
            alias CombinateSequenceImplType!(parsers) ResultType;
            static ParseResult!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                typeof(return) result;
                static if(parsers.length == 1){
                    auto r = parsers[0].parse(input, info);
                    if(r.match){
                        result.match = true;
                        static if(isTuple!(ParserType!(parsers[0]))){
                            result.value = r.value;
                        }else{
                            result.value = tuple(r.value);
                        }
                        result.next = r.next;
                    }else{
                        result.error = r.error;
                    }
                }else{
                    auto r1 = parsers[0].parse(input, info);
                    if(r1.match){
                        auto r2 = combinateSequenceImpl!(parsers[1..$]).parse(r1.next, info);
                        if(r2.match){
                            result.match = true;
                            static if(isTuple!(ParserType!(parsers[0]))){
                                result.value = tuple(r1.value.field, r2.value.field);
                            }else{
                                result.value = tuple(r1.value, r2.value.field);
                            }
                            result.next = r2.next;
                        }
                        result.error = r1.error.position > r2.error.position ? r1.error : r2.error;
                    }else{
                        result.error = r1.error;
                    }
                }
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(combinateSequence!(parseString!("hello"), parseString!("world")).parse(makeContext("helloworld"), new CallerInfo(0, "")) == makeParseResult(true, tuple("hello", "world"), makeContext("", 10)));
                assert(combinateSequence!(combinateSequence!(parseString!("hello"), parseString!("world")), parseString!"!").parse(makeContext("helloworld!"), new CallerInfo(0, "")) == makeParseResult(true, tuple("hello", "world", "!"), makeContext("", 11)));
                assert(combinateSequence!(parseString!("hello"), parseString!("world")).parse(makeContext("hellovvorld"), new CallerInfo(0, "")) == makeParseResult(false, tuple("", ""), makeContext(""), Error(q{"world"}, 5)));
                assert(combinateSequence!(parseString!("hello"), parseString!("world"), parseString!("!")).parse(makeContext("helloworld?"), new CallerInfo(0, "")) == makeParseResult(false, tuple("", "", ""), makeContext(""), Error(q{"!"}, 10)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // combinateChoice
        template CommonParserType(parsers...){
            alias CommonType!(staticMap!(ParserType, parsers)) CommonParserType;
        }

        unittest{
            static assert(is(CommonParserType!(TestParser!string, TestParser!string) == string));
            static assert(is(CommonParserType!(TestParser!int, TestParser!long) == long));
            static assert(is(CommonParserType!(TestParser!byte, TestParser!short, TestParser!int) == int));
            static assert(is(CommonParserType!(TestParser!string, TestParser!int) == void));
        }

        template combinateChoice(parsers...) if(!is(typeof(parsers[0]) == size_t) && !is(typeof(parsers[1]) == string)) {
            alias combinateChoice!(0, "", parsers) combinateChoice;
        }

        template combinateChoice(size_t line, string file, parsers...){
            alias CommonParserType!(parsers) ResultType;
            static if(is(ResultType == void)){
                static if(line){
                    mixin("#line " ~ toStringNow!line ~ " \"" ~ file ~ "\"" q{
                        static assert(false, "types of parsers: \"" ~ staticMap!(ParserType, parsers).stringof[1..$-1] ~ "\" should have a common convertible type");
                    });
                }else{
                    static assert(false, "types of parsers: \"" ~ staticMap!(ParserType, parsers).stringof[1..$-1] ~ "\" should have a common convertible type");
                }
            }
            static ParseResult!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                static assert(parsers.length > 0);
                static if(parsers.length == 1){
                    return parsers[0].parse(input, info);
                }else{
                    auto r1 = parsers[0].parse(input.save, info);
                    if(r1.match){
                        return r1;
                    }
                    auto r2 = combinateChoice!(parsers[1..$]).parse(input, info);
                    if(r2.match){
                        return r2;
                    }
                    typeof(return) result;
                    result.error = r1.error.position > r2.error.position ? r1.error : r2.error;
                    return result;
                }
            }
        }

        unittest{
            enum dg = {
                assert(combinateChoice!(parseString!"h", parseString!"w").parse(makeContext("hw"), new CallerInfo(0, "")) == makeParseResult(true, "h", makeContext("w", 1))); 
                assert(combinateChoice!(parseString!"h", parseString!"w").parse(makeContext("w"), new CallerInfo(0, "")) == makeParseResult(true, "w", makeContext("", 1)));
                assert(combinateChoice!(parseString!"h", parseString!"w").parse(makeContext(""), new CallerInfo(0, "")) == makeParseResult(false, "", makeContext(""), Error(q{"w"})));
                assert(combinateChoice!(combinateSequence!(parseString!"h", parseString!"w"), combinateSequence!(parseString!"w", parseString!"h")).parse(makeContext("h"), new CallerInfo(0, "")) == makeParseResult(false, tuple("", ""), makeContext(""), Error(q{"w"}, 1)));
                //assert(combinateChoice!(parseString!"h", combinateSequence!(parseString!"w", parseString!"w")).parse(makeContext(testRange("w"d)), new CallerInfo(0, "")) == makeParseResult(true, "w", makeContext(testRange(""d), 1)));
                //assert(combinateChoice!(__LINE__, "foo/bar.d", parseString!"h", combinateSequence!(parseString!"w", parseString!"w")).parse(makeContext(testRange("w"d)), new CallerInfo(0, "")) == makeParseResult(true, "w", makeContext(testRange(""d), 1)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // combinateMore
        template combinateMore(int n, alias parser, alias sep){
            alias ParserType!(parser)[] ResultType;
            static ParseResult!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                typeof(return) result;
                Context!R next = input;
                while(true){
                    auto input1 = next.save;
                    auto r1 = parser.parse(input1, info);
                    if(r1.match){
                        result.value ~= r1.value;
                        next = r1.next;
                        auto input2 = next.save;
                        auto r2 = sep.parse(input2, info);
                        if(r2.match){
                            next = r2.next;
                        }else{
                            result.error = r2.error;
                            break;
                        }
                    }else{
                        result.error = r1.error;
                        if(result.value.length < n){
                            return result;
                        }else{
                            break;
                        }
                    }
                }
                result.match = true;
                result.next = next;
                return result;
            }
        }

        template combinateMore0(alias parser, alias sep = success!()){
            alias combinateMore!(0, parser, sep) combinateMore0;
        }

        template combinateMore1(alias parser, alias sep = success!()){
            alias combinateMore!(1, parser, sep) combinateMore1;
        }

        unittest{
            enum dg = {
                assert(combinateMore0!(parseString!"w").parse(makeContext("www w"), new CallerInfo(0, "")) == makeParseResult(true, ["w", "w", "w"], makeContext(" w", 3), Error(q{"w"}, 3)));
                assert(combinateMore0!(parseString!"w").parse(makeContext(" w"), new CallerInfo(0, "")) == makeParseResult(true, [""][0..0], makeContext(" w"), Error(q{"w"}, 0)));
                assert(combinateMore0!(combinateSequence!(parseString!"w", parseString!"h")).parse(makeContext("whwhw"), new CallerInfo(0, "")) == makeParseResult(true, [tuple("w", "h"), tuple("w", "h")], makeContext("w", 4), Error(q{"h"}, 5)));
                assert(combinateMore1!(parseString!"w").parse(makeContext("www w"), new CallerInfo(0, "")) == makeParseResult(true, ["w", "w", "w"], makeContext(" w", 3), Error(q{"w"}, 3)));
                assert(combinateMore1!(parseString!"w").parse(makeContext(" w"), new CallerInfo(0, "")) == makeParseResult(false, [""][0..0], makeContext(""), Error(q{"w"}, 0)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // combinateOption
        template combinateOption(alias parser){
            alias Option!(ParserType!parser) ResultType;
            static ParseResult!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                typeof(return) result;
                result.match = true;
                auto r = parser.parse(input.save, info);
                if(r.match){
                    result.value = r.value;
                    result.value.some = true;
                    result.next = r.next;
                }else{
                    result.next = input;
                }
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(combinateOption!(parseString!"w").parse(makeContext("w"), new CallerInfo(0, "")) == makeParseResult(true, makeOption(true, "w"), makeContext("", 1)));
                assert(combinateOption!(parseString!"w").parse(makeContext("hoge"), new CallerInfo(0, "")) == makeParseResult(true, makeOption(false, ""), makeContext("hoge", 0)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // combinateNone
        template combinateNone(alias parser){
            alias None ResultType;
            static ParseResult!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                typeof(return) result;
                auto r = parser.parse(input, info);
                if(r.match){
                    result.match = true;
                    result.next = r.next;
                }else{
                    result.error = r.error;
                }
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")).parse(makeContext("(w)"), new CallerInfo(0, "")) == makeParseResult(true, "w", makeContext("", 3)));
                assert(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")).parse(makeContext("(w}"), new CallerInfo(0, "")) == makeParseResult(false, "", makeContext(""), Error(q{")"}, 2)));
                assert(combinateNone!(parseString!"w").parse(makeContext("a"), new CallerInfo(0, "")) == makeParseResult(false, None.init, makeContext(""), Error(q{"w"})));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // combinateAndPred
        template combinateAndPred(alias parser){
            alias None ResultType;
            static ParseResult!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                typeof(return) result;
                result.next = input;
                auto r = parser.parse(input.save, info);
                result.match = r.match;
                result.error = r.error;
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(combinateAndPred!(parseString!"w").parse(makeContext("www"), new CallerInfo(0, "")) == makeParseResult(true, None.init, makeContext("www", 0)));
                assert(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w")).parse(makeContext("www"), new CallerInfo(0, "")) == makeParseResult(true, "w", makeContext("ww", 1)));
                assert(combinateMore1!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w"))).parse(makeContext("www"), new CallerInfo(0, "")) == makeParseResult(true, ["w", "w"], makeContext("w", 2), Error(q{"w"}, 3)));
                assert(combinateMore1!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w"))).parse(makeContext("w"), new CallerInfo(0, "")) == makeParseResult(false, [""][0..0], makeContext(""), Error(q{"w"}, 1)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // combinateNotPred
        template combinateNotPred(alias parser){
            alias None ResultType;
            static ParseResult!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                typeof(return) result;
                result.next = input;
                auto r = parser.parse(input.save, info);
                result.match = !r.match;
                if(result.match){
                    result.error = r.error;
                }else{
                    result.error = Error("Expected failure", input.position, input.line);
                }
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(combinateMore1!(combinateSequence!(parseString!"w", combinateNotPred!(parseString!"s"))).parse(makeContext("wwws"), new CallerInfo(0, "")) == makeParseResult(true, ["w", "w"], makeContext("ws", 2), Error("Expected failure", 3)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // combinateConvert
        template CombinateConvertType(alias converter, T){
            static if(__traits(compiles, new converter(T.init.field))){
                alias converter CombinateConvertType;
            }else static if(__traits(compiles, new converter(T.init))){
                alias converter CombinateConvertType;
            }else static if(__traits(compiles, converter(T.init.field))){
                alias typeof(converter(T.init.field)) CombinateConvertType;
            }else static if(__traits(compiles, converter(T.init))){
                alias typeof(converter(T.init)) CombinateConvertType;
            }else{
                alias void CombinateConvertType;
            }
        }

        unittest{
            static class C1{ this(string){} }
            static class C2{ this(string, int){} }
            static struct S1{ string str;}
            static struct S2{ string str; int i;}
            static int f1(string){ return 0; }
            static int f2(string, int){ return 0; }
            static int t1(T)(T){ static assert(false); }
            static int t2(T, U)(T, U){ static assert(false); }

            static assert(is(CombinateConvertType!(C1, string) == C1));
            static assert(is(CombinateConvertType!(C1, double) == void));
            static assert(is(CombinateConvertType!(C2, Tuple!(string, int)) == C2));
            static assert(is(CombinateConvertType!(C2, Tuple!(string, double)) == void));
            static assert(is(CombinateConvertType!(S1, string) == S1));
            static assert(is(CombinateConvertType!(S1, int) == void));
            static assert(is(CombinateConvertType!(S2, Tuple!(string, int)) == S2));
            static assert(is(CombinateConvertType!(S2, Tuple!(string, double)) == void));
            static assert(is(CombinateConvertType!(f1, string) == int));
            static assert(is(CombinateConvertType!(f1, Tuple!(string, string)) == void));
            static assert(is(CombinateConvertType!(f2, Tuple!(string, int)) == int));
            static assert(is(CombinateConvertType!(f2, Tuple!(string, double)) == void));
            static assert(is(CombinateConvertType!(t1, string) == int));
            static assert(is(CombinateConvertType!(t1, void) == void));
            static assert(is(CombinateConvertType!(t2, Tuple!(string, int)) == int));
            static assert(is(CombinateConvertType!(t2, Tuple!(string, int, int)) == void));
        }

        template combinateConvert(alias parser, alias converter){
            alias combinateConvert!(0, "", parser, converter) combinateConvert;
        }

        template combinateConvert(size_t line, string file, alias parser, alias converter){
            alias CombinateConvertType!(converter, ParserType!parser) ResultType;
            static if(is(ResultType == void)){
                static if(line){
                    mixin("#line " ~ toStringNow!line ~ " \"" ~ file ~ "\"" q{
                        static assert(false, "cannot call " ~ converter.stringof ~ " using `>>` with types: " ~ ParserType!parser.stringof);
                    });
                }else{
                    static assert(false, "cannot call " ~ converter.stringof ~ " using `>>` with type: " ~ ParserType!parser.stringof);
                }
            }
            static ParseResult!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                typeof(return) result;
                auto r = parser.parse(input, info);
                if(r.match){
                    result.match = true;
                    static if(__traits(compiles, converter(r.value.field))){
                        result.value = converter(r.value.field);
                    }else static if(__traits(compiles, new converter(r.value.field))){
                        result.value = new converter(r.value.field);
                    }else static if(__traits(compiles, converter(r.value))){
                        result.value = converter(r.value);
                    }else static if(__traits(compiles, new converter(r.value))){
                        result.value = new converter(r.value);
                    }else{
                        static assert(false);
                    }
                    result.next = r.next;
                }
                result.error = r.error;
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(combinateConvert!(combinateMore1!(parseString!"w"), function(string[] ws){ return ws.length; }).parse(makeContext("www"), new CallerInfo(0, "")) == makeParseResult(true, cast(size_t)3, makeContext("", 3), Error(q{"w"}, 3)));
                assert(combinateConvert!(combinateMore1!(parseString!"w"), function(string[] ws){ return ws.length; }).parse(makeContext("a"), new CallerInfo(0, "")) == makeParseResult(false, cast(size_t)0, makeContext(""), Error(q{"w"})));
                //assert(combinateConvert!(10, "hoge/fuga.d", combinateMore1!(parseString!"w"), function(string ws){ return ws.length; }).parse(makeContext(testRange("a")), new CallerInfo(0, "")) == makeParseResult(false, cast(size_t)0, makeContext(testRange("")), Error(q{"w"})));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // combinateConvertWithState
        template CombinateConvertWithStateType(alias converter, T){
            static if(__traits(compiles, new converter(T.init.field, StateType.init))){
                alias converter CombinateConvertWithStateType;
            }else static if(__traits(compiles, new converter(T.init, StateType.init))){
                alias converter CombinateConvertWithStateType;
            }else static if(__traits(compiles, converter(T.init.field, StateType.init))){
                alias typeof(converter(T.init.field, StateType.init)) CombinateConvertWithStateType;
            }else static if(__traits(compiles, converter(T.init, StateType.init))){
                alias typeof(converter(T.init, StateType.init)) CombinateConvertWithStateType;
            }else{
                alias void CombinateConvertWithStateType;
            }
        }

        unittest{
            static class C1{ this(string, StateType){} }
            static class C2{ this(string, int, StateType){} }
            static struct S1{ string str; StateType state; }
            static struct S2{ string str; int i; StateType state; }
            static int f1(string, StateType){ return 0; }
            static int f2(string, int, StateType){ return 0; }
            static int t1(T)(T, StateType){ static assert(false); }
            static int t2(T, U)(T, U, StateType){ static assert(false); }

            static assert(is(CombinateConvertWithStateType!(C1, string) == C1));
            static assert(is(CombinateConvertWithStateType!(C1, int) == void));
            static assert(is(CombinateConvertWithStateType!(C2, Tuple!(string, int)) == C2));
            static assert(is(CombinateConvertWithStateType!(C2, Tuple!(string, double)) == void));
            static assert(is(CombinateConvertWithStateType!(S1, string) == S1));
            static assert(is(CombinateConvertWithStateType!(S2, Tuple!(string, int)) == S2));
            static assert(is(CombinateConvertWithStateType!(S2, Tuple!(string, double)) == void));
            static assert(is(CombinateConvertWithStateType!(f1, string) == int));
            static assert(is(CombinateConvertWithStateType!(f2, Tuple!(string, int)) == int));
            static assert(is(CombinateConvertWithStateType!(f2, Tuple!(string, double)) == void));
            static assert(is(CombinateConvertWithStateType!(t1, string) == int));
            static assert(is(CombinateConvertWithStateType!(t1, void) == void));
            static assert(is(CombinateConvertWithStateType!(t2, Tuple!(string, int)) == int));
            static assert(is(CombinateConvertWithStateType!(t2, Tuple!(string, int, int)) == void));
        }

        template combinateConvertWithState(alias parser, alias converter){
            alias combinateConvertWithState!(0, "", parser, converter) combinateConvertWithState;
        }

        template combinateConvertWithState(size_t line, string file, alias parser, alias converter){
            alias CombinateConvertWithStateType!(converter, ParserType!parser) ResultType;
            static if(is(ResultType == void)){
                static if(line){
                    mixin("#line " ~ toStringNow!line ~ " \"" ~ file ~ "\"" q{
                        static assert(false, "cannot call " ~ converter.stringof ~ " using `>>>` with types: " ~ ParserType!parser.stringof);
                    });
                }else{
                    static assert(false, "cannot call " ~ converter.stringof ~ " using `>>>` with type: " ~ ParserType!parser.stringof);
                }
            }
            static ParseResult!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                typeof(return) result;
                auto r = parser.parse(input, info);
                if(r.match){
                    result.match = true;
                    static if(__traits(compiles, converter(r.value.field, input.state))){
                        result.value = converter(r.value.field, input.state);
                    }else static if(__traits(compiles, new converter(r.value.field, input.state))){
                        result.value = new converter(r.value.field, input.state);
                    }else static if(__traits(compiles, converter(r.value, input.state))){
                        result.value = converter(r.value, input.state);
                    }else static if(__traits(compiles, new converter(r.value, input.state))){
                        result.value = new converter(r.value, input.state);
                    }else{
                        static assert(false, converter.mangleof ~ " cannot call with argument type " ~ typeof(r.value).stringof);
                    }
                    result.next = r.next;
                }
                result.error = r.error;
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(combinateConvertWithState!(combinateMore1!(parseString!"w"), function(string[] ws, StateType state){ return ws.length; }).parse(makeContext("www"), new CallerInfo(0, "")) == makeParseResult(true, cast(size_t)3, makeContext("", 3), Error(q{"w"}, 3)));
                assert(combinateConvertWithState!(combinateMore1!(parseString!"w"), function(string[] ws, StateType state){ return ws.length; }).parse(makeContext("a"), new CallerInfo(0, "")) == makeParseResult(false, cast(size_t)0, makeContext(""), Error(q{"w"})));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // combinateCheck
        template isValidChecker(alias checker, T){
            static if(is(typeof(checker(T.init.field)) == bool)){
                immutable isValidChecker = true;
            }else static if(is(typeof(checker(T.init)) == bool)){
                immutable isValidChecker = true;
            }else{
                immutable isValidChecker = false;
            }
        }

        unittest{
            static bool f1(string){ return true; }
            static bool f2(string, int){ return true; }
            static string f3(string){ return ""; }
            static bool t1(T)(T){ static assert(false); }
            static bool t2(T, U)(T, U){ static assert(false); }
            static string t3(T)(T){ static assert(false); }

            static assert( isValidChecker!(f1, string));
            static assert(!isValidChecker!(f1, int));
            static assert( isValidChecker!(f2, Tuple!(string, int)));
            static assert(!isValidChecker!(f2, Tuple!(string, string)));
            static assert(!isValidChecker!(f3,  string));
            static assert(!isValidChecker!(f3,  int));
            static assert( isValidChecker!(t1, int));
            static assert( isValidChecker!(t2, Tuple!(string, int)));
            static assert(!isValidChecker!(t2, Tuple!(string, int, int)));
            static assert(!isValidChecker!(t3, int));
        }

        template combinateCheck(alias parser, alias checker){
            alias combinateCheck!(0, "", parser, checker) combinateCheck;
        }

        template combinateCheck(size_t line, string file, alias parser, alias checker){
            alias ParserType!parser ResultType;
            static if(!isValidChecker!(checker, ResultType)){
                static if(line){
                    mixin("#line " ~ toStringNow!line ~ " \"" ~ file ~ "\"" q{
                        static assert(false, "cannot call " ~ checker.stringof ~ " using `>>?` with types: " ~ ParserType!parser.stringof);
                    });
                }else{
                    static assert(false, "cannot call " ~ checker.stringof ~ " using `>>?` with type: " ~ ParserType!parser.stringof);
                }
            }
            static ParseResult!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                typeof(return) result;
                auto r = parser.parse(input, info);
                if(r.match){
                    if(checker(r.value)){
                        result = r;
                    }else{
                        result.error = Error("passing check", input.position, input.line);
                    }
                }else{
                    result.error = r.error;
                }
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(combinateCheck!(combinateMore0!(parseString!"w"), function(string[] ws){ return ws.length == 5; }).parse(makeContext("wwwww"), new CallerInfo(0, "")) == makeParseResult(true, ["w", "w", "w", "w", "w"], makeContext("", 5), Error(q{"w"}, 5)));
                assert(combinateCheck!(combinateMore0!(parseString!"w"), function(string[] ws){ return ws.length == 5; }).parse(makeContext("wwww"), new CallerInfo(0, "")) == makeParseResult(false, [""][0..0], makeContext(""), Error("passing check")));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // combinateChangeState
        template combinateChangeState(alias parser){
            alias None ResultType;
            static ParseResult!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                typeof(return) result;
                auto r = parser.parse(input, info);
                if(r.match){
                    result.match = true;
                    result.next.input = r.next.input;
                    result.next.position = r.next.position;
                    result.next.line = r.next.line;
                    result.next.state = r.value;
                }
                result.error = r.error;
                return result;
            }
        }

        version(none) unittest{
            enum dg = {
                {
                    auto r = combinateChangeState!(parseString!"hoge").parse(makeContext("hoge"), new CallerInfo(0, ""));
                    assert(r.next.input == "");
                    assert(r.next.state == "hoge");
                }
                {
                    auto r = combinateSequence!(combinateChangeState!(parseString!"hoge"), combinateChangeState!(parseString!"piyo")).parse(makeContext("hogepiyo"), new CallerInfo(0, ""));
                    assert(r.next.input == "");
                    assert(r.next.state == "piyo");
                }
                return true;
            };
            dg();
            debug(ctpg_compile_time) static assert(dg());
        }

    // combinateMemoize
        template combinateMemoize(alias parser){
            alias ParserType!parser ResultType;
            ParseResult!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                if(!__ctfe){
                    static typeof(return)[typeof(input)] memo;
                    auto p = input in memo;
                    if(p){
                        return *p;
                    }
                    auto result = parser.parse(input, info);
                    memo[input] = result;
                    return result;
                }else{
                    return parser.parse(input, info);
                }
            }
        }

        unittest{
            alias combinateMemoize!(combinateConvert!(parseString!"str", (str){ "This message should be showed twice.".writeln(); return 0; })) p;
            combinateSequence!(combinateAndPred!p, p).parse(makeContext("str"), new CallerInfo(0, ""));
            combinateSequence!(combinateAndPred!p, p).parse(makeContext("str".testRange()), new CallerInfo(0, ""));
        }

// useful parser
    // parseAnyChar
        template parseAnyChar(){
            alias parseCharRange!(dchar.min, dchar.max) parseAnyChar;
        }

        alias parseAnyChar any;

        unittest{
            enum dg = {
                assert(parseAnyChar!().parse(makeContext("hoge"), new CallerInfo(0, "")) == makeParseResult(true, "h", makeContext("oge", 1)));
                assert(parseAnyChar!().parse(makeContext("\U00012345"), new CallerInfo(0, "")) == makeParseResult(true, "\U00012345", makeContext("", 4)));
                assert(parseAnyChar!().parse(makeContext("\nhoge"), new CallerInfo(0, "")) == makeParseResult(true, "\n", makeContext("hoge", 1, 2)));
                assert(parseAnyChar!().parse(makeContext(""), new CallerInfo(0, "")) == makeParseResult(false, "", makeContext(""), Error("any char")));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // parseSpaces
        template parseSpaces(){
            alias combinateNone!(combinateMore0!(parseSpace!())) parseSpaces;
        }

        alias parseSpaces ss;
        alias parseSpaces defaultSkip;

        unittest{
            static assert(is(parseSpaces!().ResultType));
            enum dg = {
                assert(parseSpaces!().parse(makeContext("\t \rhoge"), new CallerInfo(0, "")) == makeParseResult(true, None.init, makeContext("hoge", 3)));
                assert(parseSpaces!().parse(makeContext("hoge"), new CallerInfo(0, "")) == makeParseResult(true, None.init, makeContext("hoge", 0)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // parseIdent
        template parseIdent(){
            alias combinateConvert!(
                combinateSequence!(
                    combinateChoice!(
                        parseString!"_",
                        parseCharRange!('a','z'),
                        parseCharRange!('A','Z')
                    ),
                    combinateMore0!(parseIdentChar!())
                ),
                flat
            ) parseIdent;
        }

        alias parseIdent ident_p;

        private template parseIdentChar(){
            alias combinateChoice!(
                parseString!"_",
                parseCharRange!('a','z'),
                parseCharRange!('A','Z'),
                parseCharRange!('0','9')
            ) parseIdentChar;
        }

        unittest{
            enum dg = {
                assert(parseIdent!().parse(makeContext("hoge"), new CallerInfo(0, "")) == makeParseResult(true, "hoge", makeContext("", 4)));
                assert(parseIdent!().parse(makeContext("_0"), new CallerInfo(0, "")) == makeParseResult(true, "_0", makeContext("", 2)));
                assert(parseIdent!().parse(makeContext("0"), new CallerInfo(0, "")) == makeParseResult(false, "", makeContext(""), Error("c: 'A' <= c <= 'Z'")));
                assert(parseIdent!().parse(makeContext("あ"), new CallerInfo(0, "")) == makeParseResult(false, "", makeContext(""), Error("c: 'A' <= c <= 'Z'")));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // parseStringLiteral
        template parseStringLiteral(){
            alias combinateChoice!(
                combinateConvert!(
                    combinateSequence!(
                        parseString!"\"",
                        combinateMore0!(
                            combinateSequence!(
                                combinateNotPred!(parseString!"\""),
                                combinateChoice!(
                                    parseEscapeSequence!(),
                                    parseAnyChar!()
                                )
                            )
                        ),
                        parseString!"\""
                    ),
                    flat
                ),
                combinateConvert!(
                    combinateSequence!(
                        parseString!"r\"",
                        combinateMore0!(
                            combinateSequence!(
                                combinateNotPred!(parseString!"\""),
                                parseAnyChar!()
                            )
                        ),
                        parseString!"\""
                    ),
                    flat
                ),
                combinateConvert!(
                    combinateSequence!(
                        parseString!"`",
                        combinateMore0!(
                            combinateSequence!(
                                combinateNotPred!(parseString!"`"),
                                parseAnyChar!()
                            )
                        ),
                        parseString!"`"
                    ),
                    flat
                )
            ) parseStringLiteral;
        }

        alias parseStringLiteral strLit_p;

        unittest{
            enum dg = {
                assert(parseStringLiteral!().parse(makeContext("\"表が怖い噂のソフト\""), new CallerInfo(0, "")) == makeParseResult(true, "\"表が怖い噂のソフト\"", makeContext("", 29), Error("Expected failure", 28)));
                assert(parseStringLiteral!().parse(makeContext(`r"表が怖い噂のソフト"`), new CallerInfo(0, "")) == makeParseResult(true, `r"表が怖い噂のソフト"`, makeContext("", 30), Error("Expected failure", 29)));
                assert(parseStringLiteral!().parse(makeContext("`表が怖い噂のソフト`"), new CallerInfo(0, "")) == makeParseResult(true, q{`表が怖い噂のソフト`}, makeContext("", 29), Error("Expected failure", 28)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // parseIntLiteral
        template parseIntLiteral(){
            alias combinateChoice!(
                combinateConvert!(
                    combinateNone!(parseString!"0"),
                    function() => 0
                ),
                combinateConvert!(
                    combinateSequence!(
                        parseCharRange!('1', '9'),
                        combinateMore0!(parseCharRange!('0', '9'))
                    ),
                    function(string head, string[] tails){
                        int result = head[0] - '0';
                        foreach(c; tails){
                            result = result * 10 + c[0] - '0';
                        }
                        return result;
                    }
                )
            ) parseIntLiteral;
        }

        alias parseIntLiteral intLit_p;

        unittest{
            enum dg = {
                assert(parseIntLiteral!().parse(makeContext("3141"), new CallerInfo(0, "")) == makeParseResult(true, 3141, makeContext("", 4)));
                assert(parseIntLiteral!().parse(makeContext("0"), new CallerInfo(0, "")) == makeParseResult(true, 0, makeContext("", 1)));
                assert(parseIntLiteral!().parse(makeContext("0123"), new CallerInfo(0, "")) == makeParseResult(true, 0, makeContext("123", 1)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

// getters
    // getLine
        template getLine(){
            alias size_t ResultType;
            static ParseResult!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                static if(isSomeString!R || isCharRange!R){
                    return makeParseResult(true, input.line, input, Error.init);
                }else{
                    throw new Exception("");
                }
            }
        }

        unittest{
            enum dg = {
                assert(combinateSequence!(parseSpaces!(), getLine!()).parse(makeContext("\n\n"             ), new CallerInfo(0, "")) == makeParseResult(true, cast(size_t)3, makeContext(""             , 2, 3)));
                assert(combinateSequence!(parseSpaces!(), getLine!()).parse(makeContext("\n\n"w            ), new CallerInfo(0, "")) == makeParseResult(true, cast(size_t)3, makeContext(""w            , 2, 3)));
                assert(combinateSequence!(parseSpaces!(), getLine!()).parse(makeContext("\n\n"d            ), new CallerInfo(0, "")) == makeParseResult(true, cast(size_t)3, makeContext(""d            , 2, 3)));
                assert(combinateSequence!(parseSpaces!(), getLine!()).parse(makeContext("\n\n" .testRange()), new CallerInfo(0, "")) == makeParseResult(true, cast(size_t)3, makeContext("" .testRange(), 2, 3)));
                assert(combinateSequence!(parseSpaces!(), getLine!()).parse(makeContext("\n\n"w.testRange()), new CallerInfo(0, "")) == makeParseResult(true, cast(size_t)3, makeContext(""w.testRange(), 2, 3)));
                assert(combinateSequence!(parseSpaces!(), getLine!()).parse(makeContext("\n\n"d.testRange()), new CallerInfo(0, "")) == makeParseResult(true, cast(size_t)3, makeContext(""d.testRange(), 2, 3)));

                try{
                    scope(failure) assert(true);
                    auto result = combinateSequence!(parseSpaces!(), getLine!()).parse(makeContext([0, 0]), new CallerInfo(0, ""));
                }catch(Exception ex){}
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // getCallerLine
        template getCallerLine(){
            alias size_t ResultType;
            static ParseResult!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                return makeParseResult(true, info.line, input, Error.init);
            }
        }

        unittest{
            enum dg = {
                assert(getCallerLine!().parse(makeContext(""             ), new CallerInfo(__LINE__, "")) == makeParseResult(true, cast(size_t)__LINE__, makeContext(""             , 0)));
                assert(getCallerLine!().parse(makeContext(""w            ), new CallerInfo(__LINE__, "")) == makeParseResult(true, cast(size_t)__LINE__, makeContext(""w            , 0)));
                assert(getCallerLine!().parse(makeContext(""d            ), new CallerInfo(__LINE__, "")) == makeParseResult(true, cast(size_t)__LINE__, makeContext(""d            , 0)));
                assert(getCallerLine!().parse(makeContext("" .testRange()), new CallerInfo(__LINE__, "")) == makeParseResult(true, cast(size_t)__LINE__, makeContext("" .testRange(), 0)));
                assert(getCallerLine!().parse(makeContext(""w.testRange()), new CallerInfo(__LINE__, "")) == makeParseResult(true, cast(size_t)__LINE__, makeContext(""w.testRange(), 0)));
                assert(getCallerLine!().parse(makeContext(""d.testRange()), new CallerInfo(__LINE__, "")) == makeParseResult(true, cast(size_t)__LINE__, makeContext(""d.testRange(), 0)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // getCallerFile
        template getCallerFile(){
            alias string ResultType;
            static ParseResult!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                return makeParseResult(true, info.file, input, Error.init);
            }
        }

        unittest{
            enum dg = {
                assert(getCallerFile!().parse(makeContext(""             ), new CallerInfo(0, __FILE__)) == makeParseResult(true, __FILE__, makeContext(""             , 0)));
                assert(getCallerFile!().parse(makeContext(""w            ), new CallerInfo(0, __FILE__)) == makeParseResult(true, __FILE__, makeContext(""w            , 0)));
                assert(getCallerFile!().parse(makeContext(""d            ), new CallerInfo(0, __FILE__)) == makeParseResult(true, __FILE__, makeContext(""d            , 0)));
                assert(getCallerFile!().parse(makeContext("" .testRange()), new CallerInfo(0, __FILE__)) == makeParseResult(true, __FILE__, makeContext("" .testRange(), 0)));
                assert(getCallerFile!().parse(makeContext(""w.testRange()), new CallerInfo(0, __FILE__)) == makeParseResult(true, __FILE__, makeContext(""w.testRange(), 0)));
                assert(getCallerFile!().parse(makeContext(""d.testRange()), new CallerInfo(0, __FILE__)) == makeParseResult(true, __FILE__, makeContext(""d.testRange(), 0)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

string generateParsers(size_t callerLine = __LINE__, string callerFile = __FILE__)(string src){
    auto parsed = src.parse!(defs, callerLine, callerFile)();
    if(parsed.match){
        return parsed.value;
    }else{
        return "#line " ~ (parsed.error.line + callerLine - 1).to!string() ~ "\nstatic assert(false, `" ~ parsed.error.need ~ " is needed`);";
    }
}

auto parse(alias fun, size_t callerLine = __LINE__, string callerFile = __FILE__, Range)(Range input, StateType state = StateType.init){
    return fun!().parse(Context!Range(input, 0, 1, state), new CallerInfo(callerLine, callerFile));
}

// parsers of DSL
    // arch
        template arch(string open, string close){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Context!string input, in CallerInfo info){
                return combinateConvert!(
                    combinateSequence!(
                        parseString!open,
                        combinateMore0!(
                            combinateChoice!(
                                arch!(open, close),
                                combinateSequence!(
                                    combinateNotPred!(
                                        parseString!close
                                    ),
                                    combinateChoice!(
                                        parseAnyChar!(),
                                        parseStringLiteral!()
                                    )
                                )
                            )
                        ),
                        parseString!close
                    ),
                    flat
                ).parse(input, info);
            }
        }

        unittest{
            enum dg = {
                assert(arch!("(", ")").parse(makeContext("(a(i(u)e)o())"), new CallerInfo(0, "")) == makeParseResult(true, "(a(i(u)e)o())", makeContext("", 13), Error("Expected failure", 12)));
                assert(arch!("[", "]").parse(makeContext("[a[i[u]e]o[]]"), new CallerInfo(0, "")) == makeParseResult(true, "[a[i[u]e]o[]]", makeContext("", 13), Error("Expected failure", 12)));
                assert(arch!("{", "}").parse(makeContext("{a{i{u}e}o{}}"), new CallerInfo(0, "")) == makeParseResult(true, "{a{i{u}e}o{}}", makeContext("", 13), Error("Expected failure", 12)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // func
        template func(){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Context!string input, in CallerInfo info){
                return combinateConvert!(
                    combinateSequence!(
                        combinateOption!(
                            combinateSequence!(
                                arch!("(", ")"),
                                parseSpaces!()
                            )
                        ),
                        arch!("{", "}")
                    ),
                    function(Option!string arch, string brace) => arch.some ? "function" ~ arch ~ brace : "function()" ~ brace
                ).parse(input, info);
            }
        }

        unittest{
            enum dg = {
                assert(func!().parse(makeContext(
                    "(int num, string code){"
                        "string res;"
                        "foreach(staticNum; 0..num){"
                            "foreach(c;code){"
                                "if(c == '@'){"
                                    "res ~= to!string(staticNum);"
                                "}else{"
                                    "res ~= c;"
                                "}"
                            "}"
                        "}"
                        "return res;"
                    "}"),
                    new CallerInfo(0, "")) == makeParseResult(true,
                    "function(int num, string code){"
                        "string res;"
                        "foreach(staticNum; 0..num){"
                            "foreach(c;code){"
                                "if(c == '@'){"
                                    "res ~= to!string(staticNum);"
                                "}else{"
                                    "res ~= c;"
                                "}"
                            "}"
                        "}"
                        "return res;"
                    "}", makeContext("", 148))
                );
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // id
        template id(){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Context!string input, in CallerInfo info){
                return combinateConvert!(
                    combinateSequence!(
                        combinateChoice!(
                            parseCharRange!('A','Z'),
                            parseCharRange!('a','z'),
                            parseString!"_"
                        ),
                        combinateMore0!(
                            combinateChoice!(
                                parseCharRange!('0','9'),
                                parseCharRange!('A','Z'),
                                parseCharRange!('a','z'),
                                parseString!"_"
                            )
                        )
                    ),
                    flat
                ).parse(input, info);
            }
        }

        unittest{
            enum dg = {
                assert(id!().parse(makeContext("A"), new CallerInfo(0, "")) == makeParseResult(true, "A", makeContext("", 1)));
                assert(id!().parse(makeContext("int"), new CallerInfo(0, "")) == makeParseResult(true, "int", makeContext("", 3)));
                assert(id!().parse(makeContext("0"), new CallerInfo(0, "")) == makeParseResult(false, "", makeContext(""), Error(q{"_"}, 0)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // nonterminal
        template nonterminal(){
            alias string ResultType;
            version(Issue_8038_Fixed){
                ParseResult!(string, ResultType) parse()(Context!string input, in CallerInfo info){
                    return combinateConvertWithState!(
                        combinateSequence!(
                            getCallerLine!(),
                            getLine!(),
                            id!()
                        ),
                        function(size_t callerLine, size_t line, string id, StateType state)
                        =>
                        state[1].length ? " #line " ~ (callerLine + line - 1).to!string() ~ "\ncombinateSkip!(combinateMemoize!(" ~ id ~ "!())," ~ state[1] ~ ")" : " #line " ~ (callerLine + line - 1).to!string() ~ "\ncombinateMemoize!(" ~ id ~ "!())"
                    ).parse(input, info);
                }
            }else{
                ParseResult!(string, ResultType) parse()(Context!string input, in CallerInfo info){
                    return combinateConvert!(
                        combinateSequence!(
                            getCallerLine!(),
                            getLine!(),
                            id!()
                        ),
                        function(size_t callerLine, size_t line, string id) => id ~ "!()"
                    ).parse(input, info);
                }
            }
        }

        unittest{
            enum dg = {
                assert(nonterminal!().parse(makeContext("A"), new CallerInfo(__LINE__, "")) == makeParseResult(true, " #line " ~ toStringNow!__LINE__ ~ "\ncombinateMemoize!(A!())", makeContext("", 1)));
                assert(nonterminal!().parse(makeContext("int"), new CallerInfo(__LINE__, "")) == makeParseResult(true, " #line " ~ toStringNow!__LINE__ ~ "\ncombinateMemoize!(int!())", makeContext("", 3)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // typeName
        template typeName(){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Context!string input, in CallerInfo info){
                return combinateConvert!(
                    combinateSequence!(
                        combinateChoice!(
                            parseCharRange!('A','Z'),
                            parseCharRange!('a','z'),
                            parseString!"_"
                        ),
                        parseSpaces!(),
                        combinateMore0!(
                            combinateChoice!(
                                parseCharRange!('0','9'),
                                parseCharRange!('A','Z'),
                                parseCharRange!('a','z'),
                                parseString!"_",
                                parseString!",",
                                parseString!"!",
                                arch!("(", ")"),
                                arch!("[", "]")
                            )
                        )
                    ),
                    flat
                ).parse(input, info);
            }
        }

        unittest{
            enum dg = {
                assert(typeName!().parse(makeContext("int"), new CallerInfo(0, "")) == makeParseResult(true, "int", makeContext("", 3)));
                assert(typeName!().parse(makeContext("Tuple!(string, int)"), new CallerInfo(0, "")) == makeParseResult(true, "Tuple!(string, int)", makeContext("", 19)));
                assert(typeName!().parse(makeContext("int[]"), new CallerInfo(0, "")) == makeParseResult(true, "int[]", makeContext("", 5)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // eofLit
        template eofLit(){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Context!string input, in CallerInfo info){
                return combinateConvert!(
                    combinateNone!(
                        parseString!"$"
                    ),
                    function() => "parseEOF!()"
                ).parse(input, info);
            }
        }

        unittest{
            enum dg = {
                assert(eofLit!().parse(makeContext("$"), new CallerInfo(0, "")) == makeParseResult(true, "parseEOF!()", makeContext("", 1)));
                assert(eofLit!().parse(makeContext("#"), new CallerInfo(0, "")) == makeParseResult(false, "", makeContext(""), Error(q{"$"}, 0)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // rangeLit
        template rangeLit(){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Context!string input, in CallerInfo info){
                return combinateConvert!(
                    combinateSequence!(
                        combinateNone!(
                            parseString!"["
                        ),
                        combinateMore1!(
                            combinateSequence!(
                                combinateNotPred!(
                                    parseString!"]"
                                ),
                                combinateChoice!(
                                    charRange!(),
                                    oneChar!()
                                )
                            )
                        ),
                        combinateNone!(
                            parseString!"]"
                        )
                    ),
                    function(string[] strs) => strs.length == 1 ? strs[0] : "combinateChoice!("~strs.join(",")~")"
                ).parse(input, info);
            }
        }

        template charRange(){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Context!string input, in CallerInfo info){
                return combinateConvert!(
                    combinateSequence!(
                        combinateChoice!(
                            parseEscapeSequence!(),
                            parseAnyChar!()
                        ),
                        combinateNone!(
                            parseString!"-"
                        ),
                        combinateChoice!(
                            parseEscapeSequence!(),
                            parseAnyChar!()
                        ),
                    ),
                    function(string low, string high) => "parseCharRange!('" ~ low ~ "','" ~ high ~ "')"
                ).parse(input, info);
            }
        }

        template oneChar(){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Context!string input, in CallerInfo info){
                return combinateConvert!(
                    combinateChoice!(
                        parseEscapeSequence!(),
                        parseAnyChar!()
                    ),
                    function(string c) => "parseString!\"" ~ c ~ "\""
                ).parse(input, info);
            }
        }

        unittest{
            enum dg = {
                assert(rangeLit!().parse(makeContext("[a-z]"), new CallerInfo(0, "")) == makeParseResult(true, "parseCharRange!('a','z')", makeContext("", 5), Error("Expected failure", 4)));
                assert(rangeLit!().parse(makeContext("[a-zA-Z_]"), new CallerInfo(0, "")) == makeParseResult(true, "combinateChoice!(parseCharRange!('a','z'),parseCharRange!('A','Z'),parseString!\"_\"" ")", makeContext("", 9), Error("Expected failure", 8)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // stringLit
        template stringLit(){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Context!string input, in CallerInfo info){
                return combinateConvert!(
                    combinateSequence!(
                        combinateNone!(
                            parseString!"\""
                        ),
                        combinateMore0!(
                            combinateSequence!(
                                combinateNotPred!(
                                    parseString!"\""
                                ),
                                combinateChoice!(
                                    parseEscapeSequence!(),
                                    parseAnyChar!()
                                )
                            )
                        ),
                        combinateNone!(
                            parseString!"\""
                        )
                    ),
                    function(string[] strs) => "parseString!\"" ~ strs.flat() ~ "\""
                ).parse(input, info);
            }
        }

        unittest{
            enum dg = {
                assert(stringLit!().parse(makeContext("\"hello\nworld\" "), new CallerInfo(0, "")) == makeParseResult(true, "parseString!\"hello\nworld\"", makeContext(" ", 13, 2), Error("Expected failure", 12, 2)));
                assert(stringLit!().parse(makeContext("aa\""), new CallerInfo(0, "")) == makeParseResult(false, "", makeContext(""), Error(`"""`, 0)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // literal
        template literal(){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Context!string input, in CallerInfo info){
                return combinateConvertWithState!(
                    combinateChoice!(
                        rangeLit!(),
                        stringLit!(),
                        eofLit!()
                    ),
                    function(string literal, StateType state)
                    =>
                    state[1].length ? "combinateSkip!(combinateMemoize!(" ~ literal ~ ")," ~ state[1] ~ ")" : "combinateMemoize!(" ~ literal ~ ")"
                ).parse(input, info);
            }
        }

        unittest{
            enum dg = {
                assert(literal!().parse(makeContext("\"hello\nworld\""), new CallerInfo(0, "")) == makeParseResult(true, "combinateMemoize!(parseString!\"hello\nworld\")", makeContext("", 13, 2), Error("Expected failure", 12, 2)));
                assert(literal!().parse(makeContext("[a-z]"), new CallerInfo(0, "")) == makeParseResult(true, "combinateMemoize!(parseCharRange!('a','z'))", makeContext("", 5), Error("Expected failure", 4)));
                assert(literal!().parse(makeContext("$"), new CallerInfo(0, "")) == makeParseResult(true, "combinateMemoize!(parseEOF!())", makeContext("", 1)));
                assert(literal!().parse(makeContext("$", 0, 1, tuple("", "skip!()")), new CallerInfo(0, "")) == makeParseResult(true, "combinateSkip!(combinateMemoize!(parseEOF!()),skip!())", makeContext("", 1, 1, tuple("", "skip!()"))));
                assert(literal!().parse(makeContext("表が怖い噂のソフト"), new CallerInfo(0, "")) == makeParseResult(false, "", makeContext(""), Error(`"$"`, 0)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // primaryExp
        template primaryExp(){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Context!string input, in CallerInfo info){
                return combinateChoice!(
                    literal!(),
                    nonterminal!(),
                    combinateSequence!(
                        combinateNone!(
                            parseString!"("
                        ),
                        parseSpaces!(),
                        choiceExp!(),
                        parseSpaces!(),
                        combinateNone!(
                            parseString!")"
                        )
                    )
                ).parse(input, info);
            }
        }

        unittest{
            enum dg = {
                assert(primaryExp!().parse(makeContext("(&(^$)?)"), new CallerInfo(0, "")) == makeParseResult(true, "combinateOption!(combinateAndPred!(combinateNotPred!(combinateMemoize!(parseEOF!()))))", makeContext("", 8), Error(q{"("}, 7)));
                assert(primaryExp!().parse(makeContext("int"), new CallerInfo(__LINE__, "")) == makeParseResult(true, " #line " ~ toStringNow!__LINE__ ~ "\ncombinateMemoize!(int!())", makeContext("", 3)));
                assert(primaryExp!().parse(makeContext("###このコメントは表示されません###"), new CallerInfo(0, "")) == makeParseResult(false, "", makeContext(""), Error(`"("`, 0)));
                assert(primaryExp!().parse(makeContext("(&(^$)?"), new CallerInfo(0, "")) == makeParseResult(false, "", makeContext(""), Error(`")"`, 7)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // preExp
        template preExp(){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Context!string input, in CallerInfo info){
                return combinateConvert!(
                    combinateSequence!(
                        combinateOption!(
                            combinateChoice!(
                                parseString!"&",
                                parseString!"^",
                                parseString!"!!",
                                parseString!"!"
                            )
                        ),
                        primaryExp!()
                    ),
                    function(Option!string op, string primaryExp){
                        final switch(op.value){
                            case "&":
                                return "combinateAndPred!(" ~ primaryExp ~ ")";
                            case "^":
                                return "combinateNotPred!(" ~ primaryExp ~ ")";
                            case "!!":
                                return "combinateChangeState!(" ~ primaryExp ~ ")";
                            case "!":
                                return "combinateNone!(" ~ primaryExp ~ ")";
                            case "":
                                return primaryExp;
                        }
                    }
                ).parse(input, info);
            }
        }

        unittest{
            enum dg = {
                assert(preExp!().parse(makeContext("!$"), new CallerInfo(0, "")) == makeParseResult(true, "combinateNone!(combinateMemoize!(parseEOF!()))", makeContext("", 2)));
                assert(preExp!().parse(makeContext("!!$"), new CallerInfo(0, "")) == makeParseResult(true, "combinateChangeState!(combinateMemoize!(parseEOF!()))", makeContext("", 3)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // postExp
        template postExp(){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Context!string input, in CallerInfo info){
                return combinateConvert!(
                    combinateSequence!(
                        preExp!(),
                        combinateOption!(
                            combinateSequence!(
                                combinateChoice!(
                                    parseString!"+",
                                    parseString!"*"
                                ),
                                combinateOption!(
                                    combinateSequence!(
                                        combinateNone!(
                                            parseString!"<"
                                        ),
                                        choiceExp!(),
                                        combinateNone!(
                                            parseString!">"
                                        )
                                    )
                                )
                            )
                        )
                    ),
                    function(string preExp, Option!(Tuple!(string, Option!string)) op){
                        final switch(op.value[0]){
                            case "+":{
                                if(op.value[1].some){
                                    return "combinateMore1!(" ~ preExp ~ "," ~ op.value[1].value ~ ")";
                                }else{
                                    return "combinateMore1!(" ~ preExp ~ ")";
                                }
                            }
                            case "*":{
                                if(op.value[1].some){
                                    return "combinateMore0!(" ~ preExp ~ "," ~ op.value[1].value ~ ")";
                                }else{
                                    return "combinateMore0!(" ~ preExp ~ ")";
                                }
                            }
                            case "":{
                                return preExp;
                            }
                        }
                    }
                ).parse(input, info);
            }
        }

        unittest{
            enum dg = {
                assert(postExp!().parse(makeContext("!$*"), new CallerInfo(0, "")) == makeParseResult(true, "combinateMore0!(combinateNone!(combinateMemoize!(parseEOF!())))", makeContext("", 3)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // optionExp
        template optionExp(){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Context!string input, in CallerInfo info){
                return combinateConvert!(
                    combinateSequence!(
                        postExp!(),
                        parseSpaces!(),
                        combinateOption!(
                            combinateNone!(
                                parseString!"?"
                            )
                        )
                    ),
                    function(string convExp, Option!None op) => op.some ? "combinateOption!("~convExp~")" : convExp
                ).parse(input, info);
            }
        }

        unittest{
            enum dg = {
                assert(optionExp!().parse(makeContext("(&(^\"hello\"))?"), new CallerInfo(0, "")) == makeParseResult(true, "combinateOption!(combinateAndPred!(combinateNotPred!(combinateMemoize!(parseString!\"hello\"))))", makeContext("", 14)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // seqExp
        template seqExp(){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Context!string input, in CallerInfo info){
                return combinateConvert!(
                    combinateMore1!(
                        optionExp!(),
                        parseSpaces!()
                    ),
                    function(string[] optionExps) => optionExps.length > 1 ? "combinateSequence!("~optionExps.join(",")~")" : optionExps[0]
                ).parse(input, info);
            }
        }

        unittest{
            enum dg = {
                assert(seqExp!().parse(makeContext("!$* (&(^$))?"), new CallerInfo(0, "")) == makeParseResult(true, "combinateSequence!(combinateMore0!(combinateNone!(combinateMemoize!(parseEOF!()))),combinateOption!(combinateAndPred!(combinateNotPred!(combinateMemoize!(parseEOF!())))))", makeContext("", 12), Error(q{"("}, 12)));
                assert(seqExp!().parse(makeContext("!\"hello\" $"), new CallerInfo(0, "")) == makeParseResult(true, "combinateSequence!(combinateNone!(combinateMemoize!(parseString!\"hello\")),combinateMemoize!(parseEOF!()))", makeContext("", 10), Error(q{"("}, 10)));
                assert(seqExp!().parse(makeContext("!$* (&(^$)?"), new CallerInfo(0, "")) == makeParseResult(true, "combinateMore0!(combinateNone!(combinateMemoize!(parseEOF!())))", makeContext("(&(^$)?", 4), Error(q{")"}, 11)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // convExp
        template convExp(){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Context!string input, in CallerInfo info){
                return combinateConvert!(
                    combinateSequence!(
                        getCallerLine!(),
                        getCallerFile!(),
                        seqExp!(),
                        combinateMore0!(
                            combinateSequence!(
                                parseSpaces!(),
                                combinateChoice!(
                                    parseString!">>>",
                                    parseString!">>?",
                                    parseString!">>"
                                ),
                                getLine!(),
                                parseSpaces!(),
                                combinateChoice!(
                                    func!(),
                                    typeName!()
                                )
                            )
                        )
                    ),
                    function(size_t callerLine, string callerFile, string seqExp, Tuple!(string, size_t, string)[] funcs){
                        string result = seqExp;
                        foreach(func; funcs){
                            final switch(func[0]){
                                case ">>":
                                    result = "combinateConvert!(" ~ (callerLine + func[1] - 1).to!string() ~ ",`" ~ callerFile ~ "`," ~ result ~ "," ~ func[2] ~ ")";
                                    break;
                                case ">>>":
                                    result = "combinateConvertWithState!(" ~ (callerLine + func[1] - 1).to!string() ~ ",`" ~ callerFile ~ "`," ~ result ~ "," ~ func[2] ~ ")";
                                    break;
                                case ">>?":
                                    result = "combinateCheck!(" ~ (callerLine + func[1] - 1).to!string() ~ ",`" ~ callerFile ~ "`," ~ result ~ "," ~ func[2] ~ ")";
                                    break;
                            }
                        }
                        return result;
                    }
                ).parse(input, info);
            }
        }

        unittest{
            enum dg = {
                assert(convExp!().parse(makeContext(q{!"hello" $ >> {return false;}}), new CallerInfo(__LINE__, `src\ctpg.d`)) == makeParseResult(true, "combinateConvert!(" ~ toStringNow!__LINE__ ~ ",`src\\ctpg.d`,combinateSequence!(combinateNone!(combinateMemoize!(parseString!\"hello\")),combinateMemoize!(parseEOF!())),function(){return false;})", makeContext("", 29), Error(q{"("}, 11)));
                assert(convExp!().parse(makeContext(q{"hello" >> flat >> to!int}), new CallerInfo(__LINE__, `src/ctpg.d`)) == makeParseResult(true, "combinateConvert!(" ~ toStringNow!__LINE__ ~ ",`src/ctpg.d`,combinateConvert!(" ~ toStringNow!__LINE__ ~ ",`src/ctpg.d`,combinateMemoize!(parseString!\"hello\"),flat),to!int)", makeContext("", 25), Error(q{"("}, 8)));
                assert(convExp!().parse(makeContext(q{$ >>> to!string >>? isValid}, 0, 1, tuple("", "skip!()")), new CallerInfo(__LINE__, `src\ctpg.d`)) == makeParseResult(true, "combinateCheck!(" ~ toStringNow!__LINE__ ~ r",`src\ctpg.d`,combinateConvertWithState!(" ~ toStringNow!__LINE__ ~ r",`src\ctpg.d`,combinateSkip!(combinateMemoize!(parseEOF!()),skip!()),to!string),isValid)", makeContext("", 27, 1, tuple("", "skip!()")), Error(q{"("}, 2)));
                assert(convExp!().parse(makeContext(q{!"hello" $ > {return false;}}), new CallerInfo(0, "")) == makeParseResult(true, "combinateSequence!(combinateNone!(combinateMemoize!(parseString!\"hello\")),combinateMemoize!(parseEOF!()))", makeContext("> {return false;}", 11), Error(q{"("}, 11)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // choiceExp
        template choiceExp(){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Context!string input, in CallerInfo info){
                return combinateConvert!(
                    combinateSequence!(
                        getLine!(),
                        getCallerLine!(),
                        getCallerFile!(),
                        convExp!(),
                        combinateMore0!(
                            combinateSequence!(
                                parseSpaces!(),
                                combinateNone!(
                                    parseString!"/"
                                ),
                                parseSpaces!(),
                                convExp!()
                            )
                        )
                    ),
                    function(size_t line, size_t callerLine, string callerFile, string convExp, string[] convExps) => convExps.length ? "combinateChoice!(" ~ (callerLine + line - 1).to!string() ~ ",`" ~ callerFile ~ "`," ~ convExp ~ "," ~ convExps.join(",") ~ ")" : convExp
                ).parse(input, info);
            }
        }

        unittest{
            enum dg = {
                assert(choiceExp!().parse(makeContext(`!$* / (&(^"a"))?`), new CallerInfo(__LINE__, `src\ctpg.d`)) == makeParseResult(true, "combinateChoice!(" ~ toStringNow!__LINE__ ~ ",`src\\ctpg.d`,combinateMore0!(combinateNone!(combinateMemoize!(parseEOF!()))),combinateOption!(combinateAndPred!(combinateNotPred!(combinateMemoize!(parseString!\"a\")))))", makeContext("", 16), Error(q{"("}, 4)));
                assert(choiceExp!().parse(makeContext(`!"hello" $`, 0, 1, tuple("", "skip!()")), new CallerInfo(0, "")) == makeParseResult(true, "combinateSequence!(combinateNone!(combinateSkip!(combinateMemoize!(parseString!\"hello\"),skip!())),combinateSkip!(combinateMemoize!(parseEOF!()),skip!()))", makeContext("", 10, 1, tuple("", "skip!()")), Error(q{"("}, 10)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // def
        template def(){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Context!string input, in CallerInfo info){
                return combinateConvert!(
                    combinateSequence!(
                        combinateChangeState!(
                            combinateConvertWithState!(
                                combinateOption!(
                                    combinateSequence!(
                                        combinateNone!(parseString!"@skip("),
                                        combinateChangeState!(
                                            combinateConvertWithState!(
                                                success!(),
                                                function(StateType state) => tuple(state[0], "")
                                            )
                                        ),
                                        choiceExp!(),
                                        combinateNone!(parseString!")")
                                    )
                                ),
                                function(Option!string skip, StateType state)
                                =>
                                skip.some ? tuple(state[0], skip.value) : tuple(state[0], state[0])
                            )
                        ),
                        parseSpaces!(),
                        typeName!(),
                        parseSpaces!(),
                        id!(),
                        parseSpaces!(),
                        combinateNone!(
                            parseString!"="
                        ),
                        parseSpaces!(),
                        choiceExp!(),
                        parseSpaces!(),
                        combinateNone!(
                            parseString!";"
                        )
                    ),
                    function(string type, string name, string choiceExp)
                    =>
                        "template " ~ name ~ "(){"
                            "alias " ~ type ~ " ResultType;"
                            "static ParseResult!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){"
                                "return "~choiceExp~".parse(input, info);"
                            "}"
                        "}"
                ).parse(input, info);
            }
        }

        unittest{
            enum dg = {
                cast(void)__LINE__;
                assert(def!().parse(makeContext(`@skip(" ") bool hoge = !"hello" $ >> {return false;};`), new CallerInfo(__LINE__, `src/ctpg.d`)) == makeParseResult(true, "template hoge(){alias bool ResultType;static ParseResult!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){return combinateConvert!(" ~ toStringNow!__LINE__ ~ ",`src/ctpg.d`,combinateSequence!(combinateNone!(combinateSkip!(combinateMemoize!(parseString!\"hello\"),combinateMemoize!(parseString!\" \"))),combinateSkip!(combinateMemoize!(parseEOF!()),combinateMemoize!(parseString!\" \"))),function(){return false;}).parse(input, info);}}", makeContext("", 53, 1, tuple("", "combinateMemoize!(parseString!\" \")")), Error(q{"("}, 34)));
                assert(def!().parse(makeContext(`None recursive = A $;`), new CallerInfo(__LINE__, "")) == makeParseResult(true, "template recursive(){alias None ResultType;static ParseResult!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){return combinateSequence!( #line " ~ toStringNow!__LINE__ ~ "\ncombinateMemoize!(A!()),combinateMemoize!(parseEOF!())).parse(input, info);}}", makeContext("", 21), Error(q{"("}, 20)));
                assert(def!().parse(makeContext(`None recursive  A $;`), new CallerInfo(__LINE__, "")) == makeParseResult(false, "", makeContext(""), Error(q{"="}, 16)));
                assert(def!().parse(makeContext("None recursive  \nA $;"), new CallerInfo(__LINE__, "")) == makeParseResult(false, "", makeContext(""), Error(q{"="}, 17, 2)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        };

    // defs
        template defs(){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Context!string input, in CallerInfo info){
                return combinateConvert!(
                    combinateSequence!(
                        parseSpaces!(),
                        combinateMore1!(
                            combinateChoice!(
                                combinateConvert!(
                                    combinateChangeState!(
                                        combinateConvert!(
                                            combinateSequence!(
                                                combinateNone!(parseString!"@default_skip("),
                                                choiceExp!(),
                                                combinateNone!(parseString!")")
                                            ),
                                            function(string skip) => tuple(skip, "")
                                        )
                                    ),
                                    function() => ""
                                ),
                                def!(),
                            ),
                            parseSpaces!()
                        ),
                        parseSpaces!(),
                        parseEOF!()
                    ),
                    flat
                ).parse(input, info);
            }
        }

        unittest{
            enum dg = {
                cast(void)__LINE__; 
                assert(defs!().parse(makeContext(q{ @default_skip(" " / "\t" / "\n") bool hoge = !"hello" $ >> {return false;}; @skip(" ") Tuple!piyo hoge2 = hoge* >> {return tuple("foo");}; }), new CallerInfo(__LINE__, r"src\ctpg.d")) == makeParseResult(true, "template hoge(){alias bool ResultType;static ParseResult!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){return combinateConvert!(" ~ toStringNow!__LINE__ ~ ",`src\\ctpg.d`,combinateSequence!(combinateNone!(combinateSkip!(combinateMemoize!(parseString!\"hello\"),combinateChoice!(" ~ toStringNow!__LINE__ ~ ",`src\\ctpg.d`,combinateMemoize!(parseString!\" \"),combinateMemoize!(parseString!\"\\t\"),combinateMemoize!(parseString!\"\\n\")))),combinateSkip!(combinateMemoize!(parseEOF!()),combinateChoice!(" ~ toStringNow!__LINE__ ~ ",`src\\ctpg.d`,combinateMemoize!(parseString!\" \"),combinateMemoize!(parseString!\"\\t\"),combinateMemoize!(parseString!\"\\n\")))),function(){return false;}).parse(input, info);}}template hoge2(){alias Tuple!piyo ResultType;static ParseResult!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){return combinateConvert!(" ~ toStringNow!__LINE__ ~ ",`src\\ctpg.d`,combinateMore0!( #line " ~ toStringNow!__LINE__ ~ "\ncombinateSkip!(combinateMemoize!(hoge!()),combinateMemoize!(parseString!\" \"))),function(){return tuple(\"foo\");}).parse(input, info);}}", makeContext("", 138, 1, tuple("combinateChoice!(" ~ toStringNow!__LINE__ ~ ",`src\\ctpg.d`,combinateMemoize!(parseString!\" \"),combinateMemoize!(parseString!\"\\t\"),combinateMemoize!(parseString!\"\\n\"))", "combinateMemoize!(parseString!\" \")")), Error(q{"_"}, 138)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        };

