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
import std.conv:        to;
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
        Result!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
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
            return Context(input.save, line, state);
        }

        @property
        bool empty(){
            return input.empty;
        }

        equals_t opEquals(Context rhs){
            return input == rhs.input && line == rhs.line && state == rhs.state;
        }
    }

    Context!Range makeContext(Range)(Range range, size_t line = 1, StateType state = StateType.init){
        return Context!Range(range, line, state);
    }

// struct Result
    struct Result(Range, T){
        bool match;
        T value;
        Context!Range rest;
        Error error;

        void opAssign(U)(Result!(Range, U) rhs)if(isAssignable!(T, U)){
            match = rhs.match;
            value = rhs.value;
            rest = rhs.rest;
            error = rhs.error;
        }

        equals_t opEquals(Result lhs){
            return match == lhs.match && value == lhs.value && rest == lhs.rest && error == lhs.error;
        }
    }

    Result!(Range, T) result(Range, T)(bool match, T value, Context!Range rest, Error error = Error.init){
        return Result!(Range, T)(match, value, rest, error);
    }

    alias result makeResult;

// struct Error
    struct Error{
        invariant(){
            assert(line >= 1);
        }

        public{
            string need;
            size_t line = 1;

            pure @safe nothrow const
            bool opEquals(in Error rhs){
                return need == rhs.need && line == rhs.line;
            }
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
            static Result!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                return result(true, None.init, input, Error.init);
            }
        }

    // failure
        template failure(){
            alias None ResultType;
            static Result!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                return result(false, None.init, Context!R.init, Error.init);
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
            }else static if(isForwardRange!T){
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

        Tuple!(size_t, "width", size_t, "line") countBreadth(string str)in{
            assert(str.length > 0);
        }body{
            typeof(return) result;
            size_t idx;
            while(idx < str.length){
                auto c = decode(str, idx);
                if(c == '\n'){
                    ++result.line;
                }
                ++result.width;
            }
            return result;
        }

        unittest{
            enum dg = {
                assert(countBreadth("これ\nとこれ") == tuple(6, 1));
                assert(countBreadth("これ\nとこれ\nとさらにこれ") == tuple(13, 2));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

        template parseString(string str){
            static assert(str.length);
            alias string ResultType;
            static Result!(R, ResultType) parse(R)(Context!R _input, in CallerInfo info){
                auto input = _input; // Somehow this parser doesn't work well without this line.
                enum breadth = countBreadth(str);
                typeof(return) result;
                static if(isSomeString!R){
                    enum convertedString = staticConvertString!(str, R);
                    if(input.input.length >= convertedString.length && convertedString == input.input[0..convertedString.length]){
                        result.match = true;
                        result.value = str;
                        result.rest.input = input.input[convertedString.length..$];
                        result.rest.line = input.line + breadth.line;
                        result.rest.state = input.state;
                        return result;
                    }
                    result.error = Error('"' ~ str ~ '"', input.line);
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
                    result.rest.input = input.input;
                    result.rest.line = input.line + breadth.line;
                    result.rest.state = input.state;
                    return result;

                    Lerror:

                    result.error = Error('"' ~ str ~ '"', input.line);
                }else{
                    throw new Exception("");
                }
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(getResult!(parseString!"hello")("hello world" ) == result(true, "hello", makeContext(" world" )));
                assert(getResult!(parseString!"hello")("hello world"w) == result(true, "hello", makeContext(" world"w)));
                assert(getResult!(parseString!"hello")("hello world"d) == result(true, "hello", makeContext(" world"d)));
                assert(getResult!(parseString!"hello")(testRange("hello world" )) == result(true, "hello", makeContext(testRange(" world" ))));
                assert(getResult!(parseString!"hello")(testRange("hello world"w)) == result(true, "hello", makeContext(testRange(" world"w))));
                assert(getResult!(parseString!"hello")(testRange("hello world"d)) == result(true, "hello", makeContext(testRange(" world"d))));

                assert(getResult!(parseString!"hello")("hello" ) == result(true, "hello", makeContext("" )));
                assert(getResult!(parseString!"hello")("hello"w) == result(true, "hello", makeContext(""w)));
                assert(getResult!(parseString!"hello")("hello"d) == result(true, "hello", makeContext(""d)));
                assert(getResult!(parseString!"hello")(testRange("hello" )) == result(true, "hello", makeContext(testRange("" ))));
                assert(getResult!(parseString!"hello")(testRange("hello"w)) == result(true, "hello", makeContext(testRange(""w))));
                assert(getResult!(parseString!"hello")(testRange("hello"d)) == result(true, "hello", makeContext(testRange(""d))));

                assert(getResult!(parseString!"表が怖い")("表が怖い噂のソフト" ) == result(true, "表が怖い", makeContext("噂のソフト" )));
                assert(getResult!(parseString!"表が怖い")("表が怖い噂のソフト"w) == result(true, "表が怖い", makeContext("噂のソフト"w)));
                assert(getResult!(parseString!"表が怖い")("表が怖い噂のソフト"d) == result(true, "表が怖い", makeContext("噂のソフト"d)));
                assert(getResult!(parseString!"表が怖い")(testRange("表が怖い噂のソフト" )) == result(true, "表が怖い", makeContext(testRange("噂のソフト" ))));
                assert(getResult!(parseString!"表が怖い")(testRange("表が怖い噂のソフト"w)) == result(true, "表が怖い", makeContext(testRange("噂のソフト"w))));
                assert(getResult!(parseString!"表が怖い")(testRange("表が怖い噂のソフト"d)) == result(true, "表が怖い", makeContext(testRange("噂のソフト"d))));

                assert(getResult!(parseString!"hello")("hllo world" ) == result(false, "", makeContext("" ), Error("\"hello\"")));
                assert(getResult!(parseString!"hello")("hllo world"w) == result(false, "", makeContext(""w), Error("\"hello\"")));
                assert(getResult!(parseString!"hello")("hllo world"d) == result(false, "", makeContext(""d), Error("\"hello\"")));
                assert(getResult!(parseString!"hello")(testRange("hllo world" )) == result(false, "", makeContext(testRange("" )), Error("\"hello\"")));
                assert(getResult!(parseString!"hello")(testRange("hllo world"w)) == result(false, "", makeContext(testRange(""w)), Error("\"hello\"")));
                assert(getResult!(parseString!"hello")(testRange("hllo world"d)) == result(false, "", makeContext(testRange(""d)), Error("\"hello\"")));

                try{
                    scope(success) assert(false);
                    auto result = getResult!(parseString!"hello")([0, 0]);
                }catch(Exception ex){}
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // parseCharRange
        dchar decodeRange(R)(auto ref R range){
            dchar result;
            static if(is(Unqual!(ElementType!R) == char)){
                if(!(range.front & 0b_1000_0000)){
                    result = range.front;
                    range.popFront;
                    return result;
                }else if(!(range.front & 0b_0010_0000)){
                    result = range.front & 0b_0001_1111;
                    result <<= 6;
                    range.popFront;
                    result |= range.front & 0b_0011_1111;
                    range.popFront;
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
                    return result;
                }
            }else static if(is(Unqual!(ElementType!R) == wchar)){
                if(range.front <= 0xD7FF || (0xE000 <= range.front && range.front < 0xFFFF)){
                    result = range.front;
                    range.popFront;
                    return result;
                }else{
                    result = (range.front & 0b_0000_0011_1111_1111) * 0x400;
                    range.popFront;
                    result += (range.front & 0b_0000_0011_1111_1111) + 0x10000;
                    range.popFront;
                    return result;
                }
            }else static if(is(Unqual!(ElementType!R) == dchar)){
                result = range.front;
                range.popFront;
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(decodeRange(testRange("\u0001")) == '\u0001');
                assert(decodeRange(testRange("\u0081")) == '\u0081');
                assert(decodeRange(testRange("\u0801")) == '\u0801');
                assert(decodeRange(testRange("\U00012345")) == '\U00012345');
                assert(decodeRange(testRange("\u0001"w)) == '\u0001');
                assert(decodeRange(testRange("\uE001"w)) == '\uE001');
                assert(decodeRange(testRange("\U00012345"w)) == '\U00012345');
                assert(decodeRange(testRange("\U0010FFFE")) == '\U0010FFFE');
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

        template parseCharRange(dchar low, dchar high){
            static assert(low <= high);

            alias string ResultType;
            static Result!(R, ResultType) parse(R)(Context!R _input, in CallerInfo info){
                auto input = _input; // Somehow this parser doesn't work well without this line.
                typeof(return) result;
                static if(isSomeString!R){
                    if(input.input.length){
                        size_t idx;
                        dchar c = decode(input.input, idx);
                        if(low <= c && c <= high){
                            result.match = true;
                            result.value = c.to!string();
                            result.rest.input = input.input[idx..$];
                            result.rest.line = c == '\n' ? input.line + 1 : input.line;
                            result.rest.state = input.state;
                            return result;
                        }
                    }
                    if(low == dchar.min && high == dchar.max){
                        result.error = Error("any char", input.line);
                    }else{
                        result.error = Error("c: '" ~ low.to!string() ~ "' <= c <= '" ~ high.to!string() ~ "'", input.line);
                    }
                }else static if(isCharRange!R){
                    if(!input.input.empty){
                        dchar c = decodeRange(input.input);
                        if(low <= c && c <= high){
                            result.match = true;
                            result.value = c.to!string();
                            result.rest.input = input.input;
                            result.rest.line = c == '\n' ? input.line + 1 : input.line;
                            result.rest.state = input.state;
                            return result;
                        }
                    }
                    if(low == dchar.min && high == dchar.max){
                        result.error = Error("any char", input.line);
                    }else{
                        result.error = Error("c: '" ~ low.to!string() ~ "' <= c <= '" ~ high.to!string() ~ "'", input.line);
                    }
                }else{
                    throw new Exception("");
                }
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(getResult!(parseCharRange!('a', 'z'))("hoge" ) == result(true, "h", makeContext("oge" )));
                assert(getResult!(parseCharRange!('a', 'z'))("hoge"w) == result(true, "h", makeContext("oge"w)));
                assert(getResult!(parseCharRange!('a', 'z'))("hoge"d) == result(true, "h", makeContext("oge"d)));
                assert(getResult!(parseCharRange!('a', 'z'))(testRange("hoge" )) == result(true, "h", makeContext(testRange("oge" ))));
                assert(getResult!(parseCharRange!('a', 'z'))(testRange("hoge"w)) == result(true, "h", makeContext(testRange("oge"w))));
                assert(getResult!(parseCharRange!('a', 'z'))(testRange("hoge"d)) == result(true, "h", makeContext(testRange("oge"d))));

                assert(getResult!(parseCharRange!('\u0100', '\U0010FFFF'))("\U00012345hoge" ) == result(true, "\U00012345", makeContext("hoge" )));
                assert(getResult!(parseCharRange!('\u0100', '\U0010FFFF'))("\U00012345hoge"w) == result(true, "\U00012345", makeContext("hoge"w)));
                assert(getResult!(parseCharRange!('\u0100', '\U0010FFFF'))("\U00012345hoge"d) == result(true, "\U00012345", makeContext("hoge"d)));
                assert(getResult!(parseCharRange!('\u0100', '\U0010FFFF'))(testRange("\U00012345hoge" )) == result(true, "\U00012345", makeContext(testRange("hoge" ))));
                assert(getResult!(parseCharRange!('\u0100', '\U0010FFFF'))(testRange("\U00012345hoge"w)) == result(true, "\U00012345", makeContext(testRange("hoge"w))));
                assert(getResult!(parseCharRange!('\u0100', '\U0010FFFF'))(testRange("\U00012345hoge"d)) == result(true, "\U00012345", makeContext(testRange("hoge"d))));

                assert(getResult!(parseCharRange!('\u0100', '\U0010FFFF'))("hello world" ) == result(false, "", makeContext("" ), Error("c: '\u0100' <= c <= '\U0010FFFF'")));
                assert(getResult!(parseCharRange!('\u0100', '\U0010FFFF'))("hello world"w) == result(false, "", makeContext(""w), Error("c: '\u0100' <= c <= '\U0010FFFF'")));
                assert(getResult!(parseCharRange!('\u0100', '\U0010FFFF'))("hello world"d) == result(false, "", makeContext(""d), Error("c: '\u0100' <= c <= '\U0010FFFF'")));
                assert(getResult!(parseCharRange!('\u0100', '\U0010FFFF'))(testRange("hello world" )) == result(false, "", makeContext(testRange("" )), Error("c: '\u0100' <= c <= '\U0010FFFF'")));
                assert(getResult!(parseCharRange!('\u0100', '\U0010FFFF'))(testRange("hello world"w)) == result(false, "", makeContext(testRange(""w)), Error("c: '\u0100' <= c <= '\U0010FFFF'")));
                assert(getResult!(parseCharRange!('\u0100', '\U0010FFFF'))(testRange("hello world"d)) == result(false, "", makeContext(testRange(""d)), Error("c: '\u0100' <= c <= '\U0010FFFF'")));

                try{
                    scope(success) assert(false);
                    auto result = getResult!(parseCharRange!('\u0100', '\U0010FFFF'))([0, 0]);
                }catch(Exception ex){}
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // parseEscapeSequence
        template parseEscapeSequence(){
            alias string ResultType;
            static Result!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                typeof(return) result;
                static if(isSomeString!R){
                    if(input.input[0] == '\\'){
                        switch(input.input[1]){
                            case 'u':{
                                result.match = true;
                                result.value = input.input[0..6].to!string();
                                result.rest.input = input.input[6..$];
                                result.rest.line = input.line;
                                result.rest.state = input.state;
                                return result;
                            }
                            case 'U':{
                                result.match = true;
                                result.value = input.input[0..10].to!string();
                                result.rest.input = input.input[10..$];
                                result.rest.line = input.line;
                                result.rest.state = input.state;
                                return result;
                            }
                            case '\'': case '"': case '?': case '\\': case 'a': case 'b': case 'f': case 'n': case 'r': case 't': case 'v':{
                                result.match = true;
                                result.value = input.input[0..2].to!string();
                                result.rest.input = input.input[2..$];
                                result.rest.line = input.line;
                                result.rest.state = input.state;
                                return result;
                            }
                            default:{
                            }
                        }
                    }
                    result.error = Error("escape sequence", input.line);
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
                                result.rest.input = input.input;
                                result.rest.line = input.line;
                                result.rest.state = input.state;
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
                                result.rest.input = input.input;
                                result.rest.line = input.line;
                                result.rest.state = input.state;
                                return result;
                            }
                            case '\'': case '"': case '?': case '\\': case 'a': case 'b': case 'f': case 'n': case 'r': case 't': case 'v':{
                                result.match = true;
                                input.input.popFront;
                                result.value = "\\" ~ to!string(c2);
                                result.rest.input = input.input;
                                result.rest.line = input.line;
                                result.rest.state = input.state;
                                return result;
                            }
                            default:{
                            }
                        }
                    }
                    result.error = Error("escape sequence", input.line);
                }else{
                    throw new Exception("");
                }
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(getResult!(parseEscapeSequence!())(`\"hoge` ) == result(true, `\"`, makeContext("hoge" )));
                assert(getResult!(parseEscapeSequence!())(`\"hoge`w) == result(true, `\"`, makeContext("hoge"w)));
                assert(getResult!(parseEscapeSequence!())(`\"hoge`d) == result(true, `\"`, makeContext("hoge"d)));
                assert(getResult!(parseEscapeSequence!())(testRange(`\"hoge` )) == result(true, `\"`, makeContext(testRange("hoge" ))));
                assert(getResult!(parseEscapeSequence!())(testRange(`\"hoge`w)) == result(true, `\"`, makeContext(testRange("hoge"w))));
                assert(getResult!(parseEscapeSequence!())(testRange(`\"hoge`d)) == result(true, `\"`, makeContext(testRange("hoge"d))));

                assert(getResult!(parseEscapeSequence!())(`\U0010FFFFhoge` ) == result(true, `\U0010FFFF`, makeContext("hoge" )));
                assert(getResult!(parseEscapeSequence!())(`\U0010FFFFhoge`w) == result(true, `\U0010FFFF`, makeContext("hoge"w)));
                assert(getResult!(parseEscapeSequence!())(`\U0010FFFFhoge`d) == result(true, `\U0010FFFF`, makeContext("hoge"d)));
                assert(getResult!(parseEscapeSequence!())(testRange(`\U0010FFFFhoge` )) == result(true, `\U0010FFFF`, makeContext(testRange("hoge" ))));
                assert(getResult!(parseEscapeSequence!())(testRange(`\U0010FFFFhoge`w)) == result(true, `\U0010FFFF`, makeContext(testRange("hoge"w))));
                assert(getResult!(parseEscapeSequence!())(testRange(`\U0010FFFFhoge`d)) == result(true, `\U0010FFFF`, makeContext(testRange("hoge"d))));

                assert(getResult!(parseEscapeSequence!())(`\u10FFhoge` ) == result(true, `\u10FF`, makeContext("hoge" )));
                assert(getResult!(parseEscapeSequence!())(`\u10FFhoge`w) == result(true, `\u10FF`, makeContext("hoge"w)));
                assert(getResult!(parseEscapeSequence!())(`\u10FFhoge`d) == result(true, `\u10FF`, makeContext("hoge"d)));
                assert(getResult!(parseEscapeSequence!())(testRange(`\u10FFhoge` )) == result(true, `\u10FF`, makeContext(testRange("hoge" ))));
                assert(getResult!(parseEscapeSequence!())(testRange(`\u10FFhoge`w)) == result(true, `\u10FF`, makeContext(testRange("hoge"w))));
                assert(getResult!(parseEscapeSequence!())(testRange(`\u10FFhoge`d)) == result(true, `\u10FF`, makeContext(testRange("hoge"d))));

                assert(getResult!(parseEscapeSequence!())(`\nhoge` ) == result(true, `\n`, makeContext("hoge" )));
                assert(getResult!(parseEscapeSequence!())(`\nhoge`w) == result(true, `\n`, makeContext("hoge"w)));
                assert(getResult!(parseEscapeSequence!())(`\nhoge`d) == result(true, `\n`, makeContext("hoge"d)));
                assert(getResult!(parseEscapeSequence!())(testRange(`\nhoge` )) == result(true, `\n`, makeContext(testRange("hoge" ))));
                assert(getResult!(parseEscapeSequence!())(testRange(`\nhoge`w)) == result(true, `\n`, makeContext(testRange("hoge"w))));
                assert(getResult!(parseEscapeSequence!())(testRange(`\nhoge`d)) == result(true, `\n`, makeContext(testRange("hoge"d))));

                assert(getResult!(parseEscapeSequence!())("鬱hoge" ) == result(false, "", makeContext("" ), Error("escape sequence")));
                assert(getResult!(parseEscapeSequence!())("鬱hoge"w) == result(false, "", makeContext(""w), Error("escape sequence")));
                assert(getResult!(parseEscapeSequence!())("鬱hoge"d) == result(false, "", makeContext(""d), Error("escape sequence")));
                assert(getResult!(parseEscapeSequence!())(testRange("鬱hoge" )) == result(false, "", makeContext(testRange("" )), Error("escape sequence")));
                assert(getResult!(parseEscapeSequence!())(testRange("鬱hoge"w)) == result(false, "", makeContext(testRange(""w)), Error("escape sequence")));
                assert(getResult!(parseEscapeSequence!())(testRange("鬱hoge"d)) == result(false, "", makeContext(testRange(""d)), Error("escape sequence")));

                try{
                    scope(success) assert(false);
                    auto result = getResult!(parseEscapeSequence!())([0, 0][]);
                }catch(Exception ex){}
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // parseSpace
        template parseSpace(){
            alias string ResultType;
            static Result!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                typeof(return) result;
                static if(isSomeString!R){
                    if(input.input.length > 0 && (input.input[0] == ' ' || input.input[0] == '\n' || input.input[0] == '\t' || input.input[0] == '\r' || input.input[0] == '\f')){
                        result.match = true;
                        result.value = input.input[0..1].to!string();
                        result.rest.input = input.input[1..$];
                        result.rest.line = (input.input[0] == '\n' ? input.line + 1 : input.line);
                        result.rest.state = input.state;
                        return result;
                    }
                    result.error = Error("space", input.line);
                }else static if(isCharRange!R){
                    if(!input.input.empty){
                        Unqual!(ElementType!R) c = input.input.front;
                        if(c == ' ' || c == '\n' || c == '\t' || c == '\r' || c == '\f'){
                            result.match = true;
                            result.value = c.to!string();
                            input.input.popFront;
                            result.rest.input = input.input;
                            result.rest.line = (c == '\n' ? input.line + 1 : input.line);
                            result.rest.state = input.state;
                            return result;
                        }
                    }
                    result.error = Error("space", input.line);
                }else{
                    throw new Exception("");
                }
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(getResult!(parseSpace!())("\thoge" ) == result(true, "\t", makeContext("hoge" )));
                assert(getResult!(parseSpace!())("\thoge"w) == result(true, "\t", makeContext("hoge"w)));
                assert(getResult!(parseSpace!())("\thoge"d) == result(true, "\t", makeContext("hoge"d)));
                assert(getResult!(parseSpace!())(testRange("\thoge"))  == result(true, "\t", makeContext(testRange("hoge" ))));
                assert(getResult!(parseSpace!())(testRange("\thoge"w)) == result(true, "\t", makeContext(testRange("hoge"w))));
                assert(getResult!(parseSpace!())(testRange("\thoge"d)) == result(true, "\t", makeContext(testRange("hoge"d))));

                assert(getResult!(parseSpace!())("hoge" ) == result(false, "", makeContext("" ), Error("space")));
                assert(getResult!(parseSpace!())("hoge"w) == result(false, "", makeContext(""w), Error("space")));
                assert(getResult!(parseSpace!())("hoge"d) == result(false, "", makeContext(""d), Error("space")));
                assert(getResult!(parseSpace!())(testRange("hoge" )) == result(false, "", makeContext(testRange("" )), Error("space")));
                assert(getResult!(parseSpace!())(testRange("hoge"w)) == result(false, "", makeContext(testRange(""w)), Error("space")));
                assert(getResult!(parseSpace!())(testRange("hoge"d)) == result(false, "", makeContext(testRange(""d)), Error("space")));

                try{
                    scope(success) assert(false);
                    auto result = getResult!(parseSpace!())([0, 0]);
                }catch(Exception ex){}
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // parseEOF
        template parseEOF(){
            alias None ResultType;
            static Result!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                typeof(return) result;
                if(input.input.empty){
                    result.match = true;
                    result.rest.input = input.input;
                    result.rest.line = input.line;
                    result.rest.state = input.state;
                }else{
                    static if(isSomeString!R || isCharRange!R){
                        result.error = Error("EOF", input.line);
                    }else{
                        result.error = Error("EOF");
                    }
                }
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(getResult!(parseEOF!())("" ) == result(true, None.init, makeContext("" )));
                assert(getResult!(parseEOF!())(""w) == result(true, None.init, makeContext(""w)));
                assert(getResult!(parseEOF!())(""d) == result(true, None.init, makeContext(""d)));
                assert(getResult!(parseEOF!())(testRange("" )) == result(true, None.init, makeContext(testRange("" ))));
                assert(getResult!(parseEOF!())(testRange(""w)) == result(true, None.init, makeContext(testRange(""w))));
                assert(getResult!(parseEOF!())(testRange(""d)) == result(true, None.init, makeContext(testRange(""d))));

                assert(getResult!(parseEOF!())("hoge" ) == result(false, None.init, makeContext("" ), Error("EOF")));
                assert(getResult!(parseEOF!())("hoge"w) == result(false, None.init, makeContext(""w), Error("EOF")));
                assert(getResult!(parseEOF!())("hoge"d) == result(false, None.init, makeContext(""d), Error("EOF")));
                assert(getResult!(parseEOF!())(testRange("hoge" )) == result(false, None.init, makeContext(testRange("" )), Error("EOF")));
                assert(getResult!(parseEOF!())(testRange("hoge"w)) == result(false, None.init, makeContext(testRange(""w)), Error("EOF")));
                assert(getResult!(parseEOF!())(testRange("hoge"d)) == result(false, None.init, makeContext(testRange(""d)), Error("EOF")));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

// combinators
    // combinateSkip
        template combinateSkip(alias parser, alias skip){
            alias ParserType!parser ResultType;
            static Result!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                auto r = parser.parse(input.save, info);
                if(!r.match){
                    auto skipped = skip.parse(input, info);
                    if(skipped.match){
                        return parser.parse(skipped.rest, info);
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
                assert(getResult!(combinateSkip!(parseString!"foo", parseString!" "))(" foo") == result(true, "foo", makeContext("")));
                assert(getResult!(combinateSkip!(parseString!"foo", parseString!" "))("foo") == result(true, "foo", makeContext("")));
                assert(getResult!(combinateSkip!(parseString!"foo", parseString!"foo"))("foo") == result(true, "foo", makeContext("")));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // combinateUnTuple
        template combinateUnTuple(alias parser){
            static if(isTuple!(ParserType!parser) && ParserType!parser.Types.length == 1){
                alias ParserType!parser.Types[0] ResultType;
                static Result!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                    typeof(return) result;
                    auto r = parser.parse(input, info);
                    result.match = r.match;
                    result.value = r.value[0];
                    result.rest = r.rest;
                    result.error = r.error;
                    return result;
                }
            }else{
                alias parser combinateUnTuple;
            }
        }

        unittest{
            enum dg = {
                assert(getResult!(combinateUnTuple!(TestParser!int))("") == result(false, 0, makeContext("")));
                assert(getResult!(combinateUnTuple!(TestParser!long))("") == result(false, 0L, makeContext("")));
                assert(getResult!(combinateUnTuple!(TestParser!string))("") == result(false, "", makeContext("")));
                assert(getResult!(combinateUnTuple!(TestParser!wstring))("") == result(false, ""w, makeContext("")));
                assert(getResult!(combinateUnTuple!(TestParser!dstring))("") == result(false, ""d, makeContext("")));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!int)))("") == result(false, 0, makeContext("")));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(int, int))))("") == result(false, tuple(0, 0), makeContext("")));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!int))))("") == result(false, tuple(0), makeContext("")));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!(int, int)))))("") == result(false, tuple(0, 0), makeContext("")));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!(int, int), int))))("") == result(false, tuple(tuple(0, 0), 0), makeContext("")));
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
            static Result!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
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
                        result.rest = r.rest;
                    }else{
                        result.error = r.error;
                    }
                }else{
                    auto r1 = parsers[0].parse(input, info);
                    if(r1.match){
                        auto r2 = combinateSequenceImpl!(parsers[1..$]).parse(r1.rest, info);
                        if(r2.match){
                            result.match = true;
                            static if(isTuple!(ParserType!(parsers[0]))){
                                result.value = tuple(r1.value.field, r2.value.field);
                            }else{
                                result.value = tuple(r1.value, r2.value.field);
                            }
                            result.rest = r2.rest;
                        }else{
                            result.error = r2.error;
                        }
                    }else{
                        result.error = r1.error;
                    }
                }
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))("helloworld") == result(true, tuple("hello", "world"), makeContext("")));
                assert(getResult!(combinateSequence!(combinateSequence!(parseString!("hello"), parseString!("world")), parseString!"!"))("helloworld!") == result(true, tuple("hello", "world", "!"), makeContext("")));
                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))("hellovvorld") == result(false, tuple("", ""), makeContext(""), Error(q{"world"})));
                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world"), parseString!("!")))("helloworld?") == result(false, tuple("", "", ""), makeContext(""), Error(q{"!"})));
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
            static Result!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                static assert(parsers.length > 0);
                static if(parsers.length == 1){
                    return parsers[0].parse(input, info);
                }else{
                    auto r = parsers[0].parse(input.save, info);
                    if(r.match){
                        return r;
                    }
                    return combinateChoice!(parsers[1..$]).parse(input, info);
                }
            }
        }

        unittest{
            enum dg = {
                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))("hw") == result(true, "h", makeContext("w"))); 
                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))("w") == result(true, "w", makeContext("")));
                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))("") == result(false, "", makeContext(""), Error(q{"w"})));
                //assert(getResult!(combinateChoice!(parseString!"h", combinateSequence!(parseString!"w", parseString!"w")))(testRange("w"d)) == result(true, "w", makeContext(testRange(""d))));
                //assert(getResult!(combinateChoice!(__LINE__, "foo/bar.d", parseString!"h", combinateSequence!(parseString!"w", parseString!"w")))(testRange("w"d)) == result(true, "w", makeContext(testRange(""d))));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // combinateMore
        template combinateMore(int n, alias parser, alias sep){
            alias ParserType!(parser)[] ResultType;
            static Result!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                typeof(return) result;
                Context!R rest = input;
                while(true){
                    auto input1 = rest.save;
                    auto r1 = parser.parse(input1, info);
                    if(r1.match){
                        result.value ~= r1.value;
                        rest = r1.rest;
                        auto input2 = rest.save;
                        auto r2 = sep.parse(input2, info);
                        if(r2.match){
                            rest = r2.rest;
                        }else{
                            break;
                        }
                    }else{
                        if(result.value.length < n){
                            result.error = r1.error;
                            return result;
                        }else{
                            break;
                        }
                    }
                }
                result.match = true;
                result.rest = rest;
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
                assert(getResult!(combinateMore0!(parseString!"w"))("www w") == result(true, ["w", "w", "w"], makeContext(" w")));
                assert(getResult!(combinateMore0!(parseString!"w"))(" w") == result(true, [""][0..0], makeContext(" w")));
                assert(getResult!(combinateMore1!(parseString!"w"))("www w") == result(true, ["w", "w", "w"], makeContext(" w")));
                assert(getResult!(combinateMore1!(parseString!"w"))(" w") == result(false, [""][0..0], makeContext(""), Error(q{"w"})));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // combinateOption
        template combinateOption(alias parser){
            alias Option!(ParserType!parser) ResultType;
            static Result!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                typeof(return) result;
                result.match = true;
                auto r = parser.parse(input.save, info);
                if(r.match){
                    result.value = r.value;
                    result.value.some = true;
                    result.rest = r.rest;
                }else{
                    result.rest = input;
                }
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(getResult!(combinateOption!(parseString!"w"))("w") == result(true, makeOption(true, "w"), makeContext("")));
                assert(getResult!(combinateOption!(parseString!"w"))("hoge") == result(true, makeOption(false, ""), makeContext("hoge")));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // combinateNone
        template combinateNone(alias parser){
            alias None ResultType;
            static Result!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                typeof(return) result;
                auto r = parser.parse(input, info);
                if(r.match){
                    result.match = true;
                    result.rest = r.rest;
                }else{
                    result.error = r.error;
                }
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))("(w)") == result(true, "w", makeContext("")));
                assert(getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))("(w}") == result(false, "", makeContext(""), Error(q{")"})));
                assert(getResult!(combinateNone!(parseString!"w"))("a") == result(false, None.init, makeContext(""), Error(q{"w"})));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // combinateAndPred
        template combinateAndPred(alias parser){
            alias None ResultType;
            static Result!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                typeof(return) result;
                result.rest = input;
                auto r = parser.parse(input, info);
                result.match = r.match;
                result.error = r.error;
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(getResult!(combinateAndPred!(parseString!"w"))("www") == result(true, None.init, makeContext("www")));
                assert(getResult!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w")))("www") == result(true, "w", makeContext("ww")));
                assert(getResult!(combinateMore1!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w"))))("www") == result(true, ["w", "w"], makeContext("w")));
                assert(getResult!(combinateMore1!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w"))))("w") == result(false, [""][0..0], makeContext(""), Error(q{"w"})));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // combinateNotPred
        template combinateNotPred(alias parser){
            alias None ResultType;
            static Result!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                typeof(return) result;
                result.rest = input;
                result.match = !parser.parse(input.save, info).match;
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(getResult!(combinateMore1!(combinateSequence!(parseString!"w", combinateNotPred!(parseString!"s"))))("wwws") == result(true, ["w", "w"], makeContext("ws")));
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
            static Result!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
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
                    result.rest = r.rest;
                }else{
                    result.error = r.error;
                }
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), function(string[] ws){ return ws.length; }))("www") == result(true, cast(size_t)3, makeContext("")));
                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), function(string[] ws){ return ws.length; }))("a") == result(false, cast(size_t)0, makeContext(""), Error(q{"w"})));
                //assert(getResult!(combinateConvert!(10, "hoge/fuga.d", combinateMore1!(parseString!"w"), function(string ws){ return ws.length; }))(testRange("a")) == result(false, cast(size_t)0, makeContext(testRange("")), Error(q{"w"})));
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
            static Result!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
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
                    result.rest = r.rest;
                }else{
                    result.error = r.error;
                }
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(getResult!(combinateConvertWithState!(combinateMore1!(parseString!"w"), function(string[] ws, StateType state){ return ws.length; }))("www") == result(true, cast(size_t)3, makeContext("")));
                assert(getResult!(combinateConvertWithState!(combinateMore1!(parseString!"w"), function(string[] ws, StateType state){ return ws.length; }))("a") == result(false, cast(size_t)0, makeContext(""), Error(q{"w"})));
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
            static Result!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                typeof(return) result;
                auto r = parser.parse(input, info);
                if(r.match){
                    if(checker(r.value)){
                        result = r;
                    }else{
                        result.error = Error("passing check", input.line);
                    }
                }else{
                    result.error = r.error;
                }
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(getResult!(combinateCheck!(combinateMore0!(parseString!"w"), function(string[] ws){ return ws.length == 5; }))("wwwww") == result(true, ["w", "w", "w", "w", "w"], makeContext("")));
                assert(getResult!(combinateCheck!(combinateMore0!(parseString!"w"), function(string[] ws){ return ws.length == 5; }))("wwww") == result(false, [""][0..0], makeContext(""), Error("passing check")));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // combinateChangeState
        template combinateChangeState(alias parser){
            alias None ResultType;
            static Result!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                typeof(return) result;
                auto r = parser.parse(input, info);
                if(r.match){
                    result.match = true;
                    result.rest.input = r.rest.input;
                    result.rest.line = r.rest.line;
                    result.rest.state = r.value;
                }
                return result;
            }
        }

        version(none) unittest{
            enum dg = {
                {
                    auto r = getResult!(combinateChangeState!(parseString!"hoge"))("hoge");
                    assert(r.rest.input == "");
                    assert(r.rest.state == "hoge");
                }
                {
                    auto r = getResult!(combinateSequence!(combinateChangeState!(parseString!"hoge"), combinateChangeState!(parseString!"piyo")))("hogepiyo");
                    assert(r.rest.input == "");
                    assert(r.rest.state == "piyo");
                }
                return true;
            };
            dg();
            debug(ctpg_compile_time) static assert(dg());
        }

    // combinateMemoize
        template combinateMemoize(alias parser){
            alias ParserType!parser ResultType;
            Result!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
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
            getResult!(combinateSequence!(combinateAndPred!p, p))("str");
            getResult!(combinateSequence!(combinateAndPred!p, p))("str".testRange());
        }

// getters
    // getLine
        template getLine(){
            alias size_t ResultType;
            static Result!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                static if(isSomeString!R || isCharRange!R){
                    return result(true, input.line, input, Error.init);
                }else{
                    throw new Exception("");
                }
            }
        }

        unittest{
            enum dg = {
                assert(getResult!(combinateSequence!(parseSpaces!(), getLine!()))("\n\n" ) == result(true, cast(size_t)3, makeContext("" , 3)));
                assert(getResult!(combinateSequence!(parseSpaces!(), getLine!()))("\n\n"w) == result(true, cast(size_t)3, makeContext(""w, 3)));
                assert(getResult!(combinateSequence!(parseSpaces!(), getLine!()))("\n\n"d) == result(true, cast(size_t)3, makeContext(""d, 3)));
                assert(getResult!(combinateSequence!(parseSpaces!(), getLine!()))(testRange("\n\n" )) == result(true, cast(size_t)3, makeContext(testRange("" ), 3)));
                assert(getResult!(combinateSequence!(parseSpaces!(), getLine!()))(testRange("\n\n"w)) == result(true, cast(size_t)3, makeContext(testRange(""w), 3)));
                assert(getResult!(combinateSequence!(parseSpaces!(), getLine!()))(testRange("\n\n"d)) == result(true, cast(size_t)3, makeContext(testRange(""d), 3)));

                try{
                    scope(failure) assert(true);
                    auto result = getResult!(combinateSequence!(parseSpaces!(), getLine!()))([0, 0]);
                }catch(Exception ex){}
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // getCallerLine
        template getCallerLine(){
            alias size_t ResultType;
            static Result!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                return result(true, info.line, input, Error.init);
            }
        }

        unittest{
            enum dg = {
                assert(getResult!(getCallerLine!())("" ) == result(true, cast(size_t)__LINE__, makeContext("" )));
                assert(getResult!(getCallerLine!())(""w) == result(true, cast(size_t)__LINE__, makeContext(""w)));
                assert(getResult!(getCallerLine!())(""d) == result(true, cast(size_t)__LINE__, makeContext(""d)));
                assert(getResult!(getCallerLine!())(testRange("" )) == result(true, cast(size_t)__LINE__, makeContext(testRange("" ))));
                assert(getResult!(getCallerLine!())(testRange(""w)) == result(true, cast(size_t)__LINE__, makeContext(testRange(""w))));
                assert(getResult!(getCallerLine!())(testRange(""d)) == result(true, cast(size_t)__LINE__, makeContext(testRange(""d))));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // getCallerFile
        template getCallerFile(){
            alias string ResultType;
            static Result!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                return result(true, info.file, input, Error.init);
            }
        }

        unittest{
            enum dg = {
                assert(getResult!(getCallerFile!())("" ) == result(true, __FILE__, makeContext("" )));
                assert(getResult!(getCallerFile!())(""w) == result(true, __FILE__, makeContext(""w)));
                assert(getResult!(getCallerFile!())(""d) == result(true, __FILE__, makeContext(""d)));
                assert(getResult!(getCallerFile!())(testRange("" )) == result(true, __FILE__, makeContext(testRange("" ))));
                assert(getResult!(getCallerFile!())(testRange(""w)) == result(true, __FILE__, makeContext(testRange(""w))));
                assert(getResult!(getCallerFile!())(testRange(""d)) == result(true, __FILE__, makeContext(testRange(""d))));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

// useful parser
    // parseAnyChar
        template parseAnyChar(){
            alias parseCharRange!(dchar.min, dchar.max) parseAnyChar;
        }

        alias parseAnyChar any;

        unittest{
            enum dg = {
                assert(getResult!(parseAnyChar!())("hoge") == result(true, "h", makeContext("oge")));
                assert(getResult!(parseAnyChar!())("\U00012345") == result(true, "\U00012345", makeContext("")));
                assert(getResult!(parseAnyChar!())("\nhoge") == result(true, "\n", makeContext("hoge", 2)));
                assert(getResult!(parseAnyChar!())("") == result(false, "", makeContext(""), Error("any char")));
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
                assert(getResult!(parseSpaces!())("\t \rhoge") == result(true, None.init, makeContext("hoge")));
                assert(getResult!(parseSpaces!())("hoge") == result(true, None.init, makeContext("hoge")));
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
                assert(getResult!(parseIdent!())("hoge") == result(true, "hoge", makeContext("")));
                assert(getResult!(parseIdent!())("_0") == result(true, "_0", makeContext("")));
                assert(getResult!(parseIdent!())("0") == result(false, "", makeContext(""), Error("c: 'A' <= c <= 'Z'")));
                assert(getResult!(parseIdent!())("あ") == result(false, "", makeContext(""), Error("c: 'A' <= c <= 'Z'")));
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
                assert(getResult!(parseStringLiteral!())(`"表が怖い噂のソフト"`) == result(true, `"表が怖い噂のソフト"`, makeContext("")));
                assert(getResult!(parseStringLiteral!())(`r"表が怖い噂のソフト"`) == result(true, `r"表が怖い噂のソフト"`, makeContext("")));
                assert(getResult!(parseStringLiteral!())("`表が怖い噂のソフト`") == result(true, q{`表が怖い噂のソフト`}, makeContext("")));
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
                assert(getResult!(parseIntLiteral!())("3141") == result(true, 3141, makeContext("")));
                assert(getResult!(parseIntLiteral!())("0") == result(true, 0, makeContext("")));
                assert(getResult!(parseIntLiteral!())("0123") == result(true, 0, makeContext("123")));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

string generateParsers(size_t callerLine = __LINE__, string callerFile = __FILE__)(string src){
    return src.parse!(defs, callerLine, callerFile)().value;
}

string getSource(size_t callerLine = __LINE__, string callerFile = __FILE__)(string src){
    return src.getResult!(defs!(), callerLine, callerFile).value;
}

auto getResult(alias fun, size_t callerLine = __LINE__, string callerFile = __FILE__, Range)(Range input, StateType state = StateType.init){
    return fun.parse(Context!Range(input, 1, state), new CallerInfo(callerLine, callerFile));
}

auto parse(alias fun, size_t callerLine = __LINE__, string callerFile = __FILE__, Range)(Range src){
    return src.getResult!(fun!(), callerLine, callerFile)();
}

version(none) auto parse(alias fun, size_t callerLine = __LINE__, string callerFile = __FILE__, Range)(Range src){
    auto result = src.getResult!(fun!(), callerLine, callerFile)();
    if(result.match){
        return result.value;
    }else{
        throw new Exception(result.error.line.to!string() ~ q{: error } ~ result.error.need ~ q{ is needed});
    }
}

bool isMatch(alias fun)(string src){
    return src.getResult!(fun!()).match;
}

// parsers of DSL
    // arch
        template arch(string open, string close){
            alias string ResultType;
            Result!(string, ResultType) parse()(Context!string input, in CallerInfo info){
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
                assert(getResult!(arch!("(", ")"))("(a(i(u)e)o())") == result(true, "(a(i(u)e)o())", makeContext("")));
                assert(getResult!(arch!("[", "]"))("[a[i[u]e]o[]]") == result(true, "[a[i[u]e]o[]]", makeContext("")));
                assert(getResult!(arch!("{", "}"))("{a{i{u}e}o{}}") == result(true, "{a{i{u}e}o{}}", makeContext("")));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // func
        template func(){
            alias string ResultType;
            Result!(string, ResultType) parse()(Context!string input, in CallerInfo info){
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
                auto result = getResult!(func!())(
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
                "}");
                assert(result.match);
                assert(result.rest.empty);
                assert(
                    result.value ==
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
                    "}"
                );
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // nonterminal
        template nonterminal(){
            alias string ResultType;
            version(Issue_8038_Fixed){
                Result!(string, ResultType) parse()(Context!string input, in CallerInfo info){
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
                Result!(string, ResultType) parse()(Context!string input, in CallerInfo info){
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
                assert(getResult!(nonterminal!())("A") == result(true, " #line " ~ toStringNow!__LINE__ ~ "\ncombinateMemoize!(A!())", makeContext(""), Error.init));
                assert(getResult!(nonterminal!())("int") == result(true, " #line " ~ toStringNow!__LINE__ ~ "\ncombinateMemoize!(int!())", makeContext(""), Error.init));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // typeName
        template typeName(){
            alias string ResultType;
            Result!(string, ResultType) parse()(Context!string input, in CallerInfo info){
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
                assert(getResult!(typeName!())("int") == result(true, "int", makeContext(""), Error.init));
                assert(getResult!(typeName!())("Tuple!(string, int)") == result(true, "Tuple!(string, int)", makeContext(""), Error.init));
                assert(getResult!(typeName!())("int[]") == result(true, "int[]", makeContext(""), Error.init));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // id
        template id(){
            alias string ResultType;
            Result!(string, ResultType) parse()(Context!string input, in CallerInfo info){
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
                assert(getResult!(id!())("A") == result(true, "A", makeContext(""), Error.init));
                assert(getResult!(id!())("int") == result(true, "int", makeContext(""), Error.init));
                assert(getResult!(id!())("0") == result(false, "", makeContext(""), Error(`"_"`)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // eofLit
        template eofLit(){
            alias string ResultType;
            Result!(string, ResultType) parse()(Context!string input, in CallerInfo info){
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
                assert(getResult!(eofLit!())("$") == result(true, "parseEOF!()", makeContext(""), Error.init));
                assert(getResult!(eofLit!())("#") == result(false, "", makeContext(""), Error(`"$"`)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // rangeLit
        template rangeLit(){
            alias string ResultType;
            Result!(string, ResultType) parse()(Context!string input, in CallerInfo info){
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
            Result!(string, ResultType) parse()(Context!string input, in CallerInfo info){
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
            Result!(string, ResultType) parse()(Context!string input, in CallerInfo info){
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
                assert(getResult!(rangeLit!())("[a-z]") == result(true, "parseCharRange!('a','z')", makeContext(""), Error.init));
                assert(getResult!(rangeLit!())("[a-zA-Z_]") == result(true, "combinateChoice!(parseCharRange!('a','z'),parseCharRange!('A','Z'),parseString!\"_\"" ")", makeContext(""), Error.init));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // stringLit
        template stringLit(){
            alias string ResultType;
            Result!(string, ResultType) parse()(Context!string input, in CallerInfo info){
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
                assert(getResult!(stringLit!())("\"hello\nworld\" ") == result(true, "parseString!\"hello\nworld\"", makeContext(" ", 2), Error.init));
                assert(getResult!(stringLit!())("aa\"") == result(false, "", makeContext(""), Error(`"""`)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // literal
        template literal(){
            alias string ResultType;
            Result!(string, ResultType) parse()(Context!string input, in CallerInfo info){
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
                assert(getResult!(literal!())("\"hello\nworld\"") == result(true, "combinateMemoize!(parseString!\"hello\nworld\")", makeContext("", 2), Error.init));
                assert(getResult!(literal!())("[a-z]") == result(true, "combinateMemoize!(parseCharRange!('a','z'))", makeContext(""), Error.init));
                assert(getResult!(literal!())("$") == result(true, "combinateMemoize!(parseEOF!())", makeContext(""), Error.init));
                assert(getResult!(literal!())("$", tuple("", "skip!()")) == result(true, "combinateSkip!(combinateMemoize!(parseEOF!()),skip!())", makeContext("", 1, tuple("", "skip!()")), Error.init));
                assert(getResult!(literal!())("表が怖い噂のソフト") == result(false, "", makeContext(""), Error(`"$"`)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // primaryExp
        template primaryExp(){
            alias string ResultType;
            Result!(string, ResultType) parse()(Context!string input, in CallerInfo info){
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
                {
                    auto result = getResult!(primaryExp!())("(&(^$)?)");
                    assert(result.match);
                    assert(result.rest.empty);
                    assert(
                        result.value ==
                        "combinateOption!("
                            "combinateAndPred!("
                                "combinateNotPred!("
                                    "combinateMemoize!(parseEOF!())"
                                ")"
                            ")"
                        ")"
                    );
                }
                assert(getResult!(primaryExp!())("int") == result(true, " #line " ~ toStringNow!__LINE__ ~ "\ncombinateMemoize!(int!())", makeContext(""), Error.init));
                assert(getResult!(primaryExp!())("###このコメントは表示されません###") == result(false, "", makeContext(""), Error(`"("`)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // preExp
        template preExp(){
            alias string ResultType;
            Result!(string, ResultType) parse()(Context!string input, in CallerInfo info){
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
                auto result = getResult!(preExp!())("!$");
                assert(result.match);
                assert(result.rest.empty);
                assert(
                    result.value ==
                    "combinateNone!("
                        "combinateMemoize!(parseEOF!())"
                    ")"
                );
                result = getResult!(preExp!())("!!$");
                assert(result.match);
                assert(result.rest.empty);
                assert(
                    result.value ==
                    "combinateChangeState!("
                        "combinateMemoize!(parseEOF!())"
                    ")"
                );
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // postExp
        template postExp(){
            alias string ResultType;
            Result!(string, ResultType) parse()(Context!string input, in CallerInfo info){
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
                auto result = getResult!(postExp!())("!$*");
                assert(result.match);
                assert(result.rest.empty);
                assert(
                    result.value ==
                    "combinateMore0!("
                        "combinateNone!("
                            "combinateMemoize!(parseEOF!())"
                        ")"
                    ")"
                );
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // optionExp
        template optionExp(){
            alias string ResultType;
            Result!(string, ResultType) parse()(Context!string input, in CallerInfo info){
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
                auto result = getResult!(optionExp!())("(&(^\"hello\"))?");
                assert(result.match);
                assert(result.rest.empty);
                assert(
                    result.value ==
                    "combinateOption!("
                        "combinateAndPred!("
                            "combinateNotPred!("
                                "combinateMemoize!(parseString!\"hello\")"
                            ")"
                        ")"
                    ")"
                );
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // seqExp
        template seqExp(){
            alias string ResultType;
            Result!(string, ResultType) parse()(Context!string input, in CallerInfo info){
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
                {
                    auto result = getResult!(seqExp!())("!$* (&(^$))?");
                    assert(result.match);
                    assert(result.rest.empty);
                    assert(
                        result.value ==
                        "combinateSequence!("
                            "combinateMore0!("
                                "combinateNone!("
                                    "combinateMemoize!(parseEOF!())"
                                ")"
                            "),"
                            "combinateOption!("
                                "combinateAndPred!("
                                    "combinateNotPred!("
                                        "combinateMemoize!(parseEOF!())"
                                    ")"
                                ")"
                            ")"
                        ")"
                    );
                }
                {
                    auto result = getResult!(seqExp!())("!\"hello\" $");
                    assert(result.match);
                    assert(result.rest.empty);
                    assert(
                        result.value ==
                        "combinateSequence!("
                            "combinateNone!("
                                "combinateMemoize!(parseString!\"hello\")"
                            "),"
                            "combinateMemoize!(parseEOF!())"
                        ")"
                    );
                }
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // convExp
        template convExp(){
            alias string ResultType;
            Result!(string, ResultType) parse()(Context!string input, in CallerInfo info){
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
                {
                    auto result = getResult!(convExp!(), __LINE__, `src\ctpg.d`)(q{!"hello" $ >> {return false;}});
                    assert(result.match);
                    assert(result.rest.empty);
                    assert(
                        result.value ==
                        "combinateConvert!(" ~ toStringNow!(__LINE__ - 5) ~ ",`src\\ctpg.d`,"
                            "combinateSequence!("
                                "combinateNone!("
                                    "combinateMemoize!(parseString!\"hello\")"
                                "),"
                                "combinateMemoize!(parseEOF!())"
                            "),"
                            "function(){"
                                "return false;"
                            "}"
                        ")"
                    );
                }
                {
                    auto result = getResult!(convExp!(), __LINE__, `src/ctpg.d`)(q{"hello" >> flat >> to!int});
                    assert(result.match);
                    assert(result.rest.empty);
                    assert(
                        result.value ==
                        "combinateConvert!(" ~ toStringNow!(__LINE__ - 5) ~ ",`src/ctpg.d`,"
                            "combinateConvert!(" ~ toStringNow!(__LINE__ - 6) ~ ",`src/ctpg.d`,"
                                "combinateMemoize!(parseString!\"hello\"),"
                                "flat"
                            "),"
                            "to!int"
                        ")"
                    );
                }
                {
                    auto result = getResult!(convExp!(), __LINE__, `src\ctpg.d`)(q{$ >>> to!string >>? isValid}, tuple("", "skip!()"));
                    assert(result.match);
                    assert(result.rest.empty);
                    assert(result.rest.state == tuple("", "skip!()"));
                    assert(
                        result.value == 
                        "combinateCheck!(" ~ toStringNow!(__LINE__ - 6) ~ r",`src\ctpg.d`,"
                            "combinateConvertWithState!(" ~ toStringNow!(__LINE__ - 7) ~ r",`src\ctpg.d`,"
                                "combinateSkip!(combinateMemoize!(parseEOF!()),skip!()),"
                                "to!string"
                            "),"
                            "isValid"
                        ")"
                    );
                }
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // choiceExp
        template choiceExp(){
            alias string ResultType;
            Result!(string, ResultType) parse()(Context!string input, in CallerInfo info){
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
                {
                    auto result = getResult!(choiceExp!(), __LINE__, `src\ctpg.d`)(`!$* / (&(^"a"))?`);
                    assert(result.match);
                    assert(result.rest.empty);
                    assert(
                        result.value ==
                        "combinateChoice!(" ~ toStringNow!(__LINE__ - 5) ~ ",`src\\ctpg.d`,"
                            "combinateMore0!("
                                "combinateNone!("
                                    "combinateMemoize!(parseEOF!())"
                                ")"
                            "),"
                            "combinateOption!("
                                "combinateAndPred!("
                                    "combinateNotPred!("
                                        "combinateMemoize!(parseString!\"a\")"
                                    ")"
                                ")"
                            ")"
                        ")"
                    );
                }
                {
                    auto result = getResult!(choiceExp!())(`!"hello" $`, tuple("", "skip!()"));
                    assert(result.match);
                    assert(result.rest.empty);
                    assert(result.rest.state == tuple("", "skip!()"));
                    assert(
                        result.value ==
                        "combinateSequence!("
                            "combinateNone!("
                                "combinateSkip!(combinateMemoize!(parseString!\"hello\"),skip!())"
                            "),"
                            "combinateSkip!(combinateMemoize!(parseEOF!()),skip!())"
                        ")"
                    );
                }
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // def
        template def(){
            alias string ResultType;
            Result!(string, ResultType) parse()(Context!string input, in CallerInfo info){
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
                            "static Result!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){"
                                "return "~choiceExp~".parse(input, info);"
                            "}"
                        "}"
                ).parse(input, info);
            }
        }

        unittest{
            enum dg = {
                cast(void)__LINE__;
                {
                    auto result = getResult!(def!(), __LINE__, `src\ctpg.d`)(`@skip(" ") bool hoge = !"hello" $ >> {return false;};`);
                    assert(result.match);
                    assert(result.rest.empty);
                    assert(
                        result.value ==
                        "template hoge(){"
                            "alias bool ResultType;"
                            "static Result!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){"
                                "return combinateConvert!(" ~ toStringNow!(__LINE__ - 8) ~ r",`src\ctpg.d`,"
                                    "combinateSequence!("
                                        "combinateNone!("
                                            "combinateSkip!(combinateMemoize!(parseString!\"hello\"),combinateMemoize!(parseString!\" \"))"
                                        "),"
                                        "combinateSkip!(combinateMemoize!(parseEOF!()),combinateMemoize!(parseString!\" \"))"
                                    "),"
                                    "function(){"
                                        "return false;"
                                    "}"
                                ").parse(input, info);"
                            "}"
                        "}"
                    );
                }
                {
                    auto result = getResult!(def!())(`None recursive = A $;`);
                    assert(result.match);
                    assert(result.rest.empty);
                    assert(
                        result.value ==
                        "template recursive(){"
                            "alias None ResultType;"
                            "static Result!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){"
                                "return combinateSequence!("
                                    " #line " ~ toStringNow!(__LINE__ - 9) ~ "\ncombinateMemoize!(A!()),"
                                    "combinateMemoize!(parseEOF!())"
                                ").parse(input, info);"
                            "}"
                        "}"
                    );
                }
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        };

    // defs
        template defs(){
            alias string ResultType;
            Result!(string, ResultType) parse()(Context!string input, in CallerInfo info){
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
                auto result = getResult!(defs!(), __LINE__, r"src\ctpg.d")(q{
                    @default_skip(" " / "\t" / "\n")
                    bool hoge = !"hello" $ >> {return false;};
                    @skip(" ") Tuple!piyo hoge2 = hoge* >> {return tuple("foo");};
                });
                assert(result.match);
                assert(result.rest.empty);
                assert(
                    result.value ==
                    "template hoge(){"
                        "alias bool ResultType;"
                        "static Result!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){"
                            "return combinateConvert!(" ~ toStringNow!(__LINE__ - 10) ~ r",`src\ctpg.d`,"
                                "combinateSequence!("
                                    "combinateNone!("
                                        "combinateSkip!("
                                            "combinateMemoize!(parseString!\"hello\"),"
                                            "combinateChoice!(" ~ toStringNow!(__LINE__ - 16) ~ r",`src\ctpg.d`,"
                                                "combinateMemoize!(parseString!\" \"),"
                                                "combinateMemoize!(parseString!\"\\t\"),"
                                                "combinateMemoize!(parseString!\"\\n\")"
                                            ")"
                                        ")"
                                    "),"
                                    "combinateSkip!("
                                        "combinateMemoize!(parseEOF!()),"
                                        "combinateChoice!(" ~ toStringNow!(__LINE__ - 25) ~ r",`src\ctpg.d`,"
                                            "combinateMemoize!(parseString!\" \"),"
                                            "combinateMemoize!(parseString!\"\\t\"),"
                                            "combinateMemoize!(parseString!\"\\n\")"
                                        ")"
                                    ")"
                                "),"
                                "function(){"
                                    "return false;"
                                "}"
                            ").parse(input, info);"
                        "}"
                    "}"
                    "template hoge2(){"
                        "alias Tuple!piyo ResultType;"
                        "static Result!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){"
                            "return combinateConvert!(" ~ toStringNow!(__LINE__ - 39) ~ r",`src\ctpg.d`,"
                                "combinateMore0!("
                                    " #line " ~ toStringNow!(__LINE__ - 41) ~ "\ncombinateSkip!(combinateMemoize!(hoge!()),combinateMemoize!(parseString!\" \"))"
                                "),"
                                "function(){"
                                    "return tuple(\"foo\");"
                                "}"
                            ").parse(input, info);"
                        "}"
                    "}"
                );
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        };

