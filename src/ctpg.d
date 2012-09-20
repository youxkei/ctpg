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

alias string StateType;

// struct Context
    struct Context(Range) if(isCharRange!Range){
        Range input;
        size_t line = 1;
        StateType state;

        invariant(){
            assert(line >= 1);
        }

        static if(isForwardRange!Range){
            //cannot apply some qualifiers due to unclearness of R
            @property
            Context save(){
                return Context(input.save, line, state);
            }
        }

        const pure @safe nothrow @property
        bool empty(){
            return input.empty;
        }

        /+ const +/ pure @safe nothrow
        equals_t opEquals(Context rhs){
            return input == rhs.input && line == rhs.line && state == rhs.state;
        }
    }

    struct Context(Range) if(!isCharRange!Range && isInputRange!Range){
        Range input;
        StateType state;

        static if(isForwardRange!Range){
            //cannot apply some qualifiers due to unclearness of R
            @property
            Context save(){
                return Context(input.save, state);
            }
        }

        const pure @safe nothrow @property
        bool empty(){
            return input.empty;
        }

        /+ const +/ pure @safe nothrow
        equals_t opEquals(Context rhs){
            return input == rhs.input && state == rhs.state;
        }
    }

    Context!Range makeContext(Range)(Range range, size_t line = 1){
        return Context!Range(range, line);
    }

// struct Result
    struct Result(Range, T){
        public{
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

            pure @safe nothrow
            bool opEquals(Result lhs){
                return match == lhs.match && value == lhs.value && rest == lhs.rest && error == lhs.error;
            }
        }
    }

    Result!(Range, T) result(Range, T)(bool match, T value, Context!Range rest, Error error = Error.init){
        return Result!(Range, T)(match, value, rest, error);
    }

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
            {
                auto result = flat(tuple(1, "hello", tuple(2, "world")));
                assert(result == "1hello2world");
            }
            {
                auto result = flat(tuple([0, 1, 2], "hello", tuple([3, 4, 5], ["wor", "ld!!"]), ["!", "!"]));
                assert(result == "012hello345world!!!!");
            }
            {
                auto result = flat(tuple('表', 'が', '怖', 'い', '噂', 'の', 'ソ', 'フ', 'ト'));
                assert(result == "表が怖い噂のソフト");
            }
            {
                string[] ary;
                auto result = flat(tuple("A", ary));
                assert(result == "A");
            }
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
            static assert({
                assert(countBreadth("これ\nとこれ") == tuple(6, 1));
                assert(countBreadth("これ\nとこれ\nとさらにこれ") == tuple(13, 2));
                return true;
            }());
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
                    auto result = getResult!(parseString!"hello")([0, 0][]);
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
                    auto result = getResult!(parseCharRange!('\u0100', '\U0010FFFF'))([0, 0][]);
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
                                return result;
                            }
                            case 'U':{
                                result.match = true;
                                result.value = input.input[0..10].to!string();
                                result.rest.input = input.input[10..$];
                                result.rest.line = input.line;
                                return result;
                            }
                            case '\'': case '"': case '?': case '\\': case 'a': case 'b': case 'f': case 'n': case 'r': case 't': case 'v':{
                                result.match = true;
                                result.value = input.input[0..2].to!string();
                                result.rest.input = input.input[2..$];
                                result.rest.line = input.line;
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
                                return result;
                            }
                            case '\'': case '"': case '?': case '\\': case 'a': case 'b': case 'f': case 'n': case 'r': case 't': case 'v':{
                                result.match = true;
                                input.input.popFront;
                                result.value = "\\" ~ to!string(c2);
                                result.rest.input = input.input;
                                result.rest.line = input.line;
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
                    auto result = getResult!(parseSpace!())([0, 0][]);
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
                assert(getResult!(combinateSequence!(parseSpaces!(), getLine!()))("\n\n" ) == result(true, 3LU, makeContext("" , 3)));
                assert(getResult!(combinateSequence!(parseSpaces!(), getLine!()))("\n\n"w) == result(true, 3LU, makeContext(""w, 3)));
                assert(getResult!(combinateSequence!(parseSpaces!(), getLine!()))("\n\n"d) == result(true, 3LU, makeContext(""d, 3)));
                assert(getResult!(combinateSequence!(parseSpaces!(), getLine!()))(testRange("\n\n" )) == result(true, 3LU, makeContext(testRange("" ), 3)));
                assert(getResult!(combinateSequence!(parseSpaces!(), getLine!()))(testRange("\n\n"w)) == result(true, 3LU, makeContext(testRange(""w), 3)));
                assert(getResult!(combinateSequence!(parseSpaces!(), getLine!()))(testRange("\n\n"d)) == result(true, 3LU, makeContext(testRange(""d), 3)));

                try{
                    scope(failure) assert(true);
                    auto result = getResult!(combinateSequence!(parseSpaces!(), getLine!()))([0, 0][]);
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

// combinators
    // combinateMemoize
        template combinateMemoize(alias parser){
            alias ParserType!parser ResultType;
            Result!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                if(!__ctfe){
                    static ResultType[typeof(input)] memo;
                    auto p = input in memo;
                    if(p){
                        return *p;
                    }
                    auto result = parser.parse(input, info);
                    return result;
                }else{
                    return parser.parse(input, info);
                }
            }
        }

    // combinateSkip
        template combinateSkip(alias parser, alias skip){
            alias ParserType!parser ResultType;
            static Result!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                auto r = parser.parse(input, info);
                if(!r.match){
                    return parser.parse(skip.parse(input, info).rest, info);
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
                assert(getResult!(combinateUnTuple!(TestParser!int))("" ) == result(false, 0, makeContext("" )));
                assert(getResult!(combinateUnTuple!(TestParser!int))(""w) == result(false, 0, makeContext(""w)));
                assert(getResult!(combinateUnTuple!(TestParser!int))(""d) == result(false, 0, makeContext(""d)));
                assert(getResult!(combinateUnTuple!(TestParser!int))(testRange("" )) == result(false, 0, makeContext(testRange("" ))));
                assert(getResult!(combinateUnTuple!(TestParser!int))(testRange(""w)) == result(false, 0, makeContext(testRange(""w))));
                assert(getResult!(combinateUnTuple!(TestParser!int))(testRange(""d)) == result(false, 0, makeContext(testRange(""d))));

                assert(getResult!(combinateUnTuple!(TestParser!long))("" ) == result(false, 0L, makeContext("" )));
                assert(getResult!(combinateUnTuple!(TestParser!long))(""w) == result(false, 0L, makeContext(""w)));
                assert(getResult!(combinateUnTuple!(TestParser!long))(""d) == result(false, 0L, makeContext(""d)));
                assert(getResult!(combinateUnTuple!(TestParser!long))(testRange("" )) == result(false, 0L, makeContext(testRange("" ))));
                assert(getResult!(combinateUnTuple!(TestParser!long))(testRange(""w)) == result(false, 0L, makeContext(testRange(""w))));
                assert(getResult!(combinateUnTuple!(TestParser!long))(testRange(""d)) == result(false, 0L, makeContext(testRange(""d))));

                assert(getResult!(combinateUnTuple!(TestParser!string))("" ) == result(false, "", makeContext("" )));
                assert(getResult!(combinateUnTuple!(TestParser!string))(""w) == result(false, "", makeContext(""w)));
                assert(getResult!(combinateUnTuple!(TestParser!string))(""d) == result(false, "", makeContext(""d)));
                assert(getResult!(combinateUnTuple!(TestParser!string))(testRange("" )) == result(false, "", makeContext(testRange("" ))));
                assert(getResult!(combinateUnTuple!(TestParser!string))(testRange(""w)) == result(false, "", makeContext(testRange(""w))));
                assert(getResult!(combinateUnTuple!(TestParser!string))(testRange(""d)) == result(false, "", makeContext(testRange(""d))));

                assert(getResult!(combinateUnTuple!(TestParser!wstring))("" ) == result(false, ""w, makeContext("" )));
                assert(getResult!(combinateUnTuple!(TestParser!wstring))(""w) == result(false, ""w, makeContext(""w)));
                assert(getResult!(combinateUnTuple!(TestParser!wstring))(""d) == result(false, ""w, makeContext(""d)));
                assert(getResult!(combinateUnTuple!(TestParser!wstring))(testRange("" )) == result(false, ""w, makeContext(testRange("" ))));
                assert(getResult!(combinateUnTuple!(TestParser!wstring))(testRange(""w)) == result(false, ""w, makeContext(testRange(""w))));
                assert(getResult!(combinateUnTuple!(TestParser!wstring))(testRange(""d)) == result(false, ""w, makeContext(testRange(""d))));

                assert(getResult!(combinateUnTuple!(TestParser!dstring))("" ) == result(false, ""d, makeContext("" )));
                assert(getResult!(combinateUnTuple!(TestParser!dstring))(""w) == result(false, ""d, makeContext(""w)));
                assert(getResult!(combinateUnTuple!(TestParser!dstring))(""d) == result(false, ""d, makeContext(""d)));
                assert(getResult!(combinateUnTuple!(TestParser!dstring))(testRange("" )) == result(false, ""d, makeContext(testRange("" ))));
                assert(getResult!(combinateUnTuple!(TestParser!dstring))(testRange(""w)) == result(false, ""d, makeContext(testRange(""w))));
                assert(getResult!(combinateUnTuple!(TestParser!dstring))(testRange(""d)) == result(false, ""d, makeContext(testRange(""d))));

                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!int)))("" ) == result(false, 0, makeContext("" )));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!int)))(""w) == result(false, 0, makeContext(""w)));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!int)))(""d) == result(false, 0, makeContext(""d)));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!int)))(testRange("" )) == result(false, 0, makeContext(testRange("" ))));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!int)))(testRange(""w)) == result(false, 0, makeContext(testRange(""w))));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!int)))(testRange(""d)) == result(false, 0, makeContext(testRange(""d))));

                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(int, int))))("" ) == result(false, tuple(0, 0), makeContext("" )));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(int, int))))(""w) == result(false, tuple(0, 0), makeContext(""w)));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(int, int))))(""d) == result(false, tuple(0, 0), makeContext(""d)));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(int, int))))(testRange("" )) == result(false, tuple(0, 0), makeContext(testRange("" ))));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(int, int))))(testRange(""w)) == result(false, tuple(0, 0), makeContext(testRange(""w))));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(int, int))))(testRange(""d)) == result(false, tuple(0, 0), makeContext(testRange(""d))));

                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!int))))("" ) == result(false, tuple(0), makeContext("" )));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!int))))(""w) == result(false, tuple(0), makeContext(""w)));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!int))))(""d) == result(false, tuple(0), makeContext(""d)));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!int))))(testRange("" )) == result(false, tuple(0), makeContext(testRange("" ))));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!int))))(testRange(""w)) == result(false, tuple(0), makeContext(testRange(""w))));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!int))))(testRange(""d)) == result(false, tuple(0), makeContext(testRange(""d))));

                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!(int, int)))))("" ) == result(false, tuple(0, 0), makeContext("" )));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!(int, int)))))(""w) == result(false, tuple(0, 0), makeContext(""w)));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!(int, int)))))(""d) == result(false, tuple(0, 0), makeContext(""d)));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!(int, int)))))(testRange("" )) == result(false, tuple(0, 0), makeContext(testRange("" ))));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!(int, int)))))(testRange(""w)) == result(false, tuple(0, 0), makeContext(testRange(""w))));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!(int, int)))))(testRange(""d)) == result(false, tuple(0, 0), makeContext(testRange(""d))));

                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!(int, int), int))))("" ) == result(false, tuple(tuple(0, 0), 0), makeContext("" )));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!(int, int), int))))(""w) == result(false, tuple(tuple(0, 0), 0), makeContext(""w)));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!(int, int), int))))(""d) == result(false, tuple(tuple(0, 0), 0), makeContext(""d)));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!(int, int), int))))(testRange("" )) == result(false, tuple(tuple(0, 0), 0), makeContext(testRange("" ))));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!(int, int), int))))(testRange(""w)) == result(false, tuple(tuple(0, 0), 0), makeContext(testRange(""w))));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!(int, int), int))))(testRange(""d)) == result(false, tuple(tuple(0, 0), 0), makeContext(testRange(""d))));
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
                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))("helloworld" ) == result(true, tuple("hello", "world"), makeContext("" )));
                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))("helloworld"w) == result(true, tuple("hello", "world"), makeContext(""w)));
                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))("helloworld"d) == result(true, tuple("hello", "world"), makeContext(""d)));
                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))(testRange("helloworld" )) == result(true, tuple("hello", "world"), makeContext(testRange("" ))));
                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))(testRange("helloworld"w)) == result(true, tuple("hello", "world"), makeContext(testRange(""w))));
                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))(testRange("helloworld"d)) == result(true, tuple("hello", "world"), makeContext(testRange(""d))));

                assert(getResult!(combinateSequence!(combinateSequence!(parseString!("hello"), parseString!("world")), parseString!"!"))("helloworld!" ) == result(true, tuple("hello", "world", "!"), makeContext("" )));
                assert(getResult!(combinateSequence!(combinateSequence!(parseString!("hello"), parseString!("world")), parseString!"!"))("helloworld!"w) == result(true, tuple("hello", "world", "!"), makeContext(""w)));
                assert(getResult!(combinateSequence!(combinateSequence!(parseString!("hello"), parseString!("world")), parseString!"!"))("helloworld!"d) == result(true, tuple("hello", "world", "!"), makeContext(""d)));
                assert(getResult!(combinateSequence!(combinateSequence!(parseString!("hello"), parseString!("world")), parseString!"!"))(testRange("helloworld!" )) == result(true, tuple("hello", "world", "!"), makeContext(testRange("" ))));
                assert(getResult!(combinateSequence!(combinateSequence!(parseString!("hello"), parseString!("world")), parseString!"!"))(testRange("helloworld!"w)) == result(true, tuple("hello", "world", "!"), makeContext(testRange(""w))));
                assert(getResult!(combinateSequence!(combinateSequence!(parseString!("hello"), parseString!("world")), parseString!"!"))(testRange("helloworld!"d)) == result(true, tuple("hello", "world", "!"), makeContext(testRange(""d))));

                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))("hellovvorld" ) == result(false, tuple("", ""), makeContext("" ), Error(q{"world"})));
                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))("hellovvorld"w) == result(false, tuple("", ""), makeContext(""w), Error(q{"world"})));
                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))("hellovvorld"d) == result(false, tuple("", ""), makeContext(""d), Error(q{"world"})));
                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))(testRange("hellovvorld" )) == result(false, tuple("", ""), makeContext(testRange("" )), Error(q{"world"})));
                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))(testRange("hellovvorld"w)) == result(false, tuple("", ""), makeContext(testRange(""w)), Error(q{"world"})));
                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))(testRange("hellovvorld"d)) == result(false, tuple("", ""), makeContext(testRange(""d)), Error(q{"world"})));

                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world"), parseString!("!")))("helloworld?" ) == result(false, tuple("", "", ""), makeContext("" ), Error(q{"!"})));
                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world"), parseString!("!")))("helloworld?"w) == result(false, tuple("", "", ""), makeContext(""w), Error(q{"!"})));
                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world"), parseString!("!")))("helloworld?"d) == result(false, tuple("", "", ""), makeContext(""d), Error(q{"!"})));
                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world"), parseString!("!")))(testRange("helloworld?" )) == result(false, tuple("", "", ""), makeContext(testRange("" )), Error(q{"!"})));
                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world"), parseString!("!")))(testRange("helloworld?"w)) == result(false, tuple("", "", ""), makeContext(testRange(""w)), Error(q{"!"})));
                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world"), parseString!("!")))(testRange("helloworld?"d)) == result(false, tuple("", "", ""), makeContext(testRange(""d)), Error(q{"!"})));
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
                static if(isForwardRange!R){
                    static if(parsers.length == 1){
                        return parsers[0].parse(input, info);
                    }else{
                        auto r = parsers[0].parse(input.save, info);
                        if(r.match){
                            return r;
                        }
                        return combinateChoice!(parsers[1..$]).parse(input, info);
                    }
                }else{
                    throw new Exception("");
                }
            }
        }

        unittest{
            enum dg = {
                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))("hw" ) == result(true, "h", makeContext("w" ))); 
                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))("hw"w) == result(true, "h", makeContext("w"w))); 
                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))("hw"d) == result(true, "h", makeContext("w"d))); 
                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))(testRange("hw" )) == result(true, "h", makeContext(testRange("w" )))); 
                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))(testRange("hw"w)) == result(true, "h", makeContext(testRange("w"w)))); 
                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))(testRange("hw"d)) == result(true, "h", makeContext(testRange("w"d)))); 

                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))("w" ) == result(true, "w", makeContext("" )));
                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))("w"w) == result(true, "w", makeContext(""w)));
                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))("w"d) == result(true, "w", makeContext(""d)));
                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))(testRange("w" )) == result(true, "w", makeContext(testRange("" ))));
                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))(testRange("w"w)) == result(true, "w", makeContext(testRange(""w))));
                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))(testRange("w"d)) == result(true, "w", makeContext(testRange(""d))));

                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))("" ) == result(false, "", makeContext("" ), Error(q{"w"})));
                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))(""w) == result(false, "", makeContext(""w), Error(q{"w"})));
                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))(""d) == result(false, "", makeContext(""d), Error(q{"w"})));
                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))(testRange("" )) == result(false, "", makeContext(testRange("" )), Error(q{"w"})));
                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))(testRange(""w)) == result(false, "", makeContext(testRange(""w)), Error(q{"w"})));
                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))(testRange(""d)) == result(false, "", makeContext(testRange(""d)), Error(q{"w"})));

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
                static if(isForwardRange!R){
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
                }else{
                    throw new Exception("");
                }
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
                assert(getResult!(combinateConvert!(combinateMore0!(parseString!"w"), flat))("www w" ) == result(true, "www", makeContext(" w" )));
                assert(getResult!(combinateConvert!(combinateMore0!(parseString!"w"), flat))("www w"w) == result(true, "www", makeContext(" w"w)));
                assert(getResult!(combinateConvert!(combinateMore0!(parseString!"w"), flat))("www w"d) == result(true, "www", makeContext(" w"d)));
                assert(getResult!(combinateConvert!(combinateMore0!(parseString!"w"), flat))(testRange("www w" )) == result(true, "www", makeContext(testRange(" w" ))));
                assert(getResult!(combinateConvert!(combinateMore0!(parseString!"w"), flat))(testRange("www w"w)) == result(true, "www", makeContext(testRange(" w"w))));
                assert(getResult!(combinateConvert!(combinateMore0!(parseString!"w"), flat))(testRange("www w"d)) == result(true, "www", makeContext(testRange(" w"d))));

                assert(getResult!(combinateConvert!(combinateMore0!(parseString!"w"), flat))(" w" ) == result(true, "", makeContext(" w" )));
                assert(getResult!(combinateConvert!(combinateMore0!(parseString!"w"), flat))(" w"w) == result(true, "", makeContext(" w"w)));
                assert(getResult!(combinateConvert!(combinateMore0!(parseString!"w"), flat))(" w"d) == result(true, "", makeContext(" w"d)));
                assert(getResult!(combinateConvert!(combinateMore0!(parseString!"w"), flat))(testRange(" w" )) == result(true, "", makeContext(testRange(" w" ))));
                assert(getResult!(combinateConvert!(combinateMore0!(parseString!"w"), flat))(testRange(" w"w)) == result(true, "", makeContext(testRange(" w"w))));
                assert(getResult!(combinateConvert!(combinateMore0!(parseString!"w"), flat))(testRange(" w"d)) == result(true, "", makeContext(testRange(" w"d))));

                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), flat))("www w" ) == result(true, "www", makeContext(" w" )));
                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), flat))("www w"w) == result(true, "www", makeContext(" w"w)));
                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), flat))("www w"d) == result(true, "www", makeContext(" w"d)));
                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), flat))(testRange("www w" )) == result(true, "www", makeContext(testRange(" w" ))));
                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), flat))(testRange("www w"w)) == result(true, "www", makeContext(testRange(" w"w))));
                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), flat))(testRange("www w"d)) == result(true, "www", makeContext(testRange(" w"d))));

                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), flat))(" w" ) == result(false, "", makeContext("" ), Error(q{"w"})));
                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), flat))(" w"w) == result(false, "", makeContext(""w), Error(q{"w"})));
                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), flat))(" w"d) == result(false, "", makeContext(""d), Error(q{"w"})));
                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), flat))(testRange(" w" )) == result(false, "", makeContext(testRange("" )), Error(q{"w"})));
                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), flat))(testRange(" w"w)) == result(false, "", makeContext(testRange(""w)), Error(q{"w"})));
                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), flat))(testRange(" w"d)) == result(false, "", makeContext(testRange(""d)), Error(q{"w"})));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // combinateOption
        template combinateOption(alias parser){
            alias Option!(ParserType!parser) ResultType;
            static Result!(R, ResultType) parse(R)(Context!R input, in CallerInfo info){
                static if(isForwardRange!R){
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
                }else{
                    throw new Exception("");
                }
            }
        }

        unittest{
            enum dg = {
                assert(getResult!(combinateOption!(parseString!"w"))("w" ) == result(true, makeOption(true, "w"), makeContext("" )));
                assert(getResult!(combinateOption!(parseString!"w"))("w"w) == result(true, makeOption(true, "w"), makeContext(""w)));
                assert(getResult!(combinateOption!(parseString!"w"))("w"d) == result(true, makeOption(true, "w"), makeContext(""d)));
                assert(getResult!(combinateOption!(parseString!"w"))(testRange("w" )) == result(true, makeOption(true, "w"), makeContext(testRange("" ))));
                assert(getResult!(combinateOption!(parseString!"w"))(testRange("w"w)) == result(true, makeOption(true, "w"), makeContext(testRange(""w))));
                assert(getResult!(combinateOption!(parseString!"w"))(testRange("w"d)) == result(true, makeOption(true, "w"), makeContext(testRange(""d))));

                assert(getResult!(combinateOption!(parseString!"w"))("hoge" ) == result(true, makeOption(false, ""), makeContext("hoge" )));
                assert(getResult!(combinateOption!(parseString!"w"))("hoge"w) == result(true, makeOption(false, ""), makeContext("hoge"w)));
                assert(getResult!(combinateOption!(parseString!"w"))("hoge"d) == result(true, makeOption(false, ""), makeContext("hoge"d)));
                assert(getResult!(combinateOption!(parseString!"w"))(testRange("hoge" )) == result(true, makeOption(false, ""), makeContext(testRange("hoge" ))));
                assert(getResult!(combinateOption!(parseString!"w"))(testRange("hoge"w)) == result(true, makeOption(false, ""), makeContext(testRange("hoge"w))));
                assert(getResult!(combinateOption!(parseString!"w"))(testRange("hoge"d)) == result(true, makeOption(false, ""), makeContext(testRange("hoge"d))));
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
                assert(getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))("(w)" ) == result(true, "w", makeContext("" )));
                assert(getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))("(w)"w) == result(true, "w", makeContext(""w)));
                assert(getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))("(w)"d) == result(true, "w", makeContext(""d)));
                assert(getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))(testRange("(w)" )) == result(true, "w", makeContext(testRange("" ))));
                assert(getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))(testRange("(w)"w)) == result(true, "w", makeContext(testRange(""w))));
                assert(getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))(testRange("(w)"d)) == result(true, "w", makeContext(testRange(""d))));

                assert(getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))("(w}" ) == result(false, "", makeContext("" ), Error(q{")"})));
                assert(getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))("(w}"w) == result(false, "", makeContext(""w), Error(q{")"})));
                assert(getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))("(w}"d) == result(false, "", makeContext(""d), Error(q{")"})));
                assert(getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))(testRange("(w}" )) == result(false, "", makeContext(testRange("" )), Error(q{")"})));
                assert(getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))(testRange("(w}"w)) == result(false, "", makeContext(testRange(""w)), Error(q{")"})));
                assert(getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))(testRange("(w}"d)) == result(false, "", makeContext(testRange(""d)), Error(q{")"})));

                assert(getResult!(combinateNone!(parseString!"w"))("a" ) == result(false, None.init, makeContext("" ), Error(q{"w"})));
                assert(getResult!(combinateNone!(parseString!"w"))("a"w) == result(false, None.init, makeContext(""w), Error(q{"w"})));
                assert(getResult!(combinateNone!(parseString!"w"))("a"d) == result(false, None.init, makeContext(""d), Error(q{"w"})));
                assert(getResult!(combinateNone!(parseString!"w"))(testRange("a" )) == result(false, None.init, makeContext(testRange("" )), Error(q{"w"})));
                assert(getResult!(combinateNone!(parseString!"w"))(testRange("a"w)) == result(false, None.init, makeContext(testRange(""w)), Error(q{"w"})));
                assert(getResult!(combinateNone!(parseString!"w"))(testRange("a"d)) == result(false, None.init, makeContext(testRange(""d)), Error(q{"w"})));
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
                assert(getResult!(combinateAndPred!(parseString!"w"))("www" ) == result(true, None.init, makeContext("www" )));
                assert(getResult!(combinateAndPred!(parseString!"w"))("www"w) == result(true, None.init, makeContext("www"w)));
                assert(getResult!(combinateAndPred!(parseString!"w"))("www"d) == result(true, None.init, makeContext("www"d)));
                assert(getResult!(combinateAndPred!(parseString!"w"))(testRange("www" )) == result(true, None.init, makeContext(testRange("www" ))));
                assert(getResult!(combinateAndPred!(parseString!"w"))(testRange("www"w)) == result(true, None.init, makeContext(testRange("www"w))));
                assert(getResult!(combinateAndPred!(parseString!"w"))(testRange("www"d)) == result(true, None.init, makeContext(testRange("www"d))));

                assert(getResult!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w")))("www" ) == result(true, "w", makeContext("ww" )));
                assert(getResult!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w")))("www"w) == result(true, "w", makeContext("ww"w)));
                assert(getResult!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w")))("www"d) == result(true, "w", makeContext("ww"d)));
                assert(getResult!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w")))(testRange("www" )) == result(true, "w", makeContext(testRange("ww" ))));
                assert(getResult!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w")))(testRange("www"w)) == result(true, "w", makeContext(testRange("ww"w))));
                assert(getResult!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w")))(testRange("www"d)) == result(true, "w", makeContext(testRange("ww"d))));

                assert(getResult!(combinateConvert!(combinateMore1!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w"))), flat))("www" ) == result(true, "ww", makeContext("w" )));
                assert(getResult!(combinateConvert!(combinateMore1!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w"))), flat))("www"w) == result(true, "ww", makeContext("w"w)));
                assert(getResult!(combinateConvert!(combinateMore1!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w"))), flat))("www"d) == result(true, "ww", makeContext("w"d)));
                assert(getResult!(combinateConvert!(combinateMore1!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w"))), flat))(testRange("www" )) == result(true, "ww", makeContext(testRange("w" ))));
                assert(getResult!(combinateConvert!(combinateMore1!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w"))), flat))(testRange("www"w)) == result(true, "ww", makeContext(testRange("w"w))));
                assert(getResult!(combinateConvert!(combinateMore1!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w"))), flat))(testRange("www"d)) == result(true, "ww", makeContext(testRange("w"d))));

                assert(getResult!(combinateConvert!(combinateMore1!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w"))), flat))("w" ) == result(false, "", makeContext("" ), Error(q{"w"})));
                assert(getResult!(combinateConvert!(combinateMore1!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w"))), flat))("w"w) == result(false, "", makeContext(""w), Error(q{"w"})));
                assert(getResult!(combinateConvert!(combinateMore1!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w"))), flat))("w"d) == result(false, "", makeContext(""d), Error(q{"w"})));
                assert(getResult!(combinateConvert!(combinateMore1!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w"))), flat))(testRange("w" )) == result(false, "", makeContext(testRange("" )), Error(q{"w"})));
                assert(getResult!(combinateConvert!(combinateMore1!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w"))), flat))(testRange("w"w)) == result(false, "", makeContext(testRange(""w)), Error(q{"w"})));
                assert(getResult!(combinateConvert!(combinateMore1!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w"))), flat))(testRange("w"d)) == result(false, "", makeContext(testRange(""d)), Error(q{"w"})));
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
                assert(getResult!(combinateConvert!(combinateMore1!(combinateSequence!(parseString!"w", combinateNotPred!(parseString!"s"))), flat))("wwws" ) == result(true, "ww", makeContext("ws" )));
                assert(getResult!(combinateConvert!(combinateMore1!(combinateSequence!(parseString!"w", combinateNotPred!(parseString!"s"))), flat))("wwws"w) == result(true, "ww", makeContext("ws"w)));
                assert(getResult!(combinateConvert!(combinateMore1!(combinateSequence!(parseString!"w", combinateNotPred!(parseString!"s"))), flat))("wwws"d) == result(true, "ww", makeContext("ws"d)));
                assert(getResult!(combinateConvert!(combinateMore1!(combinateSequence!(parseString!"w", combinateNotPred!(parseString!"s"))), flat))(testRange("wwws" )) == result(true, "ww", makeContext(testRange("ws" ))));
                assert(getResult!(combinateConvert!(combinateMore1!(combinateSequence!(parseString!"w", combinateNotPred!(parseString!"s"))), flat))(testRange("wwws"w)) == result(true, "ww", makeContext(testRange("ws"w))));
                assert(getResult!(combinateConvert!(combinateMore1!(combinateSequence!(parseString!"w", combinateNotPred!(parseString!"s"))), flat))(testRange("wwws"d)) == result(true, "ww", makeContext(testRange("ws"d))));
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
                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), function(string[] ws){ return ws.length; }))("www" ) == result(true, 3LU, makeContext("" )));
                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), function(string[] ws){ return ws.length; }))(testRange("www" )) == result(true, 3LU, makeContext(testRange("" ))));

                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), function(string[] ws){ return ws.length; }))("a" ) == result(false, 0LU, makeContext("" ), Error(q{"w"})));
                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), function(string[] ws){ return ws.length; }))(testRange("a" )) == result(false, 0LU, makeContext(testRange("" )), Error(q{"w"})));

                //assert(getResult!(combinateConvert!(10, "hoge/fuga.d", combinateMore1!(parseString!"w"), function(string ws){ return ws.length; }))(testRange("a" )) == result(false, 0LU, makeContext(testRange("" )), Error(q{"w"})));
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
                assert(getResult!(combinateConvertWithState!(combinateMore1!(parseString!"w"), function(string[] ws, StateType state){ return ws.length; }))("www" ) == result(true, 3LU, makeContext("" )));
                assert(getResult!(combinateConvertWithState!(combinateMore1!(parseString!"w"), function(string[] ws, StateType state){ return ws.length; }))(testRange("www" )) == result(true, 3LU, makeContext(testRange("" ))));

                assert(getResult!(combinateConvertWithState!(combinateMore1!(parseString!"w"), function(string[] ws, StateType state){ return ws.length; }))("a" ) == result(false, 0LU, makeContext("" ), Error(q{"w"})));
                assert(getResult!(combinateConvertWithState!(combinateMore1!(parseString!"w"), function(string[] ws, StateType state){ return ws.length; }))(testRange("a" )) == result(false, 0LU, makeContext(testRange("" )), Error(q{"w"})));
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
                assert(getResult!(combinateConvert!(combinateCheck!(combinateMore0!(parseString!"w"), function(string[] ws){ return ws.length == 5; }), flat))("wwwww" ) == result(true, "wwwww", makeContext("" )));
                assert(getResult!(combinateConvert!(combinateCheck!(combinateMore0!(parseString!"w"), function(string[] ws){ return ws.length == 5; }), flat))(testRange("wwwww" )) == result(true, "wwwww", makeContext(testRange("" ))));

                assert(getResult!(combinateConvert!(combinateCheck!(combinateMore0!(parseString!"w"), function(string[] ws){ return ws.length == 5; }), flat))("wwww" ) == result(false, "", makeContext("" ), Error("passing check")));
                assert(getResult!(combinateConvert!(combinateCheck!(combinateMore0!(parseString!"w"), function(string[] ws){ return ws.length == 5; }), flat))(testRange("wwww" )) == result(false, "", makeContext(testRange("" )), Error("passing check")));
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

        unittest{
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

// useful parser
    // parseAnyChar
        template parseAnyChar(){
            alias parseCharRange!(dchar.min, dchar.max) parseAnyChar;
        }

        alias parseAnyChar any;

        unittest{
            enum dg = {
                assert(getResult!(parseAnyChar!())("hoge" ) == result(true, "h", makeContext("oge" )));
                assert(getResult!(parseAnyChar!())("hoge"w) == result(true, "h", makeContext("oge"w)));
                assert(getResult!(parseAnyChar!())("hoge"d) == result(true, "h", makeContext("oge"d)));
                assert(getResult!(parseAnyChar!())(testRange("hoge" )) == result(true, "h", makeContext(testRange("oge" ))));
                assert(getResult!(parseAnyChar!())(testRange("hoge"w)) == result(true, "h", makeContext(testRange("oge"w))));
                assert(getResult!(parseAnyChar!())(testRange("hoge"d)) == result(true, "h", makeContext(testRange("oge"d))));

                assert(getResult!(parseAnyChar!())("\U00012345" ) == result(true, "\U00012345", makeContext("" )));
                assert(getResult!(parseAnyChar!())("\U00012345"w) == result(true, "\U00012345", makeContext(""w)));
                assert(getResult!(parseAnyChar!())("\U00012345"d) == result(true, "\U00012345", makeContext(""d)));
                assert(getResult!(parseAnyChar!())(testRange("\U00012345" )) == result(true, "\U00012345", makeContext(testRange("" ))));
                assert(getResult!(parseAnyChar!())(testRange("\U00012345"w)) == result(true, "\U00012345", makeContext(testRange(""w))));
                assert(getResult!(parseAnyChar!())(testRange("\U00012345"d)) == result(true, "\U00012345", makeContext(testRange(""d))));

                assert(getResult!(parseAnyChar!())("\nhoge" ) == result(true, "\n", makeContext("hoge" , 2)));
                assert(getResult!(parseAnyChar!())("\nhoge"w) == result(true, "\n", makeContext("hoge"w, 2)));
                assert(getResult!(parseAnyChar!())("\nhoge"d) == result(true, "\n", makeContext("hoge"d, 2)));
                assert(getResult!(parseAnyChar!())(testRange("\nhoge" )) == result(true, "\n", makeContext(testRange("hoge" ), 2)));
                assert(getResult!(parseAnyChar!())(testRange("\nhoge"w)) == result(true, "\n", makeContext(testRange("hoge"w), 2)));
                assert(getResult!(parseAnyChar!())(testRange("\nhoge"d)) == result(true, "\n", makeContext(testRange("hoge"d), 2)));

                assert(getResult!(parseAnyChar!())("" ) == result(false, "", makeContext("" ), Error("any char")));
                assert(getResult!(parseAnyChar!())(""w) == result(false, "", makeContext(""w), Error("any char")));
                assert(getResult!(parseAnyChar!())(""d) == result(false, "", makeContext(""d), Error("any char")));
                assert(getResult!(parseAnyChar!())(testRange("" )) == result(false, "", makeContext(testRange("" )), Error("any char")));
                assert(getResult!(parseAnyChar!())(testRange(""w)) == result(false, "", makeContext(testRange(""w)), Error("any char")));
                assert(getResult!(parseAnyChar!())(testRange(""d)) == result(false, "", makeContext(testRange(""d)), Error("any char")));
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

        unittest{
            static assert(is(parseSpaces!().ResultType));
            enum dg = {
                assert(getResult!(parseSpaces!())("\t \rhoge" ) == result(true, None.init, makeContext("hoge" )));
                assert(getResult!(parseSpaces!())("\t \rhoge"w) == result(true, None.init, makeContext("hoge"w)));
                assert(getResult!(parseSpaces!())("\t \rhoge"d) == result(true, None.init, makeContext("hoge"d)));
                assert(getResult!(parseSpaces!())(testRange("\t \rhoge" )) == result(true, None.init, makeContext(testRange("hoge" ))));
                assert(getResult!(parseSpaces!())(testRange("\t \rhoge"w)) == result(true, None.init, makeContext(testRange("hoge"w))));
                assert(getResult!(parseSpaces!())(testRange("\t \rhoge"d)) == result(true, None.init, makeContext(testRange("hoge"d))));

                assert(getResult!(parseSpaces!())("hoge" ) == result(true, None.init, makeContext("hoge" )));
                assert(getResult!(parseSpaces!())("hoge"w) == result(true, None.init, makeContext("hoge"w)));
                assert(getResult!(parseSpaces!())("hoge"d) == result(true, None.init, makeContext("hoge"d)));
                assert(getResult!(parseSpaces!())(testRange("hoge" )) == result(true, None.init, makeContext(testRange("hoge" ))));
                assert(getResult!(parseSpaces!())(testRange("hoge"w)) == result(true, None.init, makeContext(testRange("hoge"w))));
                assert(getResult!(parseSpaces!())(testRange("hoge"d)) == result(true, None.init, makeContext(testRange("hoge"d))));
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
                assert(getResult!(parseIdent!())("hoge" ) == result(true, "hoge", makeContext("" )));
                assert(getResult!(parseIdent!())("hoge"w) == result(true, "hoge", makeContext(""w)));
                assert(getResult!(parseIdent!())("hoge"d) == result(true, "hoge", makeContext(""d)));
                assert(getResult!(parseIdent!())(testRange("hoge" )) == result(true, "hoge", makeContext(testRange("" ))));
                assert(getResult!(parseIdent!())(testRange("hoge"w)) == result(true, "hoge", makeContext(testRange(""w))));
                assert(getResult!(parseIdent!())(testRange("hoge"d)) == result(true, "hoge", makeContext(testRange(""d))));

                assert(getResult!(parseIdent!())("_0" ) == result(true, "_0", makeContext("" )));
                assert(getResult!(parseIdent!())("_0"w) == result(true, "_0", makeContext(""w)));
                assert(getResult!(parseIdent!())("_0"d) == result(true, "_0", makeContext(""d)));
                assert(getResult!(parseIdent!())(testRange("_0" )) == result(true, "_0", makeContext(testRange("" ))));
                assert(getResult!(parseIdent!())(testRange("_0"w)) == result(true, "_0", makeContext(testRange(""w))));
                assert(getResult!(parseIdent!())(testRange("_0"d)) == result(true, "_0", makeContext(testRange(""d))));

                assert(getResult!(parseIdent!())("0" ) == result(false, "", makeContext("" ), Error("c: 'A' <= c <= 'Z'")));
                assert(getResult!(parseIdent!())("0"w) == result(false, "", makeContext(""w), Error("c: 'A' <= c <= 'Z'")));
                assert(getResult!(parseIdent!())("0"d) == result(false, "", makeContext(""d), Error("c: 'A' <= c <= 'Z'")));
                assert(getResult!(parseIdent!())(testRange("0" )) == result(false, "", makeContext(testRange("" )), Error("c: 'A' <= c <= 'Z'")));
                assert(getResult!(parseIdent!())(testRange("0"w)) == result(false, "", makeContext(testRange(""w)), Error("c: 'A' <= c <= 'Z'")));
                assert(getResult!(parseIdent!())(testRange("0"d)) == result(false, "", makeContext(testRange(""d)), Error("c: 'A' <= c <= 'Z'")));

                assert(getResult!(parseIdent!())("あ" ) == result(false, "", makeContext("" ), Error("c: 'A' <= c <= 'Z'")));
                assert(getResult!(parseIdent!())("あ"w) == result(false, "", makeContext(""w), Error("c: 'A' <= c <= 'Z'")));
                assert(getResult!(parseIdent!())("あ"d) == result(false, "", makeContext(""d), Error("c: 'A' <= c <= 'Z'")));
                assert(getResult!(parseIdent!())(testRange("あ" )) == result(false, "", makeContext(testRange("" )), Error("c: 'A' <= c <= 'Z'")));
                assert(getResult!(parseIdent!())(testRange("あ"w)) == result(false, "", makeContext(testRange(""w)), Error("c: 'A' <= c <= 'Z'")));
                assert(getResult!(parseIdent!())(testRange("あ"d)) == result(false, "", makeContext(testRange(""d)), Error("c: 'A' <= c <= 'Z'")));
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
                assert(getResult!(parseStringLiteral!())(`"表が怖い噂のソフト"` ) == result(true, `"表が怖い噂のソフト"`, makeContext("" )));
                assert(getResult!(parseStringLiteral!())(`"表が怖い噂のソフト"`w) == result(true, `"表が怖い噂のソフト"`, makeContext(""w)));
                assert(getResult!(parseStringLiteral!())(`"表が怖い噂のソフト"`d) == result(true, `"表が怖い噂のソフト"`, makeContext(""d)));
                assert(getResult!(parseStringLiteral!())(testRange(`"表が怖い噂のソフト"` )) == result(true, `"表が怖い噂のソフト"`, makeContext(testRange("" ))));
                assert(getResult!(parseStringLiteral!())(testRange(`"表が怖い噂のソフト"`w)) == result(true, `"表が怖い噂のソフト"`, makeContext(testRange(""w))));
                assert(getResult!(parseStringLiteral!())(testRange(`"表が怖い噂のソフト"`d)) == result(true, `"表が怖い噂のソフト"`, makeContext(testRange(""d))));

                assert(getResult!(parseStringLiteral!())(`r"表が怖い噂のソフト"` ) == result(true, `r"表が怖い噂のソフト"`, makeContext("" )));
                assert(getResult!(parseStringLiteral!())(`r"表が怖い噂のソフト"`w) == result(true, `r"表が怖い噂のソフト"`, makeContext(""w)));
                assert(getResult!(parseStringLiteral!())(`r"表が怖い噂のソフト"`d) == result(true, `r"表が怖い噂のソフト"`, makeContext(""d)));
                assert(getResult!(parseStringLiteral!())(testRange(`r"表が怖い噂のソフト"` )) == result(true, `r"表が怖い噂のソフト"`, makeContext(testRange("" ))));
                assert(getResult!(parseStringLiteral!())(testRange(`r"表が怖い噂のソフト"`w)) == result(true, `r"表が怖い噂のソフト"`, makeContext(testRange(""w))));
                assert(getResult!(parseStringLiteral!())(testRange(`r"表が怖い噂のソフト"`d)) == result(true, `r"表が怖い噂のソフト"`, makeContext(testRange(""d))));

                assert(getResult!(parseStringLiteral!())("`表が怖い噂のソフト`" ) == result(true, q{`表が怖い噂のソフト`}, makeContext("" )));
                assert(getResult!(parseStringLiteral!())("`表が怖い噂のソフト`"w) == result(true, q{`表が怖い噂のソフト`}, makeContext(""w)));
                assert(getResult!(parseStringLiteral!())("`表が怖い噂のソフト`"d) == result(true, q{`表が怖い噂のソフト`}, makeContext(""d)));
                assert(getResult!(parseStringLiteral!())(testRange("`表が怖い噂のソフト`" )) == result(true, q{`表が怖い噂のソフト`}, makeContext(testRange("" ))));
                assert(getResult!(parseStringLiteral!())(testRange("`表が怖い噂のソフト`"w)) == result(true, q{`表が怖い噂のソフト`}, makeContext(testRange(""w))));
                assert(getResult!(parseStringLiteral!())(testRange("`表が怖い噂のソフト`"d)) == result(true, q{`表が怖い噂のソフト`}, makeContext(testRange(""d))));
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
                assert(getResult!(parseIntLiteral!())("3141" ) == result(true, 3141, makeContext("" )));
                assert(getResult!(parseIntLiteral!())("3141"w) == result(true, 3141, makeContext(""w)));
                assert(getResult!(parseIntLiteral!())("3141"d) == result(true, 3141, makeContext(""d)));
                assert(getResult!(parseIntLiteral!())(testRange("3141" )) == result(true, 3141, makeContext(testRange("" ))));
                assert(getResult!(parseIntLiteral!())(testRange("3141"w)) == result(true, 3141, makeContext(testRange(""w))));
                assert(getResult!(parseIntLiteral!())(testRange("3141"d)) == result(true, 3141, makeContext(testRange(""d))));

                assert(getResult!(parseIntLiteral!())("0" ) == result(true, 0, makeContext("" )));
                assert(getResult!(parseIntLiteral!())("0"w) == result(true, 0, makeContext(""w)));
                assert(getResult!(parseIntLiteral!())("0"d) == result(true, 0, makeContext(""d)));
                assert(getResult!(parseIntLiteral!())(testRange("0" )) == result(true, 0, makeContext(testRange("" ))));
                assert(getResult!(parseIntLiteral!())(testRange("0"w)) == result(true, 0, makeContext(testRange(""w))));
                assert(getResult!(parseIntLiteral!())(testRange("0"d)) == result(true, 0, makeContext(testRange(""d))));

                assert(getResult!(parseIntLiteral!())("0123" ) == result(true, 0, makeContext("123" )));
                assert(getResult!(parseIntLiteral!())("0123"w) == result(true, 0, makeContext("123"w)));
                assert(getResult!(parseIntLiteral!())("0123"d) == result(true, 0, makeContext("123"d)));
                assert(getResult!(parseIntLiteral!())(testRange("0123" )) == result(true, 0, makeContext(testRange("123" ))));
                assert(getResult!(parseIntLiteral!())(testRange("0123"w)) == result(true, 0, makeContext(testRange("123"w))));
                assert(getResult!(parseIntLiteral!())(testRange("0123"d)) == result(true, 0, makeContext(testRange("123"d))));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

string generateParsers(size_t callerLine = __LINE__, string callerFile = __FILE__)(string src){
    return src.parse!(defs, callerLine, callerFile)();
}

string getSource(size_t callerLine = __LINE__, string callerFile = __FILE__)(string src){
    return src.getResult!(defs!(), callerLine, callerFile).value;
}

auto getResult(alias fun, size_t callerLine = __LINE__, string callerFile = __FILE__, Range)(Range input){
    static if(isCharRange!Range){
        return fun.parse(Context!Range(input, 1), new CallerInfo(callerLine, callerFile));
    }else{
        return fun.parse(Context!Range(input), new CallerInfo(callerLine, callerFile));
    }
}

auto parse(alias fun, size_t callerLine = __LINE__, string callerFile = __FILE__, Range)(Range src){
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
                    return combinateConvert!(
                        combinateSequence!(
                            getCallerLine!(),
                            getLine!(),
                            id!()
                        ),
                        function(size_t callerLine, size_t line, string id) => " #line " ~ (callerLine + line - 1).to!string() ~ "\n" ~ id ~ "!()"
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
                version(Issue_8038_Fixed){
                    {
                        auto result = getResult!(nonterminal!())("A");
                        assert(result.match);
                        assert(result.rest.empty);
                        assert(result.value == " #line " ~ toStringNow!(__LINE__ - 3) ~ "\nA!()");
                    }
                    {
                        auto result = getResult!(nonterminal!())("int");
                        assert(result.match);
                        assert(result.rest.empty);
                        assert(result.value == " #line " ~ toStringNow!(__LINE__ - 3) ~ "\nint!()");
                    }
                }else{
                    {
                        auto result = getResult!(nonterminal!())("A");
                        assert(result.match);
                        assert(result.rest.empty);
                        assert(result.value == "A!()");
                    }
                    {
                        auto result = getResult!(nonterminal!())("int");
                        assert(result.match);
                        assert(result.rest.empty);
                        assert(result.value == "int!()");
                    }
                }
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
                {
                    auto result = getResult!(typeName!())("int");
                    assert(result.match);
                    assert(result.rest.empty);
                    assert(result.value == "int");
                }
                {
                    auto result = getResult!(typeName!())("Tuple!(string, int)");
                    assert(result.match);
                    assert(result.rest.empty);
                    assert(result.value == "Tuple!(string, int)");
                }
                {
                    auto result = getResult!(typeName!())("int[]");
                    assert(result.match);
                    assert(result.rest.empty);
                    assert(result.value == "int[]");
                }
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
                {
                    auto result = getResult!(id!())("A");
                    assert(result.match);
                    assert(result.rest.empty);
                    assert(result.value == "A");
                }
                {
                    auto result = getResult!(id!())("int");
                    assert(result.match);
                    assert(result.rest.empty);
                    assert(result.value == "int");
                }
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
                {
                    auto result = getResult!(eofLit!())("$");
                    assert(result.match);
                    assert(result.rest.empty);
                    assert(result.value == "parseEOF!()");
                }
                {
                    auto result = getResult!(eofLit!())("#");
                    assert(!result.match);
                }
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
                {
                    auto result = getResult!(rangeLit!())("[a-z]");
                    assert(result.match);
                    assert(result.rest.empty);
                    assert(result.value == "parseCharRange!('a','z')");
                }
                {
                    auto result = getResult!(rangeLit!())("[a-zA-Z_]");
                    assert(result.match);
                    assert(result.rest.empty);
                    assert(
                        result.value ==
                        "combinateChoice!("
                            "parseCharRange!('a','z'),"
                            "parseCharRange!('A','Z'),"
                            "parseString!\"_\""
                        ")"
                    );
                }
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
                {
                    auto result = getResult!(stringLit!())("\"hello\nworld\" ");
                    assert(result.match);
                    assert(result.rest.input == " ");
                    assert(result.value == "parseString!\"hello\nworld\"");
                }
                {
                    auto result = getResult!(stringLit!())("aa\"");
                    assert(!result.match);
                }
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // literal
        template literal(){
            alias string ResultType;
            Result!(string, ResultType) parse()(Context!string input, in CallerInfo info){
                return combinateChoice!(
                    rangeLit!(),
                    stringLit!(),
                    eofLit!(),
                ).parse(input, info);
            }
        }

        unittest{
            enum dg = {
                {
                    auto result = getResult!(literal!())("\"hello\nworld\"");
                    assert(result.match);
                    assert(result.rest.empty);
                    assert(result.value == "parseString!\"hello\nworld\"");
                }
                {
                    auto result = getResult!(literal!())("[a-z]");
                    assert(result.match);
                    assert(result.rest.empty);
                    assert(result.value == "parseCharRange!('a','z')");
                }
                {
                    auto result = getResult!(literal!())("$");
                    assert(result.match);
                    assert(result.rest.empty);
                    assert(result.value == "parseEOF!()");
                }
                {
                    auto result = getResult!(literal!())("表が怖い噂のソフト");
                    assert(!result.match);
                }
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
                                    "parseEOF!()"
                                ")"
                            ")"
                        ")"
                    );
                }
                {
                    auto result = getResult!(primaryExp!())("int");
                    assert(result.match);
                    assert(result.rest.empty);
                    version(Issue_8038_Fixed){
                        assert(result.value == " #line " ~ toStringNow!(__LINE__ - 4) ~ "\nint!()");
                    }else{
                        assert(result.value == "int!()");
                    }
                }
                {
                    auto result = getResult!(primaryExp!())("###このコメントは表示されません###");
                    assert(!result.match);
                }
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
                        "parseEOF!()"
                    ")"
                );
                result = getResult!(preExp!())("!!$");
                assert(result.match);
                assert(result.rest.empty);
                assert(
                    result.value ==
                    "combinateChangeState!("
                        "parseEOF!()"
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
                            "parseEOF!()"
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
                                "parseString!\"hello\""
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
                                    "parseEOF!()"
                                ")"
                            "),"
                            "combinateOption!("
                                "combinateAndPred!("
                                    "combinateNotPred!("
                                        "parseEOF!()"
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
                                "parseString!\"hello\""
                            "),"
                            "parseEOF!()"
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
                                    "parseString!\"hello\""
                                "),"
                                "parseEOF!()"
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
                                "parseString!\"hello\","
                                "flat"
                            "),"
                            "to!int"
                        ")"
                    );
                }
                {
                    auto result = getResult!(convExp!(), __LINE__, `src\ctpg.d`)(q{$ >>> to!string >>? isValid});
                    assert(result.match);
                    assert(result.rest.empty);
                    assert(
                        result.value == 
                        "combinateCheck!(" ~ toStringNow!(__LINE__ - 5) ~ r",`src\ctpg.d`,"
                            "combinateConvertWithState!(" ~ toStringNow!(__LINE__ - 6) ~ r",`src\ctpg.d`,"
                                "parseEOF!(),"
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
                                    "parseEOF!()"
                                ")"
                            "),"
                            "combinateOption!("
                                "combinateAndPred!("
                                    "combinateNotPred!("
                                        "parseString!\"a\""
                                    ")"
                                ")"
                            ")"
                        ")"
                    );
                }
                {
                    auto result = getResult!(choiceExp!())(`!"hello" $`);
                    assert(result.match);
                    assert(result.rest.empty);
                    assert(
                        result.value ==
                        "combinateSequence!("
                            "combinateNone!("
                                "parseString!\"hello\""
                            "),"
                            "parseEOF!()"
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
                    auto result = getResult!(def!(), __LINE__, `src\ctpg.d`)(`bool hoge = !"hello" $ >> {return false;};`);
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
                                            "parseString!\"hello\""
                                        "),"
                                        "parseEOF!()"
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
                                    " #line " ~ toStringNow!(__LINE__ - 9) ~ "\nA!(),"
                                    "parseEOF!()"
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
                            def!(),
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
                    bool hoge = !"hello" $ >> {return false;};
                    Tuple!piyo hoge2 = hoge* >> {return tuple("foo");};
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
                                        "parseString!\"hello\""
                                    "),"
                                    "parseEOF!()"
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
                            "return combinateConvert!(" ~ toStringNow!(__LINE__ - 25) ~ r",`src\ctpg.d`,"
                                "combinateMore0!("
                                    " #line " ~ toStringNow!(__LINE__ - 27) ~ "\nhoge!()"
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

