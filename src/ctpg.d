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

import std.array: save, empty, join;
import std.conv: to;
import std.range: isForwardRange, ElementType;
import std.traits: CommonType, isCallable, ReturnType, isSomeChar, isSomeString, Unqual, isAssignable, isArray;
import std.typetuple: staticMap, TypeTuple;

import std.utf: decode;

public import std.typecons: Tuple, isTuple, tuple;

alias Tuple!() None;
alias Object[size_t][string] memo_t;

version = memoize;

//version = Issue_8038_Fixed
debug = ctpg_compile_time;
debug = ctpg;

private:

import std.stdio;

debug(ctpg) void main(){
    "unittest passed".writeln;
}

version(unittest){
    template TestParser(T){
        alias T ResultType;
        Result!(R, ResultType) parse(R)(Input!R input, auto ref memo_t memo, in CallerInformation info){
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

public:

final class CallerInformation{
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

// struct Input
    struct Input(R){
        static assert(isSomeString!R || isForwardRange!R);

        invariant(){
            assert(line >= 1);
        }

        public{
            R range;
            size_t position;
            size_t line = 1;

            static if(isForwardRange!R){
                //cannot apply some qualifiers due to unclearness of R
                Input save(){
                    return Input(range.save, position, line);
                }

                @property
                bool empty(){
                    return range.empty;
                }
            }

            pure @safe nothrow
            bool opEquals(in Input lhs){
                return range == lhs.range && position == lhs.position && line == lhs.line;
            }
        }
    }

    Input!R makeInput(R)(R range){
        return Input!R(range);
    }

    Input!R makeInput(R)(R range, size_t position, size_t line = 1){
        return Input!R(range, position, line);
    }

// struct Result
    struct Result(R, T){
        public{
            bool match;
            T value;
            Input!R rest;
            Error error;

            void opAssign(U)(Result!(R, U) rhs)if(isAssignable!(T, U)){
                match = rhs.match;
                value = rhs.value;
                rest = rhs.rest;
                error = rhs.error;
            }

            pure @safe nothrow
            bool opEquals(in Result lhs){
                return match == lhs.match && value == lhs.value && rest == lhs.rest && error == lhs.error;
            }
        }
    }

    Result!(R, T) result(R, T)(bool match, T value, Input!R rest, Error error){
        return Result!(R, T)(match, value, rest, error);
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
            static Result!(R, ResultType) parse(R)(Input!R input, auto ref memo_t memo, in CallerInformation info){
                return result(true, None.init, input, Error.init);
            }
        }

    // failure
        template failure(){
            alias None ResultType;
            static Result!(R, ResultType) parse(R)(Input!R input, auto ref memo_t memo, in CallerInformation info){
                return result(false, None.init, Input!R.init, Error.init);
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
                assert(countBreadth("これ\nとこれ") == Tuple!(size_t, "width", size_t, "line")(6, 1));
                assert(countBreadth("これ\nとこれ\nとさらにこれ") == Tuple!(size_t, "width", size_t, "line")(13, 2));
                {
                    auto result = countBreadth("helloワールド");
                }
                return true;
            }());
        }

        template parseString(string str) if(str.length > 0){
            alias string ResultType;
            static Result!(R, ResultType) parse(R)(Input!R ainput, auto ref memo_t memo, in CallerInformation info){
                auto input = ainput;
                enum breadth = countBreadth(str);
                enum convertedString = staticConvertString!(str, R);
                typeof(return) result;
                static if(isSomeString!R){
                    if(input.range.length >= convertedString.length && convertedString == input.range[0..convertedString.length]){
                        result.match = true;
                        result.value = str;
                        result.rest.range = input.range[convertedString.length..$];
                        result.rest.position = input.position + breadth.width;
                        result.rest.line = input.line + breadth.line;
                        return result;
                    }
                }else{
                    foreach(c; convertedString){
                        if(input.range.empty || c != input.range.front){
                            goto Lerror;
                        }else{
                            input.range.popFront;
                        }
                    }
                    result.match = true;
                    result.value = str;
                    result.rest.range = input.range;
                    result.rest.position = input.position + breadth.width;
                    result.rest.line = input.line + breadth.line;
                    return result;
                }
            Lerror:
                result.error = Error('"' ~ str ~ '"', input.line);
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(getResult!(parseString!"hello")("hello world" ) == result(true, "hello", makeInput(" world" , 5), Error.init));
                assert(getResult!(parseString!"hello")("hello world"w) == result(true, "hello", makeInput(" world"w, 5), Error.init));
                assert(getResult!(parseString!"hello")("hello world"d) == result(true, "hello", makeInput(" world"d, 5), Error.init));
                assert(getResult!(parseString!"hello")(testRange("hello world" )) == result(true, "hello", makeInput(testRange(" world" ), 5), Error.init));
                assert(getResult!(parseString!"hello")(testRange("hello world"w)) == result(true, "hello", makeInput(testRange(" world"w), 5), Error.init));
                assert(getResult!(parseString!"hello")(testRange("hello world"d)) == result(true, "hello", makeInput(testRange(" world"d), 5), Error.init));

                assert(getResult!(parseString!"hello")("hello" ) == result(true, "hello", makeInput("" , 5), Error.init));
                assert(getResult!(parseString!"hello")("hello"w) == result(true, "hello", makeInput(""w, 5), Error.init));
                assert(getResult!(parseString!"hello")("hello"d) == result(true, "hello", makeInput(""d, 5), Error.init));
                assert(getResult!(parseString!"hello")(testRange("hello" )) == result(true, "hello", makeInput(testRange("" ), 5), Error.init));
                assert(getResult!(parseString!"hello")(testRange("hello"w)) == result(true, "hello", makeInput(testRange(""w), 5), Error.init));
                assert(getResult!(parseString!"hello")(testRange("hello"d)) == result(true, "hello", makeInput(testRange(""d), 5), Error.init));

                assert(getResult!(parseString!"表が怖い")("表が怖い噂のソフト" ) == result(true, "表が怖い", makeInput("噂のソフト" , 4), Error.init));
                assert(getResult!(parseString!"表が怖い")("表が怖い噂のソフト"w) == result(true, "表が怖い", makeInput("噂のソフト"w, 4), Error.init));
                assert(getResult!(parseString!"表が怖い")("表が怖い噂のソフト"d) == result(true, "表が怖い", makeInput("噂のソフト"d, 4), Error.init));
                assert(getResult!(parseString!"表が怖い")(testRange("表が怖い噂のソフト" )) == result(true, "表が怖い", makeInput(testRange("噂のソフト" ), 4), Error.init));
                assert(getResult!(parseString!"表が怖い")(testRange("表が怖い噂のソフト"w)) == result(true, "表が怖い", makeInput(testRange("噂のソフト"w), 4), Error.init));
                assert(getResult!(parseString!"表が怖い")(testRange("表が怖い噂のソフト"d)) == result(true, "表が怖い", makeInput(testRange("噂のソフト"d), 4), Error.init));

                assert(getResult!(parseString!"hello")("hllo world" ) == result(false, "", makeInput("" ), Error("\"hello\"")));
                assert(getResult!(parseString!"hello")("hllo world"w) == result(false, "", makeInput(""w), Error("\"hello\"")));
                assert(getResult!(parseString!"hello")("hllo world"d) == result(false, "", makeInput(""d), Error("\"hello\"")));
                assert(getResult!(parseString!"hello")(testRange("hllo world" )) == result(false, "", makeInput(testRange("" )), Error("\"hello\"")));
                assert(getResult!(parseString!"hello")(testRange("hllo world"w)) == result(false, "", makeInput(testRange(""w)), Error("\"hello\"")));
                assert(getResult!(parseString!"hello")(testRange("hllo world"d)) == result(false, "", makeInput(testRange(""d)), Error("\"hello\"")));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // parseCharRange
        dchar decodeRange(R)(ref R range){
            static assert(isForwardRange!R);
            static assert(isSomeChar!(Unqual!(ElementType!R)));
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
                assert(decodeRange([testRange("\u0001")][0]) == '\u0001');
                assert(decodeRange([testRange("\u0081")][0]) == '\u0081');
                assert(decodeRange([testRange("\u0801")][0]) == '\u0801');
                assert(decodeRange([testRange("\U00012345")][0]) == '\U00012345');
                assert(decodeRange([testRange("\u0001"w)][0]) == '\u0001');
                assert(decodeRange([testRange("\uE001"w)][0]) == '\uE001');
                assert(decodeRange([testRange("\U00012345"w)][0]) == '\U00012345');
                assert(decodeRange([testRange("\U0010FFFE")][0]) == '\U0010FFFE');
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

        template parseCharRange(dchar low, dchar high){
            static assert(low <= high);

            alias string ResultType;
            static Result!(R, ResultType) parse(R)(Input!R _input, auto ref memo_t memo, in CallerInformation info){
                auto input = _input;
                typeof(return) result;
                static if(isSomeString!R){
                    if(input.range.length){
                        size_t idx;
                        dchar c = decode(input.range, idx);
                        if(low <= c && c <= high){
                            result.match = true;
                            result.value = c.to!string();
                            result.rest.range = input.range[idx..$];
                            result.rest.position = input.position + 1;
                            result.rest.line = c == '\n' ? input.line + 1 : input.line;
                            return result;
                        }
                    }
                }else{
                    if(!input.range.empty){
                        dchar c = decodeRange(input.range);
                        if(low <= c && c <= high){
                            result.match = true;
                            result.value = c.to!string();
                            result.rest.range = input.range;
                            result.rest.position = input.position + 1;
                            result.rest.line = c == '\n' ? input.line + 1 : input.line;
                            return result;
                        }
                    }
                }
                if(low == dchar.min && high == dchar.max){
                    result.error = Error("any char", input.line);
                }else{
                    result.error = Error("c: '" ~ low.to!string() ~ "' <= c <= '" ~ high.to!string() ~ "'", input.line);
                }
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(getResult!(parseCharRange!('a', 'z'))("hoge" ) == result(true, "h", makeInput("oge" , 1), Error.init));
                assert(getResult!(parseCharRange!('a', 'z'))("hoge"w) == result(true, "h", makeInput("oge"w, 1), Error.init));
                assert(getResult!(parseCharRange!('a', 'z'))("hoge"d) == result(true, "h", makeInput("oge"d, 1), Error.init));
                assert(getResult!(parseCharRange!('a', 'z'))(testRange("hoge" )) == result(true, "h", makeInput(testRange("oge" ), 1), Error.init));
                assert(getResult!(parseCharRange!('a', 'z'))(testRange("hoge"w)) == result(true, "h", makeInput(testRange("oge"w), 1), Error.init));
                assert(getResult!(parseCharRange!('a', 'z'))(testRange("hoge"d)) == result(true, "h", makeInput(testRange("oge"d), 1), Error.init));

                assert(getResult!(parseCharRange!('\u0100', '\U0010FFFF'))("\U00012345hoge" ) == result(true, "\U00012345", makeInput("hoge" , 1), Error.init));
                assert(getResult!(parseCharRange!('\u0100', '\U0010FFFF'))("\U00012345hoge"w) == result(true, "\U00012345", makeInput("hoge"w, 1), Error.init));
                assert(getResult!(parseCharRange!('\u0100', '\U0010FFFF'))("\U00012345hoge"d) == result(true, "\U00012345", makeInput("hoge"d, 1), Error.init));
                assert(getResult!(parseCharRange!('\u0100', '\U0010FFFF'))(testRange("\U00012345hoge" )) == result(true, "\U00012345", makeInput(testRange("hoge" ), 1), Error.init));
                assert(getResult!(parseCharRange!('\u0100', '\U0010FFFF'))(testRange("\U00012345hoge"w)) == result(true, "\U00012345", makeInput(testRange("hoge"w), 1), Error.init));
                assert(getResult!(parseCharRange!('\u0100', '\U0010FFFF'))(testRange("\U00012345hoge"d)) == result(true, "\U00012345", makeInput(testRange("hoge"d), 1), Error.init));

                assert(getResult!(parseCharRange!('\u0100', '\U0010FFFF'))("hello world" ) == result(false, "", makeInput("" ), Error("c: '\u0100' <= c <= '\U0010FFFF'")));
                assert(getResult!(parseCharRange!('\u0100', '\U0010FFFF'))("hello world"w) == result(false, "", makeInput(""w), Error("c: '\u0100' <= c <= '\U0010FFFF'")));
                assert(getResult!(parseCharRange!('\u0100', '\U0010FFFF'))("hello world"d) == result(false, "", makeInput(""d), Error("c: '\u0100' <= c <= '\U0010FFFF'")));
                assert(getResult!(parseCharRange!('\u0100', '\U0010FFFF'))(testRange("hello world" )) == result(false, "", makeInput(testRange("" )), Error("c: '\u0100' <= c <= '\U0010FFFF'")));
                assert(getResult!(parseCharRange!('\u0100', '\U0010FFFF'))(testRange("hello world"w)) == result(false, "", makeInput(testRange(""w)), Error("c: '\u0100' <= c <= '\U0010FFFF'")));
                assert(getResult!(parseCharRange!('\u0100', '\U0010FFFF'))(testRange("hello world"d)) == result(false, "", makeInput(testRange(""d)), Error("c: '\u0100' <= c <= '\U0010FFFF'")));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // parseEscapeSequence
        template parseEscapeSequence(){
            alias string ResultType;
            static Result!(R, ResultType) parse(R)(Input!R input, auto ref memo_t memo, in CallerInformation info){
                typeof(return) result;
                static if(isSomeString!R){
                    if(input.range[0] == '\\'){
                        switch(input.range[1]){
                            case 'u':{
                                result.match = true;
                                result.value = input.range[0..6].to!string();
                                result.rest.range = input.range[6..$];
                                result.rest.position = input.position + 6;
                                result.rest.line = input.line;
                                return result;
                            }
                            case 'U':{
                                result.match = true;
                                result.value = input.range[0..10].to!string();
                                result.rest.range = input.range[10..$];
                                result.rest.position = input.position + 10;
                                result.rest.line = input.line;
                                return result;
                            }
                            case '\'': case '"': case '?': case '\\': case 'a': case 'b': case 'f': case 'n': case 'r': case 't': case 'v':{
                                result.match = true;
                                result.value = input.range[0..2].to!string();
                                result.rest.range = input.range[2..$];
                                result.rest.position = input.position + 2;
                                result.rest.line = input.line;
                                return result;
                            }
                            default:{
                            }
                        }
                    }
                }else{
                    auto c1 = input.range.front;
                    if(c1 == '\\'){
                        input.range.popFront;
                        auto c2 = input.range.front;
                        switch(c2){
                            case 'u':{
                                result.match = true;
                                input.range.popFront;
                                char[6] data;
                                data[0..2] = "\\u";
                                foreach(idx; 2..6){
                                    data[idx] = cast(char)input.range.front;
                                    input.range.popFront;
                                }
                                result.value = to!string(data);
                                result.rest.range = input.range;
                                result.rest.position = input.position + 6;
                                result.rest.line = input.line;
                                return result;
                            }
                            case 'U':{
                                result.match = true;
                                input.range.popFront;
                                char[10] data;
                                data[0..2] = "\\U";
                                foreach(idx; 2..10){
                                    data[idx] = cast(char)input.range.front;
                                    input.range.popFront;
                                }
                                result.value = to!string(data);
                                result.rest.range = input.range;
                                result.rest.position = input.position + 10;
                                result.rest.line = input.line;
                                return result;
                            }
                            case '\'': case '"': case '?': case '\\': case 'a': case 'b': case 'f': case 'n': case 'r': case 't': case 'v':{
                                result.match = true;
                                input.range.popFront;
                                result.value = "\\" ~ to!string(c2);
                                result.rest.position = input.position + 2;
                                result.rest.range = input.range;
                                result.rest.line = input.line;
                                return result;
                            }
                            default:{
                            }
                        }
                    }
                }
                result.error = Error("escape sequence", input.line);
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(getResult!(parseEscapeSequence!())(`\"hoge` ) == result(true, `\"`, makeInput("hoge" , 2), Error.init));
                assert(getResult!(parseEscapeSequence!())(`\"hoge`w) == result(true, `\"`, makeInput("hoge"w, 2), Error.init));
                assert(getResult!(parseEscapeSequence!())(`\"hoge`d) == result(true, `\"`, makeInput("hoge"d, 2), Error.init));
                assert(getResult!(parseEscapeSequence!())(testRange(`\"hoge` )) == result(true, `\"`, makeInput(testRange("hoge" ), 2), Error.init));
                assert(getResult!(parseEscapeSequence!())(testRange(`\"hoge`w)) == result(true, `\"`, makeInput(testRange("hoge"w), 2), Error.init));
                assert(getResult!(parseEscapeSequence!())(testRange(`\"hoge`d)) == result(true, `\"`, makeInput(testRange("hoge"d), 2), Error.init));

                assert(getResult!(parseEscapeSequence!())(`\U0010FFFFhoge` ) == result(true, `\U0010FFFF`, makeInput("hoge" , 10), Error.init));
                assert(getResult!(parseEscapeSequence!())(`\U0010FFFFhoge`w) == result(true, `\U0010FFFF`, makeInput("hoge"w, 10), Error.init));
                assert(getResult!(parseEscapeSequence!())(`\U0010FFFFhoge`d) == result(true, `\U0010FFFF`, makeInput("hoge"d, 10), Error.init));
                assert(getResult!(parseEscapeSequence!())(testRange(`\U0010FFFFhoge` )) == result(true, `\U0010FFFF`, makeInput(testRange("hoge" ), 10), Error.init));
                assert(getResult!(parseEscapeSequence!())(testRange(`\U0010FFFFhoge`w)) == result(true, `\U0010FFFF`, makeInput(testRange("hoge"w), 10), Error.init));
                assert(getResult!(parseEscapeSequence!())(testRange(`\U0010FFFFhoge`d)) == result(true, `\U0010FFFF`, makeInput(testRange("hoge"d), 10), Error.init));

                assert(getResult!(parseEscapeSequence!())(`\u10FFhoge` ) == result(true, `\u10FF`, makeInput("hoge" , 6), Error.init));
                assert(getResult!(parseEscapeSequence!())(`\u10FFhoge`w) == result(true, `\u10FF`, makeInput("hoge"w, 6), Error.init));
                assert(getResult!(parseEscapeSequence!())(`\u10FFhoge`d) == result(true, `\u10FF`, makeInput("hoge"d, 6), Error.init));
                assert(getResult!(parseEscapeSequence!())(testRange(`\u10FFhoge` )) == result(true, `\u10FF`, makeInput(testRange("hoge" ), 6), Error.init));
                assert(getResult!(parseEscapeSequence!())(testRange(`\u10FFhoge`w)) == result(true, `\u10FF`, makeInput(testRange("hoge"w), 6), Error.init));
                assert(getResult!(parseEscapeSequence!())(testRange(`\u10FFhoge`d)) == result(true, `\u10FF`, makeInput(testRange("hoge"d), 6), Error.init));

                assert(getResult!(parseEscapeSequence!())(`\nhoge` ) == result(true, `\n`, makeInput("hoge" , 2), Error.init));
                assert(getResult!(parseEscapeSequence!())(`\nhoge`w) == result(true, `\n`, makeInput("hoge"w, 2), Error.init));
                assert(getResult!(parseEscapeSequence!())(`\nhoge`d) == result(true, `\n`, makeInput("hoge"d, 2), Error.init));
                assert(getResult!(parseEscapeSequence!())(testRange(`\nhoge` )) == result(true, `\n`, makeInput(testRange("hoge" ), 2), Error.init));
                assert(getResult!(parseEscapeSequence!())(testRange(`\nhoge`w)) == result(true, `\n`, makeInput(testRange("hoge"w), 2), Error.init));
                assert(getResult!(parseEscapeSequence!())(testRange(`\nhoge`d)) == result(true, `\n`, makeInput(testRange("hoge"d), 2), Error.init));

                assert(getResult!(parseEscapeSequence!())("鬱hoge" ) == result(false, "", makeInput("" ), Error("escape sequence")));
                assert(getResult!(parseEscapeSequence!())("鬱hoge"w) == result(false, "", makeInput(""w), Error("escape sequence")));
                assert(getResult!(parseEscapeSequence!())("鬱hoge"d) == result(false, "", makeInput(""d), Error("escape sequence")));
                assert(getResult!(parseEscapeSequence!())(testRange("鬱hoge" )) == result(false, "", makeInput(testRange("" )), Error("escape sequence")));
                assert(getResult!(parseEscapeSequence!())(testRange("鬱hoge"w)) == result(false, "", makeInput(testRange(""w)), Error("escape sequence")));
                assert(getResult!(parseEscapeSequence!())(testRange("鬱hoge"d)) == result(false, "", makeInput(testRange(""d)), Error("escape sequence")));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // parseSpace
        template parseSpace(){
            alias string ResultType;
            static Result!(R, ResultType) parse(R)(Input!R input, auto ref memo_t memo, in CallerInformation info){
                typeof(return) result;
                static if(isSomeString!R){
                    if(input.range.length > 0 && (input.range[0] == ' ' || input.range[0] == '\n' || input.range[0] == '\t' || input.range[0] == '\r' || input.range[0] == '\f')){
                        result.match = true;
                        result.value = input.range[0..1].to!string();
                        result.rest.range = input.range[1..$];
                        result.rest.position = input.position + 1;
                        result.rest.line = (input.range[0] == '\n' ? input.line + 1 : input.line);
                        return result;
                    }
                }else{
                    if(!input.range.empty){
                        Unqual!(ElementType!R) c = input.range.front;
                        if(c == ' ' || c == '\n' || c == '\t' || c == '\r' || c == '\f'){
                            result.match = true;
                            result.value = c.to!string();
                            input.range.popFront;
                            result.rest.range = input.range;
                            result.rest.position = input.position + 1;
                            result.rest.line = (c == '\n' ? input.line + 1 : input.line);
                            return result;
                        }
                    }
                }
                result.error = Error("space", input.line);
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(getResult!(parseSpace!())("\thoge" ) == result(true, "\t", makeInput("hoge" , 1), Error.init));
                assert(getResult!(parseSpace!())("\thoge"w) == result(true, "\t", makeInput("hoge"w, 1), Error.init));
                assert(getResult!(parseSpace!())("\thoge"d) == result(true, "\t", makeInput("hoge"d, 1), Error.init));
                assert(getResult!(parseSpace!())(testRange("\thoge"))  == result(true, "\t", makeInput(testRange("hoge"),  1), Error.init));
                assert(getResult!(parseSpace!())(testRange("\thoge"w)) == result(true, "\t", makeInput(testRange("hoge"w), 1), Error.init));
                assert(getResult!(parseSpace!())(testRange("\thoge"d)) == result(true, "\t", makeInput(testRange("hoge"d), 1), Error.init));

                assert(getResult!(parseSpace!())("hoge" ) == result(false, "", makeInput("" ), Error("space")));
                assert(getResult!(parseSpace!())("hoge"w) == result(false, "", makeInput(""w), Error("space")));
                assert(getResult!(parseSpace!())("hoge"d) == result(false, "", makeInput(""d), Error("space")));
                assert(getResult!(parseSpace!())(testRange("hoge" )) == result(false, "", makeInput(testRange("" )), Error("space")));
                assert(getResult!(parseSpace!())(testRange("hoge"w)) == result(false, "", makeInput(testRange(""w)), Error("space")));
                assert(getResult!(parseSpace!())(testRange("hoge"d)) == result(false, "", makeInput(testRange(""d)), Error("space")));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // parseEOF
        template parseEOF(){
            alias None ResultType;
            static Result!(R, ResultType) parse(R)(Input!R input, auto ref memo_t memo, in CallerInformation info){
                typeof(return) result;
                if(input.range.empty){
                    result.match = true;
                }else{
                    result.error = Error("EOF", input.line);
                }
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(getResult!(parseEOF!())("" ) == result(true, None.init, makeInput("" , 0), Error.init));
                assert(getResult!(parseEOF!())(""w) == result(true, None.init, makeInput(""w, 0), Error.init));
                assert(getResult!(parseEOF!())(""d) == result(true, None.init, makeInput(""d, 0), Error.init));
                assert(getResult!(parseEOF!())(testRange("" )) == result(true, None.init, makeInput(testRange("" ), 0), Error.init));
                assert(getResult!(parseEOF!())(testRange(""w)) == result(true, None.init, makeInput(testRange(""w), 0), Error.init));
                assert(getResult!(parseEOF!())(testRange(""d)) == result(true, None.init, makeInput(testRange(""d), 0), Error.init));

                assert(getResult!(parseEOF!())("hoge" ) == result(false, None.init, makeInput("" ), Error("EOF")));
                assert(getResult!(parseEOF!())("hoge"w) == result(false, None.init, makeInput(""w), Error("EOF")));
                assert(getResult!(parseEOF!())("hoge"d) == result(false, None.init, makeInput(""d), Error("EOF")));
                assert(getResult!(parseEOF!())(testRange("hoge" )) == result(false, None.init, makeInput(testRange("" )), Error("EOF")));
                assert(getResult!(parseEOF!())(testRange("hoge"w)) == result(false, None.init, makeInput(testRange(""w)), Error("EOF")));
                assert(getResult!(parseEOF!())(testRange("hoge"d)) == result(false, None.init, makeInput(testRange(""d)), Error("EOF")));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

// getters
    // getLine
        template getLine(){
            alias size_t ResultType;
            static Result!(R, ResultType) parse(R)(Input!R input, auto ref memo_t memo, in CallerInformation info){
                return result(true, input.line, input, Error.init);
            }
        }

        unittest{
            enum dg = {
                assert(getResult!(combinateSequence!(parseSpaces!(), getLine!()))("\n\n" ) == result(true, 3LU, makeInput("" , 2, 3), Error.init));
                assert(getResult!(combinateSequence!(parseSpaces!(), getLine!()))("\n\n"w) == result(true, 3LU, makeInput(""w, 2, 3), Error.init));
                assert(getResult!(combinateSequence!(parseSpaces!(), getLine!()))("\n\n"d) == result(true, 3LU, makeInput(""d, 2, 3), Error.init));
                assert(getResult!(combinateSequence!(parseSpaces!(), getLine!()))(testRange("\n\n" )) == result(true, 3LU, makeInput(testRange("" ), 2, 3), Error.init));
                assert(getResult!(combinateSequence!(parseSpaces!(), getLine!()))(testRange("\n\n"w)) == result(true, 3LU, makeInput(testRange(""w), 2, 3), Error.init));
                assert(getResult!(combinateSequence!(parseSpaces!(), getLine!()))(testRange("\n\n"d)) == result(true, 3LU, makeInput(testRange(""d), 2, 3), Error.init));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // getCallerLine
        template getCallerLine(){
            alias size_t ResultType;
            static Result!(R, ResultType) parse(R)(Input!R input, auto ref memo_t memo, in CallerInformation info){
                return result(true, info.line, input, Error.init);
            }
        }

        unittest{
            enum dg = {
                assert(getResult!(getCallerLine!())("" ) == result(true, cast(size_t)__LINE__, makeInput("" , 0), Error.init));
                assert(getResult!(getCallerLine!())(""w) == result(true, cast(size_t)__LINE__, makeInput(""w, 0), Error.init));
                assert(getResult!(getCallerLine!())(""d) == result(true, cast(size_t)__LINE__, makeInput(""d, 0), Error.init));
                assert(getResult!(getCallerLine!())(testRange("" )) == result(true, cast(size_t)__LINE__, makeInput(testRange("" ), 0), Error.init));
                assert(getResult!(getCallerLine!())(testRange(""w)) == result(true, cast(size_t)__LINE__, makeInput(testRange(""w), 0), Error.init));
                assert(getResult!(getCallerLine!())(testRange(""d)) == result(true, cast(size_t)__LINE__, makeInput(testRange(""d), 0), Error.init));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // getCallerFile
        template getCallerFile(){
            alias string ResultType;
            static Result!(R, ResultType) parse(R)(Input!R input, auto ref memo_t memo, in CallerInformation info){
                return result(true, info.file, input, Error.init);
            }
        }

// combinators
    // combinateMemoize
        version(memoize){
            final class Wrapper(T){
                this(T value){
                    this.value = value;
                }
                T value;
            }

            Wrapper!T wrap(T)(T value){
                return new Wrapper!T(value);
            }

            template combinateMemoize(alias parser){
                alias ParserType!parser ResultType;
                Result!(R, ResultType) parse(R)(Input!R input, auto ref memo_t memo, in CallerInformation info){
                    auto memo0 = parser.mangleof in memo;
                    if(memo0){
                        auto memo1 = input.position in *memo0;
                        if(memo1){
                            Object p = *memo1;
                            return (cast(Wrapper!(Result!(R, ParserType!parser)))p).value;
                        }
                    }
                    auto result = parser.parse(input, memo, info);
                    memo[parser.mangleof][input.position] = wrap(result);
                    return result;
                }
            }
        }else{
            template combinateMemoize(alias parser){
                alias parser combinateMemoize;
            }
        }

    // combinateUnTuple
        template combinateUnTuple(alias parser){
            static if(isTuple!(ParserType!parser) && ParserType!parser.Types.length == 1){
                alias ParserType!parser.Types[0] ResultType;
                static Result!(R, ResultType) parse(R)(Input!R input, auto ref memo_t memo, in CallerInformation info){
                    typeof(return) result;
                    auto r = parser.parse(input, memo, info);
                    result.match = r.match;
                    result.value = r.value[0];
                    result.rest = r.rest;
                    result.error = r.error;
                    return result;
                }
            }else{
                alias combinateMemoize!parser combinateUnTuple;
            }
        }

        unittest{
            enum dg = {
                assert(getResult!(combinateUnTuple!(TestParser!int))("" ) == result(false, 0, makeInput("" ), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!int))(""w) == result(false, 0, makeInput(""w), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!int))(""d) == result(false, 0, makeInput(""d), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!int))(testRange("" )) == result(false, 0, makeInput(testRange("" )), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!int))(testRange(""w)) == result(false, 0, makeInput(testRange(""w)), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!int))(testRange(""d)) == result(false, 0, makeInput(testRange(""d)), Error.init));

                assert(getResult!(combinateUnTuple!(TestParser!long))("" ) == result(false, 0L, makeInput("" ), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!long))(""w) == result(false, 0L, makeInput(""w), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!long))(""d) == result(false, 0L, makeInput(""d), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!long))(testRange("" )) == result(false, 0L, makeInput(testRange("" )), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!long))(testRange(""w)) == result(false, 0L, makeInput(testRange(""w)), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!long))(testRange(""d)) == result(false, 0L, makeInput(testRange(""d)), Error.init));

                assert(getResult!(combinateUnTuple!(TestParser!string))("" ) == result(false, "", makeInput("" ), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!string))(""w) == result(false, "", makeInput(""w), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!string))(""d) == result(false, "", makeInput(""d), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!string))(testRange("" )) == result(false, "", makeInput(testRange("" )), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!string))(testRange(""w)) == result(false, "", makeInput(testRange(""w)), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!string))(testRange(""d)) == result(false, "", makeInput(testRange(""d)), Error.init));

                assert(getResult!(combinateUnTuple!(TestParser!wstring))("" ) == result(false, ""w, makeInput("" ), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!wstring))(""w) == result(false, ""w, makeInput(""w), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!wstring))(""d) == result(false, ""w, makeInput(""d), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!wstring))(testRange("" )) == result(false, ""w, makeInput(testRange("" )), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!wstring))(testRange(""w)) == result(false, ""w, makeInput(testRange(""w)), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!wstring))(testRange(""d)) == result(false, ""w, makeInput(testRange(""d)), Error.init));

                assert(getResult!(combinateUnTuple!(TestParser!dstring))("" ) == result(false, ""d, makeInput("" ), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!dstring))(""w) == result(false, ""d, makeInput(""w), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!dstring))(""d) == result(false, ""d, makeInput(""d), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!dstring))(testRange("" )) == result(false, ""d, makeInput(testRange("" )), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!dstring))(testRange(""w)) == result(false, ""d, makeInput(testRange(""w)), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!dstring))(testRange(""d)) == result(false, ""d, makeInput(testRange(""d)), Error.init));

                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!int)))("" ) == result(false, 0, makeInput("" ), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!int)))(""w) == result(false, 0, makeInput(""w), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!int)))(""d) == result(false, 0, makeInput(""d), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!int)))(testRange("" )) == result(false, 0, makeInput(testRange("" )), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!int)))(testRange(""w)) == result(false, 0, makeInput(testRange(""w)), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!int)))(testRange(""d)) == result(false, 0, makeInput(testRange(""d)), Error.init));

                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(int, int))))("" ) == result(false, tuple(0, 0), makeInput("" ), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(int, int))))(""w) == result(false, tuple(0, 0), makeInput(""w), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(int, int))))(""d) == result(false, tuple(0, 0), makeInput(""d), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(int, int))))(testRange("" )) == result(false, tuple(0, 0), makeInput(testRange("" )), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(int, int))))(testRange(""w)) == result(false, tuple(0, 0), makeInput(testRange(""w)), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(int, int))))(testRange(""d)) == result(false, tuple(0, 0), makeInput(testRange(""d)), Error.init));

                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!int))))("" ) == result(false, tuple(0), makeInput("" ), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!int))))(""w) == result(false, tuple(0), makeInput(""w), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!int))))(""d) == result(false, tuple(0), makeInput(""d), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!int))))(testRange("" )) == result(false, tuple(0), makeInput(testRange("" )), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!int))))(testRange(""w)) == result(false, tuple(0), makeInput(testRange(""w)), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!int))))(testRange(""d)) == result(false, tuple(0), makeInput(testRange(""d)), Error.init));

                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!(int, int)))))("" ) == result(false, tuple(0, 0), makeInput("" ), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!(int, int)))))(""w) == result(false, tuple(0, 0), makeInput(""w), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!(int, int)))))(""d) == result(false, tuple(0, 0), makeInput(""d), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!(int, int)))))(testRange("" )) == result(false, tuple(0, 0), makeInput(testRange("" )), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!(int, int)))))(testRange(""w)) == result(false, tuple(0, 0), makeInput(testRange(""w)), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!(int, int)))))(testRange(""d)) == result(false, tuple(0, 0), makeInput(testRange(""d)), Error.init));

                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!(int, int), int))))("" ) == result(false, tuple(tuple(0, 0), 0), makeInput("" ), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!(int, int), int))))(""w) == result(false, tuple(tuple(0, 0), 0), makeInput(""w), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!(int, int), int))))(""d) == result(false, tuple(tuple(0, 0), 0), makeInput(""d), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!(int, int), int))))(testRange("" )) == result(false, tuple(tuple(0, 0), 0), makeInput(testRange("" )), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!(int, int), int))))(testRange(""w)) == result(false, tuple(tuple(0, 0), 0), makeInput(testRange(""w)), Error.init));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!(int, int), int))))(testRange(""d)) == result(false, tuple(tuple(0, 0), 0), makeInput(testRange(""d)), Error.init));
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
            static Result!(R, ResultType) parse(R)(Input!R input, auto ref memo_t memo, in CallerInformation info){
                typeof(return) result;
                static if(parsers.length == 1){
                    auto r = parsers[0].parse(input, memo, info);
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
                    auto r1 = parsers[0].parse(input, memo, info);
                    if(r1.match){
                        auto r2 = combinateSequenceImpl!(parsers[1..$]).parse(r1.rest, memo, info);
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
                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))("helloworld" ) == result(true, tuple("hello", "world"), makeInput("" , 10), Error.init));
                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))("helloworld"w) == result(true, tuple("hello", "world"), makeInput(""w, 10), Error.init));
                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))("helloworld"d) == result(true, tuple("hello", "world"), makeInput(""d, 10), Error.init));
                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))(testRange("helloworld" )) == result(true, tuple("hello", "world"), makeInput(testRange("" ), 10), Error.init));
                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))(testRange("helloworld"w)) == result(true, tuple("hello", "world"), makeInput(testRange(""w), 10), Error.init));
                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))(testRange("helloworld"d)) == result(true, tuple("hello", "world"), makeInput(testRange(""d), 10), Error.init));

                assert(getResult!(combinateSequence!(combinateSequence!(parseString!("hello"), parseString!("world")), parseString!"!"))("helloworld!" ) == result(true, tuple("hello", "world", "!"), makeInput("" , 11), Error.init));
                assert(getResult!(combinateSequence!(combinateSequence!(parseString!("hello"), parseString!("world")), parseString!"!"))("helloworld!"w) == result(true, tuple("hello", "world", "!"), makeInput(""w, 11), Error.init));
                assert(getResult!(combinateSequence!(combinateSequence!(parseString!("hello"), parseString!("world")), parseString!"!"))("helloworld!"d) == result(true, tuple("hello", "world", "!"), makeInput(""d, 11), Error.init));
                assert(getResult!(combinateSequence!(combinateSequence!(parseString!("hello"), parseString!("world")), parseString!"!"))(testRange("helloworld!" )) == result(true, tuple("hello", "world", "!"), makeInput(testRange("" ), 11), Error.init));
                assert(getResult!(combinateSequence!(combinateSequence!(parseString!("hello"), parseString!("world")), parseString!"!"))(testRange("helloworld!"w)) == result(true, tuple("hello", "world", "!"), makeInput(testRange(""w), 11), Error.init));
                assert(getResult!(combinateSequence!(combinateSequence!(parseString!("hello"), parseString!("world")), parseString!"!"))(testRange("helloworld!"d)) == result(true, tuple("hello", "world", "!"), makeInput(testRange(""d), 11), Error.init));

                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))("hellovvorld" ) == result(false, tuple("", ""), makeInput("" ), Error(q{"world"})));
                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))("hellovvorld"w) == result(false, tuple("", ""), makeInput(""w), Error(q{"world"})));
                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))("hellovvorld"d) == result(false, tuple("", ""), makeInput(""d), Error(q{"world"})));
                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))(testRange("hellovvorld" )) == result(false, tuple("", ""), makeInput(testRange("" )), Error(q{"world"})));
                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))(testRange("hellovvorld"w)) == result(false, tuple("", ""), makeInput(testRange(""w)), Error(q{"world"})));
                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))(testRange("hellovvorld"d)) == result(false, tuple("", ""), makeInput(testRange(""d)), Error(q{"world"})));

                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world"), parseString!("!")))("helloworld?" ) == result(false, tuple("", "", ""), makeInput("" ), Error(q{"!"})));
                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world"), parseString!("!")))("helloworld?"w) == result(false, tuple("", "", ""), makeInput(""w), Error(q{"!"})));
                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world"), parseString!("!")))("helloworld?"d) == result(false, tuple("", "", ""), makeInput(""d), Error(q{"!"})));
                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world"), parseString!("!")))(testRange("helloworld?" )) == result(false, tuple("", "", ""), makeInput(testRange("" )), Error(q{"!"})));
                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world"), parseString!("!")))(testRange("helloworld?"w)) == result(false, tuple("", "", ""), makeInput(testRange(""w)), Error(q{"!"})));
                assert(getResult!(combinateSequence!(parseString!("hello"), parseString!("world"), parseString!("!")))(testRange("helloworld?"d)) == result(false, tuple("", "", ""), makeInput(testRange(""d)), Error(q{"!"})));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // combinateChoice
        template CommonParserType(tparsers...){
            alias CommonType!(staticMap!(ParserType, tparsers)) CommonParserType;
        }

        unittest{
            static assert(is(CommonParserType!(TestParser!string, TestParser!string) == string));
            static assert(is(CommonParserType!(TestParser!int, TestParser!long) == long));
            static assert(is(CommonParserType!(TestParser!byte, TestParser!short, TestParser!int) == int));
            static assert(is(CommonParserType!(TestParser!string, TestParser!int) == void));
        }

        template combinateChoice(parsers...){
            alias CommonParserType!(parsers) ResultType;
            static Result!(R, ResultType) parse(R)(Input!R input, auto ref memo_t memo, in CallerInformation info){
                static assert(parsers.length > 0);
                static if(parsers.length == 1){
                    return parsers[0].parse(input, memo, info);
                }else{
                    auto r = parsers[0].parse(input.save, memo, info);
                    if(r.match){
                        return r;
                    }
                    return combinateChoice!(parsers[1..$]).parse(input, memo, info);
                }
            }
        }

        unittest{
            enum dg = {
                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))("hw" ) == result(true, "h", makeInput("w" , 1), Error.init)); 
                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))("hw"w) == result(true, "h", makeInput("w"w, 1), Error.init)); 
                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))("hw"d) == result(true, "h", makeInput("w"d, 1), Error.init)); 
                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))(testRange("hw" )) == result(true, "h", makeInput(testRange("w" ), 1), Error.init)); 
                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))(testRange("hw"w)) == result(true, "h", makeInput(testRange("w"w), 1), Error.init)); 
                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))(testRange("hw"d)) == result(true, "h", makeInput(testRange("w"d), 1), Error.init)); 

                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))("w" ) == result(true, "w", makeInput("" , 1), Error.init));
                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))("w"w) == result(true, "w", makeInput(""w, 1), Error.init));
                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))("w"d) == result(true, "w", makeInput(""d, 1), Error.init));
                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))(testRange("w" )) == result(true, "w", makeInput(testRange("" ), 1), Error.init));
                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))(testRange("w"w)) == result(true, "w", makeInput(testRange(""w), 1), Error.init));
                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))(testRange("w"d)) == result(true, "w", makeInput(testRange(""d), 1), Error.init));

                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))("" ) == result(false, "", makeInput("" ), Error(q{"w"})));
                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))(""w) == result(false, "", makeInput(""w), Error(q{"w"})));
                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))(""d) == result(false, "", makeInput(""d), Error(q{"w"})));
                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))(testRange("" )) == result(false, "", makeInput(testRange("" )), Error(q{"w"})));
                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))(testRange(""w)) == result(false, "", makeInput(testRange(""w)), Error(q{"w"})));
                assert(getResult!(combinateChoice!(parseString!"h", parseString!"w"))(testRange(""d)) == result(false, "", makeInput(testRange(""d)), Error(q{"w"})));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // combinateMore
        template combinateMore(int n, alias parser, alias sep){
            alias ParserType!(parser)[] ResultType;
            static Result!(R, ResultType) parse(R)(Input!R input, auto ref memo_t memo, in CallerInformation info){
                typeof(return) result;
                Input!R rest = input;
                while(true){
                    auto input1 = rest.save;
                    auto r1 = parser.parse(input1, memo, info);
                    if(r1.match){
                        //result.value = result.value ~ r1.value;
                        result.value ~= r1.value;
                        rest = r1.rest;
                        auto input2 = rest.save;
                        auto r2 = sep.parse(input2, memo, info);
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
                assert(getResult!(combinateConvert!(combinateMore0!(parseString!"w"), flat))("www w" ) == result(true, "www", makeInput(" w" , 3), Error.init));
                assert(getResult!(combinateConvert!(combinateMore0!(parseString!"w"), flat))("www w"w) == result(true, "www", makeInput(" w"w, 3), Error.init));
                assert(getResult!(combinateConvert!(combinateMore0!(parseString!"w"), flat))("www w"d) == result(true, "www", makeInput(" w"d, 3), Error.init));
                assert(getResult!(combinateConvert!(combinateMore0!(parseString!"w"), flat))(testRange("www w" )) == result(true, "www", makeInput(testRange(" w" ), 3), Error.init));
                assert(getResult!(combinateConvert!(combinateMore0!(parseString!"w"), flat))(testRange("www w"w)) == result(true, "www", makeInput(testRange(" w"w), 3), Error.init));
                assert(getResult!(combinateConvert!(combinateMore0!(parseString!"w"), flat))(testRange("www w"d)) == result(true, "www", makeInput(testRange(" w"d), 3), Error.init));

                assert(getResult!(combinateConvert!(combinateMore0!(parseString!"w"), flat))(" w" ) == result(true, "", makeInput(" w" , 0), Error.init));
                assert(getResult!(combinateConvert!(combinateMore0!(parseString!"w"), flat))(" w"w) == result(true, "", makeInput(" w"w, 0), Error.init));
                assert(getResult!(combinateConvert!(combinateMore0!(parseString!"w"), flat))(" w"d) == result(true, "", makeInput(" w"d, 0), Error.init));
                assert(getResult!(combinateConvert!(combinateMore0!(parseString!"w"), flat))(testRange(" w" )) == result(true, "", makeInput(testRange(" w" ), 0), Error.init));
                assert(getResult!(combinateConvert!(combinateMore0!(parseString!"w"), flat))(testRange(" w"w)) == result(true, "", makeInput(testRange(" w"w), 0), Error.init));
                assert(getResult!(combinateConvert!(combinateMore0!(parseString!"w"), flat))(testRange(" w"d)) == result(true, "", makeInput(testRange(" w"d), 0), Error.init));

                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), flat))("www w" ) == result(true, "www", makeInput(" w" , 3), Error.init));
                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), flat))("www w"w) == result(true, "www", makeInput(" w"w, 3), Error.init));
                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), flat))("www w"d) == result(true, "www", makeInput(" w"d, 3), Error.init));
                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), flat))(testRange("www w" )) == result(true, "www", makeInput(testRange(" w" ), 3), Error.init));
                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), flat))(testRange("www w"w)) == result(true, "www", makeInput(testRange(" w"w), 3), Error.init));
                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), flat))(testRange("www w"d)) == result(true, "www", makeInput(testRange(" w"d), 3), Error.init));

                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), flat))(" w" ) == result(false, "", makeInput("" ), Error(q{"w"})));
                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), flat))(" w"w) == result(false, "", makeInput(""w), Error(q{"w"})));
                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), flat))(" w"d) == result(false, "", makeInput(""d), Error(q{"w"})));
                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), flat))(testRange(" w" )) == result(false, "", makeInput(testRange("" )), Error(q{"w"})));
                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), flat))(testRange(" w"w)) == result(false, "", makeInput(testRange(""w)), Error(q{"w"})));
                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), flat))(testRange(" w"d)) == result(false, "", makeInput(testRange(""d)), Error(q{"w"})));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // combinateOption
        template combinateOption(alias parser){
            alias Option!(ParserType!parser) ResultType;
            static Result!(R, ResultType) parse(R)(Input!R input, auto ref memo_t memo, in CallerInformation info){
                typeof(return) result;
                result.match = true;
                auto r = parser.parse(input.save, memo, info);
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
                assert(getResult!(combinateOption!(parseString!"w"))("w" ) == result(true, makeOption(true, "w"), makeInput("" , 1), Error.init));
                assert(getResult!(combinateOption!(parseString!"w"))("w"w) == result(true, makeOption(true, "w"), makeInput(""w, 1), Error.init));
                assert(getResult!(combinateOption!(parseString!"w"))("w"d) == result(true, makeOption(true, "w"), makeInput(""d, 1), Error.init));
                assert(getResult!(combinateOption!(parseString!"w"))(testRange("w" )) == result(true, makeOption(true, "w"), makeInput(testRange("" ), 1), Error.init));
                assert(getResult!(combinateOption!(parseString!"w"))(testRange("w"w)) == result(true, makeOption(true, "w"), makeInput(testRange(""w), 1), Error.init));
                assert(getResult!(combinateOption!(parseString!"w"))(testRange("w"d)) == result(true, makeOption(true, "w"), makeInput(testRange(""d), 1), Error.init));

                assert(getResult!(combinateOption!(parseString!"w"))("hoge" ) == result(true, makeOption(false, ""), makeInput("hoge" , 0), Error.init));
                assert(getResult!(combinateOption!(parseString!"w"))("hoge"w) == result(true, makeOption(false, ""), makeInput("hoge"w, 0), Error.init));
                assert(getResult!(combinateOption!(parseString!"w"))("hoge"d) == result(true, makeOption(false, ""), makeInput("hoge"d, 0), Error.init));
                assert(getResult!(combinateOption!(parseString!"w"))(testRange("hoge" )) == result(true, makeOption(false, ""), makeInput(testRange("hoge" ), 0), Error.init));
                assert(getResult!(combinateOption!(parseString!"w"))(testRange("hoge"w)) == result(true, makeOption(false, ""), makeInput(testRange("hoge"w), 0), Error.init));
                assert(getResult!(combinateOption!(parseString!"w"))(testRange("hoge"d)) == result(true, makeOption(false, ""), makeInput(testRange("hoge"d), 0), Error.init));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // combinateNone
        template combinateNone(alias parser){
            alias None ResultType;
            static Result!(R, ResultType) parse(R)(Input!R input, auto ref memo_t memo, in CallerInformation info){
                typeof(return) result;
                auto r = parser.parse(input, memo, info);
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
                assert(getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))("(w)" ) == result(true, "w", makeInput("" , 3), Error.init));
                assert(getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))("(w)"w) == result(true, "w", makeInput(""w, 3), Error.init));
                assert(getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))("(w)"d) == result(true, "w", makeInput(""d, 3), Error.init));
                assert(getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))(testRange("(w)" )) == result(true, "w", makeInput(testRange("" ), 3), Error.init));
                assert(getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))(testRange("(w)"w)) == result(true, "w", makeInput(testRange(""w), 3), Error.init));
                assert(getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))(testRange("(w)"d)) == result(true, "w", makeInput(testRange(""d), 3), Error.init));

                assert(getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))("(w}" ) == result(false, "", makeInput("" ), Error(q{")"})));
                assert(getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))("(w}"w) == result(false, "", makeInput(""w), Error(q{")"})));
                assert(getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))("(w}"d) == result(false, "", makeInput(""d), Error(q{")"})));
                assert(getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))(testRange("(w}" )) == result(false, "", makeInput(testRange("" )), Error(q{")"})));
                assert(getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))(testRange("(w}"w)) == result(false, "", makeInput(testRange(""w)), Error(q{")"})));
                assert(getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))(testRange("(w}"d)) == result(false, "", makeInput(testRange(""d)), Error(q{")"})));

                assert(getResult!(combinateNone!(parseString!"w"))("a" ) == result(false, None.init, makeInput("" ), Error(q{"w"})));
                assert(getResult!(combinateNone!(parseString!"w"))("a"w) == result(false, None.init, makeInput(""w), Error(q{"w"})));
                assert(getResult!(combinateNone!(parseString!"w"))("a"d) == result(false, None.init, makeInput(""d), Error(q{"w"})));
                assert(getResult!(combinateNone!(parseString!"w"))(testRange("a" )) == result(false, None.init, makeInput(testRange("" )), Error(q{"w"})));
                assert(getResult!(combinateNone!(parseString!"w"))(testRange("a"w)) == result(false, None.init, makeInput(testRange(""w)), Error(q{"w"})));
                assert(getResult!(combinateNone!(parseString!"w"))(testRange("a"d)) == result(false, None.init, makeInput(testRange(""d)), Error(q{"w"})));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // combinateAndPred
        template combinateAndPred(alias parser){
            alias None ResultType;
            static Result!(R, ResultType) parse(R)(Input!R input, auto ref memo_t memo, in CallerInformation info){
                typeof(return) result;
                result.rest = input;
                auto r = parser.parse(input, memo, info);
                result.match = r.match;
                result.error = r.error;
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(getResult!(combinateAndPred!(parseString!"w"))("www" ) == result(true, None.init, makeInput("www" , 0), Error.init));
                assert(getResult!(combinateAndPred!(parseString!"w"))("www"w) == result(true, None.init, makeInput("www"w, 0), Error.init));
                assert(getResult!(combinateAndPred!(parseString!"w"))("www"d) == result(true, None.init, makeInput("www"d, 0), Error.init));
                assert(getResult!(combinateAndPred!(parseString!"w"))(testRange("www" )) == result(true, None.init, makeInput(testRange("www" ), 0), Error.init));
                assert(getResult!(combinateAndPred!(parseString!"w"))(testRange("www"w)) == result(true, None.init, makeInput(testRange("www"w), 0), Error.init));
                assert(getResult!(combinateAndPred!(parseString!"w"))(testRange("www"d)) == result(true, None.init, makeInput(testRange("www"d), 0), Error.init));

                assert(getResult!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w")))("www" ) == result(true, "w", makeInput("ww" , 1), Error.init));
                assert(getResult!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w")))("www"w) == result(true, "w", makeInput("ww"w, 1), Error.init));
                assert(getResult!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w")))("www"d) == result(true, "w", makeInput("ww"d, 1), Error.init));
                assert(getResult!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w")))(testRange("www" )) == result(true, "w", makeInput(testRange("ww" ), 1), Error.init));
                assert(getResult!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w")))(testRange("www"w)) == result(true, "w", makeInput(testRange("ww"w), 1), Error.init));
                assert(getResult!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w")))(testRange("www"d)) == result(true, "w", makeInput(testRange("ww"d), 1), Error.init));

                assert(getResult!(combinateConvert!(combinateMore1!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w"))), flat))("www" ) == result(true, "ww", makeInput("w" , 2), Error.init));
                assert(getResult!(combinateConvert!(combinateMore1!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w"))), flat))("www"w) == result(true, "ww", makeInput("w"w, 2), Error.init));
                assert(getResult!(combinateConvert!(combinateMore1!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w"))), flat))("www"d) == result(true, "ww", makeInput("w"d, 2), Error.init));
                assert(getResult!(combinateConvert!(combinateMore1!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w"))), flat))(testRange("www" )) == result(true, "ww", makeInput(testRange("w" ), 2), Error.init));
                assert(getResult!(combinateConvert!(combinateMore1!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w"))), flat))(testRange("www"w)) == result(true, "ww", makeInput(testRange("w"w), 2), Error.init));
                assert(getResult!(combinateConvert!(combinateMore1!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w"))), flat))(testRange("www"d)) == result(true, "ww", makeInput(testRange("w"d), 2), Error.init));

                assert(getResult!(combinateConvert!(combinateMore1!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w"))), flat))("w" ) == result(false, "", makeInput("" ), Error(q{"w"})));
                assert(getResult!(combinateConvert!(combinateMore1!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w"))), flat))("w"w) == result(false, "", makeInput(""w), Error(q{"w"})));
                assert(getResult!(combinateConvert!(combinateMore1!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w"))), flat))("w"d) == result(false, "", makeInput(""d), Error(q{"w"})));
                assert(getResult!(combinateConvert!(combinateMore1!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w"))), flat))(testRange("w" )) == result(false, "", makeInput(testRange("" )), Error(q{"w"})));
                assert(getResult!(combinateConvert!(combinateMore1!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w"))), flat))(testRange("w"w)) == result(false, "", makeInput(testRange(""w)), Error(q{"w"})));
                assert(getResult!(combinateConvert!(combinateMore1!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w"))), flat))(testRange("w"d)) == result(false, "", makeInput(testRange(""d)), Error(q{"w"})));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // combinateNotPred
        template combinateNotPred(alias parser){
            alias None ResultType;
            static Result!(R, ResultType) parse(R)(Input!R input, auto ref memo_t memo, in CallerInformation info){
                typeof(return) result;
                result.rest = input;
                result.match = !parser.parse(input.save, memo, info).match;
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(getResult!(combinateConvert!(combinateMore1!(combinateSequence!(parseString!"w", combinateNotPred!(parseString!"s"))), flat))("wwws" ) == result(true, "ww", makeInput("ws" , 2), Error.init));
                assert(getResult!(combinateConvert!(combinateMore1!(combinateSequence!(parseString!"w", combinateNotPred!(parseString!"s"))), flat))("wwws"w) == result(true, "ww", makeInput("ws"w, 2), Error.init));
                assert(getResult!(combinateConvert!(combinateMore1!(combinateSequence!(parseString!"w", combinateNotPred!(parseString!"s"))), flat))("wwws"d) == result(true, "ww", makeInput("ws"d, 2), Error.init));
                assert(getResult!(combinateConvert!(combinateMore1!(combinateSequence!(parseString!"w", combinateNotPred!(parseString!"s"))), flat))(testRange("wwws" )) == result(true, "ww", makeInput(testRange("ws" ), 2), Error.init));
                assert(getResult!(combinateConvert!(combinateMore1!(combinateSequence!(parseString!"w", combinateNotPred!(parseString!"s"))), flat))(testRange("wwws"w)) == result(true, "ww", makeInput(testRange("ws"w), 2), Error.init));
                assert(getResult!(combinateConvert!(combinateMore1!(combinateSequence!(parseString!"w", combinateNotPred!(parseString!"s"))), flat))(testRange("wwws"d)) == result(true, "ww", makeInput(testRange("ws"d), 2), Error.init));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // combinateConvert
        template CombinateConvertType(alias converter, T){
            static if(is(converter == struct) || is(converter == class)){
                alias converter CombinateConvertType;
            }else static if(isCallable!converter){
                alias ReturnType!converter CombinateConvertType;
            }else static if(__traits(compiles, converter(T.init))){
                alias typeof(converter(T.init)) CombinateConvertType;
            }else static if(__traits(compiles, converter(T.init.field))){
                alias typeof(converter(T.init.field)) CombinateConvertType;
            }else{
                static assert(false);
            }
        }

        unittest{
            static assert(is(CombinateConvertType!(to!int, string) == int));
            static assert(is(CombinateConvertType!(to!string, int) == string));
            static const(real)[] func(T)(T t){ static assert(false); }
            static assert(is(CombinateConvertType!(func, float) == const(real)[]));
        }

        template combinateConvert(alias parser, alias converter){
            alias CombinateConvertType!(converter, ParserType!parser) ResultType;
            static Result!(R, ResultType) parse(R)(Input!R input, auto ref memo_t memo, in CallerInformation info){
                typeof(return) result;
                auto r = parser.parse(input, memo, info);
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
                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), function(string[] ws){ return ws.length; }))("www" ) == result(true, 3LU, makeInput("" , 3), Error.init));
                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), function(string[] ws){ return ws.length; }))("www"w) == result(true, 3LU, makeInput(""w, 3), Error.init));
                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), function(string[] ws){ return ws.length; }))("www"d) == result(true, 3LU, makeInput(""d, 3), Error.init));
                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), function(string[] ws){ return ws.length; }))(testRange("www" )) == result(true, 3LU, makeInput(testRange("" ), 3), Error.init));
                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), function(string[] ws){ return ws.length; }))(testRange("www"w)) == result(true, 3LU, makeInput(testRange(""w), 3), Error.init));
                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), function(string[] ws){ return ws.length; }))(testRange("www"d)) == result(true, 3LU, makeInput(testRange(""d), 3), Error.init));

                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), function(string[] ws){ return ws.length; }))("a" ) == result(false, 0LU, makeInput("" ), Error(q{"w"})));
                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), function(string[] ws){ return ws.length; }))("a"w) == result(false, 0LU, makeInput(""w), Error(q{"w"})));
                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), function(string[] ws){ return ws.length; }))("a"d) == result(false, 0LU, makeInput(""d), Error(q{"w"})));
                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), function(string[] ws){ return ws.length; }))(testRange("a" )) == result(false, 0LU, makeInput(testRange("" )), Error(q{"w"})));
                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), function(string[] ws){ return ws.length; }))(testRange("a"w)) == result(false, 0LU, makeInput(testRange(""w)), Error(q{"w"})));
                assert(getResult!(combinateConvert!(combinateMore1!(parseString!"w"), function(string[] ws){ return ws.length; }))(testRange("a"d)) == result(false, 0LU, makeInput(testRange(""d)), Error(q{"w"})));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // combinateCheck
        template combinateCheck(alias parser, alias checker){
            alias ParserType!parser ResultType;
            static Result!(R, ResultType) parse(R)(Input!R input, auto ref memo_t memo, in CallerInformation info){
                typeof(return) result;
                auto r = parser.parse(input, memo, info);
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
                assert(getResult!(combinateConvert!(combinateCheck!(combinateMore0!(parseString!"w"), function(string[] ws){ return ws.length == 5; }), flat))("wwwww" ) == result(true, "wwwww", makeInput("" , 5), Error.init));
                assert(getResult!(combinateConvert!(combinateCheck!(combinateMore0!(parseString!"w"), function(string[] ws){ return ws.length == 5; }), flat))("wwwww"w) == result(true, "wwwww", makeInput(""w, 5), Error.init));
                assert(getResult!(combinateConvert!(combinateCheck!(combinateMore0!(parseString!"w"), function(string[] ws){ return ws.length == 5; }), flat))("wwwww"d) == result(true, "wwwww", makeInput(""d, 5), Error.init));
                assert(getResult!(combinateConvert!(combinateCheck!(combinateMore0!(parseString!"w"), function(string[] ws){ return ws.length == 5; }), flat))(testRange("wwwww" )) == result(true, "wwwww", makeInput(testRange("" ), 5), Error.init));
                assert(getResult!(combinateConvert!(combinateCheck!(combinateMore0!(parseString!"w"), function(string[] ws){ return ws.length == 5; }), flat))(testRange("wwwww"w)) == result(true, "wwwww", makeInput(testRange(""w), 5), Error.init));
                assert(getResult!(combinateConvert!(combinateCheck!(combinateMore0!(parseString!"w"), function(string[] ws){ return ws.length == 5; }), flat))(testRange("wwwww"d)) == result(true, "wwwww", makeInput(testRange(""d), 5), Error.init));

                assert(getResult!(combinateConvert!(combinateCheck!(combinateMore0!(parseString!"w"), function(string[] ws){ return ws.length == 5; }), flat))("wwww" ) == result(false, "", makeInput("" ), Error("passing check")));
                assert(getResult!(combinateConvert!(combinateCheck!(combinateMore0!(parseString!"w"), function(string[] ws){ return ws.length == 5; }), flat))("wwww"w) == result(false, "", makeInput(""w), Error("passing check")));
                assert(getResult!(combinateConvert!(combinateCheck!(combinateMore0!(parseString!"w"), function(string[] ws){ return ws.length == 5; }), flat))("wwww"d) == result(false, "", makeInput(""d), Error("passing check")));
                assert(getResult!(combinateConvert!(combinateCheck!(combinateMore0!(parseString!"w"), function(string[] ws){ return ws.length == 5; }), flat))(testRange("wwww" )) == result(false, "", makeInput(testRange("" )), Error("passing check")));
                assert(getResult!(combinateConvert!(combinateCheck!(combinateMore0!(parseString!"w"), function(string[] ws){ return ws.length == 5; }), flat))(testRange("wwww"w)) == result(false, "", makeInput(testRange(""w)), Error("passing check")));
                assert(getResult!(combinateConvert!(combinateCheck!(combinateMore0!(parseString!"w"), function(string[] ws){ return ws.length == 5; }), flat))(testRange("wwww"d)) == result(false, "", makeInput(testRange(""d)), Error("passing check")));
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
                assert(getResult!(parseAnyChar!())("hoge" ) == result(true, "h", makeInput("oge" , 1), Error.init));
                assert(getResult!(parseAnyChar!())("hoge"w) == result(true, "h", makeInput("oge"w, 1), Error.init));
                assert(getResult!(parseAnyChar!())("hoge"d) == result(true, "h", makeInput("oge"d, 1), Error.init));
                assert(getResult!(parseAnyChar!())(testRange("hoge" )) == result(true, "h", makeInput(testRange("oge" ), 1), Error.init));
                assert(getResult!(parseAnyChar!())(testRange("hoge"w)) == result(true, "h", makeInput(testRange("oge"w), 1), Error.init));
                assert(getResult!(parseAnyChar!())(testRange("hoge"d)) == result(true, "h", makeInput(testRange("oge"d), 1), Error.init));

                assert(getResult!(parseAnyChar!())("\U00012345" ) == result(true, "\U00012345", makeInput("" , 1), Error.init));
                assert(getResult!(parseAnyChar!())("\U00012345"w) == result(true, "\U00012345", makeInput(""w, 1), Error.init));
                assert(getResult!(parseAnyChar!())("\U00012345"d) == result(true, "\U00012345", makeInput(""d, 1), Error.init));
                assert(getResult!(parseAnyChar!())(testRange("\U00012345" )) == result(true, "\U00012345", makeInput(testRange("" ), 1), Error.init));
                assert(getResult!(parseAnyChar!())(testRange("\U00012345"w)) == result(true, "\U00012345", makeInput(testRange(""w), 1), Error.init));
                assert(getResult!(parseAnyChar!())(testRange("\U00012345"d)) == result(true, "\U00012345", makeInput(testRange(""d), 1), Error.init));

                assert(getResult!(parseAnyChar!())("\nhoge" ) == result(true, "\n", makeInput("hoge" , 1, 2), Error.init));
                assert(getResult!(parseAnyChar!())("\nhoge"w) == result(true, "\n", makeInput("hoge"w, 1, 2), Error.init));
                assert(getResult!(parseAnyChar!())("\nhoge"d) == result(true, "\n", makeInput("hoge"d, 1, 2), Error.init));
                assert(getResult!(parseAnyChar!())(testRange("\nhoge" )) == result(true, "\n", makeInput(testRange("hoge" ), 1, 2), Error.init));
                assert(getResult!(parseAnyChar!())(testRange("\nhoge"w)) == result(true, "\n", makeInput(testRange("hoge"w), 1, 2), Error.init));
                assert(getResult!(parseAnyChar!())(testRange("\nhoge"d)) == result(true, "\n", makeInput(testRange("hoge"d), 1, 2), Error.init));

                assert(getResult!(parseAnyChar!())("" ) == result(false, "", makeInput("" ), Error("any char")));
                assert(getResult!(parseAnyChar!())(""w) == result(false, "", makeInput(""w), Error("any char")));
                assert(getResult!(parseAnyChar!())(""d) == result(false, "", makeInput(""d), Error("any char")));
                assert(getResult!(parseAnyChar!())(testRange("" )) == result(false, "", makeInput(testRange("" )), Error("any char")));
                assert(getResult!(parseAnyChar!())(testRange(""w)) == result(false, "", makeInput(testRange(""w)), Error("any char")));
                assert(getResult!(parseAnyChar!())(testRange(""d)) == result(false, "", makeInput(testRange(""d)), Error("any char")));
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
                assert(getResult!(parseSpaces!())("\t \rhoge" ) == result(true, None.init, makeInput("hoge" , 3), Error.init));
                assert(getResult!(parseSpaces!())("\t \rhoge"w) == result(true, None.init, makeInput("hoge"w, 3), Error.init));
                assert(getResult!(parseSpaces!())("\t \rhoge"d) == result(true, None.init, makeInput("hoge"d, 3), Error.init));
                assert(getResult!(parseSpaces!())(testRange("\t \rhoge" )) == result(true, None.init, makeInput(testRange("hoge" ), 3), Error.init));
                assert(getResult!(parseSpaces!())(testRange("\t \rhoge"w)) == result(true, None.init, makeInput(testRange("hoge"w), 3), Error.init));
                assert(getResult!(parseSpaces!())(testRange("\t \rhoge"d)) == result(true, None.init, makeInput(testRange("hoge"d), 3), Error.init));

                assert(getResult!(parseSpaces!())("hoge" ) == result(true, None.init, makeInput("hoge" , 0), Error.init));
                assert(getResult!(parseSpaces!())("hoge"w) == result(true, None.init, makeInput("hoge"w, 0), Error.init));
                assert(getResult!(parseSpaces!())("hoge"d) == result(true, None.init, makeInput("hoge"d, 0), Error.init));
                assert(getResult!(parseSpaces!())(testRange("hoge" )) == result(true, None.init, makeInput(testRange("hoge" ), 0), Error.init));
                assert(getResult!(parseSpaces!())(testRange("hoge"w)) == result(true, None.init, makeInput(testRange("hoge"w), 0), Error.init));
                assert(getResult!(parseSpaces!())(testRange("hoge"d)) == result(true, None.init, makeInput(testRange("hoge"d), 0), Error.init));
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
                assert(getResult!(parseIdent!())("hoge" ) == result(true, "hoge", makeInput("" , 4), Error.init));
                assert(getResult!(parseIdent!())("hoge"w) == result(true, "hoge", makeInput(""w, 4), Error.init));
                assert(getResult!(parseIdent!())("hoge"d) == result(true, "hoge", makeInput(""d, 4), Error.init));
                assert(getResult!(parseIdent!())(testRange("hoge" )) == result(true, "hoge", makeInput(testRange("" ), 4), Error.init));
                assert(getResult!(parseIdent!())(testRange("hoge"w)) == result(true, "hoge", makeInput(testRange(""w), 4), Error.init));
                assert(getResult!(parseIdent!())(testRange("hoge"d)) == result(true, "hoge", makeInput(testRange(""d), 4), Error.init));

                assert(getResult!(parseIdent!())("_0" ) == result(true, "_0", makeInput("" , 2), Error.init));
                assert(getResult!(parseIdent!())("_0"w) == result(true, "_0", makeInput(""w, 2), Error.init));
                assert(getResult!(parseIdent!())("_0"d) == result(true, "_0", makeInput(""d, 2), Error.init));
                assert(getResult!(parseIdent!())(testRange("_0" )) == result(true, "_0", makeInput(testRange("" ), 2), Error.init));
                assert(getResult!(parseIdent!())(testRange("_0"w)) == result(true, "_0", makeInput(testRange(""w), 2), Error.init));
                assert(getResult!(parseIdent!())(testRange("_0"d)) == result(true, "_0", makeInput(testRange(""d), 2), Error.init));

                assert(getResult!(parseIdent!())("0" ) == result(false, "", makeInput("" ), Error("c: 'A' <= c <= 'Z'")));
                assert(getResult!(parseIdent!())("0"w) == result(false, "", makeInput(""w), Error("c: 'A' <= c <= 'Z'")));
                assert(getResult!(parseIdent!())("0"d) == result(false, "", makeInput(""d), Error("c: 'A' <= c <= 'Z'")));
                assert(getResult!(parseIdent!())(testRange("0" )) == result(false, "", makeInput(testRange("" )), Error("c: 'A' <= c <= 'Z'")));
                assert(getResult!(parseIdent!())(testRange("0"w)) == result(false, "", makeInput(testRange(""w)), Error("c: 'A' <= c <= 'Z'")));
                assert(getResult!(parseIdent!())(testRange("0"d)) == result(false, "", makeInput(testRange(""d)), Error("c: 'A' <= c <= 'Z'")));

                assert(getResult!(parseIdent!())("あ" ) == result(false, "", makeInput("" ), Error("c: 'A' <= c <= 'Z'")));
                assert(getResult!(parseIdent!())("あ"w) == result(false, "", makeInput(""w), Error("c: 'A' <= c <= 'Z'")));
                assert(getResult!(parseIdent!())("あ"d) == result(false, "", makeInput(""d), Error("c: 'A' <= c <= 'Z'")));
                assert(getResult!(parseIdent!())(testRange("あ" )) == result(false, "", makeInput(testRange("" )), Error("c: 'A' <= c <= 'Z'")));
                assert(getResult!(parseIdent!())(testRange("あ"w)) == result(false, "", makeInput(testRange(""w)), Error("c: 'A' <= c <= 'Z'")));
                assert(getResult!(parseIdent!())(testRange("あ"d)) == result(false, "", makeInput(testRange(""d)), Error("c: 'A' <= c <= 'Z'")));
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
                assert(getResult!(parseStringLiteral!())(`"表が怖い噂のソフト"` ) == result(true, `"表が怖い噂のソフト"`, makeInput("" , 11), Error.init));
                assert(getResult!(parseStringLiteral!())(`"表が怖い噂のソフト"`w) == result(true, `"表が怖い噂のソフト"`, makeInput(""w, 11), Error.init));
                assert(getResult!(parseStringLiteral!())(`"表が怖い噂のソフト"`d) == result(true, `"表が怖い噂のソフト"`, makeInput(""d, 11), Error.init));
                assert(getResult!(parseStringLiteral!())(testRange(`"表が怖い噂のソフト"` )) == result(true, `"表が怖い噂のソフト"`, makeInput(testRange("" ), 11), Error.init));
                assert(getResult!(parseStringLiteral!())(testRange(`"表が怖い噂のソフト"`w)) == result(true, `"表が怖い噂のソフト"`, makeInput(testRange(""w), 11), Error.init));
                assert(getResult!(parseStringLiteral!())(testRange(`"表が怖い噂のソフト"`d)) == result(true, `"表が怖い噂のソフト"`, makeInput(testRange(""d), 11), Error.init));

                assert(getResult!(parseStringLiteral!())(`r"表が怖い噂のソフト"` ) == result(true, `r"表が怖い噂のソフト"`, makeInput("" , 12), Error.init));
                assert(getResult!(parseStringLiteral!())(`r"表が怖い噂のソフト"`w) == result(true, `r"表が怖い噂のソフト"`, makeInput(""w, 12), Error.init));
                assert(getResult!(parseStringLiteral!())(`r"表が怖い噂のソフト"`d) == result(true, `r"表が怖い噂のソフト"`, makeInput(""d, 12), Error.init));
                assert(getResult!(parseStringLiteral!())(testRange(`r"表が怖い噂のソフト"` )) == result(true, `r"表が怖い噂のソフト"`, makeInput(testRange("" ), 12), Error.init));
                assert(getResult!(parseStringLiteral!())(testRange(`r"表が怖い噂のソフト"`w)) == result(true, `r"表が怖い噂のソフト"`, makeInput(testRange(""w), 12), Error.init));
                assert(getResult!(parseStringLiteral!())(testRange(`r"表が怖い噂のソフト"`d)) == result(true, `r"表が怖い噂のソフト"`, makeInput(testRange(""d), 12), Error.init));

                assert(getResult!(parseStringLiteral!())("`表が怖い噂のソフト`" ) == result(true, q{`表が怖い噂のソフト`}, makeInput("" , 11), Error.init));
                assert(getResult!(parseStringLiteral!())("`表が怖い噂のソフト`"w) == result(true, q{`表が怖い噂のソフト`}, makeInput(""w, 11), Error.init));
                assert(getResult!(parseStringLiteral!())("`表が怖い噂のソフト`"d) == result(true, q{`表が怖い噂のソフト`}, makeInput(""d, 11), Error.init));
                assert(getResult!(parseStringLiteral!())(testRange("`表が怖い噂のソフト`" )) == result(true, q{`表が怖い噂のソフト`}, makeInput(testRange("" ), 11), Error.init));
                assert(getResult!(parseStringLiteral!())(testRange("`表が怖い噂のソフト`"w)) == result(true, q{`表が怖い噂のソフト`}, makeInput(testRange(""w), 11), Error.init));
                assert(getResult!(parseStringLiteral!())(testRange("`表が怖い噂のソフト`"d)) == result(true, q{`表が怖い噂のソフト`}, makeInput(testRange(""d), 11), Error.init));
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
                assert(getResult!(parseIntLiteral!())("3141" ) == result(true, 3141, makeInput("" , 4), Error.init));
                assert(getResult!(parseIntLiteral!())("3141"w) == result(true, 3141, makeInput(""w, 4), Error.init));
                assert(getResult!(parseIntLiteral!())("3141"d) == result(true, 3141, makeInput(""d, 4), Error.init));
                assert(getResult!(parseIntLiteral!())(testRange("3141" )) == result(true, 3141, makeInput(testRange("" ), 4), Error.init));
                assert(getResult!(parseIntLiteral!())(testRange("3141"w)) == result(true, 3141, makeInput(testRange(""w), 4), Error.init));
                assert(getResult!(parseIntLiteral!())(testRange("3141"d)) == result(true, 3141, makeInput(testRange(""d), 4), Error.init));

                assert(getResult!(parseIntLiteral!())("0" ) == result(true, 0, makeInput("" , 1), Error.init));
                assert(getResult!(parseIntLiteral!())("0"w) == result(true, 0, makeInput(""w, 1), Error.init));
                assert(getResult!(parseIntLiteral!())("0"d) == result(true, 0, makeInput(""d, 1), Error.init));
                assert(getResult!(parseIntLiteral!())(testRange("0" )) == result(true, 0, makeInput(testRange("" ), 1), Error.init));
                assert(getResult!(parseIntLiteral!())(testRange("0"w)) == result(true, 0, makeInput(testRange(""w), 1), Error.init));
                assert(getResult!(parseIntLiteral!())(testRange("0"d)) == result(true, 0, makeInput(testRange(""d), 1), Error.init));

                assert(getResult!(parseIntLiteral!())("0123" ) == result(true, 0, makeInput("123" , 1), Error.init));
                assert(getResult!(parseIntLiteral!())("0123"w) == result(true, 0, makeInput("123"w, 1), Error.init));
                assert(getResult!(parseIntLiteral!())("0123"d) == result(true, 0, makeInput("123"d, 1), Error.init));
                assert(getResult!(parseIntLiteral!())(testRange("0123" )) == result(true, 0, makeInput(testRange("123" ), 1), Error.init));
                assert(getResult!(parseIntLiteral!())(testRange("0123"w)) == result(true, 0, makeInput(testRange("123"w), 1), Error.init));
                assert(getResult!(parseIntLiteral!())(testRange("0123"d)) == result(true, 0, makeInput(testRange("123"d), 1), Error.init));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

string generateParsers(size_t callerLine = __LINE__, string callerFile = __FILE__)(string src){
    return src.parse!(defs, callerLine, callerFile);
}

string getSource(size_t callerLine = __LINE__, string callerFile = __FILE__)(string src){
    return src.getResult!(defs!(), callerLine, callerFile).value;
}

auto getResult(alias fun, size_t callerLine = __LINE__, string callerFile = __FILE__, R)(R input){
    return fun.parse(Input!R(input, 0, 1), null, new CallerInformation(callerLine, callerFile));
}

auto parse(alias fun, size_t callerLine = __LINE__, string callerFile = __FILE__)(string src){
    auto result = src.getResult!(fun!(), callerLine, callerFile);
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
            Result!(string, ResultType) parse()(Input!string input, auto ref memo_t memo, in CallerInformation info){
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
                ).parse(input, memo, info);
            }
        }

        unittest{
            enum dg = {
                assert(getResult!(arch!("(", ")"))("(a(i(u)e)o())") == result(true, "(a(i(u)e)o())", makeInput("", 13), Error.init));
                assert(getResult!(arch!("[", "]"))("[a[i[u]e]o[]]") == result(true, "[a[i[u]e]o[]]", makeInput("", 13), Error.init));
                assert(getResult!(arch!("{", "}"))("{a{i{u}e}o{}}") == result(true, "{a{i{u}e}o{}}", makeInput("", 13), Error.init));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // func
        template func(){
            alias string ResultType;
            Result!(string, ResultType) parse()(Input!string input, auto ref memo_t memo, in CallerInformation info){
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
                ).parse(input, memo, info);
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
                Result!(string, ResultType) parse()(Input!string input, auto ref memo_t memo, in CallerInformation info){
                    return combinateConvert!(
                        combinateSequence!(
                            getCallerLine!(),
                            getLine!(),
                            id!()
                        ),
                        function(size_t callerLine, size_t line, string id) => " #line " ~ (callerLine + line - 1).to!string() ~ "\n" ~ id ~ "!()"
                    ).parse(input, memo, info);
                }
            }else{
                Result!(string, ResultType) parse()(Input!string input, auto ref memo_t memo, in CallerInformation info){
                    return combinateConvert!(
                        combinateSequence!(
                            getCallerLine!(),
                            getLine!(),
                            id!()
                        ),
                        function(size_t callerLine, size_t line, string id) => id ~ "!()"
                    ).parse(input, memo, info);
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
                        assert(result.value == " #line " ~ (__LINE__ - 3).to!string() ~ "\nA!()");
                    }
                    {
                        auto result = getResult!(nonterminal!())("int");
                        assert(result.match);
                        assert(result.rest.empty);
                        assert(result.value == " #line " ~ (__LINE__ - 3).to!string() ~ "\nint!()");
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
            Result!(string, ResultType) parse()(Input!string input, auto ref memo_t memo, in CallerInformation info){
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
                ).parse(input, memo, info);
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
            Result!(string, ResultType) parse()(Input!string input, auto ref memo_t memo, in CallerInformation info){
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
                ).parse(input, memo, info);
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
            Result!(string, ResultType) parse()(Input!string input, auto ref memo_t memo, in CallerInformation info){
                return combinateConvert!(
                    combinateNone!(
                        parseString!"$"
                    ),
                    function() => "parseEOF!()"
                ).parse(input, memo, info);
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
            Result!(string, ResultType) parse()(Input!string input, auto ref memo_t memo, in CallerInformation info){
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
                ).parse(input, memo, info);
            }
        }

        template charRange(){
            alias string ResultType;
            Result!(string, ResultType) parse()(Input!string input, auto ref memo_t memo, in CallerInformation info){
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
                ).parse(input, memo, info);
            }
        }

        template oneChar(){
            alias string ResultType;
            Result!(string, ResultType) parse()(Input!string input, auto ref memo_t memo, in CallerInformation info){
                return combinateConvert!(
                    combinateChoice!(
                        parseEscapeSequence!(),
                        parseAnyChar!()
                    ),
                    function(string c) => "parseString!\"" ~ c ~ "\""
                ).parse(input, memo, info);
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
            Result!(string, ResultType) parse()(Input!string input, auto ref memo_t memo, in CallerInformation info){
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
                    function(string[] strs) => "parseString!\"" ~ strs.flat ~ "\""
                ).parse(input, memo, info);
            }
        }

        unittest{
            enum dg = {
                {
                    auto result = getResult!(stringLit!())("\"hello\nworld\" ");
                    assert(result.match);
                    assert(result.rest.range == " ");
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
            Result!(string, ResultType) parse()(Input!string input, auto ref memo_t memo, in CallerInformation info){
                return combinateChoice!(
                    rangeLit!(),
                    stringLit!(),
                    eofLit!(),
                ).parse(input, memo, info);
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
            Result!(string, ResultType) parse()(Input!string input, auto ref memo_t memo, in CallerInformation info){
                return combinateChoice!(
                    literal!(),
                    nonterminal!(),
                    combinateSequence!(
                        combinateNone!(
                            parseString!"("
                        ),
                        parseSpaces!(),
                        convExp!(),
                        parseSpaces!(),
                        combinateNone!(
                            parseString!")"
                        )
                    )
                ).parse(input, memo, info);
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
                        assert(result.value == " #line " ~ (__LINE__ - 3).to!string() ~ "\nint!()");
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
            Result!(string, ResultType) parse()(Input!string input, auto ref memo_t memo, in CallerInformation info){
                return combinateConvert!(
                    combinateSequence!(
                        combinateOption!(
                            combinateChoice!(
                                parseString!"&",
                                parseString!"^",
                                parseString!"!"
                            )
                        ),
                        primaryExp!()
                    ),
                    function(Option!string op, string primaryExp){
                        final switch(op.value){
                            case "&":{
                                return "combinateAndPred!(" ~ primaryExp ~ ")";
                            }
                            case "!":{
                                return "combinateNone!(" ~ primaryExp ~ ")";
                            }
                            case "^":{
                                return "combinateNotPred!(" ~ primaryExp ~ ")";
                            }
                            case "":{
                                return primaryExp;
                            }
                        }
                    }
                ).parse(input, memo, info);
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
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // postExp
        template postExp(){
            alias string ResultType;
            Result!(string, ResultType) parse()(Input!string input, auto ref memo_t memo, in CallerInformation info){
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
                ).parse(input, memo, info);
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
            Result!(string, ResultType) parse()(Input!string input, auto ref memo_t memo, in CallerInformation info){
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
                ).parse(input, memo, info);
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
            Result!(string, ResultType) parse()(Input!string input, auto ref memo_t memo, in CallerInformation info){
                return combinateConvert!(
                    combinateMore1!(
                        optionExp!(),
                        parseSpaces!()
                    ),
                    function(string[] optionExps) => optionExps.length > 1 ? "combinateSequence!("~optionExps.join(",")~")" : optionExps[0]
                ).parse(input, memo, info);
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
            Result!(string, ResultType) parse()(Input!string input, auto ref memo_t memo, in CallerInformation info){
                return combinateConvert!(
                    combinateSequence!(
                        seqExp!(),
                        combinateMore0!(
                            combinateSequence!(
                                parseSpaces!(),
                                combinateNone!(
                                    parseString!">>"
                                ),
                                parseSpaces!(),
                                combinateChoice!(
                                    func!(),
                                    typeName!()
                                )
                            )
                        )
                    ),
                    function(string seqExp, string[] funcs){
                        string result = seqExp;
                        foreach(func; funcs){
                            result = "combinateConvert!(" ~ result ~ "," ~ func ~ ")";
                        }
                        return result;
                    }
                ).parse(input, memo, info);
            }
        }

        unittest{
            enum dg = {
                {
                    auto result = getResult!(convExp!())(q{!"hello" $ >> {return false;}});
                    assert(result.match);
                    assert(result.rest.empty);
                    assert(
                        result.value ==
                        "combinateConvert!("
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
                    auto result = getResult!(convExp!())(q{"hello" >> flat >> to!int});
                    assert(result.match);
                    assert(result.rest.empty);
                    assert(
                        result.value ==
                        "combinateConvert!("
                            "combinateConvert!("
                                "parseString!\"hello\","
                                "flat"
                            "),"
                            "to!int"
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
            Result!(string, ResultType) parse()(Input!string input, auto ref memo_t memo, in CallerInformation info){
                return combinateConvert!(
                    combinateSequence!(
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
                    function(string convExp, string[] convExps) => convExps.length ? "combinateChoice!(" ~ convExp ~ "," ~ convExps.join(",") ~ ")" : convExp
                ).parse(input, memo, info);
            }
        }

        unittest{
            enum dg = {
                {
                    auto result = getResult!(choiceExp!())(`!$* / (&(^"a"))?`);
                    assert(result.match);
                    assert(result.rest.empty);
                    assert(
                        result.value ==
                        "combinateChoice!("
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
            Result!(string, ResultType) parse()(Input!string input, auto ref memo_t memo, in CallerInformation info){
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
                            "static Result!(R, ResultType) parse(R)(Input!R input, auto ref memo_t memo, in CallerInformation info){"
                                "return "~choiceExp~".parse(input, memo, info);"
                            "}"
                        "}"
                ).parse(input, memo, info);
            }
        }

        unittest{
            enum dg = {
                cast(void)__LINE__;
                {
                    auto result = getResult!(def!())(`bool hoge = !"hello" $ >> {return false;};`);
                    assert(result.match);
                    assert(result.rest.empty);
                    assert(
                        result.value ==
                        "template hoge(){"
                            "alias bool ResultType;"
                            "static Result!(R, ResultType) parse(R)(Input!R input, auto ref memo_t memo, in CallerInformation info){"
                                "return combinateConvert!("
                                    "combinateSequence!("
                                        "combinateNone!("
                                            "parseString!\"hello\""
                                        "),"
                                        "parseEOF!()"
                                    "),"
                                    "function(){"
                                        "return false;"
                                    "}"
                                ").parse(input, memo, info);"
                            "}"
                        "}"
                    );
                }
                {
                    auto result = getResult!(def!())(`None recursive = A $;`);
                    assert(result.match);
                    assert(result.rest.empty);
                    version(Issue_8038_Fixed){
                        assert(
                            result.value ==
                            "template recursive(){"
                                "alias None ResultType;"
                                "static Result!(R, ResultType) parse(R)(Input!R input, auto ref memo_t memo, in CallerInformation info){"
                                    "return combinateSequence!("
                                        " #line " ~ (__LINE__ - 9).to!string() ~ "\nA!(),"
                                        "parseEOF!()"
                                    ").parse(input, memo, info);"
                                "}"
                            "}"
                        );
                    }else{
                        assert(
                            result.value ==
                            "template recursive(){"
                                "alias None ResultType;"
                                "static Result!(R, ResultType) parse(R)(Input!R input, auto ref memo_t memo, in CallerInformation info){"
                                    "return combinateSequence!("
                                        "A!(),"
                                        "parseEOF!()"
                                    ").parse(input, memo, info);"
                                "}"
                            "}"
                        );
                    }
                }
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        };

    // defs
        template defs(){
            alias string ResultType;
            Result!(string, ResultType) parse()(Input!string input, auto ref memo_t memo, in CallerInformation info){
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
                ).parse(input, memo, info);
            }
        }

        unittest{
            enum dg = {
                cast(void)__LINE__;
                auto result = getResult!(defs!())(q{
                    bool hoge = !"hello" $ >> {return false;};
                    Tuple!piyo hoge2 = hoge* >> {return tuple("foo");};
                });
                assert(result.match);
                assert(result.rest.empty);
                version(Issue_8038_Fixed){
                    assert(
                        result.value ==
                        "template hoge(){"
                            "alias bool ResultType;"
                            "static Result!(R, ResultType) parse(R)(Input!R input, auto ref memo_t memo, in CallerInformation info){"
                                "return combinateConvert!("
                                    "combinateSequence!("
                                        "combinateNone!("
                                            "parseString!\"hello\""
                                        "),"
                                        "parseEOF!()"
                                    "),"
                                    "function(){"
                                        "return false;"
                                    "}"
                                ").parse(input, memo, info);"
                            "}"
                        "}"
                        "template hoge2(){"
                            "alias Tuple!piyo ResultType;"
                            "static Result!(R, ResultType) parse(R)(Input!R input, auto ref memo_t memo, in CallerInformation info){"
                                "return combinateConvert!("
                                    "combinateMore0!("
                                        " #line " ~ (__LINE__ - 27).to!string() ~ "\nhoge!()"
                                    "),"
                                    "function(){"
                                        "return tuple(\"foo\");"
                                    "}"
                                ").parse(input, memo, info);"
                            "}"
                        "}"
                    );
                }else{
                    assert(
                        result.value ==
                        "template hoge(){"
                            "alias bool ResultType;"
                            "static Result!(R, ResultType) parse(R)(Input!R input, auto ref memo_t memo, in CallerInformation info){"
                                "return combinateConvert!("
                                    "combinateSequence!("
                                        "combinateNone!("
                                            "parseString!\"hello\""
                                        "),"
                                        "parseEOF!()"
                                    "),"
                                    "function(){"
                                        "return false;"
                                    "}"
                                ").parse(input, memo, info);"
                            "}"
                        "}"
                        "template hoge2(){"
                            "alias Tuple!piyo ResultType;"
                            "static Result!(R, ResultType) parse(R)(Input!R input, auto ref memo_t memo, in CallerInformation info){"
                                "return combinateConvert!("
                                    "combinateMore0!("
                                        "hoge!()"
                                    "),"
                                    "function(){"
                                        "return tuple(\"foo\");"
                                    "}"
                                ").parse(input, memo, info);"
                            "}"
                        "}"
                    );
                }
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        };

