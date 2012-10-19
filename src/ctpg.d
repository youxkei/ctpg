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

import std.array:       save, empty, join, front;
import std.conv:        to, text;
import std.range:       isInputRange, isForwardRange, ElementType;
import std.traits:      CommonType, isCallable, ReturnType, isSomeChar, isSomeString, Unqual, isAssignable, isArray;
import std.typetuple:   staticMap, TypeTuple;
import std.metastrings: toStringNow;

import std.utf: decode;

public import std.typecons: Tuple, isTuple, tuple;

alias Tuple!() None;

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
        ParseResult!(R, ResultType) parse(R)(Input!R input, in CallerInfo info){
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

// struct Input
    struct Input(Range){
        Range source;
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
        Input save(){
            return Input(source.save, position, line, state);
        }

        @property
        bool empty(){
            return source.empty;
        }

        equals_t opEquals(Input rhs){
            return source == rhs.source && position == rhs.position && line == rhs.line && state == rhs.state;
        }
    }

    Input!Range makeInput(Range)(Range source, size_t position = 0, size_t line = 1, StateType state = StateType.init){
        return Input!Range(source, position, line, state);
    }

// struct ParseResult
    struct ParseResult(Range, T){
        bool match;
        T value;
        Input!Range next;
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

    ParseResult!(Range, T) makeParseResult(Range, T)(bool match, T value, Input!Range next, Error error = Error.init){
        return ParseResult!(Range, T)(match, value, next, error);
    }

// struct Error
    struct Error{
        invariant(){
            assert(line >= 1);
        }

        string msg;
        size_t position;
        size_t line = 1;

        pure @safe nothrow const
        bool opEquals(in Error rhs){
            return msg == rhs.msg && position == rhs.position && line == rhs.line;
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
            static ParseResult!(R, ResultType) parse(R)(Input!R input, in CallerInfo info){
                return makeParseResult(true, None.init, input, Error.init);
            }
        }

    // failure
        template failure(){
            alias None ResultType;
            static ParseResult!(R, ResultType) parse(R)(Input!R input, in CallerInfo info){
                return makeParseResult(false, None.init, Input!R.init, Error("", input.position, input.line));
            }
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
            static ParseResult!(R, ResultType) parse(R)(Input!R _input, in CallerInfo info){
                auto input = _input; // Somehow this parser doesn't work well without this line.
                typeof(return) result;
                static if(isSomeString!R){
                    if(input.source.length){
                        size_t idx;
                        dchar c = decode(input.source, idx);
                        if(low <= c && c <= high){
                            result.match = true;
                            static if(is(R == string)){
                                result.value = input.source[0..idx];
                            }else{
                                result.value = c.to!string();
                            }
                            result.next.source = input.source[idx..$];
                            result.next.line = c == '\n' ? input.line + 1 : input.line;
                            result.next.position = input.position + idx;
                            result.next.state = input.state;
                            return result;
                        }else{
                            if(low == dchar.min && high == dchar.max){
                                result.error = Error("any char expected but '" ~ c.to!string() ~ "' found", input.position, input.line);
                            }else{
                                result.error = Error("'" ~ low.to!string() ~ "' ~ '" ~ high.to!string() ~ "' expected but '" ~ c.to!string() ~ "' found", input.position, input.line);
                            }
                        }
                    }else{
                        if(low == dchar.min && high == dchar.max){
                            result.error = Error("any char expected but EOF found", input.position, input.line);
                        }else{
                            result.error = Error("'" ~ low.to!string() ~ "' ~ '" ~ high.to!string() ~ "' expected but EOF found", input.position, input.line);
                        }
                    }
                }else static if(isCharRange!R){
                    if(!input.source.empty){
                        size_t advance;
                        dchar c = decodeRange(input.source, advance);
                        if(low <= c && c <= high){
                            result.match = true;
                            result.value = c.to!string();
                            result.next.source = input.source;
                            result.next.line = c == '\n' ? input.line + 1 : input.line;
                            result.next.position = input.position + advance;
                            result.next.state = input.state;
                            return result;
                        }else{
                            if(low == dchar.min && high == dchar.max){
                                result.error = Error("any char is expected but '" ~ c.to!string() ~ "' found", input.position, input.line);
                            }else{
                                result.error = Error("'" ~ low.to!string() ~ "' ~ '" ~ high.to!string() ~ "' expected but '" ~ c.to!string() ~ "' found", input.position, input.line);
                            }
                        }
                    }else{
                        if(low == dchar.min && high == dchar.max){
                            result.error = Error("any char expected but EOF found", input.position, input.line);
                        }else{
                            result.error = Error("'" ~ low.to!string() ~ "' ~ '" ~ high.to!string() ~ "' expected but EOF found", input.position, input.line);
                        }
                    }
                }else{
                    throw new Exception("");
                }
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(parseCharRange!('a', 'z').parse(makeInput("hoge"             ), new CallerInfo(0, "")) == makeParseResult(true, "h", makeInput("oge"             , 1)));
                assert(parseCharRange!('a', 'z').parse(makeInput("hoge"w            ), new CallerInfo(0, "")) == makeParseResult(true, "h", makeInput("oge"w            , 1)));
                assert(parseCharRange!('a', 'z').parse(makeInput("hoge"d            ), new CallerInfo(0, "")) == makeParseResult(true, "h", makeInput("oge"d            , 1)));
                assert(parseCharRange!('a', 'z').parse(makeInput("hoge" .testRange()), new CallerInfo(0, "")) == makeParseResult(true, "h", makeInput("oge" .testRange(), 1)));
                assert(parseCharRange!('a', 'z').parse(makeInput("hoge"w.testRange()), new CallerInfo(0, "")) == makeParseResult(true, "h", makeInput("oge"w.testRange(), 1)));
                assert(parseCharRange!('a', 'z').parse(makeInput("hoge"d.testRange()), new CallerInfo(0, "")) == makeParseResult(true, "h", makeInput("oge"d.testRange(), 1)));

                assert(parseCharRange!('\u0100', '\U0010FFFF').parse(makeInput("\U00012345hoge"             ), new CallerInfo(0, "")) == makeParseResult(true, "\U00012345", makeInput("hoge"             , 4)));
                assert(parseCharRange!('\u0100', '\U0010FFFF').parse(makeInput("\U00012345hoge"w            ), new CallerInfo(0, "")) == makeParseResult(true, "\U00012345", makeInput("hoge"w            , 2)));
                assert(parseCharRange!('\u0100', '\U0010FFFF').parse(makeInput("\U00012345hoge"d            ), new CallerInfo(0, "")) == makeParseResult(true, "\U00012345", makeInput("hoge"d            , 1)));
                assert(parseCharRange!('\u0100', '\U0010FFFF').parse(makeInput("\U00012345hoge" .testRange()), new CallerInfo(0, "")) == makeParseResult(true, "\U00012345", makeInput("hoge" .testRange(), 4)));
                assert(parseCharRange!('\u0100', '\U0010FFFF').parse(makeInput("\U00012345hoge"w.testRange()), new CallerInfo(0, "")) == makeParseResult(true, "\U00012345", makeInput("hoge"w.testRange(), 2)));
                assert(parseCharRange!('\u0100', '\U0010FFFF').parse(makeInput("\U00012345hoge"d.testRange()), new CallerInfo(0, "")) == makeParseResult(true, "\U00012345", makeInput("hoge"d.testRange(), 1)));

                assert(parseCharRange!('\u0100', '\U0010FFFF').parse(makeInput("hello world"             ), new CallerInfo(0, "")) == makeParseResult(false, "", makeInput(""             ), Error("'\u0100' ~ '\U0010FFFF' expected but 'h' found")));
                assert(parseCharRange!('\u0100', '\U0010FFFF').parse(makeInput("hello world"w            ), new CallerInfo(0, "")) == makeParseResult(false, "", makeInput(""w            ), Error("'\u0100' ~ '\U0010FFFF' expected but 'h' found")));
                assert(parseCharRange!('\u0100', '\U0010FFFF').parse(makeInput("hello world"d            ), new CallerInfo(0, "")) == makeParseResult(false, "", makeInput(""d            ), Error("'\u0100' ~ '\U0010FFFF' expected but 'h' found")));
                assert(parseCharRange!('\u0100', '\U0010FFFF').parse(makeInput("hello world" .testRange()), new CallerInfo(0, "")) == makeParseResult(false, "", makeInput("" .testRange()), Error("'\u0100' ~ '\U0010FFFF' expected but 'h' found")));
                assert(parseCharRange!('\u0100', '\U0010FFFF').parse(makeInput("hello world"w.testRange()), new CallerInfo(0, "")) == makeParseResult(false, "", makeInput(""w.testRange()), Error("'\u0100' ~ '\U0010FFFF' expected but 'h' found")));
                assert(parseCharRange!('\u0100', '\U0010FFFF').parse(makeInput("hello world"d.testRange()), new CallerInfo(0, "")) == makeParseResult(false, "", makeInput(""d.testRange()), Error("'\u0100' ~ '\U0010FFFF' expected but 'h' found")));

                try{
                    scope(success) assert(false);
                    auto result = parseCharRange!('\u0100', '\U0010FFFF').parse(makeInput([0, 0]), new CallerInfo(0, ""));
                }catch(Exception ex){}
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

        template parseAnyChar(){
            alias parseCharRange!(dchar.min, dchar.max) parseAnyChar;
        }

        alias parseAnyChar any;

        unittest{
            enum dg = {
                assert(parseAnyChar!().parse(makeInput("hoge"), new CallerInfo(0, "")) == makeParseResult(true, "h", makeInput("oge", 1)));
                assert(parseAnyChar!().parse(makeInput("\U00012345"), new CallerInfo(0, "")) == makeParseResult(true, "\U00012345", makeInput("", 4)));
                assert(parseAnyChar!().parse(makeInput("\nhoge"), new CallerInfo(0, "")) == makeParseResult(true, "\n", makeInput("hoge", 1, 2)));
                assert(parseAnyChar!().parse(makeInput(""), new CallerInfo(0, "")) == makeParseResult(false, "", makeInput(""), Error("any char expected but EOF found")));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
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
            static ParseResult!(R, ResultType) parse(R)(Input!R _input, in CallerInfo info){
                auto input = _input; // Somehow this parser doesn't work well without this line.
                enum lines = str.countLines();
                size_t idx;
                typeof(return) result;
                static if(isSomeString!R){
                    enum convertedString = staticConvertString!(str, R);
                    if(input.source.length < convertedString.length){
                        result.error = Error(text("'", str, "' expected but EOF found"), input.position, input.line);
                    }else if(convertedString != input.source[0..convertedString.length]){
                        result.error = Error(text("'", str, "' expected but '", input.source.decode(idx), "' found"), input.position, input.line);
                    }else{
                        result.match = true;
                        result.value = str;
                        result.next.source = input.source[convertedString.length..$];
                        result.next.line = input.line + lines;
                        result.next.position = input.position + convertedString.length;
                        result.next.state = input.state;
                    }
                }else static if(isCharRange!R){
                    enum convertedString = staticConvertString!(str, R);
                    auto saved = input.source.save;
                    foreach(i, c; convertedString){
                        if(input.source.empty){
                            result.error = Error("'" ~ str ~ "' expected but EOF found", input.position, input.line);
                            goto Lerror;
                        }else if(c != input.source.front){
                            result.error = Error("'" ~ str ~ "' expected but '" ~ saved.decodeRange(idx).to!string() ~ "' found", input.position, input.line);
                            goto Lerror;
                        }else{
                            input.source.popFront;
                        }
                    }
                    result.match = true;
                    result.value = str;
                    result.next.source = input.source;
                    result.next.line = input.line + lines;
                    result.next.position = input.position + convertedString.length;
                    result.next.state = input.state;

                    Lerror:{}
                }else{
                    throw new Exception("");
                }
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(parseString!"hello".parse(makeInput("hello world"             ), new CallerInfo(0, "")) == makeParseResult(true, "hello", makeInput(" world"             , 5)));
                assert(parseString!"hello".parse(makeInput("hello world"w            ), new CallerInfo(0, "")) == makeParseResult(true, "hello", makeInput(" world"w            , 5)));
                assert(parseString!"hello".parse(makeInput("hello world"d            ), new CallerInfo(0, "")) == makeParseResult(true, "hello", makeInput(" world"d            , 5)));
                assert(parseString!"hello".parse(makeInput("hello world" .testRange()), new CallerInfo(0, "")) == makeParseResult(true, "hello", makeInput(" world" .testRange(), 5)));
                assert(parseString!"hello".parse(makeInput("hello world"w.testRange()), new CallerInfo(0, "")) == makeParseResult(true, "hello", makeInput(" world"w.testRange(), 5)));
                assert(parseString!"hello".parse(makeInput("hello world"d.testRange()), new CallerInfo(0, "")) == makeParseResult(true, "hello", makeInput(" world"d.testRange(), 5)));

                assert(parseString!"hello".parse(makeInput("hello"             ), new CallerInfo(0, "")) == makeParseResult(true, "hello", makeInput(""             , 5)));
                assert(parseString!"hello".parse(makeInput("hello"w            ), new CallerInfo(0, "")) == makeParseResult(true, "hello", makeInput(""w            , 5)));
                assert(parseString!"hello".parse(makeInput("hello"d            ), new CallerInfo(0, "")) == makeParseResult(true, "hello", makeInput(""d            , 5)));
                assert(parseString!"hello".parse(makeInput("hello" .testRange()), new CallerInfo(0, "")) == makeParseResult(true, "hello", makeInput("" .testRange(), 5)));
                assert(parseString!"hello".parse(makeInput("hello"w.testRange()), new CallerInfo(0, "")) == makeParseResult(true, "hello", makeInput(""w.testRange(), 5)));
                assert(parseString!"hello".parse(makeInput("hello"d.testRange()), new CallerInfo(0, "")) == makeParseResult(true, "hello", makeInput(""d.testRange(), 5)));


                assert(parseString!"表が怖い".parse(makeInput("表が怖い噂のソフト"             ), new CallerInfo(0, "")) == makeParseResult(true, "表が怖い", makeInput("噂のソフト"             , 12)));
                assert(parseString!"表が怖い".parse(makeInput("表が怖い噂のソフト"w            ), new CallerInfo(0, "")) == makeParseResult(true, "表が怖い", makeInput("噂のソフト"w            ,  4)));
                assert(parseString!"表が怖い".parse(makeInput("表が怖い噂のソフト"d            ), new CallerInfo(0, "")) == makeParseResult(true, "表が怖い", makeInput("噂のソフト"d            ,  4)));
                assert(parseString!"表が怖い".parse(makeInput("表が怖い噂のソフト" .testRange()), new CallerInfo(0, "")) == makeParseResult(true, "表が怖い", makeInput("噂のソフト" .testRange(), 12)));
                assert(parseString!"表が怖い".parse(makeInput("表が怖い噂のソフト"w.testRange()), new CallerInfo(0, "")) == makeParseResult(true, "表が怖い", makeInput("噂のソフト"w.testRange(),  4)));
                assert(parseString!"表が怖い".parse(makeInput("表が怖い噂のソフト"d.testRange()), new CallerInfo(0, "")) == makeParseResult(true, "表が怖い", makeInput("噂のソフト"d.testRange(),  4)));

                assert(parseString!"hello".parse(makeInput("hllo world"             ), new CallerInfo(0, "")) == makeParseResult(false, "", makeInput(""             ), Error("'hello' expected but 'h' found", 0)));
                assert(parseString!"hello".parse(makeInput("hllo world"w            ), new CallerInfo(0, "")) == makeParseResult(false, "", makeInput(""w            ), Error("'hello' expected but 'h' found", 0)));
                assert(parseString!"hello".parse(makeInput("hllo world"d            ), new CallerInfo(0, "")) == makeParseResult(false, "", makeInput(""d            ), Error("'hello' expected but 'h' found", 0)));
                assert(parseString!"hello".parse(makeInput("hllo world" .testRange()), new CallerInfo(0, "")) == makeParseResult(false, "", makeInput("" .testRange()), Error("'hello' expected but 'h' found", 0)));
                assert(parseString!"hello".parse(makeInput("hllo world"w.testRange()), new CallerInfo(0, "")) == makeParseResult(false, "", makeInput(""w.testRange()), Error("'hello' expected but 'h' found", 0)));
                assert(parseString!"hello".parse(makeInput("hllo world"d.testRange()), new CallerInfo(0, "")) == makeParseResult(false, "", makeInput(""d.testRange()), Error("'hello' expected but 'h' found", 0)));

                try{
                    scope(success) assert(false);
                    auto result = parseString!"hello".parse(makeInput([0, 0]), new CallerInfo(0, ""));
                }catch(Exception ex){}
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // parseEOF
        template parseEOF(){
            alias None ResultType;
            static ParseResult!(R, ResultType) parse(R)(Input!R input, in CallerInfo info){
                typeof(return) result;
                if(input.source.empty){
                    result.match = true;
                    result.next.source = input.source;
                    result.next.line = input.line;
                    result.next.position = input.position;
                    result.next.state = input.state;
                }else{
                    size_t idx;
                    static if(isSomeString!R){
                        result.error = Error("EOF expected but '" ~ input.source.decode(idx).to!string() ~ "' found", input.position, input.line);
                    }else static if(isCharRange!R){
                        result.error = Error("EOF expected but '" ~ input.source.decodeRange(idx).to!string() ~ "' found", input.position, input.line);
                    }else{
                        result.error = Error("EOF expected but '" ~ input.source.front.to!string() ~ "' found", input.position, input.line);
                    }
                }
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(parseEOF!().parse(makeInput(""             ), new CallerInfo(0, "")) == makeParseResult(true, None.init, makeInput(""             , 0)));
                assert(parseEOF!().parse(makeInput(""w            ), new CallerInfo(0, "")) == makeParseResult(true, None.init, makeInput(""w            , 0)));
                assert(parseEOF!().parse(makeInput(""d            ), new CallerInfo(0, "")) == makeParseResult(true, None.init, makeInput(""d            , 0)));
                assert(parseEOF!().parse(makeInput("" .testRange()), new CallerInfo(0, "")) == makeParseResult(true, None.init, makeInput("" .testRange(), 0)));
                assert(parseEOF!().parse(makeInput(""w.testRange()), new CallerInfo(0, "")) == makeParseResult(true, None.init, makeInput(""w.testRange(), 0)));
                assert(parseEOF!().parse(makeInput(""d.testRange()), new CallerInfo(0, "")) == makeParseResult(true, None.init, makeInput(""d.testRange(), 0)));

                assert(parseEOF!().parse(makeInput("hoge"             ), new CallerInfo(0, "")) == makeParseResult(false, None.init, makeInput(""             ), Error("EOF expected but 'h' found")));
                assert(parseEOF!().parse(makeInput("hoge"w            ), new CallerInfo(0, "")) == makeParseResult(false, None.init, makeInput(""w            ), Error("EOF expected but 'h' found")));
                assert(parseEOF!().parse(makeInput("hoge"d            ), new CallerInfo(0, "")) == makeParseResult(false, None.init, makeInput(""d            ), Error("EOF expected but 'h' found")));
                assert(parseEOF!().parse(makeInput("hoge" .testRange()), new CallerInfo(0, "")) == makeParseResult(false, None.init, makeInput("" .testRange()), Error("EOF expected but 'h' found")));
                assert(parseEOF!().parse(makeInput("hoge"w.testRange()), new CallerInfo(0, "")) == makeParseResult(false, None.init, makeInput(""w.testRange()), Error("EOF expected but 'h' found")));
                assert(parseEOF!().parse(makeInput("hoge"d.testRange()), new CallerInfo(0, "")) == makeParseResult(false, None.init, makeInput(""d.testRange()), Error("EOF expected but 'h' found")));

                assert(parseEOF!().parse(makeInput("鬱hoge"             ), new CallerInfo(0, "")) == makeParseResult(false, None.init, makeInput(""             ), Error("EOF expected but '鬱' found")));
                assert(parseEOF!().parse(makeInput("鬱hoge"w            ), new CallerInfo(0, "")) == makeParseResult(false, None.init, makeInput(""w            ), Error("EOF expected but '鬱' found")));
                assert(parseEOF!().parse(makeInput("鬱hoge"d            ), new CallerInfo(0, "")) == makeParseResult(false, None.init, makeInput(""d            ), Error("EOF expected but '鬱' found")));
                assert(parseEOF!().parse(makeInput("鬱hoge" .testRange()), new CallerInfo(0, "")) == makeParseResult(false, None.init, makeInput("" .testRange()), Error("EOF expected but '鬱' found")));
                assert(parseEOF!().parse(makeInput("鬱hoge"w.testRange()), new CallerInfo(0, "")) == makeParseResult(false, None.init, makeInput(""w.testRange()), Error("EOF expected but '鬱' found")));
                assert(parseEOF!().parse(makeInput("鬱hoge"d.testRange()), new CallerInfo(0, "")) == makeParseResult(false, None.init, makeInput(""d.testRange()), Error("EOF expected but '鬱' found")));

                assert(parseEOF!().parse(makeInput([0, 1, 2]), new CallerInfo(0, "")) == makeParseResult(false, None.init, makeInput([0][0..0]), Error("EOF expected but '0' found")));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

// combinators
    // combinateSkip
        template combinateSkip(alias parser, alias skip){
            alias ParserType!parser ResultType;
            static ParseResult!(R, ResultType) parse(R)(Input!R input, in CallerInfo info){
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
                assert(combinateSkip!(parseString!"foo", parseString!" ").parse(makeInput(" foo"), new CallerInfo(0, "")) == makeParseResult(true, "foo", makeInput("", 4)));
                assert(combinateSkip!(parseString!"foo", parseString!" ").parse(makeInput("foo"), new CallerInfo(0, "")) == makeParseResult(true, "foo", makeInput("", 3)));
                assert(combinateSkip!(parseString!"foo", parseString!"foo").parse(makeInput("foo"), new CallerInfo(0, "")) == makeParseResult(true, "foo", makeInput("", 3)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // combinateUnTuple
        template combinateUnTuple(alias parser){
            static if(isTuple!(ParserType!parser) && ParserType!parser.Types.length == 1){
                alias ParserType!parser.Types[0] ResultType;
                static ParseResult!(R, ResultType) parse(R)(Input!R input, in CallerInfo info){
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
                assert(combinateUnTuple!(TestParser!int).parse(makeInput(""), new CallerInfo(0, "")) == makeParseResult(false, 0, makeInput("")));
                assert(combinateUnTuple!(TestParser!long).parse(makeInput(""), new CallerInfo(0, "")) == makeParseResult(false, 0L, makeInput("")));
                assert(combinateUnTuple!(TestParser!string).parse(makeInput(""), new CallerInfo(0, "")) == makeParseResult(false, "", makeInput("")));
                assert(combinateUnTuple!(TestParser!wstring).parse(makeInput(""), new CallerInfo(0, "")) == makeParseResult(false, ""w, makeInput("")));
                assert(combinateUnTuple!(TestParser!dstring).parse(makeInput(""), new CallerInfo(0, "")) == makeParseResult(false, ""d, makeInput("")));
                assert(combinateUnTuple!(TestParser!(Tuple!int)).parse(makeInput(""), new CallerInfo(0, "")) == makeParseResult(false, 0, makeInput("")));
                assert(combinateUnTuple!(TestParser!(Tuple!(int, int))).parse(makeInput(""), new CallerInfo(0, "")) == makeParseResult(false, tuple(0, 0), makeInput("")));
                assert(combinateUnTuple!(TestParser!(Tuple!(Tuple!int))).parse(makeInput(""), new CallerInfo(0, "")) == makeParseResult(false, tuple(0), makeInput("")));
                assert(combinateUnTuple!(TestParser!(Tuple!(Tuple!(int, int)))).parse(makeInput(""), new CallerInfo(0, "")) == makeParseResult(false, tuple(0, 0), makeInput("")));
                assert(combinateUnTuple!(TestParser!(Tuple!(Tuple!(int, int), int))).parse(makeInput(""), new CallerInfo(0, "")) == makeParseResult(false, tuple(tuple(0, 0), 0), makeInput("")));
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
            static ParseResult!(R, ResultType) parse(R)(Input!R input, in CallerInfo info){
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
                assert(combinateSequence!(parseString!("hello"), parseString!("world")).parse(makeInput("helloworld"), new CallerInfo(0, "")) == makeParseResult(true, tuple("hello", "world"), makeInput("", 10)));
                assert(combinateSequence!(combinateSequence!(parseString!("hello"), parseString!("world")), parseString!"!").parse(makeInput("helloworld!"), new CallerInfo(0, "")) == makeParseResult(true, tuple("hello", "world", "!"), makeInput("", 11)));
                assert(combinateSequence!(parseString!("hello"), parseString!("world")).parse(makeInput("hellovvorld"), new CallerInfo(0, "")) == makeParseResult(false, tuple("", ""), makeInput(""), Error("'world' expected but 'v' found", 5)));
                assert(combinateSequence!(parseString!("hello"), parseString!("world"), parseString!("!")).parse(makeInput("helloworld?"), new CallerInfo(0, "")) == makeParseResult(false, tuple("", "", ""), makeInput(""), Error("'!' expected but '?' found", 10)));
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
                    pragma(msg, file ~ "(" ~ toStringNow!line ~ "): Error: types of parsers: '" ~ staticMap!(ParserType, parsers).stringof[1..$-1] ~ "' should have a common convertible type");
                }else{
                    pragma(msg, __FILE__ ~ "(" ~ toStringNow!__LINE__ ~ "): Error: types of parsers: '" ~ staticMap!(ParserType, parsers).stringof[1..$-1] ~ "' should have a common convertible type");
                }
                static assert(false);
            }
            static ParseResult!(R, ResultType) parse(R)(Input!R input, in CallerInfo info){
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
                assert(combinateChoice!(parseString!"h", parseString!"w").parse(makeInput("hw"), new CallerInfo(0, "")) == makeParseResult(true, "h", makeInput("w", 1))); 
                assert(combinateChoice!(parseString!"h", parseString!"w").parse(makeInput("w"), new CallerInfo(0, "")) == makeParseResult(true, "w", makeInput("", 1)));
                assert(combinateChoice!(parseString!"h", parseString!"w").parse(makeInput(""), new CallerInfo(0, "")) == makeParseResult(false, "", makeInput(""), Error("'w' expected but EOF found", 0)));
                assert(combinateChoice!(combinateSequence!(parseString!"h", parseString!"w"), combinateSequence!(parseString!"w", parseString!"h")).parse(makeInput("h"), new CallerInfo(0, "")) == makeParseResult(false, tuple("", ""), makeInput(""), Error("'w' expected but EOF found", 1)));
                //assert(combinateChoice!(parseString!"h", combinateSequence!(parseString!"w", parseString!"w")).parse(makeInput(testRange("w"d)), new CallerInfo(0, "")) == makeParseResult(true, "w", makeInput(testRange(""d), 1)));
                //assert(combinateChoice!(__LINE__, "foo/bar.d", parseString!"h", combinateSequence!(parseString!"w", parseString!"w")).parse(makeInput(testRange("w"d)), new CallerInfo(0, "")) == makeParseResult(true, "w", makeInput(testRange(""d), 1)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // combinateMore
        template combinateMore(int n, alias parser, alias sep){
            alias ParserType!(parser)[] ResultType;
            static ParseResult!(R, ResultType) parse(R)(Input!R input, in CallerInfo info){
                typeof(return) result;
                Input!R next = input;
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
                assert(combinateMore0!(parseString!"w").parse(makeInput("www w"), new CallerInfo(0, "")) == makeParseResult(true, ["w", "w", "w"], makeInput(" w", 3), Error("'w' expected but ' ' found", 3)));
                assert(combinateMore0!(parseString!"w").parse(makeInput(" w"), new CallerInfo(0, "")) == makeParseResult(true, [""][0..0], makeInput(" w"), Error("'w' expected but ' ' found", 0)));
                assert(combinateMore0!(combinateSequence!(parseString!"w", parseString!"h")).parse(makeInput("whwhw"), new CallerInfo(0, "")) == makeParseResult(true, [tuple("w", "h"), tuple("w", "h")], makeInput("w", 4), Error("'h' expected but EOF found", 5)));
                assert(combinateMore1!(parseString!"w").parse(makeInput("www w"), new CallerInfo(0, "")) == makeParseResult(true, ["w", "w", "w"], makeInput(" w", 3), Error("'w' expected but ' ' found", 3)));
                assert(combinateMore1!(parseString!"w").parse(makeInput(" w"), new CallerInfo(0, "")) == makeParseResult(false, [""][0..0], makeInput(""), Error("'w' expected but ' ' found", 0)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // combinateOption
        template combinateOption(alias parser){
            alias Option!(ParserType!parser) ResultType;
            static ParseResult!(R, ResultType) parse(R)(Input!R input, in CallerInfo info){
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
                assert(combinateOption!(parseString!"w").parse(makeInput("w"), new CallerInfo(0, "")) == makeParseResult(true, makeOption(true, "w"), makeInput("", 1)));
                assert(combinateOption!(parseString!"w").parse(makeInput("hoge"), new CallerInfo(0, "")) == makeParseResult(true, makeOption(false, ""), makeInput("hoge", 0)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // combinateNone
        template combinateNone(alias parser){
            alias None ResultType;
            static ParseResult!(R, ResultType) parse(R)(Input!R input, in CallerInfo info){
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
                assert(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")).parse(makeInput("(w)"), new CallerInfo(0, "")) == makeParseResult(true, "w", makeInput("", 3)));
                assert(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")).parse(makeInput("(w}"), new CallerInfo(0, "")) == makeParseResult(false, "", makeInput(""), Error("')' expected but '}' found", 2)));
                assert(combinateNone!(parseString!"w").parse(makeInput("a"), new CallerInfo(0, "")) == makeParseResult(false, None.init, makeInput(""), Error("'w' expected but 'a' found")));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // combinateAndPred
        template combinateAndPred(alias parser){
            alias None ResultType;
            static ParseResult!(R, ResultType) parse(R)(Input!R input, in CallerInfo info){
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
                assert(combinateAndPred!(parseString!"w").parse(makeInput("www"), new CallerInfo(0, "")) == makeParseResult(true, None.init, makeInput("www", 0)));
                assert(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w")).parse(makeInput("www"), new CallerInfo(0, "")) == makeParseResult(true, "w", makeInput("ww", 1)));
                assert(combinateMore1!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w"))).parse(makeInput("www"), new CallerInfo(0, "")) == makeParseResult(true, ["w", "w"], makeInput("w", 2), Error("'w' expected but EOF found", 3)));
                assert(combinateMore1!(combinateSequence!(parseString!"w", combinateAndPred!(parseString!"w"))).parse(makeInput("w"), new CallerInfo(0, "")) == makeParseResult(false, [""][0..0], makeInput(""), Error("'w' expected but EOF found", 1)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // combinateNotPred
        template combinateNotPred(alias parser){
            alias None ResultType;
            static ParseResult!(R, ResultType) parse(R)(Input!R input, in CallerInfo info){
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
                assert(combinateMore1!(combinateSequence!(parseString!"w", combinateNotPred!(parseString!"s"))).parse(makeInput("wwws"), new CallerInfo(0, "")) == makeParseResult(true, ["w", "w"], makeInput("ws", 2), Error("Expected failure", 3)));
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
                    pragma(msg, file ~ "(" ~ toStringNow!line ~ "): Error: cannot call " ~ converter.stringof ~ " using '>>' with types: " ~ ParserType!parser.stringof);
                }else{
                    pragma(msg, __FILE__ ~ "(" ~ toStringNow!__LINE__ ~ "): Error: cannot call " ~ converter.stringof ~ " using '>>' with types: " ~ ParserType!parser.stringof);
                }
                static assert(false);
            }
            static ParseResult!(R, ResultType) parse(R)(Input!R input, in CallerInfo info){
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
                assert(combinateConvert!(combinateMore1!(parseString!"w"), function(string[] ws){ return ws.length; }).parse(makeInput("www"), new CallerInfo(0, "")) == makeParseResult(true, cast(size_t)3, makeInput("", 3), Error("'w' expected but EOF found", 3)));
                assert(combinateConvert!(combinateMore1!(parseString!"w"), function(string[] ws){ return ws.length; }).parse(makeInput("a"), new CallerInfo(0, "")) == makeParseResult(false, cast(size_t)0, makeInput(""), Error("'w' expected but 'a' found", 0)));
                //assert(combinateConvert!(10, "hoge/fuga.d", combinateMore1!(parseString!"w"), function(string ws){ return ws.length; }).parse(makeInput(testRange("a")), new CallerInfo(0, "")) == makeParseResult(false, cast(size_t)0, makeInput(testRange("")), Error(q{"w"})));
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
                    pragma(msg, file ~ "(" ~ toStringNow!line ~ "): Error: cannot call " ~ converter.stringof ~ " using '>>>' with types: " ~ ParserType!parser.stringof);
                }else{
                    pragma(msg, __FILE__ ~ "(" ~ toStringNow!__LINE__ ~ "): Error: cannot call " ~ converter.stringof ~ " using '>>>' with types: " ~ ParserType!parser.stringof);
                }
                static assert(false);
            }
            static ParseResult!(R, ResultType) parse(R)(Input!R input, in CallerInfo info){
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
                    }
                    result.next = r.next;
                }
                result.error = r.error;
                return result;
            }
        }

        unittest{
            enum dg = {
                assert(combinateConvertWithState!(combinateMore1!(parseString!"w"), function(string[] ws, StateType state){ return ws.length; }).parse(makeInput("www"), new CallerInfo(0, "")) == makeParseResult(true, cast(size_t)3, makeInput("", 3), Error("'w' expected but EOF found", 3)));
                assert(combinateConvertWithState!(combinateMore1!(parseString!"w"), function(string[] ws, StateType state){ return ws.length; }).parse(makeInput("a"), new CallerInfo(0, "")) == makeParseResult(false, cast(size_t)0, makeInput(""), Error("'w' expected but 'a' found", 0)));
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
                    pragma(msg, file ~ "(" ~ toStringNow!line ~ "): Error: cannot call " ~ checker.stringof ~ " using '>>?' with types: " ~ ParserType!parser.stringof);
                }else{
                    pragma(msg, __FILE__ ~ "(" ~ toStringNow!__LINE__ ~ "): Error: cannot call " ~ checker.stringof ~ " using '>>?' with types: " ~ ParserType!parser.stringof);
                }
                static assert(false);
            }
            static ParseResult!(R, ResultType) parse(R)(Input!R input, in CallerInfo info){
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
                assert(combinateCheck!(combinateMore0!(parseString!"w"), function(string[] ws){ return ws.length == 5; }).parse(makeInput("wwwww"), new CallerInfo(0, "")) == makeParseResult(true, ["w", "w", "w", "w", "w"], makeInput("", 5), Error("'w' expected but EOF found", 5)));
                assert(combinateCheck!(combinateMore0!(parseString!"w"), function(string[] ws){ return ws.length == 5; }).parse(makeInput("wwww"), new CallerInfo(0, "")) == makeParseResult(false, [""][0..0], makeInput(""), Error("passing check", 0)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // combinateChangeState
        template combinateChangeState(alias parser){
            alias None ResultType;
            static ParseResult!(R, ResultType) parse(R)(Input!R input, in CallerInfo info){
                typeof(return) result;
                auto r = parser.parse(input, info);
                if(r.match){
                    result.match = true;
                    result.next.source = r.next.source;
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
                    auto r = combinateChangeState!(parseString!"hoge").parse(makeInput("hoge"), new CallerInfo(0, ""));
                    assert(r.next.input == "");
                    assert(r.next.state == "hoge");
                }
                {
                    auto r = combinateSequence!(combinateChangeState!(parseString!"hoge"), combinateChangeState!(parseString!"piyo")).parse(makeInput("hogepiyo"), new CallerInfo(0, ""));
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
            ParseResult!(R, ResultType) parse(R)(Input!R input, in CallerInfo info){
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
            combinateSequence!(combinateAndPred!p, p).parse(makeInput("str"), new CallerInfo(0, ""));
            combinateSequence!(combinateAndPred!p, p).parse(makeInput("str".testRange()), new CallerInfo(0, ""));
        }

// useful parser
    // parseEscapeSequence
        template parseEscapeSequence(){
            alias combinateConvert!(
                combinateSequence!(
                    parseString!"\\",
                    combinateChoice!(
                        combinateConvert!(
                            combinateSequence!(
                                parseString!"u",
                                parseAnyChar!(),
                                parseAnyChar!(),
                                parseAnyChar!(),
                                parseAnyChar!()
                            ),
                            flat
                        ),
                        combinateConvert!(
                            combinateSequence!(
                                parseString!"U",
                                parseAnyChar!(),
                                parseAnyChar!(),
                                parseAnyChar!(),
                                parseAnyChar!(),
                                parseAnyChar!(),
                                parseAnyChar!(),
                                parseAnyChar!(),
                                parseAnyChar!()
                            ),
                            flat
                        ),
                        combinateChoice!(
                            parseString!"'",
                            parseString!"\"",
                            parseString!"?",
                            parseString!"\\",
                            parseString!"a",
                            parseString!"b",
                            parseString!"f",
                            parseString!"n",
                            parseString!"r",
                            parseString!"t",
                            parseString!"v"
                        )
                    )
                ),
                flat
            ) parseEscapeSequence;
        }

        unittest{
            enum dg = {
                assert(parseEscapeSequence!().parse(makeInput(`\"hoge`             ), new CallerInfo(0, "")) == makeParseResult(true, `\"`, makeInput("hoge"             , 2)));
                assert(parseEscapeSequence!().parse(makeInput(`\"hoge`w            ), new CallerInfo(0, "")) == makeParseResult(true, `\"`, makeInput("hoge"w            , 2)));
                assert(parseEscapeSequence!().parse(makeInput(`\"hoge`d            ), new CallerInfo(0, "")) == makeParseResult(true, `\"`, makeInput("hoge"d            , 2)));
                assert(parseEscapeSequence!().parse(makeInput(`\"hoge` .testRange()), new CallerInfo(0, "")) == makeParseResult(true, `\"`, makeInput("hoge" .testRange(), 2)));
                assert(parseEscapeSequence!().parse(makeInput(`\"hoge`w.testRange()), new CallerInfo(0, "")) == makeParseResult(true, `\"`, makeInput("hoge"w.testRange(), 2)));
                assert(parseEscapeSequence!().parse(makeInput(`\"hoge`d.testRange()), new CallerInfo(0, "")) == makeParseResult(true, `\"`, makeInput("hoge"d.testRange(), 2)));

                assert(parseEscapeSequence!().parse(makeInput(`\U0010FFFFhoge`             ), new CallerInfo(0, "")) == makeParseResult(true, `\U0010FFFF`, makeInput("hoge"             , 10)));
                assert(parseEscapeSequence!().parse(makeInput(`\U0010FFFFhoge`w            ), new CallerInfo(0, "")) == makeParseResult(true, `\U0010FFFF`, makeInput("hoge"w            , 10)));
                assert(parseEscapeSequence!().parse(makeInput(`\U0010FFFFhoge`d            ), new CallerInfo(0, "")) == makeParseResult(true, `\U0010FFFF`, makeInput("hoge"d            , 10)));
                assert(parseEscapeSequence!().parse(makeInput(`\U0010FFFFhoge` .testRange()), new CallerInfo(0, "")) == makeParseResult(true, `\U0010FFFF`, makeInput("hoge" .testRange(), 10)));
                assert(parseEscapeSequence!().parse(makeInput(`\U0010FFFFhoge`w.testRange()), new CallerInfo(0, "")) == makeParseResult(true, `\U0010FFFF`, makeInput("hoge"w.testRange(), 10)));
                assert(parseEscapeSequence!().parse(makeInput(`\U0010FFFFhoge`d.testRange()), new CallerInfo(0, "")) == makeParseResult(true, `\U0010FFFF`, makeInput("hoge"d.testRange(), 10)));

                assert(parseEscapeSequence!().parse(makeInput(`\u10FFhoge`             ), new CallerInfo(0, "")) == makeParseResult(true, `\u10FF`, makeInput("hoge"             , 6)));
                assert(parseEscapeSequence!().parse(makeInput(`\u10FFhoge`w            ), new CallerInfo(0, "")) == makeParseResult(true, `\u10FF`, makeInput("hoge"w            , 6)));
                assert(parseEscapeSequence!().parse(makeInput(`\u10FFhoge`d            ), new CallerInfo(0, "")) == makeParseResult(true, `\u10FF`, makeInput("hoge"d            , 6)));
                assert(parseEscapeSequence!().parse(makeInput(`\u10FFhoge` .testRange()), new CallerInfo(0, "")) == makeParseResult(true, `\u10FF`, makeInput("hoge" .testRange(), 6)));
                assert(parseEscapeSequence!().parse(makeInput(`\u10FFhoge`w.testRange()), new CallerInfo(0, "")) == makeParseResult(true, `\u10FF`, makeInput("hoge"w.testRange(), 6)));
                assert(parseEscapeSequence!().parse(makeInput(`\u10FFhoge`d.testRange()), new CallerInfo(0, "")) == makeParseResult(true, `\u10FF`, makeInput("hoge"d.testRange(), 6)));

                assert(parseEscapeSequence!().parse(makeInput(`\nhoge`             ), new CallerInfo(0, "")) == makeParseResult(true, `\n`, makeInput("hoge"             , 2)));
                assert(parseEscapeSequence!().parse(makeInput(`\nhoge`w            ), new CallerInfo(0, "")) == makeParseResult(true, `\n`, makeInput("hoge"w            , 2)));
                assert(parseEscapeSequence!().parse(makeInput(`\nhoge`d            ), new CallerInfo(0, "")) == makeParseResult(true, `\n`, makeInput("hoge"d            , 2)));
                assert(parseEscapeSequence!().parse(makeInput(`\nhoge` .testRange()), new CallerInfo(0, "")) == makeParseResult(true, `\n`, makeInput("hoge" .testRange(), 2)));
                assert(parseEscapeSequence!().parse(makeInput(`\nhoge`w.testRange()), new CallerInfo(0, "")) == makeParseResult(true, `\n`, makeInput("hoge"w.testRange(), 2)));
                assert(parseEscapeSequence!().parse(makeInput(`\nhoge`d.testRange()), new CallerInfo(0, "")) == makeParseResult(true, `\n`, makeInput("hoge"d.testRange(), 2)));

                assert(parseEscapeSequence!().parse(makeInput("鬱hoge"             ), new CallerInfo(0, "")) == makeParseResult(false, "", makeInput(""             ), Error("'\\' expected but '鬱' found", 0)));
                assert(parseEscapeSequence!().parse(makeInput("鬱hoge"w            ), new CallerInfo(0, "")) == makeParseResult(false, "", makeInput(""w            ), Error("'\\' expected but '鬱' found", 0)));
                assert(parseEscapeSequence!().parse(makeInput("鬱hoge"d            ), new CallerInfo(0, "")) == makeParseResult(false, "", makeInput(""d            ), Error("'\\' expected but '鬱' found", 0)));
                assert(parseEscapeSequence!().parse(makeInput("鬱hoge" .testRange()), new CallerInfo(0, "")) == makeParseResult(false, "", makeInput("" .testRange()), Error("'\\' expected but '鬱' found", 0)));
                assert(parseEscapeSequence!().parse(makeInput("鬱hoge"w.testRange()), new CallerInfo(0, "")) == makeParseResult(false, "", makeInput(""w.testRange()), Error("'\\' expected but '鬱' found", 0)));
                assert(parseEscapeSequence!().parse(makeInput("鬱hoge"d.testRange()), new CallerInfo(0, "")) == makeParseResult(false, "", makeInput(""d.testRange()), Error("'\\' expected but '鬱' found", 0)));

                try{
                    scope(success) assert(false);
                    auto result = parseEscapeSequence!().parse(makeInput([0, 0][]), new CallerInfo(0, ""));
                }catch(Exception ex){}
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // parseSpaces
        template parseSpaces(){
            alias combinateNone!(combinateMore0!(combinateChoice!(parseString!" ", parseString!"\n", parseString!"\t", parseString!"\r", parseString!"\f"))) parseSpaces;
        }

        alias parseSpaces ss;
        alias parseSpaces defaultSkip;

        unittest{
            static assert(is(parseSpaces!().ResultType));
            enum dg = {
                assert(parseSpaces!().parse(makeInput("\t \rhoge"), new CallerInfo(0, "")) == makeParseResult(true, None.init, makeInput("hoge", 3)));
                assert(parseSpaces!().parse(makeInput("hoge"), new CallerInfo(0, "")) == makeParseResult(true, None.init, makeInput("hoge", 0)));
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
                assert(parseIdent!().parse(makeInput("hoge"), new CallerInfo(0, "")) == makeParseResult(true, "hoge", makeInput("", 4)));
                assert(parseIdent!().parse(makeInput("_0"), new CallerInfo(0, "")) == makeParseResult(true, "_0", makeInput("", 2)));
                assert(parseIdent!().parse(makeInput("0"), new CallerInfo(0, "")) == makeParseResult(false, "", makeInput(""), Error("'A' ~ 'Z' expected but '0' found")));
                assert(parseIdent!().parse(makeInput("あ"), new CallerInfo(0, "")) == makeParseResult(false, "", makeInput(""), Error("'A' ~ 'Z' expected but 'あ' found")));
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
                assert(parseStringLiteral!().parse(makeInput("\"表が怖い噂のソフト\""), new CallerInfo(0, "")) == makeParseResult(true, "\"表が怖い噂のソフト\"", makeInput("", 29), Error("Expected failure", 28)));
                assert(parseStringLiteral!().parse(makeInput(`r"表が怖い噂のソフト"`), new CallerInfo(0, "")) == makeParseResult(true, `r"表が怖い噂のソフト"`, makeInput("", 30), Error("Expected failure", 29)));
                assert(parseStringLiteral!().parse(makeInput("`表が怖い噂のソフト`"), new CallerInfo(0, "")) == makeParseResult(true, q{`表が怖い噂のソフト`}, makeInput("", 29), Error("Expected failure", 28)));
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
                assert(parseIntLiteral!().parse(makeInput("3141"), new CallerInfo(0, "")) == makeParseResult(true, 3141, makeInput("", 4)));
                assert(parseIntLiteral!().parse(makeInput("0"), new CallerInfo(0, "")) == makeParseResult(true, 0, makeInput("", 1)));
                assert(parseIntLiteral!().parse(makeInput("0123"), new CallerInfo(0, "")) == makeParseResult(true, 0, makeInput("123", 1)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

// getters
    // getLine
        template getLine(){
            alias size_t ResultType;
            static ParseResult!(R, ResultType) parse(R)(Input!R input, in CallerInfo info){
                return makeParseResult(true, input.line, input, Error.init);
            }
        }

        unittest{
            enum dg = {
                assert(combinateSequence!(parseSpaces!(), getLine!()).parse(makeInput("\n\n"             ), new CallerInfo(0, "")) == makeParseResult(true, cast(size_t)3, makeInput(""             , 2, 3)));
                assert(combinateSequence!(parseSpaces!(), getLine!()).parse(makeInput("\n\n"w            ), new CallerInfo(0, "")) == makeParseResult(true, cast(size_t)3, makeInput(""w            , 2, 3)));
                assert(combinateSequence!(parseSpaces!(), getLine!()).parse(makeInput("\n\n"d            ), new CallerInfo(0, "")) == makeParseResult(true, cast(size_t)3, makeInput(""d            , 2, 3)));
                assert(combinateSequence!(parseSpaces!(), getLine!()).parse(makeInput("\n\n" .testRange()), new CallerInfo(0, "")) == makeParseResult(true, cast(size_t)3, makeInput("" .testRange(), 2, 3)));
                assert(combinateSequence!(parseSpaces!(), getLine!()).parse(makeInput("\n\n"w.testRange()), new CallerInfo(0, "")) == makeParseResult(true, cast(size_t)3, makeInput(""w.testRange(), 2, 3)));
                assert(combinateSequence!(parseSpaces!(), getLine!()).parse(makeInput("\n\n"d.testRange()), new CallerInfo(0, "")) == makeParseResult(true, cast(size_t)3, makeInput(""d.testRange(), 2, 3)));

                try{
                    scope(failure) assert(true);
                    auto result = combinateSequence!(parseSpaces!(), getLine!()).parse(makeInput([0, 0]), new CallerInfo(0, ""));
                }catch(Exception ex){}
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // getCallerLine
        template getCallerLine(){
            alias size_t ResultType;
            static ParseResult!(R, ResultType) parse(R)(Input!R input, in CallerInfo info){
                return makeParseResult(true, info.line, input, Error.init);
            }
        }

        unittest{
            enum dg = {
                assert(getCallerLine!().parse(makeInput(""             ), new CallerInfo(__LINE__, "")) == makeParseResult(true, cast(size_t)__LINE__, makeInput(""             , 0)));
                assert(getCallerLine!().parse(makeInput(""w            ), new CallerInfo(__LINE__, "")) == makeParseResult(true, cast(size_t)__LINE__, makeInput(""w            , 0)));
                assert(getCallerLine!().parse(makeInput(""d            ), new CallerInfo(__LINE__, "")) == makeParseResult(true, cast(size_t)__LINE__, makeInput(""d            , 0)));
                assert(getCallerLine!().parse(makeInput("" .testRange()), new CallerInfo(__LINE__, "")) == makeParseResult(true, cast(size_t)__LINE__, makeInput("" .testRange(), 0)));
                assert(getCallerLine!().parse(makeInput(""w.testRange()), new CallerInfo(__LINE__, "")) == makeParseResult(true, cast(size_t)__LINE__, makeInput(""w.testRange(), 0)));
                assert(getCallerLine!().parse(makeInput(""d.testRange()), new CallerInfo(__LINE__, "")) == makeParseResult(true, cast(size_t)__LINE__, makeInput(""d.testRange(), 0)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // getCallerFile
        template getCallerFile(){
            alias string ResultType;
            static ParseResult!(R, ResultType) parse(R)(Input!R input, in CallerInfo info){
                return makeParseResult(true, info.file, input, Error.init);
            }
        }

        unittest{
            enum dg = {
                assert(getCallerFile!().parse(makeInput(""             ), new CallerInfo(0, __FILE__)) == makeParseResult(true, __FILE__, makeInput(""             , 0)));
                assert(getCallerFile!().parse(makeInput(""w            ), new CallerInfo(0, __FILE__)) == makeParseResult(true, __FILE__, makeInput(""w            , 0)));
                assert(getCallerFile!().parse(makeInput(""d            ), new CallerInfo(0, __FILE__)) == makeParseResult(true, __FILE__, makeInput(""d            , 0)));
                assert(getCallerFile!().parse(makeInput("" .testRange()), new CallerInfo(0, __FILE__)) == makeParseResult(true, __FILE__, makeInput("" .testRange(), 0)));
                assert(getCallerFile!().parse(makeInput(""w.testRange()), new CallerInfo(0, __FILE__)) == makeParseResult(true, __FILE__, makeInput(""w.testRange(), 0)));
                assert(getCallerFile!().parse(makeInput(""d.testRange()), new CallerInfo(0, __FILE__)) == makeParseResult(true, __FILE__, makeInput(""d.testRange(), 0)));
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
        return "pragma(msg, __FILE__ ~ `(" ~ (parsed.error.line + callerLine - 1).to!string() ~ "): Error: " ~ parsed.error.msg ~ "`);static assert(false);";
    }
}

auto parse(alias fun, size_t callerLine = __LINE__, string callerFile = __FILE__, Range)(Range input, StateType state = StateType.init){
    return fun!().parse(Input!Range(input, 0, 1, state), new CallerInfo(callerLine, callerFile));
}

// parsers of DSL
    // arch
        template arch(string open, string close){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Input!string input, in CallerInfo info){
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
                assert(arch!("(", ")").parse(makeInput("(a(i(u)e)o())"), new CallerInfo(0, "")) == makeParseResult(true, "(a(i(u)e)o())", makeInput("", 13), Error("Expected failure", 12)));
                assert(arch!("[", "]").parse(makeInput("[a[i[u]e]o[]]"), new CallerInfo(0, "")) == makeParseResult(true, "[a[i[u]e]o[]]", makeInput("", 13), Error("Expected failure", 12)));
                assert(arch!("{", "}").parse(makeInput("{a{i{u}e}o{}}"), new CallerInfo(0, "")) == makeParseResult(true, "{a{i{u}e}o{}}", makeInput("", 13), Error("Expected failure", 12)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // func
        template func(){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Input!string input, in CallerInfo info){
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
                assert(func!().parse(makeInput(
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
                    "}", makeInput("", 148))
                );
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // id
        template id(){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Input!string input, in CallerInfo info){
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
                assert(id!().parse(makeInput("A"), new CallerInfo(0, "")) == makeParseResult(true, "A", makeInput("", 1)));
                assert(id!().parse(makeInput("int"), new CallerInfo(0, "")) == makeParseResult(true, "int", makeInput("", 3)));
                assert(id!().parse(makeInput("0"), new CallerInfo(0, "")) == makeParseResult(false, "", makeInput(""), Error("'_' expected but '0' found", 0)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // nonterminal
        template nonterminal(){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Input!string input, in CallerInfo info){
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
        }

        unittest{
            enum dg = {
                assert(nonterminal!().parse(makeInput("A"), new CallerInfo(__LINE__, "")) == makeParseResult(true, " #line " ~ toStringNow!__LINE__ ~ "\ncombinateMemoize!(A!())", makeInput("", 1)));
                assert(nonterminal!().parse(makeInput("int"), new CallerInfo(__LINE__, "")) == makeParseResult(true, " #line " ~ toStringNow!__LINE__ ~ "\ncombinateMemoize!(int!())", makeInput("", 3)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // typeName
        template typeName(){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Input!string input, in CallerInfo info){
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
                assert(typeName!().parse(makeInput("int"), new CallerInfo(0, "")) == makeParseResult(true, "int", makeInput("", 3)));
                assert(typeName!().parse(makeInput("Tuple!(string, int)"), new CallerInfo(0, "")) == makeParseResult(true, "Tuple!(string, int)", makeInput("", 19)));
                assert(typeName!().parse(makeInput("int[]"), new CallerInfo(0, "")) == makeParseResult(true, "int[]", makeInput("", 5)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // eofLit
        template eofLit(){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Input!string input, in CallerInfo info){
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
                assert(eofLit!().parse(makeInput("$"), new CallerInfo(0, "")) == makeParseResult(true, "parseEOF!()", makeInput("", 1)));
                assert(eofLit!().parse(makeInput("#"), new CallerInfo(0, "")) == makeParseResult(false, "", makeInput(""), Error("'$' expected but '#' found", 0)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // rangeLit
        template rangeLit(){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Input!string input, in CallerInfo info){
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
            ParseResult!(string, ResultType) parse()(Input!string input, in CallerInfo info){
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
            ParseResult!(string, ResultType) parse()(Input!string input, in CallerInfo info){
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
                assert(rangeLit!().parse(makeInput("[a-z]"), new CallerInfo(0, "")) == makeParseResult(true, "parseCharRange!('a','z')", makeInput("", 5), Error("Expected failure", 4)));
                assert(rangeLit!().parse(makeInput("[a-zA-Z_]"), new CallerInfo(0, "")) == makeParseResult(true, "combinateChoice!(parseCharRange!('a','z'),parseCharRange!('A','Z'),parseString!\"_\"" ")", makeInput("", 9), Error("Expected failure", 8)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // stringLit
        template stringLit(){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Input!string input, in CallerInfo info){
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
                assert(stringLit!().parse(makeInput("\"hello\nworld\" "), new CallerInfo(0, "")) == makeParseResult(true, "parseString!\"hello\nworld\"", makeInput(" ", 13, 2), Error("Expected failure", 12, 2)));
                assert(stringLit!().parse(makeInput("aa\""), new CallerInfo(0, "")) == makeParseResult(false, "", makeInput(""), Error("'\"' expected but 'a' found", 0)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // literal
        template literal(){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Input!string input, in CallerInfo info){
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
                assert(literal!().parse(makeInput("\"hello\nworld\""), new CallerInfo(0, "")) == makeParseResult(true, "combinateMemoize!(parseString!\"hello\nworld\")", makeInput("", 13, 2), Error("Expected failure", 12, 2)));
                assert(literal!().parse(makeInput("[a-z]"), new CallerInfo(0, "")) == makeParseResult(true, "combinateMemoize!(parseCharRange!('a','z'))", makeInput("", 5), Error("Expected failure", 4)));
                assert(literal!().parse(makeInput("$"), new CallerInfo(0, "")) == makeParseResult(true, "combinateMemoize!(parseEOF!())", makeInput("", 1)));
                assert(literal!().parse(makeInput("$", 0, 1, tuple("", "skip!()")), new CallerInfo(0, "")) == makeParseResult(true, "combinateSkip!(combinateMemoize!(parseEOF!()),skip!())", makeInput("", 1, 1, tuple("", "skip!()"))));
                assert(literal!().parse(makeInput("表が怖い噂のソフト"), new CallerInfo(0, "")) == makeParseResult(false, "", makeInput(""), Error("'$' expected but '表' found", 0)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // primaryExp
        template primaryExp(){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Input!string input, in CallerInfo info){
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
                assert(primaryExp!().parse(makeInput("(&(^$)?)"), new CallerInfo(0, "")) == makeParseResult(true, "combinateOption!(combinateAndPred!(combinateNotPred!(combinateMemoize!(parseEOF!()))))", makeInput("", 8), Error("'(' expected but ')' found", 7)));
                assert(primaryExp!().parse(makeInput("int"), new CallerInfo(__LINE__, "")) == makeParseResult(true, " #line " ~ toStringNow!__LINE__ ~ "\ncombinateMemoize!(int!())", makeInput("", 3)));
                assert(primaryExp!().parse(makeInput("###このコメントは表示されません###"), new CallerInfo(0, "")) == makeParseResult(false, "", makeInput(""), Error("'(' expected but '#' found", 0)));
                assert(primaryExp!().parse(makeInput("(&(^$)?"), new CallerInfo(0, "")) == makeParseResult(false, "", makeInput(""), Error("')' expected but EOF found", 7)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // preExp
        template preExp(){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Input!string input, in CallerInfo info){
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
                assert(preExp!().parse(makeInput("!$"), new CallerInfo(0, "")) == makeParseResult(true, "combinateNone!(combinateMemoize!(parseEOF!()))", makeInput("", 2)));
                assert(preExp!().parse(makeInput("!!$"), new CallerInfo(0, "")) == makeParseResult(true, "combinateChangeState!(combinateMemoize!(parseEOF!()))", makeInput("", 3)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // postExp
        template postExp(){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Input!string input, in CallerInfo info){
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
                assert(postExp!().parse(makeInput("!$*"), new CallerInfo(0, "")) == makeParseResult(true, "combinateMore0!(combinateNone!(combinateMemoize!(parseEOF!())))", makeInput("", 3)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // optionExp
        template optionExp(){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Input!string input, in CallerInfo info){
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
                assert(optionExp!().parse(makeInput("(&(^\"hello\"))?"), new CallerInfo(0, "")) == makeParseResult(true, "combinateOption!(combinateAndPred!(combinateNotPred!(combinateMemoize!(parseString!\"hello\"))))", makeInput("", 14)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // seqExp
        template seqExp(){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Input!string input, in CallerInfo info){
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
                assert(seqExp!().parse(makeInput("!$* (&(^$))?"), new CallerInfo(0, "")) == makeParseResult(true, "combinateSequence!(combinateMore0!(combinateNone!(combinateMemoize!(parseEOF!()))),combinateOption!(combinateAndPred!(combinateNotPred!(combinateMemoize!(parseEOF!())))))", makeInput("", 12), Error("'(' expected but EOF found", 12)));
                assert(seqExp!().parse(makeInput("!\"hello\" $"), new CallerInfo(0, "")) == makeParseResult(true, "combinateSequence!(combinateNone!(combinateMemoize!(parseString!\"hello\")),combinateMemoize!(parseEOF!()))", makeInput("", 10), Error("'(' expected but EOF found", 10)));
                assert(seqExp!().parse(makeInput("!$* (&(^$)?"), new CallerInfo(0, "")) == makeParseResult(true, "combinateMore0!(combinateNone!(combinateMemoize!(parseEOF!())))", makeInput("(&(^$)?", 4), Error("')' expected but EOF found", 11)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // convExp
        template convExp(){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Input!string input, in CallerInfo info){
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
                assert(convExp!().parse(makeInput(q{!"hello" $ >> {return false;}}), new CallerInfo(__LINE__, `src\ctpg.d`)) == makeParseResult(true, "combinateConvert!(" ~ toStringNow!__LINE__ ~ ",`src\\ctpg.d`,combinateSequence!(combinateNone!(combinateMemoize!(parseString!\"hello\")),combinateMemoize!(parseEOF!())),function(){return false;})", makeInput("", 29), Error("'(' expected but '>' found", 11)));
                assert(convExp!().parse(makeInput(q{"hello" >> flat >> to!int}), new CallerInfo(__LINE__, `src/ctpg.d`)) == makeParseResult(true, "combinateConvert!(" ~ toStringNow!__LINE__ ~ ",`src/ctpg.d`,combinateConvert!(" ~ toStringNow!__LINE__ ~ ",`src/ctpg.d`,combinateMemoize!(parseString!\"hello\"),flat),to!int)", makeInput("", 25), Error("'(' expected but '>' found", 8)));
                assert(convExp!().parse(makeInput(q{$ >>> to!string >>? isValid}, 0, 1, tuple("", "skip!()")), new CallerInfo(__LINE__, `src\ctpg.d`)) == makeParseResult(true, "combinateCheck!(" ~ toStringNow!__LINE__ ~ r",`src\ctpg.d`,combinateConvertWithState!(" ~ toStringNow!__LINE__ ~ r",`src\ctpg.d`,combinateSkip!(combinateMemoize!(parseEOF!()),skip!()),to!string),isValid)", makeInput("", 27, 1, tuple("", "skip!()")), Error("'(' expected but '>' found", 2)));
                assert(convExp!().parse(makeInput(q{!"hello" $ > {return false;}}), new CallerInfo(0, "")) == makeParseResult(true, "combinateSequence!(combinateNone!(combinateMemoize!(parseString!\"hello\")),combinateMemoize!(parseEOF!()))", makeInput("> {return false;}", 11), Error("'(' expected but '>' found", 11)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // choiceExp
        template choiceExp(){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Input!string input, in CallerInfo info){
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
                assert(choiceExp!().parse(makeInput(`!$* / (&(^"a"))?`), new CallerInfo(__LINE__, `src\ctpg.d`)) == makeParseResult(true, "combinateChoice!(" ~ toStringNow!__LINE__ ~ ",`src\\ctpg.d`,combinateMore0!(combinateNone!(combinateMemoize!(parseEOF!()))),combinateOption!(combinateAndPred!(combinateNotPred!(combinateMemoize!(parseString!\"a\")))))", makeInput("", 16), Error("'(' expected but '/' found", 4)));
                assert(choiceExp!().parse(makeInput(`!"hello" $`, 0, 1, tuple("", "skip!()")), new CallerInfo(0, "")) == makeParseResult(true, "combinateSequence!(combinateNone!(combinateSkip!(combinateMemoize!(parseString!\"hello\"),skip!())),combinateSkip!(combinateMemoize!(parseEOF!()),skip!()))", makeInput("", 10, 1, tuple("", "skip!()")), Error("'(' expected but EOF found", 10)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        }

    // def
        template def(){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Input!string input, in CallerInfo info){
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
                        getLine!(),
                        getCallerLine!(),
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
                    function(string type, size_t line, size_t callerLine, string name, string choiceExp)
                    =>
                        "template " ~ name ~ "(){"
                            "#line " ~ (line + callerLine - 1).to!string() ~ "\n"
                            "alias " ~ type ~ " ResultType;"
                            "static ParseResult!(R, ResultType) parse(R)(Input!R input, in CallerInfo info){"
                                "return "~choiceExp~".parse(input, info);"
                            "}"
                        "}"
                ).parse(input, info);
            }
        }

        unittest{
            enum dg = {
                cast(void)__LINE__;
                assert(def!().parse(makeInput(`@skip(" ") bool hoge = !"hello" $ >> {return false;};`), new CallerInfo(__LINE__, `src/ctpg.d`)) == makeParseResult(true, "template hoge(){#line " ~ toStringNow!__LINE__~ "\nalias bool ResultType;static ParseResult!(R, ResultType) parse(R)(Input!R input, in CallerInfo info){return combinateConvert!(" ~ toStringNow!__LINE__ ~ ",`src/ctpg.d`,combinateSequence!(combinateNone!(combinateSkip!(combinateMemoize!(parseString!\"hello\"),combinateMemoize!(parseString!\" \"))),combinateSkip!(combinateMemoize!(parseEOF!()),combinateMemoize!(parseString!\" \"))),function(){return false;}).parse(input, info);}}", makeInput("", 53, 1, tuple("", "combinateMemoize!(parseString!\" \")")), Error("'(' expected but '>' found", 34)));
                assert(def!().parse(makeInput(`None recursive = A $;`), new CallerInfo(__LINE__, "")) == makeParseResult(true, "template recursive(){#line " ~ toStringNow!__LINE__~ "\nalias None ResultType;static ParseResult!(R, ResultType) parse(R)(Input!R input, in CallerInfo info){return combinateSequence!( #line " ~ toStringNow!__LINE__ ~ "\ncombinateMemoize!(A!()),combinateMemoize!(parseEOF!())).parse(input, info);}}", makeInput("", 21), Error("'(' expected but ';' found", 20)));
                assert(def!().parse(makeInput(`None recursive  A $;`), new CallerInfo(__LINE__, "")) == makeParseResult(false, "", makeInput(""), Error("'=' expected but 'A' found", 16)));
                assert(def!().parse(makeInput("None recursive  \nA $;"), new CallerInfo(__LINE__, "")) == makeParseResult(false, "", makeInput(""), Error("'=' expected but 'A' found", 17, 2)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        };

    // defs
        template defs(){
            alias string ResultType;
            ParseResult!(string, ResultType) parse()(Input!string input, in CallerInfo info){
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
                version(none) pragma(msg, defs!().parse(makeInput(q{
                    @default_skip(" " / "\t" / "\n")
                    bool hoge = !"hello" $ >> {return false;};
                    @skip(" ") Tuple!piyo hoge2 = hoge* >> {return tuple("foo");};
                }), new CallerInfo(__LINE__ - 4, r"src\ctpg.d")).error);
                assert(defs!().parse(makeInput(q{
                    @default_skip(" " / "\t" / "\n")
                    bool hoge = !"hello" $ >> {return false;};
                    @skip(" ") Tuple!piyo hoge2 = hoge* >> {return tuple("foo");};
                }), new CallerInfo(__LINE__ - 4, r"src\ctpg.d")) == makeParseResult(true, 
                    "template hoge(){"
                        "#line " ~ toStringNow!(__LINE__ - 4) ~ "\n"
                        "alias bool ResultType;"
                        "static ParseResult!(R, ResultType) parse(R)(Input!R input, in CallerInfo info){"
                            "return combinateConvert!(" ~ toStringNow!(__LINE__ - 7) ~ ",`src\\ctpg.d`,"
                                "combinateSequence!("
                                    "combinateNone!("
                                        "combinateSkip!("
                                            "combinateMemoize!(parseString!\"hello\"),"
                                            "combinateChoice!(" ~ toStringNow!(__LINE__ - 13) ~ ",`src\\ctpg.d`,"
                                                "combinateMemoize!(parseString!\" \"),"
                                                "combinateMemoize!(parseString!\"\\t\"),"
                                                "combinateMemoize!(parseString!\"\\n\")"
                                            ")"
                                        ")"
                                    "),"
                                    "combinateSkip!("
                                        "combinateMemoize!(parseEOF!()),"
                                        "combinateChoice!(" ~ toStringNow!(__LINE__ - 22) ~ ",`src\\ctpg.d`,"
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
                        "#line " ~ toStringNow!(__LINE__ - 34) ~ "\n"
                        "alias Tuple!piyo ResultType;"
                        "static ParseResult!(R, ResultType) parse(R)(Input!R input, in CallerInfo info){"
                            "return combinateConvert!(" ~ toStringNow!(__LINE__ - 37) ~ ",`src\\ctpg.d`,"
                                "combinateMore0!("
                                    " #line " ~ toStringNow!(__LINE__ - 39) ~ "\n"
                                    "combinateSkip!("
                                        "combinateMemoize!(hoge!()),"
                                        "combinateMemoize!(parseString!\" \")"
                                    ")"
                                "),"
                                "function(){"
                                    "return tuple(\"foo\");"
                                "}"
                            ").parse(input, info);"
                        "}"
                    "}",
                makeInput("", 216, 5, tuple("combinateChoice!(" ~ toStringNow!(__LINE__ - 53) ~ ",`src\\ctpg.d`,combinateMemoize!(parseString!\" \"),combinateMemoize!(parseString!\"\\t\"),combinateMemoize!(parseString!\"\\n\"))", "combinateMemoize!(parseString!\" \")")), Error("'_' expected but EOF found", 216, 5)));
                return true;
            };
            debug(ctpg_compile_time) static assert(dg());
            dg();
        };

