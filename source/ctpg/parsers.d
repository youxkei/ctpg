module ctpg.parsers;

import std.algorithm : count;
import std.array : empty;
import std.conv : to;
import std.exception : assertThrown;
import std.traits : Unqual, CommonType, isArray, isSomeString, isSomeChar;
import std.range : ElementEncodingType, isRandomAccessRange;

import ctpg : parse;

import ctpg.for_unittest;
import ctpg.parse_result : ParseResult, getParseResultType;
import ctpg.parser_kind  : ParserKind, ParserKinds;
import ctpg.input        : Input;
import ctpg.caller       : Caller;
import ctpg.none         : None;
import ctpg.macro_       : MAKE_RESULT;
import ctpg.unsupported_input_type_exception : UnsupportedInputTypeException;

import combinators = ctpg.combinators;

import selflinoin : makeCompilationErrorMessage;

import compile_time_unittest : enableCompileTimeUnittest;
mixin enableCompileTimeUnittest;


template success()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ None };

        Result parse(Input!SrcType input, in Caller caller)
        {
            Result result;

            result.match = true;
            result.nextInput = input;

            return result;
        }
    }
}

debug(ctpg) unittest
{
    foreach(conv; convs) foreach(kind; ParserKinds)
    {
        with(parse!(success!(), kind)(conv!"hoge"))
        {
            assert(match              == true);
            assert(nextInput.source   == conv!"hoge");
            assert(nextInput.position == 0);
            assert(nextInput.line     == 0);
        }

        with(parse!(success!(), kind)(conv!""))
        {
            assert(match              == true);
            assert(nextInput.source   == conv!"");
            assert(nextInput.position == 0);
            assert(nextInput.line     == 0);
        }
    }
}


template eof()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ None };

        Result parse(Input!SrcType input, in Caller caller)
        {
            Result result;

            if(input.source.empty)
            {
                result.match     = true;
                result.nextInput = input;
            }
            else
            {
                static if(kind.hasError)
                {
                    result.error.msg      = "EOF expected";
                    result.error.position = input.position;
                }
            }

            return result;
        }
    }
}

debug(ctpg) unittest
{
    foreach(conv; convs) foreach(kind; ParserKinds)
    {
        with(parse!(eof!(), kind)(conv!""))
        {
            assert(match              == true);
            assert(nextInput.source   == conv!"");
            assert(nextInput.position == 0);
            assert(nextInput.line     == 0);
        }

        with(parse!(eof!(), kind)(conv!"hoge"))
        {
                                     assert(match          == false);
            static if(kind.hasError) assert(error.msg      == "EOF expected");
            static if(kind.hasError) assert(error.position == 0);
        }

        assertThrown!UnsupportedInputTypeException(parse!(string_!"hoge", kind)([0, 1]));
    }
}


template spaces()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ None };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinators.none!
            (
                combinators.more0!
                (
                    combinators.choice!
                    (
                        string_!" ",
                        string_!"\n",
                        string_!"\t",
                        string_!"\r",
                        string_!"\f"
                    )
                )
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

alias skip = spaces;

debug(ctpg) unittest
{
    foreach(conv; convs) foreach(kind; ParserKinds)
    {
        with(parse!(spaces!())(conv!" \n\t\r\f"))
        {
            assert(match            == true);
            assert(nextInput.source == conv!"");
        }

        with(parse!(spaces!())(conv!" \n\ta\r\f"))
        {
            assert(match            == true);
            assert(nextInput.source == conv!"a\r\f");
        }

        with(parse!(spaces!())(conv!""))
        {
            assert(match            == true);
            assert(nextInput.source == conv!"");
        }
    }
}


template string_(alias string str)
{
    template build(alias kind, SrcType)
    {
        static if(is(Unqual!(ElementEncodingType!SrcType) ==  char)) enum adaptedStr =              str;
        static if(is(Unqual!(ElementEncodingType!SrcType) == wchar)) enum adaptedStr = cast(wstring)str;
        static if(is(Unqual!(ElementEncodingType!SrcType) == dchar)) enum adaptedStr = cast(dstring)str;

        enum lines = str.count('\n');
        enum errorMsg = "'" ~ str ~ "' expected";

        mixin MAKE_RESULT!q{ string };

        static if(isSomeString!SrcType)
        {
            Result parse(Input!SrcType input, in Caller caller)
            {
                Result result;

                if(input.source.length >= adaptedStr.length && input.source[0..adaptedStr.length] == adaptedStr)
                {
                    result.match              = true;
                    result.nextInput.source   = input.source[str.length..$];
                    result.nextInput.position = input.position + adaptedStr.length;
                    result.nextInput.line     = input.line + lines;

                    static if(kind.hasValue)
                    {
                        result.value = str;
                    }
                }
                else
                {
                    static if(kind.hasError)
                    {
                        result.error.msg      = errorMsg;
                        result.error.position = input.position;
                    }
                }

                return result;
            }
        }
        else static if(isSomeChar!(ElementEncodingType!SrcType))
        {
            Result parse(Input!SrcType input, in Caller caller)
            {
                Result result;

                foreach(c; adaptedStr)
                {
                    if(input.source.empty || c != input.source.front)
                    {
                        static if(kind.hasError)
                        {
                            result.error.msg      = errorMsg;
                            result.error.position = input.position;
                        }

                        return result;
                    }
                    else
                    {
                        input.source.popFront();
                    }
                }

                result.match              = true;
                result.nextInput.source   = input.source;
                result.nextInput.position = input.position + adaptedStr.length;
                result.nextInput.line     = input.line + lines;

                static if(kind.hasValue)
                {
                    result.value = str;
                }

                return result;
            }
        }
        else
        {
            Result parse(Input!SrcType input, in Caller caller)
            {
                throw new UnsupportedInputTypeException("Input should be some string or a range whose elemement type is some char");
            }
        }
    }
}

debug(ctpg) unittest
{
    foreach(conv; convs) foreach(kind; ParserKinds)
    {
        with(parse!(string_!"hoge", kind)(conv!"hogehoge"))
        {
                                     assert(match              == true);
            static if(kind.hasValue) assert(value              == "hoge");
                                     assert(nextInput.source   == conv!"hoge");
                                     assert(nextInput.position == 4);
                                     assert(nextInput.line     == 0);
        }

        with(parse!(string_!"\n\nhoge", kind)(conv!"\n\nhogehoge"))
        {
                                     assert(match              == true);
            static if(kind.hasValue) assert(value              == "\n\nhoge");
                                     assert(nextInput.source   == conv!"hoge");
                                     assert(nextInput.position == 6);
                                     assert(nextInput.line     == 2);
        }

        with(parse!(string_!"hoge", kind)(conv!"fuga"))
        {
                                     assert(match          == false);
            static if(kind.hasError) assert(error.msg      == "'hoge' expected");
            static if(kind.hasError) assert(error.position == 0);
        }

        assertThrown!UnsupportedInputTypeException(parse!(string_!"hoge", kind)([0, 1]));
    }
}


template charRange(dchar begin, dchar end, size_t line = 0, string file = "")
{
    static if(begin > end)
    {
        pragma(msg, makeCompilationErrorMessage("Error: Invalid char range", file, line));
        static assert(false);
    }

    template build(alias kind, SrcType)
    {
        dchar decode(ref SrcType input, ref size_t advance)
        {
            dchar result;

            static if(isArray!SrcType || isRandomAccessRange!SrcType)
            {
                static if(is(Unqual!(ElementEncodingType!SrcType) == char))
                {
                    if(!(input[0] & 0b_1000_0000))
                    {
                        result  = input[0];
                        input   = input[1..$];
                        advance = 1;
                    }
                    else if(!(input[0] & 0b_0010_0000))
                    {
                        result  = ((input[0] & 0b_0001_1111) << 6) | (input[1] & 0b_0011_1111);
                        input   = input[2..$];
                        advance = 2;
                    }
                    else if(!(input[0] & 0b_0001_0000))
                    {
                        result  = ((input[0] & 0b_0000_1111) << 12) | ((input[1] & 0b_0011_1111) << 6) | (input[2] & 0b_0011_1111);
                        input   = input[3..$];
                        advance = 3;
                    }
                    else
                    {
                        result  = ((input[0] & 0b_0000_0111) << 18) | ((input[1] & 0b_0011_1111) << 12) | ((input[2] & 0b_0011_1111) << 6) | (input[3] & 0b_0011_1111);
                        input   = input[4..$];
                        advance = 4;
                    }
                }
                else static if(is(Unqual!(ElementEncodingType!SrcType) == wchar))
                {
                    if(input[0] <= 0xD7FF || (0xE000 <= input[0] && input[0] < 0xFFFF))
                    {
                        result  = input[0];
                        input   = input[1..$];
                        advance = 1;
                    }
                    else
                    {
                        result  = (input[0] & 0b_0000_0011_1111_1111) * 0x400 + (input[1] & 0b_0000_0011_1111_1111) + 0x10000;
                        input   = input[2..$];
                        advance = 2;
                    }
                }
                else static if(is(Unqual!(ElementEncodingType!SrcType) == dchar))
                {
                    result  = input[0];
                    input   = input[1..$];
                    advance = 1;
                }
            }
            else
            {
                static if(is(Unqual!(ElementEncodingType!SrcType) == char))
                {
                    if(!(input.front & 0b_1000_0000))
                    {
                        result = input.front;
                        input.popFront();
                        advance = 1;
                    }
                    else if(!(input.front & 0b_0010_0000))
                    {
                        result = input.front & 0b_0001_1111;
                        result <<= 6;
                        input.popFront();
                        result |= input.front & 0b_0011_1111;
                        input.popFront();
                        advance = 2;
                    }
                    else if(!(input.front & 0b_0001_0000))
                    {
                        result = input.front & 0b_0000_1111;
                        result <<= 6;
                        input.popFront();
                        result |= input.front & 0b_0011_1111;
                        result <<= 6;
                        input.popFront();
                        result |= input.front & 0b_0011_1111;
                        input.popFront;
                        advance = 3;
                    }
                    else
                    {
                        result = input.front & 0b_0000_0111;
                        result <<= 6;
                        input.popFront();
                        result |= input.front & 0b_0011_1111;
                        result <<= 6;
                        input.popFront();
                        result |= input.front & 0b_0011_1111;
                        result <<= 6;
                        input.popFront();
                        result |= input.front & 0b_0011_1111;
                        input.popFront();
                        advance = 4;
                    }
                }
                else static if(is(Unqual!(ElementEncodingType!SrcType) == wchar))
                {
                    if(input.front <= 0xD7FF || (0xE000 <= input.front && input.front < 0xFFFF))
                    {
                        result = input.front;
                        input.popFront();
                        advance = 1;
                    }
                    else
                    {
                        result = (input.front & 0b_0000_0011_1111_1111) * 0x400;
                        input.popFront();
                        result += (input.front & 0b_0000_0011_1111_1111) + 0x10000;
                        input.popFront();
                        advance = 2;
                    }
                }
                else static if(is(Unqual!(ElementEncodingType!SrcType) == dchar))
                {
                    result = input.front;
                    input.popFront();
                    advance = 1;
                }
            }

            return result;
        }

        static if(begin == dchar.min && end == dchar.max)
        {
            enum errorMsg = "any char expected";
        }
        else
        {
            enum errorMsg = "'" ~ begin.to!string() ~ " ~ " ~ end.to!string() ~ "' expected";
        }

        mixin MAKE_RESULT!q{ dchar };

        static if(isSomeChar!(ElementEncodingType!SrcType))
        {
            Result parse(Input!SrcType input, in Caller caller)
            {
                Result result;

                if(input.source.empty)
                {
                    static if(kind.hasError)
                    {
                        result.error.msg      = errorMsg;
                        result.error.position = input.position;
                    }
                }
                else
                {
                    size_t advance;
                    dchar c = decode(input.source, advance);

                    if(begin <= c && c <= end)
                    {
                        result.match              = true;
                        result.nextInput.source   = input.source;
                        result.nextInput.position = input.position + advance;
                        result.nextInput.line     = input.line + (c == '\n' ? 1 : 0);

                        static if(kind.hasValue)
                        {
                            result.value = c;
                        }
                    }
                    else
                    {
                        static if(kind.hasError)
                        {
                            result.error.msg      = errorMsg;
                            result.error.position = input.position;
                        }
                    }
                }

                return result;
            }
        }
        else
        {
            Result parse(Input!SrcType input, in Caller caller)
            {
                throw new UnsupportedInputTypeException("Input should be some string or a range whose elemement type is some char");
            }
        }
    }
}

template anyChar(size_t line = 0, string file = "")
{
    alias anyChar = charRange!(dchar.min, dchar.max, line, file);
}

debug(ctpg) unittest
{
    foreach(conv; convs) foreach(kind; ParserKinds)
    {
        with(parse!(charRange!('a', 'z'), kind)(conv!"hoge"))
        {
                                     assert(match              == true);
            static if(kind.hasValue) assert(value              == 'h');
                                     assert(nextInput.source   == conv!"oge");
                                     assert(nextInput.position == 1);
                                     assert(nextInput.line     == 0);
        }

        with(parse!(charRange!(dchar.min, dchar.max), kind)(conv!"\nhoge"))
        {
                                     assert(match              == true);
            static if(kind.hasValue) assert(value              == '\n');
                                     assert(nextInput.source   == conv!"hoge");
                                     assert(nextInput.position == 1);
                                     assert(nextInput.line     == 1);
        }

        with(parse!(charRange!('a', 'z'), kind)(conv!""))
        {
                                     assert(match          == false);
            static if(kind.hasError) assert(error.msg      == "'a ~ z' expected");
            static if(kind.hasError) assert(error.position == 0);
        }

        with(parse!(charRange!('a', 'z'), kind)(conv!"鬱"))
        {
                                     assert(match          == false);
            static if(kind.hasError) assert(error.msg      == "'a ~ z' expected");
            static if(kind.hasError) assert(error.position == 0);
        }

        assertThrown!UnsupportedInputTypeException(parse!(charRange!('a', 'z'), kind)([1, 0]));

        debug(ctpgCompilesTest)
        {
            static assert(!__traits(compiles, parse!(charRange!('z', 'a'), kind)(conv!"")));
        }
    }
}

template getCallerLine()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ size_t };

        Result parse(Input!SrcType input, in Caller caller)
        {
            Result result;

            result.match = true;
            result.nextInput = input;

            static if(kind.hasValue)
            {
                result.value = caller.line;
            }

            return result;
        }
    }
}

debug(ctpg) unittest
{
    foreach(conv; convs) foreach(kind; ParserKinds)
    {
        with(parse!(getCallerLine!(), kind)(conv!""))
        {
                                     assert(match              == true);
                                     assert(nextInput.source   == conv!"");
                                     assert(nextInput.position == 0);
                                     assert(nextInput.line     == 0);
            static if(kind.hasValue) assert(value              == __LINE__ - 6);
        }
    }
}


template getCallerFile()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ string };

        Result parse(Input!SrcType input, in Caller caller)
        {
            Result result;

            result.match = true;
            result.nextInput = input;

            static if(kind.hasValue)
            {
                result.value = caller.file;
            }

            return result;
        }
    }
}

debug(ctpg) unittest
{
    foreach(conv; convs) foreach(kind; ParserKinds)
    {
        with(parse!(getCallerFile!(), kind)(conv!""))
        {
                                     assert(match              == true);
                                     assert(nextInput.source   == conv!"");
                                     assert(nextInput.position == 0);
                                     assert(nextInput.line     == 0);
            static if(kind.hasValue) assert(value              == __FILE__);
        }
    }
}


template getLine()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ size_t };

        Result parse(Input!SrcType input, in Caller caller)
        {
            Result result;

            result.match = true;
            result.nextInput = input;

            static if(kind.hasValue)
            {
                result.value = input.line;
            }

            return result;
        }
    }
}

debug(ctpg) unittest
{
    foreach(conv; convs) foreach(kind; ParserKinds)
    {
        with(parse!(getLine!(), kind)(conv!""))
        {
                                     assert(match              == true);
                                     assert(nextInput.source   == conv!"");
                                     assert(nextInput.position == 0);
                                     assert(nextInput.line     == 0);
            static if(kind.hasValue) assert(value              == 0);
        }
    }
}
