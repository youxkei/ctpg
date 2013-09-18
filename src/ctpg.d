import std.algorithm   : count;
import std.array       : save, empty;
import std.conv        : to, text;
import std.range       : ElementEncodingType, isForwardRange, isRandomAccessRange, hasSlicing;
import std.traits      : CommonType, EnumMembers, ReturnType, Unqual, isArray, isSomeChar, isSomeString;
import std.typecons    : Tuple, tuple;

// debug = ctpg;
// debug = ctpgSuppressErrorMsg;

debug(ctpg) version(unittest)
{
    import std.stdio     : writeln;
    import std.typetuple : TypeTuple;
    import std.exception : assertThrown;

    void main()
    {
        "pass".writeln();
    }


    template TestParser(alias value)
    {
        template build(alias kind, SrcType)
        {
            mixin MAKE_RESULT!q{ typeof(value) };

            Result parse(Input!SrcType input, in Caller caller)
            {
                Result result;

                result.match = true;
                result.nextInput = input;

                static if(kind.hasValue) result.value = value;

                return result;
            }
        }
    }


    auto rangize(T)(T source) if(isArray!T)
    {
        static struct Range
        {
            T source;

            const pure @safe nothrow @property
            Unqual!(ElementEncodingType!T) front(){ return source[0]; }

            pure @safe nothrow @property
            void popFront(){ source = source[1..$]; }

            const pure @safe nothrow @property
            bool empty(){ return source.length == 0; }

            const pure @safe nothrow @property
            Range save(){ return this; }

            const pure @safe nothrow @property
            size_t length(){ return source.length; }

            pure @safe nothrow
            Range opSlice(size_t begin, size_t end){ return Range(source[begin .. end]); }

            const pure @safe nothrow
            equals_t opEquals(Range rhs){ return source == rhs.source; }
        }

        return Range(source);
    }


    Input!SrcType inputize(SrcType)(SrcType source)
    {
        return typeof(return)(source);
    }


    template toString(alias input) {     enum toString     = cast(string)input; }
    template toWstring(alias input) {    enum toWstring    = cast(wstring)input; }
    template toDstring(alias input) {    enum toDstring    = cast(dstring)input; }
    template toCharRange(alias input) {  enum toCharRange  = (cast(string)input).rangize(); }
    template toWcharRange(alias input) { enum toWcharRange = (cast(wstring)input).rangize(); }
    template toDcharRange(alias input) { enum toDcharRange = (cast(dstring)input).rangize(); }

    alias convs = TypeTuple!(toString, toWstring, toDstring, toCharRange, toWcharRange, toDcharRange);


    alias ParserKinds = TypeTuple!(ParserKind!(true, true), ParserKind!(true, false), ParserKind!(false, true), ParserKind!(false, false));


    template root()
    {
        template build(alias kind, SrcType)
        {
            ParseResult!(kind, SrcType) parse(Input!SrcType input, in Caller caller)
            {
                return combinateChoice!
                (
                    combinateSequence!
                    (
                        parseString!"a",
                        root!(),
                        parseString!"a"
                    ),
                    parseString!"a"
                ).build!(kind, SrcType).parse(input, caller);
            }
        }
    }
}


class UnsupportedInputTypeException: Exception
{
    this(string msg)
    {
        super(msg);
    }
}


template ParserKind(bool hasValue_, bool hasError_)
{
    enum hasValue = hasValue_;
    enum hasError = hasError_;
}


mixin template MAKE_RESULT(string MixiningType)
{
    static if(kind.hasValue)
    {
        mixin("alias Result = ParseResult!(kind, SrcType, " ~ MixiningType ~ ");");
    }
    else
    {
        alias Result = ParseResult!(kind, SrcType);
    }
}


alias Caller = Tuple!(size_t, "line", string, "file");


alias None = Tuple!();


struct Error
{
    string msg;
    size_t position; 
}


struct Input(SrcType)
{
    SrcType source;
    size_t position;
    size_t line;

    @property
    Input save()
    {
        return Input(source.save, position, line);
    }
}


struct ParseResult(alias kind, SrcType, T = void)
{
    static if(kind.hasValue) static assert(!is(T == void));
    else                     static assert( is(T == void));

    bool match;
    Input!SrcType nextInput;

    static if(kind.hasValue) T value;
    static if(kind.hasError) Error error;
}


struct Option(T)
{
    bool some;
    T value;
    alias value this;
}


template getParseResultType(alias parser)
{
    static if(is(ReturnType!(parser.parse) == ParseResult!(kind, SrcType, T), SrcType, alias kind, T))
    {
        alias getParseResultType = T;
    }
}


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
    static bool test()
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

        return true;
    }

    static assert(test());
    test();
}


template parseEOF()
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
    static bool test()
    {
        foreach(conv; convs) foreach(kind; ParserKinds)
        {
            with(parse!(parseEOF!(), kind)(conv!""))
            {
                assert(match              == true);
                assert(nextInput.source   == conv!"");
                assert(nextInput.position == 0);
                assert(nextInput.line     == 0);
            }

            with(parse!(parseEOF!(), kind)(conv!"hoge"))
            {
                                         assert(match          == false);
                static if(kind.hasError) assert(error.msg      == "EOF expected");
                static if(kind.hasError) assert(error.position == 0);
            }

            assertThrown!UnsupportedInputTypeException(parse!(parseString!"hoge", kind)([0, 1]));
        }

        return true;
    }

    static assert(test());
    test();
}


template parseString(alias string str)
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
    static bool test()
    {
        foreach(conv; convs) foreach(kind; ParserKinds)
        {
            with(parse!(parseString!"hoge", kind)(conv!"hogehoge"))
            {
                                         assert(match              == true);
                static if(kind.hasValue) assert(value              == "hoge");
                                         assert(nextInput.source   == conv!"hoge");
                                         assert(nextInput.position == 4);
                                         assert(nextInput.line     == 0);
            }

            with(parse!(parseString!"\n\nhoge", kind)(conv!"\n\nhogehoge"))
            {
                                         assert(match              == true);
                static if(kind.hasValue) assert(value              == "\n\nhoge");
                                         assert(nextInput.source   == conv!"hoge");
                                         assert(nextInput.position == 6);
                                         assert(nextInput.line     == 2);
            }

            with(parse!(parseString!"hoge", kind)(conv!"fuga"))
            {
                                         assert(match          == false);
                static if(kind.hasError) assert(error.msg      == "'hoge' expected");
                static if(kind.hasError) assert(error.position == 0);
            }

            assertThrown!UnsupportedInputTypeException(parse!(parseString!"hoge", kind)([0, 1]));
        }

        return true;
    }

    static assert(test());
    test();
}


template parseCharRange(dchar begin, dchar end, size_t line = 0, string file = "")
{
    static if(begin > end)
    {
        debug(ctpgSuppressErrorMsg) {} else pragma(msg, file ~ "(" ~ line.to!string() ~ "): Error: Invalid char range");
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

template parseAnyChar(size_t line = 0, string file = "")
{
    alias parseAnyChar = parseCharRange!(dchar.min, dchar.max, line, file);
}

debug(ctpg) unittest
{
    static bool test()
    {
        foreach(conv; convs) foreach(kind; ParserKinds)
        {
            with(parse!(parseCharRange!('a', 'z'), kind)(conv!"hoge"))
            {
                                         assert(match              == true);
                static if(kind.hasValue) assert(value              == 'h');
                                         assert(nextInput.source   == conv!"oge");
                                         assert(nextInput.position == 1);
                                         assert(nextInput.line     == 0);
            }

            with(parse!(parseCharRange!(dchar.min, dchar.max), kind)(conv!"\nhoge"))
            {
                                         assert(match              == true);
                static if(kind.hasValue) assert(value              == '\n');
                                         assert(nextInput.source   == conv!"hoge");
                                         assert(nextInput.position == 1);
                                         assert(nextInput.line     == 1);
            }

            with(parse!(parseCharRange!('a', 'z'), kind)(conv!""))
            {
                                         assert(match          == false);
                static if(kind.hasError) assert(error.msg      == "'a ~ z' expected");
                static if(kind.hasError) assert(error.position == 0);
            }

            with(parse!(parseCharRange!('a', 'z'), kind)(conv!"鬱"))
            {
                                         assert(match          == false);
                static if(kind.hasError) assert(error.msg      == "'a ~ z' expected");
                static if(kind.hasError) assert(error.position == 0);
            }

            assertThrown!UnsupportedInputTypeException(parse!(parseCharRange!('a', 'z'), kind)([1, 0]));

            static assert(!__traits(compiles, parse!(parseCharRange!('z', 'a'), kind)(conv!"")));
        }

        return true;
    }

    static assert(test());
    test();
}


template parseSpaces()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ None };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinateNone!
            (
                combinateMore0!
                (
                    combinateChoice!
                    (
                        parseString!" ",
                        parseString!"\n",
                        parseString!"\t",
                        parseString!"\r",
                        parseString!"\f"
                    )
                )
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

alias skip = parseSpaces;

debug(ctpg) unittest
{
    static bool test()
    {
        foreach(conv; convs) foreach(kind; ParserKinds)
        {
        }

        return true;
    }

    static assert(test());
    test();
}


template parseGetLine()
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
    static bool test()
    {
        foreach(conv; convs) foreach(kind; ParserKinds)
        {
            with(parse!(parseGetLine!(), kind)(conv!""))
            {
                                         assert(match              == true);
                                         assert(nextInput.source   == conv!"");
                                         assert(nextInput.position == 0);
                                         assert(nextInput.line     == 0);
                static if(kind.hasValue) assert(value              == 0);
            }
        }

        return true;
    }

    static assert(test());
    test();
}


template parseGetCallerLine()
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
    static bool test()
    {
        foreach(conv; convs) foreach(kind; ParserKinds)
        {
            with(parse!(parseGetCallerLine!(), kind)(conv!""))
            {
                                         assert(match              == true);
                                         assert(nextInput.source   == conv!"");
                                         assert(nextInput.position == 0);
                                         assert(nextInput.line     == 0);
                static if(kind.hasValue) assert(value              == __LINE__ - 6);
            }
        }

        return true;
    }

    static assert(test());
    test();
}


template parseGetCallerFile()
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
    static bool test()
    {
        foreach(conv; convs) foreach(kind; ParserKinds)
        {
            with(parse!(parseGetCallerFile!(), kind)(conv!""))
            {
                                         assert(match              == true);
                                         assert(nextInput.source   == conv!"");
                                         assert(nextInput.position == 0);
                                         assert(nextInput.line     == 0);
                static if(kind.hasValue) assert(value              == __FILE__);
            }
        }

        return true;
    }

    static assert(test());
    test();
}


template combinateChangeError(alias parser, string errorMsg)
{
    template build(alias kind, SrcType)
    {
        static if(kind.hasError)
        {
            mixin MAKE_RESULT!q{ getParseResultType!(parser.build!(kind, SrcType)) };

            Result parse(Input!SrcType input, in Caller caller)
            {
                Result result;

                with(parser.build!(ParserKind!(kind.hasValue, false), SrcType).parse(input, caller))
                {
                    if(!match)
                    {
                        result.error.msg      = errorMsg;
                        result.error.position = input.position;
                    }

                    result.match     = match;
                    result.nextInput = nextInput;

                    static if(kind.hasValue)
                    {
                        result.value = value;
                    }
                }

                return result;
            }
        }
        else
        {
            alias parse = parser.build!(kind, SrcType).parse;
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        foreach(conv; convs) foreach(kind; ParserKinds)
        {
            with(parse!(combinateChangeError!(parseString!"hoge", "エラーだよ！！"), kind)(conv!"hoge"))
            {
                assert(match              == true);
                assert(nextInput.source   == conv!"");
                assert(nextInput.position == 4);
            }

            with(parse!(combinateChangeError!(parseString!"hoge", "エラーだよ！！"), kind)(conv!"fuga"))
            {
                                         assert(match          == false);
                static if(kind.hasError) assert(error.msg      == "エラーだよ！！");
                static if(kind.hasError) assert(error.position == 0);
            }

            with(parse!(combinateChangeError!(combinateSequence!(parseString!"hoge", parseString!"fuga"), "エラーだよ！！"), kind)(conv!"hoge"))
            {
                                         assert(match          == false);
                static if(kind.hasError) assert(error.msg      == "エラーだよ！！");
                static if(kind.hasError) assert(error.position == 0);
            }
        }

        return true;
    }

    static assert(test());
    test();
}


template combinateUnTuple(alias parser)
{
    template build(alias kind, SrcType)
    {
        static if(kind.hasValue)
        {
            static if(getParseResultType!(parser.build!(kind, SrcType)).length == 1)
            {
                mixin MAKE_RESULT!q{ getParseResultType!(parser.build!(kind, SrcType)).Types[0] };

                Result parse(Input!SrcType input, in Caller caller)
                {
                    Result result;

                    with(parser.build!(kind, SrcType).parse(input, caller))
                    {
                        static if(kind.hasError)
                        {
                            result.error = error;
                        }

                        if(match)
                        {
                            result.match = true;
                            result.nextInput = nextInput;
                            result.value = value[0];
                        }
                    }

                    return result;
                }
            }
            else
            {
                alias parse = parser.build!(kind, SrcType).parse;
            }
        }
        else
        {
            alias parse = parser.build!(kind, SrcType).parse;
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        foreach(conv; convs) foreach(kind; ParserKinds)
        {
            with(parse!(combinateUnTuple!(TestParser!(tuple("hoge", "fuga"))), kind)(conv!"input"))
            {
                                         assert(match            == true);
                static if(kind.hasValue) assert(value            == tuple("hoge", "fuga"));
                                         assert(nextInput.source == conv!"input");
            }

            with(parse!(combinateUnTuple!(TestParser!(tuple("hoge"))), kind)(conv!"input"))
            {
                                         assert(match            == true);
                static if(kind.hasValue) assert(value            == "hoge");
                                         assert(nextInput.source == conv!"input");
            }
        }

        return true;
    }

    static assert(test());
    test();
}


template combinateSequence(parsers...)
{
    static assert(parsers.length > 0);

    template build(alias kind, SrcType)
    {
        static if(parsers.length == 1)
        {
            alias T = getParseResultType!(parsers[0].build!(kind, SrcType));

            static if(is(T == None)) mixin MAKE_RESULT!q{ Tuple!() };
            else                     mixin MAKE_RESULT!q{ Tuple!T  };

            Result parse(Input!SrcType input, in Caller caller)
            {
                Result result;

                auto head = parsers[0].build!(kind, SrcType).parse(input, caller);

                static if(kind.hasError)
                {
                    result.error = head.error;
                }

                if(!head.match)
                {
                    return result;
                }

                result.match     = true;
                result.nextInput = head.nextInput;

                static if(kind.hasValue && !is(T == None))
                {
                    result.value = tuple(head.value);
                }

                return result;
            }
        }
        else static if(parsers.length > 1)
        {
            alias T = getParseResultType!(parsers[0].build!(kind, SrcType));

            static if(is(T == None)) mixin MAKE_RESULT!q{           getParseResultType!(combinateSequence!(parsers[1..$]).build!(kind, SrcType)) };
            else                     mixin MAKE_RESULT!q{ Tuple!(T, getParseResultType!(combinateSequence!(parsers[1..$]).build!(kind, SrcType)).Types) };

            Result parse(Input!SrcType input, in Caller caller)
            {
                Result result;

                auto head = parsers[0].build!(kind, SrcType).parse(input, caller);

                static if(kind.hasError)
                {
                    result.error = head.error;
                }

                if(!head.match)
                {
                    return result;
                }

                auto tail = combinateSequence!(parsers[1..$]).build!(kind, SrcType).parse(head.nextInput, caller);

                static if(kind.hasError)
                {
                    if(result.error.position <=  tail.error.position)
                    {
                        result.error = tail.error;
                    }
                }

                if(!tail.match)
                {
                    return result;
                }

                result.match = true;
                result.nextInput = tail.nextInput;

                static if(kind.hasValue)
                {
                    static if(is(T == None)) result.value =                   tail.value;
                    else                     result.value = tuple(head.value, tail.value.field);
                }

                return result;
            }
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        foreach(conv; convs) foreach(kind; ParserKinds)
        {
            with(parse!(combinateSequence!(parseString!"hoge", parseString!"fuga"), kind)(conv!"hogefugahoge"))
            {
                                         assert(match            == true);
                static if(kind.hasValue) assert(value            == tuple("hoge", "fuga"));
                                         assert(nextInput.source == conv!"hoge");
            }

            with(parse!(combinateSequence!(parseString!"hoge", parseString!"fuga"), kind)(conv!"hoge"))
            {
                                         assert(match          == false);
                static if(kind.hasError) assert(error.msg      == "'fuga' expected");
                static if(kind.hasError) assert(error.position == 4);
            }

            with(parse!(combinateSequence!(parseString!"hoge", parseString!"fuga"), kind)(conv!"fuga"))
            {
                                         assert(match          == false);
                static if(kind.hasError) assert(error.msg      == "'hoge' expected");
                static if(kind.hasError) assert(error.position == 0);
            }

            with(parse!(combinateSequence!(parseString!"hoge", TestParser!(None()), parseString!"fuga"), kind)(conv!"hogefuga"))
            {
                                         assert(match            == true);
                static if(kind.hasValue) assert(value            == tuple("hoge", "fuga"));
                                         assert(nextInput.source == conv!"");
            }
        }

        return true;
    }

    static assert(test());
    test();
}


template combinateChoice(parsers...)
{
    static assert(parsers.length > 0);

    template build(alias kind, SrcType)
    {
        static if(parsers.length == 1)
        {
            mixin MAKE_RESULT!q{ getParseResultType!(parsers[0].build!(kind, SrcType)) };

            Result parse(Input!SrcType input, in Caller caller)
            {
                Result result;

                auto head = parsers[0].build!(kind, SrcType).parse(input, caller);

                static if(kind.hasError)
                {
                    result.error = head.error;
                }

                if(head.match)
                {
                    result.match = true;
                    result.nextInput = head.nextInput;

                    static if(kind.hasValue)
                    {
                        result.value = head.value;
                    }
                }


                return result;
            }
        }
        else static if(parsers.length > 1)
        {
            mixin MAKE_RESULT!q{ CommonType!(getParseResultType!(parsers[0].build!(kind, SrcType)), getParseResultType!(combinateChoice!(parsers[1..$]).build!(kind, SrcType))) };

            Result parse(Input!SrcType input, in Caller caller)
            {
                Result result;

                auto head = parsers[0].build!(kind, SrcType).parse(input.save, caller);

                static if(kind.hasError)
                {
                    result.error = head.error;
                }

                if(head.match)
                {
                    result.match = true;
                    result.nextInput = head.nextInput;

                    static if(kind.hasValue)
                    {
                        result.value = head.value;
                    }

                    return result;
                }

                auto tail = combinateChoice!(parsers[1..$]).build!(kind, SrcType).parse(input, caller);

                static if(kind.hasError)
                {
                    if(result.error.position <= tail.error.position)
                    {
                        result.error = tail.error;
                    }
                }

                if(tail.match)
                {
                    result.match = true;
                    result.nextInput = tail.nextInput;

                    static if(kind.hasValue)
                    {
                        result.value = tail.value;
                    }
                }

                return result;
            }
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        foreach(conv; convs) foreach(kind; ParserKinds)
        {
            with(parse!(combinateChoice!(parseString!"hoge", parseString!"fuga"), kind)(conv!"hoge"))
            {
                                         assert(match              == true);
                static if(kind.hasValue) assert(value              == "hoge");
                                         assert(nextInput.source   == conv!"");
                                         assert(nextInput.position == 4);
            }

            with(parse!(combinateChoice!(parseString!"hoge", parseString!"fuga"), kind)(conv!"fuga"))
            {
                                         assert(match              == true);
                static if(kind.hasValue) assert(value              == "fuga");
                                         assert(nextInput.source   == conv!"");
                                         assert(nextInput.position == 4);
            }

            with(parse!(combinateChoice!(parseString!"hoge", parseString!"fuga"), kind)(conv!"piyo"))
            {
                                         assert(match          == false);
                static if(kind.hasError) assert(error.msg      == "'fuga' expected");
                static if(kind.hasError) assert(error.position == 0);
            }

            with(parse!(combinateChoice!(combinateSequence!(parseString!"hoge", parseString!"piyo"), parseString!"fuga"), ParserKind!(false, kind.hasError))(conv!"hoge"))
            {
                                         assert(match          == false);
                static if(kind.hasError) assert(error.msg      == "'piyo' expected");
                static if(kind.hasError) assert(error.position == 4);
            }
        }

        return true;
    }

    static assert(test());
    test();
}


template combinateMore(size_t n, alias parser, alias sep = success!())
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ getParseResultType!(parser.build!(kind, SrcType))[] };

        Result parse(Input!SrcType input, in Caller caller)
        {
            Result result;
            size_t size = 1;
            Input!SrcType next = input.save;

            auto head = parser.build!(kind, SrcType).parse(next, caller);

            static if(kind.hasError)
            {
                result.error = head.error;
            }

            if(!head.match)
            {
                if(n == 0)
                {
                    result.match = true;
                    result.nextInput = input;
                }

                return result;
            }

            static if(kind.hasValue)
            {
                result.value ~= head.value;
            }

            next = head.nextInput.save;

            while(true)
            {
                auto r1 = sep.build!(ParserKind!(false, kind.hasError), SrcType).parse(next, caller);

                static if(kind.hasError)
                {
                    if(result.error.position <= r1.error.position)
                    {
                        result.error = r1.error;
                    }
                }

                if(r1.match)
                {
                    auto r2 = parser.build!(kind, SrcType).parse(r1.nextInput, caller);

                    static if(kind.hasError)
                    {
                        if(result.error.position <= r2.error.position)
                        {
                            result.error = r2.error;
                        }
                    }

                    if(r2.match)
                    {
                        static if(kind.hasValue)
                        {
                            result.value ~= r2.value;
                        }

                        ++size;
                        next = r2.nextInput;
                    } 
                    else
                    {
                        if(size < n)
                        {
                            return result;
                        }

                        break;
                    }
                }
                else
                {
                    if(size < n)
                    {
                        return result;
                    }

                    break;
                }
            }

            result.match = true;
            result.nextInput = next;

            return result;
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        foreach(conv; convs) foreach(kind; ParserKinds)
        {
            with(parse!(combinateMore!(0, parseString!"hoge", parseString!","), kind)(conv!""))
            {
                                         assert(match              == true);
                static if(kind.hasValue) assert(value              == []);
                                         assert(nextInput.source   == conv!"");
                                         assert(nextInput.position == 0);
            }

            with(parse!(combinateMore!(0, parseString!"hoge", parseString!","), kind)(conv!"hoge,hoge,hoge"))
            {
                                         assert(match              == true);
                static if(kind.hasValue) assert(value              == ["hoge", "hoge", "hoge"]);
                                         assert(nextInput.source   == conv!"");
                                         assert(nextInput.position == 14);
            }

            with(parse!(combinateMore!(0, parseString!"hoge", parseString!","), kind)(conv!"hoge,hoge,hoge,"))
            {
                                         assert(match              == true);
                static if(kind.hasValue) assert(value              == ["hoge", "hoge", "hoge"]);
                                         assert(nextInput.source   == conv!",");
                                         assert(nextInput.position == 14);
            }

            with(parse!(combinateMore!(4, parseString!"hoge", parseString!","), kind)(conv!"hoge,hoge,hoge"))
            {
                                         assert(match          == false);
                static if(kind.hasError) assert(error.msg      == "',' expected");
                static if(kind.hasError) assert(error.position == 14);
            }

            with(parse!(combinateMore!(4, parseString!"hoge", parseString!","), kind)(conv!"hoge,hoge,hoge,"))
            {
                                         assert(match          == false);
                static if(kind.hasError) assert(error.msg      == "'hoge' expected");
                static if(kind.hasError) assert(error.position == 15);
            }
        }

        return true;
    }

    static assert(test());
    test();
}


template combinateMore0(alias parser, alias sep = success!())
{
    alias combinateMore0 = combinateMore!(0, parser, sep);
}


template combinateMore1(alias parser, alias sep = success!())
{
    alias combinateMore1 = combinateMore!(1, parser, sep);
}


template combinateOption(alias parser)
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Option!(getParseResultType!(parser.build!(kind, SrcType))) };

        Result parse(Input!SrcType input, in Caller caller)
        {
            Result result;
            result.match = true;

            with(parser.build!(kind, SrcType).parse(input.save, caller))
            {
                static if(kind.hasError)
                {
                    result.error = error;
                }

                if(match)
                {
                    result.nextInput = nextInput;

                    static if(kind.hasValue)
                    {
                        result.value.value = value;
                        result.value.some = true;
                    }
                }
                else
                {
                    result.nextInput = input;
                }
            }

            return result;
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        foreach(conv; convs) foreach(kind; ParserKinds)
        {
            with(parse!(combinateOption!(parseString!"hoge"), kind)(conv!"fuga"))
            {
                                         assert(match              == true);
                static if(kind.hasValue) assert(value.some         == false);
                                         assert(nextInput.source   == conv!"fuga");
                                         assert(nextInput.position == 0);
            }

            with(parse!(combinateOption!(parseString!"hoge"), kind)(conv!"hoge"))
            {
                                         assert(match              == true);
                static if(kind.hasValue) assert(value.some         == true);
                static if(kind.hasValue) assert(value        == "hoge");
                                         assert(nextInput.source   == conv!"");
            }
        }

        return true;
    }

    static assert(test());
    test();
}


template combinateNone(alias parser)
{
    template build(alias kind, SrcType)
    {
        static if(kind.hasValue)
        {
            alias Result = ParseResult!(kind, SrcType, None);

            Result parse(Input!SrcType input, in Caller caller)
            {
                Result result;

                with(parser.build!(ParserKind!(false, kind.hasError), SrcType).parse(input, caller))
                {
                    static if(kind.hasError)
                    {
                        result.error = error;
                    }

                    result.match = match;

                    if(match)
                    {
                        result.nextInput = nextInput;
                    }
                }

                return result;
            }
        }
        else
        {
            alias parse = parser.build!(kind, SrcType).parse;
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        foreach(conv; convs) foreach(kind; ParserKinds)
        {
            with(parse!(combinateNone!(parseString!"hoge"), kind)(conv!"hoge"))
            {
                                         assert(match              == true);
                static if(kind.hasValue) assert(value              == None());
                                         assert(nextInput.source   == conv!"");
                                         assert(nextInput.position == 4);
            }

            with(parse!(combinateNone!(parseString!"hoge"), kind)(conv!"fuga"))
            {
                                         assert(match          == false);
                static if(kind.hasError) assert(error.msg      == "'hoge' expected");
                static if(kind.hasError) assert(error.position == 0);
            }
        }

        return true;
    }

    static assert(test());
    test();
}


template combinateAndPred(alias parser)
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ None };

        Result parse(Input!SrcType input, in Caller caller)
        {
            Result result;
            result.nextInput = input;

            with(parser.build!(ParserKind!(false, kind.hasError), SrcType).parse(input.save, caller))
            {
                static if(kind.hasError)
                {
                    result.error = error;
                }

                result.match = match;
            }

            return result;
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        foreach(conv; convs) foreach(kind; ParserKinds)
        {
            with(parse!(combinateAndPred!(parseString!"hoge"), kind)(conv!"hoge"))
            {
                                         assert(match              == true);
                static if(kind.hasValue) assert(value              == None());
                                         assert(nextInput.source   == conv!"hoge");
                                         assert(nextInput.position == 0);
            }

            with(parse!(combinateAndPred!(parseString!"hoge"), kind)(conv!"fuga"))
            {
                                         assert(match          == false);
                static if(kind.hasError) assert(error.msg      == "'hoge' expected");
                static if(kind.hasError) assert(error.position == 0);
            }
        }

        return true;
    }

    static assert(test());
    test();
}


template combinateNotPred(alias parser)
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ None };

        Result parse(Input!SrcType input, in Caller caller)
        {
            Result result;
            result.nextInput = input;

            with(parser.build!(ParserKind!(false, false), SrcType).parse(input.save, caller))
            {
                static if(kind.hasError)
                {
                    result.error.msg = "failure expected";
                    result.error.position = input.position;
                }

                result.match = !match;
            }

            return result;
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        foreach(conv; convs) foreach(kind; ParserKinds)
        {
            with(parse!(combinateNotPred!(parseString!"hoge"), kind)(conv!"fuga"))
            {
                                         assert(match              == true);
                static if(kind.hasValue) assert(value              == None());
                                         assert(nextInput.source   == conv!"fuga");
                                         assert(nextInput.position == 0);
            }

            with(parse!(combinateNotPred!(parseString!"hoge"), kind)(conv!"hoge"))
            {
                                         assert(match          == false);
                static if(kind.hasError) assert(error.msg      == "failure expected");
                static if(kind.hasError) assert(error.position == 0);
            }
        }

        return true;
    }

    static assert(test());
    test();
}


template combinateConvert(alias parser, alias converter, size_t line = 0, string file = "")
{
    template build(alias kind, SrcType)
    {
        static if(kind.hasValue)
        {
            alias T = getParseResultType!(parser.build!(kind, SrcType));

                 static if(is(converter == class ) && __traits(compiles, new converter(T.init.field))) alias ConverterType = converter;
            else static if(is(converter == class ) && __traits(compiles, new converter(T.init      ))) alias ConverterType = converter;
            else static if(is(converter == struct) && __traits(compiles,     converter(T.init.field))) alias ConverterType = converter;
            else static if(is(converter == struct) && __traits(compiles,     converter(T.init      ))) alias ConverterType = converter;
            else static if(                           __traits(compiles,     converter(T.init.field))) alias ConverterType = typeof(converter(T.init.field));
            else static if(                           __traits(compiles,     converter(T.init      ))) alias ConverterType = typeof(converter(T.init      ));
            else                                                                                       alias ConverterType = void;

            static if(is(ConverterType == void))
            {
                debug(ctpgSuppressErrorMsg) {} else pragma(msg, file ~ "(" ~ line.to!string() ~ "): Error: Cannot call '" ~ converter.stringof ~ "' using '>>' with types: " ~ T.stringof);
                static assert(false);
            }

            mixin MAKE_RESULT!q{ ConverterType };

            static Result parse(Input!SrcType input, in Caller caller)
            {
                Result result;

                with(parser.build!(kind, SrcType).parse(input, caller))
                {
                    static if(kind.hasError)
                    {
                        result.error = error;
                    }

                    if(match)
                    {
                        result.match = true;
                        result.nextInput = nextInput;

                        static if(kind.hasValue)
                        {
                                 static if(is(converter == class ) && __traits(compiles, new converter(T.init.field))) result.value = new converter(value.field);
                            else static if(is(converter == class ) && __traits(compiles, new converter(T.init      ))) result.value = new converter(value      );
                            else static if(                           __traits(compiles,     converter(T.init.field))) result.value =     converter(value.field);
                            else static if(                           __traits(compiles,     converter(T.init      ))) result.value =     converter(value      );
                        }
                    }
                }

                return result;
            }
        }
        else
        {
            alias parse = parser.build!(kind, SrcType).parse;
        }
    }
}

debug(ctpg) unittest
{
    static struct Struct
    {
        size_t len;

        this(string str)
        {
            len = str.length;
        }
    }

    static class Class
    {
        size_t len;

        this(string str)
        {
            len = str.length;
        }
    }
    
    static size_t Function(string str)
    {
        return str.length;
    }

    static size_t TemplateFunction(T)(T str)
    {
        return str.length;
    }

    static bool test()
    {
        foreach(conv; convs) foreach(kind; ParserKinds)
        {
            with(parse!(combinateConvert!(parseString!"hoge", Struct), kind)(conv!"hogee"))
            {
                                         assert(match              == true);
                static if(kind.hasValue) assert(value.len          == 4);
                                         assert(nextInput.source   == conv!"e");
                                         assert(nextInput.position == 4);
            }

            with(parse!(combinateConvert!(parseString!"hoge", Struct), kind)(conv!"!!!!"))
            {
                                         assert(match          == false);
                static if(kind.hasError) assert(error.msg      == "'hoge' expected");
                static if(kind.hasError) assert(error.position == 0);
            }

            with(parse!(combinateConvert!(parseString!"hoge", Class), kind)(conv!"hogee"))
            {
                                         assert(match              == true);
                static if(kind.hasValue) assert(value.len          == 4);
                                         assert(nextInput.source   == conv!"e");
                                         assert(nextInput.position == 4);
            }

            with(parse!(combinateConvert!(parseString!"hoge", Class), kind)(conv!"!!!!"))
            {
                                         assert(match          == false);
                static if(kind.hasError) assert(error.msg      == "'hoge' expected");
                static if(kind.hasError) assert(error.position == 0);
            }

            with(parse!(combinateConvert!(parseString!"hoge", Function), kind)(conv!"hogee"))
            {
                                         assert(match              == true);
                static if(kind.hasValue) assert(value              == 4);
                                         assert(nextInput.source   == conv!"e");
                                         assert(nextInput.position == 4);
            }

            with(parse!(combinateConvert!(parseString!"hoge", Function), kind)(conv!"!!!!"))
            {
                                         assert(match          == false);
                static if(kind.hasError) assert(error.msg      == "'hoge' expected");
                static if(kind.hasError) assert(error.position == 0);
            }

            with(parse!(combinateConvert!(parseString!"hoge", TemplateFunction), kind)(conv!"hogee"))
            {
                                         assert(match              == true);
                static if(kind.hasValue) assert(value              == 4);
                                         assert(nextInput.source   == conv!"e");
                                         assert(nextInput.position == 4);
            }

            with(parse!(combinateConvert!(parseString!"hoge", TemplateFunction), kind)(conv!"!!!!"))
            {
                                         assert(match          == false);
                static if(kind.hasError) assert(error.msg      == "'hoge' expected");
                static if(kind.hasError) assert(error.position == 0);
            }

            with(parse!(combinateConvert!(parseString!"hoge", (x) => x.length), kind)(conv!"hogee"))
            {
                                         assert(match              == true);
                static if(kind.hasValue) assert(value              == 4);
                                         assert(nextInput.source   == conv!"e");
                                         assert(nextInput.position == 4);
            }

            with(parse!(combinateConvert!(parseString!"hoge", (x) => x.length), kind)(conv!"!!!!"))
            {
                                         assert(match          == false);
                static if(kind.hasError) assert(error.msg      == "'hoge' expected");
                static if(kind.hasError) assert(error.position == 0);
            }

            with(parse!(combinateConvert!(parseString!"hoge", (x){ return x.length; }), kind)(conv!"hogee"))
            {
                                         assert(match              == true);
                static if(kind.hasValue) assert(value              == 4);
                                         assert(nextInput.source   == conv!"e");
                                         assert(nextInput.position == 4);
            }

            with(parse!(combinateConvert!(parseString!"hoge", (x){ return x.length; }), kind)(conv!"!!!!"))
            {
                                         assert(match          == false);
                static if(kind.hasError) assert(error.msg      == "'hoge' expected");
                static if(kind.hasError) assert(error.position == 0);
            }

            static if(kind.hasValue) static assert(!__traits(compiles, parse!(combinateConvert!(parseString!"hoge", (size_t x){ return x; }), kind)(conv!"hoge")));
        }

        return true;
    }

    static assert(test());
    test();
}


template combinateCheck(alias parser, alias checker, size_t line = 0, string file = "")
{
    template build(alias kind, SrcType)
    {
        alias T = getParseResultType!(parser.build!(ParserKind!(true, kind.hasError), SrcType));

        static if(!__traits(compiles, checker(T.init.field)) && !__traits(compiles, checker(T.init)))
        {
            debug(ctpgSuppressErrorMsg) {} else pragma(msg, file ~ "(" ~ line.to!string() ~ "): Error: Cannot call '" ~ checker.stringof ~ "' using '>?' with types: " ~ T.stringof);
            static assert(false);
        }
        else static if(!is(typeof(checker(T.init.field)) == bool) && !is(typeof(checker(T.init)) == bool))
        {
            debug(ctpgSuppressErrorMsg) {} else pragma(msg, file ~ "(" ~ line.to!string() ~ "): Error: '" ~ checker.stringof ~ "' does not return bool");
            static assert(false);
        }

        mixin MAKE_RESULT!q{ T };

        Result parse(Input!SrcType input, in Caller caller)
        {
            Result result;

            with(parser.build!(ParserKind!(true, kind.hasError), SrcType).parse(input, caller))
            {
                static if(kind.hasError)
                {
                    result.error = error;
                }

                if(match)
                {
                         static if(is(typeof(checker(T.init.field)) == bool)) result.match = checker(value.field);
                    else static if(is(typeof(checker(T.init      )) == bool)) result.match = checker(value      );

                    if(result.match)
                    {
                        result.nextInput = nextInput;

                        static if(kind.hasValue)
                        {
                            result.value = value;
                        }
                    }
                    else
                    {
                        static if(kind.hasError)
                        {
                            result.error.msg = "passing check expected";
                            result.error.position = input.position;
                        }
                    }
                }
            }

            return result;
        }
    }
}

debug(ctpg) unittest
{
    static bool Function(string str)
    {
        return str.length == 4;
    }

    static bool test()
    {
        foreach(conv; convs) foreach(kind; ParserKinds)
        {
            with(parse!(combinateCheck!(parseString!"hoge", Function), kind)(conv!"hoge!"))
            {
                                         assert(match              == true);
                static if(kind.hasValue) assert(value              == "hoge");
                                         assert(nextInput.source   == conv!"!");
                                         assert(nextInput.position == 4);
            }

            with(parse!(combinateCheck!(parseString!"hoge!", Function), kind)(conv!"hoge!"))
            {
                                         assert(match          == false);
                static if(kind.hasError) assert(error.msg      == "passing check expected");
                static if(kind.hasError) assert(error.position == 0);
            }

            with(parse!(combinateCheck!(parseString!"hoge", Function), kind)(conv!"fuga"))
            {
                                         assert(match          == false);
                static if(kind.hasError) assert(error.msg      == "'hoge' expected");
                static if(kind.hasError) assert(error.position == 0);
            }

            static assert(!__traits(compiles, parse!(combinateCheck!(parseString!"hoge", (int    i  ){ return false; }), kind)(conv!"hoge")));
            static assert(!__traits(compiles, parse!(combinateCheck!(parseString!"hoge", (string str){ return 0;     }), kind)(conv!"hoge")));
        }

        return true;
    }

    static assert(test());
    test();
}


template combinateInputSlice(alias parser, size_t line = 0, string file = "")
{
    template build(alias kind, SrcType)
    {
        static if(kind.hasValue)
        {
            static if(!isArray!SrcType && !hasSlicing!SrcType)
            {
                debug(ctpgSuppressErrorMsg) {} else pragma(msg, file ~ "(" ~ line.to!string() ~ "): Error: Input type should be sliceable");
                static assert(false);
            }

            alias Result = ParseResult!(kind, SrcType, SrcType);

            Result parse(Input!SrcType input, in Caller caller)
            {
                Result result;

                with(parser.build!(ParserKind!(false, kind.hasError), SrcType).parse(input.save, caller))
                {
                    static if(kind.hasError)
                    {
                        result.error = error;
                    }

                    if(match)
                    {
                        result.match = true;
                        result.nextInput = nextInput;

                        static if(kind.hasValue)
                        {
                            result.value = input.source[0 .. nextInput.position - input.position];
                        }
                    }
                }

                return result;
            }
        }
        else
        {
            alias parse = parser.build!(kind, SrcType).parse;
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        foreach(conv; convs) foreach(kind; ParserKinds)
        {
            with(parse!(combinateInputSlice!(combinateSequence!(parseString!"hoge", parseString!"fuga")), kind)(conv!"hogefugapiyo"))
            {
                                         assert(match              == true);
                static if(kind.hasValue) assert(value              == conv!"hogefuga");
                                         assert(nextInput.source   == conv!"piyo");
                                         assert(nextInput.position == 8);
            }

            static if(kind.hasValue) static assert(!__traits(compiles, parse!(combinateInputSlice!(parseString!"hoge"), kind)(0)));
        }

        return true;
    }

    static assert(test());
    test();
}


template combinateMemoize(alias parser)
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ getParseResultType!(parser.build!(kind, SrcType)) };

        Result parse(Input!SrcType input, in Caller caller)
        {
            if(!__ctfe)
            {
                static typeof(return)[Input!SrcType] memo;

                auto p = input in memo;
                if(p)
                {
                    return *p;
                }

                auto result = parser.build!(kind, SrcType).parse(input, caller);
                memo[input] = result;

                return result;
            }
            else
            {
                return parser.build!(kind, SrcType).parse(input, caller);
            }
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        foreach(conv; convs) foreach(kind; ParserKinds)
        {
            with(parse!(combinateMemoize!(parseString!"hoge"), kind)(conv!"hogehoge"))
            {
                                         assert(match              == true);
                static if(kind.hasValue) assert(value              == "hoge");
                                         assert(nextInput.source   == conv!"hoge");
                                         assert(nextInput.position == 4);
                                         assert(nextInput.line     == 0);
            }

            with(parse!(combinateMemoize!(parseString!"hoge"), kind)(conv!"hogehoge"))
            {
                                         assert(match              == true);
                static if(kind.hasValue) assert(value              == "hoge");
                                         assert(nextInput.source   == conv!"hoge");
                                         assert(nextInput.position == 4);
                                         assert(nextInput.line     == 0);
            }

            with(parse!(combinateMemoize!(parseString!"\n\nhoge"), kind)(conv!"\n\nhogehoge"))
            {
                                         assert(match              == true);
                static if(kind.hasValue) assert(value              == "\n\nhoge");
                                         assert(nextInput.source   == conv!"hoge");
                                         assert(nextInput.position == 6);
                                         assert(nextInput.line     == 2);
            }

            with(parse!(combinateMemoize!(parseString!"\n\nhoge"), kind)(conv!"\n\nhogehoge"))
            {
                                         assert(match              == true);
                static if(kind.hasValue) assert(value              == "\n\nhoge");
                                         assert(nextInput.source   == conv!"hoge");
                                         assert(nextInput.position == 6);
                                         assert(nextInput.line     == 2);
            }
        }

        return true;
    }

    static assert(test());
    test();
}


template combinateSkip(alias skip, alias parser)
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ getParseResultType!(parser.build!(kind, SrcType)) };

        Result parse(Input!SrcType input, in Caller caller)
        {
            auto skipped = skip.build!(ParserKind!(false, kind.hasError), SrcType).parse(input.save, caller);

            if(skipped.match)
            {
                return parser.build!(kind, SrcType).parse(skipped.nextInput, caller);
            }
            else
            {
                return parser.build!(kind, SrcType).parse(input, caller);
            }
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        foreach(conv; convs) foreach(kind; ParserKinds)
        {
            with(parse!(combinateSkip!(parseString!"\n", parseString!"hoge"), kind)(conv!"hogehoge"))
            {
                                         assert(match              == true);
                static if(kind.hasValue) assert(value              == "hoge");
                                         assert(nextInput.source   == conv!"hoge");
                                         assert(nextInput.position == 4);
                                         assert(nextInput.line     == 0);
            }

            with(parse!(combinateSkip!(parseString!"\n\n", parseString!"hoge"), kind)(conv!"\n\nhogehoge"))
            {
                                         assert(match              == true);
                static if(kind.hasValue) assert(value              == "hoge");
                                         assert(nextInput.source   == conv!"hoge");
                                         assert(nextInput.position == 6);
                                         assert(nextInput.line     == 2);
            }
        }

        return true;
    }

    static assert(test());
    test();
}


debug(ctpg) unittest
{
    static bool test()
    {
        foreach(conv; convs) foreach(kind; ParserKinds)
        {
            with(parse!(root!(), ParserKind!(false, kind.hasError))(conv!"aaa"))
            {
                assert(match              == true);
                assert(nextInput.source   == conv!"");
                assert(nextInput.position == 3);
            }

            with(parse!(root!(), ParserKind!(false, kind.hasError))(conv!"aaaa"))
            {
                assert(match              == true);
                assert(nextInput.source   == conv!"aaa");
                assert(nextInput.position == 1);
            }
        }

        return true;
    }

    static assert(test());
    test();
}


struct DLex
{
    static:


    template Identifier()
    {
        template build(alias kind, SrcType)
        {
            mixin MAKE_RESULT!q{ SrcType };

            Result parse(Input!SrcType input, in Caller caller)
            {
                return combinateInputSlice!
                (
                    combinateSequence!
                    (
                        combinateChoice!
                        (
                            parseCharRange!('a', 'z'),
                            parseCharRange!('A', 'Z'),
                            parseString!"_",
                        ),
                        combinateMore0!
                        (
                            combinateChoice!
                            (
                                parseCharRange!('a', 'z'),
                                parseCharRange!('A', 'Z'),
                                parseCharRange!('0', '9'),
                                parseString!"_",
                            )
                        )
                    )
                ).build!(kind, SrcType).parse(input, caller);
            }
        }
    }

    debug(ctpg) unittest
    {
        static bool test()
        {
            foreach(conv; convs) foreach(kind; ParserKinds)
            {
                with(parse!(Identifier!(), kind)(conv!"_ab0="))
                {
                                             assert(match              == true);
                                             assert(nextInput.source   == conv!"=");
                                             assert(nextInput.position == 4);
                                             assert(nextInput.line     == 0);
                    static if(kind.hasValue) assert(value              == conv!"_ab0");
                }
            }

            return true;
        }

        static assert(test());
        test();
    }


    template StringLiteral()
    {
        template build(alias kind, SrcType)
        {
            mixin MAKE_RESULT!q{ SrcType };

            Result parse(Input!SrcType input, in Caller caller)
            {
                return combinateInputSlice!
                (
                    combinateChoice!
                    (
                        WysiwygString!(),
                        AlternateWysiwygString!(),
                        DoubleQuotedString!()
                    )
                ).build!(kind, SrcType).parse(input, caller);
            }
        }
    }

    debug(ctpg) unittest
    {
        static bool test()
        {
            foreach(conv; convs) foreach(kind; ParserKinds)
            {
            }

            return true;
        }

        static assert(test());
        test();
    }


    template WysiwygString()
    {
        template build(alias kind, SrcType)
        {
            mixin MAKE_RESULT!q{ SrcType };

            static Result parse(Input!SrcType input, in Caller caller)
            {
                return combinateInputSlice!
                (
                    combinateSequence!
                    (
                        parseString!"r\"",
                        combinateMore0!
                        (
                            combinateSequence!
                            (
                                combinateNotPred!
                                (
                                    parseString!"\""
                                ),
                                parseCharRange!(dchar.min, dchar.max)
                            )
                        ),
                        parseString!"\""
                    )
                ).build!(kind, SrcType).parse(input, caller);
            }
        }
    }

    debug(ctpg) unittest
    {
        static bool test()
        {
            foreach(conv; convs) foreach(kind; ParserKinds)
            {
            }

            return true;
        }

        static assert(test());
        test();
    }


    template AlternateWysiwygString()
    {
        template build(alias kind, SrcType)
        {
            mixin MAKE_RESULT!q{ SrcType };

            static Result parse(Input!SrcType input, in Caller caller)
            {
                return combinateInputSlice!
                (
                    combinateSequence!
                    (
                        parseString!"`",
                        combinateMore0!
                        (
                            combinateSequence!
                            (
                                combinateNotPred!
                                (
                                    parseString!"`"
                                ),
                                parseCharRange!(dchar.min, dchar.max)
                            )
                        ),
                        parseString!"`"
                    )
                ).build!(kind, SrcType).parse(input, caller);
            }
        }
    }

    debug(ctpg) unittest
    {
        static bool test()
        {
            foreach(conv; convs) foreach(kind; ParserKinds)
            {
            }

            return true;
        }

        static assert(test());
        test();
    }


    template DoubleQuotedString()
    {
        template build(alias kind, SrcType)
        {
            mixin MAKE_RESULT!q{ SrcType };

            static Result parse(Input!SrcType input, in Caller caller)
            {
                return combinateInputSlice!
                (
                    combinateSequence!
                    (
                        parseString!"\"",
                        combinateMore0!
                        (
                            combinateSequence!
                            (
                                combinateNotPred!
                                (
                                    parseString!"\""
                                ),
                                combinateChoice!
                                (
                                    EscapeSequence!(),
                                    parseCharRange!(dchar.min, dchar.max)
                                )
                            )
                        ),
                        parseString!"\""
                    )
                ).build!(kind, SrcType).parse(input, caller);
            }
        }
    }

    debug(ctpg) unittest
    {
        static bool test()
        {
            foreach(conv; convs) foreach(kind; ParserKinds)
            {
            }

            return true;
        }

        static assert(test());
        test();
    }


    template EscapeSequence()
    {
        template build(alias kind, SrcType)
        {
            mixin MAKE_RESULT!q{ SrcType };

            static Result parse(Input!SrcType input, in Caller caller)
            {
                return combinateInputSlice!
                (
                    combinateChoice!
                    (
                        parseString!`\'`,
                        parseString!`\"`,
                        parseString!`\?`,
                        parseString!`\\`,
                        parseString!`\a`,
                        parseString!`\b`,
                        parseString!`\f`,
                        parseString!`\n`,
                        parseString!`\r`,
                        parseString!`\t`,
                        parseString!`\v`,
                        parseString!"\u0000",
                        parseString!"\u001A",
                    )
                ).build!(kind, SrcType).parse(input, caller);
            }
        }
    }

    debug(ctpg) unittest
    {
        static bool test()
        {
            foreach(conv; convs) foreach(kind; ParserKinds)
            {
            }

            return true;
        }

        static assert(test());
        test();
    }
}


auto parse(alias parser, alias kind = ParserKind!(true, true), SrcType)(SrcType src, size_t line = __LINE__ , string file = __FILE__) if(__traits(compiles, parser.build))
{
    return parser.build!(kind, SrcType).parse(Input!SrcType(src), Caller(line, file));
}

auto parse(alias parser, alias kind = ParserKind!(true, true), SrcType)(SrcType src, size_t line = __LINE__ , string file = __FILE__) if(__traits(compiles, parser!().build))
{
    return parser!().build!(kind, SrcType).parse(Input!SrcType(src), Caller(line, file));
}


string genParsers(string src, size_t line = __LINE__ , string file = __FILE__)
{
    /+
        パスの順番どうしよう？
        生成オプションの中に「スキップをメモ化」ってのがあるから、生成オプション適応を先にやると、どれがスキップだかわからなくなって困る。
            SKIPを置き換えるんじゃなくて残して、SKIPの下にスキップパーサを入れるみたいな構造なら、どれがスキップパーサか分かる。
            それなら、別にapplyMemoizeSkipを先にやる必要はなくなる
        うーん、単純にスキップをメモ化だけを単独で最初にやっちゃうって方法がいいかな
        てか、それぞれの生成オプションごとに関数を用意してやるのがいいのかも知れない
        てか、生成オプションの渡し方とかどうするんですかね・・・
        うーん、オプションもDSLの中に書いてもらおうかなぁ・・・
        結局、生成オプションごとに関数を作ることにした。オプションはDSL内に書いてもらう
        古いctpgの実装だと、リテラルはskip!(memoize!(literal))ってなってるから、
        適応の順番はskip->memoizeになる
    +/
    /+ 
        applySetSkipする前と後のSKIPは別にするべきなのかどうかみたいな話
        ・別にするべき
            ・前と後で意味合いが変わる。同じだと紛らわしい
            ・childrenにスキップパーサを追加する必要がある
        ・同じにするべき
            ・前と後で、同時に出ることはないから
            ・別にすると名前空間が汚れる
        これは、別の方がいいかも知れない
        SKIPとSKIP_WITHにした。
    +/ 
    /+

    +/
        
    auto parsed = src.parse!(defs, ParserKind!(true, true))(line, file);

    if(parsed.match)
    {
        Node code = parsed.value
            .applySkipLiteral()
            .applyMemoizeSkip(true)
            .applyMemoizeLiteral(false)
            .applyMemoizeNonterminal()
            .expandSkip()
            .removeMemoizeDuplicates()
            .removeSkipWithDuplicates()
        ;

        version(ctpgPrintGeneratedCode)
        {
            return code.generate() ~ "pragma(msg, \"\n======== " ~ file ~ "(" ~ line.to!string ~ ") =========\n\n\"q{" ~ code.toString() ~ "}\"\n\n=====================\n\n\"q{" ~ code.generate() ~ "});";
        }
        else
        {
            return code.generate();
        }
    }
    else
    {
        return "pragma(msg,\"" ~ file ~ "(" ~ (line + src[0 .. parsed.error.position].count('\n') + 1).to!string() ~ "): Error: " ~ parsed.error.msg ~ "\");static assert(false);";
    }
}

alias generateParsers = genParsers;


template checkIfExist(bool exist, string exp, size_t line, string file)
{
    static if(exist)
    {
        enum checkIfExist = exp ~ "!()";
    }
    else
    {
        pragma(msg, file ~ "(" ~ line.to!string() ~ "): Error: undefined parser " ~ exp);
        static assert(false);
    }
}


private:

enum TokenType
{
    UNDEFINED,

    // 単一トークン
    CONVERTER,
    ID,
    DOLLAR,
    TEMPLATE_INSTANCE,
    NONTERMINAL,
    RANGE_ONE_CHAR,
    RANGE_CHAR_RANGE,
    RANGE,
    STRING,

    // 再帰的なトークン
    EXCLAM,
    ANPERSAND,
    ASCIICIRCUM,
    ASTERISK,
    PLUS,
    QUESTION,
    SEQUENCE,
    LEFT_SHIFT,
    LEFT_QUESTION,
    SLASH,
    DEFINITION,
    DEFINITIONS,

    // 構文定義内で使える@トークン
    SKIP,// SET_SKIPで指定されたスキップパーサでスキップする
    SKIP_WITH, // これ自身が指定したスキップパーサでスキップする
    SET_SKIP, // スキップパーサを設定する
    MEMOIZE, // メモ化する

    SKIP_LITERAL_TRUE,
    SKIP_LITERAL_FALSE,
    MEMOIZE_SKIP_TRUE,
    MEMOIZE_SKIP_FALSE,
    MEMOIZE_LITERAL_TRUE,
    MEMOIZE_LITERAL_FALSE,
    MEMOIZE_NONTERMINAL_TRUE,
    MEMOIZE_NONTERMINAL_FALSE,

    // 構文定義外で使える@トークン
    GLOBAL_SET_SKIP,

    GLOBAL_SKIP_LITERAL_TRUE,
    GLOBAL_SKIP_LITERAL_FALSE,
    GLOBAL_MEMOIZE_SKIP_TRUE,
    GLOBAL_MEMOIZE_SKIP_FALSE,
    GLOBAL_MEMOIZE_LITERAL_TRUE,
    GLOBAL_MEMOIZE_LITERAL_FALSE,
    GLOBAL_MEMOIZE_NONTERMINAL_TRUE,
    GLOBAL_MEMOIZE_NONTERMINAL_FALSE,
}

struct Token
{
    TokenType type;
    string text_;

    string text() @property 
    {
        return text_.length == 0 ? type.to!string() : text_;
    }

    void text(string text_) @property
    {
        this.text_ = text_;
    }
}


struct Node
{
    Token token;
    Node[] children;

    size_t line;
    string file;

    string toString(string indent = "", bool last = true)
    {
        string res;
        size_t lastIndex = children.length - 1;

        res = indent ~ "+-[" ~ token.text ~ "]\n";
        foreach(i, child; children)
        {
            //if(i == children.length - 1)
            if(i == lastIndex)
            {
                res ~= child.toString(indent ~ (last ? "   " : "|  "), true);
            }
            else
            {
                res ~= child.toString(indent ~ (last ? "   " : "|  "), false);
            }
        }

        return res;
    }
}


// SKIP_LITERAL_TRUEな場所にLITERALがあったらSKIPの下に入れる
// これ、普通にchildren[n].token.typeじゃなくてnode.token.typeでswitchした方がいいな・・・
// 後で試す
// 試したら、普通にテスト通った。ただ、デフォルト引数が使えなくなった。
// auto refな引数のデフォルト値にrvalueを設定したいでござる。なぜ出来ないのか。
// ふつうにDEFINITIONSを特別扱いして、デフォルト値を復活させた。
Node applySkipLiteral(Node node, bool isSkipLiteral = true)
{
    final switch(node.token.type)
    {
        case TokenType.DOLLAR:
        case TokenType.RANGE:
        case TokenType.STRING:
            if(isSkipLiteral)
            {
                Node skipNode;
                skipNode.token.type = TokenType.SKIP;
                skipNode.children ~= node;

                node = skipNode;
            }
            break;

        case TokenType.SKIP_LITERAL_TRUE:
            node = node.children[0].applySkipLiteral(true);
            break;

        case TokenType.SKIP_LITERAL_FALSE:
            node = node.children[0].applySkipLiteral(false);
            break;


        case TokenType.DEFINITIONS:
            foreach(ref child; node.children)
            {
                switch(child.token.type)
                {
                    case TokenType.GLOBAL_SKIP_LITERAL_TRUE:
                        isSkipLiteral = true;
                        break;

                    case TokenType.GLOBAL_SKIP_LITERAL_FALSE:
                        isSkipLiteral = false;
                        break;

                    default:
                        child = child.applySkipLiteral(isSkipLiteral);
                }
            }
            break;

        case TokenType.DEFINITION:
        case TokenType.SLASH:
        case TokenType.LEFT_QUESTION:
        case TokenType.LEFT_SHIFT:
        case TokenType.SEQUENCE:
        case TokenType.QUESTION:
        case TokenType.PLUS:
        case TokenType.ASTERISK:
        case TokenType.ASCIICIRCUM:
        case TokenType.ANPERSAND:
        case TokenType.EXCLAM:

        case TokenType.SKIP:
        case TokenType.MEMOIZE:

        case TokenType.MEMOIZE_SKIP_TRUE:
        case TokenType.MEMOIZE_SKIP_FALSE:
        case TokenType.MEMOIZE_LITERAL_TRUE:
        case TokenType.MEMOIZE_LITERAL_FALSE:
        case TokenType.MEMOIZE_NONTERMINAL_TRUE:
        case TokenType.MEMOIZE_NONTERMINAL_FALSE:
            foreach(ref child; node.children)
            {
                child = child.applySkipLiteral(isSkipLiteral);
            }
            break;

        case TokenType.SKIP_WITH:
        case TokenType.SET_SKIP:
            node.children[1] = node.children[1].applySkipLiteral(isSkipLiteral);
            break;

        case TokenType.GLOBAL_SKIP_LITERAL_TRUE:
        case TokenType.GLOBAL_SKIP_LITERAL_FALSE:
            assert(false);

        case TokenType.UNDEFINED:
        case TokenType.CONVERTER:
        case TokenType.ID:
        case TokenType.TEMPLATE_INSTANCE:
        case TokenType.NONTERMINAL:
        case TokenType.RANGE_ONE_CHAR:
        case TokenType.RANGE_CHAR_RANGE:

        case TokenType.GLOBAL_SET_SKIP:

        case TokenType.GLOBAL_MEMOIZE_SKIP_TRUE:
        case TokenType.GLOBAL_MEMOIZE_SKIP_FALSE:
        case TokenType.GLOBAL_MEMOIZE_LITERAL_TRUE:
        case TokenType.GLOBAL_MEMOIZE_LITERAL_FALSE:
        case TokenType.GLOBAL_MEMOIZE_NONTERMINAL_TRUE:
        case TokenType.GLOBAL_MEMOIZE_NONTERMINAL_FALSE:
    }

    return node;
}

debug(ctpg) unittest
{
    static bool test()
    {
        assert
        (
            Node(Token(TokenType.DEFINITIONS),
            [
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.DOLLAR))
                ])
            ]).applySkipLiteral()

            ==

            Node(Token(TokenType.DEFINITIONS),
            [
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.SKIP),
                    [
                        Node(Token(TokenType.DOLLAR))
                    ])
                ])
            ])
        );

        assert
        (
            Node(Token(TokenType.DEFINITIONS),
            [
                Node(Token(TokenType.GLOBAL_SKIP_LITERAL_FALSE)),
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.DOLLAR))
                ])
            ]).applySkipLiteral()

            ==

            Node(Token(TokenType.DEFINITIONS),
            [
                Node(Token(TokenType.GLOBAL_SKIP_LITERAL_FALSE)),
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.DOLLAR))
                ])
            ])
        );

        assert
        (
            Node(Token(TokenType.DEFINITIONS),
            [
                Node(Token(TokenType.GLOBAL_SKIP_LITERAL_FALSE)),
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.SKIP_LITERAL_TRUE),
                    [
                        Node(Token(TokenType.DOLLAR))
                    ])
                ])
            ]).applySkipLiteral()

            ==

            Node(Token(TokenType.DEFINITIONS),
            [
                Node(Token(TokenType.GLOBAL_SKIP_LITERAL_FALSE)),
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.SKIP),
                    [
                        Node(Token(TokenType.DOLLAR))
                    ])
                ])
            ])
        );

        assert
        (
            Node(Token(TokenType.DEFINITIONS),
            [
                Node(Token(TokenType.GLOBAL_SKIP_LITERAL_FALSE)),
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.DOLLAR))
                ]),
                Node(Token(TokenType.GLOBAL_SKIP_LITERAL_TRUE)),
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.DOLLAR))
                ])
            ]).applySkipLiteral()

            ==

            Node(Token(TokenType.DEFINITIONS),
            [
                Node(Token(TokenType.GLOBAL_SKIP_LITERAL_FALSE)),
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.DOLLAR))
                ]),
                Node(Token(TokenType.GLOBAL_SKIP_LITERAL_TRUE)),
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.SKIP),
                    [
                        Node(Token(TokenType.DOLLAR))
                    ])
                ])
            ])
        );

        assert
        (
            Node(Token(TokenType.DEFINITIONS),
            [
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.SET_SKIP),
                    [
                        Node(Token(TokenType.DOLLAR)),
                        Node(Token(TokenType.DOLLAR))
                    ])
                ])
            ]).applySkipLiteral()

            ==

            Node(Token(TokenType.DEFINITIONS),
            [
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.SET_SKIP),
                    [
                        Node(Token(TokenType.DOLLAR)),
                        Node(Token(TokenType.SKIP),
                        [
                            Node(Token(TokenType.DOLLAR))
                        ])
                    ])
                ])
            ])
        );

        assert
        (
            Node(Token(TokenType.DEFINITIONS),
            [
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.SKIP_WITH),
                    [
                        Node(Token(TokenType.DOLLAR)),
                        Node(Token(TokenType.DOLLAR))
                    ])
                ])
            ]).applySkipLiteral()

            ==

            Node(Token(TokenType.DEFINITIONS),
            [
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.SKIP_WITH),
                    [
                        Node(Token(TokenType.DOLLAR)),
                        Node(Token(TokenType.SKIP),
                        [
                            Node(Token(TokenType.DOLLAR))
                        ])
                    ])
                ])
            ])
        );

        return true;
    }

    static assert(test());
    test();
}


// MEMOIZE_SKIP_TRUEな場所にある
// SET_SKIPやSKIP_WITHで指定されてるスキップパーサをMEMOIZEする
Node applyMemoizeSkip(Node node, bool isMemoizeSkip = true)
{
    final switch(node.token.type)
    {
        case TokenType.SET_SKIP:
        case TokenType.SKIP_WITH:
            node.children[1] = node.children[1].applyMemoizeSkip(isMemoizeSkip);
            goto case;

        case TokenType.GLOBAL_SET_SKIP:
            if(isMemoizeSkip)
            {
                Node memoizeNode;
                memoizeNode.token.type = TokenType.MEMOIZE;
                memoizeNode.children ~= node.children[0];
                node.children[0] = memoizeNode;
            }
            break;

        case TokenType.MEMOIZE_SKIP_TRUE:
            node = node.children[0].applyMemoizeSkip(true);
            break;

        case TokenType.MEMOIZE_SKIP_FALSE:
            node = node.children[0].applyMemoizeSkip(false);
            break;

        case TokenType.DEFINITIONS:
            foreach(ref child; node.children)
            {
                switch(child.token.type)
                {
                    case TokenType.GLOBAL_MEMOIZE_SKIP_TRUE:
                        isMemoizeSkip = true;
                        break;

                    case TokenType.GLOBAL_MEMOIZE_SKIP_FALSE:
                        isMemoizeSkip = false;
                        break;

                    default:
                        child = child.applyMemoizeSkip(isMemoizeSkip);
                }
            }
            break;

        case TokenType.DEFINITION:
        case TokenType.SLASH:
        case TokenType.LEFT_QUESTION:
        case TokenType.LEFT_SHIFT:
        case TokenType.SEQUENCE:
        case TokenType.QUESTION:
        case TokenType.PLUS:
        case TokenType.ASTERISK:
        case TokenType.ASCIICIRCUM:
        case TokenType.ANPERSAND:
        case TokenType.EXCLAM:

        case TokenType.SKIP:
        case TokenType.MEMOIZE:

        case TokenType.SKIP_LITERAL_TRUE:
        case TokenType.SKIP_LITERAL_FALSE:
        case TokenType.MEMOIZE_LITERAL_TRUE:
        case TokenType.MEMOIZE_LITERAL_FALSE:
        case TokenType.MEMOIZE_NONTERMINAL_TRUE:
        case TokenType.MEMOIZE_NONTERMINAL_FALSE:
            foreach(ref child; node.children)
            {
                child = child.applyMemoizeSkip(isMemoizeSkip);
            }
            break;

        case TokenType.GLOBAL_MEMOIZE_SKIP_TRUE:
        case TokenType.GLOBAL_MEMOIZE_SKIP_FALSE:
            assert(false);

        case TokenType.UNDEFINED:
        case TokenType.CONVERTER:
        case TokenType.ID:
        case TokenType.DOLLAR:
        case TokenType.TEMPLATE_INSTANCE:
        case TokenType.NONTERMINAL:
        case TokenType.RANGE_ONE_CHAR:
        case TokenType.RANGE_CHAR_RANGE:
        case TokenType.RANGE:
        case TokenType.STRING:

        case TokenType.GLOBAL_SKIP_LITERAL_TRUE:
        case TokenType.GLOBAL_SKIP_LITERAL_FALSE:
        case TokenType.GLOBAL_MEMOIZE_LITERAL_TRUE:
        case TokenType.GLOBAL_MEMOIZE_LITERAL_FALSE:
        case TokenType.GLOBAL_MEMOIZE_NONTERMINAL_TRUE:
        case TokenType.GLOBAL_MEMOIZE_NONTERMINAL_FALSE:
    }

    return node;
}

debug(ctpg) unittest
{
    static bool test()
    {
        assert
        (
            Node(Token(TokenType.DEFINITIONS), 
            [
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.SET_SKIP),
                    [
                        Node(Token(TokenType.DOLLAR)),
                        Node(Token(TokenType.DOLLAR))
                    ])
                ])
            ]).applyMemoizeSkip()

            == 

            Node(Token(TokenType.DEFINITIONS), 
            [
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.SET_SKIP),
                    [
                        Node(Token(TokenType.MEMOIZE),
                        [
                            Node(Token(TokenType.DOLLAR))
                        ]),
                        Node(Token(TokenType.DOLLAR))
                    ])
                ])
            ])
        );

        assert
        (
            Node(Token(TokenType.DEFINITIONS), 
            [
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.SET_SKIP),
                    [
                        Node(Token(TokenType.DOLLAR)),
                        Node(Token(TokenType.SET_SKIP),
                        [
                            Node(Token(TokenType.DOLLAR)),
                            Node(Token(TokenType.DOLLAR))
                        ])
                    ])
                ])
            ]).applyMemoizeSkip()

            == 

            Node(Token(TokenType.DEFINITIONS), 
            [
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.SET_SKIP),
                    [
                        Node(Token(TokenType.MEMOIZE),
                        [
                            Node(Token(TokenType.DOLLAR))
                        ]),
                        Node(Token(TokenType.SET_SKIP),
                        [
                            Node(Token(TokenType.MEMOIZE),
                            [
                                Node(Token(TokenType.DOLLAR))
                            ]),
                            Node(Token(TokenType.DOLLAR))
                        ])
                    ])
                ])
            ])
        );

        assert
        (
            Node(Token(TokenType.DEFINITIONS), 
            [
                Node(Token(TokenType.GLOBAL_MEMOIZE_SKIP_FALSE)),
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.SET_SKIP),
                    [
                        Node(Token(TokenType.DOLLAR)),
                        Node(Token(TokenType.DOLLAR))
                    ])
                ])
            ]).applyMemoizeSkip()

            == 

            Node(Token(TokenType.DEFINITIONS), 
            [
                Node(Token(TokenType.GLOBAL_MEMOIZE_SKIP_FALSE)),
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.SET_SKIP),
                    [
                        Node(Token(TokenType.DOLLAR)),
                        Node(Token(TokenType.DOLLAR))
                    ])
                ])
            ])
        );

        assert
        (
            Node(Token(TokenType.DEFINITIONS), 
            [
                Node(Token(TokenType.GLOBAL_MEMOIZE_SKIP_FALSE)),
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.MEMOIZE_SKIP_TRUE),
                    [
                        Node(Token(TokenType.SET_SKIP),
                        [
                            Node(Token(TokenType.DOLLAR)),
                            Node(Token(TokenType.DOLLAR))
                        ])
                    ])
                ])
            ]).applyMemoizeSkip()

            == 

            Node(Token(TokenType.DEFINITIONS), 
            [
                Node(Token(TokenType.GLOBAL_MEMOIZE_SKIP_FALSE)),
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.SET_SKIP),
                    [
                        Node(Token(TokenType.MEMOIZE),
                        [
                            Node(Token(TokenType.DOLLAR))
                        ]),
                        Node(Token(TokenType.DOLLAR))
                    ])
                ])
            ])
        );

        assert
        (
            Node(Token(TokenType.DEFINITIONS), 
            [
                Node(Token(TokenType.GLOBAL_MEMOIZE_SKIP_FALSE)),
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.SET_SKIP),
                    [
                        Node(Token(TokenType.DOLLAR)),
                        Node(Token(TokenType.DOLLAR))
                    ])
                ]),
                Node(Token(TokenType.GLOBAL_MEMOIZE_SKIP_TRUE)),
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.SET_SKIP),
                    [
                        Node(Token(TokenType.DOLLAR)),
                        Node(Token(TokenType.DOLLAR))
                    ])
                ]),
            ]).applyMemoizeSkip()

            == 

            Node(Token(TokenType.DEFINITIONS), 
            [
                Node(Token(TokenType.GLOBAL_MEMOIZE_SKIP_FALSE)),
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.SET_SKIP),
                    [
                        Node(Token(TokenType.DOLLAR)),
                        Node(Token(TokenType.DOLLAR))
                    ])
                ]),
                Node(Token(TokenType.GLOBAL_MEMOIZE_SKIP_TRUE)),
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.SET_SKIP),
                    [
                        Node(Token(TokenType.MEMOIZE),
                        [
                            Node(Token(TokenType.DOLLAR))
                        ]),
                        Node(Token(TokenType.DOLLAR))
                    ])
                ]),
            ])
        );
        return true;
    }

    static assert(test());
}


// MEMOIZE_LITERAL_TRUEな場所にLITERALがあったらMEMOIZEの下に入れる
Node applyMemoizeLiteral(Node node, bool isMemoizeLiteral = true)
{
    final switch(node.token.type)
    {
        case TokenType.DOLLAR:
        case TokenType.RANGE:
        case TokenType.STRING:
            if(isMemoizeLiteral)
            {
                Node memoizeNode;
                memoizeNode.token.type = TokenType.MEMOIZE;
                memoizeNode.children ~= node;

                node = memoizeNode;
            }
            break;

        case TokenType.MEMOIZE_LITERAL_TRUE:
            node = node.children[0].applyMemoizeLiteral(true);
            break;

        case TokenType.MEMOIZE_LITERAL_FALSE:
            node = node.children[0].applyMemoizeLiteral(false);
            break;

        case TokenType.DEFINITIONS:
            foreach(ref child; node.children)
            {
                switch(child.token.type)
                {
                    case TokenType.GLOBAL_MEMOIZE_LITERAL_TRUE:
                        isMemoizeLiteral = true;
                        break;

                    case TokenType.GLOBAL_MEMOIZE_LITERAL_FALSE:
                        isMemoizeLiteral = false;
                        break;

                    default:
                        child = child.applyMemoizeLiteral(isMemoizeLiteral);
                }
            }
            break;

        case TokenType.DEFINITION:
        case TokenType.SLASH:
        case TokenType.LEFT_QUESTION:
        case TokenType.LEFT_SHIFT:
        case TokenType.SEQUENCE:
        case TokenType.QUESTION:
        case TokenType.PLUS:
        case TokenType.ASTERISK:
        case TokenType.ASCIICIRCUM:
        case TokenType.ANPERSAND:
        case TokenType.EXCLAM:

        case TokenType.SKIP:
        case TokenType.SKIP_WITH:
        case TokenType.SET_SKIP:
        case TokenType.MEMOIZE:

        case TokenType.SKIP_LITERAL_TRUE:
        case TokenType.SKIP_LITERAL_FALSE:
        case TokenType.MEMOIZE_SKIP_TRUE:
        case TokenType.MEMOIZE_SKIP_FALSE:
        case TokenType.MEMOIZE_NONTERMINAL_TRUE:
        case TokenType.MEMOIZE_NONTERMINAL_FALSE:

        case TokenType.GLOBAL_SET_SKIP:
            foreach(ref child; node.children)
            {
                child = child.applyMemoizeLiteral(isMemoizeLiteral);
            }
            break;

        case TokenType.GLOBAL_MEMOIZE_LITERAL_TRUE:
        case TokenType.GLOBAL_MEMOIZE_LITERAL_FALSE:
            assert(false);

        case TokenType.UNDEFINED:
        case TokenType.CONVERTER:
        case TokenType.ID:
        case TokenType.TEMPLATE_INSTANCE:
        case TokenType.NONTERMINAL:
        case TokenType.RANGE_ONE_CHAR:
        case TokenType.RANGE_CHAR_RANGE:

        case TokenType.GLOBAL_SKIP_LITERAL_TRUE:
        case TokenType.GLOBAL_SKIP_LITERAL_FALSE:
        case TokenType.GLOBAL_MEMOIZE_SKIP_TRUE:
        case TokenType.GLOBAL_MEMOIZE_SKIP_FALSE:
        case TokenType.GLOBAL_MEMOIZE_NONTERMINAL_TRUE:
        case TokenType.GLOBAL_MEMOIZE_NONTERMINAL_FALSE:
    }

    return node;
}

debug(ctpg) unittest
{
    static bool test()
    {
        assert
        (
            Node(Token(TokenType.DEFINITIONS),
            [
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.DOLLAR))
                ])
            ]).applyMemoizeLiteral()

            ==

            Node(Token(TokenType.DEFINITIONS),
            [
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.MEMOIZE),
                    [
                        Node(Token(TokenType.DOLLAR))
                    ])
                ])
            ])
        );

        assert
        (
            Node(Token(TokenType.DEFINITIONS),
            [
                Node(Token(TokenType.GLOBAL_MEMOIZE_LITERAL_FALSE)),
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.DOLLAR))
                ])
            ]).applyMemoizeLiteral()

            ==

            Node(Token(TokenType.DEFINITIONS),
            [
                Node(Token(TokenType.GLOBAL_MEMOIZE_LITERAL_FALSE)),
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.DOLLAR))
                ])
            ])
        );

        assert
        (
            Node(Token(TokenType.DEFINITIONS),
            [
                Node(Token(TokenType.GLOBAL_MEMOIZE_LITERAL_FALSE)),
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.MEMOIZE_LITERAL_TRUE),
                    [
                        Node(Token(TokenType.DOLLAR))
                    ])
                ])
            ]).applyMemoizeLiteral()

            ==

            Node(Token(TokenType.DEFINITIONS),
            [
                Node(Token(TokenType.GLOBAL_MEMOIZE_LITERAL_FALSE)),
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.MEMOIZE),
                    [
                        Node(Token(TokenType.DOLLAR))
                    ])
                ])
            ])
        );

        assert
        (
            Node(Token(TokenType.DEFINITIONS),
            [
                Node(Token(TokenType.GLOBAL_MEMOIZE_LITERAL_FALSE)),
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.DOLLAR))
                ]),
                Node(Token(TokenType.GLOBAL_MEMOIZE_LITERAL_TRUE)),
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.DOLLAR))
                ])
            ]).applyMemoizeLiteral()

            ==

            Node(Token(TokenType.DEFINITIONS),
            [
                Node(Token(TokenType.GLOBAL_MEMOIZE_LITERAL_FALSE)),
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.DOLLAR))
                ]),
                Node(Token(TokenType.GLOBAL_MEMOIZE_LITERAL_TRUE)),
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.MEMOIZE),
                    [
                        Node(Token(TokenType.DOLLAR))
                    ])
                ])
            ])
        );

        assert
        (
            Node(Token(TokenType.DEFINITIONS),
            [
                Node(Token(TokenType.GLOBAL_SET_SKIP),
                [
                    Node(Token(TokenType.DOLLAR))
                ]),
                Node(Token(TokenType.GLOBAL_MEMOIZE_LITERAL_FALSE)),
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.DOLLAR))
                ])
            ]).applyMemoizeLiteral()

            ==

            Node(Token(TokenType.DEFINITIONS),
            [
                Node(Token(TokenType.GLOBAL_SET_SKIP),
                [
                    Node(Token(TokenType.MEMOIZE),
                    [
                        Node(Token(TokenType.DOLLAR))
                    ])
                ]),
                Node(Token(TokenType.GLOBAL_MEMOIZE_LITERAL_FALSE)),
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.DOLLAR))
                ])
            ])
        );

        return true;
    }

    static assert(test());
    test();
}


// MEMOIZE_NONTERMINAL_TRUEな場所にNONTERMINALがあったらMEMOIZEの下に入れる
Node applyMemoizeNonterminal(Node node, bool isMemoizeNonterminal = true)
{
    final switch(node.token.type)
    {
        case TokenType.NONTERMINAL:
            if(isMemoizeNonterminal)
            {
                Node memoizeNode;

                memoizeNode.token.type = TokenType.MEMOIZE;
                memoizeNode.children ~= node;

                node = memoizeNode;
            }
            break;

        case TokenType.MEMOIZE_NONTERMINAL_TRUE:
            node = node.children[0].applyMemoizeNonterminal(true);
            break;

        case TokenType.MEMOIZE_NONTERMINAL_FALSE:
            node = node.children[0].applyMemoizeNonterminal(false);
            break;

        case TokenType.DEFINITIONS:
            foreach(ref child; node.children)
            {
                switch(child.token.type)
                {
                    case TokenType.GLOBAL_MEMOIZE_NONTERMINAL_TRUE:
                        isMemoizeNonterminal = true;
                        break;

                    case TokenType.GLOBAL_MEMOIZE_NONTERMINAL_FALSE:
                        isMemoizeNonterminal = false;
                        break;

                    default:
                        child = child.applyMemoizeNonterminal(isMemoizeNonterminal);
                }
            }
            break;

        case TokenType.DEFINITION:
        case TokenType.SLASH:
        case TokenType.LEFT_QUESTION:
        case TokenType.LEFT_SHIFT:
        case TokenType.SEQUENCE:
        case TokenType.QUESTION:
        case TokenType.PLUS:
        case TokenType.ASTERISK:
        case TokenType.ASCIICIRCUM:
        case TokenType.ANPERSAND:
        case TokenType.EXCLAM:

        case TokenType.SKIP:
        case TokenType.SKIP_WITH:
        case TokenType.SET_SKIP:
        case TokenType.MEMOIZE:

        case TokenType.SKIP_LITERAL_TRUE:
        case TokenType.SKIP_LITERAL_FALSE:
        case TokenType.MEMOIZE_SKIP_TRUE:
        case TokenType.MEMOIZE_SKIP_FALSE:
        case TokenType.MEMOIZE_LITERAL_TRUE:
        case TokenType.MEMOIZE_LITERAL_FALSE:

        case TokenType.GLOBAL_SET_SKIP:
            foreach(ref child; node.children)
            {
                child = child.applyMemoizeNonterminal(isMemoizeNonterminal);
            }
            break;

        case TokenType.GLOBAL_MEMOIZE_NONTERMINAL_TRUE:
        case TokenType.GLOBAL_MEMOIZE_NONTERMINAL_FALSE:
            assert(false);

        case TokenType.UNDEFINED:
        case TokenType.CONVERTER:
        case TokenType.ID:
        case TokenType.DOLLAR:
        case TokenType.TEMPLATE_INSTANCE:
        case TokenType.RANGE_ONE_CHAR:
        case TokenType.RANGE_CHAR_RANGE:
        case TokenType.RANGE:
        case TokenType.STRING:

        case TokenType.GLOBAL_SKIP_LITERAL_TRUE:
        case TokenType.GLOBAL_SKIP_LITERAL_FALSE:
        case TokenType.GLOBAL_MEMOIZE_SKIP_TRUE:
        case TokenType.GLOBAL_MEMOIZE_SKIP_FALSE:
        case TokenType.GLOBAL_MEMOIZE_LITERAL_TRUE:
        case TokenType.GLOBAL_MEMOIZE_LITERAL_FALSE:
    }

    return node;
}

debug(ctpg) unittest
{
    bool test()
    {
        assert
        (
            Node(Token(TokenType.DEFINITIONS),
            [
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.NONTERMINAL))
                ])
            ]).applyMemoizeNonterminal()

            ==

            Node(Token(TokenType.DEFINITIONS),
            [
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.MEMOIZE),
                    [
                        Node(Token(TokenType.NONTERMINAL))
                    ])
                ])
            ])
        );

        assert
        (
            Node(Token(TokenType.DEFINITIONS),
            [
                Node(Token(TokenType.GLOBAL_MEMOIZE_NONTERMINAL_FALSE)),
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.NONTERMINAL))
                ])
            ]).applyMemoizeNonterminal()

            ==

            Node(Token(TokenType.DEFINITIONS),
            [
                Node(Token(TokenType.GLOBAL_MEMOIZE_NONTERMINAL_FALSE)),
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.NONTERMINAL))
                ])
            ])
        );

        assert
        (
            Node(Token(TokenType.DEFINITIONS),
            [
                Node(Token(TokenType.GLOBAL_MEMOIZE_NONTERMINAL_FALSE)),
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.MEMOIZE_NONTERMINAL_TRUE),
                    [
                        Node(Token(TokenType.NONTERMINAL))
                    ])
                ])
            ]).applyMemoizeNonterminal()

            ==

            Node(Token(TokenType.DEFINITIONS),
            [
                Node(Token(TokenType.GLOBAL_MEMOIZE_NONTERMINAL_FALSE)),
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.MEMOIZE),
                    [
                        Node(Token(TokenType.NONTERMINAL))
                    ])
                ])
            ])
        );

        assert
        (
            Node(Token(TokenType.DEFINITIONS),
            [
                Node(Token(TokenType.GLOBAL_MEMOIZE_NONTERMINAL_FALSE)),
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.NONTERMINAL))
                ]),
                Node(Token(TokenType.GLOBAL_MEMOIZE_NONTERMINAL_TRUE)),
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.NONTERMINAL))
                ])
            ]).applyMemoizeNonterminal()

            ==

            Node(Token(TokenType.DEFINITIONS),
            [
                Node(Token(TokenType.GLOBAL_MEMOIZE_NONTERMINAL_FALSE)),
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.NONTERMINAL))
                ]),
                Node(Token(TokenType.GLOBAL_MEMOIZE_NONTERMINAL_TRUE)),
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.MEMOIZE),
                    [
                        Node(Token(TokenType.NONTERMINAL))
                    ])
                ])
            ])
        );

        assert
        (
            Node(Token(TokenType.DEFINITIONS),
            [
                Node(Token(TokenType.GLOBAL_SET_SKIP),
                [
                    Node(Token(TokenType.NONTERMINAL))
                ]),
                Node(Token(TokenType.GLOBAL_MEMOIZE_NONTERMINAL_FALSE)),
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.NONTERMINAL))
                ])
            ]).applyMemoizeNonterminal()

            ==

            Node(Token(TokenType.DEFINITIONS),
            [
                Node(Token(TokenType.GLOBAL_SET_SKIP),
                [
                    Node(Token(TokenType.MEMOIZE),
                    [
                        Node(Token(TokenType.NONTERMINAL))
                    ])
                ]),
                Node(Token(TokenType.GLOBAL_MEMOIZE_NONTERMINAL_FALSE)),
                Node(Token(TokenType.DEFINITION),
                [
                    Node(Token(TokenType.TEMPLATE_INSTANCE)),
                    Node(Token(TokenType.ID)),
                    Node(Token(TokenType.NONTERMINAL))
                ])
            ])
        );

        return true;
    }

    static assert(test());
    test();
}


// SET_SKIPで指定されたスキップパーサでSKIPをSKIP_WITHに置換する
Node expandSkip(Node node, Node skip = Node.init)
{
    final switch(node.token.type)
    {
        case TokenType.SKIP:
            if(skip.token.type != TokenType.UNDEFINED)
            {
                Node skipWithNode;

                skipWithNode.token.type = TokenType.SKIP_WITH;
                skipWithNode.children ~= skip;
                skipWithNode.children ~= node.children[0];

                node = skipWithNode;
            }
            else
            {
                node = node.children[0];
            }
            break;

        case TokenType.SET_SKIP:
            node = node.children[1].expandSkip(node.children[0]);
            break;

        case TokenType.SKIP_WITH:
            node.children[1] = node.children[1].expandSkip(skip);
            break;

        case TokenType.DEFINITIONS:
            foreach(ref child; node.children)
            {
                switch(child.token.type)
                {
                    case TokenType.GLOBAL_SET_SKIP:
                        skip = child.children[0];
                        break;

                    default:
                        child = child.expandSkip(skip);
                }
            }
            break;

        case TokenType.DEFINITION:
        case TokenType.SLASH:
        case TokenType.LEFT_QUESTION:
        case TokenType.LEFT_SHIFT:
        case TokenType.SEQUENCE:
        case TokenType.QUESTION:
        case TokenType.PLUS:
        case TokenType.ASTERISK:
        case TokenType.ASCIICIRCUM:
        case TokenType.ANPERSAND:
        case TokenType.EXCLAM:

        case TokenType.MEMOIZE:

        case TokenType.SKIP_LITERAL_TRUE:
        case TokenType.SKIP_LITERAL_FALSE:
        case TokenType.MEMOIZE_SKIP_TRUE:
        case TokenType.MEMOIZE_SKIP_FALSE:
        case TokenType.MEMOIZE_LITERAL_TRUE:
        case TokenType.MEMOIZE_LITERAL_FALSE:
        case TokenType.MEMOIZE_NONTERMINAL_TRUE:
        case TokenType.MEMOIZE_NONTERMINAL_FALSE:
            foreach(ref child; node.children)
            {
                child = child.expandSkip(skip);
            }
            break;

        case TokenType.UNDEFINED:
        case TokenType.GLOBAL_SET_SKIP:
            assert(false);

        case TokenType.CONVERTER:
        case TokenType.ID:
        case TokenType.DOLLAR:
        case TokenType.TEMPLATE_INSTANCE:
        case TokenType.NONTERMINAL:
        case TokenType.RANGE_ONE_CHAR:
        case TokenType.RANGE_CHAR_RANGE:
        case TokenType.RANGE:
        case TokenType.STRING:

        case TokenType.GLOBAL_SKIP_LITERAL_TRUE:
        case TokenType.GLOBAL_SKIP_LITERAL_FALSE:
        case TokenType.GLOBAL_MEMOIZE_SKIP_TRUE:
        case TokenType.GLOBAL_MEMOIZE_SKIP_FALSE:
        case TokenType.GLOBAL_MEMOIZE_LITERAL_TRUE:
        case TokenType.GLOBAL_MEMOIZE_LITERAL_FALSE:
        case TokenType.GLOBAL_MEMOIZE_NONTERMINAL_TRUE:
        case TokenType.GLOBAL_MEMOIZE_NONTERMINAL_FALSE:
    }

    return node;
}

debug(ctpg) unittest
{
    bool test()
    {
        with(TokenType)
        {
            // GLOBAL_SET_SKIPが動く
            assert (
                Node(Token(DEFINITIONS),
                [
                    Node(Token(GLOBAL_SET_SKIP),
                    [
                        Node(Token(STRING))
                    ]),
                    Node(Token(DEFINITION),
                    [
                        Node(Token(TEMPLATE_INSTANCE)),
                        Node(Token(ID)),
                        Node(Token(SKIP),
                        [
                            Node(Token(DOLLAR))
                        ])
                    ])
                ]).expandSkip()

                == 

                Node(Token(DEFINITIONS),
                [
                    Node(Token(GLOBAL_SET_SKIP),
                    [
                        Node(Token(STRING))
                    ]),
                    Node(Token(DEFINITION),
                    [
                        Node(Token(TEMPLATE_INSTANCE)),
                        Node(Token(ID)),
                        Node(Token(SKIP_WITH),
                        [
                            Node(Token(STRING)),
                            Node(Token(DOLLAR))
                        ])
                    ])
                ])
            );

            // 最も近いGLOBAL_SET_SKIPが優先される
            assert (
                Node(Token(DEFINITIONS),
                [
                    Node(Token(GLOBAL_SET_SKIP),
                    [
                        Node(Token(STRING, "1"))
                    ]),
                    Node(Token(DEFINITION),
                    [
                        Node(Token(TEMPLATE_INSTANCE)),
                        Node(Token(ID)),
                        Node(Token(SKIP),
                        [
                            Node(Token(DOLLAR))
                        ])
                    ]),
                    Node(Token(GLOBAL_SET_SKIP),
                    [
                        Node(Token(STRING, "2"))
                    ]),
                    Node(Token(DEFINITION),
                    [
                        Node(Token(TEMPLATE_INSTANCE)),
                        Node(Token(ID)),
                        Node(Token(SKIP),
                        [
                            Node(Token(DOLLAR))
                        ])
                    ])
                ]).expandSkip()

                == 

                Node(Token(DEFINITIONS),
                [
                    Node(Token(GLOBAL_SET_SKIP),
                    [
                        Node(Token(STRING, "1"))
                    ]),
                    Node(Token(DEFINITION),
                    [
                        Node(Token(TEMPLATE_INSTANCE)),
                        Node(Token(ID)),
                        Node(Token(SKIP_WITH),
                        [
                            Node(Token(STRING, "1")),
                            Node(Token(DOLLAR))
                        ])
                    ]),
                    Node(Token(GLOBAL_SET_SKIP),
                    [
                        Node(Token(STRING, "2"))
                    ]),
                    Node(Token(DEFINITION),
                    [
                        Node(Token(TEMPLATE_INSTANCE)),
                        Node(Token(ID)),
                        Node(Token(SKIP_WITH),
                        [
                            Node(Token(STRING, "2")),
                            Node(Token(DOLLAR))
                        ])
                    ])
                ])
            );

            // SET_SKIPが動く
            assert (
                Node(Token(DEFINITIONS),
                [
                    Node(Token(DEFINITION),
                    [
                        Node(Token(TEMPLATE_INSTANCE)),
                        Node(Token(ID)),
                        Node(Token(SET_SKIP),
                        [
                            Node(Token(STRING)),
                            Node(Token(SKIP),
                            [
                                Node(Token(DOLLAR))
                            ])
                        ])
                    ])
                ]).expandSkip()

                == 

                Node(Token(DEFINITIONS),
                [
                    Node(Token(DEFINITION),
                    [
                        Node(Token(TEMPLATE_INSTANCE)),
                        Node(Token(ID)),
                        Node(Token(SKIP_WITH),
                        [
                            Node(Token(STRING)),
                            Node(Token(DOLLAR))
                        ])
                    ])
                ])
            );

            // 最も近いSET_SKIPが優先される
            assert (
                Node(Token(DEFINITIONS),
                [
                    Node(Token(DEFINITION),
                    [
                        Node(Token(TEMPLATE_INSTANCE)),
                        Node(Token(ID)),
                        Node(Token(SET_SKIP),
                        [
                            Node(Token(STRING, "1")),
                            Node(Token(SEQUENCE),
                            [
                                Node(Token(SKIP),
                                [
                                    Node(Token(DOLLAR))
                                ]),
                                Node(Token(SET_SKIP),
                                [
                                    Node(Token(STRING, "2")),
                                    Node(Token(SKIP),
                                    [
                                        Node(Token(DOLLAR))
                                    ])
                                ])
                            ]),
                        ])
                    ])
                ]).expandSkip()

                == 

                Node(Token(DEFINITIONS),
                [
                    Node(Token(DEFINITION),
                    [
                        Node(Token(TEMPLATE_INSTANCE)),
                        Node(Token(ID)),
                        Node(Token(SEQUENCE),
                        [
                            Node(Token(SKIP_WITH),
                            [
                                Node(Token(STRING, "1")),
                                Node(Token(DOLLAR))
                            ]),
                            Node(Token(SKIP_WITH),
                            [
                                Node(Token(STRING, "2")),
                                Node(Token(DOLLAR))
                            ])
                        ])
                    ])
                ])
            );

            // GLOBAL_SET_SKIPよりもSET_SKIPが優先される
            assert (
                Node(Token(DEFINITIONS),
                [
                    Node(Token(GLOBAL_SET_SKIP),
                    [
                        Node(Token(STRING, "global"))
                    ]),
                    Node(Token(DEFINITION),
                    [
                        Node(Token(TEMPLATE_INSTANCE)),
                        Node(Token(ID)),
                        Node(Token(SET_SKIP),
                        [
                            Node(Token(STRING, "local")),
                            Node(Token(SKIP),
                            [
                                Node(Token(DOLLAR))
                            ])
                        ])
                    ])
                ]).expandSkip()

                == 

                Node(Token(DEFINITIONS),
                [
                    Node(Token(GLOBAL_SET_SKIP),
                    [
                        Node(Token(STRING, "global"))
                    ]),
                    Node(Token(DEFINITION),
                    [
                        Node(Token(TEMPLATE_INSTANCE)),
                        Node(Token(ID)),
                        Node(Token(SKIP_WITH),
                        [
                            Node(Token(STRING, "local")),
                            Node(Token(DOLLAR))
                        ])
                    ])
                ])
            );

        }
        return true;
    }

    static assert(test());
    test();
}


// MEMOIZEの重複を消す
Node removeMemoizeDuplicates(Node node)
{
    final switch(node.token.type) with(TokenType)
    {
        case MEMOIZE:
            if(node.children[0].token.type == MEMOIZE)
            {
                node = node.children[0].removeMemoizeDuplicates();
            }
            break;

        case DEFINITIONS:
        case DEFINITION:
        case SLASH:
        case LEFT_QUESTION:
        case LEFT_SHIFT:
        case SEQUENCE:
        case QUESTION:
        case PLUS:
        case ASTERISK:
        case ASCIICIRCUM:
        case ANPERSAND:
        case EXCLAM:

        case SKIP:
        case SET_SKIP:
        case SKIP_WITH:

        case SKIP_LITERAL_TRUE:
        case SKIP_LITERAL_FALSE:
        case MEMOIZE_SKIP_TRUE:
        case MEMOIZE_SKIP_FALSE:
        case MEMOIZE_LITERAL_TRUE:
        case MEMOIZE_LITERAL_FALSE:
        case MEMOIZE_NONTERMINAL_TRUE:
        case MEMOIZE_NONTERMINAL_FALSE:

        case TokenType.GLOBAL_SET_SKIP:
            foreach(ref child; node.children)
            {
                child = child.removeMemoizeDuplicates();
            }
            break;

        case UNDEFINED:
        case CONVERTER:
        case ID:
        case DOLLAR:
        case TEMPLATE_INSTANCE:
        case NONTERMINAL:
        case RANGE_ONE_CHAR:
        case RANGE_CHAR_RANGE:
        case RANGE:
        case STRING:

        case GLOBAL_SKIP_LITERAL_TRUE:
        case GLOBAL_SKIP_LITERAL_FALSE:
        case GLOBAL_MEMOIZE_SKIP_TRUE:
        case GLOBAL_MEMOIZE_SKIP_FALSE:
        case GLOBAL_MEMOIZE_LITERAL_TRUE:
        case GLOBAL_MEMOIZE_LITERAL_FALSE:
        case GLOBAL_MEMOIZE_NONTERMINAL_TRUE:
        case GLOBAL_MEMOIZE_NONTERMINAL_FALSE:
    }
    return node;
}

debug(ctpg) unittest
{
    bool test()
    {
        with(TokenType)
        {
            // MEMOIZEの重複が消される
            assert (
                Node(Token(MEMOIZE),
                [
                    Node(Token(MEMOIZE),
                    [
                        Node(Token(STRING))
                    ])
                ]).removeMemoizeDuplicates()

                == 

                Node(Token(MEMOIZE),
                [
                    Node(Token(STRING))
                ])
            );

            // スキップパーサ内のMEMOIZEが消される
            assert (
                Node(Token(SKIP_WITH),
                [
                    Node(Token(MEMOIZE),
                    [
                        Node(Token(MEMOIZE),
                        [
                            Node(Token(STRING))
                        ])
                    ]),
                    Node(Token(STRING))
                ]).removeMemoizeDuplicates()

                == 

                Node(Token(SKIP_WITH),
                [
                    Node(Token(MEMOIZE),
                    [
                        Node(Token(STRING))
                    ]),
                    Node(Token(STRING))
                ])
            );
        }
        return true;
    }

    static assert(test());
    test();
}


// SKIP_WITHの重複を消す
Node removeSkipWithDuplicates(Node node)
{
    final switch(node.token.type) with(TokenType)
    {
        case SKIP_WITH:
            if(node.children[1].token.type == SKIP_WITH && node.children[0] == node.children[1].children[0])
            {
                node = node.children[1].removeSkipWithDuplicates();
            }
            break;

        case DEFINITIONS:
        case DEFINITION:
        case SLASH:
        case LEFT_QUESTION:
        case LEFT_SHIFT:
        case SEQUENCE:
        case QUESTION:
        case PLUS:
        case ASTERISK:
        case ASCIICIRCUM:
        case ANPERSAND:
        case EXCLAM:

        case SKIP:
        case SET_SKIP:
        case MEMOIZE:

        case SKIP_LITERAL_TRUE:
        case SKIP_LITERAL_FALSE:
        case MEMOIZE_SKIP_TRUE:
        case MEMOIZE_SKIP_FALSE:
        case MEMOIZE_LITERAL_TRUE:
        case MEMOIZE_LITERAL_FALSE:
        case MEMOIZE_NONTERMINAL_TRUE:
        case MEMOIZE_NONTERMINAL_FALSE:

        case TokenType.GLOBAL_SET_SKIP:
            foreach(ref child; node.children)
            {
                child = child.removeSkipWithDuplicates();
            }
            break;

        case UNDEFINED:
        case CONVERTER:
        case ID:
        case DOLLAR:
        case TEMPLATE_INSTANCE:
        case NONTERMINAL:
        case RANGE_ONE_CHAR:
        case RANGE_CHAR_RANGE:
        case RANGE:
        case STRING:

        case GLOBAL_SKIP_LITERAL_TRUE:
        case GLOBAL_SKIP_LITERAL_FALSE:
        case GLOBAL_MEMOIZE_SKIP_TRUE:
        case GLOBAL_MEMOIZE_SKIP_FALSE:
        case GLOBAL_MEMOIZE_LITERAL_TRUE:
        case GLOBAL_MEMOIZE_LITERAL_FALSE:
        case GLOBAL_MEMOIZE_NONTERMINAL_TRUE:
        case GLOBAL_MEMOIZE_NONTERMINAL_FALSE:
    }
    return node;
}

debug(ctpg) unittest
{
    bool test()
    {
        with(TokenType)
        {
            // スキップパーサが等しいSKIP_WITHの重複が消される
            assert (
                Node(Token(SKIP_WITH),
                [
                    Node(Token(STRING)),
                    Node(Token(SKIP_WITH),
                    [
                        Node(Token(STRING)),
                        Node(Token(DOLLAR))
                    ])
                ]).removeSkipWithDuplicates()

                == 

                Node(Token(SKIP_WITH),
                [
                    Node(Token(STRING)),
                    Node(Token(DOLLAR))
                ])
            );

            // スキップパーサが等しくないSKIP_WITHの重複は消されない
            assert (
                Node(Token(SKIP_WITH),
                [
                    Node(Token(STRING, "a")),
                    Node(Token(SKIP_WITH),
                    [
                        Node(Token(STRING, "b")),
                        Node(Token(DOLLAR))
                    ])
                ]).removeSkipWithDuplicates()

                == 

                Node(Token(SKIP_WITH),
                [
                    Node(Token(STRING, "a")),
                    Node(Token(SKIP_WITH),
                    [
                        Node(Token(STRING, "b")),
                        Node(Token(DOLLAR))
                    ])
                ])
            );
        }
        return true;
    }

    static assert(test());
    test();
}


// NodeからmixinされるD言語のコードを生成する
string generate(Node node)
{
    string code;

    final switch(node.token.type)
    {
        case TokenType.DEFINITIONS:
            foreach(child; node.children)
            {
                if(child.token.type == TokenType.DEFINITION)
                {
                    code ~= child.generate();
                }
            }
            break;

        case TokenType.DEFINITION:
            code =
            "template " ~ node.children[1].token.text ~ "()"
            "{"
                "template build(alias kind, SrcType)"
                "{"
                    "static if(kind.hasValue)"
                    "{"
                        "#line " ~ node.children[0].line.to!string() ~ "\n"
                        "alias Result = ParseResult!(kind, SrcType, " ~ node.children[0].token.text ~ ");"
                    "}"
                    "else"
                    "{"
                        "alias Result = ParseResult!(kind, SrcType);"
                    "}"
                    "static Result parse(Input!SrcType input, in Caller caller)"
                    "{"
                        "static if(!is(typeof(" ~ node.children[2].generate() ~ ".build!(kind, SrcType).parse(input, caller)) : Result))"
                        "{"
                            "pragma(msg, `" ~ node.children[1].file ~ "(" ~ node.children[1].line.to!string() ~ "): '" ~ node.children[1].token.text ~ "' should return '" ~ node.children[0].token.text ~ "', not '` ~ getParseResultType!(" ~ node.children[2].generate() ~ ".build!(kind, SrcType)).stringof ~ `'`);"
                            "static assert(false);"
                        "}"
                        "return " ~ node.children[2].generate() ~ ".build!(kind, SrcType).parse(input, caller);"
                    "}"
                "}"
            "}";
            break;

        case TokenType.SLASH:
            foreach(child; node.children)
            {
                code ~= child.generate() ~ ",";
            }
            code = "combinateChoice!(" ~ code ~ ")";
            break;

        case TokenType.LEFT_SHIFT:
            code = "combinateConvert!(" ~ node.children[0].generate() ~ ",#line " ~ node.children[1].line.to!string() ~ "\n" ~ node.children[1].token.text ~ "," ~ node.line.to!string() ~ ",`" ~ node.file ~ "`)";
            break;

        case TokenType.LEFT_QUESTION:
            code = "combinateCheck!(" ~ node.children[0].generate() ~ ",#line " ~ node.children[1].line.to!string() ~ "\n" ~ node.children[1].token.text ~ "," ~ node.line.to!string() ~ ",`" ~ node.file ~ "`)";
            break;

        case TokenType.SEQUENCE:
            foreach(child; node.children)
            {
                code ~= child.generate() ~ ",";
            }
            code = "combinateUnTuple!(combinateSequence!(" ~ code ~ "))";
            break;

        case TokenType.QUESTION:
            code = "combinateOption!(" ~ node.children[0].generate() ~ ")";
            break;

        case TokenType.ASTERISK:
            if(node.children.length == 2)
            {
                code = "combinateMore0!(" ~ node.children[0].generate() ~ "," ~ node.children[1].generate() ~ ")";
            }
            else
            {
                code = "combinateMore0!(" ~ node.children[0].generate() ~ ")";
            }
            break;

        case TokenType.PLUS:
            if(node.children.length == 2)
            {
                code = "combinateMore1!(" ~ node.children[0].generate() ~ "," ~ node.children[1].generate() ~ ")";
            }
            else
            {
                code = "combinateMore1!(" ~ node.children[0].generate() ~ ")";
            }
            break;

        case TokenType.EXCLAM:
            code = "combinateNone!(" ~ node.children[0].generate() ~ ")";
            break;

        case TokenType.ANPERSAND:
            code = "combinateAnd!(" ~ node.children[0].generate() ~ ")";
            break;

        case TokenType.ASCIICIRCUM:
            code = "combinateNot!(" ~ node.children[0].generate() ~ ")";
            break;

        case TokenType.SKIP_WITH:
            code = "combinateSkip!(" ~ node.children[0].generate() ~ "," ~ node.children[1].generate() ~ ")";
            break;

        case TokenType.MEMOIZE:
            code = "combinateMemoize!(" ~ node.children[0].generate() ~ ")";
            break;

        case TokenType.DOLLAR:
            code = "parseEOF!()";
            break;

        case TokenType.RANGE:
            switch(node.children[0].token.type)
            {
                case TokenType.RANGE_CHAR_RANGE:
                    code = "parseCharRange!('" ~ node.children[0].children[0].token.text ~ "','" ~ node.children[0].children[1].token.text ~ "')";
                    break;

                case TokenType.RANGE_ONE_CHAR:
                    code = "parseCharRange!('" ~ node.children[0].token.text ~ "','" ~ node.children[0].token.text ~ "')";
                    break;

                default: assert(false);
            }
            break;

        case TokenType.STRING:
            code = "parseString!(" ~ node.token.text ~ ")";
            break;

        case TokenType.NONTERMINAL:
            code = "mixin(checkIfExist!(is(typeof(" ~ node.token.text ~ ")), \"" ~ node.token.text ~ "\", " ~ node.line.to!string() ~ ", \"" ~ node.file ~ "\"))";
            break;

        case TokenType.UNDEFINED:
        case TokenType.CONVERTER:
        case TokenType.ID:
        case TokenType.TEMPLATE_INSTANCE:
        case TokenType.RANGE_ONE_CHAR:
        case TokenType.RANGE_CHAR_RANGE:

        case TokenType.SKIP:
        case TokenType.SET_SKIP:

        case TokenType.MEMOIZE_SKIP_TRUE:
        case TokenType.MEMOIZE_SKIP_FALSE:
        case TokenType.SKIP_LITERAL_TRUE:
        case TokenType.SKIP_LITERAL_FALSE:
        case TokenType.MEMOIZE_LITERAL_TRUE:
        case TokenType.MEMOIZE_LITERAL_FALSE:
        case TokenType.MEMOIZE_NONTERMINAL_TRUE:
        case TokenType.MEMOIZE_NONTERMINAL_FALSE:

        case TokenType.GLOBAL_SET_SKIP:

        case TokenType.GLOBAL_SKIP_LITERAL_TRUE:
        case TokenType.GLOBAL_SKIP_LITERAL_FALSE:
        case TokenType.GLOBAL_MEMOIZE_SKIP_TRUE:
        case TokenType.GLOBAL_MEMOIZE_SKIP_FALSE:
        case TokenType.GLOBAL_MEMOIZE_LITERAL_TRUE:
        case TokenType.GLOBAL_MEMOIZE_LITERAL_FALSE:
        case TokenType.GLOBAL_MEMOIZE_NONTERMINAL_TRUE:
        case TokenType.GLOBAL_MEMOIZE_NONTERMINAL_FALSE:
            assert(false);
    }

    return code;
}


// 自動でnodeのlineとfileをセットするようにするコンビネータ
template combinateSetInfo(alias parser)
{
    template build(alias kind, SrcType)
    {
        static if(is(getParseResultType!(parser.build!(kind, SrcType)) == Node))
        {
            mixin MAKE_RESULT!q{ Node };

            Result parse(Input!SrcType input, in Caller caller)
            {
                return combinateConvert!
                (
                    combinateSequence!
                    (
                        parseGetLine!(),
                        parseGetCallerLine!(),
                        parseGetCallerFile!(),
                        parser
                    ),
                    (size_t line, size_t callerLine, string callerFile, Node node)
                    {
                        node.line = callerLine + line + 1;
                        node.file = callerFile;

                        return node;
                    }
                ).build!(kind, SrcType).parse(input, caller);
            }
        }
        else
        {
            static assert(false);
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        with(parse!(combinateSetInfo!(TestParser!(Node())), ParserKind!(true, true))(""))
        {
            assert(match == true);
            assert(value.line == __LINE__ - 2);
            assert(value.file == __FILE__);
        }

        return true;
    }

    static assert(test());
    test();
}


// パーサが返した文字列と、引数のtokenTypeを使ってNodeを作るコンビネータ
template combinateMakeNode(alias parser, TokenType tokenType)
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinateSetInfo!
            (
                combinateConvert!
                (
                    parser,
                    (string token) => Node(Token(tokenType, token))
                )
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}


// 一行コメントを消費するパーサ
template lineComment()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ None };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinateNone!
            (
                combinateSequence!
                (
                    parseString!"//",
                    combinateMore0!
                    (
                        combinateSequence!
                        (
                            combinateNotPred!
                            (
                                parseString!"\n"
                            ),
                            parseAnyChar!()
                        )
                    ),
                    parseString!"\n"
                )
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        with(parse!(lineComment!(), ParserKind!(true, true))("// comment\nnot comment"))
        {
            assert(match              == true);
            assert(nextInput.source   == "not comment");
        }

        with(parse!(lineComment!(), ParserKind!(true, true))("// not terminated comment"))
        {
            assert(match          == false);
            assert(error.position == 25);
            assert(error.msg      == "'\n' expected");
        }

        return true;
    }

    static assert(test());
    test();
}


// 普通のコメントを消費するパーサ
template ordinaryComment()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ None };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinateNone!
            (
                combinateSequence!
                (
                    parseString!"/*",
                    combinateMore0!
                    (
                        combinateSequence!
                        (
                            combinateNotPred!
                            (
                                parseString!"*/"
                            ),
                            parseAnyChar!()
                        )
                    ),
                    parseString!"*/"
                )
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        with(parse!(ordinaryComment!(), ParserKind!(true, true))("/* comment */not comment"))
        {
            assert(match              == true);
            assert(nextInput.source   == "not comment");
        }

        with(parse!(ordinaryComment!(), ParserKind!(true, true))("/* not terminated comment"))
        {
            assert(match          == false);
            assert(error.position == 25);
            assert(error.msg      == "'*/' expected");
        }

        return true;
    }

    static assert(test());
    test();
}


// ネストされたコメントを消費するパーサ
template nestedComment()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ None };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinateNone!
            (
                combinateSequence!
                (
                    parseString!"/+",
                    combinateMore0!
                    (
                        combinateChoice!
                        (
                            nestedComment!(),
                            combinateSequence!
                            (
                                combinateNotPred!
                                (
                                    parseString!"+/"
                                ),
                                parseAnyChar!()
                            )
                        )
                    ),
                    parseString!"+/"
                )
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        with(parse!(nestedComment!(), ParserKind!(true, true))("/+ comment +/not comment"))
        {
            assert(match              == true);
            assert(nextInput.source   == "not comment");
        }

        with(parse!(nestedComment!(), ParserKind!(true, true))("/+ comment  /+ inner comment +/ comment +/not comment"))
        {
            assert(match              == true);
            assert(nextInput.source   == "not comment");
        }

        with(parse!(nestedComment!(), ParserKind!(true, true))("/+ not terminated comment"))
        {
            assert(match          == false);
            assert(error.position == 25);
            assert(error.msg      == "'+/' expected");
        }

        return true;
    }

    static assert(test());
    test();
}


// スキップされるべき空白を消費するパーサ
template spaces()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ None };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinateNone!
            (
                combinateMore0!
                (
                    combinateChoice!
                    (
                        parseString!" ",
                        parseString!"\n",
                        parseString!"\t",
                        parseString!"\r",
                        parseString!"\f",
                        lineComment!(),
                        ordinaryComment!(),
                        nestedComment!()
                    )
                )
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        with(parse!(spaces!(), ParserKind!(true, true))("/* a */// b \nc"))
        {
            assert(match              == true);
            assert(nextInput.source   == "c");
        }

        with(parse!(spaces!(), ParserKind!(true, true))("0/* a */// b \nc"))
        {
            assert(match              == true);
            assert(nextInput.source   == "0/* a */// b \nc");
        }

        return true;
    }

    static assert(test());
    test();
}


template arch(string open, string close)
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ string };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinateInputSlice!
            (
                combinateSequence!
                (
                    parseString!open,
                    combinateMore0!
                    (
                        combinateChoice!
                        (
                            arch!(open, close),
                            combinateSequence!
                            (
                                combinateNotPred!
                                (
                                    parseString!close
                                ),
                                combinateChoice!
                                (
                                    DLex.StringLiteral!(),
                                    parseCharRange!(dchar.min, dchar.max)
                                )
                            )
                        )
                    ),
                    parseString!close
                )
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        with(parse!(arch!("(", ")"), ParserKind!(true, true))("((a(b)c)d(e))f"))
        {
            assert(match              == true);
            assert(nextInput.source   == "f");
            assert(value              == "((a(b)c)d(e))");
        }

        with(parse!(arch!("(", ")"), ParserKind!(true, true))("((a(b)c)d(e)"))
        {
            assert(match          == false);
            assert(error.position == 12);
            assert(error.msg      == "')' expected");
        }

        return true;
    }

    static assert(test());
    test();
}


template func()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinateMakeNode!
            (
                combinateInputSlice!
                (
                    combinateSequence!
                    (
                        combinateOption!
                        (
                            arch!("(", ")")
                        ),
                        arch!("{", "}")
                    )
                ),
                TokenType.CONVERTER
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        with(parse!(func!(), ParserKind!(true, true))(q"<(a, b, c){ return "{}" ~ r"{}" ~ `{}` ~ a ~ b ~ c; }>"))
        {
            assert(match                 == true);
            assert(value.token.type            == TokenType.CONVERTER);
            assert(value.token.text           == q"<(a, b, c){ return "{}" ~ r"{}" ~ `{}` ~ a ~ b ~ c; }>");
            assert(value.children.length == 0);
        }

        with(parse!(func!(), ParserKind!(true, true))(q"<(a, b, c{ return "{}" ~ r"{}" ~ `{}` ~ a ~ b ~ c; }>"))
        {
            assert(match == false);
            assert(error.msg == "')' expected");
            assert(error.position == 51);
        }

        with(parse!(func!(), ParserKind!(true, true))(q"<(a, b, c){ return "{}" ~ r"{}" ~ `{}` ~ a ~ b ~ c; >"))
        {
            assert(match == false);
            assert(error.msg == "'}' expected");
            assert(error.position == 51);
        }

        return true;
    }

    static assert(test());
    test();
}


template id()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!string input, in Caller caller)
        {
            return combinateMakeNode!
            (
                combinateChangeError!
                (
                    DLex.Identifier!(),
                    "identifier expected"
                ),
                TokenType.ID
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        with(parse!(id!(), ParserKind!(true, true))("_ab0="))
        {
            assert(match                 == true);
            assert(nextInput.source      == "=");
            assert(value.token.type            == TokenType.ID);
            assert(value.token.text           == "_ab0");
            assert(value.children.length == 0);
        }

        with(parse!(id!(), ParserKind!(true, true))("__hogehoge12345678"))
        {
            assert(match                 == true);
            assert(value.token.type            == TokenType.ID);
            assert(value.token.text           == "__hogehoge12345678");
            assert(value.children.length == 0);
        }

        with(parse!(id!(), ParserKind!(true, true))("ああ"))
        {
            assert(match          == false);
            assert(error.msg      == "identifier expected");
            assert(error.position == 0);
        }

        return true;
    }

    static assert(test());
    test();
}


template nonterminal()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!string input, in Caller caller)
        {
            return combinateMakeNode!
            (
                combinateChangeError!
                (
                    DLex.Identifier!(),
                    "identifier expected"
                ),
                TokenType.NONTERMINAL
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        with(parse!(nonterminal!(), ParserKind!(true, true))("_ab0="))
        {
            assert(match                 == true);
            assert(nextInput.source      == "=");
            assert(value.token.type            == TokenType.NONTERMINAL);
            assert(value.token.text           == "_ab0");
            assert(value.children.length == 0);
        }

        with(parse!(nonterminal!(), ParserKind!(true, true))("__hogehoge12345678"))
        {
            assert(match                 == true);
            assert(value.token.type            == TokenType.NONTERMINAL);
            assert(value.token.text           == "__hogehoge12345678");
            assert(value.children.length == 0);
        }

        with(parse!(nonterminal!(), ParserKind!(true, true))("ああ"))
        {
            assert(match          == false);
            assert(error.msg      == "identifier expected");
            assert(error.position == 0);
        }

        return true;
    }

    static assert(test());
    test();
}


template typeName()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinateMakeNode!
            (
                combinateInputSlice!
                (
                    combinateSequence!
                    (
                        combinateChoice!
                        (
                            parseCharRange!('A','Z'),
                            parseCharRange!('a','z'),
                            parseString!"_"
                        ),
                        combinateMore0!
                        (
                            combinateChoice!
                            (
                                parseCharRange!('0','9'),
                                parseCharRange!('A','Z'),
                                parseCharRange!('a','z'),
                                parseString!"_",
                                parseString!"!",
                                arch!("(", ")"),
                                arch!("[", "]")
                            )
                        )
                    )
                ),
                TokenType.TEMPLATE_INSTANCE
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        with(parse!(typeName!(), ParserKind!(true, true))("hoge"))
        {
            assert(match == true);
            assert(value.token.type == TokenType.TEMPLATE_INSTANCE);
            assert(value.token.text == "hoge");
            assert(value.children.length == 0);
        }

        return true;
    }

    static assert(test());
    test();
}


template eofLit()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!string input, in Caller caller)
        {
            return combinateMakeNode!
            (
                parseString!"$",
                TokenType.DOLLAR
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        with(parse!(eofLit!(), ParserKind!(true, true))("$"))
        {
            assert(match                 == true);
            assert(value.token.type            == TokenType.DOLLAR);
            assert(value.token.text           == "$");
            assert(value.children.length == 0);
        }

        with(parse!(eofLit!(), ParserKind!(true, true))("hoge"))
        {
            assert(match          == false);
            assert(error.msg      == "'$' expected");
            assert(error.position == 0);
        }

        return true;
    }

    static assert(test());
    test();
}


template rangeLitOneChar()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinateMakeNode!
            (
                combinateInputSlice!
                (
                    parseCharRange!(dchar.min, dchar.max),
                ),
                TokenType.RANGE_ONE_CHAR
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        with(parse!(rangeLitOneChar!(), ParserKind!(true, true))("a"))
        {
            assert(match == true);
            assert(value.token.type == TokenType.RANGE_ONE_CHAR);
            assert(value.token.text == "a");
            assert(value.children.length == 0);
        }

        with(parse!(rangeLitOneChar!(), ParserKind!(true, true))("鬱"))
        {
            assert(match == true);
            assert(value.token.type == TokenType.RANGE_ONE_CHAR);
            assert(value.token.text == "鬱");
            assert(value.children.length == 0);
        }

        return true;
    }

    static assert(test());
    test();
}


template rangeLitCharRange()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinateSetInfo!
            (
                combinateConvert!
                (
                    combinateUnTuple!
                    (
                        combinateSequence!
                        (
                            rangeLitOneChar!(),
                            combinateNone!
                            (
                                parseString!"-"
                            ),
                            rangeLitOneChar!()
                        ),
                    ),
                    (Node begin, Node end) => Node(Token(TokenType.RANGE_CHAR_RANGE, "-"), [begin, end])
                )
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        with(parse!(rangeLitCharRange!(), ParserKind!(true, true))("a-z"))
        {
            assert(match                             == true);
            assert(value.token.type                        == TokenType.RANGE_CHAR_RANGE);
            assert(value.token.text                       == "-");
            assert(value.children.length             == 2);
            assert(value.children[0].token.type            == TokenType.RANGE_ONE_CHAR);
            assert(value.children[0].token.text           == "a");
            assert(value.children[0].children.length == 0);
            assert(value.children[1].token.type            == TokenType.RANGE_ONE_CHAR);
            assert(value.children[1].token.text           == "z");
            assert(value.children[1].children.length == 0);
        }

        with(parse!(rangeLitCharRange!(), ParserKind!(true, true))("躁-鬱"))
        {
            assert(match                             == true);
            assert(value.token.type                        == TokenType.RANGE_CHAR_RANGE);
            assert(value.token.text                       == "-");
            assert(value.children.length             == 2);
            assert(value.children[0].token.type            == TokenType.RANGE_ONE_CHAR);
            assert(value.children[0].token.text           == "躁");
            assert(value.children[0].children.length == 0);
            assert(value.children[1].token.type            == TokenType.RANGE_ONE_CHAR);
            assert(value.children[1].token.text           == "鬱");
            assert(value.children[1].children.length == 0);
        }

        return true;
    }

    static assert(test());
    test();
}


template rangeLit()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinateSetInfo!
            (
                combinateConvert!
                (
                    combinateUnTuple!
                    (
                        combinateSequence!
                        (
                            combinateNone!
                            (
                                parseString!"["
                            ),
                            combinateMore1!
                            (
                                combinateUnTuple!
                                (
                                    combinateSequence!
                                    (
                                        combinateNotPred!
                                        (
                                            parseString!"]"
                                        ),
                                        combinateChoice!
                                        (
                                            rangeLitCharRange!(),
                                            rangeLitOneChar!()
                                        )
                                    )
                                )
                            ),
                            combinateNone!
                            (
                                parseString!"]"
                            )
                        ),
                    ),
                    (Node[] children) => Node(Token(TokenType.RANGE, "RANGE_LIT"), children)
                )
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        with(parse!(rangeLit!(), ParserKind!(true, true))("[a-zあ躁-鬱]"))
        {
            assert(match                                         == true);
            assert(value.token.type                                    == TokenType.RANGE);
            assert(value.token.text                                   == "RANGE_LIT");
            assert(value.children.length                         == 3);
            assert(value.children[0].token.type                        == TokenType.RANGE_CHAR_RANGE);
            assert(value.children[0].token.text                       == "-");
            assert(value.children[0].children.length             == 2);
            assert(value.children[0].children[0].token.type            == TokenType.RANGE_ONE_CHAR);
            assert(value.children[0].children[0].token.text           == "a");
            assert(value.children[0].children[0].children.length == 0);
            assert(value.children[0].children[1].token.type            == TokenType.RANGE_ONE_CHAR);
            assert(value.children[0].children[1].token.text           == "z");
            assert(value.children[0].children[1].children.length == 0);
            assert(value.children[1].token.type                        == TokenType.RANGE_ONE_CHAR);
            assert(value.children[1].token.text                       == "あ");
            assert(value.children[1].children.length             == 0);
            assert(value.children[2].token.type                        == TokenType.RANGE_CHAR_RANGE);
            assert(value.children[2].token.text                       == "-");
            assert(value.children[2].children.length             == 2);
            assert(value.children[2].children[0].token.type            == TokenType.RANGE_ONE_CHAR);
            assert(value.children[2].children[0].token.text           == "躁");
            assert(value.children[2].children[0].children.length == 0);
            assert(value.children[2].children[1].token.type            == TokenType.RANGE_ONE_CHAR);
            assert(value.children[2].children[1].token.text           == "鬱");
            assert(value.children[2].children[1].children.length == 0);
        }

        return true;
    }

    static assert(test());
    test();
}


template stringLit()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinateMakeNode!
            (
                DLex.StringLiteral!(),
                TokenType.STRING
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        with(parse!(stringLit!(), ParserKind!(true, true))(q{"hoge"}))
        {
            assert(match == true);
            assert(value.token.type == TokenType.STRING);
            assert(value.token.text == q{"hoge"});
            assert(value.children.length == 0);
        }

        with(parse!(stringLit!(), ParserKind!(true, true))(q{r"hoge\"}))
        {
            assert(match == true);
            assert(value.token.type == TokenType.STRING);
            assert(value.token.text == q{r"hoge\"});
            assert(value.children.length == 0);
        }

        with(parse!(stringLit!(), ParserKind!(true, true))(q{`"hoge"`}))
        {
            assert(match == true);
            assert(value.token.type == TokenType.STRING);
            assert(value.token.text == q{`"hoge"`});
            assert(value.children.length == 0);
        }

        return true;
    }

    static assert(test());
    test();
}


template literal()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinateChoice!
            (
                eofLit!(),
                rangeLit!(),
                stringLit!()
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        with(parse!(literal!(), ParserKind!(true, true))("$"))
        {
            assert(match                 == true);
            assert(value.token.type            == TokenType.DOLLAR);
            assert(value.token.text           == "$");
            assert(value.children.length == 0);
        }

        with(parse!(literal!(), ParserKind!(true, true))("[a-zあ躁-鬱]"))
        {
            assert(match                                         == true);
            assert(value.token.type                                    == TokenType.RANGE);
            assert(value.token.text                                   == "RANGE_LIT");
            assert(value.children.length                         == 3);
            assert(value.children[0].token.type                        == TokenType.RANGE_CHAR_RANGE);
            assert(value.children[0].token.text                       == "-");
            assert(value.children[0].children.length             == 2);
            assert(value.children[0].children[0].token.type            == TokenType.RANGE_ONE_CHAR);
            assert(value.children[0].children[0].token.text           == "a");
            assert(value.children[0].children[0].children.length == 0);
            assert(value.children[0].children[1].token.type            == TokenType.RANGE_ONE_CHAR);
            assert(value.children[0].children[1].token.text           == "z");
            assert(value.children[0].children[1].children.length == 0);
            assert(value.children[1].token.type                        == TokenType.RANGE_ONE_CHAR);
            assert(value.children[1].token.text                       == "あ");
            assert(value.children[1].children.length             == 0);
            assert(value.children[2].token.type                        == TokenType.RANGE_CHAR_RANGE);
            assert(value.children[2].token.text                       == "-");
            assert(value.children[2].children.length             == 2);
            assert(value.children[2].children[0].token.type            == TokenType.RANGE_ONE_CHAR);
            assert(value.children[2].children[0].token.text           == "躁");
            assert(value.children[2].children[0].children.length == 0);
            assert(value.children[2].children[1].token.type            == TokenType.RANGE_ONE_CHAR);
            assert(value.children[2].children[1].token.text           == "鬱");
            assert(value.children[2].children[1].children.length == 0);
        }

        with(parse!(literal!(), ParserKind!(true, true))(q{"hoge"}))
        {
            assert(match == true);
            assert(value.token.type == TokenType.STRING);
            assert(value.token.text == q{"hoge"});
            assert(value.children.length == 0);
        }

        with(parse!(literal!(), ParserKind!(true, true))(q{r"hoge\"}))
        {
            assert(match == true);
            assert(value.token.type == TokenType.STRING);
            assert(value.token.text == q{r"hoge\"});
            assert(value.children.length == 0);
        }

        with(parse!(literal!(), ParserKind!(true, true))(q{`"hoge"`}))
        {
            assert(match == true);
            assert(value.token.type == TokenType.STRING);
            assert(value.token.text == q{`"hoge"`});
            assert(value.children.length == 0);
        }

        with(parse!(literal!(), ParserKind!(true, true))("hoge"))
        {
            assert(match          == false);
            assert(error.msg      == "'\"' expected");
            assert(error.position == 0);
        }

        return true;
    }

    static assert(test());
    test();
}


template primaryExp()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinateChoice!
            (
                stringLit!(),
                rangeLit!(),
                eofLit!(),
                combinateUnTuple!
                (
                    combinateSequence!
                    (
                        combinateNone!
                        (
                            parseString!"("
                        ),
                        spaces!(),
                        choiceExp!(),
                        spaces!(),
                        combinateNone!
                        (
                            parseString!")"
                        )
                    )
                ),
                nonterminal!()
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        with(parse!(primaryExp!(), ParserKind!(true, true))("$"))
        {
            assert(match                 == true);
            assert(value.token.type            == TokenType.DOLLAR);
            assert(value.token.text           == "$");
            assert(value.children.length == 0);
        }

        with(parse!(primaryExp!(), ParserKind!(true, true))("($)"))
        {
            assert(match                 == true);
            assert(value.token.type            == TokenType.DOLLAR);
            assert(value.token.text           == "$");
            assert(value.children.length == 0);
        }

        with(parse!(primaryExp!(), ParserKind!(true, true))("_ab0="))
        {
            assert(match                 == true);
            assert(nextInput.source      == "=");
            assert(value.token.type            == TokenType.NONTERMINAL);
            assert(value.token.text           == "_ab0");
            assert(value.children.length == 0);
        }

        return true;
    }

    static assert(test());
    test();
}


template preExp()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinateConvert!
            (
                combinateSequence!
                (
                    combinateOption!
                    (
                        combinateChoice!
                        (
                            parseString!"!",
                            parseString!"&",
                            parseString!"^"
                        )
                    ),
                    primaryExp!(),
                ),
                function(Option!string op, Node primaryExp)
                {
                    if(op.some)
                    {
                        Node preExp;

                        final switch(op.value)
                        {
                            case "!":
                                preExp.token.type = TokenType.EXCLAM;
                                break;
                            case "&":
                                preExp.token.type = TokenType.ANPERSAND;
                                break;
                            case "^":
                                preExp.token.type = TokenType.ASCIICIRCUM;
                                break;
                        }
                        preExp.token.text = op;
                        preExp.children ~= primaryExp;

                        return preExp;
                    }
                    else
                    {
                        return primaryExp;
                    }
                }
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        with(parse!(preExp!(), ParserKind!(true, true))("!$"))
        {
            assert(match                             == true);
            assert(value.token.type                        == TokenType.EXCLAM);
            assert(value.token.text                       == "!");
            assert(value.children.length             == 1);
            assert(value.children[0].token.type            == TokenType.DOLLAR);
            assert(value.children[0].token.text           == "$");
            assert(value.children[0].children.length == 0);
        }

        with(parse!(preExp!(), ParserKind!(true, true))("&$"))
        {
            assert(match                             == true);
            assert(value.token.type                        == TokenType.ANPERSAND);
            assert(value.token.text                       == "&");
            assert(value.children.length             == 1);
            assert(value.children[0].token.type            == TokenType.DOLLAR);
            assert(value.children[0].token.text           == "$");
            assert(value.children[0].children.length == 0);
        }

        with(parse!(preExp!(), ParserKind!(true, true))("^$"))
        {
            assert(match                             == true);
            assert(nextInput.source                  == "");
            assert(nextInput.position                == 2);
            assert(nextInput.line                    == 0);
            assert(value.token.type                        == TokenType.ASCIICIRCUM);
            assert(value.token.text                       == "^");
            assert(value.children.length             == 1);
            assert(value.children[0].token.type            == TokenType.DOLLAR);
            assert(value.children[0].token.text           == "$");
            assert(value.children[0].children.length == 0);
        }

        with(parse!(preExp!(), ParserKind!(true, true))("$"))
        {
            assert(match                 == true);
            assert(nextInput.source      == "");
            assert(nextInput.position    == 1);
            assert(value.token.type            == TokenType.DOLLAR);
            assert(value.token.text           == "$");
            assert(value.children.length == 0);
        }

        return true;
    }

    static assert(test());
    test();
}


template postExp()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinateConvert!
            (
                combinateSequence!
                (
                    preExp!(),
                    combinateOption!
                    (
                        combinateSequence!
                        (
                            combinateChoice!
                            (
                                parseString!"*",
                                parseString!"+",
                            ),
                            combinateOption!
                            (
                                combinateUnTuple!
                                (
                                    combinateSequence!
                                    (
                                        combinateNone!
                                        (
                                            parseString!"<"
                                        ),
                                        choiceExp!(),
                                        combinateNone!
                                        (
                                            parseString!">"
                                        )
                                    )
                                )
                            )
                        )
                    )
                ),
                function(Node preExp, Option!(Tuple!(string, Option!Node)) op)
                {
                    if(op.some)
                    {
                        Node postExp;

                        final switch(op[0])
                        {
                            case "*":
                                postExp.token.type = TokenType.ASTERISK;
                                break;
                            case "+":
                                postExp.token.type = TokenType.PLUS;
                                break;
                        }

                        postExp.token.text = op[0];
                        postExp.children ~= preExp;

                        if(op[1].some)
                        {
                            postExp.children ~= op[1];
                        }

                        return postExp;
                    }
                    else
                    {
                        return preExp;
                    }
                }
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        with(parse!(postExp!(), ParserKind!(true, true))("$*"))
        {
            assert(match == true);
            assert(value.token.type == TokenType.ASTERISK);
            assert(value.token.text == "*");
            assert(value.children.length == 1);
            assert(value.children[0].token.type == TokenType.DOLLAR);
            assert(value.children[0].token.text == "$");
            assert(value.children[0].children.length == 0);
        }

        with(parse!(postExp!(), ParserKind!(true, true))("$+"))
        {
            assert(match == true);
            assert(value.token.type == TokenType.PLUS);
            assert(value.token.text == "+");
            assert(value.children.length == 1);
            assert(value.children[0].token.type == TokenType.DOLLAR);
            assert(value.children[0].token.text == "$");
            assert(value.children[0].children.length == 0);
        }

        with(parse!(postExp!(), ParserKind!(true, true))("$*<$>"))
        {
            assert(match == true);
            assert(value.token.type == TokenType.ASTERISK);
            assert(value.token.text == "*");
            assert(value.children.length == 2);
            assert(value.children[0].token.type == TokenType.DOLLAR);
            assert(value.children[0].token.text == "$");
            assert(value.children[0].children.length == 0);
            assert(value.children[1].token.type == TokenType.DOLLAR);
            assert(value.children[1].token.text == "$");
            assert(value.children[1].children.length == 0);
        }

        with(parse!(postExp!(), ParserKind!(true, true))("$+<$>"))
        {
            assert(match == true);
            assert(value.token.type == TokenType.PLUS);
            assert(value.token.text == "+");
            assert(value.children.length == 2);
            assert(value.children[0].token.type == TokenType.DOLLAR);
            assert(value.children[0].token.text == "$");
            assert(value.children[0].children.length == 0);
            assert(value.children[1].token.type == TokenType.DOLLAR);
            assert(value.children[1].token.text == "$");
            assert(value.children[1].children.length == 0);
        }

        return true;
    }

    static assert(test());
    test();
}


template optionExp()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinateConvert!
            (
                combinateSequence!
                (
                    postExp!(),
                    combinateOption!
                    (
                        combinateNone!
                        (
                            parseString!"?"
                        )
                    )
                ),
                function(Node postExp, Option!None op)
                {
                    if(op.some)
                    {
                        Node optionExp;

                        optionExp.token.type = TokenType.QUESTION;
                        optionExp.token.text = "?";
                        optionExp.children ~= postExp;

                        return optionExp;
                    }
                    else
                    {
                        return postExp;
                    }
                }
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        with(parse!(optionExp!(), ParserKind!(true, true))("$?"))
        {
            assert(match == true);
            assert(value.token.type == TokenType.QUESTION);
            assert(value.token.text == "?");
            assert(value.children.length == 1);
            assert(value.children[0].token.type == TokenType.DOLLAR);
            assert(value.children[0].token.text == "$");
            assert(value.children[0].children.length == 0);
        }

        return true;
    }

    static assert(test());
    test();
}


template seqExp()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinateConvert!
            (
                combinateMore1!
                (
                    optionExp!(),
                    spaces!()
                ),
                function(Node[] optionExps)
                {
                    if(optionExps.length > 1)
                    {
                        Node seqExp;

                        seqExp.token.type = TokenType.SEQUENCE;
                        seqExp.token.text = "SEQ";
                        seqExp.children = optionExps;

                        return seqExp;
                    }
                    else
                    {
                        return optionExps[0];
                    }
                }
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        with(parse!(seqExp!(), ParserKind!(true, true))("$"))
        {
            assert(match                 == true);
            assert(value.token.type            == TokenType.DOLLAR);
            assert(value.token.text           == "$");
            assert(value.children.length == 0);
        }

        with(parse!(seqExp!(), ParserKind!(true, true))("$ $"))
        {
            assert(match                             == true);
            assert(value.token.type                        == TokenType.SEQUENCE);
            assert(value.token.text                       == "SEQ");
            assert(value.children.length             == 2);
            assert(value.children[0].token.type            == TokenType.DOLLAR);
            assert(value.children[0].token.text           == "$");
            assert(value.children[0].children.length == 0);
            assert(value.children[1].token.type            == TokenType.DOLLAR);
            assert(value.children[1].token.text           == "$");
            assert(value.children[1].children.length == 0);
        }

        return true;
    }

    static assert(test());
    test();
}


template convExp()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinateConvert!
            (
                combinateSequence!
                (
                    seqExp!(),
                    combinateMore0!
                    (
                        combinateUnTuple!
                        (
                            combinateSequence!
                            (
                                spaces!(),
                                parseGetLine!(),
                                parseGetCallerLine!(),
                                parseGetCallerFile!(),
                                combinateChoice!
                                (
                                    parseString!">?",
                                    parseString!">>"
                                ),
                                spaces!(),
                                combinateChoice!
                                (
                                    func!(),
                                    typeName!()
                                )
                            )
                        )
                    )
                ),
                function(Node seqExp, Tuple!(size_t, size_t, string, string, Node)[] funcs)
                {
                    Node result = seqExp;

                    foreach(func; funcs)
                    {
                        Node node;

                        size_t line = func[0];
                        size_t callerLine = func[1];
                        string callerFile = func[2];
                        string op = func[3];
                        Node funcNode = func[4];

                        node.token.type = op == ">>" ? TokenType.LEFT_SHIFT : TokenType.LEFT_QUESTION;
                        node.token.text = op;
                        node.children ~= result;
                        node.children ~= funcNode;
                        node.line = line + callerLine + 1;
                        node.file = callerFile;

                        result = node;
                    }

                    return result;
                }
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        with(parse!(convExp!(), ParserKind!(true, true))("$"))
        {
            assert(match == true);
            assert(value.token.type            == TokenType.DOLLAR);
            assert(value.token.text           == "$");
            assert(value.children.length == 0);
        }

        with(parse!(convExp!(), ParserKind!(true, true))("$ >> hoge"))
        {
            assert(match == true);
            assert(value.token.type == TokenType.LEFT_SHIFT);
            assert(value.token.text == ">>");
            assert(value.line == __LINE__ - 4);
            assert(value.file == __FILE__);
            assert(value.children.length == 2);
            assert(value.children[0].token.type            == TokenType.DOLLAR);
            assert(value.children[0].token.text           == "$");
            assert(value.children[0].children.length == 0);
            assert(value.children[1].token.type            == TokenType.TEMPLATE_INSTANCE);
            assert(value.children[1].token.text           == "hoge");
            assert(value.children[1].children.length == 0);
        }

        with(parse!(convExp!(), ParserKind!(true, true))("$ >> hoge >> piyo"))
        {
            assert(match                                         == true);
            assert(value.token.type                                    == TokenType.LEFT_SHIFT);
            assert(value.token.text                                   == ">>");
            assert(value.line                                    == __LINE__ - 4);
            assert(value.file                                    == __FILE__);
            assert(value.children.length                         == 2);
            assert(value.children[0].token.type                        == TokenType.LEFT_SHIFT);
            assert(value.children[0].token.text                       == ">>");
            assert(value.children[0].line                        == __LINE__ - 9);
            assert(value.children[0].file                        == __FILE__);
            assert(value.children[0].children.length             == 2);
            assert(value.children[0].children[0].token.type            == TokenType.DOLLAR);
            assert(value.children[0].children[0].token.text           == "$");
            assert(value.children[0].children[0].children.length == 0);
            assert(value.children[0].children[1].token.type            == TokenType.TEMPLATE_INSTANCE);
            assert(value.children[0].children[1].token.text           == "hoge");
            assert(value.children[0].children[1].children.length == 0);
            assert(value.children[1].token.type                        == TokenType.TEMPLATE_INSTANCE);
            assert(value.children[1].token.text                       == "piyo");
            assert(value.children[1].children.length             == 0);
        }

        with(parse!(convExp!(), ParserKind!(true, true))("$ >> hoge >? piyo"))
        {
            assert(match == true);
            assert(value.token.type == TokenType.LEFT_QUESTION);
            assert(value.token.text == ">?");
            assert(value.children.length == 2);
            assert(value.children[0].token.type == TokenType.LEFT_SHIFT);
            assert(value.children[0].token.text == ">>");
            assert(value.children[0].children.length == 2);
            assert(value.children[0].children[0].token.type            == TokenType.DOLLAR);
            assert(value.children[0].children[0].token.text           == "$");
            assert(value.children[0].children[0].children.length == 0);
            assert(value.children[0].children[1].token.type            == TokenType.TEMPLATE_INSTANCE);
            assert(value.children[0].children[1].token.text           == "hoge");
            assert(value.children[0].children[1].children.length == 0);
            assert(value.children[1].token.type            == TokenType.TEMPLATE_INSTANCE);
            assert(value.children[1].token.text           == "piyo");
            assert(value.children[1].children.length == 0);
        }

        with(parse!(convExp!(), ParserKind!(true, true))("$ >> (a, b){ return a + b; }"))
        {
            assert(match == true);
            assert(value.token.type == TokenType.LEFT_SHIFT);
            assert(value.token.text == ">>");
            assert(value.children.length == 2);
            assert(value.children[0].token.type            == TokenType.DOLLAR);
            assert(value.children[0].token.text           == "$");
            assert(value.children[0].children.length == 0);
            assert(value.children[1].token.type            == TokenType.CONVERTER);
            assert(value.children[1].token.text           == q{(a, b){ return a + b; }});
            assert(value.children[1].children.length == 0);
        }

        return true;
    }

    static assert(test());
    test();
}


template choiceExp()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinateConvert!
            (
                combinateMore1!
                (
                    convExp!(),
                    combinateSequence!
                    (
                        spaces!(),
                        parseString!"/",
                        spaces!()
                    )
                ),
                function(Node[] convExps)
                {
                    if(convExps.length > 1)
                    {
                        Node choiceExp;

                        choiceExp.token.type = TokenType.SLASH;
                        choiceExp.token.text = "/";
                        choiceExp.children = convExps;

                        return choiceExp;
                    }
                    else
                    {
                        return convExps[0];
                    }
                }
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        with(parse!(choiceExp!(), ParserKind!(true, true))("$"))
        {
            assert(match                 == true);
            assert(value.token.type            == TokenType.DOLLAR);
            assert(value.token.text           == "$");
            assert(value.children.length == 0);
        }

        with(parse!(choiceExp!(), ParserKind!(true, true))("$ "))
        {
            assert(match                 == true);
            assert(value.token.type            == TokenType.DOLLAR);
            assert(value.token.text           == "$");
            assert(value.children.length == 0);
        }

        with(parse!(choiceExp!(), ParserKind!(true, true))("$ / $"))
        {
            assert(match                             == true);
            assert(value.token.type                        == TokenType.SLASH);
            assert(value.token.text                       == "/");
            assert(value.children.length             == 2);
            assert(value.children[0].token.type            == TokenType.DOLLAR);
            assert(value.children[0].token.text           == "$");
            assert(value.children[0].children.length == 0);
            assert(value.children[1].token.type            == TokenType.DOLLAR);
            assert(value.children[1].token.text           == "$");
            assert(value.children[1].children.length == 0);
        }

        return true;
    }

    static assert(test());
    test();
}


template def()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinateConvert!
            (
                combinateSequence!
                (
                    combinateOption!
                    (
                        combinateUnTuple!
                        (
                            combinateSequence!
                            (
                                combinateNone!
                                (
                                    parseString!"@setSkip(",
                                ),
                                spaces!(),
                                choiceExp!(),
                                spaces!(),
                                combinateNone!
                                (
                                    parseString!")"
                                ),
                                spaces!()
                            )
                        )
                    ),
                    typeName!(),
                    spaces!(),
                    id!(),
                    spaces!(),
                    combinateNone!
                    (
                        parseString!"="
                    ),
                    spaces!(),
                    choiceExp!(),
                    spaces!(),
                    combinateNone!
                    (
                        parseString!";"
                    )
                ),
                function(Option!Node skip, Node type, Node name, Node choiceExp)
                {
                    Node def;

                    def.token.type = TokenType.DEFINITION;
                    def.children ~= type;
                    def.children ~= name;

                    if(skip.some)
                    {
                        Node skipNode;

                        skipNode.token.type = TokenType.SET_SKIP;
                        skipNode.children ~= skip;
                        skipNode.children ~= choiceExp;

                        def.children ~= skipNode;
                    }
                    else
                    {
                        def.children ~= choiceExp;
                    }

                    return def;
                }
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        with(parse!(def!(), ParserKind!(true, true))(q{int hoge = $;}))
        {
            assert(match                             == true);
            assert(value.token.type                        == TokenType.DEFINITION);
            assert(value.children.length             == 3);
            assert(value.children[0].token.type            == TokenType.TEMPLATE_INSTANCE);
            assert(value.children[0].token.text           == "int");
            assert(value.children[0].children.length == 0);
            assert(value.children[1].token.type            == TokenType.ID);
            assert(value.children[1].token.text           == "hoge");
            assert(value.children[1].children.length == 0);
            assert(value.children[2].token.type            == TokenType.DOLLAR);
            assert(value.children[2].token.text           == "$");
            assert(value.children[2].children.length == 0);
        }

        with(parse!(def!(), ParserKind!(true, true))(q{@setSkip($) int hoge = $;}))
        {
            assert(match                                               == true);
            assert(value.token.type                                    == TokenType.DEFINITION);
            assert(value.children.length                               == 3);
            assert(value.children[0].token.type                        == TokenType.TEMPLATE_INSTANCE);
            assert(value.children[0].token.text                        == "int");
            assert(value.children[0].children.length                   == 0);
            assert(value.children[1].token.type                        == TokenType.ID);
            assert(value.children[1].token.text                        == "hoge");
            assert(value.children[1].children.length                   == 0);
            assert(value.children[2].token.type                        == TokenType.SET_SKIP);
            assert(value.children[2].children.length                   == 2);
            assert(value.children[2].children[0].token.type            == TokenType.DOLLAR);
            assert(value.children[2].children[0].token.text            == "$");
            assert(value.children[2].children[0].children.length       == 0);
            assert(value.children[2].children[1].token.type            == TokenType.DOLLAR);
            assert(value.children[2].children[1].token.text            == "$");
            assert(value.children[2].children[1].children.length       == 0);
        }

        return true;
    }

    static assert(test());
    test();
}


template defaultSkip()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinateConvert!
            (
                combinateUnTuple!
                (
                    combinateSequence!
                    (
                        combinateNone!
                        (
                            parseString!"@_setSkip("
                        ),
                        spaces!(),
                        choiceExp!(),
                        spaces!(),
                        combinateNone!
                        (
                            parseString!")"
                        )
                    )
                ),
                function(Node skip)
                {
                    Node setSkipNode;

                    setSkipNode.token.type = TokenType.GLOBAL_SET_SKIP;
                    setSkipNode.children ~= skip;

                    return setSkipNode;
                }
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}


template defs()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinateConvert!
            (
                combinateUnTuple!
                (
                    combinateSequence!
                    (
                        spaces!(),
                        combinateMore0!
                        (
                            combinateChoice!
                            (
                                defaultSkip!(),
                                def!()
                            ),
                            spaces!()
                        ),
                        spaces!(),
                        parseEOF!()
                    )
                ),
                function(Node[] nodes)
                {
                    Node defs;

                    defs.token.type = TokenType.DEFINITIONS;
                    defs.children = nodes;

                    return defs;
                }
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    static bool test()
    {
        with(parse!(defs!(), ParserKind!(true, true))(q{int hoge = $; int piyo = $;}))
        {
            assert(match                                         == true);
            assert(value.token.type                                    == TokenType.DEFINITIONS);
            assert(value.children.length                         == 2);
            assert(value.children[0].token.type                        == TokenType.DEFINITION);
            assert(value.children[0].children.length             == 3);
            assert(value.children[0].children[0].token.type            == TokenType.TEMPLATE_INSTANCE);
            assert(value.children[0].children[0].token.text           == "int");
            assert(value.children[0].children[0].children.length == 0);
            assert(value.children[0].children[1].token.type            == TokenType.ID);
            assert(value.children[0].children[1].token.text           == "hoge");
            assert(value.children[0].children[1].children.length == 0);
            assert(value.children[0].children[2].token.type            == TokenType.DOLLAR);
            assert(value.children[0].children[2].token.text           == "$");
            assert(value.children[0].children[2].children.length == 0);
            assert(value.children[1].token.type                        == TokenType.DEFINITION);
            assert(value.children[1].children.length             == 3);
            assert(value.children[1].children[0].token.type            == TokenType.TEMPLATE_INSTANCE);
            assert(value.children[1].children[0].token.text           == "int");
            assert(value.children[1].children[0].children.length == 0);
            assert(value.children[1].children[1].token.type            == TokenType.ID);
            assert(value.children[1].children[1].token.text           == "piyo");
            assert(value.children[1].children[1].children.length == 0);
            assert(value.children[1].children[2].token.type            == TokenType.DOLLAR);
            assert(value.children[1].children[2].token.text           == "$");
            assert(value.children[1].children[2].children.length == 0);
        }

        with(parse!(defs!(), ParserKind!(true, true))(q{@setSkip($) int hoge = $; @setSkip($) int piyo = $;}))
        {
            assert(match                                                     == true);
            assert(value.token.type                                          == TokenType.DEFINITIONS);
            assert(value.children.length                                     == 2);
            assert(value.children[0].token.type                              == TokenType.DEFINITION);
            assert(value.children[0].children.length                         == 3);
            assert(value.children[0].children[0].token.type                  == TokenType.TEMPLATE_INSTANCE);
            assert(value.children[0].children[0].token.text                  == "int");
            assert(value.children[0].children[0].children.length             == 0);
            assert(value.children[0].children[1].token.type                  == TokenType.ID);
            assert(value.children[0].children[1].token.text                  == "hoge");
            assert(value.children[0].children[1].children.length             == 0);
            assert(value.children[0].children[2].token.type                  == TokenType.SET_SKIP);
            assert(value.children[0].children[2].children.length             == 2);
            assert(value.children[0].children[2].children[0].token.type      == TokenType.DOLLAR);
            assert(value.children[0].children[2].children[0].token.text      == "$");
            assert(value.children[0].children[2].children[0].children.length == 0);
            assert(value.children[0].children[2].children[1].token.type      == TokenType.DOLLAR);
            assert(value.children[0].children[2].children[1].token.text      == "$");
            assert(value.children[0].children[2].children[1].children.length == 0);
            assert(value.children[1].token.type                              == TokenType.DEFINITION);
            assert(value.children[1].children.length                         == 3);
            assert(value.children[1].children[0].token.type                  == TokenType.TEMPLATE_INSTANCE);
            assert(value.children[1].children[0].token.text                  == "int");
            assert(value.children[1].children[0].children.length             == 0);
            assert(value.children[1].children[1].token.type                  == TokenType.ID);
            assert(value.children[1].children[1].token.text                  == "piyo");
            assert(value.children[1].children[1].children.length             == 0);
            assert(value.children[1].children[2].token.type                  == TokenType.SET_SKIP);
            assert(value.children[1].children[2].children.length             == 2);
            assert(value.children[1].children[2].children[0].token.type      == TokenType.DOLLAR);
            assert(value.children[1].children[2].children[0].token.text      == "$");
            assert(value.children[1].children[2].children[0].children.length == 0);
            assert(value.children[1].children[2].children[1].token.type      == TokenType.DOLLAR);
            assert(value.children[1].children[2].children[1].token.text      == "$");
            assert(value.children[1].children[2].children[1].children.length == 0);
        }

        with(parse!(defs!(), ParserKind!(true, true))(q{@_setSkip($) @setSkip($) int hoge = $; @setSkip($) int piyo = $;}))
        {
            assert(match                                                     == true);
            assert(value.token.type                                                == TokenType.DEFINITIONS);
            assert(value.children.length                                     == 3);
            assert(value.children[0].token.type                                    == TokenType.GLOBAL_SET_SKIP);
            assert(value.children[0].children.length                         == 1);
            assert(value.children[0].children[0].token.type                        == TokenType.DOLLAR);
            assert(value.children[0].children[0].token.text                       == "$");
            assert(value.children[0].children[0].children.length             == 0);
            assert(value.children[1].token.type                              == TokenType.DEFINITION);
            assert(value.children[1].children.length                         == 3);
            assert(value.children[1].children[0].token.type                  == TokenType.TEMPLATE_INSTANCE);
            assert(value.children[1].children[0].token.text                  == "int");
            assert(value.children[1].children[0].children.length             == 0);
            assert(value.children[1].children[1].token.type                  == TokenType.ID);
            assert(value.children[1].children[1].token.text                  == "hoge");
            assert(value.children[1].children[1].children.length             == 0);
            assert(value.children[1].children[2].token.type                  == TokenType.SET_SKIP);
            assert(value.children[1].children[2].children.length             == 2);
            assert(value.children[1].children[2].children[0].token.type      == TokenType.DOLLAR);
            assert(value.children[1].children[2].children[0].token.text      == "$");
            assert(value.children[1].children[2].children[0].children.length == 0);
            assert(value.children[1].children[2].children[1].token.type      == TokenType.DOLLAR);
            assert(value.children[1].children[2].children[1].token.text      == "$");
            assert(value.children[1].children[2].children[1].children.length == 0);
            assert(value.children[2].token.type                              == TokenType.DEFINITION);
            assert(value.children[2].children.length                         == 3);
            assert(value.children[2].children[0].token.type                  == TokenType.TEMPLATE_INSTANCE);
            assert(value.children[2].children[0].token.text                  == "int");
            assert(value.children[2].children[0].children.length             == 0);
            assert(value.children[2].children[1].token.type                  == TokenType.ID);
            assert(value.children[2].children[1].token.text                  == "piyo");
            assert(value.children[2].children[1].children.length             == 0);
            assert(value.children[2].children[2].token.type                  == TokenType.SET_SKIP);
            assert(value.children[2].children[2].children.length             == 2);
            assert(value.children[2].children[2].children[0].token.type      == TokenType.DOLLAR);
            assert(value.children[2].children[2].children[0].token.text      == "$");
            assert(value.children[2].children[2].children[0].children.length == 0);
            assert(value.children[2].children[2].children[1].token.type      == TokenType.DOLLAR);
            assert(value.children[2].children[2].children[1].token.text      == "$");
            assert(value.children[2].children[2].children[1].children.length == 0);
        }

        return true;
    }

    static assert(test());
    test();
}
