module ctpg.combinators;

import std.conv : to;
import std.typecons  : Tuple, tuple;
import std.traits : CommonType, isArray;
import std.range : hasSlicing;

import ctpg : parse;

import ctpg.for_unittest : TestParser, convs;
import ctpg.parse_result : ParseResult, getParseResultType;
import ctpg.parser_kind  : ParserKind, ParserKinds;
import ctpg.input        : Input;
import ctpg.caller       : Caller;
import ctpg.none         : None;
import ctpg.macro_       : MAKE_RESULT;
import ctpg.option       : Option;

import parsers = ctpg.parsers : string_, success;

import compile_time_unittest : enableCompileTimeUnittest;
mixin enableCompileTimeUnittest;


template untuple(alias parser)
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
    foreach(conv; convs) foreach(kind; ParserKinds)
    {
        with(parse!(untuple!(TestParser!(tuple("hoge", "fuga"))), kind)(conv!"input"))
        {
                                     assert(match            == true);
            static if(kind.hasValue) assert(value            == tuple("hoge", "fuga"));
                                     assert(nextInput.source == conv!"input");
                                     assert(nextInput.position == 0);
                                     assert(nextInput.line   == 0);
        }

        with(parse!(untuple!(TestParser!(tuple("hoge"))), kind)(conv!"input"))
        {
                                     assert(match            == true);
            static if(kind.hasValue) assert(value            == "hoge");
                                     assert(nextInput.source == conv!"input");
                                     assert(nextInput.position == 0);
                                     assert(nextInput.line   == 0);
        }
    }
}


template sequence(parsers...)
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

            static if(is(T == None)) mixin MAKE_RESULT!q{           getParseResultType!(sequence!(parsers[1..$]).build!(kind, SrcType)) };
            else                     mixin MAKE_RESULT!q{ Tuple!(T, getParseResultType!(sequence!(parsers[1..$]).build!(kind, SrcType)).Types) };

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

                auto tail = sequence!(parsers[1..$]).build!(kind, SrcType).parse(head.nextInput, caller);

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
    foreach(conv; convs) foreach(kind; ParserKinds)
    {
        with(parse!(sequence!(parsers.string_!"hoge", parsers.string_!"fuga"), kind)(conv!"hogefugahoge"))
        {
                                     assert(match            == true);
            static if(kind.hasValue) assert(value            == tuple("hoge", "fuga"));
                                     assert(nextInput.source == conv!"hoge");
                                     assert(nextInput.position == 8);
                                     assert(nextInput.line == 0);
        }

        with(parse!(sequence!(parsers.string_!"hoge", parsers.string_!"fuga"), kind)(conv!"hoge"))
        {
                                     assert(match          == false);
            static if(kind.hasError) assert(error.msg      == "'fuga' expected");
            static if(kind.hasError) assert(error.position == 4);
        }

        with(parse!(sequence!(parsers.string_!"hoge", parsers.string_!"fuga"), kind)(conv!"fuga"))
        {
                                     assert(match          == false);
            static if(kind.hasError) assert(error.msg      == "'hoge' expected");
            static if(kind.hasError) assert(error.position == 0);
        }

        with(parse!(sequence!(parsers.string_!"hoge", TestParser!(None()), parsers.string_!"fuga"), kind)(conv!"hogefuga"))
        {
                                     assert(match            == true);
            static if(kind.hasValue) assert(value            == tuple("hoge", "fuga"));
                                     assert(nextInput.source == conv!"");
                                     assert(nextInput.position == 8);
                                     assert(nextInput.line == 0);
        }
    }
}


template choice(parsers...)
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
            mixin MAKE_RESULT!q{ CommonType!(getParseResultType!(parsers[0].build!(kind, SrcType)), getParseResultType!(choice!(parsers[1..$]).build!(kind, SrcType))) };

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

                auto tail = choice!(parsers[1..$]).build!(kind, SrcType).parse(input, caller);

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
    foreach(conv; convs) foreach(kind; ParserKinds)
    {
        with(parse!(choice!(parsers.string_!"hoge", parsers.string_!"fuga"), kind)(conv!"hoge"))
        {
                                     assert(match              == true);
            static if(kind.hasValue) assert(value              == "hoge");
                                     assert(nextInput.source   == conv!"");
                                     assert(nextInput.position == 4);
                                     assert(nextInput.line == 0);
        }

        with(parse!(choice!(parsers.string_!"hoge", parsers.string_!"fuga"), kind)(conv!"fuga"))
        {
                                     assert(match              == true);
            static if(kind.hasValue) assert(value              == "fuga");
                                     assert(nextInput.source   == conv!"");
                                     assert(nextInput.position == 4);
                                     assert(nextInput.line == 0);
        }

        with(parse!(choice!(parsers.string_!"hoge", parsers.string_!"fuga"), kind)(conv!"piyo"))
        {
                                     assert(match          == false);
            static if(kind.hasError) assert(error.msg      == "'fuga' expected");
            static if(kind.hasError) assert(error.position == 0);
        }

        with(parse!(choice!(sequence!(parsers.string_!"hoge", parsers.string_!"piyo"), parsers.string_!"fuga"), ParserKind!(false, kind.hasError))(conv!"hoge"))
        {
                                     assert(match          == false);
            static if(kind.hasError) assert(error.msg      == "'piyo' expected");
            static if(kind.hasError) assert(error.position == 4);
        }
    }
}


template more(size_t n, alias parser, alias sep = success!())
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

template more0(alias parser, alias sep = success!())
{
    alias more0 = more!(0, parser, sep);
}


template more1(alias parser, alias sep = success!())
{
    alias more1 = more!(1, parser, sep);
}

debug(ctpg) unittest
{
    foreach(conv; convs) foreach(kind; ParserKinds)
    {
        with(parse!(more!(0, parsers.string_!"hoge", parsers.string_!","), kind)(conv!""))
        {
                                     assert(match              == true);
            static if(kind.hasValue) assert(value              == []);
                                     assert(nextInput.source   == conv!"");
                                     assert(nextInput.position == 0);
                                     assert(nextInput.line == 0);
        }

        with(parse!(more!(0, parsers.string_!"hoge", parsers.string_!","), kind)(conv!"hoge,hoge,hoge"))
        {
                                     assert(match              == true);
            static if(kind.hasValue) assert(value              == ["hoge", "hoge", "hoge"]);
                                     assert(nextInput.source   == conv!"");
                                     assert(nextInput.position == 14);
                                     assert(nextInput.line == 0);
        }

        with(parse!(more!(0, parsers.string_!"hoge", parsers.string_!","), kind)(conv!"hoge,hoge,hoge,"))
        {
                                     assert(match              == true);
            static if(kind.hasValue) assert(value              == ["hoge", "hoge", "hoge"]);
                                     assert(nextInput.source   == conv!",");
                                     assert(nextInput.position == 14);
                                     assert(nextInput.line == 0);
        }

        with(parse!(more!(4, parsers.string_!"hoge", parsers.string_!","), kind)(conv!"hoge,hoge,hoge"))
        {
                                     assert(match          == false);
            static if(kind.hasError) assert(error.msg      == "',' expected");
            static if(kind.hasError) assert(error.position == 14);
        }

        with(parse!(more!(4, parsers.string_!"hoge", parsers.string_!","), kind)(conv!"hoge,hoge,hoge,"))
        {
                                     assert(match          == false);
            static if(kind.hasError) assert(error.msg      == "'hoge' expected");
            static if(kind.hasError) assert(error.position == 15);
        }
    }
}


template andPred(alias parser)
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
    foreach(conv; convs) foreach(kind; ParserKinds)
    {
        with(parse!(andPred!(parsers.string_!"hoge"), kind)(conv!"hoge"))
        {
                                     assert(match              == true);
            static if(kind.hasValue) assert(value              == None());
                                     assert(nextInput.source   == conv!"hoge");
                                     assert(nextInput.position == 0);
                                     assert(nextInput.line == 0);
        }

        with(parse!(andPred!(parsers.string_!"hoge"), kind)(conv!"fuga"))
        {
                                     assert(match          == false);
            static if(kind.hasError) assert(error.msg      == "'hoge' expected");
            static if(kind.hasError) assert(error.position == 0);
        }
    }
}


template notPred(alias parser)
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
    foreach(conv; convs) foreach(kind; ParserKinds)
    {
        with(parse!(notPred!(parsers.string_!"hoge"), kind)(conv!"fuga"))
        {
                                     assert(match              == true);
            static if(kind.hasValue) assert(value              == None());
                                     assert(nextInput.source   == conv!"fuga");
                                     assert(nextInput.position == 0);
                                     assert(nextInput.line == 0);
        }

        with(parse!(notPred!(parsers.string_!"hoge"), kind)(conv!"hoge"))
        {
                                     assert(match          == false);
            static if(kind.hasError) assert(error.msg      == "failure expected");
            static if(kind.hasError) assert(error.position == 0);
        }
    }
}


template option(alias parser)
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
    foreach(conv; convs) foreach(kind; ParserKinds)
    {
        with(parse!(option!(parsers.string_!"hoge"), kind)(conv!"fuga"))
        {
                                     assert(match              == true);
            static if(kind.hasValue) assert(value.some         == false);
                                     assert(nextInput.source   == conv!"fuga");
                                     assert(nextInput.position == 0);
                                     assert(nextInput.line == 0);
        }

        with(parse!(option!(parsers.string_!"hoge"), kind)(conv!"hoge"))
        {
                                     assert(match              == true);
            static if(kind.hasValue) assert(value.some         == true);
            static if(kind.hasValue) assert(value        == "hoge");
                                     assert(nextInput.source   == conv!"");
                                     assert(nextInput.position == 4);
                                     assert(nextInput.line == 0);
        }
    }
}


template none(alias parser)
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
    foreach(conv; convs) foreach(kind; ParserKinds)
    {
        with(parse!(none!(parsers.string_!"hoge"), kind)(conv!"hoge"))
        {
                                     assert(match              == true);
            static if(kind.hasValue) assert(value              == None());
                                     assert(nextInput.source   == conv!"");
                                     assert(nextInput.position == 4);
                                     assert(nextInput.line == 0);
        }

        with(parse!(none!(parsers.string_!"hoge"), kind)(conv!"fuga"))
        {
                                     assert(match          == false);
            static if(kind.hasError) assert(error.msg      == "'hoge' expected");
            static if(kind.hasError) assert(error.position == 0);
        }
    }
}


template convert(alias parser, alias converter, size_t line = 0, string file = "")
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

    foreach(conv; convs) foreach(kind; ParserKinds)
    {
        with(parse!(convert!(parsers.string_!"hoge", Struct), kind)(conv!"hogee"))
        {
                                     assert(match              == true);
            static if(kind.hasValue) assert(value.len          == 4);
                                     assert(nextInput.source   == conv!"e");
                                     assert(nextInput.position == 4);
                                     assert(nextInput.line == 0);
        }

        with(parse!(convert!(parsers.string_!"hoge", Struct), kind)(conv!"!!!!"))
        {
                                     assert(match          == false);
            static if(kind.hasError) assert(error.msg      == "'hoge' expected");
            static if(kind.hasError) assert(error.position == 0);
        }

        with(parse!(convert!(parsers.string_!"hoge", Class), kind)(conv!"hogee"))
        {
                                     assert(match              == true);
            static if(kind.hasValue) assert(value.len          == 4);
                                     assert(nextInput.source   == conv!"e");
                                     assert(nextInput.position == 4);
                                     assert(nextInput.line == 0);
        }

        with(parse!(convert!(parsers.string_!"hoge", Class), kind)(conv!"!!!!"))
        {
                                     assert(match          == false);
            static if(kind.hasError) assert(error.msg      == "'hoge' expected");
            static if(kind.hasError) assert(error.position == 0);
        }

        with(parse!(convert!(parsers.string_!"hoge", Function), kind)(conv!"hogee"))
        {
                                     assert(match              == true);
            static if(kind.hasValue) assert(value              == 4);
                                     assert(nextInput.source   == conv!"e");
                                     assert(nextInput.position == 4);
                                     assert(nextInput.line == 0);
        }

        with(parse!(convert!(parsers.string_!"hoge", Function), kind)(conv!"!!!!"))
        {
                                     assert(match          == false);
            static if(kind.hasError) assert(error.msg      == "'hoge' expected");
            static if(kind.hasError) assert(error.position == 0);
        }

        with(parse!(convert!(parsers.string_!"hoge", TemplateFunction), kind)(conv!"hogee"))
        {
                                     assert(match              == true);
            static if(kind.hasValue) assert(value              == 4);
                                     assert(nextInput.source   == conv!"e");
                                     assert(nextInput.position == 4);
                                     assert(nextInput.line == 0);
        }

        with(parse!(convert!(parsers.string_!"hoge", TemplateFunction), kind)(conv!"!!!!"))
        {
                                     assert(match          == false);
            static if(kind.hasError) assert(error.msg      == "'hoge' expected");
            static if(kind.hasError) assert(error.position == 0);
        }

        with(parse!(convert!(parsers.string_!"hoge", (x) => x.length), kind)(conv!"hogee"))
        {
                                     assert(match              == true);
            static if(kind.hasValue) assert(value              == 4);
                                     assert(nextInput.source   == conv!"e");
                                     assert(nextInput.position == 4);
                                     assert(nextInput.line == 0);
        }

        with(parse!(convert!(parsers.string_!"hoge", (x) => x.length), kind)(conv!"!!!!"))
        {
                                     assert(match          == false);
            static if(kind.hasError) assert(error.msg      == "'hoge' expected");
            static if(kind.hasError) assert(error.position == 0);
        }

        with(parse!(convert!(parsers.string_!"hoge", (x){ return x.length; }), kind)(conv!"hogee"))
        {
                                     assert(match              == true);
            static if(kind.hasValue) assert(value              == 4);
                                     assert(nextInput.source   == conv!"e");
                                     assert(nextInput.position == 4);
                                     assert(nextInput.line == 0);
        }

        with(parse!(convert!(parsers.string_!"hoge", (x){ return x.length; }), kind)(conv!"!!!!"))
        {
                                     assert(match          == false);
            static if(kind.hasError) assert(error.msg      == "'hoge' expected");
            static if(kind.hasError) assert(error.position == 0);
        }

        static if(kind.hasValue) static assert(!__traits(compiles, parse!(convert!(parsers.string_!"hoge", (size_t x){ return x; }), kind)(conv!"hoge")));
    }
}


template check(alias parser, alias checker, size_t line = 0, string file = "")
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

    foreach(conv; convs) foreach(kind; ParserKinds)
    {
        with(parse!(check!(parsers.string_!"hoge", Function), kind)(conv!"hoge!"))
        {
                                     assert(match              == true);
            static if(kind.hasValue) assert(value              == "hoge");
                                     assert(nextInput.source   == conv!"!");
                                     assert(nextInput.position == 4);
                                     assert(nextInput.line == 0);
        }

        with(parse!(check!(parsers.string_!"hoge!", Function), kind)(conv!"hoge!"))
        {
                                     assert(match          == false);
            static if(kind.hasError) assert(error.msg      == "passing check expected");
            static if(kind.hasError) assert(error.position == 0);
        }

        with(parse!(check!(parsers.string_!"hoge", Function), kind)(conv!"fuga"))
        {
                                     assert(match          == false);
            static if(kind.hasError) assert(error.msg      == "'hoge' expected");
            static if(kind.hasError) assert(error.position == 0);
        }

        static assert(!__traits(compiles, parse!(check!(parsers.string_!"hoge", (int    i  ){ return false; }), kind)(conv!"hoge")));
        static assert(!__traits(compiles, parse!(check!(parsers.string_!"hoge", (string str){ return 0;     }), kind)(conv!"hoge")));
    }
}


template inputSlice(alias parser, size_t line = 0, string file = "")
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
    foreach(conv; convs) foreach(kind; ParserKinds)
    {
        with(parse!(inputSlice!(sequence!(parsers.string_!"hoge", parsers.string_!"fuga")), kind)(conv!"hogefugapiyo"))
        {
                                     assert(match              == true);
            static if(kind.hasValue) assert(value              == conv!"hogefuga");
                                     assert(nextInput.source   == conv!"piyo");
                                     assert(nextInput.position == 8);
                                     assert(nextInput.line     == 0);
        }

        static if(kind.hasValue) static assert(!__traits(compiles, parse!(inputSlice!(parsers.string_!"hoge"), kind)(0)));
    }
}


template memoize(alias parser)
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
    foreach(conv; convs) foreach(kind; ParserKinds)
    {
        with(parse!(memoize!(parsers.string_!"hoge"), kind)(conv!"hogehoge"))
        {
                                     assert(match              == true);
            static if(kind.hasValue) assert(value              == "hoge");
                                     assert(nextInput.source   == conv!"hoge");
                                     assert(nextInput.position == 4);
                                     assert(nextInput.line     == 0);
        }

        with(parse!(memoize!(parsers.string_!"hoge"), kind)(conv!"hogehoge"))
        {
                                     assert(match              == true);
            static if(kind.hasValue) assert(value              == "hoge");
                                     assert(nextInput.source   == conv!"hoge");
                                     assert(nextInput.position == 4);
                                     assert(nextInput.line     == 0);
        }

        with(parse!(memoize!(parsers.string_!"\n\nhoge"), kind)(conv!"\n\nhogehoge"))
        {
                                     assert(match              == true);
            static if(kind.hasValue) assert(value              == "\n\nhoge");
                                     assert(nextInput.source   == conv!"hoge");
                                     assert(nextInput.position == 6);
                                     assert(nextInput.line     == 2);
        }

        with(parse!(memoize!(parsers.string_!"\n\nhoge"), kind)(conv!"\n\nhogehoge"))
        {
                                     assert(match              == true);
            static if(kind.hasValue) assert(value              == "\n\nhoge");
                                     assert(nextInput.source   == conv!"hoge");
                                     assert(nextInput.position == 6);
                                     assert(nextInput.line     == 2);
        }
    }
}


template changeError(alias parser, string errorMsg)
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
    foreach(conv; convs) foreach(kind; ParserKinds)
    {
        with(parse!(changeError!(parsers.string_!"hoge", "エラーだよ！！"), kind)(conv!"hoge"))
        {
            assert(match              == true);
            assert(nextInput.source   == conv!"");
            assert(nextInput.position == 4);
            assert(nextInput.line     == 0);
        }

        with(parse!(changeError!(parsers.string_!"hoge", "エラーだよ！！"), kind)(conv!"fuga"))
        {
                                     assert(match          == false);
            static if(kind.hasError) assert(error.msg      == "エラーだよ！！");
            static if(kind.hasError) assert(error.position == 0);
        }

        with(parse!(changeError!(sequence!(parsers.string_!"hoge", parsers.string_!"fuga"), "エラーだよ！！"), kind)(conv!"hoge"))
        {
                                     assert(match          == false);
            static if(kind.hasError) assert(error.msg      == "エラーだよ！！");
            static if(kind.hasError) assert(error.position == 0);
        }
    }
}


template skip(alias skip, alias parser)
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
    foreach(conv; convs) foreach(kind; ParserKinds)
    {
        with(parse!(skip!(parsers.string_!"\n", parsers.string_!"hoge"), kind)(conv!"hogehoge"))
        {
                                     assert(match              == true);
            static if(kind.hasValue) assert(value              == "hoge");
                                     assert(nextInput.source   == conv!"hoge");
        }

        with(parse!(skip!(parsers.string_!"\n\n", parsers.string_!"hoge"), kind)(conv!"\n\nhogehoge"))
        {
                                     assert(match              == true);
            static if(kind.hasValue) assert(value              == "hoge");
                                     assert(nextInput.source   == conv!"hoge");
        }
    }
}
