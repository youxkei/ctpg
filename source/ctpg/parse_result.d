module ctpg.parse_result;

import std.traits : ReturnType;

import ctpg.error : Error;
import ctpg.input : Input;

struct ParseResult(alias kind, SrcType, T = void)
{
    static if(kind.hasValue) static assert(!is(T == void));
    else                     static assert( is(T == void));

    bool match;
    Input!SrcType nextInput;

    static if(kind.hasValue) T value;
    static if(kind.hasError) Error error;
}


template getParseResultType(alias parser)
{
    static if(is(ReturnType!(parser.parse) == ParseResult!(kind, SrcType, T), SrcType, alias kind, T))
    {
        alias getParseResultType = T;
    }
}
