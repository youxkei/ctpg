module ctpg.for_unittest;

debug(ctpg) version(unittest):

import std.typetuple : TypeTuple;
import std.traits : Unqual, isArray;
import std.range : ElementEncodingType;

import ctpg.caller : Caller;
import ctpg.input : Input;
import ctpg.macro_ : MAKE_RESULT;
import ctpg.parse_result : ParseResult;


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


template toString    (alias input) { enum toString     =  cast( string)input;            }
template toWstring   (alias input) { enum toWstring    =  cast(wstring)input;            }
template toDstring   (alias input) { enum toDstring    =  cast(dstring)input;            }
template toCharRange (alias input) { enum toCharRange  = (cast( string)input).rangize(); }
template toWcharRange(alias input) { enum toWcharRange = (cast(wstring)input).rangize(); }
template toDcharRange(alias input) { enum toDcharRange = (cast(dstring)input).rangize(); }

alias convs = TypeTuple!(toString, toWstring, toDstring, toCharRange, toWcharRange, toDcharRange);
