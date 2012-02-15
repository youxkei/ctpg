// Written in the D programming language.
/++
This module implements a compite-time parser generator.
+/
/*          Copyright youkei 2010 - 2012.
 * Distributed under the Boost Software License, Version 1.0.
 *    (See accompanying file LICENSE_1_0.txt or copy at
 *          http://www.boost.org/LICENSE_1_0.txt)
 */

module youkei.ctpg;

import std.algorithm;
import std.array;
import std.conv;
import std.math;
import std.range;
import std.traits;
import std.typecons;
import std.typetuple;
import std.utf;
import std.functional;

alias Tuple!() None;
alias void*[size_t][size_t][string] memo_t;

//version = memoize;

struct Option(T){
    public{
        bool some;
        T value;

        @property isNull(){
            return !some;
        }

        alias value this;
    }
}

struct Positional(Range){
    static assert(isForwardRange!Range && isSomeChar!(ElementType!Range));

    public{
        Range range;
        size_t line = 1;
        size_t column = 1;

        //cannot apply some qualifiers due to unclearness of Range
        typeof(this) save(){
            return Positional!Range(range.save, line, column);
        }

        pure @safe nothrow
        bool opEquals(typeof(this) rhs){
            return range == rhs.range && line == rhs.line && column == rhs.column;
        }

        bool isEnd(){
            return range.empty;
        }
    }
}

Positional!Range positional(Range)(Range range, size_t line, size_t column){
    return Positional!Range(range, line, column);
}

struct Result(Range, T){
    public{
        bool match;
        T value;
        Positional!Range rest;
        Error error;

        pure @safe nothrow
        void opAssign(U)(Result!(Range, U) rhs)if(isAssignable!(T, U)){
            match = rhs.match;
            value = rhs.value;
            rest = rhs.rest;
            error = rhs.error;
        }
    }
}

struct Error{
    invariant(){
        assert(line >= 1);
        assert(column >= 1);
    }

    public{
        string need;
        int line;
        int column;

        pure @safe nothrow
        bool opEquals(in Error rhs){
            return need == rhs.need && line == rhs.line && column == rhs.column;
        }
    }
}

/* combinators */ version(all){
    /* combinateMemoize */ version(all){
        version(memoize){
            template combinateMemoize(alias parser){
                alias ParserType!parser ResultType;
                Result!(Range, ResultType) apply(Range)(Positional!Range input, ref memo_t memo){
                    auto memo0 = parser.mangleof in memo;
                    if(memo0){
                        auto memo1 = input.line in *memo0;
                        if(memo1){
                            auto memo2 = input.column in *memo1;
                            if(memo2){
                                void* p = *memo2;
                                return *(cast(Result!(Range, ParserType!parser)*)p);
                            }
                        }
                    }
                    auto result = parser.apply(input, memo);
                    memo[parser.mangleof][input.line][input.column] = [result].ptr;
                    return result;
                }
            }
        }else{
            template combinateMemoize(alias parser){
                alias parser combinateMemoize;
            }
        }
    }

    /* combinateUnTuple */ version(all){
        template combinateUnTuple(alias parser){
            alias UnTuple!(ParserType!parser) ResultType;
            Result!(Range, ResultType) apply(Range)(Positional!Range input, ref memo_t memo){
                typeof(return) result;
                auto r = parser.apply(input, memo);
                static if(isTuple!(ParserType!parser) && ParserType!parser.Types.length == 1){
                    result.match = r.match;
                    result.value = r.value[0];
                    result.rest = r.rest;
                    result.error = r.error;
                }else{
                    result = r;
                }
                return result;
            }
        }

        debug(ctpg) unittest{
            enum dg = {
                assert(getResult!(combinateUnTuple!(TestParser!int))("").value == 0);
                assert(getResult!(combinateUnTuple!(TestParser!long))("").value == 0);
                assert(getResult!(combinateUnTuple!(TestParser!string))("").value == "");
                assert(getResult!(combinateUnTuple!(TestParser!wstring))("").value == ""w);
                assert(getResult!(combinateUnTuple!(TestParser!dstring))("").value == ""d);
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(int))))("").value == 0);
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(int, int))))("").value == tuple(0, 0));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!(int)))))("").value == tuple(0));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!(int, int)))))("").value == tuple(0, 0));
                assert(getResult!(combinateUnTuple!(TestParser!(Tuple!(Tuple!(int, int), int))))("").value == tuple(tuple(0, 0), 0));
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        }
    }

    /* combinateString */ version(all){
        template combinateString(alias parser){
            alias string ResultType;
            Result!(Range, ResultType) apply(Range)(Positional!Range input, ref memo_t memo){
                typeof(return) result;
                auto r = parser.apply(input, memo);
                if(r.match){
                    result.match = true;
                    result.value = flat(r.value);
                    result.rest = r.rest;
                }else{
                    result.error = r.error;
                }
                return result;
            }
        }
    }

    /* combinateSequence */ version(all){
        template combinateSequence(parsers...){
            alias combinateUnTuple!(combinateSequenceImpl!(parsers)) combinateSequence;
        }

        private template combinateSequenceImpl(parsers...){
            alias CombinateSequenceImplType!(parsers) ResultType;
            Result!(Range, ResultType) apply(Range)(Positional!Range input, ref memo_t memo){
                typeof(return) result;
                static if(parsers.length == 1){
                    auto r = parsers[0].apply(input, memo);
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
                    auto r1 = parsers[0].apply(input, memo);
                    if(r1.match){
                        auto r2 = combinateSequenceImpl!(parsers[1..$]).apply(r1.rest, memo);
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

        debug(ctpg) unittest{
            enum dg = {
                /* "hello" "world"       <= "helloworld"  */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))("helloworld");
                        assert(result.match);
                        assert(result.value == tuple("hello", "world"));
                        assert(result.rest == positional("", 1, 11));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))("helloworld"w);
                        assert(result.match);
                        assert(result.value == tuple("hello", "world"));
                        assert(result.rest == positional(""w, 1, 11));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))("helloworld"d);
                        assert(result.match);
                        assert(result.value == tuple("hello", "world"));
                        assert(result.rest == positional(""d, 1, 11));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))(testRange("helloworld"));
                        assert(result.match);
                        assert(result.value == tuple("hello", "world"));
                        assert(result.rest == positional(testRange(""), 1, 11));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))(testRange("helloworld"w));
                        assert(result.match);
                        assert(result.value == tuple("hello", "world"));
                        assert(result.rest == positional(testRange(""w), 1, 11));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))(testRange("helloworld"d));
                        assert(result.match);
                        assert(result.value == tuple("hello", "world"));
                        assert(result.rest == positional(testRange(""d), 1, 11));
                    }}
                }
                /* ("hello" "world") "!" <= "helloworld!" */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(combinateSequence!(combinateSequence!(parseString!("hello"), parseString!("world")), parseString!"!"))("helloworld!");
                        assert(result.match);
                        assert(result.value == tuple("hello", "world", "!"));
                        assert(result.rest == positional("", 1, 12));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(combinateSequence!(combinateSequence!(parseString!("hello"), parseString!("world")), parseString!"!"))("helloworld!"w);
                        assert(result.match);
                        assert(result.value == tuple("hello", "world", "!"));
                        assert(result.rest == positional(""w, 1, 12));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(combinateSequence!(combinateSequence!(parseString!("hello"), parseString!("world")), parseString!"!"))("helloworld!"d);
                        assert(result.match);
                        assert(result.value == tuple("hello", "world", "!"));
                        assert(result.rest == positional(""d, 1, 12));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(combinateSequence!(combinateSequence!(parseString!("hello"), parseString!("world")), parseString!"!"))(testRange("helloworld!"));
                        assert(result.match);
                        assert(result.value == tuple("hello", "world", "!"));
                        assert(result.rest == positional(testRange(""), 1, 12));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(combinateSequence!(combinateSequence!(parseString!("hello"), parseString!("world")), parseString!"!"))(testRange("helloworld!"w));
                        assert(result.match);
                        assert(result.value == tuple("hello", "world", "!"));
                        assert(result.rest == positional(testRange(""w), 1, 12));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(combinateSequence!(combinateSequence!(parseString!("hello"), parseString!("world")), parseString!"!"))(testRange("helloworld!"d));
                        assert(result.match);
                        assert(result.value == tuple("hello", "world", "!"));
                        assert(result.rest == positional(testRange(""d), 1, 12));
                    }}
                }
                /* "hello" "world"       <= "hellovvorld" */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))("hellovvorld");
                        assert(!result.match);
                        assert(result.error == Error(q{"world"}, 1, 6));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))("hellovvorld"w);
                        assert(!result.match);
                        assert(result.error == Error(q{"world"}, 1, 6));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))("hellovvorld"d);
                        assert(!result.match);
                        assert(result.error == Error(q{"world"}, 1, 6));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))(testRange("hellovvorld"));
                        assert(!result.match);
                        assert(result.error == Error(q{"world"}, 1, 6));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))(testRange("hellovvorld"w));
                        assert(!result.match);
                        assert(result.error == Error(q{"world"}, 1, 6));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(combinateSequence!(parseString!("hello"), parseString!("world")))(testRange("hellovvorld"d));
                        assert(!result.match);
                        assert(result.error == Error(q{"world"}, 1, 6));
                    }}
                }
                /* "hello" "world" "!"   <= "helloworld?" */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(combinateSequence!(parseString!("hello"), parseString!("world"), parseString!("!")))("helloworld?");
                        assert(!result.match);
                        assert(result.error == Error(q{"!"}, 1, 11));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(combinateSequence!(parseString!("hello"), parseString!("world"), parseString!("!")))("helloworld?"w);
                        assert(!result.match);
                        assert(result.error == Error(q{"!"}, 1, 11));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(combinateSequence!(parseString!("hello"), parseString!("world"), parseString!("!")))("helloworld?"d);
                        assert(!result.match);
                        assert(result.error == Error(q{"!"}, 1, 11));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(combinateSequence!(parseString!("hello"), parseString!("world"), parseString!("!")))(testRange("helloworld?"));
                        assert(!result.match);
                        assert(result.error == Error(q{"!"}, 1, 11));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(combinateSequence!(parseString!("hello"), parseString!("world"), parseString!("!")))(testRange("helloworld?"w));
                        assert(!result.match);
                        assert(result.error == Error(q{"!"}, 1, 11));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(combinateSequence!(parseString!("hello"), parseString!("world"), parseString!("!")))(testRange("helloworld?"d));
                        assert(!result.match);
                        assert(result.error == Error(q{"!"}, 1, 11));
                    }}
                }
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        }
    }

    /* combinateChoice */ version(all){
        template combinateChoice(parsers...){
            alias CommonParserType!(parsers) ResultType;
            Result!(Range, ResultType) apply(Range)(Positional!Range input, ref memo_t memo){
                static assert(parsers.length > 0);
                static if(parsers.length == 1){
                    return parsers[0].apply(input, memo);
                }else{
                    typeof(return) result;
                    auto r1 = parsers[0].apply(input.save, memo);
                    if(r1.match){
                        result = r1;
                        return result;
                    }else{
                        result.error = r1.error;
                    }
                    auto r2 = combinateChoice!(parsers[1..$]).apply(input, memo);
                    if(r2.match){
                        result = r2;
                        return result;
                    }else{
                        result.error.need ~= " or " ~ r2.error.need;
                    }
                    return result;
                }
            }
        }

        debug(ctpg) unittest{
            enum dg = {
                /* "h" / "w" <= "hw" */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(combinateChoice!(parseString!"h", parseString!"w"))("hw");
                        assert(result.match);
                        assert(result.value == "h");
                        assert(result.rest == positional("w", 1, 2));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(combinateChoice!(parseString!"h", parseString!"w"))("hw"w);
                        assert(result.match);
                        assert(result.value == "h");
                        assert(result.rest == positional("w"w, 1, 2));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(combinateChoice!(parseString!"h", parseString!"w"))("hw"d);
                        assert(result.match);
                        assert(result.value == "h");
                        assert(result.rest == positional("w"d, 1, 2));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(combinateChoice!(parseString!"h", parseString!"w"))(testRange("hw"));
                        assert(result.match);
                        assert(result.value == "h");
                        assert(result.rest == positional(testRange("w"), 1, 2));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(combinateChoice!(parseString!"h", parseString!"w"))(testRange("hw"w));
                        assert(result.match);
                        assert(result.value == "h");
                        assert(result.rest == positional(testRange("w"w), 1, 2));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(combinateChoice!(parseString!"h", parseString!"w"))(testRange("hw"d));
                        assert(result.match);
                        assert(result.value == "h");
                        assert(result.rest == positional(testRange("w"d), 1, 2));
                    }}
                }
                /* "h" / "w" <= "w"  */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(combinateChoice!(parseString!"h", parseString!"w"))("w");
                        assert(result.match);
                        assert(result.value == "w");
                        assert(result.rest == positional("", 1, 2));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(combinateChoice!(parseString!"h", parseString!"w"))("w");
                        assert(result.match);
                        assert(result.value == "w");
                        assert(result.rest == positional("", 1, 2));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(combinateChoice!(parseString!"h", parseString!"w"))("w");
                        assert(result.match);
                        assert(result.value == "w");
                        assert(result.rest == positional("", 1, 2));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(combinateChoice!(parseString!"h", parseString!"w"))(testRange("w"));
                        assert(result.match);
                        assert(result.value == "w");
                        assert(result.rest == positional(testRange(""), 1, 2));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(combinateChoice!(parseString!"h", parseString!"w"))(testRange("w"w));
                        assert(result.match);
                        assert(result.value == "w");
                        assert(result.rest == positional(testRange(""w), 1, 2));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(combinateChoice!(parseString!"h", parseString!"w"))(testRange("w"d));
                        assert(result.match);
                        assert(result.value == "w");
                        assert(result.rest == positional(testRange(""d), 1, 2));
                    }}
                }
                /* "h" / "w" <= ""   */ version(all){{
                    /* string          */ version(all){{
                        auto result = getResult!(combinateChoice!(parseString!"h", parseString!"w"))("");
                        assert(!result.match);
                        assert(result.error == Error(q{"h" or "w"}, 1, 1));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(combinateChoice!(parseString!"h", parseString!"w"))(""w);
                        assert(!result.match);
                        assert(result.error == Error(q{"h" or "w"}, 1, 1));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(combinateChoice!(parseString!"h", parseString!"w"))(""d);
                        assert(!result.match);
                        assert(result.error == Error(q{"h" or "w"}, 1, 1));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(combinateChoice!(parseString!"h", parseString!"w"))(testRange(""));
                        assert(!result.match);
                        assert(result.error == Error(q{"h" or "w"}, 1, 1));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(combinateChoice!(parseString!"h", parseString!"w"))(testRange(""w));
                        assert(!result.match);
                        assert(result.error == Error(q{"h" or "w"}, 1, 1));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(combinateChoice!(parseString!"h", parseString!"w"))(testRange(""d));
                        assert(!result.match);
                        assert(result.error == Error(q{"h" or "w"}, 1, 1));
                    }}
                }}
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        }
    }

    /* combinateMore */ version(all){
        template combinateMore(int n, alias parser, alias sep){
            alias ParserType!(parser)[] ResultType;
            Result!(Range, ResultType) apply(Range)(Positional!Range input, ref memo_t memo){
                typeof(return) result;
                Positional!Range rest = input;
                while(true){
                    auto r1 = parser.apply(rest.save, memo);
                    if(r1.match){
                        result.value = result.value ~ r1.value;
                        rest = r1.rest;
                        auto r2 = sep.apply(rest.save, memo);
                        if(r2.match){
                            rest = r2.rest;
                        }else{
                            break;
                        }
                    }else{
                        result.error = r1.error;
                        break;
                    }
                }
                if(result.value.length >= n){
                    result.match = true;
                    result.rest = rest;
                }
                return result;
            }
        }

        template combinateMore0(alias parser, alias sep = parseNone!()){
            alias combinateMore!(0, parser, sep) combinateMore0;
        }

        template combinateMore1(alias parser, alias sep = parseNone!()){
            alias combinateMore!(1, parser, sep) combinateMore1;
        }

        debug(ctpg) unittest{
            enum dg = {
                /* "w"* <= "www w" */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(combinateMore0!(parseString!"w"))("www w");
                        assert(result.match);
                        assert(result.value == ["w", "w", "w"]);
                        assert(result.rest == positional(" w", 1, 4));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(combinateMore0!(parseString!"w"))("www w"w);
                        assert(result.match);
                        assert(result.value == ["w", "w", "w"]);
                        assert(result.rest == positional(" w"w, 1, 4));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(combinateMore0!(parseString!"w"))("www w"d);
                        assert(result.match);
                        assert(result.value == ["w", "w", "w"]);
                        assert(result.rest == positional(" w"d, 1, 4));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(combinateMore0!(parseString!"w"))(testRange("www w"));
                        assert(result.match);
                        assert(result.value == ["w", "w", "w"]);
                        assert(result.rest == positional(testRange(" w"), 1, 4));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(combinateMore0!(parseString!"w"))(testRange("www w"w));
                        assert(result.match);
                        assert(result.value == ["w", "w", "w"]);
                        assert(result.rest == positional(testRange(" w"w), 1, 4));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(combinateMore0!(parseString!"w"))(testRange("www w"d));
                        assert(result.match);
                        assert(result.value == ["w", "w", "w"]);
                        assert(result.rest == positional(testRange(" w"d), 1, 4));
                    }}
                }
                /* "w"* <= " w"    */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(combinateString!(combinateMore0!(parseString!"w")))(" w");
                        assert(result.match);
                        assert(result.value == []);
                        assert(result.rest == positional(" w", 1, 1));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(combinateString!(combinateMore0!(parseString!"w")))(" w"w);
                        assert(result.match);
                        assert(result.value == []);
                        assert(result.rest == positional(" w"w, 1, 1));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(combinateString!(combinateMore0!(parseString!"w")))(" w"d);
                        assert(result.match);
                        assert(result.value == []);
                        assert(result.rest == positional(" w"d, 1, 1));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(combinateString!(combinateMore0!(parseString!"w")))(testRange(" w"));
                        assert(result.match);
                        assert(result.value == []);
                        assert(result.rest == positional(testRange(" w"), 1, 1));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(combinateString!(combinateMore0!(parseString!"w")))(testRange(" w"w));
                        assert(result.match);
                        assert(result.value == []);
                        assert(result.rest == positional(testRange(" w"w), 1, 1));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(combinateString!(combinateMore0!(parseString!"w")))(testRange(" w"d));
                        assert(result.match);
                        assert(result.value == []);
                        assert(result.rest == positional(testRange(" w"d), 1, 1));
                    }}
                }
                /* "w"+ <= "www w" */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(combinateMore1!(parseString!"w"))("www w");
                        assert(result.match);
                        assert(result.value == ["w", "w", "w"]);
                        assert(result.rest == positional(" w", 1, 4));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(combinateMore1!(parseString!"w"))("www w"w);
                        assert(result.match);
                        assert(result.value == ["w", "w", "w"]);
                        assert(result.rest == positional(" w"w, 1, 4));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(combinateMore1!(parseString!"w"))("www w"d);
                        assert(result.match);
                        assert(result.value == ["w", "w", "w"]);
                        assert(result.rest == positional(" w"d, 1, 4));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(combinateMore1!(parseString!"w"))(testRange("www w"));
                        assert(result.match);
                        assert(result.value == ["w", "w", "w"]);
                        assert(result.rest == positional(testRange(" w"), 1, 4));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(combinateMore1!(parseString!"w"))(testRange("www w"w));
                        assert(result.match);
                        assert(result.value == ["w", "w", "w"]);
                        assert(result.rest == positional(testRange(" w"w), 1, 4));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(combinateMore1!(parseString!"w"))(testRange("www w"d));
                        assert(result.match);
                        assert(result.value == ["w", "w", "w"]);
                        assert(result.rest == positional(testRange(" w"d), 1, 4));
                    }}
                }
                /* "w"+ <= " w"    */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(combinateString!(combinateMore1!(parseString!"w")))(" w");
                        assert(!result.match);
                        assert(result.error == Error(q{"w"}, 1, 1));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(combinateString!(combinateMore1!(parseString!"w")))(" w"w);
                        assert(!result.match);
                        assert(result.error == Error(q{"w"}, 1, 1));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(combinateString!(combinateMore1!(parseString!"w")))(" w"d);
                        assert(!result.match);
                        assert(result.error == Error(q{"w"}, 1, 1));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(combinateString!(combinateMore1!(parseString!"w")))(testRange(" w"));
                        assert(!result.match);
                        assert(result.error == Error(q{"w"}, 1, 1));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(combinateString!(combinateMore1!(parseString!"w")))(testRange(" w"w));
                        assert(!result.match);
                        assert(result.error == Error(q{"w"}, 1, 1));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(combinateString!(combinateMore1!(parseString!"w")))(testRange(" w"d));
                        assert(!result.match);
                        assert(result.error == Error(q{"w"}, 1, 1));
                    }}
                }
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        }
    }

    /* combinateOption */ version(all){
        template combinateOption(alias parser){
            alias Option!(ParserType!parser) ResultType;
            Result!(Range, ResultType) apply(Range)(Positional!Range input, ref memo_t memo){
                typeof(return) result;
                result.match = true;
                auto r = parser.apply(input.save, memo);
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

        debug(ctpg) unittest{
            enum dg = {
                /* "w"? <= "w"    */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(combinateOption!(parseString!"w"))("w");
                        assert(result.match);
                        assert(result.value == "w");
                        assert(result.rest == positional("", 1, 2));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(combinateOption!(parseString!"w"))("w"w);
                        assert(result.match);
                        assert(result.value == "w");
                        assert(result.rest == positional(""w, 1, 2));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(combinateOption!(parseString!"w"))("w"d);
                        assert(result.match);
                        assert(result.value == "w");
                        assert(result.rest == positional(""d, 1, 2));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(combinateOption!(parseString!"w"))(testRange("w"));
                        assert(result.match);
                        assert(result.value == "w");
                        assert(result.rest == positional(testRange(""), 1, 2));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(combinateOption!(parseString!"w"))(testRange("w"w));
                        assert(result.match);
                        assert(result.value == "w");
                        assert(result.rest == positional(testRange(""w), 1, 2));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(combinateOption!(parseString!"w"))(testRange("w"d));
                        assert(result.match);
                        assert(result.value == "w");
                        assert(result.rest == positional(testRange(""d), 1, 2));
                    }}
                }
                /* "w"? <= "hoge" */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(combinateOption!(parseString!"w"))("hoge");
                        assert(result.match);
                        assert(result.value.isNull);
                        assert(result.rest == positional("hoge", 1, 1));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(combinateOption!(parseString!"w"))("hoge"w);
                        assert(result.match);
                        assert(result.value.isNull);
                        assert(result.rest == positional("hoge"w, 1, 1));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(combinateOption!(parseString!"w"))("hoge"d);
                        assert(result.match);
                        assert(result.value.isNull);
                        assert(result.rest == positional("hoge"d, 1, 1));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(combinateOption!(parseString!"w"))(testRange("hoge"));
                        assert(result.match);
                        assert(result.value.isNull);
                        assert(result.rest == positional(testRange("hoge"), 1, 1));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(combinateOption!(parseString!"w"))(testRange("hoge"w));
                        assert(result.match);
                        assert(result.value.isNull);
                        assert(result.rest == positional(testRange("hoge"w), 1, 1));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(combinateOption!(parseString!"w"))(testRange("hoge"d));
                        assert(result.match);
                        assert(result.value.isNull);
                        assert(result.rest == positional(testRange("hoge"d), 1, 1));
                    }}
                }
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        }
    }

    /* combinateNone */ version(all){
        template combinateNone(alias parser){
            alias None ResultType;
            Result!(Range, ResultType) apply(Range)(Positional!Range input, ref memo_t memo){
                typeof(return) result;
                auto r = parser.apply(input, memo);
                if(r.match){
                    result.match = true;
                    result.rest = r.rest;
                }else{
                    result.error = r.error;
                }
                return result;
            }
        }

        debug(ctpg) unittest{
            enum dg = {
                /* !"(" "w" !")" <= "(w)" */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))("(w)");
                        assert(result.match);
                        assert(result.value == "w");
                        assert(result.rest == positional("", 1, 4));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))("(w)"w);
                        assert(result.match);
                        assert(result.value == "w");
                        assert(result.rest == positional(""w, 1, 4));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))("(w)"d);
                        assert(result.match);
                        assert(result.value == "w");
                        assert(result.rest == positional(""d, 1, 4));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))(testRange("(w)"));
                        assert(result.match);
                        assert(result.value == "w");
                        assert(result.rest == positional(testRange(""), 1, 4));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))(testRange("(w)"w));
                        assert(result.match);
                        assert(result.value == "w");
                        assert(result.rest == positional(testRange(""w), 1, 4));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))(testRange("(w)"d));
                        assert(result.match);
                        assert(result.value == "w");
                        assert(result.rest == positional(testRange(""d), 1, 4));
                    }}
                }
                /* !"(" "w" !")" <= "(w}" */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))("(w}");
                        assert(!result.match);
                        assert(result.error == Error(q{")"}, 1, 3));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))("(w}"w);
                        assert(!result.match);
                        assert(result.error == Error(q{")"}, 1, 3));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))("(w}"d);
                        assert(!result.match);
                        assert(result.error == Error(q{")"}, 1, 3));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))(testRange("(w}"));
                        assert(!result.match);
                        assert(result.error == Error(q{")"}, 1, 3));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))(testRange("(w}"w));
                        assert(!result.match);
                        assert(result.error == Error(q{")"}, 1, 3));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")))(testRange("(w}"d));
                        assert(!result.match);
                        assert(result.error == Error(q{")"}, 1, 3));
                    }}
                }
                /* !"w"          <= "a"   */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(combinateNone!(parseString!"w"))("a");
                        assert(!result.match);
                        assert(result.error == Error(q{"w"}, 1, 1));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(combinateNone!(parseString!"w"))("a"w);
                        assert(!result.match);
                        assert(result.error == Error(q{"w"}, 1, 1));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(combinateNone!(parseString!"w"))("a"d);
                        assert(!result.match);
                        assert(result.error == Error(q{"w"}, 1, 1));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(combinateNone!(parseString!"w"))(testRange("a"));
                        assert(!result.match);
                        assert(result.error == Error(q{"w"}, 1, 1));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(combinateNone!(parseString!"w"))(testRange("a"w));
                        assert(!result.match);
                        assert(result.error == Error(q{"w"}, 1, 1));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(combinateNone!(parseString!"w"))(testRange("a"d));
                        assert(!result.match);
                        assert(result.error == Error(q{"w"}, 1, 1));
                    }}
                }
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        }
    }

    /* combinateAnd */ version(all){
        template combinateAnd(alias parser){
            alias None ResultType;
            Result!(Range, ResultType) apply(Range)(Positional!Range input, ref memo_t memo){
                typeof(return) result;
                result.rest = input;
                version(all){
                    auto r = parser.apply(input, memo);
                    result.match = r.match;
                    result.error = r.error;
                }
                version(none) result.match = parser.apply(input, memo).match;
                return result;
            }
        }

        debug(ctpg) unittest{
            enum dg = {
                /* &"w"        <= "www" */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(combinateAnd!(parseString!"w"))("www");
                        assert(result.match);
                        assert(result.value == None());
                        assert(result.rest == positional("www", 1, 1));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(combinateAnd!(parseString!"w"))("www"w);
                        assert(result.match);
                        assert(result.value == None());
                        assert(result.rest == positional("www"w, 1, 1));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(combinateAnd!(parseString!"w"))("www"d);
                        assert(result.match);
                        assert(result.value == None());
                        assert(result.rest == positional("www"d, 1, 1));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(combinateAnd!(parseString!"w"))(testRange("www"));
                        assert(result.match);
                        assert(result.value == None());
                        assert(result.rest == positional(testRange("www"), 1, 1));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(combinateAnd!(parseString!"w"))(testRange("www"w));
                        assert(result.match);
                        assert(result.value == None());
                        assert(result.rest == positional(testRange("www"w), 1, 1));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(combinateAnd!(parseString!"w"))(testRange("www"d));
                        assert(result.match);
                        assert(result.value == None());
                        assert(result.rest == positional(testRange("www"d), 1, 1));
                    }}
                }
                /* "w" &"w"    <= "www" */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(combinateSequence!(parseString!"w", combinateAnd!(parseString!"w")))("www");
                        assert(result.match);
                        assert(result.value == "w");
                        assert(result.rest == positional("ww", 1, 2));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(combinateSequence!(parseString!"w", combinateAnd!(parseString!"w")))("www"w);
                        assert(result.match);
                        assert(result.value == "w");
                        assert(result.rest == positional("ww"w, 1, 2));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(combinateSequence!(parseString!"w", combinateAnd!(parseString!"w")))("www"d);
                        assert(result.match);
                        assert(result.value == "w");
                        assert(result.rest == positional("ww"d, 1, 2));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(combinateSequence!(parseString!"w", combinateAnd!(parseString!"w")))(testRange("www"));
                        assert(result.match);
                        assert(result.value == "w");
                        assert(result.rest == positional(testRange("ww"), 1, 2));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(combinateSequence!(parseString!"w", combinateAnd!(parseString!"w")))(testRange("www"w));
                        assert(result.match);
                        assert(result.value == "w");
                        assert(result.rest == positional(testRange("ww"w), 1, 2));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(combinateSequence!(parseString!"w", combinateAnd!(parseString!"w")))(testRange("www"d));
                        assert(result.match);
                        assert(result.value == "w");
                        assert(result.rest == positional(testRange("ww"d), 1, 2));
                    }}
                }
                /* ("w" &"w")+ <= "www" */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(combinateMore1!(combinateSequence!(parseString!"w", combinateAnd!(parseString!"w"))))("www");
                        assert(result.match);
                        assert(result.value == ["w", "w"]);
                        assert(result.rest == positional("w", 1, 3));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(combinateMore1!(combinateSequence!(parseString!"w", combinateAnd!(parseString!"w"))))("www"w);
                        assert(result.match);
                        assert(result.value == ["w", "w"]);
                        assert(result.rest == positional("w"w, 1, 3));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(combinateMore1!(combinateSequence!(parseString!"w", combinateAnd!(parseString!"w"))))("www"d);
                        assert(result.match);
                        assert(result.value == ["w", "w"]);
                        assert(result.rest == positional("w"d, 1, 3));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(combinateMore1!(combinateSequence!(parseString!"w", combinateAnd!(parseString!"w"))))(testRange("www"));
                        assert(result.match);
                        assert(result.value == ["w", "w"]);
                        assert(result.rest == positional(testRange("w"), 1, 3));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(combinateMore1!(combinateSequence!(parseString!"w", combinateAnd!(parseString!"w"))))(testRange("www"w));
                        assert(result.match);
                        assert(result.value == ["w", "w"]);
                        assert(result.rest == positional(testRange("w"w), 1, 3));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(combinateMore1!(combinateSequence!(parseString!"w", combinateAnd!(parseString!"w"))))(testRange("www"d));
                        assert(result.match);
                        assert(result.value == ["w", "w"]);
                        assert(result.rest == positional(testRange("w"d), 1, 3));
                    }}
                }
                /* ("w" &"w")+ <= "w"   */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(combinateMore1!(combinateSequence!(parseString!"w", combinateAnd!(parseString!"w"))))("w");
                        assert(!result.match);
                        assert(result.error == Error(q{"w"}, 1, 2));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(combinateMore1!(combinateSequence!(parseString!"w", combinateAnd!(parseString!"w"))))("w"w);
                        assert(!result.match);
                        assert(result.error == Error(q{"w"}, 1, 2));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(combinateMore1!(combinateSequence!(parseString!"w", combinateAnd!(parseString!"w"))))("w"d);
                        assert(!result.match);
                        assert(result.error == Error(q{"w"}, 1, 2));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(combinateMore1!(combinateSequence!(parseString!"w", combinateAnd!(parseString!"w"))))(testRange("w"));
                        assert(!result.match);
                        assert(result.error == Error(q{"w"}, 1, 2));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(combinateMore1!(combinateSequence!(parseString!"w", combinateAnd!(parseString!"w"))))(testRange("w"w));
                        assert(!result.match);
                        assert(result.error == Error(q{"w"}, 1, 2));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(combinateMore1!(combinateSequence!(parseString!"w", combinateAnd!(parseString!"w"))))(testRange("w"d));
                        assert(!result.match);
                        assert(result.error == Error(q{"w"}, 1, 2));
                    }}
                }
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        }
    }

    /* combinateNot */ version(all){
        template combinateNot(alias parser){
            alias None ResultType;
            Result!(Range, ResultType) apply(Range)(Positional!Range input, ref memo_t memo){
                typeof(return) result;
                result.rest = input;
                result.match = !parser.apply(input.save, memo).match;
                return result;
            }
        }

        debug(ctpg) unittest{
            enum dg = {
                /* ("w" ^"s")+ <= "wwws" */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(combinateMore1!(combinateSequence!(parseString!"w", combinateNot!(parseString!"s"))))("wwws");
                        assert(result.match);
                        assert(result.value == ["w", "w"]);
                        assert(result.rest == positional("ws", 1, 3));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(combinateMore1!(combinateSequence!(parseString!"w", combinateNot!(parseString!"s"))))("wwws"w);
                        assert(result.match);
                        assert(result.value == ["w", "w"]);
                        assert(result.rest == positional("ws"w, 1, 3));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(combinateMore1!(combinateSequence!(parseString!"w", combinateNot!(parseString!"s"))))("wwws"d);
                        assert(result.match);
                        assert(result.value == ["w", "w"]);
                        assert(result.rest == positional("ws"d, 1, 3));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(combinateMore1!(combinateSequence!(parseString!"w", combinateNot!(parseString!"s"))))(testRange("wwws"));
                        assert(result.match);
                        assert(result.value == ["w", "w"]);
                        assert(result.rest == positional(testRange("ws"), 1, 3));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(combinateMore1!(combinateSequence!(parseString!"w", combinateNot!(parseString!"s"))))(testRange("wwws"w));
                        assert(result.match);
                        assert(result.value == ["w", "w"]);
                        assert(result.rest == positional(testRange("ws"w), 1, 3));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(combinateMore1!(combinateSequence!(parseString!"w", combinateNot!(parseString!"s"))))(testRange("wwws"d));
                        assert(result.match);
                        assert(result.value == ["w", "w"]);
                        assert(result.rest == positional(testRange("ws"d), 1, 3));
                    }}
                }
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        }
    }

    /* combinateConvert */ version(all){
        template CombinateConvertType(alias converter){
            static if(isCallable!converter){
                alias ReturnType!converter CombinateConvertType;
            }else static if(is(converter == struct) || is(converter == class)){
                alias converter CombinateConvertType;
            }
        }

        template combinateConvert(alias parser, alias converter){
            alias CombinateConvertType!converter ResultType;
            Result!(Range, ResultType) apply(Range)(Positional!Range input, ref memo_t memo){
                typeof(return) result;
                auto r = parser.apply(input, memo);
                if(r.match){
                    result.match = true;
                    static if(isTuple!(ParserType!parser)){
                        static if(__traits(compiles, converter(r.value.field))){
                            result.value = converter(r.value.field);
                        }else static if(__traits(compiles, new converter(r.value.field))){
                            result.value = new converter(r.value.field);
                        }else{
                            static assert(false, converter.mangleof ~ " cannot call with argument type " ~ typeof(r.value.field).stringof);
                        }
                    }else{
                        static if(__traits(compiles, converter(r.value))){
                            result.value = converter(r.value);
                        }else static if(__traits(compiles, new converter(r.value))){
                            result.value = new converter(r.value);
                        }else{
                            static assert(false, converter.mangleof ~ " cannot call with argument type " ~ typeof(r.value).stringof);
                        }
                    }
                    result.rest = r.rest;
                }else{
                    result.error = r.error;
                }
                return result;
            }
        }

        debug(ctpg) unittest{
            enum dg = {
                version(all){{
                    auto result = getResult!(
                        combinateConvert!(
                            combinateMore1!(parseString!"w"),
                            function(string[] ws)@safe pure nothrow{
                                return ws.length;
                            }
                        )
                    )("www");
                    assert(result.match);
                    assert(result.rest.range == "");
                    assert(result.value == 3);
                }}
                version(all){{
                    auto result = getResult!(
                        combinateConvert!(
                            combinateMore1!(parseString!"w"),
                            function(string[] ws)@safe pure nothrow{
                                return ws.length;
                            }
                        )
                    )("a");
                    assert(!result.match);
                    assert(result.error.need == q{"w"});
                    assert(result.error.line == 1);
                    assert(result.error.column == 1);
                }}
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        }
    }

    /* combinateCheck */ version(all){
        template combinateCheck(alias parser, alias checker){
            alias ParserType!parser ResultType;
            Result!(Range, ResultType) apply(Range)(Positional!Range input, ref memo_t memo){
                typeof(return) result;
                auto r = parser.apply(input, memo);
                if(r.match){
                    if(checker(r.value)){
                        result = r;
                    }else{
                        result.error = Error("passing check", input.line, input.column);
                    }
                }else{
                    result.error = r.error;
                }
                return result;
            }
        }

        debug(ctpg) unittest{
            enum dg = {
                version(all){{
                    auto result = getResult!(
                        combinateString!(
                            combinateCheck!(
                                combinateMore0!(parseString!"w"),
                                function(string[] ws){
                                    return ws.length == 5;
                                }
                            )
                        )
                    )("wwwww");
                    assert(result.match);
                    assert(result.value == "wwwww");
                    assert(result.rest.range == "");
                }}
                version(all){{
                    auto result = getResult!(
                        combinateString!(
                            combinateCheck!(
                                combinateMore0!(parseString!"w"),
                                function(string[] ws){
                                    return ws.length == 5;
                                }
                            )
                        )
                    )("wwww");
                    assert(!result.match);
                    assert(result.error.need == "passing check");
                    assert(result.error.line == 1);
                    assert(result.error.column == 1);
                }}
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        }
    }
}

/* parsers */ version(all){
    /* parseNone */ version(all){
        template parseNone(){
            alias None ResultType;
            Result!(Range, ResultType) apply(Range)(Positional!Range input, ref memo_t memo){
                typeof(return) result;
                result.match = true;
                result.rest = input;
                return result;
            }
        }

        debug(ctpg) unittest{
            enum ldg = {
                /* \0 <= "hoge" */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(parseNone!())("hoge");
                        assert(result.match);
                        assert(result.rest == positional("hoge", 1, 1));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(parseNone!())("hoge"w);
                        assert(result.match);
                        assert(result.rest == positional("hoge"w, 1, 1));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(parseNone!())("hoge"d);
                        assert(result.match);
                        assert(result.rest == positional("hoge"d, 1, 1));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(parseNone!())(testRange("hoge"));
                        assert(result.match);
                        assert(result.rest == positional(testRange("hoge"), 1, 1));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(parseNone!())(testRange("hoge"w));
                        assert(result.match);
                        assert(result.rest == positional(testRange("hoge"w), 1, 1));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(parseNone!())(testRange("hoge"d));
                        assert(result.match);
                        assert(result.rest == positional(testRange("hoge"d), 1, 1));
                    }}
                }
                return true;
            };
            debug(ctpg_ct) static assert(ldg());
            ldg();
        }
    }

    /* parseString */ version(all){
        template parseString(string str) if(str.length > 0){
            alias string ResultType;
            Result!(Range, ResultType) apply(Range)(Positional!Range ainput, ref memo_t memo){
                auto input = ainput;
                enum breadth = countBreadth(str);
                enum convertedString = staticConvertString!(str, Range);
                typeof(return) result;
                static if(isSomeString!Range){
                    if(input.range.length >= convertedString.length && convertedString == input.range[0..convertedString.length]){
                        result.match = true;
                        result.value = str;
                        result.rest.range = input.range[convertedString.length..$];
                        result.rest.line = input.line + breadth.line;
                        result.rest.column = input.column + breadth.column;
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
                    result.rest.line = input.line + breadth.line;
                    result.rest.column = input.column + breadth.column;
                    return result;
                }
            Lerror:
                result.error = Error('"' ~ str ~ '"', input.line, input.column);
                return result;
            }
        }

        debug(ctpg) unittest{
            enum dg = {
                /* "hello"    <= "hello world"        */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(parseString!"hello")("hello world");
                        assert(result.match);
                        assert(result.value == "hello");
                        assert(result.rest == positional(" world", 1, 6));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(parseString!"hello")("hello world"w);
                        assert(result.match);
                        assert(result.value == "hello");
                        assert(result.rest == positional(" world"w, 1, 6));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(parseString!"hello")("hello world"d);
                        assert(result.match);
                        assert(result.value == "hello");
                        assert(result.rest == positional(" world"d, 1, 6));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(parseString!"hello")(testRange("hello world"));
                        assert(result.match);
                        assert(result.value == "hello");
                        assert(result.rest == positional(testRange(" world"), 1, 6));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(parseString!"hello")(testRange("hello world"w));
                        assert(result.match);
                        assert(result.value == "hello");
                        assert(result.rest == positional(testRange(" world"w), 1, 6));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(parseString!"hello")(testRange("hello world"d));
                        assert(result.match);
                        assert(result.value == "hello");
                        assert(result.rest == positional(testRange(" world"d), 1, 6));
                    }}
                }
                /* "hello"    <= "hello"              */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(parseString!"hello")("hello");
                        assert(result.match);
                        assert(result.value == "hello");
                        assert(result.rest == positional("", 1, 6));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(parseString!"hello")("hello"w);
                        assert(result.match);
                        assert(result.value == "hello");
                        assert(result.rest == positional(""w, 1, 6));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(parseString!"hello")("hello"d);
                        assert(result.match);
                        assert(result.value == "hello");
                        assert(result.rest == positional(""d, 1, 6));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(parseString!"hello")(testRange("hello"));
                        assert(result.match);
                        assert(result.value == "hello");
                        assert(result.rest == positional(testRange(""), 1, 6));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(parseString!"hello")(testRange("hello"w));
                        assert(result.match);
                        assert(result.value == "hello");
                        assert(result.rest == positional(testRange(""w), 1, 6));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(parseString!"hello")(testRange("hello"d));
                        assert(result.match);
                        assert(result.value == "hello");
                        assert(result.rest == positional(testRange(""d), 1, 6));
                    }}
                }
                /* "表が怖い" <= "表が怖い噂のソフト" */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(parseString!"表が怖い")("表が怖い噂のソフト");
                        assert(result.match);
                        assert(result.value == "表が怖い");
                        assert(result.rest == positional("噂のソフト", 1, 5));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(parseString!"表が怖い")("表が怖い噂のソフト"w);
                        assert(result.match);
                        assert(result.value == "表が怖い");
                        assert(result.rest == positional("噂のソフト"w, 1, 5));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(parseString!"表が怖い")("表が怖い噂のソフト"d);
                        assert(result.match);
                        assert(result.value == "表が怖い");
                        assert(result.rest == positional("噂のソフト"d, 1, 5));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(parseString!"表が怖い")(testRange("表が怖い噂のソフト"));
                        assert(result.match);
                        assert(result.value == "表が怖い");
                        assert(result.rest == positional(testRange("噂のソフト"), 1, 5));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(parseString!"表が怖い")(testRange("表が怖い噂のソフト"w));
                        assert(result.match);
                        assert(result.value == "表が怖い");
                        assert(result.rest == positional(testRange("噂のソフト"w), 1, 5));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(parseString!"表が怖い")(testRange("表が怖い噂のソフト"d));
                        assert(result.match);
                        assert(result.value == "表が怖い");
                        assert(result.rest == positional(testRange("噂のソフト"d), 1, 5));
                    }}
                }
                /* "hello"    <= "hllo world"         */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(parseString!"hello")("hllo world");
                        assert(!result.match);
                        assert(result.error == Error("\"hello\"", 1, 1));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(parseString!"hello")("hllo world"w);
                        assert(!result.match);
                        assert(result.error == Error("\"hello\"", 1, 1));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(parseString!"hello")("hllo world"d);
                        assert(!result.match);
                        assert(result.error == Error("\"hello\"", 1, 1));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(parseString!"hello")(testRange("hllo world"));
                        assert(!result.match);
                        assert(result.error == Error("\"hello\"", 1, 1));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(parseString!"hello")(testRange("hllo world"w));
                        assert(!result.match);
                        assert(result.error == Error("\"hello\"", 1, 1));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(parseString!"hello")(testRange("hllo world"d));
                        assert(!result.match);
                        assert(result.error == Error("\"hello\"", 1, 1));
                    }}
                }
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        }
    }

    /* parseCharRange */ version(all){
        template parseCharRange(dchar low, dchar high){
            static assert(low <= high);
            alias string ResultType;
            Result!(Range, ResultType) apply(Range)(Positional!Range input, ref memo_t memo){
                typeof(return) result;
                static if(isSomeString!Range){
                    if(input.range.length){
                        size_t idx;
                        dchar c = std.utf.decode(input.range, idx);
                        if(low <= c && c <= high){
                            result.match = true;
                            result.value = to!string(c);
                            result.rest.range = input.range[idx..$];
                            result.rest.line = c == '\n' ? input.line + 1 : input.line;
                            result.rest.column = c == '\n' ? 1 : input.column + 1;
                            return result;
                        }
                    }
                }else{
                    if(!input.range.empty){
                        dchar c = decode(input.range);
                        if(low <= c && c <= high){
                            result.match = true;
                            result.value = to!string(c);
                            result.rest.range = input.range;
                            result.rest.line = c == '\n' ? input.line + 1 : input.line;
                            result.rest.column = c == '\n' ? 1 : input.column + 1;
                        }
                    }
                }
                if(low == dchar.min && high == dchar.max){
                    result.error = Error("any char", input.line, input.column);
                }else{
                    result.error = Error("c: '" ~ to!string(low) ~ "' <= c <= '" ~ to!string(high) ~ "'", input.line, input.column);
                }
                return result;
            }
        }

        debug(ctpg) unittest{
            enum dg = {
                /* [a-z]               <= "hoge"           */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(parseCharRange!('a', 'z'))("hoge");
                        assert(result.match);
                        assert(result.value == "h");
                        assert(result.rest == positional("oge", 1, 2));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(parseCharRange!('a', 'z'))("hoge"w);
                        assert(result.match);
                        assert(result.value == "h");
                        assert(result.rest == positional("oge"w, 1, 2));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(parseCharRange!('a', 'z'))("hoge"d);
                        assert(result.match);
                        assert(result.value == "h");
                        assert(result.rest == positional("oge"d, 1, 2));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(parseCharRange!('a', 'z'))(testRange("hoge"));
                        assert(result.match);
                        assert(result.value == "h");
                        assert(result.rest == positional(testRange("oge"), 1, 2));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(parseCharRange!('a', 'z'))(testRange("hoge"w));
                        assert(result.match);
                        assert(result.value == "h");
                        assert(result.rest == positional(testRange("oge"w), 1, 2));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(parseCharRange!('a', 'z'))(testRange("hoge"d));
                        assert(result.match);
                        assert(result.value == "h");
                        assert(result.rest == positional(testRange("oge"d), 1, 2));
                    }}
                }
                /* [\u0100-\u0010FFFF] <= "\U00012345hoge" */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(parseCharRange!('\u0100', '\U0010FFFF'))("\U00012345hoge");
                        assert(result.match);
                        assert(result.value == "\U00012345");
                        assert(result.rest == positional("hoge", 1, 2));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(parseCharRange!('\u0100', '\U0010FFFF'))("\U00012345hoge"w);
                        assert(result.match);
                        assert(result.value == "\U00012345");
                        assert(result.rest == positional("hoge"w, 1, 2));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(parseCharRange!('\u0100', '\U0010FFFF'))("\U00012345hoge"d);
                        assert(result.match);
                        assert(result.value == "\U00012345");
                        assert(result.rest == positional("hoge"d, 1, 2));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(parseCharRange!('\u0100', '\U0010FFFF'))(testRange("\U00012345hoge"));
                        assert(result.match);
                        assert(result.value == "\U00012345");
                        assert(result.rest == positional(testRange("hoge"), 1, 2));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(parseCharRange!('\u0100', '\U0010FFFF'))(testRange("\U00012345hoge"w));
                        assert(result.match);
                        assert(result.value == "\U00012345");
                        assert(result.rest == positional(testRange("hoge"w), 1, 2));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(parseCharRange!('\u0100', '\U0010FFFF'))(testRange("\U00012345hoge"d));
                        assert(result.match);
                        assert(result.value == "\U00012345");
                        assert(result.rest == positional(testRange("hoge"d), 1, 2));
                    }}
                }
                /* [\u0100-\u0010FFFF] <= "hello world"    */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(parseCharRange!('\u0100', '\U0010FFFF'))("hello world");
                        assert(!result.match);
                        assert(result.error == Error("c: '\u0100' <= c <= '\U0010FFFF'", 1, 1));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(parseCharRange!('\u0100', '\U0010FFFF'))("hello world"w);
                        assert(!result.match);
                        assert(result.error == Error("c: '\u0100' <= c <= '\U0010FFFF'", 1, 1));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(parseCharRange!('\u0100', '\U0010FFFF'))("hello world"d);
                        assert(!result.match);
                        assert(result.error == Error("c: '\u0100' <= c <= '\U0010FFFF'", 1, 1));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(parseCharRange!('\u0100', '\U0010FFFF'))(testRange("hello world"));
                        assert(!result.match);
                        assert(result.error == Error("c: '\u0100' <= c <= '\U0010FFFF'", 1, 1));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(parseCharRange!('\u0100', '\U0010FFFF'))(testRange("hello world"w));
                        assert(!result.match);
                        assert(result.error == Error("c: '\u0100' <= c <= '\U0010FFFF'", 1, 1));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(parseCharRange!('\u0100', '\U0010FFFF'))(testRange("hello world"d));
                        assert(!result.match);
                        assert(result.error == Error("c: '\u0100' <= c <= '\U0010FFFF'", 1, 1));
                    }}
                }
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        }
    }

    /* parseEscapeSequence */ version(all){
        template parseEscapeSequence(){
            alias string ResultType;
            Result!(Range, ResultType) apply(Range)(Positional!Range input, ref memo_t memo){
                typeof(return) result;
                static if(isSomeString!Range){
                    if(input.range[0] == '\\'){
                        switch(input.range[1]){
                            case 'u':{
                                result.match = true;
                                result.value = to!string(input.range[0..6]);
                                result.rest.range = input.range[6..$];
                                result.rest.line = input.line;
                                result.rest.column = input.column + 6;
                                return result;
                            }
                            case 'U':{
                                result.match = true;
                                result.value = to!string(input.range[0..10]);
                                result.rest.range = input.range[10..$];
                                result.rest.line = input.line;
                                result.rest.column = input.column + 10;
                                return result;
                            }
                            case '\'': case '"': case '?': case '\\': case 'a': case 'b': case 'f': case 'n': case 'r': case 't': case 'v':{
                                result.match = true;
                                result.value = to!string(input.range[0..2]);
                                result.rest.range = input.range[2..$];
                                result.rest.line = input.line;
                                result.rest.column = input.column + 2;
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
                                result.rest.line = input.line;
                                result.rest.column = input.column + 6;
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
                                result.rest.line = input.line;
                                result.rest.column = input.column + 10;
                                return result;
                            }
                            case '\'': case '"': case '?': case '\\': case 'a': case 'b': case 'f': case 'n': case 'r': case 't': case 'v':{
                                result.match = true;
                                input.range.popFront;
                                result.value = "\\" ~ to!string(c2);
                                result.rest.range = input.range;
                                result.rest.line = input.line;
                                result.rest.column = input.column + 2;
                                return result;
                            }
                            default:{
                            }
                        }
                    }
                }
                result.error = Error("escape sequence", input.line, input.column);
                return result;
            }
        }

        debug(ctpg) unittest{
            enum dg = {
                /* \es <= "\\\"hoge"        */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(parseEscapeSequence!())("\\\"hoge");
                        assert(result.match);
                        assert(result.value == "\\\"");
                        assert(result.rest == positional("hoge", 1, 3));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(parseEscapeSequence!())("\\\"hoge"w);
                        assert(result.match);
                        assert(result.value == "\\\"");
                        assert(result.rest == positional("hoge"w, 1, 3));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(parseEscapeSequence!())("\\\"hoge"d);
                        assert(result.match);
                        assert(result.value == "\\\"");
                        assert(result.rest == positional("hoge"d, 1, 3));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(parseEscapeSequence!())(testRange("\\\"hoge"));
                        assert(result.match);
                        assert(result.value == "\\\"");
                        assert(result.rest == positional(testRange("hoge"), 1, 3));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(parseEscapeSequence!())(testRange("\\\"hoge"w));
                        assert(result.match);
                        assert(result.value == "\\\"");
                        assert(result.rest == positional(testRange("hoge"w), 1, 3));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(parseEscapeSequence!())(testRange("\\\"hoge"d));
                        assert(result.match);
                        assert(result.value == "\\\"");
                        assert(result.rest == positional(testRange("hoge"d), 1, 3));
                    }}
                }
                /* \es <= r"\U0010FFFFhoge" */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(parseEscapeSequence!())(r"\U0010FFFFhoge");
                        assert(result.match);
                        assert(result.value == r"\U0010FFFF");
                        assert(result.rest == positional("hoge", 1, 11));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(parseEscapeSequence!())(r"\U0010FFFFhoge"w);
                        assert(result.match);
                        assert(result.value == r"\U0010FFFF");
                        assert(result.rest == positional("hoge"w, 1, 11));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(parseEscapeSequence!())(r"\U0010FFFFhoge"d);
                        assert(result.match);
                        assert(result.value == r"\U0010FFFF");
                        assert(result.rest == positional("hoge"d, 1, 11));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(parseEscapeSequence!())(testRange(r"\U0010FFFFhoge"));
                        assert(result.match);
                        assert(result.value == r"\U0010FFFF");
                        assert(result.rest == positional(testRange("hoge"), 1, 11));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(parseEscapeSequence!())(testRange(r"\U0010FFFFhoge"w));
                        assert(result.match);
                        assert(result.value == r"\U0010FFFF");
                        assert(result.rest == positional(testRange("hoge"w), 1, 11));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(parseEscapeSequence!())(testRange(r"\U0010FFFFhoge"d));
                        assert(result.match);
                        assert(result.value == r"\U0010FFFF");
                        assert(result.rest == positional(testRange("hoge"d), 1, 11));
                    }}
                }
                /* \es <= r"\u10FFhoge"     */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(parseEscapeSequence!())(r"\u10FFhoge");
                        assert(result.match);
                        assert(result.value == r"\u10FF");
                        assert(result.rest == positional("hoge", 1, 7));
                    }}
                    /* wstring          */ version(all){{
                        auto result = getResult!(parseEscapeSequence!())(r"\u10FFhoge"w);
                        assert(result.match);
                        assert(result.value == r"\u10FF");
                        assert(result.rest == positional("hoge"w, 1, 7));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(parseEscapeSequence!())(r"\u10FFhoge"d);
                        assert(result.match);
                        assert(result.value == r"\u10FF");
                        assert(result.rest == positional("hoge"d, 1, 7));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(parseEscapeSequence!())(testRange(r"\u10FFhoge"));
                        assert(result.match);
                        assert(result.value == r"\u10FF");
                        assert(result.rest == positional(testRange("hoge"), 1, 7));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(parseEscapeSequence!())(testRange(r"\u10FFhoge"w));
                        assert(result.match);
                        assert(result.value == r"\u10FF");
                        assert(result.rest == positional(testRange("hoge"w), 1, 7));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(parseEscapeSequence!())(testRange(r"\u10FFhoge"d));
                        assert(result.match);
                        assert(result.value == r"\u10FF");
                        assert(result.rest == positional(testRange("hoge"d), 1, 7));
                    }}
                }
                /* \es <= r"\nhoge"         */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(parseEscapeSequence!())(r"\\hoge");
                        assert(result.match);
                        assert(result.value == r"\\");
                        assert(result.rest == positional("hoge", 1, 3));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(parseEscapeSequence!())(r"\\hoge"w);
                        assert(result.match);
                        assert(result.value == r"\\");
                        assert(result.rest == positional("hoge"w, 1, 3));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(parseEscapeSequence!())(r"\\hoge"d);
                        assert(result.match);
                        assert(result.value == r"\\");
                        assert(result.rest == positional("hoge"d, 1, 3));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(parseEscapeSequence!())(testRange(r"\\hoge"));
                        assert(result.match);
                        assert(result.value == r"\\");
                        assert(result.rest == positional(testRange("hoge"), 1, 3));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(parseEscapeSequence!())(testRange(r"\\hoge"w));
                        assert(result.match);
                        assert(result.value == r"\\");
                        assert(result.rest == positional(testRange("hoge"w), 1, 3));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(parseEscapeSequence!())(testRange(r"\\hoge"d));
                        assert(result.match);
                        assert(result.value == r"\\");
                        assert(result.rest == positional(testRange("hoge"d), 1, 3));
                    }}
                }
                /* \es <= r"欝hoge"         */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(parseEscapeSequence!())("鬱hoge");
                        assert(!result.match);
                        assert(result.error == Error("escape sequence", 1, 1));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(parseEscapeSequence!())("鬱hoge"w);
                        assert(!result.match);
                        assert(result.error == Error("escape sequence", 1, 1));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(parseEscapeSequence!())("鬱hoge"d);
                        assert(!result.match);
                        assert(result.error == Error("escape sequence", 1, 1));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(parseEscapeSequence!())(testRange("鬱hoge"));
                        assert(!result.match);
                        assert(result.error == Error("escape sequence", 1, 1));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(parseEscapeSequence!())(testRange("鬱hoge"w));
                        assert(!result.match);
                        assert(result.error == Error("escape sequence", 1, 1));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(parseEscapeSequence!())(testRange("鬱hoge"d));
                        assert(!result.match);
                        assert(result.error == Error("escape sequence", 1, 1));
                    }}
                }
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        }
    }

    /* parseSpace */ version(all){
        template parseSpace(){
            alias string ResultType;
            Result!(Range, ResultType) apply(Range)(Positional!Range input, ref memo_t memo){
                typeof(return) result;
                static if(isSomeString!Range){
                    if(input.range.length > 0 && (input.range[0] == ' ' || input.range[0] == '\n' || input.range[0] == '\t' || input.range[0] == '\r' || input.range[0] == '\f')){
                        result.match = true;
                        result.value = to!string(input.range[0..1]);
                        result.rest.range = input.range[1..$];
                        result.rest.line = (input.range[0] == '\n' ? input.line + 1 : input.line);
                        result.rest.column = (input.range[0] == '\n' ? 1 : input.column + 1);
                        return result;
                    }
                }else{
                    if(!input.range.empty){
                        Unqual!(ElementType!Range) c = input.range.front;
                        if(c == ' ' || c == '\n' || c == '\t' || c == '\r' || c == '\f'){
                            result.match = true;
                            result.value = to!string(c);
                            input.range.popFront;
                            result.rest.range = input.range;
                            result.rest.line = (c == '\n' ? input.line + 1 : input.line);
                            result.rest.column = (c == '\n' ? 1 : input.column + 1);
                            return result;
                        }
                    }
                }
                result.error = Error("space", input.line, input.column);
                return result;
            }
        }

        debug(ctpg) unittest{
            enum dg = {
                /* \s <= "\thoge" */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(parseSpace!())("\thoge");
                        assert(result.match);
                        assert(result.value == "\t");
                        assert(result.rest == positional("hoge", 1, 2));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(parseSpace!())("\thoge"w);
                        assert(result.match);
                        assert(result.value == "\t");
                        assert(result.rest == positional("hoge"w, 1, 2));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(parseSpace!())("\thoge"d);
                        assert(result.match);
                        assert(result.value == "\t");
                        assert(result.rest == positional("hoge"d, 1, 2));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(parseSpace!())(testRange("\thoge"));
                        assert(result.match);
                        assert(result.value == "\t");
                        assert(result.rest == positional(testRange("hoge"), 1, 2));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(parseSpace!())(testRange("\thoge"w));
                        assert(result.match);
                        assert(result.value == "\t");
                        assert(result.rest == positional(testRange("hoge"w), 1, 2));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(parseSpace!())(testRange("\thoge"d));
                        assert(result.match);
                        assert(result.value == "\t");
                        assert(result.rest == positional(testRange("hoge"d), 1, 2));
                    }}
                }
                /* \s <= "hoge"   */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(parseSpace!())("hoge");
                        assert(!result.match);
                        assert(result.error == Error("space", 1, 1));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(parseSpace!())("hoge"w);
                        assert(!result.match);
                        assert(result.error == Error("space", 1, 1));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(parseSpace!())("hoge"d);
                        assert(!result.match);
                        assert(result.error == Error("space", 1, 1));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(parseSpace!())("hoge");
                        assert(!result.match);
                        assert(result.error == Error("space", 1, 1));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(parseSpace!())("hoge"w);
                        assert(!result.match);
                        assert(result.error == Error("space", 1, 1));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(parseSpace!())("hoge"d);
                        assert(!result.match);
                        assert(result.error == Error("space", 1, 1));
                    }}
                }
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        }
    }

    /* parseEOF */ version(all){
        template parseEOF(){
            alias None ResultType;
            Result!(Range, ResultType) apply(Range)(Positional!Range input, ref memo_t memo){
                typeof(return) result;
                if(input.range.empty){
                    result.match = true;
                }else{
                    result.error = Error("EOF", input.line, input.column);
                }
                return result;
            }
        }

        debug(ctpg) unittest{
            enum dg = {
                /* $ <= ""     */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(parseEOF!())("");
                        assert(result.match);
                        assert(result.rest == positional("", 1, 1));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(parseEOF!())(""w);
                        assert(result.match);
                        assert(result.rest == positional(""w, 1, 1));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(parseEOF!())(""d);
                        assert(result.match);
                        assert(result.rest == positional(""d, 1, 1));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(parseEOF!())(testRange(""));
                        assert(result.match);
                        assert(result.rest == positional(testRange(""), 1, 1));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(parseEOF!())(testRange(""w));
                        assert(result.match);
                        assert(result.rest == positional(testRange(""w), 1, 1));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(parseEOF!())(testRange(""d));
                        assert(result.match);
                        assert(result.rest == positional(testRange(""d), 1, 1));
                    }}
                }
                /* $ <= "hoge" */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(parseEOF!())("hoge");
                        assert(!result.match);
                        assert(result.error == Error("EOF", 1, 1));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(parseEOF!())("hoge"w);
                        assert(!result.match);
                        assert(result.error == Error("EOF", 1, 1));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(parseEOF!())("hoge"d);
                        assert(!result.match);
                        assert(result.error == Error("EOF", 1, 1));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(parseEOF!())(testRange("hoge"));
                        assert(!result.match);
                        assert(result.error == Error("EOF", 1, 1));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(parseEOF!())(testRange("hoge"w));
                        assert(!result.match);
                        assert(result.error == Error("EOF", 1, 1));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(parseEOF!())(testRange("hoge"d));
                        assert(!result.match);
                        assert(result.error == Error("EOF", 1, 1));
                    }}
                }
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        }
    }

    debug(ctpg) unittest{
        enum dg = {
            return true;
        };
        debug(ctpg_ct) static assert(dg());
        dg();
    }

    debug(ctpg) unittest{
        enum dg = {
            return true;
        };
        debug(ctpg_ct) static assert(dg());
        dg();
    }
}

/* useful parser */ version(all){
    /* parseAnyChar */ version(all){
        template parseAnyChar(){
            alias parseCharRange!(dchar.min, dchar.max) parseAnyChar;
        }

        debug(ctpg) unittest{
            enum dg = {
                /* \a <= "hoge"       */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(parseAnyChar!())("hoge");
                        assert(result.match);
                        assert(result.value == "h");
                        assert(result.rest == positional("oge", 1, 2));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(parseAnyChar!())("hoge"w);
                        assert(result.match);
                        assert(result.value == "h");
                        assert(result.rest == positional("oge"w, 1, 2));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(parseAnyChar!())("hoge"d);
                        assert(result.match);
                        assert(result.value == "h");
                        assert(result.rest == positional("oge"d, 1, 2));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(parseAnyChar!())(testRange("hoge"));
                        assert(result.match);
                        assert(result.value == "h");
                        assert(result.rest == positional(testRange("oge"), 1, 2));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(parseAnyChar!())(testRange("hoge"w));
                        assert(result.match);
                        assert(result.value == "h");
                        assert(result.rest == positional(testRange("oge"w), 1, 2));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(parseAnyChar!())(testRange("hoge"d));
                        assert(result.match);
                        assert(result.value == "h");
                        assert(result.rest == positional(testRange("oge"d), 1, 2));
                    }}
                }
                /* \a <= "\U00012345" */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(parseAnyChar!())("\U00012345");
                        assert(result.match);
                        assert(result.value == "\U00012345");
                        assert(result.rest == positional("", 1, 2));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(parseAnyChar!())("\U00012345"w);
                        assert(result.match);
                        assert(result.value == "\U00012345");
                        assert(result.rest == positional(""w, 1, 2));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(parseAnyChar!())("\U00012345"d);
                        assert(result.match);
                        assert(result.value == "\U00012345");
                        assert(result.rest == positional(""d, 1, 2));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(parseAnyChar!())(testRange("\U00012345"));
                        assert(result.match);
                        assert(result.value == "\U00012345");
                        assert(result.rest == positional(testRange(""), 1, 2));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(parseAnyChar!())(testRange("\U00012345"w));
                        assert(result.match);
                        assert(result.value == "\U00012345");
                        assert(result.rest == positional(testRange(""w), 1, 2));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(parseAnyChar!())(testRange("\U00012345"d));
                        assert(result.match);
                        assert(result.value == "\U00012345");
                        assert(result.rest == positional(testRange(""d), 1, 2));
                    }}
                }
                /* \a <= "\nhoge"     */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(parseAnyChar!())("\nhoge");
                        assert(result.match);
                        assert(result.value == "\n");
                        assert(result.rest == positional("hoge", 2, 1));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(parseAnyChar!())("\nhoge"w);
                        assert(result.match);
                        assert(result.value == "\n");
                        assert(result.rest == positional("hoge"w, 2, 1));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(parseAnyChar!())("\nhoge"d);
                        assert(result.match);
                        assert(result.value == "\n");
                        assert(result.rest == positional("hoge"d, 2, 1));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(parseAnyChar!())(testRange("\nhoge"));
                        assert(result.match);
                        assert(result.value == "\n");
                        assert(result.rest == positional(testRange("hoge"), 2, 1));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(parseAnyChar!())(testRange("\nhoge"w));
                        assert(result.match);
                        assert(result.value == "\n");
                        assert(result.rest == positional(testRange("hoge"w), 2, 1));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(parseAnyChar!())(testRange("\nhoge"d));
                        assert(result.match);
                        assert(result.value == "\n");
                        assert(result.rest == positional(testRange("hoge"d), 2, 1));
                    }}
                }
                /* \a <= ""           */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(parseAnyChar!())("");
                        assert(!result.match);
                        assert(result.error == Error("any char", 1, 1));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(parseAnyChar!())(""w);
                        assert(!result.match);
                        assert(result.error == Error("any char", 1, 1));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(parseAnyChar!())(""d);
                        assert(!result.match);
                        assert(result.error == Error("any char", 1, 1));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(parseAnyChar!())(testRange(""));
                        assert(!result.match);
                        assert(result.error == Error("any char", 1, 1));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(parseAnyChar!())(testRange(""w));
                        assert(!result.match);
                        assert(result.error == Error("any char", 1, 1));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(parseAnyChar!())(testRange(""d));
                        assert(!result.match);
                        assert(result.error == Error("any char", 1, 1));
                    }}
                }
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        }
    }

    /* parseSpaces */ version(all){
        template parseSpaces(){
            alias combinateNone!(combinateMore0!(parseSpace!())) parseSpaces;
        }

        debug(ctpg) unittest{
            static assert(is(parseSpaces!().ResultType));
            enum dg = {
                /* \ss <= "\t \rhoge" */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(parseSpaces!())("\t \rhoge");
                        assert(result.match);
                        assert(result.rest == positional("hoge", 1, 4));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(parseSpaces!())("\t \rhoge"w);
                        assert(result.match);
                        assert(result.rest == positional("hoge"w, 1, 4));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(parseSpaces!())("\t \rhoge"d);
                        assert(result.match);
                        assert(result.rest == positional("hoge"d, 1, 4));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(parseSpaces!())(testRange("\t \rhoge"));
                        assert(result.match);
                        assert(result.rest == positional(testRange("hoge"), 1, 4));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(parseSpaces!())(testRange("\t \rhoge"w));
                        assert(result.match);
                        assert(result.rest == positional(testRange("hoge"w), 1, 4));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(parseSpaces!())(testRange("\t \rhoge"d));
                        assert(result.match);
                        assert(result.rest == positional(testRange("hoge"d), 1, 4));
                    }}
                }
                /* \ss <= "hoge" */ version(all){
                    /* string          */ version(all){{
                        auto result = getResult!(parseSpaces!())("hoge");
                        assert(result.match);
                        assert(result.rest == positional("hoge", 1, 1));
                    }}
                    /* wstring         */ version(all){{
                        auto result = getResult!(parseSpaces!())("hoge"w);
                        assert(result.match);
                        assert(result.rest == positional("hoge"w, 1, 1));
                    }}
                    /* dstring         */ version(all){{
                        auto result = getResult!(parseSpaces!())("hoge"d);
                        assert(result.match);
                        assert(result.rest == positional("hoge"d, 1, 1));
                    }}
                    /* TestRange!char  */ version(all){{
                        auto result = getResult!(parseSpaces!())(testRange("hoge"));
                        assert(result.match);
                        assert(result.rest == positional(testRange("hoge"), 1, 1));
                    }}
                    /* TestRange!wchar */ version(all){{
                        auto result = getResult!(parseSpaces!())(testRange("hoge"w));
                        assert(result.match);
                        assert(result.rest == positional(testRange("hoge"w), 1, 1));
                    }}
                    /* TestRange!dchar */ version(all){{
                        auto result = getResult!(parseSpaces!())(testRange("hoge"d));
                        assert(result.match);
                        assert(result.rest == positional(testRange("hoge"d), 1, 1));
                    }}
                }
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        }
    }

    /* parseIdent */ version(all){
        template parseIdent(){
            alias combinateMemoize!(combinateString!(
                combinateMemoize!(combinateSequence!(
                    combinateMemoize!(combinateChoice!(
                        combinateMemoize!(parseString!"_"),
                        combinateMemoize!(parseCharRange!('a','z')),
                        combinateMemoize!(parseCharRange!('A','Z'))
                    )),
                    combinateMemoize!(combinateMore0!(parseIdentChar!()))
                ))
            )) parseIdent;
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

        debug(ctpg) unittest{
            enum dg = {
                version(all){{
                    auto result = getResult!(parseIdent!())("hoge");
                    assert(result.match);
                    assert(result.value == "hoge");
                    assert(result.rest.isEnd);
                }}
                version(all){{
                    auto result = getResult!(parseIdent!())("_x");
                    assert(result.match);
                    assert(result.value == "_x");
                    assert(result.rest.isEnd);
                }}
                version(all){{
                    auto result = getResult!(parseIdent!())("_0");
                    assert(result.match);
                    assert(result.value == "_0");
                    assert(result.rest.isEnd);
                }}
                version(all){{
                    auto result = getResult!(parseIdent!())("0");
                    assert(!result.match);
                    assert(result.error == Error("\"_\" or c: 'a' <= c <= 'z' or c: 'A' <= c <= 'Z'", 1, 1));
                }}
                version(all){{
                    auto result = getResult!(parseIdent!())("あ");
                    assert(!result.match);
                    assert(result.error == Error("\"_\" or c: 'a' <= c <= 'z' or c: 'A' <= c <= 'Z'", 1, 1));
                }}
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        }
    }

    /* parseStringLiteral */ version(all){
        template parseStringLiteral(){
            alias combinateChoice!(
                combinateString!(
                    combinateSequence!(
                        parseString!"\"",
                        combinateMore0!(
                            combinateSequence!(
                                combinateNot!(parseString!"\""),
                                combinateChoice!(
                                    parseEscapeSequence!(),
                                    parseAnyChar!()
                                )
                            )
                        ),
                        parseString!"\""
                    )
                ),
                combinateString!(
                    combinateSequence!(
                        parseString!"r\"",
                        combinateMore0!(
                            combinateSequence!(
                                combinateNot!(parseString!"\""),
                                parseAnyChar!()
                            )
                        ),
                        parseString!"\""
                    )
                ),
                combinateString!(
                    combinateSequence!(
                        parseString!"`",
                        combinateMore0!(
                            combinateSequence!(
                                combinateNot!(parseString!"`"),
                                parseAnyChar!()
                            )
                        ),
                        parseString!"`"
                    )
                )
            ) parseStringLiteral;
        }

        alias parseStringLiteral strLit_p;

        debug(ctpg) unittest{
            enum dg = {
                {
                    auto r = getResult!(parseStringLiteral!())(q{"表が怖い噂のソフト"});
                    assert(r.match);
                    assert(r.rest == positional("", 1, 12));
                    assert(r.value == q{"表が怖い噂のソフト"});
                }
                {
                    auto r = getResult!(parseStringLiteral!())(q{r"表が怖い噂のソフト"});
                    assert(r.match);
                    assert(r.rest == positional("", 1, 13));
                    assert(r.value == q{r"表が怖い噂のソフト"});
                }
                {
                    auto r = getResult!(parseStringLiteral!())(q{`表が怖い噂のソフト`});
                    assert(r.match);
                    assert(r.rest == positional("", 1, 12));
                    assert(r.value == q{`表が怖い噂のソフト`});
                }
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        }
    }

    /* parseIntLiteral */ version(all){
        alias combinateChoice!(
            combinateConvert!(
                combinateNone!(parseString!"0"),
                function(){
                    return 0;
                }
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

        template intLit_p(){
            alias parseIntLiteral intLit_p;
        }

        debug(ctpg) unittest{
            enum dg = {
                version(all){{
                    auto result = getResult!parseIntLiteral(q{3141});
                    assert(result.match);
                    assert(result.value == 3141);
                    assert(result.rest == positional("", 1, 5));
                }}
                version(all){{
                    auto result = getResult!parseIntLiteral(q{0});
                    assert(result.match);
                    assert(result.rest == positional("", 1, 2));
                    assert(result.value == 0);
                }}
                version(all){{
                    auto result = getResult!parseIntLiteral("0123");
                    assert(result.match);
                    assert(result.value == 0);
                    assert(result.rest == positional("123", 1, 2));
                }}
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        }
    }
}

mixin template ctpg(string src){
    mixin(parse!defs(src));
}

template getSource(string src){
    enum getSource = getResult!(defs!())(src).value;
}

auto getResult(alias fun, Range)(Range input){
    memo_t memo;
    return fun.apply(Positional!Range(input), memo);
}

auto parse(alias fun)(string src){
    auto result = getResult!(fun!())(src);
    if(result.match){
        return result.value;
    }else{
        throw new Exception(to!string(result.error.line) ~ q{: } ~ to!string(result.error.column) ~ q{: error } ~ result.error.need ~ q{ is needed});
    }
}

bool isMatch(alias fun)(string src){
    return getResult!(fun!())(src).match;
}

/* ctpg */ version(all){
    /* defs */ version(all){
        template defs(){
            alias string ResultType;
            Result!(Range, string) apply(Range)(Positional!Range input, ref memo_t memo){
                return combinateMemoize!(combinateString!(
                    combinateMemoize!(combinateSequence!(
                        combinateMemoize!(parseSpaces!()),
                        combinateMemoize!(combinateMore1!(
                            combinateMemoize!(def!()),
                            combinateMemoize!(parseSpaces!())
                        )),
                        combinateMemoize!(parseSpaces!()),
                        combinateMemoize!(parseEOF!())
                    ))
                )).apply(input, memo);
            }
        }

        debug(ctpg) unittest{
            enum dg = {
                string src = q{
                    bool hoge = !"hello" $ >> {return false;};
                    Tuple!piyo hoge2 = hoge* >> {return tuple("foo");};
                };
                auto result = getResult!(defs!())(src);
                assert(result.match);
                assert(result.rest.range == "");
                assert(
                    result.value ==
                    "template hoge(){"
                        "alias bool ResultType;"
                        "Result!(Range, ResultType) apply(Range)(Positional!Range input, ref memo_t memo){"
                            "return combinateMemoize!(combinateConvert!("
                                "combinateMemoize!(combinateSequence!("
                                    "combinateMemoize!(combinateNone!("
                                        "combinateMemoize!(parseString!\"hello\")"
                                    ")),"
                                    "combinateMemoize!(parseEOF!())"
                                ")),"
                                "function(){"
                                    "return false;"
                                "}"
                            ")).apply(input, memo);"
                        "}"
                    "}"
                    "template hoge2(){"
                        "alias Tuple!piyo ResultType;"
                        "Result!(Range, ResultType) apply(Range)(Positional!Range input, ref memo_t memo){"
                            "return combinateMemoize!(combinateConvert!("
                                "combinateMemoize!(combinateMore0!("
                                    "combinateMemoize!(hoge!())"
                                ")),"
                                "function(){"
                                    "return tuple(\"foo\");"
                                "}"
                            ")).apply(input, memo);"
                        "}"
                    "}"
                );
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        };
    }

    /* def */ version(all){
        template def(){
            alias string ResultType;
            Result!(string, ResultType) apply(Positional!string input, ref memo_t memo){
                return combinateMemoize!(combinateConvert!(
                    combinateMemoize!(combinateSequence!(
                        combinateMemoize!(typeName!()),
                        combinateMemoize!(parseSpaces!()),
                        combinateMemoize!(id!()),
                        combinateMemoize!(parseSpaces!()),
                        combinateMemoize!(combinateNone!(
                            combinateMemoize!(parseString!"=")
                        )),
                        combinateMemoize!(parseSpaces!()),
                        combinateMemoize!(convExp!()),
                        combinateMemoize!(parseSpaces!()),
                        combinateMemoize!(combinateNone!(
                            combinateMemoize!(parseString!";")
                        ))
                    )),
                    (string type, string name, string convExp)
                    =>
                        "template " ~ name ~ "(){"
                            "alias " ~ type ~ " ResultType;"
                            "Result!(Range, ResultType) apply(Range)(Positional!Range input, ref memo_t memo){"
                                "return "~convExp~".apply(input, memo);"
                            "}"
                        "}"
                )).apply(input, memo);
            }
        }

        debug(ctpg) unittest{
            enum dg = {
                version(all){{
                    auto result = getResult!(def!())(`bool hoge = !"hello" $ >> {return false;};`);
                    assert(result.match);
                    assert(result.rest.range == "");
                    assert(
                        result.value ==
                        "template hoge(){"
                            "alias bool ResultType;"
                            "Result!(Range, ResultType) apply(Range)(Positional!Range input, ref memo_t memo){"
                                "return combinateMemoize!(combinateConvert!("
                                    "combinateMemoize!(combinateSequence!("
                                        "combinateMemoize!(combinateNone!("
                                            "combinateMemoize!(parseString!\"hello\")"
                                        ")),"
                                        "combinateMemoize!(parseEOF!())"
                                    ")),"
                                    "function(){"
                                        "return false;"
                                    "}"
                                ")).apply(input, memo);"
                            "}"
                        "}"
                    );
                }}
                version(all){{
                    auto result = getResult!(def!())(`None recursive = A $;`);
                    assert(result.match);
                    assert(result.rest.range == "");
                    assert(
                        result.value ==
                        "template recursive(){"
                            "alias None ResultType;"
                            "Result!(Range, ResultType) apply(Range)(Positional!Range input, ref memo_t memo){"
                                "return combinateMemoize!(combinateSequence!("
                                    "combinateMemoize!(A!()),"
                                    "combinateMemoize!(parseEOF!())"
                                ")).apply(input, memo);"
                            "}"
                        "}"
                    );
                }}
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        };
    }

    /* convExp */ version(all){
        template convExp(){
            alias string ResultType;
            Result!(string, ResultType) apply(Positional!string input, ref memo_t memo){
                return combinateMemoize!(combinateConvert!(
                    combinateMemoize!(combinateSequence!(
                        combinateMemoize!(choiceExp!()),
                        combinateMemoize!(combinateMore0!(
                            combinateMemoize!(combinateSequence!(
                                combinateMemoize!(parseSpaces!()),
                                combinateMemoize!(combinateNone!(
                                    parseString!">>"
                                )),
                                combinateMemoize!(parseSpaces!()),
                                combinateMemoize!(combinateChoice!(
                                    combinateMemoize!(func!()),
                                    combinateMemoize!(typeName!())
                                ))
                            ))
                        ))
                    )),
                    function(string choiceExp, string[] funcs){
                        string result = choiceExp;
                        foreach(func; funcs){
                            result = "combinateMemoize!(combinateConvert!(" ~ result ~ "," ~ func ~ "))";
                        }
                        return result;
                    }
                )).apply(input, memo);
            }
        }

        debug(ctpg) unittest{
            enum dg = {
                version(all){{
                    auto result = getResult!(convExp!())(q{!"hello" $ >> {return false;}});
                    assert(result.match);
                    assert(result.rest.range == "");
                    assert(
                        result.value ==
                        "combinateMemoize!(combinateConvert!("
                            "combinateMemoize!(combinateSequence!("
                                "combinateMemoize!(combinateNone!("
                                    "combinateMemoize!(parseString!\"hello\")"
                                ")),"
                                "combinateMemoize!(parseEOF!())"
                            ")),"
                            "function(){"
                                "return false;"
                            "}"
                        "))"
                    );
                }}
                version(all){{
                    auto result = getResult!(convExp!())(q{"hello" >> flat >> to!int});
                    assert(result.match);
                    assert(result.rest.range == "");
                    assert(
                        result.value ==
                        "combinateMemoize!(combinateConvert!("
                            "combinateMemoize!(combinateConvert!("
                                "combinateMemoize!(parseString!\"hello\"),"
                                "flat"
                            ")),"
                            "to!int"
                        "))"
                    );
                }}
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        }
    }

    /* choiceExp */ version(all){
        template choiceExp(){
            alias string ResultType;
            Result!(string, ResultType) apply(Positional!string input, ref memo_t memo){
                return combinateMemoize!(combinateConvert!(
                    combinateMemoize!(combinateSequence!(
                        combinateMemoize!(seqExp!()),
                        combinateMemoize!(combinateMore0!(
                            combinateMemoize!(combinateSequence!(
                                combinateMemoize!(parseSpaces!()),
                                combinateMemoize!(combinateNone!(
                                    combinateMemoize!(parseString!"/")
                                )),
                                combinateMemoize!(parseSpaces!()),
                                combinateMemoize!(seqExp!())
                            ))
                        ))
                    )),
                    (string seqExp, string[] seqExps) => seqExps.length ? "combinateMemoize!(combinateChoice!(" ~ seqExp ~ "," ~ seqExps.mkString(",") ~ "))" : seqExp
                )).apply(input, memo);
            }
        }

        debug(ctpg) unittest{
            enum dg = {
                version(all){{
                    auto result = getResult!(choiceExp!())(`!$* / (&(^"a"))?`);
                    assert(result.match);
                    assert(result.rest.range == "");
                    assert(
                        result.value ==
                        "combinateMemoize!(combinateChoice!("
                            "combinateMemoize!(combinateMore0!("
                                "combinateMemoize!(combinateNone!("
                                    "combinateMemoize!(parseEOF!())"
                                "))"
                            ")),"
                            "combinateMemoize!(combinateOption!("
                                "combinateMemoize!(combinateAnd!("
                                    "combinateMemoize!(combinateNot!("
                                        "combinateMemoize!(parseString!\"a\")"
                                    "))"
                                "))"
                            "))"
                        "))"
                    );
                }}
                version(all){{
                    auto result = getResult!(choiceExp!())(`!"hello" $`);
                    assert(result.match);
                    assert(result.rest.range == "");
                    assert(
                        result.value ==
                        "combinateMemoize!(combinateSequence!("
                            "combinateMemoize!(combinateNone!("
                                "combinateMemoize!(parseString!\"hello\")"
                            ")),"
                            "combinateMemoize!(parseEOF!())"
                        "))"
                    );
                }}
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        }
    }

    /* seqExp */ version(all){
        template seqExp(){
            alias string ResultType;
            Result!(string, ResultType) apply(Positional!string input, ref memo_t memo){
                return combinateMemoize!(combinateConvert!(
                    combinateMemoize!(combinateMore1!(
                        combinateMemoize!(optionExp!()),
                        combinateMemoize!(parseSpaces!())
                    )),
                    (string[] optionExps) => optionExps.length > 1 ? "combinateMemoize!(combinateSequence!("~optionExps.mkString(",")~"))" : optionExps[0]
                )).apply(input, memo);
            }
        }

        debug(ctpg) unittest{
            enum dg = {
                version(all){{
                    auto result = getResult!(seqExp!())("!$* (&(^$))?");
                    assert(result.match);
                    assert(result.rest.range == "");
                    assert(
                        result.value ==
                        "combinateMemoize!(combinateSequence!("
                            "combinateMemoize!(combinateMore0!("
                                "combinateMemoize!(combinateNone!("
                                    "combinateMemoize!(parseEOF!())"
                                "))"
                            ")),"
                            "combinateMemoize!(combinateOption!("
                                "combinateMemoize!(combinateAnd!("
                                    "combinateMemoize!(combinateNot!("
                                        "combinateMemoize!(parseEOF!())"
                                    "))"
                                "))"
                            "))"
                        "))"
                    );
                }}
                version(all){{
                    auto result = getResult!(seqExp!())("!\"hello\" $");
                    assert(result.match);
                    assert(result.rest.range == "");
                    assert(
                        result.value ==
                        "combinateMemoize!(combinateSequence!("
                            "combinateMemoize!(combinateNone!("
                                "combinateMemoize!(parseString!\"hello\")"
                            ")),"
                            "combinateMemoize!(parseEOF!())"
                        "))"
                    );
                }}
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        }
    }

    /* optionExp */ version(all){
        template optionExp(){
            alias string ResultType;
            Result!(string, ResultType) apply(Positional!string input, ref memo_t memo){
                return combinateMemoize!(combinateConvert!(
                    combinateMemoize!(combinateSequence!(
                        combinateMemoize!(postExp!()),
                        combinateMemoize!(parseSpaces!()),
                        combinateMemoize!(combinateOption!(
                            combinateMemoize!(combinateNone!(
                                combinateMemoize!(parseString!"?")
                            ))
                        ))
                    )),
                    (string convExp, Option!None op) => op.some ? "combinateMemoize!(combinateOption!("~convExp~"))" : convExp
                )).apply(input, memo);
            }
        }

        debug(ctpg) unittest{
            enum dg = {
                auto result = getResult!(optionExp!())("(&(^\"hello\"))?");
                assert(result.match);
                assert(result.rest.range == "");
                assert(
                    result.value ==
                    "combinateMemoize!(combinateOption!("
                        "combinateMemoize!(combinateAnd!("
                            "combinateMemoize!(combinateNot!("
                                "combinateMemoize!(parseString!\"hello\")"
                            "))"
                        "))"
                    "))"
                );
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        }
    }

    /* postExp */ version(all){
        template postExp(){
            alias string ResultType;
            Result!(string, ResultType) apply(Positional!string input, ref memo_t memo){
                return combinateMemoize!(combinateConvert!(
                    combinateMemoize!(combinateSequence!(
                        combinateMemoize!(preExp!()),
                        combinateMemoize!(combinateOption!(
                            combinateMemoize!(combinateSequence!(
                                combinateMemoize!(combinateChoice!(
                                    combinateMemoize!(parseString!"+"),
                                    combinateMemoize!(parseString!"*")
                                )),
                                combinateMemoize!(combinateOption!(
                                    combinateMemoize!(combinateSequence!(
                                        combinateMemoize!(combinateNone!(
                                            combinateMemoize!(parseString!"<")
                                        )),
                                        combinateMemoize!(choiceExp!()),
                                        combinateMemoize!(combinateNone!(
                                            combinateMemoize!(parseString!">")
                                        ))
                                    ))
                                ))
                            ))
                        ))
                    )),
                    function(string preExp, Option!(Tuple!(string, Option!string)) op){
                        final switch(op.value[0]){
                            case "+":{
                                if(op.value[1].some){
                                    return "combinateMemoize!(combinateMore1!(" ~ preExp ~ "," ~ op.value[1].value ~ "))";
                                }else{
                                    return "combinateMemoize!(combinateMore1!(" ~ preExp ~ "))";
                                }
                            }
                            case "*":{
                                if(op.value[1].some){
                                    return "combinateMemoize!(combinateMore0!(" ~ preExp ~ "," ~ op.value[1].value ~ "))";
                                }else{
                                    return "combinateMemoize!(combinateMore0!(" ~ preExp ~ "))";
                                }
                            }
                            case "":{
                                return preExp;
                            }
                        }
                    }
                )).apply(input, memo);
            }
        }

        debug(ctpg) unittest{
            enum dg = {
                auto result = getResult!(postExp!())("!$*");
                assert(result.match);
                assert(result.rest.range == "");
                assert(
                    result.value ==
                    "combinateMemoize!(combinateMore0!("
                        "combinateMemoize!(combinateNone!("
                            "combinateMemoize!(parseEOF!())"
                        "))"
                    "))"
                );
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        }
    }

    /* preExp */ version(all){
        template preExp(){
            alias string ResultType;
            Result!(string, ResultType) apply(Positional!string input, ref memo_t memo){
                return combinateMemoize!(combinateConvert!(
                    combinateMemoize!(combinateSequence!(
                        combinateMemoize!(combinateOption!(
                            combinateMemoize!(combinateChoice!(
                                combinateMemoize!(parseString!"&"),
                                combinateMemoize!(parseString!"^"),
                                combinateMemoize!(parseString!"!")
                            ))
                        )),
                        combinateMemoize!(primaryExp!())
                    )),
                    function(Option!string op, string primaryExp){
                        final switch(op.value){
                            case "&":{
                                return "combinateMemoize!(combinateAnd!(" ~ primaryExp ~ "))";
                            }
                            case "!":{
                                return "combinateMemoize!(combinateNone!(" ~ primaryExp ~ "))";
                            }
                            case "^":{
                                return "combinateMemoize!(combinateNot!(" ~ primaryExp ~ "))";
                            }
                            case "":{
                                return primaryExp;
                            }
                        }
                    }
                )).apply(input, memo);
            }
        }

        debug(ctpg) unittest{
            enum dg = {
                auto result = getResult!(preExp!())("!$");
                assert(result.match);
                assert(result.rest.range == "");
                assert(
                    result.value ==
                    "combinateMemoize!(combinateNone!("
                        "combinateMemoize!(parseEOF!())"
                    "))"
                );
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        }
    }

    /* primaryExp */ version(all){
        template primaryExp(){
            alias string ResultType;
            Result!(string, ResultType) apply(Positional!string input, ref memo_t memo){
                return combinateMemoize!(combinateChoice!(
                    combinateMemoize!(literal!()),
                    combinateMemoize!(nonterminal!()),
                    combinateMemoize!(combinateSequence!(
                        combinateMemoize!(combinateNone!(
                            combinateMemoize!(parseString!"(")
                        )),
                        combinateMemoize!(convExp!()),
                        combinateMemoize!(combinateNone!(
                            combinateMemoize!(parseString!")")
                        ))
                    ))
                )).apply(input, memo);
            }
        }

        debug(ctpg) unittest{
            enum dg = {
                version(all){{
                    auto result = getResult!(primaryExp!())("(&(^$)?)");
                    assert(result.match);
                    assert(result.rest.range == "");
                    assert(
                        result.value ==
                        "combinateMemoize!(combinateOption!("
                            "combinateMemoize!(combinateAnd!("
                                "combinateMemoize!(combinateNot!("
                                    "combinateMemoize!(parseEOF!())"
                                "))"
                            "))"
                        "))"
                    );
                }}
                version(all){{
                    auto result = getResult!(primaryExp!())("int");
                    assert(result.match);
                    assert(result.rest.range == "");
                    assert(result.value == "combinateMemoize!(int!())");
                }}
                version(all){{
                    auto result = getResult!(primaryExp!())("select!(true)(\"true\", \"false\")");
                    assert(result.match);
                    assert(result.rest.range == "");
                    assert(result.value == "combinateMemoize!(select!(true)(\"true\", \"false\")!())");
                }}
                version(all){{
                    auto result = getResult!(primaryExp!())("###このコメントは表示されません###");
                    assert(!result.match);
                }}
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        }
    }

    /* literal */ version(all){
        template literal(){
            alias string ResultType;
            Result!(string, ResultType) apply(Positional!string input, ref memo_t memo){
                return combinateMemoize!(combinateChoice!(
                    combinateMemoize!(rangeLit!()),
                    combinateMemoize!(stringLit!()),
                    combinateMemoize!(eofLit!()),
                    //combinateMemoize!(usefulLit!()),
                )).apply(input, memo);
            }
        }

        debug(ctpg) unittest{
            enum dg = {
                version(all){{
                    auto result = getResult!(literal!())("\"hello\nworld\"");
                    assert(result.match);
                    assert(result.rest.range == "");
                    assert(result.value == "combinateMemoize!(parseString!\"hello\nworld\")");
                }}
                version(all){{
                    auto result = getResult!(literal!())("[a-z]");
                    assert(result.match);
                    assert(result.rest.range == "");
                    assert(result.value == "combinateMemoize!(parseCharRange!('a','z'))");
                }}
                version(all){{
                    auto result = getResult!(literal!())("$");
                    assert(result.match);
                    assert(result.rest.range == "");
                    assert(result.value == "combinateMemoize!(parseEOF!())");
                }}
                version(all){{
                    auto result = getResult!(literal!())("表が怖い噂のソフト");
                    assert(!result.match);
                }}
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        }
    }

    /* stringLit */ version(all){
        template stringLit(){
            alias string ResultType;
            Result!(string, ResultType) apply(Positional!string input, ref memo_t memo){
                return combinateMemoize!(combinateConvert!(
                    combinateMemoize!(combinateSequence!(
                        combinateMemoize!(combinateNone!(
                            combinateMemoize!(parseString!"\"")
                        )),
                        combinateMemoize!(combinateMore0!(
                            combinateMemoize!(combinateSequence!(
                                combinateMemoize!(combinateNot!(
                                    combinateMemoize!(parseString!"\"")
                                )),
                                combinateMemoize!(combinateChoice!(
                                    combinateMemoize!(parseEscapeSequence!()),
                                    combinateMemoize!(parseAnyChar!())
                                ))
                            ))
                        )),
                        combinateMemoize!(combinateNone!(
                            combinateMemoize!(parseString!"\"")
                        ))
                    )),
                    (string[] strs) => "combinateMemoize!(parseString!\"" ~ strs.flat ~ "\")"
                )).apply(input, memo);
            }
        }

        debug(ctpg) unittest{
            enum dg = {
                version(all){{
                    auto result = getResult!(stringLit!())("\"hello\nworld\" ");
                    assert(result.match);
                    assert(result.rest.range == " ");
                    assert(result.value == "combinateMemoize!(parseString!\"hello\nworld\")");
                }}
                version(all){{
                    auto result = getResult!(stringLit!())("aa\"");
                    assert(!result.match);
                }}
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        }
    }

    /* rangeLit */ version(all){
        template rangeLit(){
            alias string ResultType;
            Result!(string, ResultType) apply(Positional!string input, ref memo_t memo){
                return combinateMemoize!(combinateConvert!(
                    combinateMemoize!(combinateSequence!(
                        combinateMemoize!(combinateNone!(
                            combinateMemoize!(parseString!"[")
                        )),
                        combinateMemoize!(combinateMore1!(
                            combinateMemoize!(combinateSequence!(
                                combinateMemoize!(combinateNot!(
                                    combinateMemoize!(parseString!"]")
                                )),
                                combinateMemoize!(combinateChoice!(
                                    combinateMemoize!(charRange!()),
                                    combinateMemoize!(oneChar!())
                                ))
                            ))
                        )),
                        combinateMemoize!(combinateNone!(
                            combinateMemoize!(parseString!"]")
                        ))
                    )),
                    (string[] strs) => strs.length == 1 ? strs[0] : "combinateMemoize!(combinateChoice!("~strs.mkString(",")~"))"
                )).apply(input, memo);
            }
        }

        template charRange(){
            alias string ResultType;
            Result!(string, ResultType) apply(Positional!string input, ref memo_t memo){
                return combinateMemoize!(combinateConvert!(
                    combinateMemoize!(combinateSequence!(
                        combinateMemoize!(combinateChoice!(
                            combinateMemoize!(parseEscapeSequence!()),
                            combinateMemoize!(parseAnyChar!())
                        )),
                        combinateMemoize!(combinateNone!(
                            combinateMemoize!(parseString!"-")
                        )),
                        combinateMemoize!(combinateChoice!(
                            combinateMemoize!(parseEscapeSequence!()),
                            combinateMemoize!(parseAnyChar!())
                        )),
                    )),
                    (string low, string high) => "combinateMemoize!(parseCharRange!('" ~ low ~ "','" ~ high ~ "'))"
                )).apply(input, memo);
            }
        }

        template oneChar(){
            alias string ResultType;
            Result!(string, ResultType) apply(Positional!string input, ref memo_t memo){
                return combinateMemoize!(combinateConvert!(
                    combinateMemoize!(combinateChoice!(
                        combinateMemoize!(parseEscapeSequence!()),
                        combinateMemoize!(parseAnyChar!())
                    )),
                    (string c) => "combinateMemoize!(parseString!\"" ~ c ~ "\")"
                )).apply(input, memo);
            }
        }

        debug(ctpg) unittest{
            enum dg = {
                version(all){{
                    auto result = getResult!(rangeLit!())("[a-z]");
                    assert(result.match);
                    assert(result.rest.range == "");
                    assert(result.value == "combinateMemoize!(parseCharRange!('a','z'))");
                }}
                version(all){{
                    auto result = getResult!(rangeLit!())("[a-zA-Z_]");
                    assert(result.match);
                    assert(result.rest.range == "");
                    assert(
                        result.value ==
                        "combinateMemoize!(combinateChoice!("
                            "combinateMemoize!(parseCharRange!('a','z')),"
                            "combinateMemoize!(parseCharRange!('A','Z')),"
                            "combinateMemoize!(parseString!\"_\")"
                        "))"
                    );
                }}
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        }
    }

    /* eofLit */ version(all){
        template eofLit(){
            alias string ResultType;
            Result!(string, ResultType) apply(Positional!string input, ref memo_t memo){
                return combinateMemoize!(combinateConvert!(
                    combinateMemoize!(combinateNone!(
                        combinateMemoize!(parseString!"$")
                    )),
                    () => "combinateMemoize!(parseEOF!())"
                )).apply(input, memo);
            }
        }

        debug(ctpg) unittest{
            enum dg = {
                version(all){{
                    auto result = getResult!(eofLit!())("$");
                    assert(result.match);
                    assert(result.rest.range == "");
                    assert(result.value == "combinateMemoize!(parseEOF!())");
                }}
                version(all){{
                    auto result = getResult!(eofLit!())("#");
                    assert(!result.match);
                }}
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        }
    }

    /* usefulLit */ version(none){
        template usefulLit(){
            alias string ResultType;
            Result!(string, ResultType) apply(Positional!string, input, ref memo_t memo){
                return combinateMemoize!(combinateConvert!(
                    combinateMemoize!(combinameChoice!(
                        combinateMemoize!(parseString!`\a`),
                        combinateMemoize!(parseString!`\ss`),
                        combinateMemoize!(parseString!`\s`),
                    ))
                )).apply(input, memo);
            }
        }
    }

    /* id */ version(all){
        template id(){
            alias string ResultType;
            Result!(string, ResultType) apply(Positional!string input, ref memo_t memo){
                return combinateMemoize!(combinateString!(
                    combinateMemoize!(combinateSequence!(
                        combinateMemoize!(combinateChoice!(
                            combinateMemoize!(parseCharRange!('A','Z')),
                            combinateMemoize!(parseCharRange!('a','z')),
                            combinateMemoize!(parseString!"_")
                        )),
                        combinateMemoize!(combinateMore0!(
                            combinateMemoize!(combinateChoice!(
                                combinateMemoize!(parseCharRange!('0','9')),
                                combinateMemoize!(parseCharRange!('A','Z')),
                                combinateMemoize!(parseCharRange!('a','z')),
                                combinateMemoize!(parseString!"_"),
                                combinateMemoize!(parseString!","),
                                combinateMemoize!(parseString!"!"),
                                combinateMemoize!(arch!("(", ")"))
                            ))
                        ))
                    ))
                )).apply(input, memo);
            }
        }

        debug(ctpg) unittest{
            enum dg = {
                version(all){{
                    auto result = getResult!(id!())("A");
                    assert(result.match);
                    assert(result.rest.range == "");
                    assert(result.value == "A");
                }}
                version(all){{
                    auto result = getResult!(id!())("int");
                    assert(result.match);
                    assert(result.rest.range == "");
                    assert(result.value == "int");
                }}
                version(all){{
                    auto result = getResult!(id!())("select!(true)(\"true\", \"false\")");
                    assert(result.match);
                    assert(result.rest.range == "");
                    assert(result.value == "select!(true)(\"true\", \"false\")");
                }}
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        }
    }

    /* nonterminal */ version(all){
        template nonterminal(){
            alias string ResultType;
            Result!(string, ResultType) apply(Positional!string input, ref memo_t memo){
                return combinateMemoize!(combinateConvert!(
                    id!(),
                    (string id) => "combinateMemoize!(" ~ id ~ "!())"
                )).apply(input, memo);
            }
        }

        debug(ctpg) unittest{
            enum dg = {
                version(all){{
                    auto result = getResult!(nonterminal!())("A");
                    assert(result.match);
                    assert(result.rest.range == "");
                    assert(result.value == "combinateMemoize!(A!())");
                }}
                version(all){{
                    auto result = getResult!(nonterminal!())("int");
                    assert(result.match);
                    assert(result.rest.range == "");
                    assert(result.value == "combinateMemoize!(int!())");
                }}
                version(all){{
                    auto result = getResult!(nonterminal!())("select!(true)(\"true\", \"false\")");
                    assert(result.match);
                    assert(result.rest.range == "");
                    assert(result.value == "combinateMemoize!(select!(true)(\"true\", \"false\")!())");
                }}
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        }
    }

    /* typeName */ version(all){
        template typeName(){
            alias string ResultType;
            Result!(string, ResultType) apply(Positional!string input, ref memo_t memo){
                return combinateMemoize!(combinateString!(
                    combinateMemoize!(combinateSequence!(
                        combinateMemoize!(combinateChoice!(
                            combinateMemoize!(parseCharRange!('A','Z')),
                            combinateMemoize!(parseCharRange!('a','z')),
                            combinateMemoize!(parseString!"_")
                        )),
                        combinateMemoize!(parseSpaces!()),
                        combinateMemoize!(combinateMore0!(
                            combinateMemoize!(combinateChoice!(
                                combinateMemoize!(parseCharRange!('0','9')),
                                combinateMemoize!(parseCharRange!('A','Z')),
                                combinateMemoize!(parseCharRange!('a','z')),
                                combinateMemoize!(parseString!"_"),
                                combinateMemoize!(parseString!","),
                                combinateMemoize!(parseString!"!"),
                                combinateMemoize!(arch!("(", ")")),
                                combinateMemoize!(arch!("[", "]"))
                            ))
                        ))
                    ))
                )).apply(input, memo);
            }
        }

        debug(ctpg) unittest{
            enum dg = {
                version(all){{
                    auto result = getResult!(typeName!())("int");
                    assert(result.match);
                    assert(result.rest.range == "");
                    assert(result.value == "int");
                }}
                version(all){{
                    auto result = getResult!(typeName!())("Tuple!(string, int)");
                    assert(result.match);
                    assert(result.rest.range == "");
                    assert(result.value == "Tuple!(string, int)");
                }}
                version(all){{
                    auto result = getResult!(typeName!())("int[]");
                    assert(result.match);
                    assert(result.rest.range == "");
                    assert(result.value == "int[]");
                }}
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        }
    }

    /* func */ version(all){
        template func(){
            alias string ResultType;
            Result!(Range, string) apply(Range)(Positional!Range input, ref memo_t memo){
                return combinateMemoize!(combinateConvert!(
                    combinateMemoize!(combinateSequence!(
                        combinateMemoize!(combinateOption!(
                            combinateMemoize!(combinateSequence!(
                                combinateMemoize!(arch!("(", ")")),
                                combinateMemoize!(parseSpaces!())
                            ))
                        )),
                        combinateMemoize!(arch!("{", "}"))
                    )),
                    (Option!string arch, string brace) => arch.some ? "function" ~ arch ~ brace : "function()" ~ brace
                )).apply(input, memo);
            }
        }

        debug(ctpg) unittest{
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
                assert(result.rest.range == "");
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
            debug(ctpg_ct) static assert(dg());
            dg();
        }
    }

    /* arch */ version(all){
        template arch(string open, string close){
            alias string ResultType;
            Result!(string, ResultType) apply(Positional!string input, ref memo_t memo){
                return combinateMemoize!(combinateConvert!(
                    combinateMemoize!(combinateSequence!(
                        combinateMemoize!(combinateNone!(
                            combinateMemoize!(parseString!open)
                        )),
                        combinateMemoize!(combinateMore0!(
                            combinateMemoize!(combinateChoice!(
                                combinateMemoize!(arch!(open, close)),
                                combinateMemoize!(combinateSequence!(
                                    combinateMemoize!(combinateNot!(
                                        combinateMemoize!(parseString!close)
                                    )),
                                    combinateMemoize!(parseAnyChar!())
                                ))
                            ))
                        )),
                        combinateMemoize!(combinateNone!(
                            combinateMemoize!(parseString!close)
                        ))
                    )),
                    (string[] strs) => open ~ strs.flat ~ close
                )).apply(input, memo);
            }
        }

        debug(ctpg) unittest{
            enum dg = {
                version(all){{
                    auto result = getResult!(arch!("(", ")"))("(a(i(u)e)o())");
                    assert(result.match);
                    assert(result.rest == positional("", 1, 14));
                    assert(result.value == "(a(i(u)e)o())");
                }}
                version(all){{
                    auto result = getResult!(arch!("[", "]"))("[a[i[u]e]o[]]");
                    assert(result.match);
                    assert(result.rest == positional("", 1, 14));
                    assert(result.value == "[a[i[u]e]o[]]");
                    return true;
                }}
                version(all){{
                    auto result = getResult!(arch!("{", "}"))("{a{i{u}e}o{}}");
                    assert(result.match);
                    assert(result.rest == positional("", 1, 14));
                    assert(result.value == "{a{i{u}e}o{}}");
                }}
                return true;
            };
            debug(ctpg_ct) static assert(dg());
            dg();
        }
    }
}

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
            result = to!string(arg);
        }
        return result;
    }
}

debug(ctpg) unittest{
    enum dg = {
        version(all){{
            auto result = flat(tuple(1, "hello", tuple(2, "world")));
            assert(result == "1hello2world");
        }}
        version(all){{
            auto result = flat(tuple([0, 1, 2], "hello", tuple([3, 4, 5], ["wor", "ld!!"]), ["!", "!"]));
            assert(result == "012hello345world!!!!");
        }}
        version(all){{
            auto result = flat(tuple('表', 'が', '怖', 'い', '噂', 'の', 'ソ', 'フ', 'ト'));
            assert(result == "表が怖い噂のソフト");
        }}
        version(all){{
            string[] ary;
            auto result = flat(tuple("A", ary));
            assert(result == "A");
        }}
        return true;
    };
    debug(ctpg_ct) static assert(dg());
    dg();
}

string mkString(string[] strs, string sep = ""){
    string result;
    foreach(i, str; strs){
        if(i){ result ~= sep; }
        result ~= str;
    }
    return result;
}

debug(ctpg) void main(){
    import std.stdio; writeln("unittest passed");
}

private:

debug(ctpg) version(unittest) template TestParser(T){
    alias T ResultType;
    Result!(Range, ResultType) apply(Range)(Positional!Range input, ref memo_t memo){
        typeof(return) result;
        return result;
    }
}

debug(ctpg) version(unittest) struct TestRange(T){
    immutable(T)[] source;
    @property T front(){ return source[0]; }
    @property void popFront(){ source = source[1..$]; }
    @property bool empty(){ return source.length == 0; }
    @property typeof(this) save(){ return this; }

    pure @safe nothrow
    bool opEquals(typeof(this) rhs){
        return source == rhs.source;
    }
}

debug(ctpg) version(unittest) TestRange!(T) testRange(T)(immutable(T)[] source){
    return TestRange!T(source);
}

template staticConvertString(string tstring, T){
    static if(is(T == string)){
        alias tstring staticConvertString;
    }else static if(is(T == wstring)){
        enum staticConvertString = mixin("\"" ~ tstring ~ "\"w");
    }else static if(is(T == dstring)){
        enum staticConvertString = mixin("\"" ~ tstring ~ "\"d");
    }else static if(isInputRange!T){
        static if(is(Unqual!(ElementType!T) == char)){
            alias tstring staticConvertString;
        }else static if(is(Unqual!(ElementType!T) == wchar)){
            enum staticConvertString = mixin("\"" ~ tstring ~ "\"w");
        }else static if(is(Unqual!(ElementType!T) == dchar)){
            enum staticConvertString = mixin("\"" ~ tstring ~ "\"d");
        }else{
            static assert(false);
        }
    }
}

debug(ctpg) unittest{
    static assert(staticConvertString!("foobar", string) == "foobar");
    static assert(staticConvertString!("foobar", wstring) == "foobar"w);
    static assert(staticConvertString!("foobar", dstring) == "foobar"d);
    static assert(staticConvertString!("foobar", TestRange!char) == "foobar");
    static assert(staticConvertString!("foobar", TestRange!wchar) == "foobar"w);
    static assert(staticConvertString!("foobar", TestRange!dchar) == "foobar"d);
}

Tuple!(size_t, "line", size_t, "column") countBreadth(string str)in{
    assert(str.length > 0);
}body{
    typeof(return) result;
    size_t idx;
    while(idx < str.length){
        auto c = std.utf.decode(str, idx);
        if(c == '\n'){
            result.line++;
            result.column = 0;
        }else{
            result.column++;
        }
    }
    return result;
}

debug(ctpg) unittest{
    static assert({
        version(all){{
            auto result = countBreadth("これ\nとこれ");
            assert(result.line == 1);
            assert(result.column == 3);
        }}
        version(all){{
            auto result = countBreadth("これ\nとこれ\nとさらにこれ");
            assert(result.line == 2);
            assert(result.column == 6);
        }}
        version(all){{
            auto result = countBreadth("helloワールド");
            assert(result.line == 0);
            assert(result.column == 9);
        }}
        return true;
    }());
}

template ParserType(alias parser){
    static if(is(parser.ResultType)){
        alias parser.ResultType ParserType;
    }else{
        static assert(false);
    }
}

debug(ctpg) unittest{
    static assert(is(ParserType!(TestParser!string) == string));
    static assert(is(ParserType!(TestParser!int) == int));
    static assert(is(ParserType!(TestParser!long) == long));

}

template flatTuple(T){
    static if(isTuple!T){
        alias T.Types flatTuple;
    }else{
        alias T flatTuple;
    }
}

debug(ctpg) unittest{
    static assert(is(flatTuple!(string) == string));
    static assert(is(flatTuple!(Tuple!(string)) == TypeTuple!string));
    static assert(is(flatTuple!(Tuple!(Tuple!(string))) == TypeTuple!(Tuple!string)));
}

template CombinateSequenceImplType(parsers...){
    alias Tuple!(staticMap!(flatTuple, staticMap!(ParserType, parsers))) CombinateSequenceImplType;
}

debug(ctpg) unittest{
    static assert(is(CombinateSequenceImplType!(TestParser!string, TestParser!string) == Tuple!(string, string)));
    static assert(is(CombinateSequenceImplType!(TestParser!int, TestParser!long) == Tuple!(int, long)));
    static assert(is(CombinateSequenceImplType!(TestParser!(Tuple!(int, long)), TestParser!uint) == Tuple!(int, long, uint)));
    static assert(is(CombinateSequenceImplType!(TestParser!(Tuple!(int, long)), TestParser!(Tuple!(uint, ulong))) == Tuple!(int, long, uint, ulong)));
    static assert(is(CombinateSequenceImplType!(TestParser!(Tuple!(Tuple!(byte, short), long)), TestParser!(Tuple!(uint, ulong))) == Tuple!(Tuple!(byte, short), long, uint, ulong)));
}

template UnTuple(T){
    static if(isTuple!T && T.Types.length == 1){
        alias T.Types[0] UnTuple;
    }else{
        alias T UnTuple;
    }
}

debug(ctpg) unittest{
    static assert(is(UnTuple!int == int));
    static assert(is(UnTuple!(Tuple!(int)) == int));
    static assert(is(UnTuple!(Tuple!(Tuple!(int))) == Tuple!int));
    static assert(is(UnTuple!(Tuple!(int, int)) == Tuple!(int, int)));
    static assert(is(UnTuple!(Tuple!(Tuple!(int, int))) == Tuple!(int, int)));
}

template CommonParserType(tparsers...){
    alias CommonType!(staticMap!(ParserType, tparsers)) CommonParserType;
}

debug(ctpg) unittest{
    static assert(is(CommonParserType!(TestParser!string, TestParser!string) == string));
    static assert(is(CommonParserType!(TestParser!int, TestParser!long) == long));
    static assert(is(CommonParserType!(TestParser!byte, TestParser!short, TestParser!int) == int));
    static assert(is(CommonParserType!(TestParser!string, TestParser!int) == void));
}

dchar decode(Range)(ref Range range){
    static assert(isSomeChar!(Unqual!(ElementType!Range)));
    dchar result;
    static if(is(Unqual!(ElementType!Range) == char)){
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
    }else static if(is(Unqual!(ElementType!Range) == wchar)){
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
    }else static if(is(Unqual!(ElementType!Range) == dchar)){
        result = range.front;
        range.popFront;
        return result;
    }
}

debug(ctpg) unittest{
    enum dg = {
        assert(decode([testRange("\u0001")][0]) == '\u0001');
        assert(decode([testRange("\u0081")][0]) == '\u0081');
        assert(decode([testRange("\u0801")][0]) == '\u0801');
        assert(decode([testRange("\U00012345")][0]) == '\U00012345');
        assert(decode([testRange("\u0001"w)][0]) == '\u0001');
        assert(decode([testRange("\uE001"w)][0]) == '\uE001');
        assert(decode([testRange("\U00012345"w)][0]) == '\U00012345');
        assert(decode([testRange("\U0010FFFE")][0]) == '\U0010FFFE');
        return true;
    };
    debug(ctpg_ct) static assert(dg());
    dg();
}

version(all) debug(ctpg) public:

mixin ctpg!q{
    int root = addExp $;

    int addExp = mulExp (("+" / "-") addExp)? >> (int lhs, Option!(Tuple!(string, int)) rhs){
        if(rhs.some){
            final switch(rhs.value[0]){
                case "+":{
                    return lhs + rhs.value[1];
                }
                case "-":{
                    return lhs - rhs.value[1];
                }
            }
        }else{
            return lhs;
        }
    };

    int mulExp = primary (("*" / "/") mulExp)? >> (int lhs, Option!(Tuple!(string, int)) rhs){
        if(rhs.some){
            final switch(rhs.value[0]){
                case "*":{
                    return lhs * rhs.value[1];
                }
                case "/":{
                    return lhs / rhs.value[1];
                }
            }
        }else{
            return lhs;
        }
    };

    int primary = !"(" addExp !")" / intLit_p;

    None recursive = A $;

    None A = !"a" !A !"a" / !"a";
};

unittest{
    enum dg = {
        version(all){{
            assert(parse!root("5*8+3*20") == 100);
            assert(parse!root("5*(8+3)*20") == 1100);
            try{
                parse!root("5*(8+3)20");
            }catch(Exception e){
                assert(e.msg == "1: 8: error EOF is needed");
            }
        }}
        version(all){{
            assert( isMatch!recursive("a"));
            assert( isMatch!recursive("aaa"));
            assert(!isMatch!recursive("aaaaa"));
            assert( isMatch!recursive("aaaaaaa"));
            assert(!isMatch!recursive("aaaaaaaaa"));
            assert(!isMatch!recursive("aaaaaaaaaaa"));
            assert(!isMatch!recursive("aaaaaaaaaaaaa"));
            assert( isMatch!recursive("aaaaaaaaaaaaaaa"));
        }}
        return true;
    };
    debug(ctpg_ct) static assert(dg());
    dg();
}
