// Written in the D programming language.

/**
 * Example of simple json parsing.
 */

import std.array : assocArray, join;
import std.conv : to;
import std.json : JSONValue, JSON_TYPE;
import std.typecons : Tuple;

import ctpg : parse;
import ctpg.parsers : skip, anyChar;
import ctpg.dsl.typed : CTPG_DSL_TYPED;

import compile_time_unittest : enableCompileTimeUnittest;
mixin enableCompileTimeUnittest;


mixin CTPG_DSL_TYPED!
q{
    @_setSkip(skip)

    JSONValue json = num / str / true_ / false_ / array / object_ / null_;

    JSONValue num = [0-9]+ >> to!int >> JSONValue;

    JSONValue str = stringLiteral >> JSONValue;

    JSONValue true_  = !"true"  >> { return JSONValue(true); };
    JSONValue false_ = !"false" >> { return JSONValue(false); };

    JSONValue array = !"[" json*<","> !"]" >> JSONValue;

    JSONValue object_ = !"{" (stringLiteral !":" json)*<","> !"}" >> assocArray >> JSONValue;

    JSONValue null_ = !"null" >> { return JSONValue(null); };

    string stringLiteral = !"\"" (^"\"" ("\\\"" / (anyChar >> to!string)))* !"\"" >> join >> to!string;
};

unittest
{
    assert (parse!json("42").value.integer == 42);
    assert (parse!json(`"foo"`).value.str == "foo");
    assert (parse!json(`"foo\nbar"`).value.str == "foo\\nbar");
    assert (parse!json("true").value.type == JSON_TYPE.TRUE);
    assert (parse!json("false").value.type == JSON_TYPE.FALSE);
    with (parse!json("[0, 2, 4]"))
    {
        assert (value[0].integer == 0);
        assert (value[1].integer == 2);
        assert (value[2].integer == 4);
    }
    with (parse!json(`{ "foo": "bar", "bar": "buz" }`))
    {
        assert (match);
    }
    assert (parse!json("null").value.type == JSON_TYPE.NULL);
}
