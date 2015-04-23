// Written in the D programming language.

/**
 * Example of parsing simple arithmetic expession.
 */

import std.array: join;
import std.conv: to;
import std.stdio;
import std.algorithm;

import ctpg : parse;
import ctpg.parsers : skip;
import ctpg.dsl.typed : CTPG_DSL_TYPED;

import compile_time_unittest : enableCompileTimeUnittest;
mixin enableCompileTimeUnittest;


class SimpleArithmeticParser
{
    mixin CTPG_DSL_TYPED!
    q{
        @_setSkip(skip)

        // root parser
        int root = addExp $;

        // addition and subtraction
        int addExp =
              mulExp !"+" addExp >> (lhs, rhs){ return lhs + rhs; }
            / mulExp !"-" addExp >> (lhs, rhs){ return lhs - rhs; }
            / mulExp;

        // multiplication and division
        int mulExp =
              primary !"*" mulExp >> (lhs, rhs){ return lhs * rhs; }
            / primary !"/" mulExp >> (lhs, rhs){ return lhs / rhs; }
            / primary;

        int primary = !"(" addExp !")" / [0-9]+ >> to!int;
    };
}

unittest
{
    assert(parse!(SimpleArithmeticParser.root)("5 * 8 + 3 * 20").value == 100);
    assert(parse!(SimpleArithmeticParser.root)("5 * ( 8 + 3 ) * 20").value == 1100);
    assert(parse!(SimpleArithmeticParser.root)("5 * 8 + 3 * 20".map!(to!wchar)()).value == 100);

    assert(!parse!(SimpleArithmeticParser.root)("5 * ( 8 + 3 ) 20").match);
}
