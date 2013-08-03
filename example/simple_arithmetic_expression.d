// Written in the D programming language.

/**
 * Example of parsing simple arithmetic expession.
 */

import ctpg;
import std.array: join;
import std.conv: to;
import std.stdio;
import std.algorithm;

mixin(genParsers(
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
}));

void main()
{
    static bool test()
    {
        assert(parse!root("5 * 8 + 3 * 20").value == 100);
        assert(parse!root("5 * ( 8 + 3 ) * 20").value == 1100);
        assert(parse!root("5 * 8 + 3 * 20".map!(to!wchar)()).value == 100);

        assert(!parse!root("5 * ( 8 + 3 ) 20").match);

        return true;
    };

    static assert(test());
    test();

    pragma(msg, "Compile time: " ~ parse!root("5 * 8 + 3 * 50".map!(to!dchar)).value.to!string());
    writeln(    "Runtime:      " ~ parse!root("5 * 8 + 3 * 50".map!(to!dchar)).value.to!string());
}
