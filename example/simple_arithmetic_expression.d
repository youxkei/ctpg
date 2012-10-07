// Written in the D programming language.

/**
 * Example of parsing simple arithmetic expession.
 */

import ctpg;
import std.array: join;
import std.conv: to;
import std.stdio;
import std.algorithm;

mixin(generateParsers(q{
    @default_skip(defaultSkip)

    int root = addExp $;

    int addExp =
          mulExp !"+" addExp >> (lhs, rhs){ return lhs + rhs; }
        / mulExp !"-" addExp >> (lhs, rhs){ return lhs - rhs; }
        / mulExp;

    int mulExp =
          primary !"*" mulExp >> (lhs, rhs){ return lhs * rhs; }
        / primary !"/" mulExp >> (lhs, rhs){ return lhs / rhs; }
        / primary;

    int primary = !"(" addExp !")" / [0-9]+ >> join >> to!int;
}));

class Foo{
    int result;

    mixin(generateParsers(q{
        @default_skip(defaultSkip)

        int root = addExp $;

        int addExp =
              mulExp !"+" addExp >> (lhs, rhs){ return lhs + rhs; }
            / mulExp !"-" addExp >> (lhs, rhs){ return lhs - rhs; }
            / mulExp;

        int mulExp =
              primary !"*" mulExp >> (lhs, rhs){ return lhs * rhs; }
            / primary !"/" mulExp >> (lhs, rhs){ return lhs / rhs; }
            / primary;

        int primary = !"(" addExp !")" / [0-9]+ >> join >> to!int;
    }));

    void frop(){
        result = parse!root("5*8").value;
    }
}

void main(){
    enum dg ={
        assert(parse!root("5 * 8 + 3 * 20").value == 100);
        assert(parse!root("5 * ( 8 + 3 ) * 20").value == 1100);
        assert(!parse!root("5 * ( 8 + 3 ) 20").match);
        return true;
    };
    static assert(dg());
    dg();
    assert(parse!root("5 * 8 + 3 * 20".map!(to!wchar)()).value == 100);
    pragma(msg, parse!root("5 * 8 + 3 * 50").value);
    writeln(parse!root("5 * ( 8 + 3 ) * 50").value);
    Foo foo = new Foo;
    foo.frop();
}
