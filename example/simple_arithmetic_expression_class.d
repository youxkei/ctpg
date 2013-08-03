
import ctpg;
import std.array: join;
import std.conv: to;
import std.stdio;
import std.algorithm;

class Foo
{
    int result;

    mixin(genParsers(
    q{
        @_setSkip(skip)

        int root = addExp $;

        int addExp =
              mulExp !"+" addExp >> (lhs, rhs){ return lhs + rhs; }
            / mulExp !"-" addExp >> (lhs, rhs){ return lhs - rhs; }
            / mulExp;

        int mulExp =
              primary !"*" mulExp >> (lhs, rhs){ return lhs * rhs; }
            / primary !"/" mulExp >> (lhs, rhs){ return lhs / rhs; }
            / primary;

        int primary = !"(" addExp !")" / [0-9]+ >> to!int;
    }));

    void frop()
    {
        result = parse!root("5*8").value;
    }
}

void main()
{
    Foo foo = new Foo;
    foo.frop();
}
