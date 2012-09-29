// Written in the D programming language.

/**
 * Example of parsing simple arithmetic expession.
 */

import ctpg;
import std.array: join;
import std.conv: to;
import std.stdio;

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
        int root = mulExp $;

        int mulExp =
              primary !"*" mulExp >> (lhs, rhs){ return lhs * rhs; }
            / primary;

        int primary = !"(" mulExp !")" / [0-9]+ >> join >> to!int;
    }));

    void frop(){
        result = parse!root("5*8");
    }
}

void main(){
    enum dg ={
        assert(parse!root("5 * 8 + 3 * 20") == 100);
        assert(parse!root("5 * ( 8 + 3 ) * 20") == 1100);
        try{
            parse!root("5 * ( 8 + 3 ) 20");
        }catch(Exception e){
            assert(e.msg == "1: error EOF is needed");
        } 
        return true;
    };
    static assert(dg());
    pragma(msg, parse!root("5*8+3*50"));
    writeln(parse!root("5*(8+3)*50"));
    dg();
    Foo foo = new Foo;
    foo.frop();
}
