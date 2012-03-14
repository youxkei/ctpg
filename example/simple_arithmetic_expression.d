// Written in the D programming language.

/**
 * Example of parsing simple arithmetic expession.
 */

import ctpg;
import std.conv: to;

mixin(generateParsers(q{
    int root = addExp $;

    int addExp =
          mulExp !"+" addExp >> (int lhs, int rhs){ return lhs + rhs; }
        / mulExp !"-" addExp >> (int lhs, int rhs){ return lhs - rhs; }
        / mulExp;

    int mulExp =
          primary !"*" mulExp >> (int lhs, int rhs){ return lhs * rhs; }
        / primary !"/" mulExp >> (int lhs, int rhs){ return lhs / rhs; }
        / primary;

    int primary = !"(" addExp !")" / int_;

    int int_ = s( [0-9]+ ) >> (string int_){ return to!int(int_); };
}));

void main(){
    enum dg ={
        assert(parse!root("5*8+3*20") == 100);
        assert(parse!root("5*(8+3)*20") == 1100);
        try{
            parse!root("5*(8+3)20");
        }catch(Exception e){
            assert(e.msg == "1: error EOF is needed");
        } 
        return true;
    };
    static assert(dg());
    pragma(msg, parse!root("5*8+3*50"));
    import std.stdio; writeln(parse!root("5*(8+3)*50"));
    dg();
}

