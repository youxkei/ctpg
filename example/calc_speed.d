
// Written in the D programming language.

/**
 * Example of parsing simple arithmetic expession.
 */

import ctpg;
import std.array:    join;
import std.conv:     to;
import std.stdio:    writeln;
import std.datetime: Clock;

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

string[] generateExps(){
    string [] exps;
    foreach(char c; '1'..'9' + 1)
        foreach(char d; '0'..'9' + 1)
            foreach(char e; '0'..'9' + 1)
                foreach(char f; '0'..'9' + 1)
                    exps ~= "" ~ c ~ d ~ e ~ f ~ "+7+(33/(6+5)*3)";
    return exps;
}

const exps = generateExps();
enum times = exps.length;

void main(){
    auto time = Clock.currAppTick;
    foreach(exp; exps)
        parse!root(exp);
    ((Clock.currAppTick - time).usecs / (times * 1.0)).writeln(" usecs");
}
