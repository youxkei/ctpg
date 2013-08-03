// Written in the D programming language.

/**
 * Example of recursive parsing.
 */

import ctpg;

mixin (genParsers(
q{
    // root parser
    None recursive = A $;

    None A = !"a" !A !"a" / !"a";
}));

void main(){
    static bool test(){
        assert( parse!recursive("a").match);
        assert( parse!recursive("aaa").match);
        assert(!parse!recursive("aaaaa").match);
        assert( parse!recursive("aaaaaaa").match);
        assert(!parse!recursive("aaaaaaaaa").match);
        assert(!parse!recursive("aaaaaaaaaaa").match);
        assert(!parse!recursive("aaaaaaaaaaaaa").match);
        assert( parse!recursive("aaaaaaaaaaaaaaa").match);
        return true;
    }
    static assert(test());
    test();
}

