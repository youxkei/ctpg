// Written in the D programming language.

/**
 * Example of recursive parsing.
 */

import ctpg;

mixin generateParsers!q{
    None recursive = A $;

    None A = !"a" !A !"a" / !"a";
};

void main(){
    enum dg = {
        assert( isMatch!recursive("a"));
        assert( isMatch!recursive("aaa"));
        assert(!isMatch!recursive("aaaaa"));
        assert( isMatch!recursive("aaaaaaa"));
        assert(!isMatch!recursive("aaaaaaaaa"));
        assert(!isMatch!recursive("aaaaaaaaaaa"));
        assert(!isMatch!recursive("aaaaaaaaaaaaa"));
        assert( isMatch!recursive("aaaaaaaaaaaaaaa"));
        return true;
    };
    static assert(dg());
    dg();
}

