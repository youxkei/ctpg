// Written in the D programming language.

/**
 * Example of recursive parsing.
 */

import ctpg : parse;
import ctpg.none : None;
import ctpg.dsl.typed : CTPG_DSL_TYPED;

import compile_time_unittest : enableCompileTimeUnittest;
mixin enableCompileTimeUnittest;

mixin CTPG_DSL_TYPED!
q{
    // root parser
    None recursive = A $;

    None A = !"a" !A !"a" / !"a";
};

unittest
{
    assert( parse!recursive("a").match);
    assert( parse!recursive("aaa").match);
    assert(!parse!recursive("aaaaa").match);
    assert( parse!recursive("aaaaaaa").match);
    assert(!parse!recursive("aaaaaaaaa").match);
    assert(!parse!recursive("aaaaaaaaaaa").match);
    assert(!parse!recursive("aaaaaaaaaaaaa").match);
    assert( parse!recursive("aaaaaaaaaaaaaaa").match);
}
