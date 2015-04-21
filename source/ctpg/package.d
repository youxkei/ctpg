module ctpg;

import ctpg.caller      : Caller;
import ctpg.input       : Input;
import ctpg.parser_kind : ParserKind;


auto parse(alias parser, alias kind = ParserKind!(true, true), SrcType)(SrcType src, size_t line = __LINE__ , string file = __FILE__) if(__traits(compiles, parser.build))
{
    return parser.build!(kind, SrcType).parse(Input!SrcType(src), Caller(line, file));
}

auto parse(alias parser, alias kind = ParserKind!(true, true), SrcType)(SrcType src, size_t line = __LINE__ , string file = __FILE__) if(__traits(compiles, parser!().build))
{
    return parser!().build!(kind, SrcType).parse(Input!SrcType(src), Caller(line, file));
}
