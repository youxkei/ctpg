module ctpg.parser_kind;

import std.traits : TypeTuple;

template ParserKind(bool hasValue_, bool hasError_)
{
    enum hasValue = hasValue_;
    enum hasError = hasError_;
}

alias ParserKinds = TypeTuple!(ParserKind!(true, true),
                               ParserKind!(true, false),
                               ParserKind!(false, true),
                               ParserKind!(false, false));
