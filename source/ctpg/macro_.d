module ctpg.macro_;

mixin template MAKE_RESULT(string MixiningType)
{
    static if(kind.hasValue)
    {
        mixin("alias Result = ParseResult!(kind, SrcType, " ~ MixiningType ~ ");");
    }
    else
    {
        alias Result = ParseResult!(kind, SrcType);
    }
}

