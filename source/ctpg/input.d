module ctpg.input;

import std.array : save;

struct Input(SrcType)
{
    SrcType source;
    size_t position;
    size_t line;

    @property
    Input save()
    {
        return Input(source.save, position, line);
    }
}
