module ctpg._is;

template _is(T, string op, F) if (op == "==")
{
    enum _is = is(T == F);
}

template _is(T, string op, F) if (op == ":")
{
    enum _is = is(T : F);
}
