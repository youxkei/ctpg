module ctpg.is_wrapper;

template isSameType(T, F)
{
    enum isSameType = is (T == F);
}

template isImplicitlyConvertible(From, To)
{
    enum isImplicitlyConvertible = is (From : To);
}
