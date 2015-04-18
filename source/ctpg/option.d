module ctpg.option;

struct Option(T)
{
    bool some;
    T value;
    alias value this;
}
