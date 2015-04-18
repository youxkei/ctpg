module ctpg.unsupported_input_type_exception;

class UnsupportedInputTypeException: Exception
{
    this(string msg)
    {
        super(msg);
    }
}
