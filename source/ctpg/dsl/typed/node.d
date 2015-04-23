module ctpg.dsl.typed.node;

import ctpg.dsl.typed.token : Token;

struct Node
{
    Token token;
    Node[] children;

    size_t line;
    string file;

    string toString(string indent = "", bool last = true)
    {
        string res;
        size_t lastIndex = children.length - 1;

        res = indent ~ "+-[" ~ token.text ~ "]\n";
        foreach(i, child; children)
        {
            if(i == lastIndex)
            {
                res ~= child.toString(indent ~ (last ? "   " : "|  "), true);
            }
            else
            {
                res ~= child.toString(indent ~ (last ? "   " : "|  "), false);
            }
        }

        return res;
    }
}
