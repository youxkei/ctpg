module ctpg.dsl.typed.token;

import std.conv : to;

enum TokenType
{
    UNDEFINED,

    // 単一トークン
    CONVERTER,
    ID,
    DOLLAR,
    TEMPLATE_INSTANCE,
    NONTERMINAL,
    RANGE_ONE_CHAR,
    RANGE_CHAR_RANGE,
    RANGE,
    STRING,

    // 再帰的なトークン
    EXCLAM,
    ANPERSAND,
    ASCIICIRCUM,
    ASTERISK,
    PLUS,
    QUESTION,
    SEQUENCE,
    LEFT_SHIFT,
    LEFT_QUESTION,
    SLASH,
    DEFINITION,
    DEFINITIONS,

    // 構文定義内で使える@トークン
    SKIP,// SET_SKIPで指定されたスキップパーサでスキップする
    SKIP_WITH, // これ自身が指定したスキップパーサでスキップする
    SET_SKIP, // スキップパーサを設定する
    MEMOIZE, // メモ化する

    SKIP_LITERAL_TRUE,
    SKIP_LITERAL_FALSE,
    MEMOIZE_SKIP_TRUE,
    MEMOIZE_SKIP_FALSE,
    MEMOIZE_LITERAL_TRUE,
    MEMOIZE_LITERAL_FALSE,
    MEMOIZE_NONTERMINAL_TRUE,
    MEMOIZE_NONTERMINAL_FALSE,

    // 構文定義外で使える@トークン
    GLOBAL_SET_SKIP,

    GLOBAL_SKIP_LITERAL_TRUE,
    GLOBAL_SKIP_LITERAL_FALSE,
    GLOBAL_MEMOIZE_SKIP_TRUE,
    GLOBAL_MEMOIZE_SKIP_FALSE,
    GLOBAL_MEMOIZE_LITERAL_TRUE,
    GLOBAL_MEMOIZE_LITERAL_FALSE,
    GLOBAL_MEMOIZE_NONTERMINAL_TRUE,
    GLOBAL_MEMOIZE_NONTERMINAL_FALSE,
}

struct Token
{
    TokenType type;
    string text_;

    string text() @property 
    {
        return text_.length == 0 ? type.to!string() : text_;
    }

    void text(string text_) @property
    {
        this.text_ = text_;
    }
}
