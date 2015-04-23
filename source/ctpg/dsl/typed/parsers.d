module ctpg.dsl.typed.parsers;

import std.typecons : Tuple;

import ctpg : parse;

import ctpg.caller : Caller;
import ctpg.input : Input;
import ctpg.macro_ : MAKE_RESULT;
import ctpg.none : None;
import ctpg.option : Option;
import ctpg.parse_result : ParseResult;
import ctpg.parser_kind : ParserKind;

import ctpg.dsl.typed.node : Node;
import ctpg.dsl.typed.token : Token, TokenType;

import parsers = ctpg.parsers;
import combinators = ctpg.combinators;
import ownCombinators = ctpg.dsl.typed.combinators;

import compile_time_unittest : enableCompileTimeUnittest;
mixin enableCompileTimeUnittest;


template identifier()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ SrcType };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinators.inputSlice!
            (
                combinators.sequence!
                (
                    combinators.choice!
                    (
                        parsers.charRange!('a', 'z'),
                        parsers.charRange!('A', 'Z'),
                        parsers.string_!"_",
                    ),
                    combinators.more0!
                    (
                        combinators.choice!
                        (
                            parsers.charRange!('a', 'z'),
                            parsers.charRange!('A', 'Z'),
                            parsers.charRange!('0', '9'),
                            parsers.string_!"_",
                        )
                    )
                )
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    with(parse!identifier("_ab0="))
    {
        assert(match              == true);
        assert(nextInput.source   == "=");
        assert(value              == "_ab0");
    }
}


template doubleQuotedString()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ SrcType };

        static Result parse(Input!SrcType input, in Caller caller)
        {
            return combinators.inputSlice!
            (
                combinators.sequence!
                (
                    parsers.string_!`"`,
                    combinators.more0!
                    (
                        combinators.sequence!
                        (
                            combinators.notPred!
                            (
                                parsers.string_!`"`
                            ),
                            combinators.choice!
                            (
                                parsers.string_!`\"`,
                                parsers.anyChar!()
                            )
                        )
                    ),
                    parsers.string_!`"`
                )
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}


template wysiwygString()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ SrcType };

        static Result parse(Input!SrcType input, in Caller caller)
        {
            return combinators.inputSlice!
            (
                combinators.sequence!
                (
                    parsers.string_!`r"`,
                    combinators.more0!
                    (
                        combinators.sequence!
                        (
                            combinators.notPred!
                            (
                                parsers.string_!`"`
                            ),
                            parsers.anyChar!()
                        )
                    ),
                    parsers.string_!`"`
                )
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}


template alternateWysiwygString()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ SrcType };

        static Result parse(Input!SrcType input, in Caller caller)
        {
            return combinators.inputSlice!
            (
                combinators.sequence!
                (
                    parsers.string_!"`",
                    combinators.more0!
                    (
                        combinators.sequence!
                        (
                            combinators.notPred!
                            (
                                parsers.string_!"`"
                            ),
                            parsers.anyChar!()
                        )
                    ),
                    parsers.string_!"`"
                )
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}


template stringLiteral()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ SrcType };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinators.inputSlice!
            (
                combinators.choice!
                (
                    wysiwygString!(),
                    alternateWysiwygString!(),
                    doubleQuotedString!()
                )
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    with(parse!stringLiteral(`"foo"`))
    {
        assert(match            == true);
        assert(value            == `"foo"`);
        assert(nextInput.source == "");
    }

    with(parse!stringLiteral(`"foo\nbar"`))
    {
        assert(match            == true);
        assert(value            == `"foo\nbar"`);
        assert(nextInput.source == "");
    }

    with(parse!stringLiteral(`"foo\"bar"`))
    {
        assert(match            == true);
        assert(value            == `"foo\"bar"`);
        assert(nextInput.source == "");
    }

    with(parse!stringLiteral(`"foo"bar"`))
    {
        assert(match            == true);
        assert(value            == `"foo"`);
        assert(nextInput.source == `bar"`);
    }

    with(parse!stringLiteral(`r"foo\"bar"`))
    {
        assert(match            == true);
        assert(value            == `r"foo\"`);
        assert(nextInput.source == `bar"`);
    }

    with(parse!stringLiteral("`foo`bar`"))
    {
        assert(match            == true);
        assert(value            == "`foo`");
        assert(nextInput.source == "bar`");
    }
}


// 一行コメントを消費するパーサ
template lineComment()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ None };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinators.none!
            (
                combinators.sequence!
                (
                    parsers.string_!"//",
                    combinators.more0!
                    (
                        combinators.sequence!
                        (
                            combinators.notPred!
                            (
                                parsers.string_!"\n"
                            ),
                            parsers.anyChar!()
                        )
                    ),
                    parsers.string_!"\n"
                )
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{

    with(parse!(lineComment!(), ParserKind!(true, true))("// comment\nnot comment"))
    {
        assert(match              == true);
        assert(value              == None());
        assert(nextInput.source   == "not comment");
    }

    with(parse!(lineComment!(), ParserKind!(true, true))("// not terminated comment"))
    {
        assert(match          == false);
        assert(error.position == 25);
        assert(error.msg      == "'\n' expected");
    }
}


// 普通のコメントを消費するパーサ
template ordinaryComment()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ None };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinators.none!
            (
                combinators.sequence!
                (
                    parsers.string_!"/*",
                    combinators.more0!
                    (
                        combinators.sequence!
                        (
                            combinators.notPred!
                            (
                                parsers.string_!"*/"
                            ),
                            parsers.anyChar!()
                        )
                    ),
                    parsers.string_!"*/"
                )
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    with(parse!(ordinaryComment!(), ParserKind!(true, true))("/* comment */not comment"))
    {
        assert(match              == true);
        assert(nextInput.source   == "not comment");
    }

    with(parse!(ordinaryComment!(), ParserKind!(true, true))("/* not terminated comment"))
    {
        assert(match          == false);
        assert(error.position == 25);
        assert(error.msg      == "'*/' expected");
    }
}


// ネストされたコメントを消費するパーサ
template nestedComment()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ None };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinators.none!
            (
                combinators.sequence!
                (
                    parsers.string_!"/+",
                    combinators.more0!
                    (
                        combinators.choice!
                        (
                            nestedComment!(),
                            combinators.sequence!
                            (
                                combinators.notPred!
                                (
                                    parsers.string_!"+/"
                                ),
                                parsers.anyChar!()
                            )
                        )
                    ),
                    parsers.string_!"+/"
                )
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    with(parse!(nestedComment!(), ParserKind!(true, true))("/+ comment +/not comment"))
    {
        assert(match              == true);
        assert(nextInput.source   == "not comment");
    }

    with(parse!(nestedComment!(), ParserKind!(true, true))("/+ comment  /+ inner comment +/ comment +/not comment"))
    {
        assert(match              == true);
        assert(nextInput.source   == "not comment");
    }

    with(parse!(nestedComment!(), ParserKind!(true, true))("/+ not terminated comment"))
    {
        assert(match          == false);
        assert(error.position == 25);
        assert(error.msg      == "'+/' expected");
    }
}


// スキップされるべき空白を消費するパーサ
template spaces()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ None };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinators.none!
            (
                combinators.more0!
                (
                    combinators.choice!
                    (
                        parsers.string_!" ",
                        parsers.string_!"\n",
                        parsers.string_!"\t",
                        parsers.string_!"\r",
                        parsers.string_!"\f",
                        lineComment!(),
                        ordinaryComment!(),
                        nestedComment!()
                    )
                )
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    with(parse!(spaces!(), ParserKind!(true, true))("/* a */// b \nc"))
    {
        assert(match              == true);
        assert(nextInput.source   == "c");
    }

    with(parse!(spaces!(), ParserKind!(true, true))("0/* a */// b \nc"))
    {
        assert(match              == true);
        assert(nextInput.source   == "0/* a */// b \nc");
    }
}


template arch(string open, string close)
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ string };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinators.inputSlice!
            (
                combinators.sequence!
                (
                    parsers.string_!open,
                    combinators.more0!
                    (
                        combinators.choice!
                        (
                            arch!(open, close),
                            combinators.sequence!
                            (
                                combinators.notPred!
                                (
                                    parsers.string_!close
                                ),
                                combinators.choice!
                                (
                                    stringLiteral!(),
                                    parsers.anyChar!()
                                )
                            )
                        )
                    ),
                    parsers.string_!close
                )
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    with(parse!(arch!("(", ")"), ParserKind!(true, true))("((a(b)c)d(e))f"))
    {
        assert(match              == true);
        assert(nextInput.source   == "f");
        assert(value              == "((a(b)c)d(e))");
    }

    with(parse!(arch!("(", ")"), ParserKind!(true, true))("((a(b)c)d(e)"))
    {
        assert(match          == false);
        assert(error.position == 12);
        assert(error.msg      == "')' expected");
    }
}


template func()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return ownCombinators.makeNode!
            (
                combinators.inputSlice!
                (
                    combinators.sequence!
                    (
                        combinators.option!
                        (
                            arch!("(", ")")
                        ),
                        arch!("{", "}")
                    )
                ),
                TokenType.CONVERTER
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    with(parse!(func!(), ParserKind!(true, true))(q"<(a, b, c){ return "{}" ~ r"{}" ~ `{}` ~ a ~ b ~ c; }>"))
    {
        assert(match                 == true);
        assert(nextInput.source == "");
        assert(value.token.type            == TokenType.CONVERTER);
        assert(value.token.text           == q"<(a, b, c){ return "{}" ~ r"{}" ~ `{}` ~ a ~ b ~ c; }>");
        assert(value.children.length == 0);
    }

    with(parse!(func!(), ParserKind!(true, true))(q"<(a, b, c{ return "{}" ~ r"{}" ~ `{}` ~ a ~ b ~ c; }>"))
    {
        assert(match == false);
        assert(error.msg == "')' expected");
        assert(error.position == 51);
    }

    with(parse!(func!(), ParserKind!(true, true))(q"<(a, b, c){ return "{}" ~ r"{}" ~ `{}` ~ a ~ b ~ c; >"))
    {
        assert(match == false);
        assert(error.msg == "'}' expected");
        assert(error.position == 51);
    }
}


template id()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!string input, in Caller caller)
        {
            return ownCombinators.makeNode!
            (
                combinators.changeError!
                (
                    identifier!(),
                    "identifier expected"
                ),
                TokenType.ID
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    with(parse!(id!(), ParserKind!(true, true))("_ab0="))
    {
        assert(match                 == true);
        assert(nextInput.source      == "=");
        assert(value.token.type            == TokenType.ID);
        assert(value.token.text           == "_ab0");
        assert(value.children.length == 0);
    }

    with(parse!(id!(), ParserKind!(true, true))("__hogehoge12345678"))
    {
        assert(match                 == true);
        assert(nextInput.source == "");
        assert(value.token.type            == TokenType.ID);
        assert(value.token.text           == "__hogehoge12345678");
        assert(value.children.length == 0);
    }

    with(parse!(id!(), ParserKind!(true, true))("ああ"))
    {
        assert(match          == false);
        assert(error.msg      == "identifier expected");
        assert(error.position == 0);
    }
}


template nonterminal()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!string input, in Caller caller)
        {
            return ownCombinators.makeNode!
            (
                combinators.changeError!
                (
                    identifier!(),
                    "identifier expected"
                ),
                TokenType.NONTERMINAL
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    with(parse!(nonterminal!(), ParserKind!(true, true))("_ab0="))
    {
        assert(match                 == true);
        assert(nextInput.source      == "=");
        assert(value.token.type            == TokenType.NONTERMINAL);
        assert(value.token.text           == "_ab0");
        assert(value.children.length == 0);
    }

    with(parse!(nonterminal!(), ParserKind!(true, true))("__hogehoge12345678"))
    {
        assert(match                 == true);
        assert(nextInput.source == "");
        assert(value.token.type            == TokenType.NONTERMINAL);
        assert(value.token.text           == "__hogehoge12345678");
        assert(value.children.length == 0);
    }

    with(parse!(nonterminal!(), ParserKind!(true, true))("ああ"))
    {
        assert(match          == false);
        assert(error.msg      == "identifier expected");
        assert(error.position == 0);
    }
}


template typeName()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return ownCombinators.makeNode!
            (
                combinators.inputSlice!
                (
                    combinators.sequence!
                    (
                        combinators.choice!
                        (
                            parsers.charRange!('A','Z'),
                            parsers.charRange!('a','z'),
                            parsers.string_!"_"
                        ),
                        combinators.more0!
                        (
                            combinators.choice!
                            (
                                parsers.charRange!('0','9'),
                                parsers.charRange!('A','Z'),
                                parsers.charRange!('a','z'),
                                parsers.string_!"_",
                                parsers.string_!"!",
                                arch!("(", ")"),
                                arch!("[", "]")
                            )
                        )
                    )
                ),
                TokenType.TEMPLATE_INSTANCE
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    with(parse!(typeName!(), ParserKind!(true, true))("hoge"))
    {
        assert(match == true);
        assert(nextInput.source == "");
        assert(value.token.type == TokenType.TEMPLATE_INSTANCE);
        assert(value.token.text == "hoge");
        assert(value.children.length == 0);
    }
}


template eofLit()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!string input, in Caller caller)
        {
            return ownCombinators.makeNode!
            (
                parsers.string_!"$",
                TokenType.DOLLAR
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    with(parse!(eofLit!(), ParserKind!(true, true))("$"))
    {
        assert(match                 == true);
        assert(nextInput.source == "");
        assert(value.token.type            == TokenType.DOLLAR);
        assert(value.token.text           == "$");
        assert(value.children.length == 0);
    }

    with(parse!(eofLit!(), ParserKind!(true, true))("hoge"))
    {
        assert(match          == false);
        assert(error.msg      == "'$' expected");
        assert(error.position == 0);
    }
}


template rangeLitOneChar()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return ownCombinators.makeNode!
            (
                combinators.inputSlice!
                (
                    parsers.anyChar!()
                ),
                TokenType.RANGE_ONE_CHAR
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    with(parse!(rangeLitOneChar!(), ParserKind!(true, true))("a"))
    {
        assert(match == true);
        assert(nextInput.source == "");
        assert(value.token.type == TokenType.RANGE_ONE_CHAR);
        assert(value.token.text == "a");
        assert(value.children.length == 0);
    }

    with(parse!(rangeLitOneChar!(), ParserKind!(true, true))("鬱"))
    {
        assert(match == true);
        assert(nextInput.source == "");
        assert(value.token.type == TokenType.RANGE_ONE_CHAR);
        assert(value.token.text == "鬱");
        assert(value.children.length == 0);
    }
}


template rangeLitCharRange()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return ownCombinators.setInfo!
            (
                combinators.convert!
                (
                    combinators.untuple!
                    (
                        combinators.sequence!
                        (
                            rangeLitOneChar!(),
                            combinators.none!
                            (
                                parsers.string_!"-"
                            ),
                            rangeLitOneChar!()
                        ),
                    ),
                    (Node begin, Node end) => Node(Token(TokenType.RANGE_CHAR_RANGE, "-"), [begin, end])
                )
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    with(parse!(rangeLitCharRange!(), ParserKind!(true, true))("a-z"))
    {
        assert(match                             == true);
        assert(nextInput.source == "");
        assert(value.token.type                        == TokenType.RANGE_CHAR_RANGE);
        assert(value.token.text                       == "-");
        assert(value.children.length             == 2);
        assert(value.children[0].token.type            == TokenType.RANGE_ONE_CHAR);
        assert(value.children[0].token.text           == "a");
        assert(value.children[0].children.length == 0);
        assert(value.children[1].token.type            == TokenType.RANGE_ONE_CHAR);
        assert(value.children[1].token.text           == "z");
        assert(value.children[1].children.length == 0);
    }

    with(parse!(rangeLitCharRange!(), ParserKind!(true, true))("躁-鬱"))
    {
        assert(match                             == true);
        assert(nextInput.source == "");
        assert(value.token.type                        == TokenType.RANGE_CHAR_RANGE);
        assert(value.token.text                       == "-");
        assert(value.children.length             == 2);
        assert(value.children[0].token.type            == TokenType.RANGE_ONE_CHAR);
        assert(value.children[0].token.text           == "躁");
        assert(value.children[0].children.length == 0);
        assert(value.children[1].token.type            == TokenType.RANGE_ONE_CHAR);
        assert(value.children[1].token.text           == "鬱");
        assert(value.children[1].children.length == 0);
    }
}


template rangeLit()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return ownCombinators.setInfo!
            (
                combinators.convert!
                (
                    combinators.untuple!
                    (
                        combinators.sequence!
                        (
                            combinators.none!
                            (
                                parsers.string_!"["
                            ),
                            combinators.more1!
                            (
                                combinators.untuple!
                                (
                                    combinators.sequence!
                                    (
                                        combinators.notPred!
                                        (
                                            parsers.string_!"]"
                                        ),
                                        combinators.choice!
                                        (
                                            rangeLitCharRange!(),
                                            rangeLitOneChar!()
                                        )
                                    )
                                )
                            ),
                            combinators.none!
                            (
                                parsers.string_!"]"
                            )
                        ),
                    ),
                    (Node[] children) => Node(Token(TokenType.RANGE, "RANGE_LIT"), children)
                )
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    with(parse!(rangeLit!(), ParserKind!(true, true))("[a-zあ躁-鬱]"))
    {
        assert(match                                         == true);
        assert(nextInput.source == "");
        assert(value.token.type                                    == TokenType.RANGE);
        assert(value.token.text                                   == "RANGE_LIT");
        assert(value.children.length                         == 3);
        assert(value.children[0].token.type                        == TokenType.RANGE_CHAR_RANGE);
        assert(value.children[0].token.text                       == "-");
        assert(value.children[0].children.length             == 2);
        assert(value.children[0].children[0].token.type            == TokenType.RANGE_ONE_CHAR);
        assert(value.children[0].children[0].token.text           == "a");
        assert(value.children[0].children[0].children.length == 0);
        assert(value.children[0].children[1].token.type            == TokenType.RANGE_ONE_CHAR);
        assert(value.children[0].children[1].token.text           == "z");
        assert(value.children[0].children[1].children.length == 0);
        assert(value.children[1].token.type                        == TokenType.RANGE_ONE_CHAR);
        assert(value.children[1].token.text                       == "あ");
        assert(value.children[1].children.length             == 0);
        assert(value.children[2].token.type                        == TokenType.RANGE_CHAR_RANGE);
        assert(value.children[2].token.text                       == "-");
        assert(value.children[2].children.length             == 2);
        assert(value.children[2].children[0].token.type            == TokenType.RANGE_ONE_CHAR);
        assert(value.children[2].children[0].token.text           == "躁");
        assert(value.children[2].children[0].children.length == 0);
        assert(value.children[2].children[1].token.type            == TokenType.RANGE_ONE_CHAR);
        assert(value.children[2].children[1].token.text           == "鬱");
        assert(value.children[2].children[1].children.length == 0);
    }
}


template stringLit()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return ownCombinators.makeNode!
            (
                stringLiteral!(),
                TokenType.STRING
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    with(parse!(stringLit!(), ParserKind!(true, true))(q{"hoge"}))
    {
        assert(match == true);
        assert(nextInput.source == "");
        assert(value.token.type == TokenType.STRING);
        assert(value.token.text == q{"hoge"});
        assert(value.children.length == 0);
    }

    with(parse!(stringLit!(), ParserKind!(true, true))(q{r"hoge\"}))
    {
        assert(match == true);
        assert(nextInput.source == "");
        assert(value.token.type == TokenType.STRING);
        assert(value.token.text == q{r"hoge\"});
        assert(value.children.length == 0);
    }

    with(parse!(stringLit!(), ParserKind!(true, true))(q{`"hoge"`}))
    {
        assert(match == true);
        assert(nextInput.source == "");
        assert(value.token.type == TokenType.STRING);
        assert(value.token.text == q{`"hoge"`});
        assert(value.children.length == 0);
    }
}


template literal()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinators.choice!
            (
                eofLit!(),
                rangeLit!(),
                stringLit!()
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    with(parse!(literal!(), ParserKind!(true, true))("$"))
    {
        assert(match                 == true);
        assert(nextInput.source == "");
        assert(value.token.type            == TokenType.DOLLAR);
        assert(value.token.text           == "$");
        assert(value.children.length == 0);
    }

    with(parse!(literal!(), ParserKind!(true, true))("[a-zあ躁-鬱]"))
    {
        assert(match                                         == true);
        assert(nextInput.source == "");
        assert(value.token.type                                    == TokenType.RANGE);
        assert(value.token.text                                   == "RANGE_LIT");
        assert(value.children.length                         == 3);
        assert(value.children[0].token.type                        == TokenType.RANGE_CHAR_RANGE);
        assert(value.children[0].token.text                       == "-");
        assert(value.children[0].children.length             == 2);
        assert(value.children[0].children[0].token.type            == TokenType.RANGE_ONE_CHAR);
        assert(value.children[0].children[0].token.text           == "a");
        assert(value.children[0].children[0].children.length == 0);
        assert(value.children[0].children[1].token.type            == TokenType.RANGE_ONE_CHAR);
        assert(value.children[0].children[1].token.text           == "z");
        assert(value.children[0].children[1].children.length == 0);
        assert(value.children[1].token.type                        == TokenType.RANGE_ONE_CHAR);
        assert(value.children[1].token.text                       == "あ");
        assert(value.children[1].children.length             == 0);
        assert(value.children[2].token.type                        == TokenType.RANGE_CHAR_RANGE);
        assert(value.children[2].token.text                       == "-");
        assert(value.children[2].children.length             == 2);
        assert(value.children[2].children[0].token.type            == TokenType.RANGE_ONE_CHAR);
        assert(value.children[2].children[0].token.text           == "躁");
        assert(value.children[2].children[0].children.length == 0);
        assert(value.children[2].children[1].token.type            == TokenType.RANGE_ONE_CHAR);
        assert(value.children[2].children[1].token.text           == "鬱");
        assert(value.children[2].children[1].children.length == 0);
    }

    with(parse!(literal!(), ParserKind!(true, true))(q{"hoge"}))
    {
        assert(match == true);
        assert(nextInput.source == "");
        assert(value.token.type == TokenType.STRING);
        assert(value.token.text == q{"hoge"});
        assert(value.children.length == 0);
    }

    with(parse!(literal!(), ParserKind!(true, true))(q{r"hoge\"}))
    {
        assert(match == true);
        assert(nextInput.source == "");
        assert(value.token.type == TokenType.STRING);
        assert(value.token.text == q{r"hoge\"});
        assert(value.children.length == 0);
    }

    with(parse!(literal!(), ParserKind!(true, true))(q{`"hoge"`}))
    {
        assert(match == true);
        assert(nextInput.source == "");
        assert(value.token.type == TokenType.STRING);
        assert(value.token.text == q{`"hoge"`});
        assert(value.children.length == 0);
    }

    with(parse!(literal!(), ParserKind!(true, true))("hoge"))
    {
        assert(match          == false);
        assert(error.msg      == "'\"' expected");
        assert(error.position == 0);
    }
}


template primaryExp()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinators.choice!
            (
                stringLit!(),
                rangeLit!(),
                eofLit!(),
                combinators.untuple!
                (
                    combinators.sequence!
                    (
                        combinators.none!
                        (
                            parsers.string_!"("
                        ),
                        spaces!(),
                        choiceExp!(),
                        spaces!(),
                        combinators.none!
                        (
                            parsers.string_!")"
                        )
                    )
                ),
                nonterminal!()
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    with(parse!(primaryExp!(), ParserKind!(true, true))("$"))
    {
        assert(match                 == true);
        assert(nextInput.source == "");
        assert(value.token.type            == TokenType.DOLLAR);
        assert(value.token.text           == "$");
        assert(value.children.length == 0);
    }

    with(parse!(primaryExp!(), ParserKind!(true, true))("($)"))
    {
        assert(match                 == true);
        assert(nextInput.source == "");
        assert(value.token.type            == TokenType.DOLLAR);
        assert(value.token.text           == "$");
        assert(value.children.length == 0);
    }

    with(parse!(primaryExp!(), ParserKind!(true, true))("_ab0="))
    {
        assert(match                 == true);
        assert(nextInput.source      == "=");
        assert(value.token.type            == TokenType.NONTERMINAL);
        assert(value.token.text           == "_ab0");
        assert(value.children.length == 0);
    }
}


template preExp()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinators.convert!
            (
                combinators.sequence!
                (
                    combinators.option!
                    (
                        combinators.choice!
                        (
                            parsers.string_!"!",
                            parsers.string_!"&",
                            parsers.string_!"^"
                        )
                    ),
                    primaryExp!(),
                ),
                function(Option!string op, Node primaryExp)
                {
                    if(op.some)
                    {
                        Node preExp;

                        final switch(op.value)
                        {
                            case "!":
                                preExp.token.type = TokenType.EXCLAM;
                                break;
                            case "&":
                                preExp.token.type = TokenType.ANPERSAND;
                                break;
                            case "^":
                                preExp.token.type = TokenType.ASCIICIRCUM;
                                break;
                        }
                        preExp.token.text = op;
                        preExp.children ~= primaryExp;

                        return preExp;
                    }
                    else
                    {
                        return primaryExp;
                    }
                }
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    with(parse!(preExp!(), ParserKind!(true, true))("!$"))
    {
        assert(match                             == true);
        assert(nextInput.source == "");
        assert(value.token.type                        == TokenType.EXCLAM);
        assert(value.token.text                       == "!");
        assert(value.children.length             == 1);
        assert(value.children[0].token.type            == TokenType.DOLLAR);
        assert(value.children[0].token.text           == "$");
        assert(value.children[0].children.length == 0);
    }

    with(parse!(preExp!(), ParserKind!(true, true))("&$"))
    {
        assert(match                             == true);
        assert(nextInput.source == "");
        assert(value.token.type                        == TokenType.ANPERSAND);
        assert(value.token.text                       == "&");
        assert(value.children.length             == 1);
        assert(value.children[0].token.type            == TokenType.DOLLAR);
        assert(value.children[0].token.text           == "$");
        assert(value.children[0].children.length == 0);
    }

    with(parse!(preExp!(), ParserKind!(true, true))("^$"))
    {
        assert(match                             == true);
        assert(nextInput.source                  == "");
        assert(value.token.type                        == TokenType.ASCIICIRCUM);
        assert(value.token.text                       == "^");
        assert(value.children.length             == 1);
        assert(value.children[0].token.type            == TokenType.DOLLAR);
        assert(value.children[0].token.text           == "$");
        assert(value.children[0].children.length == 0);
    }

    with(parse!(preExp!(), ParserKind!(true, true))("$"))
    {
        assert(match                 == true);
        assert(nextInput.source      == "");
        assert(value.token.type            == TokenType.DOLLAR);
        assert(value.token.text           == "$");
        assert(value.children.length == 0);
    }
}


template postExp()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinators.convert!
            (
                combinators.sequence!
                (
                    preExp!(),
                    combinators.option!
                    (
                        combinators.sequence!
                        (
                            combinators.choice!
                            (
                                parsers.string_!"*",
                                parsers.string_!"+",
                            ),
                            combinators.option!
                            (
                                combinators.untuple!
                                (
                                    combinators.sequence!
                                    (
                                        combinators.none!
                                        (
                                            parsers.string_!"<"
                                        ),
                                        choiceExp!(),
                                        combinators.none!
                                        (
                                            parsers.string_!">"
                                        )
                                    )
                                )
                            )
                        )
                    )
                ),
                function(Node preExp, Option!(Tuple!(string, Option!Node)) op)
                {
                    if(op.some)
                    {
                        Node postExp;

                        final switch(op[0])
                        {
                            case "*":
                                postExp.token.type = TokenType.ASTERISK;
                                break;
                            case "+":
                                postExp.token.type = TokenType.PLUS;
                                break;
                        }

                        postExp.token.text = op[0];
                        postExp.children ~= preExp;

                        if(op[1].some)
                        {
                            postExp.children ~= op[1];
                        }

                        return postExp;
                    }
                    else
                    {
                        return preExp;
                    }
                }
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    with(parse!(postExp!(), ParserKind!(true, true))("$*"))
    {
        assert(match == true);
        assert(nextInput.source    == "");
        assert(value.token.type == TokenType.ASTERISK);
        assert(value.token.text == "*");
        assert(value.children.length == 1);
        assert(value.children[0].token.type == TokenType.DOLLAR);
        assert(value.children[0].token.text == "$");
        assert(value.children[0].children.length == 0);
    }

    with(parse!(postExp!(), ParserKind!(true, true))("$+"))
    {
        assert(match == true);
        assert(nextInput.source    == "");
        assert(value.token.type == TokenType.PLUS);
        assert(value.token.text == "+");
        assert(value.children.length == 1);
        assert(value.children[0].token.type == TokenType.DOLLAR);
        assert(value.children[0].token.text == "$");
        assert(value.children[0].children.length == 0);
    }

    with(parse!(postExp!(), ParserKind!(true, true))("$*<$>"))
    {
        assert(match == true);
        assert(nextInput.source    == "");
        assert(value.token.type == TokenType.ASTERISK);
        assert(value.token.text == "*");
        assert(value.children.length == 2);
        assert(value.children[0].token.type == TokenType.DOLLAR);
        assert(value.children[0].token.text == "$");
        assert(value.children[0].children.length == 0);
        assert(value.children[1].token.type == TokenType.DOLLAR);
        assert(value.children[1].token.text == "$");
        assert(value.children[1].children.length == 0);
    }

    with(parse!(postExp!(), ParserKind!(true, true))("$+<$>"))
    {
        assert(match == true);
        assert(nextInput.source    == "");
        assert(value.token.type == TokenType.PLUS);
        assert(value.token.text == "+");
        assert(value.children.length == 2);
        assert(value.children[0].token.type == TokenType.DOLLAR);
        assert(value.children[0].token.text == "$");
        assert(value.children[0].children.length == 0);
        assert(value.children[1].token.type == TokenType.DOLLAR);
        assert(value.children[1].token.text == "$");
        assert(value.children[1].children.length == 0);
    }
}


template optionExp()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinators.convert!
            (
                combinators.sequence!
                (
                    postExp!(),
                    combinators.option!
                    (
                        combinators.none!
                        (
                            parsers.string_!"?"
                        )
                    )
                ),
                function(Node postExp, Option!None op)
                {
                    if(op.some)
                    {
                        Node optionExp;

                        optionExp.token.type = TokenType.QUESTION;
                        optionExp.token.text = "?";
                        optionExp.children ~= postExp;

                        return optionExp;
                    }
                    else
                    {
                        return postExp;
                    }
                }
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    with(parse!(optionExp!(), ParserKind!(true, true))("$?"))
    {
        assert(match == true);
        assert(nextInput.source    == "");
        assert(value.token.type == TokenType.QUESTION);
        assert(value.token.text == "?");
        assert(value.children.length == 1);
        assert(value.children[0].token.type == TokenType.DOLLAR);
        assert(value.children[0].token.text == "$");
        assert(value.children[0].children.length == 0);
    }
}


template seqExp()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinators.convert!
            (
                combinators.more1!
                (
                    optionExp!(),
                    spaces!()
                ),
                function(Node[] optionExps)
                {
                    if(optionExps.length > 1)
                    {
                        Node seqExp;

                        seqExp.token.type = TokenType.SEQUENCE;
                        seqExp.token.text = "SEQ";
                        seqExp.children = optionExps;

                        return seqExp;
                    }
                    else
                    {
                        return optionExps[0];
                    }
                }
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    with(parse!(seqExp!(), ParserKind!(true, true))("$"))
    {
        assert(match                 == true);
        assert(nextInput.source    == "");
        assert(value.token.type            == TokenType.DOLLAR);
        assert(value.token.text           == "$");
        assert(value.children.length == 0);
    }

    with(parse!(seqExp!(), ParserKind!(true, true))("$ $"))
    {
        assert(match                             == true);
        assert(nextInput.source    == "");
        assert(value.token.type                        == TokenType.SEQUENCE);
        assert(value.token.text                       == "SEQ");
        assert(value.children.length             == 2);
        assert(value.children[0].token.type            == TokenType.DOLLAR);
        assert(value.children[0].token.text           == "$");
        assert(value.children[0].children.length == 0);
        assert(value.children[1].token.type            == TokenType.DOLLAR);
        assert(value.children[1].token.text           == "$");
        assert(value.children[1].children.length == 0);
    }
}


template convExp()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinators.convert!
            (
                combinators.sequence!
                (
                    seqExp!(),
                    combinators.more0!
                    (
                        combinators.untuple!
                        (
                            combinators.sequence!
                            (
                                spaces!(),
                                parsers.getLine!(),
                                parsers.getCallerLine!(),
                                parsers.getCallerFile!(),
                                combinators.choice!
                                (
                                    parsers.string_!">?",
                                    parsers.string_!">>"
                                ),
                                spaces!(),
                                combinators.choice!
                                (
                                    func!(),
                                    typeName!()
                                )
                            )
                        )
                    )
                ),
                function(Node seqExp, Tuple!(size_t, size_t, string, string, Node)[] funcs)
                {
                    Node result = seqExp;

                    foreach(func; funcs)
                    {
                        Node node;

                        size_t line = func[0];
                        size_t callerLine = func[1];
                        string callerFile = func[2];
                        string op = func[3];
                        Node funcNode = func[4];

                        node.token.type = op == ">>" ? TokenType.LEFT_SHIFT : TokenType.LEFT_QUESTION;
                        node.token.text = op;
                        node.children ~= result;
                        node.children ~= funcNode;
                        node.line = line + callerLine + 1;
                        node.file = callerFile;

                        result = node;
                    }

                    return result;
                }
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    with(parse!(convExp!(), ParserKind!(true, true))("$"))
    {
        assert(match == true);
        assert(nextInput.source    == "");
        assert(value.token.type            == TokenType.DOLLAR);
        assert(value.token.text           == "$");
        assert(value.children.length == 0);
    }

    with(parse!(convExp!(), ParserKind!(true, true))("$ >> hoge"))
    {
        assert(match == true);
        assert(nextInput.source    == "");
        assert(value.token.type == TokenType.LEFT_SHIFT);
        assert(value.token.text == ">>");
        assert(value.line == __LINE__ - 5);
        assert(value.file == __FILE__);
        assert(value.children.length == 2);
        assert(value.children[0].token.type            == TokenType.DOLLAR);
        assert(value.children[0].token.text           == "$");
        assert(value.children[0].children.length == 0);
        assert(value.children[1].token.type            == TokenType.TEMPLATE_INSTANCE);
        assert(value.children[1].token.text           == "hoge");
        assert(value.children[1].children.length == 0);
    }

    with(parse!(convExp!(), ParserKind!(true, true))("$ >> hoge >> piyo"))
    {
        assert(match                                         == true);
        assert(nextInput.source    == "");
        assert(value.token.type                                    == TokenType.LEFT_SHIFT);
        assert(value.token.text                                   == ">>");
        assert(value.line                                    == __LINE__ - 5);
        assert(value.file                                    == __FILE__);
        assert(value.children.length                         == 2);
        assert(value.children[0].token.type                        == TokenType.LEFT_SHIFT);
        assert(value.children[0].token.text                       == ">>");
        assert(value.children[0].line                        == __LINE__ - 10);
        assert(value.children[0].file                        == __FILE__);
        assert(value.children[0].children.length             == 2);
        assert(value.children[0].children[0].token.type            == TokenType.DOLLAR);
        assert(value.children[0].children[0].token.text           == "$");
        assert(value.children[0].children[0].children.length == 0);
        assert(value.children[0].children[1].token.type            == TokenType.TEMPLATE_INSTANCE);
        assert(value.children[0].children[1].token.text           == "hoge");
        assert(value.children[0].children[1].children.length == 0);
        assert(value.children[1].token.type                        == TokenType.TEMPLATE_INSTANCE);
        assert(value.children[1].token.text                       == "piyo");
        assert(value.children[1].children.length             == 0);
    }

    with(parse!(convExp!(), ParserKind!(true, true))("$ >> hoge >? piyo"))
    {
        assert(match == true);
        assert(nextInput.source    == "");
        assert(value.token.type == TokenType.LEFT_QUESTION);
        assert(value.token.text == ">?");
        assert(value.children.length == 2);
        assert(value.children[0].token.type == TokenType.LEFT_SHIFT);
        assert(value.children[0].token.text == ">>");
        assert(value.children[0].children.length == 2);
        assert(value.children[0].children[0].token.type            == TokenType.DOLLAR);
        assert(value.children[0].children[0].token.text           == "$");
        assert(value.children[0].children[0].children.length == 0);
        assert(value.children[0].children[1].token.type            == TokenType.TEMPLATE_INSTANCE);
        assert(value.children[0].children[1].token.text           == "hoge");
        assert(value.children[0].children[1].children.length == 0);
        assert(value.children[1].token.type            == TokenType.TEMPLATE_INSTANCE);
        assert(value.children[1].token.text           == "piyo");
        assert(value.children[1].children.length == 0);
    }

    with(parse!(convExp!(), ParserKind!(true, true))("$ >> (a, b){ return a + b; }"))
    {
        assert(match == true);
        assert(nextInput.source    == "");
        assert(value.token.type == TokenType.LEFT_SHIFT);
        assert(value.token.text == ">>");
        assert(value.children.length == 2);
        assert(value.children[0].token.type            == TokenType.DOLLAR);
        assert(value.children[0].token.text           == "$");
        assert(value.children[0].children.length == 0);
        assert(value.children[1].token.type            == TokenType.CONVERTER);
        assert(value.children[1].token.text           == q{(a, b){ return a + b; }});
        assert(value.children[1].children.length == 0);
    }
}


template choiceExp()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinators.convert!
            (
                combinators.sequence!
                (
                    spaces!(),
                    parsers.getLine!(),
                    parsers.getCallerLine!(),
                    parsers.getCallerFile!(),
                    combinators.more1!
                    (
                        convExp!(),
                        combinators.sequence!
                        (
                            spaces!(),
                            parsers.string_!"/",
                            spaces!()
                        )
                    )
                ),
                function(size_t line, size_t callerLine, string callerFile, Node[] convExps)
                {
                    if(convExps.length > 1)
                    {
                        Node choiceExp;

                        choiceExp.token.type = TokenType.SLASH;
                        choiceExp.token.text = "/";
                        choiceExp.children = convExps;
                        choiceExp.line = line + callerLine + 1;
                        choiceExp.file = callerFile;

                        return choiceExp;
                    }
                    else
                    {
                        return convExps[0];
                    }
                }
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    with(parse!(choiceExp!(), ParserKind!(true, true))("$"))
    {
        assert(match                 == true);
        assert(nextInput.source    == "");
        assert(value.token.type            == TokenType.DOLLAR);
        assert(value.token.text           == "$");
        assert(value.children.length == 0);
    }

    with(parse!(choiceExp!(), ParserKind!(true, true))("$ "))
    {
        assert(match                 == true);
        assert(nextInput.source    == " ");
        assert(value.token.type            == TokenType.DOLLAR);
        assert(value.token.text           == "$");
        assert(value.children.length == 0);
    }

    with(parse!(choiceExp!(), ParserKind!(true, true))("$ / $"))
    {
        assert(match                             == true);
        assert(nextInput.source    == "");
        assert(value.token.type                        == TokenType.SLASH);
        assert(value.token.text                       == "/");
        assert(value.children.length             == 2);
        assert(value.children[0].token.type            == TokenType.DOLLAR);
        assert(value.children[0].token.text           == "$");
        assert(value.children[0].children.length == 0);
        assert(value.children[1].token.type            == TokenType.DOLLAR);
        assert(value.children[1].token.text           == "$");
        assert(value.children[1].children.length == 0);
    }
}


template def()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinators.convert!
            (
                combinators.sequence!
                (
                    combinators.option!
                    (
                        combinators.untuple!
                        (
                            combinators.sequence!
                            (
                                combinators.none!
                                (
                                    parsers.string_!"@setSkip(",
                                ),
                                spaces!(),
                                choiceExp!(),
                                spaces!(),
                                combinators.none!
                                (
                                    parsers.string_!")"
                                ),
                                spaces!()
                            )
                        )
                    ),
                    typeName!(),
                    spaces!(),
                    id!(),
                    spaces!(),
                    combinators.none!
                    (
                        parsers.string_!"="
                    ),
                    spaces!(),
                    choiceExp!(),
                    spaces!(),
                    combinators.none!
                    (
                        parsers.string_!";"
                    )
                ),
                function(Option!Node skip, Node type, Node name, Node choiceExp)
                {
                    Node def;

                    def.token.type = TokenType.DEFINITION;
                    def.children ~= type;
                    def.children ~= name;

                    if(skip.some)
                    {
                        Node skipNode;

                        skipNode.token.type = TokenType.SET_SKIP;
                        skipNode.children ~= skip;
                        skipNode.children ~= choiceExp;

                        def.children ~= skipNode;
                    }
                    else
                    {
                        def.children ~= choiceExp;
                    }

                    return def;
                }
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    with(parse!(def!(), ParserKind!(true, true))(q{int hoge = $;}))
    {
        assert(match                             == true);
        assert(nextInput.source    == "");
        assert(value.token.type                        == TokenType.DEFINITION);
        assert(value.children.length             == 3);
        assert(value.children[0].token.type            == TokenType.TEMPLATE_INSTANCE);
        assert(value.children[0].token.text           == "int");
        assert(value.children[0].children.length == 0);
        assert(value.children[1].token.type            == TokenType.ID);
        assert(value.children[1].token.text           == "hoge");
        assert(value.children[1].children.length == 0);
        assert(value.children[2].token.type            == TokenType.DOLLAR);
        assert(value.children[2].token.text           == "$");
        assert(value.children[2].children.length == 0);
    }

    with(parse!(def!(), ParserKind!(true, true))(q{@setSkip($) int hoge = $;}))
    {
        assert(match                                               == true);
        assert(nextInput.source    == "");
        assert(value.token.type                                    == TokenType.DEFINITION);
        assert(value.children.length                               == 3);
        assert(value.children[0].token.type                        == TokenType.TEMPLATE_INSTANCE);
        assert(value.children[0].token.text                        == "int");
        assert(value.children[0].children.length                   == 0);
        assert(value.children[1].token.type                        == TokenType.ID);
        assert(value.children[1].token.text                        == "hoge");
        assert(value.children[1].children.length                   == 0);
        assert(value.children[2].token.type                        == TokenType.SET_SKIP);
        assert(value.children[2].children.length                   == 2);
        assert(value.children[2].children[0].token.type            == TokenType.DOLLAR);
        assert(value.children[2].children[0].token.text            == "$");
        assert(value.children[2].children[0].children.length       == 0);
        assert(value.children[2].children[1].token.type            == TokenType.DOLLAR);
        assert(value.children[2].children[1].token.text            == "$");
        assert(value.children[2].children[1].children.length       == 0);
    }
}


template defaultSkip()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinators.convert!
            (
                combinators.untuple!
                (
                    combinators.sequence!
                    (
                        combinators.none!
                        (
                            parsers.string_!"@_setSkip("
                        ),
                        spaces!(),
                        choiceExp!(),
                        spaces!(),
                        combinators.none!
                        (
                            parsers.string_!")"
                        )
                    )
                ),
                function(Node skip)
                {
                    Node setSkipNode;

                    setSkipNode.token.type = TokenType.GLOBAL_SET_SKIP;
                    setSkipNode.children ~= skip;

                    return setSkipNode;
                }
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}


template defs()
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return combinators.convert!
            (
                combinators.untuple!
                (
                    combinators.sequence!
                    (
                        spaces!(),
                        combinators.more0!
                        (
                            combinators.choice!
                            (
                                defaultSkip!(),
                                def!()
                            ),
                            spaces!()
                        ),
                        spaces!(),
                        parsers.eof!()
                    )
                ),
                function(Node[] nodes)
                {
                    Node defs;

                    defs.token.type = TokenType.DEFINITIONS;
                    defs.children = nodes;

                    return defs;
                }
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    with(parse!(defs!(), ParserKind!(true, true))(q{int hoge = $; int piyo = $;}))
    {
        assert(match                                         == true);
        assert(nextInput.source    == "");
        assert(value.token.type                                    == TokenType.DEFINITIONS);
        assert(value.children.length                         == 2);
        assert(value.children[0].token.type                        == TokenType.DEFINITION);
        assert(value.children[0].children.length             == 3);
        assert(value.children[0].children[0].token.type            == TokenType.TEMPLATE_INSTANCE);
        assert(value.children[0].children[0].token.text           == "int");
        assert(value.children[0].children[0].children.length == 0);
        assert(value.children[0].children[1].token.type            == TokenType.ID);
        assert(value.children[0].children[1].token.text           == "hoge");
        assert(value.children[0].children[1].children.length == 0);
        assert(value.children[0].children[2].token.type            == TokenType.DOLLAR);
        assert(value.children[0].children[2].token.text           == "$");
        assert(value.children[0].children[2].children.length == 0);
        assert(value.children[1].token.type                        == TokenType.DEFINITION);
        assert(value.children[1].children.length             == 3);
        assert(value.children[1].children[0].token.type            == TokenType.TEMPLATE_INSTANCE);
        assert(value.children[1].children[0].token.text           == "int");
        assert(value.children[1].children[0].children.length == 0);
        assert(value.children[1].children[1].token.type            == TokenType.ID);
        assert(value.children[1].children[1].token.text           == "piyo");
        assert(value.children[1].children[1].children.length == 0);
        assert(value.children[1].children[2].token.type            == TokenType.DOLLAR);
        assert(value.children[1].children[2].token.text           == "$");
        assert(value.children[1].children[2].children.length == 0);
    }

    with(parse!(defs!(), ParserKind!(true, true))(q{@setSkip($) int hoge = $; @setSkip($) int piyo = $;}))
    {
        assert(match                                                     == true);
        assert(nextInput.source    == "");
        assert(value.token.type                                          == TokenType.DEFINITIONS);
        assert(value.children.length                                     == 2);
        assert(value.children[0].token.type                              == TokenType.DEFINITION);
        assert(value.children[0].children.length                         == 3);
        assert(value.children[0].children[0].token.type                  == TokenType.TEMPLATE_INSTANCE);
        assert(value.children[0].children[0].token.text                  == "int");
        assert(value.children[0].children[0].children.length             == 0);
        assert(value.children[0].children[1].token.type                  == TokenType.ID);
        assert(value.children[0].children[1].token.text                  == "hoge");
        assert(value.children[0].children[1].children.length             == 0);
        assert(value.children[0].children[2].token.type                  == TokenType.SET_SKIP);
        assert(value.children[0].children[2].children.length             == 2);
        assert(value.children[0].children[2].children[0].token.type      == TokenType.DOLLAR);
        assert(value.children[0].children[2].children[0].token.text      == "$");
        assert(value.children[0].children[2].children[0].children.length == 0);
        assert(value.children[0].children[2].children[1].token.type      == TokenType.DOLLAR);
        assert(value.children[0].children[2].children[1].token.text      == "$");
        assert(value.children[0].children[2].children[1].children.length == 0);
        assert(value.children[1].token.type                              == TokenType.DEFINITION);
        assert(value.children[1].children.length                         == 3);
        assert(value.children[1].children[0].token.type                  == TokenType.TEMPLATE_INSTANCE);
        assert(value.children[1].children[0].token.text                  == "int");
        assert(value.children[1].children[0].children.length             == 0);
        assert(value.children[1].children[1].token.type                  == TokenType.ID);
        assert(value.children[1].children[1].token.text                  == "piyo");
        assert(value.children[1].children[1].children.length             == 0);
        assert(value.children[1].children[2].token.type                  == TokenType.SET_SKIP);
        assert(value.children[1].children[2].children.length             == 2);
        assert(value.children[1].children[2].children[0].token.type      == TokenType.DOLLAR);
        assert(value.children[1].children[2].children[0].token.text      == "$");
        assert(value.children[1].children[2].children[0].children.length == 0);
        assert(value.children[1].children[2].children[1].token.type      == TokenType.DOLLAR);
        assert(value.children[1].children[2].children[1].token.text      == "$");
        assert(value.children[1].children[2].children[1].children.length == 0);
    }

    with(parse!(defs!(), ParserKind!(true, true))(q{@_setSkip($) @setSkip($) int hoge = $; @setSkip($) int piyo = $;}))
    {
        assert(match                                                     == true);
        assert(nextInput.source    == "");
        assert(value.token.type                                                == TokenType.DEFINITIONS);
        assert(value.children.length                                     == 3);
        assert(value.children[0].token.type                                    == TokenType.GLOBAL_SET_SKIP);
        assert(value.children[0].children.length                         == 1);
        assert(value.children[0].children[0].token.type                        == TokenType.DOLLAR);
        assert(value.children[0].children[0].token.text                       == "$");
        assert(value.children[0].children[0].children.length             == 0);
        assert(value.children[1].token.type                              == TokenType.DEFINITION);
        assert(value.children[1].children.length                         == 3);
        assert(value.children[1].children[0].token.type                  == TokenType.TEMPLATE_INSTANCE);
        assert(value.children[1].children[0].token.text                  == "int");
        assert(value.children[1].children[0].children.length             == 0);
        assert(value.children[1].children[1].token.type                  == TokenType.ID);
        assert(value.children[1].children[1].token.text                  == "hoge");
        assert(value.children[1].children[1].children.length             == 0);
        assert(value.children[1].children[2].token.type                  == TokenType.SET_SKIP);
        assert(value.children[1].children[2].children.length             == 2);
        assert(value.children[1].children[2].children[0].token.type      == TokenType.DOLLAR);
        assert(value.children[1].children[2].children[0].token.text      == "$");
        assert(value.children[1].children[2].children[0].children.length == 0);
        assert(value.children[1].children[2].children[1].token.type      == TokenType.DOLLAR);
        assert(value.children[1].children[2].children[1].token.text      == "$");
        assert(value.children[1].children[2].children[1].children.length == 0);
        assert(value.children[2].token.type                              == TokenType.DEFINITION);
        assert(value.children[2].children.length                         == 3);
        assert(value.children[2].children[0].token.type                  == TokenType.TEMPLATE_INSTANCE);
        assert(value.children[2].children[0].token.text                  == "int");
        assert(value.children[2].children[0].children.length             == 0);
        assert(value.children[2].children[1].token.type                  == TokenType.ID);
        assert(value.children[2].children[1].token.text                  == "piyo");
        assert(value.children[2].children[1].children.length             == 0);
        assert(value.children[2].children[2].token.type                  == TokenType.SET_SKIP);
        assert(value.children[2].children[2].children.length             == 2);
        assert(value.children[2].children[2].children[0].token.type      == TokenType.DOLLAR);
        assert(value.children[2].children[2].children[0].token.text      == "$");
        assert(value.children[2].children[2].children[0].children.length == 0);
        assert(value.children[2].children[2].children[1].token.type      == TokenType.DOLLAR);
        assert(value.children[2].children[2].children[1].token.text      == "$");
        assert(value.children[2].children[2].children[1].children.length == 0);
    }
}
