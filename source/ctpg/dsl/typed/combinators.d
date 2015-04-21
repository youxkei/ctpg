module ctpg.dsl.typed.combinators;

import ctpg : parse;

import ctpg.is_wrapper : isSameType;
import ctpg.for_unittest : TestParser;
import ctpg.caller : Caller;
import ctpg.input : Input;
import ctpg.macro_ : MAKE_RESULT;
import ctpg.parse_result : ParseResult, getParseResultType;
import ctpg.parser_kind : ParserKind;

import ctpg.dsl.typed.token : Token, TokenType;
import ctpg.dsl.typed.node : Node;

import parsers = ctpg.parsers;
import combinators = ctpg.combinators;

import compile_time_unittest : enableCompileTimeUnittest;
mixin enableCompileTimeUnittest;


// 自動でnodeのlineとfileをセットするようにするコンビネータ
template setInfo(alias parser)
{
    template build(alias kind, SrcType)
    {
        static if(isSameType!(getParseResultType!(parser.build!(kind, SrcType)), Node))
        {
            mixin MAKE_RESULT!q{ Node };

            Result parse(Input!SrcType input, in Caller caller)
            {
                return combinators.convert!
                (
                    combinators.sequence!
                    (
                        parsers.getLine!(),
                        parsers.getCallerLine!(),
                        parsers.getCallerFile!(),
                        parser
                    ),
                    (size_t line, size_t callerLine, string callerFile, Node node)
                    {
                        node.line = callerLine + line + 1;
                        node.file = callerFile;

                        return node;
                    }
                ).build!(kind, SrcType).parse(input, caller);
            }
        }
        else
        {
            static assert(false);
        }
    }
}

debug(ctpg) unittest
{
    with(parse!(setInfo!(TestParser!(Node())), ParserKind!(true, true))(""))
    {
        assert(match == true);
        assert(value.line == __LINE__ - 2);
        assert(value.file == __FILE__);
        assert(nextInput.source == "");
    }
}


// パーサが返した文字列と、引数のtokenTypeを使ってNodeを作るコンビネータ
template makeNode(alias parser, TokenType tokenType)
{
    template build(alias kind, SrcType)
    {
        mixin MAKE_RESULT!q{ Node };

        Result parse(Input!SrcType input, in Caller caller)
        {
            return setInfo!
            (
                combinators.convert!
                (
                    parser,
                    (string token) => Node(Token(tokenType, token))
                )
            ).build!(kind, SrcType).parse(input, caller);
        }
    }
}

debug(ctpg) unittest
{
    with(parse!(makeNode!(TestParser!"hoge", TokenType.UNDEFINED), ParserKind!(true, true))(""))
    {
        assert(match == true);
        assert(value.token == Token(TokenType.UNDEFINED, "hoge"));
        assert(value.line == __LINE__ - 3);
        assert(value.file == __FILE__);
        assert(nextInput.source == "");
    }
}
