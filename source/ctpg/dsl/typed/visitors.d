module ctpg.dsl.typed.visitors;

import std.conv : to;

import ctpg.dsl.typed.token : Token, TokenType;
import ctpg.dsl.typed.node : Node;

import compile_time_unittest : enableCompileTimeUnittest;
mixin enableCompileTimeUnittest;


Node applySkipLiteral(Node node, bool isSkipLiteral = true)
{
    final switch(node.token.type)
    {
        case TokenType.DOLLAR:
        case TokenType.RANGE:
        case TokenType.STRING:
            if(isSkipLiteral)
            {
                Node skipNode;
                skipNode.token.type = TokenType.SKIP;
                skipNode.children ~= node;

                node = skipNode;
            }
            break;

        case TokenType.SKIP_LITERAL_TRUE:
            node = node.children[0].applySkipLiteral(true);
            break;

        case TokenType.SKIP_LITERAL_FALSE:
            node = node.children[0].applySkipLiteral(false);
            break;


        case TokenType.DEFINITIONS:
            foreach(ref child; node.children)
            {
                switch(child.token.type)
                {
                    case TokenType.GLOBAL_SKIP_LITERAL_TRUE:
                        isSkipLiteral = true;
                        break;

                    case TokenType.GLOBAL_SKIP_LITERAL_FALSE:
                        isSkipLiteral = false;
                        break;

                    default:
                        child = child.applySkipLiteral(isSkipLiteral);
                }
            }
            break;

        case TokenType.DEFINITION:
        case TokenType.SLASH:
        case TokenType.LEFT_QUESTION:
        case TokenType.LEFT_SHIFT:
        case TokenType.SEQUENCE:
        case TokenType.QUESTION:
        case TokenType.PLUS:
        case TokenType.ASTERISK:
        case TokenType.ASCIICIRCUM:
        case TokenType.ANPERSAND:
        case TokenType.EXCLAM:

        case TokenType.SKIP:
        case TokenType.MEMOIZE:

        case TokenType.MEMOIZE_SKIP_TRUE:
        case TokenType.MEMOIZE_SKIP_FALSE:
        case TokenType.MEMOIZE_LITERAL_TRUE:
        case TokenType.MEMOIZE_LITERAL_FALSE:
        case TokenType.MEMOIZE_NONTERMINAL_TRUE:
        case TokenType.MEMOIZE_NONTERMINAL_FALSE:
            foreach(ref child; node.children)
            {
                child = child.applySkipLiteral(isSkipLiteral);
            }
            break;

        case TokenType.SKIP_WITH:
        case TokenType.SET_SKIP:
            node.children[1] = node.children[1].applySkipLiteral(isSkipLiteral);
            break;

        case TokenType.GLOBAL_SKIP_LITERAL_TRUE:
        case TokenType.GLOBAL_SKIP_LITERAL_FALSE:
            assert(false);

        case TokenType.UNDEFINED:
        case TokenType.CONVERTER:
        case TokenType.ID:
        case TokenType.TEMPLATE_INSTANCE:
        case TokenType.NONTERMINAL:
        case TokenType.RANGE_ONE_CHAR:
        case TokenType.RANGE_CHAR_RANGE:

        case TokenType.GLOBAL_SET_SKIP:

        case TokenType.GLOBAL_MEMOIZE_SKIP_TRUE:
        case TokenType.GLOBAL_MEMOIZE_SKIP_FALSE:
        case TokenType.GLOBAL_MEMOIZE_LITERAL_TRUE:
        case TokenType.GLOBAL_MEMOIZE_LITERAL_FALSE:
        case TokenType.GLOBAL_MEMOIZE_NONTERMINAL_TRUE:
        case TokenType.GLOBAL_MEMOIZE_NONTERMINAL_FALSE:
    }

    return node;
}

debug(ctpg) unittest
{
    assert
    (
        Node(Token(TokenType.DEFINITIONS),
        [
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.DOLLAR))
            ])
        ]).applySkipLiteral()

        ==

        Node(Token(TokenType.DEFINITIONS),
        [
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.SKIP),
                [
                    Node(Token(TokenType.DOLLAR))
                ])
            ])
        ])
    );

    assert
    (
        Node(Token(TokenType.DEFINITIONS),
        [
            Node(Token(TokenType.GLOBAL_SKIP_LITERAL_FALSE)),
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.DOLLAR))
            ])
        ]).applySkipLiteral()

        ==

        Node(Token(TokenType.DEFINITIONS),
        [
            Node(Token(TokenType.GLOBAL_SKIP_LITERAL_FALSE)),
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.DOLLAR))
            ])
        ])
    );

    assert
    (
        Node(Token(TokenType.DEFINITIONS),
        [
            Node(Token(TokenType.GLOBAL_SKIP_LITERAL_FALSE)),
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.SKIP_LITERAL_TRUE),
                [
                    Node(Token(TokenType.DOLLAR))
                ])
            ])
        ]).applySkipLiteral()

        ==

        Node(Token(TokenType.DEFINITIONS),
        [
            Node(Token(TokenType.GLOBAL_SKIP_LITERAL_FALSE)),
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.SKIP),
                [
                    Node(Token(TokenType.DOLLAR))
                ])
            ])
        ])
    );

    assert
    (
        Node(Token(TokenType.DEFINITIONS),
        [
            Node(Token(TokenType.GLOBAL_SKIP_LITERAL_FALSE)),
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.DOLLAR))
            ]),
            Node(Token(TokenType.GLOBAL_SKIP_LITERAL_TRUE)),
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.DOLLAR))
            ])
        ]).applySkipLiteral()

        ==

        Node(Token(TokenType.DEFINITIONS),
        [
            Node(Token(TokenType.GLOBAL_SKIP_LITERAL_FALSE)),
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.DOLLAR))
            ]),
            Node(Token(TokenType.GLOBAL_SKIP_LITERAL_TRUE)),
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.SKIP),
                [
                    Node(Token(TokenType.DOLLAR))
                ])
            ])
        ])
    );

    assert
    (
        Node(Token(TokenType.DEFINITIONS),
        [
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.SET_SKIP),
                [
                    Node(Token(TokenType.DOLLAR)),
                    Node(Token(TokenType.DOLLAR))
                ])
            ])
        ]).applySkipLiteral()

        ==

        Node(Token(TokenType.DEFINITIONS),
        [
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.SET_SKIP),
                [
                    Node(Token(TokenType.DOLLAR)),
                    Node(Token(TokenType.SKIP),
                    [
                        Node(Token(TokenType.DOLLAR))
                    ])
                ])
            ])
        ])
    );

    assert
    (
        Node(Token(TokenType.DEFINITIONS),
        [
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.SKIP_WITH),
                [
                    Node(Token(TokenType.DOLLAR)),
                    Node(Token(TokenType.DOLLAR))
                ])
            ])
        ]).applySkipLiteral()

        ==

        Node(Token(TokenType.DEFINITIONS),
        [
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.SKIP_WITH),
                [
                    Node(Token(TokenType.DOLLAR)),
                    Node(Token(TokenType.SKIP),
                    [
                        Node(Token(TokenType.DOLLAR))
                    ])
                ])
            ])
        ])
    );
}


// MEMOIZE_SKIP_TRUEな場所にある
// SET_SKIPやSKIP_WITHで指定されてるスキップパーサをMEMOIZEする
Node applyMemoizeSkip(Node node, bool isMemoizeSkip = true)
{
    final switch(node.token.type)
    {
        case TokenType.SET_SKIP:
        case TokenType.SKIP_WITH:
            node.children[1] = node.children[1].applyMemoizeSkip(isMemoizeSkip);
            goto case;

        case TokenType.GLOBAL_SET_SKIP:
            if(isMemoizeSkip)
            {
                Node memoizeNode;
                memoizeNode.token.type = TokenType.MEMOIZE;
                memoizeNode.children ~= node.children[0];
                node.children[0] = memoizeNode;
            }
            break;

        case TokenType.MEMOIZE_SKIP_TRUE:
            node = node.children[0].applyMemoizeSkip(true);
            break;

        case TokenType.MEMOIZE_SKIP_FALSE:
            node = node.children[0].applyMemoizeSkip(false);
            break;

        case TokenType.DEFINITIONS:
            foreach(ref child; node.children)
            {
                switch(child.token.type)
                {
                    case TokenType.GLOBAL_MEMOIZE_SKIP_TRUE:
                        isMemoizeSkip = true;
                        break;

                    case TokenType.GLOBAL_MEMOIZE_SKIP_FALSE:
                        isMemoizeSkip = false;
                        break;

                    default:
                        child = child.applyMemoizeSkip(isMemoizeSkip);
                }
            }
            break;

        case TokenType.DEFINITION:
        case TokenType.SLASH:
        case TokenType.LEFT_QUESTION:
        case TokenType.LEFT_SHIFT:
        case TokenType.SEQUENCE:
        case TokenType.QUESTION:
        case TokenType.PLUS:
        case TokenType.ASTERISK:
        case TokenType.ASCIICIRCUM:
        case TokenType.ANPERSAND:
        case TokenType.EXCLAM:

        case TokenType.SKIP:
        case TokenType.MEMOIZE:

        case TokenType.SKIP_LITERAL_TRUE:
        case TokenType.SKIP_LITERAL_FALSE:
        case TokenType.MEMOIZE_LITERAL_TRUE:
        case TokenType.MEMOIZE_LITERAL_FALSE:
        case TokenType.MEMOIZE_NONTERMINAL_TRUE:
        case TokenType.MEMOIZE_NONTERMINAL_FALSE:
            foreach(ref child; node.children)
            {
                child = child.applyMemoizeSkip(isMemoizeSkip);
            }
            break;

        case TokenType.GLOBAL_MEMOIZE_SKIP_TRUE:
        case TokenType.GLOBAL_MEMOIZE_SKIP_FALSE:
            assert(false);

        case TokenType.UNDEFINED:
        case TokenType.CONVERTER:
        case TokenType.ID:
        case TokenType.DOLLAR:
        case TokenType.TEMPLATE_INSTANCE:
        case TokenType.NONTERMINAL:
        case TokenType.RANGE_ONE_CHAR:
        case TokenType.RANGE_CHAR_RANGE:
        case TokenType.RANGE:
        case TokenType.STRING:

        case TokenType.GLOBAL_SKIP_LITERAL_TRUE:
        case TokenType.GLOBAL_SKIP_LITERAL_FALSE:
        case TokenType.GLOBAL_MEMOIZE_LITERAL_TRUE:
        case TokenType.GLOBAL_MEMOIZE_LITERAL_FALSE:
        case TokenType.GLOBAL_MEMOIZE_NONTERMINAL_TRUE:
        case TokenType.GLOBAL_MEMOIZE_NONTERMINAL_FALSE:
    }

    return node;
}

debug(ctpg) unittest
{
    assert
    (
        Node(Token(TokenType.DEFINITIONS), 
        [
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.SET_SKIP),
                [
                    Node(Token(TokenType.DOLLAR)),
                    Node(Token(TokenType.DOLLAR))
                ])
            ])
        ]).applyMemoizeSkip()

        == 

        Node(Token(TokenType.DEFINITIONS), 
        [
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.SET_SKIP),
                [
                    Node(Token(TokenType.MEMOIZE),
                    [
                        Node(Token(TokenType.DOLLAR))
                    ]),
                    Node(Token(TokenType.DOLLAR))
                ])
            ])
        ])
    );

    assert
    (
        Node(Token(TokenType.DEFINITIONS), 
        [
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.SET_SKIP),
                [
                    Node(Token(TokenType.DOLLAR)),
                    Node(Token(TokenType.SET_SKIP),
                    [
                        Node(Token(TokenType.DOLLAR)),
                        Node(Token(TokenType.DOLLAR))
                    ])
                ])
            ])
        ]).applyMemoizeSkip()

        == 

        Node(Token(TokenType.DEFINITIONS), 
        [
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.SET_SKIP),
                [
                    Node(Token(TokenType.MEMOIZE),
                    [
                        Node(Token(TokenType.DOLLAR))
                    ]),
                    Node(Token(TokenType.SET_SKIP),
                    [
                        Node(Token(TokenType.MEMOIZE),
                        [
                            Node(Token(TokenType.DOLLAR))
                        ]),
                        Node(Token(TokenType.DOLLAR))
                    ])
                ])
            ])
        ])
    );

    assert
    (
        Node(Token(TokenType.DEFINITIONS), 
        [
            Node(Token(TokenType.GLOBAL_MEMOIZE_SKIP_FALSE)),
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.SET_SKIP),
                [
                    Node(Token(TokenType.DOLLAR)),
                    Node(Token(TokenType.DOLLAR))
                ])
            ])
        ]).applyMemoizeSkip()

        == 

        Node(Token(TokenType.DEFINITIONS), 
        [
            Node(Token(TokenType.GLOBAL_MEMOIZE_SKIP_FALSE)),
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.SET_SKIP),
                [
                    Node(Token(TokenType.DOLLAR)),
                    Node(Token(TokenType.DOLLAR))
                ])
            ])
        ])
    );

    assert
    (
        Node(Token(TokenType.DEFINITIONS), 
        [
            Node(Token(TokenType.GLOBAL_MEMOIZE_SKIP_FALSE)),
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.MEMOIZE_SKIP_TRUE),
                [
                    Node(Token(TokenType.SET_SKIP),
                    [
                        Node(Token(TokenType.DOLLAR)),
                        Node(Token(TokenType.DOLLAR))
                    ])
                ])
            ])
        ]).applyMemoizeSkip()

        == 

        Node(Token(TokenType.DEFINITIONS), 
        [
            Node(Token(TokenType.GLOBAL_MEMOIZE_SKIP_FALSE)),
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.SET_SKIP),
                [
                    Node(Token(TokenType.MEMOIZE),
                    [
                        Node(Token(TokenType.DOLLAR))
                    ]),
                    Node(Token(TokenType.DOLLAR))
                ])
            ])
        ])
    );

    assert
    (
        Node(Token(TokenType.DEFINITIONS), 
        [
            Node(Token(TokenType.GLOBAL_MEMOIZE_SKIP_FALSE)),
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.SET_SKIP),
                [
                    Node(Token(TokenType.DOLLAR)),
                    Node(Token(TokenType.DOLLAR))
                ])
            ]),
            Node(Token(TokenType.GLOBAL_MEMOIZE_SKIP_TRUE)),
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.SET_SKIP),
                [
                    Node(Token(TokenType.DOLLAR)),
                    Node(Token(TokenType.DOLLAR))
                ])
            ]),
        ]).applyMemoizeSkip()

        == 

        Node(Token(TokenType.DEFINITIONS), 
        [
            Node(Token(TokenType.GLOBAL_MEMOIZE_SKIP_FALSE)),
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.SET_SKIP),
                [
                    Node(Token(TokenType.DOLLAR)),
                    Node(Token(TokenType.DOLLAR))
                ])
            ]),
            Node(Token(TokenType.GLOBAL_MEMOIZE_SKIP_TRUE)),
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.SET_SKIP),
                [
                    Node(Token(TokenType.MEMOIZE),
                    [
                        Node(Token(TokenType.DOLLAR))
                    ]),
                    Node(Token(TokenType.DOLLAR))
                ])
            ]),
        ])
    );
}


// MEMOIZE_LITERAL_TRUEな場所にLITERALがあったらMEMOIZEの下に入れる
Node applyMemoizeLiteral(Node node, bool isMemoizeLiteral = true)
{
    final switch(node.token.type)
    {
        case TokenType.DOLLAR:
        case TokenType.RANGE:
        case TokenType.STRING:
            if(isMemoizeLiteral)
            {
                Node memoizeNode;
                memoizeNode.token.type = TokenType.MEMOIZE;
                memoizeNode.children ~= node;

                node = memoizeNode;
            }
            break;

        case TokenType.MEMOIZE_LITERAL_TRUE:
            node = node.children[0].applyMemoizeLiteral(true);
            break;

        case TokenType.MEMOIZE_LITERAL_FALSE:
            node = node.children[0].applyMemoizeLiteral(false);
            break;

        case TokenType.DEFINITIONS:
            foreach(ref child; node.children)
            {
                switch(child.token.type)
                {
                    case TokenType.GLOBAL_MEMOIZE_LITERAL_TRUE:
                        isMemoizeLiteral = true;
                        break;

                    case TokenType.GLOBAL_MEMOIZE_LITERAL_FALSE:
                        isMemoizeLiteral = false;
                        break;

                    default:
                        child = child.applyMemoizeLiteral(isMemoizeLiteral);
                }
            }
            break;

        case TokenType.DEFINITION:
        case TokenType.SLASH:
        case TokenType.LEFT_QUESTION:
        case TokenType.LEFT_SHIFT:
        case TokenType.SEQUENCE:
        case TokenType.QUESTION:
        case TokenType.PLUS:
        case TokenType.ASTERISK:
        case TokenType.ASCIICIRCUM:
        case TokenType.ANPERSAND:
        case TokenType.EXCLAM:

        case TokenType.SKIP:
        case TokenType.SKIP_WITH:
        case TokenType.SET_SKIP:
        case TokenType.MEMOIZE:

        case TokenType.SKIP_LITERAL_TRUE:
        case TokenType.SKIP_LITERAL_FALSE:
        case TokenType.MEMOIZE_SKIP_TRUE:
        case TokenType.MEMOIZE_SKIP_FALSE:
        case TokenType.MEMOIZE_NONTERMINAL_TRUE:
        case TokenType.MEMOIZE_NONTERMINAL_FALSE:

        case TokenType.GLOBAL_SET_SKIP:
            foreach(ref child; node.children)
            {
                child = child.applyMemoizeLiteral(isMemoizeLiteral);
            }
            break;

        case TokenType.GLOBAL_MEMOIZE_LITERAL_TRUE:
        case TokenType.GLOBAL_MEMOIZE_LITERAL_FALSE:
            assert(false);

        case TokenType.UNDEFINED:
        case TokenType.CONVERTER:
        case TokenType.ID:
        case TokenType.TEMPLATE_INSTANCE:
        case TokenType.NONTERMINAL:
        case TokenType.RANGE_ONE_CHAR:
        case TokenType.RANGE_CHAR_RANGE:

        case TokenType.GLOBAL_SKIP_LITERAL_TRUE:
        case TokenType.GLOBAL_SKIP_LITERAL_FALSE:
        case TokenType.GLOBAL_MEMOIZE_SKIP_TRUE:
        case TokenType.GLOBAL_MEMOIZE_SKIP_FALSE:
        case TokenType.GLOBAL_MEMOIZE_NONTERMINAL_TRUE:
        case TokenType.GLOBAL_MEMOIZE_NONTERMINAL_FALSE:
    }

    return node;
}

debug(ctpg) unittest
{
    assert
    (
        Node(Token(TokenType.DEFINITIONS),
        [
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.DOLLAR))
            ])
        ]).applyMemoizeLiteral()

        ==

        Node(Token(TokenType.DEFINITIONS),
        [
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.MEMOIZE),
                [
                    Node(Token(TokenType.DOLLAR))
                ])
            ])
        ])
    );

    assert
    (
        Node(Token(TokenType.DEFINITIONS),
        [
            Node(Token(TokenType.GLOBAL_MEMOIZE_LITERAL_FALSE)),
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.DOLLAR))
            ])
        ]).applyMemoizeLiteral()

        ==

        Node(Token(TokenType.DEFINITIONS),
        [
            Node(Token(TokenType.GLOBAL_MEMOIZE_LITERAL_FALSE)),
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.DOLLAR))
            ])
        ])
    );

    assert
    (
        Node(Token(TokenType.DEFINITIONS),
        [
            Node(Token(TokenType.GLOBAL_MEMOIZE_LITERAL_FALSE)),
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.MEMOIZE_LITERAL_TRUE),
                [
                    Node(Token(TokenType.DOLLAR))
                ])
            ])
        ]).applyMemoizeLiteral()

        ==

        Node(Token(TokenType.DEFINITIONS),
        [
            Node(Token(TokenType.GLOBAL_MEMOIZE_LITERAL_FALSE)),
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.MEMOIZE),
                [
                    Node(Token(TokenType.DOLLAR))
                ])
            ])
        ])
    );

    assert
    (
        Node(Token(TokenType.DEFINITIONS),
        [
            Node(Token(TokenType.GLOBAL_MEMOIZE_LITERAL_FALSE)),
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.DOLLAR))
            ]),
            Node(Token(TokenType.GLOBAL_MEMOIZE_LITERAL_TRUE)),
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.DOLLAR))
            ])
        ]).applyMemoizeLiteral()

        ==

        Node(Token(TokenType.DEFINITIONS),
        [
            Node(Token(TokenType.GLOBAL_MEMOIZE_LITERAL_FALSE)),
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.DOLLAR))
            ]),
            Node(Token(TokenType.GLOBAL_MEMOIZE_LITERAL_TRUE)),
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.MEMOIZE),
                [
                    Node(Token(TokenType.DOLLAR))
                ])
            ])
        ])
    );

    assert
    (
        Node(Token(TokenType.DEFINITIONS),
        [
            Node(Token(TokenType.GLOBAL_SET_SKIP),
            [
                Node(Token(TokenType.DOLLAR))
            ]),
            Node(Token(TokenType.GLOBAL_MEMOIZE_LITERAL_FALSE)),
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.DOLLAR))
            ])
        ]).applyMemoizeLiteral()

        ==

        Node(Token(TokenType.DEFINITIONS),
        [
            Node(Token(TokenType.GLOBAL_SET_SKIP),
            [
                Node(Token(TokenType.MEMOIZE),
                [
                    Node(Token(TokenType.DOLLAR))
                ])
            ]),
            Node(Token(TokenType.GLOBAL_MEMOIZE_LITERAL_FALSE)),
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.DOLLAR))
            ])
        ])
    );
}


// MEMOIZE_NONTERMINAL_TRUEな場所にNONTERMINALがあったらMEMOIZEの下に入れる
Node applyMemoizeNonterminal(Node node, bool isMemoizeNonterminal = true)
{
    final switch(node.token.type)
    {
        case TokenType.NONTERMINAL:
            if(isMemoizeNonterminal)
            {
                Node memoizeNode;

                memoizeNode.token.type = TokenType.MEMOIZE;
                memoizeNode.children ~= node;

                node = memoizeNode;
            }
            break;

        case TokenType.MEMOIZE_NONTERMINAL_TRUE:
            node = node.children[0].applyMemoizeNonterminal(true);
            break;

        case TokenType.MEMOIZE_NONTERMINAL_FALSE:
            node = node.children[0].applyMemoizeNonterminal(false);
            break;

        case TokenType.DEFINITIONS:
            foreach(ref child; node.children)
            {
                switch(child.token.type)
                {
                    case TokenType.GLOBAL_MEMOIZE_NONTERMINAL_TRUE:
                        isMemoizeNonterminal = true;
                        break;

                    case TokenType.GLOBAL_MEMOIZE_NONTERMINAL_FALSE:
                        isMemoizeNonterminal = false;
                        break;

                    default:
                        child = child.applyMemoizeNonterminal(isMemoizeNonterminal);
                }
            }
            break;

        case TokenType.DEFINITION:
        case TokenType.SLASH:
        case TokenType.LEFT_QUESTION:
        case TokenType.LEFT_SHIFT:
        case TokenType.SEQUENCE:
        case TokenType.QUESTION:
        case TokenType.PLUS:
        case TokenType.ASTERISK:
        case TokenType.ASCIICIRCUM:
        case TokenType.ANPERSAND:
        case TokenType.EXCLAM:

        case TokenType.SKIP:
        case TokenType.SKIP_WITH:
        case TokenType.SET_SKIP:
        case TokenType.MEMOIZE:

        case TokenType.SKIP_LITERAL_TRUE:
        case TokenType.SKIP_LITERAL_FALSE:
        case TokenType.MEMOIZE_SKIP_TRUE:
        case TokenType.MEMOIZE_SKIP_FALSE:
        case TokenType.MEMOIZE_LITERAL_TRUE:
        case TokenType.MEMOIZE_LITERAL_FALSE:

        case TokenType.GLOBAL_SET_SKIP:
            foreach(ref child; node.children)
            {
                child = child.applyMemoizeNonterminal(isMemoizeNonterminal);
            }
            break;

        case TokenType.GLOBAL_MEMOIZE_NONTERMINAL_TRUE:
        case TokenType.GLOBAL_MEMOIZE_NONTERMINAL_FALSE:
            assert(false);

        case TokenType.UNDEFINED:
        case TokenType.CONVERTER:
        case TokenType.ID:
        case TokenType.DOLLAR:
        case TokenType.TEMPLATE_INSTANCE:
        case TokenType.RANGE_ONE_CHAR:
        case TokenType.RANGE_CHAR_RANGE:
        case TokenType.RANGE:
        case TokenType.STRING:

        case TokenType.GLOBAL_SKIP_LITERAL_TRUE:
        case TokenType.GLOBAL_SKIP_LITERAL_FALSE:
        case TokenType.GLOBAL_MEMOIZE_SKIP_TRUE:
        case TokenType.GLOBAL_MEMOIZE_SKIP_FALSE:
        case TokenType.GLOBAL_MEMOIZE_LITERAL_TRUE:
        case TokenType.GLOBAL_MEMOIZE_LITERAL_FALSE:
    }

    return node;
}

debug(ctpg) unittest
{
    assert
    (
        Node(Token(TokenType.DEFINITIONS),
        [
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.NONTERMINAL))
            ])
        ]).applyMemoizeNonterminal()

        ==

        Node(Token(TokenType.DEFINITIONS),
        [
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.MEMOIZE),
                [
                    Node(Token(TokenType.NONTERMINAL))
                ])
            ])
        ])
    );

    assert
    (
        Node(Token(TokenType.DEFINITIONS),
        [
            Node(Token(TokenType.GLOBAL_MEMOIZE_NONTERMINAL_FALSE)),
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.NONTERMINAL))
            ])
        ]).applyMemoizeNonterminal()

        ==

        Node(Token(TokenType.DEFINITIONS),
        [
            Node(Token(TokenType.GLOBAL_MEMOIZE_NONTERMINAL_FALSE)),
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.NONTERMINAL))
            ])
        ])
    );

    assert
    (
        Node(Token(TokenType.DEFINITIONS),
        [
            Node(Token(TokenType.GLOBAL_MEMOIZE_NONTERMINAL_FALSE)),
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.MEMOIZE_NONTERMINAL_TRUE),
                [
                    Node(Token(TokenType.NONTERMINAL))
                ])
            ])
        ]).applyMemoizeNonterminal()

        ==

        Node(Token(TokenType.DEFINITIONS),
        [
            Node(Token(TokenType.GLOBAL_MEMOIZE_NONTERMINAL_FALSE)),
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.MEMOIZE),
                [
                    Node(Token(TokenType.NONTERMINAL))
                ])
            ])
        ])
    );

    assert
    (
        Node(Token(TokenType.DEFINITIONS),
        [
            Node(Token(TokenType.GLOBAL_MEMOIZE_NONTERMINAL_FALSE)),
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.NONTERMINAL))
            ]),
            Node(Token(TokenType.GLOBAL_MEMOIZE_NONTERMINAL_TRUE)),
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.NONTERMINAL))
            ])
        ]).applyMemoizeNonterminal()

        ==

        Node(Token(TokenType.DEFINITIONS),
        [
            Node(Token(TokenType.GLOBAL_MEMOIZE_NONTERMINAL_FALSE)),
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.NONTERMINAL))
            ]),
            Node(Token(TokenType.GLOBAL_MEMOIZE_NONTERMINAL_TRUE)),
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.MEMOIZE),
                [
                    Node(Token(TokenType.NONTERMINAL))
                ])
            ])
        ])
    );

    assert
    (
        Node(Token(TokenType.DEFINITIONS),
        [
            Node(Token(TokenType.GLOBAL_SET_SKIP),
            [
                Node(Token(TokenType.NONTERMINAL))
            ]),
            Node(Token(TokenType.GLOBAL_MEMOIZE_NONTERMINAL_FALSE)),
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.NONTERMINAL))
            ])
        ]).applyMemoizeNonterminal()

        ==

        Node(Token(TokenType.DEFINITIONS),
        [
            Node(Token(TokenType.GLOBAL_SET_SKIP),
            [
                Node(Token(TokenType.MEMOIZE),
                [
                    Node(Token(TokenType.NONTERMINAL))
                ])
            ]),
            Node(Token(TokenType.GLOBAL_MEMOIZE_NONTERMINAL_FALSE)),
            Node(Token(TokenType.DEFINITION),
            [
                Node(Token(TokenType.TEMPLATE_INSTANCE)),
                Node(Token(TokenType.ID)),
                Node(Token(TokenType.NONTERMINAL))
            ])
        ])
    );
}


// SET_SKIPで指定されたスキップパーサでSKIPをSKIP_WITHに置換する
Node expandSkip(Node node, Node skip = Node.init)
{
    final switch(node.token.type)
    {
        case TokenType.SKIP:
            if(skip.token.type != TokenType.UNDEFINED)
            {
                Node skipWithNode;

                skipWithNode.token.type = TokenType.SKIP_WITH;
                skipWithNode.children ~= skip;
                skipWithNode.children ~= node.children[0];

                node = skipWithNode;
            }
            else
            {
                node = node.children[0];
            }
            break;

        case TokenType.SET_SKIP:
            node = node.children[1].expandSkip(node.children[0]);
            break;

        case TokenType.SKIP_WITH:
            node.children[1] = node.children[1].expandSkip(skip);
            break;

        case TokenType.DEFINITIONS:
            foreach(ref child; node.children)
            {
                switch(child.token.type)
                {
                    case TokenType.GLOBAL_SET_SKIP:
                        skip = child.children[0];
                        break;

                    default:
                        child = child.expandSkip(skip);
                }
            }
            break;

        case TokenType.DEFINITION:
        case TokenType.SLASH:
        case TokenType.LEFT_QUESTION:
        case TokenType.LEFT_SHIFT:
        case TokenType.SEQUENCE:
        case TokenType.QUESTION:
        case TokenType.PLUS:
        case TokenType.ASTERISK:
        case TokenType.ASCIICIRCUM:
        case TokenType.ANPERSAND:
        case TokenType.EXCLAM:

        case TokenType.MEMOIZE:

        case TokenType.SKIP_LITERAL_TRUE:
        case TokenType.SKIP_LITERAL_FALSE:
        case TokenType.MEMOIZE_SKIP_TRUE:
        case TokenType.MEMOIZE_SKIP_FALSE:
        case TokenType.MEMOIZE_LITERAL_TRUE:
        case TokenType.MEMOIZE_LITERAL_FALSE:
        case TokenType.MEMOIZE_NONTERMINAL_TRUE:
        case TokenType.MEMOIZE_NONTERMINAL_FALSE:
            foreach(ref child; node.children)
            {
                child = child.expandSkip(skip);
            }
            break;

        case TokenType.UNDEFINED:
        case TokenType.GLOBAL_SET_SKIP:
            assert(false);

        case TokenType.CONVERTER:
        case TokenType.ID:
        case TokenType.DOLLAR:
        case TokenType.TEMPLATE_INSTANCE:
        case TokenType.NONTERMINAL:
        case TokenType.RANGE_ONE_CHAR:
        case TokenType.RANGE_CHAR_RANGE:
        case TokenType.RANGE:
        case TokenType.STRING:

        case TokenType.GLOBAL_SKIP_LITERAL_TRUE:
        case TokenType.GLOBAL_SKIP_LITERAL_FALSE:
        case TokenType.GLOBAL_MEMOIZE_SKIP_TRUE:
        case TokenType.GLOBAL_MEMOIZE_SKIP_FALSE:
        case TokenType.GLOBAL_MEMOIZE_LITERAL_TRUE:
        case TokenType.GLOBAL_MEMOIZE_LITERAL_FALSE:
        case TokenType.GLOBAL_MEMOIZE_NONTERMINAL_TRUE:
        case TokenType.GLOBAL_MEMOIZE_NONTERMINAL_FALSE:
    }

    return node;
}

debug(ctpg) unittest
{
    with(TokenType)
    {
        // GLOBAL_SET_SKIPが動く
        assert (
            Node(Token(DEFINITIONS),
            [
                Node(Token(GLOBAL_SET_SKIP),
                [
                    Node(Token(STRING))
                ]),
                Node(Token(DEFINITION),
                [
                    Node(Token(TEMPLATE_INSTANCE)),
                    Node(Token(ID)),
                    Node(Token(SKIP),
                    [
                        Node(Token(DOLLAR))
                    ])
                ])
            ]).expandSkip()

            == 

            Node(Token(DEFINITIONS),
            [
                Node(Token(GLOBAL_SET_SKIP),
                [
                    Node(Token(STRING))
                ]),
                Node(Token(DEFINITION),
                [
                    Node(Token(TEMPLATE_INSTANCE)),
                    Node(Token(ID)),
                    Node(Token(SKIP_WITH),
                    [
                        Node(Token(STRING)),
                        Node(Token(DOLLAR))
                    ])
                ])
            ])
        );

        // 最も近いGLOBAL_SET_SKIPが優先される
        assert (
            Node(Token(DEFINITIONS),
            [
                Node(Token(GLOBAL_SET_SKIP),
                [
                    Node(Token(STRING, "1"))
                ]),
                Node(Token(DEFINITION),
                [
                    Node(Token(TEMPLATE_INSTANCE)),
                    Node(Token(ID)),
                    Node(Token(SKIP),
                    [
                        Node(Token(DOLLAR))
                    ])
                ]),
                Node(Token(GLOBAL_SET_SKIP),
                [
                    Node(Token(STRING, "2"))
                ]),
                Node(Token(DEFINITION),
                [
                    Node(Token(TEMPLATE_INSTANCE)),
                    Node(Token(ID)),
                    Node(Token(SKIP),
                    [
                        Node(Token(DOLLAR))
                    ])
                ])
            ]).expandSkip()

            == 

            Node(Token(DEFINITIONS),
            [
                Node(Token(GLOBAL_SET_SKIP),
                [
                    Node(Token(STRING, "1"))
                ]),
                Node(Token(DEFINITION),
                [
                    Node(Token(TEMPLATE_INSTANCE)),
                    Node(Token(ID)),
                    Node(Token(SKIP_WITH),
                    [
                        Node(Token(STRING, "1")),
                        Node(Token(DOLLAR))
                    ])
                ]),
                Node(Token(GLOBAL_SET_SKIP),
                [
                    Node(Token(STRING, "2"))
                ]),
                Node(Token(DEFINITION),
                [
                    Node(Token(TEMPLATE_INSTANCE)),
                    Node(Token(ID)),
                    Node(Token(SKIP_WITH),
                    [
                        Node(Token(STRING, "2")),
                        Node(Token(DOLLAR))
                    ])
                ])
            ])
        );

        // SET_SKIPが動く
        assert (
            Node(Token(DEFINITIONS),
            [
                Node(Token(DEFINITION),
                [
                    Node(Token(TEMPLATE_INSTANCE)),
                    Node(Token(ID)),
                    Node(Token(SET_SKIP),
                    [
                        Node(Token(STRING)),
                        Node(Token(SKIP),
                        [
                            Node(Token(DOLLAR))
                        ])
                    ])
                ])
            ]).expandSkip()

            == 

            Node(Token(DEFINITIONS),
            [
                Node(Token(DEFINITION),
                [
                    Node(Token(TEMPLATE_INSTANCE)),
                    Node(Token(ID)),
                    Node(Token(SKIP_WITH),
                    [
                        Node(Token(STRING)),
                        Node(Token(DOLLAR))
                    ])
                ])
            ])
        );

        // 最も近いSET_SKIPが優先される
        assert (
            Node(Token(DEFINITIONS),
            [
                Node(Token(DEFINITION),
                [
                    Node(Token(TEMPLATE_INSTANCE)),
                    Node(Token(ID)),
                    Node(Token(SET_SKIP),
                    [
                        Node(Token(STRING, "1")),
                        Node(Token(SEQUENCE),
                        [
                            Node(Token(SKIP),
                            [
                                Node(Token(DOLLAR))
                            ]),
                            Node(Token(SET_SKIP),
                            [
                                Node(Token(STRING, "2")),
                                Node(Token(SKIP),
                                [
                                    Node(Token(DOLLAR))
                                ])
                            ])
                        ]),
                    ])
                ])
            ]).expandSkip()

            == 

            Node(Token(DEFINITIONS),
            [
                Node(Token(DEFINITION),
                [
                    Node(Token(TEMPLATE_INSTANCE)),
                    Node(Token(ID)),
                    Node(Token(SEQUENCE),
                    [
                        Node(Token(SKIP_WITH),
                        [
                            Node(Token(STRING, "1")),
                            Node(Token(DOLLAR))
                        ]),
                        Node(Token(SKIP_WITH),
                        [
                            Node(Token(STRING, "2")),
                            Node(Token(DOLLAR))
                        ])
                    ])
                ])
            ])
        );

        // GLOBAL_SET_SKIPよりもSET_SKIPが優先される
        assert (
            Node(Token(DEFINITIONS),
            [
                Node(Token(GLOBAL_SET_SKIP),
                [
                    Node(Token(STRING, "global"))
                ]),
                Node(Token(DEFINITION),
                [
                    Node(Token(TEMPLATE_INSTANCE)),
                    Node(Token(ID)),
                    Node(Token(SET_SKIP),
                    [
                        Node(Token(STRING, "local")),
                        Node(Token(SKIP),
                        [
                            Node(Token(DOLLAR))
                        ])
                    ])
                ])
            ]).expandSkip()

            == 

            Node(Token(DEFINITIONS),
            [
                Node(Token(GLOBAL_SET_SKIP),
                [
                    Node(Token(STRING, "global"))
                ]),
                Node(Token(DEFINITION),
                [
                    Node(Token(TEMPLATE_INSTANCE)),
                    Node(Token(ID)),
                    Node(Token(SKIP_WITH),
                    [
                        Node(Token(STRING, "local")),
                        Node(Token(DOLLAR))
                    ])
                ])
            ])
        );
    }
}


// MEMOIZEの重複を消す
Node removeMemoizeDuplicates(Node node)
{
    final switch(node.token.type) with(TokenType)
    {
        case MEMOIZE:
            if(node.children[0].token.type == MEMOIZE)
            {
                node = node.children[0].removeMemoizeDuplicates();
            }
            break;

        case DEFINITIONS:
        case DEFINITION:
        case SLASH:
        case LEFT_QUESTION:
        case LEFT_SHIFT:
        case SEQUENCE:
        case QUESTION:
        case PLUS:
        case ASTERISK:
        case ASCIICIRCUM:
        case ANPERSAND:
        case EXCLAM:

        case SKIP:
        case SET_SKIP:
        case SKIP_WITH:

        case SKIP_LITERAL_TRUE:
        case SKIP_LITERAL_FALSE:
        case MEMOIZE_SKIP_TRUE:
        case MEMOIZE_SKIP_FALSE:
        case MEMOIZE_LITERAL_TRUE:
        case MEMOIZE_LITERAL_FALSE:
        case MEMOIZE_NONTERMINAL_TRUE:
        case MEMOIZE_NONTERMINAL_FALSE:

        case TokenType.GLOBAL_SET_SKIP:
            foreach(ref child; node.children)
            {
                child = child.removeMemoizeDuplicates();
            }
            break;

        case UNDEFINED:
        case CONVERTER:
        case ID:
        case DOLLAR:
        case TEMPLATE_INSTANCE:
        case NONTERMINAL:
        case RANGE_ONE_CHAR:
        case RANGE_CHAR_RANGE:
        case RANGE:
        case STRING:

        case GLOBAL_SKIP_LITERAL_TRUE:
        case GLOBAL_SKIP_LITERAL_FALSE:
        case GLOBAL_MEMOIZE_SKIP_TRUE:
        case GLOBAL_MEMOIZE_SKIP_FALSE:
        case GLOBAL_MEMOIZE_LITERAL_TRUE:
        case GLOBAL_MEMOIZE_LITERAL_FALSE:
        case GLOBAL_MEMOIZE_NONTERMINAL_TRUE:
        case GLOBAL_MEMOIZE_NONTERMINAL_FALSE:
    }
    return node;
}

debug(ctpg) unittest
{
    with(TokenType)
    {
        // MEMOIZEの重複が消される
        assert (
            Node(Token(MEMOIZE),
            [
                Node(Token(MEMOIZE),
                [
                    Node(Token(STRING))
                ])
            ]).removeMemoizeDuplicates()

            == 

            Node(Token(MEMOIZE),
            [
                Node(Token(STRING))
            ])
        );

        // スキップパーサ内のMEMOIZEが消される
        assert (
            Node(Token(SKIP_WITH),
            [
                Node(Token(MEMOIZE),
                [
                    Node(Token(MEMOIZE),
                    [
                        Node(Token(STRING))
                    ])
                ]),
                Node(Token(STRING))
            ]).removeMemoizeDuplicates()

            == 

            Node(Token(SKIP_WITH),
            [
                Node(Token(MEMOIZE),
                [
                    Node(Token(STRING))
                ]),
                Node(Token(STRING))
            ])
        );
    }
}


// SKIP_WITHの重複を消す
Node removeSkipWithDuplicates(Node node)
{
    final switch(node.token.type) with(TokenType)
    {
        case SKIP_WITH:
            if(node.children[1].token.type == SKIP_WITH && node.children[0] == node.children[1].children[0])
            {
                node = node.children[1].removeSkipWithDuplicates();
            }
            break;

        case DEFINITIONS:
        case DEFINITION:
        case SLASH:
        case LEFT_QUESTION:
        case LEFT_SHIFT:
        case SEQUENCE:
        case QUESTION:
        case PLUS:
        case ASTERISK:
        case ASCIICIRCUM:
        case ANPERSAND:
        case EXCLAM:

        case SKIP:
        case SET_SKIP:
        case MEMOIZE:

        case SKIP_LITERAL_TRUE:
        case SKIP_LITERAL_FALSE:
        case MEMOIZE_SKIP_TRUE:
        case MEMOIZE_SKIP_FALSE:
        case MEMOIZE_LITERAL_TRUE:
        case MEMOIZE_LITERAL_FALSE:
        case MEMOIZE_NONTERMINAL_TRUE:
        case MEMOIZE_NONTERMINAL_FALSE:

        case TokenType.GLOBAL_SET_SKIP:
            foreach(ref child; node.children)
            {
                child = child.removeSkipWithDuplicates();
            }
            break;

        case UNDEFINED:
        case CONVERTER:
        case ID:
        case DOLLAR:
        case TEMPLATE_INSTANCE:
        case NONTERMINAL:
        case RANGE_ONE_CHAR:
        case RANGE_CHAR_RANGE:
        case RANGE:
        case STRING:

        case GLOBAL_SKIP_LITERAL_TRUE:
        case GLOBAL_SKIP_LITERAL_FALSE:
        case GLOBAL_MEMOIZE_SKIP_TRUE:
        case GLOBAL_MEMOIZE_SKIP_FALSE:
        case GLOBAL_MEMOIZE_LITERAL_TRUE:
        case GLOBAL_MEMOIZE_LITERAL_FALSE:
        case GLOBAL_MEMOIZE_NONTERMINAL_TRUE:
        case GLOBAL_MEMOIZE_NONTERMINAL_FALSE:
    }
    return node;
}

debug(ctpg) unittest
{
    with(TokenType)
    {
        // スキップパーサが等しいSKIP_WITHの重複が消される
        assert (
                Node(Token(SKIP_WITH),
                     [
                     Node(Token(STRING, "a")),
                     Node(Token(SKIP_WITH),
                          [
                          Node(Token(STRING, "a")),
                          Node(Token(DOLLAR))
                          ])
                     ]).removeSkipWithDuplicates()

                == 

                Node(Token(SKIP_WITH),
                     [
                     Node(Token(STRING, "a")),
                     Node(Token(DOLLAR))
                     ])
        );

        // スキップパーサが等しくないSKIP_WITHの重複は消されない
        assert (
                Node(Token(SKIP_WITH),
                     [
                     Node(Token(STRING, "a")),
                     Node(Token(SKIP_WITH),
                          [
                          Node(Token(STRING, "b")),
                          Node(Token(DOLLAR))
                          ])
                     ]).removeSkipWithDuplicates()

                == 

                Node(Token(SKIP_WITH),
                     [
                     Node(Token(STRING, "a")),
                     Node(Token(SKIP_WITH),
                          [
                          Node(Token(STRING, "b")),
                          Node(Token(DOLLAR))
                          ])
                     ])
                );
    }
}


// NodeからmixinされるD言語のコードを生成する
string generate(Node node)
{
    string code;

    final switch(node.token.type)
    {
        case TokenType.DEFINITIONS:
            foreach(child; node.children)
            {
                if(child.token.type == TokenType.DEFINITION)
                {
                    code ~= child.generate();
                }
            }
            break;

        case TokenType.DEFINITION:
            code =
            "template " ~ node.children[1].token.text ~ "()"
            "{"
                "template build(alias kind, SrcType)"
                "{"
                    "static if(kind.hasValue)"
                    "{"
                        "#line " ~ node.children[0].line.to!string() ~ " \"" ~ node.children[0].file ~ "\"\n"
                        "alias Result = ctpg.parse_result.ParseResult!(kind, SrcType, " ~ node.children[0].token.text ~ ");"
                    "}"
                    "else"
                    "{"
                        "alias Result = ctpg.parse_result.ParseResult!(kind, SrcType);"
                    "}"
                    "static Result parse(ctpg.input.Input!SrcType input, in ctpg.caller.Caller caller)"
                    "{"
                        "static if(!ctpg.is_wrapper.isImplicitlyConvertible!(typeof(" ~ node.children[2].generate() ~ ".build!(kind, SrcType).parse(input, caller)), Result))"
                        "{"
                            "pragma(msg, `" ~ node.children[1].file ~ "(" ~ node.children[1].line.to!string() ~ "): '" ~ node.children[1].token.text ~ "' should return '" ~ node.children[0].token.text ~ "', not '` ~ ctpg.parse_result.getParseResultType!(" ~ node.children[2].generate() ~ ".build!(kind, SrcType)).stringof ~ `'`);"
                            "static assert(false);"
                        "}"
                        "return " ~ node.children[2].generate() ~ ".build!(kind, SrcType).parse(input, caller);"
                    "}"
                "}"
            "}";
            break;

        case TokenType.SLASH:
            foreach(child; node.children)
            {
                code ~= child.generate() ~ ",";
            }
            code = "ctpg.combinators.choice!(" ~ code ~ ")";
            break;

        case TokenType.LEFT_SHIFT:
            code = "ctpg.combinators.convert!(" ~ node.children[0].generate() ~ ",#line " ~ node.children[1].line.to!string() ~ "\n" ~ node.children[1].token.text ~ "," ~ node.line.to!string() ~ ",`" ~ node.file ~ "`)";
            break;

        case TokenType.LEFT_QUESTION:
            code = "ctpg.combinators.check!(" ~ node.children[0].generate() ~ ",#line " ~ node.children[1].line.to!string() ~ "\n" ~ node.children[1].token.text ~ "," ~ node.line.to!string() ~ ",`" ~ node.file ~ "`)";
            break;

        case TokenType.SEQUENCE:
            foreach(child; node.children)
            {
                code ~= child.generate() ~ ",";
            }
            code = "ctpg.combinators.untuple!(ctpg.combinators.sequence!(" ~ code ~ "))";
            break;

        case TokenType.QUESTION:
            code = "ctpg.combinators.option!(" ~ node.children[0].generate() ~ ")";
            break;

        case TokenType.ASTERISK:
            if(node.children.length == 2)
            {
                code = "ctpg.combinators.more0!(" ~ node.children[0].generate() ~ "," ~ node.children[1].generate() ~ ")";
            }
            else
            {
                code = "ctpg.combinators.more0!(" ~ node.children[0].generate() ~ ")";
            }
            break;

        case TokenType.PLUS:
            if(node.children.length == 2)
            {
                code = "ctpg.combinators.more1!(" ~ node.children[0].generate() ~ "," ~ node.children[1].generate() ~ ")";
            }
            else
            {
                code = "ctpg.combinators.more1!(" ~ node.children[0].generate() ~ ")";
            }
            break;

        case TokenType.EXCLAM:
            code = "ctpg.combinators.none!(" ~ node.children[0].generate() ~ ")";
            break;

        case TokenType.ANPERSAND:
            code = "ctpg.combinators.andPred!(" ~ node.children[0].generate() ~ ")";
            break;

        case TokenType.ASCIICIRCUM:
            code = "ctpg.combinators.notPred!(" ~ node.children[0].generate() ~ ")";
            break;

        case TokenType.SKIP_WITH:
            code = "ctpg.combinators.skip!(" ~ node.children[0].generate() ~ "," ~ node.children[1].generate() ~ ")";
            break;

        case TokenType.MEMOIZE:
            code = "ctpg.combinators.memoize!(" ~ node.children[0].generate() ~ ")";
            break;

        case TokenType.DOLLAR:
            code = "ctpg.parsers.eof!()";
            break;

        case TokenType.RANGE:
            if(node.children.length > 1)
            {
                code ~= "ctpg.combinators.choice!(";
            }

            foreach(i, child; node.children)
            {
                if(i)
                {
                    code ~= ",";
                }

                switch(child.token.type)
                {
                    case TokenType.RANGE_CHAR_RANGE:
                        code ~= "ctpg.parsers.charRange!('" ~ child.children[0].token.text ~ "','" ~ child.children[1].token.text ~ "')";
                        break;

                    case TokenType.RANGE_ONE_CHAR:
                        code ~= "ctpg.parsers.charRange!('" ~ child.token.text ~ "','" ~ child.token.text ~ "')";
                        break;

                    default: assert(false);
                }
            }

            if(node.children.length > 1)
            {
                code ~= ")";
            }
            break;

        case TokenType.STRING:
            code = "ctpg.parsers.string_!(" ~ node.token.text ~ ")";
            break;

        case TokenType.NONTERMINAL:
            code = "#line " ~ node.line.to!string() ~ " \"" ~ node.file ~ "\"\n" ~ node.token.text ~ "!()";
            break;

        case TokenType.UNDEFINED:
        case TokenType.CONVERTER:
        case TokenType.ID:
        case TokenType.TEMPLATE_INSTANCE:
        case TokenType.RANGE_ONE_CHAR:
        case TokenType.RANGE_CHAR_RANGE:

        case TokenType.SKIP:
        case TokenType.SET_SKIP:

        case TokenType.MEMOIZE_SKIP_TRUE:
        case TokenType.MEMOIZE_SKIP_FALSE:
        case TokenType.SKIP_LITERAL_TRUE:
        case TokenType.SKIP_LITERAL_FALSE:
        case TokenType.MEMOIZE_LITERAL_TRUE:
        case TokenType.MEMOIZE_LITERAL_FALSE:
        case TokenType.MEMOIZE_NONTERMINAL_TRUE:
        case TokenType.MEMOIZE_NONTERMINAL_FALSE:

        case TokenType.GLOBAL_SET_SKIP:

        case TokenType.GLOBAL_SKIP_LITERAL_TRUE:
        case TokenType.GLOBAL_SKIP_LITERAL_FALSE:
        case TokenType.GLOBAL_MEMOIZE_SKIP_TRUE:
        case TokenType.GLOBAL_MEMOIZE_SKIP_FALSE:
        case TokenType.GLOBAL_MEMOIZE_LITERAL_TRUE:
        case TokenType.GLOBAL_MEMOIZE_LITERAL_FALSE:
        case TokenType.GLOBAL_MEMOIZE_NONTERMINAL_TRUE:
        case TokenType.GLOBAL_MEMOIZE_NONTERMINAL_FALSE:
            assert(false);
    }

    return code;
}

debug(ctpg) unittest
{
    with(TokenType)
    {
        assert (
            Node(Token(RANGE), [
                Node(Token(RANGE_ONE_CHAR, "a"))
            ]).generate()

             == 

            "ctpg.parsers.charRange!('a','a')"
        );

        assert (
            Node(Token(RANGE), [
                Node(Token(RANGE_CHAR_RANGE), [
                    Node(Token(RANGE_ONE_CHAR, "a")),
                    Node(Token(RANGE_ONE_CHAR, "z"))
                ])
            ]).generate()

             == 

            "ctpg.parsers.charRange!('a','z')"
        );

        assert (
            Node(Token(RANGE), [
                Node(Token(RANGE_CHAR_RANGE), [
                    Node(Token(RANGE_ONE_CHAR, "a")),
                    Node(Token(RANGE_ONE_CHAR, "z"))
                ]),
                Node(Token(RANGE_ONE_CHAR, "_"))
            ]).generate()

             == 

             "ctpg.combinators.choice!"
             "("
                "ctpg.parsers.charRange!('a','z'),"
                "ctpg.parsers.charRange!('_','_')"
             ")"
        );
    }
}
