module ctpg.dsl.typed;

import std.algorithm   : count;
import std.conv : to;

import ctpg : parse;
import ctpg.parser_kind : ParserKind;

import ctpg.dsl.typed.node : Node;
import ctpg.dsl.typed.parsers : defs;

import ctpg.dsl.typed.visitors : applySkipLiteral, applyMemoizeSkip, applyMemoizeLiteral, applyMemoizeNonterminal, expandSkip, removeMemoizeDuplicates, removeSkipWithDuplicates, generate;

import selflinoin : makeCompilationErrorMessage;


string generateParsers(string src, size_t line = __LINE__ , string file = __FILE__)
{
    /+
        パスの順番どうしよう？
        生成オプションの中に「スキップをメモ化」ってのがあるから、生成オプション適応を先にやると、どれがスキップだかわからなくなって困る。
            SKIPを置き換えるんじゃなくて残して、SKIPの下にスキップパーサを入れるみたいな構造なら、どれがスキップパーサか分かる。
            それなら、別にapplyMemoizeSkipを先にやる必要はなくなる
        うーん、単純にスキップをメモ化だけを単独で最初にやっちゃうって方法がいいかな
        てか、それぞれの生成オプションごとに関数を用意してやるのがいいのかも知れない
        てか、生成オプションの渡し方とかどうするんですかね・・・
        うーん、オプションもDSLの中に書いてもらおうかなぁ・・・
        結局、生成オプションごとに関数を作ることにした。オプションはDSL内に書いてもらう
        古いctpgの実装だと、リテラルはskip!(memoize!(literal))ってなってるから、
        適応の順番はskip->memoizeになる
    +/
    /+
        applySetSkipする前と後のSKIPは別にするべきなのかどうかみたいな話
        ・別にするべき
            ・前と後で意味合いが変わる。同じだと紛らわしい
            ・childrenにスキップパーサを追加する必要がある
        ・同じにするべき
            ・前と後で、同時に出ることはないから
            ・別にすると名前空間が汚れる
        これは、別の方がいいかも知れない
        SKIPとSKIP_WITHにした。
    +/
    /+

    +/
    immutable static staticImports =
        "static import ctpg.is_wrapper;"
        "static import ctpg.parsers;"
        "static import ctpg.combinators;"
        "static import ctpg.caller;"
        "static import ctpg.input;"
        "static import ctpg.parse_result;"
        "static import ctpg.none;";

    auto parsed = src.parse!(defs, ParserKind!(true, true))(line, file);

    if(parsed.match)
    {
        Node code = parsed.value
            .applySkipLiteral()
            .applyMemoizeSkip(true)
            .applyMemoizeLiteral(false)
            .applyMemoizeNonterminal()
            .expandSkip()
            .removeMemoizeDuplicates()
            .removeSkipWithDuplicates()
        ;

        string generated = staticImports ~ code.generate();

        version(ctpgPrintGeneratedCode)
        {
            return generated ~ "pragma(msg, \"\n======== " ~ file ~ "(" ~ line.to!string ~ ") =========\n\n\"q{" ~ code.toString() ~ "}\"\n\n=====================\n\n\"q{" ~ generated ~ "});";
        }
        else
        {
            return generated;
        }
    }
    else
    {
        return "pragma(msg,\"" ~ makeCompilationErrorMessage(parsed.error.msg, file, line + src[0 .. parsed.error.position].count('\n') + 1) ~ "\");static assert(false);";
    }
}

mixin template CTPG_DSL_TYPED(string src, size_t line = __LINE__ , string file = __FILE__)
{
    static import ctpg.dsl.typed;
    mixin(ctpg.dsl.typed.generateParsers(src, line, file));
}
