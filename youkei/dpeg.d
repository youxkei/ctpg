module youkei.dpeg;

import std.traits;
import std.typecons;
import std.functional;

alias std.functional.memoize memoize;

alias Tuple!() None;

struct Result(T){
	bool match;
	T value;
	string rest;
	void opAssign(F)(Result!F rhs) if(isAssignable!(T, F)){
		match = rhs.match;
		value = rhs.value;
		rest = rhs.rest;
	}
}

struct Option(T){
	T value;
	bool some;
	bool opCast(E)() if(is(E == bool)){
		return some;
	}
}

/*combinators*/version(all){
	UnTuple!(CombinateSequenceImplType!parsers) combinateSequence(parsers...)(string input){
		static assert(staticLength!parsers > 0);
		return unTuple(combinateSequenceImpl!parsers(input));
	}

	private CombinateSequenceImplType!parsers combinateSequenceImpl(parsers...)(string input){
		typeof(return) res;
		static if(staticLength!parsers == 1){
			auto r = parsers[0](input);
			if(r.match){
				res.match = true;
				static if(isTuple!(ParserType!(parsers[0]))){
					res.value = r.value;
				}else{
					res.value = tuple(r.value);
				}
				res.rest = r.rest;
			}
			return res;
		}else{
			auto r1 = parsers[0](input);
			if(r1.match){
				auto r2 = combinateSequenceImpl!(parsers[1..$])(r1.rest);
				if(r2.match){
					res.match = true;
					static if(isTuple!(ParserType!(parsers[0]))){
						res.value = tuple(r1.value.field, r2.value.field);
					}else{
						res.value = tuple(r1.value, r2.value.field);
					}
					res.rest = r2.rest;
				}
			}
			return res;
		}
	}

	unittest{
		enum dg ={
			auto r = combinateSequence!(
				parseString!("hello"),
				parseString!("world")
			)("helloworld");
			assert(r.match);
			assert(r.rest == "");
			assert(r.value[0] == "hello");
			assert(r.value[1] == "world");
			auto r2 = combinateSequence!(
				combinateSequence!(
					parseString!("hello"),
					parseString!("world")
				),
				parseString!"!"
			)("helloworld!");
			assert(r2.match);
			assert(r2.rest == "");
			assert(r2.value[0] == "hello");
			assert(r2.value[1] == "world");
			assert(r2.value[2] == "!");
			return true;
		};
		debug(ct) static assert(dg());
		dg();
	}

	Result!(CommonParserType!parsers) combinateChoice(parsers...)(string input){
		static assert(staticLength!parsers > 0);
		static if(staticLength!parsers == 1){
			return parsers[0](input);
		}else{
			typeof(return) res;
			auto r1 = parsers[0](input);
			if(r1.match){
				res = r1;
				return res;
			}
			auto r2 = combinateChoice!(parsers[1..$])(input);
			if(r2.match){
				res = r2;
				return res;
			}
			return res;
		}
	}

	unittest{
		enum dg ={
			alias combinateChoice!(parseString!"h",parseString!"w") p;
			auto r1 = p("hw");
			assert(r1.match);
			assert(r1.rest == "w");
			assert(r1.value == "h");
			auto r2 = p("w");
			assert(r2.match);
			assert(r2.rest == "");
			assert(r2.value == "w");
			auto r3 = p("");
			assert(!r3.match);
			return true;
		};
		debug(ct) static assert(dg());
		dg();
	}

	Result!(ParserType!parser[]) combinateMore(int n, alias parser, alias sep = parseString!"")(string input){
		typeof(return) res;
		res.rest = input;
		while(true){
			auto r1 = parser(res.rest);
			if(r1.match){
				res.value = res.value ~ r1.value;
				res.rest = r1.rest;
				auto r2 = sep(r1.rest);
				if(r2.match){
					res.rest = r2.rest;
				}else{
					break;
				}
			}else{
				break;
			}
		}
		if(res.value.length >= n){
			res.match = true;
		}
		return res;
	}

	template combinateMore0(alias parser, alias sep = parseString!""){
		alias combinateMore!(0, parser, sep) combinateMore0;
	}

	template combinateMore1(alias parser, alias sep = parseString!""){
		alias combinateMore!(1, parser, sep) combinateMore1;
	}

	unittest{
		enum dg ={
			alias combinateMore!(0, parseString!"w") p;
			auto r1 = p("wwwwwwwww w");
			assert(r1.match);
			assert(r1.rest == " w");
			assert(r1.value.mkString() == "wwwwwwwww");
			auto r2 = p(" w");
			assert(r2.match);
			assert(r2.rest == " w");
			assert(r2.value.mkString == "");
			alias combinateMore!(1, parseString!"w") p2;
			auto r3 = p2("wwwwwwwww w");
			assert(r3.match);
			assert(r3.rest == " w");
			assert(r3.value.mkString() == "wwwwwwwww");
			auto r4 = p2(" w");
			assert(!r4.match);
			return true;
		};
		debug(ct) static assert(dg());
		dg();
	}

	Result!(Option!(ParserType!parser)) combinateOption(alias parser)(string input){
		typeof(return) res;
		res.rest = input;
		res.match = true;
		auto r = parser(input);
		if(r.match){
			res.value.value = r.value;
			res.value.some = true;
			res.rest = r.rest;
		}
		return res;
	}

	unittest{
		enum dg ={
			alias combinateOption!(parseString!"w") p;
			auto r1 = p("w");
			assert(r1.match);
			assert(r1.rest == "");
			assert(r1.value.some);
			assert(r1.value.value == "w");
			auto r2 = p("");
			assert(r2.match);
			assert(r2.rest == "");
			assert(!r2.value.some);
			return true;
		};
		debug(ct) static assert(dg());
		dg();
	}

	Result!None combinateNone(alias parser)(string input){
		typeof(return) res;
		auto r = parser(input);
		if(r.match){
			res.match = true;
			res.rest = r.rest;
		}
		return res;
	}

	unittest{
		enum dg ={
			alias combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")")) p;
			auto r1 = p("(w)");
			assert(r1.match);
			assert(r1.rest == "");
			assert(r1.value == "w");
			return true;
		};
		debug(ct) static assert(dg());
		dg();
	}

	Result!None combinateAnd(alias parser)(string input){
		typeof(return) res;
		res.rest = input;
		res.match = parser(input).match;
		return res;
	}

	unittest{
		enum dg ={
			alias combinateMore!(0, combinateSequence!(parseString!"w", combinateAnd!(parseString!"w"))) p;
			auto r1 = p("www");
			assert(r1.match);
			assert(r1.rest == "w");
			assert(r1.value.mkString() == "ww");
			return true;
		};
		debug(ct) static assert(dg());
		dg();
	}

	Result!None combinateNot(alias parser)(string input){
		typeof(return) res;
		res.rest = input;
		res.match = !parser(input).match;
		return res;
	}

	unittest{
		enum dg ={
			alias combinateMore!(0, combinateSequence!(parseString!"w", combinateNot!(parseString!"s"))) p;
			auto r1 = p("wwws");
			assert(r1.match);
			assert(r1.rest == "ws");
			assert(r1.value.mkString() == "ww");
			return true;
		};
		debug(ct) static assert(dg());
		dg();
	}

	Result!(ReturnType!(converter)) combinateConvert(alias parser, alias converter)(string input){
		typeof(return) res;
		auto r = parser(input);
		if(r.match){
			res.match = true;
			static if(isTuple!(ParserType!parser)){
				res.value = converter(r.value.field);
			}else{
				res.value = converter(r.value);
			}
			res.rest = r.rest;
		}
		return res;
	}

	unittest{
		enum dg ={
			alias combinateConvert!(
				combinateMore!(0, parseString!"w"),
				function(string[] ws){
					return ws.length;
				}
			) p;
			auto r1 = p("www");
			assert(r1.match);
			assert(r1.rest == "");
			assert(r1.value == 3);
			return true;
		};
		debug(ct) static assert(dg());
		dg();
	}

	Result!(ParserType!parser) combinateCheck(alias parser, alias checker)(string input){
		typeof(return) res;
		auto r = parser(input);
		if(r.match && checker(r.value)){
			res = r;
		}
		return res;
	}

	unittest{
		enum dg ={
			alias combinateConvert!(
				combinateCheck!(
					combinateMore!(0, parseString!"w"),
					function(string[] ws){
						return ws.length == 5;
					}
				),
				function(string[] ws){
					return ws.mkString();
				}
			) p;
			auto r1 = p("wwwww");
			assert(r1.match);
			assert(r1.value == "wwwww");
			assert(r1.rest == "");
			auto r2 = p("wwww");
			assert(!r2.match);
			return true;
		};
		debug(ct) static assert(dg());
		dg();
	}
}

/*parsers*/version(all){
static:
	Result!(string) parseString(string str)(string input) {
		typeof(return) res;
		if(!str.length){
			res.match = true;
			res.value = str;
			res.rest = input;
		}else if(input.length >= str.length && input[0..str.length] == str){
			res.match = true;
			res.value = str;
			res.rest = input[str.length..$];
		}
		return res;
	}

	debug static assert({
		auto r = parseString!"hello"("hello world");
		assert(r.match);
		assert(r.rest == " world");
		assert(r.value == "hello");
		return true;
	}());

	Result!string parseCharRange(dchar low, dchar high)(string input){
		typeof(return) res;
		res.rest = input;
		if(input.length > 0){
			size_t i;
			dchar c = decode(input, i);
			if(low <= c && c <= high){
				res.match = true;
				res.value = input[0..i];
				res.rest = input[i..$];
			}
		}
		return res;
	}

	debug static assert({
		auto r = parseCharRange!('a', 'z')("hoge");
		assert(r.match);
		assert(r.rest == "oge");
		assert(r.value == "h");
		auto r2 = parseCharRange!('\u0100', '\U0010FFFF')("はろーわーるど");
		assert(r2.match);
		assert(r2.rest == "ろーわーるど");
		assert(r2.value == "は");
		auto r3 = parseCharRange!('\u0100', '\U0010FFFF')("hello world");
		assert(!r3.match);
		return true;
	}());

	Result!string parseAnyChar(string input){
		typeof(return) res;
		res.rest = input;
		if(input.length > 0){
			size_t i;
			decode(input, i);
			res.match = true;
			res.value = input[0..i];
			res.rest = input[i..$];
		}
		return res;
	}

	debug static assert({
		auto r = parseAnyChar("hoge");
		assert(r.match);
		assert(r.rest == "oge");
		assert(r.value == "h");
		auto r2 = parseAnyChar("欝だー");
		assert(r2.match);
		assert(r2.rest == "だー");
		assert(r2.value == "欝");
		return true;
	}());

	Result!string parseAnyCharES(string input){
		typeof(return) res;
		res.rest = input;
		if(input.length > 0){
			res.match = true;
			size_t i;
			auto c = decode(input, i);
			if(c == '\\'){
				c = decode(input, i);
				if(c == 'u'){
					res.value = input[0..i+4];
					res.rest = input[i+4..$];
				}else if(c == 'U'){
					res.value = input[0..i+8];
					res.rest = input[i+8..$];
				}else{
					res.value = input[0..i];
					res.rest = input[i..$];
				}
			}else{
				res.value = input[0..i];
				res.rest = input[i..$];
			}
		}
		return res;
	}

	debug static assert({
		auto r = parseAnyCharES(`\"hoge`);
		assert(r.match);
		assert(r.rest == "hoge");
		assert(r.value == `\"`);
		auto r2 = parseAnyCharES("\\U0010FFFF");
		assert(r2.match);
		assert(r2.rest == "");
		assert(r2.value == "\\U0010FFFF");
		auto r3 = parseAnyCharES("\\u10FF");
		assert(r3.match);
		assert(r3.rest == "");
		assert(r3.value == "\\u10FF");
		auto r4 = parseAnyCharES("欝");
		assert(r4.match);
		assert(r4.rest == "");
		assert(r4.value == "欝");
		auto r5 = parseAnyCharES(`\\`);
		assert(r5.match);
		assert(r5.rest == "");
		assert(r5.value == `\\`);
		return true;
	}());

	Result!string parseSpace(string input){
		typeof(return) res;
		if(input.length > 0 && (input[0] == ' ' || input[0] == '\n' || input[0] == '\t' || input[0] == '\r' || input[0] == '\f')){
			res.match = true;
			res.value = input[0..1];
			res.rest = input[1..$];
		}
		return res;
	}

	debug static assert({
		auto r = parseSpace("\thoge");
		assert(r.match);
		assert(r.rest == "hoge");
		assert(r.value == "\t");
		return true;
	}());

	alias combinateNone!(combinateMore0!parseSpace) parseSpaces;

	debug static assert({
		auto r1 = parseSpaces("\t \rhoge");
		assert(r1.match);
		assert(r1.rest == "hoge");
		auto r2 = parseSpaces("hoge");
		assert(r2.match);
		assert(r2.rest == "hoge");
		return true;
	}());

	Result!None parseEOF(string input){
		typeof(return) res;
		if(input.length == 0){
			res.match = true;
		}
		return res;
	}

	debug static assert({
		auto r = parseEOF("");
		assert(r.match);
		return true;
	}());
}

mixin template dpegWithoutMemoize(string src){
	mixin(makeCompilers!false.defs(src).value);
}

mixin template dpeg(string src){
	mixin(makeCompilers!true.defs(src).value);
}

template makeCompilers(bool isMemoize){
	string fix(string parser){
		return isMemoize ? "memoize!(" ~ parser ~ ",uint.max)" : parser;
	}

	Result!string defs(string input){
		return combinateConvert!(
			combinateSequence!(
				parseSpaces,
				combinateMore1!(
					def,
					parseSpaces
				),
				parseSpaces,
				parseEOF
			),
			function(string[] defs){
				return defs.mkString();
			}
		)(input);
	}

	unittest{
		enum dg = {
			string src = q{
				bool hoge = ^"hello" $ >> {return false;};
				Tuple!piyo hoge2 = hoge* >> {return tuple("foo");};
			};
			auto r = defs(src);
			assert(r.match);
			assert(r.rest == "");
			static if(isMemoize){
				assert(
					r.value ==
					"Result!(bool) hoge(string input){"
						"return memoize!(combinateConvert!("
							"memoize!(combinateSequence!("
								"memoize!(combinateNone!("
									"memoize!(parseString!\"hello\",uint.max)"
								"),uint.max),"
								"memoize!(parseEOF,uint.max)"
							"),uint.max),"
							"function(){"
								"return false;"
							"}"
						"),uint.max)(input);"
					"}"
					"Result!(Tuple!piyo) hoge2(string input){"
						"return memoize!(combinateConvert!("
							"memoize!(combinateMore0!("
								"memoize!(hoge,uint.max)"
							"),uint.max),"
							"function(){"
								"return tuple(\"foo\");"
							"}"
						"),uint.max)(input);"
					"}"
				);
			}else{
				assert(
					r.value ==
					"Result!(bool) hoge(string input){"
						"return combinateConvert!("
							"combinateSequence!("
								"combinateNone!("
									"parseString!\"hello\""
								"),"
								"parseEOF"
							"),"
							"function(){"
								"return false;"
							"}"
						")(input);"
					"}"
					"Result!(Tuple!piyo) hoge2(string input){"
						"return combinateConvert!("
							"combinateMore0!("
								"hoge"
							"),"
							"function(){"
								"return tuple(\"foo\");"
							"}"
						")(input);"
					"}"
				);
			}
			return true;
		};
		debug(ct) static assert(dg());
		dg();
	};

	Result!string def(string input){
		return combinateConvert!(
			combinateSequence!(
				typeName,
				parseSpaces,
				id,
				parseSpaces,
				combinateNone!(
					parseString!"="
				),
				parseSpaces,
				convExp,
				parseSpaces,
				combinateNone!(
					parseString!";"
				)
			),
			function(string type, string name, string convExp){
				return "Result!("~type~") "~name~"(string input){"
					"return "~convExp~"(input);"
				"}";
			}
		)(input);
	}

	unittest{
		enum dg = {
			auto r = def(q{bool hoge = ^"hello" $ >> {return false;};});
			assert(r.match);
			assert(r.rest == "");
			static if(isMemoize){
				assert(
					r.value ==
					"Result!(bool) hoge(string input){"
						"return memoize!(combinateConvert!("
							"memoize!(combinateSequence!("
								"memoize!(combinateNone!("
									"memoize!(parseString!\"hello\",uint.max)"
								"),uint.max),"
								"memoize!(parseEOF,uint.max)"
							"),uint.max),"
							"function(){"
								"return false;"
							"}"
						"),uint.max)(input);"
					"}"
				);
			}else{
				assert(
					r.value ==
					"Result!(bool) hoge(string input){"
						"return combinateConvert!("
							"combinateSequence!("
								"combinateNone!("
									"parseString!\"hello\""
								"),"
								"parseEOF"
							"),"
							"function(){"
								"return false;"
							"}"
						")(input);"
					"}"
				);
			}
			return true;
		};
		debug(ct) static assert(dg());
		dg();
	};

	Result!string convExp(string input){
		return combinateConvert!(
			combinateSequence!(
				choiceExp,
				combinateOption!(
					combinateSequence!(
						parseSpaces,
						combinateNone!(
							parseString!">>"
						),
						parseSpaces,
						func
					)
				)
			),
			function(string choiceExp, Option!string func){
				if(func.some){
					return fix("combinateConvert!("~choiceExp~","~func.value~")");
				}else{
					return choiceExp;
				}
			}
		)(input);
	}

	unittest{
		enum dg = {
			auto r = convExp(q{^"hello" $ >> {return false;}});
			assert(r.match);
			assert(r.rest == "");
			static if(isMemoize){
				assert(
					r.value ==
					"memoize!(combinateConvert!("
						"memoize!(combinateSequence!("
							"memoize!(combinateNone!("
								"memoize!(parseString!\"hello\",uint.max)"
							"),uint.max),"
							"memoize!(parseEOF,uint.max)"
						"),uint.max),"
						"function(){"
							"return false;"
						"}"
					"),uint.max)"
				);
			}else{
				assert(
					r.value ==
					"combinateConvert!("
						"combinateSequence!("
							"combinateNone!("
								"parseString!\"hello\""
							"),"
							"parseEOF"
						"),"
						"function(){"
							"return false;"
						"}"
					")"
				);
			}
			return true;
		};
		debug(ct) static assert(dg());
		dg();
	}

	Result!string choiceExp(string input){
		return combinateConvert!(
			combinateSequence!(
				seqExp,
				combinateMore0!(
					combinateSequence!(
						parseSpaces,
						combinateNone!(
							parseString!"/"
						),
						parseSpaces,
						seqExp
					)
				)
			),
			function(string seqExp, string[] seqExps){
				if(seqExps.length){
					return fix("combinateChoice!("~seqExp~","~seqExps.mkString(",")~")");
				}else{
					return seqExp;
				}
			}
		)(input);
	}

	unittest{
		enum dg = {
			auto r1 = choiceExp(`^$* / (&(!"a"))?`);
			assert(r1.match);
			assert(r1.rest == "");
			static if(isMemoize){
				assert(
					r1.value ==
					"memoize!(combinateChoice!("
						"memoize!(combinateMore0!("
							"memoize!(combinateNone!("
								"memoize!(parseEOF,uint.max)"
							"),uint.max)"
						"),uint.max),"
						"memoize!(combinateOption!("
							"memoize!(combinateAnd!("
								"memoize!(combinateNot!("
									"memoize!(parseString!\"a\",uint.max)"
								"),uint.max)"
							"),uint.max)"
						"),uint.max)"
					"),uint.max)"
				);
			}else{
				assert(
					r1.value ==
					"combinateChoice!("
						"combinateMore0!("
							"combinateNone!("
								"parseEOF"
							")"
						"),"
						"combinateOption!("
							"combinateAnd!("
								"combinateNot!("
									"parseString!\"a\""
								")"
							")"
						")"
					")"
				);
			}
			auto r2 = choiceExp(`^"hello" $`);
			assert(r2.match);
			assert(r2.rest == "");
			static if(isMemoize){
				assert(
					r2.value ==
					"memoize!(combinateSequence!("
						"memoize!(combinateNone!("
							"memoize!(parseString!\"hello\",uint.max)"
						"),uint.max),"
						"memoize!(parseEOF,uint.max)"
					"),uint.max)"
				);
			}else{
				assert(
					r2.value ==
					"combinateSequence!("
						"combinateNone!("
							"parseString!\"hello\""
						"),"
						"parseEOF"
					")"
				);
			}
			return true;
		};
		debug(ct) static assert(dg());
		dg();
	}

	Result!string seqExp(string input){
		return combinateConvert!(
			combinateMore1!(
				optionExp,
				parseSpaces
			),
			function(string[] optionExps){
				if(optionExps.length > 1){
					return fix("combinateSequence!("~optionExps.mkString(",")~")");
				}else{
					return optionExps[0];
				}
			}
		)(input);
	}

	unittest{
		enum dg = {
			auto r1 = seqExp("^$* (&(!$))?");
			assert(r1.match);
			assert(r1.rest == "");
			static if(isMemoize){
				assert(
					r1.value ==
					"memoize!(combinateSequence!("
						"memoize!(combinateMore0!("
							"memoize!(combinateNone!("
								"memoize!(parseEOF,uint.max)"
							"),uint.max)"
						"),uint.max),"
						"memoize!(combinateOption!("
							"memoize!(combinateAnd!("
								"memoize!(combinateNot!("
									"memoize!(parseEOF,uint.max)"
								"),uint.max)"
							"),uint.max)"
						"),uint.max)"
					"),uint.max)"
				);
			}else{
				assert(
					r1.value ==
					"combinateSequence!("
						"combinateMore0!("
							"combinateNone!("
								"parseEOF"
							")"
						"),"
						"combinateOption!("
							"combinateAnd!("
								"combinateNot!("
									"parseEOF"
								")"
							")"
						")"
					")"
				);
			}
			enum r2 = seqExp("^\"hello\" $");
			assert(r2.match);
			assert(r2.rest == "");
			static if(isMemoize){
				assert(
					r2.value ==
					"memoize!(combinateSequence!("
						"memoize!(combinateNone!("
							"memoize!(parseString!\"hello\",uint.max)"
						"),uint.max),"
						"memoize!(parseEOF,uint.max)"
					"),uint.max)"
				);
			}else{
				assert(
					r2.value ==
					"combinateSequence!("
						"combinateNone!("
							"parseString!\"hello\""
						"),"
						"parseEOF"
					")"
				);
			}
			return true;
		};
		debug(ct) static assert(dg());
		dg();
	}

	Result!string optionExp(string input){
		return combinateConvert!(
			combinateSequence!(
				postExp,
				parseSpaces,
				combinateOption!(
					combinateNone!(
						parseString!"?"
					)
				)
			),
			function(string convExp, Option!None op){
				if(op.some){
					return fix("combinateOption!("~convExp~")");
				}else{
					return convExp;
				}
			}
		)(input);
	}

	unittest{
		enum dg = {
			auto r1 = optionExp("(&(!\"hello\"))?");
			assert(r1.match);
			assert(r1.rest == "");
			static if(isMemoize){
				assert(
					r1.value ==
					"memoize!(combinateOption!("
						"memoize!(combinateAnd!("
							"memoize!(combinateNot!("
								"memoize!(parseString!\"hello\",uint.max)"
							"),uint.max)"
						"),uint.max)"
					"),uint.max)"
				);
			}else{
				assert(
					r1.value ==
					"combinateOption!("
						"combinateAnd!("
							"combinateNot!("
								"parseString!\"hello\""
							")"
						")"
					")"
				);
			}
			return true;
		};
		debug(ct) static assert(dg());
		dg();
	}

	Result!string postExp(string input){
		return combinateConvert!(
			combinateSequence!(
				preExp,
				combinateOption!(
					combinateSequence!(
						combinateChoice!(
							parseString!"+",
							parseString!"*"
						),
						combinateOption!(
							combinateSequence!(
								combinateNone!(
									parseString!"<"
								),
								choiceExp,
								combinateNone!(
									parseString!">"
								)
							)
						)
					)
				)
			),
			function(string preExp, Option!(Tuple!(string, Option!string)) op){
				final switch(op.value[0]){
					case "+":
						if(op.value[1].some){
							return fix("combinateMore1!("~preExp~","~op.value[1].value~")");
						}else{
							return fix("combinateMore1!("~preExp~")");
						}
					case "*":
						if(op.value[1].some){
							return fix("combinateMore0!("~preExp~","~op.value[1].value~")");
						}else{
							return fix("combinateMore0!("~preExp~")");
						}
					case "":
						return preExp;
				}
			}
		)(input);
	}

	unittest{
		enum dg = {
			auto r1 = postExp("^$*");
			assert(r1.match);
			assert(r1.rest == "");
			static if(isMemoize){
				assert(
					r1.value ==
					"memoize!(combinateMore0!("
						"memoize!(combinateNone!("
							"memoize!(parseEOF,uint.max)"
						"),uint.max)"
					"),uint.max)"
				);
			}else{
				assert(
					r1.value ==
					"combinateMore0!("
						"combinateNone!("
							"parseEOF"
						")"
					")"
				);
			}
			return true;
		};
		debug(ct) static assert(dg());
		dg();
	}

	Result!string preExp(string input){
		return combinateConvert!(
			combinateSequence!(
				combinateOption!(
					combinateChoice!(
						parseString!"&",
						parseString!"^",
						parseString!"!"
					)
				),
				primaryExp
			),
			function(Option!string op, string primaryExp){
				final switch(op.value){
					case "&":
						return fix("combinateAnd!("~primaryExp~")");
					case "!":
						return fix("combinateNot!("~primaryExp~")");
					case "^":
						return fix("combinateNone!("~primaryExp~")");
					case "":
						return primaryExp;
				}
			}
		)(input);
	}

	unittest{
		enum dg = {
			auto r1 = preExp("^$");
			assert(r1.match);
			assert(r1.rest == "");
			static if(isMemoize){
				assert(
					r1.value ==
					"memoize!(combinateNone!("
						"memoize!(parseEOF,uint.max)"
					"),uint.max)"
				);
			}else{
				assert(
					r1.value ==
					"combinateNone!("
						"parseEOF"
					")"
				);
			}
			return true;
		};
		debug(ct) static assert(dg());
		dg();
	}

	Result!string primaryExp(string input){
		return combinateChoice!(
			literal,
			nonterminal,
			combinateSequence!(
				combinateNone!(
					parseString!"("
				),
				convExp,
				combinateNone!(
					parseString!")"
				)
			)
		)(input);
	}

	unittest{
		enum dg = {
			static if(isMemoize){
				auto r1 = primaryExp("(&(!$)?)");
				assert(r1.match);
				assert(r1.rest == "");
				assert(
					r1.value ==
					"memoize!(combinateOption!("
						"memoize!(combinateAnd!("
							"memoize!(combinateNot!("
								"memoize!(parseEOF,uint.max)"
							"),uint.max)"
						"),uint.max)"
					"),uint.max)"
				);
				auto r2 = primaryExp("int");
				assert(r2.match);
				assert(r2.rest == "");
				assert(r2.value == "memoize!(int,uint.max)");
				auto r3 = primaryExp("select!(true)(\"true\", \"false\")");
				assert(r3.match);
				assert(r3.rest == "");
				assert(r3.value == "memoize!(select!(true)(\"true\", \"false\"),uint.max)");
				auto rn = primaryExp("###縺薙・繧ｳ繝｡繝ｳ繝医・陦ｨ遉ｺ縺輔ｌ縺ｾ縺帙ｓ###");
				assert(!rn.match);
			}else{
				auto r1 = primaryExp("(&(!$)?)");
				assert(r1.match);
				assert(r1.rest == "");
				assert(
					r1.value ==
					"combinateOption!("
						"combinateAnd!("
							"combinateNot!("
								"parseEOF"
							")"
						")"
					")"
				);
				auto r2 = primaryExp("int");
				assert(r2.match);
				assert(r2.rest == "");
				assert(r2.value == "int");
				auto r3 = primaryExp("select!(true)(\"true\", \"false\")");
				assert(r3.match);
				assert(r3.rest == "");
				assert(r3.value == "select!(true)(\"true\", \"false\")");
				auto rn = primaryExp("###縺薙・繧ｳ繝｡繝ｳ繝医・陦ｨ遉ｺ縺輔ｌ縺ｾ縺帙ｓ###");
				assert(!rn.match);
			}
			return true;
		};
		debug(ct) static assert(dg());
		dg();
	}

	Result!string literal(string input){
		return combinateChoice!(
			rangeLit,
			stringLit,
			eofLit,
			usefulLit
		)(input);
	}

	unittest{
		enum dg = {
			auto r1 = literal("\"hello\nworld\"");
			assert(r1.match);
			assert(r1.rest == "");
			static if(isMemoize){
				assert(r1.value == "memoize!(parseString!\"hello\nworld\",uint.max)");
			}else{
				assert(r1.value == "parseString!\"hello\nworld\"");
			}
			auto r2 = literal("[a-z]");
			assert(r2.match);
			assert(r2.rest == "");
			static if(isMemoize){
				assert(r2.value == "memoize!(parseCharRange!('a','z'),uint.max)");
			}else{
				assert(r2.value == "parseCharRange!('a','z')");
			}
			auto r3 = usefulLit("@space");
			assert(r3.match);
			assert(r3.rest == "");
			static if(isMemoize){
				assert(r3.value == "memoize!(parseSpace,uint.max)");
			}else{
				assert(r3.value == "parseSpace");
			}
			auto r4 = usefulLit("@es");
			assert(r4.match);
			assert(r4.rest == "");
			static if(isMemoize){
				assert(r4.value == "memoize!(parseEscapeSequence,uint.max)");
			}else{
				assert(r4.value == "parseEscapeSequence");
			}
			auto r5 = usefulLit("@a");
			assert(r5.match);
			assert(r5.rest == "");
			static if(isMemoize){
				assert(r5.value == "memoize!(parseAnyChar,uint.max)");
			}else{
				assert(r5.value == "parseAnyChar");
			}
			auto r6 = usefulLit("@s");
			assert(r6.match);
			assert(r6.rest == "");
			static if(isMemoize){
				assert(r6.value == "memoize!(parseSpaces,uint.max)");
			}else{
				assert(r6.value == "parseSpaces");
			}
			auto r7 = literal("$");
			assert(r7.match);
			assert(r7.rest == "");
			static if(isMemoize){
				assert(r7.value == "memoize!(parseEOF,uint.max)");
			}else{
				assert(r7.value == "parseEOF");
			}
			auto rn = literal("###縺薙・繧ｳ繝｡繝ｳ繝医・陦ｨ遉ｺ縺輔ｌ縺ｾ縺帙ｓ###");
			assert(!rn.match);
			return true;
		};
		debug(ct) static assert(dg());
		dg();
	}

	Result!string stringLit(string input){
		return combinateConvert!(
			combinateSequence!(
				combinateNone!(
					parseString!"\""
				),
				combinateMore0!(
					combinateSequence!(
						combinateNot!(
							parseString!"\""
						),
						parseAnyCharES
					)
				),
				combinateNone!(
					parseString!"\""
				)
			),
			function(string[] strs){
				return fix("parseString!\""~strs.mkString()~"\"");
			}
		)(input);
	}

	unittest{
		enum dg = {
			auto r1 = stringLit("\"hello\nworld\" ");
			assert(r1.match);
			assert(r1.rest == " ");
			static if(isMemoize){
				assert(r1.value == "memoize!(parseString!\"hello\nworld\",uint.max)");
			}else{
				assert(r1.value == "parseString!\"hello\nworld\"");
			}
			auto r2 = stringLit("aa\"");
			assert(!r2.match);
			return true;
		};
		debug(ct) static assert(dg());
		dg();
	}

	Result!string rangeLit(string input){
		return combinateConvert!(
			combinateSequence!(
				combinateNone!(
					parseString!"["
				),
				combinateMore1!(
					combinateSequence!(
						combinateNot!(
							parseString!"]"
						),
						combinateChoice!(
							charRange,
							oneChar
						)
					)
				),
				combinateNone!(
					parseString!"]"
				)
			),
			function(string[] strs){
				if(strs.length == 1){
					return strs[0];
				}else{
					return fix("combinateChoice!("~strs.mkString(",")~")");
				}
			}
		)(input);
	}

	Result!string charRange(string input){
		return combinateConvert!(
			combinateSequence!(
				parseAnyCharES,
				combinateNone!(
					parseString!"-"
				),
				parseAnyCharES,
			),
			function(string low, string high){
				return fix("parseCharRange!('"~low~"','"~high~"')");
			}
		)(input);
	}

	Result!string oneChar(string input){
		return combinateConvert!(
			parseAnyCharES,
			function(string c){
				return fix("parseString!\""~c~"\"");
			}
		)(input);
	}

	unittest{
		enum dg = {
			auto r1 = rangeLit("[a-z]");
			assert(r1.match);
			assert(r1.rest == "");
			static if(isMemoize){
				assert(r1.value == "memoize!(parseCharRange!('a','z'),uint.max)");
			}else{
				assert(r1.value == "parseCharRange!('a','z')");
			}
			auto r2 = rangeLit("[a-zA-Z_]");
			assert(r2.match);
			assert(r2.rest == "");
			static if(isMemoize){
				assert(
					r2.value ==
					"memoize!(combinateChoice!("
						"memoize!(parseCharRange!('a','z'),uint.max),"
						"memoize!(parseCharRange!('A','Z'),uint.max),"
						"memoize!(parseString!\"_\",uint.max)"
					"),uint.max)"
				);
			}else{
				assert(
					r2.value ==
					"combinateChoice!("
						"parseCharRange!('a','z'),"
						"parseCharRange!('A','Z'),"
						"parseString!\"_\""
					")"
				);
			}
			return true;
		};
		debug(ct) static assert(dg());
		dg();
	}

	Result!string eofLit(string input){
		return combinateConvert!(
			combinateNone!(
				parseString!"$"
			),
			function{
				return fix("parseEOF");
			}
		)(input);
	}

    unittest{
    	enum dg = {
			auto r1 = eofLit("$");
			assert(r1.match);
			assert(r1.rest == "");
			static if(isMemoize){
				assert(r1.value == "memoize!(parseEOF,uint.max)");
			}else{
				assert(r1.value == "parseEOF");
			}
			auto r2 = eofLit("#");
			assert(!r2.match);
			return true;
    	};
    	debug(ct) static assert(dg());
    	dg();
    }

	Result!string usefulLit(string input){
		return combinateConvert!(
			combinateChoice!(
				parseString!"@space",
				parseString!"@es",
				parseString!"@a",
				parseString!"@s",
			),
			function(string str){
				final switch(str){
					case "@space":
						return fix("parseSpace");
					case "@es":
						return fix("parseEscapeSequence");
					case "@a":
						return fix("parseAnyChar");
					case "@s":
						return fix("parseSpaces");
				}
			}
		)(input);
	}

    unittest{
    	enum dg = {
			auto r1 = usefulLit("@space");
			assert(r1.match);
			assert(r1.rest == "");
			static if(isMemoize){
				assert(r1.value == "memoize!(parseSpace,uint.max)");
			} else{
				assert(r1.value == "parseSpace");
			}
			auto r2 = usefulLit("@es");
			assert(r2.match);
			assert(r2.rest == "");
			static if(isMemoize){
				assert(r2.value == "memoize!(parseEscapeSequence,uint.max)");
			}else{
				assert(r2.value == "parseEscapeSequence");
			}
			auto r3 = usefulLit("@a");
			assert(r3.match);
			assert(r3.rest == "");
			static if(isMemoize){
				assert(r3.value == "memoize!(parseAnyChar,uint.max)");
			}else{
				assert(r3.value == "parseAnyChar");
			}
			auto r4 = usefulLit("@s");
			assert(r4.match);
			assert(r4.rest == "");
			static if(isMemoize){
				assert(r4.value == "memoize!(parseSpaces,uint.max)");
			}else{
				assert(r4.value == "parseSpaces");
			}
			return true;
    	};
    	debug(ct) static assert(dg());
    	dg();
    }

	Result!string id(string input){
		return combinateConvert!(
			combinateSequence!(
				combinateChoice!(
					parseCharRange!('A','Z'),
					parseCharRange!('a','z'),
					parseString!"_"
				),
				combinateMore0!(
					combinateChoice!(
						parseCharRange!('0','9'),
						parseCharRange!('A','Z'),
						parseCharRange!('a','z'),
						parseString!"_",
						parseString!",",
						parseString!"!",
						arch
					)
				)
			),
			function(string str, string[] strs){
				return str ~ strs.mkString();
			}
		)(input);
	}

    unittest{
    	enum dg = {
			auto r1 = id("int");
			assert(r1.match);
			assert(r1.rest == "");
			assert(r1.value == "int");
			auto r2 = id("select!(true)(\"true\", \"false\")");
			assert(r2.match);
			assert(r2.rest == "");
			assert(r2.value == "select!(true)(\"true\", \"false\")");
			return true;
    	};
    	debug(ct) static assert(dg());
    	dg();
    }

	alias combinateConvert!(id,function(string id){return fix(id);}) nonterminal;

	unittest{
		enum dg = {
			auto r1 = nonterminal("int");
			assert(r1.match);
			assert(r1.rest == "");
			static if(isMemoize){
				assert(r1.value == "memoize!(int,uint.max)");
			}else{
				assert(r1.value == "int");
			}
			auto r2 = nonterminal("select!(true)(\"true\", \"false\")");
			assert(r2.match);
			assert(r2.rest == "");
			static if(isMemoize){
				assert(r2.value == "memoize!(select!(true)(\"true\", \"false\"),uint.max)");
			}else{
				assert(r2.value == "select!(true)(\"true\", \"false\")");
			}
			return true;
		};
		debug(ct) static assert(dg());
		dg();
    }

	Result!string typeName(string input){
		return combinateConvert!(
			combinateSequence!(
				combinateChoice!(
					parseCharRange!('A','Z'),
					parseCharRange!('a','z'),
					parseString!"_"
				),
				parseSpaces,
				combinateMore0!(
					combinateChoice!(
						parseCharRange!('0','9'),
						parseCharRange!('A','Z'),
						parseCharRange!('a','z'),
						parseString!"_",
						parseString!",",
						parseString!"!",
						arch,
						squareArch
					)
				)
			),
			function(string str, string[] strs){
				return str ~ strs.mkString();
			}
		)(input);
	}

	unittest{
		enum dg = {
			auto r1 = typeName("int");
			assert(r1.match);
			assert(r1.rest == "");
			assert(r1.value == "int");
			auto r2 = typeName("Tuple!(string, int)");
			assert(r2.match);
			assert(r2.rest == "");
			assert(r2.value == "Tuple!(string, int)");
			auto r3 = typeName("int[]");
			assert(r3.match);
			assert(r3.rest == "");
			assert(r3.value == "int[]");
			return true;
		};
		debug(ct) static assert(dg());
		dg();
	}

	Result!string func(string input){
		return combinateConvert!(
			combinateSequence!(
				combinateOption!(
					combinateSequence!(
						arch,
						parseSpaces
					)
				),
				brace
			),
			function(Option!string arch, string brace){
				if(arch.some){
					return "function" ~ arch.value ~ brace;
				}else{
					return "function()" ~ brace;
				}
			}
		)(input);
	}

	unittest{
		enum dg = {
			auto r = func(
			"(int num, string code){"
				"string res;"
				"foreach(staticNum; 0..num){"
					"foreach(c;code){"
						"if(c == '@'){"
							"res ~= to!string(staticNum);"
						"}else{"
							"res ~= c;"
						"}"
					"}"
				"}"
				"return res;"
			"}");
			assert(r.match);
			assert(r.rest == "");
			assert(
				r.value ==
				"function(int num, string code){"
					"string res;"
					"foreach(staticNum; 0..num){"
						"foreach(c;code){"
							"if(c == '@'){"
								"res ~= to!string(staticNum);"
							"}else{"
								"res ~= c;"
							"}"
						"}"
					"}"
					"return res;"
				"}"
			);
			return true;
		};
		debug(ct) static assert(dg());
		dg();
	}

	Result!string arch(string input){
		return combinateConvert!(
			combinateSequence!(
				combinateNone!(
					parseString!"("
				),
				combinateMore0!(
					combinateChoice!(
						arch,
						combinateSequence!(
							combinateNot!(
								parseString!")"
							),
							parseAnyChar
						)
					)
				),
				combinateNone!(
					parseString!")"
				)
			),
			function(string[] strs){
				return "("~strs.mkString()~")";
			}
		)(input);
	}

	unittest{
		enum dg = {
			auto r = arch("(a(i(u)e)o())");
			assert(r.match);
			assert(r.rest == "");
			assert(r.value == "(a(i(u)e)o())");
			return true;
		};
		debug(ct) static assert(dg());
		dg();
	}

	Result!string squareArch(string input){
		return combinateConvert!(
			combinateSequence!(
				combinateNone!(
					parseString!"["
				),
				combinateMore0!(
					combinateChoice!(
						squareArch,
						combinateSequence!(
							combinateNot!(
								parseString!"]"
							),
							parseAnyChar
						)
					)
				),
				combinateNone!(
					parseString!"]"
				)
			),
			function (string[] strs){
				return "["~strs.mkString()~"]";
			}
		)(input);
	}

	unittest{
		enum dg = {
			auto r = squareArch("[a[i[u]e]o[]]");
			assert(r.match);
			assert(r.rest == "");
			assert(r.value == "[a[i[u]e]o[]]");
			return true;
		};
		debug(ct) static assert(dg());
		dg();
	}

	Result!string brace(string input){
		return combinateConvert!(
			combinateSequence!(
				combinateNone!(
					parseString!"{"
				),
				combinateMore0!(
					combinateChoice!(
						brace,
						combinateSequence!(
							combinateNot!(
								parseString!"}"
							),
							parseAnyChar
						)
					)
				),
				combinateNone!(
					parseString!"}"
				)
			),
			function(string[] strs){
				return "{"~strs.mkString()~"}";
			}
		)(input);
	}

	unittest{
		enum dg = {
			auto r = brace("{a{i{u}e}o{}}");
			assert(r.match);
			assert(r.rest == "");
			assert(r.value == "{a{i{u}e}o{}}");
			return true;
		};
		debug(ct) static assert(dg());
		dg();
	}
}

debug pragma(msg, makeCompilers!false);
debug pragma(msg, makeCompilers!true);

debug void main(){}

private:

string mkString(string[] strs, string sep = ""){
	string res;
	foreach(i, str; strs){
		if(i){
			if(sep.length){
				res ~= sep;
			}
		}
		if(str.length){
			res ~= str;
		}
	}
	return res;
}

template ResultType(alias R){
	static if(is(R Unused == Result!E, E)){
		alias E ResultType;
	}else{
		static assert(false);
	}
}

template ParserType(alias parser){
	static if(is(ReturnType!parser Unused == Result!(T), T)){
		alias T ParserType;
	}else{
		static assert(false);
	}
}

template CombinateSequenceImplType(parsers...){
	static if(staticLength!parsers == 1){
		static if(isTuple!(ParserType!(parsers[0]))){
			alias Result!(ParserType!(parsers[0])) CombinateSequenceImplType;
		}else{
			alias Result!(Tuple!(ParserType!(parsers[0]))) CombinateSequenceImplType;
		}
	}else{
		static if(isTuple!(ParserType!(parsers[0]))){
			alias Result!(Tuple!(ParserType!(parsers[0]).Types, ResultType!(CombinateSequenceImplType!(parsers[1..$])).Types)) CombinateSequenceImplType;
		}else{
			alias Result!(Tuple!(ParserType!(parsers[0]), ResultType!(CombinateSequenceImplType!(parsers[1..$])).Types)) CombinateSequenceImplType;
		}
	}
}

template UnTuple(E){
	static if(staticLength!(ResultType!E.Types) == 1){
		alias Result!(ResultType!E.Types[0]) UnTuple;
	}else{
		alias E UnTuple;
	}
}

UnTuple!R unTuple(R)(R r){
	static if(staticLength!(ResultType!(R).Types) == 1){
		return Result!(ResultType!(R).Types[0])(r.match, r.value[0], r.rest);
	}else{
		return r;
	}
}

template CommonParserType(parsers...){
	static if(staticLength!parsers == 1){
		alias ParserType!(parsers[0]) CommonParserType;
	}else{
		alias CommonType!(ParserType!(parsers[0]), CommonParserType!(parsers[1..$])) CommonParserType;
	}
}

dchar decode(string str, ref size_t i){
	dchar res;
	if(!(str[i] & 0b_1000_0000)){
		res = str[i];
		i+=1;
		return res;
	}else if(!(str[i] & 0b_0010_0000)){
		res = str[i] & 0b_0001_1111;
		res <<= 6;
		res |= str[i+1] & 0b_0011_1111;
		i+=2;
		return res;
	}else if(!(str[i] & 0b_0001_0000)){
		res = str[i] & 0b_0000_1111;
		res <<= 6;
		res |= str[i+1] & 0b_0011_1111;
		res <<= 6;
		res |= str[i+2] & 0b_0011_1111;
		i+=3;
		return res;
	}else{
		res = str[i] & 0b_0000_0111;
		res <<= 6;
		res |= str[i+1] & 0b_0011_1111;
		res <<= 6;
		res |= str[i+2] & 0b_0011_1111;
		res <<= 6;
		res |= str[i+3] & 0b_0011_1111;
		i+=4;
		return res;
	}
}

