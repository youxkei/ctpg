module youkei.ctpg;

import std.conv;
import std.traits;
import std.typecons;
import std.typetuple;
import std.functional;

alias Tuple!() None;
alias void*[size_t][size_t][string] memo_t;

version(none){
	ReturnType!Func memoizeInput(alias Func)(stringp ainput, ref memo_t amemo){
		auto lmemo0 = Func.mangleof in amemo;
		if(lmemo0){
			auto lmemo1 = ainput.line in *lmemo0;
			if(lmemo1){
				auto lmemo2 = ainput.column in *lmemo1;
				if(lmemo2){
					return *(cast(ReturnType!Func*)(*lmemo2));
				}
			}
		}
		auto lres = Func(ainput, amemo);
		amemo[Func.mangleof][ainput.line][ainput.column] = [lres].ptr;
		return lres;
	}
}

version(all){
	ReturnType!Func memoizeInput(alias Func)(stringp ainput, ref memo_t amemo){
		auto lres = Func(ainput, amemo);
		amemo[Func.mangleof][ainput.line][ainput.column] = [lres].ptr;
		return lres;
	}
}

version(none){
	template memoizeInput(alias Func){
		alias Func memoizeInput;
	}
}

struct stringp{
	public{
		string str;
		int line = 1;
		int column = 1;


		const @safe pure nothrow
		immutable(char) opIndex(size_t ai){
			return pstr[ai];
		}


		const @safe pure nothrow
		typeof(this) opSlice(size_t ax, size_t ay){
			typeof(return) lres;
			lres.str = pstr[ax..ay];
			lres.line = pline;
			lres.column = pcolumn;
			for(size_t li; li < ax; li++){
				if(pstr[li] == '\n'){
					lres.line++;
					lres.column = 1;
				}else{
					lres.column++;
				}
			}
			return lres;
		}


		const pure @safe nothrow
		bool opEquals(T)(T arhs) if(is(T == string)){
			return pstr == arhs;
		}


		const pure @safe nothrow @property
		size_t length(){
			return pstr.length;
		}


		const pure @safe nothrow
		dchar decode(ref size_t ai){
			return .decode(pstr, ai);
		}


		pure @safe nothrow @property
		string to(){
			return pstr;
		}
	}

	private{
		invariant(){
			assert(pline >= 0);
			assert(pcolumn >= 0);
		}
		alias str pstr;
		alias line pline;
		alias column pcolumn;
	}
}

debug(ctpg) unittest{
	enum dg = {
		auto s1 = "hoge".s;
		assert(s1 == "hoge");
		assert(s1.line == 1);
		assert(s1.column == 1);
		auto s2 = s1[1..s1.length];
		assert(s2 == "oge");
		assert(s2.line == 1);
		assert(s2.column == 2);
		auto s3 = s2[s2.length..s2.length];
		assert(s3 == "");
		assert(s3.line == 1);
		assert(s3.column == 5);
		auto s4 = "メロスは激怒した。".s;
		auto s5 = s4[3..s4.length];
		assert(s5 == "ロスは激怒した。");
		assert(s5.line == 1);
		assert(s5.column == 4);//TODO: column should be 2
		auto s6 = ("hoge\npiyo".s)[5..9];
		assert(s6 == "piyo");
		assert(s6.line == 2);
		assert(s6.column == 1);
		return true;
	};
	debug(ctpg_ct) static assert(dg());
	dg();
}

struct Result(T){
	bool match;
	T value;
	stringp rest;
	Error error;

	void opAssign(F)(Result!F rhs)pure @safe nothrow if(isAssignable!(T, F)){
		match = rhs.match;
		value = rhs.value;
		rest = rhs.rest;
		error = rhs.error;
	}
}

struct Option(T){
	T value;
	bool some;
	bool opCast(E)()const if(is(E == bool)){
		return some;
	}
}

struct Error{
	invariant(){
		assert(line >= 1);
		assert(column >= 1);
	}

	string need;
	int line;
	int column;
}

/* combinators */ version(all){
	/* combinateSequence */ version(all){
		UnTuple!(CombinateSequenceImplType!Parsers) combinateSequence(Parsers...)(stringp ainput, ref memo_t amemo){
			static assert(staticLength!Parsers > 0);
			return unTuple(combinateSequenceImpl!Parsers(ainput, amemo));
		}

		private CombinateSequenceImplType!Parsers combinateSequenceImpl(Parsers...)(stringp ainput, ref memo_t amemo){
			typeof(return) lres;
			static if(staticLength!Parsers == 1){
				auto lr = Parsers[0](ainput, amemo);
				if(lr.match){
					lres.match = true;
					static if(isTuple!(ParserType!(Parsers[0]))){
						lres.value = lr.value;
					}else{
						lres.value = tuple(lr.value);
					}
					lres.rest = lr.rest;
				}else{
					lres.error = lr.error;
				}
			}else{
				static if(!__traits(compiles, {auto lr1 = Parsers[0](ainput, amemo);})){
					static assert(false);
				}
				auto lr1 = Parsers[0](ainput, amemo);
				if(lr1.match){
					auto lr2 = combinateSequenceImpl!(Parsers[1..$])(lr1.rest, amemo);
					if(lr2.match){
						lres.match = true;
						static if(isTuple!(ParserType!(Parsers[0]))){
							lres.value = tuple(lr1.value.field, lr2.value.field);
						}else{
							lres.value = tuple(lr1.value, lr2.value.field);
						}
						lres.rest = lr2.rest;
					}else{
						lres.error = lr2.error;
					}
				}else{
					lres.error = lr1.error;
				}
			}
			return lres;
		}

		debug(ctpg) unittest{
			enum ldg = {
				{
					auto lr = getResult!(combinateSequence!(
						parseString!("hello"),
						parseString!("world")
					))("helloworld");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value[0] == "hello");
					assert(lr.value[1] == "world");
				}
				{
					auto lr = getResult!(combinateSequence!(
						combinateSequence!(
							parseString!("hello"),
							parseString!("world")
						),
						parseString!"!"
					))("helloworld!");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value[0] == "hello");
					assert(lr.value[1] == "world");
					assert(lr.value[2] == "!");
				}
				{
					auto lr = getResult!(combinateSequence!(
						parseString!("hello"),
						parseString!("world")
					))("hellovvorld");
					assert(!lr.match);
					assert(lr.rest == "");
					assert(lr.error.need == q{"world"});
					assert(lr.error.line == 1);
					assert(lr.error.column == 6);
				}
				{
					auto lr = getResult!(combinateSequence!(
						parseString!("hello"),
						parseString!("world"),
						parseString!("!")
					))("helloworld?");
					assert(!lr.match);
					assert(lr.rest == "");
					assert(lr.error.need == q{"!"});
					assert(lr.error.line == 1);
					assert(lr.error.column == 11);
				}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* combinateChoice */ version(all){
		Result!(CommonParserType!Parsers) combinateChoice(Parsers...)(stringp ainput, ref memo_t amemo){
			static assert(staticLength!Parsers > 0);
			static if(staticLength!Parsers == 1){
				return Parsers[0](ainput, amemo);
			}else{
				typeof(return) lres;
				auto lr1 = Parsers[0](ainput, amemo);
				if(lr1.match){
					lres = lr1;
					return lres;
				}else{
					lres.error = lr1.error;
				}
				auto lr2 = combinateChoice!(Parsers[1..$])(ainput, amemo);
				if(lr2.match){
					lres = lr2;
					return lres;
				}else{
					lres.error.need ~= " or " ~ lr2.error.need;
				}
				return lres;
			}
		}

		debug(ctpg) unittest{
			enum ldg = {
				alias getResult!(combinateChoice!(parseString!"h",parseString!"w")) p;
				{
					auto lr = p("hw");
					assert(lr.match);
					assert(lr.rest == "w");
					assert(lr.value == "h");
				}
				{
					auto lr = p("w");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "w");
				}
				{
					auto lr = p("");
					assert(!lr.match);
					assert(lr.rest == "");
					assert(lr.error.need == q{"h" or "w"});
					assert(lr.error.line == 1);
					assert(lr.error.column == 1);
				}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* combinateMore */ version(all){
		Result!(ParserType!Parser[]) combinateMore(int N, alias Parser, alias Sep = parseString!"")(stringp ainput, ref memo_t amemo){
			typeof(return) lres;
			stringp lstr = ainput;
			while(true){
				auto lr1 = Parser(lstr, amemo);
				if(lr1.match){
					lres.value = lres.value ~ lr1.value;
					lstr = lr1.rest;
					auto lr2 = Sep(lstr, amemo);
					if(lr2.match){
						lstr = lr2.rest;
					}else{
						break;
					}
				}else{
					lres.error = lr1.error;
					break;
				}
			}
			if(lres.value.length >= N){
				lres.match = true;
				lres.rest = lstr;
			}
			return lres;
		}

		template combinateMore0(alias Parser, alias Sep = parseString!""){
			alias combinateMore!(0, Parser, Sep) combinateMore0;
		}

		template combinateMore1(alias Parser, alias Sep = parseString!""){
			alias combinateMore!(1, Parser, Sep) combinateMore1;
		}

		debug(ctpg) unittest{
			enum ldg = {
				{
					alias getResult!(combinateMore0!(parseString!"w")) p;
					{
						auto lr = p("wwwwwwwww w");
						assert(lr.match);
						assert(lr.rest == " w");
						assert(lr.value.mkString() == "wwwwwwwww");
					}
					{
						auto lr = p(" w");
						assert(lr.match);
						assert(lr.rest == " w");
						assert(lr.value.mkString == "");
					}
				}
				{
					alias getResult!(combinateMore1!(parseString!"w")) p;
					{
						auto lr = p("wwwwwwwww w");
						assert(lr.match);
						assert(lr.rest == " w");
						assert(lr.value.mkString() == "wwwwwwwww");
					}
					{
						auto lr = p(" w");
						assert(!lr.match);
						assert(lr.rest == "");
						assert(lr.error.need == q{"w"});
						assert(lr.error.line == 1);
						assert(lr.error.column == 1);
					}
				}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* combinateOption */ version(all){
		Result!(Option!(ParserType!Parser)) combinateOption(alias Parser)(stringp ainput, ref memo_t amemo){
			typeof(return) lres;
			lres.rest = ainput;
			lres.match = true;
			auto lr = Parser(ainput, amemo);
			if(lr.match){
				lres.value.value = lr.value;
				lres.value.some = true;
				lres.rest = lr.rest;
			}
			return lres;
		}

		debug(ctpg) unittest{
			enum ldg = {
				alias getResult!(combinateOption!(parseString!"w")) p;
				{
					auto lr = p("w");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value.some);
					assert(lr.value.value == "w");
				}
				{
					auto lr = p("");
					assert(lr.match);
					assert(lr.rest == "");
					assert(!lr.value.some);
				}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* combinateNone */ version(all){
		Result!None combinateNone(alias Parser)(stringp ainput, ref memo_t amemo){
			typeof(return) lres;
			auto lr = Parser(ainput, amemo);
			if(lr.match){
				lres.match = true;
				lres.rest = lr.rest;
			}else{
				lres.error = lr.error;
			}
			return lres;
		}

		debug(ctpg) unittest{
			enum ldg = {
				{
					alias getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")"))) p;
					auto lr = p("(w)");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "w");
				}
				{
					auto lr = getResult!(combinateNone!(parseString!"w"))("a");
					assert(!lr.match);
					assert(lr.rest == "");
					assert(lr.error.need == q{"w"});
					assert(lr.error.line == 1);
					assert(lr.error.column == 1);
				}
				{
					alias getResult!(combinateSequence!(combinateNone!(parseString!"("), parseString!"w", combinateNone!(parseString!")"))) p;
					auto lr = p("(w}");
					assert(!lr.match);
					assert(lr.rest == "");
					assert(lr.error.need == q{")"});
					assert(lr.error.line == 1);
					assert(lr.error.column == 3);
				}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* combinateAnd */ version(all){
		Result!None combinateAnd(alias Parser)(stringp ainput, ref memo_t amemo){
			typeof(return) lres;
			lres.rest = ainput;
			auto lr = Parser(ainput, amemo);
			lres.match = lr.match;
			lres.error = lr.error;
			return lres;
		}

		debug(ctpg) unittest{
			enum ldg = {
				alias getResult!(combinateMore1!(combinateSequence!(parseString!"w", combinateAnd!(parseString!"w")))) p;
				{
					auto lr = p("www");
					assert(lr.match);
					assert(lr.rest == "w");
					assert(lr.value.mkString() == "ww");
				}
				{
					auto lr = p("w");
					assert(!lr.match);
					assert(lr.error.need == q{"w"});
					assert(lr.error.line == 1);
					assert(lr.error.column == 2);
				}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* combinateNot */ version(all){
		Result!None combinateNot(alias Parser)(stringp ainput, ref memo_t amemo){
			typeof(return) lres;
			lres.rest = ainput;
			lres.match = !Parser(ainput, amemo).match;
			return lres;
		}

		debug(ctpg) unittest{
			enum ldg = {
				alias getResult!(combinateMore1!(combinateSequence!(parseString!"w", combinateNot!(parseString!"s")))) p;
				auto lr = p("wwws");
				assert(lr.match);
				assert(lr.rest == "ws");
				assert(lr.value.mkString() == "ww");
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* combinateConvert */ version(all){
		Result!(ReturnType!(Converter)) combinateConvert(alias Parser, alias Converter)(stringp ainput, ref memo_t amemo){
			typeof(return) lres;
			auto lr = Parser(ainput, amemo);
			if(lr.match){
				lres.match = true;
				static if(isTuple!(ParserType!Parser)){
					static if(__traits(compiles, Converter(lr.value.field))){
						lres.value = Converter(lr.value.field);
					}else static if(__traits(compiles, new Converter(lr.value.field))){
						lres.value = new Converter(lr.value.field);
					}else{
						static assert(false, Converter.mangleof ~ " cannot call with argument type " ~ typeof(lr.value.field).stringof);
					}
				}else{
					static if(__traits(compiles, Converter(lr.value))){
						lres.value = Converter(lr.value);
					}else static if(__traits(compiles, new Converter(lr.value))){
						lres.value = new Converter(lr.value);
					}else{
						static assert(false, Converter.mangleof ~ " cannot call with argument type " ~ typeof(lr.value).stringof);
					}
				}
				lres.rest = lr.rest;
			}else{
				lres.error = lr.error;
			}
			return lres;
		}

		debug(ctpg) unittest{
			enum ldg = {
				alias getResult!(
					combinateConvert!(
						combinateMore1!(parseString!"w"),
						function(string[] ws)@safe pure nothrow{
							return ws.length;
						}
					)
				) p;
				{
					auto lr = p("www");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == 3);
				}
				{
					auto lr = p("a");
					assert(!lr.match);
					assert(lr.error.need == q{"w"});
					assert(lr.error.line == 1);
					assert(lr.error.column == 1);
				}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* combinateCheck */ version(all){
		Result!(ParserType!Parser) combinateCheck(alias Parser, alias Checker)(stringp ainput, ref memo_t amemo){
			typeof(return) lres;
			auto lr = Parser(ainput, amemo);
			if(lr.match){
				if(Checker(lr.value)){
					lres = lr;
				}else{
					lres.error = Error("passing check", ainput.line, ainput.column);
				}
			}else{
				lres.error = lr.error;
			}
			return lres;
		}

		debug(ctpg) unittest{
			enum ldg = {
				alias getResult!(
					combinateConvert!(
						combinateCheck!(
							combinateMore!(0, parseString!"w"),
							function(string[] ws){
								return ws.length == 5;
							}
						),
						function(string[] ws){
							return ws.mkString();
						}
					)
				) p;
				{
					auto lr = p("wwwww");
					assert(lr.match);
					assert(lr.value == "wwwww");
					assert(lr.rest == "");
				}
				{
					auto lr = p("wwww");
					assert(!lr.match);
				}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* combinateString */ version(all){
		Result!string combinateString(alias Parser)(stringp ainput, ref memo_t amemo){
			typeof(return) lres;
			auto lr = Parser(ainput, amemo);
			if(lr.match){
				lres.match = true;
				lres.value = flat(lr.value);
				lres.rest = lr.rest;
			}else{
				lres.error = lr.error;
			}
			return lres;
		}
	}
}

/* parsers */ version(all){
	/* parseString */ version(all){
		Result!(string) parseString(string str)(stringp ainput, ref memo_t amemo){
			typeof(return) lres;
			if(!str.length){
				lres.match = true;
				lres.rest = ainput;
				return lres;
			}
			if(ainput.length >= str.length && ainput[0..str.length] == str){
				lres.match = true;
				lres.value = str;
				lres.rest = ainput[str.length..ainput.length];
				return lres;
			}
			lres.error = Error('"' ~ str ~ '"', ainput.line, ainput.column);
			return lres;
		}

		debug(ctpg) unittest{
			enum ldg = {
				{
					auto lr = getResult!(parseString!"hello")("hello world");
					assert(lr.match);
					assert(lr.rest == " world");
					assert(lr.value == "hello");
				}
				{
					auto lr = getResult!(parseString!"hello")("hllo world");
					assert(!lr.match);
					assert(lr.rest == "");
					assert(lr.error.need == "\"hello\"");
					assert(lr.error.line == 1);
					assert(lr.error.column == 1);
				}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* parseCharRange */ version(all){
		Result!string parseCharRange(dchar Low, dchar High)(stringp ainput, ref memo_t amemo){
			typeof(return) lres;
			if(ainput.length > 0){
				size_t li;
				dchar lc = ainput.decode(li);
				if(Low <= lc && lc <= High){
					lres.match = true;
					lres.value = ainput[0..li].to;
					lres.rest = ainput[li..ainput.length];
					return lres;
				}
			}
			lres.error = Error("c: '" ~ to!string(Low) ~ "' <= c <= '" ~ to!string(High) ~ "'", ainput.line, ainput.column);
			return lres;
		}

		debug(ctpg) unittest{
			enum ldg = {
				{
					auto lr = getResult!(parseCharRange!('a', 'z'))("hoge");
					assert(lr.match);
					assert(lr.rest == "oge");
					assert(lr.value == "h");
				}
				{
					auto lr = getResult!(parseCharRange!('\u0100', '\U0010FFFF'))("表が怖い噂のソフト");
					assert(lr.match);
					assert(lr.rest == "が怖い噂のソフト");
					assert(lr.value == "表");
				}
				{
					auto lr = getResult!(parseCharRange!('\u0100', '\U0010FFFF'))("hello world");
					assert(!lr.match);
					assert(lr.rest == "");
					assert(lr.error.need == "c: '\u0100' <= c <= '\U0010FFFF'");
					assert(lr.error.line == 1);
					assert(lr.error.column == 1);
				}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* parseAnyChar */ version(all){
		Result!string parseAnyChar(stringp ainput, ref memo_t amemo){
			typeof(return) lres;
			lres.rest = ainput;
			if(ainput.length > 0){
				size_t li;
				ainput.decode(li);
				lres.match = true;
				lres.value = ainput[0..li].to;
				lres.rest = ainput[li..ainput.length];
			}else{
				lres.error = Error("any char", ainput.line, ainput.column);
			}
			return lres;
		}

		debug(ctpg) unittest{
			enum ldg = {
				{
					auto lr = getResult!parseAnyChar("hoge");
					assert(lr.match);
					assert(lr.rest == "oge");
					assert(lr.value == "h");
				}
				{
					auto lr = getResult!parseAnyChar("表が怖い噂のソフト");
					assert(lr.match);
					assert(lr.rest == "が怖い噂のソフト");
					assert(lr.value == "表");
				}
				{
					auto lr = getResult!parseAnyChar("独");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "独");
				}
				{
					auto lr = getResult!parseAnyChar("");
					assert(!lr.match);
					assert(lr.error.need == "any char");
					assert(lr.error.line == 1);
					assert(lr.error.column == 1);
				}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* parseEscapeSequence */ version(all){
		Result!string parseEscapeSequence(stringp ainput, ref memo_t amemo){
			typeof(return) lres;
			if(ainput.length > 0 && ainput[0] == '\\'){
				lres.match = true;
				auto lc = ainput[1];
				if(lc == 'u'){
					lres.value = ainput[0..6].to;
					lres.rest = ainput[6..ainput.length];
				}else if(lc == 'U'){
					lres.value = ainput[0..10].to;
					lres.rest = ainput[10..ainput.length];
				}else{
					lres.value = ainput[0..2].to;
					lres.rest = ainput[2..ainput.length];
				}
				return lres;
			}else{
				lres.error = Error("escape sequence", ainput.line, ainput.column);
			}
			return lres;
		}

		debug(ctpg) unittest{
			enum ldg = {
				{
					auto lr = getResult!parseEscapeSequence(`\"hoge`);
					assert(lr.match);
					assert(lr.rest == "hoge");
					assert(lr.value == `\"`);
				}
				{
					auto lr = getResult!parseEscapeSequence("\\U0010FFFF");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "\\U0010FFFF");
				}
				{
					auto lr = getResult!parseEscapeSequence("\\u10FF");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "\\u10FF");
				}
				{
					auto lr = getResult!parseEscapeSequence("欝");
					assert(!lr.match);
					assert(lr.error.need == "escape sequence");
					assert(lr.error.line == 1);
					assert(lr.error.column == 1);
				}
				{
					auto lr = getResult!parseEscapeSequence(`\\`);
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == `\\`);
				}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* parseSpace */ version(all){
		Result!string parseSpace(stringp ainput, ref memo_t amemo){
			typeof(return) lres;
			if(ainput.length > 0 && (ainput[0] == ' ' || ainput[0] == '\n' || ainput[0] == '\t' || ainput[0] == '\r' || ainput[0] == '\f')){
				lres.match = true;
				lres.value = ainput[0..1].to;
				lres.rest = ainput[1..ainput.length];
			}else{
				lres.error = Error("space", ainput.line, ainput.column);
			}
			return lres;
		}

		debug(ctpg) unittest{
			enum ldg = {
				{
					auto lr = getResult!parseSpace("\thoge");
					assert(lr.match);
					assert(lr.rest == "hoge");
					assert(lr.value == "\t");
				}
				{
					auto lr = getResult!parseSpace("hoge");
					assert(!lr.match);
					assert(lr.rest == "");
					assert(lr.error.need == "space");
					assert(lr.error.line == 1);
					assert(lr.error.column == 1);
				}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* parseSpaces */ version(all){
		alias combinateNone!(combinateMore0!parseSpace) parseSpaces;

		debug(ctpg) unittest{
			enum ldg = {
				{
					auto lr = getResult!parseSpaces("\t \rhoge");
					assert(lr.match);
					assert(lr.rest == "hoge");
				}
				{
					auto lr = getResult!parseSpaces("hoge");
					assert(lr.match);
					assert(lr.rest == "hoge");
				}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* parseEOF */ version(all){
		Result!None parseEOF(stringp ainput, ref memo_t amemo){
			typeof(return) lres;
			if(ainput.length == 0){
				lres.match = true;
			}else{
				lres.error = Error("EOF", ainput.line, ainput.column);
			}
			return lres;
		}

		debug(ctpg) unittest{
			enum ldg = {
				{
					auto lr = getResult!parseEOF("");
					assert(lr.match);
				}
				{
					auto lr = getResult!parseEOF("hoge");
					assert(!lr.match);
					assert(lr.error.need == "EOF");
					assert(lr.error.line == 1);
					assert(lr.error.column == 1);
				}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* parseIdent */ version(all){
		alias combinateString!(
			combinateSequence!(
				combinateChoice!(
					parseString!"_",
					parseCharRange!('a','z'),
					parseCharRange!('A','Z')
				),
				combinateMore0!parseIdentChar
			)
		) parseIdent;

		alias combinateChoice!(
			parseString!"_",
			parseCharRange!('a','z'),
			parseCharRange!('A','Z'),
			parseCharRange!('0','9')
		) parseIdentChar;

		debug(ctpg) unittest{
			enum ldg = {
				{
					auto lr = getResult!parseIdent("hoge");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "hoge");
				}
				{
					auto lr = getResult!parseIdent("_x");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "_x");
				}
				{
					auto lr = getResult!parseIdent("_0");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "_0");
				}
				{
					auto lr = getResult!parseIdent("0");
					assert(!lr.match);
					assert(lr.rest == "");
					assert(lr.error.line == 1);
					assert(lr.error.column == 1);
				}
				{
					auto lr = getResult!parseIdent("あ");
					assert(!lr.match);
					assert(lr.rest == "");
					assert(lr.error.line == 1);
					assert(lr.error.column == 1);
				}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* parseStringLiteral */ version(all){
		alias combinateString!(
			combinateSequence!(
				combinateNone!(parseString!"\""),
				combinateMore0!(
					combinateSequence!(
						combinateNot!(parseString!"\""),
						combinateChoice!(
							parseEscapeSequence,
							parseAnyChar
						)
					)
				),
				combinateNone!(parseString!"\"")
			)
		) parseStringLiteral;

		debug(ctpg) unittest{
			enum ldg = {
				{
					auto lr = getResult!parseStringLiteral(q{"表が怖い噂のソフト"});
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "表が怖い噂のソフト");
				}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* parseIntLiteral */ version(all){
		alias combinateChoice!(
			combinateConvert!(
				combinateNone!(parseString!"0"),
				function(){
					return 0;
				}
			),
			combinateConvert!(
				combinateSequence!(
					parseCharRange!('1', '9'),
					combinateMore0!(parseCharRange!('0', '9'))
				),
				function(string ahead, string[] atails){
					int lres = ahead[0] - '0';
					foreach(lchar; atails){
						lres = lres * 10 + lchar[0] - '0';
					}
					return lres;
				}
			)
		) parseIntLiteral;

		debug(ctpg) unittest{
			enum ldg = {
				{
					auto lr = getResult!parseIntLiteral(q{3141});
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == 3141);
				}
				{
					auto lr = getResult!parseIntLiteral(q{0});
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == 0);
				}
				{
					auto lr = getResult!parseIntLiteral("0123");
					assert(lr.match);
					assert(lr.rest == "123");
					assert(lr.value == 0);
				}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	debug(ctpg) unittest{
		enum dg = {
			return true;
		};
		debug(ctpg_ct) static assert(dg());
		dg();
	}

	debug(ctpg) unittest{
		enum dg = {
			return true;
		};
		debug(ctpg_ct) static assert(dg());
		dg();
	}
}

mixin template ctpg(string Src){
	mixin(parse!defs(Src));
}

template getSource(string Src){
	enum getSource = getResult!defs(Src).value;
}

auto getResult(alias Func)(string asrc){
	memo_t lmemo;
	return Func(stringp(asrc), lmemo);
}

auto parse(alias Func)(string asrc){
	auto res = getResult!Func(asrc);
	if(res.match){
		return res.value;
	}else{
		if(__ctfe){
			assert(false, to!string(res.error.line) ~ q{: } ~ to!string(res.error.column) ~ q{: error } ~ res.error.need ~ q{ is needed});
		}else{
			throw new Exception(to!string(res.error.line) ~ q{: } ~ to!string(res.error.column) ~ q{: error } ~ res.error.need ~ q{ is needed});
		}
	}
}

bool isMatch(alias Func)(string asrc){
	return getResult!Func(asrc).match;
}

/* ctpg */ version(all){
	/* defs */ version(all){
		Result!string defs(stringp ainput, ref memo_t amemo){
			return memoizeInput!(combinateString!(
				memoizeInput!(combinateSequence!(
					memoizeInput!parseSpaces,
					memoizeInput!(combinateMore1!(
						memoizeInput!def,
						memoizeInput!parseSpaces
					)),
					memoizeInput!parseSpaces,
					memoizeInput!parseEOF
				))
			))(ainput, amemo);
		}

		debug(ctpg) unittest{
			enum ldg = {
				string lsrc = q{
					bool hoge = ^"hello" $ >> {return false;};
					Tuple!piyo hoge2 = hoge* >> {return tuple("foo");};
				};
				auto lr = getResult!defs(lsrc);
				assert(lr.match);
				assert(lr.rest == "");
				assert(
					lr.value ==
					"Result!(bool) hoge(stringp ainput, memo_t amemo){"
						"return memoizeInput!(combinateConvert!("
							"memoizeInput!(combinateSequence!("
								"memoizeInput!(combinateNone!("
									"memoizeInput!(parseString!\"hello\")"
								")),"
								"memoizeInput!(parseEOF)"
							")),"
							"function(){"
								"return false;"
							"}"
						"))(ainput, amemo);"
					"}"
					"Result!(Tuple!piyo) hoge2(stringp ainput, memo_t amemo){"
						"return memoizeInput!(combinateConvert!("
							"memoizeInput!(combinateMore0!("
								"memoizeInput!(hoge)"
							")),"
							"function(){"
								"return tuple(\"foo\");"
							"}"
						"))(ainput, amemo);"
					"}"
				);
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		};
	}

	/* defs */ version(all){
		Result!string def(stringp ainput, memo_t amemo){
			return memoizeInput!(combinateConvert!(
				memoizeInput!(combinateSequence!(
					memoizeInput!typeName,
					memoizeInput!parseSpaces,
					memoizeInput!id,
					memoizeInput!parseSpaces,
					memoizeInput!(combinateNone!(
						memoizeInput!(parseString!"=")
					)),
					memoizeInput!parseSpaces,
					memoizeInput!convExp,
					memoizeInput!parseSpaces,
					memoizeInput!(combinateNone!(
						memoizeInput!(parseString!";")
					))
				)),
				function(string type, string name, string convExp){
					return "Result!("~type~") "~name~"(stringp ainput, memo_t amemo){"
						"return "~convExp~"(ainput, amemo);"
					"}";
				}
			))(ainput, amemo);
		}

		debug(ctpg) unittest{
			enum ldg = {
				auto lr = getResult!def(q{bool hoge = ^"hello" $ >> {return false;};});
				assert(lr.match);
				assert(lr.rest == "");
				assert(
					lr.value ==
					"Result!(bool) hoge(stringp ainput, memo_t amemo){"
						"return memoizeInput!(combinateConvert!("
							"memoizeInput!(combinateSequence!("
								"memoizeInput!(combinateNone!("
									"memoizeInput!(parseString!\"hello\")"
								")),"
								"memoizeInput!(parseEOF)"
							")),"
							"function(){"
								"return false;"
							"}"
						"))(ainput, amemo);"
					"}"
				);
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		};
	}

	/* convExp */ version(all){
		Result!string convExp(stringp ainput, memo_t amemo){
			return memoizeInput!(combinateConvert!(
				memoizeInput!(combinateSequence!(
					memoizeInput!choiceExp,
					memoizeInput!(combinateMore0!(
						memoizeInput!(combinateSequence!(
							memoizeInput!parseSpaces,
							memoizeInput!(combinateNone!(
								parseString!">>"
							)),
							memoizeInput!parseSpaces,
							memoizeInput!(combinateChoice!(
								memoizeInput!func,
								memoizeInput!typeName
							))
						))
					))
				)),
				function(string achoiceExp, string[] afuncs){
					string lres = achoiceExp;
					foreach(lfunc; afuncs){
						lres = "memoizeInput!(combinateConvert!(" ~ lres ~ "," ~ lfunc ~ "))";
					}
					return lres;
				}
			))(ainput, amemo);
		}

		debug(ctpg) unittest{
			enum ldg = {
				{
					auto lr = getResult!convExp(q{^"hello" $ >> {return false;}});
					assert(lr.match);
					assert(lr.rest == "");
					assert(
						lr.value ==
						"memoizeInput!(combinateConvert!("
							"memoizeInput!(combinateSequence!("
								"memoizeInput!(combinateNone!("
									"memoizeInput!(parseString!\"hello\")"
								")),"
								"memoizeInput!(parseEOF)"
							")),"
							"function(){"
								"return false;"
							"}"
						"))"
					);
				}
				{
					auto lr = getResult!convExp(q{"hello" >> flat >> to!int});
					assert(lr.match);
					assert(lr.rest == "");
					assert(
						lr.value ==
						"memoizeInput!(combinateConvert!("
							"memoizeInput!(combinateConvert!("
								"memoizeInput!(parseString!\"hello\"),"
								"flat"
							")),"
							"to!int"
						"))"
					);
				}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* choiceExp */ version(all){
		Result!string choiceExp(stringp ainput, memo_t amemo){
			return memoizeInput!(combinateConvert!(
				memoizeInput!(combinateSequence!(
					memoizeInput!seqExp,
					memoizeInput!(combinateMore0!(
						memoizeInput!(combinateSequence!(
							memoizeInput!parseSpaces,
							memoizeInput!(combinateNone!(
								memoizeInput!(parseString!"/")
							)),
							memoizeInput!parseSpaces,
							memoizeInput!seqExp
						))
					))
				)),
				function(string aseqExp, string[] aseqExps){
					if(aseqExps.length){
						return "memoizeInput!(combinateChoice!("~aseqExp~","~aseqExps.mkString(",")~"))";
					}else{
						return aseqExp;
					}
				}
			))(ainput, amemo);
		}

		debug(ctpg) unittest{
			enum ldg = {
				{
					auto lr = getResult!choiceExp(`^$* / (&(!"a"))?`);
					assert(lr.match);
					assert(lr.rest == "");
					assert(
						lr.value ==
						"memoizeInput!(combinateChoice!("
							"memoizeInput!(combinateMore0!("
								"memoizeInput!(combinateNone!("
									"memoizeInput!(parseEOF)"
								"))"
							")),"
							"memoizeInput!(combinateOption!("
								"memoizeInput!(combinateAnd!("
									"memoizeInput!(combinateNot!("
										"memoizeInput!(parseString!\"a\")"
									"))"
								"))"
							"))"
						"))"
					);
				}
				{
					auto lr = getResult!choiceExp(`^"hello" $`);
					assert(lr.match);
					assert(lr.rest == "");
					assert(
						lr.value ==
						"memoizeInput!(combinateSequence!("
							"memoizeInput!(combinateNone!("
								"memoizeInput!(parseString!\"hello\")"
							")),"
							"memoizeInput!(parseEOF)"
						"))"
					);
				}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* seqExp */ version(all){
		Result!string seqExp(stringp ainput, memo_t amemo){
			return memoizeInput!(combinateConvert!(
				memoizeInput!(combinateMore1!(
					memoizeInput!optionExp,
					memoizeInput!parseSpaces
				)),
				function(string[] aoptionExps){
					if(aoptionExps.length > 1){
						return "memoizeInput!(combinateSequence!("~aoptionExps.mkString(",")~"))";
					}else{
						return aoptionExps[0];
					}
				}
			))(ainput, amemo);
		}

		debug(ctpg) unittest{
			enum ldg = {
				{
					auto lr = getResult!seqExp("^$* (&(!$))?");
					assert(lr.match);
					assert(lr.rest == "");
					assert(
						lr.value ==
						"memoizeInput!(combinateSequence!("
							"memoizeInput!(combinateMore0!("
								"memoizeInput!(combinateNone!("
									"memoizeInput!(parseEOF)"
								"))"
							")),"
							"memoizeInput!(combinateOption!("
								"memoizeInput!(combinateAnd!("
									"memoizeInput!(combinateNot!("
										"memoizeInput!(parseEOF)"
									"))"
								"))"
							"))"
						"))"
					);
				}
				{
					enum lr = getResult!seqExp("^\"hello\" $");
					assert(lr.match);
					assert(lr.rest == "");
					assert(
						lr.value ==
						"memoizeInput!(combinateSequence!("
							"memoizeInput!(combinateNone!("
								"memoizeInput!(parseString!\"hello\")"
							")),"
							"memoizeInput!(parseEOF)"
						"))"
					);
				}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* optionExp */ version(all){
		Result!string optionExp(stringp ainput, memo_t amemo){
			return memoizeInput!(combinateConvert!(
				memoizeInput!(combinateSequence!(
					memoizeInput!postExp,
					memoizeInput!parseSpaces,
					memoizeInput!(combinateOption!(
						memoizeInput!(combinateNone!(
							memoizeInput!(parseString!"?")
						))
					))
				)),
				function(string aconvExp, Option!None aop){
					if(aop.some){
						return "memoizeInput!(combinateOption!("~aconvExp~"))";
					}else{
						return aconvExp;
					}
				}
			))(ainput, amemo);
		}

		debug(ctpg) unittest{
			enum ldg = {
				auto lr = getResult!optionExp("(&(!\"hello\"))?");
				assert(lr.match);
				assert(lr.rest == "");
				assert(
					lr.value ==
					"memoizeInput!(combinateOption!("
						"memoizeInput!(combinateAnd!("
							"memoizeInput!(combinateNot!("
								"memoizeInput!(parseString!\"hello\")"
							"))"
						"))"
					"))"
				);
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* postExp */ version(all){
		Result!string postExp(stringp ainput, memo_t amemo){
			return memoizeInput!(combinateConvert!(
				memoizeInput!(combinateSequence!(
					memoizeInput!preExp,
					memoizeInput!(combinateOption!(
						memoizeInput!(combinateSequence!(
							memoizeInput!(combinateChoice!(
								memoizeInput!(parseString!"+"),
								memoizeInput!(parseString!"*")
							)),
							memoizeInput!(combinateOption!(
								memoizeInput!(combinateSequence!(
									memoizeInput!(combinateNone!(
										memoizeInput!(parseString!"<")
									)),
									memoizeInput!choiceExp,
									memoizeInput!(combinateNone!(
										memoizeInput!(parseString!">")
									))
								))
							))
						))
					))
				)),
				function(string apreExp, Option!(Tuple!(string, Option!string)) aop){
					final switch(aop.value[0]){
						case "+":
							if(aop.value[1].some){
								return "memoizeInput!(combinateMore1!("~apreExp~","~aop.value[1].value~"))";
							}else{
								return "memoizeInput!(combinateMore1!("~apreExp~"))";
							}
						case "*":
							if(aop.value[1].some){
								return "memoizeInput!(combinateMore0!("~apreExp~","~aop.value[1].value~"))";
							}else{
								return "memoizeInput!(combinateMore0!("~apreExp~"))";
							}
						case "":
							return apreExp;
					}
				}
			))(ainput, amemo);
		}

		debug(ctpg) unittest{
			enum ldg = {
				auto lr = getResult!postExp("^$*");
				assert(lr.match);
				assert(lr.rest == "");
				assert(
					lr.value ==
					"memoizeInput!(combinateMore0!("
						"memoizeInput!(combinateNone!("
							"memoizeInput!(parseEOF)"
						"))"
					"))"
				);
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* preExp */ version(all){
		Result!string preExp(stringp ainput, memo_t amemo){
			return memoizeInput!(combinateConvert!(
				memoizeInput!(combinateSequence!(
					memoizeInput!(combinateOption!(
						memoizeInput!(combinateChoice!(
							memoizeInput!(parseString!"&"),
							memoizeInput!(parseString!"^"),
							memoizeInput!(parseString!"!")
						))
					)),
					memoizeInput!primaryExp
				)),
				function(Option!string aop, string aprimaryExp){
					final switch(aop.value){
						case "&":{
							return "memoizeInput!(combinateAnd!(" ~ aprimaryExp ~ "))";
						}
						case "!":{
							return "memoizeInput!(combinateNot!(" ~ aprimaryExp ~ "))";
						}
						case "^":{
							return "memoizeInput!(combinateNone!(" ~ aprimaryExp ~ "))";
						}
						case "":{
							return aprimaryExp;
						}
					}
				}
			))(ainput, amemo);
		}

		debug(ctpg) unittest{
			enum ldg = {
				auto lr = getResult!preExp("^$");
				assert(lr.match);
				assert(lr.rest == "");
				assert(
					lr.value ==
					"memoizeInput!(combinateNone!("
						"memoizeInput!(parseEOF)"
					"))"
				);
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* primaryExp */ version(all){
		Result!string primaryExp(stringp ainput, memo_t amemo){
			return memoizeInput!(combinateChoice!(
				memoizeInput!literal,
				memoizeInput!nonterminal,
				memoizeInput!(combinateSequence!(
					memoizeInput!(combinateNone!(
						memoizeInput!(parseString!"(")
					)),
					memoizeInput!convExp,
					memoizeInput!(combinateNone!(
						memoizeInput!(parseString!")")
					))
				))
			))(ainput, amemo);
		}

		debug(ctpg) unittest{
			enum ldg = {
				{
					auto lr = getResult!primaryExp("(&(!$)?)");
					assert(lr.match);
					assert(lr.rest == "");
					assert(
						lr.value ==
						"memoizeInput!(combinateOption!("
							"memoizeInput!(combinateAnd!("
								"memoizeInput!(combinateNot!("
									"memoizeInput!(parseEOF)"
								"))"
							"))"
						"))"
					);
				}
				{
					auto lr = getResult!primaryExp("int");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "memoizeInput!(int)");
				}
				{
					auto lr = getResult!primaryExp("select!(true)(\"true\", \"false\")");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "memoizeInput!(select!(true)(\"true\", \"false\"))");
				}
				{
					auto lr = getResult!primaryExp("###このコメントは表示されません###");
					assert(!lr.match);
				}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* literal */ version(all){
		Result!string literal(stringp ainput, memo_t amemo){
			return memoizeInput!(combinateChoice!(
				memoizeInput!rangeLit,
				memoizeInput!stringLit,
				memoizeInput!eofLit,
				memoizeInput!usefulLit
			))(ainput, amemo);
		}

		debug(ctpg) unittest{
			enum ldg = {
				{
					auto lr = getResult!literal("\"hello\nworld\"");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "memoizeInput!(parseString!\"hello\nworld\")");
				}
				{
					auto lr = getResult!literal("[a-z]");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "memoizeInput!(parseCharRange!('a','z'))");
				}
				{
					auto lr = getResult!usefulLit("space_p");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "memoizeInput!(parseSpace)");
				}
				{
					auto lr = getResult!usefulLit("es");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "memoizeInput!(parseEscapeSequence)");
				}
				{
					auto lr = getResult!usefulLit("a");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "memoizeInput!(parseAnyChar)");
				}
				{
					auto lr = getResult!usefulLit("s");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "memoizeInput!(parseSpaces)");
				}
				{
					auto lr = getResult!literal("$");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "memoizeInput!(parseEOF)");
				}
				{
					auto lr = getResult!literal("ident_p");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "memoizeInput!(parseIdent)");
				}
				{
					auto lr = getResult!literal("strLit_p");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "memoizeInput!(parseStringLiteral)");
				}
				{
					auto lr = getResult!literal("intLit_p");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "memoizeInput!(parseIntLiteral)");
				}
				{
					auto lr = getResult!literal("表が怖い噂のソフト");
					assert(!lr.match);
				}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* stringLit */ version(all){
		Result!string stringLit(stringp ainput, memo_t amemo){
			return memoizeInput!(combinateConvert!(
				memoizeInput!(combinateSequence!(
					memoizeInput!(combinateNone!(
						memoizeInput!(parseString!"\"")
					)),
					memoizeInput!(combinateMore0!(
						memoizeInput!(combinateSequence!(
							memoizeInput!(combinateNot!(
								memoizeInput!(parseString!"\"")
							)),
							memoizeInput!(combinateChoice!(
								memoizeInput!parseEscapeSequence,
								memoizeInput!parseAnyChar
							))
						))
					)),
					memoizeInput!(combinateNone!(
						memoizeInput!(parseString!"\"")
					))
				)),
				function(string[] astrs){
					return "memoizeInput!(parseString!\""~astrs.mkString()~"\")";
				}
			))(ainput, amemo);
		}

		debug(ctpg) unittest{
			enum ldg = {
				{
					auto lr = getResult!stringLit("\"hello\nworld\" ");
					assert(lr.match);
					assert(lr.rest == " ");
					assert(lr.value == "memoizeInput!(parseString!\"hello\nworld\")");
				}
				{
					auto lr = getResult!stringLit("aa\"");
					assert(!lr.match);
				}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* rangeLit */ version(all){
		Result!string rangeLit(stringp ainput, memo_t amemo){
			return memoizeInput!(combinateConvert!(
				memoizeInput!(combinateSequence!(
					memoizeInput!(combinateNone!(
						memoizeInput!(parseString!"[")
					)),
					memoizeInput!(combinateMore1!(
						memoizeInput!(combinateSequence!(
							memoizeInput!(combinateNot!(
								memoizeInput!(parseString!"]")
							)),
							memoizeInput!(combinateChoice!(
								memoizeInput!charRange,
								memoizeInput!oneChar
							))
						))
					)),
					memoizeInput!(combinateNone!(
						memoizeInput!(parseString!"]")
					))
				)),
				function(string[] astrs){
					if(astrs.length == 1){
						return astrs[0];
					}else{
						return "memoizeInput!(combinateChoice!("~astrs.mkString(",")~"))";
					}
				}
			))(ainput, amemo);
		}

		Result!string charRange(stringp ainput, memo_t amemo){
			return memoizeInput!(combinateConvert!(
				memoizeInput!(combinateSequence!(
					memoizeInput!(combinateChoice!(
						memoizeInput!parseEscapeSequence,
						memoizeInput!parseAnyChar
					)),
					memoizeInput!(combinateNone!(
						memoizeInput!(parseString!"-")
					)),
					memoizeInput!(combinateChoice!(
						memoizeInput!parseEscapeSequence,
						memoizeInput!parseAnyChar
					)),
				)),
				function(string alow, string ahigh){
					return "memoizeInput!(parseCharRange!('"~alow~"','"~ahigh~"'))";
				}
			))(ainput, amemo);
		}

		Result!string oneChar(stringp ainput, memo_t amemo){
			return memoizeInput!(combinateConvert!(
				memoizeInput!(combinateChoice!(
					memoizeInput!parseEscapeSequence,
					memoizeInput!parseAnyChar
				)),
				function(string ac){
					return "memoizeInput!(parseString!\""~ac~"\")";
				}
			))(ainput, amemo);
		}

		debug(ctpg) unittest{
			enum ldg = {
				{
					auto lr = getResult!rangeLit("[a-z]");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "memoizeInput!(parseCharRange!('a','z'))");
				}
				{
					auto lr = getResult!rangeLit("[a-zA-Z_]");
					assert(lr.match);
					assert(lr.rest == "");
					assert(
						lr.value ==
						"memoizeInput!(combinateChoice!("
							"memoizeInput!(parseCharRange!('a','z')),"
							"memoizeInput!(parseCharRange!('A','Z')),"
							"memoizeInput!(parseString!\"_\")"
						"))"
					);
				}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* eofLit */ version(all){
		Result!string eofLit(stringp ainput, memo_t amemo){
			return memoizeInput!(combinateConvert!(
				memoizeInput!(combinateNone!(
					memoizeInput!(parseString!"$")
				)),
				function{
					return "memoizeInput!(parseEOF)";
				}
			))(ainput, amemo);
		}

		debug(ctpg) unittest{
			enum ldg = {
				{
					auto lr = getResult!eofLit("$");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "memoizeInput!(parseEOF)");
				}
				{
					auto lr = getResult!eofLit("#");
					assert(!lr.match);
				}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* usefulLit */ version(all){
		Result!string usefulLit(stringp ainput, memo_t amemo){
			return memoizeInput!(combinateConvert!(
				memoizeInput!(combinateChoice!(
					memoizeInput!(combinateSequence!(
						memoizeInput!(parseString!"ident_p"),
						memoizeInput!(combinateNot!parseIdentChar)
					)),
					memoizeInput!(combinateSequence!(
						memoizeInput!(parseString!"strLit_p"),
						memoizeInput!(combinateNot!parseIdentChar)
					)),
					memoizeInput!(combinateSequence!(
						memoizeInput!(parseString!"intLit_p"),
						memoizeInput!(combinateNot!parseIdentChar)
					)),
					memoizeInput!(combinateSequence!(
						memoizeInput!(parseString!"space_p"),
						memoizeInput!(combinateNot!parseIdentChar)
					)),
					memoizeInput!(combinateSequence!(
						memoizeInput!(parseString!"es"),
						memoizeInput!(combinateNot!parseIdentChar)
					)),
					memoizeInput!(combinateSequence!(
						memoizeInput!(parseString!"a"),
						memoizeInput!(combinateNot!parseIdentChar)
					)),
					memoizeInput!(combinateSequence!(
						memoizeInput!(parseString!"s"),
						memoizeInput!(combinateNot!parseIdentChar)
					))
				)),
				function(string astr){
					final switch(astr){
						case "ident_p":{
							return "memoizeInput!(parseIdent)";
						}
						case "strLit_p":{
							return "memoizeInput!(parseStringLiteral)";
						}
						case "intLit_p":{
							return "memoizeInput!(parseIntLiteral)";
						}
						case "space_p":{
							return "memoizeInput!(parseSpace)";
						}
						case "es":{
							return "memoizeInput!(parseEscapeSequence)";
						}
						case "a":{
							return "memoizeInput!(parseAnyChar)";
						}
						case "s":{
							return "memoizeInput!(parseSpaces)";
						}
					}
				}
			))(ainput, amemo);
		}

		debug(ctpg) unittest{
			enum ldg = {
				{
					auto lr = getResult!usefulLit("space_p");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "memoizeInput!(parseSpace)");
				}
				{
					auto lr = getResult!usefulLit("es");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "memoizeInput!(parseEscapeSequence)");
				}
				{
					auto lr = getResult!usefulLit("a");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "memoizeInput!(parseAnyChar)");
				}
				{
					auto lr = getResult!usefulLit("s");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "memoizeInput!(parseSpaces)");
				}
				{
					auto lr = getResult!usefulLit("ident_p");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "memoizeInput!(parseIdent)");
				}
				{
					auto lr = getResult!usefulLit("strLit_p");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "memoizeInput!(parseStringLiteral)");
				}
				{
					auto lr = getResult!usefulLit("intLit_p");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "memoizeInput!(parseIntLiteral)");
				}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* id */ version(all){
		Result!string id(stringp ainput, memo_t amemo){
			return memoizeInput!(combinateString!(
				memoizeInput!(combinateSequence!(
					memoizeInput!(combinateChoice!(
						memoizeInput!(parseCharRange!('A','Z')),
						memoizeInput!(parseCharRange!('a','z')),
						memoizeInput!(parseString!"_")
					)),
					memoizeInput!(combinateMore0!(
						memoizeInput!(combinateChoice!(
							memoizeInput!(parseCharRange!('0','9')),
							memoizeInput!(parseCharRange!('A','Z')),
							memoizeInput!(parseCharRange!('a','z')),
							memoizeInput!(parseString!"_"),
							memoizeInput!(parseString!","),
							memoizeInput!(parseString!"!"),
							memoizeInput!(arch!("(", ")"))
						))
					))
				))
			))(ainput, amemo);
		}

		debug(ctpg) unittest{
			enum ldg = {
				{
					auto lr = getResult!id("int");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "int");
				}
				{
					auto lr = getResult!id("select!(true)(\"true\", \"false\")");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "select!(true)(\"true\", \"false\")");
				}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* nonterminal */ version(all){
		Result!string nonterminal(stringp ainput, memo_t amemo){
			return memoizeInput!(combinateConvert!(
				id,
				function(string aid){
					return "memoizeInput!(" ~ aid ~ ")";
				}
			))(ainput, amemo);
		}

		debug(ctpg) unittest{
			enum ldg = {
				{
					auto lr = getResult!nonterminal("int");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "memoizeInput!(int)");
				}
				{
					auto lr = getResult!nonterminal("select!(true)(\"true\", \"false\")");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "memoizeInput!(select!(true)(\"true\", \"false\"))");
				}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* typeName */ version(all){
		Result!string typeName(stringp ainput, memo_t amemo){
			return memoizeInput!(combinateString!(
				memoizeInput!(combinateSequence!(
					memoizeInput!(combinateChoice!(
						memoizeInput!(parseCharRange!('A','Z')),
						memoizeInput!(parseCharRange!('a','z')),
						memoizeInput!(parseString!"_")
					)),
					memoizeInput!parseSpaces,
					memoizeInput!(combinateMore0!(
						memoizeInput!(combinateChoice!(
							memoizeInput!(parseCharRange!('0','9')),
							memoizeInput!(parseCharRange!('A','Z')),
							memoizeInput!(parseCharRange!('a','z')),
							memoizeInput!(parseString!"_"),
							memoizeInput!(parseString!","),
							memoizeInput!(parseString!"!"),
							memoizeInput!(arch!("(", ")")),
							memoizeInput!(arch!("[", "]"))
						))
					))
				))
			))(ainput, amemo);
		}

		debug(ctpg) unittest{
			enum ldg = {
				{
					auto lr = getResult!typeName("int");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "int");
				}
				{
					auto lr = getResult!typeName("Tuple!(string, int)");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "Tuple!(string, int)");
				}
				{
					auto lr = getResult!typeName("int[]");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "int[]");
				}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* func */ version(all){
		Result!string func(stringp ainput, memo_t amemo){
			return memoizeInput!(combinateConvert!(
				memoizeInput!(combinateSequence!(
					memoizeInput!(combinateOption!(
						memoizeInput!(combinateSequence!(
							memoizeInput!(arch!("(", ")")),
							memoizeInput!parseSpaces
						))
					)),
					memoizeInput!(arch!("{", "}"))
				)),
				function(Option!string aarch, string abrace){
					if(aarch.some){
						return "function" ~ aarch.value ~ abrace;
					}else{
						return "function()" ~ abrace;
					}
				}
			))(ainput, amemo);
		}

		debug(ctpg) unittest{
			enum ldg = {
				auto lr = getResult!func(
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
				assert(lr.match);
				assert(lr.rest == "");
				assert(
					lr.value ==
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
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* arch */ version(all){
		Result!string arch(string Open, string Close)(stringp ainput, memo_t amemo){
			return memoizeInput!(combinateConvert!(
				memoizeInput!(combinateSequence!(
					memoizeInput!(combinateNone!(
						memoizeInput!(parseString!Open)
					)),
					memoizeInput!(combinateMore0!(
						memoizeInput!(combinateChoice!(
							memoizeInput!arch,
							memoizeInput!(combinateSequence!(
								memoizeInput!(combinateNot!(
									memoizeInput!(parseString!Close)
								)),
								memoizeInput!parseAnyChar
							))
						))
					)),
					memoizeInput!(combinateNone!(
						memoizeInput!(parseString!Close)
					))
				)),
				function(string[] strs){
					return Open~strs.mkString()~Close;
				}
			))(ainput, amemo);
		}

		debug(ctpg) unittest{
			enum ldg = {
				{
					auto lr = getResult!(arch!("(", ")"))("(a(i(u)e)o())");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "(a(i(u)e)o())");
				}
				{
					auto lr = getResult!(arch!("[", "]"))("[a[i[u]e]o[]]");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "[a[i[u]e]o[]]");
					return true;
				}
				{
					auto lr = getResult!(arch!("{", "}"))("{a{i{u}e}o{}}");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "{a{i{u}e}o{}}");
				}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}
}


string flat(Arg)(Arg aarg){
	string lres;
	static if(isTuple!Arg || isArray!Arg){
		foreach(larg; aarg){
			lres ~= flat(larg);
		}
	}else{
		lres = to!string(aarg);
	}
	return lres;
}

debug(ctpg) void main(){}


private:

stringp s(string str)pure @safe nothrow{
	return stringp(str);
}

string mkString(string[] strs, string sep = "")pure @safe nothrow{
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

debug(ctpg) unittest{
	enum dg = {
		{
			auto r = flat(tuple(1, "hello", tuple(2, "world")));
			assert(r == "1hello2world");
		}
		{
			auto r = flat(tuple([0, 1, 2], "hello", tuple([3, 4, 5], ["wor", "ld!!"]), ["!", "!"]));
			assert(r == "012hello345world!!!!");
		}
		{
			auto r = flat(tuple('表', 'が', '怖', 'い', '噂', 'の', 'ソ', 'フ', 'ト'));
			assert(r == "表が怖い噂のソフト");
		}
		return true;
	};
	debug(ctpg_ct) static assert(dg());
	dg();
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

template flatTuple(arg){
	static if(isTuple!arg){
		alias arg.Types flatTuple;
	}else{
		alias arg flatTuple;
	}
}

template CombinateSequenceImplType(parsers...){
	alias Result!(Tuple!(staticMap!(flatTuple, staticMap!(ParserType, parsers)))) CombinateSequenceImplType;
}

template UnTuple(E){
	static if(staticLength!(ResultType!E.Types) == 1){
		alias Result!(ResultType!E.Types[0]) UnTuple;
	}else{
		alias E UnTuple;
	}
}

UnTuple!R unTuple(R)(R r){
	static if(staticLength!(ResultType!R.Types) == 1){
		return Result!(ResultType!R.Types[0])(r.match, r.value[0], r.rest, r.error);
	}else{
		return r;
	}
}

template CommonParserType(parsers...){
	alias CommonType!(staticMap!(ParserType, parsers)) CommonParserType;
}

dchar decode(string str, ref size_t i)@safe pure nothrow{
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

debug(ctpg) public:

mixin ctpg!q{
	int root = addExp $;

	int addExp = mulExp (("+" / "-") addExp)? >> (int lhs, Option!(Tuple!(string, int)) rhs){
		if(rhs.some){
			final switch(rhs.value[0]){
				case "+":{
					return lhs + rhs.value[1];
				}
				case "-":{
					return lhs - rhs.value[1];
				}
			}
		}else{
			return lhs;
		}
	};

	int mulExp = primary (("*" / "/") mulExp)? >> (int lhs, Option!(Tuple!(string, int)) rhs){
		if(rhs.some){
			final switch(rhs.value[0]){
				case "*":{
					return lhs * rhs.value[1];
				}
				case "/":{
					return lhs / rhs.value[1];
				}
			}
		}else{
			return lhs;
		}
	};

	int primary = ^"(" addExp ^")" / intLit_p;

	None recursive = A $;

	None A = ^"a" ^A ^"a" / ^"a";
};

unittest{
	{
		assert(parse!root("5*8+3*20") == 100);
		assert(parse!root("5*(8+3)*20") == 1100);
		try{
			parse!root("5*(8+3)20");
		}catch(Exception e){
			assert(e.msg == "1: 8: error EOF is needed");
		}
	}
	{
		assert( isMatch!recursive("a"));
		assert( isMatch!recursive("aaa"));
		assert(!isMatch!recursive("aaaaa"));
		assert( isMatch!recursive("aaaaaaa"));
		assert(!isMatch!recursive("aaaaaaaaa"));
		assert(!isMatch!recursive("aaaaaaaaaaa"));
		assert(!isMatch!recursive("aaaaaaaaaaaaa"));
		assert( isMatch!recursive("aaaaaaaaaaaaaaa"));
	}
}
