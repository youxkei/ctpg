// Written in the D programming language.

/*          Copyright youkei 2010 - 2012.
 * Distributed under the Boost Software License, Version 1.0.
 *    (See accompanying file LICENSE_1_0.txt or copy at
 *          http://www.boost.org/LICENSE_1_0.txt)
 */

module youkei.ctpg;

import std.algorithm;
import std.array;
import std.conv;
import std.range;
import std.traits;
import std.typecons;
import std.typetuple;
import std.utf;
import std.functional;

alias Tuple!() None;
alias void*[size_t][size_t][string] memo_t;

version = memoize;

version(memoize){
	ReturnType!tfunc memoizeInput(alias tfunc)(stringp ainput, ref memo_t amemo){
		auto lmemo0 = tfunc.mangleof in amemo;
		if(lmemo0){
			auto lmemo1 = ainput.line in *lmemo0;
			if(lmemo1){
				auto lmemo2 = ainput.column in *lmemo1;
				if(lmemo2){
					void* lp = *lmemo2;
					return *(cast(ReturnType!Func*)lp);
				}
			}
		}
		auto lres = tfunc(ainput, amemo);
		amemo[tfunc.mangleof][ainput.line][ainput.column] = [lres].ptr;
		return lres;
	}
}else{
	template memoizeInput(alias Func){
		alias Func memoizeInput;
	}
}

struct PositionalRange(R){
	static assert(isForwardRange!R && isSomeChar!(ElementType!R));

	public{
		R range;
		size_t line = 1;
		size_t column = 1;

		typeof(this) save(){
			return PositionalRange!R(prange.save, pline, pcolumn);
		}
	}

	private{
		alias range prange;
		alias line pline;
		alias column pcolumn;
	}
}

template isPositionalRange(R){
	static if(is(R Unused == PositionalRange!T, T)){
		enum isPositionalRange = true;
	}else{
		enum isPositionalRange = false;
	}
}

version(none) struct stringp{
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
		dchar decode(){
			return .decode(this);
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

version(none) debug(ctpg) unittest{
	enum ldg = {
		auto ls1 = stringp("hoge");
		assert(ls1 == "hoge");
		assert(ls1.line == 1);
		assert(ls1.column == 1);
		auto ls2 = s1[1..s1.length];
		assert(ls2 == "oge");
		assert(ls2.line == 1);
		assert(ls2.column == 2);
		auto ls3 = s2[s2.length..s2.length];
		assert(ls3 == "");
		assert(ls3.line == 1);
		assert(ls3.column == 5);
		auto ls4 = stringp("メロスは激怒した。");
		auto ls5 = s4[3..s4.length];
		assert(ls5 == "ロスは激怒した。");
		assert(ls5.line == 1);
		assert(ls5.column == 4);//TODO: column should be 2
		auto ls6 = stringp("hoge\npiyo")[5..9];
		assert(ls6 == "piyo");
		assert(ls6.line == 2);
		assert(ls6.column == 1);
		return true;
	};
	debug(ctpg_ct) static assert(dg());
	dg();
}

struct Result(Range, T){
	bool match;
	T value;
	PositionalRange!Range rest;
	Error error;

	pure @safe nothrow
	void opAssign(F)(Result!(Range, F) arhs)if(isAssignable!(T, F)){
		match = arhs.match;
		value = arhs.value;
		rest = arhs.rest;
		error = arhs.error;
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
		version(none) UnTuple!(CombinateSequenceImplType!Parsers) combinateSequence(Parsers...)(stringp ainput, ref memo_t amemo){
			static assert(staticLength!Parsers > 0);
			return unTuple(combinateSequenceImpl!Parsers(ainput, amemo));
		}

		template combinateSequence(tparsers...){
			static assert(tparsers.length > 0);
			UnTuple!(Range, CombinateSequenceImplType!(Range, tparsers)) apply(Range)(PositionalRange!Range ainput, ref memo_t amemo){
				return unTuple!Range(combinateSequenceImpl!(Range, tparsers)(ainput, amemo));
			}
		}

		version(none) private CombinateSequenceImplType!Parsers combinateSequenceImpl(Parsers...)(stringp ainput, ref memo_t amemo){
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

		private CombinateSequenceImplType!(Range, tparsers) combinateSequenceImpl(Range, tparsers...)(PositionalRange!Range ainput, ref memo_t amemo){
			typeof(return) lresult;
			static if(tparsers.length == 1){
				auto lr = tparsers[0].apply(ainput, amemo);
				if(lr.match){
					lresult.match = true;
					static if(isTuple!(ParserType!(Range, tparsers[0]))){
						lresult.value = lr.value;
					}else{
						lresult.value = tuple(lr.value);
					}
					lresult.rest = lr.rest;
				}else{
					lresult.error = lr.error;
				}
			}else{
				auto lr1 = tparsers[0].apply(ainput, amemo);
				if(lr1.match){
					auto lr2 = combinateSequenceImpl!(Range, tparsers[1..$])(lr1.rest, amemo);
					if(lr2.match){
						lresult.match = true;
						static if(isTuple!(ParserType!(Range, tparsers[0]))){
							lresult.value = tuple(lr1.value.field, lr2.value.field);
						}else{
							lresult.value = tuple(lr1.value, lr2.value.field);
						}
						lresult.rest = lr2.rest;
					}else{
						lresult.error = lr2.error;
					}
				}else{
					lresult.error = lr1.error;
				}
			}
			return lresult;
		}

		debug(ctpg) unittest{
			enum ldg = {
				version(all){{
					version(all){{
						auto lresult = getResult!(combinateSequence!(
							parseString!("hello"),
							parseString!("world")
						))("helloworld");
						assert(lresult.match);
						assert(lresult.rest.range == "");
						assert(lresult.value[0] == "hello");
						assert(lresult.value[1] == "world");
					}}
					version(all){{
						auto lresult = getResult!(combinateSequence!(
							parseString!("hello"),
							parseString!("world")
						))("helloworld"w);
						assert(lresult.match);
						assert(lresult.rest.range == ""w);
						assert(lresult.value[0] == "hello");
						assert(lresult.value[1] == "world");
					}}
					version(all){{
						auto lresult = getResult!(combinateSequence!(
							parseString!("hello"),
							parseString!("world")
						))("helloworld"d);
						assert(lresult.match);
						assert(lresult.rest.range == ""d);
						assert(lresult.value[0] == "hello");
						assert(lresult.value[1] == "world");
					}}
					version(all){{
						auto lresult = getResult!(combinateSequence!(
							parseString!("hello"),
							parseString!("world")
						))(TestRange!"helloworld"());
						assert(lresult.match);
						assert(lresult.rest.range.source == "");
						assert(lresult.value[0] == "hello");
						assert(lresult.value[1] == "world");
					}}
					version(all){{
						auto lresult = getResult!(combinateSequence!(
							parseString!("hello"),
							parseString!("world")
						))(TestRange!"helloworld"w());
						assert(lresult.match);
						assert(lresult.rest.range.source == ""w);
						assert(lresult.value[0] == "hello");
						assert(lresult.value[1] == "world");
					}}
					version(all){{
						auto lresult = getResult!(combinateSequence!(
							parseString!("hello"),
							parseString!("world")
						))(TestRange!"helloworld"d());
						assert(lresult.match);
						assert(lresult.rest.range.source == ""d);
						assert(lresult.value[0] == "hello");
						assert(lresult.value[1] == "world");
					}}
				}}
				version(all){{
					version(all){{
						auto lresult = getResult!(combinateSequence!(
							combinateSequence!(
								parseString!("hello"),
								parseString!("world")
							),
							parseString!"!"
						))("helloworld!");
						assert(lresult.match);
						assert(lresult.rest.range == "");
						assert(lresult.value[0] == "hello");
						assert(lresult.value[1] == "world");
						assert(lresult.value[2] == "!");
					}}
					version(all){{
						auto lresult = getResult!(combinateSequence!(
							combinateSequence!(
								parseString!("hello"),
								parseString!("world")
							),
							parseString!"!"
						))("helloworld!"w);
						assert(lresult.match);
						assert(lresult.rest.range == ""w);
						assert(lresult.value[0] == "hello");
						assert(lresult.value[1] == "world");
						assert(lresult.value[2] == "!");
					}}
					version(all){{
						auto lresult = getResult!(combinateSequence!(
							combinateSequence!(
								parseString!("hello"),
								parseString!("world")
							),
							parseString!"!"
						))("helloworld!"d);
						assert(lresult.match);
						assert(lresult.rest.range == ""d);
						assert(lresult.value[0] == "hello");
						assert(lresult.value[1] == "world");
						assert(lresult.value[2] == "!");
					}}
					version(all){{
						auto lresult = getResult!(combinateSequence!(
							combinateSequence!(
								parseString!("hello"),
								parseString!("world")
							),
							parseString!"!"
						))(TestRange!"helloworld!"());
						assert(lresult.match);
						assert(lresult.rest.range.source == "");
						assert(lresult.value[0] == "hello");
						assert(lresult.value[1] == "world");
						assert(lresult.value[2] == "!");
					}}
					version(all){{
						auto lresult = getResult!(combinateSequence!(
							combinateSequence!(
								parseString!("hello"),
								parseString!("world")
							),
							parseString!"!"
						))(TestRange!"helloworld!"w());
						assert(lresult.match);
						assert(lresult.rest.range.source == ""w);
						assert(lresult.value[0] == "hello");
						assert(lresult.value[1] == "world");
						assert(lresult.value[2] == "!");
					}}
					version(all){{
						auto lresult = getResult!(combinateSequence!(
							combinateSequence!(
								parseString!("hello"),
								parseString!("world")
							),
							parseString!"!"
						))(TestRange!"helloworld!"d());
						assert(lresult.match);
						assert(lresult.rest.range.source == ""d);
						assert(lresult.value[0] == "hello");
						assert(lresult.value[1] == "world");
						assert(lresult.value[2] == "!");
					}}
				}}
				version(all){{
					version(all){{
						auto lresult = getResult!(combinateSequence!(
							parseString!("hello"),
							parseString!("world")
						))("hellovvorld");
						assert(!lresult.match);
						assert(lresult.rest.range == "");
						assert(lresult.error.need == q{"world"});
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 6);
					}}
					version(all){{
						auto lresult = getResult!(combinateSequence!(
							parseString!("hello"),
							parseString!("world")
						))("hellovvorld"w);
						assert(!lresult.match);
						assert(lresult.rest.range == ""w);
						assert(lresult.error.need == q{"world"});
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 6);
					}}
					version(all){{
						auto lresult = getResult!(combinateSequence!(
							parseString!("hello"),
							parseString!("world")
						))("hellovvorld"d);
						assert(!lresult.match);
						assert(lresult.rest.range == ""d);
						assert(lresult.error.need == q{"world"});
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 6);
					}}
					version(all){{
						auto lresult = getResult!(combinateSequence!(
							parseString!("hello"),
							parseString!("world")
						))(TestRange!"hellovvorld"());
						assert(!lresult.match);
						assert(lresult.error.need == q{"world"});
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 6);
					}}
					version(all){{
						auto lresult = getResult!(combinateSequence!(
							parseString!("hello"),
							parseString!("world")
						))(TestRange!"hellovvorld"w());
						assert(!lresult.match);
						assert(lresult.error.need == q{"world"});
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 6);
					}}
					version(all){{
						auto lresult = getResult!(combinateSequence!(
							parseString!("hello"),
							parseString!("world")
						))(TestRange!"hellovvorld"d());
						assert(!lresult.match);
						assert(lresult.error.need == q{"world"});
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 6);
					}}
				}}
				version(all){{
					version(all){{
						auto lresult = getResult!(combinateSequence!(
							parseString!("hello"),
							parseString!("world"),
							parseString!("!")
						))("helloworld?");
						assert(!lresult.match);
						assert(lresult.error.need == q{"!"});
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 11);
					}}
					version(all){{
						auto lresult = getResult!(combinateSequence!(
							parseString!("hello"),
							parseString!("world"),
							parseString!("!")
						))("helloworld?"w);
						assert(!lresult.match);
						assert(lresult.error.need == q{"!"});
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 11);
					}}
					version(all){{
						auto lresult = getResult!(combinateSequence!(
							parseString!("hello"),
							parseString!("world"),
							parseString!("!")
						))("helloworld?"d);
						assert(!lresult.match);
						assert(lresult.error.need == q{"!"});
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 11);
					}}
					version(all){{
						auto lresult = getResult!(combinateSequence!(
							parseString!("hello"),
							parseString!("world"),
							parseString!("!")
						))(TestRange!"helloworld?"());
						assert(!lresult.match);
						assert(lresult.error.need == q{"!"});
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 11);
					}}
					version(all){{
						auto lresult = getResult!(combinateSequence!(
							parseString!("hello"),
							parseString!("world"),
							parseString!("!")
						))(TestRange!"helloworld?"w());
						assert(!lresult.match);
						assert(lresult.error.need == q{"!"});
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 11);
					}}
					version(all){{
						auto lresult = getResult!(combinateSequence!(
							parseString!("hello"),
							parseString!("world"),
							parseString!("!")
						))(TestRange!"helloworld?"d());
						assert(!lresult.match);
						assert(lresult.error.need == q{"!"});
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 11);
					}}
				}}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* combinateChoice */ version(all){
		version(none) Result!(Range, CommonParserType!tparsers) combinateChoice(Range, tparsers...)(PositionalRange!Range ainput, ref memo_t amemo){
			static assert(tparsers.length > 0);
			static if(tparsers.length == 1){
				return tparsers[0](ainput, amemo);
			}else{
				typeof(return) lresult;
				auto lr1 = tparsers[0](ainput.save, amemo);
				if(lr1.match){
					lresult = lr1;
					return lresult;
				}else{
					lresult.error = lr1.error;
				}
				auto lr2 = combinateChoice!(tparsers[1..$])(ainput, amemo);
				if(lr2.match){
					lresult = lr2;
					return lresult;
				}else{
					lresult.error.need ~= " or " ~ lr2.error.need;
				}
				return lresult;
			}
		}

		template combinateChoice(tparsers...){
			Result!(Range, CommonParserType!(Range, tparsers)) apply(Range)(PositionalRange!Range ainput, ref memo_t amemo){
				static assert(tparsers.length > 0);
				static if(tparsers.length == 1){
					return tparsers[0].apply(ainput, amemo);
				}else{
					typeof(return) lresult;
					auto lr1 = tparsers[0].apply(ainput.save, amemo);
					if(lr1.match){
						lresult = lr1;
						return lresult;
					}else{
						lresult.error = lr1.error;
					}
					auto lr2 = combinateChoice!(tparsers[1..$]).apply(ainput, amemo);
					if(lr2.match){
						lresult = lr2;
						return lresult;
					}else{
						lresult.error.need ~= " or " ~ lr2.error.need;
					}
					return lresult;
				}
			}
		}

		debug(ctpg) unittest{
			enum ldg = {
				version(all){{
					version(all){{
						auto lresult = getResult!(combinateChoice!(
							parseString!"h",
							parseString!"w"
						))("hw");
						assert(lresult.match);
						assert(lresult.rest.range == "w");
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 2);
						assert(lresult.value == "h");
					}}
					version(all){{
						auto lresult = getResult!(combinateChoice!(
							parseString!"h",
							parseString!"w"
						))("hw"w);
						assert(lresult.match);
						assert(lresult.rest.range == "w"w);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 2);
						assert(lresult.value == "h");
					}}
					version(all){{
						auto lresult = getResult!(combinateChoice!(
							parseString!"h",
							parseString!"w"
						))("hw"d);
						assert(lresult.match);
						assert(lresult.rest.range == "w"d);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 2);
						assert(lresult.value == "h");
					}}
					version(all){{
						auto lresult = getResult!(combinateChoice!(
							parseString!"h",
							parseString!"w"
						))(TestRange!"hw"());
						assert(lresult.match);
						assert(lresult.rest.range.source == "w");
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 2);
						assert(lresult.value == "h");
					}}
					version(all){{
						auto lresult = getResult!(combinateChoice!(
							parseString!"h",
							parseString!"w"
						))(TestRange!"hw"w());
						assert(lresult.match);
						assert(lresult.rest.range.source == "w"w);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 2);
						assert(lresult.value == "h");
					}}
					version(all){{
						auto lresult = getResult!(combinateChoice!(
							parseString!"h",
							parseString!"w"
						))(TestRange!"hw"d());
						assert(lresult.match);
						assert(lresult.rest.range.source == "w"d);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 2);
						assert(lresult.value == "h");
					}}
				}}
				version(all){{
					version(all){{
						auto lresult = getResult!(combinateChoice!(
							parseString!"h",
							parseString!"w"
						))("w");
						assert(lresult.match);
						assert(lresult.rest.range == "");
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 2);
						assert(lresult.value == "w");
					}}
					version(all){{
						auto lresult = getResult!(combinateChoice!(
							parseString!"h",
							parseString!"w"
						))("w"w);
						assert(lresult.match);
						assert(lresult.rest.range == ""w);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 2);
						assert(lresult.value == "w");
					}}
					version(all){{
						auto lresult = getResult!(combinateChoice!(
							parseString!"h",
							parseString!"w"
						))("w"d);
						assert(lresult.match);
						assert(lresult.rest.range == ""d);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 2);
						assert(lresult.value == "w");
					}}
					version(all){{
						auto lresult = getResult!(combinateChoice!(
							parseString!"h",
							parseString!"w"
						))(TestRange!"wh"());
						assert(lresult.match);
						assert(lresult.rest.range.source == "h");
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 2);
						assert(lresult.value == "w");
					}}
					version(all){{
						auto lresult = getResult!(combinateChoice!(
							parseString!"h",
							parseString!"w"
						))(TestRange!"wh"w());
						assert(lresult.match);
						assert(lresult.rest.range.source == "h"w);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 2);
						assert(lresult.value == "w");
					}}
					version(all){{
						auto lresult = getResult!(combinateChoice!(
							parseString!"h",
							parseString!"w"
						))(TestRange!"wh"d());
						assert(lresult.match);
						assert(lresult.rest.range.source == "h"d);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 2);
						assert(lresult.value == "w");
					}}
				}}
				version(all){{
					version(all){{
						auto lresult = getResult!(combinateChoice!(
							parseString!"h",
							parseString!"w"
						))("");
						assert(!lresult.match);
						assert(lresult.error.need == q{"h" or "w"});
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 1);
					}}
					version(all){{
						auto lresult = getResult!(combinateChoice!(
							parseString!"h",
							parseString!"w"
						))(""w);
						assert(!lresult.match);
						assert(lresult.error.need == q{"h" or "w"});
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 1);
					}}
					version(all){{
						auto lresult = getResult!(combinateChoice!(
							parseString!"h",
							parseString!"w"
						))(""d);
						assert(!lresult.match);
						assert(lresult.error.need == q{"h" or "w"});
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 1);
					}}
					version(all){{
						auto lresult = getResult!(combinateChoice!(
							parseString!"h",
							parseString!"w"
						))(TestRange!""());
						assert(!lresult.match);
						assert(lresult.error.need == q{"h" or "w"});
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 1);
					}}
					version(all){{
						auto lresult = getResult!(combinateChoice!(
							parseString!"h",
							parseString!"w"
						))(TestRange!""w());
						assert(!lresult.match);
						assert(lresult.error.need == q{"h" or "w"});
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 1);
					}}
					version(all){{
						auto lresult = getResult!(combinateChoice!(
							parseString!"h",
							parseString!"w"
						))(TestRange!""d());
						assert(!lresult.match);
						assert(lresult.error.need == q{"h" or "w"});
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 1);
					}}
				}}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* combinateMore */ version(all){
		version(none) Result!(ParserType!Parser[]) combinateMore(int N, alias Parser, alias Sep = parseNone!())(stringp ainput, ref memo_t amemo){
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

		template combinateMore(int tn, alias tparser, alias tsep){
			Result!(Range, ParserType!(Range, tparser)[]) apply(Range)(PositionalRange!Range ainput, ref memo_t amemo){
				typeof(return) lresult;
				PositionalRange!Range lrest = ainput;
				while(true){
					auto lr1 = tparser.apply(lrest, amemo);
					if(lr1.match){
						lresult.value = lresult.value ~ lr1.value;
						lrest = lr1.rest;
						auto lr2 = tsep.apply(lrest, amemo);
						if(lr2.match){
							lrest = lr2.rest;
						}else{
							break;
						}
					}else{
						lresult.error = lr1.error;
						break;
					}
				}
				if(lresult.value.length >= tn){
					lresult.match = true;
					lresult.rest = lrest;
				}
				return lresult;
			}
		}

		template combinateMore0(alias tparser, alias tsep = parseNone!()){
			alias combinateMore!(0, tparser, tsep) combinateMore0;
		}

		template combinateMore1(alias tparser, alias tsep = parseNone!()){
			alias combinateMore!(1, tparser, tsep) combinateMore1;
		}

		debug(ctpg) unittest{
			enum ldg = {
				version(all){{
					version(all){{
						version(all){{
							auto lresult = getResult!(combinateMore0!(parseString!"w"))("wwwwwwwww w");
							assert(lresult.match);
							assert(lresult.rest.range == " w");
							assert(lresult.rest.line == 1);
							assert(lresult.rest.column == 10);
							assert(lresult.value.mkString() == "wwwwwwwww");
						}}
						version(all){{
							auto lresult = getResult!(combinateMore0!(parseString!"w"))("wwwwwwwww w"w);
							assert(lresult.match);
							assert(lresult.rest.range == " w"w);
							assert(lresult.rest.line == 1);
							assert(lresult.rest.column == 10);
							assert(lresult.value.mkString() == "wwwwwwwww");
						}}
						version(all){{
							auto lresult = getResult!(combinateMore0!(parseString!"w"))("wwwwwwwww w"d);
							assert(lresult.match);
							assert(lresult.rest.range == " w"d);
							assert(lresult.rest.line == 1);
							assert(lresult.rest.column == 10);
							assert(lresult.value.mkString() == "wwwwwwwww");
						}}
						version(all){{
							auto lresult = getResult!(combinateMore0!(parseString!"w"))(TestRange!"wwwwwwwww w"());
							assert(lresult.match);
							assert(lresult.rest.range.source == " w");
							assert(lresult.rest.line == 1);
							assert(lresult.rest.column == 10);
							assert(lresult.value.mkString() == "wwwwwwwww");
						}}
						version(all){{
							auto lresult = getResult!(combinateMore0!(parseString!"w"))(TestRange!"wwwwwwwww w"w());
							assert(lresult.match);
							assert(lresult.rest.range.source == " w"w);
							assert(lresult.rest.line == 1);
							assert(lresult.rest.column == 10);
							assert(lresult.value.mkString() == "wwwwwwwww");
						}}
						version(all){{
							auto lresult = getResult!(combinateMore0!(parseString!"w"))(TestRange!"wwwwwwwww w"d());
							assert(lresult.match);
							assert(lresult.rest.range.source == " w"d);
							assert(lresult.rest.line == 1);
							assert(lresult.rest.column == 10);
							assert(lresult.value.mkString() == "wwwwwwwww");
						}}
					}}
					version(all){{
						version(all){{
							auto lresult = getResult!(combinateMore0!(parseString!"w"))(" w");
							assert(lresult.match);
							assert(lresult.rest.range == " w");
							assert(lresult.rest.line == 1);
							assert(lresult.rest.column == 1);
							assert(lresult.value.mkString == "");
						}}
						version(all){{
							auto lresult = getResult!(combinateMore0!(parseString!"w"))(" w"w);
							assert(lresult.match);
							assert(lresult.rest.range == " w"w);
							assert(lresult.rest.line == 1);
							assert(lresult.rest.column == 1);
							assert(lresult.value.mkString == "");
						}}
						version(all){{
							auto lresult = getResult!(combinateMore0!(parseString!"w"))(" w"d);
							assert(lresult.match);
							assert(lresult.rest.range == " w"d);
							assert(lresult.rest.line == 1);
							assert(lresult.rest.column == 1);
							assert(lresult.value.mkString == "");
						}}
						version(all){{
							auto lresult = getResult!(combinateMore0!(parseString!"w"))(TestRange!" w"());
							assert(lresult.match);
							assert(lresult.rest.range.source == " w");
							assert(lresult.rest.line == 1);
							assert(lresult.rest.column == 1);
							assert(lresult.value.mkString == "");
						}}
						version(all){{
							auto lresult = getResult!(combinateMore0!(parseString!"w"))(TestRange!" w"w());
							assert(lresult.match);
							assert(lresult.rest.range.source == " w"w);
							assert(lresult.rest.line == 1);
							assert(lresult.rest.column == 1);
							assert(lresult.value.mkString == "");
						}}
						version(all){{
							auto lresult = getResult!(combinateMore0!(parseString!"w"))(TestRange!" w"d());
							assert(lresult.match);
							assert(lresult.rest.range.source == " w"d);
							assert(lresult.rest.line == 1);
							assert(lresult.rest.column == 1);
							assert(lresult.value.mkString == "");
						}}
					}}
				}}
				version(all){{
					version(all){{
						version(all){{
							auto lresult = getResult!(combinateMore1!(parseString!"w"))("wwwwwwwww w");
							assert(lresult.match);
							assert(lresult.rest.range == " w");
							assert(lresult.value.mkString() == "wwwwwwwww");
						}}
						version(all){{
							auto lresult = getResult!(combinateMore1!(parseString!"w"))("wwwwwwwww w"w);
							assert(lresult.match);
							assert(lresult.rest.range == " w"w);
							assert(lresult.value.mkString() == "wwwwwwwww");
						}}
						version(all){{
							auto lresult = getResult!(combinateMore1!(parseString!"w"))("wwwwwwwww w"d);
							assert(lresult.match);
							assert(lresult.rest.range == " w"d);
							assert(lresult.value.mkString() == "wwwwwwwww");
						}}
						version(all){{
							auto lresult = getResult!(combinateMore1!(parseString!"w"))(TestRange!"wwwwwwwww w"());
							assert(lresult.match);
							assert(lresult.rest.range.source == " w");
							assert(lresult.value.mkString() == "wwwwwwwww");
						}}
						version(all){{
							auto lresult = getResult!(combinateMore1!(parseString!"w"))(TestRange!"wwwwwwwww w"w());
							assert(lresult.match);
							assert(lresult.rest.range.source == " w"w);
							assert(lresult.value.mkString() == "wwwwwwwww");
						}}
						version(all){{
							auto lresult = getResult!(combinateMore1!(parseString!"w"))(TestRange!"wwwwwwwww w"d());
							assert(lresult.match);
							assert(lresult.rest.range.source == " w"d);
							assert(lresult.value.mkString() == "wwwwwwwww");
						}}
					}}
					version(all){{
						auto lresult = getResult!(combinateMore1!(parseString!"w"))(" w");
						assert(!lresult.match);
						assert(lresult.error.need == q{"w"});
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 1);
					}}
					version(all){{
						auto lresult = getResult!(combinateMore1!(parseString!"w"))(" w"w);
						assert(!lresult.match);
						assert(lresult.error.need == q{"w"});
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 1);
					}}
					version(all){{
						auto lresult = getResult!(combinateMore1!(parseString!"w"))(" w"d);
						assert(!lresult.match);
						assert(lresult.error.need == q{"w"});
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 1);
					}}
					version(all){{
						auto lresult = getResult!(combinateMore1!(parseString!"w"))(TestRange!" w"());
						assert(!lresult.match);
						assert(lresult.error.need == q{"w"});
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 1);
					}}
					version(all){{
						auto lresult = getResult!(combinateMore1!(parseString!"w"))(TestRange!" w"w());
						assert(!lresult.match);
						assert(lresult.error.need == q{"w"});
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 1);
					}}
					version(all){{
						auto lresult = getResult!(combinateMore1!(parseString!"w"))(TestRange!" w"d());
						assert(!lresult.match);
						assert(lresult.error.need == q{"w"});
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 1);
					}}
				}}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* combinateOption */ version(none){
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

	/* combinateNone */ version(none){
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

	/* combinateAnd */ version(none){
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

	/* combinateNot */ version(none){
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

	/* combinateConvert */ version(none){
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

	/* combinateCheck */ version(none){
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

	/* combinateString */ version(none){
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
	/* parseNone */ version(all){
		template parseNone(){
			Result!(Range, None) apply(Range)(PositionalRange!Range ainput, ref memo_t amemo){
				typeof(return) lresult;
				lresult.match = true;
				lresult.rest = ainput;
				return lresult;
			}
		}

		debug(ctpg) unittest{
			enum ldg = {
				version(all){{
					version(all){{
						auto lresult = getResult!(parseNone!())("hoge");
						assert(lresult.match);
						assert(lresult.rest.range == "hoge");
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 1);
					}}
					version(all){{
						auto lresult = getResult!(parseNone!())("hoge"w);
						assert(lresult.match);
						assert(lresult.rest.range == "hoge"w);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 1);
					}}
					version(all){{
						auto lresult = getResult!(parseNone!())("hoge"d);
						assert(lresult.match);
						assert(lresult.rest.range == "hoge"d);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 1);
					}}
					version(all){{
						auto lresult = getResult!(parseNone!())(TestRange!"hoge"());
						assert(lresult.match);
						assert(lresult.rest.range.source == "hoge");
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 1);
					}}
					version(all){{
						auto lresult = getResult!(parseNone!())(TestRange!"hoge"w());
						assert(lresult.match);
						assert(lresult.rest.range.source == "hoge"w);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 1);
					}}
					version(all){{
						auto lresult = getResult!(parseNone!())(TestRange!"hoge"d());
						assert(lresult.match);
						assert(lresult.rest.range.source == "hoge"d);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 1);
					}}
				}}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* parseString */ version(all){
		template parseString(string tstring) if(tstring.length > 0){
			Result!(Range, string) apply(Range)(PositionalRange!Range ainput, ref memo_t amemo){
				enum lbreadth = countBreadth(tstring);
				enum lconvertedString = staticConvertString!(tstring, Range);
				typeof(return) lresult;
				static if(isSomeString!Range){
					if(ainput.range.length >= lconvertedString.length && lconvertedString == ainput.range[0..lconvertedString.length]){
						lresult.match = true;
						lresult.value = tstring;
						lresult.rest.range = ainput.range[lconvertedString.length..$];
						lresult.rest.line = ainput.line + lbreadth.line;
						lresult.rest.column = ainput.column + lbreadth.column;
						return lresult;
					}
				}else{
					foreach(lc; lconvertedString){
						if(ainput.range.empty || lc != ainput.range.front){
							goto Lerror;
						}else{
							ainput.range.popFront;
						}
					}
					lresult.match = true;
					lresult.value = tstring;
					lresult.rest.range = ainput.range;
					lresult.rest.line = ainput.line + lbreadth.line;
					lresult.rest.column = ainput.column + lbreadth.column;
				}
			Lerror:
				lresult.error = Error('"' ~ tstring ~ '"', ainput.line, ainput.column);
				return lresult;
			}
		}

		debug(ctpg) unittest{
			enum ldg = {
				version(all){{
					version(all){{
						auto lresult = getResult!(parseString!"hello")("hello world");
						assert(lresult.match);
						assert(lresult.rest.range == " world");
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 6);
						assert(lresult.value == "hello");
					}}
					version(all){{
						auto lresult = getResult!(parseString!"hello")("hello world"w);
						assert(lresult.match);
						assert(lresult.rest.range == " world"w);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 6);
						assert(lresult.value == "hello");
					}}
					version(all){{
						auto lresult = getResult!(parseString!"hello")("hello world"d);
						assert(lresult.match);
						assert(lresult.rest.range == " world"d);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 6);
						assert(lresult.value == "hello");
					}}
					version(all){{
						auto lresult = getResult!(parseString!"hello")(TestRange!"hello world"());
						assert(lresult.match);
						assert(lresult.rest.range.source == " world");
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 6);
						assert(lresult.value == "hello");
					}}
					version(all){{
						auto lresult = getResult!(parseString!"hello")(TestRange!"hello world"w());
						assert(lresult.match);
						assert(lresult.rest.range.source == " world"w);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 6);
						assert(lresult.value == "hello");
					}}
					version(all){{
						auto lresult = getResult!(parseString!"hello")(TestRange!"hello world"d());
						assert(lresult.match);
						assert(lresult.rest.range.source == " world"d);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 6);
						assert(lresult.value == "hello");
					}}
				}}
				version(all){{
					version(all){{
						auto lresult = getResult!(parseString!"hello")("hello");
						assert(lresult.match);
						assert(lresult.rest.range == "");
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 6);
						assert(lresult.value == "hello");
					}}
					version(all){{
						auto lresult = getResult!(parseString!"hello")("hello"w);
						assert(lresult.match);
						assert(lresult.rest.range == ""w);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 6);
						assert(lresult.value == "hello");
					}}
					version(all){{
						auto lresult = getResult!(parseString!"hello")("hello"d);
						assert(lresult.match);
						assert(lresult.rest.range == ""d);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 6);
						assert(lresult.value == "hello");
					}}
					version(all){{
						auto lresult = getResult!(parseString!"hello")(TestRange!"hello"());
						assert(lresult.match);
						assert(lresult.rest.range.source == "");
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 6);
						assert(lresult.value == "hello");
					}}
					version(all){{
						auto lresult = getResult!(parseString!"hello")(TestRange!"hello"w());
						assert(lresult.match);
						assert(lresult.rest.range.source == ""w);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 6);
						assert(lresult.value == "hello");
					}}
					version(all){{
						auto lresult = getResult!(parseString!"hello")(TestRange!"hello"d());
						assert(lresult.match);
						assert(lresult.rest.range.source == ""d);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 6);
						assert(lresult.value == "hello");
					}}
				}}
				version(all){{
					version(all){{
						auto lresult = getResult!(parseString!"今は昔、竹取の翁")("今は昔、竹取の翁といふ者ありけり。");
						assert(lresult.match);
						assert(lresult.rest.range == "といふ者ありけり。");
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 9);
						assert(lresult.value == "今は昔、竹取の翁");
					}}
					version(all){{
						auto lresult = getResult!(parseString!"今は昔、竹取の翁")("今は昔、竹取の翁といふ者ありけり。"w);
						assert(lresult.match);
						assert(lresult.rest.range == "といふ者ありけり。"w);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 9);
						assert(lresult.value == "今は昔、竹取の翁");
					}}
					version(all){{
						auto lresult = getResult!(parseString!"今は昔、竹取の翁")("今は昔、竹取の翁といふ者ありけり。"d);
						assert(lresult.match);
						assert(lresult.rest.range == "といふ者ありけり。"d);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 9);
						assert(lresult.value == "今は昔、竹取の翁");
					}}
					version(all){{
						auto lresult = getResult!(parseString!"aaaaa")(repeat(cast(char)'a'));
						assert(lresult.match);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 6);
						assert(lresult.value == "aaaaa");
					}}
					version(all){{
						auto lresult = getResult!(parseString!"aaaaa")(repeat(cast(wchar)'a'));
						assert(lresult.match);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 6);
						assert(lresult.value == "aaaaa");
					}}
					version(all){{
						auto lresult = getResult!(parseString!"aaaaa")(repeat(cast(dchar)'a'));
						assert(lresult.match);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 6);
						assert(lresult.value == "aaaaa");
					}}
				}}
				version(all){{
					version(all){{
						auto lresult = getResult!(parseString!"今は昔、竹取の翁")(TestRange!"今は昔、竹取の翁といふ者ありけり。"());
						assert(lresult.match);
						assert(lresult.rest.range.source == "といふ者ありけり。");
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 9);
						assert(lresult.value == "今は昔、竹取の翁");
					}}
					version(all){{
						auto lresult = getResult!(parseString!"今は昔、竹取の翁")(TestRange!"今は昔、竹取の翁といふ者ありけり。"w());
						assert(lresult.match);
						assert(lresult.rest.range.source == "といふ者ありけり。"w);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 9);
						assert(lresult.value == "今は昔、竹取の翁");
					}}
					version(all){{
						auto lresult = getResult!(parseString!"今は昔、竹取の翁")(TestRange!"今は昔、竹取の翁といふ者ありけり。"d());
						assert(lresult.match);
						assert(lresult.rest.range.source == "といふ者ありけり。"d);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 9);
						assert(lresult.value == "今は昔、竹取の翁");
					}}
				}}
				version(all){{
					auto lresult = getResult!(parseString!"hello")("hllo world");
					assert(!lresult.match);
					assert(lresult.rest.range == "");
					assert(lresult.error.need == "\"hello\"");
					assert(lresult.error.line == 1);
					assert(lresult.error.column == 1);
				}}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* parseCharRange */ version(all){
		version(none) Result!string parseCharRange(dchar Low, dchar High)(stringp ainput, ref memo_t amemo){
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

		template parseCharRange(dchar tlow, dchar thigh){
			static assert(tlow <= thigh);
			Result!(Range, string) apply(Range)(PositionalRange!Range ainput, memo_t amemo){
				typeof(return) lresult;
				static if(isSomeString!Range){
					if(ainput.range.length){
						size_t lidx;
						dchar lc = ainput.range.decode(lidx);
						if(tlow <= lc && lc <= thigh){
							lresult.match = true;
							lresult.value = to!string(lc);
							lresult.rest.range = ainput.range[lidx..$];
							lresult.rest.line = lc == '\n' ? ainput.line + 1 : ainput.line;
							lresult.rest.column = lc == '\n' ? 1 : ainput.column + 1;
							return lresult;
						}
					}
				}else{
					static assert(false);
				}
				lresult.error = Error("c: '" ~ to!string(tlow) ~ "' <= c <= '" ~ to!string(thigh) ~ "'", ainput.line, ainput.column);
				return lresult;
			}
		}

		debug(ctpg) unittest{
			enum ldg = {
				version(all){{
					auto lr = getResult!(parseCharRange!('a', 'z'))("hoge");
					assert(lr.match);
					assert(lr.rest.range == "oge");
					assert(lr.value == "h");
				}}
				version(all){{
					auto lr = getResult!(parseCharRange!('\u0100', '\U0010FFFF'))("表が怖い噂のソフト");
					assert(lr.match);
					assert(lr.rest.range == "が怖い噂のソフト");
					assert(lr.value == "表");
				}}
				version(all){{
					auto lr = getResult!(parseCharRange!('\u0100', '\U0010FFFF'))("hello world");
					assert(!lr.match);
					assert(lr.rest.range == "");
					assert(lr.error.need == "c: '\u0100' <= c <= '\U0010FFFF'");
					assert(lr.error.line == 1);
					assert(lr.error.column == 1);
				}}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* parseAnyChar */ version(all){
		version(none) Result!string parseAnyChar(stringp ainput, ref memo_t amemo){
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

		template parseAnyChar(){
			Result!(Range, string) apply(Range)(PositionalRange!Range ainput, memo_t amemo){
				typeof(return) lresult;
				static if(isSomeString!Range){
					if(ainput.range.length){
						size_t lidx;
						static if(is(Range : const(dchar[]))){
							dchar lc = ainput[0];
							lidx = 1;
						}else static if(is(Range : const(wchar[])) || is(Range : const(char[]))){
							dchar lc = ainput.range.decode(lidx);
						}else{
							static assert(false);
						}
						lresult.match = true;
						lresult.value = to!string(lc);
						lresult.rest.range = ainput.range[lidx..$];
						lresult.rest.line = lc == '\n' ? ainput.line + 1 : ainput.line;
						lresult.rest.column = lc == '\n' ? 1 : ainput.column + 1;
						return lresult;
					}
				}else{
					static if(is(ElementType!Range : char)){
						auto lc = ainput.range.front;

					}
				}
				lresult.error = Error("any char", ainput.line, ainput.column);
				return lresult;
			}
		}

		alias parseAnyChar a;

		debug(ctpg) unittest{
			enum ldg = {
				version(all){{
					auto lresult = getResult!(parseAnyChar!())("hoge");
					assert(lresult.match);
					assert(lresult.rest.range == "oge");
					assert(lresult.rest.line == 1);
					assert(lresult.rest.column == 2);
					assert(lresult.value == "h");
				}}
				version(all){{
					auto lresult = getResult!(parseAnyChar!())("表が怖い噂のソフト");
					assert(lresult.match);
					assert(lresult.rest.range == "が怖い噂のソフト");
					assert(lresult.rest.line == 1);
					assert(lresult.rest.column == 2);
					assert(lresult.value == "表");
				}}
				version(all){{
					auto lresult = getResult!(parseAnyChar!())("独");
					assert(lresult.match);
					assert(lresult.rest.range == "");
					assert(lresult.rest.line == 1);
					assert(lresult.rest.column == 2);
					assert(lresult.value == "独");
				}}
				version(all){{
					auto lresult = getResult!(parseAnyChar!())("\nhoge");
					assert(lresult.match);
					assert(lresult.rest.range == "hoge");
					assert(lresult.rest.line == 2);
					assert(lresult.rest.column == 1);
					assert(lresult.value == "\n");
				}}
				version(all){{
					auto lresult = getResult!(parseAnyChar!())("");
					assert(!lresult.match);
					assert(lresult.error.need == "any char");
					assert(lresult.error.line == 1);
					assert(lresult.error.column == 1);
				}}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* parseEscapeSequence */ version(all){
		version(none) Result!string parseEscapeSequence(stringp ainput, ref memo_t amemo){
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

		template parseEscapeSequence(){
			Result!(Range, string) apply(Range)(PositionalRange!Range ainput, memo_t amemo){
				typeof(return) lresult;
				static if(isSomeString!Range){
					if(ainput.range[0] == '\\'){
						switch(ainput.range[1]){
							case 'u':{
								lresult.match = true;
								lresult.value = to!string(ainput.range[0..6]);
								lresult.rest.range = ainput.range[6..$];
								lresult.rest.line = ainput.line;
								lresult.rest.column = ainput.column + 6;
								return lresult;
							}
							case 'U':{
								lresult.match = true;
								lresult.value = to!string(ainput.range[0..10]);
								lresult.rest.range = ainput.range[10..$];
								lresult.rest.line = ainput.line;
								lresult.rest.column = ainput.column + 10;
								return lresult;
							}
							case '\'':
							case '"':
							case '?':
							case '\\':
							case 'a':
							case 'b':
							case 'f':
							case 'n':
							case 'r':
							case 't':
							case 'v':{
								lresult.match = true;
								lresult.value = to!string(ainput.range[0..2]);
								lresult.rest.range = ainput.range[2..$];
								lresult.rest.line = ainput.line;
								lresult.rest.column = ainput.column + 2;
								return lresult;
							}
							default:{
							}
						}
					}
				}else{
					auto lc1 = ainput.range.front;
					if(lc1 == '\\'){
						ainput.range.popFront;
						auto lc2 = ainput.range.front;
						switch(lc2){
							case 'u':{
								lresult.match = true;
								ainput.range.popFront;
								char[6] ldata;
								ldata[0..2] = "\\u";
								foreach(lidx; 2..6){
									ldata[lidx] = cast(char)ainput.range.front;
									ainput.range.popFront;
								}
								lresult.value = to!string(ldata);
								lresult.rest.range = ainput.range;
								lresult.rest.line = ainput.line;
								lresult.rest.column = ainput.column + 6;
								return lresult;
							}
							case 'U':{
								lresult.match = true;
								ainput.range.popFront;
								char[10] ldata;
								ldata[0..2] = "\\U";
								foreach(lidx; 2..10){
									ldata[lidx] = cast(char)ainput.range.front;
									ainput.range.popFront;
								}
								lresult.value = to!string(ldata);
								lresult.rest.range = ainput.range;
								lresult.rest.line = ainput.line;
								lresult.rest.column = ainput.column + 10;
								return lresult;
							}
							case '\'':
							case '"':
							case '?':
							case '\\':
							case 'a':
							case 'b':
							case 'f':
							case 'n':
							case 'r':
							case 't':
							case 'v':{
								lresult.match = true;
								ainput.range.popFront;
								lresult.value = "\\" ~ to!string(lc2);
								lresult.rest.range = ainput.range;
								lresult.rest.line = ainput.line;
								lresult.rest.column = ainput.column + 2;
								return lresult;
							}
							default:{
							}
						}
					}
				}
				lresult.error = Error("escape sequence", ainput.line, ainput.column);
				return lresult;
			}
		}

		alias parseEscapeSequence es;

		debug(ctpg) unittest{
			static assert(isRandomAccessRange!(TestRandomRange!"hoge"));

			enum ldg = {
				/* \\hoge */ version(all){{
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())("\\\"hoge");
						assert(lresult.match);
						assert(lresult.rest.range == "hoge");
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 3);
						assert(lresult.value == "\\\"");
					}}
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())("\\\"hoge"w);
						assert(lresult.match);
						assert(lresult.rest.range == "hoge"w);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 3);
						assert(lresult.value == "\\\"");
					}}
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())("\\\"hoge"d);
						assert(lresult.match);
						assert(lresult.rest.range == "hoge"d);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 3);
						assert(lresult.value == "\\\"");
					}}
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())(TestRange!"\\\"hoge"());
						assert(lresult.match);
						assert(lresult.rest.range.source == "hoge");
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 3);
						assert(lresult.value == "\\\"");
					}}
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())(TestRange!"\\\"hoge"w());
						assert(lresult.match);
						assert(lresult.rest.range.source == "hoge");
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 3);
						assert(lresult.value == "\\\"");
					}}
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())(TestRange!"\\\"hoge"d());
						assert(lresult.match);
						assert(lresult.rest.range.source == "hoge"d);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 3);
						assert(lresult.value == "\\\"");
					}}
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())(TestRandomRange!"\\\"hoge"());
						assert(lresult.match);
						assert(lresult.rest.range.source == "hoge");
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 3);
						assert(lresult.value == "\\\"");
					}}
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())(TestRandomRange!"\\\"hoge"w());
						assert(lresult.match);
						assert(lresult.rest.range.source == "hoge");
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 3);
						assert(lresult.value == "\\\"");
					}}
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())(TestRandomRange!"\\\"hoge"d());
						assert(lresult.match);
						assert(lresult.rest.range.source == "hoge"d);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 3);
						assert(lresult.value == "\\\"");
					}}
				}}
				/* \U0010FFFF */version(all){{
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())("\\U0010FFFFhoge");
						assert(lresult.match);
						assert(lresult.rest.range == "hoge");
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 11);
						assert(lresult.value == "\\U0010FFFF");
					}}
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())("\\U0010FFFFhoge"w);
						assert(lresult.match);
						assert(lresult.rest.range == "hoge"w);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 11);
						assert(lresult.value == "\\U0010FFFF");
					}}
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())("\\U0010FFFFhoge"d);
						assert(lresult.match);
						assert(lresult.rest.range == "hoge"d);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 11);
						assert(lresult.value == "\\U0010FFFF");
					}}
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())(TestRange!"\\U0010FFFFhoge"());
						assert(lresult.match);
						assert(lresult.rest.range.source == "hoge");
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 11);
						assert(lresult.value == "\\U0010FFFF");
					}}
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())(TestRange!"\\U0010FFFFhoge"w());
						assert(lresult.match);
						assert(lresult.rest.range.source == "hoge"w);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 11);
						assert(lresult.value == "\\U0010FFFF");
					}}
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())(TestRange!"\\U0010FFFFhoge"d());
						assert(lresult.match);
						assert(lresult.rest.range.source == "hoge"d);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 11);
						assert(lresult.value == "\\U0010FFFF");
					}}
				}}
				/* /u10&& */ version(all){{
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())("\\u10FFhoge");
						assert(lresult.match);
						assert(lresult.rest.range == "hoge");
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 7);
						assert(lresult.value == "\\u10FF");
					}}
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())("\\u10FFhoge"w);
						assert(lresult.match);
						assert(lresult.rest.range == "hoge"w);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 7);
						assert(lresult.value == "\\u10FF");
					}}
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())("\\u10FFhoge"d);
						assert(lresult.match);
						assert(lresult.rest.range == "hoge"d);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 7);
						assert(lresult.value == "\\u10FF");
					}}
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())(TestRange!"\\u10FFhoge"());
						assert(lresult.match);
						assert(lresult.rest.range.source == "hoge");
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 7);
						assert(lresult.value == "\\u10FF");
					}}
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())(TestRange!"\\u10FFhoge"w());
						assert(lresult.match);
						assert(lresult.rest.range.source == "hoge"w);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 7);
						assert(lresult.value == "\\u10FF");
					}}
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())(TestRange!"\\u10FFhoge"d());
						assert(lresult.match);
						assert(lresult.rest.range.source == "hoge"d);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 7);
						assert(lresult.value == "\\u10FF");
					}}
				}}
				/* \nhoge */ version(all){{
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())(`\\hoge`);
						assert(lresult.match);
						assert(lresult.rest.range == "hoge");
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 3);
						assert(lresult.value == `\\`);
					}}
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())(`\\hoge`w);
						assert(lresult.match);
						assert(lresult.rest.range == "hoge"w);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 3);
						assert(lresult.value == `\\`);
					}}
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())(`\\hoge`d);
						assert(lresult.match);
						assert(lresult.rest.range == "hoge"d);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 3);
						assert(lresult.value == `\\`);
					}}
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())(TestRange!`\\hoge`());
						assert(lresult.match);
						assert(lresult.rest.range.source == "hoge");
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 3);
						assert(lresult.value == `\\`);
					}}
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())(TestRange!`\thoge`w());
						assert(lresult.match);
						assert(lresult.rest.range.source == "hoge"w);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 3);
						assert(lresult.value == `\t`);
					}}
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())(TestRange!`\nhoge`d());
						assert(lresult.match);
						assert(lresult.rest.range.source == "hoge"d);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 3);
						assert(lresult.value == `\n`);
					}}
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())(TestRandomRange!`\\hoge`());
						assert(lresult.match);
						assert(lresult.rest.range.source == "hoge");
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 3);
						assert(lresult.value == `\\`);
					}}
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())(TestRandomRange!`\thoge`w());
						assert(lresult.match);
						assert(lresult.rest.range.source == "hoge"w);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 3);
						assert(lresult.value == `\t`);
					}}
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())(TestRandomRange!`\nhoge`d());
						assert(lresult.match);
						assert(lresult.rest.range.source == "hoge"d);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 3);
						assert(lresult.value == `\n`);
					}}
				}}
				/* 欝hoge */ version(all){{
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())("欝hoge");
						assert(!lresult.match);
						assert(lresult.error.need == "escape sequence");
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 1);
					}}
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())("欝hoge"w);
						assert(!lresult.match);
						assert(lresult.error.need == "escape sequence");
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 1);
					}}
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())("欝hoge"d);
						assert(!lresult.match);
						assert(lresult.error.need == "escape sequence");
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 1);
					}}
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())(TestRange!"欝hoge"());
						assert(!lresult.match);
						assert(lresult.error.need == "escape sequence");
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 1);
					}}
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())(TestRange!"欝hoge"w());
						assert(!lresult.match);
						assert(lresult.error.need == "escape sequence");
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 1);
					}}
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())(TestRange!"欝hoge"d());
						assert(!lresult.match);
						assert(lresult.error.need == "escape sequence");
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 1);
					}}
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())(TestRandomRange!"欝hoge"());
						assert(!lresult.match);
						assert(lresult.error.need == "escape sequence");
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 1);
					}}
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())(TestRandomRange!"欝hoge"w());
						assert(!lresult.match);
						assert(lresult.error.need == "escape sequence");
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 1);
					}}
					version(all){{
						auto lresult = getResult!(parseEscapeSequence!())(TestRandomRange!"欝hoge"d());
						assert(!lresult.match);
						assert(lresult.error.need == "escape sequence");
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 1);
					}}
				}}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* parseSpace */ version(all){
		version(none) Result!string parseSpace(stringp ainput, ref memo_t amemo){
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

		template parseSpace(){
			Result!(Range, string) apply(Range)(PositionalRange!Range ainput, memo_t amemo){
				typeof(return) lresult;
				static if(isSomeString!Range){
					if(ainput.range.length > 0 && (ainput.range[0] == ' ' || ainput.range[0] == '\n' || ainput.range[0] == '\t' || ainput.range[0] == '\r' || ainput.range[0] == '\f')){
						lresult.match = true;
						lresult.value = to!string(ainput.range[0..1]);
						lresult.rest.range = ainput.range[1..$];
						lresult.rest.line = (ainput.range[0] == '\n' ? ainput.line + 1 : ainput.line);
						lresult.rest.column = (ainput.range[0] == '\n' ? 1 : ainput.column + 1);
						return lresult;
					}
				}else{
					if(!ainput.range.empty){
						Unqual!(ElementType!Range) lc = ainput.range.front;
						if(lc == ' ' || lc == '\n' || lc == '\t' || lc == '\r' || lc == '\f'){
							lresult.match = true;
							lresult.value = to!string(lc);
							ainput.range.popFront;
							lresult.rest.range = ainput.range;
							lresult.rest.line = (lc == '\n' ? ainput.line + 1 : ainput.line);
							lresult.rest.column = (lc == '\n' ? 1 : ainput.column + 1);
							return lresult;
						}
					}
				}
				lresult.error = Error("space", ainput.line, ainput.column);
				return lresult;
			}
		}

		alias parseSpace space_p;

		debug(ctpg) unittest{
			enum ldg = {
				/* "\thoge" */ version(all){{
					version(all){{
						auto lresult = getResult!(parseSpace!())("\thoge");
						assert(lresult.match);
						assert(lresult.rest.range == "hoge");
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 2);
						assert(lresult.value == "\t");
					}}
					version(all){{
						auto lresult = getResult!(parseSpace!())("\thoge"w);
						assert(lresult.match);
						assert(lresult.rest.range == "hoge"w);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 2);
						assert(lresult.value == "\t");
					}}
					version(all){{
						auto lresult = getResult!(parseSpace!())("\thoge"d);
						assert(lresult.match);
						assert(lresult.rest.range == "hoge"d);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 2);
						assert(lresult.value == "\t");
					}}
					version(all){{
						auto lresult = getResult!(parseSpace!())(TestRange!"\thoge"());
						assert(lresult.match);
						assert(lresult.rest.range.source == "hoge");
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 2);
						assert(lresult.value == "\t");
					}}
					version(all){{
						auto lresult = getResult!(parseSpace!())(TestRange!"\thoge"w());
						assert(lresult.match);
						assert(lresult.rest.range.source == "hoge"w);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 2);
						assert(lresult.value == "\t");
					}}
					version(all){{
						auto lresult = getResult!(parseSpace!())(TestRange!"\thoge"d());
						assert(lresult.match);
						assert(lresult.rest.range.source == "hoge"d);
						assert(lresult.rest.line == 1);
						assert(lresult.rest.column == 2);
						assert(lresult.value == "\t");
					}}
				}}
				/* hoge */ version(all){{
					version(all){{
						auto lresult = getResult!(parseSpace!())("hoge");
						assert(!lresult.match);
						assert(lresult.error.need == "space");
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 1);
					}}
					version(all){{
						auto lresult = getResult!(parseSpace!())("hoge"w);
						assert(!lresult.match);
						assert(lresult.error.need == "space");
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 1);
					}}
					version(all){{
						auto lresult = getResult!(parseSpace!())("hoge"d);
						assert(!lresult.match);
						assert(lresult.error.need == "space");
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 1);
					}}
					version(all){{
						auto lresult = getResult!(parseSpace!())(TestRange!"hoge"());
						assert(!lresult.match);
						assert(lresult.error.need == "space");
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 1);
					}}
					version(all){{
						auto lresult = getResult!(parseSpace!())(TestRange!"hoge"w());
						assert(!lresult.match);
						assert(lresult.error.need == "space");
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 1);
					}}
					version(all){{
						auto lresult = getResult!(parseSpace!())(TestRange!"hoge"d());
						assert(!lresult.match);
						assert(lresult.error.need == "space");
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 1);
					}}
				}}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* parseSpaces */ version(none){
		alias combinateNone!(combinateMore0!parseSpace) parseSpaces;

		alias parseSpaces s;

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
		version(none) Result!None parseEOF(stringp ainput, ref memo_t amemo){
			typeof(return) lres;
			if(ainput.length == 0){
				lres.match = true;
			}else{
				lres.error = Error("EOF", ainput.line, ainput.column);
			}
			return lres;
		}

		template parseEOF(){
			Result!(Range, None) apply(Range)(PositionalRange!Range ainput, memo_t amemo){
				typeof(return) lresult;
				if(ainput.range.empty){
					lresult.match = true;
				}else{
					lresult.error = Error("EOF", ainput.line, ainput.column);
				}
				return lresult;
			}
		}

		debug(ctpg) unittest{
			enum ldg = {
				/* "" */ version(all){{
					version(all){{
						auto lresult = getResult!(parseEOF!())("");
						assert(lresult.match);
					}}
					version(all){{
						auto lresult = getResult!(parseEOF!())(""w);
						assert(lresult.match);
					}}
					version(all){{
						auto lresult = getResult!(parseEOF!())(""d);
						assert(lresult.match);
					}}
					version(all){{
						auto lresult = getResult!(parseEOF!())(TestRange!""());
						assert(lresult.match);
					}}
					version(all){{
						auto lresult = getResult!(parseEOF!())(TestRange!""w());
						assert(lresult.match);
					}}
					version(all){{
						auto lresult = getResult!(parseEOF!())(TestRange!""d());
						assert(lresult.match);
					}}
				}}
				/* hoge */ version(all){{
					version(all){{
						auto lresult = getResult!(parseEOF!())("hoge");
						assert(!lresult.match);
						assert(lresult.error.need == "EOF");
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 1);
					}}
					version(all){{
						auto lresult = getResult!(parseEOF!())("hoge"w);
						assert(!lresult.match);
						assert(lresult.error.need == "EOF");
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 1);
					}}
					version(all){{
						auto lresult = getResult!(parseEOF!())("hoge"d);
						assert(!lresult.match);
						assert(lresult.error.need == "EOF");
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 1);
					}}
					version(all){{
						auto lresult = getResult!(parseEOF!())(TestRange!"hoge"());
						assert(!lresult.match);
						assert(lresult.error.need == "EOF");
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 1);
					}}
					version(all){{
						auto lresult = getResult!(parseEOF!())(TestRange!"hoge"w());
						assert(!lresult.match);
						assert(lresult.error.need == "EOF");
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 1);
					}}
					version(all){{
						auto lresult = getResult!(parseEOF!())(TestRange!"hoge"d());
						assert(!lresult.match);
						assert(lresult.error.need == "EOF");
						assert(lresult.error.line == 1);
						assert(lresult.error.column == 1);
					}}
				}}
				return true;
			};
			debug(ctpg_ct) static assert(ldg());
			ldg();
		}
	}

	/* parseIdent */ version(none){
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

		alias parseIdent ident_p;

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

	/* parseStringLiteral */ version(none){
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

		alias parseStringLiteral strLit_p;

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

	/* parseIntLiteral */ version(none){
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

		alias parseIntLiteral intLit_p;

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

version(none){
mixin template ctpg(string Src){
	mixin(parse!defs(Src));
}

template getSource(string Src){
	enum getSource = getResult!defs(Src).value;
}
}

auto getResult(alias Func, Range)(Range ainput){
	memo_t lmemo;
	return Func.apply(PositionalRange!Range(ainput), lmemo);
}

version(none){
auto parse(alias Func)(string asrc){
	auto res = getResult!Func(asrc);
	if(res.match){
		return res.value;
	}else{
		throw new Exception(to!string(res.error.line) ~ q{: } ~ to!string(res.error.column) ~ q{: error } ~ res.error.need ~ q{ is needed});
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
					bool hoge = !"hello" $ >> {return false;};
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
				auto lr = getResult!def(q{bool hoge = !"hello" $ >> {return false;};});
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
					auto lr = getResult!convExp(q{!"hello" $ >> {return false;}});
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
					auto lr = getResult!choiceExp(`!$* / (&(^"a"))?`);
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
					auto lr = getResult!choiceExp(`!"hello" $`);
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
					auto lr = getResult!seqExp("!$* (&(^$))?");
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
					enum lr = getResult!seqExp("!\"hello\" $");
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
				auto lr = getResult!optionExp("(&(^\"hello\"))?");
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
				auto lr = getResult!postExp("!$*");
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
							return "memoizeInput!(combinateNone!(" ~ aprimaryExp ~ "))";
						}
						case "^":{
							return "memoizeInput!(combinateNot!(" ~ aprimaryExp ~ "))";
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
				auto lr = getResult!preExp("!$");
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
					auto lr = getResult!primaryExp("(&(^$)?)");
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
				memoizeInput!eofLit
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
					auto lr = getResult!literal("$");
					assert(lr.match);
					assert(lr.rest == "");
					assert(lr.value == "memoizeInput!(parseEOF)");
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

debug(ctpg) struct TestRange(alias str){
	typeof(str) source = str;
	@property typeof(source[0]) front(){ return source[0]; }
	@property void popFront(){ source = source[1..$]; }
	@property bool empty(){ return source.length == 0; }
	@property typeof(this) save(){ return this; }
}

debug(ctpg) struct TestRandomRange(alias str){
	typeof(str) source = str;
	@property typeof(source[0]) front(){ return source[0]; }
	@property typeof(source[0]) back(){ return source[$]; }
	@property void popFront(){ source = source[1..$]; }
	@property void popBack(){ source = source[0..$-1]; }
	@property bool empty(){ return source.length == 0; }
	@property typeof(this) save(){ return this; }
	@property size_t length(){ return source.length; };
	typeof(source[0]) opIndex(size_t lidx){ return source[lidx]; }
}

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

template staticConvertString(string tstring, T){
	static if(is(T == string)){
		alias tstring staticConvertString;
	}else static if(is(T == wstring)){
		enum staticConvertString = mixin("\"" ~ tstring ~ "\"w");
	}else static if(is(T == dstring)){
		enum staticConvertString = mixin("\"" ~ tstring ~ "\"d");
	}else static if(isInputRange!T){
		static if(is(Unqual!(ElementType!T) == char)){
			alias tstring staticConvertString;
		}else static if(is(Unqual!(ElementType!T) == wchar)){
			enum staticConvertString = mixin("\"" ~ tstring ~ "\"w");
		}else static if(is(Unqual!(ElementType!T) == dchar)){
			enum staticConvertString = mixin("\"" ~ tstring ~ "\"d");
		}else{
			static assert(false);
		}
	}
}

debug(ctpg) unittest{
	static assert(staticConvertString!("foobar", string) == "foobar");
	static assert(staticConvertString!("foobar", wstring) == "foobar"w);
	static assert(staticConvertString!("foobar", dstring) == "foobar"d);
}

Tuple!(size_t, "line", size_t, "column") countBreadth(string astring)in{
	assert(astring.length > 0);
}body{
	typeof(return) lresult;
	size_t lidx;
	while(lidx < astring.length){
		auto lc = decode(astring, lidx);
		if(lc == '\n'){
			lresult.line++;
			lresult.column = 0;
		}else{
			lresult.column++;
		}
	}
	return lresult;
}

debug(ctpg) unittest{
	static assert({
		{
			auto lresult = countBreadth("これ\nとこれ");
			assert(lresult.line == 1);
			assert(lresult.column == 3);
		}
		{
			auto lresult = countBreadth("これ\nとこれ\nとさらにこれ");
			assert(lresult.line == 2);
			assert(lresult.column == 6);
		}
		{
			auto lresult = countBreadth("helloワールド");
			assert(lresult.line == 0);
			assert(lresult.column == 9);
		}
		return true;
	}());
}

template ResultType(Range, alias R){
	static if(is(R Unused == Result!(Range, E), E)){
		alias E ResultType;
	}else{
		static assert(false);
	}
}

debug(ctpg) unittest{
	static assert(is(ResultType!(string, Result!(string, int)) == int));
	static assert(is(ResultType!(wstring, Result!(wstring, int)) == int));
	static assert(is(ResultType!(dstring, Result!(dstring, int)) == int));
	static assert(is(ResultType!(string, Result!(string, long)) == long));
	static assert(is(ResultType!(wstring, Result!(wstring, long)) == long));
	static assert(is(ResultType!(dstring, Result!(dstring, long)) == long));
}

version(none) template ParserType(alias parser){
	static if(is(ReturnType!parser Unused == Result!(T), T)){
		alias T ParserType;
	}else{
		static assert(false);
	}
}

template ParsersTypeTuple(Range, tparsers...){
	static if(tparsers.length == 1){
		static if(is(ReturnType!(tparsers[0].apply!(Range)) Unused == Result!(Range, T), T)){
			alias Tuple!T ParsersTypeTuple;
		}else{
			static assert(false);
		}
	}else static if(tparsers.length > 1){
		static if(is(ReturnType!(tparsers[0].apply!(Range)) Unused == Result!(Range, T), T)){
			alias Tuple!(T, ParsersTypeTuple!(Range, tparsers[1..$]).Types) ParsersTypeTuple;
		}
	}else{
		static assert(false);
	}
}

debug(ctpg) unittest{
	static assert(is(ParsersTypeTuple!(string, parseString!"a", parseString!"a") == Tuple!(string, string)));
	static assert(is(ParsersTypeTuple!(string, parseString!"a") == Tuple!(string)));
	static assert(is(ParsersTypeTuple!(wstring, parseString!"a", parseString!"a") == Tuple!(string, string)));
	static assert(is(ParsersTypeTuple!(wstring, parseString!"a") == Tuple!(string)));
	static assert(is(ParsersTypeTuple!(dstring, parseString!"a", parseString!"a") == Tuple!(string, string)));
	static assert(is(ParsersTypeTuple!(dstring, parseString!"a") == Tuple!(string)));
	static assert(is(ParsersTypeTuple!(TestRange!"", parseString!"a", parseString!"a") == Tuple!(string, string)));
	static assert(is(ParsersTypeTuple!(TestRange!"", parseString!"a") == Tuple!(string)));
	static assert(is(ParsersTypeTuple!(TestRange!""w, parseString!"a", parseString!"a") == Tuple!(string, string)));
	static assert(is(ParsersTypeTuple!(TestRange!""w, parseString!"a") == Tuple!(string)));
	static assert(is(ParsersTypeTuple!(TestRange!""d, parseString!"a", parseString!"a") == Tuple!(string, string)));
	static assert(is(ParsersTypeTuple!(TestRange!""d, parseString!"a") == Tuple!(string)));
}

template ParserType(Range, alias tparser){
	static if(is(ReturnType!(tparser.apply!(Range)) Unused == Result!(Range, T), T)){
		alias T ParserType;
	}else{
		static assert(false);
	}
}

debug(ctpg) unittest{
	static assert(is(ParserType!(string, parseString!"a") == string));
	static assert(is(ParserType!(wstring, parseString!"a") == string));
	static assert(is(ParserType!(dstring, parseString!"a") == string));
	static assert(is(ParserType!(TestRange!"", parseString!"a") == string));
	static assert(is(ParserType!(TestRange!""w, parseString!"a") == string));
	static assert(is(ParserType!(TestRange!""d, parseString!"a") == string));
}

template flatTuple(arg){
	static if(isTuple!arg){
		alias arg.Types flatTuple;
	}else{
		alias arg flatTuple;
	}
}

debug(ctpg) unittest{
	static assert(is(flatTuple!(Tuple!(string, string)) == TypeTuple!(string, string)));
	static assert(is(flatTuple!(string) == string));
}

version(none) template CombinateSequenceImplType(Range, tparsers...){
	alias Result!(Tuple!(staticMap!(flatTuple, staticMap!(ParserType, tparsers)))) CombinateSequenceImplType;
}

template CombinateSequenceImplType(Range, tparsers...){
	alias Result!(Range, Tuple!(staticMap!(flatTuple, ParsersTypeTuple!(Range, tparsers).Types))) CombinateSequenceImplType;
}

debug(ctpg) unittest{
	static assert(is(CombinateSequenceImplType!(string, parseString!"a", parseString!"a") == Result!(string, Tuple!(string, string))));
	static assert(is(CombinateSequenceImplType!(wstring, parseString!"a", parseString!"a") == Result!(wstring, Tuple!(string, string))));
	static assert(is(CombinateSequenceImplType!(dstring, parseString!"a", parseString!"a") == Result!(dstring, Tuple!(string, string))));
	static assert(is(CombinateSequenceImplType!(TestRange!"", parseString!"a", parseString!"a") == Result!(TestRange!"", Tuple!(string, string))));
	static assert(is(CombinateSequenceImplType!(TestRange!""w, parseString!"a", parseString!"a") == Result!(TestRange!""w, Tuple!(string, string))));
	static assert(is(CombinateSequenceImplType!(TestRange!""d, parseString!"a", parseString!"a") == Result!(TestRange!""d, Tuple!(string, string))));
}

template UnTuple(Range, E){
	static if(ResultType!(Range, E).Types.length == 1){
		alias Result!(ResultType!(Range, E).Types[0]) UnTuple;
	}else{
		alias E UnTuple;
	}
}

UnTuple!(Range, R) unTuple(Range, R)(R r){
	static if(ResultType!(Range, R).Types.length == 1){
		return Result!(ResultType!R.Types[0])(r.match, r.value[0], r.rest, r.error);
	}else{
		return r;
	}
}

version(none) template CommonParserType(parsers...){
	alias CommonType!(staticMap!(ParserType, parsers)) CommonParserType;
}

template CommonParserType(Range, tparsers...){
	static if(tparsers.length == 1){
		alias ParserType!(Range, tparsers[0]) CommonParserType;
	}else static if(tparsers.length > 1){
		alias CommonType!(ParserType!(Range, tparsers[0]), CommonParserType!(Range, tparsers[1..$])) CommonParserType;
	}else{
		static assert(false);
	}
}

debug(ctpg) unittest{
	static assert(is(CommonParserType!(string, parseString!"a", parseString!"a") == string));
}

version(none) dchar decode(Range)(ref Range arange){
	static assert(isSomeChar!(Unqual!(ElementType!Range)));
	static if(is(Unqual!(ElementType!Range) == char)){
		dchar lresult;
		if(!(arange.front & 0b_1000_0000)){
			lresult = arange.front;
			arange.popFront;
			return lresult;
		}else if(!(arange.front & 0b_0010_0000)){
			lresult = arange.front & 0b_0001_1111;
			lresult <<= 6;
			arange.popFront;
			lresult |= arange.front & 0b_0011_1111;
			arange.popFront;
			return lresult;
		}else if(!(arange.front & 0b_0001_0000)){
			lresult = arange.front & 0b_0001_1111;
			lresult <<= 6;
			arange.popFront;
			lresult = arange.front & 0b_0001_1111;
			lresult <<= 6;
			arange.popFront;
			lresult |= arange.front & 0b_0011_1111;
			arange.popFront;
			return lresult;
		}else{
			lresult = arange.front & 0b_0001_1111;
			lresult <<= 6;
			arange.popFront;
			lresult = arange.front & 0b_0001_1111;
			lresult <<= 6;
			arange.popFront;
			lresult = arange.front & 0b_0001_1111;
			lresult <<= 6;
			arange.popFront;
			lresult |= arange.front & 0b_0011_1111;
			arange.popFront;
			return lresult;
		}
	}else static if(is(Unqual!(ElementType!Range) == wchar)){
		static assert(false);
	}else static if(is(Unqual!(ElementType!Range) == dchar)){
		lresult = arange.front;
		arange.popFront;
		return lresult;
	}
}

version(none) debug(ctpg) public:

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

	int primary = !"(" addExp !")" / intLit_p;

	None recursive = A $;

	None A = !"a" !A !"a" / !"a";
};

unittest{
	enum ldg = {
		{
			assert(parse!root("5*8+3*20") == 100);
			assert(parse!root("5*(8+3)*20") == 1100);
			if(!__ctfe){
				try{
					parse!root("5*(8+3)20");
				}catch(Exception e){
					assert(e.msg == "1: 8: error EOF is needed");
				}
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
		return true;
	};
	debug(ctpg_ct) static assert(ldg());
	ldg();
}
