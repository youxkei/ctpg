module ctpg.caller;

import std.typecons : Tuple;

alias Caller = Tuple!(size_t, "line", string, "file");
