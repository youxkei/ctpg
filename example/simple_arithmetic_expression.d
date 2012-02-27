// Written in the D programming language.

/**
 * Example of parsing simple arithmetic expession.
 */

import ctpg;

mixin generateParsers!q{
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
};

void main(){
    enum dg ={
        assert(parse!root("5*8+3*20") == 100);
        assert(parse!root("5*(8+3)*20") == 1100);
        try{
            parse!root("5*(8+3)20");
        }catch(Exception e){
            assert(e.msg == "1: 8: error EOF is needed");
        } 
        return true;
    };
    static assert(dg());
    dg();
}

