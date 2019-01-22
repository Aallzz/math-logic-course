{
open Parser
}

let variable = ['a' - 'z'] + ['a' - 'z' '0' - '9' '\'']*
let ss = [' ' '\t' '\n' '\r']

rule main = parse
        | variable as v   { VAR(v) }
        | '\\'ss*         { LAMBDA }
        | ss*'.'ss*       { POINT }
        | "("ss*          { OPEN }
        | ss*")"          { CLOSE }
        | ss+             { APPLICATION } 
        | ss*eof          { EOF }  



