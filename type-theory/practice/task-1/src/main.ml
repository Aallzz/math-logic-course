open Tree;;
open Printf;;
open Buffer;;

let read_file() =
  let buf = Buffer.create 10000 in
  try
    while true do
      let line = input_line stdin in
      Buffer.add_string buf line;
      Buffer.add_char buf '\n';
    done; assert false
  with End_of_file ->
    Buffer.contents buf
;;

let string_of_tree tree = begin 
  let buf = create (1048576 + 1000) in 
  let rec go t = match t with 
    | Var v -> add_string buf v
    | Abstraction (v, expr) -> add_string buf ("(\\"^v^"."); go expr; add_string buf ")" 
    | Application (e1, e2) -> add_string buf "("; go e1; add_string buf " "; go e2; add_string buf ")"
  in go tree;
  contents buf;
end;;

let main () = begin 
  let prepare str = 
    let str = Str.global_replace (Str.regexp "(") " (" str in 
    let str = Str.global_replace (Str.regexp ")") ") " str in 
    let str = Str.global_replace (Str.regexp "\\\\") " \\\\" str in 
  	String.trim str in  

  let line = prepare (read_file()) in
  let expr = Parser.main Lexer.main (Lexing.from_string line) in 
  fprintf stdout "%s" (string_of_tree expr);
end;;

main();;
