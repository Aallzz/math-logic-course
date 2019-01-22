open Tree;;
open Printf;;
open Buffer;;
open Set;;

let read_file ic  =
  let buf = Buffer.create 10000 in
  try
    while true do
      let line = input_line ic in
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

let read_tree ic = begin
  let prepare str =
    let str = Str.global_replace (Str.regexp "(") " (" str in
    let str = Str.global_replace (Str.regexp ")") ") " str in
    let str = Str.global_replace (Str.regexp "\\\\") " \\\\" str in
  	String.trim str in

  let line = prepare (read_file ic) in
  Parser.main Lexer.main (Lexing.from_string line)
end;;

module M = Map.Make(String);;

let index_by_de_Bruijn expression = begin
  let rec go expression current_height bound_vars = match expression with 
    | Var v when (M.mem v bound_vars) -> Var (string_of_int (current_height - M.find v bound_vars - 1))
    | Var v -> Var v
    | Abstraction (v, e) -> Abstraction(v, go e (succ current_height) (M.add v current_height bound_vars))
    | Application (e1, e2) -> Application(go e1 current_height bound_vars, go e2 current_height bound_vars)
  in go expression 0 M.empty
end;;

exception E of string;;

let is_int s = begin
  try ignore (int_of_string s); true
  with _ -> false
end;;

let _mp = Hashtbl.create 100;;

let beta_reduct expression = begin

  let rec update_link e e1_height height = match e with 
    | Var v when (is_int v) -> let h = int_of_string v in 
                                if (h <= height - 1) then
                                  Var v
                                else
                                  Var (string_of_int ((int_of_string v) + e1_height))
    | Var v -> Var v
    | Abstraction (v, e) -> Abstraction(v, update_link e e1_height (succ height))
    | Application (e1, e2) -> Application(update_link e1 e1_height height, update_link e2 e1_height height)
  in 
  let reduct e1 e2 = match e1 with  
    | Abstraction(v, exp) -> 
      let rec go expression height = match expression with 
        | Var v when (v = (string_of_int height)) -> update_link e2 height 0
        | Var v when (is_int v && int_of_string v > height) -> Var (string_of_int ((int_of_string v) - 1))
        | Var v -> Var v
        | Abstraction (v, e) -> Abstraction(v, go e (succ height))
        | Application (e1, e2) -> Application(go e1 height, go e2 height)
      in 
      (go exp 0, true)
    | _ -> raise (E "First expression is expected to be an Abstraction")
  in 
  let rec find_beta_redex expression = 
    match expression with 
    | Application (e1, e2) -> (
                                match e1 with
                                  | Abstraction (v, e) -> reduct e1 e2
                                  | _ -> let left = find_beta_redex e1 in
                                          if snd left then 
                                            (Application(fst left, e2), true) 
                                          else
                                            let right = find_beta_redex e2 in 
                                            (Application(e1, fst right), snd right) 
                              )
    | Abstraction (v, e) -> let res = find_beta_redex e in 
                              (Abstraction(v, fst res), snd res)
    | Var v -> (Var v, false) 
  in 
  find_beta_redex expression 
end;;

let normalize_de_Bruijn  expression = begin
  let rec go expression = 
    let res = beta_reduct expression in 
    if (snd res) then go (fst res) else fst res 
  in go expression
end;;

module S = Set.Make(String);;

let update_bound_vars expression = begin

  let update_var v st = 
    let rec update v st = 
      if (S.mem v st) then 
        update (v^"'") st 
      else 
        (v, S.add v st)
    in update v st
  in 

  let rec go expression height = match expression with 
    | Var v when (v = (string_of_int height)) -> (expression, S.empty)
    | Var v -> (expression, S.add v S.empty)
    | Abstraction (v, e) -> let (new_e, st) = go e (succ height) in 
                                let up = update_var v st in 
                                (Abstraction(fst up, new_e), snd up) 
    | Application (e1, e2) -> let (new_e1, st1) = go e1 height in 
                              let (new_e2, st2) = go e2 height in 
                              (Application(new_e1, new_e2), S.union st1 st2)
  in fst (go expression (-1))
end;;

let unidex_by_de_Bruijn expression = begin
  let rec go expression height bound_vars = match expression with 
    | Var v when (is_int v) -> Var (M.find (string_of_int (height - (int_of_string v) - 1)) bound_vars)
    | Var v -> Var v
    | Abstraction (v, e) -> Abstraction(v, go e (succ height) (M.add (string_of_int height) v bound_vars))
    | Application (e1, e2) -> Application(go e1 height bound_vars, go e2 height bound_vars)
  in go expression 0 M.empty
end;;

let normalize expression = begin 
  unidex_by_de_Bruijn @@ update_bound_vars @@ normalize_de_Bruijn @@ index_by_de_Bruijn expression 
end;;

let main () = begin
  let expression = read_tree stdin in 
  print_endline (string_of_tree (normalize expression))
end;;

main();;

