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

(*-------------------------------------------------------*)

exception E;;
module SSet = Set.Make(String);;

let get_free_variables tree = begin
  let rec go tree = match tree with
    | Var v -> SSet.singleton v
    | Application (e1, e2) -> let s1 = go e1 in
                              let s2 = go e2 in
                              SSet.union s1 s2
    | Abstraction (v, e) -> let s = go e in
                            SSet.remove v s
  in
  go tree
end;;

let get_variables tree = begin
  let rec go tree = match tree with
    | Var v -> SSet.singleton v
    | Application (e1, e2) -> let s1 = go e1 in
                              let s2 = go e2 in
                              SSet.union s1 s2
    | Abstraction (v, e) -> let s = go e in
                            SSet.add v s
  in
  go tree
end;;

type _type = Type of string | Impl of _type * _type;;

(*-- http://web.cs.ucla.edu/~palsberg/course/cs239/reading/wand87.pdf --*)
let build_types_equations tree = begin

  let cur_type_id = ref 0 in
  let eq = ref [] in

  let get_new_type() =
    let cur_id = !cur_type_id in
    incr(cur_type_id);
    Type("t" ^ string_of_int(cur_id));
  in

  let get_variable_type assumptions variable =
    if (Hashtbl.mem assumptions variable) then
      Hashtbl.find assumptions variable
    else
      let x = get_new_type() in
      Hashtbl.add assumptions variable x;
      x
  in

  let var_type_map = Hashtbl.create 100 in

  let initialize_type_assertion() =
    let free_variables = get_free_variables tree in
    let assumptions : (tree, _type) Hashtbl.t = Hashtbl.create 100 in
    List.iter (fun x -> Hashtbl.add assumptions (Var x) (get_new_type());
                    Hashtbl.replace var_type_map (Var x) (Hashtbl.find assumptions (Var x))) (SSet.elements free_variables);
    (assumptions, tree, (get_new_type()))
  in

  let group = (initialize_type_assertion()) in
  let type_id_tr = ref [] in 

  let rec generate group = match group with
    | (assumptions, Var v, tp) -> type_id_tr := tp::!type_id_tr;
    | (assumptions, Application (e1, e2), tp) -> let new_assumptions1 = Hashtbl.copy assumptions in 
                                                 let new_assumptions2 = Hashtbl.copy assumptions in 
                                                 let fnt = get_variable_type new_assumptions1 e1 in
                                                 let nt = get_variable_type new_assumptions2 e2 in
                                                 type_id_tr := tp::!type_id_tr;
                                                 eq := (fnt, Impl (nt, tp))::!eq;
                                                 (generate (new_assumptions1, e1, fnt));
                                                 (generate (new_assumptions2, e2, nt));
    | (assumptions, Abstraction (v, e), tp) -> let new_assumptions = Hashtbl.copy assumptions in
                                               type_id_tr := tp::!type_id_tr;
                                               let nt1 = get_variable_type assumptions (Var v) in
                                               type_id_tr := nt1::!type_id_tr;
                                               let nt2 = get_variable_type assumptions e in
                                               Hashtbl.replace new_assumptions (Var v) nt1;
                                               eq := (tp, Impl(nt1, nt2))::!eq;
                                               generate(new_assumptions, e, nt2);
  in
  generate group;
  (!eq, (List.rev !type_id_tr), var_type_map)
end;;

(*-- http://web.cs.ucla.edu/~palsberg/course/cs239/reading/types.pdf -- *)

let string_of_type tp = begin
  let buf = create 100 in
  let rec go tp = match tp with
    | Type s -> add_string buf s;
    | Impl (t1, t2) -> add_string buf "("; go t1; add_string buf " -> " ; go t2; add_string buf ")"
  in
  go tp;
  contents buf;
end;;

let string_of_equations eqs = begin
  let buf = create 100 in
  List.iter (fun(rhs, lhs) -> add_string buf (string_of_type rhs); add_string buf "="; add_string buf (string_of_type lhs); add_string buf "\n") eqs;
  contents buf;
end;;

let unificate eqs = begin
  let rec substitute old_type new_type type_value = match type_value with
             | Type tp when (tp = old_type) -> new_type
             | Type tp -> type_value
             | Impl (ltp, rtp) -> Impl (substitute old_type new_type ltp,  substitute old_type new_type rtp)
  in

  let substitute_all old_type new_type eqs =
    List.map (substitute old_type new_type) eqs
  in

  let rec get_lhs_list lst = match lst with
    | [] -> []
    | (a, b)::tail -> a::(get_lhs_list tail)
  in

  let rec get_rhs_list lst = match lst with
    | [] -> []
    | (a, b)::tail -> b::(get_rhs_list tail)
  in

  let rec combine_eqs rhs_list lhs_list = match (rhs_list, lhs_list) with
      | ([], []) -> []
      | (a::a_tail, b::b_tail) -> (a, b)::(combine_eqs a_tail b_tail)
      | _ -> []    (* should do something bad *)
  in

  let rec contains_type element = function
        | Type s when (s = element) -> true
        | Impl (e1, e2) -> let x = (contains_type element e1) in
                           let y = (contains_type element e2) in
                           (x || y)
        | _ -> false
  in

  let rec substitute_all_eqs old_type new_type eqs =
      let lhs = (substitute_all old_type new_type (get_lhs_list eqs)) in
      let rhs = (substitute_all old_type new_type (get_rhs_list eqs)) in
      (combine_eqs lhs rhs)
  in

  let sigma = ref eqs in

  let rec solve (eq : (_type * _type) list) = match eq with
    | [] -> ()
    | (Type s, Type t)::tail when (s = t) ->
            sigma := List.filter ((<>) (Type s, Type t)) !sigma;
            solve tail
    | (Type s, expr)::tail when (not (contains_type s (expr))) ->
            sigma := List.filter ((<>) (Type s, expr)) !sigma;
            sigma := substitute_all_eqs s (expr) !sigma;
            sigma := (Type s, expr)::!sigma;
            sigma := List.sort_uniq compare !sigma;
            solve (substitute_all_eqs s (expr) tail)
    | (Type s, Impl(t1, t2))::tail -> raise E
    | (expr, Type t)::tail when (not (contains_type t (expr))) ->
            sigma := List.filter ((<>) (expr, Type t)) !sigma;
            sigma := substitute_all_eqs t expr !sigma;
            sigma := (Type t, expr)::!sigma;
            sigma := List.sort_uniq compare !sigma;
            solve (substitute_all_eqs t (expr) tail)
    | (Impl (s1, s2), Type t)::tail -> raise E
    | (Type s, Type t)::tail ->
            (*sigma := List.filter ((<>) (Type s, Type t)) !sigma;
            sigma := substitute_all_eqs s (Type t) !sigma;
            sigma := (Type s, Type t)::!sigma;
            sigma := List.sort_uniq compare !sigma;
            solve (substitute_all_eqs s (Type t) tail)
            *)
            solve tail;
    | (Impl (s1, s2), Impl(t1, t2))::tail ->
            sigma := List.filter ((<>) (Impl (s1, s2), Impl (t1, t2))) !sigma;
            sigma := (s1, t1)::(s2, t2)::!sigma;
            sigma := List.sort_uniq compare !sigma;
            solve tail;
    in

  let rec same_lists a b = match a, b with 
    | [], [] -> true 
    | x::xs, y::ys -> ((same_lists xs ys) && (x = y))
    | _ -> false
  in

  let rec calc old =
    solve !sigma;  
    sigma := List.sort_uniq compare !sigma;
    if (not (same_lists !sigma old)) then 
    calc !sigma
  in

  calc !sigma;
  !sigma;

end;;


let build_type_inference tps var_type_map type_id_tr tree = begin

  let type_id_tr = ref type_id_tr in 

  let tp_tp_map = Hashtbl.create 100 in

  let rec build_tp_tp_map tps = match tps with
    | [] -> ()
    | (Type v, t)::tail -> Hashtbl.add tp_tp_map (Type v) t; build_tp_tp_map tail;
    | (Impl (_, _), _)::tail ->  raise E
  in
  build_tp_tp_map tps;

  let assumption_variables = List.map (fun x -> Var x) (SSet.elements (get_free_variables tree)) in
  let infer_list = ref [] in

  let get_var_type var =
    let cur_type = Hashtbl.find var_type_map var in
    if (Hashtbl.mem tp_tp_map cur_type) then Hashtbl.find tp_tp_map cur_type
    else cur_type
  in

  let string_of_assumption_vars assumption_variables =
    let buf = create 1000 in

    let add_var_type x =
      add_string buf (string_of_tree x);
      add_string buf " : ";
      add_string buf (string_of_type (get_var_type x));
    in

    let rec go lst = match lst with
      | [] -> ()
      | x::[] -> add_var_type x; add_string buf " ";
      | x::xs -> add_var_type x; add_string buf ", "; go xs
    in
    go assumption_variables;
    contents buf;
  in 

  let rec infer tree assumption_variables depth =
   
   let fst = List.hd !type_id_tr in 
   type_id_tr := List.tl !type_id_tr;
   Hashtbl.add var_type_map tree fst;
   infer_list := (depth ^ (string_of_assumption_vars (List.rev assumption_variables)) ^ "|- " ^(string_of_tree tree) ^ " : " ^ (string_of_type (get_var_type tree)))::!infer_list;
  
    match tree with
	  | Var v -> infer_list := ((List.hd !infer_list) ^ " [rule #1]")::(List.tl !infer_list);
                 Hashtbl.remove var_type_map tree;
      | Application (e1, e2) -> infer_list := ((List.hd !infer_list) ^ " [rule #2]")::(List.tl !infer_list);
                                infer e1 assumption_variables (depth ^ "*   ");
                                infer e2 assumption_variables (depth ^ "*   ");
                                Hashtbl.remove var_type_map tree;
      | Abstraction (v, e) -> infer_list := ((List.hd !infer_list) ^ " [rule #3]")::(List.tl !infer_list);
                              let fst = List.hd !type_id_tr in 
                              type_id_tr := List.tl !type_id_tr;
                              Hashtbl.add var_type_map (Var v) fst;
                              infer e ((Var v)::assumption_variables) (depth ^ "*   ");
                              Hashtbl.remove var_type_map tree;
  in
  infer tree assumption_variables "";
  assert ((List.length !type_id_tr) == 0); 
  !infer_list
end;;

let main () = begin
  let tree = read_tree stdin in
  try
    let (type_equations, type_id_tr, var_type_map) = build_types_equations tree in
    let ffff = unificate type_equations in
    let lst = (build_type_inference ffff var_type_map type_id_tr tree) in
    List.iter (fun x -> print_endline x) (List.rev lst);
  with E -> print_endline "Expression has no type";
end;;


main();;

