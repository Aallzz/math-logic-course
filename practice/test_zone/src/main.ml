open Tree;;
open Buffer;;
open Printf;;

let remove_blanks = Str.global_replace(Str.regexp "[ \n\r\x0c\t]+") "";;
let header_sep_regexp = (Str.regexp "\\(,\\|\\(|=\\)\\)");;
let bool_of_int i = i <> 0;; 
let strip_last_char str = if str = "" then "" else String.sub str 0 ((String.length str) - 1);; (* oppa kotlin style *)
let string_of_bool_int a = if (a) then "1" else "0";; (* oppa kotlin style *)

let (>>) x f = f x;;

let (ic,oc) = (open_in "input.txt", open_out "output.txt");;
(*                                      PART 0                                 *)

type reason = ModusPonens of int * int 
            | Axiom of int
            | Assumption of int 
            | NoProof ;;

let show (cur_reason:reason)  = match cur_reason with NoProof -> "(Не доказано)"
                           | Assumption id -> "(Предп. "^string_of_int(id)^")"
                           | Axiom id -> "(Сх. акс. "^string_of_int(id)^")"
                           | ModusPonens (id1, id2) -> "(M.P. "^string_of_int(id1)^", "^string_of_int(id2)^")";; 

let (>>) x f = f x;;

let axiom_num stmt = match stmt with Binop(Impl, a1, Binop(Impl, b, a2)) when a1 = a2 -> 1
                   | Binop(Impl, Binop(Impl, a1, b1), Binop(Impl, Binop(Impl, a2, Binop(Impl, b2, c1)),Binop(Impl, a3, c2))) 
                      when a1 = a2 && a2 = a3 && b1 = b2 && c1 = c2 -> 2
                   | Binop(Impl, a1, Binop(Impl, b1, Binop(Conj, a2, b2))) when a1 = a2 && b1 = b2 -> 3
                   | Binop(Impl, Binop(Conj, a1, b1), a2) when a1 = a2 -> 4
                   | Binop(Impl, Binop(Conj, a1, b1), b2) when b1 = b2 -> 5
                   | Binop(Impl, a1, Binop(Disj, a2, b1)) when a1 = a2 -> 6
                   | Binop(Impl, b1, Binop(Disj, a1, b2)) when b1 = b2 -> 7
                   | Binop(Impl, Binop(Impl, a1, q1), Binop(Impl, Binop(Impl, b1, q2), Binop(Impl,Binop(Disj, a2, b2) ,q3)))  
                      when a1 = a2 && b1 = b2 && q1 = q2 && q2 = q3 -> 8
                   | Binop(Impl, Binop(Impl, a1, b1), Binop(Impl, Binop(Impl, a2, Neg(b2)), Neg(a3)))
                      when a1 = a2 && a2 = a3 && b1 = b2 -> 9
                   | Binop(Impl, Neg(Neg(a1)), a2) when a1 = a2 -> 10
                   | _ -> -1;;

let find_in_hashtable hashtable key =  
  try 
    Hashtbl.find hashtable key
  with _ -> -1;;

let assumption_num hshtbl_assm stmt = find_in_hashtable hshtbl_assm stmt;;  
let modusponens_num hshtbl_mp hshtbl_stmt stmt = 
  try 
    let x = Hashtbl.find hshtbl_mp stmt in
      match x with (s, y) -> let z = find_in_hashtable hshtbl_stmt s in
                             if (z = -1) then 
                               (-1, -1)
                             else 
                               (y, z)
  with _ -> (-1, -1);;

let get_reason tree hshtbl_assm hshtbl_mp hshtbl_stmt =
  let axiom = axiom_num tree in 
    let assumption = assumption_num hshtbl_assm tree in 
      let mp = modusponens_num hshtbl_mp hshtbl_stmt tree in  
     if (axiom <> -1) then 
       Axiom axiom
     else if (assumption <> -1) then 
       Assumption assumption
     else if (mp <> (-1, -1)) then
       ModusPonens (fst(mp), snd(mp))
     else NoProof;;

let update_assumption stmt alpha = 
  (* fprintf oc "UPDATE ASSUMPTION\n"; *)
  let result = ref "" in 
    result := String.concat "" [!result; (Printf.sprintf "%s\n" stmt)];
    result := String.concat "" [!result; (sprintf "%s->%s->%s\n" stmt alpha stmt)];
    result := String.concat "" [!result; (sprintf "%s->%s\n" alpha stmt)];
    (!result);;

let update_axiom stmt alpha = 
  (* fprintf oc "UPDATE AXIOM\n"; *)
  let result = ref "" in 
    result := String.concat "" [!result; (sprintf "%s\n" stmt)];
    result := String.concat "" [!result; (sprintf "%s->%s->%s\n" stmt alpha stmt)];
    result := String.concat "" [!result; (sprintf "%s->%s\n" alpha stmt)];
  (!result);;

let find_id_in_hashtable hshtbl_ind pid = 
  try 
    Hashtbl.find hshtbl_ind pid;
  with _ -> "";;

let update_modus_ponens hshtbl_ind stmt id1 id2 alpha = 
  let stmt1 = find_id_in_hashtable hshtbl_ind id2 in
      (* fprintf oc "UPDATE MP\n"; *)
    let result = ref "" in 
        result := String.concat "" [!result; (sprintf "(%s->%s)->((%s->(%s->%s))->(%s->%s))\n" alpha stmt1 alpha stmt1 stmt alpha stmt)];
        result := String.concat "" [!result; (sprintf "(%s->(%s->%s))->(%s->%s)\n" alpha stmt1 stmt alpha stmt)];
        result := String.concat "" [!result; (sprintf "%s->%s\n" alpha stmt)];
    (!result);;

let update_alpha alpha =
  (* fprintf oc "UPDATE ALPHA\n"; *)
  let result = ref "" in 
    result := String.concat "" [!result; (sprintf "(%s->%s->%s)->(%s->(%s->%s)->%s)->(%s->%s)\n" alpha alpha alpha alpha alpha alpha alpha alpha alpha)];
    result := String.concat "" [!result; (sprintf "(%s->%s->%s)\n" alpha alpha alpha)];
    result := String.concat "" [!result; (sprintf "(%s->(%s->%s)->%s)\n" alpha alpha alpha alpha)];
    result := String.concat "" [!result; (sprintf "(%s->(%s->%s)->%s)->(%s->%s)\n" alpha alpha alpha alpha alpha alpha)];
    result := String.concat "" [!result; (sprintf "%s->%s\n" alpha alpha)];
  (!result);;

let rec string_of_tree_canon stmt = 
    let s_op op = match op with Conj -> "&" | Disj -> "|" | Impl -> "->" in
      let buf = create 1000 in
        let rec s_t t = match t with
            | Var v -> add_string buf v
            | Neg t -> add_string buf "(!"; s_t t; add_char buf ')'
            | Binop (op,l,r) -> bprintf buf "("; s_t l; bprintf buf "%s" (s_op op); s_t r; add_char buf ')'
                      in s_t stmt; 
                        contents buf;;
      
let string_of_tree (tree : Tree.tree) = 
    let s_op op = match op with Conj -> "&" | Disj -> "|" | Impl -> "->" in
      let buf = create 1000 in
        let rec s_t t = match t with
            | Var v -> add_string buf v
            | Neg t -> add_string buf "(!"; s_t t; add_char buf ')'
            | Binop (op,l,r) -> bprintf buf "(%s," (s_op op); s_t l; add_char buf ','; s_t r; add_char buf ')'
                      in s_t tree; 
                        contents buf;;

let apply_deduction assumptions element proof_list = 
 let hshtbl_assm = Hashtbl.create 255 in 
  let hshtbl_mp = Hashtbl.create 255 in 
  let hshtbl_stmt = Hashtbl.create 255 in 
  let hshtbl_ind = Hashtbl. create 255 in 
  let result = ref "" in 
  let id = ref 1 in 
  
  let prepare_hshtbl_assm assumption_list =
    let process value = Hashtbl.add hshtbl_assm value !id; incr id in  
      List.iter process assumption_list in 
        prepare_hshtbl_assm assumptions;
        
  id := 1;
  
  let add_statement tree = 
    Hashtbl.add hshtbl_stmt tree !id;
    match tree with Binop(Impl, a, b) -> Hashtbl.add hshtbl_mp b (a, !id); 
    | _ -> () in 

  let process stmt = begin  
    if (stmt <> element) then begin 
      let current_reason = get_reason stmt hshtbl_assm hshtbl_mp hshtbl_stmt in 
        (match current_reason with 
         | Assumption _ -> result := String.concat "" [!result; update_assumption (string_of_tree_canon stmt) (string_of_tree_canon element)]   
         | Axiom _ -> result := String.concat "" [!result; update_axiom (string_of_tree_canon stmt) (string_of_tree_canon element)]
         | ModusPonens (x, y) -> result := String.concat "" [!result; update_modus_ponens hshtbl_ind (string_of_tree_canon stmt) x y (string_of_tree_canon element)]
         | NoProof -> failwith ("Неправильное док-во"^(string_of_int !id)));
    end else begin 
      result := String.concat "" [!result; update_alpha (string_of_tree_canon element)];
    end;
    Hashtbl.add hshtbl_ind !id (string_of_tree_canon stmt);
    add_statement stmt;
    incr(id);
  end in 
    
  List.iter process proof_list;
  let result_string_list = Str.split(Str.regexp "\n") !result in 
    let result_tree_list = ref [] in 
      List.iter (fun value -> result_tree_list := (value >> Lexing.from_string >> Parser.main Lexer.main)::!result_tree_list) result_string_list;
      result_tree_list := List.rev (!result_tree_list);
  (!result_tree_list)
;;


let apply_bash_deduction proof_list =
  let result = List.rev proof_list in 
  match (List.hd result) with 
  | Binop (op, l, r) -> List.rev (r::l::result)
  | _ -> List.rev result;;

(*                                      PART I                                 *)
let variable_size = ref 0;;
let rec build_variable_hashtable hashtable reverse_hashtable tree = 
  match tree with 
  | Var v -> if (not (Hashtbl.mem hashtable tree)) then begin
      Hashtbl.add hashtable tree !variable_size;
      Hashtbl.add reverse_hashtable !variable_size tree;
      incr(variable_size)
    end
  | Neg v -> build_variable_hashtable hashtable reverse_hashtable v
  | Binop (op, l, r) -> build_variable_hashtable hashtable reverse_hashtable l; 
                        build_variable_hashtable hashtable reverse_hashtable r;;

let rec check var_hshtbl var_val_hshtbl tree = 
  match tree with 
  | Var v -> Hashtbl.find var_val_hshtbl tree
  | Neg v -> not (check var_hshtbl var_val_hshtbl v)
  | Binop (op, l, r) -> let value1 = check var_hshtbl var_val_hshtbl l in 
                          let value2 = check var_hshtbl var_val_hshtbl r in 
                            match op with 
                            | Disj -> value1 || value2
                            | Conj -> value1 && value2
                            | Impl-> (not value1) || value2;;

let dump_bfct_var_values = ref (Hashtbl.create 3);;
let brute_force_check_tautology var_hshtbl rev_varhshtbl tree = 
  let result = ref true in 
    let variable_value = Hashtbl.create 255 in 
      let mask = ref 0 in 
        while (!mask < (1 lsl !variable_size)) do 
          for bit = 0 to (!variable_size - 1) do 
            Hashtbl.replace variable_value (Hashtbl.find rev_varhshtbl bit) (bool_of_int(!mask land (1 lsl bit))); 
          done; 
          result := !result && (check var_hshtbl variable_value tree);
          if (not !result) then 
            dump_bfct_var_values := Hashtbl.copy variable_value;
          mask := succ !mask;
        done;
        !result;;


let assumption_count = ref 0 ;;

let build_general_formula_of_string  str =
  let elements = List.rev (Str.split header_sep_regexp (remove_blanks str)) in
    let rec builder lst =
      match lst with 
      | [] -> "" 
      | h::[] -> h
      | h::t -> incr(assumption_count); sprintf "%s->%s" (builder t) "("^h^")"
    in
      builder elements;;

let header_string = build_general_formula_of_string (input_line ic);; (* transfom a,b|-c in a->b->c *)
let hshtbl_var_ind = Hashtbl.create 255;; (* unique variable has its id *)
let hshtable_ind_var = Hashtbl.create 255;; (* rev to prev *)
let header_tree = Parser.main Lexer.main (Lexing.from_string header_string);; (* tree representation of header *)
build_variable_hashtable hshtbl_var_ind hshtable_ind_var header_tree;;
let res = brute_force_check_tautology hshtbl_var_ind hshtable_ind_var header_tree;;

(*                                                    Part II                                                   *)
module StringMap = Map.Make(String);;

(* Methods to load base proofs*)
let get_base_proof base_proof_name = 
  let ic = open_in ("base-proofs/"^base_proof_name^".txt") in 
    let n = in_channel_length ic in 
      let s = create n in 
        add_channel s ic n;
        close_in ic;
        let proof_list = Str.split (Str.regexp "\n") (contents s) in 
          let parse str = str >> Lexing.from_string >> Parser.main Lexer.main in 
              let rec process_stmt lst = match lst with 
                | [] -> [] 
                | h::[] -> (parse h)::[]; 
                | h::t -> (parse h)::(process_stmt t); in 
                (process_stmt proof_list);;

let load_base_proof base_proof_name map =
  StringMap.add base_proof_name (get_base_proof base_proof_name) map;;

let base_proof_names = [
                        "conj11"; "conj10"; "conj01"; "conj00";
                        "disj11"; "disj10"; "disj01"; "disj00";
                        "impl11"; "impl10"; "impl01"; "impl00";
                        "not1"; "not0";
                        "exclude"
];;

let rec load_base_proofs proof_map name_list = match name_list with 
  | [] -> proof_map
  | h::[] -> load_base_proof h proof_map
  | h::t -> load_base_proof h (load_base_proofs proof_map t);;
(* Methods to load base proofs END *)

(* Methods for proof generating *)

let rec substitute_in_scheme scheme stmt_a stmt_b = 
   match scheme with 
   | Var v -> if (v = "A") then 
                stmt_a
              else if (v = "B") then 
                stmt_b 
              else 
                scheme
   | Binop (op, l, r) -> Binop(op, substitute_in_scheme l stmt_a stmt_b, substitute_in_scheme r stmt_a stmt_b)
   | Neg v -> Neg (substitute_in_scheme v stmt_a stmt_b)
;;

let substitute_in_scheme_list scheme_list stmt_a stmt_b = 
  List.map (fun v -> substitute_in_scheme v stmt_a stmt_b) scheme_list;;

let rec substitute_in_scheme_one scheme stmt = 
  match scheme with
  | Var v -> if (v = "A") then 
               stmt
             else
               scheme
  | Binop (op, l, r) -> Binop(op, substitute_in_scheme_one l stmt, substitute_in_scheme_one r stmt)
  | Neg v -> Neg(substitute_in_scheme_one v stmt)
;;

let rec substitute_in_scheme_one_list scheme_list stmt = 
  List.map (fun v -> substitute_in_scheme_one v stmt) scheme_list;;

let concatanate_proofs base_proofs_map op a proofA b proofB stmt_left stmt_right = 
    let (value, concatenator) = match op with 
      | Conj -> let base_proof_scheme = StringMap.find 
                                        ("conj"^(string_of_bool_int a)^(string_of_bool_int b)) 
                                        base_proofs_map in  
                ((a && b), substitute_in_scheme_list base_proof_scheme stmt_left stmt_right)
      | Disj -> let base_proof_scheme = StringMap.find 
                                        ("disj"^(string_of_bool_int a)^(string_of_bool_int b))
                                        base_proofs_map in 
                ((a || b), substitute_in_scheme_list base_proof_scheme stmt_left stmt_right)
      | Impl -> let base_proof_scheme = StringMap.find
                                        ("impl"^(string_of_bool_int a)^(string_of_bool_int b)) 
                                        base_proofs_map in 
                ((not a) || (a && b), substitute_in_scheme_list base_proof_scheme stmt_left stmt_right)
    in
      (value, List.append (List.append proofA proofB) concatenator);;


let rec generate_atom_proof base_proofs_map (stmt : Tree.tree) mask = 
  match stmt with 
  | Var v -> let var_id = Hashtbl.find hshtbl_var_ind stmt in 
               if (mask land (1 lsl var_id) <> 0) then begin
                 (true, [stmt])
                 end else begin 
                 (false, [Neg stmt]) end
  | Binop (op, l, r) -> let (value_left, proof_left) = generate_atom_proof base_proofs_map l mask in 
                          let (value_right, proof_right) = generate_atom_proof base_proofs_map r mask in 
                            concatanate_proofs 
                              base_proofs_map 
                              op 
                              value_left proof_left 
                              value_right proof_right
                              l r
  | Neg v -> let (value, proof) = generate_atom_proof base_proofs_map v mask in 
                  let proof2 = 
                    let base_proof_scheme = StringMap.find ("not"^(string_of_bool_int value)) base_proofs_map in
                      substitute_in_scheme_one_list base_proof_scheme v in 
                  (not value, List.append proof proof2)
;;  

let generate_atom_proofs base_proofs_map (stmt : Tree.tree) = 
  let result = ref [] in 
    let mask = ref 0 in 
      while (!mask < (1 lsl !variable_size)) do
        let (_, atom_proof) = generate_atom_proof base_proofs_map stmt !mask in 
          result := atom_proof::!result;
        incr(mask);
      done;
      result := List.rev !result;
      (!result);;

let rec reduce_assumption base_proofs_map atom_proof_list var_id mask stmt_to_proof = 
  let vid = !variable_size - var_id - 1 in  
 if ((List.length atom_proof_list) <> 0) then
      let h1 = List.hd atom_proof_list in 
        let tail = List.tl atom_proof_list  in 
          let h2 = List.hd tail in 
            let tail_tail = List.tl tail  in 
                let form_assumption_list tbl mask = 
                  let result = ref [] in 
                    result := [];
                    Hashtbl.iter (fun key value -> if (key > vid) then 
                                                      if (mask land (1 lsl (key - vid)) <> 0) then  
                                                        result := value::!result
                                                      else 
                                                        result := (Neg value)::!result) tbl;
                     (!result);
                    in 
                      let element1 = Hashtbl.find hshtable_ind_var vid in 
                        let element1 = if (mask land (1 lsl 0) <> 0) then element1 else (Neg element1) in 
                          let element2 = Hashtbl.find hshtable_ind_var vid in 
                            let element2 = if ((mask + 1) land (1 lsl 0) <> 0) then element2 else (Neg element2) in 
                              let variable = Hashtbl.find hshtable_ind_var vid in 
                              let assm_list1 = form_assumption_list hshtable_ind_var mask in 
                                 let assm_list2 = form_assumption_list hshtable_ind_var (mask + 1) in 
                                   let new_proof1 = apply_deduction assm_list1 element1 h1 in 
                                     let new_proof2 = apply_deduction assm_list2 element2  h2 in 
                                      let base_proof_scheme = StringMap.find "exclude" base_proofs_map in
                                          let proof_with_exclusion = List.append new_proof1 
                                                                        (List.append  
                                                                          new_proof2 
                                                                          (substitute_in_scheme_list base_proof_scheme variable stmt_to_proof)
                                                                        )
                                          in
                                          proof_with_exclusion::(reduce_assumption base_proofs_map tail_tail var_id (mask + 2) stmt_to_proof )  
  else 
    []
;;

let rec merge_proof_lists base_proofs_map atom_proof_list var_id stmt_to_proof = 
  if (var_id = 0) then begin 
    atom_proof_list
  end  else begin
    let reduced_atom_proof_list = (reduce_assumption base_proofs_map atom_proof_list (var_id-1) 0 stmt_to_proof ) in
      merge_proof_lists base_proofs_map reduced_atom_proof_list (var_id - 1) stmt_to_proof;
  end
;;


let generate_proof base_proofs_map (stmt : Tree.tree) = 
  let atom_proof_list = generate_atom_proofs base_proofs_map stmt in
    merge_proof_lists base_proofs_map atom_proof_list !variable_size stmt; 
;; 
(* Methods for proof generating *)
let proof_map = load_base_proofs StringMap.empty base_proof_names;;

let almost_perfect_proof = List.hd (generate_proof proof_map header_tree);;

let rec make_perfect_proof almost_perfect_proof cnt  = 
  if (cnt = 1) then 
    apply_bash_deduction almost_perfect_proof
  else
    make_perfect_proof (apply_bash_deduction almost_perfect_proof) (cnt - 1);;

let perfect_proof = make_perfect_proof almost_perfect_proof !assumption_count;;

if (not res) then begin
  let str = ref "" in 
  let add a b = str := !str ^ (sprintf "%s=%s," (string_of_tree a) (match b with true -> "И" | false -> "Л")) in 
  Hashtbl.iter add !dump_bfct_var_values;
  fprintf oc "Высказывание ложно при %s\n" (strip_last_char !str);
  print_string "ASDFASD";
end else begin 
  List.iter (fun value -> fprintf oc "%s\n" (string_of_tree_canon value)) perfect_proof; 
end;;

close_out oc;;
close_in ic;;



