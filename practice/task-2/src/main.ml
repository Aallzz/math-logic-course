open Tree;;
open Buffer;;
open Printf;;

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

let remove_blanks = Str.global_replace(Str.regexp "[ \n\r\x0c\t]+") "";;

let (ic,oc) = (open_in "input.txt", open_out "output.txt");;

let string_of_tree tree = 
    let s_op op = match op with Conj -> "&" | Disj -> "|" | Impl -> "->" in
      let buf = create 1000 in
        let rec s_t t = match t with
            | Var v -> add_string buf v
            | Neg t -> add_string buf "(!"; s_t t; add_char buf ')'
            | Binop (op,l,r) -> bprintf buf "(%s," (s_op op); s_t l; add_char buf ','; s_t r; add_char buf ')'
                      in s_t tree; 
                        contents buf;;

let hshtbl_assm = Hashtbl.create 255;;
let hshtbl_mp = Hashtbl.create 255;;
let hshtbl_stmt = Hashtbl.create 255;;
let hshtbl_ind = Hashtbl. create 255;;

let id = ref 1;;

let find_in_hashtable hashtable key =  
  try 
    Hashtbl.find hashtable key
  with _ -> -1;;

let assumption_num stmt = find_in_hashtable hshtbl_assm stmt;;  
let modusponens_num stmt = 
  try 
    let x = Hashtbl.find hshtbl_mp stmt in
      match x with (s, y) -> let z = find_in_hashtable hshtbl_stmt s in
                             if (z = -1) then 
                               (-1, -1)
                             else 
                               (y, z)
  with _ -> (-1, -1);;

let get_reason tree =
  let axiom = axiom_num tree in 
    let assumption = assumption_num tree in 
      let mp = modusponens_num tree in  
     if (axiom <> -1) then 
       Axiom axiom
     else if (assumption <> -1) then 
       Assumption assumption
     else if (mp <> (-1, -1)) then
       ModusPonens (fst(mp), snd(mp))
     else NoProof;;

let add_statement tree = 
  Hashtbl.add hshtbl_stmt tree !id;
  match tree with Binop(Impl, a, b) -> Hashtbl.add hshtbl_mp b (a, !id); 
  | _ -> ();;

let alpha = ref "";;

let given = input_line ic in 
  let given = remove_blanks given in 
    let elements = Str.split (Str.regexp "\\(,\\|\\(|-\\)\\)") given in 
      let rec prepare_hshtbl_assm e = match e with 
               | [] -> ()
               | h::[] -> fprintf oc "|-%s->%s\n" !alpha ("("^h^")") 
               | h::t::[] -> alpha := "("^h^")"; 
                 Hashtbl.add hshtbl_assm (h >> Lexing.from_string >> Parser.main Lexer.main) !id;
                 prepare_hshtbl_assm (t::[])
               | h::t -> Hashtbl.add hshtbl_assm (h >> Lexing.from_string >> Parser.main Lexer.main) !id;
                 incr id;
                 let sep = match t with h::_::[] -> ""
                  | h::[] -> ""
                  | _ -> "," in 
                 fprintf oc "%s%s" h sep;
                 prepare_hshtbl_assm t in
      prepare_hshtbl_assm elements;;

id := 1;;

let update_assumption stmt = 
  (* fprintf oc "UPDATE ASSUMPTION\n"; *)
  fprintf oc "%s\n" stmt;
  fprintf oc "%s->%s->%s\n" stmt !alpha stmt;
  fprintf oc "%s->%s\n" !alpha stmt;;

let update_axiom stmt = 
  (* fprintf oc "UPDATE AXIOM\n"; *)
  fprintf oc "%s\n" stmt;
  fprintf oc "%s->%s->%s\n" stmt !alpha stmt;
  fprintf oc "%s->%s\n" !alpha stmt;;

let find_id_in_hashtable pid = 
  try 
    Hashtbl.find hshtbl_ind pid;
  with _ -> "";;

let update_modus_ponens stmt id1 id2  = 
  let stmt1 = find_id_in_hashtable id2 in
      (* fprintf oc "UPDATE MP\n"; *)
      fprintf oc "(%s->%s)->((%s->(%s->%s))->(%s->%s))\n" !alpha stmt1 !alpha stmt1 stmt !alpha stmt;
      fprintf oc "(%s->(%s->%s))->(%s->%s)\n" !alpha stmt1 stmt !alpha stmt;
      fprintf oc "%s->%s\n" !alpha stmt;;

let update_alpha () =
  (* fprintf oc "UPDATE ALPHA\n"; *)
  fprintf oc "(%s->%s->%s)->(%s->(%s->%s)->%s)->(%s->%s)\n" !alpha !alpha !alpha !alpha !alpha !alpha !alpha !alpha !alpha;
  fprintf oc "(%s->%s->%s)\n" !alpha !alpha !alpha;
  fprintf oc "(%s->(%s->%s)->%s)\n" !alpha !alpha !alpha !alpha;
  fprintf oc "(%s->(%s->%s)->%s)->(%s->%s)\n" !alpha !alpha !alpha !alpha !alpha !alpha;
  fprintf oc "%s->%s\n" !alpha !alpha;;

let alpha_tree = !alpha >> Lexing.from_string >> Parser.main Lexer.main;;

try
  while (true); do 
    let current_line = input_line ic in
        let current_line = remove_blanks current_line in
        if (current_line <> "") then
          let current_line = "("^current_line^")" in 
            let smth = Parser.main Lexer.main (Lexing.from_string current_line) in  
                if (smth <> alpha_tree) then begin 
                 let current_reason = smth >> get_reason in 
                 (match current_reason with Assumption _ -> update_assumption current_line
                   | Axiom _ -> update_axiom current_line
                   | ModusPonens (x, y) -> update_modus_ponens current_line x y
                   | NoProof -> failwith "Неправильное док-во");
                end 
                else begin  
                  update_alpha();
                end;
                  (* fprintf oc "(%d) %s %s\n" !id current_line (smth >> get_reason >> show); *)
                  Hashtbl.add hshtbl_ind !id current_line;
                  add_statement smth;
                  incr id;  
  done;
with e ->
  (* fprintf oc "%s\n" (Printexc.to_string e); *)
  close_out oc;
  close_in ic;
