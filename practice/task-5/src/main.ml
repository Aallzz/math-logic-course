open Tree;;
open Printf;;
open Buffer;;

let (ic, oc) = (open_in "input.txt", open_out "output.txt");; 

let generate_tree mask = begin
  
  let tree = Hashtbl.create 6 in 
  let curbit = ref (0) in 
  let curvertex = ref 0 in 

  let add_child v t = 
    let children = if not (Hashtbl.mem tree v) then [] else Hashtbl.find tree v in 
    Hashtbl.replace tree v (t::children); 
  in 

  let rec dfs v =
    while (mask land (1 lsl !curbit) <> 0) do 
      incr curbit;
      (incr curvertex; add_child v !curvertex; dfs !curvertex)
    done;
    incr curbit;
  in dfs 0;
  
  tree;

end;;

let next_mask mask = begin 
  
  let cur = ref mask in 
  let found = ref false in 

  let check mask = 
    let cnt = ref 0 in 
    let cur = ref mask in
    let res = ref true in 

    for i = 1 to 8 do  
      if (!cur mod 2 = 1) then incr(cnt) else decr(cnt);
      if (!cnt < 0) then res := false;
      cur := !cur / 2;
    done;

    (!res && !cnt = 0);
  in 

  while (not !found) do
    cur := !cur + 1;
    if (check !cur) then found := true; 
  done;

  !cur;
end;;

let varidx = Hashtbl.create 3;;
let curidx = ref 0;; 

let rec map_var_idx expression = match expression with 
    | Var v -> if not (Hashtbl.mem varidx v) then (Hashtbl.add varidx v !curidx; incr(curidx))
    | Neg v -> map_var_idx v;
    | Binop (op, l, r) -> map_var_idx l; map_var_idx r;
;; 

let process_tree tree expression = begin 
  
  let distr_mask mask = 
    let rmask = ref mask in 
    let msks = Hashtbl.create 5 in 
    for i = 0 to 4 do
      Hashtbl.add msks i (!rmask land ((1 lsl 3) - 1));
      rmask := !rmask / 8;
    done;
    msks;
  in 

  let check_kripke_variable tree mask_forced = 
    let res = ref true in 
    let rec dfs v mask = 
      let curmask = Hashtbl.find mask_forced v in
      if ((mask land curmask) = mask) then 
        List.iter (fun t -> dfs t curmask) (if (Hashtbl.mem tree v) then Hashtbl.find tree v else [])
      else
        res := false;
    in dfs 0 0; 
    !res;
  in

  let rec check_expression vertex mask_forced expression = match expression with 
    | Var v -> let varnum = Hashtbl.find varidx v in 
               ((Hashtbl.find mask_forced vertex) land (1 lsl varnum)) <> 0
    | Neg v -> let res = ref true in 
               let rec dfs curv =
                 if (check_expression curv mask_forced v) then res := false; 
                 List.iter(fun t -> dfs t) (if (Hashtbl.mem tree curv) then Hashtbl.find tree curv else [])
               in dfs vertex;
               !res;
    | Binop (op, l, r) -> let a = check_expression vertex mask_forced l in 
                          let b = check_expression vertex mask_forced r in 
                          match op with 
                          | Conj -> (a && b);
                          | Disj -> (a || b);
                          | Impl -> let res = ref true in 
                              let rec dfs curv = 
                                if ((check_expression curv mask_forced l) && (not(check_expression curv mask_forced r))) then res := false;
                                List.iter(fun t -> dfs t) (if (Hashtbl.mem tree curv) then Hashtbl.find tree curv else [])
                              in dfs vertex;
                              !res;

  in

  let build_heyting tree mask_forced = 
    let set = Hashtbl.create 5 in
    
    let add v t = 
      let c = if not (Hashtbl.mem set v) then [] else Hashtbl.find set v in 
      Hashtbl.replace set v (t::c); 
    in
    
    let merge_lists lst1 lst2 = 
      let res = ref lst1 in 
      let rec unite l = match l with 
        | [] -> [] 
        | h::t -> if (not (List.mem h !res)) then res := h::!res; unite t;
      in unite lst2;
      !res;
    in 
    
    (* lst2 is subset of lst1 *) 
    let is_subset lst1 lst2 = 
      let res = ref true in 
      List.iter(fun x -> res := !res && (List.mem x lst1)) lst2;
      !res;
    in 
    
    let rec dfs v st =
      add st v;
      List.iter (fun t -> dfs t st) (if (Hashtbl.mem tree v) then Hashtbl.find tree v else [])
    in 
    
    for i = 0 to 4 do 
      dfs i i;
    done;
   
    let res = Hashtbl.create 10 in
    let sz = ref 0 in 
    
    let check_entry lst = 
      let rs = ref true in 
      Hashtbl.iter (fun a b -> if((is_subset lst b) && (is_subset b lst)) then rs := false) res;
      !rs;
    in 

    for i = 0 to ((1 lsl 5) - 1) do
      let cur = ref [] in 
      for j = 0 to 4 do 
        if (i land (1 lsl j) <> 0) then cur := merge_lists !cur (Hashtbl.find set j);
      done;
      if (check_entry !cur) then (Hashtbl.add res !sz !cur; incr sz);
    done;
  
    let graph = Hashtbl.create 30 in 
    let add_vertex v t = 
      let children = if not (Hashtbl.mem graph v) then [] else Hashtbl.find graph v in 
      Hashtbl.replace graph v (t::children); 
    in
    for i = 0 to (!sz - 1) do 
      for j = 0 to (!sz - 1) do 
        if (is_subset (Hashtbl.find res i) (Hashtbl.find res j)) then add_vertex j i;
      done;
    done;

    let varvertex = Hashtbl.create 3 in
    
    Hashtbl.iter (fun lt curvr ->
      Hashtbl.iter (fun a _ -> 
          let lst = Hashtbl.find res a in (*worlds for vertex a*)
          let inall = ref true in 
          List.iter (fun x -> if ((Hashtbl.find mask_forced x) land (1 lsl curvr) == 0) then inall := false) lst; 
          if (!inall) then begin 
            if not (Hashtbl.mem varvertex lt) then 
              Hashtbl.add varvertex lt a
            else begin
              if (List.length (Hashtbl.find res (Hashtbl.find varvertex lt))) < List.length lst then 
                Hashtbl.replace varvertex lt a;
            end
          end;
        ) graph;
    ) varidx;


    (graph, !sz, varvertex);
  in 

  let print_graph (graph, sz, _) =
    fprintf oc "%d\n" sz;
    for i = 0 to (sz - 1) do 
      if not (Hashtbl.mem graph i) then 
        fprintf oc "%d" (i+1)
      else
        List.iter (fun x -> fprintf oc "%d " (x+1)) (Hashtbl.find graph i);
      fprintf oc "\n";
    done;
  in 

  let print_vars (_, _, vrs) = 
    let cnt = ref (Hashtbl.length vrs) in 
    Hashtbl.iter (fun a b -> fprintf oc "%s=%d" a (b+1); decr(cnt); if (!cnt <> 0) then fprintf oc ",") vrs;
  in 

  let mask = ref 0 in
  while (!mask < (1 lsl 15)) do 
    let mask_forced = distr_mask !mask in 
    if (check_kripke_variable tree mask_forced) then begin    
      if not (check_expression 0 mask_forced expression) then begin 
        let lattice = build_heyting tree mask_forced in
        print_graph lattice;
        print_vars lattice;
        exit 0;
      end;
    end;
    incr(mask);
  done;
  
end;;

let print_tree tree = begin
  
  Hashtbl.iter(fun a b ->
    print_endline ((string_of_int a)^": ");
    List.iter(fun x -> printf "%d " x) b;
    print_endline ""; ) tree;
end;;

let main() = begin
 
  let expression_line = input_line ic in 
  let expression = Parser.main Lexer.main (Lexing.from_string expression_line) in

  map_var_idx expression;
  
   let curmask = ref (next_mask 0) in 
   while (!curmask < (1 lsl 8)) do  
     
    let tree = generate_tree !curmask in
    process_tree tree expression; 
    curmask := next_mask !curmask;
  done; 
  
  fprintf oc "Формула общезначима";
end;;

main();
