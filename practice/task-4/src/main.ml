open Printf;;
open Scanf;;

let (ic, oc) = (open_in "input.txt", open_out "output.txt");;

let errstr = ref "";;

let vertex_cnt (a, _) = a;;
let graph_struc (_, b) = b;;

let read_graph = begin
  
  let add_edge v to_list graph = 
    Hashtbl.add graph v to_list in 

  let get_vertex_list () = 
    let x = input_line ic in
    List.map int_of_string (Str.split(Str.regexp "[, \t\n]+") (x)) in 
  
  let graph = Hashtbl.create 255 in 
  let n = get_vertex_list() |> List.hd in 
  
  let rec read_children current_node = 
    try 
      if (current_node <= n) then begin 
        add_edge current_node (get_vertex_list () ) graph;
        read_children (current_node + 1);
      end 
    with _ -> print_endline "hmm"; () in 
  read_children 1;

  (n, graph);

end;;

let topsort (n, graph) = begin 
  let top_sort_list = ref [] in 
  let used = Hashtbl.create 111 in 

  let rec dfs v graph =   
    if not (Hashtbl.mem used v) then begin
      Hashtbl.add used v 1;
      if (Hashtbl.mem graph v) then (List.iter (fun t -> if (t <> v) then dfs t graph else ()) (Hashtbl.find graph v)); 
      top_sort_list := v::!top_sort_list;
      ()    
    end else
      ()
  in for i = 1 to n do dfs i graph done; 
  
  !top_sort_list;
end;;

let graph = read_graph;;
let top_sorted_list = topsort graph;;
let vertex_num = Hashtbl.create 100;;
List.iteri (fun i v -> Hashtbl.add vertex_num v i) top_sorted_list;;
(*
List.iter (fun x -> x |> string_of_int |> (^) " " |> print_endline;) top_sorted_list;;
*)
let mem = Hashtbl.create 100;;

let plusTable = Hashtbl.create 100;;
let productTable = Hashtbl.create 100;;
let implTable = Hashtbl.create 100;;
let relationTable = Hashtbl.create 100;;

let build_reachable v (n, graph) = begin 
  if not (Hashtbl.mem mem v) then begin  
    let res = Hashtbl.create 100 in 
    let rec dfs (v : int) = 
      if not (Hashtbl.mem res v) then begin
        Hashtbl.add res v 1;
        if (Hashtbl.mem graph v) then 
          (List.iter (fun t -> dfs t) (Hashtbl.find graph v));
      end in dfs v;
    Hashtbl.add mem v res;
    Hashtbl.find mem v;
    res;
  end else (Hashtbl.find mem v);
end;;

let find_intersection_list a b (n, graph) = begin
  let hsh1 = build_reachable a (n, graph) in 
  let hsh2 = build_reachable b (n, graph) in 
  let res_list = ref [] in 
  Hashtbl.iter (fun a b -> if (Hashtbl.mem hsh2 a) then res_list := a::!res_list) hsh1;
  !res_list;
end;;


let check_plus (n, graph) vertex_num memRes op = begin
  let find_min lst = begin 
    let res = ref (List.hd lst) in 
    List.iter (fun x -> 
        let new_value = Hashtbl.find vertex_num x in 
        let old_value = Hashtbl.find vertex_num !res in 
        if (new_value < old_value) then res := x
      ) lst;
    !res;
  end in

  let ensure_min lst mn = begin
    let res= ref true in 
    List.iter (fun x -> 
      let x = List.mem x (find_intersection_list mn x (n, graph)) in 
      res := !res && x) lst;
    !res;
  end in 

  let res = ref true in 

  for i = 1 to n do 
    for j = 1 to n do 
      let lst = find_intersection_list i j (n, graph) in 
      if (List.length lst) == 0 then (errstr := (string_of_int i)^op^(string_of_int j); res := !res && false ) else
      let mn = find_min lst in 
      let x = ensure_min lst mn in 
      if not x then 
        errstr := (string_of_int i)^op^(string_of_int j);
      res := !res && x;
      Hashtbl.replace memRes (i, j) mn;
    done;
  done;
  !res;
end;;

let check_product (n, graph) memRes op = begin 
  Hashtbl.clear mem;
  let rev_vertex_num = Hashtbl.create 100 in 
  let rev_graph = Hashtbl.create 100 in 
  for i = 1 to n do Hashtbl.add rev_graph i [] done;
  Hashtbl.iter (fun a b -> 
        List.iter (fun x -> Hashtbl.replace rev_graph x (a::(Hashtbl.find rev_graph x))) b
      ) graph;
  let top_sorted_list = topsort (n, rev_graph) in 
  List.iteri (fun i v -> Hashtbl.add rev_vertex_num v i) top_sorted_list;
  let res = check_plus (n, rev_graph) rev_vertex_num memRes op in 
  Hashtbl.clear mem;
  res;
end;;

let check_destibute (n, graph) memPlus memProduct = begin 
  let res = ref true in 
  for a = 1 to n do
    for b = 1 to n do 
      for c = 1 to n do 
        (* (a + b)c = ac + bc *)
        let sm_a_b = Hashtbl.find memPlus (a, b) in 
        let lhs = Hashtbl.find memProduct (sm_a_b, c) in 
        let p_a_c = Hashtbl.find memProduct (a, c) in 
        let p_b_c = Hashtbl.find memProduct (b, c) in 
        let rhs = Hashtbl.find memPlus (p_a_c, p_b_c) in 
        if (rhs <> lhs) then 
          errstr := (string_of_int c)^"*("^(string_of_int a)^"+"^(string_of_int b)^")"; 
        res := !res && (lhs = rhs);
      done;
    done;
  done;
  !res;
end;;


let check_implementation (n, graph) memProduct vertex_num memRes = begin 
  
  let find_max lst = begin 
    let res = ref (List.hd lst) in 
    List.iter (fun x -> 
        let new_value = Hashtbl.find vertex_num x in 
        let old_value = Hashtbl.find vertex_num !res in 
        if (new_value > old_value) then res := x
      ) lst;
    !res;
  end in
  
  let ensure_max lst mx = begin
    let res= ref true in 
    List.iter (fun x -> res := !res && ((List.mem mx (find_intersection_list mx x (n, graph))))) lst;
    !res;
  end in 
  
  let gres = ref true in 
  for a = 1 to n do
    for b = 1 to n do
      let candidates = ref [] in 
      for c = 1 to n do
        let p = Hashtbl.find memProduct (a, c) in 
        let lhs = Hashtbl.find vertex_num p in 
        let rhs = Hashtbl.find vertex_num b in
        if (((Hashtbl.find relationTable (p, b)) = 1) && (lhs <= rhs)) then candidates := c::(!candidates);
      done;
        if (List.length (!candidates)) = 0 then (errstr := (string_of_int a)^"->"^(string_of_int b); gres := false) else 
        let mx = find_max (!candidates) in 
        let x = ensure_max (!candidates) mx in
        if not x then (errstr := (string_of_int a)^"->"^(string_of_int b); gres := false);
        Hashtbl.replace memRes (a, b) mx;
    done;
  done;
  !gres;
end;;


let check_bool (n, graph) implTable plusTable vertex_num = begin 

  let find_min lst =  
    let res = ref (List.hd lst) in 
    List.iter (fun x -> 
        let new_value = Hashtbl.find vertex_num x in 
        let old_value = Hashtbl.find vertex_num !res in 
        if (new_value < old_value) then res := x
      ) lst;
    !res;
  in
  
  let ensure_min lst mn = 
    let res= ref true in 
    List.iter (fun x -> res := !res && ((List.mem x (find_intersection_list mn x (n, graph))))) lst;
    !res;
  in 

  let find_max lst =  
    let res = ref (List.hd lst) in 
    List.iter (fun x ->
        let new_value = Hashtbl.find vertex_num x in 
        let old_value = Hashtbl.find vertex_num !res in 
        if (new_value > old_value) then res := x
      ) lst;
    !res;
  in
  
  let ensure_max lst mx = 
    let res= ref true in 
    List.iter (fun x -> res := !res && ((List.mem mx (find_intersection_list mx x (n, graph))))) lst;
    !res;
  in 

  
  let lst = ref [] in 
  for i = 1 to n do 
    lst := i::(!lst);
  done;

  let mn = find_min !lst in 
  if not (ensure_min !lst mn) then false
  else (
  let mx = find_max !lst in 
  if not (ensure_max !lst mx) then false
  else (
  let res = ref true in 
  for i = 1 to n do 
    let x = Hashtbl.find implTable (i, mn) in 
    let y = Hashtbl.find plusTable (x, i) in 
    if (y <> mx) then (errstr := (string_of_int i)^"+~"^(string_of_int i); res := false);  
  done;

  !res;))
end;;


let build_relation_table (n, graph) = begin

  for i = 1 to n do
    for j = 1 to n do 
      Hashtbl.add relationTable (i, j) 0;
    done;
  done;

  for i = 1 to n do
    let r = build_reachable i (n, graph) in 
    Hashtbl.iter (fun r _ -> 
      Hashtbl.replace relationTable (r, i) 2;
      Hashtbl.replace relationTable (i, r) 1;
    ) r;
  done;
end;;

build_relation_table graph;;

let plus_ok = check_plus graph vertex_num plusTable "+" in 
  if (plus_ok) then begin 
    let product_ok = check_product graph productTable "*" in 
    if (product_ok) then begin
      let destribute_ok = check_destibute graph plusTable productTable in 
      if (destribute_ok) then begin 
        let implementation_ok = check_implementation graph productTable vertex_num implTable in 
        if (implementation_ok) then begin
          let bool_ok = check_bool graph implTable plusTable vertex_num in 
          if (bool_ok) then begin 
            fprintf oc "Булева алгебра";
          end else begin 
            fprintf oc "Не булева алгебра: %s" (!errstr);
          end
        end else begin 
          fprintf oc "Операция '->' не определена: %s" (!errstr);
        end
      end else begin 
        fprintf oc "Нарушается дистрибутивность: %s" (!errstr);
      end
    end else begin
      fprintf oc "Операция '*' не определена: %s" (!errstr);
    end 
  end else begin 
    fprintf oc "Операция '+' не определена: %s" (!errstr);
  end

