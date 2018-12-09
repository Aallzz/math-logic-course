type var = string;;

type tree = 
  | Application of tree * tree
  | Abstraction of var * tree
  | Var of var;;
