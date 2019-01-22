%{
  open Tree;;
%}
%token <string> VAR
%token LAMBDA POINT 
%token OPEN CLOSE
%token APPLICATION
%token EOF
%nonassoc LAMBDA POINT
%left APPLICATION
%start main
%type <Tree.tree> main
%%
main:
        expr EOF                  { $1 }
expr:
        VAR                       { Var ($1) }
        |OPEN expr CLOSE          { $2 }     
        |LAMBDA VAR POINT expr    { Abstraction ($2, $4) }  
        |expr APPLICATION expr    { Application ($1, $3) } 
