%{
    open BDdL.BDdL

    (* Hash function *)
    let djb2 s = let rec foo n b
                   = try foo (n+1) ((Char.code (String.get s n))
                                    + 33*b) with
                     | Invalid_argument _ -> b
                 in foo 0 5381

%}

%token EOL
%token OPENP
%token CLOSP
%token ARROW
%token SAND
%token SOR
%token OMEGA
%token <string> ID
%token EOF

%start s
%type <BDdL.BDdL.term> s

%%

s:
    | term EOL { $1 }

term:
    | term2 ARROW term { Arrow($1,$3) } /* arrow is right-to-left */
    | term2 { $1 }
    ;

term2:
    | term3 SOR term2 { Union($1,$3) } /* union is right-to-left */
    | term3 { $1 }
    ;

term3:
    | term4 SAND term3 { Inter($1,$3) } /* inter is right-to-left */
    | term4 { $1 }
    ;

term4:
    | OPENP term CLOSP { $2 } /* highest precedence */
    | ID { Var (djb2 $1) }
    | OMEGA { Omega }
    ;
