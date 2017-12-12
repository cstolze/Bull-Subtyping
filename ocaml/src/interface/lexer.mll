{open Parser}

rule read = parse
   | [' ' '\t'] { read lexbuf}
   | [ '\n' ] { EOL }
   | '(' { OPENP }
   | ')' { CLOSP }
   | "->" { ARROW }
   | '&' { SAND }
   | '|' { SOR }
   | '$' { OMEGA }
   | ['A' - 'Z' 'a' - 'z' '0' - '9' '_' '\'']+ as x { ID x }
   | eof {EOF}
