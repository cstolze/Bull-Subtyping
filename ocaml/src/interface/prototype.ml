open Parser
open Lexer
open BDdL.BDdL.SubtypeRelation

let rec loop lx =
    try
      Parser.s Lexer.read lx
    with
    | _ -> print_endline "Syntax error"; loop lx

let main () =
  let lx = Lexing.from_channel stdin in
  begin
    print_endline "Enter the first type:";
    let s = loop lx in
    print_endline "Enter the second type:";
    let t = loop lx in
    print_endline (if decide_subtype s t then "true" else "false")
  end

let () = ignore (main ())
