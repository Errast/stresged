let check_elab ~mode str = 
Sexplib.Sexp.of_string str |> Parser.parse_term |> Elaborate.infer_type (Elaborate.Context.empty mode) mode
