let check_parse str =
  Sexplib.Sexp.of_string str |> Parser.parse_term |> Raw_syntax.sexp_of_term
  |> Sexplib.Sexp.to_string_hum |> print_endline

let%expect_test "var" = check_parse {| x |} ; [%expect {| (Var x) |}]

let%expect_test "app" =
  check_parse {| (((a (b : c c)) d e) f) |} ;
  [%expect
    {|
    (Ap
     (Ap (Ap (Ap (Var a) (Ascription (Var b) (Ap (Var c) (Var c)))) (Var d))
      (Var e))
     (Var f))
    |}]

let%expect_test "chained" =
  check_parse {|(-> (a : (b c)) (c d) (e : f) g) |} ;
  [%expect
    {|
    (Pi a (Ap (Var b) (Var c))
     (Arrow (Ap (Var c) (Var d)) (Pi e (Var f) (Var g))))
    |}] ;
  check_parse {|(sigma (a : (b c)) (c d) (e : f) g) |} ;
  [%expect
    {|
    (Sigma a (Ap (Var b) (Var c))
     (Prod (Ap (Var c) (Var d)) (Sigma e (Var f) (Var g))))
    |}] ;
  check_parse {|(pair (a : (b c)) (c d) (e : f) g) |};
  [%expect {|
    (Pair (Ascription (Var a) (Ap (Var b) (Var c)))
     (Pair (Ap (Var c) (Var d)) (Pair (Ascription (Var e) (Var f)) (Var g))))
    |}]

let%expect_test "literals" =
  check_parse {| Type |} ;
  check_parse {| RuntimeType |} ;
  check_parse {| true |} ;
  check_parse {| Bool |} ;
  check_parse {| false |} ;
  [%expect {|
    (Universe Type)
    (Universe RuntimeType)
    (Bool_lit true)
    Bool
    (Bool_lit false)
    |}]

let%expect_test "modifiers" =
  check_parse {| (fst fst pair a b) |} ;
  check_parse {| (snd fst pair a b) |} ;
  check_parse {| (quote unquote a b c) |} ;
  check_parse {| (lift -> a b) |};
  [%expect {|
    (Fst (Fst (Pair (Var a) (Var b))))
    (Snd (Fst (Pair (Var a) (Var b))))
    (ModalBox Lower (ModalUnbox Lower (Ap (Ap (Var a) (Var b)) (Var c))))
    (ModalBoxTy Lower (Arrow (Var a) (Var b)))
    |}]

let%expect_test "let" = check_parse {| (let ((x (a b c)) (y (b c d))) (+ x y)) |};
  [%expect {|
    (Let x (Ap (Ap (Var a) (Var b)) (Var c))
     (Let y (Ap (Ap (Var b) (Var c)) (Var d)) (Ap (Ap (Var +) (Var x)) (Var y))))
    |}]
