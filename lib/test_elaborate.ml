let inspect f a = f a ; a

let check ?(mode = Raw_syntax.Static) str =
  ( try
      let syntax = Sexplib.Sexp.of_string str |> Parser.parse_term in
      let term, typ =
        Elaborate.infer_term (Elaborate.Context.empty mode) syntax
      in
      [%message
        ""
          ~(syntax : Raw_syntax.term)
          ~(term : Elaborate.term)
          ~(typ : Elaborate.val_type)]
    with Elaborate.ElaborateExc sexp -> sexp )
  |> Sexplib.Sexp.output_hum Out_channel.stdout

let%expect_test "id" =
  check {|(\ x -> x)|} ;
  [%expect {| ("cannot synthesize" (tm (Lambda x () (Var x))) (mode Static)) |}] ;
  check {|(\ (x : true) -> x)|} ;
  [%expect
    {| ("not a type" (tm' (Literal (Bool true))) (ty' (Literal Bool))) |}] ;
  check {|(\ (x : Bool) -> x)|} ;
  [%expect
    {|
    ((syntax (Lambda x (Bool) (Var x))) (term (Lambda (Var ((index 0)))))
     (typ (Pi (Literal Bool) ((t (Literal Bool)) (env ())))))
    |}] ;
  check {|((\ (x : Bool) -> x) true)|} ;
  [%expect
    {|
    ((syntax (Ap (Lambda x (Bool) (Var x)) (Bool_lit true)))
     (term (App (Lambda (Var ((index 0)))) (Literal (Bool true))))
     (typ (Literal Bool)))
    |}] ;
  check {| (let ((T Bool))
             ((\ (x : T) -> x) true)) |} ;
  [%expect
    {|
    ((syntax (Let T Bool (Ap (Lambda x ((Var T)) (Var x)) (Bool_lit true))))
     (term (App (Lambda (Var ((index 0)))) (Literal (Bool true))))
     (typ (Literal Bool)))
    |}] ;
  check {| (-> Bool Bool) |} ;
  [%expect
    {|
    ((syntax (Arrow Bool Bool)) (term (Code (Pi (Literal Bool) (Literal Bool))))
     (typ (Literal (Universe Type))))
    |}] ;
  check {|(\ (T : Type) -> \ (x : T) -> x)|} ;
  [%expect
    {|
    ((syntax (Lambda T ((Universe Type)) (Lambda x ((Var T)) (Var x))))
     (term (Lambda (Lambda (Var ((index 0))))))
     (typ
      (Pi (Literal (Universe Type))
       ((t (Pi (El (Var ((index 0)))) (El (Var ((index 1)))))) (env ())))))
    |}] ;
  check {|(\ (T : Type) -> \ (x : T) -> T)|} ;
  [%expect
    {|
    ((syntax (Lambda T ((Universe Type)) (Lambda x ((Var T)) (Var T))))
     (term (Lambda (Lambda (Var ((index 1))))))
     (typ
      (Pi (Literal (Universe Type))
       ((t (Pi (El (Var ((index 0)))) (Literal (Universe Type)))) (env ())))))
    |}] ;
  check
    {| (let ((id ((\ (T : Type) -> \ (x : T) -> x) : (-> (T : Type) T T))))
             (id Bool true)) |} ;
  [%expect
    {|
    ((syntax
      (Let id
       (Ascription (Lambda T ((Universe Type)) (Lambda x ((Var T)) (Var x)))
        (Pi T (Universe Type) (Arrow (Var T) (Var T))))
       (Ap (Ap (Var id) Bool) (Bool_lit true))))
     (term
      (App (App (Var ((index 0))) (Code (Literal Bool))) (Literal (Bool true))))
     (typ (Literal Bool)))
    |}]

let%expect_test "quotes" =
  check {|(quote \ (x : Bool) -> x)|} ;
  [%expect
    {|
    ((syntax (ModalBox Lower (Lambda x (Bool) (Var x))))
     (term (ModalBox Lower (Lambda (Var ((index 0))))))
     (typ (ModalBoxTy Lower (Pi (Literal Bool) ((t (Literal Bool)) (env ()))))))
    |}] ;
  check {|(\ (b : lift Bool) -> (quote ((unquote b) : Bool)))|} ;
  [%expect
    {|
    ((syntax
      (Lambda b ((ModalBoxTy Lower Bool))
       (ModalBox Lower (Ascription (ModalUnbox Lower (Var b)) Bool))))
     (term (Lambda (ModalBox Lower (ModalUnbox Lower (Var ((index 0)))))))
     (typ
      (Pi (ModalBoxTy Lower (Literal Bool))
       ((t (ModalBoxTy Lower (Literal Bool))) (env ())))))
    |}]

let%expect_test "sigma" =
  check {|((sigma (x : Bool) (T : Type) T Bool) : Sig)|} ;
  [%expect
    {|
    ((syntax
      (Ascription (Sigma x Bool (Sigma T (Universe Type) (Prod (Var T) Bool)))
       (Universe Sig)))
     (term
      (Code
       (Sigma (Literal Bool)
        (Sigma (Literal (Universe Type))
         (Sigma (El (Var ((index 0)))) (Literal Bool))))))
     (typ (Literal (Universe Sig))))
    |}]

let%expect_test "sigma: fst in scope" =
  check {|(\ (T : Type) -> (sigma (S : Type) T (x : Bool) S))|} ;
  [%expect
    {|
    ((syntax
      (Lambda T ((Universe Type))
       (Sigma S (Universe Type) (Prod (Var T) (Sigma x Bool (Var S))))))
     (term
      (Lambda
       (Code
        (Sigma (Literal (Universe Type))
         (Sigma (El (Var ((index 1))))
          (Sigma (Literal Bool) (El (Var ((index 2))))))))))
     (typ
      (Pi (Literal (Universe Type)) ((t (Literal (Universe Kind))) (env ())))))
    |}]

let%expect_test "pairs" =
  check {|(pair Bool true)|} ;
  [%expect
    {| ("cannot synthesize" (tm (Pair Bool (Bool_lit true))) (mode Static)) |}] ;
  check {|((pair Bool true) : (sigma (T : Type) T))|} ;
  [%expect
    {|
    ((syntax
      (Ascription (Pair Bool (Bool_lit true)) (Sigma T (Universe Type) (Var T))))
     (term (Pair (Code (Literal Bool)) (Literal (Bool true))))
     (typ
      (Sigma (Literal (Universe Type)) ((t (El (Var ((index 0))))) (env ())))))
    |}]

let%expect_test "dynamic sigmas" =
  check {|(lift sigma (T : Type) T)|} ;
  [%expect {| ("mode is not dependent" (tm (Universe Type)) (mode Dynamic)) |}] ;
  check {|(lift sigma Bool (-> Bool Bool) Bool)|} ;
  [%expect
    {|
    ((syntax (ModalBoxTy Lower (Prod Bool (Prod (Arrow Bool Bool) Bool))))
     (term
      (Code
       (ModalBoxTy Lower
        (Sigma (Literal Bool)
         (Sigma (Pi (Literal Bool) (Literal Bool)) (Literal Bool))))))
     (typ (Literal (Universe RuntimeType))))
    |}]

let%expect_test "dynamic pairs" =
  check {|(quote pair true false true)|} ;
  [%expect
    {|
    ((syntax
      (ModalBox Lower
       (Pair (Bool_lit true) (Pair (Bool_lit false) (Bool_lit true)))))
     (term
      (ModalBox Lower
       (Pair (Literal (Bool true))
        (Pair (Literal (Bool false)) (Literal (Bool true))))))
     (typ
      (ModalBoxTy Lower
       (Sigma (Literal Bool)
        ((t (Sigma (Literal Bool) (Literal Bool))) (env ()))))))
    |}]

let%expect_test "universes" =
  check {|(sigma RuntimeType Kind Sig)|} ;
  [%expect
    {|
    ((syntax (Prod (Universe RuntimeType) (Prod (Universe Kind) (Universe Sig))))
     (term
      (Code
       (Sigma (Literal (Universe RuntimeType))
        (Sigma (Literal (Universe Kind)) (Literal (Universe Sig))))))
     (typ (Literal (Universe Sig))))
    |}] ;
  check
    {|(let ((T (lift (-> Bool Bool))))
            ((pair T T T) : (sigma RuntimeType Kind Sig)))|} ;
  [%expect
    {|
    ((syntax
      (Let T (ModalBoxTy Lower (Arrow Bool Bool))
       (Ascription (Pair (Var T) (Pair (Var T) (Var T)))
        (Prod (Universe RuntimeType) (Prod (Universe Kind) (Universe Sig))))))
     (term (Pair (Var ((index 0))) (Pair (Var ((index 0))) (Var ((index 0))))))
     (typ
      (Sigma (Literal (Universe RuntimeType))
       ((t (Sigma (Literal (Universe Kind)) (Literal (Universe Sig))))
        (env
         ((Code
           (ModalBoxTy Lower (Pi (Literal Bool) ((t (Literal Bool)) (env ())))))))))))
    |}]

let%expect_test "alpha_equiv" =
  check
    {|(\ (T : -> (-> Bool Bool) Type) -> \ (t : (T (\ (x : Bool) -> true))) ->
            (t : (T (\ (y : Bool) -> true))) )|} ;
  [%expect
    {|
    ((syntax
      (Lambda T ((Arrow (Arrow Bool Bool) (Universe Type)))
       (Lambda t ((Ap (Var T) (Lambda x (Bool) (Bool_lit true))))
        (Ascription (Var t) (Ap (Var T) (Lambda y (Bool) (Bool_lit true)))))))
     (term (Lambda (Lambda (Var ((index 0))))))
     (typ
      (Pi
       (Pi (Pi (Literal Bool) ((t (Literal Bool)) (env ())))
        ((t (Literal (Universe Type))) (env ())))
       ((t
         (Pi (El (App (Var ((index 0))) (Lambda (Literal (Bool true)))))
          (El (App (Var ((index 1))) (Lambda (Literal (Bool true)))))))
        (env ())))))
    |}] ;
  check
    {|(\ (T : -> (-> Bool Bool) Type) -> \ (t : (T (\ (x : Bool) -> true))) ->
            (t : (T (\ (y : Bool) -> false))) )|} ;
  [%expect
    {|
    ("types don't match" (tm (Var ((index 0))))
     (tm_ty
      (El
       (Neutral
        (App (Var ((level 0)))
         (Lambda ((t (Literal (Bool true))) (env ((Neutral (Var ((level 0))))))))))))
     (ty
      (El
       (Neutral
        (App (Var ((level 0)))
         (Lambda
          ((t (Literal (Bool false)))
           (env ((Neutral (Var ((level 1)))) (Neutral (Var ((level 0)))))))))))))
    |}]

let%expect_test "eta_equiv" =
  check
    {|(\ (f : -> Bool Bool) -> \ (T : -> (-> Bool Bool) Type) -> \ (t : T f) ->
           (t : (T (\ (x : Bool) -> (f x)))))|} ;
  [%expect {|
    ((syntax
      (Lambda f ((Arrow Bool Bool))
       (Lambda T ((Arrow (Arrow Bool Bool) (Universe Type)))
        (Lambda t ((Ap (Var T) (Var f)))
         (Ascription (Var t) (Ap (Var T) (Lambda x (Bool) (Ap (Var f) (Var x)))))))))
     (term (Lambda (Lambda (Lambda (Var ((index 0)))))))
     (typ
      (Pi (Pi (Literal Bool) ((t (Literal Bool)) (env ())))
       ((t
         (Pi (Pi (Pi (Literal Bool) (Literal Bool)) (Literal (Universe Type)))
          (Pi (El (App (Var ((index 0))) (Var ((index 1)))))
           (El
            (App (Var ((index 1)))
             (Lambda (App (Var ((index 3))) (Var ((index 0))))))))))
        (env ())))))
    |}] ;
  check
    {|(\ (f : sigma Bool Bool) -> \ (T : -> (sigma Bool Bool) Type) -> \ (t : T f) ->
           (t : (T (pair (fst f) (snd f)))))|} ;
  [%expect {|
    ((syntax
      (Lambda f ((Prod Bool Bool))
       (Lambda T ((Arrow (Prod Bool Bool) (Universe Type)))
        (Lambda t ((Ap (Var T) (Var f)))
         (Ascription (Var t) (Ap (Var T) (Pair (Fst (Var f)) (Snd (Var f)))))))))
     (term (Lambda (Lambda (Lambda (Var ((index 0)))))))
     (typ
      (Pi (Sigma (Literal Bool) ((t (Literal Bool)) (env ())))
       ((t
         (Pi (Pi (Sigma (Literal Bool) (Literal Bool)) (Literal (Universe Type)))
          (Pi (El (App (Var ((index 0))) (Var ((index 1)))))
           (El
            (App (Var ((index 1)))
             (Pair (Fst (Var ((index 2)))) (Snd (Var ((index 2))))))))))
        (env ())))))
    |}]
