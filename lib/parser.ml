type sexp = Sexplib.Sexp.t

let rec parse_term : sexp -> Raw_syntax.term = function
  | Atom "Bool" ->
      Bool
  | Atom "true" ->
      Bool_lit true
  | Atom "false" ->
      Bool_lit false
  | Atom "Type" ->
      Universe Type
  | Atom "RuntimeType" ->
      Universe RuntimeType
  | Atom var ->
      Var var
  | List sexps ->
      parse_list sexps

and[@warning "-8"] parse_list : sexp list -> Raw_syntax.term = function
  | [xs] ->
      parse_term xs
  | term :: Atom ":" :: typ ->
      Ascription (parse_term term, parse_list typ)
  | Atom "fst" :: tm ->
      Fst (parse_list tm)
  | Atom "snd" :: tm ->
      Snd (parse_list tm)
  | Atom "\\" :: Atom var :: Atom "->" :: body ->
      Lambda (var, parse_list body)
  | Atom "lift" :: typ ->
      ModalBoxTy (`Lower, parse_list typ)
  | Atom "quote" :: term ->
      ModalBox (`Lower, parse_list term)
  | Atom "unquote" :: body ->
      ModalUnbox (`Lower, parse_list body)
  | Atom "->" :: (_ :: _ :: _ as typs) ->
      let (ret_typ :: arg_typs) = List.rev typs in
      List.fold_left
        (fun rhs_typ (lhs_typ : sexp) : Raw_syntax.term ->
          match lhs_typ with
          | List (Atom id :: Atom ":" :: typ) ->
              Pi (id, parse_list typ, rhs_typ)
          | typ ->
              Arrow (parse_term typ, rhs_typ) )
        (parse_term ret_typ) arg_typs
  | Atom "sigma" :: (_ :: _ :: _ as typs) ->
      let (ret_typ :: arg_typs) = List.rev typs in
      List.fold_left
        (fun rhs_typ (lhs_typ : sexp) : Raw_syntax.term ->
          match lhs_typ with
          | List (Atom id :: Atom ":" :: typ) ->
              Sigma (id, parse_list typ, rhs_typ)
          | typ ->
              Pair (parse_term typ, rhs_typ) )
        (parse_term ret_typ) arg_typs
  | Atom "pair" :: fst :: (_ :: _ as rest) ->
      List.fold_left
        (fun acc snd_sexp -> Raw_syntax.Pair (acc, parse_term snd_sexp))
        (parse_term fst) rest
  | Atom "let" :: List bindings :: body ->
      List.fold_right
        (fun (List [Atom lhs; rhs] : sexp) body ->
          Raw_syntax.Let (lhs, parse_term rhs, body) )
        bindings
      @@ parse_list body
  | head :: rest ->
      List.fold_left
        (fun acc arg -> Raw_syntax.Ap (acc, parse_term arg))
        (parse_term head) rest
