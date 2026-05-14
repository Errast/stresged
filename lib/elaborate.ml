open Sexplib.Conv
open Raw_syntax

type idx = {index: int} [@@unboxed] [@@deriving sexp_of, eq]

type lvl = {level: int} [@@unboxed] [@@deriving sexp_of, eq]

let lvl_to_idx : cxt:lvl -> lvl -> idx =
 fun ~cxt:{level= cxt} {level} -> {index= cxt - level - 1}

type literal = Bool of bool [@@deriving sexp_of, eq]

type ty_literal = Bool | Universe of universe [@@deriving sexp_of, eq]

type ty =
  | Pi of ty * ty
  | Sigma of ty * ty
  | ModalBoxTy of neg_modality * ty
  | Literal of ty_literal
  | El of term

and term =
  | Var of idx
  | Lambda of term
  | App of term * term
  | Let of term * term
  | Pair of term * term
  | Fst of term
  | Snd of term
  | ModalBox of neg_modality * term
  | ModalUnbox of neg_modality * term
  | Literal of literal
  | Code of ty
[@@deriving sexp_of, eq]

type env =
  | Lock : modality * env -> env
  | Val : val_term * env -> env
  | Nil : env

and 'a closure = {t: 'a; env: env}

and val_term =
  | Lambda of term closure
  | Pair of val_term * val_term
  | Neutral of neutral
  | ModalBox of neg_modality * val_term
  | Literal of literal
  | Code of val_type

and val_type =
  | Pi of val_type * ty closure
  | Sigma of val_type * ty closure
  | ModalBoxTy of neg_modality * val_type
  | Literal of ty_literal
  | El of val_term

and neutral =
  | Var of lvl
  | App of neutral * val_term
  | Fst of neutral
  | Snd of neutral
  | ModalUnbox of neg_modality * neutral

and normal_form = {term: val_term; typ: val_type} [@@deriving sexp_of, eq]

module Env = struct
  type t = env

  let rec nth : idx -> t -> val_term =
   fun i env ->
    match (i.index, env) with
    | 0, Val (tm, _) ->
        tm
    | i, Val (_, env') ->
        nth {index= i - 1} env'
    | _, Lock (_, env') ->
        nth i env'
    | _, _ ->
        failwith "no such variable"

  let push tm env = Val (tm, env)
end

let rec instantiate : 'a 'b. (env -> 'a -> 'b) -> 'a closure -> val_term -> 'b =
 fun eval closure term -> eval (Env.push term closure.env) closure.t

and eval_term : env -> term -> val_term =
 fun env -> function
  | Var idx ->
      Env.nth idx env
  | Lambda body ->
      Lambda {t= body; env}
  | App (lhs, rhs) ->
      let lhs' = eval_term env lhs in
      let rhs' = eval_term env rhs in
      begin match lhs' with
      | Lambda clos ->
          instantiate eval_term clos rhs'
      | Neutral ne ->
          Neutral (App (ne, rhs'))
      | _ ->
          failwith "Not a lambda"
      end
  | Let (bound, body) ->
      eval_term (Env.push (eval_term env bound) env) body
  | Pair (fst, snd) ->
      Pair (eval_term env fst, eval_term env snd)
  | Fst tm ->
    begin match eval_term env tm with
    | Neutral ne ->
        Neutral (Fst ne)
    | _ ->
        failwith "not a pair"
    end
  | Snd tm ->
    begin match eval_term env tm with
    | Neutral ne ->
        Neutral (Snd ne)
    | _ ->
        failwith "not a pair"
    end
  | ModalBox (modality, tm) ->
      ModalBox (modality, eval_term (Lock (neg_adjoint modality, env)) tm)
  | ModalUnbox (modality, tm) ->
    begin match eval_term env tm with
    | ModalBox (mu, tm) when equal_modality mu modality ->
        tm
    | Neutral rhs ->
        Neutral (ModalUnbox (modality, rhs))
    | _ ->
        failwith "not a modal box"
    end
  | Literal l ->
      Literal l
  | Code ty -> (
    match eval_type env ty with El tm -> tm | ty -> Code ty )

and eval_type : env -> ty -> val_type =
 fun env -> function
  | Pi (dom, codom) ->
      Pi (eval_type env dom, {t= codom; env})
  | Sigma (t1, t2) ->
      Sigma (eval_type env t1, {t= t2; env})
  | ModalBoxTy (mu, ty) ->
    begin match eval_type (Lock ((mu :> modality), env)) ty with
    (* Idempotent *)
    | ModalBoxTy (m2, _) as ty when equal_modality mu m2 ->
        ty
    | ty ->
        ModalBoxTy (mu, ty)
    end
  | Literal l ->
      Literal l
  | El tm ->
    begin match eval_term env tm with Code ty -> ty | tm -> El tm
    end

let rec bind_quote :
    'a 'b. (env -> 'a -> 'b) -> (lvl -> 'b -> 'a) -> lvl -> 'a closure -> 'a =
 fun eval quote cxt_size clos ->
  instantiate eval clos (Neutral (Var cxt_size))
  |> quote {level= cxt_size.level + 1}

and quote_term : lvl -> val_term -> term =
 fun cxt_size -> function
  | Lambda clos ->
      Lambda (bind_quote eval_term quote_term cxt_size clos)
  | Pair (fst, snd) ->
      Pair (quote_term cxt_size fst, quote_term cxt_size snd)
  | Neutral ne ->
      quote_neutral cxt_size ne
  | ModalBox (mu, tm) ->
      ModalBox (mu, quote_term cxt_size tm)
  | Literal l ->
      Literal l
  | Code ty ->
      Code (quote_type cxt_size ty)

and quote_type : lvl -> val_type -> ty =
 fun cxt_size -> function
  | Pi (dom, codom) ->
      let dom' = quote_type cxt_size dom in
      let codom' = bind_quote eval_type quote_type cxt_size codom in
      Pi (dom', codom')
  | Sigma (fst, snd) ->
      Sigma
        (quote_type cxt_size fst, bind_quote eval_type quote_type cxt_size snd)
  | ModalBoxTy (mu, ty) ->
      ModalBoxTy (mu, quote_type cxt_size ty)
  | Literal l ->
      Literal l
  | El tm ->
      El (quote_term cxt_size tm)

and quote_neutral : lvl -> neutral -> term =
 fun cxt_size -> function
  | Var l ->
      Var (lvl_to_idx ~cxt:cxt_size l)
  | App (ne, arg) ->
      App (quote_neutral cxt_size ne, quote_term cxt_size arg)
  | Fst ne ->
      Fst (quote_neutral cxt_size ne)
  | Snd ne ->
      Snd (quote_neutral cxt_size ne)
  | ModalUnbox (mu, ne) ->
      ModalUnbox (mu, quote_neutral cxt_size ne)

module Context = struct
  module StringMap = Map.Make (String)

  type t =
    { env: env
    ; vars: (lvl * val_type * modality) StringMap.t
    ; var_size: lvl
    ; mode: mode }

  let empty : mode -> t =
   fun mode -> {env= Nil; vars= StringMap.empty; var_size= {level= 0}; mode}

  let sexp_of_t t : Sexplib.Sexp.t =
    List
      [ List [Atom "env"; sexp_of_env t.env]
      ; List
          [ Atom "vars"
          ; StringMap.to_list t.vars
            |> [%sexp_of: (string * (lvl * val_type * modality)) list] ]
      ; List [Atom "var_size"; sexp_of_lvl t.var_size] ]

  let lookup : t -> mode -> string -> idx * val_type =
    let rec go acc n = function
      | Lock (mu, env) ->
          go (modality_compose mu acc) n env
      | Val (_, _) when n = 0 ->
          acc
      | Val (_, env) ->
          go acc (n - 1) env
      | Nil ->
          failwith "not in env"
    in
    fun cxt mode var ->
      let level, typ, mu = StringMap.find var cxt.vars in
      let index = lvl_to_idx ~cxt:cxt.var_size level in
      if not @@ equal_modality mu (go (`Id mode) index.index cxt.env) then
        failwith "variable not accessible" ;
      (index, typ)

  let define : t -> string -> val_term -> modality -> val_type -> t =
   fun cxt ident value modality typ ->
    { cxt with
      env= Env.push value cxt.env
    ; vars= StringMap.add ident (cxt.var_size, typ, modality) cxt.vars
    ; var_size= {level= cxt.var_size.level + 1} }

  let bind : t -> string -> modality -> val_type -> t * val_term =
   fun cxt ident modality typ ->
    let tm = Neutral (Var cxt.var_size) in
    (define cxt ident tm modality typ, tm)

  (* Corrects the indices for Prod and Arrow *)
  let bind_anonymous : t -> mode -> t =
   fun cxt mode ->
    (* Type doesn't really matter, as it's not accessible *)
    define cxt "" (Neutral (Var cxt.var_size)) (`Id mode) (Literal Bool)

  let lock : t -> modality -> t =
   fun cxt modality -> {cxt with env= Lock (modality, cxt.env)}
end

let rec infer_term : Context.t -> mode -> Raw_syntax.term -> term * val_type =
 fun cxt mode expr ->
  match (mode, expr) with
  | _, Var x ->
      let idx, ty = Context.lookup cxt mode x in
      (Var idx, ty)
  | _, Let (x, rhs, body) ->
      let rhs_tm, rhs_ty = infer_term cxt mode rhs in
      let rhs_tm = eval_term cxt.env rhs_tm in
      infer_term (Context.define cxt x rhs_tm (`Id mode) rhs_ty) mode body
  | _, Lambda (x, Some arg_ty, body) ->
      let arg_ty = infer_type cxt mode arg_ty |> fst |> eval_type cxt.env in
      let body_tm, body_ty =
        infer_term (fst @@ Context.bind cxt x (`Id mode) arg_ty) mode body
      in
      ( Lambda body_tm
      , Pi (arg_ty, {t= quote_type cxt.var_size body_ty; env= cxt.env}) )
  | _, Ap (lhs, rhs) ->
      let lhs_tm, lhs_ty = infer_term cxt mode lhs in
      begin match lhs_ty with
      | Pi (dom, codom) ->
          let rhs = check cxt mode rhs dom in
          ( App (lhs_tm, rhs)
          , instantiate eval_type codom @@ eval_term cxt.env rhs )
      | _ ->
          failwith "not a function application"
      end
  | _, Ascription (tm, ty) ->
      let ty, _ = infer_type cxt mode ty in
      let ty = eval_type cxt.env ty in
      (check cxt mode tm ty, ty)
  | ( Static
    , (Bool | Arrow _ | Pi _ | Prod _ | Sigma _ | Universe _ | ModalBoxTy _) )
    ->
      let ty, u = infer_type cxt mode expr in
      (Code ty, Literal (Universe u))
  | ( Dynamic
    , (Bool | Arrow _ | Pi _ | Prod _ | Sigma _ | Universe _ | ModalBoxTy _) )
    ->
      failwith "mode is not dependent"
  | _, Bool_lit b ->
      (Literal (Bool b), Literal Bool)
  | _, Fst tm ->
    begin match infer_term cxt mode tm with
    | tm, Sigma (ty1, _) ->
        (Fst tm, ty1)
    | _ ->
        failwith "not a prod/sigma"
    end
  | _, Snd tm ->
    begin match infer_term cxt mode tm with
    | tm, Sigma (_, ty2) ->
        (Snd tm, instantiate eval_type ty2 @@ eval_term cxt.env (Fst tm))
    | _ ->
        failwith "not a product/sigma"
    end
  | _, ModalBox ((#neg_modality as mu), tm) ->
      if not @@ equal_mode mode (modality_domain mu) then
        failwith "modes don't match up" ;
      let mu' = neg_adjoint mu in
      let tm', ty' =
        infer_term (Context.lock cxt mu') (modality_codomain mu') tm
      in
      (ModalBox (mu, tm'), ModalBoxTy (mu, ty'))
  | _, ModalBox _ ->
      failwith "invalid modality in box"
  | _, (Pair _ | Lambda _ | ModalUnbox _) ->
      failwith "cannot synthesize"

and infer_type : Context.t -> mode -> Raw_syntax.term -> ty * universe =
 fun cxt mode tm ->
  match (mode, tm) with
  | _, Bool ->
      (Literal Bool, Type)
  | _, Arrow (dom, codom) ->
      let dom_ty, dom_universe = infer_type cxt mode dom in
      let codom_ty, codom_universe =
        infer_type (Context.bind_anonymous cxt mode) mode codom
      in
      (Pi (dom_ty, codom_ty), universe_join dom_universe codom_universe)
  | Static, Pi (x, dom, codom) ->
      let dom_ty, dom_universe = infer_type cxt mode dom in
      let dom_ty' = eval_type cxt.env dom_ty in
      let codom_ty, codom_universe =
        infer_type (fst @@ Context.bind cxt x (`Id mode) dom_ty') mode codom
      in
      (Pi (dom_ty, codom_ty), universe_join dom_universe codom_universe)
  | _, Prod (fst, snd) ->
      let fst_ty, fst_universe = infer_type cxt mode fst in
      let snd_ty, snd_universe =
        infer_type (Context.bind_anonymous cxt mode) mode snd
      in
      (Pi (fst_ty, snd_ty), universe_join fst_universe snd_universe)
  | Static, Sigma (x, first, second) ->
      let fst_ty, fst_universe = infer_type cxt mode first in
      let fst_ty' = eval_type cxt.env fst_ty in
      let snd_ty, snd_universe =
        infer_type (Context.bind cxt x (`Id mode) fst_ty' |> fst) mode second
      in
      (Pi (fst_ty, snd_ty), universe_join fst_universe snd_universe)
  | _, ModalBoxTy (`Lower, ty) ->
      if not @@ equal_mode mode Static then failwith "modality doesn't match" ;
      let ty, _ = infer_type (Context.lock cxt `Lift) Dynamic ty in
      (ModalBoxTy (`Lower, ty), RuntimeType)
  | Dynamic, _ ->
      failwith "Mode is not dependent"
  | Static, _ ->
    begin match infer_term cxt mode tm with
    | tm', Literal (Universe u) ->
        (El tm', u)
    | _ ->
        failwith "not a type"
    end

and check : Context.t -> mode -> Raw_syntax.term -> val_type -> term =
 fun cxt mode expr ty ->
  match expr with
  | Lambda (x, None, body) ->
    begin match ty with
    | Pi (lhs, rhs) ->
        let cxt, var = Context.bind cxt x (`Id mode) lhs in
        let body_ty = instantiate eval_type rhs var in
        Lambda (check cxt mode body body_ty)
    | _ ->
        failwith "not a function type"
    end
  | Pair (lhs, rhs) ->
    begin match ty with
    | Sigma (left_ty, right_ty) ->
        let left_tm = check cxt mode lhs left_ty in
        let right_ty' =
          instantiate eval_type right_ty @@ eval_term cxt.env left_tm
        in
        let right_tm = check cxt mode rhs right_ty' in
        Pair (left_tm, right_tm)
    | _ ->
        failwith "not a product type"
    end
  | _ ->
      let tm, tm_ty = infer_term cxt mode expr in
      if not @@ equal_val_type ty tm_ty then failwith "type doesn't match" ;
      tm
