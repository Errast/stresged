open Sexplib.Conv
open Raw_syntax

exception ElaborateExc of Sexplib.Sexp.t

let error sexp = raise @@ ElaborateExc sexp

type idx = {index: int} [@@unboxed] [@@deriving sexp_of, eq]

type lvl = {level: int} [@@unboxed] [@@deriving sexp_of, eq]

let lvl_to_idx : cxt_size:int -> lvl -> idx =
 fun ~cxt_size {level} -> {index= cxt_size - level - 1}

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

type env = val_term list

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

  let nth {index} env = List.nth env index

  let push = List.cons

  let length = List.length

  let bind env =
    let var = Neutral (Var {level= length env}) in
    (var :: env, var)
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
      ModalBox (modality, eval_term env tm)
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
    begin match eval_type env ty with
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
    'a 'b. (env -> 'a -> 'b) -> (int -> 'b -> 'a) -> int -> 'a closure -> 'a =
 fun eval quote cxt_size clos ->
  instantiate eval clos (Neutral (Var {level= cxt_size})) |> quote (cxt_size + 1)

and quote_term : int -> val_term -> term =
 fun cxt_size v ->
  match v with
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

and quote_type : int -> val_type -> ty =
 fun cxt_size v ->
  match v with
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

and quote_neutral : int -> neutral -> term =
 fun cxt_size n ->
  match n with
  | Var l ->
      Var (lvl_to_idx ~cxt_size l)
  | App (ne, arg) ->
      App (quote_neutral cxt_size ne, quote_term cxt_size arg)
  | Fst ne ->
      Fst (quote_neutral cxt_size ne)
  | Snd ne ->
      Snd (quote_neutral cxt_size ne)
  | ModalUnbox (mu, ne) ->
      ModalUnbox (mu, quote_neutral cxt_size ne)

(* untyped conversion *)
let rec def_eq_ty : Env.t -> val_type -> val_type -> bool =
 fun env ty1 ty2 ->
  match (ty1, ty2) with
  | Pi (dom1, cod1), Pi (dom2, cod2) | Sigma (dom1, cod1), Sigma (dom2, cod2) ->
      let env', var = Env.bind env in
      def_eq_ty env dom1 dom2
      && def_eq_ty env'
           (instantiate eval_type cod1 var)
           (instantiate eval_type cod2 var)
  | ModalBoxTy (mu1, ty1), ModalBoxTy (mu2, ty2) ->
      equal_modality mu1 mu2 && def_eq_ty env ty1 ty2
  | Literal l1, Literal l2 ->
      equal_ty_literal l1 l2
  | El code1, El code2 ->
      def_eq_term env code1 code2
  | _ ->
      false

and def_eq_term : Env.t -> val_term -> val_term -> bool =
 fun env tm1 tm2 ->
  match (tm1, tm2) with
  | Lambda body1, Lambda body2 ->
      let env', var = Env.bind env in
      def_eq_term env'
        (instantiate eval_term body1 var)
        (instantiate eval_term body2 var)
  | Lambda body, Neutral ne | Neutral ne, Lambda body ->
      let env', var = Env.bind env in
      def_eq_term env' (instantiate eval_term body var) (Neutral (App (ne, var)))
  | Pair (fst1, snd1), Pair (fst2, snd2) ->
      def_eq_term env fst1 fst2 && def_eq_term env snd1 snd2
  | Pair (fst, snd), Neutral ne | Neutral ne, Pair (fst, snd) ->
      def_eq_term env fst (Neutral (Fst ne))
      && def_eq_term env snd (Neutral (Snd ne))
  | Neutral ne1, Neutral ne2 ->
      def_eq_neutral env ne1 ne2
  | ModalBox (mu1, tm1), ModalBox (mu2, tm2) ->
      equal_modality mu1 mu2 && def_eq_term env tm1 tm2
  | Literal l1, Literal l2 ->
      equal_literal l1 l2
  | Code ty1, Code ty2 ->
      def_eq_ty env ty1 ty2
  | _, _ ->
      false

and def_eq_neutral : Env.t -> neutral -> neutral -> bool =
 fun env ne1 ne2 ->
  match (ne1, ne2) with
  | Var var1, Var var2 ->
      var1.level = var2.level
  | App (ne1, v1), App (ne2, v2) ->
      def_eq_neutral env ne1 ne2 && def_eq_term env v1 v2
  | Fst ne1, Fst ne2 | Snd ne1, Snd ne2 ->
      def_eq_neutral env ne1 ne2
  | ModalUnbox (mu1, ne1), ModalUnbox (mu2, ne2) ->
      (* it wouldn't have typechecked if the mu's aren't equal right? *)
      equal_modality mu1 mu2 && def_eq_neutral env ne1 ne2
  | _ ->
      false

module Context : sig
  type lock_list

  type t = private
    { env: env
    ; vars: (lvl * val_type * modality) Map.Make(String).t
    ; var_size: int
    ; mode: mode
    ; locks: lock_list }
  [@@deriving sexp_of]

  val empty : mode -> t

  val lookup : t -> string -> idx * val_type

  val define : t -> string -> val_term -> modality -> val_type -> t

  val bind : t -> string -> ?modality:modality -> val_type -> t * val_term

  val bind_anonymous : t -> t

  val lock : t -> modality -> t
end = struct
  module StringMap = Map.Make (String)

  (* level of the first variable in front of the lock , list must be decreasing *)
  type lock_list = (modality * lvl) list

  type t =
    { env: env
    ; vars: (lvl * val_type * modality) StringMap.t
    ; var_size: int
    ; mode: mode
    ; locks: lock_list }

  let empty : mode -> t =
   fun mode -> {env= []; vars= StringMap.empty; var_size= 0; mode; locks= []}

  let sexp_of_t t : Sexplib.Sexp.t =
    List
      [ List [Atom "env"; sexp_of_env t.env]
      ; List
          [ Atom "vars"
          ; StringMap.to_list t.vars
            |> [%sexp_of: (string * (lvl * val_type * modality)) list] ]
      ; List [Atom "locks"; [%sexp_of: (modality * lvl) list] t.locks]
      ; List [Atom "var_size"; sexp_of_int t.var_size] ]

  let lookup : t -> string -> idx * val_type =
    let rec go : modality -> lvl -> lock_list -> modality =
     fun acc n -> function
       | (_, {level}) :: _ when level <= n.level ->
           acc
       | [] ->
           acc
       | (mu, _) :: locks ->
           go (modality_compose mu acc) n locks
    in
    fun cxt var ->
      let level, typ, mu =
        match StringMap.find_opt var cxt.vars with
        | Some p ->
            p
        | None ->
            error [%message "var not in env" ~(var : string)]
      in
      let index = lvl_to_idx ~cxt_size:cxt.var_size level in
      let locks = go (`Id cxt.mode) level cxt.locks in
      if not @@ equal_modality mu locks then
        error
          [%message
            "var not accessible"
              ~(var : string)
              ~(mu : Raw_syntax.modality)
              ~(locks : Raw_syntax.modality)] ;
      (index, typ)

  let define : t -> string -> val_term -> modality -> val_type -> t =
   fun cxt ident value modality typ ->
    { cxt with
      env= Env.push value cxt.env
    ; vars= StringMap.add ident ({level= cxt.var_size}, typ, modality) cxt.vars
    ; var_size= cxt.var_size + 1 }

  let bind : t -> string -> ?modality:modality -> val_type -> t * val_term =
   fun cxt ident ?(modality = `Id cxt.mode) typ ->
    let tm = Neutral (Var {level= cxt.var_size}) in
    (define cxt ident tm modality typ, tm)

  (* Corrects the indices for Prod and Arrow *)
  let bind_anonymous : t -> t =
   fun cxt ->
    (* Type doesn't really matter, as it's not accessible *)
    bind cxt "" (Literal Bool) |> fst

  let lock : t -> modality -> t =
   fun cxt modality ->
    assert (equal_mode cxt.mode @@ modality_codomain modality) ;
    { cxt with
      locks= (modality, {level= cxt.var_size}) :: cxt.locks
    ; mode= modality_domain modality }
end

let rec infer_term : Context.t -> Raw_syntax.term -> term * val_type =
 fun cxt expr ->
  match (cxt.mode, expr) with
  | _, Var x ->
      let idx, ty = Context.lookup cxt x in
      (Var idx, ty)
  | _, Let (x, rhs, body) ->
      let rhs_tm, rhs_ty = infer_term cxt rhs in
      let rhs_tm = eval_term cxt.env rhs_tm in
      infer_term (Context.define cxt x rhs_tm (`Id cxt.mode) rhs_ty) body
  | _, Lambda (x, Some arg_ty, body) ->
      let arg_ty = infer_type cxt arg_ty |> fst |> eval_type cxt.env in
      let cxt', _ = Context.bind cxt x arg_ty in
      let body_tm, body_ty = infer_term cxt' body in
      ( Lambda body_tm
      , Pi (arg_ty, {t= quote_type cxt'.var_size body_ty; env= cxt.env}) )
  | _, Ap (lhs, rhs) ->
      let lhs_tm, lhs_ty = infer_term cxt lhs in
      begin match lhs_ty with
      | Pi (dom, codom) ->
          let rhs = check cxt rhs dom in
          ( App (lhs_tm, rhs)
          , instantiate eval_type codom @@ eval_term cxt.env rhs )
      | _ ->
          error
            [%message
              "not a function in application"
                ~(lhs_tm : term)
                ~(lhs_ty : val_type)]
      end
  | _, Ascription (tm, ty) ->
      let ty, _ = infer_type cxt ty in
      let ty = eval_type cxt.env ty in
      (check cxt tm ty, ty)
  | ( Static
    , (Bool | Arrow _ | Pi _ | Prod _ | Sigma _ | Universe _ | ModalBoxTy _) )
    ->
      let ty, u = infer_type cxt expr in
      (Code ty, Literal (Universe u))
  | ( Dynamic
    , (Bool | Arrow _ | Pi _ | Prod _ | Sigma _ | Universe _ | ModalBoxTy _) )
    ->
      error
        [%message "mode is not dependent" ~mode:(cxt.mode : Raw_syntax.mode)]
  | _, Bool_lit b ->
      (Literal (Bool b), Literal Bool)
  | _, Fst tm ->
    begin match infer_term cxt tm with
    | tm, Sigma (ty1, _) ->
        (Fst tm, ty1)
    | tm, ty ->
        error [%message "not a product type" ~(tm : term) ~(ty : val_type)]
    end
  | _, Snd tm ->
    begin match infer_term cxt tm with
    | tm, Sigma (_, ty2) ->
        (Snd tm, instantiate eval_type ty2 @@ eval_term cxt.env (Fst tm))
    | tm, ty ->
        error [%message "not a product type" ~(tm : term) ~(ty : val_type)]
    end
  | mode, ModalBox ((#neg_modality as mu), tm) ->
      if not @@ equal_mode mode (modality_domain mu) then
        error
          [%message
            "modes don't match up"
              ~(expr : Raw_syntax.term)
              ~(mu : Raw_syntax.modality)
              ~(mode : Raw_syntax.mode)] ;
      let mu' = neg_adjoint mu in
      let tm', ty' = infer_term (Context.lock cxt mu') tm in
      (ModalBox (mu, tm'), ModalBoxTy (mu, ty'))
  | _, ModalBox (mu, _) ->
      error [%message "invalid modality in box" ~(mu : Raw_syntax.modality)]
  | mode, ModalUnbox ((#neg_modality as mu), tm) ->
      if not @@ equal_mode mode (modality_codomain mu) then
        error
          [%message
            "modes don't match up"
              ~(expr : Raw_syntax.term)
              ~(mu : Raw_syntax.modality)
              ~(mode : Raw_syntax.mode)] ;
      let mu' = mu in
      let tm', ty' = infer_term (Context.lock cxt mu') tm in
      begin match ty' with
      | ModalBoxTy (mu2, ty_inner) when equal_modality mu2 mu ->
          (ModalUnbox (mu, tm'), ty_inner)
      | _ ->
          error
            [%message "cannot unbox" (expr : Raw_syntax.term) (ty' : val_type)]
      end
  | Dynamic, Pair (tm1, tm2) ->
      let tm1', ty1 = infer_term cxt tm1 in
      let tm2', ty2 = infer_term cxt tm2 in
      (* Kind of a hack, we lie about there being another variable so the context
       looks the same as a dependent sum. Essentially the val/lvl version of bind_anonymous? *)
      ( Pair (tm1', tm2')
      , Sigma (ty1, {t= quote_type (cxt.var_size + 1) ty2; env= cxt.env}) )
  | mode, ((Pair _ | Lambda _ | ModalUnbox _) as tm) ->
      error
        [%message
          "cannot synthesize" ~(tm : Raw_syntax.term) (mode : Raw_syntax.mode)]

and infer_type : Context.t -> Raw_syntax.term -> ty * universe =
 fun cxt tm ->
  match (cxt.mode, tm) with
  | Static, Universe u ->
      (Literal (Universe u), universe_inc u)
  | _, Bool ->
      (Literal Bool, Type)
  | _, Arrow (dom, codom) | Dynamic, Pi (_, dom, codom) ->
      let dom_ty, dom_universe = infer_type cxt dom in
      let codom_ty, codom_universe =
        infer_type (Context.bind_anonymous cxt) codom
      in
      (Pi (dom_ty, codom_ty), universe_join dom_universe codom_universe)
  | Static, Pi (x, dom, codom) ->
      let dom_ty, dom_universe = infer_type cxt dom in
      let dom_ty' = eval_type cxt.env dom_ty in
      let codom_ty, codom_universe =
        infer_type (fst @@ Context.bind cxt x dom_ty') codom
      in
      (Pi (dom_ty, codom_ty), universe_join dom_universe codom_universe)
  | _, Prod (fst, snd) | Dynamic, Sigma (_, fst, snd) ->
      let fst_ty, fst_universe = infer_type cxt fst in
      let snd_ty, snd_universe = infer_type (Context.bind_anonymous cxt) snd in
      (Sigma (fst_ty, snd_ty), universe_join fst_universe snd_universe)
  | Static, Sigma (x, first, second) ->
      let fst_ty, fst_universe = infer_type cxt first in
      let fst_ty' = eval_type cxt.env fst_ty in
      let snd_ty, snd_universe =
        infer_type (Context.bind cxt x fst_ty' |> fst) second
      in
      (Sigma (fst_ty, snd_ty), universe_join fst_universe snd_universe)
  | mode, ModalBoxTy ((`Lower as mu), ty) ->
      if not @@ equal_mode mode Static then
        error
          [%message
            "modality doesn't match"
              ~(mu : Raw_syntax.modality)
              ~(mode : Raw_syntax.mode)] ;
      let ty, _ = infer_type (Context.lock cxt `Lift) ty in
      (ModalBoxTy (`Lower, ty), RuntimeType)
  | mode, ModalBoxTy _ ->
      error [%message "invald modal box" ~(tm : Raw_syntax.term) ~(mode : mode)]
  | (Dynamic as mode), _ ->
      error
        [%message
          "mode is not dependent" ~(tm : Raw_syntax.term) ~(mode : mode)]
  | Static, _ ->
    begin match infer_term cxt tm with
    | tm', Literal (Universe u) ->
        (El tm', u)
    | tm', ty' ->
        error [%message "not a type" ~(tm' : term) ~(ty' : val_type)]
    end

and check : Context.t -> Raw_syntax.term -> val_type -> term =
 fun cxt expr ty ->
  match expr with
  | Lambda (x, ann, body) ->
    begin match ty with
    | Pi (lhs, rhs) ->
        begin match ann with
        | None ->
            ()
        | Some ann_ty ->
            let ann_ty = infer_type cxt ann_ty |> fst |> eval_type cxt.env in
            if not @@ def_eq_ty cxt.env ann_ty lhs then
              error
                [%message
                  "types don't match up" ~(ann_ty : val_type) ~(lhs : val_type)]
        end ;
        let cxt, var = Context.bind cxt x lhs in
        let body_ty = instantiate eval_type rhs var in
        Lambda (check cxt body body_ty)
    | _ ->
        error
          [%message
            "not a function type" ~(ty : val_type) ~(expr : Raw_syntax.term)]
    end
  | Pair (lhs, rhs) ->
    begin match ty with
    | Sigma (left_ty, right_ty) ->
        let left_tm = check cxt lhs left_ty in
        let right_ty' =
          instantiate eval_type right_ty @@ eval_term cxt.env left_tm
        in
        let right_tm = check cxt rhs right_ty' in
        Pair (left_tm, right_tm)
    | _ ->
        error
          [%message
            "not a product type" ~(ty : val_type) ~(expr : Raw_syntax.term)]
    end
  | _ ->
      let tm, tm_ty = infer_term cxt expr in
      begin match (tm_ty, ty) with
      (* Remove this to remove cumulativity *)
      | Literal (Universe tm_u), Literal (Universe u) ->
          if universe_leq tm_u u then tm
          else
            error
              [%message
                "universes don't match"
                  ~(tm : term)
                  ~(tm_ty : val_type)
                  ~(ty : val_type)]
      | _ ->
          if not @@ def_eq_ty cxt.env ty tm_ty then
            error
              [%message
                "types don't match"
                  ~(tm : term)
                  ~(tm_ty : val_type)
                  ~(ty : val_type)] ;
          tm
      end
