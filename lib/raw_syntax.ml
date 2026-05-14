open Sexplib.Conv

type ident = string [@@deriving sexp]

type universe = RuntimeType | Type | Kind | Sig [@@deriving sexp, eq]

let universe_inc = function RuntimeType | Type -> Kind | Kind | Sig -> Sig

let universe_join =
 fun lhs rhs ->
  match (lhs, rhs) with
  | Sig, _ | _, Sig ->
      Sig
  | Kind, _ | _, Kind ->
      Kind
  | _, _ ->
      Type

type mode = Dynamic | Static [@@deriving sexp, eq]

type neg_modality = [`Lower] [@@deriving eq, sexp]

type modality = [`Id of mode | `Lift | neg_modality] [@@deriving sexp, eq]

let equal_modality : [< modality] -> [< modality] -> bool =
 fun lhs rhs -> equal_modality (lhs :> modality) (rhs :> modality)

let neg_adjoint : neg_modality -> modality = function `Lower -> `Lift

let modality_domain : [< modality] -> mode = function
  | `Id m ->
      m
  | `Lift ->
      Dynamic
  | `Lower ->
      Static

let modality_codomain : [< modality] -> mode = function
  | `Id m ->
      m
  | `Lift ->
      Static
  | `Lower ->
      Dynamic

let modality_compose lhs rhs =
  match ((lhs :> modality), (rhs :> modality)) with
  | `Id m, other when equal_mode m @@ modality_codomain other ->
      other
  | other, `Id m when equal_mode m @@ modality_domain other ->
      other
  (* close enough *)
  | `Lift, `Lower ->
      `Id Static
  | `Lower, `Lift ->
      `Id Dynamic
  | _ ->
      failwith "invalid compose"

type term =
  | Var of ident
  | Let of ident * term * term
  | Lambda of ident * term option * term
  | Ap of term * term
  | Arrow of term * term
  | Pi of ident * term * term
  | Ascription of term * term
  | Bool
  | Bool_lit of bool
  | Sigma of ident * term * term
  | Prod of term * term
  | Pair of term * term
  | Fst of term
  | Snd of term
  | ModalBoxTy of modality * term
  | ModalBox of modality * term
  | ModalUnbox of modality * term
  | Universe of universe
[@@deriving sexp]

type decl = Def of {name: string; term: term; typ: term; mode: mode}
[@@deriving sexp]
