type mode = Basic | Dependent [@@deriving sexp, eq]

type modality = Runtime | Lift | LiftRuntime [@@deriving sexp, eq]

let domain = function Runtime | Lift | LiftRuntime -> Basic

let codomain = function Runtime -> Basic | Lift | LiftRuntime -> Dependent

exception IllegalCompose of modality * modality

let compose lhs rhs =
  match (lhs, rhs) with
  | Runtime, Runtime ->
      Runtime
  | Lift, Runtime ->
      LiftRuntime
  | _, _ ->
      raise @@ IllegalCompose (lhs, rhs)
