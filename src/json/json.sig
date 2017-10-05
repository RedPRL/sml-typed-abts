signature ABT_JSON =
sig
  structure Abt : ABT

  structure NameEnv : DICT where type key = string

  type env = Abt.metavariable NameEnv.dict * Abt.variable NameEnv.dict
  type ctx = Abt.metactx * Abt.varctx

  val encode : Abt.abt -> Json.json_value
  val decode : env -> ctx -> Json.json_value -> Abt.abt

  exception DecodeAbt of string
end

signature ABT_JSON_KIT =
sig
  structure Abt : ABT

  val encodeSort : Abt.sort -> Json.json_value
  val decodeSort : Json.json_value -> Abt.sort option

  val encodeOperator : Abt.O.t -> Json.json_value
  val decodeOperator : Json.json_value -> Abt.O.t option
end
