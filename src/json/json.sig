signature ABT_JSON =
sig
  structure Abt : ABT

  structure NameEnv : DICT where type key = string

  type env = Abt.metavariable NameEnv.dict * Abt.symbol NameEnv.dict * Abt.variable NameEnv.dict
  type ctx = Abt.metactx * Abt.symctx * Abt.varctx

  val encode : Abt.abt -> Json.json_value
  val decode : env -> ctx -> Json.json_value -> Abt.abt

  exception DecodeAbt of string
end

signature ABT_JSON_KIT =
sig
  structure Abt : ABT where type 'a O.Ar.Vl.Sp.t = 'a list

  val encodeParamSort : Abt.psort -> Json.json_value
  val decodeParamSort : Json.json_value -> Abt.psort option

  val encodeSort : Abt.sort -> Json.json_value
  val decodeSort : Json.json_value -> Abt.sort option

  val encodeParam : ('a -> Json.json_value) -> 'a Abt.O.P.t -> Json.json_value
  val decodeParam : (Json.json_value -> 'a option) -> Json.json_value -> 'a Abt.O.P.t option

  val encodeOperator : ('a -> Json.json_value) -> 'a Abt.O.t -> Json.json_value
  val decodeOperator : (Json.json_value -> 'a option) -> Json.json_value -> 'a Abt.O.t option
end
