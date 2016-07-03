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

  val encodeSort : Abt.sort -> Json.json_value
  val decodeSort : Json.json_value -> Abt.sort option

  val encodeOperator : Abt.operator -> Json.json_value
  val decodeOperator : Json.json_value -> Abt.operator option
end
