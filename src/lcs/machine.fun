functor LcsMachine
  (structure Cl : LCS_CLOSURE
   structure K : ABT_OPERATOR
   val isFinal : Cl.Abt.abt Cl.closure -> bool) : LCS_MACHINE =
struct
  structure Cl = Cl and K = K
  open Cl

  datatype ('o, 'a) pat = `$ of 'o * 'a Abt.bview list

  type 'a cont_operator = 'a K.t

  type expr = Abt.abt
  type cont = (Abt.symbol K.t, expr Cl.closure) pat
  type stack = cont list

  datatype 'a state =
      <| of 'a Cl.closure * stack
    | |> of 'a Cl.closure * stack

  infix 1 <| |>
  infix 2 <:
  infix `$

  fun start m =
    new m <| []

  val closureIsFinal = isFinal

  fun isFinal (cl |> []) = closureIsFinal cl
    | isFinal _ = false

  fun star step st =
    if isFinal st then
      st
    else
      star step (step st)

  fun map f =
    fn cl <| st => Cl.map f cl <| st
     | cl |> st => Cl.map f cl |> st


  local
    fun bindingToString (Abt.\ ((us, xs), cl)) =
      "{" ^ Abt.O.Ar.Vl.Sp.pretty Abt.Sym.toString ", " us ^ "}"
        ^ "[" ^ Abt.O.Ar.Vl.Sp.pretty Abt.Var.toString ", " xs ^ "]"
        ^ "."
        ^ Cl.toString cl
  in
    fun contToString (k `$ es) =
      K.toString Abt.Sym.toString k
        ^ "("
        ^ ListSpine.pretty bindingToString ", " es
        ^ ")"
  end

  fun stackToString ks =
    "[" ^ ListSpine.pretty contToString ", " ks ^ "]"

  val toString =
    fn cl <| st => Cl.toString cl ^ " <| " ^ stackToString st
     | cl |> st => Cl.toString cl ^ " |> " ^ stackToString st
end
