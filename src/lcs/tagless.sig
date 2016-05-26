signature INSTR =
sig
  type addr = int
  type var
  type sym
  type term

  type 'a operator

  type instr

  datatype scope = \\ of (int -> var) * term

  val expect : addr * unit operator * (scope -> instr) -> instr

  val self : (term -> instr) -> instr

  val use : term * addr * (scope -> instr) -> instr
  val subst : term * var * term * (term -> instr) -> instr
  val final : instr
  val ret : term -> instr
  val stuck : instr

  val orElse : instr * instr -> instr
end

signature INITIAL_INSTR =
sig
end
