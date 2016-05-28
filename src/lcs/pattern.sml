structure LcsPattern :> LCS_PATTERN =
struct
  (* Instructions, with symbols in 's, variables in 'v, terms in 'a. *)
  datatype ('s, 'v, 'a) instr =
     RETURN of 'a
   | SUBST of ('v * ('s, 'v, 'a) instr) * ('s, 'v, 'a) instr
   | REN of ('s * 's) * ('s, 'v, 'a) instr

  (* A term pattern is an operator and a spine of abstractions *)
  datatype ('s, 'v, 'o, 't) pat = $ of 'o * ('s, 'v, 't) bpat list
  and ('s, 'v, 't) bpat = \ of ('s list * 'v list) * 't
end
