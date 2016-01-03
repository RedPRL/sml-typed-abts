functor Pattern (Abt : LIST_ABT) : PATTERN =
struct
  open Abt

  datatype 'a argument =
      MVAR of metavariable
    | PAT of 'a
  and 'a view = $@ of operator * 'a argument spine

  datatype pattern = IN of pattern view * metacontext

  infix $@

  structure Error =
  struct
    datatype t =
        NON_LINEAR
      | OTHER
  end

  exception InvalidPattern of Error.t

  fun extend Theta (mv, vl) =
    Metacontext.extend Theta (mv, vl)
    handle Metacontext.MergeFailure => raise InvalidPattern Error.NON_LINEAR

  fun concat (Theta, Theta') =
    Metacontext.concat (Theta, Theta')
    handle Metacontext.MergeFailure => raise InvalidPattern Error.NON_LINEAR

  fun into (theta $@ args) =
    let
      val (vls, tau) = Operator.arity theta
      fun go [] [] = Metacontext.empty
        | go (MVAR mv :: args) (vl :: vls) = extend (go args vls) (mv, vl)
        | go (PAT p :: args) ((([], []), tau) :: vls) =
            let
              val (theta' $@ args', Theta) = out p
              val (_, tau') = Operator.arity theta'
              val _ = Operator.Arity.Sort.Eq.eq (tau, tau')
            in
              concat (go args vls, Theta)
            end
        | go _ _ = raise InvalidPattern Error.OTHER
    in
      IN (theta $@ args, go args vls)
    end

  and out (IN p) = p
end
