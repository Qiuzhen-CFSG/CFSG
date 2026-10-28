module

public import Theory.Representation.GoldschmidtONan.OddTerminal
public import FeitThompson.FinalTheorem

/-!
# The odd transitive Goldschmidt–O'Nan case

The Step 4 orbital argument forces the fixed space to be a line. The Odd Order
Theorem supplies solvability, and the abelian-kernel terminal argument gives
dimension three and a nonabelian acting group of order 21. Thus all four
exceptional clauses follow from the original odd transitive geometry inputs.

Source: GLS, Number 2, Chapter C, Definition 14.1 and Proposition 14.2,
Step 4 and the terminal argument (`refs/KGroup/GLS2/ChapterC.tex`).
The assembly is above Theory because the Feit–Thompson development has not
yet been promoted with its dependency closure into that layer.
-/

namespace CFSG.Quasithin.GoldschmidtONan

open Representation Representation.GoldschmidtONan

universe u v

variable {X : Type u} {V : Type v} [Group X] [Finite X]
  [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {ρ : Representation (ZMod 2) X V} {Y : Subgroup X}

/-- The odd transitive exceptional source implication, with solvability and
the fixed-line conclusion both discharged. -/
public theorem exceptionalCase_of_odd (h : Input ρ Y)
    (hsub : SuborbitGeometry ρ Y) (hgeom : TransitiveGeometry ρ Y)
    (hodd : Odd (Nat.card X)) : ExceptionalCase ρ Y := by
  let : Group.IsSolvable X := odd_order_theorem X hodd
  exact h.exceptionalCase_of_solvable hsub hgeom hodd

end CFSG.Quasithin.GoldschmidtONan
