module

public import Theory.SpecificGroups.PSL3Three.Cardinality
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.MatrixModel
public import Theory.GroupTheory.PrimeRankElementary

/-!
# An elementary nine in the actual PSL3(3)

The first unitriangular root plane embeds faithfully in the projective group.
Its two additive coordinates form an elementary abelian group of order nine.
This supplies the lower rank used to rule out two component conjugates in
Aschbacher--Smith 2.5.3(4), printed p.553.
-/

namespace Matrix.PSL3Three
open Matrix.PSL3Even.UnipotentGeometry

/-- The actual projective model has three-rank at least two. -/
public theorem primeRank_three_ge_two : 2 ≤ primeRank 3 PSL := by
  let f := (projective (ZMod 3)).comp (axis₁ (ZMod 3))
  apply primeRank_ge_of_elementary_embedding (p := 3) (e := 2) (f := f)
  · decide +kernel
  · norm_num [Nat.card_eq_fintype_card]
  · apply (projective_injective (ZMod 3)).comp
    intro x y h
    exact Multiplicative.toAdd.injective
      (Prod.ext (congrArg U.x h) (congrArg U.c h))

end Matrix.PSL3Three
