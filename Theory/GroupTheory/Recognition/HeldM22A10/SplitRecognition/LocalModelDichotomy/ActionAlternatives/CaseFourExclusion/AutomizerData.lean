module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.Coordinates

/-!
# Coordinates for the Case IV elementary normalizer

In the ordered basis z₁,z₃,a,d of F, conjugation by z₂,z₄,b gives the three
binary automorphisms below. Their closure is the local group T/F of order
eight. These definitions fix the precise finite subgroup for the remaining
normalizer calculation; they do not assert a subgroup classification.

Source: Janko, A characterization of the Mathieu simple groups, I,
J. Algebra 9 (1968), Section 1, printed p.3.
-/

namespace Theory.GroupTheory.HeldM22A10.LocalModelDichotomy.CaseFour

/-- The distinguished first vector of the elementary normalizer coordinates. -/
@[expose] public def automizerPoint : BinaryFour := Multiplicative.ofAdd ![1, 0, 0, 0]

/-- The source conjugators z₂,z₄,b, in the basis z₁,z₃,a,d of F. -/
@[expose] public def automizerGeneratorFun (i : Fin 3) (v : BinaryFour) : BinaryFour :=
  let x := v.toAdd
  Multiplicative.ofAdd <| ![
    ![x 0 + x 3, x 1, x 2, x 3],
    ![x 0 + x 2, x 1 + x 3, x 2, x 3],
    ![x 0 + x 1, x 1, x 2 + x 3, x 3]] i

/-- The three concrete involutory binary automorphisms. -/
@[expose] public def automizerGenerator (i : Fin 3) : MulAut BinaryFour where
  toFun := automizerGeneratorFun i
  invFun := automizerGeneratorFun i
  left_inv := by
    have h : ∀ i v, automizerGeneratorFun i (automizerGeneratorFun i v) = v := by
      decide +kernel
    exact h i
  right_inv := by
    have h : ∀ i v, automizerGeneratorFun i (automizerGeneratorFun i v) = v := by
      decide +kernel
    exact h i
  map_mul' := by
    have h : ∀ i v w, automizerGeneratorFun i (v*w) =
        automizerGeneratorFun i v * automizerGeneratorFun i w := by decide +kernel
    exact h i

/-- The exact local automizer, with the three literal source generators. -/
@[expose] public def localAutomizer : Subgroup (MulAut BinaryFour) :=
  Subgroup.closure (Set.range automizerGenerator)

end Theory.GroupTheory.HeldM22A10.LocalModelDichotomy.CaseFour
