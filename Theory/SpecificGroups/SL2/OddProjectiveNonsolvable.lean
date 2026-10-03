module

public import Theory.SpecificGroups.SL2.BinaryTetrahedral
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.GroupTheory.Nilpotent

/-!
# The lower field-order bound for nonsolvable odd PSL2 groups

If `PSL₂(F)` is nonsolvable over a finite field of odd cardinality, then
`|F| > 3`. A field has at least two elements, so an odd field of cardinality
at most three has exactly three elements. Such a field is isomorphic to
`ZMod 3`. The concrete binary tetrahedral equivalence identifies `SL₂(3)`
with `Q₈ ⋊ C₃`, which is solvable because its normal subgroup and quotient
are solvable. Entrywise field transport gives solvability of `SL₂(F)`, and
the quotient by its center gives solvability of `PSL₂(F)`.

This removes the small solvable parameter from odd-field projective-linear
recognition. The matrix-model input is the binary tetrahedral construction
in `Theory.SpecificGroups.SL2.BinaryTetrahedral`, extracted from the GLS3
5.2.4 development. No classification or simplicity hypothesis is required.
-/

namespace Matrix.ProjectiveSpecialLinearGroup

open GLS3.Chapter5.SchurPresentation

private theorem isSolvable_of_card_three
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 3) :
    Group.IsSolvable (ProjectiveSpecialLinearGroup (Fin 2) F) := by
  have hQ : IsPGroup 2 (QuaternionGroup 2) :=
    IsPGroup.of_card (n := 3) (by norm_num [QuaternionGroup.card])
  let : Group.IsNilpotent (QuaternionGroup 2) := hQ.isNilpotent
  let : Group.IsSolvable
      (QuaternionGroup 2 ⋊[q8C3Action] Multiplicative (ZMod 3)) :=
    Group.isSolvable_of_ker_le_range SemidirectProduct.inl
      SemidirectProduct.rightHom SemidirectProduct.range_inl_eq_ker_rightHom.ge
  let : Group.IsSolvable SL23 :=
    Group.isSolvable_of_surjective (f := binaryTetrahedralEquivSL.toMonoidHom)
      binaryTetrahedralEquivSL.surjective
  let : Fintype F := Fintype.ofFinite F
  let e := ZMod.ringEquivOfPrime F Nat.prime_three
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hsurj : Function.Surjective (SpecialLinearGroup.map (n := Fin 2) e.toRingHom) := by
    intro g
    refine ⟨SpecialLinearGroup.map e.symm.toRingHom g, ?_⟩
    ext i j
    exact e.apply_symm_apply (g i j)
  let : Group.IsSolvable (SpecialLinearGroup (Fin 2) F) :=
    Group.isSolvable_of_surjective hsurj
  infer_instance

/-- Nonsolvability excludes the three-element field from odd-field PSL2 models. -/
public theorem card_gt_three_of_odd_of_not_isSolvable
    {F : Type*} [Field F] [Finite F]
    (hodd : Odd (Nat.card F))
    (hns : ¬ Group.IsSolvable (ProjectiveSpecialLinearGroup (Fin 2) F)) :
    3 < Nat.card F := by
  by_contra hle
  have htwo : 1 < Nat.card F := Finite.one_lt_card
  have hthree : Nat.card F = 3 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  exact hns (isSolvable_of_card_three hthree)

end Matrix.ProjectiveSpecialLinearGroup
