module

public import Theory.SpecificGroups.GL2.ThreeClassFunctions
public import Theory.Representation.GLTwoBorelIndex

/-!
# The element census of the upper-triangular subgroup of GL₂(3)

The twelve upper-triangular invertible matrices comprise the identity,
seven involutions, two elements of order three and two of order six.
A power-based integer weight gives a kernel-checked sum on these matrices.
It is the restriction of the values `[12,4,0,3,1,4,0,0]` on the eight
GL₂(3) conjugacy classes.

Source: the explicit GL₂(3) matrices in Wong (1964), Table 1, p.97,
and the shared subgroup in Appendix (b), p.110.
-/

namespace Matrix.GeneralLinearGroup
open Matrix
open scoped BigOperators
noncomputable section

private abbrev Mat := Matrix (Fin 2) (Fin 2) (ZMod 3)
private abbrev GLThree := GL (Fin 2) (ZMod 3)

private def weight (A : Mat) : ℕ :=
  if A = 1 then 12 else if A ^ 2 = 1 then 4 else
    if A ^ 3 = 1 then 3 else if A ^ 6 = 1 then 1 else 0

private theorem weight_eq (x : GLThree) : weight x.val =
    if x = 1 then 12 else if x ^ 2 = 1 then 4 else
      if x ^ 3 = 1 then 3 else if x ^ 6 = 1 then 1 else 0 := by
  have h1 : x.val = 1 ↔ x = 1 :=
    ⟨fun h => Units.ext h, fun h => congrArg Units.val h⟩
  have hp (n : ℕ) : x.val ^ n = 1 ↔ x ^ n = 1 :=
    ⟨fun h => Units.ext h, fun h => congrArg Units.val h⟩
  simp only [weight, h1, hp]

private theorem weight_conj (x g : GLThree) :
    weight (g * x * g⁻¹).val = weight x.val := by
  simp only [weight_eq, conj_pow]
  have hc (y : GLThree) : g * y * g⁻¹ = 1 ↔ y = 1 := by
    constructor
    · intro h
      have := congrArg (fun z => g⁻¹ * z * g) h
      simpa [mul_assoc] using this
    · rintro rfl
      simp
  simp only [hc]

private theorem weight_class (i : Fin 8) :
    weight (threeClassRepr i).val = ![12,4,0,3,1,4,0,0] i := by
  fin_cases i <;> decide +kernel

private theorem matrix_weight_sum :
    ∑ A ∈ Finset.univ.filter (fun A : Mat => A.det ≠ 0 ∧ A 1 0 = 0), weight A = 48 := by
  decide +kernel

private def borelMatrixEquiv : GLTwo.borelSubgroup (ZMod 3) ≃
    {A : Mat // A.det ≠ 0 ∧ A 1 0 = 0} where
  toFun x := ⟨x.val.val, x.val.det_ne_zero, x.property⟩
  invFun A := ⟨mkOfDetNeZero A.val A.property.1, A.property.2⟩
  left_inv _ := Subtype.ext (Units.ext rfl)
  right_inv _ := Subtype.ext rfl

set_option maxRecDepth 2048 in
/-- A class function with these eight actual values has sum 48 on the Borel. -/
public theorem three_borel_sum_of_class_values (f : ClassFunction (GL (Fin 2) (ZMod 3)))
    [Fintype (GLTwo.borelSubgroup (ZMod 3))]
    (hf : IsClassFunction f)
    (hv : ∀ i : Fin 8, f (threeClassRepr i) = (![12,4,0,3,1,4,0,0] i : ℂ)) :
    ∑ x : GLTwo.borelSubgroup (ZMod 3), f (x : GL (Fin 2) (ZMod 3)) = 48 := by
  classical
  have hweight (x : GLThree) : f x = (weight x.val : ℂ) := by
    obtain ⟨i, hi, _⟩ := three_conjugacy_data.1 x
    obtain ⟨g, hg⟩ := isConj_iff.mp hi
    have hw := weight_conj x g
    rw [hg, weight_class] at hw
    rw [← hw, ← hf x g, hg, hv]
    fin_cases i <;> norm_num
  simp_rw [hweight]
  calc
    _ = ∑ A : {A : Mat // A.det ≠ 0 ∧ A 1 0 = 0}, (weight A.val : ℂ) := by
      exact Fintype.sum_equiv borelMatrixEquiv _ _ (fun _ => rfl)
    _ = ∑ A ∈ Finset.univ.filter (fun A : Mat => A.det ≠ 0 ∧ A 1 0 = 0),
        (weight A : ℂ) := by
      symm
      exact Finset.sum_subtype _ (by simp) _
    _ = 48 := by exact_mod_cast matrix_weight_sum

end
end Matrix.GeneralLinearGroup
