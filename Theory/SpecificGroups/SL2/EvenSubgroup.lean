module

public import Theory.SpecificGroups.GL2.ProjectiveFourGroupObstruction
public import Mathlib.GroupTheory.Sylow

/-!
# The scalar involution in even-order SL₂ subgroups

Cauchy's theorem supplies an involution in any finite subgroup of even
order. In odd characteristic a determinant-one involution in dimension
two is scalar, so this involution is minus identity.

This supplies the nontrivial central kernel in the exceptional-subgroup
lift for Aschbacher–Smith, A.1.29(1), printed p.27.
-/

open Matrix Subgroup
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup

/-- Every finite even-order subgroup of odd-characteristic SL₂ contains
the scalar involution. -/
public theorem neg_one_mem_of_even_card {F : Type*} [Field F]
    (hF : (2 : F) ≠ 0) (K : Subgroup SL(2,F)) [Finite K]
    (hK : 2 ∣ Nat.card K) : (-1 : SL(2,F)) ∈ K := by
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 hK
  have hpow : a ^ 2 = 1 := by simpa only [ha] using pow_orderOf_eq_one a
  have hs : (a : SL(2,F)) ^ 2 = 1 :=
    congrArg (fun x : K => (x : SL(2,F))) hpow
  have hd : (toGL (a : SL(2,F))).det = 1 := by
    apply Units.ext
    exact a.val.property
  rcases GeneralLinearGroup.eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one hF
      (toGL (a : SL(2,F))) (by rw [← map_pow, hs, map_one]) hd with h | h
  · have hae : a = 1 := Subtype.ext (toGL_injective (by simpa using h))
    simp [hae] at ha
  · have hae : (a : SL(2,F)) = -1 := Subtype.ext (congrArg Units.val h)
    exact hae ▸ a.property

end Matrix.SpecialLinearGroup
