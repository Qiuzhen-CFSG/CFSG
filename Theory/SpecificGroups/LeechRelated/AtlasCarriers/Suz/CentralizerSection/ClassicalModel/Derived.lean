module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Suz.CentralizerSection.ClassicalModel.Action
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# The two Suz block generators belong to Omega

Four kernel-checked word relations force both generator images to be trivial
in every abelian quotient. Consequently their whole generated subgroup lies
in the commutator subgroup of the full quadratic isometry group. The reverse
containment is a separate generation assertion.

The relations are c^5 = d^6 = (c^2 d^2)^5 = (c^2 d)^9 = 1 for the
literal matrices of `Coordinates`; no presentation or order-recognition
hypothesis is used. Source motivation: GLS3 Table 5.3o, with the orthogonal
commutator convention of GLS3 section 2.7.
-/

@[expose] public section
namespace Sporadic.LeechRelated.Suz.CentralizerSection.ClassicalModel

theorem c_pow_five : cIsometry ^ 5 = 1 := by
  apply orthogonalAction_injective
  simp only [map_pow, map_one, orthogonalAction_c]
  decide +kernel

theorem d_pow_six : dIsometry ^ 6 = 1 := by
  apply orthogonalAction_injective
  simp only [map_pow, map_one, orthogonalAction_d]
  decide +kernel

theorem square_product_pow_five : (cIsometry ^ 2 * dIsometry ^ 2) ^ 5 = 1 := by
  apply orthogonalAction_injective
  simp only [map_pow, map_mul, map_one, orthogonalAction_c, orthogonalAction_d]
  decide +kernel

theorem square_c_product_pow_nine : (cIsometry ^ 2 * dIsometry) ^ 9 = 1 := by
  apply orthogonalAction_injective
  simp only [map_pow, map_mul, map_one, orthogonalAction_c, orthogonalAction_d]
  decide +kernel

private theorem abelian_relations {A : Type*} [CommGroup A] (x y : A)
    (hx5 : x ^ 5 = 1) (hy6 : y ^ 6 = 1)
    (hxy5 : (x ^ 2 * y ^ 2) ^ 5 = 1) (hxy9 : (x ^ 2 * y) ^ 9 = 1) :
    x = 1 ∧ y = 1 := by
  have hx10 : x ^ 10 = 1 := by
    calc
      x ^ 10 = (x ^ 5) ^ 2 := (pow_mul x 5 2)
      _ = 1 := by rw [hx5, one_pow]
  have hy10 : y ^ 10 = 1 := by
    simpa only [mul_pow, ← pow_mul, hx10, one_mul] using hxy5
  have hy2 : y ^ 2 = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    exact Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr hy6)
      (orderOf_dvd_iff_pow_eq_one.mpr hy10)
  have hx36 : x ^ 36 = 1 := by
    have h := congrArg (fun a : A => a ^ 2) hxy9
    have hy18 : y ^ 18 = 1 := by
      calc
        y ^ 18 = (y ^ 2) ^ 9 := (pow_mul y 2 9)
        _ = 1 := by rw [hy2, one_pow]
    simpa only [mul_pow, ← pow_mul, hy18, mul_one, one_pow] using h
  have hx1 : x = 1 := by
    have h : x ^ 1 = 1 := orderOf_dvd_iff_pow_eq_one.mp
      (Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr hx5)
        (orderOf_dvd_iff_pow_eq_one.mpr hx36))
    exact (pow_one x).symm.trans h
  have hy9 : y ^ 9 = 1 := by simpa only [hx1, one_pow, one_mul] using hxy9
  have hy1 : y = 1 := by
    have h : y ^ 1 = 1 := orderOf_dvd_iff_pow_eq_one.mp
      (Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr hy2)
        (orderOf_dvd_iff_pow_eq_one.mpr hy9))
    exact (pow_one y).symm.trans h
  exact ⟨hx1, hy1⟩

theorem generators_mem_commutator : cIsometry ∈ commutator O ∧ dIsometry ∈ commutator O := by
  have h5 := congrArg (Abelianization.of : O →* Abelianization O) c_pow_five
  have h6 := congrArg (Abelianization.of : O →* Abelianization O) d_pow_six
  have h25 := congrArg (Abelianization.of : O →* Abelianization O) square_product_pow_five
  have h29 := congrArg (Abelianization.of : O →* Abelianization O) square_c_product_pow_nine
  simp only [map_mul, map_pow, map_one] at h5 h6 h25 h29
  have h := abelian_relations _ _ h5 h6 h25 h29
  rw [← Abelianization.ker_of]
  exact h

theorem generated_le_commutator : generated ≤ commutator O := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases hg with rfl | hg
  · exact generators_mem_commutator.1
  · have he : g = dIsometry := hg
    subst g
    exact generators_mem_commutator.2

end Sporadic.LeechRelated.Suz.CentralizerSection.ClassicalModel
