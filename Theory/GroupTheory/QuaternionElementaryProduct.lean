module

public import Theory.GroupTheory.QuaternionCentralProductCenter
public import Theory.Frattini.CentralElementarySupplement
public import Theory.Frattini.BinarySquares
public import Theory.GroupTheory.PGroup.OmegaAmbient

/-!
# A quaternion factor with a central elementary supplement

If B is a quaternion group of order eight, U is elementary abelian, the two
subgroups commute and their intersection has order two, then Ω₁(BU) = U
and Φ(BU) = B ∩ U, in the common ambient group. Square-one elements of B
are central, and the shared intersection is its entire center. Adjoining U
does not change the Frattini subgroup, which is the center of B.

The two quaternion tables range over just eight elements and are checked
by the kernel. No ambient normality or group recognition is assumed.

Source: the central-product calculation in Aschbacher–Smith, J.2.6(4),
printed p.434 (PDF p.445 of `refs/quasithin.pdf`).
-/

public section
noncomputable section
open Subgroup
open scoped Pointwise

namespace QuaternionGroup
variable {E : Type*} [Group E] [Finite E]

/-- The Frattini subgroup of a quaternion eight is its center. -/
theorem frattini_eq_center_of_equiv (e : E ≃* QuaternionGroup 2) :
    frattini E = center E := by
  have hp : IsPGroup 2 E := IsPGroup.of_card (n := 3) (by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    decide)
  rw [hp.frattini_eq_closure_squares]
  have hsq : ∀ x : QuaternionGroup 2, ∀ y, y * x ^ 2 = x ^ 2 * y := by decide
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro x ⟨y, rfl⟩
    apply mem_center_iff.mpr
    intro z
    apply e.injective
    simpa only [map_mul, map_pow] using hsq (e y) (e z)
  · intro x hx
    have hc : ∀ y : QuaternionGroup 2, y * e x = e x * y := by
      intro y
      simpa only [map_mul, e.apply_symm_apply] using
        congrArg e (mem_center_iff.mp hx (e.symm y))
    have ht : ∀ a : QuaternionGroup 2,
        (∀ b, b * a = a * b) → ∃ b, b ^ 2 = a := by decide
    obtain ⟨y, hy⟩ := ht (e x) hc
    apply subset_closure
    refine ⟨e.symm y, ?_⟩
    apply e.injective
    simpa only [map_pow, e.apply_symm_apply] using hy

end QuaternionGroup

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- All square-one elements of this central product lie in its elementary factor. -/
theorem omegaOne_eq_of_quaternion_elementary_product (B U : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2)) [IsElementaryAbelian 2 U]
    (hinter : Nat.card (B ⊓ U : Subgroup G) = 2)
    (hcomm : B ≤ centralizer (U : Set G)) :
    omegaOneAmbient (B ⊔ U) = U := by
  have he := intersection_eq_factor_center B U hB hinter
    (fun b hb u hu => (hcomm hb u hu).symm)
  apply le_antisymm
  · apply (omegaOneAmbient_le_iff _ _).mpr
    intro x hx hx2
    have hm : x ∈ (B : Set G) * (U : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right B U
        (hcomm.trans (centralizer_le_normalizer _))]
      exact hx
    obtain ⟨b, hb, u, hu, rfl⟩ := hm
    have hbu : Commute b u := (hcomm hb u hu).symm
    have hb2 : b ^ 2 = 1 := by
      simpa only [hbu.mul_pow, elemPow_eq_one_of_isElementaryAbelian u hu,
        mul_one] using hx2
    have hbcent : (⟨b, hb⟩ : B) ∈ center B := by
      obtain ⟨e⟩ := hB
      have hsq : (e ⟨b, hb⟩) ^ 2 = 1 := by
        rw [← map_pow, show (⟨b, hb⟩ : B) ^ 2 = 1 from Subtype.ext hb2, map_one]
      have ht : ∀ a : QuaternionGroup 2, a ^ 2 = 1 → ∀ c, c * a = a * c := by decide
      apply mem_center_iff.mpr
      intro y
      apply e.injective
      simpa only [map_mul] using ht _ hsq (e y)
    have hbU : b ∈ U := by
      have hi : b ∈ B ⊓ U := by
        rw [he]
        exact ⟨⟨b, hb⟩, hbcent, rfl⟩
      exact hi.2
    exact U.mul_mem hbU hu
  · calc
      U = omegaOneAmbient U := (omegaOneAmbient_eq_self U).symm
      _ ≤ omegaOneAmbient (B ⊔ U) := omegaOneAmbient_mono
        (show U ≤ B ⊔ U from le_sup_right)

/-- The ambient Frattini subgroup is the shared central subgroup of order two. -/
theorem frattini_eq_of_quaternion_elementary_product (B U : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2)) [IsElementaryAbelian 2 U]
    (hinter : Nat.card (B ⊓ U : Subgroup G) = 2)
    (hcomm : B ≤ centralizer (U : Set G)) :
    (frattini (B ⊔ U : Subgroup G)).map (B ⊔ U).subtype = B ⊓ U := by
  obtain ⟨e⟩ := hB
  have hpB : IsPGroup 2 B := IsPGroup.of_card (n := 3) (by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    decide)
  have hp := hpB.to_sup_of_normal_right' (IsElementaryAbelian.isPGroup 2 U)
    (hcomm.trans (centralizer_le_normalizer _))
  have hcent : U ≤ centralizer ((B ⊔ U : Subgroup G) : Set G) := by
    exact le_centralizer_iff.mpr (sup_le hcomm U.le_centralizer)
  rw [frattini_map_eq_of_central_elementary_supplement (B ⊔ U) B U hp
    inferInstance hcent (sup_comm B U), QuaternionGroup.frattini_eq_center_of_equiv e]
  exact (intersection_eq_factor_center B U ⟨e⟩ hinter
    (fun b hb u hu => (hcomm hb u hu).symm)).symm
end Subgroup
