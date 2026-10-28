module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry.Relative

/-!
# Symmetric commutator bounds under right conjugation

The normalizer of the central line normalizes U, so the line determines
each conjugate of U. The stabilizer of V₁^g is transitive on the other
points of the earlier natural L₃(2)-module. Conjugating [D,U]≤V₁ by
that stabilizer gives [D,U^x]≤V₁^x for every x in L. The equal-point
case follows directly from D≤C_G(U^g).

The point-stabilizer orbit is kept as a precise earlier natural-module
input, to be discharged from 14.3.16 by the source assembly owner.
Source: Aschbacher--Smith, 14.4.7, printed p.1009.
-/

public section

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry
open Subgroup
variable {G : Type*} [Group G]
theorem conjugate_one (A : Subgroup G) : conjugate A 1 = A := by
  simp only [conjugate, inv_one, map_one]
  exact map_id A
theorem conjugate_conjugate (A : Subgroup G) (x y : G) :
    conjugate (conjugate A x) y = conjugate A (x * y) := by
  simp only [conjugate, map_map]
  congr 1
  ext a
  simp [mul_assoc]
theorem conjugate_eq_self (A : Subgroup G) {x : G} (hx : x ∈ normalizer (A : Set G)) :
    conjugate A x = A :=
  mem_normalizer_iff_map_conj_eq.mp ((normalizer (A : Set G)).inv_mem hx)
theorem mem_normalizer_of_conjugate_eq (A : Subgroup G) {x : G}
    (hx : conjugate A x = A) : x ∈ normalizer (A : Set G) := by
  have hh : x⁻¹ ∈ normalizer (A : Set G) := mem_normalizer_iff_map_conj_eq.mpr hx
  simpa only [inv_inv] using (normalizer (A : Set G)).inv_mem hh
theorem conjugate_eq_of_center_eq (H U A : Subgroup G)
    (hH : H = normalizer (A : Set G)) (hHU : H ≤ normalizer (U : Set G))
    (x y : G) (hxy : conjugate A x = conjugate A y) :
    conjugate U x = conjugate U y := by
  have he : conjugate A (x * y⁻¹) = A := by
    rw [← conjugate_conjugate, hxy, conjugate_conjugate, mul_inv_cancel, conjugate_one]
  have hn : x * y⁻¹ ∈ H := hH ▸ mem_normalizer_of_conjugate_eq A he
  have hu := conjugate_eq_self U (hHU hn)
  have hh := congrArg (fun B : Subgroup G => conjugate B y) hu
  simpa only [conjugate_conjugate, inv_mul_cancel_right] using hh

/-- The point stabilizer orbit in the natural L₃(2)-module supplies all the
symmetric bounds. The point orbit is an earlier natural-module input, and
the commutator bound is transported through actual right conjugation. -/
theorem symmetric_commutator_bounds (H U A L V : Subgroup G) (g : G)
    (hH : H = normalizer (A : Set G)) (hHU : H ≤ normalizer (U : Set G))
    (hAV : A ≤ V) (hLV : L ≤ normalizer (V : Set G))
    (hpoints : ∀ x ∈ L, conjugate A x = conjugate A g ∨
      ∃ t ∈ conjugate H g, conjugate A x = conjugate A t)
    (hcomm : ⁅D H U g, U⁆ ≤ A) :
    ∀ x ∈ L, ⁅D H U g, conjugate U x⁆ ≤ conjugate A x ∧ conjugate A x ≤ V := by
  have hHgD : conjugate H g ≤ normalizer (D H U g : Set G) :=
    relative_centralizer_normalized _ _ (conjugate_normalizes H U g hHU)
  intro x hx
  refine ⟨?_, ?_⟩
  · rcases hpoints x hx with he | ⟨t, ht, he⟩
    · rw [conjugate_eq_of_center_eq H U A hH hHU x g he]
      have hc : ⁅D H U g, conjugate U g⁆ = ⊥ :=
        commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
      rw [hc]
      exact bot_le
    · have hu := conjugate_eq_of_center_eq H U A hH hHU x t he
      have hd := conjugate_eq_self (D H U g) (hHgD ht)
      have hh := map_mono (f := (MulAut.conj t⁻¹).toMonoidHom) hcomm
      rw [map_commutator] at hh
      change ⁅conjugate (D H U g) t, conjugate U t⁆ ≤ conjugate A t at hh
      rwa [hd, ← he, ← hu] at hh
  · have hh : conjugate A x ≤ conjugate V x := map_mono hAV
    rwa [conjugate_eq_self V (hLV hx)] at hh
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry
