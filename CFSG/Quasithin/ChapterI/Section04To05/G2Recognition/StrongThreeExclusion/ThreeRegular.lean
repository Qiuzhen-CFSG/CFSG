module

public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.StrongThreeExclusion.AmbientCharacters
public import Theory.Character.DefectZeroVanishing

/-!
# Three-regular vanishing and exclusion of defect-zero constituents

The induced local virtual rows vanish on every three-regular element of G.
A character whose degree is divisible by the Sylow order nine vanishes on
the complementary singular set. It is therefore orthogonal to every induced
row, and cannot occur in the signed common-constituent identity.
-/

public section
noncomputable section
attribute [local instance] Fintype.ofFinite
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour LocalCharacters
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)

/-- The actual induced virtual rows vanish on the entire three-regular
locus of the ambient group. -/
theorem induced_localAlpha_three_regular (i : Fin 4) (g : G)
    (hg : ¬ 3 ∣ orderOf g) : inducedClassFunction c.H (localAlpha c i) g = 0 := by
  classical
  unfold inducedClassFunction
  have hterm (x : G) : (if hx : x⁻¹ * g * x ∈ c.H then
      localAlpha c i ⟨x⁻¹ * g * x,hx⟩ else 0) = 0 := by
    split
    · next hx =>
      apply localAlpha_supported c i
      intro hd
      change 3 ∣ orderOf (⟨x⁻¹ * g * x,hx⟩ : c.H) at hd
      apply hg
      have ho : orderOf (⟨x⁻¹ * g * x,hx⟩ : c.H) = orderOf g := by
        rw [← orderOf_coe]
        simpa only [MulAut.conj_apply, inv_inv] using (MulAut.conj x⁻¹).orderOf_eq g
      rwa [ho] at hd
    · rfl
  simp only [hterm, Finset.sum_const_zero, mul_zero]

include c in
private theorem sylow_three_card_nine (hsmall : ¬ 3 ^ 3 ∣ Nat.card G) :
    ∃ P : Sylow 3 G, Nat.card P = 9 := by
  obtain ⟨t⟩ := exists_cubic_torus c
  obtain ⟨P,hP⟩ := t.cubic_plane_sylow_iff.mpr
    (t.small_cores_iff_not_cube_dvd.mpr hsmall)
  refine ⟨P, ?_⟩
  rw [hP]
  exact (cubic_plane_data c t.x t.y t.x_order t.y_order).2

/-- Every constituent of an actual induced row has degree prime to nine
in the small-Sylow branch. -/
theorem not_nine_dvd_degree_of_induced_pairing
    (hsmall : ¬ 3 ^ 3 ∣ Nat.card G) (i : Fin 4)
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ)
    (hpair : scalarProduct G (inducedClassFunction c.H (localAlpha c i)) χ ≠ 0) :
    ¬ 9 ∣ hχ.degree := by
  intro hd
  obtain ⟨P,hP⟩ := sylow_three_card_nine c hsmall
  apply hpair
  unfold scalarProduct
  have hz (g : G) : inducedClassFunction c.H (localAlpha c i) g * star (χ g) = 0 := by
    by_cases hg : 3 ∣ orderOf g
    · rw [OrdinaryCharacter.value_eq_zero_of_sylow_card_dvd_degree P hχ hχ.degree_eq
        (by rwa [hP]) g hg, star_zero, mul_zero]
    · rw [induced_localAlpha_three_regular c i g hg, zero_mul]
  simp only [hz, Finset.sum_const_zero, mul_zero]

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
