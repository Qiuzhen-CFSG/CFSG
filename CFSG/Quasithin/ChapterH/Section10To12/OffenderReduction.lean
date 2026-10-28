module

public import CFSG.Quasithin.ChapterH.Section05To09.AlternatingPair.Parameters
public import Theory.Representation.BinaryOffender.UniformFixedSpace

/-!
# The numerical offender reduction in H.11

In a ten-dimensional module with involution displacement at least four,
an (F - 1)-offender has rank at least three. If all elementary actors have
rank at most four and the rank-four actors fix at most three dimensions,
the offender has rank three and displacement four. Every nonidentity
element then has the same fixed space, forcing quadratic action.

This supplies the reduction in the last paragraph of H.11.1, printed p.393
(Aschbacher–Smith, combined manuscript of 1 March 2004). The remaining
M₁₂-specific input must exclude the resulting quadratic rank-three actor.
The local calculations are not hypotheses of an asserted source theorem.
-/

public section
namespace CFSG.Quasithin.ChapterH.Section10To12

open Representation.BinaryOffender

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The exact residual offender configuration used by the M₁₂ proof. -/
theorem m12_offender_reduction (ρ : Representation (ZMod 2) G V)
    (hdim : Module.finrank (ZMod 2) V = 10)
    (hm : 4 ≤ ChapterE.moduleM ρ)
    (hr : ∀ A : Subgroup G, IsElementaryTwo A → rank A ≤ 4)
    (hfour : ∀ A : Subgroup G, IsElementaryTwo A → rank A = 4 →
      Module.finrank (ZMod 2) (fixedSpace ρ A) ≤ 3)
    {A : Subgroup G} (hA : AlternatingPair.IsFMinusOneOffender ρ A) :
    rank A = 3 ∧ fixedCodim ρ A = 4 ∧
      (∀ a ∈ A, a ≠ 1 → fixedSpace ρ A = fixedSpace ρ (Subgroup.zpowers a)) ∧
      IsQuadratic ρ A := by
  have hmin := hm.trans (ChapterE.moduleM_le_fixedCodim ρ hA.1)
  have hmax := hr A hA.1
  have hcodim := hA.2
  have hnotfour : rank A ≠ 4 := by
    intro heq
    have hfix := hfour A hA.1 heq
    have hsum := fixedCodim_add_finrank ρ A
    omega
  have hrank : rank A = 3 := by omega
  have hcod : fixedCodim ρ A = 4 := by omega
  let _ : IsElementaryAbelian 2 A := hA.1.2
  have hsame : ∀ a ∈ A, a ≠ 1 → fixedSpace ρ A = fixedSpace ρ (Subgroup.zpowers a) := by
    intro a ha ha1
    have horder : orderOf a = 2 :=
      orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian a ha) ha1
    have hlo := hm.trans (ChapterE.moduleM_le_involution ρ horder)
    have hle : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.mpr ha
    have hhi := ChapterE.fixedCodim_mono ρ hle
    exact fixedSpace_eq_of_fixedCodim_eq ρ hle (by omega)
  exact ⟨hrank, hcod, hsame, isQuadratic_of_common_fixedSpace ρ hsame⟩

end CFSG.Quasithin.ChapterH.Section10To12
