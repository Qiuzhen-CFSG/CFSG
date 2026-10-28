module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.CoreAction.Descent.ComponentImage
public import Theory.GroupTheory.Commutator.TwoCoverComparison
public import GorensteinWalter.SL2ProjectiveCover
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168

/-!
# The remaining intrinsic kernel is the binary SL₂(7) cover

For abelian D=[O₂(J),L], the component action image K is perfect and its
projection onto SL₃(2) has central two-group kernel equal to Z(K).
Transport the quotient to the actual PSL₂(7). Its dihedral Sylow groups
allow comparison with the canonical SL₂(7) double cover by the derived
fiber-product argument. Thus a nontrivial Z(K) gives an actual equivalence
K≃SL₂(7), and in every case |Z(K)|≤2.

Only the two-primary cover comparison is used; full Schur-multiplier
universality is unnecessary. This does not exclude the SL₂(7) possibility.
That remaining exclusion must use the genuine MS setup and elementary D.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.31–34,
printed pp.135–137, and I.1.3, printed p.407. The cover comparison is the
proved two-primary argument of Alperin–Brauer–Gorenstein, Chapter II,
Section 3, Proposition 2 (article p.22).
-/

public section

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterC.BinaryMS
local instance intrinsicKernelPrimeSeven : Fact (Nat.Prime 7) := ⟨by decide⟩

universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}
variable (h : Input κ L R)

private noncomputable def binaryProjectiveEquiv :
    AbelianCore.QuotientRecognition.SL ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7) :=
  Matrix.PSL3Two.equiv.trans Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.symm

/-- Every nontrivial remaining component kernel is the genuine SL₂(7)
double-cover case, with an actual group equivalence. -/
theorem Input.abelianCore_componentImage_SL2Seven_of_center_ne_bot
    (hc : IsMulCommutative (commutatorCore L))
    (hz : center h.coreConjugation.range ≠ ⊥) :
    Nonempty (h.coreConjugation.range ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 7)) := by
  let K := h.coreConjugation.range
  let : Group.IsPerfect K := h.coreComponentImage_perfect
  let f : K →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7) :=
    binaryProjectiveEquiv.toMonoidHom.comp h.coreComponentProjection
  have hf : Function.Surjective f :=
    binaryProjectiveEquiv.surjective.comp h.coreComponentProjection_surjective
  have hk : f.ker = h.coreComponentProjection.ker :=
    MonoidHom.ker_comp_of_injective _ _ binaryProjectiveEquiv.injective
  have hfcentral : f.ker ≤ center K := by
    rw [hk]
    exact h.abelianCore_componentProjection_kernel_central hc
  have hf2 : IsPGroup 2 f.ker := by
    rw [hk]
    exact h.coreComponentProjection_kernel_isPGroup
  have hfn : f.ker ⊓ commutator K ≠ ⊥ := by
    rw [Group.IsPerfect.commutator_eq_top, inf_top_eq, hk,
      h.abelianCore_componentProjection_kernel_eq_center hc]
    exact hz
  obtain ⟨hg, hgcentral, hgcard, hg2, hperfect, hdihedral⟩ :=
    GorensteinWalter.sl2_projective_cover_model (ZMod 7)
      (by rw [Nat.card_zmod]; decide) (by rw [Nat.card_zmod]; decide)
  let := hperfect
  obtain ⟨e⟩ := CentralExtension.commutator_mulEquiv_of_central_two_covers
    f (GorensteinWalter.sl2ProjectiveProjection (ZMod 7)) hf hg hfcentral hgcentral
    hf2 hg2 hfn hgcard hdihedral
  exact ⟨(topEquiv.symm.trans
    (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top.symm)).trans e⟩

/-- The intrinsic central kernel has at most two elements. -/
theorem Input.abelianCore_componentImage_center_card_le_two
    (hc : IsMulCommutative (commutatorCore L)) :
    Nat.card (center h.coreConjugation.range) ≤ 2 := by
  by_cases hz : center h.coreConjugation.range = ⊥
  · rw [hz]
    simp
  · obtain ⟨e⟩ := h.abelianCore_componentImage_SL2Seven_of_center_ne_bot hc hz
    have hh := Nat.card_congr (centerCongr e).toEquiv
    rw [← GorensteinWalter.sl2ProjectiveProjection_ker (ZMod 7),
      GorensteinWalter.sl2ProjectiveProjection_ker_card (ZMod 7)
        (by rw [Nat.card_zmod]; decide)] at hh
    exact hh.le


/-- The full remaining alternative: the component action is centerless,
or it is SL₂(7) with center of order two. -/
theorem Input.abelianCore_componentImage_center_cases
    (hc : IsMulCommutative (commutatorCore L)) :
    center h.coreConjugation.range = ⊥ ∨
      (Nat.card (center h.coreConjugation.range) = 2 ∧
        Nonempty (h.coreConjugation.range ≃*
          Matrix.SpecialLinearGroup (Fin 2) (ZMod 7))) := by
  by_cases hz : center h.coreConjugation.range = ⊥
  · exact Or.inl hz
  · let : Nontrivial (center h.coreConjugation.range) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hz
    have hlo : 1 < Nat.card (center h.coreConjugation.range) := Finite.one_lt_card
    have hhi := h.abelianCore_componentImage_center_card_le_two hc
    exact Or.inr ⟨by omega,
      h.abelianCore_componentImage_SL2Seven_of_center_ne_bot hc hz⟩

end CFSG.Quasithin.ChapterC.BinaryMS
