module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.CoreAction.Descent.IntrinsicKernel.MaximumOffender
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.CoreAction.Descent.IntrinsicKernel.QuaternionExclusion.ActionSetup
public import Theory.Representation.SL2SevenCentralProductOffenders

/-!
# Exclusion of the SL₂(7) action on the elementary MS core

The supplied equivalence with SL₂(7) gives a concrete normal matrix
component in the faithful action on D=[O₂(J),L]. Its centralizer is the
intrinsic two-core of that action group. The two subgroups generate the
action group and meet in the central involution subgroup. The component
generates all of D by displacements.

Any maximum elementary subgroup E of R outside O₂(J) supplies a best
offender outside the action two-core. The standalone SL₂(7) central-product
bound puts this offender inside that two-core. Pulling back along the
literal conjugation map contradicts E≰O₂(J), so every such E lies in O₂(J).

The genuine MS characteristic-subgroup condition supplies a maximum
elementary subgroup outside O₂(J). Thus the component action image cannot
be isomorphic to SL₂(7). All premises of the standalone bound are discharged
for this action, including the exact central overlap and full commutator
generation. Assembly of intrinsic kernel vanishing belongs in IntrinsicKernel.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.31–34,
printed pp.135–137, and B.2.3–5, printed pp.75–76.
-/

public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterC.BinaryMS
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}
variable (h : Input κ L R) [IsElementaryAbelian 2 (commutatorCore L)]

/-- The concrete cover leaves a best offender outside the intrinsic action
two-core, retaining the original maximum elementary witness in R. Its
intersection with the component alone cannot supply that outside action. -/
theorem Input.exists_coreSL2SevenBestOffender
    (e : h.coreConjugation.range ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 7)) :
    ∃ E ∈ Stellmacher.elementaryAbelianMaxSubgroups R, ¬ E ≤ pCore 2 J ∧
      IsBestOffender h.coreAmbientRepresentation
        (E.map h.coreAmbientConjugation.rangeRestrict) ∧
      ¬ E.map h.coreAmbientConjugation.rangeRestrict ≤
        pCore 2 h.coreAmbientConjugation.range ∧
      (E.map h.coreAmbientConjugation.rangeRestrict) ⊓
        (h.coreSL2SevenEmbedding e).range ≤ pCore 2 h.coreAmbientConjugation.range := by
  obtain ⟨E, hE, hEN, hbest⟩ := h.exists_coreAmbientBestOffender
  have hout : ¬ E.map h.coreAmbientConjugation.rangeRestrict ≤ h.coreActionTwoCore := by
    intro he
    exact hEN ((h.map_coreAction_le_twoCore_iff E).mp he)
  have hinter := h.coreSL2SevenEmbedding_elementary_inter_le_twoCore e
    (inferInstance : IsMulCommutative (commutatorCore L))
    (E.map h.coreAmbientConjugation.rangeRestrict) hbest.1.2
  rw [h.coreActionTwoCore_eq_pCore] at hout hinter
  exact ⟨E, hE, hEN, hbest, hout, hinter⟩

/-- In the concrete SL₂(7) cover branch, every maximum elementary subgroup
of R lies in O₂(J). The central-product offender bound applies to its whole
ambient action image, including images across both commuting factors. -/
theorem Input.elementaryCore_maxElementary_le_core_of_SL2Seven
    (e : h.coreConjugation.range ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 7))
    (E : Subgroup J) (hE : E ∈ Stellmacher.elementaryAbelianMaxSubgroups R) :
    E ≤ pCore 2 J := by
  by_contra hEN
  have hc : IsMulCommutative (commutatorCore L) := inferInstance
  have hcomm := h.coreSL2SevenEmbedding_commutes_twoCore e hc
  have hsup := h.coreSL2SevenEmbedding_sup_twoCore e
  have hoverlap := h.coreSL2SevenEmbedding_comap_twoCore e hc
  rw [h.coreActionTwoCore_eq_pCore] at hcomm hsup hoverlap
  have hle := bestOffender_le_twoCore_of_SL2Seven
    h.coreAmbientRepresentation h.coreAmbientRepresentation_injective
    (h.coreSL2SevenEmbedding e) (h.coreSL2SevenEmbedding_injective e)
    hcomm hsup hoverlap (h.coreSL2SevenEmbedding_full_commutator e)
    (E.map h.coreAmbientConjugation.rangeRestrict)
    (h.coreAmbient_maxElementary_isBestOffender E hE hEN)
  rw [← h.coreActionTwoCore_eq_pCore] at hle
  exact hEN ((h.map_coreAction_le_twoCore_iff E).mp hle)

/-- The genuine MS hypotheses exclude an SL₂(7) component action on the
elementary commutator core. No module-shape or descended-offender premise
remains. -/
theorem Input.elementaryCore_not_nonempty_SL2Seven :
    ¬ Nonempty (h.coreConjugation.range ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 7)) := by
  rintro ⟨e⟩
  obtain ⟨E, hE, hEN⟩ := h.exists_maxElementary_not_le_core
  exact hEN (h.elementaryCore_maxElementary_le_core_of_SL2Seven e E hE)

end CFSG.Quasithin.ChapterC.BinaryMS
