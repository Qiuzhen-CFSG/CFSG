module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.OffenderSource
public import CFSG.Quasithin.Chapter3.Section01.E23Input

/-!
# The original qrc offender action satisfies B.5.3

Use the actual omega-center orbit and its original centralizer quotient.
The original qrc hypotheses provide reduction and Thompson movement, so the
entire B.5.3 input and the residual/Sylow supplement follow. This is the
literal Chapter 3 entry into the earlier full B.5.6 classification; no module
chart, component list or classification conclusion is assumed.

Source: Aschbacher–Smith 3.1.7, E.2.3 and B.6.9, printed pp.575–576,
216–217 and 116.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

/-- All original B.5.3 assumptions are proved for the actual source offender action. -/
theorem QrcHypotheses.e23_offender_source_hypotheses
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE K G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hZ : ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype) :
    let S := T.subtype h.right_mem.1.1.2
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    let hU := h.sylowOmega_reduced (hG.evenCharacteristic T)
    letI := hU.normal
    letI := hU.elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let Y := offenderSubgroup ρ
    ChapterB.SourceInduction.FFHypothesis K (ρ.comp Y.subtype) ∧
      pResidual 2 (H ⧸ C) ≤ Y ∧ Y ⊔ (S : Subgroup H).map q = ⊤ := by
  obtain ⟨hsq,_,hp,hU,hj⟩ := h.e23_hypotheses hG hM hu hJ hZ
  exact ChapterE.ThompsonAction.source_offender_hypotheses hsq _ hp _ hU hj

end CFSG.Quasithin.Chapter3
