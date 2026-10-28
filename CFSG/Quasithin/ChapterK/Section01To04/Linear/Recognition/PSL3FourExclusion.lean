module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.SourceQuadratic
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.SpecificGroups.PSL3.UniversalProjection.Basic

/-!
# The centerless PSL₃(4) exclusion at quadratic ratio two

The proved degree-three source recognition forces a representation with
quadratic ratio at most two to be natural. Faithfulness then identifies its
generalized Fitting subgroup with SL₃(4), whose center has order three.
A centerless PSL₃(4) component is therefore impossible. This stronger intrinsic
exclusion does not require an additional diagram automorphism hypothesis.

The concrete representation wrapper derives quasisimplicity and centerlessness
from the actual PSL₃(4) model. Its FF consequence applies to the same faithful
representation irreducible on the generalized Fitting subgroup; passage to such
an irreducible section remains the caller's responsibility.

Source: Aschbacher–Smith B.4.2 and B.4.5, printed pp.86–87, as used in
14.2.13, printed p.984; K.3.2.4, printed pp.455–456.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.PSL3FourExclusion

universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K : GroupClass.{u}} {L : Subgroup G}

/-- The source recognition contradicts a centerless layer with projective
quotient PSL₃(4), without assuming a natural module model. -/
theorem quadraticRatio_gt_two_of_source (h : SourceHypothesis K ρ L)
    (hm : ClassicalGroup.IsPSL (L ⧸ center L) 3 4) (hz : center L = ⊥) :
    2 < quadraticRatio ρ := by
  by_contra hn
  have hq : quadraticRatio ρ ≤ 2 := le_of_not_gt hn
  have hm' : ClassicalGroup.IsPSL (L ⧸ center L) 3 (2 ^ 2) := hm
  obtain ⟨B, hB, eQ, C, _⟩ := SourceFF.exists_binaryField_cover h 2 (by decide) hm'
  obtain ⟨hN⟩ := SourceQuadratic.naturalSourceInput_of_quadratic_le_two h C eQ hq
  have hc := Nat.card_congr (centerCongr hN.natural.groupEquiv).toEquiv
  change Nat.card (center L) = Nat.card (center SL(3, B.Carrier)) at hc
  rw [hz, Atlas.ExceptionalSupport.card_sl_center, B.card_eq, hB] at hc
  norm_num at hc

/-- The literal PSL₃(4) layer is quasisimple and centerless, and its central
quotient retains the same projective model. -/
theorem model_facts (hm : ClassicalGroup.IsPSL L 3 4) :
    IsQuasisimple L ∧ center L = ⊥ ∧ ClassicalGroup.IsPSL (L ⧸ center L) 3 4 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  have hqs : IsQuasisimple L := IsQuasisimple.of_mulEquiv e.symm
  have hzP : center PSL(3, F) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot SL(3, F)
  have hz : center L = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro a ha
    have hb := (centerCongr e ⟨a, ha⟩).property
    change e a ∈ center PSL(3, F) at hb
    rw [hzP, mem_bot] at hb
    exact e.injective (hb.trans e.map_one.symm)
  refine ⟨hqs, hz, F, inferInstance, inferInstance, hF, ⟨?_⟩⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans e

/-- Original finite SQTK representation hypotheses exclude the actual
centerless PSL₃(4) layer at quadratic ratio two. -/
theorem quadraticRatio_gt_two [Finite G] [FiniteDimensional (ZMod 2) V]
    (hsq : IsSQTK K G) (hfit : generalizedFitting G = L)
    (hm : ClassicalGroup.IsPSL L 3 4) (hf : Function.Injective ρ)
    (hi : Representation.IsIrreducible (ρ.comp L.subtype)) :
    2 < quadraticRatio ρ := by
  by_contra hn
  have hq : quadraticRatio ρ ≤ 2 := le_of_not_gt hn
  obtain ⟨hqs, hz, hquot⟩ := model_facts hm
  have h : SourceHypothesis K ρ L :=
    ⟨inferInstance, inferInstance, hsq, hfit, hqs, hf, hi,
      (cubicRatio_le_quadraticRatio ρ).trans hq⟩
  exact not_le_of_gt (quadraticRatio_gt_two_of_source h hquot hz) hq

/-- In particular the same faithful irreducible source action cannot be an
FF-module. -/
theorem not_isFFModule [Finite G] [FiniteDimensional (ZMod 2) V]
    (hsq : IsSQTK K G) (hfit : generalizedFitting G = L)
    (hm : ClassicalGroup.IsPSL L 3 4) (hf : Function.Injective ρ)
    (hi : Representation.IsIrreducible (ρ.comp L.subtype)) :
    ¬ IsFFModule ρ := by
  intro hff
  have hq : quadraticRatio ρ ≤ 2 :=
    ((isFFModule_iff_quadraticRatio_le_one ρ).mp hff).trans (by norm_num)
  exact not_le_of_gt (quadraticRatio_gt_two hsq hfit hm hf hi) hq

end CFSG.Quasithin.ChapterK.Linear.Recognition.PSL3FourExclusion
