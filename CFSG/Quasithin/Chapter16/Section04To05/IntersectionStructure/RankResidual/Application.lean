module

public import CFSG.Quasithin.Chapter16.Section04To05.IntersectionStructure.RankResidual.Local
public import Theory.GroupTheory.CComponent.Basic

/-!
# The hypotheses of A.3.18 in the standard setup

An ordinary component is a C-component: a smaller perfect subnormal
subgroup would be central in the quasisimple component and hence trivial.
Condition (E1) identifies Z(L) with O₂(L), so the two-core quotient is
quasisimple. Transport these facts and the given rank through the actual
subgroup inclusion into C_G(i), and supply its SQTK property.

This establishes the input of the universal earlier theorem A.3.18. It
does not assume, or assert, the alternatives of Lemma 16.4.5.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.3.1,
A.3.18, pp.41, 51–52, and Lemma 16.4.5, p.1184.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter16.Intersections
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z : G} {L : Subgroup G}

omit [Finite G] in
private theorem ordinary_isCComponent {A : Subgroup G} (hA : IsComponent G A) :
    A.IsCComponent := by
  let := hA.2
  let : IsSimpleGroup (A ⧸ center A) := IsQuasisimple.simple
  let : Nontrivial A := (QuotientGroup.mk'_surjective (center A)).nontrivial
  refine ⟨(nontrivial_iff_ne_bot A).mp inferInstance, inferInstance, hA.1, ?_⟩
  intro B hBA hB hp hs
  let := hp
  let : Group.IsPerfect (B.subgroupOf A) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hBA).symm.toMonoidHom)
    (subgroupOfEquivOfLe hBA).symm.surjective
  rcases IsQuasisimple.subnormal_le_center_or_eq_top (B.subgroupOf A) hs.subgroupOf with hc | ht
  · have hb : B.subgroupOf A = ⊥ := by
      apply le_bot_iff.mp
      calc
        B.subgroupOf A = ⁅B.subgroupOf A, B.subgroupOf A⁆ := commutator_eq_self.symm
        _ ≤ ⁅center A, center A⁆ := commutator_mono hc hc
        _ = ⊥ := commutator_self_eq_bot_iff.mpr inferInstance
    have hm := congrArg (Subgroup.map A.subtype) hb
    exact (hB (by simpa only [map_subgroupOf_eq_of_le hBA, Subgroup.map_bot] using hm)).elim
  · exact subgroupOf_eq_top.mp ht

/-- The ordinary component is also a C-component in the correct local group. -/
theorem StandardSetup.involution_ccomponent (h : StandardSetup T z L) {i : G}
    (hi : i ∈ centralizer (L : Set G)) (hi2 : orderOf i = 2) :
    (L.subgroupOf (involutionCentralizer i)).IsCComponent :=
  ordinary_isCComponent (h.involution_component hi hi2).2

/-- The quotient required by A.3.18 is quasisimple, by (E1). -/
theorem StandardSetup.component_twoCoreQuotient_quasisimple {κ : GroupClass} (hG : Hypothesis1611 κ G) (h : StandardSetup T z L) :
    IsQuasisimple (L ⧸ pCore 2 L) := by
  let := h.component.quasisimple
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : IsQuasisimple (L ⧸ center L) := {
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (Group.IsPerfect.center_quotient_center_eq_bot L)).trans QuotientGroup.quotientBot).isSimpleGroup }
  exact IsQuasisimple.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq
    (hG.evenType.component_center_eq_twoCore h.involution h.component))

/-- All hypotheses of A.3.18, transported to the actual relative component. -/
theorem StandardSetup.oddPrime_application_hypotheses {κ : GroupClass} (hG : Hypothesis1611 κ G) (h : StandardSetup T z L)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hr : 1 < primeRank p L)
    {i : G} (hi : i ∈ centralizer (L : Set G)) (hi2 : orderOf i = 2) :
    IsSQTK κ (involutionCentralizer i) ∧
    (L.subgroupOf (involutionCentralizer i)).IsCComponent ∧
    IsQuasisimple ((L.subgroupOf (involutionCentralizer i)) ⧸
      pCore 2 (L.subgroupOf (involutionCentralizer i))) ∧
    p.Prime ∧ Odd p ∧ 1 < primeRank p (L.subgroupOf (involutionCentralizer i)) := by
  have hL := h.involution_component hi hi2
  have e := (subgroupOfEquivOfLe hL.1).symm
  let := h.component_twoCoreQuotient_quasisimple hG
  refine ⟨hG.involution_centralizer_sqtk hi2, h.involution_ccomponent hi hi2,
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)),
    Fact.out, hp, ?_⟩
  rwa [primeRank_equiv p (subgroupOfEquivOfLe hL.1)]

end CFSG.Quasithin.Chapter16.Intersections
