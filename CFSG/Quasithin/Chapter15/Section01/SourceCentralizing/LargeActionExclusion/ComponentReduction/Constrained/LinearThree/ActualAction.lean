module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.LinearThree
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.LinearThree.Exclusion
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.LinearThree.FixedModule
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Nine

/-!
# The binary SL3 terminal obstruction on the original Nine selection

Select the component and exchanged planes from the original action once.
For that component the parabolic centralizer identity gives fixed-plane
centralization, and the two later source conclusions cannot hold together.
This is a consumer of the checked normalizer contradiction, not a claim
that those remaining block-action conclusions have been proved.
The final application discharges the complete L3 block exclusion.
The residual-geometry consumer additionally supplies the original faithful
quotient action, central core placement, and trivial exchanged action on
L/O₂(L), with the same component and both plane rows.

Source: Aschbacher--Smith 15.1.24(2), printed p.1101.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The terminal implication uses the same component and planes selected
from the actual Nine action. The earlier 15.1.14 input remains explicit. -/
theorem PreparedChosenModule.source_caseI_nine_l3_terminal_obstruction
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (h9 : letI := h.elementary
      SourceCases.Nine (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.ExchangedSource ∧
      (d.ConstrainedL3Alternative →
        d.nineFixedPlane ≤ centralizer (d.L : Set G) ∧
          ∀ t ∈ (T : Subgroup G), t ∉ d.S →
            d.L = (primeToResidual 3 (centralizer (d.nineFixedPlane : Set G))).map
              (centralizer (d.nineFixedPlane : Set G)).subtype →
            ¬ d.linearThreeU.map (MulAut.conj t).toMonoidHom ≤ centralizer (d.L : Set G)) := by
  obtain ⟨d,s⟩ :=
    h.source_caseI_nine_exchanged_source hG T hempty hM hmany hJ hu hne hfull h9 hres
  refine ⟨d,s,fun a => ⟨a.fixedPlane_centralizes hM.1.2 h,?_⟩⟩
  intro t ht htS hr hc
  exact s.false_of_constrained_l3_residual_geometry hG hempty hu a hr ht htS hc


/-- The original Nine selection supplies both the earlier marker and the
exchanged source on the identical component. The literal second residual
has index-three action, its core contains the moving plane centrally, and
its exchanged conjugate normalizes L and centralizes L/O₂(L).
The earlier 15.1.14 input is retained
for the large-component assembly owner to discharge. -/
theorem PreparedChosenModule.source_caseI_nine_l3_residual_geometry
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (h9 : letI := h.elementary
      SourceCases.Nine (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.ExchangedSource ∧
      (d.ConstrainedL3Alternative →
        ⁅V,d.linearThreeY⁆ = d.nineMovingPlane ∧
        ⁅d.nineMovingPlane,d.linearThreeY⁆ = d.nineMovingPlane ∧
        d.nineMovingPlane ≤ d.linearThreeY.pCoreIn 2 ⊓
          centralizer (d.linearThreeY.pCoreIn 2 : Set G) ∧
        (centralizer (d.nineMovingPlane : Set G)).relIndex d.linearThreeY = 3 ∧
        d.nineMovingPlane ⊓ centralizer (d.linearThreeY : Set G) = ⊥ ∧
        ((d.nineMovingPlane ≤ d.linearThreeU ∧ d.row = .four ∧
          Nat.card d.Z1 = 2 ∧ Nat.card d.nineFixedPlane = 4 ∧
          Nat.card d.nineMovingPlane = 4) ∨
        (∃ v : d.L, (v : G) ∈ d.nineMovingPlane ∧
          orderOf (QuotientGroup.mk' (pCore 2 d.L) v) = 2)) ∧
        ∀ t ∈ (T : Subgroup G), t ∉ d.S →
          IsPPerfect 2 (d.linearThreeY.map (MulAut.conj t).toMonoidHom) ∧
          d.linearThreeY.map (MulAut.conj t).toMonoidHom ≤
            centralizer (d.nineMovingPlane : Set G) ∧
          ⁅d.nineFixedPlane,d.linearThreeY.map (MulAut.conj t).toMonoidHom⁆ =
            d.nineFixedPlane ∧
          d.linearThreeY.map (MulAut.conj t).toMonoidHom ≤ normalizer (d.L : Set G) ∧
          ⁅d.linearThreeY.map (MulAut.conj t).toMonoidHom,d.L⁆ ≤ d.L.pCoreIn 2) := by
  obtain ⟨d,_,_,sp,g⟩ :=
    h.source_nine_preExclusion_component hG T hempty hM hmany hJ hu hne hfull h9 hres
  let s := sp.exchangedSource hG h g
  refine ⟨d,s,fun a => ?_⟩
  obtain ⟨hm,hm2,_⟩ := s.linearThree_residual_action (h := h) sp hM.1.2 a
  obtain ⟨_,hi,hfixed⟩ := s.linearThree_moving_action_kernel (h := h) sp hM.1.2 a
  refine ⟨hm,hm2,s.linearThree_moving_in_core_center (h := h) sp hM.1.2 a,
    hi,hfixed,s.linearThree_moving_dichotomy (h := h) sp hM.1.2 a,?_⟩
  intro t ht htS
  obtain ⟨hp,hc,hmove⟩ := s.linearThree_exchanged_action (h := h) sp hM.1.2 a ht htS
  exact ⟨hp,hc,hmove,s.linearThree_exchanged_normalizes (h := h) sp hG hM.1.2 a ht htS,
    s.linearThree_exchanged_core_quotient (h := h) sp hG hM.1.2 a ht htS⟩

/-- Original 15.1.24(2) applied to the component and residual selected by
an actual Nine action. The earlier 15.1.14 input remains for the parent
large-component assembly to discharge. -/
theorem PreparedChosenModule.source_caseI_nine_no_constrained_l3
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (h9 : letI := h.elementary
      SourceCases.Nine (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.ExchangedSource ∧
      ¬ d.ConstrainedL3Alternative := by
  obtain ⟨d,_,_,sp,g⟩ :=
    h.source_nine_preExclusion_component hG T hempty hM hmany hJ hu hne hfull h9 hres
  let s := sp.exchangedSource hG h g
  exact ⟨d,s,s.no_constrained_l3 (h := h) sp hG hempty hM.1.2 hu⟩

end CFSG.Quasithin.Chapter15.Section01
