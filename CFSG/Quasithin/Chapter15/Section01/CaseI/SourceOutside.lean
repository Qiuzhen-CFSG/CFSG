module
public import CFSG.Quasithin.Chapter15.Section01.CaseI.SourceNineComponents
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.LocalAction
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# Escape of the original Case-I component

The source14.1.6 centralization of the solvable residual of M applies to
any perfect subgroup of M. The component selected in15.1.19 is perfect,
so containment in M would place it in the centralizer of V(M), hence in
Mc. This contradicts its actual outside-component property. This proves
15.1.20(1) without requiring membership in the global family L(G,T).

Source: Aschbacher--Smith15.1.20(1), printed p.1094, using14.1.6(1).
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Perfect subgroups of the actual maximal local group fix its original local module. -/
theorem perfect_subgroup_centralizes_localModule
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M L : Subgroup G} (hM : IsOrderingMaximal T M)
    [Group.IsPerfect L] (hLM : L ≤ M) :
    L ≤ centralizer (localModule T M : Set G) := by
  exact (le_map_solvableResidual_of_isPerfect L M hLM).trans
    (residual_le_centralizer_localModule
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hG T hempty
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩)

/-- The actual selected Case-I component escapes M, without a global-family premise. -/
theorem CaseIComponentData.L_not_le_M
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (d : CaseIComponentData T M Mc V) : ¬ d.L ≤ M := by
  intro hLM
  let : Group.IsPerfect (d.L.subgroupOf d.G1) := d.L_isCComponent_in_G1.perfect
  have hLG1 : d.L ≤ d.G1 := d.L_component.1
  let : Group.IsPerfect d.L := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hLG1).toMonoidHom)
    (subgroupOfEquivOfLe hLG1).surjective
  exact d.L_not_le_Mc ((perfect_subgroup_centralizes_localModule hG T hempty hM hLM).trans
    (localModule_centralizer_le_partner T M hu))

/-- The original Nine branch supplies a component outside both selected
maximal groups. Its normalizer also escapes M, as needed by15.1.20. -/
theorem PreparedChosenModule.source_caseI_nine_outside
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
    ∃ d : CaseIComponentData T M Mc V, d.row = .four ∧ Nat.card d.Z1 = 2 ∧
      pPrimeCore 2 d.G1 = ⊥ ∧ IsQuasisimple (d.L ⧸ pCore 2 d.L) ∧
      d.L ∈ Chapter1.L G d.S ∧ Chapter1.IsSylowIn 2 d.SL d.L ∧
      ¬ d.L ≤ M ∧ ¬ normalizer (d.L : Set G) ≤ M := by
  obtain ⟨d,hr,hz,ho,hq,hlocal,hsyl,_⟩ :=
    h.source_caseI_nine_components hG T hempty hM hmany hJ hu hne hfull h9 hres
  have hout := d.L_not_le_M hG T hempty hM hu
  exact ⟨d,hr,hz,ho,hq,hlocal,hsyl,hout,
    ComponentModels.source20_normalizer_not_le_M hout⟩

end CFSG.Quasithin.Chapter15.Section01
