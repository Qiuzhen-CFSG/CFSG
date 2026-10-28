module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Ordinary.FullSelection
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Ordinary.BinaryModels
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
/-!
# Ordinary exclusions on one source component

The original Nine marker retains its complete ordinary1.1.5 action marking,
its literal residual escape and fixed-plane movement. On this same component,
the Mathieu/J2 and four small binary Lie alternatives are excluded using their
intrinsic fixer bounds. The actual C-component is ordinary or constrained;
no exhaustive quotient catalogue is assumed here.
Source: Aschbacher--Smith15.1.19--22,15.1.25--26.
-/
public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor Section03 Section03.InitialSource ChapterA.Section05To06
open Theory.SpecificGroups.BinaryComponentResidual
variable {G : Type*} [Group G] [Finite G]

/-- The selected source C-component is ordinary or has its own F* equal to O2. -/
theorem CaseIComponentData.ordinary_or_constrained
    {T : Sylow 2 G} {M Mc V : Subgroup G} (d : CaseIComponentData T M Mc V)
    (ho : pPrimeCore 2 d.G1 = ⊥) :
    IsComponent d.G1 (d.L.subgroupOf d.G1) ∨ generalizedFitting d.L = pCore 2 d.L := by
  rcases d.L_isCComponent_in_G1.component_or_generalizedFitting_eq_pCore ho with hc | hf
  · exact Or.inl hc
  · right
    let e : d.L.subgroupOf d.G1 ≃* d.L := subgroupOfEquivOfLe d.L_component.1
    have hh := congrArg (map e.toMonoidHom) hf
    rwa [map_generalizedFitting_equiv, pCore_map_iso] at hh

private theorem source_plane_contradiction
    {T : Sylow 2 G} {M Mc V : Subgroup G} (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M) (h : PreparedChosenModule T M V)
    [IsQuasisimple (d.L ⧸ pCore 2 d.L)] (hf : Facts (d.L ⧸ pCore 2 d.L))
    (heq : d.S ⊓ centralizer (((primeToResidual 3 (M ⊓ d.L : Subgroup G)).map
      (M ⊓ d.L).subtype) : Set G) = d.S ⊓ centralizer (d.L : Set G))
    (hm : ¬ V ⊓ centralizer (((pResidual 2 (M ⊓ d.G1 : Subgroup G)).map
      (M ⊓ d.G1).subtype) : Set G) ≤ centralizer (d.L : Set G)) : False := by
  let := h.elementary
  have hY := (d.source_cubic_component hG h hf).2
  let C := M ⊓ d.G1
  let R := (pResidual 2 C).map C.subtype
  let Y := (primeToResidual 3 C).map C.subtype
  let V1 := V ⊓ centralizer (R : Set G)
  have hYR : Y ≤ R := map_mono (le_pResidual_of_isPPerfect _
    (isPPerfect_primeToResidual 3 2 (by decide)))
  have hVT : V ≤ (T : Subgroup G) := by
    let : (V.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer h.normalized
    let := IsElementaryAbelian.subgroupOf h.le_selected (p := 2)
    have hh := (IsElementaryAbelian.isPGroup 2 (V.subgroupOf M)).le_sylow_of_normal
      (T.subtype hTM)
    simpa only [map_subgroupOf_eq_of_le h.le_selected, Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hTM] using map_mono (f := M.subtype) hh
  have hV1SY : V1 ≤ d.S ⊓ centralizer (Y : Set G) :=
    le_inf (le_inf (inf_le_left.trans hVT)
      (inf_le_left.trans (V.le_centralizer.trans
        (centralizer_le (d.Z1_le_fixed.trans inf_le_left)))))
      (inf_le_right.trans (centralizer_le hYR))
  have heq' : d.S ⊓ centralizer (Y : Set G) = d.S ⊓ centralizer (d.L : Set G) := by
    change d.S ⊓ centralizer (((primeToResidual 3 (M ⊓ d.G1 : Subgroup G)).map
      (M ⊓ d.G1).subtype) : Set G) = _
    rw [hY]
    exact heq
  exact hm ((hV1SY.trans heq'.le).trans inf_le_right)

theorem PreparedChosenModule.source_caseI_nine_ordinary_model_exclusions
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
      Chapter1.IsSylowIn 2 d.S d.G1 ∧ ¬ d.L ≤ M ∧
      (IsComponent d.G1 (d.L.subgroupOf d.G1) → d.OrdinarySource) ∧
      let R := (pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype
      let V1 := V ⊓ centralizer (R : Set G)
      let V2 := ⁅V,R⁆
      Nat.card V1 = 4 ∧ Nat.card V2 = 4 ∧ V1 ⊔ V2 = V ∧ V1 ⊓ V2 = ⊥ ∧
      d.Z1 ≤ V1 ∧ d.S.relIndex (T : Subgroup G) = 2 ∧
      ¬ (primeToResidual 3 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype ≤ d.MZ ∧
      (Facts (d.L ⧸ pCore 2 d.L) → ¬ V1 ≤ centralizer (d.L : Set G)) ∧
      (IsComponent d.G1 (d.L.subgroupOf d.G1) ∨
        generalizedFitting d.L = pCore 2 d.L) ∧
      (IsComponent d.G1 (d.L.subgroupOf d.G1) →
        ¬ CaseIComponentData.SmallOrdinaryModel (d.L ⧸ pCore 2 d.L) ∧
        ¬ CaseIComponentData.SmallBinaryOrdinaryModel (d.L ⧸ pCore 2 d.L)) := by
  let := h.elementary
  obtain ⟨d,hr,hz,ho,hq,hL,hSL,hs,houtM,ha,hv1,hv2,hj,hi,hzv,hidx,hout,hm⟩ :=
    h.source_caseI_nine_component_selection hG T hempty hM hmany hJ hu hne hfull h9 hres
  refine ⟨d,hr,hz,ho,hq,hL,hSL,hs,houtM,ha,hv1,hv2,hj,hi,hzv,hidx,hout,hm,
    d.ordinary_or_constrained ho,?_⟩
  intro hc
  let := hq
  constructor
  · intro he
    have hf := CaseIComponentData.facts_of_small_model he
    exact source_plane_contradiction d hG hM.1.2 h hf
      (d.ordinary_small_model_centralizer hG hM.1.2 hu h hc ho hSL hf he hout) (hm hf)
  · intro he
    have hf := CaseIComponentData.facts_of_small_binary_model he
    exact source_plane_contradiction d hG hM.1.2 h hf
      (d.ordinary_small_binary_model_centralizer hG hM.1.2 hu h hc ho hSL he hout) (hm hf)
end CFSG.Quasithin.Chapter15.Section01
