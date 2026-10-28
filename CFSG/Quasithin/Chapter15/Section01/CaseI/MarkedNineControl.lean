module
public import CFSG.Quasithin.Chapter15.Section01.CaseI.MarkedNineResidual
public import CFSG.Quasithin.Chapter15.Section01.CaseI.Normalization
public import CFSG.Quasithin.Chapter15.Section01.CaseI.ResidualNormalizer
public import CFSG.Quasithin.Chapter15.Section01.OrderingSource.Assembly
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.LocalAction
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Source normalizer control for the elementary-nine marking

The cyclic Sylow action in original 15.1.7(4) makes the literal centralizer
S = C_T(Z₁) normal in T. The original ordering gives
M_c = (M ∩ M_c) C_{M_c}(V(M_c)). Its residual intersection, together with
15.1.14(1), expresses O²(M_Z) as the join of two T-invariant residuals.
The actual Sylow supplement then proves T-normalization of M_Z.

The final theorem retains the same Z₁ chosen by the Nine source marking
and supplies the Sylow, core and residual normalizer inputs to 15.1.19.
The earlier residual centralization 15.1.14(1) remains explicit; no marked
normality, factorization, core control or component witness is assumed.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
15.1.16(b)--18, printed pp.1092--1093.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A cyclic literal action image makes every relative pointwise fixer normal. -/
theorem chosen_centralizer_normal_of_cyclic_image
    (T : Sylow 2 G) {M V Z1 : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (hZV : Z1 ≤ V)
    (hcyc : IsCyclic (((T : Subgroup G).subgroupOf M).map
      (actionHom M V hn).rangeRestrict)) :
    (((T : Subgroup G) ⊓ centralizer (Z1 : Set G)).subgroupOf
      (T : Subgroup G)).Normal := by
  let f := (actionHom M V hn).rangeRestrict
  let D := ((T : Subgroup G).subgroupOf M).map f
  let C := (centralizer (Z1 : Set G)).subgroupOf M
  let := hcyc
  let g : T →* D := (f.comp (inclusion hTM)).codRestrict D (by
    intro t
    exact mem_map_of_mem f t.property)
  let K := (C.map f).subgroupOf D
  have hker : f.ker ≤ C := by
    intro m hm
    have ha : (actionHom M V hn) m = 1 := congrArg Subtype.val hm
    have hc : m ∈ (actionHom M V hn).ker := ha
    rw [actionHom_ker] at hc
    exact centralizer_le hZV hc
  have he : K.comap g = (((T : Subgroup G) ⊓
      centralizer (Z1 : Set G)).subgroupOf (T : Subgroup G)) := by
    ext t
    change (inclusion hTM t) ∈ (C.map f).comap f ↔
      (t : G) ∈ (T : Subgroup G) ∧ (t : G) ∈ centralizer (Z1 : Set G)
    rw [comap_map_eq_self hker]
    exact ⟨fun ht => ⟨t.property, ht⟩, fun ht => ht.2⟩
  rw [← he]
  exact (normal_of_isMulCommutative K).comap g

omit [Finite G] in
/-- Original 15.1.18(3), for the Sylow centralizer in the Nine row. -/
theorem chosen_nine_centralizer_normal
    (T : Sylow 2 G) {M V Z1 : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (hZV : Z1 ≤ V)
    (h9 : SourceCases.Nine (imageRepresentation M V hn)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict)) :
    (((T : Subgroup G) ⊓ centralizer (Z1 : Set G)).subgroupOf
      (T : Subgroup G)).Normal := by
  obtain ⟨_, _, _, _, _, _, hS, _⟩ := h9
  exact chosen_centralizer_normal_of_cyclic_image T hTM hn hZV hS.1

/-- Derive the literal ordering factorization and both residual normalizations
used in original 15.1.18(3). The earlier marked row supplies its Sylow and
residual intersection, and 15.1.14(1) supplies residual centralization. -/
theorem PreparedChosenModule.caseI_T_normalizes_MZ_from_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V Z1 : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hZ : Z1 ≤ thompsonFixed T V)
    (hSyl : ∃ P : Sylow 2 (M ⊓ centralizer (Z1 : Set G) : Subgroup G),
      (P : Subgroup (M ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
        (M ⊓ centralizer (Z1 : Set G)).subtype =
          (T : Subgroup G) ⊓ centralizer (Z1 : Set G))
    (hSnT : (((T : Subgroup G) ⊓ centralizer (Z1 : Set G)).subgroupOf
      (T : Subgroup G)).Normal)
    (hresI : (pResidual 2 (M ⊓ Mc ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
        (M ⊓ Mc ⊓ centralizer (Z1 : Set G)).subtype =
      (pResidual 2 (M ⊓ centralizer (V : Set G) : Subgroup G)).map
        (M ⊓ centralizer (V : Set G)).subtype)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    (T : Subgroup G) ≤ normalizer (centralizer (Z1 : Set G) ⊓ Mc : Set G) := by
  let G1 := centralizer (Z1 : Set G)
  let MZ := G1 ⊓ Mc
  let A := M ⊓ Mc
  let C := Mc ⊓ centralizer (localModule T Mc : Set G)
  let R := (pResidual 2 (M ⊓ centralizer (V : Set G) : Subgroup G)).map
    (M ⊓ centralizer (V : Set G)).subtype
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have ho := source_ordering_of_centralizing_orderingMaximal hG T hempty hM hJ Mc
    ⟨hMc.1, hTMc⟩
  have hfactor : Mc = A ⊔ C := by
    apply le_antisymm ?_ (sup_le inf_le_right inf_le_left)
    intro x hx
    obtain ⟨a, ha, c, hc, rfl⟩ := ho x hx
    exact (A ⊔ C).mul_mem ((show A ≤ A ⊔ C from le_sup_left) ⟨ha.2, ha.1⟩)
      ((show C ≤ A ⊔ C from le_sup_right) hc)
  have hCn : Mc ≤ normalizer (C : Set G) :=
    (le_inf Mc.le_normalizer ((le_normalizer_conjugateSpanBy _ _).trans
      (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hCZ : C ≤ centralizer (centralInvolutions T : Set G) :=
    inf_le_right.trans (centralizer_le (le_conjugateSpanBy _ _))
  have hresC : (pResidual 2 C).map C.subtype ≤ MZ :=
    le_inf ((embedded_pResidual_mono 2 hCZ).trans
      (hres.trans (centralizer_le hZ))) ((map_subtype_le _).trans inf_le_left)
  have hAMZ : A ⊓ MZ = M ⊓ Mc ⊓ G1 := by
    ext x
    simp only [A, MZ, mem_inf]
    tauto
  have hresA : (pResidual 2 (A ⊓ MZ : Subgroup G)).map (A ⊓ MZ).subtype = R := by
    rw [hAMZ]
    exact hresI
  have hMn : M ≤ normalizer (M ⊓ centralizer (V : Set G) : Set G) :=
    (le_inf M.le_normalizer (h.normalized.trans
      (normalizer_le_normalizer_centralizer V))).trans inf_normalizer_le_normalizer_inf
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (hM.1.2.trans hMn).trans (normalizer_le_normalizer_characteristic_image
      (M ⊓ centralizer (V : Set G)) (pResidual 2 (M ⊓ centralizer (V : Set G) : Subgroup G)))
  have hSylG : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ G1) G1 :=
    h.caseI_centralizer_sylow hG T hM hJ hZ (by
      rw [inf_comm (centralizer (Z1 : Set G)) M]
      exact hSyl)
  have hSylMZ : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ G1) MZ :=
    hSylG.restrict (le_inf inf_le_right (inf_le_left.trans hTMc)) inf_le_left
  exact caseI_T_normalizes_MZ_of_ordering_factor T hfactor
    (le_inf hM.1.2 hTMc) hCn inf_le_right hresC hresA hTR
    inf_le_left hSnT hSylMZ

/-- The Nine marking supplies every Sylow and normalizer input to the outside
component construction, retaining only genuine earlier 15.1.14(1). The source
equality V = V(M) is retained to record the original choice in this row. -/
theorem PreparedChosenModule.caseI_nine_source_controls
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
    ∃ Z1 : Subgroup G, Z1 ≤ thompsonFixed T V ∧ Z1 ≠ ⊥ ∧
      M = (M ⊓ centralizer (Z1 : Set G)) ⊔ (T : Subgroup G) ∧
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
        (centralizer (Z1 : Set G)) ∧
      (T : Subgroup G) ≤ normalizer (centralizer (Z1 : Set G) ⊓ Mc : Set G) ∧
      (centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2 ≠ ⊥ ∧
      ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2).characteristicNormalizerClosure ≤ Mc ∧
      centralizer (Z1 : Set G) ⊓
        normalizer ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2 : Set G) =
          centralizer (Z1 : Set G) ⊓ Mc ∧
      ¬ M ⊓ centralizer (Z1 : Set G) ≤ centralizer (Z1 : Set G) ⊓ Mc ∧
      normalizer ((pResidual 2 (centralizer (Z1 : Set G) ⊓ Mc : Subgroup G)).map
        (centralizer (Z1 : Set G) ⊓ Mc).subtype : Set G) ≤ Mc := by
  let := h.elementary
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hNMc : M ⊓ centralizer (V : Set G) ≤ Mc := by
    rw [hfull]
    exact inf_le_right.trans (localModule_centralizer_le_partner T M hu)
  have hMnot : ¬ M ≤ Mc := fun hm => hne (hM.1.1.eq_of_le hMc.1.1 hm)
  obtain ⟨Z1, hZ, hZne, hgen, hSyl, hprime⟩ :=
    chosen_nine_marked_residual T hM.1.2 h.normalized h9
  have hI := caseI_residual_intersection T M Mc V Z1 h.normalized
    (hZ.trans inf_le_left) hNMc hTMc hMnot hgen hSyl (by
      let := caseI_module_centralizer_normal (Z1 := Z1) h.normalized
      rw [hprime]
      decide)
  have hSnT := chosen_nine_centralizer_normal T hM.1.2 h.normalized
    (hZ.trans inf_le_left) h9
  have hTn := h.caseI_T_normalizes_MZ_from_source hG T hempty hM hJ hu hZ hSyl hSnT hI hres
  have hSylG := h.caseI_centralizer_sylow hG T hM hJ hZ
    (by
      rw [inf_comm (centralizer (Z1 : Set G)) M]
      exact hSyl)
  obtain ⟨hc, hn⟩ := CaseIMarkedSubgroup.core_normalizer_control
    hZ hZne hgen hM hu hne h hres hTn
  refine ⟨Z1, hZ, hZne, hgen, hSylG, hTn,
    CaseIMarkedSubgroup.core_nontrivial hZ hZne hM hu h, hc, hn, ?_, ?_⟩
  · exact (CaseIMarkedSubgroup.residual_and_uniqueness hZ hgen hM hu hne hres).2.1
  · exact CaseIMarkedSubgroup.residual_normalizer_control hG
      hZ hZne hgen hM hu hne h hmany hres hTn hSylG

end CFSG.Quasithin.Chapter15.Section01
