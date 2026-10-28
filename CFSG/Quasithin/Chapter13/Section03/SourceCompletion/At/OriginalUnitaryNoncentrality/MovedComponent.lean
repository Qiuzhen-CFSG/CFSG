module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.MovedComponent
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalUnitaryNoncentrality.SourceComponentGeometry

/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalUnitaryNoncentrality.MovedComponent`.
Its proof retains the original subgroups, actions, relative Sylow placement,
and quotient maps. Only the earlier 12.2.2 and 12.2.13 inputs are restricted
to the fixed G,T. The universal public API remains in the imported module.
The source argument and reference are recorded there; no additional local
classification or normalizer premise is introduced by this specialization.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Atlas.G2.Natural.BinaryPointFlag
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Original (a)--(f), with the native point-action premises discharged. -/
theorem unitary_original_moved_component
    (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
    (h : Hypothesis1331 D.T D.L) (chosen : ChosenModule D.T D.L D.V)
    (hmax : D.L ∈ Chapter1.LStar G (D.T : Subgroup G))
    (eL : (D.L ⧸ pCore 2 D.L) ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (structural : Structural1222At KnownSimple.IsKnownSimple D.T)
    (e : inducedAutomizer D.V D.L ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E0 : Additive D.V ≃ₗ[F] Atlas.G2.Natural.Space F)
    (he0 : ∀ (l : inducedAutomizer D.V D.L) v,
      E0 (automizerRepresentation D.V l v) =
        Atlas.G2.Natural.derivedAction F (e l) (E0 v))
    (hUV : D.Vplus ≤ D.V) (hZV : D.V₁ ≤ D.V)
    (hTZ : (D.T : Subgroup G) ≤ normalizer (D.V₁ : Set G))
    (hTU : (D.T : Subgroup G) ≤ normalizer (D.Vplus : Set G))
    (hZ : Nat.card D.V₁ = 2) (hU : Nat.card D.Vplus = 8)
    (B : Subgroup G) (hBV : B ≤ D.V)
    (hTB : (D.T : Subgroup G) ≤ normalizer (B : Set G)) (hB : Nat.card B = 4)
    (hHfull : D.H = normalizer (D.V₁ : Set G))
    (earlier : Theorem12213At KnownSimple.IsKnownSimple D.T)
    (hplanes : UnitaryPlaneCentralizers D.V (normalizer (D.L : Set G)))
    (h1332 : Noncentrality.SupercriticalSource.Source1332OneTwo D.T)
    (hc : ⁅D.QH,B⁆ = ⊥) :
    ∃ K : Subgroup D.H, K.IsCComponent ∧
      IsComponent (Noncentrality.Star D.H) (K.map (QuotientGroup.mk' (pCore 2 D.H))) ∧
      (∀ hLH : D.L₁ ≤ D.H,
        ⁅K.map (QuotientGroup.mk' (pCore 2 D.H)),
          (Noncentrality.star D.H D.L₁ hLH).pCoreIn 2⁆ ≠ ⊥) ∧
      D.L₁.subgroupOf D.H ≤ normalizer (K : Set D.H) ∧
      ⁅K,D.L₁.subgroupOf D.H⁆ = K ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      K.map D.H.subtype ∈ MainForward.faithfulLocalComponents D.T ∧
      K.map D.H.subtype ∈ Chapter1.LStar G D.T ∧
      D.H ≤ normalizer (K.map D.H.subtype : Set G) ∧
      ¬ D.L ≤ normalizer (K.map D.H.subtype : Set G) ∧
      ¬ K.map D.H.subtype ≤ normalizer (D.L : Set G) ∧
      ¬ (pResidual 2 (D.L ⊓ normalizer (B : Set G) : Subgroup G)).map
          (D.L ⊓ normalizer (B : Set G)).subtype ≤ normalizer (K.map D.H.subtype : Set G) ∧
      ⁅K.map D.H.subtype,Stellmacher.elementaryAbelianMaxJ (D.T : Subgroup G)⁆ = K.map D.H.subtype := by
  obtain ⟨hTN,hNL⟩ := unitary_original_module_normalizers h hmax eL chosen structural
  have ha := (unitary_flag_reduction_a D h chosen hTN hNL
    e E0 he0 hUV hZV hTZ hTU hZ hU B hBV hTB hB hHfull hc).2
  have hb := unitary_original_residual_solvable_and_odd_rank D h chosen hmax eL structural
    e E0 he0 hUV hZV hTZ hTU hZ hU B hBV hTB hB hHfull earlier hplanes
  have hTH : (D.T : Subgroup G) ≤ D.H := hHfull ▸ hTZ
  have hZn : D.V₁ ≠ ⊥ := D.V₁.one_lt_card_iff_ne_bot.mp (by omega)
  have hH : IsTwoLocal D.H := by
    rw [hHfull]
    exact ⟨D.V₁,hZn,(IsElementaryAbelian.isPGroup 2 D.V).to_le hZV,rfl⟩
  have hHe := Chapter1.twoLocal_mem_He_of_sylow_le D.T (h.qtke.evenCharacteristic D.T) hH hTH
  have hL1 : D.L₁ ≤ D.L ⊓ centralizer (D.V₁ : Set G) := map_subtype_le _
  have hLH : D.L₁ ≤ D.H := by
    rw [hHfull]
    exact (hL1.trans inf_le_right).trans (Subgroup.centralizer_le_normalizer _)
  have hTC : (D.T : Subgroup G) ≤ normalizer (centralizer (D.V₁ : Set G) : Set G) :=
    hTZ.trans (normalizer_le_normalizer_centralizer D.V₁)
  have hTL1 : (D.T : Subgroup G) ≤ normalizer (D.L₁ : Set G) :=
    ((le_inf chosen.sylow_normalizes_component hTC).trans inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image
        (D.L ⊓ centralizer (D.V₁ : Set G)) (pResidual 2 (D.L ⊓ centralizer (D.V₁ : Set G) : Subgroup G)))
  have hL : IsPPerfect 2 D.L₁ := isPPerfect_embedded_pResidual 2 _
  obtain ⟨rho,E,he,_,hd,hz,_,hs⟩ := exists_unitary_flag_marking D.T D.L D.V₁ B D.Vplus
    chosen.normalizes hNL e E0 he0 hTN hZV hBV hUV hTZ hTB hTU hZ hB hU
  let : IsSimpleGroup Atlas.G2.Natural.BinaryNormalizer.Derived := Atlas.G2.isSimple_commutator_binary
  have hfaith : D.L ⊓ centralizer (D.V : Set G) ≤ D.L.pCoreIn 2 := by
    have hh := congrArg (map D.L.subtype) (chosen.centralizer_eq_core_of_simple eL.isSimpleGroup)
    exact (show D.L ⊓ centralizer (D.V : Set G) = D.L.pCoreIn 2 by
      simpa only [pCoreIn,subgroupOf_map_subtype,inf_comm] using hh).le
  have hres : pResidual 2 D.L = ⊤ :=
    (pResidual_eq_top_iff 2 D.L).mpr (Chapter1.Section02.Adequate.mem_L_isPPerfect hmax.1)
  have hL3 : Nat.card (D.L₁ ⧸ pCore 2 D.L₁) = 3 :=
    unitary_point_residual_quotient_card D.L D.V₁ rho E he hz hZV chosen.normalizes hfaith hres hd
  have hmoves : ¬ D.L₁.pCoreIn 2 ≤ centralizer (D.Vplus : Set G) :=
    unitary_point_residual_core_moves_seed D.L D.V₁ D.Vplus rho E he hz hs hZV hUV
      chosen.normalizes hfaith hres hd
  have hn := Noncentrality.reduction_c_of_reduction_a D.H D.L₁ D.Vplus hLH ha hmoves
  have h12 := unitary_original_hypothesis1223 h hmax eL
  have huniq := h12.source_normalizer_maximal_unique_at structural
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hout : ¬ D.H ≤ normalizer (D.L : Set G) := by
    rw [hHfull]
    exact unitary_original_line_escape h h12 earlier chosen e E0 he0 hZV hZ
  obtain ⟨K,hK,hKs,hm,hnK,hgen,hq⟩ := Noncentrality.source_moved_component_of_source1332
    h.qtke D.T h1332 D.H D.L₁ D.UH (normalizer (D.L : Set G)) hHe hH hTH hLH hTL1
    hL hL3 huniq.1 chosen.sylow_normalizes_component hout ha hb.2 hn
  obtain ⟨hf,hstar,hHN,hN,_,hLN,hKM,hX⟩ := unitary_original_selected_component_geometry
    D h chosen hmax eL structural e E0 he0 hUV hZV hTZ hTU hZ hU
    B hBV hTB hB hHfull earlier hplanes h1332 hc K hK
  have hj := unitary_component_thompson_generation h.qtke D.T D.V₁ D.H
    (normalizer (D.L : Set G)) (hZV.trans chosen.le_sylow) hZ hTZ hHfull
    K hq hf hstar hHN hN huniq.1 chosen.sylow_normalizes_component hKM
  exact ⟨K,hK,hKs,fun _ => hm,hnK,hgen,hq,hf,hstar,hHN,hLN,hKM,hX,hj⟩
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
