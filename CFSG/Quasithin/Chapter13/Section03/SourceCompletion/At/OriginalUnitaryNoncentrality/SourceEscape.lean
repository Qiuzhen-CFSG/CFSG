module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.SourceEscape
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalUnitaryNoncentrality.BaumannEscape

/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalUnitaryNoncentrality.SourceEscape`.
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
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Noncentrality
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original contrary plane-centrality assumption forces precisely the
Baumann normalizer escape contradicted by 13.3.10(2) in the unitary case.
The plane-centralizer and earlier universal source statements remain explicit;
no local component, module, radical identity or diagonal premise is assumed. -/
theorem unitary_original_baumann_escape
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
    (fixed : OriginalFixedModule1332At D.T D.L)
    (five : OriginalAlternatingFiveModules1332At D.T D.L)
    (hc : ⁅D.QH,B⁆ = ⊥) :
    ¬ normalizer (ChapterB.baumann ((D.L₁ ⊔ (D.T : Subgroup G)).pCoreIn 2) : Set G) ≤
      normalizer (D.L : Set G) := by
  obtain ⟨K,hK,hKs,hm,hn,hgen,hq,hf,hstar,hHN,hLN,hKM,hX,hJgen⟩ :=
    unitary_original_moved_component D h chosen hmax eL structural e E0 he0 hUV hZV
      hTZ hTU hZ hU B hBV hTB hB hHfull earlier hplanes h1332 hc
  have hnot := unitary_original_reduction_g D h chosen hmax eL structural e E0 he0
    hUV hZV hTZ hTU hZ hU B hBV hTB hB hHfull fixed hc K hK hq hf hHN hJgen
  have hTH : (D.T : Subgroup G) ≤ D.H := hHfull ▸ hTZ
  have hZn : D.V₁ ≠ ⊥ := D.V₁.one_lt_card_iff_ne_bot.mp (by omega)
  have hH : IsTwoLocal D.H := by
    rw [hHfull]
    exact ⟨D.V₁,hZn,(IsElementaryAbelian.isPGroup 2 D.V).to_le hZV,rfl⟩
  have hL1 : D.L₁ ≤ D.L ⊓ centralizer (D.V₁ : Set G) := map_subtype_le _
  have hLH : D.L₁ ≤ D.H := by
    rw [hHfull]
    exact (hL1.trans inf_le_right).trans (Subgroup.centralizer_le_normalizer _)
  have hTA : (D.T : Subgroup G) ≤ normalizer (D.L₁ : Set G) :=
    ((le_inf chosen.sylow_normalizes_component
      (hTZ.trans (normalizer_le_normalizer_centralizer D.V₁))).trans
      inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image
        (D.L ⊓ centralizer (D.V₁ : Set G))
        (pResidual 2 (D.L ⊓ centralizer (D.V₁ : Set G) : Subgroup G)))
  have hA : IsPPerfect 2 D.L₁ := isPPerfect_embedded_pResidual 2 _
  obtain ⟨hTN,hNL⟩ := unitary_original_module_normalizers h hmax eL chosen structural
  obtain ⟨rho,E,he,_,hd,hz,_,_⟩ := exists_unitary_flag_marking D.T D.L D.V₁ B D.Vplus
    chosen.normalizes hNL e E0 he0 hTN hZV hBV hUV hTZ hTB hTU hZ hB hU
  let : IsSimpleGroup Atlas.G2.Natural.BinaryNormalizer.Derived := Atlas.G2.isSimple_commutator_binary
  have hfaith : D.L ⊓ centralizer (D.V : Set G) ≤ D.L.pCoreIn 2 := by
    have hh := congrArg (map D.L.subtype) (chosen.centralizer_eq_core_of_simple eL.isSimpleGroup)
    exact (show D.L ⊓ centralizer (D.V : Set G) = D.L.pCoreIn 2 by
      simpa only [pCoreIn,subgroupOf_map_subtype,inf_comm] using hh).le
  have hres : pResidual 2 D.L = ⊤ :=
    (pResidual_eq_top_iff 2 D.L).mpr (Chapter1.Section02.Adequate.mem_L_isPPerfect hmax.1)
  have hA3 : Nat.card (D.L₁ ⧸ pCore 2 D.L₁) = 3 :=
    unitary_point_residual_quotient_card D.L D.V₁ rho E he hz hZV chosen.normalizes hfaith hres hd
  obtain ⟨eK⟩ := unitary_selected_five_quotient h.qtke D.T D.H D.L₁ hH hTH hLH
    hA hA3 hTA h1332 K hK hq hf hHN hgen hnot
  have hgenG := congrArg (map D.H.subtype) hgen
  rw [map_commutator,map_subgroupOf_eq_of_le hLH] at hgenG
  exact unitary_baumann_escape_of_selected_five h structural five h1332
    (K.map D.H.subtype) D.L₁ hf eK hTA (hLH.trans hHN) hA hA3 hnot hgenG hKM
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
