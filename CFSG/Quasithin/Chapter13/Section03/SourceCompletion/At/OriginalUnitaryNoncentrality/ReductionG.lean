module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.ReductionG
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalUnitaryNoncentrality.MovedComponent

/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalUnitaryNoncentrality.ReductionG`.
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
open Noncentrality ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Original unitary reduction (g). The chosen moved module, its fixed line,
and the six-core coordinates are all constructed from the original data. -/
theorem unitary_original_reduction_g
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
    (fixed : OriginalFixedModule1332At D.T D.L)
    (hc : ⁅D.QH,B⁆ = ⊥)
    (K : Subgroup D.H) (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : K.map D.H.subtype ∈ MainForward.faithfulLocalComponents D.T)
    (hHN : D.H ≤ normalizer (K.map D.H.subtype : Set G))
    (hJgen : ⁅K.map D.H.subtype,Stellmacher.elementaryAbelianMaxJ (D.T : Subgroup G)⁆ =
      K.map D.H.subtype) :
    ¬ D.L₁ ≤ K.map D.H.subtype := by
  intro hAK
  obtain ⟨hTN,hNL⟩ := unitary_original_module_normalizers h hmax eL chosen structural
  have ha := (unitary_flag_reduction_a D h chosen hTN hNL
    e E0 he0 hUV hZV hTZ hTU hZ hU B hBV hTB hB hHfull hc).2
  have hTH : (D.T : Subgroup G) ≤ D.H := hHfull ▸ hTZ
  have hZn : D.V₁ ≠ ⊥ := D.V₁.one_lt_card_iff_ne_bot.mp (by omega)
  have hH : IsTwoLocal D.H := by
    rw [hHfull]
    exact ⟨D.V₁,hZn,(IsElementaryAbelian.isPGroup 2 D.V).to_le hZV,rfl⟩
  have hL1 : D.L₁ ≤ D.L ⊓ centralizer (D.V₁ : Set G) := map_subtype_le _
  have hLH : D.L₁ ≤ D.H := by
    rw [hHfull]
    exact (hL1.trans inf_le_right).trans (Subgroup.centralizer_le_normalizer _)
  have hA : IsPPerfect 2 D.L₁ := isPPerfect_embedded_pResidual 2 _
  obtain ⟨rho,E,he,_,hd,hz,_,hs⟩ := exists_unitary_flag_marking D.T D.L D.V₁ B D.Vplus
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
  have hAU : D.L₁ ≤ normalizer (D.Vplus : Set G) :=
    point_centralizer_normalizes_marked_seed D.Vplus D.V₁ D.L₁ rho E he hs hz hUV
      (hL1.trans (inf_le_left.trans chosen.normalizes)) (hL1.trans inf_le_right)
  have hgenU : ⁅D.Vplus,D.L₁⁆ = D.Vplus :=
    unitary_point_residual_generates_seed D.L D.V₁ D.Vplus rho E he hz hs hZV hUV
      chosen.normalizes hfaith hres hd
  let : IsElementaryAbelian 2 D.Vplus := IsElementaryAbelian.of_le hUV
  have hUW := seed_le_movedModule_of_actor_le D.T D.H D.L₁ D.Vplus hTH hLH hU hA
    hA3 hAU hTU hgenU ((le_conjugateSpanBy D.Vplus D.H).trans ha) K hK hqK hHN hAK
  have hZU : D.V₁ ≤ D.Vplus := by
    intro z hz'
    let v : Additive D.V := Additive.ofMul ⟨z,hZV hz'⟩
    exact (mem_pointCoordinateSubspace E D.Vplus v).mp (hs.symm ▸
      pointLine_le_seed (hz ▸ (mem_pointCoordinateSubspace E D.V₁ v).mpr hz'))
  let A := K.map D.H.subtype
  let J := Diagonal.localGroup A D.L₁ D.T
  let W := Diagonal.movedModule A D.L₁ D.T
  have hZC : D.V₁ ≤ centralizer (A : Set G) := by
    apply le_centralizer_iff.mp
    exact (map_subtype_le K).trans (hHfull ▸
      normalizer_le_centralizer_of_card_two D.V₁ hZ)
  have hfix : W ⊓ centralizer (A : Set G) ≠ ⊥ := fun he =>
    hZn (le_bot_iff.mp ((le_inf (hZU.trans hUW) hZC).trans he.le))
  have hAJ : A ≤ J := le_sup_left.trans le_sup_left
  have hJH : J ≤ D.H := sup_le (sup_le (map_subtype_le K) hLH) hTH
  have hKJ : (A.subgroupOf J).IsCComponent := by
    have hh : (A.subgroupOf D.H).IsCComponent := by
      change ((K.map D.H.subtype).comap D.H.subtype).IsCComponent
      rwa [comap_map_eq_self_of_injective D.H.subtype_injective]
    exact hh.subgroupOf_of_le hAJ hJH
  let := hqK
  let c : K ≃* A := K.equivMapOfInjective D.H.subtype D.H.subtype_injective
  have hqA : IsQuasisimple (A ⧸ pCore 2 A) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ c (pCore_map_iso 2 c))
  have hSQH := h.qtke.twoLocal_sqtk hH
  have hSQJ : IsSQTK KnownSimple.IsKnownSimple J :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hJH)).mp (hSQH.subgroup (J.subgroupOf D.H))
  have hfaithA := ((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff D.T A).mp hf).2.2
  obtain ⟨C⟩ := containing_moved_module_chosen D.T A D.L₁ hAK (hTH.trans hHN)
    hSQJ hKJ hqA hfaithA hJgen hfix
  obtain ⟨ec⟩ := fixed h A hf W C hfix
  obtain ⟨β,hβ,cW,hcW⟩ := faithful_chosen_action_coordinates C _ ec
  exact unitary_point_residual_core_moves_seed D.L D.V₁ D.Vplus rho E he hz hs hZV hUV
    chosen.normalizes hfaith hres hd
    (BinaryPermutation.SixCover.core_model_twoCore_centralizes_seed A D.L₁ W D.Vplus D.V₁
      hAK hA C.normalizes hAU hUW hZU hZC hU hZ β hβ cW hcW)

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
