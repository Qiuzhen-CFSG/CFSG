module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeOriginal.MSGeometry
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.CheckedCenterAction.Models
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters

/-!
# Original linear-three MS alternatives

The natural and doubled-natural section models carry the actual source
four-group into their representations. Its stabilizer determines the
parabolic residual, so the source residual and the whole component have the
same fixed subgroup in U. The checked-center identity then makes the original
marked conjugate centralize K, contradicting 13.6.17.

This applies to the first three alternatives of C.1.34. The fifth is excluded
by the original central involution. Thus the original 13.6.22 configuration
reduces the full module alternatives to case four. The C.1.34 classification
and the case-four nonabelian-center argument remain independent inputs.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, C.1.34,
printed pp.136–137, and 13.6.22, printed pp.932–933.
-/

public section
open Subgroup Representation Stellmacher
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
open A5Module ComponentSelection BinaryRankTwo MSSourceModels.NonabelianCenters
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {K L M V V₁ V₂ : Subgroup G}

theorem center_centralizes_markedA_of_localConfiguration
    (d : FlagSource T L V V₁ V₂) (c : LocalConfiguration M d.flag)
    (hp : IsPPerfect 2 K)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hn : Tv (T : Subgroup G) (markedV d.flag.module) ≤ normalizer (K : Set G))
    (hLK : Lv L (markedV d.flag.module) ≤ K)
    (hchar : Theory.GroupTheory.generalizedFitting (Gv (markedV d.flag.module)) =
      pCore 2 (Gv (markedV d.flag.module)))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hU : IsElementaryAbelian 2 (BinaryRankTwo.sourceU K))
    (hcenter : ⁅BinaryRankTwo.CenterPreimage.sourceZ0 K (markedV d.flag.module) hK.1.1, K⁆ =
      BinaryRankTwo.sourceU K)
    (hfix : BinaryRankTwo.sourceU K ⊓ centralizer (Lv L (markedV d.flag.module) : Set G) =
      BinaryRankTwo.sourceU K ⊓ centralizer (K : Set G)) :
    K ≤ Gv (markedA d.flag.module) := by
  let := hU
  obtain ⟨e⟩ := center_sourceLineData_of_localConfiguration d c hp hK hn hLK hchar hTL
  obtain ⟨P, hP⟩ := SourceActors.exists_source_sylow hn e.sylow e.sylow_eq
  have hP' : (P : Subgroup K).map K.subtype ≤ Tv (T : Subgroup G) (markedV d.flag.module) := by
    rintro _ ⟨k, hk, rfl⟩
    rw [hP] at hk
    exact hk
  have hv : markedV d.flag.module ^ 2 = 1 := by
    change d.flag.module.map (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v) ^ 2 = 1
    rw [← map_pow]
    exact (congrArg d.flag.module.map
      (show (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v) ^ 2 = 1
        by decide +kernel)).trans d.flag.module.map.map_one
  have haD : ((inclusion inf_le_right c.aPoint : Gv (markedV d.flag.module)) : G) ∈
      centralizer (Lv L (markedV d.flag.module) : Set G) := by
    change (c.aPoint : G) ∈ _
    rw [c.aPoint_val]
    exact c.a_centralizes.2
  have ha : checkedQuotientMap (markedV d.flag.module) (inclusion inf_le_right c.aPoint) ∈
      centralizer (checkedImage (markedV d.flag.module)
        (Tv (T : Subgroup G) (markedV d.flag.module)) : Set (Gcheck (markedV d.flag.module))) := by
    rintro x ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (mem_center_iff.mp c.a_checked_central
      ((checkedSylowMap (T : Subgroup G) (markedV d.flag.module)).rangeRestrict ⟨y, hy⟩))
  have hc := checked_centralizes_of_center_preimage_commutator L K
    (Tv (T : Subgroup G) (markedV d.flag.module)) (BinaryRankTwo.sourceU K)
    (markedV d.flag.module) hK.1.1 hv hp hcenter hn c.reductions.centralizerSylow
    c.reductions.sylow_image P hP' hchar hLK hfix
    (inclusion inf_le_right c.aPoint) haD ha
  change K ≤ Gv (c.aPoint : G) at hc
  rwa [c.aPoint_val] at hc

theorem natural_section_centralizes_markedA_of_localConfiguration
    (d : FlagSource T L V V₁ V₂) (c : LocalConfiguration M d.flag)
    (hp : IsPPerfect 2 K)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hn : Tv (T : Subgroup G) (markedV d.flag.module) ≤ normalizer (K : Set G))
    (hLK : Lv L (markedV d.flag.module) ≤ K)
    (hchar : Theory.GroupTheory.generalizedFitting (Gv (markedV d.flag.module)) =
      pCore 2 (Gv (markedV d.flag.module)))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (hmodel : HasSectionModel K (BinaryRankTwo.sourceU K) ⊥ (linearThreeActor e) BinaryLinearThree.W)
    (hcenter : ⁅BinaryRankTwo.CenterPreimage.sourceZ0 K (markedV d.flag.module) hK.1.1, K⁆ =
      BinaryRankTwo.sourceU K) :
    K ≤ Gv (markedA d.flag.module) := by
  obtain ⟨dL⟩ := center_sourceLineData_of_localConfiguration d c hp hK hn hLK hchar hTL
  obtain ⟨m, hm⟩ := MSSourceModels.natural_model_of_section e hmodel
  have hf := natural_model_source_centralizer_eq dL m
    (hm ▸ MSSourceModels.linearThreeActor_surjective e)
    (by rw [hm, MSSourceModels.linearThreeActor_kernel])
  exact center_centralizes_markedA_of_localConfiguration d c hp hK hn hLK hchar hTL
    (MSSourceModels.sourceU_elementary_of_model hp m) hcenter hf

theorem doubled_section_centralizes_markedA_of_localConfiguration
    (d : FlagSource T L V V₁ V₂) (c : LocalConfiguration M d.flag)
    (hp : IsPPerfect 2 K)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hn : Tv (T : Subgroup G) (markedV d.flag.module) ≤ normalizer (K : Set G))
    (hLK : Lv L (markedV d.flag.module) ≤ K)
    (hchar : Theory.GroupTheory.generalizedFitting (Gv (markedV d.flag.module)) =
      pCore 2 (Gv (markedV d.flag.module)))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (hmodel : HasSectionModel K (BinaryRankTwo.sourceU K) ⊥ (linearThreeActor e)
      (BinaryLinearThree.W.prod BinaryLinearThree.W))
    (hcenter : ⁅BinaryRankTwo.CenterPreimage.sourceZ0 K (markedV d.flag.module) hK.1.1, K⁆ =
      BinaryRankTwo.sourceU K) :
    K ≤ Gv (markedA d.flag.module) := by
  obtain ⟨dL⟩ := center_sourceLineData_of_localConfiguration d c hp hK hn hLK hchar hTL
  obtain ⟨m, hm⟩ := MSSourceModels.doubled_model_of_section e hmodel
  have hf := doubled_model_source_centralizer_eq dL m
    (hm ▸ MSSourceModels.linearThreeActor_surjective e)
    (by rw [hm, MSSourceModels.linearThreeActor_kernel])
  exact center_centralizes_markedA_of_localConfiguration d c hp hK hn hLK hchar hTL
    (MSSourceModels.sourceU_elementary_of_model hp m) hcenter hf
variable {S : Subgroup G}

theorem msModule_centralizes_markedA_or_caseFour
    (d : FlagSource T L V V₁ V₂) (c : LocalConfiguration M d.flag)
    (hp : IsPPerfect 2 K)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hn : Tv (T : Subgroup G) (markedV d.flag.module) ≤ normalizer (K : Set G))
    (hLK : Lv L (markedV d.flag.module) ≤ K)
    (hchar : Theory.GroupTheory.generalizedFitting (Gv (markedV d.flag.module)) =
      pCore 2 (Gv (markedV d.flag.module)))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hS : Chapter1.IsSylowIn 2 S (K ⊔ Tv (T : Subgroup G) (markedV d.flag.module)))
    (hTS : Tv (T : Subgroup G) (markedV d.flag.module) ≤ S)
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (hmodel : MSModuleAlternatives K (Tv (T : Subgroup G) (markedV d.flag.module)) S 1 (ZMod 2) e) :
    K ≤ Gv (markedA d.flag.module) ∨
      CaseFour K (Tv (T : Subgroup G) (markedV d.flag.module)) S e := by
  have hv : markedV d.flag.module ^ 2 = 1 := by
    change d.flag.module.map (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v) ^ 2 = 1
    rw [← map_pow]
    exact (congrArg d.flag.module.map
      (show (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v) ^ 2 = 1
        by decide +kernel)).trans d.flag.module.map.map_one
  rcases hmodel with h | h | h | h | h
  · obtain ⟨hU, _, hcenter⟩ := MSSourceModels.natural_ms_section_realization
      (markedV d.flag.module) hK.1.1 hv hK.1.2.1.subnormal hp e h.2.2
    apply Or.inl
    apply natural_section_centralizes_markedA_of_localConfiguration d c hp hK hn hLK hchar hTL e _ hcenter
    change HasSectionModel K (MSSourceModels.sourceU K) ⊥ (linearThreeActor e) BinaryLinearThree.W
    rw [hU]
    exact h.2.2
  · obtain ⟨hU, _, hcenter⟩ := MSSourceModels.doubled_ms_section_realization
      (markedV d.flag.module) hK.1.1 hv hK.1.2.1.subnormal hp e h.1
    apply Or.inl
    apply doubled_section_centralizes_markedA_of_localConfiguration d c hp hK hn hLK hchar hTL e _ hcenter
    change HasSectionModel K (MSSourceModels.sourceU K) ⊥ (linearThreeActor e)
      (BinaryLinearThree.W.prod BinaryLinearThree.W)
    rw [hU]
    exact h.1
  · have hthree : CaseThree K (Tv (T : Subgroup G) (markedV d.flag.module)) S e := h
    obtain ⟨hU, _, hcenter⟩ := caseThree_realization
      (markedV d.flag.module) hK.1.1 hv hK.1.2.1.subnormal hp e hthree
    apply Or.inl
    apply natural_section_centralizes_markedA_of_localConfiguration d c hp hK hn hLK hchar hTL e _ hcenter
    change HasSectionModel K (MSSourceModels.sourceU K) ⊥ (linearThreeActor e) BinaryLinearThree.W
    rw [hU]
    exact hthree.1
  · exact Or.inr h
  · have hzmem := (mem_omegaOneCenterAmbient_iff (T : Subgroup G) _).mp d.flag.z_central
    have hzOmega : markedZ d.flag.module ∈ omegaOneCenterAmbient
        (Tv (T : Subgroup G) (markedV d.flag.module)) :=
      (mem_omegaOneCenterAmbient_iff _ _).mpr
        ⟨⟨hzmem.1, markedZ_mem_Gv d.flag.module⟩, hzmem.2.1, fun t ht => hzmem.2.2 t ht.1⟩
    exact (MSSourceModels.SeedCarrier.not_ms_caseFive hK hn hzOmega hS hTS e h).elim
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
