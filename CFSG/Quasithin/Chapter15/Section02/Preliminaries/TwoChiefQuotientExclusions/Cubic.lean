module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.TwoChiefQuotientExclusions.Pair
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.CentralOmegaCubic
public import Theory.GroupTheory.SymmetricThreeNormalSupplementIndex
public import Theory.GroupTheory.SylowIndexThreeQuotient

/-!
# Cubic recognition for the original small residual factor

The literal first factor Y₁Rc is normal in its full parabolic Y₁T. Its S₃
quotient gives index three over T, and the proper Borel prevents T from
being normal. Thus the full parabolic also has quotient S₃. The pair has
whole intersection T and trivial generated two-core. Since H centralizes
the original Sylow omega-center, the proved cubic recognition theorem
identifies its actual marked amalgam, with both possible orientations.

Source: Aschbacher--Smith 15.2.6--8, printed pp.1109--1110, and the
cubic cases of F.1.12. The construction does not require T ≤ Y₁Rc.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor
open ChapterF.Source ChapterF.SourceAssembly
variable {G : Type*} [Group G] [Finite G]

/-- The cubic first factor gives the actual exceptional cubic amalgam. -/
theorem SmallResidualWitness.cubic_symmetricThree_amalgam
    {T : Sylow 2 G} {M Mc V Y₁ H : Subgroup G} {h : ChosenSmallSource T M Mc V}
    (hw : SmallResidualWitness h Y₁) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)))
    (hfirst : Nonempty (((Y₁ ⊔ (M ⊓ Mc).pCoreIn 2 : Subgroup G) ⧸
      pCore 2 (Y₁ ⊔ (M ⊓ Mc).pCoreIn 2 : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    ExceptionalMarkedAmalgam H (Y₁ ⊔ (T : Subgroup G)) ∨
      ExceptionalMarkedAmalgam (Y₁ ⊔ (T : Subgroup G)) H := by
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  let A := Y₁ ⊔ (M ⊓ Mc).pCoreIn 2
  let L := ![A,H]
  let P := parabolic L (T : Subgroup G) 0
  obtain ⟨hF,hB₀,hP₁,hN,_⟩ := hw.symmetricThree_pair hH he
  have hB₁ : borel H (T : Subgroup G) = T := borel_eq_of_cubic_local_sylow H T
    ⟨T.subtype hH.1.1.2,map_subgroupOf_eq_of_le hH.1.1.2⟩ he.some
  have hB : commonBorel L (T : Subgroup G) = T := by
    change borel A (T : Subgroup G) ⊔ borel H (T : Subgroup G) ⊔ (T : Subgroup G) = T
    rw [hB₀,hB₁]
    exact le_antisymm (sup_le (sup_le inf_le_left le_rfl) le_rfl) le_sup_right
  have hHM : H ⊓ M = T := by
    have hh := hF.commonBorel_eq_normalizer 1
    rw [hP₁] at hh
    exact hN.trans (hh.symm.trans hB)
  have hP : P = Y₁ ⊔ (T : Subgroup G) := by
    obtain ⟨_,hp,_,_⟩ := hw.rankOne_pair_geometry hH le_rfl H.le_normalizer
      (sup_eq_left.mpr hH.1.1.2)
      (show Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ H) H by
        rw [inf_eq_left.mpr hTH]
        exact ⟨T.subtype hH.1.1.2,map_subgroupOf_eq_of_le hH.1.1.2⟩)
      (hF.quotient 1)
    exact hp.trans (congrArg (fun I => Y₁ ⊔ I) hHM)
  have hTP : (T : Subgroup G) ≤ P := le_sup_right.trans le_sup_left
  have hAP : A ≤ P := le_sup_left.trans le_sup_left
  have hPT : A ⊔ (T : Subgroup G) = P := by
    change A ⊔ (T : Subgroup G) = A ⊔ (T : Subgroup G) ⊔ borel H (T : Subgroup G)
    rw [hB₁,sup_eq_left.mpr (show (T : Subgroup G) ≤ A ⊔ T from le_sup_right)]
  have hnormA : P ≤ normalizer (A : Set G) :=
    sup_le (sup_le A.le_normalizer (hF.S_normalizes 0)) (hF.cross 0)
  have hproper : borel A (T : Subgroup G) < A := (hF.rankOneBorelFacts 0).proper
  have hnotAT : ¬ A ≤ (T : Subgroup G) := by
    intro ha
    apply hproper.not_ge
    rw [hB₀]
    exact le_inf ha le_rfl
  have hnT : ¬ ((T : Subgroup G).subgroupOf P).Normal := by
    intro hn
    have hnormT : P ≤ normalizer (T : Set G) :=
      (normal_subgroupOf_iff_le_normalizer hTP).mp hn
    apply hproper.not_ge
    exact le_inf le_rfl (le_normalizer_inf (hAP.trans hnormT) A.le_normalizer)
  let AP := A.subgroupOf P
  let TP := (T : Subgroup G).subgroupOf P
  let : AP.Normal := normal_subgroupOf_of_le_normalizer hnormA
  let eA := subgroupOfEquivOfLe hAP
  let eQ := QuotientGroup.congr (pCore 2 AP) (pCore 2 A) eA (pCore_map_iso 2 eA)
  have hi : TP.index = 3 := by
    apply index_three_of_symmetricThree_normal_supplement AP TP (eQ.trans hfirst.some)
      (T.subtype hTP) le_rfl
    · intro ht
      apply hnotAT
      intro a ha
      exact show (⟨a,hAP ha⟩ : P) ∈ TP from ht.ge (mem_top _)
    · rw [←subgroupOf_sup hAP hTP,hPT,subgroupOf_self]
  have hlt : pCore 2 P < TP := by
    refine lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal (T.subtype hTP)) ?_
    intro heq
    apply hnT
    change TP.Normal
    rw [←heq]
    infer_instance
  obtain ⟨eP⟩ := sylow_index_three_core_quotient (T.subtype hTP) hi hlt
  have hHP : H ⊓ P = (T : Subgroup G) := by
    have hh := ChapterF.Source.lemma_F_1_3_6 hF
    change P ⊓ parabolic L (T : Subgroup G) 1 = _ at hh
    rw [hP₁,hB] at hh
    exact (inf_comm H P).trans hh
  have hfree : pCore 2 (H ⊔ P : Subgroup G) = ⊥ := by
    have hg := parabolics_generate L (T : Subgroup G)
    change P ⊔ parabolic L (T : Subgroup G) 1 = generated L (T : Subgroup G) at hg
    rw [hP₁, sup_comm P H] at hg
    exact hg.symm ▸ hF.twoCore_free
  have hcH : Subgroup.centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
    apply (ChapterA.generalizedFitting_eq_pCore_iff 2).mp
    have hc := hF.characteristic_two 1
    change generalizedFitting (parabolic L (T : Subgroup G) 1) = _ at hc
    rw [hP₁] at hc
    exact hc
  have hZ : H ≤ Subgroup.centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) :=
    source_centralizing_HStar_le_seed_centralizer h.ambient T h.maximal hH h.centralizing
  have hout := ChapterF.Source.exceptional_cubic_of_centralized_omegaCenter H P T
    hH.1.1.2 hTP hHP he.some eP hcH (hF.characteristic_two 0) hfree hZ
  rwa [hP] at hout

end CFSG.Quasithin.Chapter15.Section02
