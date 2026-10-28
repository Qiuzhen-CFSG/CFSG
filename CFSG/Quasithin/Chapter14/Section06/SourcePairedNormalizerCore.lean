module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedPointRadical
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedPointCoreCover
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedNormalizerBlocks
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedCentralizerNormalizer
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingPairFamily
public import Theory.GroupTheory.PCoreImage

/-!
# Core recovery in the normalizer of the paired residual centralizer

The full generalized-Fitting preimage of M_c centralizes its core omega-center.
If D lies in that center, the preimage lies in N_G(D), so the literal A.4.4(1)
intersection recovers O₂(M_c). Normality of the paired residual in N_G(D)
then identifies the two cores. Thompson heredity and maximal two-local
normalizer control give the contradiction in the original source geometry.

Source: Aschbacher--Smith, original14.6.9, printed p.1026.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section06
open ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A point-core cover places the elementary residual centralizer in its omega-center. -/
theorem paired_centralizer_le_omega_of_core_cover
    (K D A W : Subgroup G) (hD : D ≤ A) (hA : IsElementaryAbelian 2 A)
    (hAW : A ≤ W) (hDK : D ≤ centralizer (K : Set G))
    (hW : W ≤ K ⊔ A) : D ≤ omegaOneCenterAmbient W := by
  let := hA
  have hDA : D ≤ centralizer (A : Set G) := by
    intro d hd a ha
    exact congrArg (fun x : A => (x : G))
      (hA.toIsMulCommutative.is_comm.comm (⟨a,ha⟩ : A) ⟨d,hD hd⟩)
  have hDC : D ≤ centralizer ((K ⊔ A : Subgroup G) : Set G) :=
    le_centralizer_iff.mp (sup_le (le_centralizer_iff.mp hDK)
      (le_centralizer_iff.mp hDA))
  intro d hd
  exact (mem_omegaOneCenterAmbient_iff W d).mpr
    ⟨hAW (hD hd),elemPow_eq_one_of_isElementaryAbelian (p := 2) d (hD hd),
      centralizer_le hW (hDC hd)⟩

/-- A.4.4(1) at the literal normalizer of a centralized subgroup. -/
theorem normalizer_intersection_core_of_fittingPreimage
    (M D Z : Subgroup G) (hDZ : D ≤ Z)
    (hcentral : twoGeneralizedFittingPreimage M ≤ centralizer (Z : Set G)) :
    M.pCoreIn 2 = (normalizer (D : Set G) ⊓ M).pCoreIn 2 := by
  have hpre : twoGeneralizedFittingPreimage M ≤ normalizer (D : Set G) :=
    (hcentral.trans (centralizer_le hDZ)).trans (Subgroup.centralizer_le_normalizer _)
  have ha : IntersectionAlternative
      (twoCoreQuotientImage M (twoGeneralizedFittingPreimage M)) := by
    rw [twoCoreQuotientImage_fittingPreimage]
    refine Or.inr ⟨le_rfl,?_,?_⟩
    · exact (inferInstance : ((generalizedFitting (M ⧸ pCore 2 M)).subgroupOf
        (generalizedFitting (M ⧸ pCore 2 M))).Normal).isSubnormal
    · exact (closure_le _).mpr (fun x hx => hx.1.1)
  simpa only [inf_comm M] using lemma_A_4_4_1 M (normalizer (D : Set G))
    (twoGeneralizedFittingPreimage M) (twoCore_le_fittingPreimage M)
    (le_inf (map_subtype_le _) hpre) ha

omit [Finite G] in
/-- Normal residual and centralizer factors identify the normalizer's core. -/
theorem paired_normalizer_core_eq
    (I K D : Subgroup G) (S : Sylow 2 (normalizer (D : Set G)))
    (hI : I ≤ normalizer (D : Set G)) (hKI : K ≤ I)
    (hS : (S : Subgroup (normalizer (D : Set G))).map
      (normalizer (D : Set G)).subtype ≤ I)
    (hD : IsPGroup 2 D)
    (hK : normalizer (D : Set G) ≤ normalizer (K : Set G))
    (hcore : I.pCoreIn 2 = K.pCoreIn 2 ⊔ D) :
    I.pCoreIn 2 = (normalizer (D : Set G)).pCoreIn 2 := by
  let N := normalizer (D : Set G)
  have hIN : N.pCoreIn 2 ≤ I.pCoreIn 2 := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 N) ((pCoreIn_le_sylow N S).trans hS)
    (hI.trans (N.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image N (pCore 2 N))))
  apply le_antisymm _ hIN
  rw [hcore]
  exact sup_le (pCoreIn_mono_of_normalizes (hKI.trans hI) hK)
    (le_pCoreIn_of_normalizes hD D.le_normalizer le_rfl)

/-- The source Thompson sandwich forces the original group into M_c. -/
theorem paired_core_thompson_exclusion
    (I M W : Subgroup G) (hM : IsMaximalTwoLocal M)
    (hout : ¬ I ≤ M) (hne : I.pCoreIn 2 ≠ ⊥)
    (hJ : elementaryAbelianMaxJ W = I.pCoreIn 2)
    (hIQ : I.pCoreIn 2 ≤ M.pCoreIn 2) (hQW : M.pCoreIn 2 ≤ W) : False := by
  have hJQ : elementaryAbelianMaxJ (M.pCoreIn 2) = I.pCoreIn 2 :=
    (elementaryAbelianMaxJ_eq_of_intermediate W (M.pCoreIn 2)
      (hJ.symm ▸ hIQ) hQW).trans hJ
  have hMn : M ≤ normalizer (I.pCoreIn 2 : Set G) := by
    rw [←hJQ]
    exact (M.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image M (pCore 2 M))).trans
      (normalizer_le_normalizer_elementaryAbelianMaxJ _)
  have hN : IsTwoLocal (normalizer (I.pCoreIn 2 : Set G)) :=
    ⟨I.pCoreIn 2,hne,isPGroup_pCoreIn 2 I,rfl⟩
  exact hout ((I.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image I (pCore 2 I))).trans (hM.2 hN hMn))

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterC ChapterC.Section05.BlockAnalysis

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G))
    (hU3 : Mc ⊓ normalizer (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u : Set G) =
        (T : Subgroup G))
    (hlocal : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
      (H ⊓ centralizer ({u} : Set G)))

include hG hempty hM hunique hmany hcard e hab H hH hu hindex hmove hproduct hU3 hlocal

omit hindex hmove hproduct hU3 hlocal in
/-- The original pre-D=1 point-core cover centralizes D, without any
Baumann containment hypothesis. -/
theorem source_paired_centralizer_le_point_core_omega
    (I Λ : Subgroup G)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (b : OrbitDecomposition (c.sylow : Subgroup I)
      (((T : Subgroup G) ⊓ I).subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5)
    (hpairIndex : (((T : Subgroup G) ⊓ I).relIndex Λ) = 2) :
    ((T : Subgroup G) ⊓ I) ⊓
      centralizer ((pResidual 2 I).map I.subtype : Set G) ≤
        omegaOneCenterAmbient ((I ⊓ Mc).pCoreIn 2) := by
  let K := (pResidual 2 I).map I.subtype
  let D := ((T : Subgroup G) ⊓ I) ⊓ centralizer (K : Set G)
  let A := I.pCoreIn 2
  let W := (I ⊓ Mc).pCoreIn 2
  obtain ⟨_,_,_,_,_,hcore,hmax,_⟩ := c.alternating_pair_family b i j hij hs hi hpairIndex
  have hDA : D ≤ A := le_sup_right.trans_eq hcore.symm
  have hJ : elementaryAbelianMaxJ W = A := source_paired_point_thompson
    hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b i j hij hs hi hpairIndex
  have hAW : A ≤ W := hJ ▸ (sSup_le fun _ hE => hE.1)
  have hcover := source_paired_point_core_cover_mod_core
    hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b i j hij hs hi
  have hPK : ((b.block i).map I.subtype ⊓ Mc).pCoreIn 2 ⊔
      ((b.block j).map I.subtype ⊓ Mc).pCoreIn 2 ≤ K := by
    exact (sup_le_sup ((pCoreIn_le 2 _).trans inf_le_left)
      ((pCoreIn_le 2 _).trans inf_le_left)).trans_eq (c.pair_join b i j hij hs)
  exact paired_centralizer_le_omega_of_core_cover K D A W hDA hmax.2.1 hAW
    inf_le_right (hcover.trans (sup_le_sup hPK le_rfl))

/-- The literal source endgame. Only residual normality in N(D) remains;
the source point-core cover discharges the omega-center geometry. -/
theorem source_paired_centralizer_trivial_of_normalized_residual
    (I Λ : Subgroup G)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (b : OrbitDecomposition (c.sylow : Subgroup I)
      (((T : Subgroup G) ⊓ I).subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5)
    (hpairIndex : (((T : Subgroup G) ⊓ I).relIndex Λ) = 2)
    (hKnormal : let K := (pResidual 2 I).map I.subtype
      let D := ((T : Subgroup G) ⊓ I) ⊓ centralizer (K : Set G)
      D ≠ ⊥ → normalizer (D : Set G) ≤ normalizer (K : Set G)) :
    ((T : Subgroup G) ⊓ I) ⊓
      centralizer ((pResidual 2 I).map I.subtype : Set G) = ⊥ := by
  let R := (T : Subgroup G) ⊓ I
  let K := (pResidual 2 I).map I.subtype
  let D := R ⊓ centralizer (K : Set G)
  let ID := normalizer (D : Set G)
  have hDcenter := source_paired_centralizer_le_point_core_omega hG T hempty hM hunique
    hmany hcard e hab H hH u hu I Λ hI c b i j hij hs hi hpairIndex
  by_contra hne
  obtain ⟨hIid,_,_,_,_,_,S,z,hS,_,_,_⟩ :=
    source_paired_centralizer_normalizer_data hG T hempty hM hunique hmany hcard e hab
      H hH u hu hindex hmove hproduct hU3 hlocal I Λ hI.1 c hne
  obtain ⟨hJ,_,hQW,_,hOmega⟩ := source_paired_point_radical hG T hempty hM hunique
    hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I hI Λ c b i j hij hs hi hpairIndex
  obtain ⟨x,hx,hxR,_,_,hcore,_⟩ := c.alternating_pair_family b i j hij hs hi hpairIndex
  have hcoreID : I.pCoreIn 2 = ID.pCoreIn 2 :=
    paired_normalizer_core_eq I K D S hIid (map_subtype_le _) (hS.le.trans inf_le_right)
      (T.isPGroup'.to_le (inf_le_left.trans inf_le_left)) (hKnormal hne) hcore
  have hZ : Nat.card (centralInvolutions T) = 2 :=
    plane_centralInvolutions_card T M hM.1.2 hcard e
  obtain ⟨_,hneM,hMc,_⟩ :=
    plane_ordering_and_overgroups hG T hempty hM hunique hmany hcard hZ
  have hMcMax : IsMaximalTwoLocal Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      hunique ▸ Set.mem_singleton Mc).1
  have hTMc : (T : Subgroup G) ≤ Mc := by
    rw [hMc]
    exact le_centralizer_iff.mp (centralInvolutions_le_centralizer_sylow T)
  have hMcOutside : Mc ∈ Chapter1.HOutside G (T : Set G) (M : Set G) :=
    ⟨⟨Chapter1.mem_H_of_isTwoLocal hMcMax.1,hTMc⟩,
      fun hh => hneM (hMcMax.eq_of_le hM.1.1.1 hh).symm⟩
  have hF := source_generalizedFittingPreimage_centralizes_omegaCore hG T hempty
    hMcOutside hMc.le
  have hIDcore : Mc.pCoreIn 2 = (ID ⊓ Mc).pCoreIn 2 :=
    normalizer_intersection_core_of_fittingPreimage Mc D _ (hDcenter.trans hOmega) hF
  have hcoreMc : ID.pCoreIn 2 ≤ Mc := (pCoreIn_le_sylow ID S).trans
    (hS.le.trans (inf_le_left.trans hTMc))
  have hcoreB : ID.pCoreIn 2 ≤ (ID ⊓ Mc).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 ID) (le_inf (pCoreIn_le 2 ID) hcoreMc)
      (inf_le_left.trans (ID.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image ID (pCore 2 ID))))
  exact paired_core_thompson_exclusion I Mc ((I ⊓ Mc).pCoreIn 2) hMcMax
    hI.1.1.2.2.1 hI.1.1.1 hJ (hcoreID.le.trans (hcoreB.trans hIDcore.ge)) hQW

end CFSG.Quasithin.Chapter14.Section06
