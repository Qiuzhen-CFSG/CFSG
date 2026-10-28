module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedNormalizerCore
public import CFSG.Quasithin.ChapterC.Section01.LocalShortCoreContainment

/-!
# Triviality of the paired residual centralizer in characteristic two

The original two blocks are local components for the actual full Sylow of
N_G(D). Characteristic two forces each moved block module into O₂(N_G(D)).
The paired C.5 core formula and normality of D put all of O₂(I) there.
The literal point-core omega containment, A.4.4(1), and the Thompson
contradiction then give D=1.

Only the independently produced characteristic-two assertion for N_G(D)
remains. No minimality of this normalizer or containing-block witness is used.

Source: Aschbacher--Smith14.6.9, printed p.1026.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section06
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original paired core lies in the actual normalizer core whenever
the latter is self-centralizing. -/
theorem source_paired_core_le_normalizer_core
    (T : Sylow 2 G) (I Λ : Subgroup G)
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (b : OrbitDecomposition (c.sylow : Subgroup I)
      (((T : Subgroup G) ⊓ I).subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5)
    (hpairIndex : (((T : Subgroup G) ⊓ I).relIndex Λ) = 2) :
    let K := (pResidual 2 I).map I.subtype
    let D := ((T : Subgroup G) ⊓ I) ⊓ centralizer (K : Set G)
    let ID := normalizer (D : Set G)
    ∀ S : Sylow 2 ID, (S : Subgroup ID).map ID.subtype = (T : Subgroup G) ⊓ I →
      generalizedFitting ID = pCore 2 ID → I.pCoreIn 2 ≤ ID.pCoreIn 2 := by
  intro K D ID S hS hf
  let R := (T : Subgroup G) ⊓ I
  let K₁ := (b.block i).map I.subtype
  let K₂ := (b.block j).map I.subtype
  have hIid : I ≤ ID := c.sylow_centralizer_normalized
  obtain ⟨⟨h⟩,⟨h'⟩⟩ := c.alternating_paired_setups b i j hij hs hi
  have hmodule (a : Fin b.size) (ha : IsAlternatingBlock ((b.block a).map I.subtype) 5) :
      sourceModule ((b.block a).map I.subtype) ≤ ID.pCoreIn 2 := by
    let B := (b.block a).map I.subtype
    have hB : B ≤ ID := (map_subtype_le _).trans hIid
    have hl := source_paired_block_local_in_centralizer_normalizer T I Λ c b a ha S hS
    have hb : IsAlternatingBlock (B.subgroupOf ID) 5 :=
      RankOne.Solvable.isAlternatingBlock_of_equiv (subgroupOfEquivOfLe hB).symm ha
    have hh := local_short_module_le_core_of_characteristicTwo hf S
      (B.subgroupOf ID) hb.2.1 hl
    have hm := map_mono (f := ID.subtype) hh
    change (moduleLayer (B.subgroupOf ID)).map ID.subtype ≤ ID.pCoreIn 2 at hm
    rw [←moduleLayer_map ID.subtype ID.subtype_injective,
      map_subgroupOf_eq_of_le hB] at hm
    exact hm
  obtain ⟨x,hx,hcomm⟩ := c.exists_noncommuting_module b i
  have hnc : ¬ (sourceModule K₁).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K₁ : Set G) := by
    rw [ambientModule_eq_literal] at hcomm
    exact fun hh => hcomm (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hh))
  have hpair : ∀ r ∈ R, K₁.conjBy r = K₁ ∨ K₁.conjBy r = K₂ :=
    c.pair_action b i j hij hs
  obtain ⟨t,ht,_,hte⟩ := c.pair_exchange b i j hij
  have ht' : ∃ t : Λ, (t : G) ∈ R ∧ K₁.conjBy (t : G) = K₂ :=
    ⟨⟨t,c.R_le_M ht⟩,ht,hte⟩
  have hKcore : K.pCoreIn 2 = sourceModule K₁ ⊔ sourceModule K₂ :=
    (congrArg (fun X : Subgroup G => X.pCoreIn 2) (c.pair_join b i j hij hs).symm).trans
      (h.two_block_core_eq_module h' Λ R x hx (c.R_normal hx) hpairIndex hpair ht' hnc)
  obtain ⟨_,_,_,_,_,hcore,_⟩ := c.alternating_pair_family b i j hij hs hi hpairIndex
  rw [hcore,hKcore]
  exact sup_le (sup_le (hmodule i hi) (hmodule j h'.block))
    (le_pCoreIn_of_normalizes (T.isPGroup'.to_le (inf_le_left.trans inf_le_left))
      D.le_normalizer le_rfl)

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

theorem source_paired_centralizer_trivial_of_characteristicTwo
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
    (hfID : let K := (pResidual 2 I).map I.subtype
      let D := ((T : Subgroup G) ⊓ I) ⊓ centralizer (K : Set G)
      D ≠ ⊥ → generalizedFitting (normalizer (D : Set G)) = pCore 2 (normalizer (D : Set G))) :
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
  have hcoreID : I.pCoreIn 2 ≤ ID.pCoreIn 2 :=
    source_paired_core_le_normalizer_core T I Λ c b i j hij hs hi hpairIndex S hS (hfID hne)
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
    hI.1.1.2.2.1 hI.1.1.1 hJ (hcoreID.trans (hcoreB.trans hIDcore.ge)) hQW

end CFSG.Quasithin.Chapter14.Section06
