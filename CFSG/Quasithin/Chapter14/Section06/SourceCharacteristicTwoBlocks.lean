module
public import CFSG.Quasithin.Chapter14.Section06.SourceBlockOrderBound
public import CFSG.Quasithin.Chapter14.Section06.SourceMinimalParabolic
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingPairFamily

/-!
# Original characteristic-two block alternatives in 14.6.9

The original outside-family normalizer control constructs the exact C.5
configuration inside T. The numerical hypotheses give |T ∩ I| > 2⁹,
excluding the A₃, A₅ and paired-A₃ residuals by the proved C.6 bound.
The complete C.5 orbit therefore yields a natural block or two A₅ blocks.
In the latter case its literal orbit constructs the C.5.6(7)(iii) core
product and the two invariant maximum elementary abelian subgroups.

The actual Sylow, minimal-parabolic maximum I ∩ Mc, block orbit and
conjugator are retained. No block-selection, marked-action or C.5 callback
is assumed. The natural-block exclusion and the later paired-A₅ argument
that kills the centralizer D remain separate source obligations.

Source: Aschbacher--Smith, 14.6.9, printed pp.1025--1027,
using C.5.3--6 and C.6.1 (refs/quasithin.pdf).
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section06 ChapterC.Section06.Original
variable {G : Type*} [Group G] [Finite G]

/-- The literal C.5 configuration constructed inside the original Sylow group. -/
theorem source_characteristicTwo_c5_configuration
    (T : Sylow 2 G) (Tu M₀ Mc I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G) Tu Mc M₀))
    (hf : generalizedFitting I = pCore 2 I)
    (S : Sylow 2 I) (hS : (S : Subgroup I).map I.subtype = (T : Subgroup G) ⊓ I)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup I) ⊤)
    (hproper : (T : Subgroup G) ⊓ I < (T : Subgroup G)) :
    ∃ Λ : Subgroup G, Λ ≤ (T : Subgroup G) ∧
      ((T : Subgroup G) ⊓ I).relIndex Λ = 2 ∧
      ∃ c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
        ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I), c.sylow = S := by
  let R := (T : Subgroup G) ⊓ I
  let K := (pResidual 2 I).map I.subtype
  have hR : R.subgroupOf (T : Subgroup G) < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    exact fun he => hproper.not_ge (subgroupOf_eq_top.mp he)
  obtain ⟨X,hX,_⟩ := exists_covBy_le_of_lt hR
  have hiX := SubgroupEnumeration.relIndex_two_of_covBy T.isPGroup' hX
  let M := X.map (T : Subgroup G).subtype
  have hRM : R ≤ M := by
    rw [←map_subgroupOf_eq_of_le (show R ≤ (T : Subgroup G) from inf_le_left)]
    exact map_mono hX.le
  have hMT : M ≤ (T : Subgroup G) := map_subtype_le _
  have hi : R.relIndex M = 2 := by
    have he := relIndex_map_map_of_injective (R.subgroupOf (T : Subgroup G)) X
      (T : Subgroup G).subtype_injective
    rw [map_subgroupOf_eq_of_le (show R ≤ (T : Subgroup G) from inf_le_left)] at he
    exact he.trans hiX
  have hn : (R.subgroupOf M).Normal := normal_of_index_eq_two hi
  have hMR : M ≤ normalizer (R : Set G) := (normal_subgroupOf_iff_le_normalizer hRM).mp hn
  have hRH : R ⊔ K = I := by
    have hh := congrArg (Subgroup.map I.subtype) (pResidual_sup_sylow_eq_top S)
    simpa only [Subgroup.map_sup,hS,←MonoidHom.range_eq_map,range_subtype,sup_comm] using hh
  have hSylow : ∃ P : Sylow 2 (R ⊔ K : Subgroup G),
      (P : Subgroup (R ⊔ K : Subgroup G)).map (R ⊔ K).subtype = R := by
    rw [hRH]
    exact ⟨S,hS⟩
  obtain ⟨P,hP⟩ := hSylow
  let c : OriginalHypotheses I M K R R := {
    fitting := hf
    sylow := S
    sylow_image := hS
    unique := hu
    residual := rfl
    R_le := le_rfl
    T_le := hRM
    R_normal := hMR
    residual_sylow := P
    residual_sylow_image := hP
    no_common_normal := by
      intro W hWR hWnormal
      by_contra hW
      have hw : M ⊔ I ≤ normalizer (W : Set G) :=
        (normal_subgroupOf_iff_le_normalizer (hWR.trans (hRM.trans le_sup_left))).mp hWnormal
      have hc := (source_lemma_14_6_9_normalizers T Tu M₀ Mc I hI W hW hWR
        (le_sup_right.trans hw)).2.2.2 M hRM hMT
      have he : M ≤ R := (le_inf le_rfl (le_sup_left.trans hw)).trans hc.le
      have hh : R.relIndex M = 1 := relIndex_eq_one.mpr he
      omega }
  exact ⟨M,hMT,hi,c,rfl⟩

private theorem orbit_natural_or_paired_five
    {I Λ K R : Subgroup G} (c : OriginalHypotheses I Λ K R R)
    (b : OrbitDecomposition (c.sylow : Subgroup I) (R.subgroupOf I) (pResidual 2 I))
    (hsmall : ¬ (IsAlternatingBlock K 3 ∨ IsAlternatingBlock K 5 ∨ CubicPair K)) :
    (∃ i : Fin b.size, ∃ n, IsL2EvenBlock ((b.block i).map I.subtype) n) ∨
      (∃ i j : Fin b.size, i ≠ j ∧ b.size = 2 ∧
        IsAlternatingBlock ((b.block i).map I.subtype) 5) := by
  let i : Fin b.size := ⟨0,b.positive⟩
  have ht : IsChiZeroBlock ((b.block i).map I.subtype) :=
    (b.type i).2.of_mulEquiv (equivMapOfInjective (b.block i) I.subtype I.subtype_injective)
  rcases ht with ⟨n,hn⟩ | h3 | h5
  · exact Or.inl ⟨i,n,hn⟩
  · have hs : b.size = 2 := by
      by_contra hn
      have hs1 : b.size = 1 := by have := b.positive; have := b.size_le; omega
      have he := single_block_eq_residual c b i hs1
      exact hsmall (Or.inl (he ▸ h3))
    let j : Fin b.size := ⟨1,by omega⟩
    have hij : i ≠ j := by intro he; have := congrArg Fin.val he; simp [i,j] at this
    have h3i : IsAlternatingBlock (b.block i) 3 :=
      ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv
        (equivMapOfInjective (b.block i) I.subtype I.subtype_injective).symm h3
    obtain ⟨t,_,he⟩ := b.transitive i j
    have h3j : IsAlternatingBlock ((b.block j).map I.subtype) 3 :=
      ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv
        (equivMapOfInjective (b.block j) I.subtype I.subtype_injective)
        (ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv
          (((MulAut.conj t⁻¹).subgroupMap (b.block i)).trans (MulEquiv.subgroupCongr he.symm)) h3i)
    have hne : (b.block i).map I.subtype ≠ (b.block j).map I.subtype :=
      fun he => hij (b.injective (map_injective I.subtype_injective he))
    have hc : (b.block j).map I.subtype ≤ centralizer ((b.block i).map I.subtype : Set G) := by
      apply commutator_eq_bot_iff_le_centralizer.mp
      rw [←map_commutator,commutator_eq_bot_iff_le_centralizer.mpr (b.commute (Ne.symm hij)),Subgroup.map_bot]
    exact (hsmall (Or.inr (Or.inr ⟨_,_,hne,h3,h3j,hc,c.pair_join b i j hij hs⟩))).elim
  · have hs : b.size = 2 := by
      by_contra hn
      have hs1 : b.size = 1 := by have := b.positive; have := b.size_le; omega
      have he := single_block_eq_residual c b i hs1
      exact hsmall (Or.inr (Or.inl (he ▸ h5)))
    let j : Fin b.size := ⟨1,by omega⟩
    have hij : i ≠ j := by intro he; have := congrArg Fin.val he; simp [i,j] at this
    exact Or.inr ⟨i,j,hij,hs,h5⟩

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

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


/-- In the characteristic-two branch, the original numerical hypotheses
exclude every small C.6 block type on the actual residual. -/
theorem source_characteristicTwo_blocks_or_factorization
    (hcoreIndex : 4 < (H.pCoreIn 2).relIndex (T : Subgroup G))
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)))
    (I : Subgroup G) (hf : generalizedFitting I = pCore 2 I)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M)) :
    (let R := (T : Subgroup G) ⊓ I
     let K := (pResidual 2 I).map I.subtype
     2 ^ 9 < Nat.card R ∧
     ¬ (IsAlternatingBlock K 3 ∨ IsAlternatingBlock K 5 ∨ CubicPair K) ∧
     ∃ Λ : Subgroup G, Λ ≤ (T : Subgroup G) ∧ R.relIndex Λ = 2 ∧
       ∃ c : OriginalHypotheses I Λ K R R,
       ∃ hP : ChapterB.IsMinimalParabolicOver c.sylow ⊤,
         ChapterB.minimalParabolicMax c.sylow hP = (I ⊓ Mc).subgroupOf I ∧
         Nonempty (OrbitDecomposition (c.sylow : Subgroup I) (R.subgroupOf I) (pResidual 2 I))) ∨
    (let L := sourceResidual M Mc
     let LI := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
     (L : Set G) = (LI : Set G) * (L.pCoreIn 2 : Set G) ∧
       (L ⊔ (T : Subgroup G) : Subgroup G) =
         (LI : Set G) * ((T : Subgroup G) ⊓ I : Subgroup G) *
           ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)) := by
  rcases source_minimal_parabolic_or_factorization hG T hempty hM hunique hmany hcard e
    hab H hH u hu hindex hmove hproduct hU3 hlocal I hI with ⟨S,hS,hP,hmax⟩ | hfactor
  · left
    let R := (T : Subgroup G) ⊓ I
    let K := (pResidual 2 I).map I.subtype
    have hsq : IsSQTK KnownSimple.IsKnownSimple I := by
      let N := normalizer (I.pCoreIn 2 : Set G)
      have hIN : I ≤ N := I.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
      have hN : IsTwoLocal N := ⟨I.pCoreIn 2,hI.1.1.1,isPGroup_pCoreIn 2 I,rfl⟩
      exact (IsSQTK.equiv (subgroupOfEquivOfLe hIN)).mp
        ((hG.twoLocal_sqtk hN).subgroup (I.subgroupOf N))
    have hproper := (source_suitable_intersection_sylow hG T hempty hM hunique hmany
      hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I hI.1.1).2
    have hlarge : 2 ^ 9 < Nat.card R := by
      have hTcard := (source_lemma_14_6_9_order hG T hempty hM hunique hmany hcard e hab
        H hH hcoreIndex hrank).2
      let Tu := (T : Subgroup G) ⊓ centralizer ({u} : Set G)
      have hi := source_lemma_14_6_3_1 hG T hempty hM hunique hmany hcard e hab H hH
        u hu hindex hmove hproduct
      have hTuIndex : Tu.relIndex (T : Subgroup G) = 4 := hi.2.1
      have hc : Nat.card Tu * 4 = Nat.card T := by
        simpa only [relIndex_bot_left,hTuIndex] using
          relIndex_mul_relIndex (⊥ : Subgroup G) Tu (T : Subgroup G) bot_le inf_le_left
      have hTuR : Tu ≤ R := le_inf inf_le_left hI.1.1.2.1
      have hle := Nat.card_le_card_of_injective (Subgroup.inclusion hTuR)
        (Subgroup.inclusion_injective _)
      norm_num at hTcard ⊢
      omega
    obtain ⟨Λ,hΛT,hi,c,hc⟩ := source_characteristicTwo_c5_configuration T _ M Mc I hI.1 hf
      S hS hP.1 hproper
    have hPc : ChapterB.IsMinimalParabolicOver c.sylow ⊤ := by
      simpa only [hc] using hP
    have hmaxc : ChapterB.minimalParabolicMax c.sylow hPc = (I ⊓ Mc).subgroupOf I := by
      simpa only [hc] using hmax
    refine ⟨hlarge,?_,Λ,hΛT,hi,c,hPc,hmaxc,c.block_decomposition_knownSimple hsq⟩
    intro hsmall
    have hc := source_lemma_14_6_9_small_blocks T _ M Mc I hI.1 hsq hf S hS hP.1 hproper hsmall
    exact (not_le_of_gt hlarge) hc
  · exact Or.inr hfactor

/-- The source characteristic-two branch reduces to a genuine natural block,
or gives the actual C.5.6(7)(iii) paired-A₅ core and invariant family.
The numerical assumptions eliminate all small residual types; the original
C.5 orbit supplies every marked action and moving conjugator. -/
theorem source_characteristicTwo_natural_or_paired_or_factorization
    (hcoreIndex : 4 < (H.pCoreIn 2).relIndex (T : Subgroup G))
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)))
    (I : Subgroup G) (hf : generalizedFitting I = pCore 2 I)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M)) :
    (let R := (T : Subgroup G) ⊓ I
     let K := (pResidual 2 I).map I.subtype
     (∃ Λ : Subgroup G, Λ ≤ (T : Subgroup G) ∧ R.relIndex Λ = 2 ∧
       ∃ c : OriginalHypotheses I Λ K R R,
       ∃ hP : ChapterB.IsMinimalParabolicOver c.sylow ⊤,
       ChapterB.minimalParabolicMax c.sylow hP = (I ⊓ Mc).subgroupOf I ∧
       ∃ b : OrbitDecomposition (c.sylow : Subgroup I) (R.subgroupOf I) (pResidual 2 I),
       (∃ i : Fin b.size, ∃ n, IsL2EvenBlock ((b.block i).map I.subtype) n) ∨
       (∃ i j : Fin b.size, i ≠ j ∧ b.size = 2 ∧
       IsAlternatingBlock ((b.block i).map I.subtype) 5 ∧
       ∃ x ∈ (T : Subgroup G), x ∉ R ∧
       let D := R ⊓ centralizer (K : Set G)
       let Q := I.pCoreIn 2
       (frattini D).map D.subtype = ⊥ ∧
       D ⊓ D.map (MulAut.conj x⁻¹).toMonoidHom = ⊥ ∧
       Q = K.pCoreIn 2 ⊔ D ∧
       Q ∈ elementaryAbelianMaxSubgroups R ∧
       ChapterB.baumann R = elementaryAbelianMaxJ R ∧
       {A ∈ elementaryAbelianMaxSubgroups R | R ≤ normalizer (A : Set G)} =
         {Q,Q.map (MulAut.conj x⁻¹).toMonoidHom}))) ∨
    (let L := sourceResidual M Mc
     let LI := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
     (L : Set G) = (LI : Set G) * (L.pCoreIn 2 : Set G) ∧
       (L ⊔ (T : Subgroup G) : Subgroup G) =
         (LI : Set G) * ((T : Subgroup G) ⊓ I : Subgroup G) *
           ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)) := by
  rcases source_characteristicTwo_blocks_or_factorization hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal hcoreIndex hrank I hf hI with
    ⟨_,hsmall,Λ,hΛ,hi,c,hPc,hmaxc,⟨b⟩⟩ | hfactor
  · left
    refine ⟨Λ,hΛ,hi,c,hPc,hmaxc,b,?_⟩
    rcases orbit_natural_or_paired_five c b hsmall with hn | ⟨i,j,hij,hs,h5⟩
    · exact Or.inl hn
    · obtain ⟨x,hx,hout,hgeom⟩ := c.alternating_pair_family b i j hij hs h5 hi
      exact Or.inr ⟨i,j,hij,hs,h5,x,hΛ hx,hout,hgeom⟩
  · exact Or.inr hfactor

end CFSG.Quasithin.Chapter14.Section06
