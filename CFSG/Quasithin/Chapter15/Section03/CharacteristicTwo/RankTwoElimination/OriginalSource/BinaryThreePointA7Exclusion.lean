module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeFixedFourNormalizer
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointA7FourInvariant
public import Theory.GroupTheory.CComponent.CentralizerMovement
public import Theory.SpecificGroups.Alternating.SevenComponent.Normality
public import Theory.SpecificGroups.Alternating.SevenComponent
public import Theory.GroupTheory.PerfectSmallTwoAction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFiniteModels

/-!
# The A7 component cannot persist in the full four-normalizer

An invariant four at the original point is centralized by the perfect
containing component. That component persists through the full four
centralizer into its normalizer. Its centerless A7 two-core quotient and
three-rank two force the component to have index prime to three there.
The full six-element automizer of the four contradicts that index,
since the component lies in its kernel. The argument keeps the component's
literal two-core quotient and never assumes the point kernel self-centralizing.

Source: Aschbacher--Smith15.3.23 and A.3.18, pp.1128--1129 and51--53.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource LinearThree.CoreActions LinearThree.Extension.SourceCases ChapterC BinaryMS.MS93
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

private theorem a7_component_full_four_normalizer_false
    (F C : Subgroup G) (hF : Nat.card F = 4)
    (hCF : centralizer (F : Set G) ≤ C) (hCN : C ≤ normalizer (F : Set G))
    (hfull : Function.Surjective F.normalizerMonoidHom)
    (hAut : Nat.card (MulAut F) = 6)
    (hr : primeRank 3 (normalizer (F : Set G)) ≤ 2)
    (K : Subgroup C) (hK : K.IsCComponent)
    (a : K.map (QuotientGroup.mk' (pCore 2 C)) ≃* alternatingGroup (Fin 7)) : False := by
  let NF := normalizer (F : Set G)
  let A := K.map C.subtype
  let E := A.subgroupOf NF
  have hAC : A ≤ C := map_subtype_le _
  have hAN : A ≤ NF := hAC.trans hCN
  let i : E ≃* K := (subgroupOfEquivOfLe hAN).trans
    (K.equivMapOfInjective C.subtype C.subtype_injective).symm
  let : Group.IsPerfect K := hK.perfect
  let : Group.IsPerfect E := Group.IsPerfect.ofSurjective (f := i.symm.toMonoidHom) i.symm.surjective
  let M := F.subgroupOf NF
  let : M.Normal := normal_subgroupOf_of_le_normalizer (show NF ≤ normalizer (F : Set G) from le_rfl)
  have hM : Nat.card M ≤ 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe F.le_normalizer).toEquiv,hF]
  have hEM := le_centralizer_of_isPerfect_of_card_le_four E M hM
  have hAF : A ≤ centralizer (F : Set G) := by
    intro x hx y hy
    exact congrArg Subtype.val
      (hEM (show (⟨x,hAN hx⟩ : NF) ∈ E from hx) ⟨y,F.le_normalizer hy⟩ hy)
  have hAp : (A.subgroupOf C).IsCComponent := by
    change ((K.map C.subtype).comap C.subtype).IsCComponent
    rwa [comap_map_eq_self_of_injective C.subtype_injective]
  have hE : E.IsCComponent := hAp.in_normalizer_of_centralizes hAF hCF
  let eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7) :=
    (cComponentTwoCoreQuotientEquiv hK).trans a
  let eE := (QuotientGroup.congr _ _ i (pCore_map_iso 2 i)).trans eK
  let : E.Normal := alternatingGroup.SevenComponent.normal_of_core_quotient hE eE hr
  have hz : center (E ⧸ pCore 2 E) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh := (centerCongr eE ⟨x,hx⟩).property
    change eE x ∈ center (alternatingGroup (Fin 7)) at hh
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at hh
    exact eE.map_eq_one_iff.mp hh
  have hthree : 2 ≤ primeRank 3 (E ⧸ pCore 2 E) := by
    rw [primeRank_congr 3 eE]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)
  have ho : Nat.Coprime 3 (Nat.card (MulAut.Outer (E ⧸ pCore 2 E))) := by
    rw [Nat.card_congr (MulAut.outerCongr eE).toEquiv]
    obtain ⟨n,hn⟩ := alternatingGroup.SevenComponent.outer_two.exists_card_dvd_pow
    exact ((by decide : Nat.Coprime 3 2).pow_right n).coprime_dvd_right hn
  have hi : Nat.Coprime 3 E.index :=
    cComponent_index_coprime_three_of_quotient E hE hz hthree hr ho
  have hker : E ≤ F.normalizerMonoidHom.ker := by
    rw [normalizerMonoidHom_ker]
    intro x hx
    exact hAF hx
  have hindex : F.normalizerMonoidHom.ker.index = 6 := by
    rw [index_ker,MonoidHom.range_eq_top.mpr hfull,card_top,hAut]
  have hdiv : 3 ∣ E.index :=
    (by rw [hindex]; decide : 3 ∣ F.normalizerMonoidHom.ker.index).trans (index_dvd_of_le hker)
  exact (Nat.prime_three.coprime_iff_not_dvd.mp hi) hdiv

/-- The actual original large-distance point has no normal containing
C-component whose same point-quotient image is A7. -/
theorem binary_three_source_point_not_a7
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hzH : z ∈ LinearThree.OriginalSource.intrinsicFour c.L)
    (hz2 : orderOf z = 2) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup (centralizer ({z} : Set G)))
    (hK : K.IsCComponent) (hKn : K.Normal)
    (hLK : c.L.subgroupOf (centralizer ({z} : Set G)) ≤ K)
    (a : K.map (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≃*
      alternatingGroup (Fin 7)) : False := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let F := coreFixed c.L
  let : K.Normal := hKn
  let : (K.map q).Normal := hKn.map q (QuotientGroup.mk'_surjective _)
  have hBK := map_mono (f := q) hLK
  have hCH := binary_three_source_a7_four_invariant
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
    (K.map q) hBK a
  obtain ⟨hF,hFH,_,_⟩ := binary_three_large_distance_fixed_factor_bound
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb
  change Nat.card F = 4 at hF
  change F = intrinsicFour c.L at hFH
  have hCN : C ≤ normalizer (F : Set G) := by rw [show F = intrinsicFour c.L from hFH]; exact hCH
  have hFC : centralizer (F : Set G) ≤ C := by
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    exact (hx z (hFH.symm ▸ hzH)).symm
  have hnormal := binary_three_large_distance_fixed_four_normalizer
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb
  have hr := hnormal.2.1.stronglyQuasithin 3 (by decide) (by decide)
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  let : IsElementaryAbelian 2 F := coreFixed_elementary_of_MS93 d c.L b t common earlier
  let : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour F := ⟨hF,IsElementaryAbelian.exponent_eq_prime⟩
  exact a7_component_full_four_normalizer_false F C hF hFC hCN
    hnormal.2.2.2.1 (IsKleinFour.card_mulAut F) hr K hK a

/-- The full original point packet retains its actual Sylow, quotient,
strict component containment and finite catalogue, with A7 now excluded. -/
theorem binary_three_large_distance_point_finite_models_not_a7
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    ∃ z : G, z ∈ intrinsicFour c.L ∧ orderOf z = 2 ∧
      c.L ⊔ d.S ≤ centralizer ({z} : Set G) ∧
      ¬ centralizer ({z} : Set G) ≤ d.M ∧
      let C := centralizer ({z} : Set G)
      let q := QuotientGroup.mk' (pCore 2 C)
      let B := (c.L.subgroupOf C).map q
      IsSQTK KnownSimple.IsKnownSimple (C ⧸ pCore 2 C) ∧
      pCore 2 (C ⧸ pCore 2 C) = ⊥ ∧
      Nat.card (intrinsicFour B) ≤ 2 ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2)) ∧
      primeRank 3 (C ⧸ pCore 2 C) = 2 ∧
      primeRank 3 (normalizer (B : Set (C ⧸ pCore 2 C))) ≤ 1 ∧
      ∃ P : Sylow 2 C, (P : Subgroup C).map C.subtype = d.S ∧
        B ∈ ChapterA.Section03.localCComponents
          (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C))) ∧
        (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C)) : Subgroup _) ≤
          normalizer (B : Set (C ⧸ pCore 2 C)) ∧
        Nonempty (((B ⊔ (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C)) :
          Subgroup (C ⧸ pCore 2 C)) : Subgroup (C ⧸ pCore 2 C)) ⧸
          pCore 2 (B ⊔ (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C)) :
            Subgroup (C ⧸ pCore 2 C)) : Subgroup (C ⧸ pCore 2 C))) ≃*
          PSL(3,ZMod 2)) ∧
        ∃ K : Subgroup C, K.IsCComponent ∧ K.Normal ∧ c.L.subgroupOf C ≤ K ∧
          (K.map q).IsCComponent ∧ (K.map q).Normal ∧ B < K.map q ∧
          IsSimpleGroup (K.map q) ∧ BinaryThreeFiniteSimpleCarrier (K.map q) ∧
          ¬ IsAlternating (K.map q) 7 := by
  obtain ⟨z,hz,hz2,hLS,hout,hsq,hzero,hfour,he,hr,hn,
    P,hP,hB,hSB,hjoin,K,hK,hKn,hLK,hKq,hKnq,hBKq,hsimple,hmodel⟩ :=
    binary_three_large_distance_point_finite_models
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb g hgT hgS
  refine ⟨z,hz,hz2,hLS,hout,hsq,hzero,hfour,he,hr,hn,
    P,hP,hB,hSB,hjoin,K,hK,hKn,hLK,hKq,hKnq,hBKq,hsimple,hmodel,?_⟩
  rintro ⟨a⟩
  exact binary_three_source_point_not_a7
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hz hz2 hLS P hP K hK hKn hLK a

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
