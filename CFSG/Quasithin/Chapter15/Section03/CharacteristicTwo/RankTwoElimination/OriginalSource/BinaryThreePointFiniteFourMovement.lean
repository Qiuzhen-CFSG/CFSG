module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointA7Exclusion
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointCubicSupport
public import Theory.GroupTheory.CComponent.CenterlessRankNormal
public import Theory.GroupTheory.PrimeRankCoprimeIndex

/-!
# Every remaining finite point component moves the original four

The literal finite containing component has the full three-rank of the
point quotient: its index is prime to three by the original smaller
normalizer bound and the proved outer-two catalogue. If that component
normalized the original four, perfectness would make it centralize the
four. It would then persist as a C-component in the full four-normalizer.
The rank bound forces this same component to be normal there and to have
index prime to three. The nontrivial cubic automizer of the four contradicts
that index. This proves movement by the actual component itself, retaining
the point quotient and its maps.

Source: Aschbacher--Smith A.3.18 and15.3.23, pp.51--53 and1128--1129.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource LinearThree.CoreActions LinearThree.Extension.SourceCases ChapterC BinaryMS.MS93
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

private theorem component_not_normalizes_four
    (F C : Subgroup G) (hF : Nat.card F ≤ 4)
    (hCF : centralizer (F : Set G) ≤ C)
    (hmove : 3 ∣ Nat.card F.normalizerMonoidHom.range)
    (hr : primeRank 3 (normalizer (F : Set G)) ≤ 2)
    (K : Subgroup C) (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hz : center (K ⧸ pCore 2 K) = ⊥)
    (hthree : 2 ≤ primeRank 3 (K ⧸ pCore 2 K))
    (ho : Nat.Coprime 3 (Nat.card (MulAut.Outer (K ⧸ pCore 2 K)))) :
    ¬ K.map C.subtype ≤ normalizer (F : Set G) := by
  intro hAN
  let NF := normalizer (F : Set G)
  let A := K.map C.subtype
  let E := A.subgroupOf NF
  let i : E ≃* K := (subgroupOfEquivOfLe hAN).trans
    (K.equivMapOfInjective C.subtype C.subtype_injective).symm
  let : Group.IsPerfect K := hK.perfect
  let : Group.IsPerfect E := Group.IsPerfect.ofSurjective (f := i.symm.toMonoidHom) i.symm.surjective
  let M := F.subgroupOf NF
  let : M.Normal := normal_subgroupOf_of_le_normalizer (show NF ≤ normalizer (F : Set G) from le_rfl)
  have hM : Nat.card M ≤ 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe F.le_normalizer).toEquiv]
    exact hF
  have hEM := le_centralizer_of_isPerfect_of_card_le_four E M hM
  have hAF : A ≤ centralizer (F : Set G) := by
    intro x hx y hy
    exact congrArg Subtype.val
      (hEM (show (⟨x,hAN hx⟩ : NF) ∈ E from hx) ⟨y,F.le_normalizer hy⟩ hy)
  have hAp : (A.subgroupOf C).IsCComponent := by
    change ((K.map C.subtype).comap C.subtype).IsCComponent
    rwa [comap_map_eq_self_of_injective C.subtype_injective]
  have hE : E.IsCComponent := hAp.in_normalizer_of_centralizes hAF hCF
  let e := QuotientGroup.congr _ _ i (pCore_map_iso 2 i)
  let : IsQuasisimple (E ⧸ pCore 2 E) := IsQuasisimple.of_mulEquiv e.symm
  have hzE : center (E ⧸ pCore 2 E) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    exact e.map_eq_one_iff.mp (hz.le ((centerCongr e) ⟨x,hx⟩).property)
  have hrE : 2 ≤ primeRank 3 (E ⧸ pCore 2 E) := by
    rwa [primeRank_congr 3 e]
  have hoE : Nat.Coprime 3 (Nat.card (MulAut.Outer (E ⧸ pCore 2 E))) := by
    rwa [Nat.card_congr (MulAut.outerCongr e).toEquiv]
  let : E.Normal := hE.normal_of_centerless_core_threeRank hzE hrE hr
  have hi := cComponent_index_coprime_three_of_quotient E hE hzE hrE hr hoE
  have hker : E ≤ F.normalizerMonoidHom.ker := by
    rw [normalizerMonoidHom_ker]
    intro x hx
    exact hAF hx
  have hdiv : 3 ∣ E.index := by
    have hh : 3 ∣ F.normalizerMonoidHom.ker.index := by
      rwa [index_ker]
    exact hh.trans (index_dvd_of_le hker)
  exact (Nat.prime_three.coprime_iff_not_dvd.mp hi) hdiv

/-- The original finite point packet forces the containing component,
and hence the point centralizer, to move the unchanged intrinsic four. -/
theorem binary_three_source_finite_component_moves_four
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
    (z : G) (hzH : z ∈ intrinsicFour c.L)
    (K : Subgroup (centralizer ({z} : Set G)))
    (hK : K.IsCComponent) (hKn : K.Normal)
    (hLK : c.L.subgroupOf (centralizer ({z} : Set G)) ≤ K)
    [IsSimpleGroup (K.map (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))))]
    (eB : (((c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))) ⧸
      pCore 2 ((c.L.subgroupOf (centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))))) ≃* PSL(3,ZMod 2))
    (hrX : primeRank 3 ((centralizer ({z} : Set G)) ⧸
      pCore 2 (centralizer ({z} : Set G))) = 2)
    (hrB : primeRank 3 (normalizer ((c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) :
        Set ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))) ≤ 1)
    (hm : BinaryThreeFiniteSimpleCarrier (K.map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))))) :
    ¬ K.map (centralizer ({z} : Set G)).subtype ≤ normalizer (intrinsicFour c.L) ∧
      ¬ centralizer ({z} : Set G) ≤ normalizer (intrinsicFour c.L) := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let B := (c.L.subgroupOf C).map q
  let F := coreFixed c.L
  let : K.Normal := hKn
  let : (K.map q).Normal := hKn.map q (QuotientGroup.mk'_surjective _)
  have hi := binary_three_finite_containing_index_coprime_three (map_mono hLK) eB hrB hm
  have hthree : 2 ≤ primeRank 3 (K.map q) := by
    rw [primeRank_eq_of_not_dvd_index (K.map q) (Nat.prime_three.coprime_iff_not_dvd.mp hi),hrX]
  let eK := cComponentTwoCoreQuotientEquiv hK
  let : Group.IsPerfect K := hK.perfect
  let : IsSimpleGroup (K ⧸ pCore 2 K) := eK.isSimpleGroup
  have hz : center (K ⧸ pCore 2 K) = ⊥ :=
    (inferInstance : (center (K ⧸ pCore 2 K)).Normal).eq_bot_or_eq_top.resolve_right
      (fun h => Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp h))
  let : IsQuasisimple (K ⧸ pCore 2 K) :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  have hrK : 2 ≤ primeRank 3 (K ⧸ pCore 2 K) := by rwa [primeRank_congr 3 eK]
  have ho : Nat.Coprime 3 (Nat.card (MulAut.Outer (K ⧸ pCore 2 K))) := by
    rw [Nat.card_congr (MulAut.outerCongr eK).toEquiv]
    obtain ⟨n,hn⟩ := (binary_three_finite_carrier_outer_two hm).exists_card_dvd_pow
    exact ((by decide : Nat.Coprime 3 2).pow_right n).coprime_dvd_right hn
  obtain ⟨hF,hFH,_,_⟩ := binary_three_large_distance_fixed_factor_bound
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb
  change Nat.card F = 4 at hF
  change F = intrinsicFour c.L at hFH
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
  have hmove : 3 ∣ Nat.card F.normalizerMonoidHom.range := by
    rw [MonoidHom.range_eq_top.mpr hnormal.2.2.2.1,card_top,IsKleinFour.card_mulAut F]
    decide
  have hnot := component_not_normalizes_four F C hF.le hFC hmove hr K hK hz hrK ho
  rw [hFH] at hnot
  exact ⟨hnot,fun hC => hnot ((map_subtype_le K).trans hC)⟩

/-- The complete original finite point packet retains every flag and
the A7 exclusion, and records genuine movement of the original four. -/
theorem binary_three_large_distance_finite_point_four_movement
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
          ¬ IsAlternating (K.map q) 7 ∧
          ¬ K.map C.subtype ≤ normalizer (intrinsicFour c.L) ∧
          ¬ C ≤ normalizer (intrinsicFour c.L) := by
  obtain ⟨z,hz,hz2,hLS,hout,hsq,hzero,hfour,⟨eB⟩,hr,hn,
    P,hP,hB,hSB,hjoin,K,hK,hKn,hLK,hKq,hKnq,hBKq,hsimple,hmodel,hnot7⟩ :=
    binary_three_large_distance_point_finite_models_not_a7
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb g hgT hgS
  let := hsimple
  obtain ⟨hKmove,hCmove⟩ := binary_three_source_finite_component_moves_four
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hz K hK hKn hLK eB hr hn hmodel
  exact ⟨z,hz,hz2,hLS,hout,hsq,hzero,hfour,⟨eB⟩,hr,hn,
    P,hP,hB,hSB,hjoin,K,hK,hKn,hLK,hKq,hKnq,hBKq,hsimple,hmodel,hnot7,hKmove,hCmove⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
