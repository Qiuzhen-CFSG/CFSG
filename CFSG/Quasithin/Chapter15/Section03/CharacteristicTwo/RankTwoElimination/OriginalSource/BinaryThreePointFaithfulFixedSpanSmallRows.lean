module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanSmallRows
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFiniteFourMovement

/-!
# The actual containing component removes the fixed-four row

The original component and normalizer-rank data already force the point
centralizer to move H. In the complete small-order list for U=span_C(H),
order4 would give U=H and make H C-normal. Thus the literal original fixed
span has order32 or64. The actual containing component and both rank flags
are retained; no faithfulness of the whole point quotient is assumed.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- In the actual original containing-component source, U has order32 or64. -/
theorem binary_three_source_four_fixed_span_card
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
    [IsSimpleGroup (K.map (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))))]
    (eB : (((c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))) ⧸
      pCore 2 ((c.L.subgroupOf (centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))))) ≃* PSL(3,ZMod 2))
    (hrX : primeRank 3 (centralizer ({z} : Set G) ⧸ pCore 2 (centralizer ({z} : Set G))) = 2)
    (hrB : primeRank 3 (normalizer ((c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) :
        Set ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))) ≤ 1)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))) 4 2) :
    let U := conjugateSpanBy (intrinsicFour c.L) (centralizer ({z} : Set G))
    Nat.card U=32 ∨ Nat.card U=64 := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let H := intrinsicFour c.L
  let U := conjugateSpanBy H C
  let := hKn
  let : (K.map q).Normal := hKn.map q (QuotientGroup.mk'_surjective _)
  have hBK := map_mono (f := q) hLK
  have hmodel : BinaryThreeFiniteSimpleCarrier (K.map q) := Or.inr (Or.inl ⟨4,Or.inl rfl,hm⟩)
  have hmove := (binary_three_source_finite_component_moves_four
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH K hK hKn hLK eB hrX hrB hmodel).2
  rcases binary_three_source_fixed_span_card_trichotomy
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP (K.map q) hBK hm
    with hfour | hsmall
  · exfalso
    obtain ⟨common⟩ := t.commonFacts hc
    have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
    have hH : Nat.card H=4 := (intrinsicFour_properties_of_MS93 d c.L b t common earlier).2.1
    have he : H=U := eq_of_le_of_card_ge (le_conjugateSpanBy H C) (hfour.trans hH.symm).le
    have hn : C ≤ normalizer U := le_normalizer_conjugateSpanBy H C
    rw [←he] at hn
    exact hmove hn
  · exact hsmall

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
