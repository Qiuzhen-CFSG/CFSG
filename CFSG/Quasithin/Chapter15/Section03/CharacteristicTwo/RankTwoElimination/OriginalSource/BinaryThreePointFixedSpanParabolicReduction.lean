module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanComponentWitness
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryExclusion

/-!
# The actual smaller parabolic after binary-five promotion

The containing component supplies a genuine binary-five witness on its
join with the original Sylow. The five-dimensional parabolic construction
therefore produces an actual smaller characteristic-two outside subgroup,
with the same Sylow and rank-two alternative. Its containment here is in
the promoted join; comparison with the initial I is a separate question.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The original degree-four point carrier produces a genuine smaller
outside parabolic inside the promoted binary-five component join. -/
theorem binary_three_source_fixed_span_smaller_parabolic
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
    let A := normalizer (U : Set G)
    ∃ D : Subgroup A, D.IsCComponent ∧ D.Normal ∧ c.L.subgroupOf A ≤ D ∧
      let B := D.map A.subtype
      let J := B ⊔ d.S
      J ∈ d.Hplus ∧ HasCharacteristicTwo J ∧ J ≤ A ∧
      ∃ c5 : ComponentWitness d J, c5.L = B ∧
        Nonempty ((c5.L ⧸ pCore 2 c5.L) ≃* PSL(5,ZMod 2)) ∧
        ∃ H : Subgroup G, H < J ∧ H ∈ d.Hplus ∧ HasCharacteristicTwo H ∧
          Chapter1.IsSylowIn 2 d.S H ∧ OutsideStructure.RankTwoCase d H ∧
          d.Yplus ⊔ d.S ≤ H ∧ H ≤ A := by
  let U := conjugateSpanBy (intrinsicFour c.L) (centralizer ({z} : Set G))
  let A := normalizer (U : Set G)
  obtain ⟨D,hD,hDn,hLD,hfull,hker,hJ,hSJ,hchar,htwoJ,hJA,
    c5,hc5,⟨e5⟩,hY,hθJ,hθNU,hθM⟩ :=
    binary_three_source_fixed_span_component_witness
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
        K hK hKn hLK eB hrX hrB hm
  have hr := OutsideStructure.rankTwoCase_three_rank hG d hI htwo
  obtain ⟨H,hHJ,hH,hfH⟩ := smaller_characteristicTwo_of_binary_five
    d hJ hSJ hchar hr c5 e5 hY hθJ hθM htwoJ
  have htwoH := rankTwoCase_uniform hG d hempty hM hu hmany hI htwo H hH
  have hSH : Chapter1.IsSylowIn 2 d.S H := hSJ.restrict
    (le_sup_right.trans hH.1.2) hHJ.le
  exact ⟨D,hD,hDn,hLD,hJ,hchar,hJA,c5,hc5,⟨e5⟩,
    H,hHJ,hH,hfH,hSH,htwoH,hH.1.2,hHJ.le.trans hJA⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
