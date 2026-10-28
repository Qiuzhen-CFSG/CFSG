module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanComponentStar
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanThompsonJoin

/-!
# A genuine binary-five component witness in the actual Sylow join

The normal containing component lies in the elementary Thompson subgroup
of its join with the original Sylow. Its genuine star image and residual
commutator generation complete all fields of ComponentWitness. The original
selection then supplies theta and rank-two statements for this same join.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- All fields of the binary-five ComponentWitness hold for the same
promoted component and the literal join with the original S. -/
theorem binary_three_source_fixed_span_component_witness
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
      Function.Surjective (U.normalizerMonoidHom.comp D.subtype) ∧
      (U.normalizerMonoidHom.comp D.subtype).ker = pCore 2 D ∧
      let B := D.map A.subtype
      let J := B ⊔ d.S
      J ∈ d.Hplus ∧ Chapter1.IsSylowIn 2 d.S J ∧ HasCharacteristicTwo J ∧
      OutsideStructure.RankTwoCase d J ∧ J ≤ A ∧
      ∃ c5 : ComponentWitness d J, c5.L = B ∧
        Nonempty ((c5.L ⧸ pCore 2 c5.L) ≃* PSL(5,ZMod 2)) ∧
        d.Yplus ≤ c5.L ∧ c5.L = theta J ∧ c5.L = theta A ∧
        theta (d.MI J) = d.Yplus := by
  let U := conjugateSpanBy (intrinsicFour c.L) (centralizer ({z} : Set G))
  let A := normalizer (U : Set G)
  obtain ⟨D,hD,hDn,hLD,hfull,hker,⟨eG⟩,hθ,hY,hchar,hJ,hSJ,hBM,hr,hq,hstar,hcomm⟩ :=
    binary_three_source_fixed_span_component_star
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
        K hK hKn hLK eB hrX hrB hm
  let B := D.map A.subtype
  let J := B ⊔ d.S
  have hTh := binary_three_source_fixed_span_thompson_join
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm D hD hDn hLD
  let c5 : ComponentWitness d J :=
    { L := B
      le_thompson := hTh.1
      component := hTh.2
      outside := hBM
      rank_pos := le_trans (by decide : 1 ≤ 2) hr
      commutator_eq := hcomm
      star_quasisimple := hstar
      core_quotient_quasisimple := hq }
  have hθJ : c5.L = theta J := (source_lemma_15_3_17_binary_four_five
    hG d hempty hM hu hmany hJ c5 (Or.inr rfl) eG).2
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany J hJ
  have htwoJ : OutsideStructure.RankTwoCase d J :=
    ComponentIntersection.rank_two_case_of_three_rank_two d J h11.local_structure
      (OutsideStructure.rankTwoCase_three_rank hG d hI htwo)
  have hout := binary_three_source_fixed_span_outside
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm
  have hJA : J ≤ A := sup_le (map_subtype_le D) (le_sup_right.trans hout.2.1)
  exact ⟨D,hD,hDn,hLD,hfull,hker,hJ,hSJ,hchar,htwoJ,hJA,
    c5,rfl,⟨eG⟩,hY,hθJ,hθ,h11.theta_eq.symm⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
