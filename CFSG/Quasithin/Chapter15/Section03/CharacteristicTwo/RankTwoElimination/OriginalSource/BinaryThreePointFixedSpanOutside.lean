module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanUnique
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanKernelIndex
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource.Residual

/-!
# The fixed-span normalizer is an original outside subgroup

The unique span is normalized by the original component normalizer, hence
by Yplus and S. It is a nontrivial normal elementary two-subgroup of its
normalizer. The original outside-subgroup theorem therefore supplies the
same S as a Sylow subgroup and trivial odd core.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The actual fixed-span normalizer retains the original outside family,
Sylow subgroup, strong quasithin hypothesis, and odd-core control. -/
theorem binary_three_source_fixed_span_outside
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
    let NU := normalizer (U : Set G)
    d.Yplus ⊔ d.S ≤ NU ∧ c.L ⊔ d.S ≤ NU ∧ NU ∈ d.Hplus ∧
      Chapter1.IsSylowIn 2 d.S NU ∧ IsSQTK KnownSimple.IsKnownSimple NU ∧
      pPrimeCore 2 NU = ⊥ := by
  let C := centralizer ({z} : Set G)
  let U := conjugateSpanBy (intrinsicFour c.L) C
  let NU := normalizer (U : Set G)
  have hnorm : normalizer (c.L : Set G) ≤ NU :=
    (binary_three_source_fixed_span_unique
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
        K hK hKn hLK eB hrX hrB hm).2
  have hYL : d.Yplus ≤ normalizer (c.L : Set G) :=
    LinearThree.OriginalSource.residual_normalizes_component d c
  have hSL : d.S ≤ normalizer (c.L : Set G) :=
    le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer
      (show c.L ≤ c.L ⊔ d.S from le_sup_left)).mp b.component_normal)
  have hYS : d.Yplus ⊔ d.S ≤ NU := sup_le (hYL.trans hnorm) (hSL.trans hnorm)
  have hLNU : c.L ≤ NU := c.L.le_normalizer.trans hnorm
  have hLSNU : c.L ⊔ d.S ≤ NU := sup_le hLNU (hSL.trans hnorm)
  have hUp : IsPGroup 2 U := (binary_three_source_fixed_span_kernel_index
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm).1.isPGroup
  have hUne : U ≠ ⊥ := by
    intro hbot
    have hz1 : z = 1 := hbot.le (le_conjugateSpanBy _ C hzH)
    rw [hz1,orderOf_one] at hz2
    norm_num at hz2
  have hlocal : IsTwoLocal NU := ⟨U,hUne,hUp,rfl⟩
  have hplus : NU ∈ d.Hplus :=
    ⟨⟨Chapter1.mem_H_of_isTwoLocal hlocal,hYS⟩,fun hh => c.outside (hLNU.trans hh)⟩
  have hout := OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany NU hplus
  exact ⟨hYS,hLSNU,hplus,hout.sylow,hG.twoLocal_sqtk hlocal,hout.odd_core⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
