module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanContainingComponent
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanNormalizerCore
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanProduct
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.Inheritance

/-!
# Strict enlargement of the original outside subgroup

The original relative Thompson component is a C-component of I. Full
Sylow normalization makes it normal in I, so uniqueness of its fixed span
puts I inside N_G(U). The two-core strictly decreases: it centralizes U,
whereas the original core contains Q and [U,Q] is the nontrivial four H.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The fixed-span normalizer strictly contains the original I, and has
strictly smaller two-core, all as literal ambient subgroups. -/
theorem binary_three_source_fixed_span_strict_overgroup
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
    I < NU ∧ NU.pCoreIn 2 < I.pCoreIn 2 := by
  let C := centralizer ({z} : Set G)
  let U := conjugateSpanBy (intrinsicFour c.L) C
  let NU := normalizer (U : Set G)
  have hSI : d.S ≤ I := le_sup_right.trans hI.1.2
  have hLSI : c.L ⊔ d.S ≤ I := sup_le (component_le c) hSI
  have hSyl := (OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI).sylow
  obtain ⟨D,hD,hDn,hLD,_⟩ := binary_three_source_outside_normal_component
    hG d c.L b I hI hLSI hSyl
  have hcomp := LocalData.thompson_component_in c.le_thompson c.component
  have hDeq : c.L.subgroupOf I = D := hcomp.eq_of_le hD hLD
  have hnormal : (c.L.subgroupOf I).Normal := hDeq.symm ▸ hDn
  have hIL : I ≤ normalizer (c.L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (component_le c)).mp hnormal
  have hINU : I ≤ NU := hIL.trans (binary_three_source_fixed_span_unique
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm).2
  have hout := binary_three_source_fixed_span_outside
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm
  have hcorele : NU.pCoreIn 2 ≤ I.pCoreIn 2 :=
    twoCoreIn_le_of_sylow_overgroup hout.2.2.2.1 hINU hSI
  have hcorefix : NU.pCoreIn 2 ≤ centralizer (U : Set G) := by
    rw [binary_three_source_fixed_span_normalizer_core
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
        K hK hKn hLK eB hrX hrB hm]
    exact inf_le_right
  have hQcore : LinearThree.commutatorCore c.L ≤ I.pCoreIn 2 :=
    (LinearThree.commutatorCore_le c.L).trans
      (pCoreIn_mono_of_normalizes (component_le c) hIL)
  have hstrict : NU.pCoreIn 2 < I.pCoreIn 2 := by
    apply lt_of_le_of_ne hcorele
    intro heq
    have hQfix := hQcore.trans (heq ▸ hcorefix)
    have hcomm : ⁅U,LinearThree.commutatorCore c.L⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hQfix)
    have hH := (binary_three_source_fixed_span_frattini_product
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
        K hK hKn hLK eB hrX hrB hm).2
    have hz1 : z = 1 := (hH.symm.trans hcomm).le hzH
    rw [hz1,orderOf_one] at hz2
    norm_num at hz2
  refine ⟨lt_of_le_of_ne hINU ?_,hstrict⟩
  intro heq
  exact hstrict.ne (congrArg (fun A : Subgroup G => A.pCoreIn 2) heq).symm

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
