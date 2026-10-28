module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanCore
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointNaturalIrreducible

/-!
# The original fixed span has a small center intersection

The checked U≤Q makes U disjoint from the natural four-space W: a nonzero
intersection contains the marked natural eight V, whose C-translates fill W,
contradicting W not≤Q. Consequently U meets Z(Q) in exactly H. The actual
indices Phi:Z(Q)=8 and R:D=8 then bound U intersection Phi by32 and U by256.
All subgroups and the full point kernel are the original ones.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions Extension.SourceCases ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The actual fixed span meets the original center exactly in H and has order at most256. -/
theorem binary_three_source_fixed_span_center_bound
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
    (K : Subgroup ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    (hm : ClassicalGroup.IsPSL K 4 2) :
    let C := centralizer ({z} : Set G)
    let Q := LinearThree.commutatorCore c.L
    let Phi := frattiniIn Q
    let H := intrinsicFour c.L
    let U := conjugateSpanBy H C
    let W := conjugateSpanBy ⁅coreCenter c.L,c.L⁆ C
    U ⊓ W=⊥ ∧ U ⊓ coreCenter c.L=H ∧
      Nat.card (U ⊓ Phi : Subgroup G) ≤ 32 ∧ Nat.card U ≤ 256 := by
  let C := centralizer ({z} : Set G)
  let N := C.pCoreIn 2
  let Q := LinearThree.commutatorCore c.L
  let Phi := frattiniIn Q
  let ZQ := coreCenter c.L
  let D := Q ⊓ centralizer (Phi : Set G)
  let R := Q ⊓ N
  let H := intrinsicFour c.L
  let U := conjugateSpanBy H C
  let V := ⁅ZQ,c.L⁆
  let W := conjugateSpanBy V C
  have hz1 : z ≠ 1 := by
    intro he
    rw [he,orderOf_one] at hz2
    norm_num at hz2
  have hUQ : U ≤ Q := binary_three_source_fixed_span_le_core
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP K hBK hm
  obtain ⟨_,_,hHU,hUN,hCU,_⟩ := binary_three_source_binary_fixed_span
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP K hBK (Or.inl rfl) hm
  obtain ⟨_,hWQ,hWnot⟩ := binary_three_source_natural_core_intersection
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm hzH hz1
  obtain ⟨_,_,hVW,_,hCW,_⟩ := binary_three_source_binary_central_eight_span
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK (Or.inl rfl) hm
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  have hLU : c.L ≤ normalizer U := (le_sup_left.trans hLS).trans hCU
  have hUW : U ⊓ W=⊥ := by
    by_contra hne
    have hle : U ⊓ W ≤ V :=
      (le_inf inf_le_right (inf_le_left.trans hUQ)).trans hWQ.le
    have hn : c.L ≤ normalizer (U ⊓ W : Subgroup G) :=
      (le_inf hLU ((le_sup_left.trans hLS).trans hCW)).trans inf_normalizer_le_normalizer_inf
    have he := binary_three_source_natural_invariant_eq d c.L b t common hb
      (U ⊓ W) V hle hn hne rfl
    have hVU : V ≤ U := he.symm.le.trans inf_le_left
    exact hWnot ((conjugateSpanBy_le hVU hCU).trans hUQ)
  have hHF := (intrinsicFour_properties_of_MS93 d c.L b t common earlier).2.2
  have hHZ : H ≤ ZQ := by
    intro x hx
    refine ⟨⟨x,(hHF hx).1⟩,mem_center_iff.mpr ?_,rfl⟩
    intro y
    exact Subtype.ext ((hHF hx).2 y
      (((LinearThree.commutatorCore_le c.L).trans (c.L.pCoreIn_le 2)) y.property))
  have hUZ : U ⊓ ZQ=H := by
    have hm : ⁅U ⊓ ZQ,c.L⁆ ≤ U ⊓ W := le_inf
      ((commutator_mono inf_le_left le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp hLU))
      ((commutator_mono inf_le_right le_rfl).trans hVW)
    have hcentral : U ⊓ ZQ ≤ centralizer (c.L : Set G) :=
      commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp (hm.trans hUW.le))
    have hfixed : U ⊓ ZQ ≤ coreFixed c.L := le_inf
      (inf_le_right.trans (map_subtype_le _)) hcentral
    have he : coreFixed c.L=H := (binary_three_large_distance_fixed_factor_bound
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb).2.1
    exact le_antisymm (hfixed.trans he.le) (le_inf hHU hHZ)
  have hsizes := binary_three_large_distance_original_core_structure
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb
  have hZcard : Nat.card ZQ=32 := by
    change Nat.card ((center Q).map Q.subtype)=32
    rw [card_map_of_injective Q.subtype_injective]
    exact hsizes.2.1
  have hPhicard : Nat.card Phi=256 := by
    change Nat.card ((frattini Q).map Q.subtype)=256
    rw [card_map_of_injective Q.subtype_injective]
    exact hsizes.2.2.1
  have hZPhi : ZQ ≤ Phi := map_mono hsizes.2.2.2.2.1
  have hZindex : ZQ.relIndex Phi=8 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) ZQ Phi bot_le hZPhi
    rw [relIndex_bot_left,relIndex_bot_left,hZcard,hPhicard] at hh
    omega
  have hHcard : Nat.card H=4 :=
    (intrinsicFour_properties_of_MS93 d c.L b t common earlier).2.1
  have hAcard : Nat.card (U ⊓ Phi : Subgroup G) ≤ 32 := by
    let A := U ⊓ Phi
    have hi : (A ⊓ ZQ).relIndex A ≤ 8 := by
      rw [inf_relIndex_left]
      exact (relIndex_le_of_le_right inf_le_right (by rw [hZindex]; decide)).trans_eq hZindex
    have hb : Nat.card (A ⊓ ZQ : Subgroup G) ≤ 4 :=
      (card_le_of_le ((inf_le_inf_right ZQ inf_le_left).trans hUZ.le)).trans_eq hHcard
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) (A ⊓ ZQ) A bot_le inf_le_left
    rw [relIndex_bot_left,relIndex_bot_left] at hh
    rw [←hh]
    exact (Nat.mul_le_mul hb hi).trans_eq (by decide)
  have hUR : U ≤ R := le_inf hUQ hUN
  have hDindex : D.relIndex R=8 := (binary_three_source_fixed_span_displacement_bound
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm hzH hz1).1
  have hUD : U ⊓ D=U ⊓ Phi := (binary_three_source_fixed_span_middle_intersection
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm hzH hz1).1
  have hUcard : Nat.card U ≤ 256 := by
    have hi : (U ⊓ D).relIndex U ≤ 8 := by
      rw [inf_relIndex_left]
      exact (relIndex_le_of_le_right hUR (by rw [hDindex]; decide)).trans_eq hDindex
    have hb : Nat.card (U ⊓ D : Subgroup G) ≤ 32 := hUD.symm ▸ hAcard
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) (U ⊓ D) U bot_le inf_le_left
    rw [relIndex_bot_left,relIndex_bot_left] at hh
    rw [←hh]
    exact (Nat.mul_le_mul hb hi).trans_eq (by decide)
  exact ⟨hUW,hUZ,hAcard,hUcard⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
