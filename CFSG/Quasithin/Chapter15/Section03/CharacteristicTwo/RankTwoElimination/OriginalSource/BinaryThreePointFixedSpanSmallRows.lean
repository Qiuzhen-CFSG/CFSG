module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanCenter

/-!
# The complete original fixed-span order alternatives

The actual center/intersection bound puts U at order at most256. The unchanged
fifteen-coordinate kernel certificate then leaves quotient dimensions1,4,5.
The original point line is the full kernel of order2, so U has order4,32,64.
This retains the small trivial-action row; it is not a faithfulness assumption.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Matrix
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open BinaryEndpointInduction
variable {G : Type*} [Group G] [Finite G]

/-- All actual fixed-span orders surviving the full original fifteen-coordinate kernel list. -/
theorem binary_three_source_fixed_span_card_trichotomy
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
    let U := conjugateSpanBy (intrinsicFour c.L) (centralizer ({z} : Set G))
    Nat.card U=4 ∨ Nat.card U=32 ∨ Nat.card U=64 := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let B := (c.L.subgroupOf C).map q
  let H := intrinsicFour c.L
  let Z := zpowers z
  let U := conjugateSpanBy H C
  have hUcard : Nat.card U ≤ 256 := (binary_three_source_fixed_span_center_bound
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP K hBK hm).2.2.2
  obtain ⟨hZ,hel,ρ,_,h,hw,_,_,hcoords⟩ := binary_three_source_fixed_span_coordinates
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP K hBK hm
  let := hZ
  let := hel
  let E := Additive (U ⧸ Z.subgroupOf U)
  obtain ⟨_,_,_,a,v,_,hflag⟩ :=
    binary_three_point_four_endpoint_equality d c.L b z hLS P hP K hBK hm
  obtain ⟨eK,heK⟩ := exists_endpointParabolic_marking (B.subgroupOf K) a v hflag
  obtain ⟨F,hF,_,_,r,_,hd⟩ := hcoords eK heK
  have hEcard : Nat.card E ≤ 256 := (Nat.card_le_card_of_surjective
    (QuotientGroup.mk' (Z.subgroupOf U)) (QuotientGroup.mk'_surjective _)).trans hUcard
  have hdim : Module.finrank (ZMod 2) E ≤ 8 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hEcard
    exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hEcard
  have hpos : 0 < Module.finrank (ZMod 2) E :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_,hw⟩
  have hcases : Module.finrank (ZMod 2) E=1 ∨
      Module.finrank (ZMod 2) E=4 ∨ Module.finrank (ZMod 2) E=5 := by
    change Module.finrank (ZMod 2) E + BinaryFifteenPoint.rowDimension r=15 at hd
    fin_cases r <;> norm_num [BinaryFifteenPoint.rowDimension] at hd <;> omega
  have hZU : Z ≤ U := zpowers_le.mpr (le_conjugateSpanBy H C hzH)
  have hZcard : Nat.card (Z.subgroupOf U)=2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hZU).toEquiv,Nat.card_zpowers,hz2]
  have hcount := card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf U)
  change Nat.card U=Nat.card E*Nat.card (Z.subgroupOf U) at hcount
  rw [hZcard,Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E),Nat.card_zmod] at hcount
  rcases hcases with hcase | hcase | hcase
  · left
    norm_num [hcase] at hcount ⊢
    exact hcount
  · right; left
    norm_num [hcase] at hcount ⊢
    exact hcount
  · right; right
    norm_num [hcase] at hcount ⊢
    exact hcount

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
