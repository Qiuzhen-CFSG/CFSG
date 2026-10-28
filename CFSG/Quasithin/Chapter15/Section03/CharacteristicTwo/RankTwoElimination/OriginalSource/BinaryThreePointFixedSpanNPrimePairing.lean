module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointBinaryFixedSpan
public import Theory.GroupTheory.Commutator.NormalSpan

/-!
# Pairing of the fixed span with the derived point kernel

The original four span U is central modulo the original displacement line Z
inside the point 2-core N.  The line Z is central in the full point
centralizer, so the three-subgroup rotation gives [U,[N,N]]=1.  We retain
this literal pairing without identifying the derived point kernel with the
original component core.

Source: Aschbacher--Smith 15.3.23, pp.1128--1129.  No containment of the
derived point kernel in the component core is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource ChapterC BinaryMS.MS93
variable {G : Type*} [Group G] [Finite G]

/-- The original fixed span centralizes the derived point-kernel layer. -/
theorem binary_three_source_fixed_span_nprime_pairing
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
    {n : ℕ} (hn : n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL K n 2) :
    let C := centralizer ({z} : Set G)
    let N := C.pCoreIn 2
    let H := intrinsicFour c.L
    let U := conjugateSpanBy H C
    let E := ⁅N,N⁆
    U ≤ N ∧ U ≤ normalizer E ∧ ⁅E,U⁆ = ⊥ := by
  let C := centralizer ({z} : Set G)
  let N := C.pCoreIn 2
  let H := intrinsicFour c.L
  let Z := zpowers z
  let U := conjugateSpanBy H C
  let E := ⁅N,N⁆
  obtain ⟨_,_,_,hUN,hCU,hUNcomm,_⟩ := binary_three_source_binary_fixed_span
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP K hBK hn hm
  have hNC : N ≤ C := C.pCoreIn_le 2
  have hCN : C ≤ normalizer N := C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hCE : C ≤ normalizer E := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator, mem_normalizer_iff_map_conj_eq.mp (hCN hx)]
  have hZC : Z ≤ centralizer (C : Set G) := by
    apply zpowers_le.mpr
    intro x hx
    exact mem_centralizer_singleton_iff.mp hx
  have hZN : ⁅Z,N⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (hZC.trans (centralizer_le hNC))
  have hNUN : ⁅⁅N,U⁆,N⁆ = ⊥ := by
    rw [commutator_comm N U]
    exact le_bot_iff.mp ((commutator_mono hUNcomm le_rfl).trans hZN.le)
  have hEU : ⁅E,U⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate hNUN
    (by rwa [commutator_comm U N])
  have hUC : U ≤ C := hUN.trans hNC
  exact ⟨hUN, hUC.trans hCE, hEU⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
