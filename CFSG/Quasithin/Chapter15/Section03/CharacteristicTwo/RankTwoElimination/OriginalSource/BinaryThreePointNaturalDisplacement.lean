module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointMiddleKernel
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointNaturalIrreducible

/-!
# Exact displacement of the original natural-four span

The original L and its core Q both move W onto the same marked natural
three-space V. The middle core lies in the actual point kernel, so it
centralizes W. All three conclusions retain the original ambient subgroups.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The actual natural-four span has exact L- and Q-displacement V, and the middle core centralizes it. -/
theorem binary_three_source_natural_displacement
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
    (z : G) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    (hm : ClassicalGroup.IsPSL K 4 2)
    (hz : z ∈ intrinsicFour c.L) (hz1 : z ≠ 1) :
    let C := centralizer ({z} : Set G)
    let N := C.pCoreIn 2
    let Q := LinearThree.commutatorCore c.L
    let D := Q ⊓ centralizer (frattiniIn Q : Set G)
    let V := ⁅coreCenter c.L,c.L⁆
    let W := conjugateSpanBy V C
    ⁅W,c.L⁆ = V ∧ ⁅W,Q⁆ = V ∧ D ≤ N ∧ ⁅W,D⁆ = ⊥ := by
  let C := centralizer ({z} : Set G)
  let N := C.pCoreIn 2
  let Q := LinearThree.commutatorCore c.L
  let D := Q ⊓ centralizer (frattiniIn Q : Set G)
  let V := ⁅coreCenter c.L,c.L⁆
  let W := conjugateSpanBy V C
  obtain ⟨hWcard,_,_⟩ := binary_three_source_natural_core_intersection
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm hz hz1
  change Nat.card W = 16 at hWcard
  obtain ⟨hfix,hWQ,hWL,_⟩ := binary_three_source_natural_core_quotient
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm hz hz1
  obtain ⟨_,_,_,hWcenter,hCW,_⟩ := binary_three_source_binary_central_eight_span
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK (Or.inl rfl) hm
  have hLW : c.L ≤ normalizer W := (le_sup_left.trans hLS).trans hCW
  have hLQ : c.L ≤ normalizer Q := c.L.le_normalizer.trans
    (normalizer_le_normalizer_commutatorCore c.L)
  have hWLne : ⁅W,c.L⁆ ≠ ⊥ := by
    intro he
    have hcL : W ≤ centralizer (c.L : Set G) :=
      commutator_eq_bot_iff_le_centralizer.mp he
    have hh := (binary_three_source_four_fixed_intersection
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm).1
    rw [inf_eq_left.mpr hcL] at hh
    rw [hh,Subgroup.card_bot] at hWcard
    omega
  have hWQne : ⁅W,Q⁆ ≠ ⊥ := by
    intro he
    have hQW : Q ≤ centralizer (W : Set G) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)
    have hQR : Q = Q ⊓ N := (inf_eq_left.mpr hQW).symm.trans hfix
    have hRcard : Nat.card (Q ⊓ N : Subgroup G) = 131072 := by
      have hh := (binary_three_source_binary_core_sizes
        hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK (Or.inl rfl) hm).2
      simpa only [Nat.reduceSub,Nat.reduceMul,Nat.reducePow] using hh
    have hQcard : Nat.card Q = 1048576 := (binary_three_large_distance_original_core_structure
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb).2.2.2.1
    rw [hQR,hRcard] at hQcard
    omega
  obtain ⟨common⟩ := t.commonFacts hc
  have hWLeq : ⁅W,c.L⁆ = V := binary_three_source_natural_invariant_eq
    d c.L b t common hb _ V hWL (normalizer_commutator_ge_right _ _) hWLne rfl
  have hLWQ : c.L ≤ normalizer (⁅W,Q⁆ : Subgroup G) := by
    intro l hl
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp (hLW hl),
      mem_normalizer_iff_map_conj_eq.mp (hLQ hl)]
  have hWQeq : ⁅W,Q⁆ = V := binary_three_source_natural_invariant_eq
    d c.L b t common hb _ V hWQ hLWQ hWQne rfl
  have hDN : D ≤ N := binary_three_source_natural_middle_kernel
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm hz hz1
  have hWNc : W ≤ centralizer (N : Set G) := by
    intro x hx
    obtain ⟨w,hw,rfl⟩ := hWcenter hx
    intro n hn
    exact congrArg Subtype.val (mem_center_iff.mp hw ⟨n,hn⟩)
  exact ⟨hWLeq,hWQeq,hDN,commutator_eq_bot_iff_le_centralizer.mpr
    (hWNc.trans (centralizer_le hDN))⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
