module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.HexadCover.Design
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.PartitionStructure.Actions
public import Mathlib.GroupTheory.Perm.MaximalSubgroups

/-!
# Generating the marked hexad stabilizer

The pair stabilizer on six points is maximal in S₆. A permutation
interchanging two marked pairs preserves the three-pair partition but
moves the distinguished pair. Its actual inner lift, together with the
pair--hexad stabilizer, therefore generates the whole hexad stabilizer.
This is the design-level generation input in Aschbacher--Smith 14.4.12,
printed pp.1011--1012; native generation is supplied by cubic survival.
-/

@[expose] public section
open Subgroup Sporadic.Mathieu
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.HexadCover
open M22ValueBound.Concrete

private def markedPair : Set m22Hexad123 := {⟨1, by decide⟩, ⟨2, by decide⟩}

private theorem markedPair_mem (a : m22Hexad123) :
    a ∈ markedPair ↔ a.val ∈ m22Pair12 := by
  simp only [markedPair, Set.mem_insert_iff, Set.mem_singleton_iff, m22Pair12,
    Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]

private theorem pair_preimage :
    (MulAction.stabilizer (Equiv.Perm m22Hexad123) markedPair).comap
      (M22OuterHexad.setAction m22Hexad123) =
      outerPairHexad.subgroupOf (MulAction.stabilizer m22DesignAut m22Hexad123) := by
  ext g
  change M22OuterHexad.setAction m22Hexad123 g ∈
    MulAction.stabilizer (Equiv.Perm m22Hexad123) markedPair ↔
    g.val ∈ outerPairHexad
  rw [MulAction.mem_stabilizer_set]
  change (∀ a : m22Hexad123, _ ↔ _) ↔
    (g.val ∈ MulAction.stabilizer m22DesignAut m22Hexad123 ∧ g.val ∈ outerFirst)
  rw [and_iff_right g.property]
  constructor
  · intro h
    apply MulAction.mem_stabilizer_finset'.mpr
    intro a ha
    have haB := PartitionStructure.subset_hexad_of_mem pair_mem_hexadPartition ha
    exact (markedPair_mem _).mp ((h ⟨a, haB⟩).mpr ((markedPair_mem _).mpr ha))
  · intro h a
    rw [markedPair_mem, markedPair_mem]
    change (g.val • a.val ∈ m22Pair12) ↔ (a.val ∈ m22Pair12)
    exact MulAction.mem_stabilizer_finset.mp h a.val

private theorem pair_isCoatom :
    IsCoatom (outerPairHexad.subgroupOf
      (MulAction.stabilizer m22DesignAut m22Hexad123)) := by
  rw [← pair_preimage]
  have hs : Function.Surjective (M22OuterHexad.setAction m22Hexad123) := by
    intro x
    obtain ⟨g, hg⟩ := action_surjective m22Hexad123_mem
      ((m22HexadLabels m22Hexad123_mem).permCongrHom x)
    exact ⟨g, (m22HexadLabels m22Hexad123_mem).permCongrHom.injective hg⟩
  apply isCoatom_comap_of_surjective hs
  apply Equiv.Perm.isCoatom_stabilizer_of_ncard_lt_ncard_compl
  · exact ⟨⟨1, by decide⟩, Set.mem_insert _ _⟩
  · have hpair : markedPair.ncard = 2 := by
      rw [markedPair, Set.ncard_pair (by decide)]
    have htotal := Set.ncard_add_ncard_compl markedPair
    have hc : Nat.card m22Hexad123 = 6 := by
      rw [Nat.card_eq_fintype_card]
      decide +kernel
    rw [hpair, hc] at htotal
    omega

theorem outerSecond_le_hexad :
    outerSecond ≤ MulAction.stabilizer m22DesignAut m22Hexad123 := by
  intro g hg
  change g • m22Hexad123 = m22Hexad123
  rw [← hexadPartition_union]
  have he : g • hexadPartition.biUnion id = (g • hexadPartition).biUnion id := by
    simp only [Finset.smul_finset_def, Finset.image_biUnion, Finset.biUnion_image]
    rfl
  rw [he, MulAction.mem_stabilizer_iff.mp hg]

private theorem second_not_le_pair : ¬ outerSecond ≤ outerPairHexad := by
  intro h
  let w := PartitionStructure.smallSwap₁
  have hw : w.val ∈ (m22SetAction m22Hexad123).range := by
    rw [PartitionStructure.restriction_range]
    exact w.property.2
  obtain ⟨g, hg⟩ := hw
  have hs : g.val ∈ second := by
    change g ∈ second.subgroupOf (MulAction.stabilizer M22 m22Hexad123)
    rw [← PartitionStructure.second_preimage]
    change m22SetAction m22Hexad123 g ∈ PartitionStructure.smallGroup
    rw [hg]
    exact w.property
  have hp := (h (show inclusion g.val ∈ outerSecond from hs)).2
  have hm : Equiv.Perm.ofSubtype w.val • m22Pair12 = m22Pair12 := by
    rw [← hg, PartitionStructure.restriction_agrees g
      (PartitionStructure.subset_hexad_of_mem pair_mem_hexadPartition)]
    exact MulAction.mem_stabilizer_iff.mp hp
  have hn : Equiv.Perm.ofSubtype PartitionStructure.smallSwap₁.val • m22Pair12 ≠ m22Pair12 := by
    decide +kernel
  exact hn hm

/-- The two marked parabolics generate the literal full hexad stabilizer. -/
theorem outerPairHexad_sup_outerSecond :
    outerPairHexad ⊔ outerSecond = MulAction.stabilizer m22DesignAut m22Hexad123 := by
  let H := MulAction.stabilizer m22DesignAut m22Hexad123
  have hP : outerPairHexad ≤ H := inf_le_left
  have hS : outerSecond ≤ H := outerSecond_le_hexad
  have hlt : outerPairHexad.subgroupOf H <
      (outerPairHexad ⊔ outerSecond).subgroupOf H := by
    apply lt_of_le_of_ne (subgroupOf_mono H le_sup_left)
    intro he
    apply second_not_le_pair
    intro x hx
    have hm : (⟨x, hS hx⟩ : H) ∈ (outerPairHexad ⊔ outerSecond).subgroupOf H :=
      (show outerSecond ≤ outerPairHexad ⊔ outerSecond from le_sup_right) hx
    rw [← he] at hm
    exact hm
  have ht := pair_isCoatom.2 _ hlt
  exact (sup_le hP hS).antisymm (subgroupOf_eq_top.mp ht)

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.HexadCover
