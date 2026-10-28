module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Involution centralizers and pair partitions

For an actual involution t, its centralizer is exactly the setwise stabilizer of
the blocks {a,t(a)}. The proof recovers the commuting action equation from the
unordered pair in each block. In cycle type 2,2,2 on seven points these blocks
are precisely the cyclic orbits, and their sizes form the partition 2,2,2,1.

Source: Aschbacher–Smith, 1.1.5(3)(d), printed pp.501–502, and the A7 paragraph
of 15.3.43, printed p.1140. These intrinsic action identities do not assume the
normalizer classification required in that paragraph.
-/

@[expose] public section

open Subgroup
open scoped Pointwise
namespace AlternatingSeven.ThreeResidualLocals

/-- The blocks of the partition associated to an involution, including its fixed points. -/
def pairPartition {α : Type*} (t : Equiv.Perm α) : Set (Set α) :=
  Set.range (fun a => ({a, t a} : Set α))

/-- The setwise stabilizer of the family of blocks, allowing permutation of the blocks. -/
def pairPartitionStabilizer {α : Type*} (t : Equiv.Perm α) : Subgroup (Equiv.Perm α) :=
  MulAction.stabilizer (Equiv.Perm α) (pairPartition t)

private theorem image_pair {α : Type*} (g t : Equiv.Perm α) (a : α) :
    g • ({a, t a} : Set α) = ({g a, g (t a)} : Set α) := by
  exact Set.image_pair _ _ _

/-- For an involution, preserving its blocks is exactly commuting with its actual action. -/
theorem mem_pairPartitionStabilizer_iff {α : Type*} (t g : Equiv.Perm α)
    (ht : t ^ 2 = 1) :
    g ∈ pairPartitionStabilizer t ↔ ∀ a, g (t a) = t (g a) := by
  have htt (a : α) : t (t a) = a := by
    have h := congrArg (fun f : Equiv.Perm α => f a) ht
    simpa [pow_two] using h
  change g • pairPartition t = pairPartition t ↔ _
  constructor
  · intro h a
    have hi : g • ({a, t a} : Set α) ∈ pairPartition t := by
      rw [← h]
      exact Set.smul_mem_smul_set ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := hi
    rw [image_pair] at hb
    rcases Set.pair_eq_pair_iff.mp hb.symm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, htt]
  · intro h
    ext s
    constructor
    · rintro ⟨u, ⟨a, rfl⟩, rfl⟩
      refine ⟨g a, ?_⟩
      change {g a, t (g a)} = g • ({a, t a} : Set α)
      rw [image_pair, h]
    · rintro ⟨a, rfl⟩
      refine Set.mem_smul_set.mpr ⟨{g⁻¹ a, t (g⁻¹ a)}, ⟨g⁻¹ a, rfl⟩, ?_⟩
      rw [image_pair, h]
      simp

/-- The centralizer of an involution is its partition stabilizer. -/
theorem centralizer_eq_pairPartitionStabilizer {α : Type*} (t : Equiv.Perm α)
    (ht : t ^ 2 = 1) :
    centralizer ({t} : Set (Equiv.Perm α)) = pairPartitionStabilizer t := by
  ext g
  rw [mem_centralizer_singleton_iff, mem_pairPartitionStabilizer_iff t g ht]
  exact Equiv.ext_iff

/-- Cycle type `2,2,2` gives the partition `2,2,2,1` on seven points. -/
theorem partition_parts_of_cycleType_three_twos (t : Equiv.Perm (Fin 7))
    (ht : t.cycleType = {2, 2, 2}) : t.partition.parts = {2, 2, 2, 1} := by
  rw [Equiv.Perm.parts_partition, ← t.sum_cycleType, ht]
  decide

/-- The action equation follows from the cycle type, without an abstract involution tag. -/
theorem sq_eq_one_of_cycleType_three_twos (t : Equiv.Perm (Fin 7))
    (ht : t.cycleType = {2, 2, 2}) : t ^ 2 = 1 := by
  have ho : orderOf t = 2 := by
    rw [← t.lcm_cycleType, ht]
    decide
  rw [← ho]
  exact pow_orderOf_eq_one t

/-- The blocks are the actual cyclic orbits of the permutation in the seven-point action. -/
theorem orbit_eq_pair_of_cycleType_three_twos (t : Equiv.Perm (Fin 7))
    (ht : t.cycleType = {2, 2, 2}) (a : Fin 7) :
    MulAction.orbit (zpowers t) a = ({a, t a} : Set (Fin 7)) := by
  have ho : orderOf t = 2 := by
    rw [← t.lcm_cycleType, ht]
    decide
  have hz (g : Equiv.Perm (Fin 7)) : g ∈ zpowers t ↔ g = 1 ∨ g = t := by
    rw [mem_zpowers_iff_mem_range_orderOf, ho]
    simp [Finset.range_add_one, eq_comm, or_comm]
  ext b
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    rcases (hz g).mp g.property with h | h
    · left
      change (g : Equiv.Perm (Fin 7)) a = a
      rw [h]
      rfl
    · right
      change (g : Equiv.Perm (Fin 7)) a = t a
      rw [h]
  · rintro (rfl | rfl)
    · exact ⟨1, rfl⟩
    · exact ⟨⟨t, mem_zpowers t⟩, rfl⟩

end AlternatingSeven.ThreeResidualLocals
