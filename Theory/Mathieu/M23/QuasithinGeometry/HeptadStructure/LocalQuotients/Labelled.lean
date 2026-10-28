module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.Algebra.Group.Action.Pointwise.Finset

/-!
# The labelled 3+2+2 partition of a heptad

These permutation subgroups describe the local intersections without making
any assumptions about the construction of M23. The even partition stabilizer
preserves each of the three parts individually; the even four-point fixer
fixes the last four labels pointwise.

Source: Aschbacher--Smith, Lemma 5.2.20(2--3), printed pp. 656--657.
-/

@[expose] public section
namespace Sporadic.Mathieu.M23Geometry
open scoped Pointwise

def heptadTripleLabels : Finset (Fin 7) := {0, 1, 2}
def heptadMiddleLabels : Finset (Fin 7) := {3, 4}
def heptadPairLabels : Finset (Fin 7) := {5, 6}
def heptadFourLabels : Finset (Fin 7) := {3, 4, 5, 6}

/-- The three parts are stabilized individually, not permuted. -/
def heptadPartitionStabilizer : Subgroup (Equiv.Perm (Fin 7)) :=
  MulAction.stabilizer _ heptadTripleLabels ⊓
    (MulAction.stabilizer _ heptadMiddleLabels ⊓
      MulAction.stabilizer _ heptadPairLabels)

def heptadEvenPartition : Subgroup (Equiv.Perm (Fin 7)) :=
  alternatingGroup (Fin 7) ⊓ heptadPartitionStabilizer

def heptadEvenFourFixer : Subgroup (Equiv.Perm (Fin 7)) :=
  alternatingGroup (Fin 7) ⊓
    fixingSubgroup (Equiv.Perm (Fin 7)) (heptadFourLabels : Set (Fin 7))

/-- The source three-cycle on the first three labels. -/
def heptadTripleCycle : alternatingGroup (Fin 7) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by
    simp [Equiv.Perm.mem_alternatingGroup]⟩

@[simp] theorem heptadTripleCycle_coe :
    (heptadTripleCycle : Equiv.Perm (Fin 7)) = Equiv.swap 0 1 * Equiv.swap 1 2 := rfl

theorem mem_heptadPartitionStabilizer (p : Equiv.Perm (Fin 7)) :
    p ∈ heptadPartitionStabilizer ↔
      p • heptadTripleLabels = heptadTripleLabels ∧
      p • heptadMiddleLabels = heptadMiddleLabels ∧
      p • heptadPairLabels = heptadPairLabels := by
  simp only [heptadPartitionStabilizer, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]

theorem mem_heptadEvenFourFixer (p : Equiv.Perm (Fin 7)) :
    p ∈ heptadEvenFourFixer ↔ p ∈ alternatingGroup (Fin 7) ∧
      ∀ i ∈ heptadFourLabels, p i = i := by
  simp only [heptadEvenFourFixer, Subgroup.mem_inf, mem_fixingSubgroup_iff,
    Finset.mem_coe, Equiv.Perm.smul_def]

end Sporadic.Mathieu.M23Geometry
