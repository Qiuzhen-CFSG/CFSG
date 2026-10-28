module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.Subgroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.Group

/-!
# A concrete normal subgroup of the ATLAS local subgroup

Write `x,y` for the two outputs of `J4G1-max1W1`, now regarded as elements
of the subgroup they generate. We specify the normal closure of `(xy)^14`
inside that subgroup. This gives a fixed matrix-defined kernel and quotient
for the local order proof, without choosing an abstract group of the desired
order. The kernel count and identification of the quotient are separate
certificate obligations, not assertions of this module.

The elementary proofs here establish generation, the involution relation for
`x`, and the universal property needed to descend a representation to the
quotient. Source for the generators:
https://brauer.maths.qmul.ac.uk/Atlas/spor/J4/words/J4G1-max1W1 .
-/

@[expose] public section
namespace Janko4.Cardinality

variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)

/-- First ATLAS output as an element of the local subgroup. -/
def localX : max1Subgroup hA hB :=
  ⟨(max1Program (sourceA hA) (sourceB hB)).1,
    Subgroup.subset_closure (Set.mem_insert _ _)⟩

/-- Second ATLAS output as an element of the local subgroup. -/
def localY : max1Subgroup hA hB :=
  ⟨(max1Program (sourceA hA) (sourceB hB)).2,
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩

theorem localX_mul_self : localX hA hB * localX hA hB = 1 := by
  apply Subtype.ext
  change (max1Program (sourceA hA) (sourceB hB)).1 *
    (max1Program (sourceA hA) (sourceB hB)).1 = 1
  rw [max1Program_fst]
  calc
    _ = (sourceA hA * sourceB hB)⁻¹ *
        (sourceA hA * sourceA hA) * (sourceA hA * sourceB hB) := by group
    _ = 1 := by rw [sourceA_mul_self]; simp

/-- The lifted generators generate the actual subgroup carrier. -/
theorem localXY_generate :
    Subgroup.closure {localX hA hB, localY hA hB} = ⊤ := by
  apply Subgroup.map_injective (max1Subgroup hA hB).subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]
  rw [Set.image_pair]
  rfl

/-- The explicit word whose normal closure is used as the kernel. -/
def localKernelSeed : max1Subgroup hA hB := (localX hA hB * localY hA hB) ^ 14

/-- Normal closure in the local subgroup, not in the full J₄ carrier. -/
def localKernel : Subgroup (max1Subgroup hA hB) :=
  Subgroup.normalClosure {localKernelSeed hA hB}

instance localKernel_normal : (localKernel hA hB).Normal :=
  inferInstanceAs (Subgroup.normalClosure {localKernelSeed hA hB}).Normal

theorem localKernelSeed_mem : localKernelSeed hA hB ∈ localKernel hA hB :=
  Subgroup.subset_normalClosure (Set.mem_singleton _)

/-- A representation kills this normal closure exactly when it kills the seed. -/
theorem localKernel_le_ker_iff {G : Type*} [Group G]
    (f : max1Subgroup hA hB →* G) :
    localKernel hA hB ≤ f.ker ↔ f (localKernelSeed hA hB) = 1 := by
  constructor
  · intro h
    exact h (localKernelSeed_mem hA hB)
  · intro h
    apply Subgroup.normalClosure_le_normal
    rw [Set.singleton_subset_iff]
    exact h

/-- The specific quotient whose identification with M24 remains to be certified. -/
abbrev LocalQuotient := max1Subgroup hA hB ⧸ localKernel hA hB

/-- The word `(xy)^14` vanishes in the specified quotient by construction. -/
theorem localQuotient_xy_pow_fourteen :
    ((QuotientGroup.mk' (localKernel hA hB)) (localX hA hB) *
      (QuotientGroup.mk' (localKernel hA hB)) (localY hA hB)) ^ 14 = 1 := by
  rw [← map_mul, ← map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr (localKernelSeed_mem hA hB)

end Janko4.Cardinality
