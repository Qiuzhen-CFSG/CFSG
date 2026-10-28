module

public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.Perm.List
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Theory.GroupTheory.SteinerSystem
public import Theory.Mathieu.M23.Block

open Theory.GroupTheory

namespace Sporadic.Mathieu

/-!
# The Mathieu group M₂₃ as the automorphism group of the derived Witt design

This file follows GLS, Number 3, Part I, Chapter A, Table 5.3d
(printed page 265, PDF page 282), together with the cited Aschbacher/Atlas
construction. The concrete S(4, 7, 23) block set consists of the 253
heptads obtained by taking the W24 octads through point 24 and deleting that
point.

The group is defined as the full automorphism group of this verified design.
The MulEquiv with a point stabilizer in M24 is a separate identification
node and is not assumed here. Order and simplicity are also deferred.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

private theorem m23BlockCardCheck :
    ∀ B ∈ m23Blocks, B.card = 7 := by
  intro B hB
  rw [m23Blocks] at hB
  rcases Finset.mem_image.mp hB with ⟨i, _, rfl⟩
  exact m23BlockAt_card i

private theorem m23PairwiseIntersectionCheck :
    ∀ B₁ ∈ m23Blocks, ∀ B₂ ∈ m23Blocks,
      B₁ ≠ B₂ → (B₁ ∩ B₂).card < 4 := by
  intro B₁ hB₁ B₂ hB₂ hne
  rw [m23Blocks] at hB₁ hB₂
  rcases Finset.mem_image.mp hB₁ with ⟨i, _, rfl⟩
  rcases Finset.mem_image.mp hB₂ with ⟨j, _, rfl⟩
  apply m23BlockAt_inter i j
  intro hij
  apply hne
  rw [hij]

/-- The concrete derived Witt S(4,7,23) design. -/
public noncomputable def m23WittDesign : SteinerSystem (Fin 23) 4 7 :=
  SteinerSystem.ofPairwiseIntersection m23Blocks
    m23BlockCardCheck
    m23PairwiseIntersectionCheck
    (by
      rw [m23BlocksCardinalityCheck]
      decide +kernel)

/-- The Mathieu group M₂₃, defined as the full automorphism group of W23. -/
public noncomputable def M23 : Subgroup (Equiv.Perm (Fin 23)) :=
  m23WittDesign.aut

open scoped Pointwise

/-- Membership in M₂₃ is exactly preservation of the explicit heptad set. -/
public theorem mem_M23_iff (g : Equiv.Perm (Fin 23)) :
    g ∈ M23 ↔ g • (m23Blocks : Set (Finset (Fin 23))) = m23Blocks := by
  rw [M23, SteinerSystem.mem_aut_iff]
  rfl

/-- M₂₃ is finite as a subgroup of a finite permutation group. -/
public noncomputable instance : Fintype M23 := Fintype.ofFinite _

/-- W23 has exactly 253 blocks. -/
public theorem m23Blocks_cardinality : m23Blocks.card = 253 :=
  m23BlocksCardinalityCheck

/-- Every block of W23 has size seven. -/
public theorem m23Blocks_card (B : Finset (Fin 23)) (hB : B ∈ m23Blocks) : B.card = 7 :=
  m23WittDesign.block_card B hB

/-- Every four-set lies in exactly one W23 block. -/
public theorem m23Blocks_unique_block (S : Finset (Fin 23)) (hS : S.card = 4) :
    (m23Blocks.filter (fun B => S ⊆ B)).card = 1 :=
  m23WittDesign.steiner S hS

end Sporadic.Mathieu
