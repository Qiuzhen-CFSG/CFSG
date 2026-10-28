module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.Actions

/-!
# Four-point orbits from residual-core images

Each chosen six-point action has a specified four-point block. The two double
transpositions displayed here generate its regular four-group. Containment
of O₂(O²(K)) in K supplies the upper orbit bound; membership of the two
permutations in its action image supplies the lower bound.

The root-image memberships are concrete model obligations, not consequences
of the size of the pair-product image. The residual and its two-core retain
their separate intrinsic definitions and embeddings throughout.

Sources: the local calculation for the retained Held case, GLS3 Table 5.3p,
and the literal ATLAS candidate words; quasithin printed pp.509–511 and 747–748.
-/

public section

open Subgroup
open scoped Pointwise
namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry

/-- The four ordered letters of the block, with zero first. -/
@[expose] def blockPoint (i : Bool) (j : Fin 2) : Fin 4 → Fin 6 :=
  if i then (if j = 0 then ![0, 2, 4, 5] else ![0, 3, 4, 5]) else ![0, 2, 3, 5]

/-- First generator of the regular four-group on the block. -/
@[expose] def rootOne (i : Bool) (j : Fin 2) : Equiv.Perm (Fin 6) :=
  Equiv.swap (blockPoint i j 0) (blockPoint i j 1) *
    Equiv.swap (blockPoint i j 2) (blockPoint i j 3)

/-- Second generator of the regular four-group on the block. -/
@[expose] def rootTwo (i : Bool) (j : Fin 2) : Equiv.Perm (Fin 6) :=
  Equiv.swap (blockPoint i j 0) (blockPoint i j 2) *
    Equiv.swap (blockPoint i j 1) (blockPoint i j 3)

private theorem block_reachable (i : Bool) (j : Fin 2) :
    ∀ y : Fin 6, y ∈ block i j → y = 0 ∨ y = rootOne i j 0 ∨
      y = rootTwo i j 0 ∨ y = (rootOne i j * rootTwo i j) 0 := by
  unfold block
  cases i <;> fin_cases j <;> decide +kernel

/-- Two explicit double transpositions give transitivity on the four-point block. -/
theorem orbit_eq_block_of_roots (i : Bool) (j : Fin 2) (P : Subgroup (Equiv.Perm (Fin 6)))
    (hP : P ≤ MulAction.stabilizer (Equiv.Perm (Fin 6)) (block i j))
    (hOne : rootOne i j ∈ P) (hTwo : rootTwo i j ∈ P) :
    MulAction.orbit P (0 : Fin 6) = block i j := by
  apply Set.Subset.antisymm
  · rintro y ⟨g, rfl⟩
    exact (MulAction.mem_stabilizer_set.mp (hP g.property) 0).mpr (zero_mem_block i j)
  · intro y hy
    rcases block_reachable i j y hy with rfl | rfl | rfl | rfl
    · exact MulAction.mem_orbit_self 0
    · exact ⟨⟨rootOne i j, hOne⟩, rfl⟩
    · exact ⟨⟨rootTwo i j, hTwo⟩, rfl⟩
    · exact ⟨⟨rootOne i j * rootTwo i j, P.mul_mem hOne hTwo⟩, rfl⟩

/-- The two-core is taken in the residual, then embedded in Held. -/
@[expose] def pairTwoCore (i : Bool) (j : Fin 2) : Subgroup Held.He :=
  Held.LocalPairs.twoCore (LocalActions.candidateTwo i j) (LocalActions.candidateOdd i j)

theorem pairTwoCore_le_pairProduct (i : Bool) (j : Fin 2) :
    pairTwoCore i j ≤ pairProduct i j :=
  (Held.LocalPairs.twoCore_le_residual _ _).trans (Held.LocalPairs.residual_le _ _)

/-- The upper orbit bound uses only containment of O₂(O²(K)) in K. -/
theorem pairTwoCore_image_le_stabilizer (i : Bool) (j : Fin 2) :
    (localImage i (pairTwoCore i j)).map (quotientAction i j) ≤
      MulAction.stabilizer (Equiv.Perm (Fin 6)) (block i j) := by
  rw [map_localImage]
  exact (map_mono (subgroupOf_mono _ (pairTwoCore_le_pairProduct i j))).trans
    (pairProduct_image_le_stabilizer i j)

/-- Only these two concrete residual-core image memberships remain for the orbit. -/
theorem pairTwoCore_orbit_of_roots (i : Bool) (j : Fin 2)
    (hOne : rootOne i j ∈ (localImage i (pairTwoCore i j)).map (quotientAction i j))
    (hTwo : rootTwo i j ∈ (localImage i (pairTwoCore i j)).map (quotientAction i j)) :
    MulAction.orbit ((localImage i (pairTwoCore i j)).map (quotientAction i j)) (0 : Fin 6) =
      block i j :=
  orbit_eq_block_of_roots i j _ (pairTwoCore_image_le_stabilizer i j) hOne hTwo

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry
