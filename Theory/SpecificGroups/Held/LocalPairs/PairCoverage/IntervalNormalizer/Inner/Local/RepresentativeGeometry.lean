module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.Orbits
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.CoreKernel
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.ResidualRoots
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.Transport

/-!
# Concrete six-point geometry for Held representatives

The four actual actions and their complete pair-product images are certified
in Actions. Two double-transposition images in O₂(O²(K)), together with
containment of the native action kernel in K, give the requested geometric
witness. CoreKernel identifies the word core with the intrinsic local two-core
and proves its commutator equality and native kernel containment. ResidualRoots
places both double transpositions in the image of the actual residual core.
Thus all four literal representatives have unconditional geometric witnesses,
using the native action for the first candidate and its outer S₆ twist for
the second. All normality is relative to the corresponding local subgroup;
no group identification is inferred from an order comparison.

Sources: GLS3 Table 5.3p; the unchanged ATLAS max3/max4 and degree-2058 data;
Aschbacher–Smith, quasithin printed pp.509–511 and 747–748.
-/

public section

open Subgroup
open scoped Pointwise
namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry

/-- The normality used for this inclusion is relative to the literal local group. -/
theorem commutator_le_localTwoCore (i : Bool) (j : Fin 2) :
    ⁅localTwoCore i, LocalActions.candidateOdd i j⁆ ≤ localTwoCore i := by
  rw [commutator_comm]
  exact le_normalizer_iff_commutator_le_right.mp
    ((LocalActions.candidateOdd_le_localOvergroup i j).trans
      (localOvergroup_le_normalizer_localTwoCore i))

/-- Assemble the exact geometric witnesses from native kernel containment and
the two specified residual-core images. Each premise is a concrete Held
subgroup calculation and must be certified before obtaining the unconditional
representative theorem. -/
theorem geometry_of_kernel_and_roots (i : Bool) (j : Fin 2)
    (hker : (SixPoint.action i).ker ≤ (pairProduct i j).subgroupOf (localOvergroup i))
    (hOne : rootOne i j ∈ ((pairTwoCore i j).subgroupOf (localOvergroup i)).map (action i j))
    (hTwo : rootTwo i j ∈ ((pairTwoCore i j).subgroupOf (localOvergroup i)).map (action i j)) :
    ∃ f : LocalQuotient i →* Equiv.Perm (Fin 6), ∃ B : Set (Fin 6), ∃ x : Fin 6,
      B.ncard = 4 ∧
      (MulAction.stabilizer (Equiv.Perm (Fin 6)) B).comap f =
        localImage i (LocalActions.candidateOdd i j ⊔ LocalActions.candidateTwo i j) ∧
      MulAction.orbit ((localImage i
        (Held.LocalPairs.twoCore (LocalActions.candidateTwo i j)
          (LocalActions.candidateOdd i j))).map f) x = B := by
  refine ⟨quotientAction i j, block i j, 0, block_ncard i j,
    stabilizer_preimage_of_kernel i j hker, ?_⟩
  exact pairTwoCore_orbit_of_roots i j (by rwa [map_localImage]) (by rwa [map_localImage])

/-- Each literal odd candidate generates the entire intrinsic local two-core
by commutators. -/
theorem localTwoCore_commutator (i : Bool) (j : Fin 2) :
    ⁅localTwoCore i, LocalActions.candidateOdd i j⁆ = localTwoCore i :=
  CoreKernel.localTwoCore_commutator i j

/-- The full stabilizer preimage is the image of the actual pair product in
M/O₂(M), including the native action kernel. -/
theorem stabilizer_preimage (i : Bool) (j : Fin 2) :
    (MulAction.stabilizer (Equiv.Perm (Fin 6)) (block i j)).comap (quotientAction i j) =
      localImage i (pairProduct i j) :=
  stabilizer_preimage_of_kernel i j (CoreKernel.nativeKernel_le_pairProduct i j)

/-- The image of O₂(O²(K)) has the specified four-point orbit. -/
theorem pairTwoCore_orbit (i : Bool) (j : Fin 2) :
    MulAction.orbit ((localImage i (pairTwoCore i j)).map (quotientAction i j)) (0 : Fin 6) =
      block i j := by
  apply pairTwoCore_orbit_of_roots
  · rw [map_localImage]
    exact rootOne_mem_pairTwoCore_image i j
  · rw [map_localImage]
    exact rootTwo_mem_pairTwoCore_image i j

/-- Exact geometric witnesses for every published literal Held pair, with no
additional model premises. The witnesses are the marked quotient action,
its four-point block, and the letter zero. -/
theorem geometry (i : Bool) (j : Fin 2) :
    ∃ f : LocalQuotient i →* Equiv.Perm (Fin 6), ∃ B : Set (Fin 6), ∃ x : Fin 6,
      B.ncard = 4 ∧
      (MulAction.stabilizer (Equiv.Perm (Fin 6)) B).comap f =
        localImage i (LocalActions.candidateOdd i j ⊔ LocalActions.candidateTwo i j) ∧
      MulAction.orbit ((localImage i
        (Held.LocalPairs.twoCore (LocalActions.candidateTwo i j)
          (LocalActions.candidateOdd i j))).map f) x = B :=
  ⟨quotientAction i j, block i j, 0, block_ncard i j,
    stabilizer_preimage i j, pairTwoCore_orbit i j⟩

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry
