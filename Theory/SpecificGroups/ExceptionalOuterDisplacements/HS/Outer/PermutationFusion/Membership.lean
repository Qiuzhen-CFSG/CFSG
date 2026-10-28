module

public import Theory.SpecificGroups.ExceptionalOuterDisplacements.HS.Outer.Representatives
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.IndexNormal

/-!
Adapted from `CFSG/Quasithin/Chapter16/Section01To02/OtherPreliminaries/
JankoTwoHigmanSims/HSOuter/` for the intrinsic HS displacement theorem.
The original modules and their public interfaces are preserved. Original
ATLAS HSG1-p100B0 attribution is retained in `LICENSES/ATLAS.txt`.

# The two representatives are outer elements of the HS normalizer

The checked HS order and graph-automorphism bound give relative index at most
 two for HS in the graph group. Thus HS is normal in that group, which equals
its permutation normalizer. Both specified involutions preserve the graph and
are odd, whereas the defining HS generators are even. Consequently both lie
in the normalizer outside HS, and the normalizer has order 88,704,000.

Source: Aschbacher–Smith 16.1.5(10), printed p.1172; GLS3 Table 5.3m,
classes 2C and 2D. The graph and permutation calculations use only kernel
reduction. No conjugacy or centralizer-structure assertion is assumed here.
-/

@[expose] public section
namespace Theory.SpecificGroups.ExceptionalOuterDisplacements.HS.Outer
open Subgroup Sporadic.LeechRelated.HS
open Sporadic.LeechRelated.HS.OrderCertificate Sporadic.LeechRelated.HS.NormalizerIndex
set_option maxRecDepth 20000

/-- The normalizer of the exact degree-100 carrier, in the same permutation group. -/
abbrev PermutationNormalizer : Subgroup (Equiv.Perm (Fin 100)) :=
  normalizer (generated : Set (Equiv.Perm (Fin 100)))

private theorem graph_relative_index :
    generated.relIndex graphGroup = 1 ∨ generated.relIndex graphGroup = 2 := by
  have he := relIndex_mul_relIndex (⊥ : Subgroup (Equiv.Perm (Fin 100)))
    generated graphGroup bot_le generated_le_graphGroup
  simp only [relIndex_bot_left] at he
  change Nat.card Carrier * generated.relIndex graphGroup = Nat.card graphGroup at he
  rw [card_carrier] at he
  have hp : 0 < Nat.card graphGroup := Nat.card_pos
  have hb := graphGroup_card_le
  omega

/-- Every graph automorphism normalizes HS; normality is relative to the graph group. -/
theorem graphGroup_le_permutationNormalizer : graphGroup ≤ PermutationNormalizer := by
  apply (normal_subgroupOf_iff_le_normalizer generated_le_graphGroup).mp
  rcases graph_relative_index with h | h
  · exact normal_of_index_eq_one h
  · exact normal_of_index_eq_two h

/-- The full graph group is the normalizer of the defining HS carrier. -/
theorem permutationNormalizer_eq_graphGroup : PermutationNormalizer = graphGroup :=
  le_antisymm normalizer_le_graphGroup graphGroup_le_permutationNormalizer

private theorem generatorA_even : Equiv.Perm.sign generatorA = 1 := by
  rw [← a_eq_generator]
  decide +kernel

private theorem generatorB_even : Equiv.Perm.sign generatorB = 1 := by
  rw [← b_eq_generator]
  decide +kernel

/-- All permutations in the exact HS carrier are even. -/
theorem generated_le_sign_ker : generated ≤ Equiv.Perm.sign.ker := by
  apply (closure_le _).mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact generatorA_even
  · exact (Set.mem_singleton_iff.mp hx) ▸ generatorB_even

theorem elementaryPermutation_sign : Equiv.Perm.sign elementaryPermutation = -1 := by
  decide +kernel

theorem symmetricPermutation_sign : Equiv.Perm.sign symmetricPermutation = -1 := by
  decide +kernel

theorem elementaryPermutation_not_mem_generated : elementaryPermutation ∉ generated := by
  intro h
  have hs : Equiv.Perm.sign elementaryPermutation = 1 := generated_le_sign_ker h
  rw [elementaryPermutation_sign] at hs
  exact (by decide : (-1 : ℤˣ) ≠ 1) hs

theorem symmetricPermutation_not_mem_generated : symmetricPermutation ∉ generated := by
  intro h
  have hs : Equiv.Perm.sign symmetricPermutation = 1 := generated_le_sign_ker h
  rw [symmetricPermutation_sign] at hs
  exact (by decide : (-1 : ℤˣ) ≠ 1) hs

private theorem elementaryPermutation_mem_graphGroup : elementaryPermutation ∈ graphGroup := by
  rw [mem_graphGroup_iff]
  apply allFin
  decide +kernel

private theorem symmetricPermutation_mem_graphGroup : symmetricPermutation ∈ graphGroup := by
  rw [mem_graphGroup_iff]
  apply allFin
  decide +kernel

theorem elementaryPermutation_mem_normalizer : elementaryPermutation ∈ PermutationNormalizer :=
  graphGroup_le_permutationNormalizer elementaryPermutation_mem_graphGroup

theorem symmetricPermutation_mem_normalizer : symmetricPermutation ∈ PermutationNormalizer :=
  graphGroup_le_permutationNormalizer symmetricPermutation_mem_graphGroup

/-- The two specified permutations, now as elements of the actual normalizer. -/
def elementaryNormalizer : PermutationNormalizer :=
  ⟨elementaryPermutation, elementaryPermutation_mem_normalizer⟩

def symmetricNormalizer : PermutationNormalizer :=
  ⟨symmetricPermutation, symmetricPermutation_mem_normalizer⟩

/-- The carrier has relative index exactly two, not merely an index dividing two. -/
theorem permutationNormalizer_relative_index : generated.relIndex PermutationNormalizer = 2 := by
  rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp normalizer_relIndex_dvd_two with h | h
  · exact (elementaryPermutation_not_mem_generated
      (relIndex_eq_one.mp h elementaryPermutation_mem_normalizer)).elim
  · exact h

/-- The exact order needed to certify a subgroup of order 1024 as Sylow. -/
theorem permutationNormalizer_card : Nat.card PermutationNormalizer = 88704000 := by
  have he := relIndex_mul_relIndex (⊥ : Subgroup (Equiv.Perm (Fin 100)))
    generated PermutationNormalizer bot_le generated.le_normalizer
  simp only [relIndex_bot_left] at he
  change Nat.card Carrier * generated.relIndex PermutationNormalizer =
    Nat.card PermutationNormalizer at he
  rw [card_carrier, permutationNormalizer_relative_index] at he
  exact he.symm

/-- Within the normalizer, every element outside HS is odd. -/
theorem sign_of_normalizer_not_mem (n : PermutationNormalizer) (hn : n.val ∉ generated) :
    Equiv.Perm.sign n.val = -1 := by
  have hm : n * elementaryNormalizer ∈ generated.subgroupOf PermutationNormalizer :=
    ((generated.subgroupOf PermutationNormalizer).mul_mem_iff_of_index_two
      permutationNormalizer_relative_index).mpr
      (iff_of_false hn elementaryPermutation_not_mem_generated)
  have hs : Equiv.Perm.sign (n.val * elementaryPermutation) = 1 := generated_le_sign_ker hm
  rw [map_mul, elementaryPermutation_sign] at hs
  simpa using eq_inv_iff_mul_eq_one.mpr hs

end Theory.SpecificGroups.ExceptionalOuterDisplacements.HS.Outer
