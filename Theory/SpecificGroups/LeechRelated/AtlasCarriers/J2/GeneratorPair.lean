module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# The standard generating pair of the degree-100 J₂ carrier

The two defining permutations generate the actual carrier, so homomorphisms
are determined by their values on this pair. We verify the word equations
a² = b³ = (ab)⁷ = (abab⁻¹)¹² = 1 and the inequality (abab⁻¹)⁴ ≠ 1.
Every automorphism preserves these tests. They are necessary word tests,
not a claimed presentation or a classification of their solutions.

For efficient kernel checking, lookup-table permutations are proved equal
to the original cycle products. The tables are calculated from the cycles
in the parent module, including its inverse/right-action convention.
Both their inverse laws and the comparisons are checked by Lean's kernel.

Source: R. A. Wilson et al., ATLAS of Finite Group Representations,
`J2G1-p100B0`; the original data and attribution are retained in the adjacent
`source/` directory. The outer-automorphism application is GLS3, Table 5.3g.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.GeneratorPair

def tableAValues : Fin 100 → Fin 100 :=
  ![83, 19, 47, 55, 81, 66, 54, 40, 34, 39, 77, 99, 48, 36, 93, 75, 18, 43, 16, 1,
    33, 84, 91, 56, 74, 27, 63, 25, 89, 96, 37, 67, 68, 20, 8, 52, 13, 30, 60, 9,
    7, 72, 90, 17, 85, 80, 88, 2, 12, 92, 95, 71, 35, 73, 6, 3, 23, 98, 94, 62,
    38, 82, 59, 26, 69, 87, 5, 31, 32, 64, 86, 51, 41, 53, 24, 15, 97, 10, 79, 78,
    45, 4, 61, 0, 21, 44, 70, 65, 46, 28, 42, 22, 49, 14, 58, 50, 29, 76, 57, 11]
def tableBValues : Fin 100 → Fin 100 :=
  ![21, 10, 86, 77, 17, 23, 6, 59, 1, 46, 8, 30, 18, 51, 24, 31, 32, 50, 63, 57,
    66, 79, 3, 36, 97, 98, 7, 34, 54, 44, 64, 72, 38, 81, 56, 35, 5, 93, 16, 90,
    40, 43, 39, 67, 68, 88, 61, 89, 76, 87, 4, 60, 2, 55, 70, 94, 27, 96, 37, 26,
    13, 9, 71, 12, 11, 49, 95, 41, 29, 74, 28, 73, 15, 62, 80, 47, 91, 22, 82, 0,
    69, 85, 99, 83, 45, 33, 52, 65, 84, 75, 42, 48, 25, 58, 53, 20, 19, 14, 92, 78]
def tableBInvValues : Fin 100 → Fin 100 :=
  ![79, 8, 52, 22, 50, 36, 6, 26, 10, 61, 1, 64, 63, 60, 97, 72, 38, 4, 12, 96,
    95, 0, 77, 5, 14, 92, 59, 56, 70, 68, 11, 15, 16, 85, 27, 35, 23, 58, 32, 42,
    40, 67, 90, 41, 29, 84, 9, 75, 91, 65, 17, 13, 86, 94, 28, 53, 34, 19, 93, 7,
    51, 46, 73, 18, 30, 87, 20, 43, 44, 80, 54, 62, 31, 71, 69, 89, 48, 3, 99, 21,
    74, 33, 78, 83, 88, 81, 2, 49, 45, 47, 39, 76, 98, 37, 55, 66, 57, 24, 25, 82]
set_option maxRecDepth 20000 in
def tableA : Equiv.Perm (Fin 100) where
  toFun := tableAValues
  invFun := tableAValues
  left_inv := by decide +kernel
  right_inv := by decide +kernel
set_option maxRecDepth 20000 in
def tableB : Equiv.Perm (Fin 100) where
  toFun := tableBValues
  invFun := tableBInvValues
  left_inv := by decide +kernel
  right_inv := by decide +kernel
set_option maxRecDepth 20000 in
theorem generatorA_eq_table : generatorA = tableA := by
  apply Equiv.ext
  decide +kernel
set_option maxRecDepth 20000 in
theorem generatorB_eq_table : generatorB = tableB := by
  apply Equiv.ext
  decide +kernel

/-- The first published generator as an element of the actual carrier. -/
def a : Carrier := ⟨generatorA, Subgroup.subset_closure (by simp)⟩

/-- The second published generator as an element of the actual carrier. -/
def b : Carrier := ⟨generatorB, Subgroup.subset_closure (by simp)⟩

/-- These elements generate the whole carrier. -/
theorem closure_pair_eq_top : Subgroup.closure ({a, b} : Set Carrier) = ⊤ := by
  have hs : ({a, b} : Set Carrier) =
      inclusion ⁻¹' ({generatorA, generatorB} : Set (Equiv.Perm (Fin 100))) := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro (rfl | rfl) <;> simp [inclusion, a, b]
    · rintro (ha | hb)
      · exact Or.inl (inclusion_injective ha)
      · exact Or.inr (inclusion_injective hb)
  rw [hs]
  exact Subgroup.closure_closure_coe_preimage

set_option maxRecDepth 20000 in
/-- The first standard generator has square one. -/
theorem a_pow_two : a ^ 2 = 1 := by
  apply Subtype.ext
  change generatorA ^ 2 = 1
  rw [generatorA_eq_table]
  decide +kernel

set_option maxRecDepth 20000 in
/-- The second standard generator has cube one. -/
theorem b_pow_three : b ^ 3 = 1 := by
  apply Subtype.ext
  change generatorB ^ 3 = 1
  rw [generatorB_eq_table]
  decide +kernel

set_option maxRecDepth 20000 in
/-- The product of the standard generators has seventh power one. -/
theorem ab_pow_seven : (a * b) ^ 7 = 1 := by
  apply Subtype.ext
  change (generatorA * generatorB) ^ 7 = 1
  rw [generatorA_eq_table, generatorB_eq_table]
  decide +kernel

set_option maxRecDepth 20000 in
/-- The commutator word used in the pair test has twelfth power one. -/
theorem comm_word_pow_twelve : (a * b * a * b⁻¹) ^ 12 = 1 := by
  apply Subtype.ext
  change (generatorA * generatorB * generatorA * generatorB⁻¹) ^ 12 = 1
  rw [generatorA_eq_table, generatorB_eq_table]
  decide +kernel

set_option maxRecDepth 20000 in
/-- The commutator word does not have fourth power one. -/
theorem comm_word_pow_four_ne : (a * b * a * b⁻¹) ^ 4 ≠ 1 := by
  intro h
  have hh := congrArg Subtype.val h
  change (generatorA * generatorB * generatorA * generatorB⁻¹) ^ 4 = 1 at hh
  rw [generatorA_eq_table, generatorB_eq_table] at hh
  exact (by decide +kernel : (tableA * tableB * tableA * tableB⁻¹) ^ 4 ≠ 1) hh

/-- The finite word tests used for the J₂ generating pair. -/
def PairProfile (x y : Carrier) : Prop :=
  x ^ 2 = 1 ∧ y ^ 3 = 1 ∧ (x * y) ^ 7 = 1 ∧
  (x * y * x * y⁻¹) ^ 12 = 1 ∧ (x * y * x * y⁻¹) ^ 4 ≠ 1

theorem PairProfile.map {x y : Carrier} (h : PairProfile x y) (f : MulAut Carrier) :
    PairProfile (f x) (f y) := by
  rcases h with ⟨hx, hy, hxy, h12, h4⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [map_pow, map_one] using congrArg f hx
  · simpa only [map_pow, map_one] using congrArg f hy
  · simpa only [map_pow, map_mul, map_one] using congrArg f hxy
  · simpa only [map_pow, map_mul, map_inv, map_one] using congrArg f h12
  · intro heq
    apply h4
    apply f.injective
    simpa only [map_pow, map_mul, map_inv, map_one] using heq

/-- The actual standard generators pass the finite word tests. -/
theorem pair_profile : PairProfile a b :=
  ⟨a_pow_two, b_pow_three, ab_pow_seven, comm_word_pow_twelve, comm_word_pow_four_ne⟩

end Sporadic.LeechRelated.J2.GeneratorPair
