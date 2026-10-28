module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.LocalInertia
public import Theory.Character.Generalized

/-!
# Ordinary columns and their centralizer restrictions

The supplied decomposition column is an actual nonnegative sum of the
specified ordinary irreducible characters. Orthogonality recovers each of
its coefficients. Restriction to the literal Sylow centralizer and pairing
with a difference of two local characters gives an integer linear functional
on these coefficients.

These are the interfaces used in Feit VII.5.6--7 and the final argument for
VII.2.15 on printed p.299. This module does not identify the supplied
projective module as a projective cover, construct the local characters, or
assert the Thompson restriction bound.
-/

public section
noncomputable section
open scoped BigOperators Classical

namespace Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.ColumnNorms
open ModularBlock.PrimeBlockConstruction

variable {p : ℕ} {G : Type*} [Group G] [Finite G]
attribute [local instance] Fintype.ofFinite

/-- A nonnegative ordinary character with the prescribed block constituents. -/
@[expose] def ordinarySum (d : PrimeCongruenceBlockData p G)
    (c : {i // i ∈ d.block} → ℕ) : ConjClassFunction G :=
  ∑ v, (c v : ℂ) • d.chi v.val

@[simp] theorem ordinarySum_apply (d : PrimeCongruenceBlockData p G)
    (c : {i // i ∈ d.block} → ℕ) (g : G) :
    ordinarySum d c (ConjClasses.mk g) =
      ∑ v, (c v : ℂ) * d.chi v.val (ConjClasses.mk g) := by
  simp [ordinarySum]

/-- The actual ordinary scalar product recovers each supplied coefficient. -/
theorem ordinarySum_inner (d : PrimeCongruenceBlockData p G)
    (c : {i // i ∈ d.block} → ℕ) (v : {i // i ∈ d.block}) :
    classFunctionInner (ordinarySum d c) (d.chi v.val) = (c v : ℂ) := by
  rw [ordinarySum, classFunctionInner_sum_left]
  simp only [completeFamily_orthonormal d.complete, smul_eq_mul]
  have heq (w : {i // i ∈ d.block}) : w.val = v.val ↔ w = v := Subtype.ext_iff.symm
  simp_rw [heq]
  simp

omit [Finite G] in
private theorem character_nsmul {χ : ClassFunction G} (hχ : IsCharacter χ) (n : ℕ) :
    IsCharacter (n • χ) := by
  induction n with
  | zero => simpa using (isCharacter_zero (G := G))
  | succ n ih => simpa only [succ_nsmul] using ih.add hχ

/-- The sums used as subcharacters in the restriction argument are characters. -/
theorem ordinarySum_isCharacter (d : PrimeCongruenceBlockData p G)
    (c : {i // i ∈ d.block} → ℕ) :
    IsCharacter (fun g => ordinarySum d c (ConjClasses.mk g)) := by
  have hterm (v : {i // i ∈ d.block}) :
      IsCharacter (fun g => (c v : ℂ) * d.chi v.val (ConjClasses.mk g)) := by
    obtain ⟨k, ρ, hρ⟩ := (d.complete.1 v.val).1
    have hχ : IsCharacter (fun g => d.chi v.val (ConjClasses.mk g)) :=
      ⟨k, ρ, by funext g; rw [hρ]; rfl⟩
    convert character_nsmul hχ (c v) using 1
    ext g
    simp
  have hsum (s : Finset {i // i ∈ d.block}) :
      IsCharacter (∑ v ∈ s, fun g => (c v : ℂ) * d.chi v.val (ConjClasses.mk g)) := by
    induction s using Finset.induction_on with
    | empty => simpa using (isCharacter_zero (G := G))
    | @insert v s hv ih => rw [Finset.sum_insert hv]; exact (hterm v).add ih
  convert hsum Finset.univ using 1
  ext g
  simp

/-- Taking a coefficientwise smaller sum really gives an ordinary subcharacter. -/
theorem ordinarySum_subcharacter (d : PrimeCongruenceBlockData p G)
    (f c : {i // i ∈ d.block} → ℕ) (hc : ∀ v, c v ≤ f v) :
    ∃ ψ : ClassFunction G, IsCharacter ψ ∧
      (fun g => ordinarySum d f (ConjClasses.mk g)) =
        (fun g => ordinarySum d c (ConjClasses.mk g)) + ψ := by
  refine ⟨fun g => ordinarySum d (fun v => f v - c v) (ConjClasses.mk g),
    ordinarySum_isCharacter d _, ?_⟩
  ext g
  simp only [Pi.add_apply, ordinarySum_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  rw [← add_mul, ← Nat.cast_add, Nat.add_sub_of_le (hc v)]

/-- The literal restriction of an ordinary block row. -/
@[expose] def rowRestriction (d : PrimeCongruenceBlockData p G)
    (H : Subgroup G) (v : {i // i ∈ d.block}) : ClassFunction H :=
  fun x => d.chi v.val (ConjClasses.mk (x : G))

theorem rowRestriction_isCharacter (d : PrimeCongruenceBlockData p G)
    (H : Subgroup G) (v : {i // i ∈ d.block}) :
    IsCharacter (rowRestriction d H v) := by
  obtain ⟨k, ρ, hρ⟩ := (d.complete.1 v.val).1
  exact ⟨k, ρ.comp H.subtype,
    by funext x; change d.chi v.val (ConjClasses.mk (x : G)) = _; rw [hρ]; rfl⟩

/-- Two actual local irreducible characters with the same regular restriction.
The source producer must construct these in the local principal block. -/
structure LocalCharacterPair (p : ℕ) (P : Sylow p G) where
  first : ClassFunction (Subgroup.centralizer (P : Set G))
  second : ClassFunction (Subgroup.centralizer (P : Set G))
  first_irreducible : IsIrreducibleCharacter first
  second_irreducible : IsIrreducibleCharacter second
  first_principal : first = 1
  different : first ≠ second
  regular_eq : ∀ x : Subgroup.centralizer (P : Set G),
    ¬ p ∣ orderOf (x : G) → first x = second x

namespace LocalCharacterPair
variable {P : Sylow p G} (q : LocalCharacterPair p P)

/-- The local generalized character used in Thompson's restriction argument. -/
@[expose] def difference : ClassFunction (Subgroup.centralizer (P : Set G)) :=
  q.first - q.second

/-- Feit VII.5.6's assertion for a given ordinary projective character.
This is a source obligation, not a field of decomposition data. -/
@[expose] def ThompsonBound (Φ : ClassFunction G) : Prop :=
  ∀ η ψ : ClassFunction G, IsCharacter η → IsCharacter ψ → Φ = η + ψ →
    ∃ z : ℤ,
      @scalarProduct _ (Fintype.ofFinite (Subgroup.centralizer (P : Set G)))
        (fun x => η (x : G)) q.difference = (z : ℂ) ∧ -1 ≤ z ∧ z ≤ 1

omit [Finite G] in
theorem difference_isGeneralized : IsGeneralizedCharacter q.difference := by
  obtain ⟨k, ρ, _, hρ⟩ := q.first_irreducible
  obtain ⟨l, σ, _, hσ⟩ := q.second_irreducible
  exact ⟨q.first, q.second, ⟨k, ρ, hρ⟩, ⟨l, σ, hσ⟩, rfl⟩

/-- The integral difference of actual local constituent multiplicities. -/
def rowDifference (d : PrimeCongruenceBlockData p G) (v : {i // i ∈ d.block}) : ℤ :=
  ((rowRestriction_isCharacter d _ v).scalarProduct_generalized_int
    q.difference_isGeneralized).choose

theorem rowDifference_cast (d : PrimeCongruenceBlockData p G)
    (v : {i // i ∈ d.block}) :
    (q.rowDifference d v : ℂ) =
      @scalarProduct _ (Fintype.ofFinite (Subgroup.centralizer (P : Set G)))
      (rowRestriction d _ v) q.difference :=
  ((rowRestriction_isCharacter d _ v).scalarProduct_generalized_int
    q.difference_isGeneralized).choose_spec.symm

/-- The integer sum is the scalar product of the literal restricted character. -/
theorem ordinarySum_pairing (d : PrimeCongruenceBlockData p G)
    (c : {i // i ∈ d.block} → ℕ) :
    @scalarProduct _ (Fintype.ofFinite (Subgroup.centralizer (P : Set G)))
      (fun x => ordinarySum d c (ConjClasses.mk (x : G))) q.difference =
        ((∑ v, (c v : ℤ) * q.rowDifference d v : ℤ) : ℂ) := by
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, q.rowDifference_cast,
    scalarProduct, ordinarySum_apply, rowRestriction]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  simp_rw [mul_assoc, ← Finset.mul_sum]
  ring

/-- Vanishing of the ordinary projective character on singular elements kills
the local difference pairing. The vanishing assertion is an upstream theorem. -/
theorem ordinarySum_pairing_eq_zero (d : PrimeCongruenceBlockData p G)
    (c : {i // i ∈ d.block} → ℕ)
    (hsingular : ∀ g : G, p ∣ orderOf g → ordinarySum d c (ConjClasses.mk g) = 0) :
    ∑ v, (c v : ℤ) * q.rowDifference d v = 0 := by
  let : Fintype (Subgroup.centralizer (P : Set G)) := Fintype.ofFinite _
  apply Int.cast_injective (α := ℂ)
  rw [Int.cast_zero, ← q.ordinarySum_pairing]
  unfold scalarProduct
  suffices (∑ x : Subgroup.centralizer (P : Set G),
      ordinarySum d c (ConjClasses.mk (x : G)) * star (q.difference x)) = 0 by
    rw [this, mul_zero]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : p ∣ orderOf (x : G)
  · rw [hsingular x hx, zero_mul]
  · simp [difference, q.regular_eq x hx]

end LocalCharacterPair
end Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.ColumnNorms
