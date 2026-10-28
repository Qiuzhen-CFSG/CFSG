module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Counting binary partial spreads

Pairwise disjoint n-dimensional subspaces contribute disjoint sets of
2^n - 1 nonzero vectors. The resulting injection gives the counting bound;
equality makes it surjective and hence gives a partition of the nonzero vectors.

This is the finite geometry used in Aschbacher–Smith, *The Classification of
Quasithin Groups*, B.7.2, printed p. 119 (PDF p. 130).
-/

@[expose] public section

namespace Submodule
variable {V ι : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem card_nonzero (W : Type*) [Zero W] [Finite W] :
    Nat.card {w : W // w ≠ 0} = Nat.card W - 1 := by
  classical
  let := Fintype.ofFinite W
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_unique]

private def nonzeroPacking (U : ι → Submodule (ZMod 2) V) :
    (Σ i, {v : U i // v ≠ 0}) → {v : V // v ≠ 0} :=
  fun ⟨_i, v⟩ => ⟨v.val.val, fun h => v.property (Subtype.ext h)⟩

private theorem nonzeroPacking_injective (U : ι → Submodule (ZMod 2) V)
    (hdis : Pairwise (fun i j => Disjoint (U i) (U j))) :
    Function.Injective (nonzeroPacking U) := by
  rintro ⟨i, v⟩ ⟨j, w⟩ h
  have he : (v.val : V) = w.val := congrArg Subtype.val h
  have hij : i = j := by
    by_contra hn
    have hm : (v.val : V) ∈ U i ⊓ U j := ⟨v.val.property, he ▸ w.val.property⟩
    rw [(hdis hn).eq_bot] at hm
    exact v.property (Subtype.ext hm)
  subst j
  congr 1
  exact Subtype.ext (Subtype.ext he)

private theorem card_nonzeroPacking [Finite ι] [FiniteDimensional (ZMod 2) V]
    (U : ι → Submodule (ZMod 2) V) {n : ℕ}
    (hdim : ∀ i, Module.finrank (ZMod 2) (U i) = n) :
    Nat.card (Σ i, {v : U i // v ≠ 0}) = Nat.card ι * (2 ^ n - 1) := by
  classical
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let := Fintype.ofFinite ι
  have hc (i : ι) : Nat.card {v : U i // v ≠ 0} = 2 ^ n - 1 := by
    rw [card_nonzero, Module.natCard_eq_pow_finrank (K := ZMod 2), hdim i]
    simp
  rw [Nat.card_sigma]
  simp only [hc, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

/-- Counting nonzero vectors bounds the number of disjoint equal-dimensional binary subspaces. -/
theorem binary_partialSpread_bound [Finite ι] [FiniteDimensional (ZMod 2) V]
    (U : ι → Submodule (ZMod 2) V) {n : ℕ}
    (hdis : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hdim : ∀ i, Module.finrank (ZMod 2) (U i) = n) :
    Nat.card ι * (2 ^ n - 1) ≤ 2 ^ Module.finrank (ZMod 2) V - 1 := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  have h := Nat.card_le_card_of_injective (nonzeroPacking U) (nonzeroPacking_injective U hdis)
  rw [card_nonzeroPacking U hdim, card_nonzero, Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)] at h
  simpa using h

/-- Equality in the disjoint-subspace bound forces coverage of every nonzero vector. -/
theorem binary_partialSpread_cover [Finite ι] [FiniteDimensional (ZMod 2) V]
    (U : ι → Submodule (ZMod 2) V) {n : ℕ}
    (hdis : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hdim : ∀ i, Module.finrank (ZMod 2) (U i) = n)
    (hcard : Nat.card ι * (2 ^ n - 1) = 2 ^ Module.finrank (ZMod 2) V - 1) :
    ∀ v : V, v ≠ 0 → ∃ i, v ∈ U i := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  have he : Nat.card {v : V // v ≠ 0} ≤ Nat.card (Σ i, {v : U i // v ≠ 0}) := by
    rw [card_nonzeroPacking U hdim, hcard, card_nonzero, Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)]
    simp
  have hs := ((nonzeroPacking_injective U hdis).bijective_of_nat_card_le he).2
  intro v hv
  obtain ⟨⟨i, w⟩, hw⟩ := hs ⟨v, hv⟩
  have hw' : (w.val : V) = v := congrArg Subtype.val hw
  exact ⟨i, hw' ▸ w.val.property⟩
end Submodule
