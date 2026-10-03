module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.SetTheory.Cardinal.Finite

/-!+# Four-element additive groups of binary idempotent matrices

A four-element additive subgroup of the binary two-by-two matrices consisting
of idempotents is exactly `0, I, P, I + P` for a nontrivial projection `P`.
The two complementary projections fix distinct nonzero vectors. The third
nonzero vector is fixed by neither. This gives unequal sums for the weighted
fiber profile used for homocyclic automorphisms.

The small matrix facts are exhaustive finite calculations checked by the kernel;
the passage from an arbitrary group is an injective-image cardinality argument.
Source context: the homocyclic case of the MacWilliams–Sah bound, quoted in
Janko–Thompson, Math. Z. 113 (1970), 1.1, printed p.385.
-/

namespace BinaryIdempotentPlane

open Matrix

public abbrev Mat := Matrix (Fin 2) (Fin 2) (ZMod 2)
public abbrev Vec := Fin 2 → ZMod 2

set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 8192 in
private theorem compatible_cases : ∀ P Q : Mat, P * P = P → P ≠ 0 → P ≠ 1 →
    Q * Q = Q → (P + Q) * (P + Q) = P + Q →
    Q = 0 ∨ Q = 1 ∨ Q = P ∨ Q = 1 + P := by decide

set_option maxRecDepth 8192 in
private theorem distinguished_vectors : ∀ P : Mat, P * P = P → P ≠ 0 → P ≠ 1 →
    ∃ w z : Vec, w ≠ 0 ∧ z ≠ 0 ∧
      P *ᵥ w ≠ w ∧ (1 + P) *ᵥ w ≠ w ∧
      P *ᵥ z = z ∧ (1 + P) *ᵥ z ≠ z := by decide

set_option maxRecDepth 8192 in
private theorem complement_facts : ∀ P : Mat, P ≠ 0 → P ≠ 1 →
    1 + P ≠ 0 ∧ 1 + P ≠ 1 ∧ 1 + P ≠ P ∧ 1 + (1 + P) = P := by decide

/-- The image of a faithful four-element group of binary idempotents is a
complementary pair of projections together with zero and the identity. -/
public theorem image_eq_four {G : Type*} [Group G] [Fintype G]
    (f : G →* Multiplicative Mat) (hi : Function.Injective f)
    (hc : Nat.card G = 4) (hp : ∀ g, (f g).toAdd * (f g).toAdd = (f g).toAdd) :
    ∃ P : Mat, P * P = P ∧ P ≠ 0 ∧ P ≠ 1 ∧
      Finset.univ.image (fun g => (f g).toAdd) = {0, 1, P, 1 + P} := by
  classical
  let S := Finset.univ.image (fun g => (f g).toAdd)
  have hinj : Function.Injective (fun g => (f g).toAdd) :=
    Multiplicative.toAdd.injective.comp hi
  have hcard : S.card = 4 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact hc
  have hex : ∃ P ∈ S, P ≠ 0 ∧ P ≠ 1 := by
    by_contra h
    have hsub : S ⊆ {0, 1} := by
      intro P hP
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_contra hP'
      exact h ⟨P, hP, fun h0 => hP' (Or.inl h0), fun h1 => hP' (Or.inr h1)⟩
    have hle := Finset.card_le_card hsub
    have hpair : ({0, 1} : Finset Mat).card ≤ 2 := Finset.card_insert_le _ _
    omega
  obtain ⟨P, hP, hP0, hP1⟩ := hex
  obtain ⟨p, _, hpeq⟩ := Finset.mem_image.mp hP
  have hPP : P * P = P := hpeq ▸ hp p
  refine ⟨P, hPP, hP0, hP1, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro Q hQ
    obtain ⟨q, _, hqeq⟩ := Finset.mem_image.mp hQ
    have hadd : (P + Q) * (P + Q) = P + Q := by
      have h := hp (p * q)
      simpa only [map_mul, toAdd_mul, hpeq, hqeq] using h
    simpa only [Finset.mem_insert, Finset.mem_singleton] using
      compatible_cases P Q hPP hP0 hP1 (hqeq ▸ hp q) hadd
  · have hbound : ({0, 1, P, 1 + P} : Finset Mat).card ≤ 4 := by
      calc
        _ ≤ ({1, P, 1 + P} : Finset Mat).card + 1 := Finset.card_insert_le _ _
        _ ≤ (({P, 1 + P} : Finset Mat).card + 1) + 1 :=
          Nat.add_le_add_right (Finset.card_insert_le _ _) _
        _ ≤ ((({1 + P} : Finset Mat).card + 1) + 1) + 1 :=
          Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_insert_le _ _) _) _
        _ = 4 := by simp
    exact hcard ▸ hbound

/-- The fiber weight of a binary projection: the identity contributes the
base multiplicity, a rank-one projection contributes on its fixed line. -/
public def weight (base line : ℕ) (Q : Mat) (w : Vec) : ℕ :=
  if Q = 0 then 0 else if Q = 1 then base else if Q *ᵥ w = w then line else 0

/-- The explicit cases of the fiber weight, available across module boundaries. -/
public theorem weight_eq (base line : ℕ) (Q : Mat) (w : Vec) :
    weight base line Q w =
      if Q = 0 then 0 else if Q = 1 then base else if Q *ᵥ w = w then line else 0 := by
  unfold weight
  rfl

/-- Summing over four binary idempotents gives both the base multiplicity
and the base plus one line multiplicity on nonzero vectors. -/
public theorem exists_weight_sums {G : Type*} [Group G] [Fintype G]
    (f : G →* Multiplicative Mat) (hi : Function.Injective f)
    (hc : Nat.card G = 4) (hp : ∀ g, (f g).toAdd * (f g).toAdd = (f g).toAdd)
    (base line : ℕ) :
    ∃ w z : Vec, w ≠ 0 ∧ z ≠ 0 ∧
      (∑ g, weight base line (1 + (f g).toAdd) w) = base ∧
      (∑ g, weight base line (1 + (f g).toAdd) z) = base + line := by
  classical
  obtain ⟨P, hPP, hP0, hP1, himage⟩ := image_eq_four f hi hc hp
  obtain ⟨w, z, hw, hz, hPw, hCw, hPz, hCz⟩ := distinguished_vectors P hPP hP0 hP1
  obtain ⟨hC0, hC1, hCP, hCC⟩ := complement_facts P hP0 hP1
  have hsum (v : Vec) : (∑ g, weight base line (1 + (f g).toAdd) v) =
      ∑ Q ∈ ({0, 1, P, 1 + P} : Finset Mat), weight base line (1 + Q) v := by
    rw [← himage, Finset.sum_image]
    intro a _ b _ hab
    exact hi (Multiplicative.toAdd.injective hab)
  have h11 : (1 : Mat) + 1 = 0 := by decide
  refine ⟨w, z, hw, hz, ?_, ?_⟩
  · rw [hsum]
    simp [weight, hP0, hC0, hCC, h11,
      Ne.symm hP0, Ne.symm hP1, Ne.symm hC0, Ne.symm hC1, Ne.symm hCP, hPw, hCw]
  · rw [hsum]
    simp [weight, hP0, hC0, hCC, h11,
      Ne.symm hP0, Ne.symm hP1, Ne.symm hC0, Ne.symm hC1, Ne.symm hCP, hPz, hCz]

end BinaryIdempotentPlane
