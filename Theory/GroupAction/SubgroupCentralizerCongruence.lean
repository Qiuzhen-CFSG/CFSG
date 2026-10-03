module

public import Theory.GroupAction.SubgroupConjugation
public import Theory.GroupAction.Lemmas
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Index

/-!
# The centralizer congruence for a normalizing prime-power subgroup

If a finite p-group A normalizes B, its conjugation orbits on B give
|B| ≡ |C_B(A)| modulo p. The centralizer is expressed in the ambient group,
so the result applies directly to supplied subgroup inclusions.
-/

open Subgroup

/-- Count the conjugation orbits of a normalizing p-subgroup. -/
public theorem Subgroup.card_modEq_card_inf_centralizer
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (A B : Subgroup G) (hA : IsPGroup p A) (hAB : A ≤ normalizer (B : Set G)) :
    Nat.card B ≡ Nat.card (B ⊓ centralizer (A : Set G) : Subgroup G) [MOD p] := by
  let : Normalizes A B := ⟨hAB⟩
  have hmap : (FixedPoints.subgroup A B).map B.subtype =
      B ⊓ centralizer (A : Set G) := by
    ext x
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨b.property, ?_⟩
      intro a ha
      have hh := congrArg B.subtype (hb (⟨a, ha⟩ : A))
      change a * (b : G) * a⁻¹ = b at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    · rintro ⟨hxB, hxC⟩
      refine ⟨⟨x, hxB⟩, ?_, rfl⟩
      intro a
      apply Subtype.ext
      change (a : G) * x * (a : G)⁻¹ = x
      exact mul_inv_eq_iff_eq_mul.mpr (hxC a a.property)
  have hh := hA.card_modEq_card_fixedPoints B
  change Nat.card B ≡ Nat.card (FixedPoints.subgroup A B) [MOD p] at hh
  rwa [← card_map_of_injective (K := FixedPoints.subgroup A B) B.subtype_injective,
    hmap] at hh
