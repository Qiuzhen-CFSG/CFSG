module
public import Mathlib.Combinatorics.Configuration

/-!
# Nondegeneracy from regular finite incidence counts

Consider a finite point-line configuration with `q² + q + 1` points and
lines, `q + 1` points on each line and lines through each point, where
`1 < q`. If every two distinct lines meet, the configuration is nondegenerate:
there are off-line points and off-point lines, and two distinct lines cannot
have two distinct common points. Incidence is an arbitrary `Membership P L`;
no projective-plane structure or intersection-uniqueness assumption is used.

This is the counting step of Brauer, *On finite Desarguesian planes I*,
Theorem (3B)(b), article page 122, using the counts of (3A), page 121.
It supplies the nondegeneracy boundary required before the existing Mathlib
configuration results can construct lines through pairs of points.

Fix a line. Pairs of a point on it and a different line through that point
number `(q + 1) * q`. Their projection onto the other lines is surjective by
intersection existence, and the target has the same cardinality. Finite
surjectivity plus equal cardinality gives injectivity, hence intersection
uniqueness. The total counts exceed the number incident with a single line
or point, giving the other two nondegeneracy conditions.
-/

open scoped BigOperators

namespace Configuration

private theorem card_subtype_and_ne {A : Type*} [Finite A]
    (R : A → Prop) (a : A) (ha : R a) :
    Nat.card {x : A // R x ∧ x ≠ a} = Nat.card {x : A // R x} - 1 := by
  classical
  let : Fintype A := Fintype.ofFinite A
  have hsingle : Fintype.card {x : {x : A // R x} // x.1 = a} = 1 := by
    simpa only [Subtype.ext_iff] using Fintype.card_subtype_eq (⟨a, ha⟩ : {x : A // R x})
  rw [← Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter R (fun x => x ≠ a))]
  simp only [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl (fun x : {x : A // R x} => x.1 = a), hsingle]

private theorem intersection_unique_of_regular_counts
    {P L : Type*} [Membership P L] [Finite P] [Finite L] (q : ℕ)
    (hL : Nat.card L = q ^ 2 + q + 1)
    (hpoints : ∀ l : L, pointCount P l = q + 1)
    (hlines : ∀ p : P, lineCount L p = q + 1)
    (hinter : ∀ l₁ l₂ : L, l₁ ≠ l₂ → ∃ p : P, p ∈ l₁ ∧ p ∈ l₂)
    {p₁ p₂ : P} {l₁ l₂ : L} (hne : l₁ ≠ l₂)
    (h₁ : p₁ ∈ l₁) (h₂ : p₂ ∈ l₁) (h₃ : p₁ ∈ l₂) (h₄ : p₂ ∈ l₂) : p₁ = p₂ := by
  classical
  let : Fintype P := Fintype.ofFinite P
  let : Fintype L := Fintype.ofFinite L
  let T := Σ p : {p : P // p ∈ l₁}, {l : L // p.1 ∈ l ∧ l ≠ l₁}
  let f : T → {l : L // l ≠ l₁} := fun t => ⟨t.2.1, t.2.2.2⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨l, hl⟩
    obtain ⟨p, hp₁, hpl⟩ := hinter l₁ l hl.symm
    exact ⟨⟨⟨p, hp₁⟩, ⟨l, hpl, hl⟩⟩, rfl⟩
  have hT : Nat.card T = (q + 1) * q := by
    dsimp only [T]
    rw [Nat.card_sigma]
    calc
      _ = ∑ _p : {p : P // p ∈ l₁}, q := by
        apply Finset.sum_congr rfl
        intro p _
        rw [card_subtype_and_ne (fun l : L => p.1 ∈ l) l₁ p.2]
        change lineCount L p.1 - 1 = q
        rw [hlines, Nat.add_sub_cancel]
      _ = (q + 1) * q := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        rw [← Nat.card_eq_fintype_card]
        change pointCount P l₁ * q = (q + 1) * q
        rw [hpoints]
  have hrest : Nat.card {l : L // l ≠ l₁} = (q + 1) * q := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun l : L => l = l₁),
      Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card, hL, Nat.add_sub_cancel]
    ring
  have hinj : Function.Injective f :=
    ((Nat.bijective_iff_surjective_and_card f).mpr ⟨hsurj, hT.trans hrest.symm⟩).1
  let t₁ : T := ⟨⟨p₁, h₁⟩, ⟨l₂, h₃, hne.symm⟩⟩
  let t₂ : T := ⟨⟨p₂, h₂⟩, ⟨l₂, h₄, hne.symm⟩⟩
  have ht : t₁ = t₂ := hinj rfl
  exact congrArg (fun t : T => t.1.1) ht

/-- Regular projective-size counts and existence of line intersections imply
nondegeneracy, without assuming intersection uniqueness or a plane structure. -/
public theorem nondegenerate_of_regular_counts
    {P L : Type*} [Membership P L] [Finite P] [Finite L] (q : ℕ) (hq : 1 < q)
    (hP : Nat.card P = q ^ 2 + q + 1) (hL : Nat.card L = q ^ 2 + q + 1)
    (hpoints : ∀ l : L, pointCount P l = q + 1)
    (hlines : ∀ p : P, lineCount L p = q + 1)
    (hinter : ∀ l₁ l₂ : L, l₁ ≠ l₂ → ∃ p : P, p ∈ l₁ ∧ p ∈ l₂) :
    Nondegenerate P L := by
  classical
  have hlt : q + 1 < q ^ 2 + q + 1 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · intro l
    by_contra h
    have hall : ∀ p : P, p ∈ l := by simpa only [not_exists, not_not] using h
    have hcard : pointCount P l = Nat.card P := Nat.card_congr (Equiv.subtypeUnivEquiv hall)
    rw [hpoints, hP] at hcard
    exact (Nat.ne_of_lt hlt) hcard
  · intro p
    by_contra h
    have hall : ∀ l : L, p ∈ l := by simpa only [not_exists, not_not] using h
    have hcard : lineCount L p = Nat.card L := Nat.card_congr (Equiv.subtypeUnivEquiv hall)
    rw [hlines, hL] at hcard
    exact (Nat.ne_of_lt hlt) hcard
  · intro p₁ p₂ l₁ l₂ h₁ h₂ h₃ h₄
    by_cases heq : l₁ = l₂
    · exact Or.inr heq
    · exact Or.inl (intersection_unique_of_regular_counts q hL hpoints hlines hinter heq h₁ h₂ h₃ h₄)

end Configuration
