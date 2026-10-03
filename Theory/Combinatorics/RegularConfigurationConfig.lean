module
public import Mathlib.Combinatorics.Configuration

/-!
# A projective-plane configuration from regular incidence counts

A finite nondegenerate point-line configuration with `q² + q + 1` points,
`q + 1` points on each line, and `q + 1` lines through each point, where
`1 < q`, has the three-point, three-line configuration required by
`Configuration.ProjectivePlane.exists_config`. The result states that exact
existential conclusion without assuming `HasPoints`, `HasLines`, or a
projective-plane structure. The given membership relation is unchanged.

This is the finite counting reduction used for Brauer, *On finite Desarguesian
planes I*, Theorem (3B)(d), article page 122. It supports the final assembly
of the projective plane after the incidence counts and nondegeneracy have
been established.

Choose a point `p₂`, distinct lines `l₂,l₃` through it, and a line `l₁`
avoiding it. Intersection uniqueness excludes at most two points of `l₂`
when avoiding `l₁` and `l₃`, so a suitable `p₃` exists. The total number
of points exceeds `2 * (q + 1)`, yielding a point `p₁` outside both `l₂`
and `l₃`. A private union-cardinality argument supplies both choices.
-/

namespace Configuration

private theorem exists_not_of_subtype_card_sum_lt {A : Type*} [Finite A]
    (R S : A → Prop)
    (hcard : Nat.card {x : A // R x} + Nat.card {x : A // S x} < Nat.card A) :
    ∃ x : A, ¬ R x ∧ ¬ S x := by
  classical
  let : Fintype A := Fintype.ofFinite A
  by_contra h
  have hcover : ∀ x : A, R x ∨ S x := by
    intro x
    by_contra hx
    exact h ⟨x, (not_or.mp hx).1, (not_or.mp hx).2⟩
  have heq : Nat.card {x : A // R x ∨ S x} = Nat.card A :=
    Nat.card_congr (Equiv.subtypeUnivEquiv hcover)
  have hle : Nat.card A ≤ Nat.card {x : A // R x} + Nat.card {x : A // S x} := by
    rw [← heq]
    simpa only [Nat.card_eq_fintype_card] using Fintype.card_subtype_or R S
  exact (not_le_of_gt hcard) hle

/-- Regular finite counts in a nondegenerate configuration supply the exact
eight incidence relations used by `ProjectivePlane.exists_config`. -/
public theorem exists_config_of_regular_counts
    {P L : Type*} [Membership P L] [Finite P] [Finite L] [Nondegenerate P L]
    (q : ℕ) (hq : 1 < q) (hP : Nat.card P = q ^ 2 + q + 1)
    (hpoints : ∀ l : L, pointCount P l = q + 1)
    (hlines : ∀ p : P, lineCount L p = q + 1) :
    ∃ (p₁ p₂ p₃ : P) (l₁ l₂ l₃ : L),
      p₁ ∉ l₂ ∧ p₁ ∉ l₃ ∧ p₂ ∉ l₁ ∧ p₂ ∈ l₂ ∧ p₂ ∈ l₃ ∧
        p₃ ∉ l₁ ∧ p₃ ∈ l₂ ∧ p₃ ∉ l₃ := by
  classical
  let : Fintype P := Fintype.ofFinite P
  let : Fintype L := Fintype.ofFinite L
  have hPpos : 0 < Fintype.card P := by
    rw [← Nat.card_eq_fintype_card, hP]
    positivity
  obtain ⟨p₂⟩ := Fintype.card_pos_iff.mp hPpos
  have hlinesgt : 1 < Fintype.card {l : L // p₂ ∈ l} := by
    rw [← Nat.card_eq_fintype_card]
    change 1 < lineCount L p₂
    rw [hlines]
    omega
  obtain ⟨l₂, l₃, hne⟩ := Fintype.one_lt_card_iff.mp hlinesgt
  have h₂₃ : (l₂ : L) ≠ (l₃ : L) := fun h => hne (Subtype.ext h)
  obtain ⟨l₁, hp₂₁⟩ := Nondegenerate.exists_line (L := L) p₂
  have h₂₁ : (l₂ : L) ≠ l₁ := by
    intro h
    exact hp₂₁ (h ▸ l₂.property)
  have hsmall (l : L) (hl : (l₂ : L) ≠ l) :
      Nat.card {p : {p : P // p ∈ (l₂ : L)} // p.1 ∈ l} ≤ 1 := by
    rw [Nat.card_eq_fintype_card]
    apply Fintype.card_le_one_iff.mpr
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    exact (Nondegenerate.eq_or_eq a.val.property b.val.property a.property b.property).resolve_right hl
  have hsmall₁ := hsmall l₁ h₂₁
  have hsmall₃ := hsmall l₃ h₂₃
  have hpointsize : Nat.card {p : P // p ∈ (l₂ : L)} = q + 1 := hpoints l₂
  obtain ⟨p₃, hp₃₁, hp₃₃⟩ := exists_not_of_subtype_card_sum_lt
    (fun p : {p : P // p ∈ (l₂ : L)} => p.1 ∈ l₁)
    (fun p : {p : P // p ∈ (l₂ : L)} => p.1 ∈ (l₃ : L)) (by omega)
  have htotal : Nat.card {p : P // p ∈ (l₂ : L)} +
      Nat.card {p : P // p ∈ (l₃ : L)} < Nat.card P := by
    change pointCount P (l₂ : L) + pointCount P (l₃ : L) < Nat.card P
    rw [hpoints, hpoints, hP]
    nlinarith
  obtain ⟨p₁, hp₁₂, hp₁₃⟩ := exists_not_of_subtype_card_sum_lt
    (fun p : P => p ∈ (l₂ : L)) (fun p : P => p ∈ (l₃ : L)) htotal
  exact ⟨p₁, p₂, p₃, l₁, l₂, l₃, hp₁₂, hp₁₃, hp₂₁, l₂.property,
    l₃.property, hp₃₁, p₃.property, hp₃₃⟩

end Configuration
