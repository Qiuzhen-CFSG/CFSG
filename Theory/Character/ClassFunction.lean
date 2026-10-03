module

public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.RepresentationTheory.Character
public import Mathlib.GroupTheory.Index

/-!
# Class functions and the scalar product

Class functions `G → ℂ`, the scalar product `(φ, ψ)_G = |G|⁻¹ Σ φ(g) conj(ψ(g))`,
and the predicates character / irreducible character / generalized character /
linear character / disjointness.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

universe u

/-- A class function `G → ℂ`. -/
abbrev ClassFunction (G : Type u) := G → ℂ

/-- Constant on conjugacy classes. -/
def IsClassFunction {G : Type u} [Group G] (φ : ClassFunction G) : Prop :=
  ∀ x g : G, φ (g * x * g⁻¹) = φ x

/-- The paper's inner product `(φ, ψ)_G = |G|⁻¹ Σ φ(g) conj(ψ(g))`. -/
def scalarProduct (G : Type u) [Fintype G] (φ ψ : ClassFunction G) : ℂ :=
  (Nat.card G : ℂ)⁻¹ * ∑ g : G, φ g * star (ψ g)

/-- `|φ| = (φ, φ)`. -/
def normSq (G : Type u) [Fintype G] (φ : ClassFunction G) : ℂ :=
  scalarProduct G φ φ

/-- Supported on a set `A`. -/
def supportedOn {G : Type u} (φ : ClassFunction G) (A : Set G) : Prop :=
  ∀ g : G, g ∉ A → φ g = 0

/-- The characters of `G`. -/
def IsCharacter {G : Type u} [Group G] (φ : ClassFunction G) : Prop :=
  ∃ n : ℕ, ∃ ρ : Representation ℂ G (Fin n → ℂ), φ = ρ.character

/-- The irreducible characters of `G`. -/
def IsIrreducibleCharacter {G : Type u} [Group G] (φ : ClassFunction G) : Prop :=
  ∃ n : ℕ,
  ∃ ρ : Representation ℂ G (Fin n → ℂ), Representation.IsIrreducible ρ ∧ φ = ρ.character

/-- A generalized character is a difference of two characters. -/
def IsGeneralizedCharacter {G : Type u} [Group G] (φ : ClassFunction G) : Prop :=
  ∃ χ ψ : ClassFunction G, IsCharacter χ ∧ IsCharacter ψ ∧ φ = χ - ψ

/-- A linear (i.e. degree-one irreducible) character. -/
def IsLinearCharacter {G : Type u} [Group G] (φ : ClassFunction G) : Prop :=
  IsIrreducibleCharacter φ ∧ φ 1 = 1

/-- Two class functions are disjoint if no irreducible character occurs in both. -/
def ClassFunction.Disjoint {G : Type u} [Group G] [Fintype G] (φ ψ : ClassFunction G)
    : Prop :=
  ∀ χ : ClassFunction G,
    IsIrreducibleCharacter χ → scalarProduct G χ φ ≠ 0 → scalarProduct G χ ψ = 0

/-! ## Basic algebra of the scalar product -/

section ScalarProduct


lemma scalarProduct_add_left {G : Type u} [Fintype G] (φ₁ φ₂ ψ : ClassFunction G)
    : scalarProduct G (φ₁ + φ₂) ψ = scalarProduct G φ₁ ψ + scalarProduct G φ₂ ψ := by
  calc
    scalarProduct G (φ₁ + φ₂) ψ
        = (Nat.card G : ℂ)⁻¹ * ∑ x : G, (φ₁ x + φ₂ x) * star (ψ x) := by
      rfl
    _ = (Nat.card G : ℂ)⁻¹ * ∑ x : G, (φ₁ x * star (ψ x) + φ₂ x * star (ψ x)) := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro x hx
      rw [add_mul]
    _ = (Nat.card G : ℂ)⁻¹
        * (∑ x : G, φ₁ x * star (ψ x) + ∑ x : G, φ₂ x * star (ψ x)) := by
      rw [Finset.sum_add_distrib]
    _ = scalarProduct G φ₁ ψ + scalarProduct G φ₂ ψ := by
      rw [mul_add]
      rfl

lemma scalarProduct_smul_left {G : Type u} [Fintype G] (z : ℂ) (φ ψ : ClassFunction G)
    : scalarProduct G (z • φ) ψ = z * scalarProduct G φ ψ := by
  calc
    scalarProduct G (z • φ) ψ = (Nat.card G : ℂ)⁻¹ * ∑ g : G, z * (φ g * star (ψ g)) := by
      simp [scalarProduct, mul_assoc]
    _ = (Nat.card G : ℂ)⁻¹ * (z * ∑ g : G, φ g * star (ψ g)) := by
      rw [← Finset.mul_sum]
    _ = z * scalarProduct G φ ψ := by
      simp [scalarProduct, mul_left_comm]

lemma scalarProduct_add_right {G : Type u} [Fintype G] (φ ψ₁ ψ₂ : ClassFunction G)
    : scalarProduct G φ (ψ₁ + ψ₂) = scalarProduct G φ ψ₁ + scalarProduct G φ ψ₂ := by
  calc
    scalarProduct G φ (ψ₁ + ψ₂)
        = (Nat.card G : ℂ)⁻¹ * ∑ x : G, φ x * star (ψ₁ x + ψ₂ x) := by
      rfl
    _ = (Nat.card G : ℂ)⁻¹ * ∑ x : G, (φ x * star (ψ₁ x) + φ x * star (ψ₂ x)) := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro x hx
      calc
        φ x * star (ψ₁ x + ψ₂ x) = φ x * (star (ψ₁ x) + star (ψ₂ x)) := by
          congr 1
          exact map_add (starRingEnd ℂ) (ψ₁ x) (ψ₂ x)
        _ = φ x * star (ψ₁ x) + φ x * star (ψ₂ x) := by rw [mul_add]
    _ = (Nat.card G : ℂ)⁻¹
        * (∑ x : G, φ x * star (ψ₁ x) + ∑ x : G, φ x * star (ψ₂ x)) := by
      rw [Finset.sum_add_distrib]
    _ = scalarProduct G φ ψ₁ + scalarProduct G φ ψ₂ := by
      rw [mul_add]
      rfl

lemma scalarProduct_smul_right {G : Type u} [Fintype G] (z : ℂ) (φ ψ : ClassFunction G)
    : scalarProduct G φ (z • ψ) = scalarProduct G φ ψ * star z := by
  calc
    scalarProduct G φ (z • ψ)
        = (Nat.card G : ℂ)⁻¹ * ∑ g : G, (φ g * star (ψ g)) * star z := by
      unfold scalarProduct
      congr 1
      refine Finset.sum_congr rfl ?_
      intro g hg
      simp [mul_left_comm, mul_comm]
    _ = (Nat.card G : ℂ)⁻¹ * ((∑ g : G, φ g * star (ψ g)) * star z) := by
      rw [Finset.sum_mul]
    _ = scalarProduct G φ ψ * star z := by
      simp [scalarProduct, mul_left_comm, mul_comm]

lemma scalarProduct_sub_left {G : Type u} [Fintype G] (φ₁ φ₂ ψ : ClassFunction G)
    : scalarProduct G (φ₁ - φ₂) ψ = scalarProduct G φ₁ ψ - scalarProduct G φ₂ ψ := by
  calc
    scalarProduct G (φ₁ - φ₂) ψ = scalarProduct G (φ₁ + (-1 : ℂ) • φ₂) ψ := by
      simp [sub_eq_add_neg]
    _ = scalarProduct G φ₁ ψ + (-1 : ℂ) * scalarProduct G φ₂ ψ := by
      rw [scalarProduct_add_left, scalarProduct_smul_left]
    _ = scalarProduct G φ₁ ψ - scalarProduct G φ₂ ψ := by
      ring

lemma scalarProduct_conj {G : Type u} [Fintype G] (φ ψ : ClassFunction G)
    : star (scalarProduct G φ ψ) = scalarProduct G ψ φ := by
  unfold scalarProduct
  calc
    star ((Nat.card G : ℂ)⁻¹ * ∑ g : G, φ g * star (ψ g))
        = star ((Nat.card G : ℂ)⁻¹) * star (∑ g : G, φ g * star (ψ g)) := by
      simp
    _ = (Nat.card G : ℂ)⁻¹ * (∑ g : G, star (φ g * star (ψ g))) := by
      simp
    _ = (Nat.card G : ℂ)⁻¹ * (∑ g : G, star (φ g) * ψ g) := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro g hg
      calc
        star (φ g * star (ψ g)) = star (φ g) * star (star (ψ g)) := by
          exact map_mul (starRingEnd ℂ) (φ g) (star (ψ g))
        _ = star (φ g) * ψ g := by simp
    _ = (Nat.card G : ℂ)⁻¹ * ∑ g : G, ψ g * star (φ g) := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro g hg
      ring

lemma scalarProduct_self_real {G : Type u} [Fintype G] (φ : ClassFunction G)
    : star (scalarProduct G φ φ) = scalarProduct G φ φ := by
  simp [scalarProduct_conj]


/-- The `g⁻¹`-form product; agrees with `scalarProduct` on characters. -/
def characterProduct (G : Type u) [Group G] [Fintype G] (φ ψ : ClassFunction G) : ℂ :=
  (Nat.card G : ℂ)⁻¹ * ∑ g : G, φ g * ψ g⁻¹

lemma characterProduct_add_left {G : Type u} [Group G] [Fintype G] (φ₁ φ₂ ψ : ClassFunction G)
    : characterProduct G (φ₁ + φ₂) ψ
      = characterProduct G φ₁ ψ + characterProduct G φ₂ ψ := by
  calc
    characterProduct G (φ₁ + φ₂) ψ
        = (Nat.card G : ℂ)⁻¹ * ∑ x : G, (φ₁ x + φ₂ x) * ψ x⁻¹ := by
      rfl
    _ = (Nat.card G : ℂ)⁻¹ * ∑ x : G, (φ₁ x * ψ x⁻¹ + φ₂ x * ψ x⁻¹) := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro x hx
      rw [add_mul]
    _ = (Nat.card G : ℂ)⁻¹ * (∑ x : G, φ₁ x * ψ x⁻¹ + ∑ x : G, φ₂ x * ψ x⁻¹) := by
      rw [Finset.sum_add_distrib]
    _ = characterProduct G φ₁ ψ + characterProduct G φ₂ ψ := by
      rw [mul_add]
      rfl

lemma characterProduct_smul_left {G : Type u} [Group G] [Fintype G] (z : ℂ) (φ ψ : ClassFunction G)
    : characterProduct G (z • φ) ψ = z * characterProduct G φ ψ := by
  calc
    characterProduct G (z • φ) ψ = (Nat.card G : ℂ)⁻¹ * ∑ g : G, z * (φ g * ψ g⁻¹) := by
      simp [characterProduct, mul_assoc]
    _ = (Nat.card G : ℂ)⁻¹ * (z * ∑ g : G, φ g * ψ g⁻¹) := by
      rw [← Finset.mul_sum]
    _ = z * characterProduct G φ ψ := by
      simp [characterProduct, mul_left_comm]

end ScalarProduct

/-- The scalar product is positive definite. The proof sums the nonnegative
complex squared norms; compare `BenderGlauberman.normSq_eq_zero_iff`. -/
theorem scalarProduct_self_eq_zero_iff {G : Type*} [Group G] [Fintype G] (φ : ClassFunction G) :
    scalarProduct G φ φ = 0 ↔ φ = 0 := by
  classical
  constructor
  · intro h
    ext g
    have hsum0 : (∑ x : G, φ x * star (φ x)) =
        ∑ x : G, (Complex.normSq (φ x) : ℂ) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Complex.normSq_eq_conj_mul_self, mul_comm]
      simp
    have h1 : (Nat.card G : ℂ) * scalarProduct G φ φ =
        ∑ x : G, (Complex.normSq (φ x) : ℂ) := by
      unfold scalarProduct
      rw [hsum0, ← mul_assoc,
        mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.card_pos (α := G)).ne'), one_mul]
    have hsum : (∑ x : G, (Complex.normSq (φ x) : ℂ)) = 0 := by
      rw [← h1, h, mul_zero]
    have hsum' : (∑ x : G, Complex.normSq (φ x) : ℝ) = 0 := by
      rw [← Complex.ofReal_sum] at hsum
      exact Complex.ofReal_injective (by simpa only [Complex.ofReal_zero] using hsum)
    exact Complex.normSq_eq_zero.mp
      ((Finset.sum_eq_zero_iff_of_nonneg (fun x _ => Complex.normSq_nonneg (φ x))).mp
        hsum' g (Finset.mem_univ g))
  · rintro rfl
    simp [scalarProduct]

/-- Invariant functions are determined by their scalar products with invariant functions. -/
theorem IsClassFunction.eq_of_scalarProduct_eq {G : Type*} [Group G] [Fintype G]
    {f h : ClassFunction G} (hf : IsClassFunction f) (hh : IsClassFunction h)
    (heq : ∀ ψ : ClassFunction G, IsClassFunction ψ →
      scalarProduct G f ψ = scalarProduct G h ψ) : f = h := by
  apply sub_eq_zero.mp
  apply (scalarProduct_self_eq_zero_iff (f - h)).mp
  rw [scalarProduct_sub_left, heq (f - h) (by
    intro x g
    simp only [Pi.sub_apply, hf x g, hh x g]), sub_self]
