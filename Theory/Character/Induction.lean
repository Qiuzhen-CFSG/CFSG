module

public import Mathlib.Data.Complex.Basic
public import Mathlib.GroupTheory.Index
public import Theory.Character.ClassFunction

/-!
# Induction of class functions

The class function on `G` induced from a class function of a subgroup `H`,
its support property, and Frobenius reciprocity for the scalar product.
The reciprocity proof changes variables by conjugation and then sums over H.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

universe u

/-- The class function on `G` induced from a class function of the subgroup `H`. -/
def inducedClassFunction {G : Type u} [Group G] [Fintype G] (H : Subgroup G)
    (φ : ClassFunction (↥H))
    : ClassFunction G := by
  classical
  exact fun g => (Nat.card (↥H) : ℂ)⁻¹ * ∑ x : G,
    if hx : x⁻¹ * g * x ∈ H then φ ⟨x⁻¹ * g * x, hx⟩ else 0

/-- The induced function vanishes on elements with no conjugate in `H`. -/
lemma inducedClassFunction_supportedOn {G : Type u} [Group G] [Fintype G] (H : Subgroup G)
    (φ : ClassFunction (↥H)) (g : G) (hg : ∀ x : G, x⁻¹ * g * x ∉ H)
    : inducedClassFunction H φ g = 0 := by
  classical
  unfold inducedClassFunction
  simp [hg]

attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

variable {G : Type u} [Group G] [Fintype G]

/-- Frobenius reciprocity: `(δ^G, χ)_G = (δ, χ|_H)_H` for a class function `χ`. -/
theorem scalarProduct_inducedClassFunction {G : Type u} [Group G] [Fintype G] (H : Subgroup G)
    (δ : ClassFunction (↥H)) {χ : ClassFunction G} (hχ : IsClassFunction χ) :
    scalarProduct G (inducedClassFunction H δ) χ =
      scalarProduct (↥H) δ (fun x : ↥H => χ (x : G)) := by
  classical
  let F : G → G → ℂ := fun g x =>
    if hx : x⁻¹ * g * x ∈ H then δ ⟨x⁻¹ * g * x, hx⟩ else 0
  calc
    scalarProduct G (inducedClassFunction H δ) χ
        = (Nat.card G : ℂ)⁻¹ * ∑ g : G, (inducedClassFunction H δ) g * star (χ g) := rfl
    _ = (Nat.card G : ℂ)⁻¹ * ∑ g : G,
          ((Nat.card (↥H) : ℂ)⁻¹ * ∑ x : G, F g x) * star (χ g) := rfl
    _ = (Nat.card G : ℂ)⁻¹ * (Nat.card (↥H) : ℂ)⁻¹ *
          ∑ g : G, ∑ x : G, F g x * star (χ g) := by
          calc
            (Nat.card G : ℂ)⁻¹ * ∑ g : G, ((Nat.card (↥H) : ℂ)⁻¹ * ∑ x : G, F g x) * star (χ g)
                = (Nat.card G : ℂ)⁻¹ * ((Nat.card (↥H) : ℂ)⁻¹ *
                    ∑ g : G, ∑ x : G, F g x * star (χ g)) := by
                    congr 1
                    calc
                      (∑ g : G, ((Nat.card (↥H) : ℂ)⁻¹ * ∑ x : G, F g x) * star (χ g))
                          = ∑ g : G, (Nat.card (↥H) : ℂ)⁻¹ *
                              ((∑ x : G, F g x) * star (χ g)) := by
                              refine Finset.sum_congr rfl ?_
                              intro g hg
                              ring
                      _ = (Nat.card (↥H) : ℂ)⁻¹ * ∑ g : G, (∑ x : G, F g x) * star (χ g) := by
                              rw [← Finset.mul_sum]
                      _ = (Nat.card (↥H) : ℂ)⁻¹ * ∑ g : G, ∑ x : G, F g x * star (χ g) := by
                              refine congrArg (fun t : ℂ => (Nat.card (↥H) : ℂ)⁻¹ * t) ?_
                              refine Finset.sum_congr rfl ?_
                              intro g hg
                              rw [Finset.sum_mul]
            _ = (Nat.card G : ℂ)⁻¹ * (Nat.card (↥H) : ℂ)⁻¹ *
                  ∑ g : G, ∑ x : G, F g x * star (χ g) := by
                  rw [← mul_assoc]
    _ = (Nat.card G : ℂ)⁻¹ * (Nat.card (↥H) : ℂ)⁻¹ *
          ∑ x : G, ∑ g : G, F g x * star (χ g) := by
          congr 1
          exact Finset.sum_comm
    _ = (Nat.card G : ℂ)⁻¹ * (Nat.card (↥H) : ℂ)⁻¹ *
          ∑ x : G, ∑ h : ↥H, δ h * star (χ (x * (h : G) * x⁻¹)) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro x hx
          calc
            (∑ g : G, F g x * star (χ g))
                = ∑ g ∈ Finset.univ.filter (fun g : G => x⁻¹ * g * x ∈ H),
                    F g x * star (χ g) := by
                    symm
                    exact Finset.sum_subset (Finset.subset_univ _) (by
                      intro g hg hnot
                      have hg' : ¬ x⁻¹ * g * x ∈ H := by
                        intro h
                        exact hnot (by simpa)
                      simp [F, hg'])
            _ = ∑ h : ↥H, δ h * star (χ (x * (h : G) * x⁻¹)) := by
                    refine Finset.sum_bij (fun g hg => ⟨x⁻¹ * g * x, (Finset.mem_filter.mp hg).2⟩)
                      (by intro g hg; simp)
                      ?_ ?_ ?_
                    · intro a ha b hb hEq
                      have hval : (⟨x⁻¹ * a * x, (Finset.mem_filter.mp ha).2⟩ : ↥H).1 =
                          (⟨x⁻¹ * b * x, (Finset.mem_filter.mp hb).2⟩ : ↥H).1 :=
                        congrArg Subtype.val hEq
                      exact mul_left_cancel (mul_right_cancel hval)
                    · intro h hh
                      refine ⟨x * (h : G) * x⁻¹, ?_, ?_⟩
                      · apply Finset.mem_filter.mpr
                        constructor
                        · exact Finset.mem_univ _
                        · rw [show x⁻¹ * (x * (h : G) * x⁻¹) * x = (h : G) by simp [mul_assoc]]
                          exact h.property
                      · apply Subtype.ext
                        simp [mul_assoc]
                    · intro g hg
                      have hmem : x⁻¹ * g * x ∈ H := (Finset.mem_filter.mp hg).2
                      simp [F, hmem]
                      · left
                        congr 2
                        simp [mul_assoc]
    _ = (Nat.card G : ℂ)⁻¹ * (Nat.card (↥H) : ℂ)⁻¹ *
          ((Nat.card G : ℂ) * ∑ h : ↥H, δ h * star (χ h)) := by
          congr 1
          have hinner : ∀ x : G,
              (∑ h : ↥H, δ h * star (χ (x * (h : G) * x⁻¹))) =
                ∑ h : ↥H, δ h * star (χ h) := by
            intro x
            refine Finset.sum_congr rfl ?_
            intro h hh
            congr 2
            exact hχ h x
          calc
            ∑ x : G, ∑ h : ↥H, δ h * star (χ (x * (h : G) * x⁻¹))
                = ∑ x : G, ∑ h : ↥H, δ h * star (χ h) := by
                    refine Finset.sum_congr rfl ?_
                    intro x hx
                    exact hinner x
            _ = (Nat.card G : ℂ) * ∑ h : ↥H, δ h * star (χ h) := by
                    rw [Nat.card_eq_fintype_card]
                    simp
    _ = (Nat.card (↥H) : ℂ)⁻¹ * ∑ h : ↥H, δ h * star (χ h) := by
          let S : ℂ := ∑ h : ↥H, δ h * star (χ h)
          have hc : (Nat.card G : ℂ) ≠ 0 := by
            exact_mod_cast (Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩)
          calc
            (Nat.card G : ℂ)⁻¹ * (Nat.card (↥H) : ℂ)⁻¹ * ((Nat.card G : ℂ) * S)
                = (Nat.card G : ℂ)⁻¹ * (Nat.card G : ℂ) * ((Nat.card (↥H) : ℂ)⁻¹ * S) := by ring
            _ = (Nat.card (↥H) : ℂ)⁻¹ * S := by
                    rw [inv_mul_cancel₀ hc, one_mul]
    _ = scalarProduct (↥H) δ (fun x : ↥H => χ (x : G)) := rfl

/-- Induction is additive in the function being induced. -/
theorem inducedClassFunction_add (H : Subgroup G) (f h : ClassFunction H) :
    inducedClassFunction H (f + h) = inducedClassFunction H f + inducedClassFunction H h := by
  classical
  ext g
  simp only [inducedClassFunction, Pi.add_apply]
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  split <;> simp_all

/-- Induction commutes with integer multiples. -/
theorem inducedClassFunction_zsmul (H : Subgroup G) (a : ℤ) (f : ClassFunction H) :
    inducedClassFunction H (a • f) = a • inducedClassFunction H f := by
  classical
  ext g
  simp only [inducedClassFunction, Pi.smul_apply]
  have hterm (x : G) :
      (if hx : x⁻¹ * g * x ∈ H then a • f ⟨_, hx⟩ else 0) =
        a • (if hx : x⁻¹ * g * x ∈ H then f ⟨_, hx⟩ else 0) := by
    split <;> simp_all
  simp_rw [hterm]
  rw [← Finset.smul_sum]
  simp only [zsmul_eq_mul]
  ring

/-- Induction as a map of integer modules, for use with character lattices. -/
def inducedClassFunctionIntLinear (H : Subgroup G) :
    ClassFunction H →ₗ[ℤ] ClassFunction G where
  toFun := inducedClassFunction H
  map_add' := inducedClassFunction_add H
  map_smul' := inducedClassFunction_zsmul H

/-- The projection formula for induction and multiplication by an ambient class function. -/
theorem inducedClassFunction_mul_restrict (H : Subgroup G) (f : ClassFunction H)
    {h : ClassFunction G} (hh : IsClassFunction h) :
    inducedClassFunction H (fun x => f x * h x) = inducedClassFunction H f * h := by
  classical
  ext g
  simp only [inducedClassFunction, Pi.mul_apply]
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  have heq : h (x⁻¹ * g * x) = h g := by simpa using hh g x⁻¹
  split <;> simp_all

/-- Induction produces a conjugacy-invariant function. -/
theorem inducedClassFunction_isClassFunction (H : Subgroup G) (f : ClassFunction H) :
    IsClassFunction (inducedClassFunction H f) := by
  classical
  intro a g
  unfold inducedClassFunction
  congr 1
  apply Fintype.sum_equiv (Equiv.mulLeft g⁻¹)
  intro z
  have heq : (g⁻¹ * z)⁻¹ * a * (g⁻¹ * z) = z⁻¹ * (g * a * g⁻¹) * z := by group
  change (if h : z⁻¹ * (g * a * g⁻¹) * z ∈ H then f ⟨_, h⟩ else 0) =
    (if h : (g⁻¹ * z)⁻¹ * a * (g⁻¹ * z) ∈ H then f ⟨_, h⟩ else 0)
  simp only [heq]
