module

public import Theory.Character.ClassFunctionSum
public import Theory.Character.Orthogonality

/-!
# Character inner products from centralizer orders

Partition the sum over a finite group into its actual conjugacy classes.
Orbit–stabilizer cancels the group order against each class size, leaving
the reciprocal centralizer orders as weights. No character assumption is
needed; the formula holds for arbitrary complex class functions.

This is the usual class-sum form of the ordinary character inner product.
It is used to realize numerical tables once genuine generalized-character
and class-enumeration inputs have been supplied.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite

/-- Compute the scalar product from actual conjugacy representatives and
centralizer orders. -/
public theorem classFunctionInner_eq_sum_div_centralizer
    {G : Type*} [Group G] [Finite G] {I : Type*} [Fintype I]
    (r : I → G) (hr : Function.Bijective (fun i => ConjClasses.mk (r i)))
    (φ ψ : ConjClassFunction G) :
    classFunctionInner φ ψ = ∑ i,
      φ (ConjClasses.mk (r i)) * star (ψ (ConjClasses.mk (r i))) /
        (Nat.card (Subgroup.centralizer ({r i} : Set G)) : ℂ) := by
  classical
  let f : ClassFunction G := fun g =>
    φ (ConjClasses.mk g) * star (ψ (ConjClasses.mk g))
  have hf : IsClassFunction f := by
    intro x g
    change ofConjClassFunction φ (g * x * g⁻¹) *
      star (ofConjClassFunction ψ (g * x * g⁻¹)) =
        ofConjClassFunction φ x * star (ofConjClassFunction ψ x)
    rw [ofConjClassFunction_isClassFunction φ x g,
      ofConjClassFunction_isClassFunction ψ x g]
  change (Nat.card G : ℂ)⁻¹ * ∑ g, f g = _
  rw [hf.sum_eq_sum_class_representatives r hr, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hc : Nat.card (ConjClasses.mk (r i)).carrier *
      Nat.card (Subgroup.centralizer ({r i} : Set G)) = Nat.card G := by
    have he : Subgroup.centralizer ({r i} : Set G) ≃
        {x : G // x * r i = r i * x} :=
      Equiv.subtypeEquivRight (fun _ => Subgroup.mem_centralizer_singleton_iff)
    rw [Nat.card_congr he]
    exact class_card_mul_centralizer_card (r i)
  have hc' : (Nat.card (ConjClasses.mk (r i)).carrier : ℂ) *
      (Nat.card (Subgroup.centralizer ({r i} : Set G)) : ℂ) = (Nat.card G : ℂ) := by
    exact_mod_cast hc
  have hG : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := G)).ne'
  have hC : (Nat.card (Subgroup.centralizer ({r i} : Set G)) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := Subgroup.centralizer ({r i} : Set G))).ne'
  dsimp only [f]
  field_simp [hG, hC]
  linear_combination (φ (ConjClasses.mk (r i)) * star (ψ (ConjClasses.mk (r i)))) * hc'
