module

public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.NormalForm
public import Theory.SpecificGroups.PSL3.CartanActions.ActorCoverage
public import Theory.SpecificGroups.PSL3.ProjectionKernel

/-!
# Lifting odd-prime projective automorphisms in degree three

The odd-prime normal form lifts a projective automorphism to conjugation or
conjugation followed by inverse transpose on the actual special linear group.
Perfectness makes the central-quotient action injective, so every prescribed
power relation is retained by the lift. The scalar kernel embeds in the field's
unit group and its cardinality is therefore nonzero in the coefficient field,
including characteristic three.

The formulas use the original projection SL₃ → PSL₃ and the original matrix
inclusion. Source: GLS3, Theorem 2.5.12(a) and §2.7; the degree-three inspection
in Aschbacher–Smith, *The Classification of Quasithin Groups*, 1.3.4.
-/

public section
open scoped MatrixGroups
namespace Matrix.PSL3.ThreeWeightLift
open OuterSolvable
variable (F : Type*) [Field F] [Finite F]

/-- The actual scalar kernel has invertible cardinality in the defining field. -/
theorem projection_kernel_card_ne_zero : (Nat.card (projection F).ker : F) ≠ 0 := by
  classical
  let := Fintype.ofFinite F
  rw [Nat.card_congr (projectionKernelEquivRoots F).toEquiv, Nat.card_eq_fintype_card]
  exact FiniteField.card_cast_subgroup_card_ne_zero (rootsOfUnity 3 F)

variable [IsSimpleGroup PSL(3,F)]

/-- The odd-prime normal form lifts with its literal conjugation or inverse-transpose formula. -/
theorem exists_lift
    (hns : ¬ Group.IsSolvable PSL(3,F)) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p) (β : MulAut PSL(3,F)) :
    ∃ α : MulAut SL(3,F), centerAction F α = β ∧
      ∃ g : GL (Fin 3) F,
        (∀ x : SL(3,F), SpecialLinearGroup.toGL (α x) =
          g * SpecialLinearGroup.toGL x * g⁻¹) ∨
        (∀ x : SL(3,F), (SpecialLinearGroup.toGL (α x)).val =
          g.val * (SpecialLinearGroup.toGL x).inv.transpose * g.inv) := by
  obtain ⟨g, h | h⟩ := OddInvolutionFixed.automorphism_normal_form hns hp ho hF β
  · exact ⟨linearConjSL F g, h.symm, g, Or.inl (linearConjSL_toGL F g)⟩
  · refine ⟨linearConjSL F g * graphSL F, ?_, g, Or.inr ?_⟩
    · rw [map_mul]
      exact h.symm
    · intro x
      rw [MulAut.mul_apply, linearConjSL_toGL, OddInvolutionFixed.graphSL_toGL]
      rfl

omit [Finite F] [IsSimpleGroup PSL(3,F)] in
/-- A lift through the faithful central-quotient action satisfies exactly the same power relations. -/
theorem lift_pow_eq_one_iff (α : MulAut SL(3,F)) (β : MulAut PSL(3,F))
    (h : centerAction F α = β) (m : ℕ) : α ^ m = 1 ↔ β ^ m = 1 := by
  rw [← h, ← map_pow, ← map_one (centerAction F)]
  exact (CartanActions.ActorCoverage.centerAction_injective F).eq_iff.symm

/-- A two-power projective actor lifts to a two-power actor with the exact required matrix formula. -/
theorem exists_two_power_lift
    (hns : ¬ Group.IsSolvable PSL(3,F)) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p)
    (β : MulAut PSL(3,F)) (hβ : ∃ n : ℕ, β ^ (2 ^ n) = 1) :
    ∃ α : MulAut SL(3,F),
      (∀ x, projection F (α x) = β (projection F x)) ∧
      (∃ n : ℕ, α ^ (2 ^ n) = 1) ∧
      ∃ g : GL (Fin 3) F,
        (∀ x : SL(3,F), SpecialLinearGroup.toGL (α x) =
          g * SpecialLinearGroup.toGL x * g⁻¹) ∨
        (∀ x : SL(3,F), (SpecialLinearGroup.toGL (α x)).val =
          g.val * (SpecialLinearGroup.toGL x).inv.transpose * g.inv) := by
  obtain ⟨α, hα, hm⟩ := exists_lift F hns hp ho hF β
  refine ⟨α, ?_, ?_, hm⟩
  · intro x
    rw [← hα]
    rfl
  · obtain ⟨n, hn⟩ := hβ
    exact ⟨n, (lift_pow_eq_one_iff F α β hα (2 ^ n)).mpr hn⟩

end Matrix.PSL3.ThreeWeightLift
