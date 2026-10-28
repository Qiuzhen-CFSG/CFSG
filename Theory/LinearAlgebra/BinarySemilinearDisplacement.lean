module

public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Basic

/-!
# Minimum binary displacement for degree-two semilinear operators

A nonidentity operator linear over a quadratic extension has positive binary
displacement divisible by two. For a nontrivial field twist, multiplication
by a moved scalar embeds the fixed space into the displacement space. In
binary dimension at least four, both arguments give moved rank at least two.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, the natural
L₂(4) tensor exclusion in 14.4.6(a), printed p.1008.
-/

public section
namespace Representation.BinaryOffender.NaturalTensor
open Module
variable {F V : Type*} [Field F] [Algebra (ZMod 2) F]
  [AddCommGroup V] [Module F V] [Module (ZMod 2) V] [IsScalarTower (ZMod 2) F V]
  [Module.Finite (ZMod 2) V]

/-- A nonidentity semilinear operator cannot be a binary transvection here. -/
theorem two_le_semilinear_displacement
    (hdegree : finrank (ZMod 2) F = 2) (hdim : 4 ≤ finrank (ZMod 2) V)
    (T : Module.End (ZMod 2) V) (hne : T ≠ 1)
    (σ : F →+* F) (hT : ∀ a v, T (a • v) = σ a • T v) :
    2 ≤ finrank (ZMod 2) (LinearMap.range (T - LinearMap.id)) := by
  by_cases hσ : ∃ a, σ a ≠ a
  · have hb := finrank_le_twice_operatorFixedCodim T σ hσ hT
    change finrank (ZMod 2) V ≤
      2 * finrank (ZMod 2) (LinearMap.range (T - LinearMap.id)) at hb
    omega
  · push Not at hσ
    let δ : V →ₗ[F] V :=
      { toFun := fun v => T v - v
        map_add' := by intro x y; simp only [map_add]; abel
        map_smul' := by intro a v; simp only [hT, hσ, smul_sub]; rfl }
    have he : finrank (ZMod 2) (LinearMap.range (T - LinearMap.id)) =
        2 * finrank F δ.range := by
      change finrank (ZMod 2) (δ.restrictScalars (ZMod 2)).range = _
      rw [LinearMap.range_restrictScalars]
      have he := ((Submodule.restrictScalarsEquiv (ZMod 2) F V δ.range).restrictScalars
        (ZMod 2)).finrank_eq
      rw [he, ← Module.finrank_mul_finrank (ZMod 2) F δ.range, hdegree]
    have hpos : 0 < finrank (ZMod 2) (LinearMap.range (T - LinearMap.id)) := by
      by_contra! hz
      have hb := LinearMap.range_eq_bot.mp
        (Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero hz))
      exact hne (sub_eq_zero.mp hb)
    omega
end Representation.BinaryOffender.NaturalTensor
