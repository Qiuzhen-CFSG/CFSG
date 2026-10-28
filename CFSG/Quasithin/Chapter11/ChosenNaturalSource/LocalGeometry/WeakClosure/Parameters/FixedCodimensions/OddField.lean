module
public import Theory.Representation.FiniteFieldSemilinearDisplacement

/-!
# Odd prime field actors on the marked natural quotient

The actual semilinearity equation forces the coefficient automorphism's
order to divide the actor's order. A nontrivial coefficient part of prime
order therefore has that same order, so finite-field descent gives the
sharp two-thirds displacement bound. SymplecticOdd applies it to the
faithful quotient of the original chosen module.

Source: Aschbacher--Smith, H.0.1 and 11.2.2, printed pp.377,767--768.
-/

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FullAutomizer
variable {H F W : Type*} [Group H] [Field F] [Finite F] [Algebra (ZMod 2) F]
  [AddCommGroup W] [Module F W] [Module (ZMod 2) W] [IsScalarTower (ZMod 2) F W]
  [FiniteDimensional F W]

omit [Finite F] [Algebra (ZMod 2) F] [IsScalarTower (ZMod 2) F W]
    [FiniteDimensional F W] in
private theorem coefficient_pow_eq_one [Nontrivial W]
    (ρ : Representation (ZMod 2) H W) (a : H) {p : ℕ} (ha : a ^ p = 1)
    (σ : F ≃+* F) (hσ : ∀ r v, ρ a (r • v) = σ r • ρ a v) : σ ^ p = 1 := by
  have hs (k : ℕ) (r : F) (v : W) :
      ρ (a ^ k) (r • v) = (σ ^ k) r • ρ (a ^ k) v := by
    induction k with
    | zero => simp
    | succ k ih =>
      simp only [pow_succ', map_mul, Module.End.mul_apply, RingAut.mul_apply]
      rw [ih, hσ]
  obtain ⟨v,hv⟩ := exists_ne (0 : W)
  ext r
  apply smul_left_injective F hv
  simpa only [ha, map_one, Module.End.one_apply, RingAut.one_apply] using (hs p r v).symm

omit [IsScalarTower (ZMod 2) F W] in
/-- A nontrivial field part of an odd prime actor moves at least two thirds
of the binary space. Its order is derived from the actual action. -/
theorem odd_field_lower [Nontrivial W]
    (ρ : Representation (ZMod 2) H W) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (a : H) (ha : orderOf a = p) (σ : F ≃+* F) (hσ1 : σ ≠ 1)
    (hσ : ∀ r v, ρ a (r • v) = σ r • ρ a v) :
    2 * Module.finrank (ZMod 2) F * Module.finrank F W ≤
      3 * fixedCodim ρ (zpowers a) := by
  let : Fact p.Prime := ⟨hp⟩
  have hap : a ^ p = 1 := ha ▸ pow_orderOf_eq_one a
  have hsp := coefficient_pow_eq_one ρ a hap σ hσ
  exact FiniteFieldSemilinearDisplacement.two_thirds_le_fixedCodim ρ hp ho a ha σ
    (orderOf_eq_prime hsp hσ1) hσ

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FullAutomizer
