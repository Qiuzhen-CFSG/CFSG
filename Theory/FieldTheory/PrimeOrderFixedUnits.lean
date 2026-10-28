module
public import Mathlib.FieldTheory.Fixed
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Prime-order field actors retain a split prime torus

If p divides |F|−1, a field automorphism of order p has a fixed field whose
unit group still has order divisible by p. Apply the p-group fixed-point
congruence directly to the additive underlying set of F. This supplies the
fixed torus used in the symplectic case of Aschbacher–Smith A.3.18,
printed pp.51–53, without choosing Frobenius coordinates.
-/

public section
open Subgroup
namespace FiniteField
variable {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]

theorem prime_dvd_fixed_units (σ : F ≃+* F) (hσ : orderOf σ = p)
    (hd : p ∣ Nat.card F - 1) : p ∣ Nat.card (FixedBy.subfield F σ)ˣ := by
  let P := zpowers σ
  have hP : IsPGroup p P := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,hσ,pow_one])
  have hc := hP.card_modEq_card_fixedPoints F
  change Nat.card F ≡ Nat.card (FixedPoints.subfield P F) [MOD p] at hc
  have hK : FixedPoints.subfield P F = FixedBy.subfield F σ := by
    ext x
    change (∀ g : P, g • x = x) ↔ σ x = x
    constructor
    · intro hx
      exact hx ⟨σ,mem_zpowers σ⟩
    · intro hx g
      exact smul_eq_self_of_mem_zpowers g.property hx
  rw [hK] at hc
  have hh := Nat.ModEq.sub_right (a := 1) (by have := Nat.card_pos (α := F); omega)
    (by have := Nat.card_pos (α := FixedBy.subfield F σ); omega) hc
  rw [Nat.card_units]
  exact Nat.modEq_zero_iff_dvd.mp (hh.symm.trans hd.modEq_zero_nat)

end FiniteField
