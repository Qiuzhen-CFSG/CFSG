module

public import Theory.FieldTheory.BinaryTorusInvolution
public import Mathlib.FieldTheory.Fixed
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.Subgroup.Actions


/-!
# Cubic field automorphisms and multiplicative displacements

The displacement homomorphism on the unit group has kernel the units of
its fixed field. For an automorphism of order three, finite fixed-field
theory gives an extension of degree three. If the fixed field has r elements,
the displacement image therefore has order r² + r + 1. This number is
larger than three and never divisible by nine, so it is not a three-power.
Consequently a cubic field actor whose displacement image is a three-group
is the identity. No characteristic or Frobenius-coordinate choice is needed.

Source application: the PSL₂ Borel-action argument in Aschbacher--Smith,
proof of 15.3.37, `refs/quasithin.pdf`, printed p.1135.
-/

@[expose] public section

open Subgroup
namespace FiniteField.CubicTorusDisplacement
open BinaryTorusInvolution
variable {F : Type*} [Field F] [Finite F]

omit [Finite F] in
private theorem card_displacement_kernel (σ : F ≃+* F) :
    Nat.card (displacement σ).ker = Nat.card (FixedBy.subfield F σ) - 1 := by
  let K := FixedBy.subfield F σ
  let f : Kˣ →* Fˣ := Units.map K.subtype.toMonoidHom
  have hf (u : Kˣ) : f u ∈ (displacement σ).ker := by
    change Units.map σ.toMonoidHom (f u) * (f u)⁻¹ = 1
    apply mul_inv_eq_one.mpr
    apply Units.ext
    exact (u : K).property
  let g : Kˣ →* (displacement σ).ker := f.codRestrict _ hf
  have hg : Function.Bijective g := by
    constructor
    · intro u v huv
      apply Units.ext
      apply Subtype.ext
      exact congrArg (fun a : (displacement σ).ker => (a.val : F)) huv
    · intro u
      have hu : σ (u.val : F) = (u.val : F) := by
        have hh := u.property
        change Units.map σ.toMonoidHom u.val * u.val⁻¹ = 1 at hh
        exact congrArg Units.val (mul_inv_eq_one.mp hh)
      let x : K := ⟨(u.val : F), hu⟩
      have hx : x ≠ 0 := fun hh => Units.ne_zero u.val (congrArg Subtype.val hh)
      refine ⟨Units.mk0 x hx, ?_⟩
      apply Subtype.ext
      apply Units.ext
      rfl
  exact (Nat.card_congr (MulEquiv.ofBijective g hg).toEquiv).symm.trans (Nat.card_units K)

private theorem card_eq_cube_of_order_three (σ : F ≃+* F) (hσ : orderOf σ = 3) :
    Nat.card F = Nat.card (FixedBy.subfield F σ) ^ 3 := by
  let H := zpowers σ
  let K := FixedPoints.subfield H F
  let : Finite H := Finite.of_injective
    (fun g : H => (g.val : F → F)) (fun a b h => Subtype.ext (DFunLike.coe_injective h))
  let : Fintype H := Fintype.ofFinite H
  let : FaithfulSMul H F := ⟨fun {a b} he => Subtype.ext (RingEquiv.ext he)⟩
  have hd : Module.finrank K F = 3 := by
    rw [FixedPoints.finrank_eq_card, Fintype.card_eq_nat_card, Nat.card_zpowers, hσ]
  have hK : K = FixedBy.subfield F σ := by
    ext x
    change (∀ g : H, g • x = x) ↔ σ x = x
    constructor
    · intro hx
      exact hx ⟨σ, mem_zpowers σ⟩
    · intro hx g
      exact smul_eq_self_of_mem_zpowers g.property hx
  rw [Module.natCard_eq_pow_finrank (K := K), hd, hK]

/-- The displacement image has the cubic extension norm-kernel cardinality. -/
theorem card_displacement_of_order_three (σ : F ≃+* F) (hσ : orderOf σ = 3) :
    Nat.card (displacement σ).range =
      Nat.card (FixedBy.subfield F σ) ^ 2 + Nat.card (FixedBy.subfield F σ) + 1 := by
  let r := Nat.card (FixedBy.subfield F σ)
  have hr : 1 < r := Finite.one_lt_card
  have hc := (displacement σ).ker.card_mul_index
  rw [index_ker, card_displacement_kernel, Nat.card_units,
    card_eq_cube_of_order_three σ hσ] at hc
  change (r - 1) * Nat.card (displacement σ).range = r ^ 3 - 1 at hc
  apply Nat.eq_of_mul_eq_mul_left (show 0 < r - 1 by omega)
  calc
    (r - 1) * Nat.card (displacement σ).range = r ^ 3 - 1 := hc
    _ = (r - 1) * (r ^ 2 + r + 1) := by
      have hr1 : r - 1 + 1 = r := Nat.sub_add_cancel (by omega)
      have hr3 : r ^ 3 - 1 + 1 = r ^ 3 := Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))
      nlinarith

private theorem not_nine_dvd (r : ℕ) : ¬ 9 ∣ r ^ 2 + r + 1 := by
  intro h
  have hh := Nat.mod_eq_zero_of_dvd h
  have hr := Nat.mod_lt r (by decide : 0 < 9)
  rw [Nat.add_mod (r ^ 2 + r) 1, Nat.add_mod (r ^ 2) r, Nat.pow_mod] at hh
  interval_cases he : r % 9 <;> norm_num [he] at hh

/-- A cubic coefficient action with three-primary displacement is trivial. -/
theorem eq_one_of_three_primary_displacement (σ : F ≃+* F)
    (hσ : σ ^ 3 = 1) (hp : IsPGroup 3 (displacement σ).range) : σ = 1 := by
  by_contra hne
  have ho : orderOf σ = 3 := orderOf_eq_prime hσ hne
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  rw [card_displacement_of_order_three σ ho] at hk
  have hr := Finite.one_lt_card (α := FixedBy.subfield F σ)
  have hk2 : 2 ≤ k := by
    by_contra hn
    interval_cases k <;> norm_num only [pow_zero, pow_one] at hk <;> nlinarith
  apply not_nine_dvd (Nat.card (FixedBy.subfield F σ))
  rw [hk]
  exact pow_dvd_pow 3 hk2

end FiniteField.CubicTorusDisplacement
