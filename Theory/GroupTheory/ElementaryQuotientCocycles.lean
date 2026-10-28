module
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

/-!
# Involution cocycles through an elementary quotient

An involution on an elementary two-group has image equal to its fixed subgroup
when the square of the fixed subgroup order is the group order. Lift this
coboundary calculation through an arbitrary equivariant quotient; a second
correction in the kernel completes the nonabelian cocycle. This is the
two-layer argument of Aschbacher, *Sporadic Groups*, Exercise 2.8, used in
45.5(4), printed p.244.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory

 theorem elementary_fixed_is_coboundary {A : Type*} [Group A] [Finite A]
    [IsElementaryAbelian 2 A] (α : A →* A) (hα : ∀ a, α (α a) = a)
    (hc : Nat.card (α.eqLocus (MonoidHom.id A)) ^ 2 = Nat.card A)
    (x : A) (hx : α x = x) : ∃ y : A, x = y * α y⁻¹ := by
  let δ : A →* A := MonoidHom.id A / α
  have hi (a : A) : a⁻¹ = a := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A) a
  have hk : δ.ker = α.eqLocus (MonoidHom.id A) := by
    ext a
    change a / α a = 1 ↔ α a = a
    rw [div_eq_one, eq_comm]
  have hr : δ.range ≤ δ.ker := by
    rintro a ⟨b, rfl⟩
    change b / α b / α (b / α b) = 1
    rw [div_eq_one, map_div, hα]
    simp only [div_eq_mul_inv, hi, mul_comm]
  have hcard := δ.ker.card_mul_index
  rw [index_ker] at hcard
  have hpos : 0 < Nat.card δ.ker := Nat.card_pos
  have he : δ.range = δ.ker := by
    apply eq_of_le_of_card_ge hr
    have hc' : Nat.card δ.ker ^ 2 = Nat.card A := hk ▸ hc
    nlinarith
  have hx' : x ∈ δ.range := he ▸ (show x ∈ δ.ker from hk ▸ hx)
  obtain ⟨y, hy⟩ := hx'
  change y / α y = x at hy
  exact ⟨y, by simpa only [div_eq_mul_inv, map_inv] using hy.symm⟩

 theorem cocycle_of_elementary_quotient {R A : Type*} [Group R] [Group A]
    [Finite A] [IsElementaryAbelian 2 A]
    (f : R →* A) (hf : Function.Surjective f)
    (α : R →* R) (hα : ∀ r, α (α r) = r)
    (β : A →* A) (hβ : ∀ a, β (β a) = a)
    (hab : ∀ r, β (f r) = f (α r))
    (hc : Nat.card (β.eqLocus (MonoidHom.id A)) ^ 2 = Nat.card A)
    (hk : ∀ x : R, f x = 1 → x * α x = 1 →
      ∃ y : R, x = y * α y⁻¹)
    (x : R) (hx : x * α x = 1) : ∃ y : R, x = y * α y⁻¹ := by
  have hi (a : A) : a⁻¹ = a := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A) a
  have hfix : β (f x) = f x := by
    rw [hab]
    have he : f x * f (α x) = 1 := by rw [← map_mul, hx, map_one]
    exact (eq_inv_of_mul_eq_one_right he).trans (hi _)
  obtain ⟨b, hb⟩ := elementary_fixed_is_coboundary β hβ hc (f x) hfix
  obtain ⟨y, rfl⟩ := hf b
  let v := y⁻¹ * x * α y
  have hvf : f v = 1 := by
    simp only [v, map_mul, map_inv]
    rw [hb, map_inv, hab]
    group
  have hv : v * α v = 1 := by
    simp only [v, map_mul, map_inv, hα]
    calc
      _ = y⁻¹ * (x * α x) * y := by group
      _ = 1 := by rw [hx]; group
  obtain ⟨z, hz⟩ := hk v hvf hv
  refine ⟨y*z, ?_⟩
  have he := congrArg (fun w : R => y*w*(α y)⁻¹) hz
  calc
    x = y * v * (α y)⁻¹ := by dsimp [v]; group
    _ = y * (z * α z⁻¹) * (α y)⁻¹ := he
    _ = (y*z) * α (y*z)⁻¹ := by simp only [map_mul, map_inv, mul_inv_rev]; group
end Theory.GroupTheory
