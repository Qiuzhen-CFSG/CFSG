module
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Displacement bounds from a commuting fixed-point-free action

Every orbit of a nonzero vector under a fixed-point-free linear action is
free. If the actor group has order 2ⁿ−1, every nonzero invariant binary
subspace therefore has dimension at least n. The displacement space of an
operator commuting with the action is such a subspace.

The application is the central Cartan on the literal U/Z₁ in
Aschbacher–Smith 5.1.17, printed p.641 (refs/quasithin.pdf).
-/

open Subgroup Representation
public noncomputable section
namespace Representation.FixedFreeCentralAction
variable {G A V : Type*} [Group G] [Group A] [Finite A]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- A fixed-point-free action has a free orbit inside every nonzero invariant subspace. -/
theorem card_lt_of_invariant
    (ρ : Representation (ZMod 2) G V) (f : A →* G)
    (hf : ∀ a : A, a ≠ 1 → ∀ v, ρ (f a) v = v → v = 0)
    (S : Submodule (ZMod 2) V) (hs : ∀ a : A, ∀ v ∈ S, ρ (f a) v ∈ S)
    (hne : S ≠ ⊥) : Nat.card A < Nat.card S := by
  classical
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Fintype A := Fintype.ofFinite A
  let : Fintype S := Fintype.ofFinite S
  obtain ⟨v,hv,hv0⟩ : ∃ v ∈ S, v ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hne (bot_unique (fun v hv => hn v hv))
  let j : A → S := fun a => ⟨ρ (f a) v,hs a v hv⟩
  have hj : Function.Injective j := by
    intro a b he
    by_contra hab
    have hne : b⁻¹*a ≠ 1 := by
      intro he
      apply hab
      have hh := congrArg (fun c => b*c) he
      simpa only [← mul_assoc,mul_inv_cancel,one_mul,mul_one] using hh
    have hv' : ρ (f (b⁻¹*a)) v = v := by
      have hh := congrArg (fun w : S => ρ (f b⁻¹) w.val) he
      simpa only [j,← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one,
        Module.End.one_apply] using hh
    exact hv0 (hf _ hne v hv')
  have hz : (0 : S) ∉ Set.range j := by
    rintro ⟨a,ha⟩
    have hh := congrArg (fun w : S => ρ (f a⁻¹) w.val) ha
    have hv0' : v = 0 := by
      simpa only [j,← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one,
        Module.End.one_apply,map_zero,ZeroMemClass.coe_zero] using hh
    exact hv0 hv0'
  simpa only [Nat.card_eq_fintype_card] using Fintype.card_lt_of_injective_of_notMem j hj hz

/-- A central fixed-point-free actor group forces every nonzero displacement
space to have at least the binary logarithm of its order plus one. -/
theorem degree_le_displacement
    (ρ : Representation (ZMod 2) G V) (f : A →* G)
    (hf : ∀ a : A, a ≠ 1 → ∀ v, ρ (f a) v = v → v = 0)
    (n : ℕ) (hcard : Nat.card A + 1 = 2 ^ n)
    (y : G) (hcomm : ∀ a : A, Commute (f a) y) (hy : ρ y ≠ 1) :
    n ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ y - LinearMap.id)) := by
  let S := LinearMap.range (ρ y - LinearMap.id)
  have hs (a : A) (v : V) (hv : v ∈ S) : ρ (f a) v ∈ S := by
    obtain ⟨w,rfl⟩ := hv
    refine ⟨ρ (f a) w,?_⟩
    change ρ y (ρ (f a) w) - ρ (f a) w = ρ (f a) (ρ y w - w)
    rw [map_sub]
    have hc := congrArg (fun g => ρ g w) (hcomm a).eq.symm
    simpa only [map_mul,Module.End.mul_apply] using congrArg (fun z => z - ρ (f a) w) hc
  have hn : S ≠ ⊥ := by
    intro hb
    apply hy
    apply LinearMap.ext
    intro v
    have hv : (ρ y - LinearMap.id : Module.End (ZMod 2) V) v ∈ S := ⟨v,rfl⟩
    rw [hb] at hv
    exact sub_eq_zero.mp hv
  have hc := card_lt_of_invariant ρ f hf S hs hn
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := S),Nat.card_zmod] at hc
  apply (pow_le_pow_iff_right₀ (by decide : (1 : ℕ) < 2)).mp
  rw [← hcard]
  exact hc
end Representation.FixedFreeCentralAction
