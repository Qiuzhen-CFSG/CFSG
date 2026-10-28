module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Fixed points detected by an odd orbit

Multiply the distinct points in an odd orbit of an involution in an abelian
group. The product is fixed by the acting subgroup and by any normalizing
subgroup fixing the original point. Its ratio with the original point lies
in the subgroup containing the displacements. Thus fixed-point detection
on that subgroup detects the original point.

This is the orbit-norm argument used for the final block-centrality step
in Aschbacher–Smith, proof of 15.4.20, printed p.1164.
-/

@[expose] public section

open Subgroup MulAction
open scoped BigOperators

namespace Theory.GroupAction.OddOrbitFixedPoints
variable {A V : Type*} [Group A] [CommGroup V] [Finite V]
variable [MulDistribMulAction A V]

/-- The product of the distinct points in a finite orbit. -/
noncomputable def orbitProduct (L : Subgroup A) (v : V) : V := by
  classical
  let := Fintype.ofFinite V
  let := Fintype.ofFinite (orbit L v)
  exact ∏ w : orbit L v, w.val

/-- Any automorphism preserving the orbit fixes its product. -/
lemma orbitProduct_fixed (L : Subgroup A) (v : V) (a : A)
    (ha : ∀ w ∈ orbit L v, a • w ∈ orbit L v) :
    a • orbitProduct L v = orbitProduct L v := by
  classical
  let := Fintype.ofFinite V
  let := Fintype.ofFinite (orbit L v)
  let f : orbit L v → orbit L v := fun w => ⟨a • w.val, ha w.val w.property⟩
  have hi : Function.Injective f := by
    intro u w h
    exact Subtype.ext ((MulAction.injective a) (congrArg Subtype.val h))
  have hb : Function.Bijective f := ⟨hi, Finite.surjective_of_injective hi⟩
  unfold orbitProduct
  rw [Finset.smul_prod']
  exact Fintype.prod_bijective f hb (fun w => a • w.val) (fun w => w.val) (fun _ => rfl)

lemma orbitProduct_fixed_left (L : Subgroup A) (v : V) (l : L) :
    (l : A) • orbitProduct L v = orbitProduct L v := by
  apply orbitProduct_fixed
  intro w hw
  exact mem_orbit_of_mem_orbit l hw

lemma orbitProduct_fixed_normalizer (L X : Subgroup A) (hXL : X ≤ normalizer L)
    (v : V) (hv : ∀ x : X, (x : A) • v = v) (x : X) :
    (x : A) • orbitProduct L v = orbitProduct L v := by
  apply orbitProduct_fixed
  rintro w ⟨l, rfl⟩
  have hn : (x : A) * (l : A) * (x : A)⁻¹ ∈ L :=
    (hXL x.property l).mp l.property
  refine ⟨⟨_, hn⟩, ?_⟩
  change ((x : A) * (l : A) * (x : A)⁻¹) • v = (x : A) • ((l : A) • v)
  have hi : (x : A)⁻¹ • v = v := by simpa using hv x⁻¹
  simp only [mul_smul, hi]

/-- An odd orbit detects fixed points through a displacement subgroup. -/
lemma fixed_of_odd_orbit (L X : Subgroup A) (hXL : X ≤ normalizer L)
    (D : Subgroup V) (v : V) (hv : ∀ x : X, (x : A) • v = v)
    (hv2 : v ^ 2 = 1) (hodd : Odd (Nat.card (orbit L v)))
    (hdisp : ∀ l : L, ((l : A) • v) / v ∈ D)
    (hfixed : ∀ w ∈ D, (∀ x : X, (x : A) • w = w) →
      ∀ l : L, (l : A) • w = w) :
    ∀ l : L, (l : A) • v = v := by
  classical
  let := Fintype.ofFinite V
  let := Fintype.ofFinite (orbit L v)
  let y := orbitProduct L v
  have hyL (l : L) : (l : A) • y = y := orbitProduct_fixed_left L v l
  have hyX (x : X) : (x : A) • y = y := orbitProduct_fixed_normalizer L X hXL v hv x
  have hD : y / v ∈ D := by
    have hp : (∏ w : orbit L v, w.val / v) ∈ D := by
      apply D.prod_mem
      intro w _
      obtain ⟨l, hl⟩ := w.property
      rw [← hl]
      exact hdisp l
    have hvpow : v ^ Fintype.card (orbit L v) = v := by
      obtain ⟨k, hk⟩ := hodd
      rw [Nat.card_eq_fintype_card] at hk
      rw [hk, pow_add, pow_mul, hv2]
      simp
    change (∏ w : orbit L v, w.val) / v ∈ D
    simpa only [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, hvpow] using hp
  have hf := hfixed (y / v) hD (fun x => by rw [smul_div', hyX, hv])
  intro l
  have he := hf l
  rw [smul_div', hyL] at he
  exact div_right_inj.mp he
end Theory.GroupAction.OddOrbitFixedPoints
