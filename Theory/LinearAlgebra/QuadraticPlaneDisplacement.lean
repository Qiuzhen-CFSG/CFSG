module
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic

/-!
# Small elementary actors on a binary quadratic space

An elementary group of isometries with movement in a plane and no nonidentity
rank-one actor has order at most two. Every nonidentity displacement fills the
plane and has its orthogonal complement as kernel. The plane is polar-isotropic,
so the quadratic form restricts to a linear form. A suitable vector outside the
common fixed space distinguishes all actors, while the quadratic equation puts
its displacements in one line of the plane. That line has two elements.

Source application: the equality case for the orthogonal six-space in
Aschbacher–Smith, *The Classification of Quasithin Groups*, 13.8.32,
printed p.965. The result applies to any binary polar-nondegenerate quadratic
space and does not use an enumeration of its isometry group.
-/

public section
open Module
namespace QuadraticForm
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- A binary elementary group of orthogonal isometries with displacement in a
plane and no nontrivial rank-one actor has order at most two. -/
theorem card_le_two_of_plane_displacement
    {A : Type*} [Group A] [Finite A]
    (q : QuadraticForm (ZMod 2) V) (hq : q.polarBilin.Nondegenerate)
    (ρ : A →* (V ≃ₗ[ZMod 2] V))
    (hsq : ∀ a : A, a ^ 2 = 1)
    (hiso : ∀ a x, q (ρ a x) = q x)
    (hlower : ∀ a : A, a ≠ 1 →
      2 ≤ finrank (ZMod 2) ((ρ a).toLinearMap - LinearMap.id).range)
    (P : Submodule (ZMod 2) V) (hP : finrank (ZMod 2) P = 2)
    (hmove : ∀ a : A, ((ρ a).toLinearMap - LinearMap.id).range ≤ P) :
    Nat.card A ≤ 2 := by
  classical
  let : Finite V := Module.finite_of_finite (ZMod 2)
  have hneg (v : V) : -v = v := neg_eq_iff_add_eq_zero.mpr (ZModModule.add_self v)
  let B : LinearMap.BilinForm (ZMod 2) V := q.polarBilin
  let N (a : A) := (ρ a).toLinearMap - LinearMap.id
  have hs (x y : V) : B x y = B y x := QuadraticMap.polar_comm q x y
  have hi (a : A) (x y : V) : B (ρ a x) (ρ a y) = B x y := by
    change q (ρ a x + ρ a y) - q (ρ a x) - q (ρ a y) = _
    rw [← map_add, hiso, hiso, hiso]
    rfl
  have htwo (a : A) (x : V) : ρ a (ρ a x) = x := by
    have hh := congrArg (fun t : A => ρ t x) (hsq a)
    simpa only [pow_two, map_mul, LinearEquiv.mul_apply, map_one,
      LinearEquiv.coe_one, id_eq] using hh
  have hrange (a : A) (ha : a ≠ 1) : (N a).range = P := by
    apply Submodule.eq_of_le_of_finrank_le (hmove a)
    rw [hP]
    exact hlower a ha
  have hfixed (a : A) (ha : a ≠ 1) (x : V) :
      ρ a x = x ↔ x ∈ B.orthogonal P := by
    rw [← hrange a ha]
    constructor
    · intro hx y hy
      obtain ⟨z,rfl⟩ := hy
      change B (ρ a z - z) x = 0
      rw [map_sub, LinearMap.sub_apply]
      exact sub_eq_zero.mpr (by simpa only [hx] using hi a z x)
    · intro hx
      apply sub_eq_zero.mp
      apply hq.2
      intro z
      have hz := hx (N a z) (LinearMap.mem_range_self _ _)
      have he : B (ρ a z) x = B z (ρ a x) := by
        rw [← htwo a x, hi, htwo]
      change B (ρ a z - z) x = 0 at hz
      simp only [map_sub, LinearMap.sub_apply] at hz ⊢
      rwa [he] at hz
  by_cases htriv : ∀ a : A, a = 1
  · let : Subsingleton A := ⟨fun a b => (htriv a).trans (htriv b).symm⟩
    have hh : Nat.card A = 1 := by simp
    omega
  push Not at htriv
  obtain ⟨a,ha⟩ := htriv
  have hPP (x y : P) : B x y = 0 := by
    have hy : (y : V) ∈ (N a).range := (hrange a ha).symm ▸ y.property
    obtain ⟨z,hz⟩ := hy
    have hfy : ρ a (y : V) = y := by
      rw [← hz]
      change ρ a (ρ a z - z) = ρ a z - z
      rw [map_sub, htwo]
      simp only [sub_eq_add_neg, hneg, add_comm]
    exact (hfixed a ha y).mp hfy x x.property
  let r : P →ₗ[ZMod 2] ZMod 2 := {
    toFun x := q x
    map_add' x y := by
      change q ((x : V) + y) = _
      rw [QuadraticMap.map_add q]
      change _ + B x y = _
      rw [hPP, add_zero]
    map_smul' c x := by
      change q (c • (x : V)) = c * q x
      rw [q.map_smul, smul_eq_mul]
      have hc : c = 0 ∨ c = 1 := (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c
      rcases hc with rfl | rfl <;> simp }
  obtain ⟨ℓ,hℓ,hℓr⟩ : ∃ ℓ : Module.Dual (ZMod 2) P, ℓ ≠ 0 ∧ ℓ ≠ r := by
    by_contra! hh
    let f : Bool → Module.Dual (ZMod 2) P := fun b => if b then r else 0
    have hf : Function.Surjective f := by
      intro ℓ
      by_cases hz : ℓ = 0
      · exact ⟨false,hz.symm⟩
      · exact ⟨true,(hh ℓ hz).symm⟩
    have hc := Nat.card_le_card_of_surjective f hf
    have hd : Nat.card (Module.Dual (ZMod 2) P) = 4 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
        Subspace.dual_finrank_eq, hP]
      decide
    simp only [Nat.card_eq_fintype_card, Fintype.card_bool] at hc
    rw [hd] at hc
    omega
  let z : V := (B.toDual hq).symm (Subspace.dualLift P ℓ)
  have hz (x : P) : B z x = ℓ x := by
    simp only [z, LinearMap.BilinForm.apply_toDual_symm_apply, Subspace.dualLift_of_subtype]
  have hzout : z ∉ B.orthogonal P := by
    intro hh
    apply hℓ
    ext x
    rw [← hz, hs]
    exact hh x x.property
  let m : P →ₗ[ZMod 2] ZMod 2 := r - ℓ
  have hm : m ≠ 0 := fun hh => hℓr (sub_eq_zero.mp hh).symm
  have hker : Nat.card m.ker ≤ 2 := by
    have hd := m.finrank_range_add_finrank_ker
    have hpos : 0 < finrank (ZMod 2) m.range := by
      apply Nat.pos_of_ne_zero
      intro he
      exact hm (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp he))
    have hdker : finrank (ZMod 2) m.ker ≤ 1 := by omega
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact Nat.pow_le_pow_right (by decide) hdker
  let f (b : A) : m.ker := ⟨⟨N b z,hmove b (LinearMap.mem_range_self _ _)⟩, by
    change q (ρ b z - z) - ℓ ⟨N b z,hmove b (LinearMap.mem_range_self _ _)⟩ = 0
    rw [← hz]
    change q (ρ b z - z) - B z (ρ b z - z) = 0
    have hh := hiso b z
    have he : ρ b z = z + (ρ b z - z) := by abel
    rw [he, QuadraticMap.map_add q] at hh
    change q z + q (ρ b z - z) + B z (ρ b z - z) = q z at hh
    simpa only [sub_eq_add_neg, CharTwo.neg_eq] using (add_left_cancel
      (show q z + (q (ρ b z - z) + B z (ρ b z - z)) = q z + 0 by
        simpa only [add_assoc, add_zero] using hh) : q (ρ b z - z) + B z (ρ b z - z) = 0)⟩
  have hf : Function.Injective f := by
    intro b c he
    have hzsame : ρ b z = ρ c z := sub_left_inj.mp (congrArg (fun x : m.ker => (x : P).val) he)
    by_contra hbc
    have hne : c⁻¹ * b ≠ 1 := by
      intro hh
      have he := congrArg (fun x : A => c * x) hh
      exact hbc (by simpa only [mul_inv_cancel_left, mul_one] using he)
    have hh : ρ (c⁻¹ * b) z = z := by
      rw [map_mul, LinearEquiv.mul_apply, hzsame, ← LinearEquiv.mul_apply, ← map_mul,
        inv_mul_cancel, map_one, LinearEquiv.coe_one, id_eq]
    exact hzout ((hfixed _ hne z).mp hh)
  exact (Nat.card_le_card_of_injective f hf).trans hker

end QuadraticForm
