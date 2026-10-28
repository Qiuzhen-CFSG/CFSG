module
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Detecting a p-subgroup from two fixed orbit points

A marked point stabilizer is the inverse image of a Sylow normalizer.
If nonidentity Sylow elements separate conjugate normalizers, a p-subgroup
fixing two distinct points in that orbit lies in the marking kernel.
Conjugating the subgroup to the first point puts its image in the Sylow;
the second fixed point then forces every image element to be trivial.
TI Sylows supply the separation condition, without an ambient finite-group
assumption.

The literal linear/Suzuki graph application is DGS85 (12.7), printed p.184,
in CommutingThreeProfile.TwoNeighborCore and PathCoreControl.
-/

public section
open Subgroup
namespace Theory.GroupAction
variable {A B X : Type*} [Group A] [Group B] [MulAction A X]

/-- Two distinct orbit points detect every p-subgroup modulo the marked kernel. -/
theorem pGroup_le_kernel_of_two_fixed
    {p : ℕ} (f : A →* B) (T : Sylow p B) (x : X)
    (hmark : (normalizer (T : Set B)).comap f = MulAction.stabilizer A x)
    (hsep : ∀ t g : B, t ∈ (T : Subgroup B) → t ≠ 1 →
      g * t * g⁻¹ ∈ normalizer (T : Set B) → g ∈ normalizer (T : Set B))
    (D : Subgroup A) (hp : IsPGroup p D) (a b : A)
    (hne : a • x ≠ b • x)
    (ha : D ≤ MulAction.stabilizer A (a • x))
    (hb : D ≤ MulAction.stabilizer A (b • x)) : D ≤ f.ker := by
  let c := f.comp (MulAut.conj a⁻¹).toMonoidHom
  have hcN : D.map c ≤ normalizer (T : Set B) := by
    rintro _ ⟨d, hd, rfl⟩
    change f (a⁻¹ * d * a⁻¹⁻¹) ∈ normalizer (T : Set B)
    have hh : a⁻¹ * d * a ∈ (normalizer (T : Set B)).comap f := by
      rw [hmark]
      change (a⁻¹ * d * a) • x = x
      rw [mul_smul, mul_smul, show d • (a • x) = a • x from ha hd, inv_smul_smul]
    change f (a⁻¹ * d * a) ∈ normalizer (T : Set B) at hh
    simpa only [inv_inv] using hh
  have hcT : D.map c ≤ T := by
    have hh := (hp.map c).inf_normalizer_sylow T
    rw [inf_eq_left.mpr hcN] at hh
    exact hh.le.trans inf_le_right
  intro d hd
  change f d = 1
  by_contra hfd
  have hcd : c d ≠ 1 := by
    intro hh
    have he : f a * c d * (f a)⁻¹ = 1 := by rw [hh, mul_one, mul_inv_cancel]
    change f a * f (a⁻¹ * d * a⁻¹⁻¹) * (f a)⁻¹ = 1 at he
    exact hfd (by simpa only [map_mul, map_inv, inv_inv, mul_assoc,
      mul_inv_cancel_left, mul_inv_cancel_right, mul_inv_cancel, mul_one] using he)
  have hconj : (f (b⁻¹ * a)) * c d * (f (b⁻¹ * a))⁻¹ ∈ normalizer (T : Set B) := by
    have hh : b⁻¹ * d * b ∈ (normalizer (T : Set B)).comap f := by
      rw [hmark]
      change (b⁻¹ * d * b) • x = x
      rw [mul_smul, mul_smul, show d • (b • x) = b • x from hb hd, inv_smul_smul]
    change f (b⁻¹ * d * b) ∈ normalizer (T : Set B) at hh
    change f (b⁻¹ * a) * f (a⁻¹ * d * a⁻¹⁻¹) * (f (b⁻¹ * a))⁻¹ ∈ _
    simpa only [map_mul, map_inv,
      inv_inv, mul_inv_rev, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left] using hh
  have hbm := hsep (c d) (f (b⁻¹ * a)) (hcT (mem_map_of_mem c hd)) hcd hconj
  have hh : b⁻¹ * a ∈ (normalizer (T : Set B)).comap f := hbm
  rw [hmark] at hh
  have hfix : (b⁻¹ * a) • x = x := hh
  exact hne (by simpa only [mul_smul, smul_inv_smul] using congrArg (b • ·) hfix)
end Theory.GroupAction

namespace Sylow
open scoped Pointwise
variable {B : Type*} [Group B] {p : ℕ}

/-- TI Sylows separate their nonidentity elements from conjugate normalizers. -/
theorem mem_normalizer_of_conjugate_mem_of_ti (T : Sylow p B)
    (hti : ∀ P R : Sylow p B, (P : Subgroup B) ⊓ (R : Subgroup B) ≠ ⊥ → P = R)
    (x g : B) (hx : x ∈ (T : Subgroup B)) (hne : x ≠ 1)
    (hconj : g * x * g⁻¹ ∈ normalizer (T : Set B)) :
    g ∈ normalizer (T : Set B) := by
  have hR : g * x * g⁻¹ ∈ ((g • T : Sylow p B) : Subgroup B) := ⟨x, hx, rfl⟩
  have hh : g * x * g⁻¹ ∈ ((g • T : Sylow p B) : Subgroup B) ⊓ normalizer (T : Set B) :=
    ⟨hR, hconj⟩
  rw [(g • T : Sylow p B).isPGroup'.inf_normalizer_sylow T] at hh
  have he : (g • T : Sylow p B) = T := hti _ _ (by
    intro hb
    rw [hb] at hh
    have h1 : g * x * g⁻¹ = 1 := hh
    exact hne (by
      have h2 := congrArg (fun z => g⁻¹ * z * g) h1
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right, mul_one, inv_mul_cancel] using h2))
  exact Sylow.smul_eq_iff_mem_normalizer.mp he
end Sylow
