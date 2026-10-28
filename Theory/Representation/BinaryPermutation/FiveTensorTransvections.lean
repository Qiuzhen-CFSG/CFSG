module

public import Theory.Representation.BinaryPermutation.FiveTensorTransvections.Coordinates
public import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# No transvections on the natural binary S₅ × S₃ tensor module

The finite coordinate certificate detects two distinct nonzero displacements
for every nonidentity pair of permutations. A binary rank-one displacement
has only one nonzero value, so the certificate excludes it. An actual
 equivariant linear equivalence transports the calculation to any module
with these group coordinates, including the literal source quotient.

Source: Aschbacher–Smith 13.8.18(4) and the S₅ × S₃ branch of 13.8.20,
printed pp.953–954 (combined manuscript, 1 March 2004).
-/

@[expose] public section
namespace BinaryPermutation.FiveTensorTransvections
open TensorProduct FiveTensorQuadratic Coordinates
/-- The external tensor product of the two even-weight permutation cores. -/
abbrev Space := BinaryPermutation.core (Fin 5) ⊗[ZMod 2] BinaryPermutation.core (Fin 3)
/-- The specified S₅ × S₃ action, acting in the two tensor factors. -/
noncomputable abbrev action := tensorAction (BinaryPermutation.coreRepresentation (Fin 3))

private def coordinates : Space →ₗ[ZMod 2] (Fin 5 × Fin 3 → ZMod 2) :=
  TensorProduct.lift
    { toFun := fun v =>
        { toFun := fun w ij => v.val ij.1 * w.val ij.2
          map_add' := by intros; ext; simp [mul_add]
          map_smul' := by intros; ext; simp [mul_left_comm] }
      map_add' := by intros; ext; simp [add_mul]
      map_smul' := by intros; ext; simp [mul_assoc] }

private theorem coordinates_delta (g : Equiv.Perm (Fin 5)) (h : Equiv.Perm (Fin 3))
    (ij : Fin 4 × Fin 2) :
    coordinates (action (g,h) (coreVector 4 ij.1 ⊗ₜ[ZMod 2] coreVector 2 ij.2) -
      (coreVector 4 ij.1 ⊗ₜ[ZMod 2] coreVector 2 ij.2)) = delta g h ij := by
  rw [map_sub]
  rfl

variable {H V : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]
  [Module.Finite (ZMod 2) V]

/-- An element moving at most one binary dimension must be the identity. -/
theorem eq_one_of_displacement_le_one
    (e : H ≃* Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3))
    (ρ : Representation (ZMod 2) H V) (f : V ≃ₗ[ZMod 2] Space)
    (heq : ∀ g v, f (ρ g v) = action (e g) (f v))
    (g : H) (hg : Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) ≤ 1) :
    g = 1 := by
  let t : V ≃ₗ[ZMod 2] V :=
    LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V (ρ.asGroupHom g)
  obtain ⟨φ, v, ht⟩ := LinearEquiv.mem_dilatransvections_iff_finrank.mpr (show
    Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) ≤ 1 from hg)
  have hd (x : V) : ρ g x - x = φ x • v := by
    have hx := congrArg (fun l : V →ₗ[ZMod 2] V => l x) ht
    change ρ g x = _ at hx
    rw [hx, LinearMap.transvection.apply, add_sub_cancel_left]
  have binary (a : ZMod 2) : a = 0 ∨ a = 1 := (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a
  have small (z : Space) : action (e g) z - z = 0 ∨ action (e g) z - z = f v := by
    obtain ⟨x, rfl⟩ := f.surjective z
    have h := congrArg f (hd x)
    rw [map_sub, heq, map_smul] at h
    rcases binary (φ x) with hz | ho
    · left; simpa [hz] using h
    · right; simpa [ho] using h
  have htest : ∀ i j, delta (e g).1 (e g).2 i = 0 ∨
      delta (e g).1 (e g).2 j = 0 ∨
      delta (e g).1 (e g).2 i = delta (e g).1 (e g).2 j := by
    intro i j
    rw [← coordinates_delta, ← coordinates_delta]
    rcases small (coreVector 4 i.1 ⊗ₜ[ZMod 2] coreVector 2 i.2) with hi | hi
    · left; rw [Prod.eta, hi, map_zero]
    rcases small (coreVector 4 j.1 ⊗ₜ[ZMod 2] coreVector 2 j.2) with hj | hj
    · right; left; rw [Prod.eta, hj, map_zero]
    · right; right; rw [Prod.eta, hi, hj]
  have he := displacement_test (e g).1 (e g).2 htest
  apply e.injective
  rw [map_one]
  exact Prod.ext he.1 he.2

/-- No element induces a nonidentity transvection: displacement rank is never one. -/
theorem no_transvection
    (e : H ≃* Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3))
    (ρ : Representation (ZMod 2) H V) (f : V ≃ₗ[ZMod 2] Space)
    (heq : ∀ g v, f (ρ g v) = action (e g) (f v)) (g : H) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) ≠ 1 := by
  intro hr
  have hg := eq_one_of_displacement_le_one e ρ f heq g hr.le
  rw [hg, map_one] at hr
  change Module.finrank (ZMod 2) (LinearMap.range (1 - 1 : V →ₗ[ZMod 2] V)) = 1 at hr
  rw [sub_self, LinearMap.range_zero, finrank_bot] at hr
  exact Nat.zero_ne_one hr
end BinaryPermutation.FiveTensorTransvections

end
