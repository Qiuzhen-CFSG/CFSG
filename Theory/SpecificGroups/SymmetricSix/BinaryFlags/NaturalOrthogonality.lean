module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing

/-!
# Fixation and displacement in the binary natural pairing

An isometry fixes a subspace pointwise precisely when every displacement
lies in its perpendicular. Invariance proves the forward direction;
nondegeneracy and invertibility recover fixation in the converse.
This uses the actual natural six-letter quotient and coordinate action.

Source: Aschbacher–Smith,13.7.3(6), printed p.936, applied to the source
line and hyperplane. No finite subgroup enumeration is used.
-/

@[expose] public section
open BinaryPermutation
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalOrthogonality
open NaturalPairing

/-- Pointwise fixation and perpendicular displacement are dual for the actual natural action. -/
theorem fixes_iff_displacement (g : Equiv.Perm (Fin 6))
    (P : Submodule (ZMod 2) (natural (Fin 6))) :
    (∀ x ∈ P, naturalRepresentation (Fin 6) g x = x) ↔
      ∀ v, naturalRepresentation (Fin 6) g v - v ∈ form.orthogonal P := by
  constructor
  · intro hf v x hx
    have h := form_invariant g x v
    rw [hf x hx] at h
    change form x (naturalRepresentation (Fin 6) g v - v) = 0
    rw [map_sub, h, sub_self]
  · intro hd x hx
    apply sub_eq_zero.mp
    apply form_nondegenerate.1
    intro y
    let v := naturalRepresentation (Fin 6) g⁻¹ y
    have he : naturalRepresentation (Fin 6) g v = y := by
      change naturalRepresentation (Fin 6) g (naturalRepresentation (Fin 6) g⁻¹ y) = y
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have h := hd v x hx
    change form x (naturalRepresentation (Fin 6) g v - v) = 0 at h
    rw [map_sub, he, sub_eq_zero] at h
    have hp := form_invariant g x v
    rw [he] at hp
    change form (naturalRepresentation (Fin 6) g x - x) y = 0
    rw [map_sub, LinearMap.sub_apply, hp, h, sub_self]

end Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalOrthogonality
