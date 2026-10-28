module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.HolomorphGeometry.Coordinates

/-!
# The marked semidihedral subgroup of the A₆ Sylow holomorph

An SD16 pair whose subgroup contains the inner reflection lies in the
subgroup with even cyclic coordinate over multipliers 1 and 7 and odd
cyclic coordinate over multipliers 3 and 5. Its displayed normal forms map
into the literal M₁₀ extension. The reflection marking excludes the other
SD16 subgroup, whose multipliers are 1 and 3.

All computations are on the 32-element holomorph and checked by the kernel.
Source: Aschbacher–Smith, J.2.7, printed p.435 (PDF p.446).
-/

@[expose] public section
open Subgroup
namespace AlternatingSix.M10.SylowRecognition.Coordinates
open AlternatingSix.ShadowLocal.Holomorph

def selected : Subgroup Model where
  carrier := {x | x.left.toAdd.val % 2 = if (x.right : ZMod 8) = 1 ∨ (x.right : ZMod 8) = 7 then 0 else 1}
  one_mem' := by decide +kernel
  mul_mem' := by decide +kernel
  inv_mem' := by decide +kernel
instance instDecidableMemSelected : DecidablePred (· ∈ selected) := fun x =>
  inferInstanceAs (Decidable (x.left.toAdd.val % 2 =
    if (x.right : ZMod 8) = 1 ∨ (x.right : ZMod 8) = 7 then 0 else 1))

theorem selected_normal_form (x : Model) (hx : x ∈ selected) :
    ∃ (i : Fin 4) (j k : Fin 2),
      x = (rotation ^ 2) ^ i.val * reflection ^ j.val * (rotation * transposition) ^ k.val := by
  revert x
  decide +kernel

theorem generators_selected (x y : Model) (hx : x ^ 4 ≠ 1) (hy : y ^ 2 = 1)
    (hxy : y * x * y⁻¹ = x ^ 3)
    (hc : ∃ (i : Fin 8) (j : Fin 2), reflection = x ^ i.val * y ^ j.val) :
    x ∈ selected ∧ y ∈ selected := by
  revert x y
  decide +kernel
end AlternatingSix.M10.SylowRecognition.Coordinates
