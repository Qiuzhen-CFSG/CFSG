module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part1ResidualReduction

/-!
# Point slices for the dense Rudvalis part-1 group-0 certificates

A permutation identity on 4060 points can be checked on 29 slices of 140
points. Keeping each slice in a separate theorem bounds the memory used by
kernel reduction. This module proves that the slices recover the original
transition check, with no change to its representative or factor word.
Source: the finite transition identities in `OrderLevel0Reduction`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part1Residual.Residual0Checks
open Theory.GroupTheory

@[expose] public def slicePoint (c : Fin 29) (x : Fin 140) : Fin 4060 :=
  ⟨140 * c.val + x.val, by omega⟩

@[expose] public def pointSliceCheck (i : Fin 2) (r : Fin 4060) (c : Fin 29) : Prop :=
  checkFin (fun x : Fin 140 => decide (
    (L0Gen (i.castLE (by decide)) * L0Rep r) (slicePoint c x) =
      (L0Rep (L0Act (i.castLE (by decide)) r) *
        evalWord L1Gen (L0Factor (i.castLE (by decide)) r)) (slicePoint c x))) = true

public instance (i : Fin 2) (r : Fin 4060) (c : Fin 29) :
    Decidable (pointSliceCheck i r c) := inferInstanceAs (Decidable (_ = _))

/-- Independently checked point slices imply the full transition certificate. -/
public theorem ofPointSlices (i : Fin 2) (r : Fin 4060)
    (h : ∀ c : Fin 29, pointSliceCheck i r c) : stepCheck i r := by
  right
  apply (checkFin_spec _).mpr
  intro x
  let c : Fin 29 := ⟨x.val / 140, by omega⟩
  let y : Fin 140 := ⟨x.val % 140, by omega⟩
  have hxy : slicePoint c y = x := by
    apply Fin.ext
    dsimp [slicePoint, c, y]
    omega
  have hp := (checkFin_spec _).mp (h c) y
  change decide ((L0Gen (i.castLE (by decide)) * L0Rep r) (slicePoint c y) =
    (L0Rep (L0Act (i.castLE (by decide)) r) *
      evalWord L1Gen (L0Factor (i.castLE (by decide)) r)) (slicePoint c y)) = true at hp
  simpa only [hxy] using hp

end Rudvalis.OrderCertificate.ForwardReduction.Part1Residual.Residual0Checks
