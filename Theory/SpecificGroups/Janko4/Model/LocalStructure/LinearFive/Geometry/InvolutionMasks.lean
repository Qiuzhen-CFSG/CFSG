module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Geometry.KernelOrbit

/-!
# Reduced kernel masks for involutions in Q

Removing the six known common-fixed coordinates leaves five bits. For each
nonzero quotient coordinate, the fixed reduced masks give either F or its
seed conjugate. These bounded equations are checked against the actual native
lift actions, for the occurrence calculation in KW (1988), Lemma 1.1.2(ii).
-/
@[expose] public section
namespace Janko4.LocalStructure.LinearFive.Geometry
open Cardinality KernelCount QuotientCount.Image Subgroup
open Simplicity.Max1Fusion.KernelOrbits

def kernelPartMask (m : ℕ) : ℕ :=
  (List.ofFn (fun j : Fin 6 => if m.testBit (j.val + 5) then kernelMasks j else 0)).foldr Nat.xor 0

def reducedMask (m : ℕ) : ℕ := Nat.xor m (kernelPartMask m)

set_option maxRecDepth 10000 in
theorem reducedMask_lt : ∀ m : Fin 2048, reducedMask m.val < 32 := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem reduced_action_lt : ∀ (v : Fin 4 → Bool) (m : Fin 32), liftAction v m.val < 2048 := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem reduced_involution_masks : ∀ (v : Fin 4 → Bool) (m : Fin 32),
    v ≠ (fun _ => false) → liftAction v m.val = m.val →
      m.val = 0 ∨ ∀ i : Fin 4,
        maskImage (liftKernelMasks i) (Nat.xor m.val (Nat.xor (liftAction v 1) 1)) =
          Nat.xor m.val (Nat.xor (liftAction v 1) 1) := by
  decide +kernel

end Janko4.LocalStructure.LinearFive.Geometry
