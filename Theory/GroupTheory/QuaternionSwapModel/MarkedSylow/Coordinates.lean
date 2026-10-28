module
public import Theory.GroupTheory.QuaternionSwapModel.MarkedCubic

/-!
# Finite normal forms for the marked Sylow extension

The 64 quaternion-swap coordinates are extended by an involution that sends
`i` to `ji`, `j` to `-j`, and the factor swap to its product with the marked
central involution. This is a coordinate calculation for the whole Sylow
subgroup, not an identification of the swap subgroup with a parabolic core.
Every involution outside the displayed sixteen has fewer than sixteen
commuting involutions. This census forces all largest elementary subgroups
into the sixteen. The quotient comparison is checked on the covering group.

Source: Aschbacher--Smith, proof of 14.2.21, printed p.988 (PDF p.1005).
-/

@[expose] public section
open QuaternionSwapModel
namespace QuaternionSwapModel.MarkedSylow
abbrev CoreCoordinates := QuaternionGroup 2 × Fin 4 × Bool
abbrev Coordinates := CoreCoordinates × Bool

def rightRep (n : Fin 4) : QuaternionGroup 2 :=
  if n.val < 2 then .a (n.val : ZMod 4) else .xa ((n.val - 2 : ℕ) : ZMod 4)

def raw (n : CoreCoordinates) : Raw :=
  leftRaw n.1 * rightRaw (rightRep n.2.1) * (if n.2.2 then swapRaw else 1)

def quaternionFlip (q : QuaternionGroup 2) : QuaternionGroup 2 :=
  match q with
  | .a n => (QuaternionGroup.xa 1) ^ n.val
  | .xa n => QuaternionGroup.xa 2 * (QuaternionGroup.xa 1) ^ n.val

def twist (w : Raw) : Raw :=
  leftRaw (QuaternionGroup.a 2) ^ w.right.toAdd.val *
    ⟨fun a => quaternionFlip (w.left a), w.right⟩

def productRaw (n m : Coordinates) : Raw :=
  raw n.1 * (if n.2 then twist (raw m.1) else raw m.1)

def Square (n : Coordinates) : Prop := productRaw n n = 1 ∨ productRaw n n = killed
instance (n : Coordinates) : Decidable (Square n) := inferInstanceAs (Decidable (_ ∨ _))
def Commutes (n m : Coordinates) : Prop :=
  (productRaw n m)⁻¹ * productRaw m n = 1 ∨
    (productRaw n m)⁻¹ * productRaw m n = killed
instance (n m : Coordinates) : Decidable (Commutes n m) := inferInstanceAs (Decidable (_ ∨ _))
def InA (n : Coordinates) : Prop := n.2 = false ∧
  (rawWreathMap (raw n.1)).left 1 = (rawWreathMap (raw n.1)).left turn
instance (n : Coordinates) : Decidable (InA n) := inferInstanceAs (Decidable (_ ∧ _))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem census : ∀ n : Coordinates, Square n → ¬ InA n →
    Fintype.card {m : Coordinates // Square m ∧ Commutes n m} < 16 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem raw_injective : ∀ n m : CoreCoordinates,
    (raw n)⁻¹ * raw m = 1 ∨ (raw n)⁻¹ * raw m = killed → n = m := by
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem raw_surjective : ∀ w : Raw, ∃ n : CoreCoordinates,
    (raw n)⁻¹ * w = 1 ∨ (raw n)⁻¹ * w = killed := by
  decide +kernel
end QuaternionSwapModel.MarkedSylow
