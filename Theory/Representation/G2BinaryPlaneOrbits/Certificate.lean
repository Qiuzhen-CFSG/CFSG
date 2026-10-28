module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fin.VecNotation

/-!
# A finite binary Sylow plane certificate

The three displayed linear operators are the six off-diagonal actions of the
positive-root tuples (0,0,0,1,0,1), (1,1,1,0,0,1), and (0,0,0,0,1,0).
If a binary span of at most two vectors is invariant under all three, all four
last coordinates vanish. The 64-by-64 check uses ordinary kernel reduction.
The connection to actual derived-group elements is proved in `Sylow`.

This is the finite calculation for the plane geometry in Aschbacher–Smith,
printed p.1132 (PDF p.1149), C.1.30 and B.5.3–6. Root conventions are inherited
from the attributed ATLAS port; see LICENSES/ATLAS.txt.
-/

@[expose] public section
namespace Atlas.G2.Natural.BinaryPlane.SylowCoordinates
abbrev Six := Fin 6 → ZMod 2
def stepS (x : Six) : Six := ![x 0+x 1+x 2+x 3, x 1+x 4+x 5, x 2+x 3, x 3+x 5, x 4+x 5, x 5]
def stepT (x : Six) : Six := ![x 0+x 1+x 3+x 4, x 1+x 3+x 5, x 2+x 3+x 4, x 3, x 4+x 5, x 5]
def stepZ (x : Six) : Six := ![x 0, x 1+x 2, x 2, x 3+x 4, x 4, x 5]
def inPair (x y z : Six) : Prop := z = 0 ∨ z = x ∨ z = y ∨ z = x+y
instance (x y z : Six) : Decidable (inPair x y z) := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))
set_option synthInstance.maxSize 1024 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem certificate : ∀ x y : Six,
    inPair x y (stepS x) → inPair x y (stepS y) →
    inPair x y (stepT x) → inPair x y (stepT y) →
    inPair x y (stepZ x) → inPair x y (stepZ y) →
    x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0 ∧
    y 2 = 0 ∧ y 3 = 0 ∧ y 4 = 0 ∧ y 5 = 0 := by
  unfold inPair
  decide +kernel
end Atlas.G2.Natural.BinaryPlane.SylowCoordinates
