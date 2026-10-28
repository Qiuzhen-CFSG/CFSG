module

public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Calculation
import Mathlib.Tactic
/-!
# Binary coordinates for the duad cores

Two independent double transpositions give coordinates on the Klein four
group. Adding the swap on the two-letter block gives coordinates on the
eight-group. The finite homomorphism and bijectivity checks are kernel checked.

These are the elementary abelian parabolic cores used in Aschbacher–Smith,
*The Classification of Quasithin Groups*, I.5.7, printed pp. 420–421.
-/

@[expose] public section

namespace Theory.SpecificGroups.SymmetricSix.DuadCalculation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

local instance : DecidablePred (· ∈ productCore) := fun x =>
  inferInstanceAs (Decidable (True ∧ quotientHom x.2 = 1))

/-- Binary coordinates on the four-group, using two double transpositions. -/
def binaryFourHom : Multiplicative (Fin 2 → ZMod 2) →* Four where
  toFun v := (if v.toAdd 0 = 0 then 1 else doubleSwap 0) *
    (if v.toAdd 1 = 0 then 1 else doubleSwap 1)
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

def binaryFourToCore : Multiplicative (Fin 2 → ZMod 2) →* core :=
  binaryFourHom.codRestrict _ (by decide +kernel)

noncomputable def binaryFourEquiv : Multiplicative (Fin 2 → ZMod 2) ≃* core :=
  MulEquiv.ofBijective binaryFourToCore (by decide +kernel)

/-- Binary coordinates on the eight-group: first the two-letter swap, then
  two independent double transpositions on the complementary four letters. -/
def binaryEightHom : Multiplicative (Fin 3 → ZMod 2) →* (Two × Four) where
  toFun v := (if v.toAdd 0 = 0 then 1 else Equiv.swap 0 1,
    (if v.toAdd 1 = 0 then 1 else doubleSwap 0) *
    (if v.toAdd 2 = 0 then 1 else doubleSwap 1))
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

def binaryEightToCore : Multiplicative (Fin 3 → ZMod 2) →* productCore :=
  binaryEightHom.codRestrict _ (by decide +kernel)

noncomputable def binaryEightEquiv : Multiplicative (Fin 3 → ZMod 2) ≃* productCore :=
  MulEquiv.ofBijective binaryEightToCore (by decide +kernel)
end Theory.SpecificGroups.SymmetricSix.DuadCalculation
