module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.MiddleParabolic.Coordinates

/-!
# The four coordinate roots for the seed calculation

The existing actors 1, 3, and 5 are respectively I+E₀₁, I+E₁₃,
and I+E₁₂. The new central root is I+E₀₃. Their conjugation and
commutation identities are checked on the actual binary four-space.
A single pullback equivalence preserves the chosen head identification
and an adapted flag basis in every later root calculation.

Source: the root calculation in Aschbacher–Smith, *The Classification
of Quasithin Groups*, 13.8.25, printed p.962 (PDF p.979).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking.RootSeed
open BinaryLinear BinaryLinear.MiddleParabolic

def centralRoot : BinaryLinear.GL V :=
  transvection (Pi.single 0 1) (LinearMap.proj 3) (by simp)

theorem centralRoot_apply (v : V) : centralRoot v = ![v 0 + v 3, v 1, v 2, v 3] := by
  ext i
  fin_cases i <;> simp [centralRoot, transvection]

theorem root_conjugation : actor 3 * actor 1 * (actor 3)⁻¹ = centralRoot * actor 1 := by
  have he : ∀ v : V, actorFun 3 (actorFun 1 (actorFun 3 v)) =
      ![(actorFun 1 v) 0 + (actorFun 1 v) 3,
        (actorFun 1 v) 1, (actorFun 1 v) 2, (actorFun 1 v) 3] := by decide +kernel
  ext v i
  simpa only [LinearEquiv.mul_apply, actor_inv, actor_apply, centralRoot_apply] using congrFun (he v) i

theorem shear_commutes_centralRoot : actor 5 * centralRoot = centralRoot * actor 5 := by
  have he : ∀ v : V, actorFun 5 ![v 0 + v 3, v 1, v 2, v 3] =
      ![(actorFun 5 v) 0 + (actorFun 5 v) 3,
        (actorFun 5 v) 1, (actorFun 5 v) 2, (actorFun 5 v) 3] := by decide +kernel
  ext v i
  simpa only [LinearEquiv.mul_apply, actor_apply, centralRoot_apply] using congrFun (he v) i

/-- Pull back the four root actors along the fixed head coordinates and one adapted
flag basis. This is a single group equivalence for every subsequent calculation. -/
def flagPullback {H : Type*} [Group H] (eH : H ≃* BinaryLinear.GL V)
    (c : BinaryLinear.GL V) : BinaryLinear.GL V ≃* H :=
  (MulAut.conj c).trans eH.symm

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking.RootSeed
