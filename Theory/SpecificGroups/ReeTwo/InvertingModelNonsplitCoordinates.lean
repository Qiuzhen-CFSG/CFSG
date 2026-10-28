module
public import Theory.SpecificGroups.ReeTwo.InvertingModelFirstCoreBasic
public import Theory.SpecificGroups.ReeTwo.RootTwistedCoordinates

/-!
# Coordinates for the nonsplit root-twisted extension

Census action 19 is the root-twisted action. Its polynomial formulas give
collected multiplication with an additional last-root carry at actor exponent
four. These coordinates retain the nonsplit fourth-power relation.

Source: Shinoda (1975), pp.81–83, via `RootTwistedCoordinates`, and the central
carry construction in `CyclicFourCentralExtension`.
-/

@[expose] public section
namespace ReeTwo.InvertingModel.NonsplitZero
open Core.InvertingActionCensus
abbrev G := Model 19 true
abbrev K := firstCore 19 true

theorem action_nineteen : representative 19 = Core.rootTwist * Core.a := by
  apply Core.aut_ext
  intro j
  rw [representative_root]
  exact (by decide +kernel : ∀ j : CoreRoot,
    representativeRoots 19 j = (Core.rootTwist * Core.a) (Core.root j)) j

def coordinateAction (t : Fin 4) (x : Core) : Core :=
  RootTwistedSylow.coordinateAction (Multiplicative.ofAdd (t.val : ZMod 4)) x

theorem coordinateAction_eq (t : Fin 4) (x : Core) :
    coordinateAction t x = (representative 19 ^ t.val) x := by
  rw [coordinateAction, RootTwistedSylow.coordinateAction_eq, action_nineteen]
  change ((Core.rootTwist * Core.a) ^ (t.val : ZMod 4).val) x = _
  rw [ZMod.val_natCast_of_lt t.isLt]

def coordinateMul (x y : G) : G :=
  ⟨x.core * coordinateAction x.idx y.core * Core.root 9 ^ ((x.idx.val + y.idx.val) / 4),
    ⟨(x.idx.val + y.idx.val) % 4, Nat.mod_lt _ (by decide)⟩⟩

theorem coordinateMul_eq_mul (x y : G) : coordinateMul x y = x * y := by
  apply CyclicFourCentralExtension.Model.ext
  · exact congrArg (fun q => x.core * q * Core.root 9 ^ ((x.idx.val + y.idx.val) / 4))
      (coordinateAction_eq x.idx y.core)
  · rfl

def root (i : CoreRoot) : G := CyclicFourCentralExtension.embed (Core.root i)
def actor : G := CyclicFourCentralExtension.actor
end ReeTwo.InvertingModel.NonsplitZero
