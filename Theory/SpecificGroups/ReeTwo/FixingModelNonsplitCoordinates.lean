module
public import Theory.SpecificGroups.ReeTwo.FixingModelFirstCoreBasic
public import Theory.SpecificGroups.ReeTwo.SylowCollectedArithmetic

/-!
# Coordinates for the nonsplit fixing extension

Fixing census action 19 is `Core.a`. Explicit polynomials for its powers give
collected multiplication, retaining the last-root carry at exponent four.
The polynomial identities are checked in characteristic two.

Source: Shinoda (1975), pp.81–83, via `SylowCollectedArithmetic` and the
central carry construction in `CyclicFourCentralExtension`.
-/

@[expose] public section
namespace ReeTwo.FixingModel.NonsplitZero
open Core.FixingActionCensus
abbrev G := Model 19 true
abbrev K := firstCore 19 true

theorem action_nineteen : representative 19 = Core.a := by
  apply Core.aut_ext
  intro j
  rw [representative_root]
  exact (by decide +kernel : ∀ j : CoreRoot,
    representativeRoots 19 j = Core.a (Core.root j)) j

def action2 (x : Core) : Core :=
  ⟨x.b0,
    x.b1,
    x.b0 + x.b2,
    x.b0 + x.b3,
    x.b0 + x.b1 + x.b4,
    x.b0 + x.b5,
    x.b0 + x.b0*x.b1 + x.b6,
    x.b0 + x.b0*x.b1 + x.b0*x.b2 + x.b5 + x.b7,
    x.b1 + x.b0*x.b1 + x.b0*x.b2 + x.b1*x.b2 + x.b0*x.b3 + x.b5 + x.b6 + x.b8,
    x.b0 + x.b1 + x.b0*x.b2 + x.b0*x.b3 + x.b0*x.b1*x.b3 + x.b0*x.b4 + x.b5 + x.b9⟩

set_option maxHeartbeats 8000000 in
theorem action2_eq (x : Core) : action2 x = SylowModel.Collected.actionPolynomial (SylowModel.Collected.actionPolynomial x) := by
  apply Core.ext <;> simp only [action2, SylowModel.Collected.actionPolynomial] <;> ring_nf
  all_goals reduce_mod_char
  all_goals simp only [show ∀ z : ZMod 2, z ^ 2 = z from by decide,
    show ∀ z : ZMod 2, z ^ 3 = z from by decide]
  all_goals ring_nf
  all_goals reduce_mod_char

def action3 (x : Core) : Core :=
  ⟨x.b0,
    x.b0 + x.b1,
    x.b1 + x.b2,
    x.b0 + x.b1 + x.b3,
    x.b0 + x.b3 + x.b4,
    x.b0*x.b1 + x.b5,
    x.b0 + x.b1 + x.b5 + x.b6,
    x.b0 + x.b0*x.b2 + x.b1*x.b2 + x.b5 + x.b6 + x.b7,
    x.b0 + x.b0*x.b1 + x.b0*x.b2 + x.b0*x.b3 + x.b1*x.b3 + x.b5 + x.b7 + x.b8,
    x.b1*x.b2 + x.b0*x.b3 + x.b1*x.b3 + x.b0*x.b1*x.b3 + x.b0*x.b1*x.b4 + x.b6 + x.b9⟩

set_option maxHeartbeats 8000000 in
theorem action3_eq (x : Core) : action3 x = SylowModel.Collected.actionPolynomial (action2 x) := by
  apply Core.ext <;> simp only [action3, action2, SylowModel.Collected.actionPolynomial] <;> ring_nf
  all_goals reduce_mod_char
  all_goals simp only [show ∀ z : ZMod 2, z ^ 2 = z from by decide]
  all_goals ring_nf
  all_goals reduce_mod_char

def coordinateAction (t : Fin 4) (x : Core) : Core :=
  if t.val = 0 then x else if t.val = 1 then SylowModel.Collected.actionPolynomial x
  else if t.val = 2 then action2 x else action3 x

theorem coordinateAction_eq (t : Fin 4) (x : Core) :
    coordinateAction t x = (representative 19 ^ t.val) x := by
  rw [action_nineteen]
  fin_cases t <;> simp [coordinateAction, action3_eq, action2_eq,
    SylowModel.Collected.actionPolynomial_eq, pow_succ, MulAut.mul_apply]

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
end ReeTwo.FixingModel.NonsplitZero
