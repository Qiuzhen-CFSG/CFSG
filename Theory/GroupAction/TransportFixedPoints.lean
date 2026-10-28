module
public import Mathlib.Algebra.Group.Action.TransferInstance
public import Mathlib.GroupTheory.GroupAction.FixedPoints
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Fixed points under transport of an action

An equivalence of the underlying sets transports a monoid action and identifies
the fixed points of each element. In particular, their natural cardinalities
are unchanged. This is useful when replacing a finite action by one on `Fin n`.
-/

noncomputable section

namespace Equiv
variable {G X Y : Type*} [Monoid G] [MulAction G X]

/-- Fixed-point sets agree under the action transported along an equivalence. -/
public def fixedByMulActionEquiv (e : Y ≃ X) (g : G) :
    letI := e.mulAction G
    MulAction.fixedBy Y g ≃ MulAction.fixedBy X g := by
  letI := e.mulAction G
  exact {
    toFun := fun y => ⟨e y, by
      have h := congrArg e y.property
      simpa [Equiv.smul_def] using h⟩
    invFun := fun x => ⟨e.symm x, by
      change e.symm (g • e (e.symm x)) = e.symm x
      rw [e.apply_symm_apply, x.property]⟩
    left_inv := fun y => Subtype.ext (e.symm_apply_apply y)
    right_inv := fun x => Subtype.ext (e.apply_symm_apply x) }

/-- Transporting an action preserves every fixed-point count. -/
public theorem card_fixedBy_mulAction (e : Y ≃ X) (g : G) :
    letI := e.mulAction G
    Nat.card (MulAction.fixedBy Y g) = Nat.card (MulAction.fixedBy X g) :=
  Nat.card_congr (e.fixedByMulActionEquiv g)
end Equiv
