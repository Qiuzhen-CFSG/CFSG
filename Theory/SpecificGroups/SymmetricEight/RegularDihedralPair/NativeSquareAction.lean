module

public import Theory.SpecificGroups.ClassicalOrthogonal.BinaryD3Comparison
public import Theory.SpecificGroups.SymmetricEight.RegularDihedralPair.Order168Model
import all Theory.SpecificGroups.ClassicalOrthogonal.BinaryD3Comparison

/-!
# Explicit coordinates for the native deleted-eight action

The six binary decoder formulas invert the established hyperbolic basis after
subtracting the last coordinate. The quotient calculation identifies this
computable formula with the actual split-six orthogonal action. The local
`import all` is used only to prove the behavior of the frozen, unexposed
`symmetricEquiv`; no private implementation is exposed in a theorem statement.
-/

@[expose] public noncomputable section
open scoped BigOperators
namespace Theory.SpecificGroups.SymmetricEight.RegularDihedralPair.SquareModule
open ClassicalOrthogonal Atlas.Order20160A8

abbrev F := ZMod 2
abbrev D := VectorD 3 F

/-- Coordinates on the even words with last coordinate zero. -/
def decode (w : Fin 8 → F) : D := Sum.elim
  ![w 0 + w 1 + w 2 + w 4, w 1 + w 3 + w 4 + w 5, w 2 + w 3 + w 4]
  ![w 0 + w 1 + w 2 + w 3, w 0 + w 3 + w 4 + w 5, w 0 + w 1 + w 5]

/-- The literal permutation action in the retained hyperbolic coordinates. -/
def nativeAction (g : P8) (v : D) : D :=
  decode (fun i => DeletedEight.raw v (g.symm i) - DeletedEight.raw v (g.symm 7))

private theorem decode_normalized (w : Fin 8 → F) (hw : ∑ i, w i = 0) :
    DeletedEight.raw (decode (fun i => w i - w 7)) = fun i => w i - w 7 := by
  decide +revert +kernel

private theorem split_nativeAction (g : P8) (v : D) :
    DeletedEight.splitMap (nativeAction g v) =
      DeletedEight.quotientPerm g (DeletedEight.splitMap v) := by
  let w := DeletedEight.evenPerm g (DeletedEight.intoEven v)
  have hw : ∑ i, w.val i = 0 := w.property
  have hd := decode_normalized w.val hw
  change (Submodule.Quotient.mk (DeletedEight.intoEven (nativeAction g v)) :
      DeletedEight.W) = Submodule.Quotient.mk w
  apply (Submodule.Quotient.eq DeletedEight.constants).mpr
  apply Submodule.mem_span_singleton.mpr
  refine ⟨-w.val 7, ?_⟩
  apply Subtype.ext
  funext i
  change (-w.val 7) * 1 = DeletedEight.raw (nativeAction g v) i - w.val i
  have hi : DeletedEight.raw (nativeAction g v) i = w.val i - w.val 7 :=
    congrFun hd i
  rw [hi]
  ring

/-- The formula is the genuine S₈ action on the actual split quadratic space. -/
theorem nativeAction_eq (g : P8) (v : D) :
    nativeAction g v = (BinaryD3Comparison.symmetricEquiv g).val v := by
  have he : BinaryD3Comparison.symmetricEquiv g = DeletedEight.orthogonalHom g := rfl
  rw [he]
  apply DeletedEight.splitIsometry.injective
  change DeletedEight.splitMap (nativeAction g v) =
    DeletedEight.splitIsometry (DeletedEight.splitIsometry.symm
      (DeletedEight.quotientPerm g (DeletedEight.splitMap v)))
  rw [DeletedEight.splitIsometry.apply_symm_apply]
  exact split_nativeAction g v

end Theory.SpecificGroups.SymmetricEight.RegularDihedralPair.SquareModule
