module

public import Theory.SpecificGroups.Suzuki.SchurEightCover.AtlasModel.Tables

/-!
# Sound Boolean checks on all 2080 points

The Boolean loop avoids constructing a large decidability proof for nested
universal quantifiers. Its soundness is the elementary `List.all` theorem;
all concrete Boolean evaluations are still checked by Lean's kernel.
-/

@[expose] public section
namespace BenderSuzuki.MatrixGroups.SchurEightCover.AtlasModel.Data

def checkPoints (f : Point → Bool) : Bool :=
  (List.range 32).all fun i =>
    (List.range 65).all fun j => f (fromNat (i * 65 + j))

theorem of_checkPoints {P : Point → Prop} [DecidablePred P]
    (h : checkPoints (fun p => decide (P p)) = true) : ∀ p, P p := by
  apply forall_fromNat
  intro i j
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  have hj := List.all_eq_true.mp hi j.val (List.mem_range.mpr j.isLt)
  exact of_decide_eq_true hj

end BenderSuzuki.MatrixGroups.SchurEightCover.AtlasModel.Data
