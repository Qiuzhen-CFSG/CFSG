module

public import Theory.GroupTheory.Recognition.TransvectionFive.LocalData
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# The marked inverse-transpose symmetry

Inverse transpose followed by reversal of the ordered basis fixes the
distinguished transvection and reverses every positive root. These symbolic
identities implement the symmetry in Aschbacher, *Sporadic Groups* (1994),
39.1(4), p.213. The subgroup and ambient-marking transports are in
`UniquenessLinearSourceColumn`. Keeping the concrete matrix construction
behind its public equations avoids reducing matrix inverses in those proofs.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear
private def reverseSL : MulAut SL where
  toFun g := ⟨Matrix.reindex (Fin.revPerm : Equiv.Perm (Fin 5)) Fin.revPerm (g : Matrix (Fin 5) (Fin 5) (ZMod 2)),
    (Matrix.det_reindex_self (Fin.revPerm : Equiv.Perm (Fin 5))
      (g : Matrix (Fin 5) (Fin 5) (ZMod 2))).trans g.property⟩
  invFun g := ⟨Matrix.reindex (Fin.revPerm : Equiv.Perm (Fin 5)) Fin.revPerm (g : Matrix (Fin 5) (Fin 5) (ZMod 2)),
    (Matrix.det_reindex_self (Fin.revPerm : Equiv.Perm (Fin 5))
      (g : Matrix (Fin 5) (Fin 5) (ZMod 2))).trans g.property⟩
  left_inv g := by apply Subtype.ext; ext i j; exact congrArg₂ g (Fin.rev_rev i) (Fin.rev_rev j)
  right_inv g := by apply Subtype.ext; ext i j; exact congrArg₂ g (Fin.rev_rev i) (Fin.rev_rev j)
  map_mul' g h := by apply Subtype.ext; exact (Matrix.reindexRingEquiv (ZMod 2) Fin.revPerm).map_mul _ _

private theorem reverseSL_sq (g : SL) : reverseSL (reverseSL g) = g :=
  reverseSL.symm_apply_apply g

private theorem reverseSL_transpose (g : SL) :
    reverseSL (Matrix.SpecialLinearGroup.transpose g) =
      Matrix.SpecialLinearGroup.transpose (reverseSL g) := by
  apply Subtype.ext
  rfl

private abbrev graphSL := BinaryLinear.OuterCyclic.graphSL 5
private theorem graphSL_square (g : SL) : graphSL (graphSL g) = g := by
  have h := congrArg (fun a : MulAut SL => a g) (BinaryLinear.OuterCyclic.graphSL_sq 5)
  simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using h

/-- Inverse transpose followed by reversal preserves the marked point and
interchanges the two ends of its standard flag. -/
def modelDual : MulAut SL := graphSL.trans reverseSL

/-- Reversing the flag twice restores the original matrix. -/
theorem modelDual_square (g : SL) : modelDual (modelDual g) = g := by
  have hc (x : SL) : graphSL (reverseSL x) = reverseSL (graphSL x) := by
    change (Matrix.SpecialLinearGroup.transpose (reverseSL x))⁻¹ =
      reverseSL (Matrix.SpecialLinearGroup.transpose x)⁻¹
    rw [← reverseSL_transpose, map_inv]
  change reverseSL (graphSL (reverseSL (graphSL g))) = g
  rw [hc, graphSL_square, reverseSL_sq]

/-- The positive root at (i,j) goes to the positive root at (4-j,4-i). -/
theorem modelDual_root (i j : Fin 5) (h : i < j) :
    modelDual (root h) = root (Fin.rev_lt_rev.mpr h) := by
  have ht : Matrix.SpecialLinearGroup.transpose (root h) =
      Matrix.SpecialLinearGroup.transvection (ne_of_gt h) (1 : ZMod 2) := by
    apply Subtype.ext
    change (1 + Matrix.single i j (1 : ZMod 2)).transpose = 1 + Matrix.single j i 1
    rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single]
  change reverseSL (Matrix.SpecialLinearGroup.transpose (root h))⁻¹ = _
  rw [ht, Matrix.SpecialLinearGroup.transvection_inv]
  apply Subtype.ext
  change Matrix.reindex Fin.revPerm Fin.revPerm
      (1 + Matrix.single j i (-1 : ZMod 2)) = 1 + Matrix.single j.rev i.rev 1
  ext k l
  change (1 + Matrix.single j i (-1 : ZMod 2)) k.rev l.rev = _
  simp only [show (-1 : ZMod 2) = 1 from rfl, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, Fin.rev_inj]
  have hk : j = k.rev ↔ j.rev = k := by rw [← Fin.rev_inj, Fin.rev_rev]
  have hl : i = l.rev ↔ i.rev = l := by rw [← Fin.rev_inj, Fin.rev_rev]
  simp only [hk, hl]

/-- The distinguished transvection retains its marking. -/
theorem modelDual_point : modelDual transvection = transvection :=
  modelDual_root 0 4 (by decide)

end Theory.GroupTheory.TransvectionFive.UniquenessLinear
