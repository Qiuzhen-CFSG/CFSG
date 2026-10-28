module
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates.Packed
/-!
# Sequential packed matrix certificates

This checker scans right-hand rows and successive bits of a left-hand row.
Its correctness is the equality with `packedRow`, and hence the existing
`decode_packedMul` theorem. It avoids repeated indexed lookup during reduction.

Adapted from `Cardinality/LocalOrder/QuotientCount/UpperBound/RelatorCertificates/
FastArithmetic.lean`, itself adapted from the proved checker in
`Model/Simplicity/PrimeCoverage/Elevens/RepresentativeBridges/Checker.lean`.
-/
@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.Relators
open Janko4.GeneratorCertificates
def fastRow : ℕ → List ℕ → ℕ
| _, [] => 0
| x, y :: ys => (if x.testBit 0 then y else 0) ^^^ fastRow (x >>> 1) ys
lemma fastRow_ofFn {n : ℕ} (x : ℕ) (f : Fin n → ℕ) :
    fastRow x (List.ofFn f) =
      xorList (List.ofFn (fun i => if x.testBit i.val then f i else 0)) := by
  induction n generalizing x with
  | zero => simp [fastRow, xorList]
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, fastRow, xorList, ih]
    congr 1
    apply congrArg xorList
    apply congrArg List.ofFn
    funext i
    simp [Nat.testBit_shiftRight, Nat.add_comm]

lemma vector_ofFn_list (v : Vector ℕ 112) : List.ofFn v.get = v.toList := by
  have hv : Vector.ofFn v.get = v := Vector.ofFn_getElem
  exact Vector.toList_ofFn.symm.trans (congrArg Vector.toList hv)

lemma fastRow_eq (x : ℕ) (v : Vector ℕ 112) : fastRow x v.toList = packedRow x v := by
  rw [← vector_ofFn_list, fastRow_ofFn]
  rfl

theorem packed_of_list (xs ys zs : Vector ℕ 112)
    (h : xs.toList.map (fun x => fastRow x ys.toList) = zs.toList) :
    packedMul xs ys = zs := by
  apply packedMul_eq_of_rows
  intro i
  have e := congrArg (fun l : List ℕ => l[i.val]?) h
  simpa [List.getElem?_map, Vector.getElem?_toList, i.isLt, fastRow_eq, Vector.get] using e

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.Relators
