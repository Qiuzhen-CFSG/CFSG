module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.PullbackCoefficients.PackedTable.Contracts

/-!
# List traversal for the packed input certificates

The column test compares every bit with the unchanged source row arrays.
The image test multiplies each candidate form by scanning the selected packed
coefficient rows with XOR. The soundness proofs identify these list traversals
with exactly `ColumnCheck` and `ImageCheck`; they impose no calibration premise.

The traversal avoids repeated indexing into the large literal arrays during
kernel reduction. Source and ATLAS conventions: `../../../../source/README.md`
and `../source/README.md`.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate.PullbackCoefficients.PackedTable.InputChecks
open Janko4.GeneratorCertificates

private theorem get_eq_index {α : Type*} {n : ℕ} (v : Vector α n) (i : Fin n) :
    v.get i = v[i.val] := by
  unfold Vector.get
  exact Vector.getElem_toArray _

def scan : ℕ → List ℕ → ℕ
  | _, [] => 0
  | x, y :: ys => (if x.testBit 0 then y else 0) ^^^ scan (x >>> 1) ys

private theorem scan_ofFn {n : ℕ} (x : ℕ) (f : Fin n → ℕ) :
    scan x (List.ofFn f) =
      xorList (List.ofFn (fun i => if x.testBit i.val then f i else 0)) := by
  induction n generalizing x with
  | zero => simp [scan, xorList]
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, scan, xorList, ih]
    congr 1
    apply congrArg xorList
    apply congrArg List.ofFn
    funext i
    simp [Nat.testBit_shiftRight, Nat.add_comm]

private theorem scan_eq {n : ℕ} (x : ℕ) (v : Vector ℕ n) :
    scan x v.toList = rowProduct x v := by
  have hv : List.ofFn v.get = v.toList :=
    Vector.toList_ofFn.symm.trans (congrArg Vector.toList
      (show Vector.ofFn v.get = v from Vector.ofFn_getElem))
  rw [← hv, scan_ofFn]
  rfl


def allIndexed {α : Type*} (p : ℕ → α → Bool) : ℕ → List α → Bool
  | _, [] => true
  | j, c :: cs => p j c && allIndexed p (j+1) cs

private theorem allIndexed_spec {α : Type*} (p : ℕ → α → Bool) (xs : List α)
    (j : ℕ) (h : allIndexed p j xs = true) :
    ∀ i (hi : i < xs.length), p (j+i) xs[i] = true := by
  induction xs generalizing j with
  | nil => simp
  | cons x xs ih =>
    simp only [allIndexed, Bool.and_eq_true] at h
    intro i hi
    cases i with
    | zero => simpa using h.1
    | succ i => simpa [Nat.add_assoc, Nat.add_comm 1] using ih (j+1) h.2 i (by simpa using hi)

def columnTest (a : Fin 125) : Bool :=
  allIndexed (fun j c =>
    c.toList.map (fun x => x.testBit a.val) ==
      (restrictionLinearRows.get a).toList.map (fun x => x.testBit j)) 0 columns.toList

theorem columnTest_sound (a : Fin 125) (h : columnTest a = true) :
    ColumnCheck a := by
  intro i j
  have hj := allIndexed_spec _ _ _ h j.val (by simp)
  simp only [Nat.zero_add, beq_iff_eq, Vector.getElem_toList] at hj
  have hi := congrArg (fun xs : List Bool => xs[i.val]?) hj
  simpa only [List.getElem?_map, Vector.getElem?_toList,
    Vector.getElem?_eq_getElem i.isLt, Option.map_some, Option.some.injEq,
    get_eq_index] using hi

def imageTest (t : Fin 10) : Bool :=
  (images.get t).toList.map Vector.toList ==
    columns.toList.map (fun c =>
      (testFormRows t).toList.map (fun r => scan r c.toList))

theorem imageTest_sound (t : Fin 10) (h : imageTest t = true) :
    ImageCheck t := by
  simp only [imageTest, beq_iff_eq] at h
  apply Vector.ext
  intro j hj
  apply Vector.ext
  intro i hi
  have he := congrArg (fun xs : List (List ℕ) => xs[j]?.bind (fun ys => ys[i]?)) h
  simp only [List.getElem?_map, Vector.getElem?_toList,
    Vector.getElem?_eq_getElem hj, Option.map_some, Option.bind_some,
    Vector.getElem?_eq_getElem hi] at he
  simp only [scan_eq] at he
  simpa only [formColumns, Vector.getElem_map, rowsProduct, Vector.getElem_ofFn,
    Vector.get, Vector.getElem_toArray, Fin.val_cast] using Option.some.inj he

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate.PullbackCoefficients.PackedTable.InputChecks
