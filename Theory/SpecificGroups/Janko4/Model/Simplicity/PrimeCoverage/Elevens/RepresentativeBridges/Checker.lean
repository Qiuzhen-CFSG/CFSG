module

public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates.Packed

/-!
# List certificates for the eleven-element bridges

A sequential scan of a packed row selects the right-hand rows using successive
bits. The soundness proof identifies this scan with `packedRow`, and hence with
ordinary binary matrix multiplication. Explicit lists avoid rebuilding the
indexed row enumeration during each kernel reduction.

This is an arithmetic checker only; the ATLAS source and conjugating words are
documented in the sibling `Witnesses` module.
-/

@[expose] public section
namespace Janko4.Simplicity.Elevens.BridgeCertificate
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

def rows (xs : List ℕ) (h : xs.length = 112) : Vector ℕ 112 :=
  ⟨xs.toArray, by simpa using h⟩
theorem product_lists (xs ys zs : List ℕ) (hx : xs.length = 112)
    (hy : ys.length = 112) (hz : zs.length = 112)
    (h : xs.map (fun x => fastRow x ys) = zs) :
    decodeRows (rows xs hx) * decodeRows (rows ys hy) = decodeRows (rows zs hz) := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packed_of_list
  simpa [rows] using h

/-- Transfer a certified product to an element of the concrete group. -/
theorem mul_certificate (g h : Model) (xs ys zs : Vector ℕ 112)
    (hg : toMatrix g = decodeRows xs) (hh : toMatrix h = decodeRows ys)
    (hp : decodeRows xs * decodeRows ys = decodeRows zs) :
    toMatrix (g * h) = decodeRows zs := by
  rw [map_mul, hg, hh, hp]

/-- A certified right inverse is the matrix of the group inverse. -/
theorem inv_certificate (g : Model) (xs ys : Vector ℕ 112)
    (hg : toMatrix g = decodeRows xs)
    (hp : decodeRows xs * decodeRows ys = 1) :
    toMatrix g⁻¹ = decodeRows ys := by
  have hi : toMatrix g⁻¹ * toMatrix g = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  calc
    toMatrix g⁻¹ = toMatrix g⁻¹ * 1 := (mul_one _).symm
    _ = toMatrix g⁻¹ * (decodeRows xs * decodeRows ys) := by rw [hp]
    _ = decodeRows ys := by rw [← hg, ← mul_assoc, hi, one_mul]

end Janko4.Simplicity.Elevens.BridgeCertificate
