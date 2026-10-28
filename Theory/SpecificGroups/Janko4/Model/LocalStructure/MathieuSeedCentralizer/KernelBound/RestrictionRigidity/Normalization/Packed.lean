module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Data
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.LocalElements
/-!
# Packed arithmetic for kernel normalization

XOR scans certify binary linear combinations and 56-by-56 products. The
lemmas identify these computations with ordinary matrix operations. The
literal witnesses are generated from the source data cited in
`KernelBound/source/README.md`; only Lean kernel reduction certifies them.
-/

@[expose] public section
open scoped BigOperators Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.NormalizationCertificate
open Coordinates GeneratorCertificates

def scan : ℕ → List ℕ → ℕ
  | _, [] => 0
  | x, y :: ys => (if x.testBit 0 then y else 0) ^^^ scan (x >>> 1) ys

lemma scan_ofFn {n : ℕ} (x : ℕ) (f : Fin n → ℕ) :
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

def wordRow (x : ℕ) (i : Fin 56) : ℕ := (x >>> (56*i.val)) % 2^56

lemma bit_wordRow (x : ℕ) (i j : Fin 56) :
    bit (wordRow x i) j.val = decodeHalf x i j := by
  simp only [wordRow, bit, decodeHalf, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
    j.isLt, decide_true, Bool.true_and]

lemma product_eq (x y z : ℕ)
    (h : ∀ i : Fin 56, scan (wordRow x i) (List.ofFn (wordRow y)) = wordRow z i) :
    decodeHalf x * decodeHalf y = decodeHalf z := by
  ext i j
  have hh := congrArg (fun n => bit n j.val) (h i)
  rw [scan_ofFn, bit_xorList, List.map_ofFn, List.sum_ofFn, bit_wordRow] at hh
  rw [← hh, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [← bit_wordRow x i k, ← bit_wordRow y k j]
  simp only [bit]
  cases hbit : (wordRow x i).testBit k.val <;> simp [hbit]

def combination {n : ℕ} (ws : Vector ℕ n) (c : ℕ) : ℕ := scan c ws.toList

lemma decode_combination {n : ℕ} (ws : Vector ℕ n) (c : ℕ) :
    decodeHalf (combination ws c) = ∑ i : Fin n, bit c i.val • decodeHalf (ws.get i) := by
  have hlist : List.ofFn ws.get = ws.toList :=
    Vector.toList_ofFn.symm.trans (congrArg Vector.toList (Vector.ofFn_getElem (xs := ws)))
  ext i j
  simp only [combination, ← hlist, scan_ofFn, decodeHalf, bit_xorList,
    List.map_ofFn, List.sum_ofFn, Matrix.sum_apply, Matrix.smul_apply]
  apply Finset.sum_congr rfl
  intro k _
  simp only [bit]
  cases hbit : c.testBit k.val <;> simp [hbit]

lemma combination_mem {n : ℕ} (ws : Vector ℕ n) (c : ℕ)
    (S : Submodule (ZMod 2) HalfMatrix) (h : ∀ i, decodeHalf (ws.get i) ∈ S) :
    decodeHalf (combination ws c) ∈ S := by
  rw [decode_combination]
  exact S.sum_mem (fun i _ => S.smul_mem _ (h i))

lemma scan_eq_packedRow (x : ℕ) (ys : Vector ℕ 112) :
    scan x ys.toList = packedRow x ys := by
  have hlist : List.ofFn ys.get = ys.toList :=
    Vector.toList_ofFn.symm.trans (congrArg Vector.toList (Vector.ofFn_getElem (xs := ys)))
  rw [← hlist, scan_ofFn]
  rfl

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.NormalizationCertificate
