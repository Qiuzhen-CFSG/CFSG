module
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates
/-!
# List scanning for the second-involution certificates

`listRow_eq` proves that scanning a row list computes the original packed row
product. `checkProduct_sound` turns the Boolean check into the existing packed
matrix equality. This avoids rebuilding a finite-indexed list at every row.
The concrete consumers are `Second.Products01` through `Second.Products12`.
-/

@[expose] public section
namespace Janko4.ThreeConjugates.SecondCertificate
open GeneratorCertificates

def listRow (x : ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 0
  | y :: ys, k => (if x.testBit k then y else 0) ^^^ listRow x ys (k + 1)

theorem listRow_ofFn {n : ℕ} (f : Fin n → ℕ) (x k : ℕ) :
    listRow x (List.ofFn f) k =
      xorList (List.ofFn (fun i : Fin n => if x.testBit (k + i.val) then f i else 0)) := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ, listRow, List.ofFn_succ, xorList, ih]
    simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ, Nat.add_assoc,
      Nat.add_comm 1]
    rfl

theorem listRow_eq (x : ℕ) (ys : Vector ℕ 112) :
    listRow x ys.toList 0 = packedRow x ys := by
  have he : ys.toList = List.ofFn ys.get := by
    apply List.ext_getElem
    · simp only [Vector.length_toList, List.length_ofFn]
    · intro i hi hj
      simp only [Vector.getElem_toList, List.getElem_ofFn]
      rfl
  rw [he, listRow_ofFn]
  simp only [Nat.zero_add, packedRow]

def checkProduct (xs ys zs : Vector ℕ 112) : Bool :=
  (List.finRange 112).all (fun i => listRow (xs.get i) ys.toList 0 == zs.get i)

theorem checkProduct_sound {xs ys zs : Vector ℕ 112}
    (h : checkProduct xs ys zs = true) : packedMul xs ys = zs := by
  apply packedMul_eq_of_rows
  intro i
  have hi := List.all_eq_true.mp h i (List.mem_finRange i)
  simpa only [beq_iff_eq, listRow_eq] using hi
/-- Identity products avoid reducing `Vector.ofFn` inside a Boolean test. -/
def checkIdentity (xs ys : Vector ℕ 112) : Bool :=
  (List.finRange 112).all (fun i => listRow (xs.get i) ys.toList 0 == 2 ^ i.val)

theorem checkIdentity_sound {xs ys : Vector ℕ 112}
    (h : checkIdentity xs ys = true) : packedMul xs ys = packedOne := by
  apply packedMul_eq_of_rows
  intro i
  have hi := List.all_eq_true.mp h i (List.mem_finRange i)
  simpa only [beq_iff_eq, listRow_eq, packedOne, get_ofFn] using hi
end Janko4.ThreeConjugates.SecondCertificate
