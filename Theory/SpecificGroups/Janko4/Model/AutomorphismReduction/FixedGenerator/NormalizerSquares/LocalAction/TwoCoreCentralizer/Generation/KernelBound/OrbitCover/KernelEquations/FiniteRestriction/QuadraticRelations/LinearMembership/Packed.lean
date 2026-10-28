module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.Data

/-!
# Rectangular binary products for the mixed-space certificates

A decoded product is the XOR of the selected right rows, as in
Janko4/Model/GeneratorCertificates/Packed.lean. The dimensions here are
arbitrary, so the same kernel-checked calculation handles H and J.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership
open GeneratorCertificates

def rectDecode {m : ℕ} (n : ℕ) (rows : Vector ℕ m) :
    Matrix (Fin m) (Fin n) (ZMod 2) := fun i j => bit (rows.get i) j.val

def rectRowProduct {n : ℕ} (x : ℕ) (ys : Vector ℕ n) : ℕ :=
  xorList (List.ofFn (fun k : Fin n => if x.testBit k.val then ys.get k else 0))

theorem rectDecode_product {m n k : ℕ} (xs : Vector ℕ m) (ys : Vector ℕ n) :
    rectDecode k (Vector.ofFn (fun i => rectRowProduct (xs.get i) ys)) =
      rectDecode n xs * rectDecode k ys := by
  funext i j
  simp only [rectDecode, get_ofFn]
  rw [rectRowProduct, bit_xorList, List.map_ofFn, List.sum_ofFn, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro a _
  simp only [rectDecode, bit]
  cases h : (xs.get i).testBit a.val <;> simp [h]

theorem rectProduct_eq {m n k : ℕ} (xs : Vector ℕ m) (ys : Vector ℕ n)
    (zs : Vector ℕ m) (h : ∀ i, rectRowProduct (xs.get i) ys = zs.get i) :
    rectDecode n xs * rectDecode k ys = rectDecode k zs := by
  rw [← rectDecode_product]
  congr 1
  apply Vector.ext
  intro i hi
  change (Vector.ofFn _).get ⟨i, hi⟩ = zs.get ⟨i, hi⟩
  rw [get_ofFn, h]

theorem rectDecode_one (n : ℕ) :
    rectDecode n (Vector.ofFn (fun i : Fin n => 2 ^ i.val)) = 1 := by
  funext i j
  simp only [rectDecode, get_ofFn, bit, Nat.testBit_two_pow, decide_eq_true_eq,
    Matrix.one_apply, Fin.ext_iff]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership
