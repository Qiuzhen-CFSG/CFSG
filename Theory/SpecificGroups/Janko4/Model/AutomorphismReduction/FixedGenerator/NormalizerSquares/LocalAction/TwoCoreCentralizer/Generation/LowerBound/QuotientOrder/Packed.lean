module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.QuotientOrder.Core
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates.Packed
open Janko4.GeneratorCertificates
/-!
# Packed arithmetic for the literal twelve-dimensional quotient

The existing binary-row XOR theorem identifies the packed calculation with
ordinary right row multiplication over `ZMod 2`. The resulting lemmas turn
finite integer equalities into vector and matrix equalities. This arithmetic
bridge checks the orbit-tree edges and stabilizer-word products; it does not
assume any orbit size or group identification.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.LowerBound.QuotientOrderCertificate

def packedRow (x : ℕ) (ys : Vector ℕ 12) : ℕ :=
  xorList (List.ofFn (fun k : Fin 12 => if x.testBit k.val then ys.get k else 0))

theorem packedRow_spec (x : ℕ) (ys : Vector ℕ 12) (j : Fin 12) :
    bit (packedRow x ys) j.val =
      Matrix.vecMul (fun k : Fin 12 => bit x k.val) (quotientDecode ys) j := by
  rw [packedRow, bit_xorList, List.map_ofFn, List.sum_ofFn]
  change (∑ k : Fin 12, bit (if x.testBit k.val then ys.get k else 0) j.val) =
    ∑ k : Fin 12, bit x k.val * bit (ys.get k) j.val
  apply Finset.sum_congr rfl
  intro k _
  simp only [bit]
  cases x.testBit k.val <;> simp

theorem vecMul_eq_of_packed (v w : BitVec 12) (ys : Vector ℕ 12)
    (h : packedRow v.toNat ys = w.toNat) :
    Matrix.vecMul (row v) (quotientDecode ys) = row w := by
  funext j
  change Matrix.vecMul (fun k : Fin 12 => bit v.toNat k.val) (quotientDecode ys) j =
    bit w.toNat j.val
  rw [← packedRow_spec, h]

theorem mul_eq_of_packed (xs ys zs : Vector ℕ 12)
    (h : ∀ i : Fin 12, packedRow (xs.get i) ys = zs.get i) :
    quotientDecode xs * quotientDecode ys = quotientDecode zs := by
  funext i j
  change Matrix.vecMul (fun k : Fin 12 => bit (xs.get i) k.val) (quotientDecode ys) j =
    bit (zs.get i) j.val
  rw [← packedRow_spec, h i]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.LowerBound.QuotientOrderCertificate
