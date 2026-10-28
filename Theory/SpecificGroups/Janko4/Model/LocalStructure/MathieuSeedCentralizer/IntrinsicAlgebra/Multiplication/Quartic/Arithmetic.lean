module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.Multiplication.Structure
/-!
# Packed column arithmetic for quartic evaluation

The existing XOR row algorithm, applied to a vector selecting matrix columns,
computes matrix action on columns. This is only an encoding lemma; the concrete
input and intermediate words are certified separately in `Certificates`.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.QuarticCertificate
open MultiplicationCertificate

def decodeColumn (v : ℕ) : SmallColumn := fun i => bit v i.val

lemma decodeColumn_rowProduct (v : ℕ) (cols : Fin 56 → ℕ) :
    decodeColumn (rowProduct v cols) =
      (fun i j => bit (cols j) i.val) *ᵥ decodeColumn v := by
  funext i
  rw [decodeColumn, rowProduct_spec]
  simp only [Matrix.mulVec, dotProduct, decodeColumn]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

lemma decodeColumn_zero : decodeColumn 0 = 0 := by
  funext i
  simp [decodeColumn, bit]

lemma decodeColumn_ite (b : Bool) (v : ℕ) :
    decodeColumn (if b then v else 0) = (if b then (1 : ZMod 2) else 0) • decodeColumn v := by
  cases b <;> simp [decodeColumn_zero]
end Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.QuarticCertificate
