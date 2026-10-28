module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.Multiplication.Structure
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.Multiplication.Quartic.Arithmetic
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.Multiplication.Quartic.Tables

/-!
# Finite checks of the actual quartic coordinates

Every auxiliary column and every intermediate product is certified against the
published `Data` definitions by Lean's kernel. Keeping the numerical checks
separate lets symbolic applications reuse these completed certificates.
Input and reproduction: `source/README.md`.
-/

public section
namespace Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.QuarticCertificate
open MultiplicationCertificate

set_option maxRecDepth 100000 in
lemma operatorColumns_entry (a : Fin 10) (i j : Fin 56) :
    bit ((operatorColumns.get a).get j) i.val = operator a i j := by
  have h : ∀ a : Fin 10, ∀ i j : Fin 56,
      ((operatorColumns.get a).get j).testBit i.val =
        (operatorWords.get a).testBit (56*i.val+j.val) := by decide +kernel
  simp only [operator, decodeFlat, bit, h]

set_option maxRecDepth 100000 in
lemma topColumn_entry (i : Fin 56) : topOperator i 0 = bit topColumn i.val := by
  have h : ∀ i : Fin 56, topOperatorWord.testBit (56*i.val) =
      topColumn.testBit i.val := by decide +kernel
  change bit topOperatorWord (56*i.val+0) = bit topColumn i.val
  simp only [Nat.add_zero, bit, h]

set_option maxRecDepth 100000 in
lemma tailTwo_check (q : Fin 210) :
    rowProduct ((operatorColumns.get (quarticTuples.get q 3)).get 0)
      (operatorColumns.get (quarticTuples.get q 2)).get = tailTwo.get q := by
  have h : ∀ q : Fin 210,
      rowProduct ((operatorColumns.get (quarticTuples.get q 3)).get 0)
        (operatorColumns.get (quarticTuples.get q 2)).get = tailTwo.get q := by decide +kernel
  exact h q

set_option maxRecDepth 100000 in
lemma tailThree_check (q : Fin 210) :
    rowProduct (tailTwo.get q) (operatorColumns.get (quarticTuples.get q 1)).get =
      tailThree.get q := by
  have h : ∀ q : Fin 210,
      rowProduct (tailTwo.get q) (operatorColumns.get (quarticTuples.get q 1)).get =
        tailThree.get q := by decide +kernel
  exact h q

set_option maxRecDepth 100000 in
lemma quartic_check (q : Fin 210) :
    rowProduct (tailThree.get q) (operatorColumns.get (quarticTuples.get q 0)).get =
      if quarticPacked.testBit q.val then topColumn else 0 := by
  have h : ∀ q : Fin 210,
      rowProduct (tailThree.get q) (operatorColumns.get (quarticTuples.get q 0)).get =
        if quarticPacked.testBit q.val then topColumn else 0 := by decide +kernel
  exact h q

end Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.QuarticCertificate
