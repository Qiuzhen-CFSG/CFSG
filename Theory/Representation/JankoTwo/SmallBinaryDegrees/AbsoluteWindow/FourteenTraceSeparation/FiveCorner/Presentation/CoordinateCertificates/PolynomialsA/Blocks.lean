module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.Tables
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.MatrixCertificate.NumericalData

/-!
# Joining finite blocks of checked coordinate actions

A bitset describes the sparse domain. Boolean checks certify parent closure
and monomial coverage without repeated large finite-set normalization.

The data come from the unchanged arrays and polynomial rows documented in
`Presentation/source/README.md`. Every numerical equality is checked in Lean's
kernel; the generating Python program is not part of the trusted proof.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.CoordinateCertificates.PolynomialsA

def support (mask bound : ℕ) : Finset ℕ :=
  (Finset.range bound).filter (fun n => mask.testBit n)

lemma mem_support {mask bound n : ℕ} :
    n ∈ support mask bound ↔ n < bound ∧ mask.testBit n = true := by
  simp only [support, Finset.mem_filter, Finset.mem_range]

lemma parents_of_all (mask bound : ℕ)
    (h : ((List.range bound).all (fun n =>
      if mask.testBit n then mask.testBit (n / 2) else true)) = true) :
    ∀ n ∈ support mask bound, 2 ≤ n → n / 2 ∈ support mask bound := by
  intro n hn _
  obtain ⟨hlt, hbit⟩ := mem_support.mp hn
  apply mem_support.mpr
  refine ⟨(Nat.div_le_self n 2).trans_lt hlt, ?_⟩
  have hc := List.all_eq_true.mp h n (List.mem_range.mpr hlt)
  simpa only [hbit, if_true] using hc

lemma covered_of_all (mask bound : ℕ) (ns : List ℕ)
    (h : (ns.all (fun n => decide (n < bound) && mask.testBit n)) = true) :
    ∀ n ∈ ns, n ∈ support mask bound := by
  intro n hn
  obtain ⟨hlt, hbit⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp h n hn)
  exact mem_support.mpr ⟨of_decide_eq_true hlt, hbit⟩

def Steps (i j : Fin 9) (table : ℕ → ℕ) (mask : ℕ) (ns : List ℕ) : Prop :=
  ∀ n ∈ ns, 2 ≤ n → mask.testBit n = true →
    action (if n.testBit 0 then j else i) (table (n / 2)) = table n

lemma steps_append {i j : Fin 9} {table : ℕ → ℕ} {mask : ℕ} {as bs : List ℕ}
    (ha : Steps i j table mask as) (hb : Steps i j table mask bs) :
    Steps i j table mask (as ++ bs) := by
  intro n hn
  rcases List.mem_append.mp hn with h | h
  · exact ha n h
  · exact hb n h

lemma steps_of_listProduct (i j : Fin 9) (table : ℕ → ℕ) (mask : ℕ) (ns : List ℕ)
    (h : (ns.all (fun n => if n < 2 then true else if mask.testBit n then
      PackedBinaryRows.listProduct (table (n / 2)) 0
        (rows (if n.testBit 0 then j else i)).toList == table n else true)) = true) :
    Steps i j table mask ns := by
  intro n hn hbig hbit
  have hc := List.all_eq_true.mp h n hn
  simp only [if_neg (Nat.not_lt.mpr hbig), hbit, if_true] at hc
  exact action_of_listProduct (beq_iff_eq.mp hc)

lemma steps_support {i j : Fin 9} {table : ℕ → ℕ} {mask bound : ℕ}
    (h : Steps i j table mask (List.range bound)) :
    ∀ n ∈ support mask bound, 2 ≤ n →
      action (if n.testBit 0 then j else i) (table (n / 2)) = table n := by
  intro n hn hbig
  obtain ⟨hlt, hbit⟩ := mem_support.mp hn
  exact h n (List.mem_range.mpr hlt) hbig hbit

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.CoordinateCertificates.PolynomialsA
