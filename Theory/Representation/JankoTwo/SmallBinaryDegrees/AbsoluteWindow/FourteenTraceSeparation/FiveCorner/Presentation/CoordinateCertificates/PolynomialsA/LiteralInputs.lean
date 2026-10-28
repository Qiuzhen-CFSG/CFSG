module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.CoordinateCertificates.PolynomialsA.Blocks

/-!
# Literal input certificates for the packed action scans

Each witness names a code, its input vector, and its output vector. The checker
verifies both table equalities as well as the original packed matrix action.
This avoids repeatedly normalizing a table lookup inside the row scan.

The data come from the unchanged arrays and polynomial rows documented in
`Presentation/source/README.md`. Every numerical equality is checked in Lean's
kernel; the generating Python program is not part of the trusted proof.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.CoordinateCertificates.PolynomialsA

/-- Literal inputs prevent repeated table lookup during the 1008-row scan. -/
def witnessCheck (i j : Fin 9) (table : ℕ → ℕ) (mask : ℕ)
    (p : ℕ × ℕ × ℕ) : Bool :=
  if p.1 < 2 then true else if mask.testBit p.1 then
    ((table (p.1 / 2) == p.2.1) && (table p.1 == p.2.2)) &&
      (PackedBinaryRows.listProduct p.2.1 0
        (rows (if p.1.testBit 0 then j else i)).toList == p.2.2)
  else true

lemma steps_of_witnesses (i j : Fin 9) (table : ℕ → ℕ) (mask : ℕ)
    (ps : List (ℕ × ℕ × ℕ))
    (h : (ps.all (witnessCheck i j table mask)) = true) :
    Steps i j table mask (ps.map Prod.fst) := by
  intro n hn hbig hbit
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn
  have hc := List.all_eq_true.mp h p hp
  simp only [witnessCheck, if_neg (Nat.not_lt.mpr hbig), hbit, if_true] at hc
  obtain ⟨hc, ha⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨hx, hy⟩ := Bool.and_eq_true_iff.mp hc
  rw [beq_iff_eq.mp hx, beq_iff_eq.mp hy]
  exact action_of_listProduct (beq_iff_eq.mp ha)

lemma steps_of_witnesses_for (i j : Fin 9) (table : ℕ → ℕ) (mask : ℕ)
    (ps : List (ℕ × ℕ × ℕ)) (ns : List ℕ)
    (hcodes : ps.map Prod.fst = ns)
    (h : (ps.all (witnessCheck i j table mask)) = true) :
    Steps i j table mask ns := by
  rw [← hcodes]
  exact steps_of_witnesses i j table mask ps h

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.CoordinateCertificates.PolynomialsA
