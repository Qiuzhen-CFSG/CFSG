module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.QuotientInvolutions.SylowData

/-!
# The marked pair and involutions in the concrete star group

These are the actual permutations attached to the max1 quotient, with the
left-conjugation convention. The seed has pair label 1, on the unordered
pair {0,1}. The finite checks identify this label and count invariant pairs
for the two quotient representatives. They assert no conjugacy-class size.

Source: the certified star tables in `QuotientCount.Image.StarData` and the
marked quotient comparison in `Max1Fusion.QuotientInvolutions.Bridge`.
-/

@[expose] public section
namespace Janko4.LocalStructure.MathieuSeedCentralizer.InvolutionBound
open Cardinality.QuotientCount.Image Simplicity.Max1Fusion.QuotientInvolutions

/-- The two marked quotient representatives in the concrete permutation carrier. -/
def starBase (b : Bool) : StarGroup :=
  if b then (starFirst * starSecond)^7 else starFirst

/-- Quotient conjugacy classes restricted to the stabilizer of the seed pair. -/
abbrev StarClass (b : Bool) :=
  {g : StarGroup // pairLabel (g.val 0) (g.val 1) = 1 ∧ IsConj (starBase b) g}

/-- Label 1 specifies exactly the unordered pair {0,1}. -/
theorem pairLabel_eq_one_iff : ∀ i j : Fin 24,
    pairLabel i j = 1 ↔ (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
  decide +kernel

/-- Number of invariant unordered pairs in the literal 24-point action. -/
def fixedPairCount (p : Equiv.Perm (Fin 24)) : ℕ :=
  (Finset.univ.filter (fun ij : Fin 24 × Fin 24 => ij.1 < ij.2 ∧
    ((p ij.1 = ij.1 ∧ p ij.2 = ij.2) ∨ (p ij.1 = ij.2 ∧ p ij.2 = ij.1)))).card

set_option maxRecDepth 10000 in
/-- The first quotient representative fixes twelve unordered pairs. -/
theorem fixedPairCount_false : fixedPairCount (starBase false).val = 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
/-- The second quotient representative fixes thirty-six unordered pairs. -/
theorem fixedPairCount_true : fixedPairCount (starBase true).val = 36 := by
  decide +kernel

end Janko4.LocalStructure.MathieuSeedCentralizer.InvolutionBound
