module

public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.factsTable
public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.Output
public import Theory.GroupTheory.CosetWordCertificateBoolean

/-! Kernel-checked certificate data for Gebhardt (2000), Section 3B.
Reproduce with `Theory/SpecificGroups/Lyons/GebhardtParabolicIndexCertificate/source/generate.py`. -/

public section
namespace Lyons.Gebhardt.ParabolicIndexCertificate
open Subgroup.CosetWordCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem hshape : ∀ i a, facts (output i a) =
    ⟨survivor i, [a], survivor (dest i a)⟩ := by
  have h : ∀ i a, factBEq (facts (output i a))
      ⟨survivor i, [a], survivor (dest i a)⟩ = true := by decide +kernel
  exact fun i a => (factBEq_eq_true_iff _ _).mp (h i a)

theorem hlt : ∀ i a, output i a < 249178 := by
  intro i a
  exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)

end Lyons.Gebhardt.ParabolicIndexCertificate
