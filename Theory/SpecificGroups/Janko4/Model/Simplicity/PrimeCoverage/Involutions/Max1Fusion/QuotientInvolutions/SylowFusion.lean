module
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.QuotientInvolutions.SylowFusion.Coverage
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.QuotientInvolutions.SylowFusion.Checks

/-!
# Involution fusion in the fixed local star candidate

The finite word table is closed under each fixed generator and its inverse,
so it covers the generated subgroup. Every table entry is certified to be
trivial, to have nontrivial square, or to conjugate to one of the two marked
words. The conjugators are actual elements of the star group, certified by
words in its generators. This proves local coverage independently of any
order calculation or Sylow assertion.

Source: the fixed ATLAS-derived candidate in `SylowData`; the exploratory
GAP witnesses in `QuotientInvolutions/source/fusion.json` are checked by the
kernel in the `SylowFusion` modules, with the conventions documented there.
-/

public section
namespace Janko4.Simplicity.Max1Fusion.QuotientInvolutions
open Cardinality.QuotientCount.Image SylowFusionCertificate

/-- Every involution in the fixed candidate fuses inside `StarGroup` to one
of the two marked targets. No Sylow or cardinality hypothesis is required. -/
theorem sylowCandidate_involution_coverage (w : StarGroup)
    (hw : w ∈ sylowCandidate) (ho : orderOf w = 2) :
    ∃ g : StarGroup,
      starFirst = g * w * g⁻¹ ∨ (starFirst * starSecond)^7 = g * w * g⁻¹ := by
  obtain ⟨r, rfl⟩ := candidate_covered w hw
  rcases checked_cases r with h | h | h
  · rw [h, orderOf_one] at ho
    norm_num at ho
  · exact False.elim (h (by rw [← ho]; exact pow_orderOf_eq_one _))
  · refine ⟨conjugator r, ?_⟩
    unfold target at h
    split_ifs at h
    · exact Or.inl h
    · exact Or.inr h

end Janko4.Simplicity.Max1Fusion.QuotientInvolutions
