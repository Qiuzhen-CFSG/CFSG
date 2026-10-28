module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.Words
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.ExtensionChecks.Action
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.ExtensionChecks.Branches
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.ExtensionChecks.NodeMembers

/-!
# Finite normal elementary extension criterion for the Held representative

The finite checker uses the unchanged literal nodes and normal forms. The
certified membership lists for the 23 nodes and all 23,552 Boolean branch checks
discharge its two finite premises. Under normality and elementary abelianness,
the rejection cases are impossible and the acceptance check proves both
subgroup inclusions. The four-point action detects genuine equality in Held;
normality is in the fixed representative.

The resulting `extension_checks` supplies the extension premise of the
normal-index-two enumeration reduction. It neither uses nor assumes
surjectivity of the 1024 normal forms; that is a separate input to the full
intrinsic subgroup enumeration.

Source: `IntrinsicEnumeration/source/extension_discovery.json`, the literal
ATLAS subgroup words, and the Held local calculation for GLS3 Table 5.3p.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration
open LocalPairs.SylowGeometry.Calculations

/-- Assembly from explicit finite membership and Boolean certificates. -/
public theorem extension_checks_of_certificates
    (hmem : ∀ (i : Option (Fin 22)) (x : representative),
      x ∈ node i ↔ ∃ m ∈ ExtensionChecks.members i, normalForm m = x)
    (hcheck : ∀ (i : Option (Fin 22)) (n : Fin 1024),
      ExtensionChecks.branchAction i n = true)
    (i : Option (Fin 22)) (n : Fin 1024)
    (hnormal : (extension i n).Normal)
    (helem : IsElementaryAbelian 2 (extension i n)) :
    ∃ j : Option (Fin 22), extension i n = node j := by
  refine ⟨ExtensionChecks.target i n, ?_⟩
  apply ExtensionChecks.eq_target_of_branchCheck hmem i n _ hnormal helem
  rw [← ExtensionChecks.branchAction_eq]
  exact hcheck i n

/-- Every normal elementary extension by a literal normal form is one of the
original nodes. Both finite certificates are discharged, independently of
normal-form coverage. This supplies `hstep` in `intrinsicEnumeration_of_word_checks`. -/
public theorem extension_checks
    (i : Option (Fin 22)) (n : Fin 1024)
    (hnormal : (extension i n).Normal)
    (helem : IsElementaryAbelian 2 (extension i n)) :
    ∃ j : Option (Fin 22), extension i n = node j :=
  extension_checks_of_certificates ExtensionChecks.certified_members
    ExtensionChecks.branchAction_true i n hnormal helem

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration
