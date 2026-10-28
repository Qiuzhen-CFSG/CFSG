module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ElementaryWords
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.Words
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.NormalSteps
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.WordCoverage
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.ExtensionChecks

/-!
# Held's intrinsic normal elementary subgroup enumeration

The requested enumeration concerns normal elementary subgroups inside the fixed
four-word representative, not normality in Held. Normal-index-two steps reduce
it to adjoining one of 1024 literal binary words to one of the 22 published
entries or to bottom.

The reduction is retained as a separate theorem. `intrinsicEnumeration`
discharges both finite premises using the proved word coverage and extension
checks, leaving only the representative's two-group hypothesis explicit. The
accompanying GAP data guide the certificates; the proofs concern actual words
and generated subgroups in the fixed representative.

Source application: Aschbacher–Smith, even characteristic on printed pp.3–4
and 481–482; GLS3 Table 5.3p; the literal ATLAS degree-2058 Held model.
The ambient normalizer catalogue is assembled separately by the parent module.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue
open LocalPairs.SylowGeometry.Calculations IntrinsicEnumeration

/-- Normal-index-two induction reduces the exact 22-entry enumeration to two
independent finite certificates, discharged below in `intrinsicEnumeration`. -/
public theorem intrinsicEnumeration_of_word_checks
    (hp : IsPGroup 2 representative)
    (hcover : Function.Surjective normalForm)
    (hstep : ∀ (i : Option (Fin 22)) (n : Fin 1024),
      (extension i n).Normal → IsElementaryAbelian 2 (extension i n) →
      ∃ j : Option (Fin 22), extension i n = node j)
    (R : Subgroup representative) (hR : R ≠ ⊥) (hn : R.Normal)
    (he : IsElementaryAbelian 2 R) : ∃ j : Fin 22, R = entry j := by
  obtain ⟨i, hi⟩ := eq_node_of_normal_elementary_extensions hp node normalForm
    hcover ⟨none, rfl⟩ hstep R hn he
  cases i with
  | none => exact (hR hi).elim
  | some j => exact ⟨j, hi⟩

/-- Every nontrivial normal elementary subgroup of the fixed representative
equals a literal published entry. This supplies the enumeration premise of the
ambient maximal-normalizer catalogue; normality here is intrinsic to the
representative. -/
public theorem intrinsicEnumeration
    (hp : IsPGroup 2 representative)
    (R : Subgroup representative) (hR : R ≠ ⊥) (hn : R.Normal)
    (he : IsElementaryAbelian 2 R) : ∃ j : Fin 22, R = entry j :=
  intrinsicEnumeration_of_word_checks hp normalForm_surjective extension_checks R hR hn he

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue
