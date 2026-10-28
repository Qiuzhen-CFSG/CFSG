module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Fusion.LinearWords
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Fusion.TreeData

/-!
# Propagation of O'Nan involution fusion along the seven trees

The finite data have an earlier parent at every nonroot vertex. A conjugating
edge preserves order, so strong induction reduces every candidate involution
to one of the seven roots. At a root the odd-product lemma constructs its
conjugator to `generatorA`. Neither closure nor injectivity of normal forms
is used. Tree and root witnesses are the reproducible data from `Two/source/`;
the group identities are explicit premises until their matrix proofs are given.
-/

namespace ONan.Simplicity.TwoCertificate.Fusion

/-- Candidate coverage, tree products and root powers imply full fusion. -/
public theorem normalForms_involution_fusion_of_tree
    (hclass : ∀ i, orderOf (indexedForm i) = 2 → ∃ t, vertex t = i)
    (hedge : ∀ t, parent t < t → indexedForm (vertex t) * generators (label t) =
      generators (label t) * indexedForm (vertex (parent t)))
    (hroot : ∀ r, (indexedForm (vertex (root r)) *
      (ambientWord generatorA generatorB (rootWord r) * generatorA *
        (ambientWord generatorA generatorB (rootWord r))⁻¹)) ^
          (2 * rootHalfExponent r + 1) = 1) :
    ∀ v : Fin 9 → Bool, orderOf (normalForm v) = 2 →
      ∃ g : Model, generatorA = g * normalForm v * g⁻¹ := by
  have hf (t : Fin 87) : orderOf (indexedForm (vertex t)) = 2 →
      ∃ g : Model, generatorA = g * indexedForm (vertex t) * g⁻¹ := by
    induction t using WellFoundedLT.induction with
    | ind t ih =>
      intro ht
      rcases root_or_parent_lt t with ⟨r, rfl⟩ | hlt
      · apply generatorA_eq_conj_of_odd_power _ _ (rootHalfExponent r) _ (hroot r)
        rw [← ht]
        exact pow_orderOf_eq_one _
      · have he := hedge t hlt
        have hs : SemiconjBy (generators (label t))
            (indexedForm (vertex (parent t))) (indexedForm (vertex t)) := he.symm
        have hp := (SemiconjBy.orderOf_eq _ hs).trans ht
        obtain ⟨g, hg⟩ := ih (parent t) hlt hp
        refine ⟨g * (generators (label t))⁻¹, ?_⟩
        have hc : indexedForm (vertex t) = generators (label t) *
            indexedForm (vertex (parent t)) * (generators (label t))⁻¹ :=
          eq_mul_inv_iff_mul_eq.mpr he
        rw [hc]
        simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left,
          mul_inv_cancel_left] using hg
  intro v hv
  obtain ⟨i, rfl⟩ := bits_surjective v
  obtain ⟨t, ht⟩ := hclass i hv
  exact ht ▸ hf t (ht.symm ▸ hv)

end ONan.Simplicity.TwoCertificate.Fusion
