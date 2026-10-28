module

public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.AutomizerConjugacy.Reduction
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.AutomizerConjugacy.FullStructure
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.AutomizerConjugacy.SemilinearRecognition

/-!
# Assembly of the root-automorphism subgroup calculation

Sylow conjugacy aligns the diagonal torus. The resulting candidate normalizes
the order-144 inner–torus join, so a concrete normalizer bound puts it in the
semilinear overgroup. A classification there gives the full literal subgroup
equality, and coordinate-change invariance transfers all original hypotheses.

The full automorphism normal forms prove the Sylow and normalizer facts, and
the semilinear calculation identifies the subgroup using its center action
and central cubic coset. The final theorem discharges these concrete inputs,
leaving only the published `AutomizerInvariants` on the original subgroup.

Source motivation: Aschbacher, *Sporadic Groups* (1994), 8.15, 46.3 and 46.14.
-/

@[expose] public section
open Subgroup
namespace Matrix.PSL3Four.RootNormalizerModel.AutomizerConjugacy

/-- Conditional assembly of the two independent concrete calculations. -/
theorem exists_adjustment_of_semilinear_classification
    (hsyl : ∃ T : Sylow 3 (MulAut Root), (T : Subgroup (MulAut Root)) = torus)
    (hnormal : normalizer (innerTorus : Set (MulAut Root)) ≤ inner ⊔ semilinear)
    (recognize : ∀ K : Subgroup (MulAut Root), AutomizerInvariants K →
      torus ≤ K → K ≤ inner ⊔ semilinear → K = inner ⊔ actor)
    (H : Subgroup (MulAut Root)) (h : AutomizerInvariants H) :
    ∃ a : MulAut Root, H.map (MulAut.congr a).toMonoidHom = inner ⊔ actor := by
  obtain ⟨a, ha⟩ := exists_torus_le_map hsyl h.card
  have hinv := invariants_map h a
  exact ⟨a, recognize _ hinv ha ((le_normalizer_innerTorus hinv ha).trans hnormal)⟩

/-- Every subgroup with the published automizer invariants becomes the literal
inner–actor join after changing coordinates on the root group. -/
theorem exists_adjustment_of_invariants (H : Subgroup (MulAut Root))
    (h : AutomizerInvariants H) :
    ∃ a : MulAut Root, H.map (MulAut.congr a).toMonoidHom =
      (MulAut.conj : Root →* MulAut Root).range ⊔ actor :=
  exists_adjustment_of_semilinear_classification torus_sylow
    normalizer_innerTorus_le eq_standard_of_semilinear H h

end Matrix.PSL3Four.RootNormalizerModel.AutomizerConjugacy
