module

public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.Coverage.InvolutionIndices

/-!
# Assembly of the finite Held involution fusion forest

Explicit root conjugations and parent-to-child conjugations imply coverage
of every selected word, by induction on the vertex index. The checked square
witnesses then give coverage of every binary word of order two.

The two finite families of conjugation equations remain explicit premises.
Neither is inferred from the discovery data or from this conditional result.
Source: GLS3 Table 5.3p; the actual degree-2058 ATLAS Held carrier.
-/

public section

namespace Held.InvolutionFixedData.Coverage
open LocalPairs.SylowGeometry.Calculations
open TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration

/-- Finite conjugation identities suffice for fusion of every binary involution.
The normal-form surjectivity and ambient Sylow placement are not needed for
this finite implication. -/
theorem normalForm_fusion_of_forest_identities
    (hroots : ∀ j : Fin 25,
      MulAut.conj (rootConjugator j) (rootRepresentative j) =
        (normalForm (rootIndex j)).val)
    (hedges : ∀ i : Fin 191, (forestParent i).val < i.val →
      MulAut.conj (generator (forestGenerator i))
          (normalForm (forestIndex (forestParent i))).val =
        (normalForm (forestIndex i)).val)
    (n : Fin 1024) (hn : orderOf (normalForm n).val = 2) :
    IsCovered (normalForm n).val := by
  have hroot (j : Fin 25) : IsCovered (normalForm (rootIndex j)).val := by
    have hb : IsCovered (rootRepresentative j) := by
      unfold rootRepresentative
      split
      · exact Or.inl ⟨1, by simp⟩
      · exact Or.inr ⟨1, by simp⟩
    exact hroots j ▸ hb.conj (rootConjugator j)
  have hforest (i : Fin 191) : IsCovered (normalForm (forestIndex i)).val := by
    induction i using Fin.strong_induction_on with
    | h i ih =>
      rcases forest_parent_lt_or_root i with hp | hr
      · exact hedges i hp ▸ (ih (forestParent i) hp).conj (generator (forestGenerator i))
      · rw [hr]
        exact hroot (forestRoot i)
  obtain ⟨i, rfl⟩ := normalForm_involution_index n hn
  exact hforest i

end Held.InvolutionFixedData.Coverage
