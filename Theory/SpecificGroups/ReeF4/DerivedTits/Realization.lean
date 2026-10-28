module

public import Theory.SpecificGroups.ReeF4.DerivedTits.Realization.SimpleData
public import Theory.SpecificGroups.ReeF4.DerivedTits.Realization.SimpleComparison
public import Theory.SpecificGroups.ReeF4.DerivedTits.Realization.TransportComparison

/-!
# Parrott's presentation in the binary Ree fixed matrices

The ten concrete root and Weyl words are exceptional fixed points. The complete
Geck basis enumeration in `SimpleComparison` identifies the eight signed
simple-root matrices with their literal binary tables. `TransportComparison`
propagates those identities along certified Weyl routes to all ten words.
`Comparison` then transfers the 37 checked Parrott relations and the nonzero
off-diagonal entry of `s₈` to the actual split carrier.

The unconditional `parrott_realization` discharges both matrix comparisons.
Its witness is `Realization.assignment`, with the source's commutator and
substitution conventions. Identification of its image with the derived binary
Ree group belongs to `DerivedTits.Reduction` and also requires an ambient size
bound; that identification is separate from the realization proved here.

Sources: Parrott (1972), §5, printed p.683; GLS3, §§2.3–2.4 and Table 2.4;
the integral Geck and Tits constructions used by `ReeF4.Model`.
-/

namespace ReeF4.DerivedTits

/-- The two matrix comparisons suffice for the full realization. -/
public theorem parrott_realization_of_simple_comparisons
    (hsimple : ∃ e : Theory.AlgebraicGroup.F4Chevalley.BasisIndex ≃ Fin 52,
      Realization.SimpleMatrixComparison e)
    (htransport : ∀ e : Theory.AlgebraicGroup.F4Chevalley.BasisIndex ≃ Fin 52,
      Realization.SimpleMatrixComparison e → Realization.MatrixComparison e) :
    ∃ g : Tits.ParrottGenerator → SplitGroup 0,
      (∀ i, reeTwist 0 (g i) = g i) ∧
      Tits.SatisfiesParrottRelations g ∧ (∃ i, g i ≠ 1) := by
  obtain ⟨e, he⟩ := hsimple
  exact parrott_realization_of_matrixComparison e (htransport e he)

/-- Concrete exceptional fixed root/Weyl words satisfy all 37 Parrott relations,
and the nonzero `(0, 28)` entry of the numbered `s₈` matrix makes the realization
nontrivial. No comparison, embedding, or recognition premise is required. -/
public theorem parrott_realization :
    ∃ g : Tits.ParrottGenerator → SplitGroup 0,
      (∀ i, reeTwist 0 (g i) = g i) ∧
      Tits.SatisfiesParrottRelations g ∧ (∃ i, g i ≠ 1) :=
  parrott_realization_of_simple_comparisons
    Realization.exists_simpleMatrixComparison
    Realization.matrixComparison_of_simpleMatrixComparison

end ReeF4.DerivedTits
