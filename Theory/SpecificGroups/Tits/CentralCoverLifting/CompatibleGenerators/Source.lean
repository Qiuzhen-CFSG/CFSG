module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations

/-!
# Compatible Parrott generators in the canonical universal cover

The power/root calculation proves all 23 equations in source groups I–V.
It discharges the only hypothesis of the Weyl calculation, giving all 37
Parrott relations in the auxiliary normalized presentation. Its homomorphism
to the canonical universal cover transfers these relations to the ten
normalized lifts, whose images are the original named Parrott generators.

Thus the presentation gives a section of the literal universal projection.
Perfectness of the cover makes that section surjective and removes the
kernel. All relation premises of the earlier conditional constructions are
discharged here.

Sources: Parrott (1972), §5, p.683, transcribed in
`refs/original/n-group-global/parrott-tits-presentation.md`; Aschbacher–Smith
I.1.3, printed p.407, and GLS3 §6.1 for the multiplier consequence.
The endpoint is `ParrottGroup`, and the commutator remains `a⁻¹ b⁻¹ a b`.
-/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators

open PerfectCentralCovering
attribute [local instance] parrott_perfect_from_relators

/-- All 37 original source relations hold in the auxiliary presentation. -/
theorem normalizedGenerator_satisfies_relations :
    SatisfiesParrottRelations normalizedGenerator :=
  relations_of_powerRoot powerRoot_relations

/-- The ten constructed lifts satisfy all 37 relations in the actual
canonical universal cover. -/
theorem universalGenerators_satisfies_relations :
    SatisfiesParrottRelations universalGenerators := by
  intro j
  exact relation_of_normalizedPresentation universalGenerators
    universalGenerators_relators_central universalGenerators_correctionWord j
    (normalizedGenerator_satisfies_relations j)

/-- Compatible lifts of every named Parrott generator under the original
universal projection, with no remaining relation hypotheses. -/
theorem compatibleLifts :
    ∃ g : ParrottGenerator → UniversalGroup ParrottGroup,
      SatisfiesParrottRelations g ∧
        ∀ i, universalProjection ParrottGroup (g i) = parrottGenerator i :=
  ⟨universalGenerators, universalGenerators_satisfies_relations,
    universalGenerators_projection⟩

/-- The compatible generators give a section; perfectness of the canonical
cover then proves that its literal projection has trivial kernel. -/
theorem universalProjection_ker_eq_bot :
    (universalProjection ParrottGroup).ker = ⊥ :=
  universalProjection_ker_eq_bot_of_lifts compatibleLifts

end Tits.CentralCoverLifting.CompatibleGenerators
