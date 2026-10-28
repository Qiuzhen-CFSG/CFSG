module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.NormalizedPresentation
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.OddOrder
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.Braid
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.RemainingConjugations

/-!
# The normalized Weyl relations from the power/root relations

The odd-power arguments prove VII(s₅) and VIII(s₄), and the checked central-word
calculations prove the other four conjugation seeds. These conjugations kill
the central braid defect: its square and fifth power are both one. Thus all
seven Weyl seeds hold under precisely the power/root hypothesis in the actual
normalized presentation.

Applying the correction-word reduction then gives all 37 original Parrott
relations, including the fifth- and third-power equations. The power/root
hypothesis remains explicit for the compatible-lift assembly to discharge.

Source: Parrott (1972), §5, p.683, especially VI–VIII; see
`refs/original/n-group-global/parrott-tits-presentation.md`.
-/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators

/-- The two proved odd-power cases, four remaining conjugation equations,
and the braid equation give exactly the seven Weyl seeds. -/
theorem weyl_seed_relations_of_remaining
    (hroot : ∀ j, isPowerRootRelator j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1)
    (hconj : ∀ j, isRemainingWeylConjugation j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1)
    (hbraid : FreeGroup.lift normalizedGenerator (parrottRelator .vi_r1_r8) = 1) :
    ∀ j, isWeylSeed j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1 := by
  intro j hj
  cases j <;> first
    | exact hbraid
    | exact weyl_vii_s5_relation hroot
    | exact weyl_viii_s4_relation hroot
    | exact hconj _ rfl
    | cases hj

/-- Actual application to the checked 37-relation reduction. The four
conjugation equations and the braid identity are still explicit premises. -/
theorem relations_of_powerRoot_and_remaining_weyl
    (hroot : ∀ j, isPowerRootRelator j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1)
    (hconj : ∀ j, isRemainingWeylConjugation j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1)
    (hbraid : FreeGroup.lift normalizedGenerator (parrottRelator .vi_r1_r8) = 1) :
    SatisfiesParrottRelations normalizedGenerator :=
  relations_of_powerRoot_and_weyl_seed hroot
    (weyl_seed_relations_of_remaining hroot hconj hbraid)

/-- All seven Weyl seed equations in the normalized presentation follow from
the power/root relations. The conjugation and braid premises of the earlier
assembly are discharged by their checked word calculations. -/
theorem weyl_seed_relations
    (hroot : ∀ j, isPowerRootRelator j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1) :
    ∀ j, isWeylSeed j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1 := by
  have hconj := weyl_remaining_conjugation_relations hroot
  exact weyl_seed_relations_of_remaining hroot hconj
    (weyl_braid_relation_of_remaining hroot hconj)

/-- The power/root relations alone give all 37 original Parrott relations in
the normalized presentation, supplying the complete relation family used to
construct compatible lifts in the canonical universal cover. -/
theorem relations_of_powerRoot
    (hroot : ∀ j, isPowerRootRelator j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1) :
    SatisfiesParrottRelations normalizedGenerator :=
  relations_of_powerRoot_and_weyl_seed hroot (weyl_seed_relations hroot)

end Tits.CentralCoverLifting.CompatibleGenerators
