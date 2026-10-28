module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.FourSeedReduction
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.RemainingCommutators
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.RemainingPowers
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.NormalizedPresentation
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators

/-!
# Power/root relations for compatible Parrott lifts

The checked word calculation reduces all twenty power/root seeds to four
original source equations. The remaining power and commutator calculations
prove those four equations from centrality and normalization in the literal
`NormalizedPresentation`. This gives the twenty seeds unconditionally;
the correction identities then recover all 23 relations in groups I–V.

Applying the canonical-cover constructor discharges its power/root premise,
leaving only the independently supplied Weyl seeds for compatible lifts.
Source: Parrott (1972), §5, p.683, transcribed in
`refs/original/n-group-global/parrott-tits-presentation.md`.
All commutators retain the convention `a⁻¹ b⁻¹ a b`.
-/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators

/-- All twenty selected power/root equations hold in the auxiliary presentation. -/
theorem powerRoot_seed_relations :
    ∀ j, isPowerRootSeed j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1 :=
  powerRoot_seed_relations_of_two_powers powerRoot_r1_square powerRoot_s3_fourth

/-- The correction identities recover all 23 source equations in groups I–V. -/
theorem powerRoot_relations :
    ∀ j, isPowerRootRelator j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1 :=
  powerRoot_relations_of_seed powerRoot_seed_relations

/-- The power/root calculation discharges that premise of the canonical-cover
constructor; the seven independent Weyl seeds suffice for compatible lifts. -/
theorem compatibleLifts_of_weyl_seeds
    (hweyl : ∀ j, isWeylSeed j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1) :
    ∃ g : ParrottGenerator → PerfectCentralCovering.UniversalGroup ParrottGroup,
      SatisfiesParrottRelations g ∧
        ∀ i, PerfectCentralCovering.universalProjection ParrottGroup (g i) =
          parrottGenerator i :=
  compatibleLifts_of_seeds powerRoot_seed_relations hweyl

/-- Application to the actual canonical cover, retaining precisely the four
remaining power/root equations and the independent Weyl-seed obligation. -/
theorem compatibleLifts_of_four_powerRoot_seeds
    (hroot : ∀ j, isRemainingPowerRootSeed j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1)
    (hweyl : ∀ j, isWeylSeed j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1) :
    ∃ g : ParrottGenerator → PerfectCentralCovering.UniversalGroup ParrottGroup,
      SatisfiesParrottRelations g ∧
        ∀ i, PerfectCentralCovering.universalProjection ParrottGroup (g i) =
          parrottGenerator i :=
  compatibleLifts_of_seeds (powerRoot_seed_relations_of_four hroot) hweyl

end Tits.CentralCoverLifting.CompatibleGenerators
