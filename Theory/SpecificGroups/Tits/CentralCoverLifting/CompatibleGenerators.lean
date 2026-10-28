module

public import Theory.SpecificGroups.Tits.CentralCoverLifting
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.NormalizedPresentation

/-!
# Normalized Parrott generators in the canonical universal cover

Choose preimages under the literal universal projection and apply the explicit
central corrections. The resulting tuple projects to all ten named Parrott
generators, has central relator values, and satisfies the ten normalization
identities. It is independent of the choice of preimages. Perfectness needed
for the projection's surjectivity follows directly from the presentation.

The finite auxiliary presentation maps to this actual tuple. The final
theorems show exactly how proving its power/root and Weyl relation families
constructs compatible lifts and removes the canonical kernel. Those two
nonabelian calculations remain explicit here. The correction identities reduce
them to twenty power/root and seven Weyl equations. No splitting or multiplier
vanishing is assumed or asserted.

Sources: Parrott (1972), §5, p.683; Aschbacher--Smith I.1.3, printed p.407,
and GLS3 §6.1 for the multiplier consequence.
-/

public section

namespace Tits.CentralCoverLifting.CompatibleGenerators

open PerfectCentralCovering
attribute [local instance] parrott_perfect_from_relators

private noncomputable def initialGenerators : ParrottGenerator → UniversalGroup ParrottGroup :=
  fun i => Classical.choose (universalProjection_surjective ParrottGroup (parrottGenerator i))

private theorem initialGenerators_projection (i : ParrottGenerator) :
    universalProjection ParrottGroup (initialGenerators i) = parrottGenerator i :=
  Classical.choose_spec (universalProjection_surjective ParrottGroup (parrottGenerator i))

private theorem initialGenerators_relators_central (j : ParrottRelatorIndex) :
    FreeGroup.lift initialGenerators (parrottRelator j) ∈
      Subgroup.center (UniversalGroup ParrottGroup) :=
  universalProjection_ker_le_center ParrottGroup
    (relators_mem_ker _ _ initialGenerators_projection j)

/-- The actual normalized tuple in the canonical cover; full relation satisfaction
still requires the residual word calculation. -/
noncomputable def universalGenerators : ParrottGenerator → UniversalGroup ParrottGroup :=
  normalize initialGenerators

/-- Every normalized generator has its required image under the original projection. -/
@[simp] theorem universalGenerators_projection (i : ParrottGenerator) :
    universalProjection ParrottGroup (universalGenerators i) = parrottGenerator i :=
  normalize_projection _ initialGenerators initialGenerators_projection i

/-- All 37 source relator values are central in the actual canonical cover. -/
theorem universalGenerators_relators_central (j : ParrottRelatorIndex) :
    FreeGroup.lift universalGenerators (parrottRelator j) ∈
      Subgroup.center (UniversalGroup ParrottGroup) :=
  normalize_relators_central initialGenerators initialGenerators_relators_central j

/-- The ten proved normalization identities in the actual canonical cover. -/
theorem universalGenerators_correctionWord (i : ParrottGenerator) :
    FreeGroup.lift universalGenerators (correctionWord i) = 1 :=
  normalize_correctionWord initialGenerators initialGenerators_relators_central i

/-- Any other choice of preimages gives exactly the same normalized tuple. -/
theorem normalize_eq_universalGenerators (g : ParrottGenerator → UniversalGroup ParrottGroup)
    (hg : ∀ i, universalProjection ParrottGroup (g i) = parrottGenerator i) :
    normalize g = universalGenerators :=
  normalize_eq_of_projection_eq _ (universalProjection_ker_le_center _) g initialGenerators
    (fun i => (hg i).trans (initialGenerators_projection i).symm)

/-- The two residual relation families give compatible lifts with the exact
projection required by `CentralCoverLifting.universalProjection_ker_eq_bot_of_lifts`. -/
theorem compatibleLifts_of_relation_families
    (hroot : ∀ j, isPowerRootRelator j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1)
    (hweyl : ∀ j, isPowerRootRelator j = false →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1) :
    ∃ g : ParrottGenerator → UniversalGroup ParrottGroup,
      SatisfiesParrottRelations g ∧
        ∀ i, universalProjection ParrottGroup (g i) = parrottGenerator i := by
  refine ⟨universalGenerators, ?_, universalGenerators_projection⟩
  intro j
  apply relation_of_normalizedPresentation universalGenerators
    universalGenerators_relators_central universalGenerators_correctionWord j
  cases h : isPowerRootRelator j with
  | false => exact hweyl j h
  | true => exact hroot j h

/-- Application to the literal canonical kernel, conditional only on the two
identified residual calculations in the finite auxiliary presentation. -/
theorem universalProjection_ker_eq_bot_of_relation_families
    (hroot : ∀ j, isPowerRootRelator j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1)
    (hweyl : ∀ j, isPowerRootRelator j = false →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1) :
    (universalProjection ParrottGroup).ker = ⊥ :=
  universalProjection_ker_eq_bot_of_lifts (compatibleLifts_of_relation_families hroot hweyl)

/-- Twenty selected power/root equations and seven selected Weyl equations
construct all ten compatible lifts in the actual canonical cover. -/
theorem compatibleLifts_of_seeds
    (hroot : ∀ j, isPowerRootSeed j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1)
    (hweyl : ∀ j, isWeylSeed j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1) :
    ∃ g : ParrottGenerator → UniversalGroup ParrottGroup,
      SatisfiesParrottRelations g ∧
        ∀ i, universalProjection ParrottGroup (g i) = parrottGenerator i := by
  have hrel := relations_of_powerRoot_and_weyl_seed (powerRoot_relations_of_seed hroot) hweyl
  exact compatibleLifts_of_relation_families (fun j _ => hrel j) (fun j _ => hrel j)

/-- The reduced set of 27 residual equations suffices for the required
canonical-kernel conclusion. Their proofs remain separate obligations. -/
theorem universalProjection_ker_eq_bot_of_seeds
    (hroot : ∀ j, isPowerRootSeed j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1)
    (hweyl : ∀ j, isWeylSeed j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1) :
    (universalProjection ParrottGroup).ker = ⊥ :=
  universalProjection_ker_eq_bot_of_lifts (compatibleLifts_of_seeds hroot hweyl)

end Tits.CentralCoverLifting.CompatibleGenerators
