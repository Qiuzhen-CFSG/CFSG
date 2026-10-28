module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.CubicResidualActor
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.FullResidualSeed
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaChosenComplete

/-!
# Corrected arbitrary-seed exclusion in 15.2.22

The original residual has action image of order three or nine. In the
cubic case, the intersection core supplies an element of T − S normalizing
the literal YY₁. In the full-image case, Y contains and normalizes the seed.
Both cases give the conjugate-seed commutator relation. The original
residual pair is unchanged when the outside actor is replaced, so the
characteristic-two normalizer argument applies to its actual second factor.

The final application constructs that pair from S-reducibility; no actor,
image-size or commutator premise remains. The earlier Omega, NI-action and
plane-geometry inputs retain their existing producers and final discharge
by qt-e-152-plane-uniqueness. Identifying the earlier distinguished H₁,H₂
in 15.2.21(1) remains a separate obligation.

Source: Aschbacher--Smith 15.2.22, printed pp.1114--1115,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
open Section01 ChapterD ChapterD.UniqueFactor PlaneUniquenessPreceding.OmegaAction
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I E : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The arbitrary-seed cubic branch, with its actor constructed from the
original intersection core. -/
theorem source_15_2_22_of_cubic_residual
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (s : Seed M I (smallActionS T ZS) E)
    (hC : IsSmallActionThreePrime (M ⊓ centralizer (V : Set G)))
    (eNI : intersectionImage hsource I ≃* Equiv.Perm (Fin 3))
    {t : G} (p : ResidualPair (T : Subgroup G) (smallActionS T ZS) (smallActionK H) t) :
    letI := hsource.prepared.elementary
    SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized) →
    let Y := caseIIResidual T M (chosenStarredPreimage M V hsource.prepared.normalized) Mc
    Nat.card ((Y.subgroupOf M).map (action hsource)) = 3 →
    ¬ ⁅E,p.K₂⁆ ≤ E ⊓ p.K₂ := by
  let := hsource.prepared.elementary
  intro ho
  dsimp only
  intro hc
  obtain ⟨u,hu,huS,hn⟩ := s.exists_cubic_normalizing_actor d hI (s.not_le_MI d hC) eNI ho hc
  exact source_15_2_22_of_cubic_actor d hI hfit s hC p u hu huS ho hc hn

/-- Corrected 15.2.22 for every source seed and every actual conjugate pair.
The original residual has image of order three or nine, and both branches
supply the needed same-family commutator relation without an extra premise. -/
theorem source_15_2_22_from_preceding
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (s : Seed M I (smallActionS T ZS) E)
    (hC : IsSmallActionThreePrime (M ⊓ centralizer (V : Set G)))
    (eNI : intersectionImage hsource I ≃* Equiv.Perm (Fin 3))
    {t : G} (p : ResidualPair (T : Subgroup G) (smallActionS T ZS) (smallActionK H) t) :
    letI := hsource.prepared.elementary
    SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized) →
    ¬ ⁅E,p.K₂⁆ ≤ E ⊓ p.K₂ := by
  let := hsource.prepared.elementary
  intro ho
  have hRc := source_chosen_core_noncentral hsource.ambient T hsource.empty
    hsource.maximal hsource.centralizing hsource.partner hsource.many hsource.prepared
  rcases source_omega_caseIIResidual_image_order T hsource.maximal.1.2
    hsource.prepared.normalized ho hRc with h3 | h9
  · exact source_15_2_22_of_cubic_residual d hI hfit s hC eNI p ho h3
  · exact source_15_2_22_of_full_residual d hI hfit s hC p ho h9

/-- Reducibility constructs the actual residual pair, which immediately
satisfies the arbitrary-seed source exclusion. No actor, image-size or
same-family commutator premise is retained. -/
theorem exists_pair_exclusion_from_preceding
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hnot : ¬ IsSmallActionIrreducible (smallActionS T ZS) (smallActionK H))
    (s : Seed M I (smallActionS T ZS) E)
    (hC : IsSmallActionThreePrime (M ⊓ centralizer (V : Set G)))
    (eNI : intersectionImage hsource I ≃* Equiv.Perm (Fin 3))
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ smallActionS T ZS) :
    letI := hsource.prepared.elementary
    SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized) →
    ∃ p : ResidualPair (T : Subgroup G) (smallActionS T ZS) (smallActionK H) t,
      ¬ ⁅E,p.K₂⁆ ≤ E ⊓ p.K₂ := by
  let := hsource.prepared.elementary
  intro ho
  obtain ⟨p⟩ := exists_residualPair d hI hnot t ht htS
  exact ⟨p,source_15_2_22_from_preceding d hI hfit s hC eNI p ho⟩

end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
