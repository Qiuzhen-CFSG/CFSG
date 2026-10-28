module

public import Theory.Representation.BinaryOffender.Restriction
public import Theory.Representation.BinaryOffender.RatioInheritance
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Comparison.ModelFacts.Transport

/-!
# The original strong actor survives on its actual component seed

A noncentral invariant subspace of a minimal strong offender has a strong
faithful actor image. Otherwise minimal replacement gives a trivial
restriction kernel and a fixed-space supplement; rank and fixed codimension
then agree with the original action, contradicting its strict inequality.

The second theorem transports this conclusion to the literal B.5 seed
quotient. It retains the original seed-offender image and makes no claim
that its rank equals the rank of the original actor.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.DecomposableQuinticControl
variable {G W : Type*} [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- Minimal strength survives on the actual image of a noncentral invariant
subspace, without assuming that the original actor is faithful there. -/
theorem strong_restricted_of_minimal_strong
    (σ : Representation (ZMod 2) G W) {A : Subgroup G}
    (hmin : IsMinimalBestOffender σ A) (hstrong : IsStrongOffender σ A)
    (I : Submodule (ZMod 2) W) (hAI : A ≤ subspaceStabilizer σ I)
    (hn : ¬ I ≤ fixedSpace σ A) :
    IsStrongOffender (subspaceImageRepresentation σ I) (restrictedSubgroup σ I A) := by
  by_contra hnot
  obtain ⟨hker, hsum⟩ := hmin.faithful_span_of_not_strong σ I hAI hn hnot
  let : IsElementaryAbelian 2 A := hstrong.1.2
  have hr := rank_subspaceKernel_add_image σ I A hAI (IsElementaryAbelian.isPGroup 2 A)
  have hr' : rank (restrictedSubgroup σ I A) = rank A := by
    simpa only [hker, Representation.BinaryOffender.rank_bot, zero_add] using hr
  have hd := fixedCodim_restricted_eq_of_sup σ I hAI hsum
  exact hnot ⟨(hmin.1.restricted σ I hAI hn).1, by rw [hd, hr']; exact hstrong.2⟩

open ChapterB.SourceInduction.ComponentReduction
open ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
open ChapterB.QuasisimpleSource

/-- The prepared B.5 quotient retains a strong image of the original actor.
The proof uses the exact seed-image rank and fixed-codimension transports. -/
theorem prepared_seed_strong_of_minimal_strong
    (σ : Representation (ZMod 2) G W) {K : GroupClass} {A L : Subgroup G}
    (hLA : ⁅L,A⁆ = L) (p : Prepared σ K hLA)
    (hmin : IsMinimalBestOffender σ A) (hstrong : IsStrongOffender σ A) :
    IsStrongOffender (seedQuotientAction σ hLA) (seedOffenderImage σ hLA) := by
  have hn : ¬ naturalSeedSpace σ L A ≤ fixedSpace σ A := by
    intro hc
    exact p.noncentral ((subspaceCommutator_eq_bot_iff σ _ A).mpr hc)
  have hs := strong_restricted_of_minimal_strong σ hmin hstrong
    (naturalSeedSpace σ L A) (le_sup_right.trans (seedSpace_stable σ hLA)) hn
  refine ⟨p.minimal.1.1, ?_⟩
  rw [seedOffenderImage_fixedCodim, seedOffenderImage_rank]
  exact hs.2

end CFSG.Quasithin.Chapter15.DecomposableQuinticControl
