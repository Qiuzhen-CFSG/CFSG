module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientSeedInvariant
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalStationarySelection
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientSource

/-!
# Selecting an invariant constituent in the original stationary module

An actual outside H-star member centralizes omega in the stationary Thompson
branch. Original maximal-local uniqueness then removes fixed vectors. Selecting
a homogeneous constituent inside the specified reduced subgroup, and using the
all-degree invariance theorem, gives actual natural or Hermitian coordinates on
that same constituent. Neither a model nor Sylow invariance is assumed.

This retains the original commutator layer in Hypothesis 6.1.1. Equality of the
selected constituent with the whole layer is a separate classification step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped IsMulCommutative MatrixGroups
attribute [local instance] seedInvariantFixedAlgebra seedInvariantBinarySpace

namespace CFSG.Quasithin.Chapter6.Source
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G]

/-- The actual stationary reduced subgroup contains a Sylow-invariant chosen
constituent, with full natural or Hermitian coordinates in every degree. -/
theorem RankOneGeneric.Input.stationary_reduced_seed_models
    {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}
    (h : RankOneGeneric.Input KnownSimple.IsKnownSimple T L W n)
    (hj : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G)) :
    ∃ (U : Subgroup G) (D : ChosenModule T L U),
      U ≤ W ∧ D.sourceOrbit = U ∧ U ⊓ centralizer (L : Set G) = ⊥ ∧
      (IsNaturalModule L U n ∨
        ∃ s : ℕ, n = 2 * s ∧ ∃ hs : 0 < s, letI : NeZero s := ⟨hs.ne'⟩;
          IsConjugationModel L U (SL2.BinarySmall.hermitian s)) := by
  obtain ⟨H, hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside h.outside
  have hc := h.reduced_fixed_eq_bot_of_outside_centralizes hH
    (h.omega_centralizes_of_thompson_centralizes hH hj)
  let J := L ⊔ (T : Subgroup G)
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.maximal_local.1
  have hm : ⁅W.subgroupOf J, L.subgroupOf J⁆ ≠ ⊥ := by
    intro he
    apply h.noncentral
    have hh := congrArg (map J.subtype) he
    rw [map_commutator, map_subgroupOf_eq_of_le h.reduced.1,
      map_subgroupOf_eq_of_le (show L ≤ J from le_sup_left), Subgroup.map_bot] at hh
    exact hh
  obtain ⟨U, ⟨D⟩, hUW⟩ := exists_chosen_le_reduced_witness h.sylow_normalizes
    (W.subgroupOf J) h.reduced_internal hm
  rw [map_subgroupOf_eq_of_le h.reduced.1] at hUW
  have hU : U ⊓ centralizer (L : Set G) = ⊥ :=
    bot_unique ((inf_le_inf_right _ hUW).trans_eq hc)
  exact ⟨U, D, hUW, D.rankOne_sourceOrbit_eq_of_fixed_free h hU, hU,
    D.rankOne_fixed_free_seed_models h hU⟩

/-- Original Hypothesis 6.1.1 selects the constituent inside its actual moved
layer. No model, invariant-subgroup, or H-star centralization premise remains. -/
theorem Hypothesis611.stationary_layer_seed_models
    {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hj : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (layer L V : Set G)) :
    ∃ (U : Subgroup G) (D : ChosenModule T L U),
      U ≤ layer L V ∧ D.sourceOrbit = U ∧ U ⊓ centralizer (L : Set G) = ⊥ ∧
      (IsNaturalModule L U n ∨
        ∃ s : ℕ, n = 2 * s ∧ ∃ hs : 0 < s, letI : NeZero s := ⟨hs.ne'⟩;
          IsConjugationModel L U (SL2.BinarySmall.hermitian s)) := by
  exact (h.rankOneInput hout).commutator_input.stationary_reduced_seed_models hj

end CFSG.Quasithin.Chapter6.Source
