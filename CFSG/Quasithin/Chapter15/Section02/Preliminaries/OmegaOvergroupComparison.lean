module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaOvergroupComparison.Full
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaOvergroupComparison.Proper
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallRankOneSelection.Omega

/-!
# Maximal overgroups and residual witnesses for every small chosen action

The Omega comparison, including proper chosen supports, discharges the last
maximal-overgroup premise in the existing whole-action assembly. Every small
chosen module therefore has exactly the two original maximal overgroups.
The literal rank-one selections now supply the residual-witness and
cubic-normalizer clauses of 15.2.6--7 without a selection or uniqueness callback.
Both noncentral chief factors consequently have the actual kernel O₂(H).

For Omega the actual H-star quotient reduces to S₃, S₃ wr C₂, or S₅, with
the symmetric-five wreath excluded. The two-chief S₃/S₅ exclusions and the
marked-five wreath exclusion remain with qt-e-152-small-parabolic. The retained
SmallSourcePrior contains only the earlier-source and counterexample inputs
allowed by that source-family contract; it contains no conclusion of 15.2.1--8.

Source: Aschbacher--Smith 15.2.5--8, printed pp.1107--1110.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The complete maximal-overgroup family for full small chosen modules. -/
theorem ChosenSmallSource.maximal_overgroups_of_full
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V) (hfull : V = localModule T M) :
    maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc} :=
  h.maximal_overgroups_of_action_alternatives hprior h.action_alternatives
    (fun ho => h.maximal_overgroups_of_full_omega ho hfull)

/-- All rank-one and cubic-normalizer clauses in the full chosen-module family. -/
theorem ChosenSmallSource.smallResidualWitness_of_full
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V) (hfull : V = localModule T M) :
    ∃ Y₁ : Subgroup G, SmallResidualWitness h Y₁ ∧ SmallCubicNormalizer h Y₁ :=
  h.smallResidualWitness_of_overgroups (h.maximal_overgroups_of_full hprior hfull)

/-- Full-module Omega selection, without any overgroup premise. -/
theorem ChosenSmallSource.smallResidualWitness_of_full_omega
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ho : letI := h.prepared.elementary
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized))
    (hfull : V = localModule T M) :
    ∃ Y₁ : Subgroup G, SmallResidualWitness h Y₁ ∧ SmallCubicNormalizer h Y₁ :=
  h.smallResidualWitness_of_omega ho (h.maximal_overgroups_of_full_omega ho hfull)

/-- The actual H-star quotient reduction in the full Omega row. Only the
original two-chief S₃ and S₅ exclusions remain before the wreath conclusion. -/
theorem ChosenSmallSource.HStar_quotient_of_full_omega
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ho : letI := h.prepared.elementary
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized))
    (hfull : V = localModule T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5)) :=
  h.HStar_quotient_of_omega ho (h.maximal_overgroups_of_full_omega ho hfull) hH

/-- Original 15.2.5 for all four small-action alternatives. -/
theorem ChosenSmallSource.maximal_overgroups
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V) :
    maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc} :=
  h.maximal_overgroups_of_action_alternatives hprior h.action_alternatives
    (fun ho => h.maximal_overgroups_of_omega ho)

/-- The complete literal selection and cubic normalizer family of 15.2.6--7. -/
theorem ChosenSmallSource.smallResidualWitness
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V) :
    ∃ Y₁ : Subgroup G, SmallResidualWitness h Y₁ ∧ SmallCubicNormalizer h Y₁ :=
  h.smallResidualWitness_of_overgroups (h.maximal_overgroups hprior)

/-- The Omega selection needs no retained earlier-source prior. -/
theorem ChosenSmallSource.smallResidualWitness_of_source_omega
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ho : letI := h.prepared.elementary
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized)) :
    ∃ Y₁ : Subgroup G, SmallResidualWitness h Y₁ ∧ SmallCubicNormalizer h Y₁ :=
  h.smallResidualWitness_of_omega ho (h.maximal_overgroups_of_omega ho)

/-- Original 15.2.7(1), with the literal residual and no uniqueness premise. -/
theorem ChosenSmallSource.residual_unique
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V) :
    maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M} := by
  obtain ⟨Y₁,hw,_⟩ := h.smallResidualWitness hprior
  exact hw.residual_unique

/-- The actual H-star quotient reduction for every Omega support. The two-chief
S₃/S₅ exclusions remain before the final symmetric-three wreath conclusion. -/
theorem ChosenSmallSource.HStar_quotient_of_source_omega
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ho : letI := h.prepared.elementary
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5)) :=
  h.HStar_quotient_of_omega ho (h.maximal_overgroups_of_omega ho) hH

/-- The four actual chief-actor quotient alternatives, with residual uniqueness discharged. -/
theorem ChosenSmallSource.HStar_small_quotient
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    ChapterB.ChiefSmallActor (H ⧸ pCore 2 H) :=
  h.HStar_small_quotient_of_residual_unique (h.residual_unique hprior) hH

open NoncentralChiefRefinement in
/-- Both literal noncentral chief actions are faithful modulo O₂(H).
These two factors are retained for the remaining original 15.2.8 exclusions. -/
theorem ChosenSmallSource.two_faithful_chief_factors
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    letI := h.prepared.elementary
    let U := (conjugateSpan H V).subgroupOf H
    letI := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      (show conjugateSpan H V ≤ H by
        rw [UniqueFactor.conjugateSpan_eq]
        exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
    ∀ s : SeriesOn U, ∃ i j : Fin s.series.length, i ≠ j ∧
      (¬ s.Central i ∧
        (Representation.BinaryOffender.actionHom (s.factorRepresentation i)).ker = pCore 2 H ∧
        ChapterB.ChiefSmallWholeAction
          (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))) ∧
      (¬ s.Central j ∧
        (Representation.BinaryOffender.actionHom (s.factorRepresentation j)).ker = pCore 2 H ∧
        ChapterB.ChiefSmallWholeAction
          (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation j))) :=
  h.two_faithful_chief_factors_of_residual_unique (h.residual_unique hprior) hH

end CFSG.Quasithin.Chapter15.Section02
