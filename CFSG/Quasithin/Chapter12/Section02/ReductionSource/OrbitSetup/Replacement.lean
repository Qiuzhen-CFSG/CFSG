module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.OrbitSetup.At
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Source

/-!
# Chapter 12 normalization with the actual replacement discharged

The completed Chapter 10 replacement constructs a maximal faithful A₅
component in the original group from the marked linear-three survivor.
Applying the A₅ contradiction to that replacement proves normalization,
after the independent tensor exclusion and survivor reduction are supplied.
Only then do we choose the Chapter 12 Irr⁺ module. The structural application
also retains the separate surviving FSU branches on every chosen module.

The multiple-overgroup guard, ambient group and Sylow subgroup are unchanged.
Minimal fundamental setups are reselected by the Chapter 10 argument; no
irreducibility of an arbitrary fixed setup is assumed. The universal
conditional APIs remain available without modification.

The remaining normalization inputs are owned by `qt-d-tensor-exclusion` and
`qt-d-10-linear-three-survivor`. Under the conditional adapter contract,
their final discharge and the independent FSU branches remain with
`qt-d-1222-source`, feeding the final `qt-d-1317-source` assembly. These
adapters do not assert an unconditional proof of 10.0.1 or 12.2.2.

Source: Aschbacher--Smith, 10.0.1, the final paragraph of §10.3, and the
normalization and module-choice steps of 12.2.2(3), printed pp.741,757,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The actual replacement discharges the last construction in the guarded
Chapter 10 endgame before choosing the original Chapter 12 module. -/
theorem Hypothesis1221.normalizes_and_chosen_after_replacement_of_many
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (htensor : Chapter10.SourceA5TensorExclusionAt T)
    (hreduction : Chapter10.SourceNonnormalReductionAt T) :
    (T : Subgroup G) ≤ normalizer (L : Set G) ∧
      ∃ V : Subgroup G, Nonempty (ChosenModule T L V) :=
  h.normalizes_and_chosen_after_source_branches_of_many hmany htensor hreduction
    (Chapter10.source_linearThreeReplacement T)

/-- The same completed replacement supplies the original Hypothesis 12.2.3
normalization and module-existence prefix, with the standing guard explicit. -/
theorem Hypothesis1223.normalizes_and_chosen_after_replacement_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (htensor : Chapter10.SourceA5TensorExclusionAt T)
    (hreduction : Chapter10.SourceNonnormalReductionAt T) :
    (T : Subgroup G) ≤ normalizer (L : Set G) ∧
      Nonempty {V : Subgroup G // Nonempty (ChosenModule T L V)} :=
  h.normalizes_and_chosen_after_source_branches_of_many hmany htensor hreduction
    (Chapter10.source_linearThreeReplacement T)

/-- The precise normalization input to the Chapter 12 assembly, with no
replacement callback and no chosen-module premise. -/
theorem sourceNormalization1222At_after_replacement_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (htensor : Chapter10.SourceA5TensorExclusionAt T)
    (hreduction : Chapter10.SourceNonnormalReductionAt T) :
    SourceNormalization1222At KnownSimple.IsKnownSimple T :=
  sourceNormalization1222At_of_source_branches_of_many hmany htensor hreduction
    (Chapter10.source_linearThreeReplacement T)

/-- Apply normalization to the actual structural consumer. Invariance,
reducedness and TI use the separate FSU branches for every original choice. -/
theorem structural1222At_after_replacement_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (htensor : Chapter10.SourceA5TensorExclusionAt T)
    (hreduction : Chapter10.SourceNonnormalReductionAt T)
    (branches : SourceBranches1222At KnownSimple.IsKnownSimple T) :
    Structural1222At KnownSimple.IsKnownSimple T :=
  structural1222At_of_source_branches
    (sourceNormalization1222At_after_replacement_of_many hmany htensor hreduction)
    branches

end CFSG.Quasithin.Chapter12.Section02
