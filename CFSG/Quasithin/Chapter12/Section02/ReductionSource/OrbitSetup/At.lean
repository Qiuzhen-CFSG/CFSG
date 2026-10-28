module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.OrbitSetup
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At

/-!
# The Chapter 10 endgame at the original Chapter 12 ambient group

The guarded normalization theorem supplies precisely the independent
`SourceNormalization1222At` input: no chosen module is assumed. The structural
application then chooses an Irr⁺ member and proves invariance, reducedness and
TI for every such member from the separately supplied surviving FSU branches.
Both steps retain the original G and T and their multiple-overgroup hypothesis.

Tensor exclusion, the non-A5 survivor and the actual replacement remain explicit.
Their producers are `qt-d-tensor-exclusion`, `qt-d-10-linear-three-survivor` and
`qt-d-10-linear-three-replacement`; `qt-d-1222-normalization` retains their final
discharge. The structural branches remain with `qt-d-1222-source`, which feeds
the final `qt-d-1317-source` application. These are conditional implications,
not unconditional proofs of 10.0.1 or 12.2.2.

Source: Aschbacher--Smith, 10.0.1 and the proof of 12.2.2(3), printed
pp.741,756--757,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

/-- The original Chapter 10 source branches supply the exact local
normalization contract, before choosing any Section 12.2 module. -/
theorem sourceNormalization1222At_of_source_branches_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (htensor : Chapter10.SourceA5TensorExclusionAt T)
    (hreduction : Chapter10.SourceNonnormalReductionAt T)
    (hreplacement : Chapter10.SourceLinearThreeReplacementAt T) :
    SourceNormalization1222At KnownSimple.IsKnownSimple T := by
  intro L h
  exact (h.normalizes_and_chosen_after_source_branches_of_many
    hmany htensor hreduction hreplacement).1

/-- The literal structural consumer of the guarded Chapter 10 endgame.
The independent FSU branch theorem is still required for the conclusions
about every chosen module; normalization alone does not assert them. -/
theorem structural1222At_of_normalization_source_branches_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (htensor : Chapter10.SourceA5TensorExclusionAt T)
    (hreduction : Chapter10.SourceNonnormalReductionAt T)
    (hreplacement : Chapter10.SourceLinearThreeReplacementAt T)
    (branches : SourceBranches1222At KnownSimple.IsKnownSimple T) :
    Structural1222At KnownSimple.IsKnownSimple T :=
  structural1222At_of_source_branches
    (sourceNormalization1222At_of_source_branches_of_many
      hmany htensor hreduction hreplacement) branches

end CFSG.Quasithin.Chapter12.Section02
