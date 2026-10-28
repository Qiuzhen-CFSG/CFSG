module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.LocalUniqueness
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric
public import CFSG.Quasithin.Chapter5.RankOneBaumannSourceBound
public import Theory.AtlasPort.ExceptionalIsomorphisms.SmallParameters

/-!
# Independent Baumann control in the original A₅ context

The actual A₅ action identifies L/O₂(L) with PSL₂(4). Maximality in the
original local family and faithfulness give Hypothesis 12.2.1. The chosen
module then constructs the rank-one Input on the whole reduced subgroup
R₂(LT), retaining the genuine multiple-overgroup hypothesis. Applying the
original 5.1.7 bound proves 13.2.5 before outside-centralization 13.2.7.

Source: Aschbacher--Smith 13.2.5, printed p.879, and 5.1.7(1), pp.633--634.
The universal Sylow transport and terminal application are in
SourceAssembly/BaumannSource. No outside-centralization or nonsingular
centralizer containment is used here.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Chapter1.Section02.Adequate
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d

/-- The original Context supplies every field of Hypothesis 12.2.1. -/
theorem rankOne_hypothesis :
    Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L :=
  ⟨d.hypothesis.qtke, ⟨d.maximal_local,
    ((mem_faithfulLocalComponents_iff T L).mp d.hypothesis.local_component).2⟩,
    IsQuasisimple.of_mulEquiv d.quotient.symm⟩

/-- The rank-one input uses the entire original R₂(LT), with exponent two
and the actual quotient marking transported through PSL₂(4) ≃ A₅. -/
theorem rankOne_input_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    Chapter6.Source.RankOneGeneric.Input KnownSimple.IsKnownSimple T L
      (Chapter12.Section02.RankOneModule.wholeReduced T L) 2 := by
  have hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ 2) :=
    ⟨GaloisField 2 2, inferInstance, inferInstance,
      by rw [GaloisField.card 2 2 (by decide)],
      ⟨d.quotient.trans Atlas.Comparisons.Exceptional.psl2FourEquivAlt5.symm⟩⟩
  exact d.chosen.rankOne_generic_input_of_many (rankOne_hypothesis d)
    hmany (by decide) hpsl

/-- Original 13.2.5, independently of 13.2.7 and C_T(L)=1. -/
theorem baumann_normalizer_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G) :=
  (rankOne_input_of_many d hmany).baumann_normalizer_le

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
