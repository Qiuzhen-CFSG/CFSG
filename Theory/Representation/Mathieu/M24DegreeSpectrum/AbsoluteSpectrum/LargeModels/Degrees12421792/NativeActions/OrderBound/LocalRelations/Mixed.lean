module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.LocalRelations.Mixed.NativeKernel
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.LocalRelations.Mixed.CyclicTrace

/-!
# A cyclic reduction of the six mixed max8 identities

The checked trace places every fixed mixed word in `⟨xyxyxy⁻¹⟩` using the
quartic and first mixed identities. The native image kills those words and
is injective on this cyclic subgroup once its order-23 equation is supplied.
The first mixed identity and the cyclic power equation remain explicit source
obligations. No ambient finiteness or presentation faithfulness is used.

Source: ATLAS M24G1-P1 and M24G1-max8W1; see `Mixed/source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.LocalRelations

/-- The six literal words follow from two specific source obligations. -/
theorem mixed_relations_of_first_and_cycle (hq : QuarticRelation)
    (hf : Mixed.FirstRelation) (hp : Mixed.CyclePowerRelation) : MixedRelations := by
  intro i
  exact Mixed.eq_one_of_cycle_mem hp (Mixed.Trace.mixed_mem_cycle hq hf i)
    (Mixed.nativeMap_mixed i)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.LocalRelations
