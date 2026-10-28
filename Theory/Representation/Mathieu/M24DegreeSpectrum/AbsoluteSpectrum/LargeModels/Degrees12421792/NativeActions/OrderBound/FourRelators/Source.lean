module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.DoubleBound
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.FourRelators.Bound
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.LocalRelations.Quartic

/-!
# Native comparison using only the first mixed max8 identity

The first four local relations bound the literal subgroup by 12144. The
40320-coset cover therefore bounds the ambient presentation by twice the
native M24 order. Perfectness and the proved trivial native multiplier remove
the possible kernel of order two. This discharges the cycle-power premise
of the earlier max8 route, without asserting the remaining first identity
or cover. The full large-model and spectrum consumers use this comparison.

Sources: John Bray, ATLAS M24G1-P1 and M24G1-max8W1; Aschbacher–Smith
I.1.3, printed p.407, and K.4, printed p.457.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation
open OrderBound

/-- The remaining two source obligations give the relaxed ambient bound. -/
theorem double_bound_of_first_and_cover
    (hf : LocalRelations.Mixed.FirstRelation)
    (cover : Subgroup.GeneratorCosetCover boundSubgroup generator (Fin 40320)) :
    Finite UniversalGroup ∧ Nat.card UniversalGroup ≤ 489646080 := by
  obtain ⟨hfin, hc⟩ := FourRelators.boundSubgroup_bound LocalRelations.quartic_relation hf
  let : Finite boundSubgroup := hfin
  obtain ⟨hg, hb⟩ := cover.finite_card_le (PresentedGroup.closure_range_of relators)
  refine ⟨hg, hb.trans ?_⟩
  simpa only [Nat.card_fin] using Nat.mul_le_mul_right 40320 hc

/-- The literal native comparison, without a cycle-power premise. -/
theorem toCarrier_injective_of_first_and_cover
    (hf : LocalRelations.Mixed.FirstRelation)
    (cover : Subgroup.GeneratorCosetCover boundSubgroup generator (Fin 40320)) :
    Function.Injective toCarrier :=
  toCarrier_injective_of_double_bound (double_bound_of_first_and_cover hf cover)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation
