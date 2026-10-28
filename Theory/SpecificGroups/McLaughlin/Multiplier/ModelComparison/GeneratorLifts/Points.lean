module
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.GeneratorLifts.PointGeometry
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.GeneratorLifts.PointDistinct
/-!
# The common marked point equivalence

The coordinate rows give 275 distinct points of the actual Leech triangle
slice. Its proved cardinality 275 makes the displayed injection a bijection.
-/
@[expose] public section
noncomputable section
namespace Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison
theorem markedPoint_injective : Function.Injective markedPoint := by
  intro i j he
  apply pointVectors_injective
  funext k
  have hk := congrArg (fun p : Atlas.Sporadic.McLaughlin.Points => p.val.val (coordinate k)) he
  simpa only [markedPoint, vectorOfData, coordinateIndex_coordinate] using hk

def markedPointEquiv : Fin 275 ≃ Atlas.Sporadic.McLaughlin.Points := by
  letI : Finite Atlas.Sporadic.McLaughlin.Points := Nat.finite_of_card_ne_zero (by
    rw [Atlas.Sporadic.McLaughlin.degree]; decide)
  exact Equiv.ofBijective markedPoint ((Nat.bijective_iff_injective_and_card _).mpr
    ⟨markedPoint_injective, by rw [Nat.card_fin, Atlas.Sporadic.McLaughlin.degree]⟩)

end Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison
