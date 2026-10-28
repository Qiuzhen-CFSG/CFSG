module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.Inputs
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.ActorFusion.Inputs
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.ActorFusion.LocalCalculation
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.ActorFusion.PairIntersection

/-!
# Assembly of actor coverage and full ambient fusion spans

A failed usable image bounds every ambient conjugate by the same large
subgroup. Normality of the original linear kernel and the marked local
intersection give the small span; a local conjugator gives the large span
for the other actors. The independent overlap bound gives direct coverage.

The final theorem discharges both coordinate calculations in the actual
order-25 field model, proving `Frame.Fusion` for every supplied frame and
comparison. It retains the literal projective maps and distinguished
subgroups. The family-union and source-theorem assemblies remain in `Geometry`.

Source: Aschbacher--Smith E.1.5, E.1.8 and E.1.14(6), printed pp.210--214,
referring to Aschbacher (1982), Lemma 4.10.
-/

public section
noncomputable section
open Subgroup GorensteinWalter Matrix
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.Frame

variable {F : Type*} [Field F] [Finite F] {σ : F ≃+* F}
variable (c : Frame σ) (hF : Nat.card F = 5 ^ 2) (hσ : orderOf σ = 2)

variable [Finite (innerModel F σ)]

/-- The remaining local coordinate calculations imply both exact Fusion
clauses, including full ambient conjugacy spans. -/
theorem fusion_of_actorCalculations
    (hlocal : ActorFusion.LocalCalculation c hF hσ)
    (hcross : ActorFusion.PairIntersectionBound c hF hσ) : c.Fusion hF hσ := by
  constructor
  · intro A hA
    rcases c.positioned_coverage_of_intersection_bound hF hσ hcross hA with h | h
    · exact Or.inl (c.usable_of_isPositioned hF hσ hA.2.1 false h)
    · exact Or.inr (c.usable_of_isPositioned hF hσ hA.2.1 true h)
  · intro i A hA hn
    by_cases hlin : A ≤ pGammaL2LinearKernel F (innerModel F σ)
    · exact Or.inl (c.orbitSpan_eq_small_of_linear hF hσ hA i hn hlin
        (hlocal.linear_marking i) (hlocal.small_card i))
    · have hnpos : ¬ c.IsPositioned hF hσ i A :=
        fun h => hn (c.usable_of_isPositioned hF hσ hA.2.1 i h)
      obtain ⟨g, _, hgT, hg⟩ := hlocal.spread i A hA hnpos hlin
      exact Or.inr (c.orbitSpan_eq_large_of_local_join hF hσ hA i hn g hgT hg)

/-- Every characteristic-five frame has actor coverage and the exact full
ambient conjugacy spans. The local marking, conjugate joins, and overlap
bound are all discharged; no generation or family-escape premise is needed. -/
theorem fusion : c.Fusion hF hσ :=
  c.fusion_of_actorCalculations hF hσ
    (c.localCalculation hF hσ) (c.pairIntersectionBound hF hσ)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.Frame
