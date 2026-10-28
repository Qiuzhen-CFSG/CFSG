module

public import CFSG.Quasithin.ChapterI.Section01.SQTKMultipliers
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison.BinaryG2Exclusion.MultiplierTable

/-!
# The literal B.5 application of the neutral I.1.3 assembly

The six shape constructors, their actual group carriers, and every model
condition agree with the unchanged earlier B.5 multiplier interface. The
adapter transports both the exhaustive iff and every canonical-kernel
isomorphism, including both noncyclic rows.

`earlierMultiplierInput_of_model_inputs` is the actual conditional B.5
consumer of the full catalogue proof in Chapter I. Its individual kernel
and family-rank premises remain to be discharged by the I.1.3 assembly
owner; this adapter does not assert that they have been proved.
Source: Aschbacher--Smith I.1.3, printed p.407, used in B.5.7.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison.BinaryG2Exclusion
namespace MultiplierTable
namespace FromChapterI
universe u

/-- The source's six rows in the neutral Chapter I boundary. -/
def sourceShape : MultiplierShape → ChapterI.SQTKMultipliers.MultiplierShape
  | .two => .two
  | .three => .three
  | .six => .six
  | .twelve => .twelve
  | .elementaryFour => .elementaryFour
  | .exceptionalFortyEight => .exceptionalFortyEight

/-- The actual carriers, including C₂ × C₂ and (C₄ × C₄) × C₃, coincide. -/
theorem sourceShape_carrier (r : MultiplierShape) : (sourceShape r).Carrier = r.Carrier := by
  cases r <;> rfl

/-- Every field convention and both exceptional exclusions agree literally. -/
theorem sourceShape_row (S : Type u) [Group S] (r : MultiplierShape) :
    MultiplierRow S r ↔ ChapterI.SQTKMultipliers.MultiplierRow S (sourceShape r) := by
  cases r <;> rfl

/-- Transport the complete source table to the unchanged B.5 fields. -/
theorem table {S : Type u} [Group S] [Group.IsPerfect S]
    (h : ChapterI.SQTKMultipliers.MultiplierTable S) : MultiplierTable S := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro hn
    obtain ⟨r, hr⟩ := h.exhaustive.mp hn
    cases r with
    | two => exact ⟨.two, hr⟩
    | three => exact ⟨.three, hr⟩
    | six => exact ⟨.six, hr⟩
    | twelve => exact ⟨.twelve, hr⟩
    | elementaryFour => exact ⟨.elementaryFour, hr⟩
    | exceptionalFortyEight => exact ⟨.exceptionalFortyEight, hr⟩
  · rintro ⟨r, hr⟩
    exact h.exhaustive.mpr ⟨sourceShape r, (sourceShape_row S r).mp hr⟩
  · intro r hr
    have hv := h.values (sourceShape r) ((sourceShape_row S r).mp hr)
    cases r <;> exact hv

/-- The neutral universal source statement yields the literal earlier B.5 input. -/
theorem earlierMultiplierInput (h : ChapterI.SQTKMultipliers.SourceStatement.{u}) :
    EarlierMultiplierInput KnownSimple.IsKnownSimple.{u} := by
  intro S _ _ _ _ hS
  exact table (h S hS)

/-- Application of the actual conditional full-catalogue I.1.3 proof to B.5.
No global table or classification premise is assumed in place of that proof. -/
theorem earlierMultiplierInput_of_model_inputs
    (hK : ∀ (S : Type u) [Group S] [Finite S] [Group.IsPerfect S] [IsSimpleGroup S],
      IsSQTK KnownSimple.IsKnownSimple S → ChapterI.SQTKMultipliers.KernelInputs S)
    (hR : ∀ (S : Type u) [Group S] [Finite S] [Group.IsPerfect S] [IsSimpleGroup S],
      IsSQTK KnownSimple.IsKnownSimple S → ChapterI.SQTKMultipliers.RankInputs S) :
    EarlierMultiplierInput KnownSimple.IsKnownSimple.{u} :=
  earlierMultiplierInput (ChapterI.SQTKMultipliers.sourceStatement_of_model_inputs hK hR)

end FromChapterI
end MultiplierTable
end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison.BinaryG2Exclusion
