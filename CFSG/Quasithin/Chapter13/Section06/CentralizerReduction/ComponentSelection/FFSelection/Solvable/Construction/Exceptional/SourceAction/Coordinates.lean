module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Exceptional.SourceAction.Coordinates.Cubic
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Exceptional.SourceAction.Coordinates.Assembly

/-!
# Ambient parity coordinates from the recovered B.5.7 actions

The marked symmetric supplement extends the six-point action through the
quotient by the original cubic. The faithful cubic moved plane supplies the
three-point action with kernel the original alternating factor. Their signs
agree, and the two projections jointly identify G with the literal parity
subgroup of S₆ × S₃. Both linear intertwiners use this same isomorphism.

This completes the coordinate construction from `Recovered`; its recovery
from earlier source inputs remains with the source-action assembly. No
splitting of the ambient fixed space is asserted, and the five-dimensional
augmentation core retains its fixed line.

Source: Aschbacher–Smith, B.5.7, printed p.106; B.5.6(4), printed p.105.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional.SourceAction
universe u v

/-- The recovered local actions determine simultaneous ambient parity
coordinates, including both literal kernels and whole-group intertwiners. -/
theorem coordinates {G : Type u} [Group G] [Finite G]
    (c : ChapterB.OuterSixThreeShape G)
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) {K : GroupClass.{u}}
    (hyp : ChapterB.SourceInduction.FFHypothesis K ρ) (d : Recovered c ρ) :
    Nonempty (AmbientCoordinates c ρ) := by
  obtain ⟨s⟩ := six_coordinates c ρ d
  obtain ⟨t⟩ := cubic_coordinates c ρ hyp d
  exact assemble_coordinates c ρ d s t

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional.SourceAction
