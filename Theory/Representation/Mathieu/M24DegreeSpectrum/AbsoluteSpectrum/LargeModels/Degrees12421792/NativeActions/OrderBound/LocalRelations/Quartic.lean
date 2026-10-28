module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.LocalRelations.Quartic.Checked

/-!
# The max8 quartic word in the original M24 presentation

The literal signed half-word is carried by source-derived substitutions and
conjugations to `(a*b*a*b⁻¹)^6`, whose square reduces to one. Every retained
source equation and every trace command is checked by the Lean kernel.
No permutation-image identity or presentation faithfulness is assumed.

Source: John Bray's ATLAS M24G1-P1 and M24G1-max8W1; see
`Quartic/source/README.md` for the frozen certificate and its verification.
The six mixed local identities remain an independent obligation.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.LocalRelations

/-- The fixed quartic local identity holds unconditionally in `UniversalGroup`. -/
theorem quartic_relation : QuarticRelation := Quartic.Certificate.checked_quartic

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.LocalRelations
