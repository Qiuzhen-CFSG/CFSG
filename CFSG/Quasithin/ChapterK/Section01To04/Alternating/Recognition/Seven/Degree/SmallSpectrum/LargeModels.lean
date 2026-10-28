module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven.Degree.SmallSpectrum.Inputs
public import Theory.Representation.AlternatingSevenBinaryLargeModels.Fourteen.Absolute
public import Theory.Representation.AlternatingSevenBinaryLargeModels.Twenty.Absolute

/-!
# Construction of the larger binary A₇ candidates

The fourteen-space is an invariant subspace of the edge permutation module.
The twenty-space is an invariant subspace of the permutation module on four
ordered letters, supported on configurations of two disjoint pairs. Checked
matrix-density certificates prove absolute irreducibility of both actual A₇
actions. Together they discharge `LargeModelsExist`, supplying the two larger
candidates for the six-class exhaustion argument. No table or classification
premise is used.

Source: the concrete candidates in the degree-spectrum argument for
Aschbacher–Smith K.1.2, printed p.452/PDF p.463.
-/

public section

open Representation
namespace CFSG.Quasithin.ChapterK.Alternating.SevenSmallSpectrum

/-- The independently constructed twenty-space completes the two large candidates. -/
theorem largeModelsExist_of_twenty
    (ρ₂₀ : Representation (ZMod 2) (alternatingGroup (Fin 7)) (Fin 20 → ZMod 2))
    (h₂₀ : IsAbsolutelyIrreducible ρ₂₀) : LargeModelsExist :=
  ⟨AlternatingSevenBinaryLargeModels.Fourteen.representation, ρ₂₀,
    AlternatingSevenBinaryLargeModels.Fourteen.absolutelyIrreducible, h₂₀⟩

/-- The actual fourteen- and twenty-dimensional binary A₇ representations are
absolutely irreducible, supplying both larger candidates for the spectrum. -/
theorem largeModelsExist : LargeModelsExist :=
  largeModelsExist_of_twenty AlternatingSevenBinaryLargeModels.Twenty.representation
    AlternatingSevenBinaryLargeModels.Twenty.absolutelyIrreducible

end CFSG.Quasithin.ChapterK.Alternating.SevenSmallSpectrum
