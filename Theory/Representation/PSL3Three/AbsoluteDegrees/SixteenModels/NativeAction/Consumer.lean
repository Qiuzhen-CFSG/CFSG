module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels

/-!
# Application of the native action to the four-model construction

`sixteenModelsExist_of_density` discharges the action premise of
`SixteenModels.sixteenModelsExist_of_certificates` using the complete native
construction. The independent density certificate is retained with its existing
producer. No simplicity or inequivalence premise is added. Final unconditional
assembly remains with the owner of `SixteenModels`.

Source: GM02 Proposition 4.2, manuscript pp.9–10; numerical generator data and
ATLAS attribution are in `SixteenModels.Data`.
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction

universe v

theorem sixteenModelsExist_of_packed (h : Packed.MultiplicationCorrect)
    (E : Packed.Certificate) (hd : GeneratorDensity.{v}) : SixteenModelsExist.{v} :=
  sixteenModelsExist_of_certificates (actionsExist_of_packed h E) hd

/-- The native construction discharges the action assumption; matrix density
is the sole remaining premise for the four simple, inequivalent models. -/
theorem sixteenModelsExist_of_density (hd : GeneratorDensity.{v}) : SixteenModelsExist.{v} :=
  sixteenModelsExist_of_certificates actionsExist hd

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction
