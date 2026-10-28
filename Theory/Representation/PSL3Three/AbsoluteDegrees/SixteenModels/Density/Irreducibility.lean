module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.Density
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels

/-!
# Application of the density certificate to the native action

The proved full matrix algebra certificate supplies exactly the premise of
`SixteenModels.irreducible_of_realizes`. A native action with the prescribed
ATLAS matrices is therefore irreducible without an additional density premise.
Constructing that action remains the independent native-action task.

Source: the degree-sixteen representations underlying GM02 Proposition 4.2,
pp.9–10; the literal ATLAS data are attributed in `SixteenModels.Data`.
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels
variable {F : Type*} [Field F] [CharP F 2]

theorem irreducible_of_realizes_parameter (t : F) (ht : t ^ 4 = t + 1)
    (ρ : Representation F Matrix.PSL3Three.PSL (Fin 16 → F)) (hρ : Realizes t ρ) :
    IsIrreducible ρ :=
  irreducible_of_realizes t ρ hρ (generatorDensity F t ht)

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels
