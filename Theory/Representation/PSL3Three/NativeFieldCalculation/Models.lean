module

public import Theory.Representation.PSL3Three.NativeFieldCalculation
public import Theory.Representation.PSL3Three.AbsoluteDegrees.OddClasses
public import Theory.Representation.PSL3Three.AbsoluteDegrees.PrincipalModels
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels

/-!
# The unconditional native degree-sixteen field obstruction

The checked conjugacy certificates prove the seven-class bound. Applying this
bound to the Frobenius obstruction first leaves the two independent simple-model
construction contracts. The geometric degree-twelve and degree-twenty-six models
and the four checked degree-sixteen actions discharge both contracts. Thus every
absolute degree-sixteen module has a nonbinary trace, and cannot be defined over
the binary prime field. The actual Schur endomorphism-field descent then gives
degree twelve for every faithful irreducible binary module of degree at most
eighteen.

Source context: Guralnick--Malle, *Classification of 2F-modules I*, Proposition
4.2. No character table, field table or lifting theorem is assumed. The final
exports below have no construction, class-count or field-obstruction premises.
-/

namespace Representation.PSL3Three.NativeFieldCalculation
open AbsoluteDegrees
universe v

/-- No binary definition for an absolute degree-sixteen module, once the two
native model-construction families have been supplied. The class bound is proved. -/
public theorem degreeSixteenFieldObstruction_of_models
    (hprincipal : PrincipalModelsExist.{v}) (hsixteen : SixteenModelsExist.{v}) :
    DegreeSixteenFieldObstruction.{v} :=
  degreeSixteenFieldObstruction_of_native_inputs hprincipal hsixteen
    Matrix.PSL3Three.odd_conjClasses_card_le_seven

/-- The actual binary descent requires only the two construction families. -/
public theorem binary_degree_twelve_of_models
    (hprincipal : PrincipalModelsExist.{v}) (hsixteen : SixteenModelsExist.{v})
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) Matrix.PSL3Three.PSL W) [IsIrreducible σ]
    (hf : Function.Injective σ) (hd : Module.finrank (ZMod 2) W ≤ 18) :
    Module.finrank (ZMod 2) W = 12 :=
  binary_degree_twelve_of_native_inputs hprincipal hsixteen
    Matrix.PSL3Three.odd_conjClasses_card_le_seven σ hf hd

/-- Every irreducible degree-sixteen module over an algebraically closed field
of characteristic two has a trace outside the binary prime field. -/
public theorem exists_character_sq_ne_of_degree_sixteen
    {F W : Type v} [Field F] [IsAlgClosed F] [CharP F 2]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (σ : Representation F Matrix.PSL3Three.PSL W) [IsIrreducible σ]
    (hdim : Module.finrank F W = 16) :
    ∃ g, σ.character g ^ 2 ≠ σ.character g :=
  exists_character_sq_ne principalModelsExist SixteenModels.sixteenModelsExist
    Matrix.PSL3Three.odd_conjClasses_card_le_seven σ hdim

/-- The requested field-of-definition obstruction for arbitrary faithful
absolutely irreducible degree-sixteen representations of the native PSL₃(3).
All native calculation and model-construction premises are discharged. -/
public theorem degreeSixteenFieldObstruction : DegreeSixteenFieldObstruction.{v} :=
  degreeSixteenFieldObstruction_of_models
    principalModelsExist SixteenModels.sixteenModelsExist

/-- Unconditional binary descent on the literal projective matrix group.
Only irreducibility, faithfulness and the degree bound are required. -/
public theorem binary_degree_twelve
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) Matrix.PSL3Three.PSL W) [IsIrreducible σ]
    (hf : Function.Injective σ) (hd : Module.finrank (ZMod 2) W ≤ 18) :
    Module.finrank (ZMod 2) W = 12 :=
  binary_degree_twelve_of_models
    principalModelsExist SixteenModels.sixteenModelsExist σ hf hd

end Representation.PSL3Three.NativeFieldCalculation
