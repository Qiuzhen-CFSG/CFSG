module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.Models
public import Theory.Representation.G2NaturalBinary

/-!
# Coordinates for the binary target in G.9.3(10)

The intrinsic natural action is expressed on `F₂⁶` in
`Theory.Representation.G2NaturalBinary`. Here the same coordinate map is
linear for the scalar restriction used by `derivedNaturalBinary`, and
intertwines that exact action with the coordinate action. The scalar module
structure is named explicitly because specializing a scalar restriction to
its base field need not give the native module instance definitionally.
No global instance is changed.

Source: Aschbacher--Smith G.9.3(10), printed pp.354,356--357, including the
actual derived group at the binary endpoint.
-/

@[expose] public noncomputable section

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.BinarySix

open Atlas.G2.Natural

attribute [local instance] ZMod.algebra

/-- The scalar module structure used by the generic target action in `Models`. -/
abbrev restrictedModule (F : Type*) [Field F] [CharP F 2] :
    Module (ZMod 2) (Space F) := inferInstance

/-- The exact specialization of that scalar structure at the binary field.
Consumers may enable it locally; this is not a global instance. -/
abbrev scalars : Module (ZMod 2) (Space (ZMod 2)) := restrictedModule (ZMod 2)

attribute [local instance] scalars

/-- Off-diagonal coordinates on the scalar-restricted target. Additive maps
between binary modules are automatically binary linear. -/
def coordinatesEquiv : Space (ZMod 2) ≃ₗ[ZMod 2] Binary.Six :=
  LinearEquiv.ofBijective (Binary.coordinatesEquiv.toAddMonoidHom.toZModLinearMap 2)
    Binary.coordinatesEquiv.bijective

/-- The coordinate model is equivalent to the precise target of G.9.3(10),
with the identity isomorphism on the actual commutator subgroup. -/
def coordinateEquiv : (derivedNaturalBinary (ZMod 2)).Equiv Binary.coordinateAction :=
  Representation.Equiv.mk coordinatesEquiv (by
    intro g
    apply LinearMap.ext
    intro v
    exact Binary.coordinatesEquiv_action g v)

/-- Dimension of the target with its specialized scalar instance. -/
theorem finrank_natural : Module.finrank (ZMod 2) (Space (ZMod 2)) = 6 :=
  coordinatesEquiv.finrank_eq.trans (by simp)

/-- Finite dimensionality with the same scalar instance as the target action. -/
theorem finiteDimensional_natural : FiniteDimensional (ZMod 2) (Space (ZMod 2)) :=
  Module.Finite.equiv coordinatesEquiv.symm

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.BinarySix
