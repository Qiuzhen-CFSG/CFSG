module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.ChiefFlag.Spaces
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryTransvectionGroups.Basic
public import Theory.Representation.BinaryPermutationNaturalStructure

/-!
# Explicit action data for the hexad fixed quotient

These are the permitted independently constructed inputs from H.16.4(1)--(3).
The five-space is the actual code commutator and the one-space the actual
kernel fixed space. The kernel is marked multiplicatively, so the dual
identification retains conjugation rather than a group-family label. The
six-point marking retains the genuine quotient map and every intertwiner.
No fixed-quotient assertion or involution intersection is an input.

Source: Aschbacher--Smith, H.16.4, printed p.403, manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
namespace MathieuCode.Hexad.ChiefFlag.FixedQuotientData
open Representation Representation.BinaryOffender

abbrev codeAction := m22OuterCodeRepresentation.comp Stabilizer.subtype
abbrev V1 := codeFixedSubrepresentation
abbrev V5 := codeCommutatorSubrepresentation

/-- The literal fixed line inside the actual commutator space. -/
def center : Subrepresentation V5.toRepresentation := sectionLower codeAction V1 V5

/-- The representation as invertible linear transformations. -/
def linearAction {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W) : G →* BinaryLinear.GL W :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).toMonoidHom.comp
    ρ.asGroupHom

/-- The actual kernel action on V5, with its relative inclusion in the stabilizer. -/
def kernelAction : Kernel →* BinaryLinear.GL V5.toSubmodule :=
  (linearAction V5.toRepresentation).comp (Subgroup.inclusion kernel_le_stabilizer)

/-- Independent chief/action data. The parent constructs these by duality;
the fixed-quotient argument does not assume its own conclusion. -/
structure Actions (E : Type*) [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] where
  six : Subrepresentation codeAction
  five_le_six : V5 ≤ six
  six_dim : Module.finrank (ZMod 2) six.toSubmodule = 6
  transvections_faithful : Function.Injective kernelAction
  transvections_full : kernelAction.range = BinaryLinear.radical center.toSubmodule
  conjugation : Representation (ZMod 2) Stabilizer E
  kernelMarking : Multiplicative E ≃* Kernel
  kernelMarking_equivariant : ∀ (g : Stabilizer) (v : E),
    (kernelMarking (Multiplicative.ofAdd (conjugation g v))).val =
      g.val * (kernelMarking (Multiplicative.ofAdd v)).val * g.val⁻¹
  middleEquiv : (V5.toSubmodule ⧸ center.toSubmodule) ≃ₗ[ZMod 2]
    Module.Dual (ZMod 2) E
  middleEquiv_equivariant : ∀ (g : Stabilizer) v,
    middleEquiv (center.quotientRepresentation g v) = conjugation.dual g (middleEquiv v)
  quotientMap : Stabilizer →* Equiv.Perm (Fin 6)
  quotientMap_surjective : Function.Surjective quotientMap
  quotientMap_ker : quotientMap.ker = Kernel.subgroupOf Stabilizer
  coreEquiv : (M22Code ⧸ V5.toSubmodule) ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 6)
  coreEquiv_equivariant : ∀ (g : Stabilizer) v,
    coreEquiv (V5.quotientRepresentation g v) =
      BinaryPermutation.coreRepresentation (Fin 6) (quotientMap g) (coreEquiv v)

end MathieuCode.Hexad.ChiefFlag.FixedQuotientData
