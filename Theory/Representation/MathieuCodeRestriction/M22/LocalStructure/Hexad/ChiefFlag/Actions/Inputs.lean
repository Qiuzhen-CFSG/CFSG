module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.ChiefFlag.Spaces
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.ChiefFlag.Actions.Permutation
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.ChiefFlag.Actions.Linear

/-!
# Precise cocode witnesses for hexad duality

These inputs are the action statements of H.15.2, on the actual outer cocode,
its intrinsic hexad kernel, and the actual image of xi in the quotient by the
fixed space. The kernel module is marked by a group isomorphism intertwining
conjugation. No code conclusion or chiefness assertion is an input.

The earlier H.14 kernel model has its own permutation marking. In particular,
we do not identify it with the natural section for the six-point marking of
the cocode fixed space without an intertwiner.

Source: Aschbacher--Smith H.14.4, H.15.2(2),(6), and H.16.4(1)--(3), printed
pp.397--399,403, combined manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
open Representation Representation.BinaryOffender
namespace MathieuCode.Hexad.ChiefFlag.Actions

abbrev codeAction := m22OuterCodeRepresentation.comp Stabilizer.subtype
abbrev cocodeAction := m22OuterCocodeRepresentation.comp Stabilizer.subtype
abbrev U := cocodeFixedSubrepresentation
abbrev V1 := codeFixedSubrepresentation
abbrev V5 := codeCommutatorSubrepresentation

/-- Normality is relative to the hexad stabilizer. -/
instance kernel_relativeNormal : (Kernel.subgroupOf Stabilizer).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer stabilizer_le_normalizer

def kernelInclusion : Kernel →* Stabilizer := Subgroup.inclusion kernel_le_stabilizer

def cocodeKernelAction : Kernel →* BinaryLinear.GL (M22Cocode ⧸ U.toSubmodule) :=
  (linearAction U.quotientRepresentation).comp kernelInclusion

def codeKernelAction : Kernel →* BinaryLinear.GL V5.toSubmodule :=
  (linearAction V5.toRepresentation).comp kernelInclusion

/-- The literal source axis xi/U, without replacing it by an abstract four-space. -/
def cocodeAxis : Submodule (ZMod 2) (M22Cocode ⧸ U.toSubmodule) :=
  (fixedSpaceSpan m22OuterCocodeRepresentation Kernel).map U.toSubmodule.mkQ

/-- Precisely the permitted H.15.2 action witnesses. -/
structure CocodeActionData (E : Type*) [AddCommGroup E] [Module (ZMod 2) E] where
  quotientMap : Stabilizer →* Equiv.Perm (Fin 6)
  quotientMap_surjective : Function.Surjective quotientMap
  quotientMap_ker : quotientMap.ker = Kernel.subgroupOf Stabilizer
  fixedEquiv : U.toSubmodule ≃ₗ[ZMod 2] BinaryPermutation.Deleted (Fin 6)
  fixedEquiv_equivariant : ∀ g v, fixedEquiv (U.toRepresentation g v) =
    BinaryPermutation.deletedRepresentation (Fin 6) (quotientMap g) (fixedEquiv v)
  axis : Subrepresentation U.quotientRepresentation
  axis_space : axis.toSubmodule = cocodeAxis
  kernelRepresentation : Representation (ZMod 2) Stabilizer E
  kernelMarking : Multiplicative E ≃* Kernel
  kernelMarking_equivariant : ∀ (g : Stabilizer) v,
    (kernelMarking (Multiplicative.ofAdd (kernelRepresentation g v))).val =
      g.val * (kernelMarking (Multiplicative.ofAdd v)).val * g.val⁻¹
  axisEquiv : axis.toSubmodule ≃ₗ[ZMod 2] E
  axisEquiv_equivariant : ∀ g v, axisEquiv (axis.toRepresentation g v) =
    kernelRepresentation g (axisEquiv v)
  axisAction_full : cocodeKernelAction.range = BinaryLinear.radical axis.toSubmodule

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

/-- The genuine quotient by the intrinsic kernel, with the given six-point marking. -/
def CocodeActionData.symmetricQuotientEquiv (D : CocodeActionData E) :
    (Stabilizer ⧸ Kernel.subgroupOf Stabilizer) ≃* Equiv.Perm (Fin 6) :=
  QuotientGroup.liftEquiv _ D.quotientMap_surjective D.quotientMap_ker.symm

@[simp] theorem CocodeActionData.symmetricQuotientEquiv_mk (D : CocodeActionData E)
    (g : Stabilizer) :
    D.symmetricQuotientEquiv (QuotientGroup.mk g) = D.quotientMap g := rfl

/-- An earlier H.14 identification of the actual kernel conjugation module.
Its marking may differ from the six-point marking in `CocodeActionData`. -/
structure KernelModel {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (D : CocodeActionData E) where
  quotientMap : Stabilizer →* Equiv.Perm (Fin 6)
  quotientMap_surjective : Function.Surjective quotientMap
  quotientMap_ker : quotientMap.ker = Kernel.subgroupOf Stabilizer
  naturalEquiv : E ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6)
  naturalEquiv_equivariant : ∀ g v, naturalEquiv (D.kernelRepresentation g v) =
    BinaryPermutation.naturalRepresentation (Fin 6) (quotientMap g) (naturalEquiv v)

end MathieuCode.Hexad.ChiefFlag.Actions
