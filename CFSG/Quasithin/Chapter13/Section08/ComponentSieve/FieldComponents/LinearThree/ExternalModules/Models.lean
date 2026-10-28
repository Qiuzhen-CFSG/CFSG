module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Definitions
public import Theory.Representation.BinaryOffender.QuadraticSection

/-!+# The external-component module alternatives

The paired alternatives are actual representations of the fixed SL₃(2)
carrier, with intertwining equivalences. The natural tensor module is the
external tensor product with the two-dimensional augmentation module of S₃.
Chief sections use the literal quotient of two invariant subspaces, and the
component restriction uses the specified inclusion and group equivalence.

These are specifications for the two module arguments of Aschbacher–Smith
13.8.21(1), printed pp.956–957 (1 March 2004 manuscript). Their construction
from the source hypotheses is a separate obligation; none of these definitions
asserts that a source chief factor has the displayed form.
-/

@[expose] public section
open Representation Representation.BinaryOffender TensorProduct
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules

/-- One natural and one contragredient natural module. -/
noncomputable abbrev naturalDual := BinaryLinearThree.W.prod BinaryLinearThree.W.dual

/-- Two Steinberg modules for the same component. -/
noncomputable abbrev pairedSteinberg := BinaryLinearThree.S.prod BinaryLinearThree.S

/-- Two natural and two dual modules, grouped into natural-dual pairs. -/
noncomputable abbrev pairedNaturalDual := naturalDual.prod naturalDual

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]

/-- The precise K-module conclusion, with multiplicities and equivariance. -/
def PairedAlternatives (ρ : Representation (ZMod 2) BinaryLinearThree.Group U) : Prop :=
  Nonempty (ρ.Equiv pairedSteinberg) ∨ Nonempty (ρ.Equiv pairedNaturalDual)

/-- Restriction to the actual component through a specified identification. -/
def componentAction (ρ : Representation (ZMod 2) H U) (K : Subgroup H)
    (eK : K ≃* BinaryLinearThree.Group) :
    Representation (ZMod 2) BinaryLinearThree.Group U :=
  ρ.comp (K.subtype.comp eK.symm.toMonoidHom)

/-- Every noncentral chief section has the paired K-module form. The cover
relation refers to invariant subspaces of the original H-action. -/
def PairedNoncentralChiefFactors (ρ : Representation (ZMod 2) H U)
    (K : Subgroup H) (eK : K ≃* BinaryLinearThree.Group) : Prop :=
  ∀ L N : Subrepresentation ρ, L ⋖ N →
    (∃ k : K, ∃ v, sectionRepresentation ρ L N k v ≠ v) →
    PairedAlternatives (componentAction (sectionRepresentation ρ L N) K eK)

/-- The source direct-product actor, with the actual permutation S₃ carrier. -/
abbrev TensorGroup := BinaryLinearThree.Group × Equiv.Perm (Fin 3)

/-- The binary two-dimensional natural module for S₃. -/
abbrev S3Natural := BinaryPermutation.core (Fin 3)

noncomputable abbrev TensorSpace := BinaryLinearThree.Vector ⊗[ZMod 2] S3Natural

/-- The external product of the two natural actions. -/
noncomputable def naturalTensor : Representation (ZMod 2) TensorGroup TensorSpace :=
  Representation.tprod (BinaryLinearThree.W.comp (MonoidHom.fst _ _))
    ((BinaryPermutation.coreRepresentation (Fin 3)).comp (MonoidHom.snd _ _))

/-- A literal chief section identified with the natural tensor module using
the same marked product identification as the source geometry. -/
def IsNaturalTensorChiefSection (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* TensorGroup) (L N : Subrepresentation ρ) : Prop :=
  L ⋖ N ∧ Nonempty ((sectionRepresentation ρ L N).Equiv
    (naturalTensor.comp eH.toMonoidHom))

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules
