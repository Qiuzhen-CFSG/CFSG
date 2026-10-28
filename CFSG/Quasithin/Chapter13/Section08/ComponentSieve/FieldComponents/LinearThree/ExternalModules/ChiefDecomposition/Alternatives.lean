module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.Models
public import Theory.Representation.AbsolutelyIrreducible
public import Theory.GroupTheory.GeneralizedFitting.Defs
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Inputs and tensor alternatives for the external linear-three action

The H.6.1 input classifies nontrivial irreducible component modules by actual
intertwining equivalences and separately records absolute irreducibility.
The product alternatives retain the natural, dual-natural and Steinberg tensor
modules with the concrete S₃ augmentation module. The A₆ structural interface
uses the intrinsic generalized Fitting subgroup and the full conjugation map.
None of these interfaces asserts a chief-factor decomposition.

Source: Aschbacher–Smith H.6.1 and 13.8.21(1), printed pp.386 and 956–957,
combined manuscript of 1 March 2004.
-/

@[expose] public section

open Representation Representation.BinaryOffender TensorProduct
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules
universe u

/-- The part of H.6.1 consumed by this decomposition, together with the
absolute irreducibility of its three nontrivial models. This is an explicit
earlier-result input, not an assertion that H.6.1 has been proved here. -/
structure LinearThreeIrreducibleCatalogue : Prop where
  classify : ∀ (V : Type u) [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (σ : Representation (ZMod 2) BinaryLinearThree.Group V),
    IsIrreducible σ → (∃ k v, σ k v ≠ v) →
    Nonempty (σ.Equiv BinaryLinearThree.W) ∨
      Nonempty (σ.Equiv BinaryLinearThree.W.dual) ∨ Nonempty (σ.Equiv BinaryLinearThree.S)
  natural_absolute : IsAbsolutelyIrreducible BinaryLinearThree.W
  dual_absolute : IsAbsolutelyIrreducible BinaryLinearThree.W.dual
  steinberg_absolute : IsAbsolutelyIrreducible BinaryLinearThree.S

/-- External tensoring with the concrete S₃ augmentation action. -/
noncomputable def tensorWithS3 {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) BinaryLinearThree.Group V) :
    Representation (ZMod 2) TensorGroup (V ⊗[ZMod 2] S3Natural) :=
  Representation.tprod (σ.comp (MonoidHom.fst _ _))
    ((BinaryPermutation.coreRepresentation (Fin 3)).comp (MonoidHom.snd _ _))

noncomputable abbrev dualNaturalTensor := tensorWithS3 BinaryLinearThree.W.dual
noncomputable abbrev steinbergTensor := tensorWithS3 BinaryLinearThree.S

/-- All three possibilities are retained before the parent's numerical sieve. -/
def TensorAlternatives {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) TensorGroup V) : Prop :=
  Nonempty (σ.Equiv naturalTensor) ∨ Nonempty (σ.Equiv dualNaturalTensor) ∨
    Nonempty (σ.Equiv steinbergTensor)

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]

/-- The product conclusion on literal chief sections, transported using the
specified group identification. The first factor is the marked component. -/
def TensorNoncentralChiefFactors (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* TensorGroup) : Prop :=
  ∀ L N : Subrepresentation ρ, L ⋖ N →
    (∃ k : BinaryLinearThree.Group, ∃ v,
      sectionRepresentation ρ L N (eH.symm (k, 1)) v ≠ v) →
    TensorAlternatives ((sectionRepresentation ρ L N).comp eH.symm.toMonoidHom)

/-- Genuine structural data for the A₆ branch. The generalized Fitting
subgroup is the internal direct product of the marked normal factors, and
the conjugation map has the entire automorphism group as its image. -/
structure PairedStructure (K X : Subgroup H) [K.Normal] [X.Normal] : Prop where
  card_three : Nat.card X = 3
  commute : ∀ k : K, ∀ x : X, Commute (k : H) (x : H)
  disjoint : Disjoint K X
  fitting : Theory.GroupTheory.generalizedFitting H = K ⊔ X
  full_conjugation : Function.Surjective (MulAut.conjNormal (H := K) : H →* MulAut K)
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules