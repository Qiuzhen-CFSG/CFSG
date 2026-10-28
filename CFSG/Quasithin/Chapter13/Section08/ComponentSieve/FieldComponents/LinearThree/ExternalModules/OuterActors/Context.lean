module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.Models
public import Theory.Representation.BinaryOffender.IrreducibleTransport
public import Theory.GroupTheory.GeneralizedFitting.Defs

/-!
# The paired-module outer-action setup

This records the actual normal subgroups K and X, their internal direct product
as F*(H), the faithful irreducible binary action, and its specified restriction
to K. Full conjugation image is stated using the literal automorphisms of K.
In particular the centralizer of K is retained in H; no identification of H
with Aut(K) is made.

These are inputs to the ordinary-A₆ branch of Aschbacher–Smith 13.8.21(1),
printed p.956, combined manuscript of 1 March 2004. The record contains no
actor-rank or fixed-codimension conclusions. Constructing it from the source
local configuration belongs to the external-component assembly.
-/

@[expose] public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.OuterActors

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]

/-- Conjugation by the actual ambient element is not induced by an element of K. -/
def OuterOnComponent (K : Subgroup H) (a : H) : Prop :=
  ¬ ∃ k : K, ∀ u : K, a * u.val * a⁻¹ = k.val * u.val * k.val⁻¹

/-- The structural and module inputs for the paired outer-actor calculation. -/
structure PairedSetup (σ : Representation (ZMod 2) H U)
    (K X : Subgroup H) (eK : K ≃* BinaryLinearThree.Group) : Prop where
  component_normal : K.Normal
  cyclic_normal : X.Normal
  cyclic : IsCyclic X
  cyclic_order : Nat.card X = 3
  commute : ∀ k ∈ K, ∀ x ∈ X, Commute k x
  disjoint : K ⊓ X = ⊥
  fitting : Theory.GroupTheory.generalizedFitting H = K ⊔ X
  faithful : Function.Injective σ
  irreducible : σ.IsIrreducible
  moved : subspaceCommutator σ ⊤ X = ⊤
  full_conjugation : ∀ α : MulAut K, ∃ h : H,
    ∀ k : K, h * k.val * h⁻¹ = (α k).val
  paired : PairedAlternatives (componentAction σ K eK)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.OuterActors
