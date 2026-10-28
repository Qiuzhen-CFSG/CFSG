module

public import Mathlib.RepresentationTheory.Irreducible
public import Theory.LinearAlgebra.FiniteLengthSimpleQuotients

/-!
# Complete simple representation families

Coordinate spaces keep the family in a fixed universe. Completeness on these
spaces implies completeness on every finite-dimensional representation through
a chosen basis. Every simple module is a cyclic quotient of the regular group
algebra, which has finite length because the group is finite. The finite-length
simple-quotient theorem makes the set of isomorphism classes finite; choosing
one representative per class then gives a nonredundant complete family.

The construction uses the actual `asModule` actions and the equivalence between
intertwining maps and group-algebra linear maps from Mathlib's
`RepresentationTheory.Intertwining`. The cyclic quotient fact comes from
`RingTheory.SimpleModule.Basic`, and the finite-length argument is supplied by
`Theory.LinearAlgebra.FiniteLengthSimpleQuotients`, using Mathlib's composition
series theory. No semisimplicity of the regular representation, algebraic
closure of the field, or restriction on its characteristic is required.

This module supplies the finite simple-representation family used in the
construction of modular character bases. Only the family and its completeness
and existence theorems are public; the coordinate isomorphism-class quotient
is an implementation detail.
-/

open scoped MonoidAlgebra

universe u v w

namespace Representation

variable {k : Type u} {G : Type v} [Field k] [Group G]

private noncomputable def moduleEquivOfEquiv
    {V : Type*} {W : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] {ρ : Representation k G V}
    {σ : Representation k G W} (equiv : ρ.Equiv σ) :
    ρ.asModule ≃ₗ[k[G]] σ.asModule :=
  LinearEquiv.ofBijective
    (IntertwiningMap.equivLinearMapAsModule ρ σ equiv.toIntertwiningMap)
    equiv.toLinearEquiv.bijective

private noncomputable def equivOfModuleEquiv
    {V : Type*} {W : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] {ρ : Representation k G V}
    {σ : Representation k G W} (equiv : ρ.asModule ≃ₗ[k[G]] σ.asModule) :
    ρ.Equiv σ :=
  ((IntertwiningMap.equivLinearMapAsModule ρ σ).symm equiv.toLinearMap).ofBijective
    equiv.bijective

private theorem exists_coordinate_equiv
    {V : Type w} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : Representation k G V) [IsIrreducible ρ] :
    ∃ (dimension : ℕ) (σ : Representation k G (Fin dimension → k)),
      IsIrreducible σ ∧ Nonempty (σ.Equiv ρ) := by
  classical
  let basisEquiv := (Module.finBasis k V).equivFun
  let σ : Representation k G (Fin (Module.finrank k V) → k) :=
    (basisEquiv.conjAlgEquiv k).toAlgHom.toMonoidHom.comp ρ
  let equiv : ρ.Equiv σ := .mk basisEquiv (by
    intro groupElement
    ext vector
    simp [σ, LinearEquiv.conjAlgEquiv_apply])
  refine ⟨_, σ, ?_, ⟨equiv.symm⟩⟩
  rw [irreducible_iff_isSimpleModule_asModule]
  let moduleEquiv := moduleEquivOfEquiv equiv.symm
  exact moduleEquiv.isSimpleModule_iff.mpr inferInstance

/-- A finite, nonredundant family complete on coordinate simple representations.
The theorem `SimpleRepresentationFamily.complete` extends completeness to any
universe of finite-dimensional representation spaces. -/
public structure SimpleRepresentationFamily (k : Type u) (G : Type v)
    [Field k] [Group G] where
  size : ℕ
  dimension : Fin size → ℕ
  representation : (index : Fin size) → Representation k G (Fin (dimension index) → k)
  irreducible : ∀ index, IsIrreducible (representation index)
  pairwise_nonisomorphic : ∀ left right,
    Nonempty ((representation left).Equiv (representation right)) → left = right
  complete_coordinates : ∀ dimension (ρ : Representation k G (Fin dimension → k)),
    IsIrreducible ρ → ∃ index, Nonempty ((representation index).Equiv ρ)

/-- Coordinate completeness gives actual equivalences to all finite-dimensional
irreducible representations, without a restriction on the space's universe. -/
public theorem SimpleRepresentationFamily.complete
    (family : SimpleRepresentationFamily k G)
    {V : Type w} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : Representation k G V) [IsIrreducible ρ] :
    ∃ index, Nonempty ((family.representation index).Equiv ρ) := by
  obtain ⟨dimension, σ, simple, ⟨equiv⟩⟩ := exists_coordinate_equiv ρ
  obtain ⟨index, ⟨representativeEquiv⟩⟩ := family.complete_coordinates dimension σ simple
  exact ⟨index, ⟨representativeEquiv.trans equiv⟩⟩

private abbrev CoordinateSimple (k : Type u) (G : Type v) [Field k] [Group G] :=
  Σ dimension : ℕ, {ρ : Representation k G (Fin dimension → k) // IsIrreducible ρ}

private def coordinateSetoid : Setoid (CoordinateSimple k G) where
  r left right := Nonempty (left.2.1.Equiv right.2.1)
  iseqv := {
    refl := fun _ => ⟨.refl _⟩
    symm := fun ⟨equiv⟩ => ⟨equiv.symm⟩
    trans := fun ⟨first⟩ ⟨second⟩ => ⟨first.trans second⟩ }

private noncomputable def representative
    (index : Quotient (coordinateSetoid (k := k) (G := G))) : CoordinateSimple k G :=
  index.out

private theorem representative_eq_of_equiv
    (left right : Quotient (coordinateSetoid (k := k) (G := G)))
    (equiv : Nonempty ((representative left).2.1.Equiv (representative right).2.1)) :
    left = right := by
  have same := Quotient.sound (s := coordinateSetoid) equiv
  simpa only [representative, Quotient.out_eq] using same

private theorem family_of_finite_classes
    [Finite (Quotient (coordinateSetoid (k := k) (G := G)))] :
    Nonempty (SimpleRepresentationFamily k G) := by
  classical
  let classes := Quotient (coordinateSetoid (k := k) (G := G))
  let enumeration := Finite.equivFin classes
  let selected := fun index => representative (enumeration.symm index)
  refine ⟨{
    size := Nat.card classes
    dimension := fun index => (selected index).1
    representation := fun index => (selected index).2.1
    irreducible := fun index => (selected index).2.2
    pairwise_nonisomorphic := ?_
    complete_coordinates := ?_ }⟩
  · intro left right equiv
    exact enumeration.symm.injective (representative_eq_of_equiv _ _ equiv)
  · intro dimension ρ simple
    let coordinate : CoordinateSimple k G := ⟨dimension, ρ, simple⟩
    let index : classes := Quotient.mk _ coordinate
    refine ⟨enumeration index, ?_⟩
    change Nonempty ((representative (enumeration.symm (enumeration index))).2.1.Equiv ρ)
    rw [enumeration.symm_apply_apply]
    exact Quotient.exact (Quotient.out_eq index)

/-- Every finite group over a field has a finite, pairwise nonisomorphic
complete family of finite-dimensional irreducible representations. -/
public theorem exists_complete_simple_representation_family [Finite G] :
    Nonempty (SimpleRepresentationFamily k G) := by
  classical
  let classes := Quotient (coordinateSetoid (k := k) (G := G))
  let spaces := fun index : classes => (representative index).2.1.asModule
  let (index : classes) : IsIrreducible (representative index).2.1 :=
    (representative index).2.2
  let : IsNoetherianRing k[G] := IsNoetherianRing.of_finite k k[G]
  let : IsArtinianRing k[G] := IsArtinianRing.of_finite k k[G]
  have finiteLength : IsFiniteLength k[G] k[G] :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  have : Finite classes := finiteLength.finite_simple_quotients spaces
    (fun left right ⟨equiv⟩ =>
      representative_eq_of_equiv left right ⟨equivOfModuleEquiv equiv⟩)
    (by
      intro index
      have : Nontrivial (spaces index) := IsSimpleModule.nontrivial k[G] (spaces index)
      obtain ⟨vector, nonzero⟩ := exists_ne (0 : spaces index)
      exact ⟨LinearMap.toSpanSingleton k[G] (spaces index) vector,
        IsSimpleModule.toSpanSingleton_surjective k[G] nonzero⟩)
  exact family_of_finite_classes


end Representation
