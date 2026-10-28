module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Setup
public import Theory.Representation.SymplecticNatural
public import Theory.Representation.EndFieldRep
public import Theory.Representation.ExtendScalars
public import Theory.Representation.FirstCohomologyCyclic
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.Basic

/-!
# Actual representation identifications for K.3.4

The tensor is the natural four-space tensored with its coefficient twist.
Descent is expressed by an intertwiner from the scalar extension of the
original representation over its actual Schur endomorphism field. In
particular, a natural-plus-graph direct sum does not inhabit this interface.
The dimension 16s follows from this scalar extension and the Schur-field
order, rather than being included in the identification.

These structures specify the recognition targets; no classification theorem
or inhabitant of either target is asserted here. Source: Aschbacher–Smith,
K.3.4, printed pp.456–457, citing GM04 Proposition 6.2 and Table 9.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.Symplectic
open scoped TensorProduct MonoidAlgebra
open Representation
open Theory.SpecificGroups.SymplecticFour

variable {F : Type*} [Field F]

/-- The actual natural tensor coefficient-twisted natural representation. -/
noncomputable def twistedTensor (σ : F ≃+* F) :
    Representation F (Sp F) (Vector F ⊗[F] Vector F) :=
  (symplecticNatural 2).tprod
    ((symplecticNatural 2).comp (DiagramAutomorphisms.fieldAutomorphism σ).toMonoidHom)

/-- The scalar-extended tensor has dimension sixteen over its defining field. -/
theorem twistedTensor_finrank : Module.finrank F (Vector F ⊗[F] Vector F) = 16 := by
  rw [Module.finrank_tensorProduct]
  norm_num [Theory.SpecificGroups.SymplecticFour.Vector, Module.finrank_pi_fintype]

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) D V)
  [ρ.IsIrreducible]

/-- The actual commuting endomorphism field of the component action. -/
abbrev SchurField := Module.End (ZMod 2)[D] ρ.asModule

/-- Natural-module recognition requires genuine group, module, and Schur-field maps. -/
structure NaturalIdentification [Algebra (ZMod 2) F] where
  groupEquiv : D ≃* Sp F
  linearEquiv : V ≃ₗ[ZMod 2] Vector F
  intertwines : ∀ g v, linearEquiv (ρ g v) =
    symplecticNatural 2 (groupEquiv g) (linearEquiv v)
  schurEquiv : SchurField ρ ≃+* F

/-- Recognition of the descended tensor over the actual endomorphism field.
The degree-two extension and its nontrivial involution retain the source's
Galois convention. All module identifications use the displayed group map. -/
structure TensorIdentification (F : Type*) [Field F]
    [Algebra (SchurField ρ) F] (s : ℕ) where
  groupEquiv : D ≃* Sp F
  sigma : F ≃ₐ[SchurField ρ] F
  sigma_ne : sigma ≠ AlgEquiv.refl
  sigma_involutive : Function.Involutive sigma
  extension_degree : Module.finrank (SchurField ρ) F = 2
  schur_card : Nat.card (SchurField ρ) = 2 ^ s
  field_card : Nat.card F = 2 ^ (2 * s)
  linearEquiv : (F ⊗[SchurField ρ] ρ.asModule) ≃ₗ[F] (Vector F ⊗[F] Vector F)
  intertwines : ∀ g v, linearEquiv (extendScalars F ρ.endFieldRep g v) =
    twistedTensor sigma.toRingEquiv (groupEquiv g) (linearEquiv v)

variable {ρ}

omit [FiniteDimensional (ZMod 2) V] [ρ.IsIrreducible] in
/-- An actual natural identification yields the stated binary dimension. -/
theorem NaturalIdentification.finrank [Finite F] [Algebra (ZMod 2) F]
    {r : ℕ} (hF : Nat.card F = 2 ^ r) (h : NaturalIdentification (F := F) ρ) :
    Module.finrank (ZMod 2) V = 4 * r := by
  rw [h.linearEquiv.finrank_eq, Module.finrank_pi_fintype]
  simp [OneCohomology.coefficient_finrank_of_card 2 r hF]

/-- Scalar extension preserves dimension, so the descended module is 16-dimensional
over its actual Schur field. -/
theorem TensorIdentification.schur_finrank [Algebra (SchurField ρ) F]
    {s : ℕ} (h : TensorIdentification ρ F s) :
    Module.finrank (SchurField ρ) ρ.asModule = 16 := by
  rw [← Module.finrank_baseChange (R := F), h.linearEquiv.finrank_eq]
  exact twistedTensor_finrank

/-- K.3.4.2's binary degree is derived from the tensor identification. -/
theorem TensorIdentification.binary_finrank [Algebra (SchurField ρ) F]
    {s : ℕ} (h : TensorIdentification ρ F s) :
    Module.finrank (ZMod 2) V = 16 * s := by
  rw [← ρ.asModuleEquiv.finrank_eq, ← Module.finrank_mul_finrank (ZMod 2) (SchurField ρ),
    h.schur_finrank, OneCohomology.coefficient_finrank_of_card 2 s h.schur_card]
  omega

end CFSG.Quasithin.ChapterK.Symplectic
