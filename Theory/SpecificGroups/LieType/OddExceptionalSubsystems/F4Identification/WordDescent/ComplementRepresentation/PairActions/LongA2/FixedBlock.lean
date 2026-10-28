module
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.AdjointRestriction.RootLifts
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.AdjointRestriction.Curves
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.Eigenspaces
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# The fixed-block action from the literal orbit-sum comparison

The existing map from the F4 Geck coordinates is injective and lands in the
fixed E6 diagram eigenspace. Surjectivity makes it a linear equivalence, along
which the actual F4 matrix-cover action transports. The proved polynomial
specialization then supplies exactly the signed folded-generator marking.

Surjectivity and the integral polynomial identity remain explicit. The
`LongA2.actionOfIntegralComparison` consumer combines this representation
with the concrete complement injection; neither representation irreducibility
nor division by three is used. Source: GLS3 §2.6.2, the common-lattice
construction, and Aschbacher--Smith A.2.17, printed p.39.
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.LongA2.FixedBlock
open WordDescent AdjointRestriction Matrix
attribute [local instance] Classical.decEq
local instance : Fintype Theory.AlgebraicGroup.StandardRootSystem.typeF4Roots := Fintype.ofFinite _
variable (F : Type*) [Field F]

/-- The existing integral orbit-sum map, with its codomain restricted. -/
def comparison : (SourceIndex → F) →ₗ[F] fixedSpace F :=
  (AdjointRestriction.linearMap F).codRestrict _ (by
    intro x
    rw [mem_eigenspace, one_smul]
    ext i
    exact linearMap_diagram F x i)

@[simp] theorem comparison_val (x : SourceIndex → F) :
    (comparison F x : Space F) = AdjointRestriction.linearMap F x := rfl

theorem comparison_injective : Function.Injective (comparison F) := by
  intro x y h
  exact AdjointRestriction.linearMap_injective F (congrArg Subtype.val h)

/-- Surjectivity is the remaining geometric assertion, not an assumption of
irreducibility or a hidden choice of model. -/
def comparisonEquiv (hsurj : Function.Surjective (comparison F)) :
    (SourceIndex → F) ≃ₗ[F] fixedSpace F :=
  LinearEquiv.ofBijective (comparison F) ⟨comparison_injective F, hsurj⟩

/-- The literal matrix-cover action on its 52-coordinate space. -/
def sourceAction : Cover F →* ((SourceIndex → F) ≃ₗ[F] (SourceIndex → F)) :=
  (Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F (SourceIndex → F))).toMonoidHom.comp
      (Cover F).subtype

@[simp] theorem sourceAction_apply (g : Cover F) (x : SourceIndex → F) :
    sourceAction F g x = g.val.val *ᵥ x := rfl

/-- Transport along the actual orbit-sum equivalence. -/
def representation (hsurj : Function.Surjective (comparison F)) :
    Cover F →* (fixedSpace F ≃ₗ[F] fixedSpace F) where
  toFun g := (comparisonEquiv F hsurj).symm.trans
    ((sourceAction F g).trans (comparisonEquiv F hsurj))
  map_one' := by
    ext v
    simp
  map_mul' g h := by
    ext v
    simp

@[simp] theorem representation_comparison
    (hsurj : Function.Surjective (comparison F)) (g : Cover F) (x : SourceIndex → F) :
    representation F hsurj g (comparison F x) =
      comparison F (g.val.val *ᵥ x) := by
  change comparisonEquiv F hsurj (sourceAction F g
    ((comparisonEquiv F hsurj).symm (comparisonEquiv F hsurj x))) = _
  rw [LinearEquiv.symm_apply_apply, sourceAction_apply]
  rfl

/-- The independent integral curve identity gives both signed markings with
the unchanged parameter, including in characteristic three. -/
theorem representation_simple (hsurj : Function.Surjective (comparison F))
    (hpoly : ∀ s i,
      foldedCurve (Polynomial ℤ) s i Polynomial.X * matrix (Polynomial ℤ) =
        matrix (Polynomial ℤ) * sourceCurve (Polynomial ℤ) s i Polynomial.X)
    (s : Bool) (i : Fin 4) (t : F) :
    representation F hsurj (coverSimple F s i t) =
      eigenspaceAction F 1 (f4Simple F s i t) := by
  apply LinearEquiv.ext
  intro v
  obtain ⟨x, rfl⟩ := hsurj v
  rw [representation_comparison]
  apply Subtype.ext
  exact (simple_mulVec_intertwines_of_integral_polynomial F hpoly s i t x).symm

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.LongA2.FixedBlock
