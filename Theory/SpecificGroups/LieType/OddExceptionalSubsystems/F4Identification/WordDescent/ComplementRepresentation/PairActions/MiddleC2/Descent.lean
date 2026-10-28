module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions.Transport
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.Coordinates
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.AdjointRestriction.Curves
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions.MiddleC2.FiniteLattice
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Middle C2 descent from explicit coordinate comparisons

An injective integral map from the finite complementary lattice into the
finite F4 lattice intertwines all four signed polynomial curves. Coordinate
comparisons with the actual root-indexed Geck spaces therefore transport
identity words from the literal F4 cover to the E6 complement. Descent along
word evaluation constructs a homomorphism on the actual pair subgroup.

The source and target coordinate comparisons remain explicit: the finite
tables alone do not identify either actual representation. This construction
needs neither an Sp4 recognition theorem nor irreducibility, and its integral
recovery identity uses only invertibility of two.

Sources: GLS3 §2.6.2, the common-lattice construction, and the F4 inclusions in
Aschbacher--Smith A.2.17, printed p.39 (`refs/quasithin.pdf`).
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.MiddleC2
open WordDescent AdjointRestriction Matrix
attribute [local instance] Classical.decEq
local instance : Fintype Theory.AlgebraicGroup.StandardRootSystem.typeF4Roots := Fintype.ofFinite _

variable (F : Type*) [Field F]

/-- The literal F4 cover acting on its own root-indexed Geck coordinates. -/
def coverAction : Cover F →* ((SourceIndex → F) ≃ₗ[F] (SourceIndex → F)) :=
  (Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F (SourceIndex → F))).toMonoidHom.comp
      (Cover F).subtype

@[simp] theorem coverAction_apply (g : Cover F) (v : SourceIndex → F) :
    coverAction F g v = g.val.val *ᵥ v := rfl

/-- Exact signed polynomial comparison on the actual F4 coordinate space. -/
structure SourceComparison where
  chart : (Fin 52 → F) ≃ₗ[F] (SourceIndex → F)
  map_curve : ∀ (s k : Bool) (t : F) (v : Fin 52 → F),
    chart (FiniteLattice.sourceCurve F s k t v) =
      sourceCurve F s (pairNode 1 2 k) t *ᵥ chart v

/-- Exact signed polynomial comparison with the literal minus-one eigenspace. -/
structure ComplementComparison where
  chart : complementSpace F ≃ₗ[F] (Fin 26 → F)
  map_curve : ∀ (s k : Bool) (t : F) (v : complementSpace F),
    chart (eigenspaceAction F (-1) (f4Simple F s (pairNode 1 2 k) t) v) =
      FiniteLattice.targetCurve F s k t (chart v)

variable (S : SourceComparison F) (C : ComplementComparison F)

/-- The concrete finite lattice embedding transported to the actual spaces. -/
def comparisonEmbedding : complementSpace F →ₗ[F] (SourceIndex → F) :=
  S.chart.toLinearMap.comp ((FiniteLattice.embedding F).comp C.chart.toLinearMap)

@[simp] theorem comparisonEmbedding_apply (v : complementSpace F) :
    comparisonEmbedding F S C v = S.chart (FiniteLattice.embedding F (C.chart v)) := rfl

theorem comparisonEmbedding_injective (htwo : (2 : F) ≠ 0) :
    Function.Injective (comparisonEmbedding F S C) :=
  S.chart.injective.comp ((FiniteLattice.embedding_injective F htwo).comp C.chart.injective)

/-- Both exact coordinate comparisons feed the actual signed-generator equation. -/
theorem comparisonEmbedding_simple (s k : Bool) (t : F) (v : complementSpace F) :
    comparisonEmbedding F S C
        (eigenspaceAction F (-1) (f4Simple F s (pairNode 1 2 k) t) v) =
      coverAction F (coverSimple F s (pairNode 1 2 k) t)
        (comparisonEmbedding F S C v) := by
  simp only [comparisonEmbedding_apply, C.map_curve]
  rw [← FiniteLattice.curve_intertwines, S.map_curve, coverAction_apply,
    coverSimple_matrix]

/-- Word action on the actual complementary eigenspace. -/
def complementWordAction : PairWord F →* (complementSpace F ≃ₗ[F] complementSpace F) :=
  ((eigenspaceAction F (-1)).comp (foldedEvaluation F)).comp (pairInclusion F 1 2)

@[simp] theorem complementWordAction_of (s k : Bool) (t : F) :
    complementWordAction F (FreeGroup.of (s, k, t)) =
      eigenspaceAction F (-1) (f4Simple F s (pairNode 1 2 k) t) := by
  simp [complementWordAction]

/-- Multiplication and inversion extend the four marked comparisons to every word. -/
theorem comparisonEmbedding_word (w : PairWord F) (v : complementSpace F) :
    comparisonEmbedding F S C (complementWordAction F w v) =
      coverAction F (pairEvaluation F 1 2 w) (comparisonEmbedding F S C v) := by
  induction w using FreeGroup.induction_on generalizing v with
  | C1 => simp
  | of x =>
    obtain ⟨s, k, t⟩ := x
    simpa only [complementWordAction_of, pairEvaluation_of] using
      comparisonEmbedding_simple F S C s k t v
  | inv_of x ih =>
    simp only [map_inv]
    change comparisonEmbedding F S C ((complementWordAction F (FreeGroup.of x)).symm v) =
      (coverAction F (pairEvaluation F 1 2 (FreeGroup.of x))).symm
        (comparisonEmbedding F S C v)
    apply (coverAction F (pairEvaluation F 1 2 (FreeGroup.of x))).injective
    rw [LinearEquiv.apply_symm_apply]
    simpa only [LinearEquiv.apply_symm_apply] using
      (ih ((complementWordAction F (FreeGroup.of x)).symm v)).symm
  | mul x y hx hy =>
    simp only [map_mul, LinearEquiv.mul_apply, hx, hy]

include S C in
/-- A literal F4 pair relation acts trivially on the actual E6 complement. -/
theorem complementWordAction_eq_one (htwo : (2 : F) ≠ 0) (w : PairWord F)
    (hw : pairEvaluation F 1 2 w = 1) : complementWordAction F w = 1 := by
  apply LinearEquiv.ext
  intro v
  apply comparisonEmbedding_injective F S C htwo
  rw [comparisonEmbedding_word, hw, map_one]
  rfl

/-- The local action, conditional only on the two concrete coordinate comparisons. -/
def actionOfComparisons (htwo : (2 : F) ≠ 0) : PairAction F 1 2 where
  hom := (pairEvaluationRange F 1 2).liftOfSurjective
    (pairEvaluationRange_surjective F 1 2)
    ⟨complementWordAction F, by
      intro w hw
      apply complementWordAction_eq_one F S C htwo
      exact congrArg Subtype.val hw⟩
  map_generator s k t := by
    change (pairEvaluationRange F 1 2).liftOfSurjective _ _
      (pairEvaluationRange F 1 2 (FreeGroup.of (s, k, t))) = _
    rw [MonoidHom.liftOfRightInverse_comp_apply]
    exact complementWordAction_of F s k t

@[simp] theorem actionOfComparisons_map_generator (htwo : (2 : F) ≠ 0)
    (s k : Bool) (t : F) :
    (actionOfComparisons F S C htwo).hom (pairGenerator F 1 2 s k t) =
      eigenspaceAction F (-1) (f4Simple F s (pairNode 1 2 k) t) :=
  (actionOfComparisons F S C htwo).map_generator s k t

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.MiddleC2
