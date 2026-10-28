module

public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.Coordinates
public import Theory.Representation.FactorDegreeFiltration

/-!
# Restricting the natural induced filtration from F₄ to F₂

The actual central element acts as omega on every transversal slot of the
natural induced module. This follows from centrality and the proved marked
point-stabilizer equivalence. On every invariant quotient, the same action
makes binary invariant subspaces closed under F₄ scalars. Thus scalar
restriction preserves simplicity and doubles each factor degree.

`binary_filtration` transports the actual invariant subspaces and literal
quotients of an arbitrary field filtration. Its natural-module application
reduces the required binary degrees to field degrees 6, 15 and 45. The field
filtration remains an explicit premise, not an assumed source theorem.
Source context: Guralnick–Malle, Classification of 2F-modules I,
Proposition 5.1, pp.15–16 and Theorem 6.6/Table 6.7.
-/

@[expose] public noncomputable section

open Representation
open Representation.SL3FourLocalCatalogue
open scoped Matrix
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates
open Uniqueness Uniqueness.PointRestriction Uniqueness.PointRestriction.PointModel

lemma scalar_permutation : corePermutationAction scalar = 1 := by
  apply MonoidHom.mem_ker.mp
  rw [corePermutationAction_ker_eq_center]
  exact scalar_mem_center

lemma cocycle_scalar (i : Fin 22) : cocycle scalar i = pointScalar := by
  apply Subtype.ext
  simp only [cocycle, scalar_permutation, Equiv.Perm.one_apply, pointScalar]
  rw [mul_assoc, ← Subgroup.mem_center_iff.mp scalar_mem_center (transversal i)]
  simp

lemma natural_scalar (v : Space) :
    fieldRepresentation .natural scalar v =
      (QuadraticAlgebra.omega : Representation.SL3FourNaturalDual.F) • v := by
  funext i
  change representation .natural scalar v i = _
  have e := action_apply .natural scalar v i
  rw [scalar_permutation] at e
  change representation .natural scalar v i = _ at e
  rw [e, cocycle_scalar, pointStabilizerEquiv_pointScalar]
  change (Reference.scalar.val *ᵥ v i) = _
  simp [Reference.scalar, Pi.smul_apply]

end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates

namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates.NaturalFiltration
abbrev CoefficientField := Representation.SL3FourNaturalDual.F

section Transfer
variable {V : Type*} [AddCommGroup V] [Module CoefficientField V]
  {τ : Representation CoefficientField M22TripleCover V}

/-- Restrict an actual invariant subspace to the binary field. -/
def binarySubspace [Module (ZMod 2) V] [IsScalarTower (ZMod 2) CoefficientField V]
    (S : Subrepresentation τ) : Subrepresentation (restrictScalars (k := ZMod 2) τ) where
  toSubmodule := S.toSubmodule.restrictScalars (ZMod 2)
  apply_mem_toSubmodule g _ hv := S.apply_mem_toSubmodule g hv

/-- Scalar restriction commutes with the literal quotient action. -/
def binaryQuotientEquiv [Module (ZMod 2) V] [IsScalarTower (ZMod 2) CoefficientField V]
    (S : Subrepresentation τ) :
    Representation.RepEquiv (binarySubspace S).quotientRepresentation
      (restrictScalars (k := ZMod 2) S.quotientRepresentation) where
  toLinearEquiv := Submodule.Quotient.restrictScalarsEquiv (ZMod 2) S.toSubmodule
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    induction v using Submodule.Quotient.induction_on with
    | H v => rfl

/-- The central scalar acts on every literal invariant quotient. -/
lemma scalar_quotient (S : Subrepresentation τ)
    (hs : ∀ v, τ scalar v = (QuadraticAlgebra.omega : CoefficientField) • v)
    (v : V ⧸ S.toSubmodule) :
    S.quotientRepresentation scalar v = (QuadraticAlgebra.omega : CoefficientField) • v := by
  induction v using Submodule.Quotient.induction_on with
  | H v =>
    change S.toSubmodule.mkQ (τ scalar v) = _ • S.toSubmodule.mkQ v
    rw [hs, map_smul]

lemma binaryQuotient_irreducible [Module (ZMod 2) V] [IsScalarTower (ZMod 2) CoefficientField V]
    (S : Subrepresentation τ) (hs : ∀ v, τ scalar v = (QuadraticAlgebra.omega : CoefficientField) • v)
    (hi : S.quotientRepresentation.IsIrreducible) :
    (binarySubspace S).quotientRepresentation.IsIrreducible := by
  let := hi
  exact (binaryQuotientEquiv S).irreducible_of_euqiv
    (restrictScalars_isIrreducible S.quotientRepresentation (scalar_quotient S hs))

lemma binaryQuotient_finrank [Module (ZMod 2) V] [IsScalarTower (ZMod 2) CoefficientField V]
    (S : Subrepresentation τ) :
    Module.finrank (ZMod 2) (V ⧸ (binarySubspace S).toSubmodule) =
      2 * Module.finrank CoefficientField (V ⧸ S.toSubmodule) := by
  rw [(binaryQuotientEquiv S).toLinearEquiv.finrank_eq,
    ← Module.finrank_mul_finrank (ZMod 2) CoefficientField (V ⧸ S.toSubmodule),
    Representation.SL3FourNaturalDual.finrank_field]

/-- Actual field filtrations restrict to binary filtrations, with every degree doubled. -/
lemma binary_filtration {D : Set ℕ} (h : FactorDegreeFiltration D τ) :
    ∀ [Module (ZMod 2) V] [IsScalarTower (ZMod 2) CoefficientField V],
    (∀ v, τ scalar v = (QuadraticAlgebra.omega : CoefficientField) • v) →
    FactorDegreeFiltration ((fun d => 2*d) '' D) (restrictScalars (k := ZMod 2) τ) := by
  induction h with
  | zero σ =>
    intro _ _ _
    exact .zero _
  | @step X _ _ σ S previous simple degree ih =>
    intro _ _ hs
    refine .step (binarySubspace S) ?_ (binaryQuotient_irreducible S hs simple) ?_
    · exact ih (fun v => Subtype.ext (hs v))
    · rw [binaryQuotient_finrank]
      exact Set.mem_image_of_mem _ degree

end Transfer

lemma natural_filtration_of_field
    (h : FactorDegreeFiltration ({6, 15, 45} : Set ℕ) (fieldRepresentation .natural)) :
    FactorDegreeFiltration ({12, 30, 90} : Set ℕ) (representation .natural) := by
  have hb := binary_filtration h natural_scalar
  rw [fieldRepresentation_restrictScalars] at hb
  convert hb using 1
  ext n
  simp
  omega

end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates.NaturalFiltration
