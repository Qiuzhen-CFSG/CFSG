module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.KernelCentrality.Transport
public import Theory.AlgebraicGroup.RootSystems.IntegralChevalleyOperatorOrientation
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.CoverCenter.Equivariance.Integration

/-!
# The signed integral E7 adjoint operator family

On E7's Cartan-plus-root lattice, the simple positive, negative and Cartan
coordinates map to εᵢEᵢ, -εᵢFᵢ and -εᵢ[Eᵢ,Fᵢ]. Canonical Tits routes carry
these signs to all root coordinates. Restricting this family along the literal
E6 basis inclusion will give the required 78-coordinate tensor.

The definitions and opposition transfer adapt the checked F4 construction in
`CoverCenter.Operators` and `CoverCenter.Equivariance.IntegralModel`.
Source: the integral Geck construction and GLS3 §§1.10–1.12 and 2.6.2.
The commutator identities are proved in the sibling modules.
-/

@[expose] public section
open scoped Matrix Classical
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open Theory.AlgebraicGroup
open ReeF4.WordRelations.Faithfulness
noncomputable section
namespace TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality.E7AdjointTensor
attribute [local instance] Classical.decEq
local instance rootsInModel : Fintype typeE7Roots := Fintype.ofFinite _

/-- The actual 133-coordinate integral E7 Geck carrier. -/
abbrev Coordinate := typeE7RootPairing_base.support ⊕ typeE7Roots

def rootOperatorOrientation (r : typeE7Roots) : ℤ :=
  let := typeE7RootPairing.indexNeg
  if typeE7RootPairing_base.IsPos r then
    simpleRouteOperatorOrientation true
      (rootRoute (P := typeE7RootPairing) (b := typeE7RootPairing_base) r).word
      (rootRoute (P := typeE7RootPairing) (b := typeE7RootPairing_base) r).simple
  else simpleRouteOperatorOrientation false
      (rootRoute (P := typeE7RootPairing) (b := typeE7RootPairing_base) (-r)).word
      (rootRoute (P := typeE7RootPairing) (b := typeE7RootPairing_base) (-r)).simple


theorem rootOperatorOrientation_sq (r : typeE7Roots) :
    rootOperatorOrientation r * rootOperatorOrientation r = 1 := by
  unfold rootOperatorOrientation
  split <;> exact simpleRouteOperatorOrientation_sq _ _ _

theorem rootOperatorOrientation_simple (i : typeE7RootPairing_base.support) :
    rootOperatorOrientation i = simpleOperatorOrientation (b := typeE7RootPairing_base) i := by
  simp [rootOperatorOrientation, typeE7RootPairing_base.isPos_of_mem_support i.property,
    simpleRouteOperatorOrientation, titsWordSign]

theorem rootOperatorOrientation_neg_simple (i : typeE7RootPairing_base.support) :
    let := typeE7RootPairing.indexNeg
    rootOperatorOrientation (-i : typeE7Roots) =
      -simpleOperatorOrientation (b := typeE7RootPairing_base) i := by
  let := typeE7RootPairing.indexNeg
  dsimp only
  have hi := typeE7RootPairing_base.isPos_of_mem_support i.property
  have hn : ¬typeE7RootPairing_base.IsPos (-i : typeE7Roots) := by
    rw [RootPairing.Base.IsPos.neg_iff_not]
    exact not_not_intro hi
  rw [rootOperatorOrientation]
  rw [if_neg hn, neg_neg, rootRoute_word_simple, rootRoute_simple]
  simp only [simpleRouteOperatorOrientation, titsWordSign, one_mul,
    signedSimpleOperatorOrientation_false]


def integralCoordinateOperator : Coordinate → Matrix Coordinate Coordinate ℤ
  | Sum.inr r => rootOperatorOrientation r •
      rootOperator (P := typeE7RootPairing) (b := typeE7RootPairing_base) r
  | Sum.inl i => -simpleOperatorOrientation (b := typeE7RootPairing_base) i •
      (eMatrix (P := typeE7RootPairing) i * fMatrix i - fMatrix i * eMatrix i)

/-- The integral form of the fixed signed adjoint map. -/
def integralAdjointMap : (Coordinate → ℤ) →ₗ[ℤ] Matrix Coordinate Coordinate ℤ :=
  Adjoint.linearExtension integralCoordinateOperator

lemma integralAdjointMap_single (j : Coordinate) :
    integralAdjointMap (Pi.single j 1) = integralCoordinateOperator j :=
  Adjoint.linearExtension_single _ _


/-- The infinitesimal positive-simple intertwining contract. -/
def PositiveIntegralCommutators : Prop :=
  ∀ (i : typeE7RootPairing_base.support) (v : Coordinate → ℤ),
    integralAdjointMap (eMatrix (P := typeE7RootPairing) i *ᵥ v) =
      eMatrix i * integralAdjointMap v - integralAdjointMap v * eMatrix i

/-- The infinitesimal negative-simple intertwining contract. -/
def NegativeIntegralCommutators : Prop :=
  ∀ (i : typeE7RootPairing_base.support) (v : Coordinate → ℤ),
    integralAdjointMap (fMatrix (P := typeE7RootPairing) i *ᵥ v) =
      fMatrix i * integralAdjointMap v - integralAdjointMap v * fMatrix i

/-- Opposition acts on adjoint operators with the sign forced by
`D(vᵢ) = εᵢEᵢ` and `D(v₋ᵢ) = -εᵢFᵢ`. -/
def IntegralOppositionCovariance : Prop :=
  ∀ v : Coordinate → ℤ,
    integralAdjointMap
      (omegaMatrix (P := typeE7RootPairing) (b := typeE7RootPairing_base) *ᵥ v) =
    -(omegaMatrix (P := typeE7RootPairing) (b := typeE7RootPairing_base) *
      integralAdjointMap v * omegaMatrix (P := typeE7RootPairing) (b := typeE7RootPairing_base))

/-- Signed opposition and positive infinitesimal intertwining give the
negative infinitesimal identity for the same fixed map. -/
theorem negative_integral_commutators_of_positive_and_opposition
    (hE : PositiveIntegralCommutators) (hO : IntegralOppositionCovariance) :
    NegativeIntegralCommutators := by
  intro i v
  let O := omegaMatrix (P := typeE7RootPairing) (b := typeE7RootPairing_base)
  let E := eMatrix (P := typeE7RootPairing) i
  let N := fMatrix (P := typeE7RootPairing) i
  have hOO : O * O = 1 := omegaMatrix_sq
  have hOE : O * E = N * O := omegaMatrix_mul_eMatrix i
  have hvec : O *ᵥ (E *ᵥ (O *ᵥ v)) = N *ᵥ v := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hOE, mul_assoc, hOO, mul_one]
  change integralAdjointMap (N *ᵥ v) = N * integralAdjointMap v - integralAdjointMap v * N
  calc
    _ = -(O * integralAdjointMap (E *ᵥ (O *ᵥ v)) * O) := by
      have h := hO (E *ᵥ (O *ᵥ v))
      change integralAdjointMap (O *ᵥ (E *ᵥ (O *ᵥ v))) = _ at h
      rw [hvec] at h
      exact h
    _ = (O * E) * O * integralAdjointMap v * (O * O) -
        (O * O) * integralAdjointMap v * (O * E) * O := by
      rw [hE i, hO v]
      change -(O * (E * -(O * integralAdjointMap v * O) -
        -(O * integralAdjointMap v * O) * E) * O) = _
      noncomm_ring
    _ = _ := by
      rw [hOE, hOO]
      simp only [one_mul, mul_one, mul_assoc, hOO]


end TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality.E7AdjointTensor
