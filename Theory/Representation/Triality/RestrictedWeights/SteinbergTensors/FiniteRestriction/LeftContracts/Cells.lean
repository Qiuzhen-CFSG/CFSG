module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftContracts
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.RegularFunctions

/-!
# Left covariant finite-cell contracts

On the negative cell use the positive-root covariance E_left(delta); on the
positive cell use its inverse. Complementary sections have weight delta-a.
The existing character-parametrized product and domain arguments apply verbatim.
Source: Steinberg §13.2(d), §13.3, and GLS3 2.8.2.
-/

@[expose] public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]
/-- The two evaluation statements needed for the finite highest-line and
orbit-span arguments. The opposite Borel uses the inverse character. -/
def LeftRestrictedCellInjectivity (S : Geometry K) (n : ℕ) : Prop :=
  ∀ a : Weight, InRestrictedRange n a →
    CellInjective S n S.roots.positive (S.roots.neg ⁻¹' S.roots.positive)
      (S.leftWeightEmbedding a) ∧
    CellInjective S n (S.roots.neg ⁻¹' S.roots.positive) S.roots.positive
      (S.leftWeightEmbedding a)⁻¹

/-- A purely regular-function version of the extremal finite-cell calculation.
This predicate is an unproved obligation, not a representation assumption. -/
def LeftExtremalCellInjectivity (S : Geometry K) (n : ℕ) : Prop :=
  CellInjective S n S.roots.positive (S.roots.neg ⁻¹' S.roots.positive)
    (S.leftWeightEmbedding (maximalRestrictedWeight n)) ∧
  CellInjective S n (S.roots.neg ⁻¹' S.roots.positive) S.roots.positive
    (S.leftWeightEmbedding (maximalRestrictedWeight n))⁻¹

/-- Nonzero sections used to raise each restricted weight to the extremal
one. These are existence obligations, with no finite-group conclusion. -/
def LeftComplementarySections (S : Geometry K) (n : ℕ) : Prop :=
  ∀ a : Weight, InRestrictedRange n a →
    (∃ f : K.PolynomialFunction, f ≠ 0 ∧ RootCovariant S S.roots.positive
      (S.leftWeightEmbedding (maximalRestrictedWeight n - a)) f) ∧
    (∃ f : K.PolynomialFunction, f ≠ 0 ∧
      RootCovariant S (S.roots.neg ⁻¹' S.roots.positive)
        (S.leftWeightEmbedding (maximalRestrictedWeight n - a))⁻¹ f)

/-- Rational highest-weight existence supplies both complementary sections.
The opposite section comes from the dual, with its character verified by the
nonzero opposite-highest pairing. -/
theorem leftComplementarySections_of_highestWeightExistence (S : Geometry K) (n : ℕ)
    (hex : ∀ b : Weight, (∀ i, 0 ≤ b i) →
      ∃ A : RationalFactor K, HasLeftHighestWeight S A b) :
    LeftComplementarySections S n := by
  intro a ha
  let b := maximalRestrictedWeight n - a
  have hb : ∀ i, 0 ≤ b i := by
    intro i
    have hi := (ha i).2
    change 0 ≤ (2 : ℤ) ^ n - 1 - a i
    omega
  obtain ⟨A, v, hv⟩ := hex b hb
  obtain ⟨tau, htau, htaur⟩ := rationalRepresentation_dual_exists A.action A.irreducible.1
  obtain ⟨l, hl, hlv⟩ := exists_opposite_dual_highestWeight S.bigCell S.maximalTorus
    A.action A.irreducible v (S.leftWeightEmbedding b) hv tau htau htaur
  obtain ⟨f, hf, hfval⟩ := exists_rootCovariant_matrixCoefficient S A.action A.irreducible.1
    S.bigCell.data.positive_witness v (S.leftWeightEmbedding b) hv l
  obtain ⟨h, hh, hhval⟩ := exists_rootCovariant_matrixCoefficient S tau htaur
    S.bigCell.data.opposite_witness l (S.leftWeightEmbedding b)⁻¹ hl (Module.Dual.eval k A.Space v)
  refine ⟨⟨f, ?_, hf⟩, ⟨h, ?_, hh⟩⟩
  · intro hz
    have hval := hfval 1
    rw [hz] at hval
    exact hlv (by simpa using hval.symm)
  · intro hz
    have hval := hhval 1
    rw [hz] at hval
    exact hlv (by simpa using hval.symm)

omit [IsAlgClosed k] in
/-- Extremal finite-cell injectivity and complementary section existence
supply both cell calculations for every restricted weight. -/
theorem leftRestrictedCellInjectivity_of_extremal_of_sections (S : Geometry K) (n : ℕ)
    (hext : LeftExtremalCellInjectivity S n) (hsections : LeftComplementarySections S n) :
    LeftRestrictedCellInjectivity S n := by
  intro a ha
  have hchar : S.leftWeightEmbedding a *
      S.leftWeightEmbedding (maximalRestrictedWeight n - a) =
      S.leftWeightEmbedding (maximalRestrictedWeight n) := by
    rw [← S.leftWeightEmbedding_add]
    congr 1
    abel
  have hinv : (S.leftWeightEmbedding a)⁻¹ *
      (S.leftWeightEmbedding (maximalRestrictedWeight n - a))⁻¹ =
      (S.leftWeightEmbedding (maximalRestrictedWeight n))⁻¹ := by
    rw [← mul_inv, hchar]
  constructor
  · apply cellInjective_of_complementarySection S n _ _ _ _ _ (hsections a ha).1
    rw [hchar]
    exact hext.1
  · apply cellInjective_of_complementarySection S n _ _ _ _ _ (hsections a ha).2
    rw [hinv]
    exact hext.2

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
