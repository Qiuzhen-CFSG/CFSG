module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.Inputs
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.Unipotent
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.Algebraic

/-!
# Regular functions on the two finite unipotent cells

Right Borel covariance is stated by the actual torus character and the actual
root-generated subgroup. The finite evaluation sets use the literal elementary
inclusion. No identification with the full fixed-point group is built in.

The maximal restricted weight is `(2^n - 1)ρ`. Injectivity of evaluation at
this one weight implies injectivity at every smaller dominant weight: multiply
by a nonzero complementary covariant function, and use that the coordinate
ring of a connected algebraic group is a domain. The extremal injectivity and
complementary-function existence statements below are proof obligations, not
fields of the geometric input or asserted source theorems.

Sources: GLS3, Definition 2.8.1 and Theorem 2.8.2; Steinberg,
`Chapter2St2.tex`, Sections 13.2(d) and 13.3(a).
-/

@[expose] public noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction

open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight

universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- The opposite unipotent radical also has two-power element orders. -/
theorem negativeRoots_isPGroup (S : Geometry K) :
    IsPGroup 2 (RootSubgroupGenerated S.roots (S.roots.neg ⁻¹' S.roots.positive)) := by
  rw [← S.bigCell.data.opposite_witness.root_generated]
  exact S.bigCell.data.opposite_witness.unipotent.isPGroup_of_unipotent
    S.bigCell.data.opposite_witness.radical.2.1 2

/-- All opposite-unipotent fixed points survive passage to the elementary
group, just as the positive-unipotent points do. -/
theorem negativeFixed_le_elementary (S : Geometry K) (n : ℕ) :
    (RootSubgroupGenerated S.roots (S.roots.neg ⁻¹' S.roots.positive)).comap
      (graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n).subtype ≤
        graphFieldElementarySubgroup S.diagram.toMulEquiv S.frobenius.onPoints n := by
  intro x hx
  have hU := (negativeRoots_isPGroup S).comap_of_injective
    (graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n).subtype
    Subtype.coe_injective
  obtain ⟨m, hm⟩ := hU ⟨x, hx⟩
  apply Subgroup.subset_closure
  exact ⟨m, congrArg Subtype.val hm⟩

/-- A regular function transforming on the right by a torus character and
fixed by the indicated root subgroup. -/
def RootCovariant (S : Geometry K) (P : Set S.roots.Root)
    (chi : TorusWeight S.torus) (f : K.PolynomialFunction) : Prop :=
  ∀ (g : Variety.Point K) (t : Variety.Point S.torus.carrierVariety)
    (u : Variety.Point K), u ∈ RootSubgroupGenerated S.roots P →
      f (g * S.torus.includePoint t * u) = chi.pointCharacter t * f g

/-- Evaluation on the actual elementary points of a root cell separates
regular functions with the specified right covariance. -/
def CellInjective (S : Geometry K) (n : ℕ) (P Q : Set S.roots.Root)
    (chi : TorusWeight S.torus) : Prop :=
  ∀ f : K.PolynomialFunction, RootCovariant S P chi f →
    (∀ g, S.inclusion n g ∈ RootSubgroupGenerated S.roots Q →
      f (S.inclusion n g) = 0) → f = 0

/-- The two evaluation statements needed for the finite highest-line and
orbit-span arguments. The opposite Borel uses the inverse character. -/
def RestrictedCellInjectivity (S : Geometry K) (n : ℕ) : Prop :=
  ∀ a : Weight, InRestrictedRange n a →
    CellInjective S n S.roots.positive (S.roots.neg ⁻¹' S.roots.positive)
      (S.coordinateEmbedding a) ∧
    CellInjective S n (S.roots.neg ⁻¹' S.roots.positive) S.roots.positive
      (S.coordinateEmbedding a)⁻¹

/-- The highest weight of the Steinberg module in simple-coroot coordinates. -/
def maximalRestrictedWeight (n : ℕ) : Weight := fun _ => (2 : ℤ) ^ n - 1

/-- A purely regular-function version of the extremal finite-cell calculation.
This predicate is an unproved obligation, not a representation assumption. -/
def ExtremalCellInjectivity (S : Geometry K) (n : ℕ) : Prop :=
  CellInjective S n S.roots.positive (S.roots.neg ⁻¹' S.roots.positive)
    (S.coordinateEmbedding (maximalRestrictedWeight n)) ∧
  CellInjective S n (S.roots.neg ⁻¹' S.roots.positive) S.roots.positive
    (S.coordinateEmbedding (maximalRestrictedWeight n))⁻¹

/-- Nonzero sections used to raise each restricted weight to the extremal
one. These are existence obligations, with no finite-group conclusion. -/
def ComplementarySections (S : Geometry K) (n : ℕ) : Prop :=
  ∀ a : Weight, InRestrictedRange n a →
    (∃ f : K.PolynomialFunction, f ≠ 0 ∧ RootCovariant S S.roots.positive
      (S.coordinateEmbedding (maximalRestrictedWeight n - a)) f) ∧
    (∃ f : K.PolynomialFunction, f ≠ 0 ∧
      RootCovariant S (S.roots.neg ⁻¹' S.roots.positive)
        (S.coordinateEmbedding (maximalRestrictedWeight n - a))⁻¹ f)

omit [IsAlgClosed k] in
private theorem pointCharacter_mul (S : Geometry K) (chi psi : TorusWeight S.torus)
    (t : Variety.Point S.torus.carrierVariety) :
    (chi * psi).pointCharacter t = chi.pointCharacter t * psi.pointCharacter t := by
  change (dPointEquiv 1 (chi.onPoints t * psi.onPoints t) 0 : k) =
    (dPointEquiv 1 (chi.onPoints t) 0 : k) * (dPointEquiv 1 (psi.onPoints t) 0 : k)
  exact congrArg Units.val (congrFun (dPointEquiv_mul 1 (chi.onPoints t) (psi.onPoints t)) 0)

omit [IsAlgClosed k] in
/-- Multiplication adds the actual Borel characters. -/
theorem RootCovariant.mul (S : Geometry K) {P : Set S.roots.Root}
    {chi psi : TorusWeight S.torus} {f h : K.PolynomialFunction}
    (hf : RootCovariant S P chi f) (hh : RootCovariant S P psi h) :
    RootCovariant S P (chi * psi) (f * h) := by
  intro g t u hu
  change f (g * S.torus.includePoint t * u) * h (g * S.torus.includePoint t * u) =
    (chi * psi).pointCharacter t * (f g * h g)
  rw [hf g t u hu, hh g t u hu, pointCharacter_mul]
  ring

omit [IsAlgClosed k] in
/-- A nonzero complementary section reduces injectivity to a larger weight. -/
theorem cellInjective_of_complementarySection (S : Geometry K) (n : ℕ)
    (P Q : Set S.roots.Root) (chi psi : TorusWeight S.torus)
    (hgrid : CellInjective S n P Q (chi * psi))
    (hsection : ∃ h : K.PolynomialFunction, h ≠ 0 ∧ RootCovariant S P psi h) :
    CellInjective S n P Q chi := by
  obtain ⟨h, hh, hcov⟩ := hsection
  let : IsDomain (coordinateRing K) :=
    isDomain_coordinateRing_of_isIrreducible K (connectedAlgebraicGroup_irreducible K S.simple.1)
  let : IsDomain K.PolynomialFunction :=
    (coordinateRingAlgEquivPolynomialFunction K).toRingEquiv.isDomain_iff.mp inferInstance
  intro f hf hz
  have hzero : f * h = 0 := hgrid (f * h) (hf.mul S hcov) (by
    intro g hg
    change f (S.inclusion n g) * h (S.inclusion n g) = 0
    rw [hz g hg, zero_mul])
  exact (mul_eq_zero.mp hzero).resolve_right hh

/-- Matrix coefficients of an actual highest vector have right Borel
covariance. This applies equally to the positive and opposite Borels. -/
theorem exists_rootCovariant_matrixCoefficient (S : Geometry K)
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : RationalRepresentation K V) (hrho : IsRationalRepresentation rho)
    {P : Set S.roots.Root} {B : ClosedSubgroup K}
    (hB : IsBorelOfPositiveSystem S.roots P B)
    (v : V) (chi : TorusWeight S.torus) (hv : HasHighWeight rho B S.torus v chi)
    (l : Module.Dual k V) :
    ∃ f : K.PolynomialFunction, RootCovariant S P chi f ∧
      ∀ g, f g = l ((rho.action g).1 v) := by
  obtain ⟨e, r, hr⟩ := hrho
  let f := rationalRepresentationLinearMatrixCoefficient rho e r l v
  have hf (g) : f g = l ((rho.action g).1 v) :=
    rationalRepresentationLinearMatrixCoefficient_apply rho e r hr l v g
  refine ⟨f, ?_, hf⟩
  intro g t u hu
  have hfix : (rho.action u).1 v = v := by
    apply invariantLine_fixed_of_unipotent_subgroup rho ⟨e, r, hr⟩ B hB.unipotent
      v hv.1 hB.radical.1 hB.radical.2.1 u
    rwa [← hB.root_generated] at hu
  rw [hf, hf, map_mul, map_mul]
  change l ((rho.action g).1 ((rho.action (S.torus.includePoint t)).1
    ((rho.action u).1 v))) = _
  rw [hfix, hv.2.2 t, map_smul, map_smul, smul_eq_mul]

/-- Rational highest-weight existence supplies both complementary sections.
The opposite section comes from the dual, with its character verified by the
nonzero opposite-highest pairing. -/
theorem complementarySections_of_highestWeightExistence (S : Geometry K) (n : ℕ)
    (hex : ∀ b : Weight, (∀ i, 0 ≤ b i) →
      ∃ A : RationalFactor K, HasHighestWeight S A b) :
    ComplementarySections S n := by
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
    A.action A.irreducible v (S.coordinateEmbedding b) hv tau htau htaur
  obtain ⟨f, hf, hfval⟩ := exists_rootCovariant_matrixCoefficient S A.action A.irreducible.1
    S.bigCell.data.positive_witness v (S.coordinateEmbedding b) hv l
  obtain ⟨h, hh, hhval⟩ := exists_rootCovariant_matrixCoefficient S tau htaur
    S.bigCell.data.opposite_witness l (S.coordinateEmbedding b)⁻¹ hl (Module.Dual.eval k A.Space v)
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
theorem restrictedCellInjectivity_of_extremal_of_sections (S : Geometry K) (n : ℕ)
    (hext : ExtremalCellInjectivity S n) (hsections : ComplementarySections S n) :
    RestrictedCellInjectivity S n := by
  intro a ha
  have hchar : S.coordinateEmbedding a *
      S.coordinateEmbedding (maximalRestrictedWeight n - a) =
      S.coordinateEmbedding (maximalRestrictedWeight n) := by
    change S.weight (Multiplicative.ofAdd a) *
      S.weight (Multiplicative.ofAdd (maximalRestrictedWeight n - a)) = _
    rw [← map_mul]
    change S.weight (Multiplicative.ofAdd (a + (maximalRestrictedWeight n - a))) = _
    rw [show a + (maximalRestrictedWeight n - a) = maximalRestrictedWeight n by abel]
    rfl
  have hinv : (S.coordinateEmbedding a)⁻¹ *
      (S.coordinateEmbedding (maximalRestrictedWeight n - a))⁻¹ =
      (S.coordinateEmbedding (maximalRestrictedWeight n))⁻¹ := by
    rw [← mul_inv, hchar]
  constructor
  · apply cellInjective_of_complementarySection S n _ _ _ _ _ (hsections a ha).1
    rw [hchar]
    exact hext.1
  · apply cellInjective_of_complementarySection S n _ _ _ _ _ (hsections a ha).2
    rw [hinv]
    exact hext.2

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
