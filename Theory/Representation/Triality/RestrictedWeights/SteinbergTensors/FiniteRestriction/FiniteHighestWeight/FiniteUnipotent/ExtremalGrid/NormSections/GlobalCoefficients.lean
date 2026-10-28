module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.Realization
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.RootCoordinates
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.FundamentalModules.OuterFunctions.NaturalInput
public import Theory.AlgebraicGroup.Variety.AffineSpace

/-!
# Normalized global extremal coefficients and their root-chart polynomials

An actual rational highest vector is fixed by the root-generated unipotent
radical of its Borel. A linear functional taking value one on that vector
therefore gives a globally regular, normalized covariant matrix coefficient.
The positive construction reuses `OuterFunctions.regularFunction_exists_of_vector`;
the arbitrary-Borel construction reuses `exists_rootCovariant_matrixCoefficient`.
Both use the actual algebraic representation map and
`rationalRepresentationLinearMatrixCoefficient`.

Applied to the two explicit `HighestWeightCover`s, this gives sections of the
left extremal character and its inverse, for every `n`, including `n = 1`.
Existence of the covers is a separate obligation. Their universal mapping
property is unnecessary for this coefficient construction.

The ordered root-product chart is a polynomial morphism: each factor is an
actual `Geometry.rootParameter` composed with a coordinate projection, and
the factors are combined using regular multiplication. Pullback consequently
gives an `MvPolynomial (Fin 12) k` with its evaluation identity on every field
tuple. The same statement holds after any actual left translation. The
universe lift in the morphism's domain only matches the variety's coordinate
universe; polynomial renaming returns the original twelve coordinate indices.

These are global regularity and chart realization results. They assert no
support bound, nonzero top coefficient, finite-cell sum, or interpolation.

Sources: GLS3, Definitions 1.14.3 and 1.14.5, and the setup of 2.8.1--2.8.2;
Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, Sections 12--13, particularly
13.2(d) and 13.3(a), and its reference [26]. Left characters follow (6.1).
-/

public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid
open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
universe u
variable {k : Type u} [Field k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

section Coefficients
variable [IsAlgClosed k]

/-- Borel line invariance in a rational representation implies fixation by
the actual root-generated unipotent radical, for either Borel. -/
theorem highestVector_fixed_by_rootGenerated (S : Geometry K)
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : RationalRepresentation K V) (hrho : IsRationalRepresentation rho)
    {P : Set S.roots.Root} {B : ClosedSubgroup K}
    (hB : IsBorelOfPositiveSystem S.roots P B)
    {v : V} {chi : TorusWeight S.torus} (hv : HasHighWeight rho B S.torus v chi)
    (g : Variety.Point K) (hg : g ∈ RootSubgroupGenerated S.roots P) :
    (rho.action g).1 v = v := by
  apply invariantLine_fixed_of_unipotent_subgroup rho hrho B hB.unipotent
    v hv.1 hB.radical.1 hB.radical.2.1 g
  rwa [← hB.root_generated] at hg

/-- A genuine dual functional normalized at a nonzero highest vector gives
a globally regular normalized coefficient for any supplied Borel. -/
theorem exists_normalizedRootCovariant_of_highest (S : Geometry K)
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : RationalRepresentation K V) (hrho : IsRationalRepresentation rho)
    {P : Set S.roots.Root} {B : ClosedSubgroup K}
    (hB : IsBorelOfPositiveSystem S.roots P B)
    (v : V) (chi : TorusWeight S.torus) (hv : HasHighWeight rho B S.torus v chi) :
    ∃ f : K.PolynomialFunction, f 1 = 1 ∧ RootCovariant S P chi f := by
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one k hv.1.1
  obtain ⟨f, hf, heval⟩ :=
    exists_rootCovariant_matrixCoefficient S rho hrho hB v chi hv l
  refine ⟨f, ?_, hf⟩
  rw [heval, map_one]
  exact hl

/-- The positive left-weight section, using the existing vector-to-function
construction and deriving every root fixation equation from the Borel law. -/
theorem exists_leftNormalizedSection_of_highest (S : Geometry K)
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : RationalRepresentation K V) (hrho : IsRationalRepresentation rho)
    (v : V) (a : Weight)
    (hv : HasHighWeight rho S.bigCell.data.B S.torus v (S.leftWeightEmbedding a)) :
    ∃ f : K.PolynomialFunction, f 1 = 1 ∧
      RootCovariant S S.roots.positive (S.leftWeightEmbedding a) f := by
  have hu : ∀ r ∈ S.roots.positive,
      ∀ z : (S.roots.rootSubgroup r).carrierVariety.Point,
        (rho.action ((S.roots.rootSubgroup r).includePoint z)).1 v = v := by
    intro r hr z
    apply highestVector_fixed_by_rootGenerated S rho hrho
      S.bigCell.data.positive_witness hv
    exact Subgroup.subset_closure (Set.mem_iUnion₂.mpr
      ⟨r, hr, ((S.roots.rootSubgroup r).pointEquiv z).property⟩)
  obtain ⟨f, hf⟩ := OuterFunctions.regularFunction_exists_of_vector S rho hrho
    v hv.1.1 hv.2.2 hu
  refine ⟨f, hf.at_one, ?_⟩
  intro g t w hw
  rw [((isLeftHighestWeightRegularFunction_iff S a f).mp hf).positive_generated w hw]
  exact hf.torus t g

/-- The two explicit covers supply actual normalized global sections at the
left extremal character and its inverse. This includes every positive `n`.
No further representation-existence premise is required. -/
theorem exists_leftNormalizedExtremalSections_of_covers (S : Geometry K) (n : ℕ)
    (Cpos : HighestWeightCover S S.bigCell.data.B
      (S.leftWeightEmbedding (maximalRestrictedWeight n)))
    (Cneg : HighestWeightCover S S.bigCell.data.Bopp
      (S.leftWeightEmbedding (maximalRestrictedWeight n))⁻¹) :
    ∃ fpos fneg : K.PolynomialFunction,
      fpos 1 = 1 ∧ fneg 1 = 1 ∧
      RootCovariant S S.roots.positive
        (S.leftWeightEmbedding (maximalRestrictedWeight n)) fpos ∧
      RootCovariant S (S.roots.neg ⁻¹' S.roots.positive)
        (S.leftWeightEmbedding (maximalRestrictedWeight n))⁻¹ fneg := by
  obtain ⟨fpos, hpos1, hpos⟩ := exists_leftNormalizedSection_of_highest S
    Cpos.action Cpos.rational Cpos.vector (maximalRestrictedWeight n) Cpos.highest
  obtain ⟨fneg, hneg1, hneg⟩ := exists_normalizedRootCovariant_of_highest S
    Cneg.action Cneg.rational S.bigCell.data.opposite_witness
    Cneg.vector _ Cneg.highest
  exact ⟨fpos, fneg, hpos1, hneg1, hpos, hneg⟩

end Coefficients

private def coordinateMorphism (i : Fin 12) :
    Variety.Morphism (affineSpaceVariety k (ULift.{u} (Fin 12))) (KPlus k) where
  toFun z := kPlusPoint (z.val (ULift.up i))
  regular := by
    intro j
    refine ⟨MvPolynomial.X (ULift.up i), ?_⟩
    intro z
    rw [show j = PUnit.unit by rfl]
    exact (evalPolynomial_X z.val (ULift.up i)).symm

private def morphismListProduct {X : Variety k} :
    List (Variety.Morphism X K) → Variety.Morphism X K
  | [] => Variety.Morphism.const X K 1
  | f :: fs => (Theory.AlgebraicGroup.mulMorphism K).comp
      (f.pair (morphismListProduct fs))

omit [CharP k 2] in
private theorem morphismListProduct_apply {X : Variety k}
    (fs : List (Variety.Morphism X K)) (z : X.Point) :
    (morphismListProduct fs).toFun z = (fs.map fun f => f.toFun z).prod := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    change f.toFun z * (morphismListProduct fs).toFun z = _
    rw [ih]
    rfl

/-- The regular ordered product of the supplied one-parameter root maps.
The `ULift` only aligns the affine coordinate universe with that of `k`. -/
def orderedRootMorphism (S : Geometry K) (r : Fin 12 → S.roots.Root) :
    Variety.Morphism (affineSpaceVariety k (ULift.{u} (Fin 12))) K :=
  morphismListProduct (List.ofFn fun i =>
    ((S.roots.rootSubgroup (r i)).inclusion.toVariety.comp
      (S.rootParameter (r i)).hom.toVariety).comp (coordinateMorphism i))

/-- The root-chart morphism has exactly the published ordered-product point map. -/
theorem orderedRootMorphism_apply (S : Geometry K) (r : Fin 12 → S.roots.Root)
    (x : Fin 12 → k) :
    (orderedRootMorphism S r).toFun (affineSpacePoint fun i => x i.down) =
      orderedRootPoint S r x := by
  rw [orderedRootMorphism, morphismListProduct_apply, List.map_ofFn]
  rfl

/-- Every global polynomial function restricts to an actual polynomial on
any ordered twelve-root chart, with equality at every field tuple. -/
theorem exists_polynomial_on_orderedRootPoint (S : Geometry K)
    (r : Fin 12 → S.roots.Root) (f : K.PolynomialFunction) :
    ∃ p : MvPolynomial (Fin 12) k,
      ∀ x : Fin 12 → k, f (orderedRootPoint S r x) = MvPolynomial.eval x p := by
  obtain ⟨p, hp⟩ :=
    (Variety.PolynomialFunction.pullback (orderedRootMorphism S r) f).representedBy
  refine ⟨MvPolynomial.rename ULift.down p, ?_⟩
  intro x
  have h := hp (affineSpacePoint fun i => x i.down)
  change f ((orderedRootMorphism S r).toFun _) = evalPolynomial _ p at h
  rw [orderedRootMorphism_apply] at h
  change f (orderedRootPoint S r x) = evalPolynomial x (MvPolynomial.rename ULift.down p)
  rw [evalPolynomial_rename]
  exact h

/-- The polynomial realization also applies after an arbitrary actual left
translation of the root chart. -/
theorem exists_polynomial_on_leftTranslatedOrderedRootPoint (S : Geometry K)
    (r : Fin 12 → S.roots.Root) (f : K.PolynomialFunction) (g : K.Point) :
    ∃ p : MvPolynomial (Fin 12) k,
      ∀ x : Fin 12 → k, f (g * orderedRootPoint S r x) = MvPolynomial.eval x p := by
  exact exists_polynomial_on_orderedRootPoint S r
    (Variety.PolynomialFunction.pullback (Theory.AlgebraicGroup.leftMulMorphism K g) f)

/-- Both normalized global sections together with their polynomial
restrictions to the opposite root charts, valid on all field tuples. -/
theorem exists_leftNormalizedExtremalSections_with_chartPolynomials_of_covers
    [IsAlgClosed k] (S : Geometry K) (n : ℕ)
    (Cpos : HighestWeightCover S S.bigCell.data.B
      (S.leftWeightEmbedding (maximalRestrictedWeight n)))
    (Cneg : HighestWeightCover S S.bigCell.data.Bopp
      (S.leftWeightEmbedding (maximalRestrictedWeight n))⁻¹) :
    ∃ (fpos fneg : K.PolynomialFunction) (ppos pneg : MvPolynomial (Fin 12) k),
      fpos 1 = 1 ∧ fneg 1 = 1 ∧
      RootCovariant S S.roots.positive
        (S.leftWeightEmbedding (maximalRestrictedWeight n)) fpos ∧
      RootCovariant S (S.roots.neg ⁻¹' S.roots.positive)
        (S.leftWeightEmbedding (maximalRestrictedWeight n))⁻¹ fneg ∧
      (∀ x : Fin 12 → k, fpos (orderedRootPoint S (negativeCoordinateRoot S) x) =
        MvPolynomial.eval x ppos) ∧
      (∀ x : Fin 12 → k, fneg (orderedRootPoint S (positiveCoordinateRoot S) x) =
        MvPolynomial.eval x pneg) := by
  obtain ⟨fpos, fneg, hpos1, hneg1, hpos, hneg⟩ :=
    exists_leftNormalizedExtremalSections_of_covers S n Cpos Cneg
  obtain ⟨ppos, hppos⟩ := exists_polynomial_on_orderedRootPoint S
    (negativeCoordinateRoot S) fpos
  obtain ⟨pneg, hpneg⟩ := exists_polynomial_on_orderedRootPoint S
    (positiveCoordinateRoot S) fneg
  exact ⟨fpos, fneg, ppos, pneg, hpos1, hneg1, hpos, hneg, hppos, hpneg⟩

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid
