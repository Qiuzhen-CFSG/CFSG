module
public import Theory.SpecificGroups.Monster.Construction.LocalC.LatticeComparison.Additivity
public import Theory.SpecificGroups.Monster.Construction.LocalC.LatticeComparison.Forms
public import Theory.SpecificGroups.Monster.Construction.LocalC.ShortLifts

/-!
# The fixed Golay–Leech isometry and the actual quadratic quotient

The explicit representative map is additive for the twisted coordinate sum
and preserves its square form. Polarization and nonsingularity give
injectivity; equal dimensions then give surjectivity. This constructs the
fixed source isometry, rather than choosing an abstract plus-type isometry.
Its composite with the actual triality coordinate homomorphism has kernel
`⟨z1,k1⟩`. The final equations identify its factorization through `Q1/⟨k1⟩`
and then through the center with the same explicit map.

The cocode image is twelve-dimensional; equivariance on that image alone
does not establish equivariance on the full coordinate space. Generator
equivariance remains a separate calculation.

Source: Aschbacher, *Sporadic Groups*, Lemmas 23.9–23.10 and Exercise 8.10,
printed pp. 119–122, and Lemma 27.2, pp. 144–145.
-/

@[expose] public section
noncomputable section
open Atlas.Codes Atlas.Fischer Atlas.Lattices
namespace Sporadic.Monster.Construction.LocalC
open TrialitySpin

/-- Polarization of the explicitly computed quadratic identity. -/
theorem sourceCoordinateMap_polar (x y : QuadraticCoordinates) :
    leechPolar (sourceCoordinateMap x) (sourceCoordinateMap y) = coordinatePolar x y := by
  have h := sourceCoordinateMap_quadratic (x + y)
  rw [sourceCoordinateMap_add, leechQuadratic_add, sourceCoordinateMap_quadratic,
    sourceCoordinateMap_quadratic, coordinateQuadratic_add] at h
  exact add_left_cancel h

/-- Nonsingularity of the source form forces this particular map to be injective. -/
theorem sourceCoordinateMap_injective : Function.Injective sourceCoordinateMap := by
  change Function.Injective sourceCoordinateLinearMap
  apply (injective_iff_map_eq_zero sourceCoordinateLinearMap).mpr
  intro x hx
  apply coordinatePolar_separates x
  intro y
  rw [← sourceCoordinateMap_polar]
  change sourceCoordinateMap x = 0 at hx
  rw [hx]
  change leechPolarBilin 0 (sourceCoordinateMap y) = 0
  rw [map_zero]
  rfl

/-- The source and target both have dimension twenty-four. -/
theorem sourceCoordinateMap_surjective : Function.Surjective sourceCoordinateMap :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (quadraticCoordinates_finrank.trans leechModTwo_finrank.symm)
    (f := sourceCoordinateLinearMap)).mp sourceCoordinateMap_injective

/-- The fixed source map `(v,J+Golay) ↦ f_v+f(J)+2Λ`, with the twisted sum. -/
def sourceLatticeComparison : LatticeComparison :=
  { LinearEquiv.ofBijective sourceCoordinateLinearMap
      ⟨sourceCoordinateMap_injective, sourceCoordinateMap_surjective⟩ with
    map_app' := sourceCoordinateMap_quadratic }

@[simp] theorem sourceLatticeComparison_apply (x : QuadraticCoordinates) :
    sourceLatticeComparison x = sourceCoordinateMap x := rfl

/-- The actual source formula certifies the chosen isometry, including its normalization. -/
theorem sourceLatticeComparison_mk (v : golay) (J : BinaryWord) :
    sourceLatticeComparison ⟨v, Submodule.Quotient.mk J⟩ =
      leechReduction (sourceCodeVector v + sourceCocodeVector J) :=
  sourceCoordinateMap_mk v J

/-- Lemma 23.9: no further binary words are killed beyond the Golay code. -/
theorem sourceWordClass_eq_zero_iff (J : BinaryWord) : sourceWordClass J = 0 ↔ J ∈ golay := by
  constructor
  · intro h
    have he : sourceCoordinateMap ⟨0, Submodule.Quotient.mk J⟩ =
        sourceCoordinateMap coordinateZero := by
      rw [sourceCoordinateMap_zero, sourceCoordinateMap, sourceCodeVector_zero,
        map_zero, zero_add, sourceCocodeClass_mk, ← sourceWordClass_eq_reduction]
      exact h
    have hc := congrArg QuadraticCoordinates.cocode (sourceCoordinateMap_injective he)
    exact (Submodule.Quotient.mk_eq_zero golay).mp hc
  · intro h
    exact sourceWordClass_code ⟨J,h⟩

theorem sourceCocodeClass_injective : Function.Injective sourceCocodeClass := by
  intro c d h
  have he : sourceCoordinateMap ⟨0,c⟩ = sourceCoordinateMap ⟨0,d⟩ := by
    simpa [sourceCoordinateMap] using h
  exact congrArg QuadraticCoordinates.cocode (sourceCoordinateMap_injective he)

/-- The cocode image has dimension twelve; it is only half of the full coordinate space. -/
theorem sourceCocodeClass_range_finrank : Module.finrank Bit sourceCocodeClass.range = 12 :=
  (LinearEquiv.ofInjective sourceCocodeClass sourceCocodeClass_injective).finrank_eq.symm.trans
    cocode_finrank

/-- The central quotient of the actual `Q1/⟨k1⟩` is the actual Leech quotient. -/
def sourceQ1QuotientLatticeIsometry :
    q1QuotientQuadraticForm.IsometryEquiv leechQuadraticForm :=
  q1QuotientCoordinatesIsometry.trans sourceLatticeComparison

@[simp] theorem sourceQ1QuotientLatticeIsometry_apply
    (x : Additive Q1QuotientCentralQuotient) :
    sourceQ1QuotientLatticeIsometry x =
      sourceCoordinateMap (q1QuotientCoordinatesIsometry x) := rfl

/-- The source surjection, on the actual triality subgroup rather than formal words. -/
def sourceQ1LatticeHom : Q1 →* Multiplicative LeechModTwo :=
  sourceLatticeComparison.toLinearEquiv.toAddEquiv.toMultiplicative.toMonoidHom.comp
    q1Coordinates

@[simp] theorem sourceQ1LatticeHom_apply (q : Q1) :
    (sourceQ1LatticeHom q).toAdd = sourceCoordinateMap (q1Coordinates q).toAdd := rfl

/-- Lemma 27.2 on each source normal-form word, in Lean's reversed product convention. -/
theorem sourceQ1LatticeHom_param (d : ParkerLoop) (t : ParkerBit) (J : BinaryWord) :
    (sourceQ1LatticeHom (q1Param (d,t,Submodule.Quotient.mk J))).toAdd =
      leechReduction (sourceCodeVector (d.1 + t • golayOne) + sourceCocodeVector J) := by
  rw [sourceQ1LatticeHom_apply, q1Coordinates_param]
  exact sourceCoordinateMap_mk _ _

theorem sourceQ1LatticeHom_surjective : Function.Surjective sourceQ1LatticeHom :=
  sourceLatticeComparison.toLinearEquiv.toAddEquiv.toMultiplicative.surjective.comp
    q1Coordinates_surjective

/-- The kernel is exactly the source `⟨z1,k1⟩` inside `Q1`. -/
theorem sourceQ1LatticeHom_kernel :
    sourceQ1LatticeHom.ker = Q1CentralKernel.subgroupOf Q1 := by
  rw [← q1Coordinates_kernel]
  ext q
  change sourceLatticeComparison.toLinearEquiv.toAddEquiv.toMultiplicative
    (q1Coordinates q) = 1 ↔ q1Coordinates q = 1
  exact sourceLatticeComparison.toLinearEquiv.toAddEquiv.toMultiplicative.map_eq_one_iff

/-- Compatibility with both actual quotient maps, first by `⟨k1⟩` and then by the center. -/
theorem sourceQ1QuotientLatticeIsometry_mk (q : Q1) :
    sourceQ1QuotientLatticeIsometry (Additive.ofMul
      (QuotientGroup.mk' (Subgroup.center Q1Quotient)
        (QuotientGroup.mk' (K1.subgroupOf Q1) q))) = (sourceQ1LatticeHom q).toAdd := by
  change sourceLatticeComparison ((q1CentralCoordinatesEquiv
    (q1QuotientCentralEquiv (QuotientGroup.mk' (Subgroup.center Q1Quotient)
      (QuotientGroup.mk' (K1.subgroupOf Q1) q)))).toAdd) =
    sourceLatticeComparison (q1Coordinates q).toAdd
  rw [q1QuotientCentralEquiv_mk, q1QuotientEquivImage_mk,
    q1CentralCoordinatesEquiv_mk, q1ImageCoordinates_apply]

/-- The class map used by the short-lift consumers specializes to this source homomorphism. -/
theorem sourceLatticeClass_image (q : Q1) :
    latticeClass sourceLatticeComparison (q1ImageMap q) = (sourceQ1LatticeHom q).toAdd := by
  rw [latticeClass, q1ImageCoordinates_apply]
  rfl

end Sporadic.Monster.Construction.LocalC
