module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Generation.FixedOpposition.AmbientNormalizer.SimpleReflections.WordConstruction
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.TorusGeometry.Coordinates
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords.Normalization

/-!
# Comparing D4 rank-one charts with the supplied coroots

In characteristic two the four actual simple-root characters separate torus
points. Indeed, twice every integral D4 weight is a combination of the Cartan
rows, and squaring is injective in the field. Thus the Cartan equations
uniquely identify a cocharacter with the one supplied by `Geometry`.

A compatible SL₂ chart, including containment of its diagonal image in the
torus, satisfies all Cartan equations by `RootGroupData.chart_isCartan`.
The latter derives the reflection on the finite set of actual roots; it does
not assume the coroot comparison. The chart's normalized word therefore
recovers the supplied coroot with the convention `n(1)⁻¹ n(z)`.

Chart existence is a separate geometric obligation. None of the declarations
below constructs the compatible morphism or assumes the ambient group has
already been identified with a concrete D4 carrier.

Sources: GLS3, `refs/KGroup/GLS3/Chapter1.tex`, Theorem 1.9.5(d),
Remarks 1.9.6 and the defining formulas of Theorem 1.12.1;
`refs/KGroup/GLS3/Chapter2St2.tex`, Section 6.
-/

@[expose] public noncomputable section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open D4RestrictedWeight
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.FixedOpposition.AmbientNormalizer.CorootRealization
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

private def rootCoefficients (a : Weight) : Fin 4 → ℤ :=
  ![2 * a 0 + 2 * a 1 + a 2 + a 3,
    2 * a 0 + 4 * a 1 + 2 * a 2 + 2 * a 3,
    a 0 + 2 * a 1 + 2 * a 2 + a 3,
    a 0 + 2 * a 1 + a 2 + 2 * a 3]

private theorem twice_weight (a : Weight) :
    (2 : ℕ) • a =
      rootCoefficients a 0 • typeDCartanMatrix 2 0 +
      rootCoefficients a 1 • typeDCartanMatrix 2 1 +
      rootCoefficients a 2 • typeDCartanMatrix 2 2 +
      rootCoefficients a 3 • typeDCartanMatrix 2 3 := by
  funext j
  fin_cases j <;> simp [rootCoefficients, typeDCartanMatrix] <;> ring

omit [IsAlgClosed k] in
private theorem square_weight (S : Geometry K) (a : Weight) :
    S.weight (Multiplicative.ofAdd a) ^ 2 =
      S.roots.rootWeight (S.simpleRoot 0).val ^ rootCoefficients a 0 *
      S.roots.rootWeight (S.simpleRoot 1).val ^ rootCoefficients a 1 *
      S.roots.rootWeight (S.simpleRoot 2).val ^ rootCoefficients a 2 *
      S.roots.rootWeight (S.simpleRoot 3).val ^ rootCoefficients a 3 := by
  simp only [AmbientCount.TorusGeometry.simple_rootWeight,
    ← map_zpow, ← map_mul, ← map_pow]
  congr 1
  exact twice_weight a

/-- The actual simple-root characters separate torus points in characteristic
two, although the D4 root lattice need not equal the full weight lattice. -/
theorem torusPoint_ext_simpleRoots (S : Geometry K)
    {t v : Variety.Point S.torus.carrierVariety}
    (h : ∀ i : Fin 4, (S.roots.rootWeight (S.simpleRoot i).val).pointCharacter t =
      (S.roots.rootWeight (S.simpleRoot i).val).pointCharacter v) : t = v := by
  apply (torusPointEval_bijective S.maximalTorus.1).1
  apply MonoidHom.ext
  intro χ
  obtain ⟨a, rfl⟩ := S.weight.surjective χ
  apply Units.ext
  apply CharTwo.sq_injective
  have hr (i : Fin 4) : torusPointEval _ t (S.roots.rootWeight (S.simpleRoot i).val) =
      torusPointEval _ v (S.roots.rootWeight (S.simpleRoot i).val) := Units.ext (h i)
  have he : torusPointEval _ t (S.weight (Multiplicative.ofAdd a.toAdd) ^ 2) =
      torusPointEval _ v (S.weight (Multiplicative.ofAdd a.toAdd) ^ 2) := by
    rw [square_weight]
    simp only [map_mul, map_zpow, hr]
  simpa only [map_pow, Units.val_pow_eq_pow_val, ofAdd_toAdd] using congrArg Units.val he

/-- Cartan equations uniquely determine every supplied D4 root cocharacter. -/
theorem rootCocharacter_unique (S : Geometry K) (a : S.roots.Root)
    (h : ClosedSubgroupTorusCocharacter S.torus)
    (hh : S.roots.IsCartanRootCocharacter a h) :
    h = S.roots.rootCocharacter a := by
  apply Morphism.ext
  funext t
  apply torusPoint_ext_simpleRoots S
  intro i
  exact (hh (S.simpleRoot i).val t).trans
    (S.realized.rootWeight_rootCocharacter (S.simpleRoot i).val a t).symm

/-- A compatible regular SL₂ chart for one marked actual opposite-root pair.
Its geometric diagonal containment is part of the chart, not its Cartan
normalization or an equality with the stored coroot. -/
abbrev SimpleRootSL2Chart (S : Geometry K) (i : Fin 4) :=
  BinaryOppositeRootSL2Chart S.torus
    (S.roots.rootSubgroup (S.simpleRoot i).val)
    (S.roots.rootSubgroup (S.roots.neg (S.simpleRoot i).val))

/-- The chart cocharacter equals the supplied coroot, with no normalization
hypothesis beyond the geometry of the chart. -/
theorem SimpleRootSL2Chart.cocharacter_eq (S : Geometry K) (i : Fin 4)
    (C : SimpleRootSL2Chart S i) :
    C.cocharacter = S.roots.rootCocharacter (S.simpleRoot i).val := by
  let : Finite S.roots.Root := Finite.of_injective S.rootIndex S.rootIndex.injective
  exact rootCocharacter_unique S (S.simpleRoot i).val C.cocharacter
    (S.roots.chart_isCartan S.realized S.maximalTorus.1 (S.simpleRoot i).val C)

/-- Keep the two compatible parametrizations of the chart. -/
def SimpleRootSL2Chart.parameters {S : Geometry K} {i : Fin 4}
    (C : SimpleRootSL2Chart S i) : SimpleRootParameters S i :=
  ⟨C.plus, C.minus⟩

/-- The ambient word made from these same parametrizations realizes the
supplied coroot simultaneously for every nonzero parameter. -/
theorem SimpleRootSL2Chart.coroot_eq {S : Geometry K} {i : Fin 4}
    (C : SimpleRootSL2Chart S i) (z : Variety.Point (KMult k)) :
    S.torus.includePoint ((S.roots.rootCocharacter (S.simpleRoot i).val).onPoints z) =
      (C.parameters.word 1)⁻¹ * C.parameters.word (dPointEquiv 1 z 0) := by
  have h := C.word_eq_cocharacter z
  rw [SimpleRootSL2Chart.cocharacter_eq S i C, binaryCorootWord_apply] at h
  change S.torus.inclusion.onPoints
    ((S.roots.rootCocharacter (S.simpleRoot i).val).onPoints z) = _
  rw [← h]
  simp only [SimpleRootParameters.word, SimpleRootSL2Chart.parameters,
    inv_one, Units.val_one, CharTwo.neg_eq, Units.val_inv_eq_inv_val]
  rfl

/-- Assemble the four actual normalized words from four geometric charts. -/
def simpleCorootWordData_of_charts (S : Geometry K)
    (C : ∀ i, SimpleRootSL2Chart S i) : SimpleCorootWordData S where
  parameters i := (C i).parameters
  coroot_eq i := (C i).coroot_eq

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.FixedOpposition.AmbientNormalizer.CorootRealization
