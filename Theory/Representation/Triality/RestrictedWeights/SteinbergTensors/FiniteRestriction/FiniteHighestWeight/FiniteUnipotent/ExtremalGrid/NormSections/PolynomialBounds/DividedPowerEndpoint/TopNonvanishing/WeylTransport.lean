module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.PolynomialBounds.DividedPowerEndpoint.Operators
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.PolynomialBounds.DividedPowerEndpoint.TopNonvanishing.Charts
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.PolynomialBounds.DividedPowerEndpoint.TopNonvanishing.WeylOrder
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Generation.FixedOpposition.AmbientNormalizer.SimpleReflections
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Normalizer.Lifts.RootTransport.UniquenessInput
public import Theory.AlgebraicGroup.RootSubgroups.Conjugation
/-!
# Root curves and divided coefficients along the D4 opposition prefixes

For the list-order prefix products of the actual chart words, inverse torus
conjugation acts on characters by the reversed reflection word. The checked
convex-root coordinates and root-subgroup uniqueness therefore identify the
actual conjugated positive and negative root subgroups. Comparing their regular
one-parameter parametrizations introduces separate nonzero scalars for the two
signs; no simultaneous normalization of the supplied root parameters is used.

The curve equations use the reciprocal convention: the supplied root curve at
`t` is the conjugate of the chart curve at `c * t`. Coefficient comparison and
intertwining then give `D_beta(m) * A = c^m • (A * D_simple(m))` for every degree
and every vector. Each coefficient theorem chooses one scalar for all degrees.
The subgroup-uniqueness premise is explicit and must be supplied by the consumer.

Sources: GLS3 Chapter 1, §§1.9 and 1.12; Steinberg (1963), §4.3. Raw root
characters retain inverse conjugation, as in the triality coroot convention
correction; the actual positive root groups and the chart words are unchanged.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.DividedPowerEndpoint
open AlgebraicTensor.RestrictedStep CyclicDimension D4RestrictedWeight
open ClassBound.FixedOpposition.AmbientNormalizer
open ClassBound.FixedOpposition.AmbientNormalizer.CorootRealization
open ClassBound.ConnectedCentralizer.Normalizer
public noncomputable section
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]
variable (S : Geometry K) (C : ∀ i, SimpleRootSL2Chart S i)

/-- Actual products in list order, including the empty and full prefixes. -/
@[expose] def oppositionPrefix (j : ℕ) : Variety.Point K :=
  ((oppositionWord.take j).map fun i => (C i).parameters.word 1).prod

/-- The empty prefix is the identity point. -/
theorem oppositionPrefix_zero : oppositionPrefix S C 0 = 1 := rfl

/-- The twelfth prefix contains all twelve chart words. -/
theorem oppositionPrefix_twelve :
    oppositionPrefix S C 12 = (oppositionWord.map fun i => (C i).parameters.word 1).prod := rfl

/-- Append the next simple chart word on the right, for all twelve steps. -/
theorem oppositionPrefix_succ (j : Fin 12) :
    oppositionPrefix S C (j.val + 1) =
      oppositionPrefix S C j.val * (C (oppositionSimpleStep j)).parameters.word 1 := by
  fin_cases j <;>
    simp [oppositionPrefix, oppositionWord, oppositionSimpleStep, mul_assoc]

omit [IsAlgClosed k] in
private theorem representativeWord_eq (D : SimpleReflectionLifts S) (w : List (Fin 4)) :
    D.representativeWord w = (w.reverse.map D.representative).prod := by
  induction w with
  | nil => rfl
  | cons i w ih => simp [SimpleReflectionLifts.representativeWord, ih]

private def chartLifts : SimpleReflectionLifts S :=
  (simpleCorootWordData_of_charts S C).toSimpleReflectionLifts

private theorem prefix_eq (j : ℕ) :
    oppositionPrefix S C j =
      (chartLifts S C).representativeWord (oppositionWord.take j).reverse := by
  rw [representativeWord_eq]
  simp only [List.reverse_reverse]
  rfl

/-- Every actual prefix normalizes the supplied torus. -/
theorem oppositionPrefix_mem_normalizer (j : ℕ) :
    oppositionPrefix S C j ∈ S.torus.normalizer.toSubgroup := by
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg
  exact (simpleCorootWordData_of_charts S C).mem_normalizer i

omit [IsAlgClosed k] in
private theorem rootWeight_raw (a : S.roots.Root) :
    S.weight (Multiplicative.ofAdd (rootWeight S a)) = S.roots.rootWeight a := by
  apply inv_injective
  exact (S.leftWeightEmbedding_eq_inv (rootWeight S a)).symm.trans (rootWeight_character S a)

omit [IsAlgClosed k] in
private theorem simple_rootWeight (i : Fin 4) :
    rootWeight S (S.simpleRoot i).val = typeDCartanMatrix 2 i := by
  funext j
  apply Int.cast_injective (α := ℝ)
  have h := S.based.1 (S.simpleRoot i).val (S.simpleRoot j).val
  rw [S.simpleRoot_index, S.simpleRoot_index, typeDRootPairing_simpleIndex_pairing] at h
  exact h

omit [IsAlgClosed k] in
private theorem neg_rootWeight (a : S.roots.Root) :
    rootWeight S (S.roots.neg a) = -rootWeight S a := by
  apply S.leftWeightEmbedding.injective
  rw [rootWeight_character, S.leftWeightEmbedding_neg, rootWeight_character]
  exact congrArg Inv.inv (S.realized.2.2.2.1 a)

private theorem wordAction_neg' (a : Weight) (w : List (Fin 4)) :
    wordAction (-a) w = -wordAction a w := by
  induction w generalizing a with
  | nil => rfl
  | cons i w ih =>
    change wordAction (reflection i (-a)) w = -wordAction (reflection i a) w
    rw [LeftWeights.reflection_neg, ih]

private theorem prefix_rootSubgroup (hunique : RootSubgroupUniqueness S)
    (j : ℕ) (a b : S.roots.Root)
    (hab : rootWeight S b = wordAction (rootWeight S a) (oppositionWord.take j).reverse) :
    (S.roots.rootSubgroup a).conjugate (oppositionPrefix S C j) =
      S.roots.rootSubgroup b := by
  apply hunique b _
  · exact IsTorusRootSubgroup.conjugate_of_mem_normalizer _
      (oppositionPrefix_mem_normalizer S C j) (S.realized.2.2.1 a).1
  intro y z t
  let g := oppositionPrefix S C j
  let X := S.roots.rootSubgroup a
  let e := X.conjugateIso g
  let x : OneParameterParametrization X.carrierVariety := e.symm.comp y
  let t₀ := (chartLifts S C).torusWord (oppositionWord.take j).reverse t
  have ht : S.torus.includePoint t₀ = g⁻¹ * S.torus.includePoint t * g := by
    have h := (chartLifts S C).word_conjugation (oppositionWord.take j).reverse t
    rw [← prefix_eq S C j] at h
    change S.torus.includePoint t * g = g * S.torus.includePoint t₀ at h
    rw [mul_assoc, h, inv_mul_cancel_left]
  have hx (v : k) : X.includePoint (x.value v) =
      g⁻¹ * (X.conjugate g).includePoint (y.value v) * g :=
    X.conjugateIso_inv_inclusion_apply g (y.value v)
  have hc : (S.roots.rootWeight a).pointCharacter t₀ =
      (S.roots.rootWeight b).pointCharacter t := by
    rw [← rootWeight_raw S a, ← rootWeight_raw S b, hab]
    exact (chartLifts S C).word_character _ _ _
  have h := (S.realized.2.2.1 a).2 x z t₀
  apply (MulAut.conj g⁻¹).injective
  rw [MulAut.conj_apply, MulAut.conj_apply, inv_inv]
  calc
    _ = (S.torus.includePoint t₀)⁻¹ * X.includePoint (x.value z) *
        S.torus.includePoint t₀ := by rw [ht, hx]; dsimp only [X, g]; group
    _ = X.includePoint (x.value ((S.roots.rootWeight a).pointCharacter t₀ * z)) := h
    _ = _ := by rw [hx, hc]

/-- Left conjugation carries the positive simple root subgroup to the crossed root. -/
theorem oppositionPrefix_positive_subgroup (hunique : RootSubgroupUniqueness S)
    (j : Fin 12) :
    (S.roots.rootSubgroup (S.simpleRoot (oppositionSimpleStep j)).val).conjugate
        (oppositionPrefix S C j.val) =
      S.roots.rootSubgroup (positiveCoordinateRoot S (convexStepOrder j)) := by
  apply prefix_rootSubgroup S C hunique
  rw [simple_rootWeight]
  exact convexStep_rootWeight S j

/-- Left conjugation carries the opposite simple root subgroup to the opposite crossed root. -/
theorem oppositionPrefix_negative_subgroup (hunique : RootSubgroupUniqueness S)
    (j : Fin 12) :
    (S.roots.rootSubgroup (S.roots.neg (S.simpleRoot (oppositionSimpleStep j)).val)).conjugate
        (oppositionPrefix S C j.val) =
      S.roots.rootSubgroup (S.roots.neg (positiveCoordinateRoot S (convexStepOrder j))) := by
  apply prefix_rootSubgroup S C hunique
  rw [neg_rootWeight, neg_rootWeight, wordAction_neg', simple_rootWeight]
  exact congrArg Neg.neg (convexStep_rootWeight S j)

omit [CharP k 2] in
private theorem conjugate_parameter (X Y : ClosedSubgroup K) (g : Variety.Point K)
    (hXY : X.conjugate g = Y)
    (x : OneParameterParametrization X.carrierVariety)
    (y : OneParameterParametrization Y.carrierVariety) :
    ∃ c : k, c ≠ 0 ∧ ∀ t : k,
      Y.includePoint (y.value t) = g * X.includePoint (x.value (c * t)) * g⁻¹ := by
  subst Y
  let z : OneParameterParametrization (X.conjugate g).carrierVariety :=
    (X.conjugateIso g).comp x
  obtain ⟨c, hc, _⟩ := oneParameterParametrization_eq_rescale z y
  refine ⟨c, hc.1, fun t => ?_⟩
  rw [hc.2 t]
  exact X.conjugateIso_hom_inclusion_apply g (x.value (c * t))

/-- Reciprocal parameter convention: the supplied root at `t` is the
conjugate of the chart curve at `c * t`. -/
theorem oppositionPrefix_positive_curve (hunique : RootSubgroupUniqueness S)
    (j : Fin 12) :
    ∃ c : k, c ≠ 0 ∧ ∀ t : k,
      (rootCurve S (positiveCoordinateRoot S (convexStepOrder j))).onPoints (kPlusPoint t) =
        oppositionPrefix S C j.val *
          ((simpleChartMap (C (oppositionSimpleStep j))).comp standardSL2UpperMorphism).onPoints
            (kPlusPoint (c * t)) * (oppositionPrefix S C j.val)⁻¹ := by
  rw [simpleChartMap_upper]
  exact conjugate_parameter _ _ _ (oppositionPrefix_positive_subgroup S C hunique j)
    (C (oppositionSimpleStep j)).plus (S.rootParameter _)

/-- The negative supplied curve is the conjugated lower chart curve after an
independent nonzero parameter rescaling, in the same reciprocal convention. -/
theorem oppositionPrefix_negative_curve (hunique : RootSubgroupUniqueness S)
    (j : Fin 12) :
    ∃ c : k, c ≠ 0 ∧ ∀ t : k,
      (rootCurve S (S.roots.neg (positiveCoordinateRoot S (convexStepOrder j)))).onPoints
          (kPlusPoint t) =
        oppositionPrefix S C j.val *
          ((simpleChartMap (C (oppositionSimpleStep j))).comp standardSL2LowerMorphism).onPoints
            (kPlusPoint (c * t)) * (oppositionPrefix S C j.val)⁻¹ := by
  rw [simpleChartMap_lower]
  exact conjugate_parameter _ _ _ (oppositionPrefix_negative_subgroup S C hunique j)
    (C (oppositionSimpleStep j)).minus (S.rootParameter _)

variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

omit [FiniteDimensional k V] in
/-- The prefix recurrence after applying a representation, in operator order. -/
theorem oppositionPrefix_action_succ (rho : RationalRepresentation K V) (j : Fin 12) :
    (rho.action (oppositionPrefix S C (j.val + 1))).val =
      (rho.action (oppositionPrefix S C j.val)).val *
        (rho.action ((simpleChartMap (C (oppositionSimpleStep j))).onPoints rankOneWeylPoint)).val := by
  rw [oppositionPrefix_succ, simpleChartMap_weyl, map_mul, Units.val_mul]

omit [CharP k 2] in
private theorem conjugate_coefficients (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (X Y : ClosedSubgroup K) (g : Variety.Point K)
    (hXY : X.conjugate g = Y)
    (x : OneParameterParametrization X.carrierVariety)
    (y : OneParameterParametrization Y.carrierVariety) :
    ∃ c : k, c ≠ 0 ∧ ∀ m : ℕ,
      curveCoefficient rho hr (Y.inclusion.comp y.hom) m * (rho.action g).val =
        c ^ m • ((rho.action g).val * curveCoefficient rho hr (X.inclusion.comp x.hom) m) := by
  subst Y
  let z : OneParameterParametrization (X.conjugate g).carrierVariety :=
    (X.conjugateIso g).comp x
  obtain ⟨c, hc, he⟩ := coefficient_change_parameter rho hr (X.conjugate g) z y
  refine ⟨c, hc, fun m => ?_⟩
  have hpoint (t : k) :
      g * (X.inclusion.comp x.hom).onPoints (kPlusPoint t) =
        ((X.conjugate g).inclusion.comp z.hom).onPoints (kPlusPoint t) * g := by
    change g * X.inclusion.onPoints (x.value t) =
      (X.conjugate g).inclusion.onPoints ((X.conjugateIso g).hom.onPoints (x.value t)) * g
    rw [X.conjugateIso_hom_inclusion_apply]
    group
  have hi := curveCoefficient_intertwine rho hr (X.inclusion.comp x.hom)
    ((X.conjugate g).inclusion.comp z.hom) (rho.action g).val (rho.action g).val 1
    (fun t v => by
      have h := congrArg (fun a => (rho.action a).val v) (hpoint t)
      simpa only [one_mul, map_mul, Units.val_mul, Module.End.mul_apply] using h) m
  simp only [one_pow, one_smul] at hi
  rw [he m, smul_mul_assoc, ← hi]

/-- Positive coefficient transport on the entire representation, with one
nonzero reciprocal parameter scalar valid in every degree. -/
theorem oppositionPrefix_positive_coefficients (hunique : RootSubgroupUniqueness S)
    (j : Fin 12) (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho) :
    ∃ c : k, c ≠ 0 ∧ ∀ m : ℕ,
      rootDividedPower S rho hr (positiveCoordinateRoot S (convexStepOrder j)) m *
          (rho.action (oppositionPrefix S C j.val)).val =
        c ^ m • ((rho.action (oppositionPrefix S C j.val)).val *
          curveCoefficient rho hr
            ((simpleChartMap (C (oppositionSimpleStep j))).comp standardSL2UpperMorphism) m) := by
  rw [simpleChartMap_upper]
  exact conjugate_coefficients rho hr _ _ _ (oppositionPrefix_positive_subgroup S C hunique j)
    (C (oppositionSimpleStep j)).plus (S.rootParameter _)

/-- Negative coefficient transport on the entire representation, with its own
nonzero reciprocal parameter scalar valid in every degree. -/
theorem oppositionPrefix_negative_coefficients (hunique : RootSubgroupUniqueness S)
    (j : Fin 12) (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho) :
    ∃ c : k, c ≠ 0 ∧ ∀ m : ℕ,
      rootDividedPower S rho hr (S.roots.neg (positiveCoordinateRoot S (convexStepOrder j))) m *
          (rho.action (oppositionPrefix S C j.val)).val =
        c ^ m • ((rho.action (oppositionPrefix S C j.val)).val *
          curveCoefficient rho hr
            ((simpleChartMap (C (oppositionSimpleStep j))).comp standardSL2LowerMorphism) m) := by
  rw [simpleChartMap_lower]
  exact conjugate_coefficients rho hr _ _ _ (oppositionPrefix_negative_subgroup S C hunique j)
    (C (oppositionSimpleStep j)).minus (S.rootParameter _)

end
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.DividedPowerEndpoint
