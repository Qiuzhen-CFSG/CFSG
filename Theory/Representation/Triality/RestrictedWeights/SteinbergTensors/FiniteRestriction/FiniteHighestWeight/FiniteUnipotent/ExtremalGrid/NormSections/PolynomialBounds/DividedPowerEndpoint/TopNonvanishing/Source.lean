module
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.PolynomialBounds.DividedPowerEndpoint.TopNonvanishing.WeylTransport
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.PolynomialBounds.DividedPowerEndpoint.TopNonvanishing.OrderComparison
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.SimpleRootOrbits.ChartTransport
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.PolynomialBounds.DividedPowerEndpoint
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.PolynomialBounds.DividedPowerEndpoint.HighestLine
/-!
# Nonzero extremal top words from the actual D4 rank-one endpoints

Conjugate each simple rank-one coefficient along the twelve checked opposition
prefixes. Every step sends the original highest vector to a nonzero scalar
multiple of the next Weyl translate. The finite collection theorem identifies
the resulting convex product with the literal height-ordered top word.
This proves both signs, including n=0, without irreducibility or a basis premise.
For cyclic modules the existing highest-line theorem gives the full endpoint.
The root uniqueness, charts and parameter relations are discharged by the
concrete Spin consumer.
Source: Steinberg (1963), sections 2.8 and 4.3; GLS3 13.2(d).
-/

public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.DividedPowerEndpoint
open AlgebraicTensor.RestrictedStep CyclicDimension D4RestrictedWeight
open ClassBound.FixedOpposition.AmbientNormalizer.CorootRealization
open ClassBound.ConnectedCentralizer.Normalizer
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

private def prefixOperator (D : Fin 12 → Module.End k V) : ℕ → Module.End k V
 | 0 => 1
 | j+1 => D ⟨j%12,Nat.mod_lt _ (by decide)⟩ * prefixOperator D j

omit [FiniteDimensional k V] in
private theorem prefix_endpoint (S : Geometry K) (C : ∀ i, SimpleRootSL2Chart S i)
    (rho : RationalRepresentation K V) (v : V) (D : Fin 12 → Module.End k V)
    (hstep : ∀ i : Fin 12, ∃ c:k,c≠0 ∧
      D i ((rho.action (oppositionPrefix S C i.val)).val v) =
      c • (rho.action (oppositionPrefix S C (i.val+1))).val v)
    (j : ℕ) (hj:j≤12) : ∃ c:k,c≠0 ∧
      prefixOperator D j v = c • (rho.action (oppositionPrefix S C j)).val v := by
  induction j with
  | zero => exact ⟨1,one_ne_zero,by simp [prefixOperator,oppositionPrefix_zero]⟩
  | succ j ih =>
    obtain ⟨c,hc,he⟩ := ih (by omega)
    let i : Fin 12 := ⟨j,by omega⟩
    obtain ⟨d,hd,hs⟩ := hstep i
    refine ⟨c*d,mul_ne_zero hc hd,?_⟩
    change (D ⟨j%12,_⟩) (prefixOperator D j v) = _
    have hi : (⟨j%12,Nat.mod_lt _ (by decide)⟩ : Fin 12)=i := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt (by omega)
    rw [hi,he,map_smul,hs,smul_smul]

private theorem negative_convex_step (S : Geometry K)
    (C : ∀ i, SimpleRootSL2Chart S i) (hu : RootSubgroupUniqueness S)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (v : V) (m : ℕ)
    (hend : ∀ i, curveCoefficient rho hr
        ((simpleChartMap (C i)).comp standardSL2LowerMorphism) m v =
      (rho.action ((simpleChartMap (C i)).onPoints rankOneWeylPoint)).val v)
    (j : Fin 12) : ∃ c:k,c≠0 ∧
      rootDividedPower S rho hr (negativeCoordinateRoot S (convexStepOrder j)) m
        ((rho.action (oppositionPrefix S C j.val)).val v) =
      c • (rho.action (oppositionPrefix S C (j.val+1))).val v := by
  obtain ⟨c,hc,he⟩ := oppositionPrefix_negative_coefficients S C hu j rho hr
  refine ⟨c^m,pow_ne_zero _ hc,?_⟩
  have h := congrArg (fun f:Module.End k V => f v) (he m)
  simp only [Module.End.mul_apply,LinearMap.smul_apply,hend] at h
  rw [oppositionPrefix_action_succ]
  exact h

private theorem positive_convex_step (S : Geometry K)
    (C : ∀ i, SimpleRootSL2Chart S i) (hu : RootSubgroupUniqueness S)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (v : V) (m : ℕ)
    (hend : ∀ i, curveCoefficient rho hr
        ((simpleChartMap (C i)).comp standardSL2UpperMorphism) m v =
      (rho.action ((simpleChartMap (C i)).onPoints rankOneWeylPoint)).val v)
    (j : Fin 12) : ∃ c:k,c≠0 ∧
      rootDividedPower S rho hr (positiveCoordinateRoot S (convexStepOrder j)) m
        ((rho.action (oppositionPrefix S C j.val)).val v) =
      c • (rho.action (oppositionPrefix S C (j.val+1))).val v := by
  obtain ⟨c,hc,he⟩ := oppositionPrefix_positive_coefficients S C hu j rho hr
  refine ⟨c^m,pow_ne_zero _ hc,?_⟩
  have h := congrArg (fun f:Module.End k V => f v) (he m)
  simp only [Module.End.mul_apply,LinearMap.smul_apply,hend] at h
  rw [oppositionPrefix_action_succ]
  exact h

private theorem prefixOperator_twelve (S : Geometry K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (r : Fin 12 → S.roots.Root) (n : ℕ) :
    prefixOperator (fun i => rootDividedPower S rho hr (r (convexStepOrder i)) (2^n-1)) 12 =
      topOperator S rho hr (fun i => r (convexOperatorOrder i)) n := by
  simp [prefixOperator,topOperator,List.ofFn_succ,convexOperatorOrder,Fin.rev,Fin.revPerm,
    Equiv.trans_apply]

private theorem negative_top_ne_zero_of_endpoints (S : Geometry K)
    (C : ∀ i, SimpleRootSL2Chart S i) (hu : RootSubgroupUniqueness S)
    (hrel : RootPairParameterRelations S)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (v : V) (hv:v≠0) (n : ℕ)
    (hend : ∀ i, curveCoefficient rho hr
        ((simpleChartMap (C i)).comp standardSL2LowerMorphism) (2^n-1) v =
      (rho.action ((simpleChartMap (C i)).onPoints rankOneWeylPoint)).val v) :
    topOperator S rho hr (negativeCoordinateRoot S) n v ≠ 0 := by
  obtain ⟨c,hc,he⟩ := prefix_endpoint S C rho v _
    (negative_convex_step S C hu rho hr v (2^n-1) hend) 12 (by decide)
  rw [prefixOperator_twelve] at he
  rw [negative_topOperator_eq_convexOrder_of_relations S hrel rho hr n,he]
  apply smul_ne_zero hc
  exact fun h => hv (((LinearMap.GeneralLinearGroup.generalLinearEquiv k V)
    (rho.action (oppositionPrefix S C 12))).injective (h.trans (map_zero _).symm))

private theorem positive_top_ne_zero_of_endpoints (S : Geometry K)
    (C : ∀ i, SimpleRootSL2Chart S i) (hu : RootSubgroupUniqueness S)
    (hrel : RootPairParameterRelations S)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (v : V) (hv:v≠0) (n : ℕ)
    (hend : ∀ i, curveCoefficient rho hr
        ((simpleChartMap (C i)).comp standardSL2UpperMorphism) (2^n-1) v =
      (rho.action ((simpleChartMap (C i)).onPoints rankOneWeylPoint)).val v) :
    topOperator S rho hr (positiveCoordinateRoot S) n v ≠ 0 := by
  obtain ⟨c,hc,he⟩ := prefix_endpoint S C rho v _
    (positive_convex_step S C hu rho hr v (2^n-1) hend) 12 (by decide)
  rw [prefixOperator_twelve] at he
  rw [positive_topOperator_eq_convexOrder_of_relations S hrel rho hr n,he]
  apply smul_ne_zero hc
  exact fun h => hv (((LinearMap.GeneralLinearGroup.generalLinearEquiv k V)
    (rho.action (oppositionPrefix S C 12))).injective (h.trans (map_zero _).symm))

omit [IsAlgClosed k] in
private theorem simple_positive (S : Geometry K) (i : Fin 4) :
    (S.simpleRoot i).val ∈ S.roots.positive :=
  ((S.realized.2.2.2.2.2.2.2.2.2.2.2.1 _).mp (S.simpleRoot i).property).1

omit [FiniteDimensional k V] in
private theorem highest_fixes_root (S : Geometry K)
    {P : Set S.roots.Root} {B : ClosedSubgroup K}
    (hB : IsBorelOfPositiveSystem S.roots P B)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (v : V) {chi : TorusWeight S.torus} (hv : HasHighWeight rho B S.torus v chi)
    (r : S.roots.Root) (hrP : r ∈ P)
    (x : OneParameterParametrization (S.roots.rootSubgroup r).carrierVariety) (t : k) :
    (rho.action ((S.roots.rootSubgroup r).includePoint (x.value t))).val v = v := by
  apply invariantLine_fixed_of_unipotent_subgroup rho hr B hB.unipotent v hv.1
    hB.radical.1 hB.radical.2.1
  change (S.roots.rootSubgroup r).includePoint (x.value t) ∈ hB.unipotent.toSubgroup
  rw [hB.root_generated]
  exact rootSubgroup_le_RootSubgroupGenerated S.roots hrP
    ((S.roots.rootSubgroup r).pointEquiv _).property

private theorem maximal_coordinate (n : ℕ) (i : Fin 4) :
    maximalRestrictedWeight n i = ((2^n-1:ℕ):ℤ) := by
  have hp : 0 < (2:ℕ)^n := pow_pos (by decide) _
  dsimp [maximalRestrictedWeight]
  rw [Nat.cast_sub (by omega),Nat.cast_pow]
  norm_num

/-- The actual negative top coefficient word does not kill a nonzero extremal highest vector. -/
theorem negative_topOperator_ne_zero (S : Geometry K)
    (hcharts : ∀ i, Nonempty (SimpleRootSL2Chart S i))
    (hu : RootSubgroupUniqueness S) (hrel : RootPairParameterRelations S)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (n : ℕ) (v : V)
    (hv : HasHighWeight rho S.bigCell.data.B S.torus v
      (S.leftWeightEmbedding (maximalRestrictedWeight n))) :
    topOperator S rho hr (negativeCoordinateRoot S) n v ≠ 0 := by
  let C := fun i => Classical.choice (hcharts i)
  apply negative_top_ne_zero_of_endpoints S C hu hrel rho hr v hv.2.1 n
  intro i
  apply rankOne_lower_endpoint rho hr (simpleChartMap (C i)) v (2^n-1)
  · intro t
    change (rho.action (((simpleChartMap (C i)).comp standardSL2UpperMorphism).onPoints
      (kPlusPoint t))).val v = _
    rw [simpleChartMap_upper]
    exact highest_fixes_root S S.bigCell.data.positive_witness rho hr v hv _
      (simple_positive S i) (C i).plus t
  · intro t
    rw [simpleChartMap_diagonal,hv.2.2,S.leftWeightEmbedding_coroot,
      maximal_coordinate,zpow_natCast]

/-- The positive top word has the same nonvanishing on an opposite highest vector. -/
theorem positive_topOperator_ne_zero (S : Geometry K)
    (hcharts : ∀ i, Nonempty (SimpleRootSL2Chart S i))
    (hu : RootSubgroupUniqueness S) (hrel : RootPairParameterRelations S)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (n : ℕ) (v : V)
    (hv : HasHighWeight rho S.bigCell.data.Bopp S.torus v
      (S.leftWeightEmbedding (maximalRestrictedWeight n))⁻¹) :
    topOperator S rho hr (positiveCoordinateRoot S) n v ≠ 0 := by
  let C := fun i => Classical.choice (hcharts i)
  apply positive_top_ne_zero_of_endpoints S C hu hrel rho hr v hv.2.1 n
  intro i
  apply rankOne_upper_endpoint rho hr (simpleChartMap (C i)) v (2^n-1)
  · intro t
    change (rho.action (((simpleChartMap (C i)).comp standardSL2LowerMorphism).onPoints
      (kPlusPoint t))).val v = _
    rw [simpleChartMap_lower]
    apply highest_fixes_root S S.bigCell.data.opposite_witness rho hr v hv _ ?_ (C i).minus t
    change S.roots.neg (S.roots.neg (S.simpleRoot i).val) ∈ S.roots.positive
    rw [S.realized.neg_neg]
    exact simple_positive S i
  · intro t
    rw [simpleChartMap_diagonal,hv.2.2]
    have he : ((S.leftWeightEmbedding (maximalRestrictedWeight n))⁻¹).pointCharacter
        ((S.leftSimpleCoroot i).onPoints t) =
      ((S.leftWeightEmbedding (maximalRestrictedWeight n)).pointCharacter
        ((S.leftSimpleCoroot i).onPoints t))⁻¹ := by
      change (torusPointEval _ _ ((S.leftWeightEmbedding _)⁻¹) : k) = _
      rw [map_inv,Units.val_inv_eq_inv_val]
      rfl
    rw [he,S.leftWeightEmbedding_coroot,maximal_coordinate,zpow_natCast,inv_pow]

/-- A positive cyclic highest module has the actual nonzero divided-power endpoint. -/
theorem negative_endpoint_of_source (S : Geometry K)
    (hcharts : ∀ i, Nonempty (SimpleRootSL2Chart S i))
    (hu : RootSubgroupUniqueness S) (hrel : RootPairParameterRelations S)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (n : ℕ) (v : V)
    (hv : HasHighWeight rho S.bigCell.data.B S.torus v
      (S.leftWeightEmbedding (maximalRestrictedWeight n)))
    (hcyc : IsCyclicRepresentation rho v) (r : Variety.Point K)
    (hinv : ∀ t : Variety.Point S.torus.carrierVariety,
      r*S.torus.includePoint t*r⁻¹=(S.torus.includePoint t)⁻¹) :
    ∃ c:k,c≠0 ∧ topOperator S rho hr (negativeCoordinateRoot S) n v =
      c • (rho.action r).val v :=
  negative_endpoint_of_highestLine_of_top_ne_zero S rho hr n v hv r hinv
    (positive_extremal_highest_weightSpace S n rho hr hv hcyc)
    (negative_topOperator_ne_zero S hcharts hu hrel rho hr n v hv)

/-- The same endpoint for the opposite Borel and literal positive root order. -/
theorem positive_endpoint_of_source (S : Geometry K)
    (hcharts : ∀ i, Nonempty (SimpleRootSL2Chart S i))
    (hu : RootSubgroupUniqueness S) (hrel : RootPairParameterRelations S)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (n : ℕ) (v : V)
    (hv : HasHighWeight rho S.bigCell.data.Bopp S.torus v
      (S.leftWeightEmbedding (maximalRestrictedWeight n))⁻¹)
    (hcyc : IsCyclicRepresentation rho v) (r : Variety.Point K)
    (hinv : ∀ t : Variety.Point S.torus.carrierVariety,
      r*S.torus.includePoint t*r⁻¹=(S.torus.includePoint t)⁻¹) :
    ∃ c:k,c≠0 ∧ topOperator S rho hr (positiveCoordinateRoot S) n v =
      c • (rho.action r).val v :=
  positive_endpoint_of_highestLine_of_top_ne_zero S rho hr n v hv r hinv
    (opposite_extremal_highest_weightSpace S n rho hr hv hcyc)
    (positive_topOperator_ne_zero S hcharts hu hrel rho hr n v hv)
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.DividedPowerEndpoint
