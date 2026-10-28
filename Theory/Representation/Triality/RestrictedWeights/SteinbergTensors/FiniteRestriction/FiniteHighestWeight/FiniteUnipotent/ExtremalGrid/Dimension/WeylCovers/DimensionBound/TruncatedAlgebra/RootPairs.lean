module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.CoefficientLaws
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.RootPairs.Basic
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.RootPairs.PolynomialTransfer
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.RootPairs.SimpleGeneration
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.RootPairs.PositiveParameters
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.RootPairs.GeometryRelations

/-!
# Nonopposite root coefficients

Positive commutator containment gives a regular commutator polynomial; torus
characters force its sum-root parameter to be κst. The four SL₂ charts and
root-subgroup uniqueness transport these laws to every nonopposite pair and
prove κ ≠ 0, retaining the arbitrary supplied root parametrizations.

Two polynomial coefficient extractions give the complete higher-coefficient
straightening relation. Transport of a coefficient below q is an explicit sum
of products of coefficients still below q. Root-addition induction, followed
by degree induction using κ ≠ 0, proves generation by the eight signed simple
root strings. The geometric assembly theorems require only the displayed chart,
commutator-containment and root-subgroup-uniqueness inputs; their construction
is the responsibility of the source-theorem assembly owner.

Sources: GLS3 1.12.1 and 1.12.7; Chapter2St2 6.2(b);
Steinberg, Representations of algebraic groups (1963), §2.
-/

open Theory.AlgebraicGroup
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
public noncomputable section
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The complete coefficient identity for an actual sum-root parameter relation. -/
theorem rootCoefficient_exchange_of_parameterRelations (S : Geometry K)
    (hrel : RootPairParameterRelations S) (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (a b c : S.roots.Root) (hsum : RootSum S a b c) :
    ∃ κ : k, κ ≠ 0 ∧ ∀ i j : ℕ,
      rootCoefficient S rho hr a i * rootCoefficient S rho hr b j =
        ∑ m ∈ Finset.range (min i j + 1), κ ^ m •
          (rootCoefficient S rho hr b (j - m) * rootCoefficient S rho hr c m *
            rootCoefficient S rho hr a (i - m)) := by
  obtain ⟨κ, hκ, he⟩ := hrel.exchange a b c hsum
  exact ⟨κ, hκ, curveCoefficient_exchange rho hr _ _ _ κ he⟩

/-- The absent-sum branch gives commutation in every coefficient degree. -/
theorem rootCoefficient_commute_of_parameterRelations (S : Geometry K)
    (hrel : RootPairParameterRelations S) (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (a b : S.roots.Root)
    (hne : a ≠ b) (hop : b ≠ S.roots.neg a) (hsum : ¬ ∃ c, RootSum S a b c)
    (i j : ℕ) : Commute (rootCoefficient S rho hr a i) (rootCoefficient S rho hr b j) :=
  curveCoefficient_commute rho hr _ _ (hrel.commute a b hne hop hsum) i j

/-- The explicitly transported operator, obtained by extracting the second parameter. -/
@[expose] def rootPairTransport (S : Geometry K) (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (b c : S.roots.Root) (κ s : k) (j : ℕ) :
    Module.End k V :=
  ∑ m ∈ Finset.range (j + 1), (κ * s) ^ m •
    (rootCoefficient S rho hr b (j - m) * rootCoefficient S rho hr c m)

theorem rootPairTransport_mem (S : Geometry K) (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (b c : S.roots.Root) (κ s : k) (q j : ℕ)
    (hj : j < q) : rootPairTransport S rho hr b c κ s j ∈ coefficientAlgebra S rho hr q := by
  apply (coefficientAlgebra S rho hr q).sum_mem
  intro m hm
  have hmj : m ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
  exact (coefficientAlgebra S rho hr q).smul_mem
    ((coefficientAlgebra S rho hr q).mul_mem
      (rootCoefficient_mem S rho hr q b _ (by omega))
      (rootCoefficient_mem S rho hr q c _ (by omega))) _

/-- A fixed root point transports a coefficient to the displayed convolution. -/
theorem rootCoefficient_transport_of_exchange (S : Geometry K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (a b c : S.roots.Root) (κ : k)
    (he : ∀ s t : k,
      (rootCurve S a).onPoints (kPlusPoint s) * (rootCurve S b).onPoints (kPlusPoint t) =
        (rootCurve S b).onPoints (kPlusPoint t) *
          (rootCurve S c).onPoints (kPlusPoint (κ * s * t)) *
            (rootCurve S a).onPoints (kPlusPoint s)) (s : k) (j : ℕ) :
    (rho.action ((rootCurve S a).onPoints (kPlusPoint s))).val * rootCoefficient S rho hr b j =
      rootPairTransport S rho hr b c κ s j *
        (rho.action ((rootCurve S a).onPoints (kPlusPoint s))).val := by
  rw [rootPairTransport, Finset.sum_mul]
  simp only [smul_mul_assoc]
  exact curveCoefficient_product_intertwine rho hr _ _ _ _ (κ * s) (fun t => by
    simpa only [map_mul, Units.val_mul] using
      congrArg (fun g => (rho.action g).val) (he s t)) j

/-- Both nonopposite branches give an operator in the actual truncated algebra. -/
theorem rootCoefficient_transport_of_parameterRelations (S : Geometry K)
    (hrel : RootPairParameterRelations S) (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (a b : S.roots.Root)
    (hne : a ≠ b) (hop : b ≠ S.roots.neg a) (s : k) (q j : ℕ) (hj : j < q) :
    ∃ L ∈ coefficientAlgebra S rho hr q,
      (rho.action ((rootCurve S a).onPoints (kPlusPoint s))).val * rootCoefficient S rho hr b j =
        L * (rho.action ((rootCurve S a).onPoints (kPlusPoint s))).val := by
  classical
  by_cases hsum : ∃ c, RootSum S a b c
  · obtain ⟨c, hc⟩ := hsum
    obtain ⟨κ, _, he⟩ := hrel.exchange a b c hc
    exact ⟨rootPairTransport S rho hr b c κ s j,
      rootPairTransport_mem S rho hr b c κ s q j hj,
      rootCoefficient_transport_of_exchange S rho hr a b c κ he s j⟩
  · refine ⟨rootCoefficient S rho hr b j, rootCoefficient_mem S rho hr q b j hj, ?_⟩
    have ht := curveCoefficient_intertwine rho hr (rootCurve S b) (rootCurve S b)
      (rho.action ((rootCurve S a).onPoints (kPlusPoint s))).val 1 (fun t => ?_) j
    · simpa only [one_pow, one_smul, rootCoefficient] using ht
    simpa only [one_mul, map_mul, Units.val_mul] using
      congrArg (fun g => (rho.action g).val) (hrel.commute a b hne hop hsum s t).eq

section GeometryAssembly

variable (S : Geometry K)
variable (hcharts : ∀ i : Fin 4, Nonempty
  (ClassBound.FixedOpposition.AmbientNormalizer.CorootRealization.SimpleRootSL2Chart S i))
variable (hcomm :
  ClassBound.ConnectedCentralizer.Bruhat.Coordinates.Normalization.PositiveCommutatorContainment S)
variable (hunique : ClassBound.ConnectedCentralizer.Normalizer.RootSubgroupUniqueness S)
include hcharts hcomm hunique

/-- Actual nonopposite parameter laws from precisely the three geometric inputs.
The positive polynomial laws and nonvanishing are discharged here. -/
theorem rootPairParameterRelations_of_geometry : RootPairParameterRelations S :=
  rootPairParameterRelations_of_positive_and_charts S hcharts hunique
    (positiveRootPairParameterRelations_of_containment S hcomm)

/-- Distinct nonopposite roots whose sum is absent have commuting root points. -/
theorem rootCurve_commute_of_geometry (a b : S.roots.Root)
    (hne : a ≠ b) (hop : b ≠ S.roots.neg a) (hsum : ¬ ∃ c, RootSum S a b c)
    (s t : k) :
    Commute ((rootCurve S a).onPoints (kPlusPoint s))
      ((rootCurve S b).onPoints (kPlusPoint t)) :=
  (rootPairParameterRelations_of_geometry S hcharts hcomm hunique).commute
    a b hne hop hsum s t

/-- Arbitrary supplied parameters admit a nonzero, parameter-independent
sum-root constant. Root addition is through the actual D4 root-index map. -/
theorem rootCurve_exchange_of_geometry (a b c : S.roots.Root) (hsum : RootSum S a b c) :
    ∃ κ : k, κ ≠ 0 ∧ ∀ s t : k,
      (rootCurve S a).onPoints (kPlusPoint s) * (rootCurve S b).onPoints (kPlusPoint t) =
        (rootCurve S b).onPoints (kPlusPoint t) *
          (rootCurve S c).onPoints (kPlusPoint (κ * s * t)) *
            (rootCurve S a).onPoints (kPlusPoint s) :=
  (rootPairParameterRelations_of_geometry S hcharts hcomm hunique).exchange a b c hsum

/-- The complete coefficient relation in all degrees, retaining the powers of
the actual nonzero exchange constant. -/
theorem rootCoefficient_exchange_of_geometry (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (a b c : S.roots.Root) (hsum : RootSum S a b c) :
    ∃ κ : k, κ ≠ 0 ∧ ∀ i j : ℕ,
      rootCoefficient S rho hr a i * rootCoefficient S rho hr b j =
        ∑ m ∈ Finset.range (min i j + 1), κ ^ m •
          (rootCoefficient S rho hr b (j - m) * rootCoefficient S rho hr c m *
            rootCoefficient S rho hr a (i - m)) :=
  rootCoefficient_exchange_of_parameterRelations S
    (rootPairParameterRelations_of_geometry S hcharts hcomm hunique) rho hr a b c hsum

/-- The absent-sum coefficient relation, with no restriction on the degrees. -/
theorem rootCoefficient_commute_of_geometry (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (a b : S.roots.Root)
    (hne : a ≠ b) (hop : b ≠ S.roots.neg a) (hsum : ¬ ∃ c, RootSum S a b c) (i j : ℕ) :
    Commute (rootCoefficient S rho hr a i) (rootCoefficient S rho hr b j) :=
  rootCoefficient_commute_of_parameterRelations S
    (rootPairParameterRelations_of_geometry S hcharts hcomm hunique) rho hr
    a b hne hop hsum i j

/-- In the sum-root branch, the explicitly displayed convolution is the
transported operator and belongs to the truncated coefficient algebra. One
nonzero constant works for all parameters, truncations and degrees. -/
theorem rootCoefficient_transport_sum_of_geometry (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (a b c : S.roots.Root) (hsum : RootSum S a b c) :
    ∃ κ : k, κ ≠ 0 ∧ ∀ (s : k) (q j : ℕ), j < q →
      rootPairTransport S rho hr b c κ s j ∈ coefficientAlgebra S rho hr q ∧
        (rho.action ((rootCurve S a).onPoints (kPlusPoint s))).val *
            rootCoefficient S rho hr b j =
          rootPairTransport S rho hr b c κ s j *
            (rho.action ((rootCurve S a).onPoints (kPlusPoint s))).val := by
  obtain ⟨κ, hκ, he⟩ := rootCurve_exchange_of_geometry S hcharts hcomm hunique a b c hsum
  exact ⟨κ, hκ, fun s q j hj =>
    ⟨rootPairTransport_mem S rho hr b c κ s q j hj,
      rootCoefficient_transport_of_exchange S rho hr a b c κ he s j⟩⟩

/-- In the absent-sum branch, the transported operator is the original
coefficient itself, which lies in the truncated algebra whenever j < q. -/
theorem rootCoefficient_transport_no_sum_of_geometry (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (a b : S.roots.Root)
    (hne : a ≠ b) (hop : b ≠ S.roots.neg a) (hsum : ¬ ∃ c, RootSum S a b c)
    (s : k) (q j : ℕ) (hj : j < q) :
    rootCoefficient S rho hr b j ∈ coefficientAlgebra S rho hr q ∧
      (rho.action ((rootCurve S a).onPoints (kPlusPoint s))).val *
          rootCoefficient S rho hr b j =
        rootCoefficient S rho hr b j *
          (rho.action ((rootCurve S a).onPoints (kPlusPoint s))).val := by
  refine ⟨rootCoefficient_mem S rho hr q b j hj, ?_⟩
  have ht := curveCoefficient_intertwine rho hr (rootCurve S b) (rootCurve S b)
    (rho.action ((rootCurve S a).onPoints (kPlusPoint s))).val 1 (fun t => ?_) j
  · simpa only [one_pow, one_smul, rootCoefficient] using ht
  simpa only [one_mul, map_mul, Units.val_mul] using congrArg (fun g => (rho.action g).val)
    (rootCurve_commute_of_geometry S hcharts hcomm hunique a b hne hop hsum s t).eq

/-- Every distinct nonopposite root point transports every coefficient below q
to an operator of the actual coefficient algebra. -/
theorem rootCoefficient_transport_of_geometry (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (a b : S.roots.Root)
    (hne : a ≠ b) (hop : b ≠ S.roots.neg a) (s : k) (q j : ℕ) (hj : j < q) :
    ∃ L ∈ coefficientAlgebra S rho hr q,
      (rho.action ((rootCurve S a).onPoints (kPlusPoint s))).val * rootCoefficient S rho hr b j =
        L * (rho.action ((rootCurve S a).onPoints (kPlusPoint s))).val :=
  rootCoefficient_transport_of_parameterRelations S
    (rootPairParameterRelations_of_geometry S hcharts hcomm hunique) rho hr
    a b hne hop s q j hj

/-- The full coefficient algebra is generated by coefficients below q on the
eight signed simple roots, for every natural truncation q. -/
theorem coefficientAlgebra_eq_simpleCoefficientAlgebra_of_geometry
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho) (q : ℕ) :
    coefficientAlgebra S rho hr q = simpleCoefficientAlgebra S rho hr q :=
  coefficientAlgebra_eq_simpleCoefficientAlgebra_of_parameterRelations S
    (rootPairParameterRelations_of_geometry S hcharts hcomm hunique) rho hr q

end GeometryAssembly

end
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
