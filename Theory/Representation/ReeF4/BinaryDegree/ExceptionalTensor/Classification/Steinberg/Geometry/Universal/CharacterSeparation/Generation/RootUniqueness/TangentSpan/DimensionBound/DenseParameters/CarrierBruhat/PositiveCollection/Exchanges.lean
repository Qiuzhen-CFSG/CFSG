module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.RootUniqueness.TangentSpan.DimensionBound.DenseParameters.CarrierBruhat.PositiveCollection.MixedLength
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.RootUniqueness.TangentSpan.DimensionBound.DenseParameters.CarrierBruhat.PositiveCollection.EqualGeometry
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.MatrixExchanges.EqualLength.Exponential
public import Theory.GroupTheory.FilteredCollection

/-!
# Height-filtered exchanges in the literal F4 carrier

The absent-sum, equal-length and mixed-length matrix calculations exhaust
pairs of positive roots. Lift each correction root to the positive subtype,
then reflect the matrix identity through the injective carrier inclusion.
The resulting word has height strictly above both inputs.

Source: GLS3 1.12.1(b), `refs/KGroup/GLS3/Chapter1.tex`. The lifting argument
adapts `SplitCoordinates.MatrixExchanges` without importing its finite carrier.
-/

public section
noncomputable section
namespace Theory.AlgebraicGroup.F4Chevalley.DenseParameters.CarrierBruhat
open ReeF4 StandardRootSystem FilteredCollection CollectionMatrices
local instance positiveExchangeRootNeg : InvolutiveNeg Root := typeF4RootPairing.indexNeg

private theorem matrixExchange_equal {K : Type*} [CommRing K] (r s : Root)
    (hr : typeF4RootPairing_base.IsPos r) (hs : typeF4RootPairing_base.IsPos s)
    (hlen : IsLongRoot r ↔ IsLongRoot s)
    (hsum : typeF4RootPairing.root r + typeF4RootPairing.root s ∈
      Set.range typeF4RootPairing.root) (a b : K) : MatrixExchange r s a b := by
  obtain ⟨t, ht⟩ := hsum
  obtain ⟨ε, _, hn⟩ := SignedBrackets.positive_operator_bracket_signed r s t hr hs ht
  let n : ℤ := ε * (typeF4RootPairing.chainBotCoeff r s + 1 : ℤ)
  obtain ⟨hrt, hst⟩ := EqualLength.integralOperators_commute_with_sum r s t hr hs hlen ht
  refine ⟨[(t, (n : K) * a * b)], ?_, ?_⟩
  · intro z hz
    obtain rfl := List.mem_singleton.mp hz
    exact positiveCone_of_add ht
  · simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      using ReeF4.Parabolics.RadicalCoordinates.EqualLength.rootCurve_exchange_of_central_integral_bracket
        r s t n hn hrt hst a b

private theorem positive_root_sum_ne_zero (r s : PositiveRoot) :
    typeF4RootPairing.root r.val + typeF4RootPairing.root s.val ≠ 0 := by
  intro h
  have he : s.val = -r.val := by
    apply typeF4RootPairing.root.injective
    simpa only [RootPairing.indexNeg_neg, typeF4RootPairing.root_reflectionPerm,
      typeF4RootPairing.reflection_apply_self] using eq_neg_of_add_eq_zero_right h
  have hs := s.property
  rw [he] at hs
  exact (RootPairing.Base.IsPos.neg_iff_not _ _).mp hs r.property

variable {k : Type*} [Field k] [IsAlgClosed k]

private def carrierMatrix : Variety.Point (Carrier (k := k)) →* (Matrix BasisIndex BasisIndex k)ˣ :=
  matrixAmbientEquiv.symm.toMonoidHom.comp (ambientClosedCarrier (k := k)).inclusion.onPoints

private theorem carrierMatrix_injective : Function.Injective (carrierMatrix (k := k)) :=
  matrixAmbientEquiv.symm.injective.comp (ambientClosedCarrier (k := k)).inclusion_injective

@[simp] private theorem carrierMatrix_root (r : Root) (t : k) :
    carrierMatrix (rootElement r t) = rootCurve r t := by
  apply matrixAmbientEquiv.injective
  change matrixAmbientEquiv (matrixAmbientEquiv.symm _) = _
  rw [MulEquiv.apply_symm_apply]
  exact rootElement_inclusion r t

private theorem exchange_of_matrix (r s : PositiveRoot) (a b : k)
    (h : MatrixExchange r.val s.val a b) :
    ∃ correction : List (PositiveRoot × k),
      (∀ z ∈ correction,
        max (rootDegree r.val) (rootDegree s.val) < rootDegree z.1.val) ∧
      rootElement r.val a * rootElement s.val b =
        rootElement s.val b * rootElement r.val a *
          wordProduct (fun q : PositiveRoot => rootElement q.val) correction := by
  obtain ⟨c, hc, he⟩ := h
  let lift : {z // z ∈ c} → PositiveRoot × k := fun z =>
    (⟨z.val.1, (positiveCone_degree r s (hc z.val z.property)).1⟩, z.val.2)
  refine ⟨c.attach.map lift, ?_, ?_⟩
  · intro z hz
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz
    exact (positiveCone_degree r s (hc w.val w.property)).2
  · apply carrierMatrix_injective
    simp only [map_mul, carrierMatrix_root]
    apply Units.ext
    change (rootCurve r.val a).val * (rootCurve s.val b).val = _
    rw [he]
    congr 1
    let ρ : Variety.Point (Carrier (k := k)) →* Matrix BasisIndex BasisIndex k :=
      (Units.coeHom (Matrix BasisIndex BasisIndex k)).comp carrierMatrix
    change (c.map (fun z => (rootCurve z.1 z.2).val)).prod =
      ρ (wordProduct (fun q : PositiveRoot => rootElement q.val) (c.attach.map lift))
    have hρ (q : Root) (t : k) : ρ (rootElement q t) = (rootCurve q t).val := by
      change (carrierMatrix (rootElement q t)).val = _
      rw [carrierMatrix_root]
    simp only [wordProduct, map_list_prod, List.map_map, Function.comp_def, hρ]
    change (c.map (fun z => (rootCurve z.1 z.2).val)).prod =
      (c.attach.map (fun z => (rootCurve z.val.1 z.val.2).val)).prod
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (fun l => (l.map (fun z : Root × k =>
        (rootCurve z.1 z.2).val)).prod) (List.attach_map_subtype_val c)).symm

/-- Every pair of distinct positive root elements exchanges with corrections
strictly above both heights, over any characteristic-two algebraically closed field. -/
theorem positiveRoot_exchange [CharP k 2] (r s : PositiveRoot) (a b : k) (hrs : r ≠ s) :
    ∃ correction : List (PositiveRoot × k),
      (∀ z ∈ correction,
        max (rootDegree r.val) (rootDegree s.val) < rootDegree z.1.val) ∧
      rootElement r.val a * rootElement s.val b =
        rootElement s.val b * rootElement r.val a *
          wordProduct (fun q : PositiveRoot => rootElement q.val) correction := by
  classical
  by_cases hsum : typeF4RootPairing.root r.val + typeF4RootPairing.root s.val ∈
      Set.range typeF4RootPairing.root
  · apply exchange_of_matrix r s a b
    by_cases hlen : IsLongRoot r.val ↔ IsLongRoot s.val
    · exact matrixExchange_equal r.val s.val r.property s.property hlen hsum a b
    · exact matrixExchange_of_mixed_length_sum r.val s.val r.property s.property
        (fun h => hrs (Subtype.ext h)) hlen hsum a b
  · refine ⟨[], by simp, ?_⟩
    simp only [wordProduct, List.map_nil, List.prod_nil, mul_one]
    apply carrierMatrix_injective
    simp only [map_mul, carrierMatrix_root]
    exact (rootCurve_commute_of_integralOperators r.val s.val
      (integralOperators_commute_of_no_sum r.val s.val r.property s.property
        (positive_root_sum_ne_zero r s) hsum) a b).eq

end Theory.AlgebraicGroup.F4Chevalley.DenseParameters.CarrierBruhat
