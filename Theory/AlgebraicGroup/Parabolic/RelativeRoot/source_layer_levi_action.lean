module

public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.source_fiber_supported_coordinate_equiv

/-!
# Source Levi action on a relative-root fiber

For a representation source, the actual Levi normalizes every adjacent source
relative-root layer.  The maintained quotient conjugation action is rational
in exact-layer coordinates, and its fiber-supported coordinate subspace is
stable.  This module restricts that action to one relative-root fiber and
proves both its quotient-class formula and its compatibility with the rational
coordinate representation.

The action convention is left conjugation, `l * x * l⁻¹`, matching the
repaired `RelativeRootFiberModule` generator contract.  We also record the
inverse-conjugation formula at the inverse action index, which supports source
calculations naturally written as `l⁻¹ * x * l`.  The construction uses only
the source Chevalley data, Levi alignment, and the maintained relative-root
series action API; it does not depend on either numbered relative-root theorem.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

private noncomputable def sourceFiberConjugationValue
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (l : Variety.Point S.L.carrierVariety)
    (q : relativeRootFiberQuotientSubgroup S) :
    relativeRootFiberQuotientSubgroup S := by
  let v : RelativeRootSourceExactIndex S → k :=
    (Multiplicative.toAdd (relativeRootFiberSupportedCoordinateEquiv S q) :
      sourceRelativeRootFiberCoordinateSubmodule S)
  let f := (S.sourceLayerCoordinateRationalRepresentation.action l : Module.End k
    (RelativeRootSourceExactIndex S → k))
  have hm : f v ∈ sourceRelativeRootFiberCoordinateSubmodule S := by
    have hm' : f v ∈ Submodule.map f
        (sourceRelativeRootFiberCoordinateSubmodule S) :=
      Submodule.mem_map_of_mem
        (Multiplicative.toAdd (relativeRootFiberSupportedCoordinateEquiv S q)).property
    rw [sourceRelativeRootFiberCoordinateSubmodule_stable S l] at hm'
    exact hm'
  exact (relativeRootFiberSupportedCoordinateEquiv S).symm
    (Multiplicative.ofAdd ⟨f v, hm⟩)

private theorem sourceFiberConjugationValue_coe
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (l : Variety.Point S.L.carrierVariety)
    (q : relativeRootFiberQuotientSubgroup S) :
    (sourceFiberConjugationValue S l q : relativeRootLayerQuotient S) =
      (S.sourceLayerCarrierQuotientConjugationAction).smul l
        (q : relativeRootLayerQuotient S) := by
  apply (relativeRootLayerQuotient_coordinateEquiv S).injective
  apply Multiplicative.toAdd.injective
  rw [← relativeRootFiberSupportedCoordinateEquiv_coe S
    (sourceFiberConjugationValue S l q)]
  unfold sourceFiberConjugationValue
  rw [MulEquiv.apply_symm_apply]
  change ((S.sourceLayerCoordinateRationalRepresentation.action l : Module.End k
      (RelativeRootSourceExactIndex S → k))
    (((Multiplicative.toAdd (relativeRootFiberSupportedCoordinateEquiv S q) :
      sourceRelativeRootFiberCoordinateSubmodule S) :
        RelativeRootSourceExactIndex S → k))) = _
  rw [relativeRootFiberSupportedCoordinateEquiv_coe]
  rw [show S.sourceLayerCoordinateRationalRepresentation.action l =
    S.sourceLayerCarrierCoordinateLinearAction l from rfl]
  rw [S.sourceLayerCarrierCoordinateLinearAction_apply]
  unfold sourceCoordinateActionValue
  change Multiplicative.toAdd
      ((S.sourceLayerCarrierCoordinateConjugationAction).smul l
        (relativeRootLayerQuotient_coordinateEquiv S
          (q : relativeRootLayerQuotient S))) = _
  rw [S.sourceLayerCarrierCoordinateConjugationAction_apply]
  simp

/-- Source-Levi conjugation restricted to the chosen relative-root fiber. -/
public noncomputable def RelativeRootRepresentationSource.sourceFiberConjugationHom
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    Variety.Point S.L.carrierVariety →* MulAut (relativeRootFiberQuotientSubgroup S) where
  toFun l :=
    { toFun := sourceFiberConjugationValue S l
      invFun := sourceFiberConjugationValue S l⁻¹
      left_inv := by
        intro q
        apply Subtype.ext
        rw [sourceFiberConjugationValue_coe, sourceFiberConjugationValue_coe]
        let _ := S.sourceLayerCarrierQuotientConjugationAction
        exact inv_smul_smul l (q : relativeRootLayerQuotient S)
      right_inv := by
        intro q
        apply Subtype.ext
        rw [sourceFiberConjugationValue_coe, sourceFiberConjugationValue_coe]
        let _ := S.sourceLayerCarrierQuotientConjugationAction
        exact smul_inv_smul l (q : relativeRootLayerQuotient S)
      map_mul' := by
        intro q r
        apply Subtype.ext
        rw [sourceFiberConjugationValue_coe]
        change (S.sourceLayerCarrierQuotientConjugationAction).smul l
          ((q : relativeRootLayerQuotient S) * r) = _
        change _ = (sourceFiberConjugationValue S l q : relativeRootLayerQuotient S) *
          (sourceFiberConjugationValue S l r : relativeRootLayerQuotient S)
        rw [sourceFiberConjugationValue_coe, sourceFiberConjugationValue_coe]
        exact (S.sourceLayerCarrierQuotientConjugationAction).smul_mul l q r
      }
  map_one' := by
    ext q
    change (sourceFiberConjugationValue S 1 q : relativeRootLayerQuotient S) = _
    rw [sourceFiberConjugationValue_coe]
    change (S.sourceLayerCarrierQuotientConjugationAction).smul 1
      (q : relativeRootLayerQuotient S) = (q : relativeRootLayerQuotient S)
    exact (S.sourceLayerCarrierQuotientConjugationAction).one_smul q
  map_mul' := by
    intro l m
    ext q
    change (sourceFiberConjugationValue S (l * m) q : relativeRootLayerQuotient S) =
      (sourceFiberConjugationValue S l (sourceFiberConjugationValue S m q) :
        relativeRootLayerQuotient S)
    rw [sourceFiberConjugationValue_coe, sourceFiberConjugationValue_coe,
      sourceFiberConjugationValue_coe]
    exact (S.sourceLayerCarrierQuotientConjugationAction).mul_smul l m q

/-- The restricted fiber action is the ambient exact-layer quotient action. -/
public theorem RelativeRootRepresentationSource.sourceFiberConjugationHom_coe
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (l : Variety.Point S.L.carrierVariety)
    (q : relativeRootFiberQuotientSubgroup S) :
    (S.sourceFiberConjugationHom l q : relativeRootLayerQuotient S) =
      (S.sourceLayerCarrierQuotientConjugationAction).smul l
        (q : relativeRootLayerQuotient S) := by
  exact sourceFiberConjugationValue_coe S l q

/-- On a fiber generator, the restricted action is represented by left
conjugation of its Chevalley root element. -/
public theorem RelativeRootRepresentationSource.sourceFiberConjugationHom_generator_value
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (l : Variety.Point S.L.carrierVariety)
    (z : {gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root} × k) :
    ∃ y : sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
        S.coeff S.J S.height,
      (y : Variety.Point K) = S.L.includePoint l * S.C.x z.1.1 z.2 *
          (S.L.includePoint l)⁻¹ ∧
        (S.sourceFiberConjugationHom l
            (relativeRootFiberQuotientGenerator S z) :
              relativeRootLayerQuotient S) = QuotientGroup.mk' _ y := by
  let x := relativeRootLayerElement S z.1.1 z.1.2 z.2
  let y : sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
      S.coeff S.J S.height :=
    ⟨S.L.includePoint l * x.1 * (S.L.includePoint l)⁻¹, by
      have hnorm := S.levi_le_sourceRelativeRootLayer_normalizer S.height
        (S.L.pointEquiv l).2
      rw [Subgroup.mem_normalizer_iff] at hnorm
      exact (hnorm x.1).mp x.2⟩
  refine ⟨y, ?_, ?_⟩
  · change S.L.includePoint l * (x : Variety.Point K) *
      (S.L.includePoint l)⁻¹ = _
    rw [relativeRootLayerElement_coe]
  · rw [S.sourceFiberConjugationHom_coe,
      relativeRootFiberQuotientGenerator_coe,
      S.sourceLayerCarrierQuotientConjugationAction_mk]

/-- The inverse-indexed action gives the compatibility form of the generator
contract for inverse-conjugation source calculations. -/
public theorem RelativeRootRepresentationSource.sourceFiberConjugationHom_inv_generator_value
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (l : Variety.Point S.L.carrierVariety)
    (z : {gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root} × k) :
    ∃ y : sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
        S.coeff S.J S.height,
      (y : Variety.Point K) = (S.L.includePoint l)⁻¹ * S.C.x z.1.1 z.2 *
          S.L.includePoint l ∧
        (S.sourceFiberConjugationHom l⁻¹
            (relativeRootFiberQuotientGenerator S z) :
              relativeRootLayerQuotient S) = QuotientGroup.mk' _ y := by
  rcases S.sourceFiberConjugationHom_generator_value l⁻¹ z with
    ⟨y, hy, hqy⟩
  refine ⟨y, ?_, hqy⟩
  have hinv : S.L.includePoint l⁻¹ = (S.L.includePoint l)⁻¹ := by rfl
  rw [hinv, inv_inv] at hy
  exact hy

/-- The supported-coordinate equivalence intertwines the restricted action
with the maintained rational coordinate representation. -/
public theorem RelativeRootRepresentationSource.sourceFiberConjugationHom_coordinate
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (l : Variety.Point S.L.carrierVariety)
    (q : relativeRootFiberQuotientSubgroup S) :
    (((Multiplicative.toAdd
        (relativeRootFiberSupportedCoordinateEquiv S
          (S.sourceFiberConjugationHom l q)) :
            sourceRelativeRootFiberCoordinateSubmodule S) :
              RelativeRootSourceExactIndex S → k)) =
      (S.sourceLayerCoordinateRationalRepresentation.action l).1
        (((Multiplicative.toAdd
          (relativeRootFiberSupportedCoordinateEquiv S q) :
            sourceRelativeRootFiberCoordinateSubmodule S) :
              RelativeRootSourceExactIndex S → k)) := by
  rw [relativeRootFiberSupportedCoordinateEquiv_coe,
    S.sourceFiberConjugationHom_coe,
    show S.sourceLayerCoordinateRationalRepresentation.action l =
      S.sourceLayerCarrierCoordinateLinearAction l from rfl,
    S.sourceLayerCarrierCoordinateLinearAction_apply]
  unfold sourceCoordinateActionValue
  rw [S.sourceLayerCarrierCoordinateConjugationAction_apply]
  have hq : (relativeRootLayerQuotient_coordinateEquiv S).symm
      (Multiplicative.ofAdd
        (((Multiplicative.toAdd
          (relativeRootFiberSupportedCoordinateEquiv S q) :
            sourceRelativeRootFiberCoordinateSubmodule S) :
              RelativeRootSourceExactIndex S → k))) =
        (q : relativeRootLayerQuotient S) := by
    apply (relativeRootLayerQuotient_coordinateEquiv S).injective
    rw [(relativeRootLayerQuotient_coordinateEquiv S).apply_symm_apply]
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd]
    exact relativeRootFiberSupportedCoordinateEquiv_coe S q
  rw [hq]

end Theory.AlgebraicGroup
