module

public import Theory.AlgebraicGroup.Instance.Additive
public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.LayerCoordinateEquivalence

/-!
# Algebraic models for relative-root layer quotients

This module realizes every positive adjacent quotient in a
`ParabolicRelativeRootSetup` as the additive algebraic group on the affine
space of its exact-height root coordinates. The model structure is kept here,
below the unresolved parabolic structure theorems, so consumers do not need a
placeholder-backed import.

The essential input is the exact coordinate equivalence from
`LayerCoordinateEquivalence`: filtered Chevalley collection proves that the
exact-height root coordinates are independent, while root generation proves
that they exhaust the adjacent quotient. Transporting coordinatewise addition
across the standard point equivalence equips the affine space with its algebraic
group structure. The quotient equivalence and its single-root formula then
supply the point isomorphism and root-coordinate field of the model.

This is the direct-product description of a positive relative-root layer used
in the proof of GLS3, Theorem 1.13.5.
-/

universe u

set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- An algebraic-group realization of an adjacent positive relative-root layer
quotient in its exact-height affine coordinates. -/
public structure RelativeRootLayerQuotientModel
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) (i : ℕ)
    (hle : S.layer (i + 1) ≤ S.layer i)
    (hnormal : ((S.layer (i + 1)).subgroupOf (S.layer i)).Normal) where
  quotientVariety : Variety k
  [quotientAlgebraicGroup : AlgebraicGroup quotientVariety]
  quotientPointIso :
    S.layer i ⧸ (S.layer (i + 1)).subgroupOf (S.layer i) ≃*
      Variety.Point quotientVariety
  [coordinateAlgebraicGroup :
    AlgebraicGroup (affineSpaceVariety k (S.layerRootIndex i))]
  coordinatePointIso :
    Variety.Point (affineSpaceVariety k (S.layerRootIndex i)) ≃*
      Multiplicative (S.layerRootIndex i → k)
  algebraicCoordinateIso : AlgebraicGroup.Iso quotientVariety
      (affineSpaceVariety k (S.layerRootIndex i))
  rootElement : S.layerRootIndex i → k → S.layer i
  rootElement_value : ∀ (alpha : S.layerRootIndex i) t,
    (rootElement alpha t : Variety.Point K) = S.C.x alpha.1 t
  rootElement_coordinate : ∀ (alpha : S.layerRootIndex i) t,
    coordinatePointIso
        (algebraicCoordinateIso.hom.onPoints
          (quotientPointIso
            (QuotientGroup.mk'
              ((S.layer (i + 1)).subgroupOf (S.layer i))
              (rootElement alpha t)))) =
      Multiplicative.ofAdd
        (@Pi.single _ (fun _ => k) _ (Classical.decEq _) alpha t)

private noncomputable def affineSpaceAdditivePointEquiv
    (sigma : Type u) [Finite sigma] :
    Variety.Point (affineSpaceVariety k sigma) ≃ Multiplicative (sigma → k) where
  toFun := fun x ↦ x.val
  invFun := fun x ↦ affineSpacePoint x.toAdd
  left_inv := by
    intro x
    apply Variety.Point.ext
    rfl
  right_inv := by
    intro x
    rfl

@[instance_reducible]
private noncomputable def affineSpaceAdditiveAlgebraicGroup
    (sigma : Type u) [Finite sigma] :
    AlgebraicGroup (affineSpaceVariety k sigma) := by
  let e := affineSpaceAdditivePointEquiv (k := k) sigma
  let hGroup : Group (Variety.Point (affineSpaceVariety k sigma)) := e.group
  letI : Group (Variety.Point (affineSpaceVariety k sigma)) := hGroup
  exact
    { toGroup := hGroup
      mulPolynomial := fun i ↦
        MvPolynomial.X (Sum.inl i) + MvPolynomial.X (Sum.inr i)
      invPolynomial := fun i ↦ -MvPolynomial.X i
      mul_regular := by
        intro i x y
        change (e.symm (e x * e y)).val i =
          evalPolynomial (Sum.elim x.val y.val)
            (MvPolynomial.X (Sum.inl i) + MvPolynomial.X (Sum.inr i))
        simp only [evalPolynomial, MvPolynomial.eval₂_add, MvPolynomial.eval₂_X]
        have hz : ∀ z : Multiplicative (sigma → k),
            (e.symm z).val i = z.toAdd i := by
          intro z
          rfl
        rw [hz]
        rfl
      inv_regular := by
        intro i x
        change (e.symm (e x)⁻¹).val i =
          evalPolynomial x.val (-MvPolynomial.X i)
        simp only [evalPolynomial, MvPolynomial.eval₂_neg, MvPolynomial.eval₂_X]
        have hz : ∀ z : Multiplicative (sigma → k),
            (e.symm z).val i = z.toAdd i := by
          intro z
          rfl
        rw [hz]
        rfl }

private noncomputable def affineSpaceAdditivePointMulEquiv
    (sigma : Type u) [Finite sigma] :
    letI := affineSpaceAdditiveAlgebraicGroup (k := k) sigma
    Variety.Point (affineSpaceVariety k sigma) ≃* Multiplicative (sigma → k) := by
  letI := affineSpaceAdditiveAlgebraicGroup (k := k) sigma
  exact Equiv.mulEquiv (affineSpaceAdditivePointEquiv (k := k) sigma)

/-- Every positive adjacent relative-root layer quotient has its canonical
exact-height affine coordinate model. The result accepts any proofs of layer
inclusion and normality, so it can fill models whose types already contain
those witnesses. -/
public theorem parabolicRelativeRootLayer_quotientModel_nonempty
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i)
    (hle : S.layer (i + 1) ≤ S.layer i)
    (hnormal : ((S.layer (i + 1)).subgroupOf (S.layer i)).Normal) :
    Nonempty (RelativeRootLayerQuotientModel S i hle hnormal) := by
  letI := hnormal
  let coordinateEquiv :=
    parabolicRelativeRootLayer_quotientCoordinateEquiv S i hi
  let coordinateAG := affineSpaceAdditiveAlgebraicGroup
    (k := k) (S.layerRootIndex i)
  letI : AlgebraicGroup (affineSpaceVariety k (S.layerRootIndex i)) := coordinateAG
  let pointCoordinates := affineSpaceAdditivePointMulEquiv
    (k := k) (S.layerRootIndex i)
  let quotientPointIso :
      S.layer i ⧸ (S.layer (i + 1)).subgroupOf (S.layer i) ≃*
        Variety.Point (affineSpaceVariety k (S.layerRootIndex i)) :=
    coordinateEquiv.trans pointCoordinates.symm
  refine ⟨
    { quotientVariety := affineSpaceVariety k (S.layerRootIndex i)
      quotientAlgebraicGroup := coordinateAG
      quotientPointIso := quotientPointIso
      coordinateAlgebraicGroup := coordinateAG
      coordinatePointIso := pointCoordinates
      algebraicCoordinateIso := AlgebraicGroup.Iso.id _
      rootElement := S.layerRootElement i
      rootElement_value := S.layerRootElement_value i
      rootElement_coordinate := ?_ }⟩
  intro alpha t
  change pointCoordinates
      (pointCoordinates.symm
        (coordinateEquiv
          (QuotientGroup.mk'
            ((S.layer (i + 1)).subgroupOf (S.layer i))
            (S.layerRootElement i alpha t)))) =
    Multiplicative.ofAdd
      (@Pi.single _ (fun _ : S.layerRootIndex i => k) _
        (Classical.decEq _) alpha t)
  rw [pointCoordinates.apply_symm_apply,
    parabolicRelativeRootLayer_quotientCoordinateEquiv_root]

end Theory.AlgebraicGroup
