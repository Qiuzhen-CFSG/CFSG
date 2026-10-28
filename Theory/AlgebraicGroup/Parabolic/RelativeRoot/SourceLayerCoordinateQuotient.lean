module

public import Theory.AlgebraicGroup.Bor1.GeometricQuotientDescent
public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.RepresentationSourceCoordinateEquivalence
public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.SourceLayerClosedInterface
public import Theory.AlgebraicGroup.RootSubgroups.Tangent
public import Theory.AlgebraicGroup.Representations.Algebraic.WeightSpaces
public import Theory.AlgebraicGroup.Dimension.Group

/-!
# The regular coordinate quotient of a source relative-root layer

For a `RelativeRootRepresentationSource`, this module equips the affine space
indexed by the roots of exact source height with its additive algebraic-group
structure and constructs the regular quotient morphism from the closed source
layer.  Its point map is the established Chevalley coordinate equivalence after
the abstract quotient projection, its kernel is the next source layer, and an
exact-height Chevalley element has the corresponding `Pi.single` coordinate.

Regularity comes from the source Chevalley parametrization: the coordinate root
curves are the restrictions of `S.chevalleyParametrization`, and their point
values are identified using `S.chevalleyParametrization_value`.  Ordered products
of these curves give a surjective parametrization of the source layer.  Their
identity tangents span the layer, so the induced coordinate map to the geometric
quotient has surjective differential.  This proves surjectivity on coordinate
rings and upgrades the pointwise coordinate equivalence to an algebraic-group
isomorphism.  The construction then composes the geometric quotient projection
with that isomorphism.

This is a source-layer construction below the representation layer.  The
mathematical input is the Chevalley collection and exact-layer coordinate
independence already recorded by `RepresentationSourceCoordinateEquivalence`,
together with the affine geometric quotient descent API.
-/

set_option linter.style.haveILetI false

universe u

namespace Theory.AlgebraicGroup

open scoped Cardinal

variable {k : Type u} [Field k] [IsAlgClosed k]

public abbrev RelativeRootSourceExactIndex
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :=
  {alpha : S.D.Root //
    RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J alpha = S.height}

public abbrev RelativeRootSourceCoordinateSpace
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :=
  affineSpaceVariety k (RelativeRootSourceExactIndex S)

private noncomputable def affineAdditivePointEquiv
    (sigma : Type u) [Finite sigma] :
    Variety.Point (affineSpaceVariety k sigma) ≃ Multiplicative (sigma → k) where
  toFun := fun x => x.val
  invFun := fun x => affineSpacePoint x.toAdd
  left_inv := by
    intro x
    apply Variety.Point.ext
    rfl
  right_inv := by intro x; rfl

@[instance_reducible]
private noncomputable def affineAdditiveAlgebraicGroup
    (sigma : Type u) [Finite sigma] :
    AlgebraicGroup (affineSpaceVariety k sigma) := by
  let e := affineAdditivePointEquiv (k := k) sigma
  let hGroup : Group (Variety.Point (affineSpaceVariety k sigma)) := e.group
  letI : Group (Variety.Point (affineSpaceVariety k sigma)) := hGroup
  exact
    { toGroup := hGroup
      mulPolynomial := fun i =>
        MvPolynomial.X (Sum.inl i) + MvPolynomial.X (Sum.inr i)
      invPolynomial := fun i => -MvPolynomial.X i
      mul_regular := by
        intro i x y
        change (e.symm (e x * e y)).val i =
          evalPolynomial (Sum.elim x.val y.val)
            (MvPolynomial.X (Sum.inl i) + MvPolynomial.X (Sum.inr i))
        simp only [evalPolynomial, MvPolynomial.eval₂_add, MvPolynomial.eval₂_X]
        rfl
      inv_regular := by
        intro i x
        change (e.symm (e x)⁻¹).val i =
          evalPolynomial x.val (-MvPolynomial.X i)
        simp only [evalPolynomial, MvPolynomial.eval₂_neg, MvPolynomial.eval₂_X]
        rfl }

@[instance_reducible]
public noncomputable def RelativeRootRepresentationSource.coordinateAlgebraicGroup
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    AlgebraicGroup (RelativeRootSourceCoordinateSpace S) :=
  affineAdditiveAlgebraicGroup (k := k) (RelativeRootSourceExactIndex S)

public noncomputable def RelativeRootRepresentationSource.coordinatePointEquiv
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    letI := S.coordinateAlgebraicGroup
    Variety.Point (RelativeRootSourceCoordinateSpace S) ≃*
      Multiplicative (RelativeRootSourceExactIndex S → k) := by
  letI := S.coordinateAlgebraicGroup
  exact Equiv.mulEquiv
    (affineAdditivePointEquiv (k := k) (RelativeRootSourceExactIndex S))

omit [IsAlgClosed k] in
/-- The coordinate-space point equivalence reads off the underlying affine
coordinate function. -/
public theorem RelativeRootRepresentationSource.coordinatePointEquiv_apply
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (z : Variety.Point (RelativeRootSourceCoordinateSpace S)) :
    letI := S.coordinateAlgebraicGroup
    S.coordinatePointEquiv z = Multiplicative.ofAdd z.val := by
  rfl

private noncomputable def affineCoordinateMorphism
    (sigma : Type u) [Finite sigma] (i : sigma) :
    Variety.Morphism (affineSpaceVariety k sigma) (KPlus k) where
  toFun z := kPlusPoint (z.val i)
  regular := by
    intro j
    refine ⟨MvPolynomial.X i, ?_⟩
    intro z
    rw [show j = PUnit.unit by rfl]
    change z.val i = evalPolynomial z.val (MvPolynomial.X i)
    rw [evalPolynomial_X]

@[expose]
public noncomputable def sourceChevalleyRootCurve
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (alpha : S.D.Root) :
    AlgebraicGroup.Morphism (KPlus k) K :=
  (S.D.rootSubgroup alpha).inclusion.comp (S.chevalleyParametrization alpha).hom

omit [IsAlgClosed k] in
public theorem sourceChevalleyRootCurve_apply
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (alpha : S.D.Root) (t : k) :
    (sourceChevalleyRootCurve S alpha).onPoints (kPlusPoint t) = S.C.x alpha t := by
  exact S.chevalleyParametrization_value alpha t

private noncomputable def varietyMorphismListProduct
    {X K : Variety k} [AlgebraicGroup K] :
    List (Variety.Morphism X K) → Variety.Morphism X K
  | [] => Variety.Morphism.const X K 1
  | f :: fs => (AlgebraicGroup.mulMorphism K).comp
      (f.pair (varietyMorphismListProduct fs))

omit [IsAlgClosed k] in
private theorem varietyMorphismListProduct_apply
    {X K : Variety k} [AlgebraicGroup K]
    (fs : List (Variety.Morphism X K)) (z : Variety.Point X) :
    (varietyMorphismListProduct fs).toFun z =
      (fs.map fun f => f.toFun z).prod := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      change f.toFun z * (varietyMorphismListProduct fs).toFun z = _
      rw [ih]
      rfl

private noncomputable def sourceLayerParametrization
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (n : Nat) :
    Variety.Morphism
      (affineSpaceVariety k (RelativeRootSourceAtLeastIndex S n)) K :=
  varietyMorphismListProduct
    ((sourceRelativeRootAtLeastList S n).map fun alpha =>
      (sourceChevalleyRootCurve S alpha.1).toVariety.comp
        (affineCoordinateMorphism (RelativeRootSourceAtLeastIndex S n) alpha))

omit [IsAlgClosed k] in
private theorem sourceLayerParametrization_apply
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (n : Nat)
    (z : Variety.Point
      (affineSpaceVariety k (RelativeRootSourceAtLeastIndex S n))) :
    (sourceLayerParametrization S n).toFun z =
      ((sourceRelativeRootAtLeastList S n).map fun alpha =>
        S.C.x alpha.1 (z.val alpha)).prod := by
  rw [sourceLayerParametrization, varietyMorphismListProduct_apply]
  simp only [List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro alpha halpha
  exact sourceChevalleyRootCurve_apply S alpha.1 (z.val alpha)

omit [IsAlgClosed k] in
private theorem sourceChevalleyRoot_mem_layer
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (n : Nat)
    (alpha : RelativeRootSourceAtLeastIndex S n) (t : k) :
    S.C.x alpha.1 t ∈ sourceRelativeRootLayer S.D
      S.D.simple.toFinite.toFinset S.coeff S.J n := by
  rw [sourceRelativeRootLayer, RelativeRootSeries]
  apply rootSubgroup_le_RootSubgroupGenerated S.D
  simpa [relativeRootSourceHeight] using alpha.2
  change S.C.x alpha.1 t ∈ (S.D.rootSubgroup alpha.1 : Set (Variety.Point K))
  have : S.C.x alpha.1 t ∈ Set.range (S.C.x alpha.1) := ⟨t, rfl⟩
  simpa only [(S.chevalleySystem.1 alpha.1).2] using this

omit [IsAlgClosed k] in
private theorem sourceLayerParametrization_mem
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (n : Nat)
    (z : Variety.Point
      (affineSpaceVariety k (RelativeRootSourceAtLeastIndex S n))) :
    (sourceLayerParametrization S n).toFun z ∈
      sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J n := by
  rw [sourceLayerParametrization_apply]
  apply Subgroup.list_prod_mem
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨alpha, _, rfl⟩ := hx
  exact sourceChevalleyRoot_mem_layer S n alpha (z.val alpha)

private def Variety.Morphism.codRestrictClosedSubgroup
    {X K : Variety k} [AlgebraicGroup K]
    (f : Variety.Morphism X K) (H : ClosedSubgroup K)
    (hmap : ∀ x, f.toFun x ∈ H.toSubgroup) :
    Variety.Morphism X H.carrierVariety where
  toFun := fun x => H.pointEquiv.symm ⟨f.toFun x, hmap x⟩
  regular := by
    intro i
    rcases f.regular i with ⟨p, hp⟩
    refine ⟨p, fun x => ?_⟩
    change (H.pointEquiv (H.pointEquiv.symm ⟨f.toFun x, hmap x⟩)).val.val i =
      evalPolynomial x.val p
    rw [H.pointEquiv.apply_symm_apply]
    exact hp x

omit [IsAlgClosed k] in
private theorem Variety.Morphism.codRestrictClosedSubgroup_inclusion_apply
    {X K : Variety k} [AlgebraicGroup K]
    (f : Variety.Morphism X K) (H : ClosedSubgroup K)
    (hmap : ∀ x, f.toFun x ∈ H.toSubgroup) (x : Variety.Point X) :
    H.inclusion.onPoints ((f.codRestrictClosedSubgroup H hmap).toFun x) = f.toFun x := by
  change (H.pointEquiv (H.pointEquiv.symm ⟨f.toFun x, hmap x⟩)).val = f.toFun x
  rw [H.pointEquiv.apply_symm_apply]

private noncomputable def sourceLayerParametrizationToLayer
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (n : Nat) :
    Variety.Morphism
      (affineSpaceVariety k (RelativeRootSourceAtLeastIndex S n))
      (S.sourceSimpleLayerClosedSubgroup n).carrierVariety :=
  (sourceLayerParametrization S n).codRestrictClosedSubgroup
    (S.sourceSimpleLayerClosedSubgroup n)
    (sourceLayerParametrization_mem S n)

private theorem sourceLayerParametrizationToLayer_surjective
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (n : Nat) (hn : 0 < n) :
    Function.Surjective (sourceLayerParametrizationToLayer S n).toFun := by
  intro y
  obtain ⟨params, hparams⟩ := sourceRelativeRootLayer_exists_collected
    S n hn ((S.sourceSimpleLayerClosedSubgroup n).inclusion.onPoints y)
      ((S.sourceSimpleLayerClosedSubgroup n).pointEquiv y).property
  let z : Variety.Point
      (affineSpaceVariety k (RelativeRootSourceAtLeastIndex S n)) :=
    affineSpacePoint params
  refine ⟨z, (S.sourceSimpleLayerClosedSubgroup n).inclusion_injective ?_⟩
  change ((S.sourceSimpleLayerClosedSubgroup n).pointEquiv
    ((S.sourceSimpleLayerClosedSubgroup n).pointEquiv.symm
      ⟨(sourceLayerParametrization S n).toFun z, _⟩)).val =
        (S.sourceSimpleLayerClosedSubgroup n).inclusion.onPoints y
  calc
    _ = (sourceLayerParametrization S n).toFun z :=
      congrArg Subtype.val
        ((S.sourceSimpleLayerClosedSubgroup n).pointEquiv.apply_symm_apply _)
    _ = ((sourceRelativeRootAtLeastList S n).map fun alpha =>
        S.C.x alpha.1 (z.val alpha)).prod :=
      sourceLayerParametrization_apply S n z
    _ = (S.sourceSimpleLayerClosedSubgroup n).inclusion.onPoints y := hparams.symm

private theorem sourceRootSubgroup_le_layer
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (n : Nat)
    (alpha : RelativeRootSourceAtLeastIndex S n) :
    S.D.rootSubgroup alpha.1 ≤ S.sourceSimpleLayerClosedSubgroup n := by
  intro x hx
  change x ∈ sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
    S.coeff S.J n
  rw [sourceRelativeRootLayer, RelativeRootSeries]
  exact rootSubgroup_le_RootSubgroupGenerated S.D
    (by simpa [relativeRootSourceHeight] using alpha.2) hx

private theorem sourceRootTangent_mem_layerRange
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (n : Nat)
    (alpha : RelativeRootSourceAtLeastIndex S n) :
    oneParameterTangent (S.D.rootSubgroup alpha.1)
        (S.chevalleyParametrization alpha.1) ∈
      LinearMap.range (identityTangentMorphismLinearMap
        (S.sourceSimpleLayerClosedSubgroup n).inclusion) := by
  obtain ⟨Y, hY⟩ := oneParameterTangent_mem_range_inclusion
    (S.D.rootSubgroup alpha.1) (S.chevalleyParametrization alpha.1)
  let i := (S.D.rootSubgroup alpha.1).inclusion.codRestrictClosedSubgroup
    (S.sourceSimpleLayerClosedSubgroup n)
    (fun z => sourceRootSubgroup_le_layer S n alpha
      ((S.D.rootSubgroup alpha.1).pointEquiv z).property)
  refine ⟨identityTangentMorphismLinearMap i Y, ?_⟩
  rw [← hY]
  apply Derivation.ext
  intro f
  rfl

private noncomputable def sourceLayerRootTangent
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (n : Nat)
    (alpha : RelativeRootSourceAtLeastIndex S n) :
    IdentityPointDerivation (S.sourceSimpleLayerClosedSubgroup n).carrierVariety :=
  Classical.choose (sourceRootTangent_mem_layerRange S n alpha)

private theorem sourceLayerRootTangent_inclusion
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (n : Nat)
    (alpha : RelativeRootSourceAtLeastIndex S n) :
    identityTangentMorphismLinearMap
        (S.sourceSimpleLayerClosedSubgroup n).inclusion
        (sourceLayerRootTangent S n alpha) =
      oneParameterTangent (S.D.rootSubgroup alpha.1)
        (S.chevalleyParametrization alpha.1) :=
  Classical.choose_spec (sourceRootTangent_mem_layerRange S n alpha)

private theorem sourceRootTangents_linearIndependent
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (n : Nat) :
    LinearIndependent k (fun alpha : RelativeRootSourceAtLeastIndex S n =>
      oneParameterTangent (S.D.rootSubgroup alpha.1)
        (S.chevalleyParametrization alpha.1)) := by
  let weights : RelativeRootSourceAtLeastIndex S n → TorusWeight S.T :=
    fun alpha => (S.D.rootWeight alpha.1)⁻¹
  have hweights : Function.Injective weights := by
    intro alpha beta hab
    apply Subtype.ext
    apply S.isRealization.1
    exact inv_injective hab
  let p : RelativeRootSourceAtLeastIndex S n →
      Submodule k (IdentityPointDerivation K) := fun alpha =>
    weightSpace (identityTangentRepresentation K) S.T (weights alpha)
  have hp : iSupIndep p :=
    (weightSpace_iSupIndep (identityTangentRepresentation K) S.T).comp hweights
  apply iSupIndep.linearIndependent p hp
  · intro alpha
    exact (oneParameterTangent_isWeightVector S.T (S.D.rootSubgroup alpha.1)
      (S.chevalleyParametrization alpha.1)
      (S.isRealization.2.2.1 alpha.1).2).2
  · intro alpha
    exact (oneParameterTangent_isWeightVector S.T (S.D.rootSubgroup alpha.1)
      (S.chevalleyParametrization alpha.1)
      (S.isRealization.2.2.1 alpha.1).2).1

private theorem sourceLayerRootTangents_linearIndependent
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (n : Nat) :
    LinearIndependent k (sourceLayerRootTangent S n) := by
  apply LinearIndependent.of_comp
    (identityTangentMorphismLinearMap
      (S.sourceSimpleLayerClosedSubgroup n).inclusion)
  have h := sourceRootTangents_linearIndependent S n
  convert h using 1
  funext alpha
  exact sourceLayerRootTangent_inclusion S n alpha

omit [IsAlgClosed k] in
private theorem dimension_eq_trdeg_polynomialFunction
    (V : Variety k)
    (hV : IsIrreducible (Set.univ : Set (Variety.Point V))) :
    Variety.dimension V =
      Algebra.trdeg k (Variety.PolynomialFunction V) := by
  let : IsDomain (coordinateRing V) :=
    isDomain_coordinateRing_of_isIrreducible V hV
  let : IsDomain (Variety.PolynomialFunction V) :=
    (coordinateRingAlgEquivPolynomialFunction V).toRingEquiv.isDomain_iff.mp
      inferInstance
  rw [dimension_eq_fractionRing_of_isIrreducible V hV,
    trdeg_fractionRing_eq]
  exact (coordinateRingAlgEquivPolynomialFunction V).trdeg_eq

omit [IsAlgClosed k] in
private theorem dimension_le_of_surjective_morphism
    {V W : Variety k} (f : Variety.Morphism V W)
    (hV : IsIrreducible (Set.univ : Set (Variety.Point V)))
    (hW : IsIrreducible (Set.univ : Set (Variety.Point W)))
    (hf : Function.Surjective f.toFun) :
    Variety.dimension W ≤ Variety.dimension V := by
  rw [dimension_eq_trdeg_polynomialFunction W hW,
    dimension_eq_trdeg_polynomialFunction V hV]
  apply trdeg_le_of_injective f.pullbackAlgHom
  intro p q hpq
  apply Variety.PolynomialFunction.ext
  intro y
  obtain ⟨x, rfl⟩ := hf y
  exact congrArg (fun r : Variety.PolynomialFunction V => r x) hpq

private theorem affineSpace_dimension
    (sigma : Type u) [Finite sigma] :
    Variety.dimension (affineSpaceVariety k sigma) = Cardinal.mk sigma := by
  let : Nonempty (Variety.Point (affineSpaceVariety k sigma)) :=
    ⟨affineSpacePoint (fun _ => 0)⟩
  let : IsDomain (coordinateRing (affineSpaceVariety k sigma)) :=
    (Ideal.Quotient.isDomain_iff_prime
      (I := vanishingIdeal (Set.univ : Set
        (Variety.Point (affineSpaceVariety k sigma))))).mpr (by
          rw [affineSpaceVariety_vanishingIdeal_eq_bot]
          exact Ideal.isPrime_bot)
  have hirreducible := isIrreducible_univ_of_prime_vanishingIdeal
    (affineSpaceVariety k sigma) (by
      rw [affineSpaceVariety_vanishingIdeal_eq_bot]
      exact Ideal.isPrime_bot)
  rw [dimension_eq_fractionRing_of_isIrreducible
    (affineSpaceVariety k sigma) hirreducible, trdeg_fractionRing_eq]
  change Algebra.trdeg k (MvPolynomial sigma k ⧸
    vanishingIdeal (Set.univ : Set
      (Variety.Point (affineSpaceVariety k sigma)))) = Cardinal.mk sigma
  rw [affineSpaceVariety_vanishingIdeal_eq_bot]
  calc
    Algebra.trdeg k (MvPolynomial sigma k ⧸
        (⊥ : Ideal (MvPolynomial sigma k))) =
        Algebra.trdeg k (MvPolynomial sigma k) :=
      (AlgEquiv.quotientBot k (MvPolynomial sigma k)).trdeg_eq
    _ = Cardinal.mk sigma := by
      simpa only [Cardinal.lift_id] using
        (MvPolynomial.trdeg_of_isDomain :
          Algebra.trdeg k (MvPolynomial sigma k) = Cardinal.lift.{u} #sigma)

omit [IsAlgClosed k] in
private theorem ClosedSubgroup.carrierVariety_isConnected
    {K : Variety k} [AlgebraicGroup K] (H : ClosedSubgroup K)
    (hH : _root_.IsConnected (H : Set (Variety.Point K))) :
    Variety.IsConnected H.carrierVariety := by
  let e := Variety.closedSubvarietyPointHomeomorph H.isZariskiClosed
  let : ConnectedSpace {x : Variety.Point K // x ∈ (H : Set (Variety.Point K))} :=
    Subtype.connectedSpace hH
  let : ConnectedSpace (Variety.Point H.carrierVariety) :=
    e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

private theorem sourceLayer_dimension_le
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (n : Nat) (hn : 0 < n) :
    Variety.dimension (S.sourceSimpleLayerClosedSubgroup n).carrierVariety ≤
      Cardinal.mk (RelativeRootSourceAtLeastIndex S n) := by
  let H := S.sourceSimpleLayerClosedSubgroup n
  have hHconn : Variety.IsConnected H.carrierVariety :=
    H.carrierVariety_isConnected (by
      change _root_.IsConnected (H.toSubgroup : Set (Variety.Point K))
      rw [show H.toSubgroup = sourceRelativeRootLayer S.D
        S.D.simple.toFinite.toFinset S.coeff S.J n by
          exact S.sourceSimpleLayerClosedSubgroup_toSubgroup n]
      exact sourceRelativeRootLayer_simple_isConnected S n)
  have hHirr := connectedAlgebraicGroup_irreducible H.carrierVariety hHconn
  let : Nonempty (Variety.Point
      (affineSpaceVariety k (RelativeRootSourceAtLeastIndex S n))) :=
    ⟨affineSpacePoint (fun _ => 0)⟩
  have hAirr := isIrreducible_univ_of_prime_vanishingIdeal
    (affineSpaceVariety k (RelativeRootSourceAtLeastIndex S n)) (by
      rw [affineSpaceVariety_vanishingIdeal_eq_bot]
      exact Ideal.isPrime_bot)
  calc
    Variety.dimension H.carrierVariety ≤
        Variety.dimension
          (affineSpaceVariety k (RelativeRootSourceAtLeastIndex S n)) :=
      dimension_le_of_surjective_morphism
        (sourceLayerParametrizationToLayer S n) hAirr hHirr
        (sourceLayerParametrizationToLayer_surjective S n hn)
    _ = Cardinal.mk (RelativeRootSourceAtLeastIndex S n) :=
      affineSpace_dimension (RelativeRootSourceAtLeastIndex S n)

private theorem sourceLayerRootTangents_span
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (n : Nat) (hn : 0 < n) :
    Submodule.span k (Set.range (sourceLayerRootTangent S n)) = ⊤ := by
  letI := Fintype.ofFinite S.D.Root
  letI : Fintype (RelativeRootSourceAtLeastIndex S n) := Fintype.ofFinite _
  have hli := sourceLayerRootTangents_linearIndependent S n
  apply hli.span_eq_top_of_card_eq_finrank'
  apply le_antisymm
  · exact hli.fintype_card_le_finrank
  · calc
      Module.finrank k
          (IdentityPointDerivation
            (S.sourceSimpleLayerClosedSubgroup n).carrierVariety) =
          Cardinal.toNat
            (Variety.dimension
              (S.sourceSimpleLayerClosedSubgroup n).carrierVariety) :=
        Bor1.identityPointDerivation_finrank_eq_dimension _
      _ ≤ Cardinal.toNat (Cardinal.mk (RelativeRootSourceAtLeastIndex S n)) :=
        Cardinal.toNat_le_toNat (sourceLayer_dimension_le S n hn)
          (Cardinal.lt_aleph0_iff_finite.mpr inferInstance)
      _ = Fintype.card (RelativeRootSourceAtLeastIndex S n) :=
        Cardinal.mk_toNat_eq_card

private noncomputable def sourceExactRootList
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    List (RelativeRootSourceExactIndex S) := by
  letI := Fintype.ofFinite S.D.Root
  letI : Fintype (RelativeRootSourceExactIndex S) := Fintype.ofFinite _
  exact Finset.univ.toList

omit [IsAlgClosed k] in
private theorem sourceExactRootList_mem
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (gamma : RelativeRootSourceExactIndex S) :
    gamma ∈ sourceExactRootList S := by
  classical
  simp [sourceExactRootList]

omit [IsAlgClosed k] in
private theorem sourceExactRootList_nodup
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    (sourceExactRootList S).Nodup := by
  exact Finset.nodup_toList _

@[expose]
public noncomputable def sourceExactRootAtLeast
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (gamma : RelativeRootSourceExactIndex S) :
    RelativeRootSourceAtLeastIndex S S.height :=
  ⟨gamma.1, by simpa [relativeRootSourceHeight] using gamma.2.ge⟩

private noncomputable def sourceExactLayerParametrization
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    Variety.Morphism (RelativeRootSourceCoordinateSpace S) K :=
  varietyMorphismListProduct
    ((sourceExactRootList S).map fun gamma =>
      (sourceChevalleyRootCurve S gamma.1).toVariety.comp
        (affineCoordinateMorphism (RelativeRootSourceExactIndex S) gamma))

omit [IsAlgClosed k] in
private theorem sourceExactLayerParametrization_apply
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (z : Variety.Point (RelativeRootSourceCoordinateSpace S)) :
    (sourceExactLayerParametrization S).toFun z =
      ((sourceExactRootList S).map fun gamma =>
        S.C.x gamma.1 (z.val gamma)).prod := by
  rw [sourceExactLayerParametrization, varietyMorphismListProduct_apply]
  simp only [List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro gamma hgamma
  exact sourceChevalleyRootCurve_apply S gamma.1 (z.val gamma)

private theorem sourceExactLayerParametrization_mem
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (z : Variety.Point (RelativeRootSourceCoordinateSpace S)) :
    (sourceExactLayerParametrization S).toFun z ∈
      (S.sourceSimpleLayerClosedSubgroup S.height).toSubgroup := by
  rw [sourceExactLayerParametrization_apply]
  apply Subgroup.list_prod_mem
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨gamma, _, rfl⟩ := hx
  exact sourceChevalleyRoot_mem_layer S S.height
    (sourceExactRootAtLeast S gamma) (z.val gamma)

private noncomputable def sourceExactLayerParametrizationToLayer
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    Variety.Morphism (RelativeRootSourceCoordinateSpace S)
      (S.sourceSimpleLayerClosedSubgroup S.height).carrierVariety :=
  (sourceExactLayerParametrization S).codRestrictClosedSubgroup
    (S.sourceSimpleLayerClosedSubgroup S.height)
    (sourceExactLayerParametrization_mem S)

private theorem sourceExactLayerParametrizationToLayer_pointEquiv
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (z : Variety.Point (RelativeRootSourceCoordinateSpace S)) :
    (S.sourceSimpleLayerClosedSubgroup S.height).pointEquiv
        ((sourceExactLayerParametrizationToLayer S).toFun z) =
      ((sourceExactRootList S).map fun gamma =>
        relativeRootLayerExactElement S gamma (z.val gamma)).prod := by
  apply Subtype.ext
  change (sourceExactLayerParametrization S).toFun z = _
  rw [sourceExactLayerParametrization_apply]
  simp only [SubmonoidClass.coe_list_prod, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro gamma hgamma
  exact (relativeRootLayerExactElement_value S gamma (z.val gamma)).symm

@[expose]
public noncomputable def sourceSimpleLayerPointEquiv
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (n : Nat) :
    Variety.Point (S.sourceSimpleLayerClosedSubgroup n).carrierVariety ≃*
      sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J n :=
  (Equiv.mulEquiv (S.sourceSimpleLayerClosedSubgroup n).pointEquiv).trans
    (MulEquiv.subgroupCongr
      (S.sourceSimpleLayerClosedSubgroup_toSubgroup n))

public noncomputable abbrev sourceAbstractNextLayer
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :=
  (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
    (S.height + 1)).subgroupOf
      (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
        S.height)

private theorem sourceExactLayerParametrization_coordinate
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (z : Variety.Point (RelativeRootSourceCoordinateSpace S)) :
    relativeRootLayerQuotient_coordinateEquiv S
        (QuotientGroup.mk' (sourceAbstractNextLayer S)
          (sourceSimpleLayerPointEquiv S S.height
            ((sourceExactLayerParametrizationToLayer S).toFun z))) =
      Multiplicative.ofAdd z.val := by
  classical
  letI : DecidableEq (RelativeRootSourceExactIndex S) := Classical.decEq _
  letI : (sourceAbstractNextLayer S).Normal :=
    sourceRelativeRootLayer_next_normal S
  let roots := sourceExactRootList S
  let terms := roots.map fun gamma =>
    relativeRootLayerExactElement S gamma (z.val gamma)
  let xs : List (relativeRootLayerQuotient S) := roots.map fun gamma =>
      (QuotientGroup.mk' (sourceAbstractNextLayer S)
        (relativeRootLayerExactElement S gamma (z.val gamma)) :
          relativeRootLayerQuotient S)
  have hpoint : sourceSimpleLayerPointEquiv S S.height
      ((sourceExactLayerParametrizationToLayer S).toFun z) = terms.prod := by
    exact congrArg
      (MulEquiv.subgroupCongr
        (S.sourceSimpleLayerClosedSubgroup_toSubgroup S.height))
      (sourceExactLayerParametrizationToLayer_pointEquiv S z)
  calc
    relativeRootLayerQuotient_coordinateEquiv S
          (QuotientGroup.mk' (sourceAbstractNextLayer S)
          (sourceSimpleLayerPointEquiv S S.height
            ((sourceExactLayerParametrizationToLayer S).toFun z))) =
        relativeRootLayerQuotient_coordinateEquiv S
          (QuotientGroup.mk' (sourceAbstractNextLayer S) terms.prod) := by
      rw [hpoint]
    _ = relativeRootLayerQuotient_coordinateEquiv S xs.prod := by
      apply congrArg (relativeRootLayerQuotient_coordinateEquiv S)
      have hmap := map_list_prod (QuotientGroup.mk' (sourceAbstractNextLayer S)) terms
      refine hmap.trans ?_
      apply congrArg List.prod
      dsimp [xs, terms]
      rw [List.map_map]
      apply List.map_congr_left
      intro gamma hgamma
      rfl
    _ = (xs.map (relativeRootLayerQuotient_coordinateEquiv S)).prod :=
      map_list_prod (relativeRootLayerQuotient_coordinateEquiv S) xs
    _ = (roots.map fun gamma =>
        Multiplicative.ofAdd (Pi.single gamma (z.val gamma))).prod := by
      have hmapxs :
          xs.map (relativeRootLayerQuotient_coordinateEquiv S) =
            roots.map fun gamma =>
              relativeRootLayerQuotient_coordinateEquiv S
                (QuotientGroup.mk' (sourceAbstractNextLayer S)
                  (relativeRootLayerExactElement S gamma (z.val gamma)) :
                    relativeRootLayerQuotient S) := by
        dsimp only [xs]
        induction roots with
        | nil => rfl
        | cons gamma roots ih =>
            change _ :: _ = _ :: _
            rw [ih]
      rw [hmapxs]
      apply congrArg List.prod
      apply List.map_congr_left
      intro gamma hgamma
      simpa only [sourceAbstractNextLayer] using
        relativeRootLayerQuotient_coordinateEquiv_root S gamma (z.val gamma)
    _ = Multiplicative.ofAdd z.val := by
      apply Multiplicative.toAdd.injective
      change (roots.map fun gamma => Pi.single gamma (z.val gamma)).sum = z.val
      funext gamma
      simp [roots, sourceExactRootList]

@[expose]
public noncomputable def sourceNextLayerInCurrent
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    ClosedSubgroup (S.sourceSimpleLayerClosedSubgroup S.height).carrierVariety :=
  (S.sourceSimpleLayerClosedSubgroup S.height).inclusion.closedSubgroupPreimage
    (S.sourceSimpleLayerClosedSubgroup (S.height + 1))

private theorem sourceNextLayerInCurrent_normal
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    (sourceNextLayerInCurrent S).toSubgroup.Normal := by
  let H := S.sourceSimpleLayerClosedSubgroup S.height
  let N := S.sourceSimpleLayerClosedSubgroup (S.height + 1)
  let eH : Variety.Point H.carrierVariety ≃* H.toSubgroup :=
    Equiv.mulEquiv H.pointEquiv
  let Nabs := (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
    S.coeff S.J (S.height + 1)).subgroupOf
      (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
        S.coeff S.J S.height)
  have hnormal : Nabs.Normal := sourceRelativeRootLayer_next_normal S
  refine ⟨?_⟩
  intro n hn g
  have hn' : eH n ∈ Nabs := hn
  have hconj := hnormal.conj_mem (eH n) hn' (eH g)
  exact hconj

private noncomputable def sourceLayerQuotientData
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    Bor1.Theorem112BQuotientData (sourceNextLayerInCurrent S) :=
  Bor1.theorem_1_1_2_b_quotientData
    (sourceNextLayerInCurrent S) (sourceNextLayerInCurrent_normal S)

public theorem sourceNextLayerInCurrent_mem_iff
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (x : Variety.Point
      (S.sourceSimpleLayerClosedSubgroup S.height).carrierVariety) :
    x ∈ (sourceNextLayerInCurrent S).toSubgroup ↔
      sourceSimpleLayerPointEquiv S S.height x ∈
        sourceAbstractNextLayer S := by
  change (S.sourceSimpleLayerClosedSubgroup S.height).inclusion.onPoints x ∈
      (S.sourceSimpleLayerClosedSubgroup (S.height + 1)).toSubgroup ↔ _
  rfl

private theorem sourceLayerQuotientProjection_eq_iff
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (x y : Variety.Point
      (S.sourceSimpleLayerClosedSubgroup S.height).carrierVariety) :
    let D := sourceLayerQuotientData S
    letI := D.quotientAlgebraicGroup
    D.projection.onPoints x = D.projection.onPoints y ↔
      QuotientGroup.mk' (sourceAbstractNextLayer S)
          (sourceSimpleLayerPointEquiv S S.height x) =
        QuotientGroup.mk' (sourceAbstractNextLayer S)
          (sourceSimpleLayerPointEquiv S S.height y) := by
  let D := sourceLayerQuotientData S
  letI := D.quotientAlgebraicGroup
  letI : (sourceAbstractNextLayer S).Normal :=
    sourceRelativeRootLayer_next_normal S
  dsimp only
  constructor
  · intro hxy
    change D.projection.onPoints x = D.projection.onPoints y at hxy
    apply (QuotientGroup.eq_iff_div_mem).2
    have hker : x / y ∈ D.projection.kernel := by
      change D.projection.onPoints (x / y) = 1
      rw [map_div, hxy]
      rw [div_eq_mul_inv]
      exact mul_inv_cancel _
    rw [D.kernel_eq] at hker
    exact (sourceNextLayerInCurrent_mem_iff S (x / y)).mp hker
  · intro hxy
    have hxy' := (QuotientGroup.eq_iff_div_mem).1 hxy
    have hker : x / y ∈ D.projection.kernel := by
      rw [D.kernel_eq]
      exact (sourceNextLayerInCurrent_mem_iff S (x / y)).mpr hxy'
    have hdiv : D.projection.onPoints x / D.projection.onPoints y = 1 := by
      rw [← map_div]
      exact hker
    exact div_eq_one.mp hdiv

private noncomputable def sourceCoordinateToQuotient
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    let D := sourceLayerQuotientData S
    letI := S.coordinateAlgebraicGroup
    letI := D.quotientAlgebraicGroup
    AlgebraicGroup.Morphism (RelativeRootSourceCoordinateSpace S) D.quotient := by
  let D := sourceLayerQuotientData S
  letI := S.coordinateAlgebraicGroup
  letI := D.quotientAlgebraicGroup
  let f : Variety.Morphism (RelativeRootSourceCoordinateSpace S) D.quotient :=
    D.projection.toVariety.comp (sourceExactLayerParametrizationToLayer S)
  refine { toVariety := f, map_one := ?_, map_mul := ?_ }
  · change D.projection.onPoints
      ((sourceExactLayerParametrizationToLayer S).toFun 1) = 1
    rw [← D.projection.map_one]
    apply (sourceLayerQuotientProjection_eq_iff S _ _).2
    apply (relativeRootLayerQuotient_coordinateEquiv S).injective
    rw [sourceExactLayerParametrization_coordinate]
    calc
      Multiplicative.ofAdd (Variety.Point.val (1 :
          Variety.Point (RelativeRootSourceCoordinateSpace S))) = 1 :=
        S.coordinatePointEquiv.map_one
      _ = relativeRootLayerQuotient_coordinateEquiv S
          (QuotientGroup.mk' (sourceAbstractNextLayer S)
            (sourceSimpleLayerPointEquiv S S.height 1)) := by
        rw [map_one, map_one]
        exact (relativeRootLayerQuotient_coordinateEquiv S).map_one.symm
  · intro x y
    change D.projection.onPoints
        ((sourceExactLayerParametrizationToLayer S).toFun (x * y)) =
      D.projection.onPoints
          ((sourceExactLayerParametrizationToLayer S).toFun x) *
        D.projection.onPoints
          ((sourceExactLayerParametrizationToLayer S).toFun y)
    rw [← D.projection.onPoints.map_mul]
    apply (sourceLayerQuotientProjection_eq_iff S _ _).2
    apply (relativeRootLayerQuotient_coordinateEquiv S).injective
    calc
      relativeRootLayerQuotient_coordinateEquiv S
          (QuotientGroup.mk' (sourceAbstractNextLayer S)
            (sourceSimpleLayerPointEquiv S S.height
              ((sourceExactLayerParametrizationToLayer S).toFun (x * y)))) =
          Multiplicative.ofAdd (x * y).val :=
        sourceExactLayerParametrization_coordinate S (x * y)
      _ = Multiplicative.ofAdd x.val * Multiplicative.ofAdd y.val :=
        S.coordinatePointEquiv.map_mul x y
      _ = relativeRootLayerQuotient_coordinateEquiv S
          (QuotientGroup.mk' (sourceAbstractNextLayer S)
            (sourceSimpleLayerPointEquiv S S.height
              ((sourceExactLayerParametrizationToLayer S).toFun x *
                (sourceExactLayerParametrizationToLayer S).toFun y))) := by
        let qx : relativeRootLayerQuotient S :=
          QuotientGroup.mk' (sourceAbstractNextLayer S)
            (sourceSimpleLayerPointEquiv S S.height
              ((sourceExactLayerParametrizationToLayer S).toFun x))
        let qy : relativeRootLayerQuotient S :=
          QuotientGroup.mk' (sourceAbstractNextLayer S)
            (sourceSimpleLayerPointEquiv S S.height
              ((sourceExactLayerParametrizationToLayer S).toFun y))
        calc
          Multiplicative.ofAdd x.val * Multiplicative.ofAdd y.val =
              relativeRootLayerQuotient_coordinateEquiv S qx *
                relativeRootLayerQuotient_coordinateEquiv S qy := by
            rw [sourceExactLayerParametrization_coordinate S x,
              sourceExactLayerParametrization_coordinate S y]
          _ = relativeRootLayerQuotient_coordinateEquiv S (qx * qy) :=
            (relativeRootLayerQuotient_coordinateEquiv S).map_mul qx qy |>.symm
          _ = _ := by
            apply congrArg (relativeRootLayerQuotient_coordinateEquiv S)
            dsimp only [qx, qy]
            rw [map_mul, map_mul]

private theorem sourceCoordinateToQuotient_bijective
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    let D := sourceLayerQuotientData S
    letI := S.coordinateAlgebraicGroup
    letI := D.quotientAlgebraicGroup
    Function.Bijective (sourceCoordinateToQuotient S).onPoints := by
  let D := sourceLayerQuotientData S
  letI := S.coordinateAlgebraicGroup
  letI := D.quotientAlgebraicGroup
  constructor
  · intro x y hxy
    have hproj : D.projection.onPoints
          ((sourceExactLayerParametrizationToLayer S).toFun x) =
        D.projection.onPoints
          ((sourceExactLayerParametrizationToLayer S).toFun y) := hxy
    have hquot := (sourceLayerQuotientProjection_eq_iff S _ _).mp hproj
    have hcoord := congrArg (relativeRootLayerQuotient_coordinateEquiv S) hquot
    rw [sourceExactLayerParametrization_coordinate,
      sourceExactLayerParametrization_coordinate] at hcoord
    apply Variety.Point.ext
    exact congrArg Multiplicative.toAdd hcoord
  · intro q
    obtain ⟨x, hx⟩ := D.pointSurjective q
    let a := relativeRootLayerQuotient_coordinateEquiv S
      (QuotientGroup.mk' (sourceAbstractNextLayer S)
        (sourceSimpleLayerPointEquiv S S.height x))
    let z : Variety.Point (RelativeRootSourceCoordinateSpace S) :=
      affineSpacePoint a.toAdd
    refine ⟨z, ?_⟩
    rw [← hx]
    apply (sourceLayerQuotientProjection_eq_iff S _ _).2
    apply (relativeRootLayerQuotient_coordinateEquiv S).injective
    rw [sourceExactLayerParametrization_coordinate]
    rfl

private noncomputable def affineCoordinateAxis
    (sigma : Type u) [Finite sigma] (i : sigma) :
    letI := affineAdditiveAlgebraicGroup (k := k) sigma
    AlgebraicGroup.Morphism (KPlus k) (affineSpaceVariety k sigma) := by
  classical
  letI : DecidableEq sigma := Classical.decEq _
  letI := affineAdditiveAlgebraicGroup (k := k) sigma
  refine
    { toVariety :=
        { toFun := fun x =>
            { val := Pi.single i (x.val PUnit.unit)
              isZero := by simp }
          regular := ?_ }
      map_one := ?_
      map_mul := ?_ }
  · intro j
    by_cases hji : j = i
    · subst j
      refine ⟨MvPolynomial.X PUnit.unit, ?_⟩
      intro x
      rw [evalPolynomial_X]
      change (Pi.single i (x.val PUnit.unit) : sigma → k) i = x.val PUnit.unit
      simp only [Pi.single_apply]
      rw [if_pos trivial]
    · refine ⟨0, ?_⟩
      intro x
      change (Pi.single i (x.val PUnit.unit) : sigma → k) j = 0
      simp only [Pi.single_apply, hji, if_false]
  · apply Variety.Point.ext
    funext j
    have hzero : (1 : Variety.Point (KPlus k)).val PUnit.unit = 0 := by
      rw [← kPlusPoint_coordinate (k := k) (1 : Variety.Point (KPlus k))]
      rfl
    have htarget :
        (1 : Variety.Point (affineSpaceVariety k sigma)).val j = 0 := by
      have h := congrArg
        (fun z : Multiplicative (sigma → k) => z.toAdd j)
        ((Equiv.mulEquiv (affineAdditivePointEquiv (k := k) sigma)).map_one)
      exact h
    change (Pi.single i
      ((1 : Variety.Point (KPlus k)).val PUnit.unit) : sigma → k) j =
        (1 : Variety.Point (affineSpaceVariety k sigma)).val j
    rw [hzero, htarget]
    simp only [Pi.single_zero, Pi.zero_apply]
  · intro x y
    apply Variety.Point.ext
    funext j
    let xAxis : Variety.Point (affineSpaceVariety k sigma) :=
      ⟨Pi.single i (x.val PUnit.unit), by simp⟩
    let yAxis : Variety.Point (affineSpaceVariety k sigma) :=
      ⟨Pi.single i (y.val PUnit.unit), by simp⟩
    have htarget :
        (xAxis * yAxis).val j = xAxis.val j + yAxis.val j := by
      have h := congrArg
        (fun z : Multiplicative (sigma → k) => z.toAdd j)
        ((Equiv.mulEquiv (affineAdditivePointEquiv (k := k) sigma)).map_mul
          xAxis yAxis)
      exact h
    change (Pi.single i ((x * y).val PUnit.unit) : sigma → k) j =
      (xAxis * yAxis).val j
    rw [htarget, kPlusPoint_coordinate_mul]
    simp only [xAxis, yAxis, Pi.single_apply]
    split_ifs
    · rfl
    · exact (zero_add 0).symm

omit [IsAlgClosed k] in
private theorem affineCoordinateAxis_apply
    (sigma : Type u) [Finite sigma] (i : sigma) (t : k) :
    letI : DecidableEq sigma := Classical.decEq _
    letI := affineAdditiveAlgebraicGroup (k := k) sigma
    (affineCoordinateAxis sigma i).onPoints (kPlusPoint t) =
      affineSpacePoint (Pi.single i t) := by
  apply Variety.Point.ext
  rfl

@[expose]
public noncomputable def sourceChevalleyRootCurveToLayer
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (n : Nat)
    (alpha : RelativeRootSourceAtLeastIndex S n) :
    AlgebraicGroup.Morphism (KPlus k)
      (S.sourceSimpleLayerClosedSubgroup n).carrierVariety :=
  (sourceChevalleyRootCurve S alpha.1).codRestrictClosedSubgroup
    (S.sourceSimpleLayerClosedSubgroup n) (fun z => by
      change (S.D.rootSubgroup alpha.1).inclusion.onPoints
        ((S.chevalleyParametrization alpha.1).hom.onPoints z) ∈
          (S.sourceSimpleLayerClosedSubgroup n).toSubgroup
      apply sourceRootSubgroup_le_layer S n alpha
      exact ((S.D.rootSubgroup alpha.1).pointEquiv
        ((S.chevalleyParametrization alpha.1).hom.onPoints z)).property)

public theorem sourceChevalleyRootCurveToLayer_inclusion_apply
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (n : Nat)
    (alpha : RelativeRootSourceAtLeastIndex S n) (t : k) :
    (S.sourceSimpleLayerClosedSubgroup n).inclusion.onPoints
        ((sourceChevalleyRootCurveToLayer S n alpha).onPoints (kPlusPoint t)) =
      S.C.x alpha.1 t := by
  unfold sourceChevalleyRootCurveToLayer
  rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
  exact sourceChevalleyRootCurve_apply S alpha.1 t

private theorem sourceChevalleyRootCurveToLayer_tangent
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) (n : Nat)
    (alpha : RelativeRootSourceAtLeastIndex S n) :
    identityTangentMorphismLinearMap
        (sourceChevalleyRootCurveToLayer S n alpha)
        Theory.AlgebraicGroup.kPlusIdentityDerivation =
      sourceLayerRootTangent S n alpha := by
  apply identityTangentMorphismLinearMap_inclusion_injective
    (S.sourceSimpleLayerClosedSubgroup n)
  rw [sourceLayerRootTangent_inclusion]
  have hcomp :
      (S.sourceSimpleLayerClosedSubgroup n).inclusion.comp
          (sourceChevalleyRootCurveToLayer S n alpha) =
        sourceChevalleyRootCurve S alpha.1 := by
    apply AlgebraicGroup.Morphism.ext
    funext z
    exact AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply
      (sourceChevalleyRootCurve S alpha.1)
        (S.sourceSimpleLayerClosedSubgroup n) _ z
  have hdiff :
      identityTangentMorphismLinearMap
          ((S.sourceSimpleLayerClosedSubgroup n).inclusion.comp
            (sourceChevalleyRootCurveToLayer S n alpha))
          Theory.AlgebraicGroup.kPlusIdentityDerivation =
        identityTangentMorphismLinearMap
          (S.sourceSimpleLayerClosedSubgroup n).inclusion
          (identityTangentMorphismLinearMap
            (sourceChevalleyRootCurveToLayer S n alpha)
            Theory.AlgebraicGroup.kPlusIdentityDerivation) := by
    apply Derivation.ext
    intro f
    rfl
  rw [← hdiff, hcomp]
  apply Derivation.ext
  intro f
  exact (oneParameterTangent_apply
    (S.D.rootSubgroup alpha.1) (S.chevalleyParametrization alpha.1) f).symm

private theorem sourceCoordinateToQuotient_comp_axis
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (gamma : RelativeRootSourceExactIndex S) :
    let D := sourceLayerQuotientData S
    letI := S.coordinateAlgebraicGroup
    letI := D.quotientAlgebraicGroup
    (sourceCoordinateToQuotient S).comp
        (affineCoordinateAxis (RelativeRootSourceExactIndex S) gamma) =
      D.projection.comp
        (sourceChevalleyRootCurveToLayer S S.height
          (sourceExactRootAtLeast S gamma)) := by
  classical
  let D := sourceLayerQuotientData S
  letI := S.coordinateAlgebraicGroup
  letI := D.quotientAlgebraicGroup
  letI : (sourceAbstractNextLayer S).Normal :=
    sourceRelativeRootLayer_next_normal S
  apply AlgebraicGroup.Morphism.ext
  funext x
  let t := Multiplicative.toAdd (additiveGroupPointEquiv k x)
  rw [← kPlusPoint_coordinate (k := k) x]
  change (sourceCoordinateToQuotient S).onPoints
      ((affineCoordinateAxis (RelativeRootSourceExactIndex S) gamma).onPoints
        (kPlusPoint t)) =
    D.projection.onPoints
      ((sourceChevalleyRootCurveToLayer S S.height
        (sourceExactRootAtLeast S gamma)).onPoints (kPlusPoint t))
  rw [affineCoordinateAxis_apply]
  apply (sourceLayerQuotientProjection_eq_iff S _ _).2
  apply (relativeRootLayerQuotient_coordinateEquiv S).injective
  rw [sourceExactLayerParametrization_coordinate]
  have hpoint :
      sourceSimpleLayerPointEquiv S S.height
          ((sourceChevalleyRootCurveToLayer S S.height
            (sourceExactRootAtLeast S gamma)).onPoints (kPlusPoint t)) =
        relativeRootLayerExactElement S gamma t := by
    apply Subtype.ext
    change (sourceChevalleyRootCurve S gamma.1).onPoints (kPlusPoint t) = _
    rw [sourceChevalleyRootCurve_apply, relativeRootLayerExactElement_value]
  rw [hpoint, relativeRootLayerQuotient_coordinateEquiv_root]
  apply Multiplicative.toAdd.injective
  rfl

private theorem sourceExactRootTangent_projection_mem_range
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (gamma : RelativeRootSourceExactIndex S) :
    let D := sourceLayerQuotientData S
    letI := S.coordinateAlgebraicGroup
    letI := D.quotientAlgebraicGroup
    identityTangentMorphismLinearMap D.projection
        (sourceLayerRootTangent S S.height
          (sourceExactRootAtLeast S gamma)) ∈
      LinearMap.range
        (identityTangentMorphismLinearMap (sourceCoordinateToQuotient S)) := by
  let D := sourceLayerQuotientData S
  letI := S.coordinateAlgebraicGroup
  letI := D.quotientAlgebraicGroup
  let axis := affineCoordinateAxis (k := k)
    (RelativeRootSourceExactIndex S) gamma
  let tangent := identityTangentMorphismLinearMap axis
    Theory.AlgebraicGroup.kPlusIdentityDerivation
  refine ⟨tangent, ?_⟩
  have hmorphism := sourceCoordinateToQuotient_comp_axis S gamma
  have htangent := congrArg
    (fun f => identityTangentMorphismLinearMap f
      Theory.AlgebraicGroup.kPlusIdentityDerivation) hmorphism
  change identityTangentMorphismLinearMap (sourceCoordinateToQuotient S)
      (identityTangentMorphismLinearMap axis
        Theory.AlgebraicGroup.kPlusIdentityDerivation) =
    identityTangentMorphismLinearMap D.projection
      (identityTangentMorphismLinearMap
        (sourceChevalleyRootCurveToLayer S S.height
          (sourceExactRootAtLeast S gamma))
        Theory.AlgebraicGroup.kPlusIdentityDerivation) at htangent
  rw [sourceChevalleyRootCurveToLayer_tangent] at htangent
  exact htangent

private noncomputable def sourceHigherRootAtLeast
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (alpha : RelativeRootSourceAtLeastIndex S S.height)
    (hgreater : relativeRootSourceHeight S alpha.1 ≠ S.height) :
    RelativeRootSourceAtLeastIndex S (S.height + 1) :=
  ⟨alpha.1, by omega⟩

private noncomputable def sourceHigherChevalleyRootCurveToNext
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (alpha : RelativeRootSourceAtLeastIndex S S.height)
    (hgreater : relativeRootSourceHeight S alpha.1 ≠ S.height) :
    letI := (sourceNextLayerInCurrent S).carrierAlgebraicGroup
    AlgebraicGroup.Morphism (KPlus k)
      (sourceNextLayerInCurrent S).carrierVariety := by
  letI := (sourceNextLayerInCurrent S).carrierAlgebraicGroup
  exact (sourceChevalleyRootCurveToLayer S S.height alpha).codRestrictClosedSubgroup
    (sourceNextLayerInCurrent S) (fun z => by
      change (S.sourceSimpleLayerClosedSubgroup S.height).inclusion.onPoints
          ((sourceChevalleyRootCurveToLayer S S.height alpha).onPoints z) ∈
        (S.sourceSimpleLayerClosedSubgroup (S.height + 1)).toSubgroup
      change (S.D.rootSubgroup alpha.1).inclusion.onPoints
          ((S.chevalleyParametrization alpha.1).hom.onPoints z) ∈
        (S.sourceSimpleLayerClosedSubgroup (S.height + 1)).toSubgroup
      apply sourceRootSubgroup_le_layer S (S.height + 1)
        (sourceHigherRootAtLeast S alpha hgreater)
      exact ((S.D.rootSubgroup alpha.1).pointEquiv
        ((S.chevalleyParametrization alpha.1).hom.onPoints z)).property)

private theorem sourceHigherRootTangent_mem_next_range
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (alpha : RelativeRootSourceAtLeastIndex S S.height)
    (hgreater : relativeRootSourceHeight S alpha.1 ≠ S.height) :
    letI := (sourceNextLayerInCurrent S).carrierAlgebraicGroup
    sourceLayerRootTangent S S.height alpha ∈
      LinearMap.range (identityTangentMorphismLinearMap
        (sourceNextLayerInCurrent S).inclusion) := by
  letI := (sourceNextLayerInCurrent S).carrierAlgebraicGroup
  let curve := sourceHigherChevalleyRootCurveToNext S alpha hgreater
  let tangent := identityTangentMorphismLinearMap curve
    Theory.AlgebraicGroup.kPlusIdentityDerivation
  refine ⟨tangent, ?_⟩
  have hcomp :
      (sourceNextLayerInCurrent S).inclusion.comp curve =
        sourceChevalleyRootCurveToLayer S S.height alpha := by
    apply AlgebraicGroup.Morphism.ext
    funext z
    exact AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply
      (sourceChevalleyRootCurveToLayer S S.height alpha)
        (sourceNextLayerInCurrent S) _ z
  have htangent := congrArg
    (fun f => identityTangentMorphismLinearMap f
      Theory.AlgebraicGroup.kPlusIdentityDerivation) hcomp
  change identityTangentMorphismLinearMap
      (sourceNextLayerInCurrent S).inclusion tangent =
    identityTangentMorphismLinearMap
      (sourceChevalleyRootCurveToLayer S S.height alpha)
      Theory.AlgebraicGroup.kPlusIdentityDerivation at htangent
  rw [sourceChevalleyRootCurveToLayer_tangent] at htangent
  exact htangent

private theorem sourceHigherRootTangent_projection_eq_zero
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (alpha : RelativeRootSourceAtLeastIndex S S.height)
    (hgreater : relativeRootSourceHeight S alpha.1 ≠ S.height) :
    let D := sourceLayerQuotientData S
    letI := D.quotientAlgebraicGroup
    identityTangentMorphismLinearMap D.projection
        (sourceLayerRootTangent S S.height alpha) = 0 := by
  let D := sourceLayerQuotientData S
  letI := (sourceNextLayerInCurrent S).carrierAlgebraicGroup
  letI := D.quotientAlgebraicGroup
  have hrange := sourceHigherRootTangent_mem_next_range S alpha hgreater
  have hrange' : sourceLayerRootTangent S S.height alpha ∈
      LinearMap.range (Bor1.identityTangentMorphismLinearMap
        (sourceNextLayerInCurrent S).inclusion) := by
    simpa only [Bor1.identityTangentMorphismLinearMap,
      Theory.AlgebraicGroup.identityTangentMorphismLinearMap] using hrange
  have hker : sourceLayerRootTangent S S.height alpha ∈
      LinearMap.ker
        (Bor1.identityTangentMorphismLinearMap D.projection) := by
    rw [D.tangentKernel_eq]
    exact hrange'
  simpa only [LinearMap.mem_ker,
    Bor1.identityTangentMorphismLinearMap,
    Theory.AlgebraicGroup.identityTangentMorphismLinearMap] using hker

private theorem sourceRootTangent_projection_mem_range
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (alpha : RelativeRootSourceAtLeastIndex S S.height) :
    let D := sourceLayerQuotientData S
    letI := S.coordinateAlgebraicGroup
    letI := D.quotientAlgebraicGroup
    identityTangentMorphismLinearMap D.projection
        (sourceLayerRootTangent S S.height alpha) ∈
      LinearMap.range
        (identityTangentMorphismLinearMap (sourceCoordinateToQuotient S)) := by
  let D := sourceLayerQuotientData S
  letI := S.coordinateAlgebraicGroup
  letI := D.quotientAlgebraicGroup
  dsimp only
  by_cases hheight : relativeRootSourceHeight S alpha.1 = S.height
  · let gamma : RelativeRootSourceExactIndex S := ⟨alpha.1, hheight⟩
    have halpha : sourceExactRootAtLeast S gamma = alpha := by
      apply Subtype.ext
      rfl
    rw [← halpha]
    exact sourceExactRootTangent_projection_mem_range S gamma
  · rw [sourceHigherRootTangent_projection_eq_zero S alpha hheight]
    exact ⟨0, map_zero _⟩

private theorem sourceCoordinateToQuotient_tangent_surjective
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    let D := sourceLayerQuotientData S
    letI := S.coordinateAlgebraicGroup
    letI := D.quotientAlgebraicGroup
    Function.Surjective
      (identityTangentMorphismLinearMap (sourceCoordinateToQuotient S)) := by
  let D := sourceLayerQuotientData S
  letI := S.coordinateAlgebraicGroup
  letI := D.quotientAlgebraicGroup
  dsimp only
  let dCoordinate :=
    identityTangentMorphismLinearMap (sourceCoordinateToQuotient S)
  let dProjection := identityTangentMorphismLinearMap D.projection
  have hProjection : Function.Surjective dProjection := by
    simpa only [dProjection, Bor1.identityTangentMorphismLinearMap,
      Theory.AlgebraicGroup.identityTangentMorphismLinearMap] using
        D.tangentSurjective
  intro y
  obtain ⟨x, hx⟩ := hProjection y
  let P := (LinearMap.range dCoordinate).comap dProjection
  have hroot : Set.range (sourceLayerRootTangent S S.height) ⊆ P := by
    rintro _ ⟨alpha, rfl⟩
    exact sourceRootTangent_projection_mem_range S alpha
  have hP : P = ⊤ := by
    apply top_unique
    rw [← sourceLayerRootTangents_span S S.height S.height_pos]
    exact Submodule.span_le.mpr hroot
  have hxP : x ∈ P := by rw [hP]; exact Submodule.mem_top
  change dProjection x ∈ LinearMap.range dCoordinate at hxP
  obtain ⟨z, hz⟩ := hxP
  refine ⟨z, ?_⟩
  rw [hz, hx]

private theorem sourceCoordinateToQuotient_pullback_surjective
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    let D := sourceLayerQuotientData S
    letI := S.coordinateAlgebraicGroup
    letI := D.quotientAlgebraicGroup
    Function.Surjective
      (sourceCoordinateToQuotient S).toVariety.pullbackRingHom := by
  let D := sourceLayerQuotientData S
  letI := S.coordinateAlgebraicGroup
  letI := D.quotientAlgebraicGroup
  dsimp only
  let f := sourceCoordinateToQuotient S
  let B : ClosedSubgroup (RelativeRootSourceCoordinateSpace S) :=
    ClosedSubgroup.bot
  have hbij := sourceCoordinateToQuotient_bijective S
  have hker : f.kernel = B.toSubgroup := by
    change f.onPoints.ker = ⊥
    exact (MonoidHom.ker_eq_bot_iff f.onPoints).2 hbij.1
  have hdf : Function.Surjective
      (Bor1.identityTangentMorphismLinearMap f) := by
    simpa only [Bor1.identityTangentMorphismLinearMap,
      Theory.AlgebraicGroup.identityTangentMorphismLinearMap] using
        sourceCoordinateToQuotient_tangent_surjective S
  have hinvariant : Function.Surjective
      (f.pullbackToRightInvariantCoordinateRing B (by rw [hker])) :=
    Bor1.pullbackToRightInvariantCoordinateRing_surjective
      B f hbij.2 hker hdf
  intro a
  let b : AlgebraicGroup.rightInvariantCoordinateRing B :=
    ⟨a, by
      rw [AlgebraicGroup.mem_rightInvariantCoordinateRing_iff]
      intro g h hh
      change h = 1 at hh
      rw [hh, mul_one]⟩
  obtain ⟨q, hq⟩ := hinvariant b
  refine ⟨q, ?_⟩
  exact congrArg Subtype.val hq

private noncomputable def sourceCoordinateQuotientIso
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    let D := sourceLayerQuotientData S
    letI := S.coordinateAlgebraicGroup
    letI := D.quotientAlgebraicGroup
    AlgebraicGroup.Iso (RelativeRootSourceCoordinateSpace S) D.quotient := by
  let D := sourceLayerQuotientData S
  letI := S.coordinateAlgebraicGroup
  letI := D.quotientAlgebraicGroup
  exact Classical.choose
    (algebraicGroupIso_of_bijective_morphism_of_pullback_surjective
      (sourceCoordinateToQuotient S)
      (sourceCoordinateToQuotient_bijective S)
      (sourceCoordinateToQuotient_pullback_surjective S))

private theorem sourceCoordinateQuotientIso_hom
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    let D := sourceLayerQuotientData S
    letI := S.coordinateAlgebraicGroup
    letI := D.quotientAlgebraicGroup
    (sourceCoordinateQuotientIso S).hom = sourceCoordinateToQuotient S := by
  let D := sourceLayerQuotientData S
  letI := S.coordinateAlgebraicGroup
  letI := D.quotientAlgebraicGroup
  exact Classical.choose_spec
    (algebraicGroupIso_of_bijective_morphism_of_pullback_surjective
      (sourceCoordinateToQuotient S)
      (sourceCoordinateToQuotient_bijective S)
      (sourceCoordinateToQuotient_pullback_surjective S))

public noncomputable def RelativeRootRepresentationSource.sourceLayerCoordinateQuotientMorphism
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    letI := S.coordinateAlgebraicGroup
    AlgebraicGroup.Morphism
      (S.sourceSimpleLayerClosedSubgroup S.height).carrierVariety
      (RelativeRootSourceCoordinateSpace S) := by
  let D := sourceLayerQuotientData S
  letI := S.coordinateAlgebraicGroup
  letI := D.quotientAlgebraicGroup
  exact (sourceCoordinateQuotientIso S).inv.comp D.projection

public theorem RelativeRootRepresentationSource.sourceLayerCoordinateQuotientMorphism_surjective
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    letI := S.coordinateAlgebraicGroup
    Function.Surjective S.sourceLayerCoordinateQuotientMorphism.onPoints := by
  let D := sourceLayerQuotientData S
  letI := S.coordinateAlgebraicGroup
  letI := D.quotientAlgebraicGroup
  intro z
  let e := sourceCoordinateQuotientIso S
  obtain ⟨x, hx⟩ := D.pointSurjective (e.hom.onPoints z)
  refine ⟨x, ?_⟩
  change e.inv.onPoints (D.projection.onPoints x) = z
  rw [hx, e.hom_inv_id]

public theorem RelativeRootRepresentationSource.sourceLayerCoordinateQuotientMorphism_point
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (x : Variety.Point
      (S.sourceSimpleLayerClosedSubgroup S.height).carrierVariety) :
    letI := S.coordinateAlgebraicGroup
    S.coordinatePointEquiv
        (S.sourceLayerCoordinateQuotientMorphism.onPoints x) =
      relativeRootLayerQuotient_coordinateEquiv S
        (QuotientGroup.mk' (sourceAbstractNextLayer S)
          (sourceSimpleLayerPointEquiv S S.height x)) := by
  let D := sourceLayerQuotientData S
  letI := S.coordinateAlgebraicGroup
  letI := D.quotientAlgebraicGroup
  letI : (sourceAbstractNextLayer S).Normal :=
    sourceRelativeRootLayer_next_normal S
  let e := sourceCoordinateQuotientIso S
  let z := S.sourceLayerCoordinateQuotientMorphism.onPoints x
  have heq : D.projection.onPoints
      ((sourceExactLayerParametrizationToLayer S).toFun z) =
        D.projection.onPoints x := by
    calc
      D.projection.onPoints
          ((sourceExactLayerParametrizationToLayer S).toFun z) =
          (sourceCoordinateToQuotient S).onPoints z := rfl
      _ = e.hom.onPoints z := by rw [sourceCoordinateQuotientIso_hom]
      _ = D.projection.onPoints x := by
        change e.hom.onPoints (e.inv.onPoints (D.projection.onPoints x)) = _
        rw [e.inv_hom_id]
  have hquot := (sourceLayerQuotientProjection_eq_iff S _ _).1 heq
  have hcoord := congrArg (relativeRootLayerQuotient_coordinateEquiv S) hquot
  rw [sourceExactLayerParametrization_coordinate] at hcoord
  change Multiplicative.ofAdd z.val = _
  exact hcoord

public theorem RelativeRootRepresentationSource.sourceLayerCoordinateQuotientMorphism_kernel
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    letI := S.coordinateAlgebraicGroup
    S.sourceLayerCoordinateQuotientMorphism.kernel =
      (sourceNextLayerInCurrent S).toSubgroup := by
  let D := sourceLayerQuotientData S
  letI := S.coordinateAlgebraicGroup
  letI := D.quotientAlgebraicGroup
  let e := sourceCoordinateQuotientIso S
  ext x
  change e.inv.onPoints (D.projection.onPoints x) = 1 ↔
    x ∈ (sourceNextLayerInCurrent S).toSubgroup
  rw [← D.kernel_eq]
  change e.inv.onPoints (D.projection.onPoints x) = 1 ↔
    D.projection.onPoints x = 1
  constructor
  · intro hx
    have h := congrArg e.hom.onPoints hx
    simpa only [map_one, e.inv_hom_id] using h
  · intro hx
    rw [hx, map_one]

public theorem RelativeRootRepresentationSource.sourceLayerCoordinateQuotientMorphism_chevalley
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (gamma : RelativeRootSourceExactIndex S) (t : k) :
    letI : DecidableEq (RelativeRootSourceExactIndex S) := Classical.decEq _
    letI := S.coordinateAlgebraicGroup
    S.sourceLayerCoordinateQuotientMorphism.onPoints
        ((sourceChevalleyRootCurveToLayer S S.height
          (sourceExactRootAtLeast S gamma)).onPoints (kPlusPoint t)) =
      affineSpacePoint
        (Pi.single gamma t : RelativeRootSourceExactIndex S → k) := by
  classical
  letI := S.coordinateAlgebraicGroup
  apply S.coordinatePointEquiv.injective
  rw [S.sourceLayerCoordinateQuotientMorphism_point]
  have hpoint :
      sourceSimpleLayerPointEquiv S S.height
          ((sourceChevalleyRootCurveToLayer S S.height
            (sourceExactRootAtLeast S gamma)).onPoints (kPlusPoint t)) =
        relativeRootLayerExactElement S gamma t := by
    apply Subtype.ext
    change (sourceChevalleyRootCurve S gamma.1).onPoints (kPlusPoint t) = _
    rw [sourceChevalleyRootCurve_apply, relativeRootLayerExactElement_value]
  rw [hpoint, relativeRootLayerQuotient_coordinateEquiv_root]
  rfl

end Theory.AlgebraicGroup
