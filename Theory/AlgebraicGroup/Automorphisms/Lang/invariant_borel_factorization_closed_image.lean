module

public import Theory.AlgebraicGroup.Automorphisms.Lang.FiniteFiberDominance
public import Theory.AlgebraicGroup.Borel.Defs
public import Theory.AlgebraicGroup.Morphism.Operations

universe u v

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-!
This module isolates the closed-image part of Steinberg's invariant-Borel
factorization.  A quotient witness for `K / B` supplies the two closed-image
facts used in the source proof: descending a right-`B`-saturated closed set
from `K x K` to `(K / B) x K` and projecting a closed subset from the complete
quotient.  The relation
`x⁻¹ y sigma(x) in B` is closed because it is the inverse image of the closed
Borel under a regular morphism.  Its second-coordinate image is therefore
closed; the quotient construction itself is intentionally a separate API.

The statement follows the source proof in GLS3, Chapter 2, Steinberg 7.3.
-/

/-! A complete quotient turns a closed relation into a closed second image. -/

public theorem isClosed_secondProjection_of_complete_quotient
    {A : Type u} {Q : Type v} {X : Type u}
    [TopologicalSpace A] [TopologicalSpace Q] [TopologicalSpace X]
    (rho : A → Q × X)
    (hRho : IsClosedMap rho)
    (hSecond : IsClosedMap (Prod.snd : Q × X → X))
    {S : Set A} (hS : IsClosed S) :
    IsClosed ((Prod.snd : Q × X → X) '' (rho '' S)) := by
  exact hSecond _ (hRho _ hS)

/-! The quotient contract needed by the Borel argument. -/

public def rightBSaturated
    {K : Variety k} [AlgebraicGroup K]
    (B : ClosedSubgroup K)
    (S : Set (Variety.Point (Variety.prod K K))) : Prop :=
  ∀ x y b : Variety.Point K, b ∈ B.toSubgroup →
    (((Variety.prodPointEquiv K K).symm (x * b, y) ∈ S) ↔
      ((Variety.prodPointEquiv K K).symm (x, y) ∈ S))

public structure BorelCompleteQuotientWitness
    {K : Variety k} [AlgebraicGroup K]
    (B : ClosedSubgroup K) (Q : Type v) [TopologicalSpace Q] where
  pi : Variety.Point K → Q
  surjective : Function.Surjective pi
  fiber : ∀ x y : Variety.Point K,
    pi x = pi y ↔ ∃ b : Variety.Point K, b ∈ B.toSubgroup ∧ y = x * b
  /-- Closed descent for the saturated sets to which the quotient argument is
  applied.  This is deliberately restricted to right-`B`-saturated sets;
  requiring a closed map on all subsets would imply that the ordinary
  projection `K × K → K` is closed. -/
  closedSaturated : ∀ {S : Set (Variety.Point (Variety.prod K K))},
    IsClosed S → rightBSaturated B S →
      IsClosed ((fun z : Variety.Point (Variety.prod K K) =>
        (pi (Variety.prodPointEquiv K K z).1,
          (Variety.prodPointEquiv K K z).2)) '' S)
  closedSecond : IsClosedMap
    (Prod.snd : Q × Variety.Point K → Variety.Point K)

/-! The regular relation in the invariant-Borel factorization. -/

@[expose]
public def borelLangRelationMorphism
    {K : Variety k} [AlgebraicGroup K]
    (sigma : AlgebraicGroup.Morphism K K) : Variety.Morphism
      (Variety.prod K K) K := by
  let fst := Variety.Morphism.fst K K
  let snd := Variety.Morphism.snd K K
  let xinv := (AlgebraicGroup.invMorphism K).comp fst
  let xinvY := (AlgebraicGroup.mulMorphism K).comp (xinv.pair snd)
  exact (AlgebraicGroup.mulMorphism K).comp
    (xinvY.pair (sigma.toVariety.comp fst))

omit [IsAlgClosed k] in
public lemma borelLangRelationMorphism_apply
    {K : Variety k} [AlgebraicGroup K]
    (sigma : AlgebraicGroup.Morphism K K)
    (x y : Variety.Point K) :
    (borelLangRelationMorphism sigma).toFun
      ((Variety.prodPointEquiv K K).symm (x, y)) =
      x⁻¹ * y * sigma.onPoints x := by
  rfl

@[expose]
public def borelLangRelation
    {K : Variety k} [AlgebraicGroup K]
    (sigma : AlgebraicGroup.Morphism K K) (B : ClosedSubgroup K) :
    Set (Variety.Point (Variety.prod K K)) :=
  (borelLangRelationMorphism sigma).toFun ⁻¹'
    (B.toSubgroup : Set (Variety.Point K))

@[expose]
public def borelLangImage
    {K : Variety k} [AlgebraicGroup K]
    (sigma : AlgebraicGroup.Morphism K K) (B : ClosedSubgroup K) :
    Set (Variety.Point K) :=
  (Variety.Morphism.snd K K).toFun '' borelLangRelation sigma B

omit [IsAlgClosed k] in
public lemma borelLangRelation_isClosed
    {K : Variety k} [AlgebraicGroup K]
    (sigma : AlgebraicGroup.Morphism K K) (B : ClosedSubgroup K) :
    IsClosed (borelLangRelation sigma B) := by
  exact Variety.isClosed_iff_isZariskiClosed.mpr
    ((borelLangRelationMorphism sigma).isZariskiClosed_preimage
      B.isZariskiClosed)

omit [IsAlgClosed k] in
public lemma borelLangRelation_rightBSaturated
    {K : Variety k} [AlgebraicGroup K]
    (sigma : AlgebraicGroup.Morphism K K) (B : ClosedSubgroup K)
    (hStable : ∀ x : Variety.Point B.carrierVariety,
      sigma.onPoints (B.inclusion.onPoints x) ∈ B.toSubgroup) :
    rightBSaturated B (borelLangRelation sigma B) := by
  intro x y b hb
  let b' : Variety.Point B.carrierVariety := B.pointEquiv.symm ⟨b, hb⟩
  have hσb : sigma.onPoints b ∈ B.toSubgroup := by
    have h := hStable b'
    have hbval : B.inclusion.onPoints b' = b := by
      change (B.pointEquiv b').val = b
      dsimp [b']
      rw [B.pointEquiv.apply_symm_apply]
    rw [hbval] at h
    exact h
  change (x * b)⁻¹ * y * sigma.onPoints (x * b) ∈ B.toSubgroup ↔
    x⁻¹ * y * sigma.onPoints x ∈ B.toSubgroup
  have hform : (x * b)⁻¹ * y * sigma.onPoints (x * b) =
      b⁻¹ * (x⁻¹ * y * sigma.onPoints x) * sigma.onPoints b := by
    rw [sigma.onPoints.map_mul, mul_inv_rev]
    group
  rw [hform]
  constructor
  · intro h
    have h' := B.toSubgroup.mul_mem
      (B.toSubgroup.mul_mem hb h) (B.toSubgroup.inv_mem hσb)
    simpa [mul_assoc] using h'
  · intro h
    have h' := B.toSubgroup.mul_mem
      (B.toSubgroup.inv_mem hb) (B.toSubgroup.mul_mem h hσb)
    simpa [mul_assoc] using h'

omit [IsAlgClosed k] in
public theorem borelLangImage_isClosed_of_complete_quotient
    {K : Variety k} [AlgebraicGroup K]
    (sigma : AlgebraicGroup.Morphism K K) (B : ClosedSubgroup K)
    (hStable : ∀ x : Variety.Point B.carrierVariety,
      sigma.onPoints (B.inclusion.onPoints x) ∈ B.toSubgroup)
    {Q : Type v} [TopologicalSpace Q]
    (q : BorelCompleteQuotientWitness B Q) :
    IsClosed (borelLangImage sigma B) := by
  let rho : Variety.Point (Variety.prod K K) → Q × Variety.Point K :=
    fun z => (q.pi (Variety.prodPointEquiv K K z).1,
      (Variety.prodPointEquiv K K z).2)
  have hclosed := q.closedSaturated
    (borelLangRelation_isClosed sigma B)
    (borelLangRelation_rightBSaturated sigma B hStable)
  have hEq :
      (Prod.snd : Q × Variety.Point K → Variety.Point K) '' (rho ''
        borelLangRelation sigma B) = borelLangImage sigma B := by
    ext y
    constructor
    · rintro ⟨q', ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨rho z, ⟨z, hz, rfl⟩, rfl⟩
  have hclosed' := q.closedSecond _ hclosed
  rw [hEq] at hclosed'
  exact hclosed'

omit [IsAlgClosed k] in
public lemma borelLangImage_mem_iff
    {K : Variety k} [AlgebraicGroup K]
    (sigma : AlgebraicGroup.Morphism K K) (B : ClosedSubgroup K)
    (y : Variety.Point K) :
    y ∈ borelLangImage sigma B ↔
      ∃ x : Variety.Point K, x⁻¹ * y * sigma.onPoints x ∈ B.toSubgroup := by
  constructor
  · rintro ⟨z, hz, hzy⟩
    refine ⟨(Variety.prodPointEquiv K K z).1, ?_⟩
    have hzy' : (Variety.prodPointEquiv K K z).2 = y := hzy
    rw [← hzy']
    change (borelLangRelationMorphism sigma).toFun z ∈ B.toSubgroup at hz
    have hzform : z = (Variety.prodPointEquiv K K).symm
        ((Variety.prodPointEquiv K K z).1,
          (Variety.prodPointEquiv K K z).2) := by
      simp
    rw [hzform, borelLangRelationMorphism_apply] at hz
    exact hz
  · rintro ⟨x, hx⟩
    let z := (Variety.prodPointEquiv K K).symm (x, y)
    refine ⟨z, ?_, ?_⟩
    · simpa [borelLangRelation, z, borelLangRelationMorphism_apply] using hx
    · exact congrArg Prod.snd
        ((Variety.prodPointEquiv K K).apply_symm_apply (x, y))

@[expose]
public def borelLangFactorizationImage
    {K : Variety k} [AlgebraicGroup K]
    (sigma : AlgebraicGroup.Morphism K K) (B : ClosedSubgroup K) :
    Set (Variety.Point K) :=
  {y | ∃ x : Variety.Point K, ∃ b : Variety.Point K,
      b ∈ B.toSubgroup ∧ y = x * b * sigma.onPoints x⁻¹}

omit [IsAlgClosed k] in
public lemma borelLangImage_eq_factorizationImage
    {K : Variety k} [AlgebraicGroup K]
    (sigma : AlgebraicGroup.Morphism K K) (B : ClosedSubgroup K) :
    borelLangImage sigma B = borelLangFactorizationImage sigma B := by
  ext y
  rw [borelLangImage_mem_iff]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, x⁻¹ * y * sigma.onPoints x, hx, ?_⟩
    rw [sigma.onPoints.map_inv]
    group
  · rintro ⟨x, b, hb, rfl⟩
    refine ⟨x, ?_⟩
    rw [sigma.onPoints.map_inv]
    simp [hb, mul_assoc]

/-! Context-specialized entry point used by the Lang factorization proof.  The
Steinberg and connectedness hypotheses belong to the surrounding argument.
Stability is retained explicitly because it is exactly what proves that the
Lang relation is right-`B`-saturated. -/

omit [IsAlgClosed k] in
public theorem invariantBorel_factorization_closedImage
    {K : Variety k} [AlgebraicGroup K]
    (sigma : AlgebraicGroup.Morphism K K)
    (_hSigma : IsAlgebraicSteinbergEndomorphism sigma)
    (_hK : Variety.IsConnected K)
    (B : ClosedSubgroup K)
    (_hB : IsBorelSubgroup B)
    (_hStable : ∀ x : Variety.Point B.carrierVariety,
      sigma.onPoints (B.inclusion.onPoints x) ∈ B.toSubgroup)
    {Q : Type v} [TopologicalSpace Q]
    (q : BorelCompleteQuotientWitness B Q) :
    IsClosed (borelLangFactorizationImage sigma B) := by
  rw [← borelLangImage_eq_factorizationImage sigma B]
  exact borelLangImage_isClosed_of_complete_quotient sigma B _hStable q

end Theory.AlgebraicGroup
