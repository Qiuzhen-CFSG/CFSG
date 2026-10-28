module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.EvenOrthogonalSpinCarrier
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.EvenSpinActionKernel
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.EvenSpinDerivedRange
public import Theory.AlgebraicGroup.RootSystems.EvenOrthogonalCarrier
public import Theory.AlgebraicGroup.Bor1.ConjugationRational
public import Theory.AlgebraicGroup.Representations.Algebraic.Natural
public import Theory.AlgebraicGroup.Representations.RationalBasis
public import Theory.AlgebraicGroup.Morphism.ClosedImage

/-!
# The split even Spin-to-Omega isogeny

This module adapts the left-regular conjugation argument used by the odd Spin
isogeny to the characteristic-free split carrier.  It constructs the
regular action on the quadratic space, restricts it to its exact closed image,
and identifies that image with the commutator subgroup of the full quadratic-
isometry group in split rank at least four.  It also proves surjectivity,
finiteness of the kernel, and the exact point formula for the resulting
isogeny.

Mathematically this is the classical Spin-to-Omega cover for split
nondegenerate quadratic spaces of dimension at least eight: the split witness
identifies the dimension with twice its hyperbolic rank.  Regularity is proved
by restricting Clifford-conjugation matrix coefficients to the embedded
vector space.  The image calculation uses the characteristic-free split
Cartan--Dieudonne and Dickson-parity results, while scalar centralizer rigidity
gives the finite kernel.  The final point formulas use the exact closed Spin
and quadratic-isometry carrier equivalences required by the concrete
even-orthogonal model.
-/

universe u

open CliffordAlgebra MulAction

namespace Theory.AlgebraicGroup

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {k V : Type u} [Field k] [IsAlgClosed k]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable (Q : QuadraticForm k V)

private noncomputable def evenSpinCarrierRepresentation
    (s : SplitQuadraticForm Q) :
    let S := splitSpinClosedSubgroup s
    letI := S.carrierAlgebraicGroup
    RationalRepresentation S.carrierVariety (CliffordAlgebra Q) := by
  let _ : Module.Finite k (CliffordAlgebra Q) := s.moduleFinite
  let S := splitSpinClosedSubgroup s
  letI := S.carrierAlgebraicGroup
  exact ⟨
    (LinearMap.GeneralLinearGroup.generalLinearEquiv k
        (CliffordAlgebra Q)).symm.toMonoidHom.comp
      ((Units.mulLeftLinearEquiv k (CliffordAlgebra Q)).comp
        (spinGroup.toUnits.comp
          (splitSpinClosedSubgroupPoints s).toMonoidHom))⟩

private lemma evenSpinCarrierRepresentation_action
    (s : SplitQuadraticForm Q) :
    let S := splitSpinClosedSubgroup s
    letI := S.carrierAlgebraicGroup
    ∀ g,
      LinearMap.GeneralLinearGroup.generalLinearEquiv k (CliffordAlgebra Q)
          ((evenSpinCarrierRepresentation Q s).action g) =
        (spinGroup.toUnits (splitSpinClosedSubgroupPoints s g)).mulLeftLinearEquiv
          k (CliffordAlgebra Q) := by
  dsimp only
  intro g
  exact (LinearMap.GeneralLinearGroup.generalLinearEquiv k
    (CliffordAlgebra Q)).apply_symm_apply _

private lemma evenSpinCarrierRepresentation_isRational
    (s : SplitQuadraticForm Q) :
    let S := splitSpinClosedSubgroup s
    letI := S.carrierAlgebraicGroup
    IsRationalRepresentation (evenSpinCarrierRepresentation Q s) := by
  dsimp only
  let _ : Module.Finite k (CliffordAlgebra Q) := s.moduleFinite
  let e := splitSpinCliffordBasis s
  refine ⟨e, (splitSpinClosedSubgroup s).inclusion, ?_⟩
  intro g
  apply (LinearMap.GeneralLinearGroup.generalLinearEquiv k
    (CliffordAlgebra Q)).injective
  rw [evenSpinCarrierRepresentation_action Q s]
  exact splitSpinClosedSubgroup_linear_points s g

private def cliffordVectorLeftEmbedding :
    V →ₗ[k] Module.End k (CliffordAlgebra Q) :=
  (Algebra.lmul k (CliffordAlgebra Q)).toLinearMap.comp (CliffordAlgebra.ι Q)

private lemma cliffordVectorLeftEmbedding_injective
    (s : SplitQuadraticForm Q) :
    Function.Injective (cliffordVectorLeftEmbedding Q) := by
  intro v w hvw
  apply CliffordAlgebra.ι_injective_of_actionForm Q s.actionForm
  have h := LinearMap.congr_fun hvw 1
  simpa [cliffordVectorLeftEmbedding] using h

private noncomputable def cliffordVectorLeftEquivRange
    (s : SplitQuadraticForm Q) :
    V ≃ₗ[k] LinearMap.range (cliffordVectorLeftEmbedding Q) :=
  LinearEquiv.ofInjective (cliffordVectorLeftEmbedding Q)
    (cliffordVectorLeftEmbedding_injective Q s)

private noncomputable def cliffordVectorLeftBasis
    (s : SplitQuadraticForm Q) :
    Module.Basis (Fin (Module.finrank k V)) k
      (LinearMap.range (cliffordVectorLeftEmbedding Q)) :=
  (Module.finBasis k V).map (cliffordVectorLeftEquivRange Q s)

private noncomputable def evenSpinCarrierAction
    (s : SplitQuadraticForm Q) :
    let S := splitSpinClosedSubgroup s
    letI := S.carrierAlgebraicGroup
    Variety.Point S.carrierVariety →* LinearMap.GeneralLinearGroup k V := by
  let _ : Module.Finite k (CliffordAlgebra Q) := s.moduleFinite
  let S := splitSpinClosedSubgroup s
  letI := S.carrierAlgebraicGroup
  exact
    (LinearMap.GeneralLinearGroup.generalLinearEquiv k V).symm.toMonoidHom.comp
      ((quadraticIsometrySubgroup Q).subtype.comp
        ((cliffordSpinActionOfSplit Q s).comp
          (splitSpinClosedSubgroupPoints s).toMonoidHom))

private lemma evenSpinCarrierAction_linearEquiv
    (s : SplitQuadraticForm Q) :
    let S := splitSpinClosedSubgroup s
    letI := S.carrierAlgebraicGroup
    ∀ g,
      LinearMap.GeneralLinearGroup.generalLinearEquiv k V
          (evenSpinCarrierAction Q s g) =
        (cliffordSpinActionOfSplit Q s
          (splitSpinClosedSubgroupPoints s g)).1 := by
  dsimp only
  intro g
  exact (LinearMap.GeneralLinearGroup.generalLinearEquiv k V).apply_symm_apply _

private lemma evenSpinCarrier_conj_vectorLeft
    (s : SplitQuadraticForm Q) :
    let S := splitSpinClosedSubgroup s
    letI := S.carrierAlgebraicGroup
    ∀ g v,
      Bor1.conjEndLinearMap
          ((evenSpinCarrierRepresentation Q s).action g)
          (cliffordVectorLeftEmbedding Q v) =
        cliffordVectorLeftEmbedding Q
          ((evenSpinCarrierAction Q s g : Module.End k V) v) := by
  dsimp only
  intro g v
  let x := splitSpinClosedSubgroupPoints s g
  have hleft := evenSpinCarrierRepresentation_action Q s g
  have haction := evenSpinCarrierAction_linearEquiv Q s g
  have hleftGL :
      (evenSpinCarrierRepresentation Q s).action g =
        (LinearMap.GeneralLinearGroup.generalLinearEquiv k
          (CliffordAlgebra Q)).symm
            ((spinGroup.toUnits x).mulLeftLinearEquiv k (CliffordAlgebra Q)) := by
    apply (LinearMap.GeneralLinearGroup.generalLinearEquiv k
      (CliffordAlgebra Q)).injective
    simpa using hleft
  apply LinearMap.ext
  intro z
  change
    ((evenSpinCarrierRepresentation Q s).action g :
        Module.End k (CliffordAlgebra Q))
      (CliffordAlgebra.ι Q v *
        (↑(((evenSpinCarrierRepresentation Q s).action g)⁻¹) :
          Module.End k (CliffordAlgebra Q)) z) =
      CliffordAlgebra.ι Q ((evenSpinCarrierAction Q s g :
        Module.End k V) v) * z
  rw [hleftGL]
  change (x : CliffordAlgebra Q) *
      (CliffordAlgebra.ι Q v *
        ((↑((spinGroup.toUnits x)⁻¹) : CliffordAlgebra Q) * z)) = _
  rw [← mul_assoc, ← mul_assoc]
  rw [← cliffordSpinActionOfSplit_spec Q s x v]
  rw [← haction]
  rfl

private noncomputable def evenSpinCarrierRationalRepresentation
    (s : SplitQuadraticForm Q) :
    let S := splitSpinClosedSubgroup s
    letI := S.carrierAlgebraicGroup
    RationalRepresentation S.carrierVariety V := by
  let _ : Module.Finite k (CliffordAlgebra Q) := s.moduleFinite
  let S := splitSpinClosedSubgroup s
  letI := S.carrierAlgebraicGroup
  exact ⟨evenSpinCarrierAction Q s⟩

private theorem evenSpinCarrierRationalRepresentation_isRational
    (s : SplitQuadraticForm Q) :
    let S := splitSpinClosedSubgroup s
    letI := S.carrierAlgebraicGroup
    IsRationalRepresentation
      (evenSpinCarrierRationalRepresentation Q s) := by
  let _ : Module.Finite k (CliffordAlgebra Q) := s.moduleFinite
  let S := splitSpinClosedSubgroup s
  letI := S.carrierAlgebraicGroup
  let b := Module.finBasis k V
  let e := splitSpinCliffordBasis s
  let ρ := evenSpinCarrierRepresentation Q s
  let σ := Bor1.conjEndRationalRepresentation ρ
  obtain ⟨c, f, hf⟩ := Bor1.conjEndRationalRepresentation_isRational ρ
    (evenSpinCarrierRepresentation_isRational Q s)
  let U := LinearMap.range (cliffordVectorLeftEmbedding Q)
  let cU := cliffordVectorLeftBasis Q s
  let matrixCoefficient : Fin (Module.finrank k V) →
      Fin (Module.finrank k V) → S.carrierVariety.PolynomialFunction := fun i j =>
    rationalRepresentationLinearMatrixCoefficient σ c f
      (Subspace.dualLift U (cU.dualBasis i))
      (cU j : Module.End k (CliffordAlgebra Q))
  have matrixCoefficient_apply : ∀ i j g,
      matrixCoefficient i j g =
        b.repr (((evenSpinCarrierAction Q s g : Module.End k V)) (b j)) i := by
    intro i j g
    rw [show matrixCoefficient i j =
      rationalRepresentationLinearMatrixCoefficient σ c f
        (Subspace.dualLift U (cU.dualBasis i))
          (cU j : Module.End k (CliffordAlgebra Q)) by rfl]
    rw [rationalRepresentationLinearMatrixCoefficient_apply σ c f hf]
    change (Subspace.dualLift U (cU.dualBasis i))
      (Bor1.conjEndLinearMap (ρ.action g)
        (cU j : Module.End k (CliffordAlgebra Q))) = _
    have hcUj : (cU j : Module.End k (CliffordAlgebra Q)) =
        cliffordVectorLeftEmbedding Q (b j) := by
      rw [show cU = cliffordVectorLeftBasis Q s by rfl,
        cliffordVectorLeftBasis, Module.Basis.map_apply]
      rfl
    rw [hcUj]
    rw [show ρ = evenSpinCarrierRepresentation Q s by rfl]
    rw [evenSpinCarrier_conj_vectorLeft Q s]
    let y : U := cliffordVectorLeftEquivRange Q s
      ((evenSpinCarrierAction Q s g : Module.End k V) (b j))
    change (Subspace.dualLift U (cU.dualBasis i))
      (y : Module.End k (CliffordAlgebra Q)) = _
    rw [Subspace.dualLift_of_subtype]
    rw [Module.Basis.dualBasis_apply]
    rw [show cU = cliffordVectorLeftBasis Q s by rfl,
      cliffordVectorLeftBasis, Module.Basis.map_repr]
    simp [y, cliffordVectorLeftEquivRange]
    rfl
  let inverseMatrixCoefficient : Fin (Module.finrank k V) →
      Fin (Module.finrank k V) → S.carrierVariety.PolynomialFunction := fun i j =>
    Variety.PolynomialFunction.pullback (AlgebraicGroup.invMorphism S.carrierVariety)
      (matrixCoefficient i j)
  have inverseMatrixCoefficient_apply : ∀ i j g,
      inverseMatrixCoefficient i j g =
        b.repr (((((evenSpinCarrierAction Q s g)⁻¹ :
          LinearMap.GeneralLinearGroup k V) : Module.End k V)) (b j)) i := by
    intro i j g
    change matrixCoefficient i j g⁻¹ = _
    rw [matrixCoefficient_apply]
    simp
  let F := generalLinearRepresentationMorphismOfInverseMatrixCoefficient b
    (evenSpinCarrierAction Q s) matrixCoefficient inverseMatrixCoefficient
      matrixCoefficient_apply inverseMatrixCoefficient_apply
  refine ⟨b, F, ?_⟩
  intro g
  change glPointEquivOf k V b
    (generalLinearRepresentationPoint b (evenSpinCarrierAction Q s g)) = _
  exact glPointEquivOf_generalLinearRepresentationPoint b _

public noncomputable def evenSpinAmbientActionMorphism
    (s : SplitQuadraticForm Q) :
    let S := splitSpinClosedSubgroup s
    letI := S.carrierAlgebraicGroup
    AlgebraicGroup.Morphism S.carrierVariety (glVarietyOf k V) := by
  let _ : Module.Finite k (CliffordAlgebra Q) := s.moduleFinite
  let S := splitSpinClosedSubgroup s
  letI := S.carrierAlgebraicGroup
  exact Classical.choose
    (IsRationalRepresentation.exists_morphism_in_basis
      (evenSpinCarrierRationalRepresentation_isRational Q s) (Module.finBasis k V))

private lemma evenSpinAmbientActionMorphism_points
    (s : SplitQuadraticForm Q) :
    let S := splitSpinClosedSubgroup s
    letI := S.carrierAlgebraicGroup
    ∀ g,
      glPointEquivOf k V (Module.finBasis k V)
          ((evenSpinAmbientActionMorphism Q s).onPoints g) =
        evenSpinCarrierAction Q s g := by
  dsimp only
  intro g
  exact (Classical.choose_spec
    (IsRationalRepresentation.exists_morphism_in_basis
      (evenSpinCarrierRationalRepresentation_isRational Q s)
        (Module.finBasis k V))) g

/-- The regular ambient action is the split Clifford action on every point. -/
public theorem evenSpinAmbientActionMorphism_linear_points
    (s : SplitQuadraticForm Q) :
    let S := splitSpinClosedSubgroup s
    letI := S.carrierAlgebraicGroup
    ∀ g,
      LinearMap.GeneralLinearGroup.generalLinearEquiv k V
          (glPointEquivOf k V (Module.finBasis k V)
            ((evenSpinAmbientActionMorphism Q s).onPoints g)) =
        (cliffordSpinActionOfSplit Q s
          (splitSpinClosedSubgroupPoints s g)).1 := by
  dsimp only
  intro g
  rw [evenSpinAmbientActionMorphism_points Q s]
  exact evenSpinCarrierAction_linearEquiv Q s g

public noncomputable def evenSpinActionImageClosedSubgroup
    (s : SplitQuadraticForm Q) :
    let S := splitSpinClosedSubgroup s
    letI := S.carrierAlgebraicGroup
    ClosedSubgroup (glVarietyOf k V) :=
  (evenSpinAmbientActionMorphism Q s).imageClosedSubgroup

/-- Membership in the closed action image is exactly realization by a Spin
point, expressed through the ambient linear inclusion. -/
public theorem evenSpinActionImageClosedSubgroup_carrier
    (s : SplitQuadraticForm Q) :
    let S := splitSpinClosedSubgroup s
    let I := evenSpinActionImageClosedSubgroup Q s
    letI := S.carrierAlgebraicGroup
    ∀ g, g ∈ I.toSubgroup ↔ ∃ x : spinGroup Q,
      (cliffordSpinActionOfSplit Q s x).1 =
        LinearMap.GeneralLinearGroup.generalLinearEquiv k V
          (glPointEquivOf k V (Module.finBasis k V) g) := by
  dsimp only
  intro g
  let _ : Module.Finite k (CliffordAlgebra Q) := s.moduleFinite
  unfold evenSpinActionImageClosedSubgroup
  change (∃ p, (evenSpinAmbientActionMorphism Q s).onPoints p = g) ↔ _
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨splitSpinClosedSubgroupPoints s p, ?_⟩
    exact (evenSpinAmbientActionMorphism_linear_points Q s p).symm
  · rintro ⟨x, hx⟩
    refine ⟨(splitSpinClosedSubgroupPoints s).symm x, ?_⟩
    apply (glPointEquivOf k V (Module.finBasis k V)).injective
    apply (LinearMap.GeneralLinearGroup.generalLinearEquiv k V).injective
    rw [evenSpinAmbientActionMorphism_linear_points Q s]
    rw [(splitSpinClosedSubgroupPoints s).apply_symm_apply]
    exact hx

/-- In split rank at least four, the closed action image is precisely the
ambient carrier of the derived quadratic-isometry group. -/
public theorem evenSpinActionImageClosedSubgroup_commutator_carrier
    (s : SplitQuadraticForm Q) (hrank : 4 ≤ s.rank) :
    let S := splitSpinClosedSubgroup s
    let I := evenSpinActionImageClosedSubgroup Q s
    letI := S.carrierAlgebraicGroup
    ∀ g, g ∈ I.toSubgroup ↔
      ∃ x : commutator (quadraticIsometrySubgroup Q),
        x.1.1 = LinearMap.GeneralLinearGroup.generalLinearEquiv k V
          (glPointEquivOf k V (Module.finBasis k V) g) := by
  dsimp only
  intro g
  rw [evenSpinActionImageClosedSubgroup_carrier Q s]
  constructor
  · rintro ⟨x, hx⟩
    have hmem : cliffordSpinActionOfSplit Q s x ∈
        commutator (quadraticIsometrySubgroup Q) := by
      rw [← cliffordSpinActionOfSplit_range_eq_commutator s hrank]
      exact ⟨x, rfl⟩
    exact ⟨⟨cliffordSpinActionOfSplit Q s x, hmem⟩, hx⟩
  · rintro ⟨y, hy⟩
    have hymem : y.1 ∈ (cliffordSpinActionOfSplit Q s).range := by
      rw [cliffordSpinActionOfSplit_range_eq_commutator s hrank]
      exact y.2
    obtain ⟨x, hx⟩ := hymem
    refine ⟨x, ?_⟩
    exact (congrArg Subtype.val hx).trans hy

public theorem evenSpinAmbientActionMorphism_mem_image
    (s : SplitQuadraticForm Q) :
    let S := splitSpinClosedSubgroup s
    let I := evenSpinActionImageClosedSubgroup Q s
    letI := S.carrierAlgebraicGroup
    ∀ g, (evenSpinAmbientActionMorphism Q s).onPoints g ∈ I.toSubgroup := by
  dsimp only
  intro g
  unfold evenSpinActionImageClosedSubgroup
  change (evenSpinAmbientActionMorphism Q s).onPoints g ∈
    (evenSpinAmbientActionMorphism Q s).image
  exact ⟨g, rfl⟩

public noncomputable def evenSpinActionImageCover
    (s : SplitQuadraticForm Q) :
    let S := splitSpinClosedSubgroup s
    let I := evenSpinActionImageClosedSubgroup Q s
    letI := S.carrierAlgebraicGroup
    letI := I.carrierAlgebraicGroup
    AlgebraicGroup.Morphism S.carrierVariety I.carrierVariety := by
  let _ : Module.Finite k (CliffordAlgebra Q) := s.moduleFinite
  let S := splitSpinClosedSubgroup s
  let I := evenSpinActionImageClosedSubgroup Q s
  letI := S.carrierAlgebraicGroup
  letI := I.carrierAlgebraicGroup
  exact (evenSpinAmbientActionMorphism Q s).codRestrictClosedSubgroup I
    (evenSpinAmbientActionMorphism_mem_image Q s)

public theorem evenSpinActionImageCover_surjective
    (s : SplitQuadraticForm Q) :
    let S := splitSpinClosedSubgroup s
    let I := evenSpinActionImageClosedSubgroup Q s
    letI := S.carrierAlgebraicGroup
    letI := I.carrierAlgebraicGroup
    Function.Surjective (evenSpinActionImageCover Q s).onPoints := by
  dsimp only
  exact (evenSpinAmbientActionMorphism Q s).codRestrictImageClosedSubgroup_surjective
    (evenSpinAmbientActionMorphism_mem_image Q s)

/-- The ambient linear inclusion of the closed-image cover is the Clifford
action. -/
public theorem evenSpinActionImageCover_linear_points
    (s : SplitQuadraticForm Q) :
    let S := splitSpinClosedSubgroup s
    let I := evenSpinActionImageClosedSubgroup Q s
    letI := S.carrierAlgebraicGroup
    letI := I.carrierAlgebraicGroup
    ∀ g,
      LinearMap.GeneralLinearGroup.generalLinearEquiv k V
          (glPointEquivOf k V (Module.finBasis k V)
            (I.inclusion.onPoints ((evenSpinActionImageCover Q s).onPoints g))) =
        (cliffordSpinActionOfSplit Q s
          (splitSpinClosedSubgroupPoints s g)).1 := by
  dsimp only
  intro g
  rw [evenSpinActionImageCover]
  rw [Morphism.codRestrictClosedSubgroup_inclusion_apply
    (hmap := evenSpinAmbientActionMorphism_mem_image Q s)]
  exact evenSpinAmbientActionMorphism_linear_points Q s g

private noncomputable def evenSpinActionImageToQuadraticHom
    (s : SplitQuadraticForm Q) :
    let S := splitSpinClosedSubgroup s
    let I := evenSpinActionImageClosedSubgroup Q s
    let H := quadraticIsometryClosedSubgroup Q (Module.finBasis k V)
    letI := S.carrierAlgebraicGroup
    letI := I.carrierAlgebraicGroup
    letI := H.carrierAlgebraicGroup
    I.toSubgroup →* quadraticIsometrySubgroup Q := by
  let _ : Module.Finite k (CliffordAlgebra Q) := s.moduleFinite
  let S := splitSpinClosedSubgroup s
  let I := evenSpinActionImageClosedSubgroup Q s
  let H := quadraticIsometryClosedSubgroup Q (Module.finBasis k V)
  letI := S.carrierAlgebraicGroup
  letI := I.carrierAlgebraicGroup
  letI := H.carrierAlgebraicGroup
  let pointEquiv : Variety.Point H.carrierVariety ≃* H.toSubgroup :=
    { toEquiv := H.pointEquiv
      map_mul' := fun _ _ => rfl }
  let toQuadraticCarrier : I.toSubgroup →* H.toSubgroup :=
    { toFun := fun x => ⟨x.1, by
        rw [quadraticIsometryClosedSubgroup_carrier]
        obtain ⟨a, ha⟩ :=
          (evenSpinActionImageClosedSubgroup_carrier Q s x.1).mp x.2
        rw [← ha]
        exact (cliffordSpinActionOfSplit Q s a).2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact (quadraticIsometryClosedSubgroupPoints Q (Module.finBasis k V)).toMonoidHom.comp
    (pointEquiv.symm.toMonoidHom.comp toQuadraticCarrier)

private theorem evenSpinActionImageToQuadraticHom_linear_points
    (s : SplitQuadraticForm Q) :
    let S := splitSpinClosedSubgroup s
    let I := evenSpinActionImageClosedSubgroup Q s
    letI := S.carrierAlgebraicGroup
    letI := I.carrierAlgebraicGroup
    ∀ x,
      (evenSpinActionImageToQuadraticHom Q s x).1 =
        LinearMap.GeneralLinearGroup.generalLinearEquiv k V
          (glPointEquivOf k V (Module.finBasis k V) x.1) := by
  dsimp only
  intro x
  let _ : Module.Finite k (CliffordAlgebra Q) := s.moduleFinite
  let S := splitSpinClosedSubgroup s
  let I := evenSpinActionImageClosedSubgroup Q s
  let H := quadraticIsometryClosedSubgroup Q (Module.finBasis k V)
  letI := S.carrierAlgebraicGroup
  letI := I.carrierAlgebraicGroup
  letI := H.carrierAlgebraicGroup
  let pointEquiv : Variety.Point H.carrierVariety ≃* H.toSubgroup :=
    { toEquiv := H.pointEquiv
      map_mul' := fun _ _ => rfl }
  let toQuadraticCarrier : I.toSubgroup →* H.toSubgroup :=
    { toFun := fun z => ⟨z.1, by
        rw [quadraticIsometryClosedSubgroup_carrier]
        obtain ⟨a, ha⟩ :=
          (evenSpinActionImageClosedSubgroup_carrier Q s z.1).mp z.2
        rw [← ha]
        exact (cliffordSpinActionOfSplit Q s a).2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let p := pointEquiv.symm (toQuadraticCarrier x)
  have hp : H.inclusion.onPoints p = x.1 := by
    have h := congrArg Subtype.val
      (pointEquiv.apply_symm_apply (toQuadraticCarrier x))
    exact h
  have hlinear := quadraticIsometryClosedSubgroup_linear_points Q
    (Module.finBasis k V) p
  rw [hp] at hlinear
  change (quadraticIsometryClosedSubgroupPoints Q (Module.finBasis k V) p).1 = _
  exact hlinear.symm

private noncomputable def evenSpinActionImageToCommutatorHom
    (s : SplitQuadraticForm Q) (hrank : 4 ≤ s.rank) :
    let S := splitSpinClosedSubgroup s
    let I := evenSpinActionImageClosedSubgroup Q s
    letI := S.carrierAlgebraicGroup
    letI := I.carrierAlgebraicGroup
    I.toSubgroup →* commutator (quadraticIsometrySubgroup Q) := by
  let _ : Module.Finite k (CliffordAlgebra Q) := s.moduleFinite
  let S := splitSpinClosedSubgroup s
  let I := evenSpinActionImageClosedSubgroup Q s
  letI := S.carrierAlgebraicGroup
  letI := I.carrierAlgebraicGroup
  exact (evenSpinActionImageToQuadraticHom Q s).codRestrict
    (commutator (quadraticIsometrySubgroup Q)) fun x => by
      rw [← cliffordSpinActionOfSplit_range_eq_commutator s hrank]
      obtain ⟨a, ha⟩ :=
        (evenSpinActionImageClosedSubgroup_carrier Q s x.1).mp x.2
      refine ⟨a, ?_⟩
      apply Subtype.ext
      exact ha.trans (evenSpinActionImageToQuadraticHom_linear_points Q s x).symm

private theorem evenSpinActionImageToCommutatorHom_linear_points
    (s : SplitQuadraticForm Q) (hrank : 4 ≤ s.rank) :
    let S := splitSpinClosedSubgroup s
    let I := evenSpinActionImageClosedSubgroup Q s
    letI := S.carrierAlgebraicGroup
    letI := I.carrierAlgebraicGroup
    ∀ x,
      (evenSpinActionImageToCommutatorHom Q s hrank x).1.1 =
        LinearMap.GeneralLinearGroup.generalLinearEquiv k V
          (glPointEquivOf k V (Module.finBasis k V) x.1) := by
  dsimp only
  intro x
  exact evenSpinActionImageToQuadraticHom_linear_points Q s x

private theorem evenSpinActionImageToCommutatorHom_injective
    (s : SplitQuadraticForm Q) (hrank : 4 ≤ s.rank) :
    let S := splitSpinClosedSubgroup s
    let I := evenSpinActionImageClosedSubgroup Q s
    letI := S.carrierAlgebraicGroup
    letI := I.carrierAlgebraicGroup
    Function.Injective (evenSpinActionImageToCommutatorHom Q s hrank) := by
  dsimp only
  intro x y hxy
  apply Subtype.ext
  apply (glPointEquivOf k V (Module.finBasis k V)).injective
  apply (LinearMap.GeneralLinearGroup.generalLinearEquiv k V).injective
  calc
    LinearMap.GeneralLinearGroup.generalLinearEquiv k V
          (glPointEquivOf k V (Module.finBasis k V) x.1) =
        (evenSpinActionImageToCommutatorHom Q s hrank x).1.1 :=
      (evenSpinActionImageToCommutatorHom_linear_points Q s hrank x).symm
    _ = (evenSpinActionImageToCommutatorHom Q s hrank y).1.1 :=
      congrArg (fun z => z.1.1) hxy
    _ = LinearMap.GeneralLinearGroup.generalLinearEquiv k V
          (glPointEquivOf k V (Module.finBasis k V) y.1) :=
      evenSpinActionImageToCommutatorHom_linear_points Q s hrank y

private theorem evenSpinActionImageToCommutatorHom_surjective
    (s : SplitQuadraticForm Q) (hrank : 4 ≤ s.rank) :
    let S := splitSpinClosedSubgroup s
    let I := evenSpinActionImageClosedSubgroup Q s
    letI := S.carrierAlgebraicGroup
    letI := I.carrierAlgebraicGroup
    Function.Surjective (evenSpinActionImageToCommutatorHom Q s hrank) := by
  dsimp only
  intro y
  have hymem : y.1 ∈ (cliffordSpinActionOfSplit Q s).range := by
    rw [cliffordSpinActionOfSplit_range_eq_commutator s hrank]
    exact y.2
  obtain ⟨a, ha⟩ := hymem
  let g := (evenSpinActionImageCover Q s).onPoints
    ((splitSpinClosedSubgroupPoints s).symm a)
  let x : (evenSpinActionImageClosedSubgroup Q s).toSubgroup :=
    (evenSpinActionImageClosedSubgroup Q s).pointEquiv g
  refine ⟨x, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  rw [evenSpinActionImageToCommutatorHom_linear_points Q s hrank]
  have hcover := evenSpinActionImageCover_linear_points Q s
    ((splitSpinClosedSubgroupPoints s).symm a)
  rw [(splitSpinClosedSubgroupPoints s).apply_symm_apply] at hcover
  have hxval : x.1 =
      (evenSpinActionImageClosedSubgroup Q s).inclusion.onPoints g := by
    apply Variety.Point.ext
    calc
      x.1.val = g.val := by
        exact (evenSpinActionImageClosedSubgroup Q s).pointEquiv_val g
      _ = ((evenSpinActionImageClosedSubgroup Q s).inclusion.onPoints g).val := by
        rfl
  calc
    LinearMap.GeneralLinearGroup.generalLinearEquiv k V
          (glPointEquivOf k V (Module.finBasis k V) x.1) =
        (cliffordSpinActionOfSplit Q s a).1 := by
      rw [hxval]
      exact hcover
    _ = y.1.1 := congrArg Subtype.val ha

/-- Points of the closed action image are canonically the derived subgroup of
the full quadratic-isometry group. -/
public noncomputable def evenSpinActionImageClosedSubgroupPoints
    (s : SplitQuadraticForm Q) (hrank : 4 ≤ s.rank) :
    let S := splitSpinClosedSubgroup s
    let I := evenSpinActionImageClosedSubgroup Q s
    letI := S.carrierAlgebraicGroup
    letI := I.carrierAlgebraicGroup
    Variety.Point I.carrierVariety ≃*
      commutator (quadraticIsometrySubgroup Q) := by
  let _ : Module.Finite k (CliffordAlgebra Q) := s.moduleFinite
  let S := splitSpinClosedSubgroup s
  let I := evenSpinActionImageClosedSubgroup Q s
  letI := S.carrierAlgebraicGroup
  letI := I.carrierAlgebraicGroup
  let pointEquiv : Variety.Point I.carrierVariety ≃* I.toSubgroup :=
    { toEquiv := I.pointEquiv
      map_mul' := fun _ _ => rfl }
  exact pointEquiv.trans <| MulEquiv.ofBijective
    (evenSpinActionImageToCommutatorHom Q s hrank)
    ⟨evenSpinActionImageToCommutatorHom_injective Q s hrank,
      evenSpinActionImageToCommutatorHom_surjective Q s hrank⟩

/-- The image-carrier point equivalence is the ambient linear inclusion. -/
public theorem evenSpinActionImageClosedSubgroup_linear_points
    (s : SplitQuadraticForm Q) (hrank : 4 ≤ s.rank) :
    let S := splitSpinClosedSubgroup s
    let I := evenSpinActionImageClosedSubgroup Q s
    letI := S.carrierAlgebraicGroup
    letI := I.carrierAlgebraicGroup
    ∀ x,
      LinearMap.GeneralLinearGroup.generalLinearEquiv k V
          (glPointEquivOf k V (Module.finBasis k V)
            (I.inclusion.onPoints x)) =
        (evenSpinActionImageClosedSubgroupPoints Q s hrank x).1.1 := by
  dsimp only
  intro x
  exact (evenSpinActionImageToCommutatorHom_linear_points Q s hrank
    ((evenSpinActionImageClosedSubgroup Q s).pointEquiv x)).symm

/-- Under the Spin and derived-isometry point equivalences, the algebraic
cover is exactly Clifford conjugation. -/
public theorem evenSpinActionImageCover_points
    (s : SplitQuadraticForm Q) (hrank : 4 ≤ s.rank) :
    let S := splitSpinClosedSubgroup s
    let I := evenSpinActionImageClosedSubgroup Q s
    letI := S.carrierAlgebraicGroup
    letI := I.carrierAlgebraicGroup
    ∀ g,
      (evenSpinActionImageClosedSubgroupPoints Q s hrank
        ((evenSpinActionImageCover Q s).onPoints g)).1 =
          cliffordSpinActionOfSplit Q s
            (splitSpinClosedSubgroupPoints s g) := by
  dsimp only
  intro g
  apply Subtype.ext
  rw [← evenSpinActionImageClosedSubgroup_linear_points Q s hrank]
  exact evenSpinActionImageCover_linear_points Q s g

/-- The cover is surjective onto the derived quadratic-isometry group under
the canonical point equivalence. -/
public theorem evenSpinActionImageCover_commutator_surjective
    (s : SplitQuadraticForm Q) (hrank : 4 ≤ s.rank) :
    let S := splitSpinClosedSubgroup s
    let I := evenSpinActionImageClosedSubgroup Q s
    letI := S.carrierAlgebraicGroup
    letI := I.carrierAlgebraicGroup
    Function.Surjective (fun g =>
      evenSpinActionImageClosedSubgroupPoints Q s hrank
        ((evenSpinActionImageCover Q s).onPoints g)) := by
  dsimp only
  exact (evenSpinActionImageClosedSubgroupPoints Q s hrank).surjective.comp
    (evenSpinActionImageCover_surjective Q s)

/-- Model-facing point formula for the algebraic Spin cover. -/
public theorem evenSpinActionImageCover_spin_points
    (s : SplitQuadraticForm Q) (hrank : 4 ≤ s.rank) :
    let S := splitSpinClosedSubgroup s
    let I := evenSpinActionImageClosedSubgroup Q s
    letI := S.carrierAlgebraicGroup
    letI := I.carrierAlgebraicGroup
    ∀ x,
      (evenSpinActionImageClosedSubgroupPoints Q s hrank
        ((evenSpinActionImageCover Q s).onPoints
          ((splitSpinClosedSubgroupPoints s).symm x))).1 =
            cliffordSpinActionOfSplit Q s x := by
  dsimp only
  intro x
  rw [evenSpinActionImageCover_points Q s hrank]
  rw [(splitSpinClosedSubgroupPoints s).apply_symm_apply]

private theorem ambientLinearPoint_one
    (s : SplitQuadraticForm Q) :
    LinearMap.GeneralLinearGroup.generalLinearEquiv k V
        (glPointEquivOf k V (Module.finBasis k V)
          (1 : Variety.Point (glVarietyOf k V))) = 1 := by
  let _ : Module.Finite k (CliffordAlgebra Q) := s.moduleFinite
  let S := splitSpinClosedSubgroup s
  letI := S.carrierAlgebraicGroup
  have h := evenSpinAmbientActionMorphism_linear_points Q s
    (1 : Variety.Point S.carrierVariety)
  simpa using h

/-- The point kernel of the regular Spin action onto its closed image is
finite. -/
public theorem evenSpinActionImageCover_kernel_finite
    (s : SplitQuadraticForm Q) :
    let S := splitSpinClosedSubgroup s
    let I := evenSpinActionImageClosedSubgroup Q s
    letI := S.carrierAlgebraicGroup
    letI := I.carrierAlgebraicGroup
    Finite (evenSpinActionImageCover Q s).kernel := by
  dsimp only
  let _ : Module.Finite k (CliffordAlgebra Q) := s.moduleFinite
  let S := splitSpinClosedSubgroup s
  let I := evenSpinActionImageClosedSubgroup Q s
  letI := S.carrierAlgebraicGroup
  letI := I.carrierAlgebraicGroup
  let A := cliffordSpinActionOfSplit Q s
  have hA : A = cliffordSpinAction Q s.actionForm := by
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    apply CliffordAlgebra.ι_injective_of_actionForm Q s.actionForm
    rw [cliffordSpinActionOfSplit_spec, cliffordSpinAction_spec]
  have hker : Set.Finite (A.ker : Set (spinGroup Q)) := by
    rw [hA]
    exact cliffordSpinAction_ker_finite s
  letI : Finite A.ker := Set.finite_coe_iff.mpr hker
  let toActionKernel : (evenSpinActionImageCover Q s).kernel → A.ker :=
    fun z => ⟨splitSpinClosedSubgroupPoints s z.1, by
      apply MonoidHom.mem_ker.mpr
      have hz := MonoidHom.mem_ker.mp z.2
      have hz' := congrArg
        (fun y => LinearMap.GeneralLinearGroup.generalLinearEquiv k V
          (glPointEquivOf k V (Module.finBasis k V)
            (I.inclusion.onPoints y))) hz
      rw [evenSpinActionImageCover_linear_points Q s] at hz'
      apply Subtype.ext
      change (cliffordSpinActionOfSplit Q s
        (splitSpinClosedSubgroupPoints s z.1)).1 = (1 : V ≃ₗ[k] V)
      rw [hz']
      exact ambientLinearPoint_one Q s⟩
  exact Finite.of_injective toActionKernel fun a c hac => by
    apply Subtype.ext
    apply (splitSpinClosedSubgroupPoints s).injective
    exact congrArg Subtype.val hac

/-- The regular Spin action is an isogeny onto its exact closed image. -/
public theorem evenSpinActionImageCover_isIsogeny
    (s : SplitQuadraticForm Q) :
    let S := splitSpinClosedSubgroup s
    let I := evenSpinActionImageClosedSubgroup Q s
    letI := S.carrierAlgebraicGroup
    letI := I.carrierAlgebraicGroup
    IsIsogeny (evenSpinActionImageCover Q s) := by
  dsimp only
  exact ⟨evenSpinActionImageCover_surjective Q s,
    evenSpinActionImageCover_kernel_finite Q s⟩

end Theory.AlgebraicGroup
