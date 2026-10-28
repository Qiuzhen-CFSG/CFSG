module
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Theory.AlgebraicGroup.ClosedSubgroup.Invariant
public import Theory.AlgebraicGroup.RightTranslation.Chevalley

universe u v

set_option linter.style.haveILetI false

/-! The exterior-power representation and projective Plücker point attached to a closed subgroup. -/

namespace Theory.AlgebraicGroup

section

open scoped ExteriorAlgebra LinearAlgebra.Projectivization

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The exterior-power representation carrying the Chevalley Plücker vector. -/
@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingExteriorGeneralLinear
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Variety.Point G →*
      LinearMap.GeneralLinearGroup k
        (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
          H.rightTranslateVanishingSpan) :=
  (exteriorPowerGeneralLinear k H.rightTranslateVanishingSpan
    H.rightTranslateVanishingTopWedgeData.degree).comp
      H.rightTranslateVanishingSpanGeneralLinear

/-- The projective point represented by the nonzero Chevalley Plücker vector. -/
@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingPluckerPoint
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    ℙ k (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
      H.rightTranslateVanishingSpan) :=
  Projectivization.mk k H.rightTranslateVanishingPluckerVector
    H.rightTranslateVanishingPluckerVector_ne_zero

end

/-! The projective Chevalley Plücker point has stabilizer exactly the prescribed subgroup. -/

section
open scoped ExteriorAlgebra LinearAlgebra.Projectivization
variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
lemma ClosedSubgroup.chevalleyPluckerPoint_stabilizer
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    letI : MulAction (Variety.Point G)
      (ℙ k (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
        H.rightTranslateVanishingSpan)) :=
      MulAction.compHom _ H.rightTranslateVanishingExteriorGeneralLinear
    MulAction.stabilizer (Variety.Point G)
      H.rightTranslateVanishingPluckerPoint = H.toSubgroup := by
  letI : MulAction (Variety.Point G)
      (ℙ k (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
        H.rightTranslateVanishingSpan)) :=
    MulAction.compHom _ H.rightTranslateVanishingExteriorGeneralLinear
  ext g
  change g • H.rightTranslateVanishingPluckerPoint =
      H.rightTranslateVanishingPluckerPoint ↔ g ∈ H.toSubgroup
  rw [ClosedSubgroup.rightTranslateVanishingPluckerPoint]
  change H.rightTranslateVanishingExteriorGeneralLinear g •
      Projectivization.mk k H.rightTranslateVanishingPluckerVector _ =
        Projectivization.mk k H.rightTranslateVanishingPluckerVector _ ↔ _
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  change (∃ a : k, a • H.rightTranslateVanishingPluckerVector =
      exteriorPower.map H.rightTranslateVanishingTopWedgeData.degree
        (LinearMap.GeneralLinearGroup.toLinearEquiv
          (H.rightTranslateVanishingSpanGeneralLinear g)).toLinearMap
        H.rightTranslateVanishingPluckerVector) ↔ _
  rw [← Submodule.mem_span_singleton]
  exact H.chevalleyPluckerLine_stabilizer_iff g

end

/-! A normal point stabilizer is the kernel of the induced action on its orbit. -/

variable {G : Type u} [Group G]
variable {X : Type v} [MulAction G X]

lemma stabilizer_eq_ker_toPermHom_orbit_of_normal
    (x : X) (hN : (MulAction.stabilizer G x).Normal) :
    (MulAction.toPermHom G (MulAction.orbit G x)).ker =
      MulAction.stabilizer G x := by
  ext g
  constructor
  · intro hg
    change (MulAction.toPermHom G (MulAction.orbit G x)) g = 1 at hg
    have hbase := congrArg (fun σ : Equiv.Perm (MulAction.orbit G x) =>
      σ ⟨x, MulAction.mem_orbit_self x⟩) hg
    change g • x = x
    exact Subtype.ext_iff.mp hbase
  · intro hg
    change (MulAction.toPermHom G (MulAction.orbit G x)) g = 1
    apply Equiv.Perm.ext
    intro y
    obtain ⟨a, ha⟩ := y.2
    apply Subtype.ext
    change g • (y : X) = (y : X)
    rw [← ha]
    rw [← mul_smul]
    have hconj : a⁻¹ * g * a ∈ MulAction.stabilizer G x := by
      simpa [mul_assoc] using hN.conj_mem g hg a⁻¹
    have hfix : (a⁻¹ * g * a) • x = x := hconj
    calc
      (g * a) • x = (a * (a⁻¹ * g * a)) • x := by
        congr 1
        simp [mul_assoc]
      _ = a • ((a⁻¹ * g * a) • x) := by rw [mul_smul]
      _ = a • x := by rw [hfix]

/-! A normal closed subgroup is the exact kernel of the action on its Chevalley Plücker orbit. -/

section

open scoped ExteriorAlgebra LinearAlgebra.Projectivization

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
lemma ClosedSubgroup.chevalleyPluckerOrbitAction_ker
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal) :
    letI : MulAction (Variety.Point G)
      (ℙ k (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
        H.rightTranslateVanishingSpan)) :=
      MulAction.compHom _ H.rightTranslateVanishingExteriorGeneralLinear
    (MulAction.toPermHom (Variety.Point G)
      (MulAction.orbit (Variety.Point G)
        H.rightTranslateVanishingPluckerPoint)).ker = H.toSubgroup := by
  letI : MulAction (Variety.Point G)
      (ℙ k (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
        H.rightTranslateVanishingSpan)) :=
    MulAction.compHom _ H.rightTranslateVanishingExteriorGeneralLinear
  have hstab : MulAction.stabilizer (Variety.Point G)
      H.rightTranslateVanishingPluckerPoint = H.toSubgroup :=
    H.chevalleyPluckerPoint_stabilizer
  have hstabN : (MulAction.stabilizer (Variety.Point G)
      H.rightTranslateVanishingPluckerPoint).Normal := by
    rw [hstab]
    exact hN
  calc
    (MulAction.toPermHom (Variety.Point G)
      (MulAction.orbit (Variety.Point G)
        H.rightTranslateVanishingPluckerPoint)).ker =
        MulAction.stabilizer (Variety.Point G)
          H.rightTranslateVanishingPluckerPoint :=
      stabilizer_eq_ker_toPermHom_orbit_of_normal
        H.rightTranslateVanishingPluckerPoint hstabN
    _ = H.toSubgroup := hstab

end

/-! Pointwise evaluation after restricting the right tensor factor to a closed subgroup. -/

section
open scoped TensorProduct
variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
lemma ClosedSubgroup.tensorRestriction_apply
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (t : Variety.PolynomialFunction G ⊗[k] Variety.PolynomialFunction G)
    (g : Variety.Point G) (h : Variety.Point H.carrierVariety) :
    polynomialFunctionTensor G H.carrierVariety
      (TensorProduct.map LinearMap.id H.restrictionAlgHom.toLinearMap t)
      ((Variety.prodPointEquiv G H.carrierVariety).symm (g, h)) =
    polynomialFunctionTensor G G t
      ((Variety.prodPointEquiv G G).symm (g, H.inclusion.onPoints h)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
      rw [TensorProduct.map_tmul, polynomialFunctionTensor_tmul,
        polynomialFunctionTensor_tmul]
      change a g * H.restrictionAlgHom b h =
        a g * b (H.inclusion.onPoints h)
      rfl
  | add x y hx hy =>
      simp only [map_add]
      simp only [Variety.PolynomialFunction.toFun, Subring.coe_add, Pi.add_apply]
      exact congrArg₂ (· + ·) hx hy

end

/-! The subgroup coaction is ambient comultiplication followed by restriction. -/

section
open scoped TensorProduct
variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
lemma ClosedSubgroup.coordinateCoaction_natural
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    H.coordinateCoaction =
      (Algebra.TensorProduct.map
        (AlgHom.id k (Variety.PolynomialFunction G)) H.restrictionAlgHom).comp
        (AlgebraicGroup.coordinateComultiplication G) := by
  apply AlgHom.ext
  intro f
  apply polynomialFunctionTensor_injective G H.carrierVariety
  apply Variety.PolynomialFunction.ext
  intro z
  let gh := Variety.prodPointEquiv G H.carrierVariety z
  let g := gh.1
  let h := gh.2
  have hz : z =
      (Variety.prodPointEquiv G H.carrierVariety).symm (g, h) := by
    exact ((Variety.prodPointEquiv G H.carrierVariety).symm_apply_apply z).symm
  rw [hz]
  change polynomialFunctionTensor G H.carrierVariety (H.coordinateCoaction f) _ =
    polynomialFunctionTensor G H.carrierVariety
      (TensorProduct.map LinearMap.id H.restrictionAlgHom.toLinearMap
        (AlgebraicGroup.coordinateComultiplication G f)) _
  rw [H.coordinateCoaction_apply, H.tensorRestriction_apply,
    AlgebraicGroup.coordinateComultiplication_apply]

end

section
open scoped ExteriorAlgebra
variable {k : Type u} [Field k] [IsAlgClosed k]

public abbrev ClosedSubgroup.rightTranslateVanishingExteriorIndex
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :=
  Set.powersetCard
    (Fin (Module.finrank k H.rightTranslateVanishingSpan))
    H.rightTranslateVanishingTopWedgeData.degree

@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingExteriorBasis
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Module.Basis (Fin (Fintype.card H.rightTranslateVanishingExteriorIndex)) k
      (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
        H.rightTranslateVanishingSpan) :=
  ((H.rightTranslateVanishingSpanBasis).exteriorPower
    H.rightTranslateVanishingTopWedgeData.degree).reindex
      (Fintype.equivFin H.rightTranslateVanishingExteriorIndex)

end

/-! Determinantal matrix coefficients of the exterior Chevalley representation. -/

section
open scoped ExteriorAlgebra
variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingExteriorMatrixCoefficient
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (s t : H.rightTranslateVanishingExteriorIndex) :
    G.PolynomialFunction :=
  Matrix.det fun i j =>
    H.rightTranslateVanishingMatrixCoefficient
      H.rightTranslateVanishingSpanBasis
      (Set.powersetCard.ofFinEmbEquiv.symm s j)
      (Set.powersetCard.ofFinEmbEquiv.symm t i)

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.rightTranslateVanishingExteriorMatrixCoefficient_apply
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (s t : H.rightTranslateVanishingExteriorIndex)
    (g : Variety.Point G) :
    H.rightTranslateVanishingExteriorMatrixCoefficient s t g =
      (((H.rightTranslateVanishingSpanBasis).exteriorPower
          H.rightTranslateVanishingTopWedgeData.degree).coord s)
        (exteriorPower.map H.rightTranslateVanishingTopWedgeData.degree
          (LinearMap.GeneralLinearGroup.toLinearEquiv
            (H.rightTranslateVanishingSpanGeneralLinear g)).toLinearMap
          (((H.rightTranslateVanishingSpanBasis).exteriorPower
            H.rightTranslateVanishingTopWedgeData.degree) t)) := by
  let ev : G.PolynomialFunction →+* k :=
    { toFun := fun f => f g
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let M : Matrix
      (Fin H.rightTranslateVanishingTopWedgeData.degree)
      (Fin H.rightTranslateVanishingTopWedgeData.degree)
      G.PolynomialFunction := fun i j =>
    H.rightTranslateVanishingMatrixCoefficient
      H.rightTranslateVanishingSpanBasis
      (Set.powersetCard.ofFinEmbEquiv.symm s j)
      (Set.powersetCard.ofFinEmbEquiv.symm t i)
  change ev (Matrix.det M) = _
  rw [RingHom.map_det]
  change (Matrix.det fun i j =>
    H.rightTranslateVanishingMatrixCoefficient
      H.rightTranslateVanishingSpanBasis
      (Set.powersetCard.ofFinEmbEquiv.symm s j)
      (Set.powersetCard.ofFinEmbEquiv.symm t i) g) = _
  rw [exteriorPower.basis_coord, exteriorPower.basis_apply,
    exteriorPower.map_apply_ιMulti_family]
  rw [exteriorPower.ιMulti_family]
  rw [exteriorPower.ιMultiDual_apply_ιMulti]
  congr 1
  ext i j
  rw [H.rightTranslateVanishingMatrixCoefficient_apply]
  rfl

end

/-! Fin-indexed matrix coefficients for the exterior Chevalley representation. -/

section

open scoped ExteriorAlgebra

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingExteriorFinMatrixCoefficient
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (i j : Fin (Fintype.card H.rightTranslateVanishingExteriorIndex)) :
    G.PolynomialFunction :=
  H.rightTranslateVanishingExteriorMatrixCoefficient
    ((Fintype.equivFin H.rightTranslateVanishingExteriorIndex).symm i)
    ((Fintype.equivFin H.rightTranslateVanishingExteriorIndex).symm j)

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.rightTranslateVanishingExteriorFinMatrixCoefficient_apply
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (i j : Fin (Fintype.card H.rightTranslateVanishingExteriorIndex))
    (g : Variety.Point G) :
    H.rightTranslateVanishingExteriorFinMatrixCoefficient i j g =
      (H.rightTranslateVanishingExteriorBasis.repr
        (exteriorPower.map H.rightTranslateVanishingTopWedgeData.degree
          (LinearMap.GeneralLinearGroup.toLinearEquiv
            (H.rightTranslateVanishingSpanGeneralLinear g)).toLinearMap
          (H.rightTranslateVanishingExteriorBasis j))) i := by
  rw [ClosedSubgroup.rightTranslateVanishingExteriorFinMatrixCoefficient]
  rw [ClosedSubgroup.rightTranslateVanishingExteriorBasis,
    Module.Basis.reindex_apply]
  rw [show (((H.rightTranslateVanishingSpanBasis).exteriorPower
      H.rightTranslateVanishingTopWedgeData.degree).reindex
        (Fintype.equivFin H.rightTranslateVanishingExteriorIndex)).repr
      (exteriorPower.map H.rightTranslateVanishingTopWedgeData.degree
        (LinearMap.GeneralLinearGroup.toLinearEquiv
          (H.rightTranslateVanishingSpanGeneralLinear g)).toLinearMap
        (((H.rightTranslateVanishingSpanBasis).exteriorPower
          H.rightTranslateVanishingTopWedgeData.degree)
            ((Fintype.equivFin H.rightTranslateVanishingExteriorIndex).symm j))) i =
    (((H.rightTranslateVanishingSpanBasis).exteriorPower
      H.rightTranslateVanishingTopWedgeData.degree).repr
      (exteriorPower.map H.rightTranslateVanishingTopWedgeData.degree
        (LinearMap.GeneralLinearGroup.toLinearEquiv
          (H.rightTranslateVanishingSpanGeneralLinear g)).toLinearMap
        (((H.rightTranslateVanishingSpanBasis).exteriorPower
          H.rightTranslateVanishingTopWedgeData.degree)
            ((Fintype.equivFin H.rightTranslateVanishingExteriorIndex).symm j))))
      ((Fintype.equivFin H.rightTranslateVanishingExteriorIndex).symm i) by
        rfl]
  exact H.rightTranslateVanishingExteriorMatrixCoefficient_apply
    ((Fintype.equivFin H.rightTranslateVanishingExteriorIndex).symm i)
    ((Fintype.equivFin H.rightTranslateVanishingExteriorIndex).symm j) g

end

/-! Evaluation of the exterior Chevalley representation. -/

section

open scoped ExteriorAlgebra

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.rightTranslateVanishingExteriorGeneralLinear_apply
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (g : Variety.Point G)
    (x : ⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
      H.rightTranslateVanishingSpan) :
    ((H.rightTranslateVanishingExteriorGeneralLinear g :
      LinearMap.GeneralLinearGroup k
        (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
          H.rightTranslateVanishingSpan)) :
      Module.End k
        (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
          H.rightTranslateVanishingSpan)) x =
      exteriorPower.map H.rightTranslateVanishingTopWedgeData.degree
        (LinearMap.GeneralLinearGroup.toLinearEquiv
          (H.rightTranslateVanishingSpanGeneralLinear g)).toLinearMap x := by
  rfl

end

/-! Inverse matrix coefficients for the exterior Chevalley representation. -/

section

open scoped ExteriorAlgebra

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A matrix coefficient of the inverse exterior Chevalley representation,
obtained by pullback along group inversion. -/
@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingExteriorInverseMatrixCoefficient
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (i j : Fin (Fintype.card H.rightTranslateVanishingExteriorIndex)) :
    G.PolynomialFunction :=
  Variety.PolynomialFunction.pullback (AlgebraicGroup.invMorphism G)
    (H.rightTranslateVanishingExteriorFinMatrixCoefficient i j)

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.rightTranslateVanishingExteriorInverseMatrixCoefficient_apply
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (i j : Fin (Fintype.card H.rightTranslateVanishingExteriorIndex))
    (g : Variety.Point G) :
    H.rightTranslateVanishingExteriorInverseMatrixCoefficient i j g =
      (H.rightTranslateVanishingExteriorBasis.repr
        (exteriorPower.map H.rightTranslateVanishingTopWedgeData.degree
          (LinearMap.GeneralLinearGroup.toLinearEquiv
            (H.rightTranslateVanishingSpanGeneralLinear g⁻¹)).toLinearMap
          (H.rightTranslateVanishingExteriorBasis j))) i := by
  exact H.rightTranslateVanishingExteriorFinMatrixCoefficient_apply i j g⁻¹

end

/-! The matrix of the exterior Chevalley representation in its fixed basis. -/

section

open scoped ExteriorAlgebra

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingExteriorRepresentationMatrix
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (g : Variety.Point G) :
    Matrix (Fin (Fintype.card H.rightTranslateVanishingExteriorIndex))
      (Fin (Fintype.card H.rightTranslateVanishingExteriorIndex)) k :=
  LinearMap.toMatrix H.rightTranslateVanishingExteriorBasis
    H.rightTranslateVanishingExteriorBasis
    ((H.rightTranslateVanishingExteriorGeneralLinear g :
      LinearMap.GeneralLinearGroup k
        (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
          H.rightTranslateVanishingSpan)) :
      Module.End k
        (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
          H.rightTranslateVanishingSpan))

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.rightTranslateVanishingExteriorRepresentationMatrix_apply
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (g : Variety.Point G)
    (i j : Fin (Fintype.card H.rightTranslateVanishingExteriorIndex)) :
    H.rightTranslateVanishingExteriorRepresentationMatrix g i j =
      H.rightTranslateVanishingExteriorFinMatrixCoefficient i j g := by
  rw [ClosedSubgroup.rightTranslateVanishingExteriorRepresentationMatrix,
    LinearMap.toMatrix_apply,
    H.rightTranslateVanishingExteriorFinMatrixCoefficient_apply]
  rfl

end

/-! The inverse-determinant coordinate for the exterior Chevalley representation. -/

section

open scoped ExteriorAlgebra

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The determinant of the inverse exterior representation matrix. -/
@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingExteriorInverseDeterminant
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    G.PolynomialFunction :=
  Matrix.det (fun i j =>
    H.rightTranslateVanishingExteriorInverseMatrixCoefficient i j)

omit [IsAlgClosed k] in
/-- Evaluation of the exterior inverse-determinant function is the inverse
of the determinant of the exterior representation matrix. -/
public lemma ClosedSubgroup.rightTranslateVanishingExteriorInverseDeterminant_apply
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (g : Variety.Point G) :
    H.rightTranslateVanishingExteriorInverseDeterminant g =
      (H.rightTranslateVanishingExteriorRepresentationMatrix g).det⁻¹ := by
  let ev : G.PolynomialFunction →+* k :=
    { toFun := fun f => f g
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let M : Matrix
      (Fin (Fintype.card H.rightTranslateVanishingExteriorIndex))
      (Fin (Fintype.card H.rightTranslateVanishingExteriorIndex))
      G.PolynomialFunction := fun i j =>
    H.rightTranslateVanishingExteriorInverseMatrixCoefficient i j
  have hEval : H.rightTranslateVanishingExteriorInverseDeterminant g =
      (H.rightTranslateVanishingExteriorRepresentationMatrix g⁻¹).det := by
    change ev (Matrix.det M) = _
    rw [RingHom.map_det]
    congr 1
    funext i j
    change H.rightTranslateVanishingExteriorInverseMatrixCoefficient i j g = _
    rw [H.rightTranslateVanishingExteriorInverseMatrixCoefficient_apply]
    symm
    rw [H.rightTranslateVanishingExteriorRepresentationMatrix_apply,
      H.rightTranslateVanishingExteriorFinMatrixCoefficient_apply]
  rw [hEval]
  exact generalLinear_toMatrix_inv_det H.rightTranslateVanishingExteriorBasis
    (H.rightTranslateVanishingExteriorGeneralLinear g)

end

/-! Regular matrix coefficients against arbitrary ambient vectors and covectors. -/

section

open scoped ExteriorAlgebra BigOperators

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingExteriorLinearMatrixCoefficient
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (L : Module.Dual k
      (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
        H.rightTranslateVanishingSpan))
    (x : ⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
      H.rightTranslateVanishingSpan) : G.PolynomialFunction :=
  ∑ p, ∑ q, algebraMap k G.PolynomialFunction
      (L (H.rightTranslateVanishingExteriorBasis p) *
        H.rightTranslateVanishingExteriorBasis.repr x q) *
      H.rightTranslateVanishingExteriorFinMatrixCoefficient p q

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.rightTranslateVanishingExteriorLinearMatrixCoefficient_apply
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (L : Module.Dual k
      (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
        H.rightTranslateVanishingSpan))
    (x : ⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
      H.rightTranslateVanishingSpan) (g : Variety.Point G) :
    H.rightTranslateVanishingExteriorLinearMatrixCoefficient L x g =
      L (((H.rightTranslateVanishingExteriorGeneralLinear g :
        LinearMap.GeneralLinearGroup k
          (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
            H.rightTranslateVanishingSpan)) :
        Module.End k
          (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
            H.rightTranslateVanishingSpan)) x) := by
  rw [ClosedSubgroup.rightTranslateVanishingExteriorLinearMatrixCoefficient]
  let ev : G.PolynomialFunction →+* k :=
    { toFun := fun f => f g
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev (∑ p, ∑ q, algebraMap k G.PolynomialFunction
      (L (H.rightTranslateVanishingExteriorBasis p) *
        H.rightTranslateVanishingExteriorBasis.repr x q) *
      H.rightTranslateVanishingExteriorFinMatrixCoefficient p q) = _
  rw [map_sum]
  simp_rw [map_sum, map_mul]
  have hev (q : G.PolynomialFunction) : ev q = q g := rfl
  simp_rw [hev]
  simp_rw [polynomialFunction_algebraMap_apply]
  simp_rw [← H.rightTranslateVanishingExteriorRepresentationMatrix_apply]
  exact LinearMap.dual_apply_eq_sum_toMatrix
    H.rightTranslateVanishingExteriorBasis L
    (((H.rightTranslateVanishingExteriorGeneralLinear g :
      LinearMap.GeneralLinearGroup k
        (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
          H.rightTranslateVanishingSpan)) :
      Module.End k
        (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
          H.rightTranslateVanishingSpan))) x

end

/-! Matrix multiplication for the exterior Chevalley representation. -/

section

open scoped ExteriorAlgebra BigOperators

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.rightTranslateVanishingExteriorRepresentationMatrix_mul_repr
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (i : Fin (Fintype.card H.rightTranslateVanishingExteriorIndex))
    (g : Variety.Point G) :
    ∑ j, (H.rightTranslateVanishingExteriorBasis.repr
      H.rightTranslateVanishingPluckerVector j) *
      H.rightTranslateVanishingExteriorRepresentationMatrix g i j =
      H.rightTranslateVanishingExteriorBasis.repr
        (((H.rightTranslateVanishingExteriorGeneralLinear g :
          LinearMap.GeneralLinearGroup k
            (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
              H.rightTranslateVanishingSpan)) :
          Module.End k
            (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
              H.rightTranslateVanishingSpan))
          H.rightTranslateVanishingPluckerVector) i := by
  exact LinearMap.repr_apply_eq_sum_toMatrix
    H.rightTranslateVanishingExteriorBasis
    (((H.rightTranslateVanishingExteriorGeneralLinear g :
      LinearMap.GeneralLinearGroup k
        (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
          H.rightTranslateVanishingSpan)) :
      Module.End k
        (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
          H.rightTranslateVanishingSpan)))
    H.rightTranslateVanishingPluckerVector i

end

/-! The exterior Chevalley representation as a regular algebraic-group morphism. -/

section

open scoped ExteriorAlgebra

variable {k : Type u} [Field k] [IsAlgClosed k]

public noncomputable def ClosedSubgroup.rightTranslateVanishingExteriorPointMulEquiv
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Variety.Point
        (glVariety (Fintype.card H.rightTranslateVanishingExteriorIndex) : Variety k) ≃*
      LinearMap.GeneralLinearGroup k
        (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
          H.rightTranslateVanishingSpan) :=
  (translationGLPointMulEquiv
    (Fintype.card H.rightTranslateVanishingExteriorIndex)).trans
      (Matrix.GeneralLinearGroup.toLin' H.rightTranslateVanishingExteriorBasis)

@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingExteriorRepresentationPoint
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (g : Variety.Point G) :
    Variety.Point
      (glVariety (Fintype.card H.rightTranslateVanishingExteriorIndex) : Variety k) :=
  H.rightTranslateVanishingExteriorPointMulEquiv.symm
    (H.rightTranslateVanishingExteriorGeneralLinear g)

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.rightTranslateVanishingExteriorRepresentationPoint_matrix
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (g : Variety.Point G)
    (i j : Fin (Fintype.card H.rightTranslateVanishingExteriorIndex)) :
    (H.rightTranslateVanishingExteriorRepresentationPoint g).val (Sum.inl (i, j)) =
      H.rightTranslateVanishingExteriorFinMatrixCoefficient i j g := by
  rw [rightTranslateVanishingExteriorRepresentationPoint,
    rightTranslateVanishingExteriorPointMulEquiv, translationGLPointMulEquiv]
  change glMatrixOfPoint (Fintype.card H.rightTranslateVanishingExteriorIndex)
    ((glPointEquiv (Fintype.card H.rightTranslateVanishingExteriorIndex)).symm
      ((Matrix.GeneralLinearGroup.toLin'
        H.rightTranslateVanishingExteriorBasis).symm
          (H.rightTranslateVanishingExteriorGeneralLinear g))) i j = _
  change H.rightTranslateVanishingExteriorRepresentationMatrix g i j = _
  exact H.rightTranslateVanishingExteriorRepresentationMatrix_apply g i j

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.rightTranslateVanishingExteriorRepresentationPoint_scalar
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (g : Variety.Point G) :
    (H.rightTranslateVanishingExteriorRepresentationPoint g).val
        (Sum.inr PUnit.unit) =
      H.rightTranslateVanishingExteriorInverseDeterminant g := by
  rw [rightTranslateVanishingExteriorRepresentationPoint,
    rightTranslateVanishingExteriorPointMulEquiv, translationGLPointMulEquiv]
  change glScalarOfPoint (Fintype.card H.rightTranslateVanishingExteriorIndex)
    ((glPointEquiv (Fintype.card H.rightTranslateVanishingExteriorIndex)).symm
      ((Matrix.GeneralLinearGroup.toLin'
        H.rightTranslateVanishingExteriorBasis).symm
          (H.rightTranslateVanishingExteriorGeneralLinear g))) = _
  rw [glScalarOfPoint_eq_inv_det,
    H.rightTranslateVanishingExteriorInverseDeterminant_apply]
  congr 1

/-- The exterior Chevalley representation is regular. -/
@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingExteriorRepresentationMorphism
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    AlgebraicGroup.Morphism G
      (glVariety (Fintype.card H.rightTranslateVanishingExteriorIndex) : Variety k) where
  toVariety :=
    { toFun := H.rightTranslateVanishingExteriorRepresentationPoint
      regular := by
        intro c
        cases c with
        | inl ij =>
            rcases ij with ⟨i, j⟩
            rcases (H.rightTranslateVanishingExteriorFinMatrixCoefficient i j).representedBy with
              ⟨p, hp⟩
            refine ⟨p, fun g => ?_⟩
            rw [← hp g]
            exact H.rightTranslateVanishingExteriorRepresentationPoint_matrix g i j
        | inr q =>
            cases q
            rcases H.rightTranslateVanishingExteriorInverseDeterminant.representedBy with
              ⟨p, hp⟩
            refine ⟨p, fun g => ?_⟩
            rw [← hp g]
            exact H.rightTranslateVanishingExteriorRepresentationPoint_scalar g }
  map_one := by
    simp [rightTranslateVanishingExteriorRepresentationPoint]
  map_mul := by
    intro g h
    simp [rightTranslateVanishingExteriorRepresentationPoint]

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.rightTranslateVanishingExteriorRepresentationMorphism_apply
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (g : Variety.Point G) :
    H.rightTranslateVanishingExteriorRepresentationMorphism.onPoints g =
      H.rightTranslateVanishingExteriorRepresentationPoint g :=
  rfl

end

end Theory.AlgebraicGroup
