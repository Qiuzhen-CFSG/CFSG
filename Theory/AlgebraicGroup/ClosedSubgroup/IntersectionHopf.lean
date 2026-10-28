module

public import Mathlib.RingTheory.HopfAlgebra.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Theory.AlgebraicGroup.ClosedSubgroup.VanishingIdeal
public import Theory.AlgebraicGroup.CoordinateRing.Hopf.Bialgebra

/-!
# The Hopf algebra of a closed-subgroup intersection

For closed algebraic subgroups `B` and `C`, the sum of their vanishing ideals
is a Hopf ideal in the coordinate Hopf algebra.  Consequently its quotient
carries a canonical finite-type Hopf algebra structure.  This is the
scheme-theoretic intersection algebra, before taking its reduction.

The proof constructs the coordinate antipode, proves that restriction to a
closed subgroup is a bialgebra morphism, and uses right exactness of tensor
products to identify the kernel of the tensor-square restriction.  Stability
under the antipode follows pointwise from closure of each subgroup under
inversion.  Finally, over an algebraically closed field, reducedness of this
quotient implies that the sum ideal already equals the vanishing ideal of the
pointwise intersection: the Nullstellensatz is applied through maximal ideals
of the finite-type coordinate algebra.

This module supplies the algebraic bridge needed by the characteristic-zero
Cartier argument in `TangentIntersectionFoundation`.
-/

open scoped TensorProduct

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

noncomputable local instance coordinateBialgebraInstance
    (G : Variety k) [AlgebraicGroup G] :
    Bialgebra k G.PolynomialFunction :=
  coordinateBialgebra G

private noncomputable def coordinatePullbackBialgHom
    {H G : Variety k} [AlgebraicGroup H] [AlgebraicGroup G]
    (f : AlgebraicGroup.Morphism H G) :
    G.PolynomialFunction →ₐc[k] H.PolynomialFunction := by
  apply BialgHom.ofAlgHom f.toVariety.pullbackAlgHom
  · apply AlgHom.ext
    intro a
    change a (f.onPoints 1) = a 1
    rw [map_one]
  · apply AlgHom.ext
    intro a
    apply polynomialFunctionTensor_injective H H
    apply Variety.PolynomialFunction.ext
    intro z
    let xy := Variety.prodPointEquiv H H z
    generalize hxy : xy = p
    obtain ⟨x, y⟩ := p
    have hz : z = (Variety.prodPointEquiv H H).symm (x, y) := by
      apply (Variety.prodPointEquiv H H).injective
      change xy = (x, y)
      exact hxy
    rw [hz]
    have hmap (t : G.PolynomialFunction ⊗[k] G.PolynomialFunction) :
        polynomialFunctionTensor H H
            (Algebra.TensorProduct.map f.toVariety.pullbackAlgHom
              f.toVariety.pullbackAlgHom t)
            ((Variety.prodPointEquiv H H).symm (x, y)) =
          polynomialFunctionTensor G G t
            ((Variety.prodPointEquiv G G).symm
              (f.onPoints x, f.onPoints y)) := by
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add s t hs ht =>
          simpa [map_add, Variety.PolynomialFunction.toFun] using
            congrArg₂ (· + ·) hs ht
      | tmul g h =>
          rw [Algebra.TensorProduct.map_tmul, polynomialFunctionTensor_tmul,
            polynomialFunctionTensor_tmul]
          rfl
    change polynomialFunctionTensor H H
        (Algebra.TensorProduct.map f.toVariety.pullbackAlgHom
          f.toVariety.pullbackAlgHom (coordinateComultiplication G a)) _ =
      polynomialFunctionTensor H H
        (coordinateComultiplication H (f.toVariety.pullbackAlgHom a)) _
    rw [hmap, coordinateComultiplication_apply,
      coordinateComultiplication_apply]
    change a (f.onPoints x * f.onPoints y) = a (f.onPoints (x * y))
    rw [f.onPoints.map_mul]

private theorem vanishingIdeal_isCoideal
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    (H.vanishingIdeal.restrictScalars k).IsCoideal := by
  apply (Submodule.isCoideal_iff_comul_mem
    (H.vanishingIdeal.restrictScalars k)).mpr
  constructor
  · intro f hf
    change coordinateCounit G f = 0
    rw [coordinateCounit_apply]
    exact (H.mem_vanishingIdeal_iff f).mp hf 1 H.toSubgroup.one_mem
  · intro f hf
    let r := H.inclusion.toVariety.pullbackAlgHom
    have hr : Function.Surjective r := by
      intro y
      obtain ⟨x, hx⟩ := H.restrictionRingHom_surjective y
      exact ⟨x, hx⟩
    let pb : G.PolynomialFunction →ₐc[k]
        H.carrierVariety.PolynomialFunction :=
      coordinatePullbackBialgHom H.inclusion
    have hrf : r f = 0 := by
      change H.restrictionRingHom f = 0
      exact hf
    have hzero :
        TensorProduct.map r.toLinearMap r.toLinearMap
          (coordinateComultiplication G f) = 0 := by
      have hnat :
          TensorProduct.map r.toLinearMap r.toLinearMap
              (coordinateComultiplication G f) =
            coordinateComultiplication H.carrierVariety (r f) := by
        change TensorProduct.map pb.toLinearMap pb.toLinearMap
              (CoalgebraStruct.comul f) =
            CoalgebraStruct.comul (pb f)
        exact CoalgHomClass.map_comp_comul_apply pb f
      calc
        _ = coordinateComultiplication H.carrierVariety (r f) := hnat
        _ = coordinateComultiplication H.carrierVariety 0 :=
          congrArg (coordinateComultiplication H.carrierVariety) hrf
        _ = 0 := map_zero _
    have hker : coordinateComultiplication G f ∈
        LinearMap.ker (TensorProduct.map r.toLinearMap r.toLinearMap) :=
      hzero
    rw [TensorProduct.map_ker
      (LinearMap.exact_subtype_ker_map r.toLinearMap) hr
      (LinearMap.exact_subtype_ker_map r.toLinearMap) hr] at hker
    have hkr : LinearMap.ker r.toLinearMap =
        H.vanishingIdeal.restrictScalars k := by
      ext x
      change r x = 0 ↔ H.restrictionRingHom x = 0
      rfl
    rw [hkr] at hker
    exact hker

private lemma range_lTensor_subtype_mono
    {R : Type*} [CommRing R] [Module k R]
    {P Q : Submodule k R} (h : P ≤ Q) :
    LinearMap.range (LinearMap.lTensor R P.subtype) ≤
      LinearMap.range (LinearMap.lTensor R Q.subtype) := by
  rw [show P.subtype = Q.subtype.comp (Submodule.inclusion h) from rfl,
    LinearMap.lTensor_comp]
  exact LinearMap.range_comp_le_range _ _

private lemma range_rTensor_subtype_mono
    {R : Type*} [CommRing R] [Module k R]
    {P Q : Submodule k R} (h : P ≤ Q) :
    LinearMap.range (LinearMap.rTensor R P.subtype) ≤
      LinearMap.range (LinearMap.rTensor R Q.subtype) := by
  rw [show P.subtype = Q.subtype.comp (Submodule.inclusion h) from rfl,
    LinearMap.rTensor_comp]
  exact LinearMap.range_comp_le_range _ _

private theorem vanishingIdeal_sup_isCoideal
    {G : Variety k} [AlgebraicGroup G] (B C : ClosedSubgroup G) :
    ((B.vanishingIdeal ⊔ C.vanishingIdeal).restrictScalars k).IsCoideal := by
  let J : Ideal G.PolynomialFunction :=
    B.vanishingIdeal ⊔ C.vanishingIdeal
  have hBco := (Submodule.isCoideal_iff_comul_mem
    (B.vanishingIdeal.restrictScalars k)).mp (vanishingIdeal_isCoideal B)
  have hCco := (Submodule.isCoideal_iff_comul_mem
    (C.vanishingIdeal.restrictScalars k)).mp (vanishingIdeal_isCoideal C)
  apply (Submodule.isCoideal_iff_comul_mem (J.restrictScalars k)).mpr
  constructor
  · intro f hf
    rcases Submodule.mem_sup.mp hf with ⟨b, hb, c, hc, rfl⟩
    rw [map_add, hBco.1 b hb, hCco.1 c hc, add_zero]
  · intro f hf
    rcases Submodule.mem_sup.mp hf with ⟨b, hb, c, hc, rfl⟩
    rw [map_add]
    apply (LinearMap.range (LinearMap.lTensor G.PolynomialFunction
        (J.restrictScalars k).subtype) ⊔
      LinearMap.range (LinearMap.rTensor G.PolynomialFunction
        (J.restrictScalars k).subtype)).add_mem
    · have hBJ :
          (LinearMap.range (LinearMap.lTensor G.PolynomialFunction
              (B.vanishingIdeal.restrictScalars k).subtype) ⊔
            LinearMap.range (LinearMap.rTensor G.PolynomialFunction
              (B.vanishingIdeal.restrictScalars k).subtype)) ≤
            (LinearMap.range (LinearMap.lTensor G.PolynomialFunction
              (J.restrictScalars k).subtype) ⊔
            LinearMap.range (LinearMap.rTensor G.PolynomialFunction
              (J.restrictScalars k).subtype)) := sup_le_sup
        (range_lTensor_subtype_mono
          (show B.vanishingIdeal ≤ J from le_sup_left))
        (range_rTensor_subtype_mono
          (show B.vanishingIdeal ≤ J from le_sup_left))
      exact hBJ (hBco.2 b hb)
    · have hCJ :
          (LinearMap.range (LinearMap.lTensor G.PolynomialFunction
              (C.vanishingIdeal.restrictScalars k).subtype) ⊔
            LinearMap.range (LinearMap.rTensor G.PolynomialFunction
              (C.vanishingIdeal.restrictScalars k).subtype)) ≤
            (LinearMap.range (LinearMap.lTensor G.PolynomialFunction
              (J.restrictScalars k).subtype) ⊔
            LinearMap.range (LinearMap.rTensor G.PolynomialFunction
              (J.restrictScalars k).subtype)) := sup_le_sup
        (range_lTensor_subtype_mono
          (show C.vanishingIdeal ≤ J from le_sup_right))
        (range_rTensor_subtype_mono
          (show C.vanishingIdeal ≤ J from le_sup_right))
      exact hCJ (hCco.2 c hc)

private theorem vanishingIdeal_sup_antipode_mem
    {G : Variety k} [AlgebraicGroup G] (B C : ClosedSubgroup G)
    {f : G.PolynomialFunction}
    (hf : f ∈ B.vanishingIdeal ⊔ C.vanishingIdeal) :
    coordinateAntipode G f ∈ B.vanishingIdeal ⊔ C.vanishingIdeal := by
  rcases Submodule.mem_sup.mp hf with ⟨b, hb, c, hc, rfl⟩
  rw [map_add]
  apply Submodule.add_mem
  · apply (show B.vanishingIdeal ≤
        B.vanishingIdeal ⊔ C.vanishingIdeal from le_sup_left)
    rw [B.mem_vanishingIdeal_iff]
    intro x hx
    rw [coordinateAntipode_apply]
    exact (B.mem_vanishingIdeal_iff b).mp hb x⁻¹ (B.toSubgroup.inv_mem hx)
  · apply (show C.vanishingIdeal ≤
        B.vanishingIdeal ⊔ C.vanishingIdeal from le_sup_right)
    rw [C.mem_vanishingIdeal_iff]
    intro x hx
    rw [coordinateAntipode_apply]
    exact (C.mem_vanishingIdeal_iff c).mp hc x⁻¹ (C.toSubgroup.inv_mem hx)

set_option warn.classDefReducibility false in
/-- The quotient by the sum of two closed-subgroup vanishing ideals is the
coordinate Hopf algebra of their scheme-theoretic intersection. -/
public noncomputable def ClosedSubgroup.intersectionQuotientHopfAlgebra
    {G : Variety k} [AlgebraicGroup G] (B C : ClosedSubgroup G) :
    HopfAlgebra k
      (G.PolynomialFunction ⧸ (B.vanishingIdeal ⊔ C.vanishingIdeal)) := by
  letI : HopfAlgebra k G.PolynomialFunction := coordinateHopfAlgebra G
  letI hcoideal :
      ((B.vanishingIdeal ⊔ C.vanishingIdeal).restrictScalars k).IsCoideal :=
    vanishingIdeal_sup_isCoideal B C
  letI : (B.vanishingIdeal ⊔ C.vanishingIdeal).IsHopfIdeal k :=
    Ideal.IsHopfIdeal.mk (R := k) (toIsCoideal := hcoideal) (by
      intro f hf
      change coordinateAntipode G f ∈
        B.vanishingIdeal ⊔ C.vanishingIdeal
      exact vanishingIdeal_sup_antipode_mem B C hf)
  infer_instance

/-- The scheme-theoretic intersection quotient is a finite-type algebra over
the base field, for the algebra structure carried by its Hopf algebra. -/
public theorem ClosedSubgroup.intersectionQuotientHopfAlgebra_finiteType
    {G : Variety k} [AlgebraicGroup G] (B C : ClosedSubgroup G) :
    @Algebra.FiniteType k
      (G.PolynomialFunction ⧸ (B.vanishingIdeal ⊔ C.vanishingIdeal)) _ _
      (B.intersectionQuotientHopfAlgebra C).toAlgebra := by
  let : Algebra.FiniteType k G.PolynomialFunction :=
    polynomialFunction_finiteType G
  exact Algebra.FiniteType.quotient k
    (B.vanishingIdeal ⊔ C.vanishingIdeal)

section AlgebraicallyClosed

variable [IsAlgClosed k]

/-- If the scheme-theoretic intersection quotient is reduced, its defining
ideal is exactly controlled by the pointwise closed-subgroup intersection. -/
public theorem ClosedSubgroup.inter_vanishingIdeal_le_sup_of_isReduced
    {G : Variety k} [AlgebraicGroup G] (B C : ClosedSubgroup G)
    (hred : IsReduced
      (G.PolynomialFunction ⧸ (B.vanishingIdeal ⊔ C.vanishingIdeal))) :
    (B.inter C).vanishingIdeal ≤ B.vanishingIdeal ⊔ C.vanishingIdeal := by
  let J : Ideal G.PolynomialFunction :=
    B.vanishingIdeal ⊔ C.vanishingIdeal
  let : IsReduced (G.PolynomialFunction ⧸ J) := hred
  have hJrad : J.IsRadical :=
    (Ideal.isRadical_iff_quotient_reduced J).mpr inferInstance
  let : Algebra.FiniteType k G.PolynomialFunction :=
    polynomialFunction_finiteType G
  let : IsJacobsonRing G.PolynomialFunction :=
    isJacobsonRing_of_finiteType (A := k)
  intro f hf
  have hfvan : ∀ x : Variety.Point G,
      x ∈ (B.inter C).toSubgroup → f x = 0 :=
    ((B.inter C).mem_vanishingIdeal_iff f).mp hf
  change f ∈ J
  rw [← hJrad.radical]
  rw [Ideal.radical_eq_jacobson, Ideal.jacobson, Ideal.mem_sInf]
  intro m hm
  rcases hm with ⟨hJm, hmmax⟩
  obtain ⟨x, hx⟩ := G.exists_pointPrime_eq_of_isMaximal m hmmax
  have hmx : m = (G.pointPrime x).asIdeal :=
    (congrArg PrimeSpectrum.asIdeal hx).symm
  have hxB : x ∈ B.toSubgroup := by
    rw [B.mem_iff_forall_vanishingIdeal]
    intro g hg
    have hgm : g ∈ m := hJm (show g ∈ J from
      (show B.vanishingIdeal ≤ J from le_sup_left) hg)
    rw [hmx] at hgm
    exact hgm
  have hxC : x ∈ C.toSubgroup := by
    rw [C.mem_iff_forall_vanishingIdeal]
    intro g hg
    have hgm : g ∈ m := hJm (show g ∈ J from
      (show C.vanishingIdeal ≤ J from le_sup_right) hg)
    rw [hmx] at hgm
    exact hgm
  rw [hmx]
  exact hfvan x ((ClosedSubgroup.mem_inter_iff B C x).mpr ⟨hxB, hxC⟩)

end AlgebraicallyClosed

end Theory.AlgebraicGroup
