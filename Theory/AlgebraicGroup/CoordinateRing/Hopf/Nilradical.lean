module

public import Mathlib.RingTheory.HopfAlgebra.Quotient
public import Theory.AlgebraicGroup.CoordinateRing.Hopf.Bialgebra
public import Theory.AlgebraicGroup.CoordinateRing.Hopf.Presentation
public import Theory.AlgebraicGroup.Variety.ReducedProduct

/-!
# The nilradical is a Hopf ideal

For a finite-type commutative Hopf algebra over an algebraically closed field,
the nilradical is stable under the counit, comultiplication, and antipode.  The
first and third assertions follow by mapping a nilpotence witness through the
corresponding algebra homomorphism.  For comultiplication, quotient by the
nilradical, identify the quotient with the polynomial functions on a reduced
affine variety, and use reducedness of the product variety to show that the
image of the comultiplication of a nilpotent element vanishes.  Tensor-product
right exactness then identifies this kernel with the two coideal summands.

The reduced-product input is the algebraically closed-field theorem in
`Theory.AlgebraicGroup.Variety.ReducedProduct`; the quotient and Hopf-ideal
interfaces are supplied by Mathlib's Hopf-algebra quotient API.
-/

open scoped TensorProduct
open Coalgebra Bialgebra

universe u

namespace Theory.AlgebraicGroup

variable {k A : Type u} [Field k] [IsAlgClosed k] [CommRing A]
  [HopfAlgebra k A] [Algebra.FiniteType k A]

set_option linter.style.haveILetI false in
/-- The nilradical of a finite-type commutative Hopf algebra over an
algebraically closed field is a Hopf ideal. -/
public theorem nilradical_isHopfIdeal :
    (nilradical A).IsHopfIdeal k := by
  let I : Ideal A := nilradical A
  have hIred : IsReduced (A ⧸ I) := by
    apply (Ideal.isRadical_iff_quotient_reduced I).mp
    simpa [I, nilradical] using (Ideal.radical_isRadical (⊥ : Ideal A))
  letI : IsReduced (A ⧸ I) := hIred
  let B := A ⧸ I
  let q : A →ₐ[k] B := Ideal.Quotient.mkₐ k I
  have hBtensorred : IsReduced (B ⊗[k] B) := by
    let P : ReducedFiniteTypeAlgebraPresentation k B :=
      Classical.choice (ReducedFiniteTypeAlgebraPresentation.exists k B)
    let e : B ⊗[k] B ≃ₐ[k]
        Variety.PolynomialFunction (Variety.prod P.toVariety P.toVariety) :=
      (Algebra.TensorProduct.congr P.polynomialFunctionAlgEquiv
        P.polynomialFunctionAlgEquiv).trans
        (polynomialFunction_prod_algEquiv P.toVariety P.toVariety)
    exact isReduced_of_injective e.toAlgHom e.injective
  letI : IsReduced (B ⊗[k] B) := hBtensorred
  have hco : (I.restrictScalars k).IsCoideal := by
    apply (Submodule.isCoideal_iff_comul_mem (I.restrictScalars k)).mpr
    constructor
    · intro x hx
      apply (isReduced_iff k).mp inferInstance
      simpa only [Bialgebra.counitAlgHom_apply] using
        ((mem_nilradical.mp hx).map (Bialgebra.counitAlgHom k A))
    · intro x hx
      have hn : IsNilpotent x := mem_nilradical.mp hx
      let qt : (A ⊗[k] A) →ₐ[k] (B ⊗[k] B) :=
        Algebra.TensorProduct.map q q
      have hmap : IsNilpotent
          (qt (Coalgebra.comul x)) := by
        simpa only [Bialgebra.comulAlgHom_apply] using
          (hn.map (Bialgebra.comulAlgHom k A)).map qt
      have hz : qt (Coalgebra.comul x) = 0 :=
        IsReduced.eq_zero _ hmap
      have hk : Coalgebra.comul x ∈
          LinearMap.ker (TensorProduct.map q.toLinearMap q.toLinearMap) := by
        exact hz
      have hk' : Coalgebra.comul x ∈
          LinearMap.ker (TensorProduct.map
            (I.restrictScalars k).mkQ (I.restrictScalars k).mkQ) := by
        exact hk
      rw [TensorProduct.map_ker
        (LinearMap.exact_subtype_mkQ (I.restrictScalars k))
        (I.restrictScalars k).mkQ_surjective
        (LinearMap.exact_subtype_mkQ (I.restrictScalars k))
        (I.restrictScalars k).mkQ_surjective] at hk'
      exact hk'
  let hhopf : I.IsHopfIdeal k := {
    toIsCoideal := hco
    antipode_mem := by
      intro x hx
      apply mem_nilradical.mpr
      obtain ⟨n, hn⟩ := mem_nilradical.mp hx
      refine ⟨n, ?_⟩
      change (HopfAlgebra.antipodeAlgHom k A x) ^ n = 0
      rw [← map_pow]
      rw [show x ^ n = 0 from hn, map_zero]
  }
  exact hhopf

end Theory.AlgebraicGroup
