module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Nullstellensatz

universe u

namespace Theory.AlgebraicGroup.Bor1

set_option linter.style.haveILetI false in
/-- Over an algebraically closed field, every maximal ideal in a finite-type
algebra is the kernel of a base-field-valued character. -/
public theorem exists_algHom_ker_eq_of_isMaximal_finiteType
    {k A : Type u} [Field k] [IsAlgClosed k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A]
    (m : Ideal A) (hm : m.IsMaximal) :
    ∃ φ : A →ₐ[k] k, RingHom.ker φ.toRingHom = m := by
  letI : m.IsMaximal := hm
  let L := A ⧸ m
  letI : Field L := Ideal.Quotient.field m
  let q : A →ₐ[k] L := Ideal.Quotient.mkₐ k m
  letI : Algebra.FiniteType k L :=
    Algebra.FiniteType.of_surjective q Ideal.Quotient.mk_surjective
  letI : Module.Finite k L := finite_of_finite_type_of_isJacobsonRing k L
  letI : Algebra.IsIntegral k L := Algebra.IsIntegral.of_finite k L
  letI : Algebra.IsAlgebraic k L := inferInstance
  let ψ : L →ₐ[k] k := IsAlgClosed.lift
  refine ⟨ψ.comp q, ?_⟩
  change RingHom.ker (ψ.toRingHom.comp q.toRingHom) = m
  rw [RingHom.ker_comp_of_injective q.toRingHom ψ.injective]
  exact Ideal.Quotient.mkₐ_ker k m

end Theory.AlgebraicGroup.Bor1
