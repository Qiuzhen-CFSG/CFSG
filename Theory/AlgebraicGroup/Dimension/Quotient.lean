module

public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.NoetherNormalization

universe u v

/-! Transcendence-degree bounds for quotients of affine coordinate rings. -/

namespace Theory.AlgebraicGroup

open scoped TensorProduct Cardinal

open LinearMap Submodule

variable {k : Type u} [Field k]

/-- For nested ideals `J ≤ I`, the transcendence degree of the quotient by the
smaller ideal is at most that of the quotient by the larger one. -/
public theorem trdeg_le_of_quotient_le (σ : Type*) (I J : Ideal (MvPolynomial σ k))
    (hIJ : J ≤ I) :
    Algebra.trdeg k (MvPolynomial σ k ⧸ I) ≤
      Algebra.trdeg k (MvPolynomial σ k ⧸ J) := by
  have hzero : ∀ p ∈ J, Ideal.Quotient.mkₐ k I p = 0 := by
    intro p hp
    rw [show Ideal.Quotient.mkₐ k I p = Ideal.Quotient.mk I p from
      congrFun (Ideal.Quotient.mkₐ_eq_mk k I) p]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hIJ hp)
  let φ : MvPolynomial σ k ⧸ J →ₐ[k] MvPolynomial σ k ⧸ I :=
    Ideal.Quotient.liftₐ J (Ideal.Quotient.mkₐ k I) hzero
  have hφsurj : Function.Surjective φ := by
    intro y
    rcases Ideal.Quotient.mk_surjective y with ⟨p, hp⟩
    refine ⟨Ideal.Quotient.mk J p, ?_⟩
    have hcalc : φ (Ideal.Quotient.mk J p) = Ideal.Quotient.mk I p := by
      dsimp [φ]
      change (Ideal.Quotient.lift J (Ideal.Quotient.mkₐ k I).toRingHom hzero)
          (Ideal.Quotient.mk J p) = (Ideal.Quotient.mkₐ k I).toRingHom p
      exact Ideal.Quotient.lift_mk J (Ideal.Quotient.mkₐ k I).toRingHom hzero
        (a := p)
    exact hcalc.trans hp
  exact trdeg_le_of_surjective φ hφsurj

/-- A nontrivial prime quotient of a polynomial ring in finitely many
variables has transcendence degree strictly smaller than the number of
variables. -/
public theorem trdeg_quotient_lt_coordinates_of_ne_bot (σ : Type v) [Finite σ]
    (I : Ideal (MvPolynomial σ k)) [IsDomain (MvPolynomial σ k ⧸ I)]
    (hI : I ≠ ⊥) :
    Algebra.trdeg k (MvPolynomial σ k ⧸ I) < Cardinal.lift.{max u v} #(σ) := by
  let x : σ → MvPolynomial σ k ⧸ I := fun i =>
    Ideal.Quotient.mk I (MvPolynomial.X i)
  have hx : Algebra.adjoin k (Set.range x) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval]
    rw [← MvPolynomial.mkₐ_eq_aeval I]
    exact (AlgHom.range_eq_top _).mpr (Ideal.Quotient.mkₐ_surjective k I)
  let : Algebra.IsAlgebraic (Algebra.adjoin k (Set.range x))
      (MvPolynomial σ k ⧸ I) := by
    rw [hx]
    rw [Algebra.isAlgebraic_def]
    intro y
    let yTop : (⊤ : Subalgebra k (MvPolynomial σ k ⧸ I)) := ⟨y, trivial⟩
    have hy : algebraMap (⊤ : Subalgebra k (MvPolynomial σ k ⧸ I))
        (MvPolynomial σ k ⧸ I) yTop = y := rfl
    rw [← hy]
    exact isAlgebraic_algebraMap yTop
  have hrange : #(Set.range x) ≤ Cardinal.lift.{max u v} #(σ) := by
    have hr := Cardinal.mk_range_le_lift (f := x)
    rw [Cardinal.lift_id'.{v, u}] at hr
    exact hr
  have hle : Algebra.trdeg k (MvPolynomial σ k ⧸ I) ≤
      Cardinal.lift.{max u v} #(σ) :=
    (Algebra.IsAlgebraic.trdeg_le_cardinalMk k (Set.range x)).trans hrange
  by_contra hlt
  have hge : Cardinal.lift.{max u v} #(σ) ≤
      Algebra.trdeg k (MvPolynomial σ k ⧸ I) :=
    not_lt.mp hlt
  have hbasis : IsTranscendenceBasis k x :=
    Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg_of_finite k x (by
      rw [Cardinal.lift_id'.{v, u}]
      exact hge)
  have hinj : Function.Injective (MvPolynomial.aeval x :
      MvPolynomial σ k →ₐ[k] MvPolynomial σ k ⧸ I) :=
    algebraicIndependent_iff_injective_aeval.mp hbasis.1
  have hmkInj : Function.Injective (Ideal.Quotient.mkₐ k I) := by
    rw [MvPolynomial.mkₐ_eq_aeval I]
    exact hinj
  have hbot : I = ⊥ := (Ideal.Quotient.mk_bijective_iff_eq_bot I).mp ⟨by
    simpa [Ideal.Quotient.mkₐ_eq_mk] using hmkInj,
    Ideal.Quotient.mk_surjective⟩
  exact hI hbot

/-- Quotienting a finitely generated domain over a field by a nonzero prime
ideal strictly lowers transcendence degree.  Noether normalization reduces
the comparison to a polynomial ring; integrality makes a nonzero ideal have
nonzero contraction and preserves transcendence degree. -/
public theorem trdeg_quotient_lt_of_ne_bot (A : Type u) [CommRing A]
    [Algebra k A] [IsDomain A] [Algebra.FiniteType k A]
    (I : Ideal A) [IsDomain (A ⧸ I)] (hI : I ≠ ⊥) :
    Algebra.trdeg k (A ⧸ I) < Algebra.trdeg k A := by
  obtain ⟨n, g, hg, hgint⟩ := exists_integral_inj_algHom_of_fg k A
  let B := MvPolynomial (Fin n) k
  let : Algebra B A := g.toRingHom.toAlgebra
  have : IsScalarTower k B A :=
    IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  let : Algebra.IsIntegral B A := ⟨hgint⟩
  let : I.IsPrime := (Ideal.Quotient.isDomain_iff_prime I).mp inferInstance
  let P : Ideal B := I.comap (algebraMap B A)
  let : P.IsPrime := Ideal.comap_isPrime (algebraMap B A) I
  have hP : P ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot B hI
  have hfaithfulBA : FaithfulSMul B A :=
    (faithfulSMul_iff_algebraMap_injective (R := B) (A := A)).mpr hg
  let : FaithfulSMul B A := hfaithfulBA
  have htrA : Algebra.trdeg k B + Algebra.trdeg B A = Algebra.trdeg k A :=
    trdeg_add_eq (R := k) (S := B) (A := A)
  have htrBA : Algebra.trdeg B A = 0 := trdeg_eq_zero (R := B) (A := A)
  have hAeq : Algebra.trdeg k A = Algebra.trdeg k B := by
    rw [← htrA, htrBA, add_zero]
  have hfaithfulQ : FaithfulSMul (B ⧸ P) (A ⧸ I) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    change Function.Injective
      (Ideal.quotientMap I (algebraMap B A)
        (show P ≤ I.comap (algebraMap B A) from le_rfl))
    exact Ideal.quotientMap_injective
  let : FaithfulSMul (B ⧸ P) (A ⧸ I) := hfaithfulQ
  have htrQ : Algebra.trdeg k (B ⧸ P) +
      Algebra.trdeg (B ⧸ P) (A ⧸ I) = Algebra.trdeg k (A ⧸ I) :=
    trdeg_add_eq (R := k) (S := B ⧸ P) (A := A ⧸ I)
  have htrPQ : Algebra.trdeg (B ⧸ P) (A ⧸ I) = 0 :=
    trdeg_eq_zero (R := B ⧸ P) (A := A ⧸ I)
  have hQeq : Algebra.trdeg k (A ⧸ I) = Algebra.trdeg k (B ⧸ P) := by
    rw [← htrQ, htrPQ, add_zero]
  have hB : Algebra.trdeg k B = Cardinal.lift.{u} #(Fin n) := by
    simp [B]
  calc
    Algebra.trdeg k (A ⧸ I) = Algebra.trdeg k (B ⧸ P) := hQeq
    _ < Cardinal.lift.{u} #(Fin n) :=
      trdeg_quotient_lt_coordinates_of_ne_bot (k := k) (Fin n) P hP
    _ = Algebra.trdeg k B := hB.symm
    _ = Algebra.trdeg k A := hAeq.symm

end Theory.AlgebraicGroup
