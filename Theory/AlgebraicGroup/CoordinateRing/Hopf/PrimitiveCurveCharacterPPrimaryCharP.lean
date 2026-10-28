module

public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Finiteness.Quotient
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Polynomial.Quotient
public import Theory.AlgebraicGroup.CoordinateRing.Hopf.PrimitiveCurveFinite

/-!
# Primitive Hopf-curve characters in positive characteristic

This module proves that the convolution group of `k`-valued characters of a
normal affine Hopf curve is a `p`-group when the curve has a transcendental
primitive coordinate and `k` has characteristic `p`.  It is the coordinate-ring
form of Borel, Theorem 10.9, applied as in the sketch following Theorem 11.6:
the primitive coordinate gives a nonconstant homomorphism to the additive group,
and its finite kernel controls all remaining torsion.

The proof is direct and does not classify the curve as an affine line.  Finiteness
of the primitive map first makes its zero fibre finite.  Nullstellensatz separation
then shows that commutators of characters are trivial.  If a nontrivial character
had prime order away from the characteristic, its translations would act
semisimply on a finite-dimensional translation span.  Commutativity supplies a
common translation eigenfunction.  Its norm over `k[t]` transforms by polynomial
Taylor translation; comparison of leading coefficients makes all eigenweights
torsion of one bounded order.  The eigenfunction consequently has only finitely
many point-values, so Nullstellensatz makes it scalar, contradicting its nontrivial
eigenvalue.  Finally, every character has finite order because its `p`-th power
lies in the finite zero fibre, and the prime-divisor argument leaves only `p`.

No parent rationality theorem, affine-line classification, primitive-generator
result, `ConilpotentDedekindParameter`, or classification chain is used.
-/

open scoped TensorProduct

universe u v

namespace Theory.AlgebraicGroup

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

variable {k : Type u} {A : Type v}
variable [Field k] [IsAlgClosed k] [CommRing A] [HopfAlgebra k A]

private lemma character_mul_apply_of_primitive
    (q r : WithConv (A →ₐ[k] k)) (t : A)
    (ht : Coalgebra.comul (R := k) t =
      t ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] t) :
    (q * r) t = q t + r t := by
  rw [AlgHom.convMul_apply, ht]
  simp

private lemma character_one_apply_of_primitive
    (t : A) (ht : Coalgebra.comul (R := k) t =
      t ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] t) :
    (1 : WithConv (A →ₐ[k] k)) t = 0 := by
  have h := character_mul_apply_of_primitive
    (1 : WithConv (A →ₐ[k] k)) 1 t ht
  rw [one_mul] at h
  apply add_left_cancel (a := (1 : WithConv (A →ₐ[k] k)) t)
  simpa using h.symm

private lemma character_pow_apply_of_primitive
    (q : WithConv (A →ₐ[k] k)) (t : A)
    (ht : Coalgebra.comul (R := k) t =
      t ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] t) (n : ℕ) :
    (q ^ n) t = n • q t := by
  induction n with
  | zero => simp only [pow_zero, character_one_apply_of_primitive t ht, zero_nsmul]
  | succ n ih =>
      rw [pow_succ, character_mul_apply_of_primitive _ _ t ht, ih, succ_nsmul]

private def primitiveCharacterKernel
    (t : A) (hprimitive : reducedComultiplication (k := k) t = 0) :
    Subgroup (WithConv (A →ₐ[k] k)) where
  carrier := {q | q t = 0}
  one_mem' := character_one_apply_of_primitive t
    ((reducedComultiplication_eq_zero_iff (k := k) t).mp hprimitive)
  mul_mem' := by
    intro q r hq hr
    rw [Set.mem_ofPred_eq,
      character_mul_apply_of_primitive q r t
        ((reducedComultiplication_eq_zero_iff (k := k) t).mp hprimitive),
      hq, hr, add_zero]
  inv_mem' := by
    intro q hq
    change q t = 0 at hq
    change q⁻¹ t = 0
    have hone : (1 : WithConv (A →ₐ[k] k)) t = 0 :=
      character_one_apply_of_primitive t
        ((reducedComultiplication_eq_zero_iff (k := k) t).mp hprimitive)
    have h := character_mul_apply_of_primitive q⁻¹ q t
      ((reducedComultiplication_eq_zero_iff (k := k) t).mp hprimitive)
    have hgroup : q⁻¹ * q = 1 := by simp
    rw [hgroup, hone, hq, add_zero] at h
    exact h.symm

variable [IsDomain A] [Algebra.FiniteType k A]

private lemma polynomial_comap_span_primitive_eq_span_X
    (t : A) (hprimitive : reducedComultiplication (k := k) t = 0) :
    letI : Algebra (Polynomial k) A :=
      (Polynomial.aeval t).toRingHom.toAlgebra
    (Ideal.span ({t} : Set A)).comap (algebraMap (Polynomial k) A) =
      Ideal.span ({Polynomial.X} : Set (Polynomial k)) := by
  letI : Algebra (Polynomial k) A :=
    (Polynomial.aeval t).toRingHom.toAlgebra
  apply le_antisymm
  · intro f hf
    rw [Ideal.mem_comap] at hf
    have hcounit : Bialgebra.counitAlgHom k A t = 0 := by
      simpa using character_one_apply_of_primitive t
        ((reducedComultiplication_eq_zero_iff (k := k) t).mp hprimitive)
    have hcoeff : f.coeff 0 = 0 := by
      have hle : Ideal.span ({t} : Set A) ≤
          RingHom.ker (Bialgebra.counitAlgHom k A) := by
        rw [Ideal.span_le]
        intro x hx
        obtain rfl := Set.mem_singleton_iff.mp hx
        simpa [RingHom.mem_ker] using hcounit
      have hkill : Bialgebra.counitAlgHom k A
          ((algebraMap (Polynomial k) A) f) = 0 :=
        RingHom.mem_ker.mp (hle hf)
      simpa [RingHom.algebraMap_toAlgebra, Polynomial.aeval_def, hcounit] using hkill
    rw [Ideal.mem_span_singleton, Polynomial.X_dvd_iff]
    exact hcoeff
  · rw [Ideal.span_le]
    intro f hf
    obtain rfl := Set.mem_singleton_iff.mp hf
    change (algebraMap (Polynomial k) A) Polynomial.X ∈
      Ideal.span ({t} : Set A)
    rw [RingHom.algebraMap_toAlgebra]
    rw [show (Polynomial.aeval t).toRingHom Polynomial.X = t by
      exact Polynomial.aeval_X (R := k) (A := A) (x := t)]
    exact Ideal.subset_span (Set.mem_singleton t)

private lemma zero_fibre_module_finite
    (htrdeg : Algebra.trdeg k A = 1) (t : A)
    (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0) :
    Module.Finite k (A ⧸ Ideal.span ({t} : Set A)) := by
  let p : Ideal (Polynomial k) := Ideal.span ({Polynomial.X} : Set (Polynomial k))
  let P : Ideal A := Ideal.span ({t} : Set A)
  letI : Algebra (Polynomial k) A :=
    (Polynomial.aeval t).toRingHom.toAlgebra
  have hfinite : Module.Finite (Polynomial k) A :=
    primitive_hopf_curve_aeval_finite htrdeg t ht hprimitive
  letI : Module.Finite (Polynomial k) A := hfinite
  have hcomap : P.comap (algebraMap (Polynomial k) A) = p :=
    polynomial_comap_span_primitive_eq_span_X t hprimitive
  letI : P.LiesOver p := ⟨hcomap.symm⟩
  letI : Module.Finite ((Polynomial k) ⧸ p) (A ⧸ P) := inferInstance
  have hpfinite : Module.Finite k ((Polynomial k) ⧸ p) := by
    change Module.Finite k
      ((Polynomial k) ⧸ Ideal.span ({Polynomial.X} : Set (Polynomial k)))
    rw [show Ideal.span ({Polynomial.X} : Set (Polynomial k)) =
        Ideal.span ({Polynomial.X - Polynomial.C 0} : Set (Polynomial k)) by simp]
    exact Module.Finite.equiv (M := k)
      (Polynomial.quotientSpanXSubCAlgEquiv (R := k) 0).symm.toLinearEquiv
  letI : Module.Finite k ((Polynomial k) ⧸ p) := hpfinite
  exact Module.Finite.trans ((Polynomial k) ⧸ p) (A ⧸ P)

private noncomputable def primitiveCharacterKernelToZeroFibre
    (t : A) (hprimitive : reducedComultiplication (k := k) t = 0) :
    primitiveCharacterKernel t hprimitive →
      (A ⧸ Ideal.span ({t} : Set A)) →ₐ[k] k := fun q ↦
  Ideal.Quotient.liftₐ (Ideal.span ({t} : Set A)) q.1.1 <| by
    intro a ha
    have hle : Ideal.span ({t} : Set A) ≤ RingHom.ker q.1.1 := by
      rw [Ideal.span_le]
      intro x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact q.2
    exact RingHom.mem_ker.mp (hle ha)

private lemma primitiveCharacterKernelToZeroFibre_injective
    (t : A) (hprimitive : reducedComultiplication (k := k) t = 0) :
    Function.Injective (primitiveCharacterKernelToZeroFibre t hprimitive) := by
  intro q r hqr
  apply Subtype.ext
  apply WithConv.ofConv_injective
  have h := congrArg
    (fun z : (A ⧸ Ideal.span ({t} : Set A)) →ₐ[k] k ↦
      z.comp (Ideal.Quotient.mkₐ k (Ideal.span ({t} : Set A)))) hqr
  simpa only [primitiveCharacterKernelToZeroFibre,
    Ideal.Quotient.liftₐ_comp] using h

private theorem primitiveCharacterKernel_finite
    (htrdeg : Algebra.trdeg k A = 1) (t : A)
    (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0) :
    Finite (primitiveCharacterKernel t hprimitive) := by
  letI : Module.Finite k (A ⧸ Ideal.span ({t} : Set A)) :=
    zero_fibre_module_finite htrdeg t ht hprimitive
  exact Finite.of_injective
    (primitiveCharacterKernelToZeroFibre t hprimitive)
    (primitiveCharacterKernelToZeroFibre_injective t hprimitive)

private noncomputable def quotientCharacter (J : Ideal A) [J.IsMaximal] :
    (A ⧸ J) →ₐ[k] k := by
  letI : Field (A ⧸ J) := Ideal.Quotient.field J
  letI : Algebra.FiniteType k (A ⧸ J) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k J)
      (Ideal.Quotient.mkₐ_surjective k J)
  letI : Module.Finite k (A ⧸ J) :=
    finite_of_finite_type_of_isJacobsonRing k (A ⧸ J)
  exact IsAlgClosed.lift

private noncomputable def characterOfMaximal (J : Ideal A) [J.IsMaximal] :
    A →ₐ[k] k :=
  (quotientCharacter (k := k) J).comp (Ideal.Quotient.mkₐ k J)

private lemma characterOfMaximal_eq_zero_iff_mem
    (J : Ideal A) [J.IsMaximal] (a : A) :
    characterOfMaximal (k := k) J a = 0 ↔ a ∈ J := by
  letI : Field (A ⧸ J) := Ideal.Quotient.field J
  constructor
  · intro h
    have hq : Ideal.Quotient.mk J a = 0 :=
      (quotientCharacter (k := k) J).injective
        (by simpa [characterOfMaximal] using h)
    exact Ideal.Quotient.eq_zero_iff_mem.mp hq
  · intro h
    have hq : Ideal.Quotient.mk J a = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr h
    change quotientCharacter (k := k) J (Ideal.Quotient.mk J a) = 0
    rw [hq, map_zero]

private lemma eq_zero_of_forall_character_eq_zero
    (a : A) (ha : ∀ φ : A →ₐ[k] k, φ a = 0) : a = 0 := by
  letI : IsJacobsonRing A :=
    isJacobsonRing_of_finiteType (A := k) (B := A)
  have hjac : a ∈ (⊥ : Ideal A).jacobson := by
    rw [Ideal.jacobson]
    apply Ideal.mem_sInf.mpr
    intro J hJ
    letI : J.IsMaximal := hJ.2
    exact (characterOfMaximal_eq_zero_iff_mem (k := k) J a).mp
      (ha (characterOfMaximal (k := k) J))
  rw [← Ideal.radical_eq_jacobson, Ideal.radical_bot_of_isReduced] at hjac
  exact Ideal.mem_bot.mp hjac

private lemma eq_algebraMap_counit_of_finite_character_range
    (a : A)
    (ha : Set.Finite (Set.range fun φ : A →ₐ[k] k ↦ φ a)) :
    a = algebraMap k A (Bialgebra.counitAlgHom k A a) := by
  let values := ha.toFinset
  have hprod : values.prod (fun c ↦ a - algebraMap k A c) = 0 := by
    apply eq_zero_of_forall_character_eq_zero (k := k)
    intro φ
    rw [map_prod]
    have hmem : φ a ∈ values := ha.mem_toFinset.mpr ⟨φ, rfl⟩
    exact Finset.prod_eq_zero hmem (by simp)
  obtain ⟨c, hc, hzero⟩ := Finset.prod_eq_zero_iff.mp hprod
  have hac : a = algebraMap k A c := sub_eq_zero.mp hzero
  have hcounit := congrArg (Bialgebra.counitAlgHom k A) hac
  have hcounit' : Bialgebra.counitAlgHom k A a = c := by
    simpa using hcounit
  exact hac.trans (congrArg (algebraMap k A) hcounit'.symm)

private noncomputable def translation (q : WithConv (A →ₐ[k] k)) : A →ₐ[k] A :=
  (WithConv.toConv ((Algebra.ofId k A).comp q.ofConv) *
    WithConv.toConv (AlgHom.id k A)).ofConv

private lemma translation_mul (q r : WithConv (A →ₐ[k] k)) :
    (translation q).comp (translation r) = translation (r * q) := by
  have hscalar :
      (WithConv.toConv ((Algebra.ofId k A).comp q.ofConv) *
          WithConv.toConv (AlgHom.id k A)).ofConv.comp
          ((Algebra.ofId k A).comp r.ofConv) =
        (Algebra.ofId k A).comp r.ofConv := by
    ext x
    simp
  have hid :
      (WithConv.toConv ((Algebra.ofId k A).comp q.ofConv) *
          WithConv.toConv (AlgHom.id k A)).ofConv.comp (AlgHom.id k A) =
        (WithConv.toConv ((Algebra.ofId k A).comp q.ofConv) *
          WithConv.toConv (AlgHom.id k A)).ofConv := by rfl
  simp only [translation, AlgHom.comp_convMul_distrib, WithConv.toConv_ofConv]
  rw [hscalar, hid]
  simp only [WithConv.toConv_ofConv, mul_assoc]

private lemma translation_one :
    translation (1 : WithConv (A →ₐ[k] k)) = AlgHom.id k A := by
  have hscalar :
      WithConv.toConv ((Algebra.ofId k A).comp
          (1 : WithConv (A →ₐ[k] k)).ofConv) =
        (1 : WithConv (A →ₐ[k] A)) := by
    apply WithConv.ofConv_injective
    ext x
    simp
  rw [translation, hscalar, one_mul]

private noncomputable def translationEquiv
    (q : WithConv (A →ₐ[k] k)) : A ≃ₐ[k] A :=
  AlgEquiv.ofAlgHom (translation q) (translation q⁻¹)
    (by rw [translation_mul]; simp [translation_one])
    (by rw [translation_mul]; simp [translation_one])

private lemma translation_apply_of_primitive
    (q : WithConv (A →ₐ[k] k)) (t : A)
    (ht : Coalgebra.comul (R := k) t =
      t ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] t) :
    translation q t = algebraMap k A (q t) + t := by
  rw [translation, AlgHom.convMul_apply, ht]
  simp

private lemma translation_aeval_of_primitive
    (q : WithConv (A →ₐ[k] k)) (t : A)
    (ht : Coalgebra.comul (R := k) t =
      t ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] t)
    (f : Polynomial k) :
    translation q (Polynomial.aeval t f) =
      Polynomial.aeval t (Polynomial.taylor (q t) f) := by
  rw [← Polynomial.aeval_algHom_apply (translation q) t f,
    translation_apply_of_primitive q t ht]
  rw [Polynomial.taylor_apply, Polynomial.aeval_comp]
  simp [add_comm]

private noncomputable def commutatorCoordinateMap
    (q : WithConv (A →ₐ[k] k)) : A →ₐ[k] A :=
  (WithConv.toConv ((Algebra.ofId k A).comp q.ofConv) *
    WithConv.toConv (AlgHom.id k A) *
    WithConv.toConv ((Algebra.ofId k A).comp q⁻¹.ofConv) *
    WithConv.toConv (HopfAlgebra.antipodeAlgHom k A)).ofConv

private lemma character_comp_commutatorCoordinateMap
    (q r : WithConv (A →ₐ[k] k)) :
    r.ofConv.comp (commutatorCoordinateMap q) =
      (q * r * q⁻¹ * r⁻¹).ofConv := by
  have hq : r.ofConv.comp ((Algebra.ofId k A).comp q.ofConv) = q.ofConv := by
    ext x
    simp
  have hqinv : r.ofConv.comp ((Algebra.ofId k A).comp q⁻¹.ofConv) = q⁻¹.ofConv := by
    ext x
    simp
  have hr : r.ofConv.comp (AlgHom.id k A) = r.ofConv := rfl
  have hrinv : r.ofConv.comp (HopfAlgebra.antipodeAlgHom k A) = r⁻¹.ofConv := rfl
  simp only [commutatorCoordinateMap, AlgHom.comp_convMul_distrib,
    WithConv.toConv_ofConv]
  rw [hq, hr, hqinv, hrinv]

private lemma character_inv_apply_of_primitive
    (q : WithConv (A →ₐ[k] k)) (t : A)
    (ht : Coalgebra.comul (R := k) t =
      t ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] t) :
    q⁻¹ t = -q t := by
  have h := character_mul_apply_of_primitive q⁻¹ q t ht
  have hone := character_one_apply_of_primitive t ht
  have hgroup : q⁻¹ * q = 1 := by simp
  rw [hgroup, hone] at h
  exact eq_neg_of_add_eq_zero_left h.symm

private lemma character_commutator_apply_primitive
    (q r : WithConv (A →ₐ[k] k)) (t : A)
    (ht : Coalgebra.comul (R := k) t =
      t ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] t) :
    (q * r * q⁻¹ * r⁻¹) t = 0 := by
  rw [character_mul_apply_of_primitive, character_mul_apply_of_primitive,
    character_mul_apply_of_primitive, character_inv_apply_of_primitive,
    character_inv_apply_of_primitive] <;> try assumption
  abel

/-- The convolution group of characters of a primitive Hopf curve is commutative. -/
public theorem primitive_hopf_curve_character_mul_comm
    (htrdeg : Algebra.trdeg k A = 1) (t : A)
    (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0)
    (q r : WithConv (A →ₐ[k] k)) :
    q * r = r * q := by
  let K := primitiveCharacterKernel t hprimitive
  letI : Finite K :=
    primitiveCharacterKernel_finite htrdeg t ht hprimitive
  have ht' : Coalgebra.comul (R := k) t =
      t ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] t :=
    (reducedComultiplication_eq_zero_iff (k := k) t).mp hprimitive
  have hcommutator : q * r * q⁻¹ * r⁻¹ = 1 := by
    apply WithConv.ofConv_injective
    ext a
    let b := commutatorCoordinateMap q a
    have hrange : Set.Finite (Set.range fun s : A →ₐ[k] k ↦ s b) := by
      let values : Set k := Set.range fun x : K ↦ x.1 a
      have hvalues : Set.Finite values := Set.toFinite values
      apply hvalues.subset
      rintro c ⟨s, rfl⟩
      let s' : WithConv (A →ₐ[k] k) := WithConv.toConv s
      let x : K := ⟨q * s' * q⁻¹ * s'⁻¹,
        character_commutator_apply_primitive q s' t ht'⟩
      refine ⟨x, ?_⟩
      have hcomp := character_comp_commutatorCoordinateMap q s'
      simpa [x, b, s'] using
        (congrArg (fun f : A →ₐ[k] k ↦ f a) hcomp).symm
    have hb := eq_algebraMap_counit_of_finite_character_range b hrange
    have hcounit : Bialgebra.counitAlgHom k A b =
        Bialgebra.counitAlgHom k A a := by
      have hcomp := character_comp_commutatorCoordinateMap q
        (1 : WithConv (A →ₐ[k] k))
      have happ := congrArg (fun f : A →ₐ[k] k ↦ f a) hcomp
      simpa [b] using happ
    have hs := congrArg r.ofConv hb
    have hcomp := character_comp_commutatorCoordinateMap q r
    have happ := congrArg (fun f : A →ₐ[k] k ↦ f a) hcomp
    simpa [hcounit] using happ.symm.trans hs
  calc
    q * r = (q * r * q⁻¹ * r⁻¹) * (r * q) := by group
    _ = r * q := by rw [hcommutator, one_mul]

private lemma translation_apply_repr
    (q : WithConv (A →ₐ[k] k)) (a : A) {ι : Type*}
    (r : Coalgebra.Repr k a ι) :
    translation q a =
      ∑ i ∈ r.index, q (r.left i) • r.right i := by
  rw [translation, AlgHom.convMul_apply, ← r.eq]
  simp [Algebra.smul_def]

private def translationSpan (a : A) : Submodule k A :=
  Submodule.span k
    (Set.range fun q : WithConv (A →ₐ[k] k) ↦ translation q a)

private lemma translationSpan_self_mem (a : A) :
    a ∈ translationSpan (k := k) a := by
  have hmem : translation (1 : WithConv (A →ₐ[k] k)) a ∈
      translationSpan (k := k) a :=
    Submodule.subset_span ⟨1, rfl⟩
  simpa [translation_one] using hmem

private lemma translationSpan_stable (a : A)
    (q : WithConv (A →ₐ[k] k)) :
    Set.MapsTo (translation q) (translationSpan (k := k) a)
      (translationSpan (k := k) a) := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨r, rfl⟩ := hx
      rw [← AlgHom.comp_apply, translation_mul]
      exact Submodule.subset_span ⟨r * q, rfl⟩
  | zero => simp
  | add x y hx hy hx' hy' => simpa using Submodule.add_mem _ hx' hy'
  | smul c x hx hx' => simpa using Submodule.smul_mem _ c hx'

private theorem translationSpan_finite (a : A) :
    Module.Finite k (translationSpan (k := k) a) := by
  classical
  let r := Coalgebra.Repr.arbitrary k a
  let V : Submodule k A :=
    Submodule.span k (↑(r.index.image r.right) : Set A)
  have hVfinite : Module.Finite k V :=
    Module.Finite.span_of_finite k (r.index.image r.right).finite_toSet
  letI : Module.Finite k V := hVfinite
  have hle : translationSpan (k := k) a ≤ V := by
    rw [translationSpan, Submodule.span_le]
    rintro x ⟨q, rfl⟩
    change translation q a ∈ V
    rw [translation_apply_repr q a r]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  exact Module.Finite.of_injective (Submodule.inclusion hle)
    (Submodule.inclusion_injective hle)

private noncomputable def translationOnSpan (a : A)
    (q : WithConv (A →ₐ[k] k)) :
    Module.End k (translationSpan (k := k) a) :=
  (translation q).toLinearMap.restrict (translationSpan_stable (k := k) a q)

private lemma translationOnSpan_mul (a : A)
    (q r : WithConv (A →ₐ[k] k)) :
    translationOnSpan (k := k) a q * translationOnSpan (k := k) a r =
      translationOnSpan (k := k) a (r * q) := by
  ext x
  exact AlgHom.congr_fun (translation_mul q r) x

private lemma translationOnSpan_one (a : A) :
    translationOnSpan (k := k) a (1 : WithConv (A →ₐ[k] k)) = 1 := by
  ext x
  change translation (1 : WithConv (A →ₐ[k] k)) x = x
  rw [translation_one]
  rfl

private lemma translationOnSpan_pow (a : A)
    (q : WithConv (A →ₐ[k] k)) (n : ℕ) :
    translationOnSpan (k := k) a q ^ n =
      translationOnSpan (k := k) a (q ^ n) := by
  induction n with
  | zero => simp [translationOnSpan_one]
  | succ n hn =>
      rw [pow_succ, hn, translationOnSpan_mul]
      congr 1
      exact (Commute.self_pow q n).eq

private lemma counit_translation
    (q : WithConv (A →ₐ[k] k)) (a : A) :
    Bialgebra.counitAlgHom k A (translation q a) = q a := by
  let r := Coalgebra.Repr.arbitrary k a
  have hright :
      ∑ i ∈ r.index, Coalgebra.counit (R := k) (r.right i) • r.left i = a := by
    have h := Coalgebra.sum_tmul_counit_eq r
    apply_fun (TensorProduct.rid k A) at h
    simpa only [map_sum, TensorProduct.rid_tmul, one_smul] using h
  rw [translation_apply_repr q a r, map_sum]
  calc
    ∑ i ∈ r.index,
        Bialgebra.counitAlgHom k A (q (r.left i) • r.right i) =
        q (∑ i ∈ r.index,
          Coalgebra.counit (R := k) (r.right i) • r.left i) := by
            simp [mul_comm]
    _ = q a := by rw [hright]

private lemma translation_eq_id_iff
    (q : WithConv (A →ₐ[k] k)) :
    translation q = AlgHom.id k A ↔ q = 1 := by
  constructor
  · intro h
    apply WithConv.ofConv_injective
    ext a
    have ha := congrArg
      (fun f : A →ₐ[k] A ↦ Bialgebra.counitAlgHom k A (f a)) h
    rw [counit_translation] at ha
    simpa using ha
  · rintro rfl
    exact translation_one

private lemma exists_moved_coordinate
    {q : WithConv (A →ₐ[k] k)} (hq : q ≠ 1) :
    ∃ a : A, translation q a ≠ a := by
  have hne : translation q ≠ AlgHom.id k A :=
    (translation_eq_id_iff q).not.mpr hq
  by_contra h
  apply hne
  ext a
  by_contra ha
  exact h ⟨a, ha⟩

private lemma exists_nontrivial_eigenvalue_of_finite_order
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (f : Module.End k V) (n : ℕ) (hncast : (n : k) ≠ 0)
    (hpow : f ^ n = 1) (hf : f ≠ 1) :
    ∃ μ : k, μ ≠ 1 ∧ f.eigenspace μ ≠ ⊥ := by
  have hpoly : Polynomial.aeval f
      (Polynomial.X ^ n - (1 : Polynomial k)) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, hpow]
    simp
  have hsemi : f.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero
      ((Polynomial.X_pow_sub_one_separable_iff.mpr hncast).squarefree) hpoly
  by_contra hex
  have hall : ∀ μ : k, f.eigenspace μ ≠ ⊥ → μ = 1 := by
    intro μ hμ
    by_contra hμone
    exact hex ⟨μ, hμone, hμ⟩
  have hle : (⨆ μ : k, f.eigenspace μ) ≤ f.eigenspace 1 := by
    apply iSup_le
    intro μ
    by_cases hμ : f.eigenspace μ = ⊥
    · simp [hμ]
    · rw [hall μ hμ]
  have heig : f.eigenspace 1 = ⊤ := by
    apply top_unique
    rw [← hsemi.iSup_eigenspace_eq_top]
    exact hle
  apply hf
  ext x
  have hx : x ∈ f.eigenspace 1 := heig.symm ▸ Submodule.mem_top
  simpa using (Module.End.mem_eigenspace_iff.mp hx)

private lemma exists_nontrivial_common_eigenspace_of_commuting_family
    {ι V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [Nontrivial V] (f : ι → Module.End k V)
    (hcomm : Pairwise fun i j => Commute (f i) (f j)) :
    ∃ χ : ι → k, Nontrivial ↥(⨅ i, (f i).eigenspace (χ i)) := by
  generalize hdim : Module.finrank k V = n
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
      choose χ hχ using fun i => Module.End.exists_eigenvalue (f i)
      by_cases hall : ∀ i, (f i).eigenspace (χ i) = ⊤
      · refine ⟨χ, ?_⟩
        have htop : (⨅ i, (f i).eigenspace (χ i)) = ⊤ := by simp [hall]
        rw [htop]
        exact Equiv.nontrivial Submodule.topEquiv.toEquiv
      · obtain ⟨i, hi⟩ := not_forall.mp hall
        let E : Submodule k V := (f i).eigenspace (χ i)
        haveI : Nontrivial E := (Submodule.nontrivial_iff_ne_bot).mpr (hχ i)
        have hE_lt : Module.finrank k E < n := by
          rw [← hdim]
          exact Submodule.finrank_lt hi
        have hstable (j : ι) : Set.MapsTo (f j) E E := by
          dsimp [E]
          by_cases hij : i = j
          · subst j
            exact Module.End.mapsTo_genEigenspace_of_comm
              (Commute.refl _) (χ i) 1
          · exact Module.End.mapsTo_genEigenspace_of_comm
              (hcomm hij) (χ i) 1
        let fE : ι → Module.End k E := fun j => (f j).restrict (hstable j)
        have hcommE : Pairwise fun a b => Commute (fE a) (fE b) := by
          intro a b hab
          apply LinearMap.ext
          intro x
          apply Subtype.ext
          have hc := LinearMap.congr_fun (hcomm hab).eq (x : E)
          exact hc
        obtain ⟨χE, hχE⟩ := ih (Module.finrank k E) hE_lt fE hcommE rfl
        let W : Submodule k E := ⨅ j, (fE j).eigenspace (χE j)
        letI : Nontrivial W := hχE
        obtain ⟨x, hx⟩ := exists_ne (0 : W)
        refine ⟨χE, ?_⟩
        rw [Submodule.nontrivial_iff_ne_bot]
        intro hbot
        have hxmem : (x : E) ∈ ⨅ j, (fE j).eigenspace (χE j) := x.property
        have hxmem' : (x : V) ∈ ⨅ j, (f j).eigenspace (χE j) := by
          rw [Submodule.mem_iInf] at hxmem ⊢
          intro j
          exact Module.End.eigenspace_restrict_le_eigenspace
            (f j) (hstable j) (χE j) ⟨x, hxmem j, rfl⟩
        rw [hbot] at hxmem'
        have hxzeroV : (x : V) = 0 := (Submodule.mem_bot k).mp hxmem'
        apply hx
        apply Subtype.ext
        apply Subtype.ext
        exact hxzeroV

private lemma translationOnSpan_commute
    (htrdeg : Algebra.trdeg k A = 1) (t : A)
    (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0)
    (a : A) (q r : WithConv (A →ₐ[k] k)) :
    Commute (translationOnSpan (k := k) a q)
      (translationOnSpan (k := k) a r) := by
  change translationOnSpan (k := k) a q * translationOnSpan (k := k) a r =
    translationOnSpan (k := k) a r * translationOnSpan (k := k) a q
  rw [translationOnSpan_mul, translationOnSpan_mul,
    primitive_hopf_curve_character_mul_comm htrdeg t ht hprimitive q r]

private theorem exists_common_translation_eigenfunction_of_finite_order
    (htrdeg : Algebra.trdeg k A = 1) (t : A)
    (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0)
    (q : WithConv (A →ₐ[k] k)) (n : ℕ) (hncast : (n : k) ≠ 0)
    (hqpow : q ^ n = 1) (hq : q ≠ 1) :
    ∃ (μ : k) (χ : WithConv (A →ₐ[k] k) → k) (z : A),
      μ ≠ 1 ∧ z ≠ 0 ∧
      translation q z = algebraMap k A μ * z ∧
      ∀ r : WithConv (A →ₐ[k] k),
        translation r z = algebraMap k A (χ r) * z := by
  obtain ⟨a, ha⟩ := exists_moved_coordinate hq
  let W : Submodule k A := translationSpan (k := k) a
  letI : Module.Finite k W := translationSpan_finite a
  let f : Module.End k W := translationOnSpan (k := k) a q
  have hfpow : f ^ n = 1 := by
    dsimp [f]
    rw [translationOnSpan_pow, hqpow, translationOnSpan_one]
  have hfne : f ≠ 1 := by
    intro hf
    have hfa := LinearMap.congr_fun hf
      (⟨a, translationSpan_self_mem (k := k) a⟩ : W)
    have hfa' := congrArg Subtype.val hfa
    change translation q a = a at hfa'
    exact ha hfa'
  obtain ⟨μ, hμone, hμ⟩ :=
    exists_nontrivial_eigenvalue_of_finite_order f n hncast hfpow hfne
  let E : Submodule k W := f.eigenspace μ
  haveI : Nontrivial E := (Submodule.nontrivial_iff_ne_bot).mpr hμ
  have hstable (r : WithConv (A →ₐ[k] k)) :
      Set.MapsTo (translationOnSpan (k := k) a r) E E := by
    dsimp [E]
    exact Module.End.mapsTo_genEigenspace_of_comm
      (translationOnSpan_commute htrdeg t ht hprimitive a q r) μ 1
  let fE : WithConv (A →ₐ[k] k) → Module.End k E := fun r =>
    (translationOnSpan (k := k) a r).restrict (hstable r)
  have hcommE : Pairwise fun r s => Commute (fE r) (fE s) := by
    intro r s hrs
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hcomm := translationOnSpan_commute htrdeg t ht hprimitive a r s
    exact LinearMap.congr_fun hcomm.eq (x : E)
  obtain ⟨χ, hχ⟩ :=
    exists_nontrivial_common_eigenspace_of_commuting_family
      (k := k) (ι := WithConv (A →ₐ[k] k)) (V := E) fE hcommE
  let C : Submodule k E := ⨅ r : WithConv (A →ₐ[k] k),
    Module.End.eigenspace (R := k) (M := E) (fE r) (χ r)
  letI : Nontrivial C := hχ
  obtain ⟨z, hz⟩ := exists_ne (0 : C)
  let zA : A := (((z : E) : W) : A)
  have hzA : zA ≠ 0 := by
    intro hzA0
    apply hz
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact hzA0
  have hweight (r : WithConv (A →ₐ[k] k)) :
      translation r zA = algebraMap k A (χ r) * zA := by
    have hzall : ∀ s : WithConv (A →ₐ[k] k),
        (z : E) ∈ (fE s).eigenspace (χ s) := by
      simpa only [C, Submodule.mem_iInf] using z.property
    have hzmem : (z : E) ∈ (fE r).eigenspace (χ r) := hzall r
    have heig := Module.End.mem_eigenspace_iff.mp hzmem
    have heigW := congrArg (fun x : E => (x : W)) heig
    change (translationOnSpan (k := k) a r) (z : E) =
      (χ r) • ((z : E) : W) at heigW
    calc
      translation r zA =
          ((translationOnSpan (k := k) a r) ((z : E) : W) : A) := by
            rfl
      _ = ((χ r) • ((z : E) : W) : W) := congrArg Subtype.val heigW
      _ = algebraMap k A (χ r) * zA := by
        simp only [Submodule.coe_smul, Algebra.smul_def, zA]
  have hqweight : translation q zA = algebraMap k A μ * zA := by
    have heig := Module.End.mem_eigenspace_iff.mp (z : E).property
    change (translationOnSpan (k := k) a q) ((z : E) : W) =
      μ • ((z : E) : W) at heig
    calc
      translation q zA =
          ((translationOnSpan (k := k) a q) ((z : E) : W) : A) := by
            rfl
      _ = (μ • ((z : E) : W) : W) := congrArg Subtype.val heig
      _ = algebraMap k A μ * zA := by
        simp only [Submodule.coe_smul, Algebra.smul_def, zA]
  exact ⟨μ, χ, zA, hμone, hzA, hqweight, hweight⟩

private theorem common_translation_eigenweight_pow_eq_one
    (htrdeg : Algebra.trdeg k A = 1) (t : A) (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0)
    (χ : WithConv (A →ₐ[k] k) → k) (z : A) (hz : z ≠ 0)
    (hweight : ∀ r : WithConv (A →ₐ[k] k),
      translation r z = algebraMap k A (χ r) * z) :
    ∃ d : ℕ, 0 < d ∧ ∀ r : WithConv (A →ₐ[k] k), χ r ^ d = 1 := by
  letI : Algebra (Polynomial k) A :=
    (Polynomial.aeval t).toRingHom.toAlgebra
  letI : Module.Finite (Polynomial k) A :=
    primitive_hopf_curve_aeval_finite htrdeg t ht hprimitive
  have hinj : Function.Injective (algebraMap (Polynomial k) A) := by
    change Function.Injective (Polynomial.aeval t)
    exact transcendental_iff_injective.mp ht
  letI : Module.IsTorsionFree (Polynomial k) A :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  letI : Module.Free (Polynomial k) A :=
    Module.free_of_finite_type_torsion_free'
  let d := Module.finrank (Polynomial k) A
  have hd : 0 < d := Module.finrank_pos
  let N : Polynomial k := Algebra.norm (Polynomial k) z
  have hN : N ≠ 0 := Algebra.norm_ne_zero_iff.mpr hz
  have hcomul : Coalgebra.comul (R := k) t =
      t ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] t :=
    (reducedComultiplication_eq_zero_iff (k := k) t).mp hprimitive
  refine ⟨d, hd, ?_⟩
  intro r
  have hχ : χ r ≠ 0 := by
    intro hχ0
    have hztrans : translation r z = 0 := by
      simpa only [hχ0, map_zero, zero_mul] using hweight r
    have hztrans' : translationEquiv r z = translationEquiv r 0 := by
      change translation r z = translation r 0
      simpa only [map_zero] using hztrans
    exact hz ((translationEquiv r).injective hztrans')
  have hcomp :
      (algebraMap (Polynomial k) A).comp
          (Polynomial.taylorEquiv (r t)).toRingEquiv.toRingHom =
        (translationEquiv r).toRingEquiv.toRingHom.comp
          (algebraMap (Polynomial k) A) := by
    apply DFunLike.ext _ _
    intro f
    change Polynomial.aeval t (Polynomial.taylor (r t) f) =
      translation r (Polynomial.aeval t f)
    exact (translation_aeval_of_primitive r t hcomul f).symm
  have hnorm :
      Polynomial.taylor (r t) N =
        Algebra.norm (Polynomial k) (translation r z) := by
    have h := congrArg (Polynomial.taylorEquiv (r t))
      (Algebra.norm_eq_of_equiv_equiv
        (Polynomial.taylorEquiv (r t)).toRingEquiv
        (translationEquiv r).toRingEquiv hcomp z)
    calc
      Polynomial.taylor (r t) N =
          (Polynomial.taylorEquiv (r t))
            ((Polynomial.taylorEquiv (r t)).toRingEquiv.symm
              (Algebra.norm (Polynomial k) ((translationEquiv r) z))) := h
      _ = Algebra.norm (Polynomial k) (translation r z) := by
        exact (Polynomial.taylorEquiv (r t)).apply_symm_apply _
  have hscalar :
      algebraMap k A (χ r) =
        algebraMap (Polynomial k) A (Polynomial.C (χ r)) := by
    change algebraMap k A (χ r) =
      Polynomial.aeval t (Polynomial.C (χ r))
    exact (Polynomial.aeval_C t (χ r)).symm
  have hnorm' :
      Polynomial.taylor (r t) N = Polynomial.C (χ r) ^ d * N := by
    rw [hnorm, hweight r, hscalar, map_mul, Algebra.norm_algebraMap]
  have hlead := congrArg Polynomial.leadingCoeff hnorm'
  simp only [Polynomial.leadingCoeff_taylor, Polynomial.leadingCoeff_mul,
    Polynomial.leadingCoeff_pow, Polynomial.leadingCoeff_C, N] at hlead
  apply mul_right_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr hN)
  simpa only [one_mul] using hlead.symm

private lemma finite_range_of_pow_eq_one {ι : Type*} (f : ι → k)
    (d : ℕ) (hd : 0 < d) (hpow : ∀ i, f i ^ d = 1) :
    Set.Finite (Set.range f) := by
  let P : Polynomial k := Polynomial.X ^ d - 1
  refine (Polynomial.rootSet_finite P k).subset ?_
  rintro y ⟨i, rfl⟩
  rw [Polynomial.mem_rootSet]
  constructor
  · exact Polynomial.X_pow_sub_C_ne_zero hd 1
  · simp only [P, map_sub, map_pow, Polynomial.aeval_X, map_one, hpow i,
      sub_self]

private theorem eq_one_of_prime_order_ne_char
    {p ℓ : ℕ} [CharP k p] (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (htrdeg : Algebra.trdeg k A = 1) (t : A) (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0)
    (q : WithConv (A →ₐ[k] k)) (hqpow : q ^ ℓ = 1) : q = 1 := by
  by_contra hqne
  have hℓcast : (ℓ : k) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime k hℓ hℓp.symm
  obtain ⟨μ, χ, z, hμone, hz, hqweight, hweight⟩ :=
    exists_common_translation_eigenfunction_of_finite_order
      htrdeg t ht hprimitive q ℓ hℓcast hqpow hqne
  obtain ⟨d, hd, hχpow⟩ :=
    common_translation_eigenweight_pow_eq_one
      htrdeg t ht hprimitive χ z hz hweight
  have hχfinite : Set.Finite (Set.range χ) :=
    finite_range_of_pow_eq_one χ d hd hχpow
  have hvalue (r : WithConv (A →ₐ[k] k)) :
      r z = χ r * Bialgebra.counitAlgHom k A z := by
    rw [← counit_translation r z, hweight r, map_mul]
    rw [(Bialgebra.counitAlgHom k A).commutes]
    simp
  have hzfinite :
      Set.Finite (Set.range fun r : A →ₐ[k] k => r z) := by
    have himage := hχfinite.image
      (fun c : k => c * Bialgebra.counitAlgHom k A z)
    refine himage.subset ?_
    rintro y ⟨r, rfl⟩
    exact ⟨χ (WithConv.toConv r), ⟨WithConv.toConv r, rfl⟩,
      (hvalue (WithConv.toConv r)).symm⟩
  have hzscalar := eq_algebraMap_counit_of_finite_character_range z hzfinite
  have hqfix : translation q z = z := by
    rw [hzscalar]
    exact (translation q).commutes _
  have hmapμ : algebraMap k A μ = 1 := by
    apply mul_right_cancel₀ hz
    calc
      algebraMap k A μ * z = translation q z := hqweight.symm
      _ = z := hqfix
      _ = 1 * z := (one_mul z).symm
  apply hμone
  apply (algebraMap k A).injective
  simpa only [map_one] using hmapμ

private theorem character_isOfFinOrder
    {p : ℕ} [CharP k p] [Fact p.Prime]
    (htrdeg : Algebra.trdeg k A = 1) (t : A) (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0)
    (q : WithConv (A →ₐ[k] k)) : IsOfFinOrder q := by
  have hcomul : Coalgebra.comul (R := k) t =
      t ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] t :=
    (reducedComultiplication_eq_zero_iff (k := k) t).mp hprimitive
  have hkernel : q ^ p ∈ primitiveCharacterKernel t hprimitive := by
    change (q ^ p) t = 0
    rw [character_pow_apply_of_primitive q t hcomul p,
      ← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]
  let K := primitiveCharacterKernel t hprimitive
  letI : Finite K := primitiveCharacterKernel_finite htrdeg t ht hprimitive
  let x : K := ⟨q ^ p, hkernel⟩
  have hx : IsOfFinOrder x := isOfFinOrder_of_finite x
  obtain ⟨n, hn, hxpow⟩ := hx.exists_pow_eq_one
  have hxpow' : (q ^ p) ^ n = 1 := by
    have h := congrArg (fun y : K => (y : WithConv (A →ₐ[k] k))) hxpow
    simpa only [x, Subgroup.coe_pow, Subgroup.coe_one] using h
  have hqpow : IsOfFinOrder (q ^ p) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hxpow'⟩
  exact hqpow.of_pow (Fact.out : Nat.Prime p).ne_zero

public theorem primitive_hopf_curve_characters_are_pGroup
    {p : ℕ} [CharP k p] [Fact p.Prime] [IsIntegrallyClosed A]
    (htrdeg : Algebra.trdeg k A = 1) (t : A) (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0) :
    IsPGroup p (WithConv (A →ₐ[k] k)) := by
  apply IsPGroup.iff_orderOf.mpr
  intro q
  have hqfin : IsOfFinOrder q :=
    character_isOfFinOrder htrdeg t ht hprimitive q
  have horder : orderOf q ≠ 0 := hqfin.orderOf_pos.ne'
  refine ⟨(orderOf q).primeFactorsList.length,
    Nat.eq_prime_pow_of_unique_prime_dvd horder ?_⟩
  intro ℓ hℓ hℓdvd
  by_contra hℓp
  let y : WithConv (A →ₐ[k] k) := q ^ (orderOf q / ℓ)
  have hyorder : orderOf y = ℓ := by
    exact orderOf_pow_orderOf_div horder hℓdvd
  have hypow : y ^ ℓ = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hyorder]
  have hyone : y = 1 :=
    eq_one_of_prime_order_ne_char hℓ hℓp htrdeg t ht hprimitive y hypow
  have hyorder' : orderOf y = 1 := by rw [hyone, orderOf_one]
  exact hℓ.ne_one (hyorder.symm.trans hyorder')

end Theory.AlgebraicGroup
