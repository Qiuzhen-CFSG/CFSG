module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Theory.AlgebraicGroup.CoordinateRing.Hopf.ConilpotentCurve
import all Theory.AlgebraicGroup.CoordinateRing.Hopf.ConilpotentCurve
public import Theory.AlgebraicGroup.CoordinateRing.Hopf.PrimitiveCurveSeparableKernelCharP
import all Theory.AlgebraicGroup.CoordinateRing.Hopf.PrimitiveCurveSeparableKernelCharP
public import Theory.AlgebraicGroup.CoordinateRing.Hopf.PrimitiveCurveAffineSeparableTranslation
public import Theory.AlgebraicGroup.CoordinateRing.Hopf.PolynomialArtinSchreierCocycle
import all Theory.AlgebraicGroup.CoordinateRing.Hopf.PolynomialArtinSchreierCocycle

/-!
# Artin--Schreier cocycle descent for a primitive Hopf curve

Let `t` be a transcendental primitive element of a normal affine Hopf curve in
characteristic `p`.  Given an index-`p` fixed field and a regular, counit-zero
element `s0` translated to `s0 + 1` by a lifted primitive character, this module
descends both the Artin--Schreier difference of `s0` and its actual reduced
coproduct to polynomials in `t`.  The resulting bivariate polynomial is
normalized, symmetric, and an additive two-cocycle; its Artin--Schreier
difference is the additive coboundary of the univariate polynomial.  The same
argument proves that `s0` generates the fixed field and that the subgroup is
strictly smaller than the full Galois group.

The central tensor descent does not infer polynomiality from the
Artin--Schreier equation.  Regular character translations first show that every
left slice of the reduced coproduct lies in `k[t]`; cocommutativity gives the
same conclusion for right slices.  Character separation, quotient exactness,
and flatness then identify the intersection of the two one-sided polynomial
tensor subspaces with the tensor square of `k[t]`, producing the bivariate
polynomial. Polynomial descent of `s0 ^ p - s0` instead uses Galois invariance
followed by the intersection of the rational function field with the
integrally closed coordinate ring.

The local `import all` edges expose the implementation equations for reduced
comultiplication, regular character translation, and polynomial coboundaries
only while proving this module.  The resulting public tensor-evaluation lemma
lets later modules rebase a descended cocycle without exposing those bodies.
The public boundary otherwise remains the ordinary imported APIs.  This is the
independent index-`p` descent step in the positive-characteristic primitive
function-field argument, following the Artin--Schreier layer in Borel, *Linear
Algebraic Groups*, Theorem 10.9 and the post-11.6 discussion.
-/

open scoped TensorProduct

namespace Theory.AlgebraicGroup

noncomputable section

universe u v

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

section BivariateEvaluation

variable {k : Type u} {A : Type v}
variable [Field k] [CommRing A] [Algebra k A]

public noncomputable def bivariateAeval (t : A) :
    BivariatePolynomial k →ₐ[k] A ⊗[k] A := by
  let e := Polynomial.aeval (R := k) (t ⊗ₜ[k] (1 : A))
  letI : Algebra (Polynomial k) (A ⊗[k] A) := e.toRingHom.toAlgebra
  letI : IsScalarTower k (Polynomial k) (A ⊗[k] A) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (e.commutes x).symm
  exact (Polynomial.aeval (R := Polynomial k) ((1 : A) ⊗ₜ[k] t)).restrictScalars k

private noncomputable def tensorEvalPair
    {B C : Type*} [CommRing B] [Algebra k B] [CommRing C] [Algebra k C]
    (q : B →ₐ[k] k) (r : C →ₐ[k] k) : B ⊗[k] C →ₐ[k] k :=
  Algebra.TensorProduct.lift q r fun _ _ ↦ Commute.all _ _

/-- Evaluating a constant-in-the-second-variable polynomial inserts its value
in the left tensor factor. -/
public lemma bivariateAeval_C (t : A) (f : Polynomial k) :
    bivariateAeval t (Polynomial.C f) = Polynomial.aeval t f ⊗ₜ[k] (1 : A) := by
  let e := Polynomial.aeval (R := k) (t ⊗ₜ[k] (1 : A))
  letI : Algebra (Polynomial k) (A ⊗[k] A) := e.toRingHom.toAlgebra
  letI : IsScalarTower k (Polynomial k) (A ⊗[k] A) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (e.commutes x).symm
  simp only [bivariateAeval]
  change (Polynomial.aeval (R := Polynomial k) ((1 : A) ⊗ₜ[k] t))
    (Polynomial.C f) = _
  rw [Polynomial.aeval_C]
  change Polynomial.aeval (t ⊗ₜ[k] (1 : A)) f = _
  have h : Polynomial.aeval (t ⊗ₜ[k] (1 : A)) =
      (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] A).comp
        (Polynomial.aeval t) := by
    apply Polynomial.algHom_ext
    simp
  simpa using DFunLike.congr_fun h f

/-- The outer polynomial variable evaluates to `1` tensored with `t`. -/
public lemma bivariateAeval_X (t : A) :
    bivariateAeval t Polynomial.X = (1 : A) ⊗ₜ[k] t := by
  let e := Polynomial.aeval (R := k) (t ⊗ₜ[k] (1 : A))
  letI : Algebra (Polynomial k) (A ⊗[k] A) := e.toRingHom.toAlgebra
  letI : IsScalarTower k (Polynomial k) (A ⊗[k] A) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (e.commutes x).symm
  change Polynomial.aeval (R := Polynomial k) ((1 : A) ⊗ₜ[k] t) Polynomial.X = _
  simp

private lemma tensorEvalPair_bivariateAeval (q r : A →ₐ[k] k) (t : A)
    (C : BivariatePolynomial k) :
    tensorEvalPair q r (bivariateAeval t C) = C.evalEval (q t) (r t) := by
  induction C using Polynomial.induction_on' with
  | add a b ha hb =>
      simp only [map_add, Polynomial.evalEval_add, ha, hb]
  | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp only [map_mul, map_pow, bivariateAeval_C, bivariateAeval_X,
        tensorEvalPair, Algebra.TensorProduct.lift_tmul, map_one, one_mul,
        Polynomial.evalEval_mul, Polynomial.evalEval_C, Polynomial.evalEval_pow,
        Polynomial.evalEval_X]
      rw [← Polynomial.aeval_algHom_apply q t a]
      simp [Polynomial.aeval_def]

private lemma map_evalRingHom_eval_local (x y : k) (C : BivariatePolynomial k) :
    (C.map (Polynomial.evalRingHom x)).eval y = C.evalEval x y := by
  induction C using Polynomial.induction_on' with
  | add a b ha hb => simp [ha, hb]
  | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp [Polynomial.evalEval]

private lemma tensorEvalPair_tensorMap
    {B C : Type*} [CommRing B] [Algebra k B] [CommRing C] [Algebra k C]
    (f : B →ₐ[k] A) (g : C →ₐ[k] A) (q r : A →ₐ[k] k)
    (z : B ⊗[k] C) :
    tensorEvalPair q r (Algebra.TensorProduct.map f g z) =
      tensorEvalPair (q.comp f) (r.comp g) z := by
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp [tensorEvalPair]
  · intro x y
    simp [tensorEvalPair]
  · intro x y hx hy
    simp [map_add, hx, hy]

private lemma bivariateAeval_universal_injective [Infinite k] :
    Function.Injective
      (bivariateAeval (k := k) (A := Polynomial k) Polynomial.X) := by
  intro C D hCD
  apply Polynomial.ext
  intro n
  apply Polynomial.funext
  intro x
  have hxy : ∀ y : k, C.evalEval x y = D.evalEval x y := by
    intro y
    have h := congrArg
      (tensorEvalPair (Polynomial.aeval x) (Polynomial.aeval y)) hCD
    simpa [tensorEvalPair_bivariateAeval] using h
  have hmap : C.map (Polynomial.evalRingHom x) =
      D.map (Polynomial.evalRingHom x) := by
    apply Polynomial.funext
    intro y
    simpa [map_evalRingHom_eval_local] using hxy y
  have hcoeff := congrArg (fun P : Polynomial k ↦ P.coeff n) hmap
  simpa using hcoeff

private lemma bivariateAeval_map_C (t : A) (f : Polynomial k) :
    bivariateAeval t (f.map (Polynomial.C : k →+* Polynomial k)) =
      (1 : A) ⊗ₜ[k] Polynomial.aeval t f := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
      rw [Polynomial.map_add, map_add, hf, hg, map_add]
      exact (TensorProduct.tmul_add (1 : A)
        (Polynomial.aeval t f) (Polynomial.aeval t g)).symm
  | monomial n a =>
      rw [Polynomial.map_monomial]
      nth_rewrite 1 [← Polynomial.C_mul_X_pow_eq_monomial]
      rw [map_mul, map_pow, bivariateAeval_C, bivariateAeval_X,
        Polynomial.aeval_C, Algebra.TensorProduct.tmul_pow, one_pow,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [Polynomial.aeval_def, Polynomial.eval₂_monomial]
      simpa only [Algebra.smul_def, mul_one] using
        (TensorProduct.smul_tmul a (1 : A) (t ^ n))

private lemma bivariateAeval_addSub (t : A) (f : Polynomial k) :
    bivariateAeval t (bivariateAddSub f) =
      Polynomial.aeval ((t ⊗ₜ[k] (1 : A)) + ((1 : A) ⊗ₜ[k] t)) f := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
      rw [bivariateAddSub] at hf hg ⊢
      rw [Polynomial.eval₂_add, map_add, hf, hg]
      exact (map_add (Polynomial.aeval
        ((t ⊗ₜ[k] (1 : A)) + ((1 : A) ⊗ₜ[k] t))) f g).symm
  | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      rw [bivariateAddSub, Polynomial.eval₂_mul, Polynomial.eval₂_C,
        Polynomial.eval₂_pow, Polynomial.eval₂_X, map_mul, map_pow,
        map_add, bivariateAeval_C]
      change bivariateAeval t (Polynomial.C (Polynomial.C a)) *
          ((Polynomial.aeval t Polynomial.X ⊗ₜ[k] (1 : A)) +
            bivariateAeval t Polynomial.X) ^ n = _
      rw [bivariateAeval_C, bivariateAeval_X,
        Polynomial.aeval_C, Polynomial.aeval_X, map_mul, map_pow,
        Polynomial.aeval_C, Polynomial.aeval_X]
      rw [Algebra.TensorProduct.algebraMap_apply]

private lemma bivariateAeval_universal_surjective :
    Function.Surjective
      (bivariateAeval (k := k) (A := Polynomial k) Polynomial.X) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul f g =>
      refine ⟨Polynomial.C f * g.map (Polynomial.C : k →+* Polynomial k), ?_⟩
      rw [map_mul, bivariateAeval_C, bivariateAeval_map_C,
        Algebra.TensorProduct.tmul_mul_tmul]
      simp
  | add x y hx hy =>
      obtain ⟨C, rfl⟩ := hx
      obtain ⟨D, rfl⟩ := hy
      refine ⟨C + D, ?_⟩
      simp

end BivariateEvaluation

section HopfBivariateEvaluation

variable {k : Type u} {A : Type v}
variable [Field k] [CommRing A] [HopfAlgebra k A]

/-- Evaluating the polynomial coboundary of `f` at a primitive Hopf
coordinate is the reduced coproduct of `f(t)`. -/
public lemma bivariateAeval_additiveCoboundary
    (t : A) (hprimitive : reducedComultiplication (k := k) t = 0)
    (f : Polynomial k) :
    bivariateAeval t (additiveCoboundary f) =
      reducedComultiplication (k := k) (Polynomial.aeval t f) := by
  rw [reducedComultiplication, additiveCoboundary]
  rw [map_sub, map_sub, bivariateAeval_addSub, bivariateLeft,
    bivariateAeval_C, bivariateRight, bivariateAeval_map_C]
  rw [← (reducedComultiplication_eq_zero_iff (k := k) t).mp hprimitive]
  change Polynomial.aeval ((Bialgebra.comulAlgHom k A) t) f - _ - _ = _
  rw [Polynomial.aeval_algHom_apply]
  rfl

end HopfBivariateEvaluation

variable {k : Type u} {A : Type v}
variable [Field k] [IsAlgClosed k] [CommRing A] [HopfAlgebra k A]
variable [IsDomain A] [Algebra.FiniteType k A]
variable {p : Nat}

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

private lemma exists_character_ne_zero (a : A) (ha : a ≠ 0) :
    ∃ φ : A →ₐ[k] k, φ a ≠ 0 := by
  by_contra h
  push Not at h
  exact ha (eq_zero_of_forall_character_eq_zero (k := k) a h)

private lemma exists_character_apply_eq
    (htrdeg : Algebra.trdeg k A = 1) (t : A)
    (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0)
    (x : k) : ∃ q : A →ₐ[k] k, q t = x := by
  let P := Polynomial k
  letI : Algebra P A := (Polynomial.aeval t).toRingHom.toAlgebra
  letI : Module.Finite P A :=
    primitive_hopf_curve_aeval_finite htrdeg t ht hprimitive
  letI : FaithfulSMul P A :=
    (faithfulSMul_iff_algebraMap_injective P A).mpr
      (transcendental_iff_injective.mp ht)
  let I : Ideal P := RingHom.ker (Polynomial.evalRingHom x)
  have heval : Function.Surjective (Polynomial.evalRingHom x) := by
    intro y
    exact ⟨Polynomial.C y, by simp⟩
  letI : I.IsMaximal := RingHom.ker_isMaximal_of_surjective
    (Polynomial.evalRingHom x) heval
  obtain ⟨J, hJmax, hJover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := A) I
  letI : J.IsMaximal := hJmax
  letI : J.LiesOver I := hJover
  let q := characterOfMaximal (k := k) J
  refine ⟨q, sub_eq_zero.mp ?_⟩
  have hqx : q (algebraMap k A x) = x := by simp
  rw [← hqx]
  rw [← map_sub, characterOfMaximal_eq_zero_iff_mem]
  have hpoly : Polynomial.X - Polynomial.C x ∈ I := by
    change Polynomial.evalRingHom x
      (Polynomial.X - Polynomial.C x) = 0
    simp
  have hmem := (Ideal.mem_of_liesOver (P := J) (p := I)
    (Polynomial.X - Polynomial.C x)).mp hpoly
  change Polynomial.aeval t (Polynomial.X - Polynomial.C x) ∈ J at hmem
  simpa [q] using hmem

private noncomputable def evalLeft (q : A →ₐ[k] k) :
    A ⊗[k] A →ₐ[k] A :=
  Algebra.TensorProduct.lift ((Algebra.ofId k A).comp q) (AlgHom.id k A)
    fun _ _ ↦ Commute.all _ _

private noncomputable def evalPair (q r : A →ₐ[k] k) :
    A ⊗[k] A →ₐ[k] k :=
  tensorEvalPair q r

private noncomputable def evalLeftLinear
    {M : Type*} [AddCommGroup M] [Module k M] (q : A →ₐ[k] k) :
    A ⊗[k] M →ₗ[k] M :=
  (TensorProduct.lid k M).toLinearMap.comp
    (LinearMap.rTensor M q.toLinearMap)

private lemma evalLeftLinear_tmul
    {M : Type*} [AddCommGroup M] [Module k M]
    (q : A →ₐ[k] k) (a : A) (m : M) :
    evalLeftLinear q (a ⊗ₜ[k] m) = q a • m := by
  simp [evalLeftLinear]

private lemma repr_evalLeftLinear_eq
    {M ι : Type*} [AddCommGroup M] [Module k M]
    (b : Module.Basis ι k M) (c : ι →₀ A) (z : A ⊗[k] M)
    (hc : c.sum (fun i a ↦ a ⊗ₜ[k] b i) = z)
    (q : A →ₐ[k] k) (i : ι) :
    b.repr (evalLeftLinear q z) i = q (c i) := by
  rw [← hc]
  have hsum :
      (∑ j ∈ c.support, Finsupp.single j (q (c j))) i = q (c i) := by
    rw [congrFun (Finsupp.coe_finsetSum c.support
      (fun j ↦ Finsupp.single j (q (c j)))) i]
    rw [Finset.sum_apply]
    by_cases hi : i ∈ c.support
    · rw [Finset.sum_eq_single i]
      · simp
      · intro j hj hji
        simp [Ne.symm hji]
      · exact fun hi' ↦ (hi' hi).elim
    · have hci : c i = 0 := by
        by_contra hne
        exact hi (Finsupp.mem_support_iff.mpr hne)
      rw [hci, map_zero]
      apply Finset.sum_eq_zero
      intro j hj
      have hji : j ≠ i := by
        intro h
        subst j
        exact hi hj
      simp [hji]
  simp [evalLeftLinear, Finsupp.sum, hsum]

private lemma tensor_eq_zero_of_forall_evalLeftLinear_eq_zero
    {M : Type*} [AddCommGroup M] [Module k M]
    (z : A ⊗[k] M) (hz : ∀ q : A →ₐ[k] k, evalLeftLinear q z = 0) : z = 0 := by
  classical
  letI : Module.Free k M := Module.Free.of_divisionRing k M
  let b := Module.Free.chooseBasis k M
  obtain ⟨c, hc⟩ := TensorProduct.eq_repr_basis_right (x := z) b
  have hci : ∀ i, c i = 0 := by
    intro i
    apply eq_zero_of_forall_character_eq_zero (k := k)
    intro q
    have hq := congrArg (fun x : M ↦ b.repr x i) (hz q)
    rw [repr_evalLeftLinear_eq b c z hc q i, map_zero] at hq
    exact hq
  have hc0 : c = 0 := Finsupp.ext fun i ↦ by simpa using hci i
  rw [hc0] at hc
  simpa using hc.symm

private lemma evalPair_bivariateAeval (q r : A →ₐ[k] k) (t : A)
    (C : BivariatePolynomial k) :
    evalPair q r (bivariateAeval t C) = C.evalEval (q t) (r t) := by
  exact tensorEvalPair_bivariateAeval q r t C

private lemma evalPair_eq (q r : A →ₐ[k] k) (z : A ⊗[k] A) :
    evalPair q r z = r (evalLeft q z) := by
  have h : evalPair q r = r.comp (evalLeft q) := by
    apply Algebra.TensorProduct.ext'
    intro x y
    simp [evalPair, evalLeft, tensorEvalPair, Algebra.TensorProduct.lift_tmul]
  exact DFunLike.congr_fun h z

private lemma evalPair_comm (q r : A →ₐ[k] k) (z : A ⊗[k] A) :
    evalPair q r (TensorProduct.comm k A A z) = evalPair r q z := by
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp [evalPair]
  · intro x y
    simp [evalPair, tensorEvalPair, Algebra.TensorProduct.lift_tmul, mul_comm]
  · intro x y hx hy
    simp [map_add, hx, hy]

private lemma evalPair_comul (q r : A →ₐ[k] k) (a : A) :
    evalPair q r (Coalgebra.comul (R := k) a) =
      (WithConv.toConv q * WithConv.toConv r) a := by
  rw [AlgHom.convMul_apply]
  rfl

private lemma evalLeft_reducedComultiplication
    (q : A →ₐ[k] k) (a : A) :
    evalLeft q (reducedComultiplication (k := k) a) =
      regularCharacterTranslation (WithConv.toConv q) a -
        algebraMap k A (q a) - a := by
  unfold reducedComultiplication
  simp only [map_sub]
  have hcomul : evalLeft q (Coalgebra.comul (R := k) a) =
      regularCharacterTranslation (WithConv.toConv q) a := by
    change evalLeft q (Coalgebra.comul (R := k) a) =
      (WithConv.toConv ((Algebra.ofId k A).comp q) *
        WithConv.toConv (AlgHom.id k A)).ofConv a
    rw [AlgHom.convMul_apply]
    rfl
  rw [hcomul]
  simp [evalLeft]

private lemma repr_evalLeft_eq
    {ι : Type*} (b : Module.Basis ι k A) (c : ι →₀ A) (z : A ⊗[k] A)
    (hc : c.sum (fun i m ↦ m ⊗ₜ[k] b i) = z)
    (q : A →ₐ[k] k) (i : ι) :
    b.repr (evalLeft q z) i = q (c i) := by
  rw [← hc]
  have hsum :
      (∑ j ∈ c.support, Finsupp.single j (q (c j))) i = q (c i) := by
    rw [congrFun (Finsupp.coe_finsetSum c.support
      (fun j ↦ Finsupp.single j (q (c j)))) i]
    rw [Finset.sum_apply]
    by_cases hi : i ∈ c.support
    · rw [Finset.sum_eq_single i]
      · simp
      · intro j hj hji
        simp [Ne.symm hji]
      · exact fun hi' ↦ (hi' hi).elim
    · have hci : c i = 0 := by
        by_contra hne
        exact hi (Finsupp.mem_support_iff.mpr hne)
      rw [hci, map_zero]
      apply Finset.sum_eq_zero
      intro j hj
      have hji : j ≠ i := by
        intro h
        subst j
        exact hi hj
      simp [hji]
  simp [evalLeft, Finsupp.sum, ← Algebra.smul_def, hsum]

private lemma tensor_eq_zero_of_forall_evalLeft_eq_zero
    (z : A ⊗[k] A) (hz : ∀ q : A →ₐ[k] k, evalLeft q z = 0) : z = 0 := by
  classical
  let b := Module.Free.chooseBasis k A
  obtain ⟨c, hc⟩ := TensorProduct.eq_repr_basis_right (x := z) b
  have hci : ∀ i, c i = 0 := by
    intro i
    apply eq_zero_of_forall_character_eq_zero (k := k)
    intro q
    have hq := congrArg (fun x : A ↦ b.repr x i) (hz q)
    rw [repr_evalLeft_eq b c z hc q i, map_zero] at hq
    exact hq
  have hc0 : c = 0 := Finsupp.ext fun i ↦ by simpa using hci i
  rw [hc0] at hc
  simpa using hc.symm

private lemma tensor_eq_zero_of_forall_evalPair_eq_zero
    (z : A ⊗[k] A) (hz : ∀ q r : A →ₐ[k] k, evalPair q r z = 0) : z = 0 := by
  apply tensor_eq_zero_of_forall_evalLeft_eq_zero (k := k) z
  intro q
  apply eq_zero_of_forall_character_eq_zero (k := k)
  intro r
  rw [← evalPair_eq]
  exact hz q r

private lemma exists_evalLeft_ne_zero_both
    (z w : A ⊗[k] A) (hz : z ≠ 0) (hw : w ≠ 0) :
    ∃ q : A →ₐ[k] k, evalLeft q z ≠ 0 ∧ evalLeft q w ≠ 0 := by
  classical
  let b := Module.Free.chooseBasis k A
  obtain ⟨c, hc⟩ := TensorProduct.eq_repr_basis_right (x := z) b
  obtain ⟨d, hd⟩ := TensorProduct.eq_repr_basis_right (x := w) b
  have hcne : c ≠ 0 := by
    intro hc0
    apply hz
    rw [← hc, hc0]
    simp
  have hdne : d ≠ 0 := by
    intro hd0
    apply hw
    rw [← hd, hd0]
    simp
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hcne
  obtain ⟨j, hj⟩ := Finsupp.ne_iff.mp hdne
  simp only [Finsupp.zero_apply] at hi hj
  obtain ⟨q, hq⟩ := exists_character_ne_zero (k := k) (c i * d j) (mul_ne_zero hi hj)
  have hqi : q (c i) ≠ 0 := by
    intro h
    apply hq
    rw [map_mul, h, zero_mul]
  have hqj : q (d j) ≠ 0 := by
    intro h
    apply hq
    rw [map_mul, h, mul_zero]
  refine ⟨q, ?_, ?_⟩
  · intro hzero
    apply hqi
    have hcoord := congrArg (fun x : A ↦ b.repr x i) hzero
    rw [repr_evalLeft_eq b c z hc q i] at hcoord
    simpa using hcoord
  · intro hzero
    apply hqj
    have hcoord := congrArg (fun x : A ↦ b.repr x j) hzero
    rw [repr_evalLeft_eq b d w hd q j] at hcoord
    simpa using hcoord

private lemma tensor_mul_ne_zero
    {z w : A ⊗[k] A} (hz : z ≠ 0) (hw : w ≠ 0) : z * w ≠ 0 := by
  obtain ⟨q, hqz, hqw⟩ := exists_evalLeft_ne_zero_both (k := k) z w hz hw
  obtain ⟨r, hr⟩ := exists_character_ne_zero (k := k)
    (evalLeft q z * evalLeft q w) (mul_ne_zero hqz hqw)
  intro hzw
  apply hr
  rw [map_mul, ← evalPair_eq, ← evalPair_eq, ← map_mul, hzw, map_zero]

private lemma tensorProduct_isDomain : IsDomain (A ⊗[k] A) := by
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] A) :=
    Algebra.TensorProduct.includeLeft_injective (algebraMap k A).injective
  have hone : (1 : A ⊗[k] A) ≠ 0 := by
    intro h
    rw [Algebra.TensorProduct.one_def] at h
    have h' := hinj (show Algebra.TensorProduct.includeLeft (R := k) (1 : A) =
      Algebra.TensorProduct.includeLeft (R := k) (0 : A) by simpa using h)
    exact (one_ne_zero : (1 : A) ≠ 0) h'
  letI : Nontrivial (A ⊗[k] A) := nontrivial_of_ne 1 0 hone
  letI : NoZeroDivisors (A ⊗[k] A) := NoZeroDivisors.mk fun h ↦ by
    by_contra hn
    push Not at hn
    exact tensor_mul_ne_zero (k := k) hn.1 hn.2 h
  exact IsDomain.mk

private lemma bivariateAeval_factor (t : A) (C : BivariatePolynomial k) :
    bivariateAeval t C =
      Algebra.TensorProduct.map (Polynomial.aeval t) (Polynomial.aeval t)
        (bivariateAeval (k := k) (A := Polynomial k) Polynomial.X C) := by
  apply sub_eq_zero.mp
  apply tensor_eq_zero_of_forall_evalPair_eq_zero (k := k)
  intro q r
  simp only [evalPair]
  rw [map_sub, sub_eq_zero, tensorEvalPair_bivariateAeval,
    tensorEvalPair_tensorMap, tensorEvalPair_bivariateAeval]
  simp

private lemma bivariateAeval_injective (t : A) (ht : Transcendental k t) :
    Function.Injective (bivariateAeval (k := k) t) := by
  let f : Polynomial k →ₗ[k] A := (Polynomial.aeval t).toLinearMap
  have hf : Function.Injective f := transcendental_iff_injective.mp ht
  have hr : Function.Injective (LinearMap.rTensor (Polynomial k) f) :=
    Module.Flat.rTensor_preserves_injective_linearMap f hf
  have hl : Function.Injective (LinearMap.lTensor A f) :=
    Module.Flat.lTensor_preserves_injective_linearMap f hf
  have hmap : Function.Injective
      (Algebra.TensorProduct.map (R := k) (S := k)
        (Polynomial.aeval t) (Polynomial.aeval t)) := by
    intro x y hxy
    change TensorProduct.map f f x = TensorProduct.map f f y at hxy
    rw [← LinearMap.lTensor_comp_rTensor] at hxy
    exact hr (hl hxy)
  intro C D hCD
  apply bivariateAeval_universal_injective (k := k)
  apply hmap
  rw [← bivariateAeval_factor t C, ← bivariateAeval_factor t D]
  exact hCD

private lemma evalLeftLinear_lTensor
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module k M] [Module k N]
    (q : A →ₐ[k] k) (g : M →ₗ[k] N) (z : A ⊗[k] M) :
    evalLeftLinear q (LinearMap.lTensor A g z) =
      g (evalLeftLinear q z) := by
  induction z with
  | zero => simp
  | tmul a m => simp [evalLeftLinear_tmul]
  | add x y hx hy => simp [hx, hy]

private lemma evalLeftLinear_self_eq_evalLeft
    (q : A →ₐ[k] k) (z : A ⊗[k] A) :
    evalLeftLinear q z = evalLeft q z := by
  induction z with
  | zero => simp
  | tmul a b => simp [evalLeftLinear_tmul, evalLeft, Algebra.smul_def]
  | add x y hx hy => simp [hx, hy]

private lemma comm_rTensor_eq_lTensor_comm
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module k M] [Module k N]
    (g : A →ₗ[k] M) (z : A ⊗[k] N) :
    TensorProduct.comm k M N (LinearMap.rTensor N g z) =
      LinearMap.lTensor N g (TensorProduct.comm k A N z) := by
  induction z with
  | zero => simp
  | tmul a n => simp
  | add x y hx hy => simp [hx, hy]

private lemma lTensor_rTensor_commute
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module k M] [Module k N]
    (f : A →ₗ[k] M) (g : N →ₗ[k] A) (z : A ⊗[k] N) :
    LinearMap.lTensor M g (LinearMap.rTensor N f z) =
      LinearMap.rTensor A f (LinearMap.lTensor A g z) := by
  induction z with
  | zero => simp
  | tmul a n => simp
  | add x y hx hy => simp [hx, hy]

private lemma tensorMap_rangeRestrict_eq_subtype_maps
    (t : A) (P : Submodule k A)
    (hP : P = LinearMap.range (Polynomial.aeval t).toLinearMap)
    (y : Polynomial k ⊗[k] Polynomial k) :
    let e : Polynomial k →ₗ[k] P := by
      subst P
      exact (Polynomial.aeval t).toLinearMap.rangeRestrict
    TensorProduct.map (Polynomial.aeval t).toLinearMap
        (Polynomial.aeval t).toLinearMap y =
      LinearMap.lTensor A P.subtype
        (LinearMap.rTensor P P.subtype (TensorProduct.map e e y)) := by
  subst P
  dsimp only
  induction y with
  | zero => simp
  | tmul f g => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private lemma exists_bivariate_of_polynomial_slices
    (t : A) (D : A ⊗[k] A)
    (hsymmetric : TensorProduct.comm k A A D = D)
    (hslices : ∀ q : A →ₐ[k] k,
      ∃ g : Polynomial k, evalLeft q D = Polynomial.aeval t g) :
    ∃ C : BivariatePolynomial k, D = bivariateAeval t C := by
  let P : Submodule k A := LinearMap.range (Polynomial.aeval t).toLinearMap
  have hleftQ : LinearMap.lTensor A P.mkQ D = 0 := by
    apply tensor_eq_zero_of_forall_evalLeftLinear_eq_zero (A := A)
    intro q
    rw [evalLeftLinear_lTensor, evalLeftLinear_self_eq_evalLeft]
    obtain ⟨g, hg⟩ := hslices q
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨g, hg.symm⟩
  have hrightQ : LinearMap.rTensor A P.mkQ D = 0 := by
    apply (TensorProduct.comm k (A ⧸ P) A).injective
    rw [comm_rTensor_eq_lTensor_comm, hsymmetric, hleftQ, map_zero]
  have hDRange : D ∈ LinearMap.range (LinearMap.lTensor A P.subtype) := by
    rw [← lTensor_mkQ A P]
    exact hleftQ
  obtain ⟨x, hx⟩ := hDRange
  have hxQ : LinearMap.rTensor P P.mkQ x = 0 := by
    have hinj : Function.Injective (LinearMap.lTensor (A ⧸ P) P.subtype) :=
      Module.Flat.lTensor_preserves_injective_linearMap P.subtype
        Subtype.val_injective
    apply hinj
    rw [map_zero, lTensor_rTensor_commute, hx, hrightQ]
  have hxRange : x ∈ LinearMap.range (LinearMap.rTensor P P.subtype) := by
    rw [← rTensor_mkQ P P]
    exact hxQ
  obtain ⟨z, hz⟩ := hxRange
  let e : Polynomial k →ₗ[k] P :=
    (Polynomial.aeval t).toLinearMap.rangeRestrict
  have he : Function.Surjective e := by
    intro a
    obtain ⟨f, hf⟩ := a.2
    exact ⟨f, Subtype.ext hf⟩
  have hsurj : Function.Surjective (TensorProduct.map e e) :=
    TensorProduct.map_surjective he he
  obtain ⟨y, hy⟩ := hsurj z
  obtain ⟨C, hC⟩ := bivariateAeval_universal_surjective (k := k) y
  refine ⟨C, ?_⟩
  rw [bivariateAeval_factor, hC]
  change D = TensorProduct.map (Polynomial.aeval t).toLinearMap
    (Polynomial.aeval t).toLinearMap y
  rw [tensorMap_rangeRestrict_eq_subtype_maps t P rfl, hy, hz, hx]

private lemma tensor_cocommutative
    (htrdeg : Algebra.trdeg k A = 1) (t : A)
    (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0) (a : A) :
    TensorProduct.comm k A A (Coalgebra.comul (R := k) a) =
      Coalgebra.comul (R := k) a := by
  apply sub_eq_zero.mp
  apply tensor_eq_zero_of_forall_evalPair_eq_zero (k := k)
  intro q r
  rw [map_sub, evalPair_comm, evalPair_comul, evalPair_comul]
  rw [primitive_hopf_curve_character_mul_comm htrdeg t ht hprimitive
    (WithConv.toConv q) (WithConv.toConv r)]
  exact sub_self _

private lemma reducedComultiplication_symmetric
    (htrdeg : Algebra.trdeg k A = 1) (t : A)
    (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0) (a : A) :
    TensorProduct.comm k A A (reducedComultiplication (k := k) a) =
      reducedComultiplication (k := k) a := by
  unfold reducedComultiplication
  rw [map_sub, map_sub, tensor_cocommutative htrdeg t ht hprimitive]
  simp [TensorProduct.comm_tmul]
  abel

private lemma evalPair_reducedComultiplication
    (q r : A →ₐ[k] k) (a : A) :
    evalPair q r (reducedComultiplication (k := k) a) =
      (WithConv.toConv q * WithConv.toConv r) a - q a - r a := by
  unfold reducedComultiplication
  rw [map_sub, map_sub, evalPair_comul]
  simp [evalPair, tensorEvalPair]

private lemma conv_apply_primitive
    (q r : A →ₐ[k] k) (t : A)
    (hprimitive : reducedComultiplication (k := k) t = 0) :
    (WithConv.toConv q * WithConv.toConv r) t = q t + r t := by
  rw [← evalPair_comul, (reducedComultiplication_eq_zero_iff t).mp hprimitive]
  simp [evalPair, tensorEvalPair]

private lemma counit_toConv_eq_one :
    WithConv.toConv (Bialgebra.counitAlgHom k A) =
      (1 : WithConv (A →ₐ[k] k)) := by
  rw [AlgHom.convOne_def]
  rfl

private lemma counit_apply_of_primitive (t : A)
    (hprimitive : reducedComultiplication (k := k) t = 0) :
    Bialgebra.counitAlgHom k A t = 0 := by
  have h := conv_apply_primitive
    (1 : WithConv (A →ₐ[k] k)).ofConv
    (1 : WithConv (A →ₐ[k] k)).ofConv t hprimitive
  simp only [WithConv.toConv_ofConv, one_mul] at h
  have hone : (1 : WithConv (A →ₐ[k] k)) t = 0 := by
    apply add_left_cancel (a := (1 : WithConv (A →ₐ[k] k)) t)
    simpa using h.symm
  rw [← counit_toConv_eq_one] at hone
  exact hone

private lemma bivariatePolynomial_ext [Infinite k]
    {C D : BivariatePolynomial k}
    (h : ∀ x y : k, C.evalEval x y = D.evalEval x y) : C = D := by
  apply Polynomial.ext
  intro n
  apply Polynomial.funext
  intro x
  have hmap : C.map (Polynomial.evalRingHom x) =
      D.map (Polynomial.evalRingHom x) := by
    apply Polynomial.funext
    intro y
    simpa [map_evalRingHom_eval_local] using h x y
  have hc := congrArg (fun P : Polynomial k ↦ P.coeff n) hmap
  simpa using hc

private lemma bivariate_eval_of_reducedComultiplication
    {t s0 : A} {C : BivariatePolynomial k}
    (hC : reducedComultiplication (k := k) s0 = bivariateAeval t C)
    (q r : A →ₐ[k] k) :
    C.evalEval (q t) (r t) =
      (WithConv.toConv q * WithConv.toConv r) s0 - q s0 - r s0 := by
  rw [← evalPair_bivariateAeval, ← hC,
    evalPair_reducedComultiplication]

private lemma counit_eq_zero_of_normalized_bivariate_reducedComultiplication
    {t s0 : A} {C : BivariatePolynomial k}
    (hprimitive : reducedComultiplication (k := k) t = 0)
    (hC : reducedComultiplication (k := k) s0 = bivariateAeval t C)
    (hnormalized : IsNormalizedPolynomialCocycle C) :
    Bialgebra.counitAlgHom k A s0 = 0 := by
  have ht0 := counit_apply_of_primitive t hprimitive
  have hzero :=
    (isNormalizedPolynomialCocycle_iff C).mp hnormalized |>.1 0
  have heval := bivariate_eval_of_reducedComultiplication hC
    (Bialgebra.counitAlgHom k A) (Bialgebra.counitAlgHom k A)
  rw [counit_toConv_eq_one, one_mul] at heval
  rw [ht0] at heval
  simp only [AlgHom.convOne_apply] at heval
  have heval' : C.evalEval 0 0 =
      Bialgebra.counitAlgHom k A s0 -
        Bialgebra.counitAlgHom k A s0 -
          Bialgebra.counitAlgHom k A s0 := by
    simpa using heval
  have hneg : -(Bialgebra.counitAlgHom k A s0) = 0 := by
    calc
      -(Bialgebra.counitAlgHom k A s0) =
          Bialgebra.counitAlgHom k A s0 -
            Bialgebra.counitAlgHom k A s0 -
              Bialgebra.counitAlgHom k A s0 := by ring
      _ = C.evalEval 0 0 := heval'.symm
      _ = 0 := hzero
  exact neg_eq_zero.mp hneg

private lemma bivariate_normalized_of_reducedComultiplication
    (htrdeg : Algebra.trdeg k A = 1) (t : A)
    (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0)
    (s0 : A) (C : BivariatePolynomial k)
    (hcounit : Bialgebra.counitAlgHom k A s0 = 0)
    (hC : reducedComultiplication (k := k) s0 = bivariateAeval t C) :
    IsNormalizedPolynomialCocycle C := by
  have hcounit_t := counit_apply_of_primitive t hprimitive
  rw [isNormalizedPolynomialCocycle_iff]
  constructor
  · intro y
    obtain ⟨r, hr⟩ := exists_character_apply_eq htrdeg t ht hprimitive y
    have h := bivariate_eval_of_reducedComultiplication hC
      (Bialgebra.counitAlgHom k A) r
    rw [counit_toConv_eq_one, one_mul] at h
    simpa [hcounit_t, hcounit, hr] using h
  · intro x
    obtain ⟨q, hq⟩ := exists_character_apply_eq htrdeg t ht hprimitive x
    have h := bivariate_eval_of_reducedComultiplication hC q
      (Bialgebra.counitAlgHom k A)
    rw [counit_toConv_eq_one, mul_one] at h
    simpa [hcounit_t, hcounit, hq] using h

private lemma bivariate_symmetric_of_reducedComultiplication
    (htrdeg : Algebra.trdeg k A = 1) (t : A)
    (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0)
    (s0 : A) (C : BivariatePolynomial k)
    (hC : reducedComultiplication (k := k) s0 = bivariateAeval t C) :
    IsSymmetricPolynomialCocycle C := by
  rw [isSymmetricPolynomialCocycle_iff]
  intro x y
  obtain ⟨q, hq⟩ := exists_character_apply_eq htrdeg t ht hprimitive x
  obtain ⟨r, hr⟩ := exists_character_apply_eq htrdeg t ht hprimitive y
  rw [← hq, ← hr, ← evalPair_bivariateAeval, ← evalPair_bivariateAeval,
    ← hC]
  have hsym := congrArg (evalPair q r)
    (reducedComultiplication_symmetric htrdeg t ht hprimitive s0)
  simpa only [evalPair_comm] using hsym.symm

private lemma bivariate_cocycle_of_reducedComultiplication
    (htrdeg : Algebra.trdeg k A = 1) (t : A)
    (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0)
    (s0 : A) (C : BivariatePolynomial k)
    (hC : reducedComultiplication (k := k) s0 = bivariateAeval t C) :
    IsAdditivePolynomialTwoCocycle C := by
  rw [isAdditivePolynomialTwoCocycle_iff]
  intro x y z
  obtain ⟨q, hq⟩ := exists_character_apply_eq htrdeg t ht hprimitive x
  obtain ⟨r, hr⟩ := exists_character_apply_eq htrdeg t ht hprimitive y
  obtain ⟨w, hw⟩ := exists_character_apply_eq htrdeg t ht hprimitive z
  subst x
  subst y
  subst z
  let qr : A →ₐ[k] k :=
    (WithConv.toConv q * WithConv.toConv r).ofConv
  let rw' : A →ₐ[k] k :=
    (WithConv.toConv r * WithConv.toConv w).ofConv
  have hqrt : qr t = q t + r t := by
    simpa [qr] using conv_apply_primitive q r t hprimitive
  have hrwt : rw' t = r t + w t := by
    simpa [rw'] using conv_apply_primitive r w t hprimitive
  rw [← hqrt, ← hrwt,
    bivariate_eval_of_reducedComultiplication hC q r,
    bivariate_eval_of_reducedComultiplication hC qr w,
    bivariate_eval_of_reducedComultiplication hC r w,
    bivariate_eval_of_reducedComultiplication hC q rw']
  dsimp only [qr, rw']
  simp only [WithConv.toConv_ofConv]
  rw [mul_assoc]
  ring

private lemma bivariate_artinSchreier_of_reducedComultiplication
    [CharP k p] [Fact p.Prime]
    (htrdeg : Algebra.trdeg k A = 1) (t : A)
    (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0)
    (s0 : A) (g : Polynomial k) (C : BivariatePolynomial k)
    (hg : s0 ^ p - s0 = Polynomial.aeval t g)
    (hC : reducedComultiplication (k := k) s0 = bivariateAeval t C) :
    C ^ p - C = additiveCoboundary g := by
  apply bivariatePolynomial_ext
  intro x y
  obtain ⟨q, hq⟩ := exists_character_apply_eq htrdeg t ht hprimitive x
  obtain ⟨r, hr⟩ := exists_character_apply_eq htrdeg t ht hprimitive y
  subst x
  subst y
  let qr : A →ₐ[k] k :=
    (WithConv.toConv q * WithConv.toConv r).ofConv
  have hqrt : qr t = q t + r t := by
    simpa [qr] using conv_apply_primitive q r t hprimitive
  have hqg : (q s0) ^ p - q s0 = g.eval (q t) := by
    calc
      (q s0) ^ p - q s0 = q (s0 ^ p - s0) := by rw [map_sub, map_pow]
      _ = q (Polynomial.aeval t g) := congrArg q hg
      _ = g.eval (q t) := by
        change q (Polynomial.aeval t g) = Polynomial.aeval (q t) g
        exact (Polynomial.aeval_algHom_apply q t g).symm
  have hrg : (r s0) ^ p - r s0 = g.eval (r t) := by
    calc
      (r s0) ^ p - r s0 = r (s0 ^ p - s0) := by rw [map_sub, map_pow]
      _ = r (Polynomial.aeval t g) := congrArg r hg
      _ = g.eval (r t) := by
        change r (Polynomial.aeval t g) = Polynomial.aeval (r t) g
        exact (Polynomial.aeval_algHom_apply r t g).symm
  have hqrg : (qr s0) ^ p - qr s0 = g.eval (q t + r t) := by
    calc
      (qr s0) ^ p - qr s0 = qr (s0 ^ p - s0) := by rw [map_sub, map_pow]
      _ = qr (Polynomial.aeval t g) := congrArg qr hg
      _ = g.eval (qr t) := by
        change qr (Polynomial.aeval t g) = Polynomial.aeval (qr t) g
        exact (Polynomial.aeval_algHom_apply qr t g).symm
      _ = g.eval (q t + r t) := by rw [hqrt]
  rw [Polynomial.evalEval_sub, Polynomial.evalEval_pow,
    bivariate_eval_of_reducedComultiplication hC q r,
    additiveCoboundary_eval, sub_pow_char, sub_pow_char]
  dsimp only [qr] at hqrg ⊢
  linear_combination hqrg - hqg - hrg

private lemma sup_zpowers_eq_top_of_prime_index
    {G : Type*} [Group G] [Finite G] {p : Nat} (hp : p.Prime)
    (H : Subgroup G) (hH : H.index = p) (sigma : G) (hsigma : sigma ∉ H) :
    H ⊔ Subgroup.zpowers sigma = ⊤ := by
  let K := H ⊔ Subgroup.zpowers sigma
  have hHK : H ≤ K := le_sup_left
  have hrel_ne : H.relIndex K ≠ 1 := by
    intro hrel
    have hKH : K ≤ H := Subgroup.relIndex_eq_one.mp hrel
    exact hsigma (hKH (show sigma ∈ K from
      (show Subgroup.zpowers sigma ≤ K from le_sup_right)
        (Subgroup.mem_zpowers sigma)))
  have hmul := Subgroup.relIndex_mul_index hHK
  rw [hH] at hmul
  have hrel_dvd : H.relIndex K ∣ p := ⟨K.index, hmul.symm⟩
  have hrel : H.relIndex K = p :=
    ((Nat.dvd_prime hp).mp hrel_dvd).resolve_left hrel_ne
  apply Subgroup.index_eq_one.mp
  rw [hrel] at hmul
  nlinarith [hp.pos]

private lemma mem_fixedField_top_of_prime_index
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    {p : Nat} [Finite (E ≃ₐ[K] E)] (hp : p.Prime)
    (H : Subgroup (E ≃ₐ[K] E)) (hH : H.index = p)
    (sigma : E ≃ₐ[K] E) (hsigmaH : sigma ∉ H) (x : E)
    (hxH : x ∈ IntermediateField.fixedField H)
    (hxsigma : sigma x = x) :
    x ∈ IntermediateField.fixedField
      (⊤ : Subgroup (E ≃ₐ[K] E)) := by
  let G := E ≃ₐ[K] E
  let S : Subgroup G := MulAction.stabilizer G x
  have hHS : H ≤ S := by
    intro tau htau
    exact (IntermediateField.mem_fixedField_iff (H := H) x).mp hxH tau htau
  have hsigmaS : sigma ∈ S := hxsigma
  have hgen := sup_zpowers_eq_top_of_prime_index hp H hH sigma hsigmaH
  rw [IntermediateField.mem_fixedField_iff]
  intro tau _
  have htop : (⊤ : Subgroup G) ≤ S := by
    rw [← hgen]
    exact sup_le hHS (Subgroup.zpowers_le.mpr hsigmaS)
  exact htop (Subgroup.mem_top tau)

private lemma card_lt_of_prime_index
    {G : Type*} [Group G] [Finite G] {p : Nat} (hp : p.Prime)
    (H : Subgroup G) (hH : H.index = p) : Nat.card H < Nat.card G := by
  rw [← H.card_mul_index, hH]
  have hcard : 0 < Nat.card H := Nat.card_pos
  nlinarith [hp.two_le]

private lemma adjoin_eq_fixedField_of_prime_index
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E]
    {p : Nat} (hp : p.Prime)
    (H : Subgroup (E ≃ₐ[K] E)) (hH : H.index = p)
    (sigma : E ≃ₐ[K] E) (s : E)
    (hs : s ∈ IntermediateField.fixedField H)
    (hsigma : sigma s = s + 1) :
    IntermediateField.adjoin K ({s} : Set E) =
      IntermediateField.fixedField H := by
  let L := IntermediateField.adjoin K ({s} : Set E)
  let M := IntermediateField.fixedField H
  have hLM : L ≤ M := by
    rw [IntermediateField.adjoin_le_iff]
    exact Set.singleton_subset_iff.mpr hs
  have hsnot : s ∉ (⊥ : IntermediateField K E) := by
    intro hsbot
    obtain ⟨x, hx⟩ := hsbot
    have hfix : sigma s = s := by
      rw [← hx]
      exact sigma.commutes x
    have hone : (1 : E) = 0 := by
      apply add_left_cancel (a := s)
      simpa using hsigma.symm.trans hfix
    exact one_ne_zero hone
  have hLne : Module.finrank K L ≠ 1 := by
    intro hfin
    exact hsnot ((IntermediateField.finrank_adjoin_simple_eq_one_iff).mp hfin)
  have hMtop : Module.finrank M E = Nat.card H :=
    by simpa [M] using
      (IntermediateField.finrank_fixedField_eq_card (H := H))
  have hKtop : Module.finrank K E = Nat.card (E ≃ₐ[K] E) := by
    rw [IsGalois.card_aut_eq_finrank]
  have hcard : Nat.card H * p = Nat.card (E ≃ₐ[K] E) := by
    rw [← H.card_mul_index, hH]
  have hKM : Module.finrank K M = p := by
    have htower := Module.finrank_mul_finrank K M E
    rw [hMtop, hKtop, ← hcard] at htower
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos : 0 < Nat.card H) (by
      simpa [mul_comm] using htower)
  have hLd : Module.finrank K L ∣ p := by
    rw [← hKM]
    exact IntermediateField.finrank_dvd_of_le_right hLM
  have hL : Module.finrank K L = p :=
    ((Nat.dvd_prime hp).mp hLd).resolve_left hLne
  exact IntermediateField.eq_of_le_of_finrank_eq hLM (hL.trans hKM.symm)

private lemma artinSchreierDifference_mem_fixedField_top
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    {p : Nat} [CharP E p] [Fact p.Prime]
    [Finite (E ≃ₐ[K] E)] (hp : p.Prime)
    (H : Subgroup (E ≃ₐ[K] E)) (hH : H.index = p)
    (sigma : E ≃ₐ[K] E) (hsigmaH : sigma ∉ H) (s : E)
    (hs : s ∈ IntermediateField.fixedField H)
    (hsigma : sigma s = s + 1) :
    s ^ p - s ∈ IntermediateField.fixedField
      (⊤ : Subgroup (E ≃ₐ[K] E)) := by
  let G := E ≃ₐ[K] E
  let z : E := s ^ p - s
  let S : Subgroup G := MulAction.stabilizer G z
  have hHfix : H ≤ S := by
    intro tau htau
    change tau z = z
    dsimp only [z]
    rw [map_sub, map_pow, show tau s = s from
      (IntermediateField.mem_fixedField_iff (H := H) s).mp hs tau htau]
  have hsigfix : sigma ∈ S := by
    change sigma z = z
    dsimp only [z]
    rw [map_sub, map_pow, hsigma, add_pow_char]
    simp
  have hgen := sup_zpowers_eq_top_of_prime_index hp H hH sigma hsigmaH
  rw [IntermediateField.mem_fixedField_iff]
  intro tau _
  change tau z = z
  have htop : (⊤ : Subgroup G) ≤ S := by
    rw [← hgen]
    exact sup_le hHfix (Subgroup.zpowers_le.mpr hsigfix)
  exact htop (Subgroup.mem_top tau)

private lemma exists_polynomial_of_fraction_mem_ratFunc
    [IsIntegrallyClosed A]
    (htrdeg : Algebra.trdeg k A = 1) (t : A)
    (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0)
    (a : A) (x : RatFunc k)
    (hx : primitiveFractionMap (k := k) t ht x =
      algebraMap A (FractionRing A) a) :
    ∃ g : Polynomial k, a = Polynomial.aeval t g := by
  let P := Polynomial k
  let K := RatFunc k
  let L := FractionRing A
  let f := primitiveFractionMap (k := k) t ht
  letI : Algebra P A := (Polynomial.aeval t).toRingHom.toAlgebra
  letI : Module.Finite P A :=
    primitive_hopf_curve_aeval_finite htrdeg t ht hprimitive
  letI : Algebra P L :=
    (f.toRingHom.comp (algebraMap P K)).toAlgebra
  have hcomp (q : P) :
      f (algebraMap P K q) =
        algebraMap A L (algebraMap P A q) := by
    change primitiveFractionMap (k := k) t ht
        (algebraMap (Polynomial k) (RatFunc k) q) =
      algebraMap A (FractionRing A) (Polynomial.aeval t q)
    rw [show algebraMap (Polynomial k) (RatFunc k) q =
        algebraMap (Polynomial k) (RatFunc k) q /
          algebraMap (Polynomial k) (RatFunc k) 1 by simp,
      primitiveFractionMap_apply_div]
    simp
  let fP : K →ₐ[P] L :=
    { f with commutes' := fun q ↦ rfl }
  let iA : A →ₐ[P] L :=
    { IsScalarTower.toAlgHom k A L with
      commutes' := fun q ↦ (hcomp q).symm }
  have ha : IsIntegral P a :=
    Algebra.IsIntegral.isIntegral a
  have hfx : IsIntegral P (fP x) := by
    rw [show fP x = iA a by exact hx]
    exact (isIntegral_algHom_iff iA (IsFractionRing.injective A L)).mpr ha
  have hxint : IsIntegral P x :=
    (isIntegral_algHom_iff fP f.injective).mp hfx
  obtain ⟨g, hg⟩ := IsIntegrallyClosed.isIntegral_iff.mp hxint
  refine ⟨g, (IsFractionRing.injective A L) ?_⟩
  change algebraMap A L a = algebraMap A L (Polynomial.aeval t g)
  rw [← hx]
  change f x = iA (Polynomial.aeval t g)
  rw [← hg]
  exact hcomp g

private lemma exists_polynomial_evalLeft_reducedComultiplication
    [CharP k p] [Fact p.Prime] [IsIntegrallyClosed A]
    (htrdeg : Algebra.trdeg k A = 1) (t : A)
    (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0) :
    let f := primitiveFractionMap (k := k) t ht
    letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
    letI : IsScalarTower k (RatFunc k) (FractionRing A) :=
      IsScalarTower.of_algebraMap_eq fun x ↦ (f.commutes x).symm
    let F := separableClosure (RatFunc k) (FractionRing A)
    ∀ H : Subgroup (F ≃ₐ[RatFunc k] F), H.index = p →
    ∀ sigma : F ≃ₐ[RatFunc k] F, sigma ∉ H →
    ∀ s0 : A, ∀ hsF : algebraMap A (FractionRing A) s0 ∈ F,
    let sF : F := ⟨algebraMap A (FractionRing A) s0, hsF⟩
    ∀ _hsE : sF ∈ IntermediateField.fixedField H,
      sigma sF = sF + 1 →
    ∀ q : A →ₐ[k] k,
      ∃ g : Polynomial k,
        evalLeft q (reducedComultiplication (k := k) s0) =
          Polynomial.aeval t g := by
  let K := RatFunc k
  let L := FractionRing A
  let f := primitiveFractionMap (k := k) t ht
  letI : Algebra K L := f.toRingHom.toAlgebra
  letI : IsScalarTower k K L :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (f.commutes x).symm
  let F := separableClosure K L
  letI : Module.Finite K L :=
    primitive_hopf_curve_fraction_map_finite htrdeg t ht hprimitive
  letI : Module.Finite K F :=
    primitive_hopf_curve_separableClosure_finite htrdeg t ht hprimitive
  letI : IsGalois K F :=
    (primitive_hopf_curve_separable_kernel_is_galois_pGroup
      (p := p) htrdeg t ht hprimitive).1
  letI : CharP F p :=
    charP_of_injective_algebraMap (algebraMap k F).injective p
  dsimp only
  intro H hH sigma hsigmaH s0 hsF
  let sF : F := ⟨algebraMap A L s0, hsF⟩
  intro hsE hsigma q
  have hsigma' : sigma sF = sF + 1 := by
    simpa only [sF] using hsigma
  let tau := regularCharacterSeparableTranslation t ht hprimitive
    (WithConv.toConv q)
  let z : F := tau sF - sF
  have hzH : z ∈ IntermediateField.fixedField H := by
    exact sub_mem
      ((regularCharacterSeparableTranslation_mem_fixedField_iff
        htrdeg t ht hprimitive (WithConv.toConv q) H sF).2 hsE) hsE
  have hzSigma : sigma z = z := by
    dsimp only [z]
    rw [map_sub, ← regularCharacterSeparableTranslation_commute
      htrdeg t ht hprimitive (WithConv.toConv q) sigma sF, hsigma']
    simp [tau]
  have hzTop : z ∈ IntermediateField.fixedField
      (⊤ : Subgroup (F ≃ₐ[K] F)) :=
    mem_fixedField_top_of_prime_index (Fact.out : p.Prime)
      H hH sigma hsigmaH z hzH hzSigma
  have hzBot : z ∈ (⊥ : IntermediateField K F) := by
    rw [← primitive_hopf_curve_separable_kernel_fixedField_eq_bot
      (p := p) htrdeg t ht hprimitive]
    exact hzTop
  obtain ⟨x, hx⟩ := hzBot
  let a0 := regularCharacterTranslation (WithConv.toConv q) s0 - s0
  have hxa0 : f x = algebraMap A L a0 := by
    have hxval := congrArg Subtype.val hx
    change f x =
      (((regularCharacterSeparableTranslation t ht hprimitive
        (WithConv.toConv q)) sF : F) : L) - sF.1 at hxval
    rw [regularCharacterSeparableTranslation_apply,
      regularCharacterFractionTranslation_algebraMap] at hxval
    simpa only [sF, a0, map_sub] using hxval
  obtain ⟨g, hg⟩ := exists_polynomial_of_fraction_mem_ratFunc
    htrdeg t ht hprimitive a0 x hxa0
  refine ⟨g - Polynomial.C (q s0), ?_⟩
  rw [map_sub, Polynomial.aeval_C, ← hg,
    evalLeft_reducedComultiplication]
  dsimp only [a0]
  abel

/-- Polynomial Artin--Schreier and actual reduced-coproduct descent for a
counit-zero generator of a normal index-`p` fixed-field layer. -/
public theorem primitive_hopf_curve_artin_schreier_cocycle_descent
    [CharP k p] [Fact p.Prime] [IsIntegrallyClosed A]
    (htrdeg : Algebra.trdeg k A = 1) (t : A)
    (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0) :
    let f := primitiveFractionMap (k := k) t ht
    letI : Algebra (RatFunc k) (FractionRing A) := f.toRingHom.toAlgebra
    letI : IsScalarTower k (RatFunc k) (FractionRing A) :=
      IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
    let F := separableClosure (RatFunc k) (FractionRing A)
    forall H : Subgroup (F ≃ₐ[RatFunc k] F), H.index = p ->
    forall sigma : F ≃ₐ[RatFunc k] F,
    forall q : primitiveCharacterKernel t hprimitive,
    forall s0 : A,
    Bialgebra.counitAlgHom k A s0 = 0 ->
    forall hsF : algebraMap A (FractionRing A) s0 ∈ F,
      primitiveSeparableKernelAction t ht hprimitive
          (MulOpposite.op q) = sigma ->
      sigma ∉ H ->
      let sF : F := ⟨algebraMap A (FractionRing A) s0, hsF⟩
      forall _hsE : sF ∈ IntermediateField.fixedField H,
      sigma sF = sF + 1 ->
      exists g : Polynomial k, exists C : BivariatePolynomial k,
        s0 ^ p - s0 = Polynomial.aeval t g /\
        reducedComultiplication (k := k) s0 = bivariateAeval t C /\
        IsNormalizedPolynomialCocycle C /\
        IsSymmetricPolynomialCocycle C /\
        IsAdditivePolynomialTwoCocycle C /\
        C ^ p - C = additiveCoboundary g /\
        IntermediateField.adjoin (RatFunc k) ({sF} : Set F) =
          IntermediateField.fixedField H /\
        Nat.card H < Nat.card (F ≃ₐ[RatFunc k] F) := by
  let K := RatFunc k
  let L := FractionRing A
  let f := primitiveFractionMap (k := k) t ht
  letI : Algebra K L := f.toRingHom.toAlgebra
  letI : IsScalarTower k K L :=
    IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  let F := separableClosure K L
  letI : Module.Finite K L :=
    primitive_hopf_curve_fraction_map_finite htrdeg t ht hprimitive
  letI : Module.Finite K F :=
    primitive_hopf_curve_separableClosure_finite htrdeg t ht hprimitive
  letI : IsGalois K F :=
    (primitive_hopf_curve_separable_kernel_is_galois_pGroup
      (p := p) htrdeg t ht hprimitive).1
  letI : CharP F p :=
    charP_of_injective_algebraMap (algebraMap k F).injective p
  dsimp only
  intro H hH sigma q s0 hcounit hsF _hqaction hsigmaH
  let sF : F := ⟨algebraMap A L s0, hsF⟩
  intro hsE hsigma
  have hsigma' : sigma sF = sF + 1 := by
    simpa only [sF] using hsigma
  have htop : sF ^ p - sF ∈ IntermediateField.fixedField
      (⊤ : Subgroup (F ≃ₐ[K] F)) :=
    artinSchreierDifference_mem_fixedField_top
      (Fact.out : p.Prime) H hH sigma hsigmaH sF hsE hsigma'
  have hbot : sF ^ p - sF ∈ (⊥ : IntermediateField K F) := by
    rw [← primitive_hopf_curve_separable_kernel_fixedField_eq_bot
      (p := p) htrdeg t ht hprimitive]
    exact htop
  obtain ⟨x, hx⟩ := hbot
  have hxf : f x = algebraMap A L (s0 ^ p - s0) := by
    have hxval := congrArg Subtype.val hx
    change f x = sF.1 ^ p - sF.1 at hxval
    simpa only [sF, map_sub, map_pow] using hxval
  obtain ⟨g, hg⟩ := exists_polynomial_of_fraction_mem_ratFunc
    htrdeg t ht hprimitive (s0 ^ p - s0) x hxf
  have hslices : ∀ r : A →ₐ[k] k,
      ∃ h : Polynomial k,
        evalLeft r (reducedComultiplication (k := k) s0) =
          Polynomial.aeval t h :=
    exists_polynomial_evalLeft_reducedComultiplication
      htrdeg t ht hprimitive H hH sigma hsigmaH s0 hsF hsE hsigma'
  obtain ⟨C, hC⟩ := exists_bivariate_of_polynomial_slices t
    (reducedComultiplication (k := k) s0)
    (reducedComultiplication_symmetric htrdeg t ht hprimitive s0) hslices
  refine ⟨g, C, hg, hC,
    bivariate_normalized_of_reducedComultiplication
      htrdeg t ht hprimitive s0 C hcounit hC,
    bivariate_symmetric_of_reducedComultiplication
      htrdeg t ht hprimitive s0 C hC,
    bivariate_cocycle_of_reducedComultiplication
      htrdeg t ht hprimitive s0 C hC,
    bivariate_artinSchreier_of_reducedComultiplication
      htrdeg t ht hprimitive s0 g C hg hC, ?_, ?_⟩
  · exact adjoin_eq_fixedField_of_prime_index
      (Fact.out : p.Prime) H hH sigma sF hsE hsigma'
  · exact card_lt_of_prime_index (Fact.out : p.Prime) H hH

end

end Theory.AlgebraicGroup
