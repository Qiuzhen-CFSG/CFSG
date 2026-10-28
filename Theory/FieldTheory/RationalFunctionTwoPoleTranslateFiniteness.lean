module

public import Theory.FieldTheory.RationalFunctionProjectivePoles
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Finiteness of affine translates for rational functions with two poles

Let `t : k(X)` have exactly two projective poles.  This module proves that a
constant identity `sigma t = t + c`, with `sigma` a `k`-automorphism of the
rational function field, can only occur for `c = 0`.  In particular, the set
of such translation parameters is finite.  This is the two-boundary-point
branch of Borel, *Linear Algebraic Groups*, Theorem 10.9, as transcribed in
`refs/KGroup/Bor1/Chapter3.tex`.

The two poles are first moved to `0` and infinity by an explicit Mobius
automorphism.  Pole covariance then forces the matrix of every witnessing
automorphism either to preserve or to exchange those two points.  The reduced
denominator of the normalized function is a power of `X`, so the function is
a Laurent polynomial `p / X^n`.  In the preserving case the variable is sent
to `r X`; in the exchanging case it is sent to `r / X`.  Embedding Laurent
polynomials into `k(X)` and comparing the coefficient of degree zero in the
translation identity gives `p_n = p_n + c` in both cases.  The factors `r^n`
cancel because the Mobius matrix is invertible.  This coefficient argument is
valid in every characteristic and uses no affine-line or algebraic-group
classification.
-/

universe u

open IntermediateField Polynomial
open scoped LaurentPolynomial OnePoint Pointwise

namespace RatFunc

variable {k : Type u} [Field k]

noncomputable section

local instance : DecidableEq k := Classical.decEq k

private def zeroInfinity : Set (OnePoint k) :=
  {OnePoint.infty, ((0 : k) : OnePoint k)}

private def Xunit : (RatFunc k)ˣ := Units.mk0 X X_ne_zero

private def laurentEval : LaurentPolynomial k →+* RatFunc k :=
  LaurentPolynomial.eval₂ C Xunit

private lemma laurentEval_injective : Function.Injective (laurentEval (k := k)) := by
  rw [IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (Polynomial.X : k[X]))]
  intro p q
  simp only [LaurentPolynomial.algebraMap_eq_toLaurent]
  change Polynomial.toLaurent p = Polynomial.toLaurent q ↔
    LaurentPolynomial.eval₂ C Xunit (Polynomial.toLaurent p) =
      LaurentPolynomial.eval₂ C Xunit (Polynomial.toLaurent q)
  rw [LaurentPolynomial.eval₂_toLaurent, LaurentPolynomial.eval₂_toLaurent]
  have heval (s : k[X]) : Polynomial.eval₂ C (Xunit (k := k) : RatFunc k) s =
      algebraMap k[X] (RatFunc k) s := by
    simpa [Xunit] using Polynomial.eval₂_algebraMap_X s
      (IsScalarTower.toAlgHom k k[X] (RatFunc k))
  rw [heval, heval]
  constructor
  · intro h
    exact congrArg (algebraMap k[X] (RatFunc k))
      (Polynomial.toLaurent_injective h)
  · intro h
    exact congrArg Polynomial.toLaurent
      ((FaithfulSMul.algebraMap_injective k[X] (RatFunc k)) h)

private lemma laurentEval_toLaurent (p : k[X]) :
    laurentEval p.toLaurent = algebraMap k[X] (RatFunc k) p := by
  rw [laurentEval]
  simp only [LaurentPolynomial.eval₂_toLaurent]
  simpa [Xunit] using Polynomial.eval₂_algebraMap_X p
    (IsScalarTower.toAlgHom k k[X] (RatFunc k))

private lemma laurentEval_invert_toLaurent (p : k[X]) :
    laurentEval (LaurentPolynomial.invert p.toLaurent) =
      aeval ((X : RatFunc k)⁻¹) p := by
  rw [p.as_sum_range_C_mul_X_pow]
  simp only [map_sum, map_mul, Polynomial.toLaurent_C,
    Polynomial.toLaurent_X, map_pow, LaurentPolynomial.invert_C,
    LaurentPolynomial.invert_T, Int.reduceNeg, map_sum, map_mul, map_pow,
    aeval_C, aeval_X]
  simp [laurentEval, Xunit, LaurentPolynomial.eval₂_T]

private lemma laurentEval_T_nat (n : ℕ) :
    laurentEval (LaurentPolynomial.T (n : ℤ)) = (X : RatFunc k)^n := by
  simp [laurentEval, Xunit, LaurentPolynomial.eval₂_T]

private lemma laurentEval_T_neg_nat (n : ℕ) :
    laurentEval (LaurentPolynomial.T (-(n : ℤ))) = ((X : RatFunc k)^n)⁻¹ := by
  simp [laurentEval, Xunit, LaurentPolynomial.eval₂_T, zpow_neg]

private lemma coeff_mul_T (f : LaurentPolynomial k) (n m : ℤ) :
    (f * LaurentPolynomial.T n).coeff m = f.coeff (m - n) := by
  change (f * AddMonoidAlgebra.single n 1).coeff m = _
  rw [AddMonoidAlgebra.coeff_mul_single_apply]
  simp [sub_eq_add_neg]

private lemma coeff_C_mul (f : LaurentPolynomial k) (a : k) (m : ℤ) :
    (LaurentPolynomial.C a * f).coeff m = a * f.coeff m := by
  change (AddMonoidAlgebra.single 0 a * f).coeff m = _
  rw [AddMonoidAlgebra.coeff_single_mul_apply]
  simp

private lemma coeff_toLaurent_nat (p : k[X]) (n : ℕ) :
    p.toLaurent.coeff (n : ℤ) = p.coeff n := by
  rw [LaurentPolynomial.coeff_toLaurent]
  change (Finsupp.mapDomain (⇑Nat.castEmbedding) p.toFinsupp.coeff)
      (Nat.castEmbedding n) = p.coeff n
  rw [Finsupp.mapDomain_apply Nat.castEmbedding.injective]
  rfl

private lemma coeff_comp_C_mul_X (p : k[X]) (r : k) (i : ℕ) :
    (p.comp (Polynomial.C r * Polynomial.X)).coeff i = p.coeff i * r^i := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow]
  simp only [sum_comp, mul_comp, C_comp, pow_comp, X_comp]
  rw [finsetSum_coeff]
  have hcoeff (a : k) (x : ℕ) :
      (Polynomial.C a * (Polynomial.C r * Polynomial.X)^x).coeff i =
        if i = x then a * r^x else 0 := by
    rw [mul_pow, ← Polynomial.C_pow (a := r) (n := x), ← mul_assoc]
    simp only [← Polynomial.C_mul]
    rw [Polynomial.C_mul_X_pow_eq_monomial]
    by_cases hix : i = x
    · subst i
      simp
    · simp [Polynomial.coeff_monomial, hix, Ne.symm hix]
  simp_rw [hcoeff]
  by_cases hi : i ≤ p.natDegree
  · have himem : i ∈ Finset.range (p.natDegree + 1) := by simp; omega
    rw [Finset.sum_eq_single i]
    · simp
    · intro b hb hbi
      simp [Ne.symm hbi]
    · intro hnot
      exact (hnot himem).elim
  · have hilt : p.natDegree < i := Nat.lt_of_not_ge hi
    rw [coeff_eq_zero_of_natDegree_lt hilt]
    simp only [zero_mul]
    apply Finset.sum_eq_zero
    intro b hb
    have hbi : i ≠ b := by
      intro h
      have : i ≤ p.natDegree := by simpa [h] using (Finset.mem_range.mp hb)
      exact hi this
    simp [hbi]

private lemma scale_translation_constant_eq_zero (p : k[X]) (n : ℕ) (r c : k)
    (hr : r ≠ 0)
    (h : aeval (C r * X) p / (C r * X)^n =
      algebraMap k[X] (RatFunc k) p /
          algebraMap k[X] (RatFunc k) (Polynomial.X^n) + C c) : c = 0 := by
  let q := p.comp (Polynomial.C r * Polynomial.X)
  let lhs : LaurentPolynomial k :=
    LaurentPolynomial.C ((r^n)⁻¹) * q.toLaurent *
      LaurentPolynomial.T (-(n : ℤ))
  let rhs : LaurentPolynomial k :=
    p.toLaurent * LaurentPolynomial.T (-(n : ℤ)) + LaurentPolynomial.C c
  have hrR : C r ≠ (0 : RatFunc k) := by
    simpa using (C : k →+* RatFunc k).injective.ne hr
  have hqeval : aeval (X : RatFunc k) q = aeval (C r * X) p := by
    dsimp [q]
    rw [aeval_comp]
    congr 1
    simp
  have hlhs : laurentEval lhs = aeval (C r * X) p / (C r * X)^n := by
    dsimp [lhs]
    rw [map_mul, map_mul, laurentEval_toLaurent, ← aeval_X_left_eq_algebraMap,
      hqeval, laurentEval_T_neg_nat]
    have hC : laurentEval (LaurentPolynomial.C ((r^n)⁻¹)) = C ((r^n)⁻¹) := by
      simp [laurentEval]
    rw [hC]
    simp only [map_inv₀, map_pow]
    rw [mul_pow]
    field_simp [hrR, X_ne_zero]
  have hrhs : laurentEval rhs =
      algebraMap k[X] (RatFunc k) p /
          algebraMap k[X] (RatFunc k) (Polynomial.X^n) + C c := by
    dsimp [rhs]
    rw [map_add, map_mul, laurentEval_toLaurent, laurentEval_T_neg_nat]
    simp only [map_pow, algebraMap_X]
    simp [div_eq_mul_inv, laurentEval]
  have hlr : lhs = rhs := laurentEval_injective (hlhs.trans (h.trans hrhs.symm))
  have hcoeff := congrArg (fun f : LaurentPolynomial k => f.coeff 0) hlr
  dsimp [lhs, rhs] at hcoeff
  rw [coeff_mul_T, coeff_C_mul, coeff_mul_T] at hcoeff
  simp only [zero_sub, neg_neg] at hcoeff
  have hcoeff' : (r^n)⁻¹ * q.coeff n = p.coeff n + c := by
    simpa only [coeff_toLaurent_nat, LaurentPolynomial.C_apply, if_pos] using hcoeff
  rw [coeff_comp_C_mul_X] at hcoeff'
  have hcancel : (r^n)⁻¹ * (p.coeff n * r^n) = p.coeff n := by
    field_simp
  rw [hcancel] at hcoeff'
  apply add_left_cancel (a := p.coeff n)
  exact hcoeff'.symm.trans (add_zero (p.coeff n)).symm

private lemma inversion_translation_constant_eq_zero (p : k[X]) (n : ℕ) (r c : k)
    (hr : r ≠ 0)
    (h : aeval (C r / X) p / (C r / X)^n =
      algebraMap k[X] (RatFunc k) p /
          algebraMap k[X] (RatFunc k) (Polynomial.X^n) + C c) : c = 0 := by
  let q := p.comp (Polynomial.C r * Polynomial.X)
  let lhs : LaurentPolynomial k :=
    LaurentPolynomial.C ((r^n)⁻¹) * LaurentPolynomial.invert q.toLaurent *
      LaurentPolynomial.T n
  let rhs : LaurentPolynomial k :=
    p.toLaurent * LaurentPolynomial.T (-(n : ℤ)) + LaurentPolynomial.C c
  have hrR : C r ≠ (0 : RatFunc k) := by
    simpa using (C : k →+* RatFunc k).injective.ne hr
  have hqeval : aeval ((X : RatFunc k)⁻¹) q = aeval (C r / X) p := by
    dsimp [q]
    rw [aeval_comp]
    congr 1
    simp [div_eq_mul_inv]
  have hlhs : laurentEval lhs = aeval (C r / X) p / (C r / X)^n := by
    dsimp [lhs]
    rw [map_mul, map_mul, laurentEval_invert_toLaurent, hqeval, laurentEval_T_nat]
    have hC : laurentEval (LaurentPolynomial.C ((r^n)⁻¹)) = C ((r^n)⁻¹) := by
      simp [laurentEval]
    rw [hC]
    simp only [map_inv₀, map_pow]
    rw [div_pow]
    field_simp [hrR, X_ne_zero]
  have hrhs : laurentEval rhs =
      algebraMap k[X] (RatFunc k) p /
          algebraMap k[X] (RatFunc k) (Polynomial.X^n) + C c := by
    dsimp [rhs]
    rw [map_add, map_mul, laurentEval_toLaurent, laurentEval_T_neg_nat]
    simp only [map_pow, algebraMap_X]
    simp [div_eq_mul_inv, laurentEval]
  have hlr : lhs = rhs := laurentEval_injective (hlhs.trans (h.trans hrhs.symm))
  have hcoeff := congrArg (fun f : LaurentPolynomial k => f.coeff 0) hlr
  dsimp [lhs, rhs] at hcoeff
  rw [coeff_mul_T, coeff_C_mul, LaurentPolynomial.invert_apply, coeff_mul_T] at hcoeff
  simp only [zero_sub, neg_neg] at hcoeff
  have hcoeff' : (r^n)⁻¹ * q.coeff n = p.coeff n + c := by
    simpa only [coeff_toLaurent_nat, LaurentPolynomial.C_apply, if_pos] using hcoeff
  rw [coeff_comp_C_mul_X] at hcoeff'
  have hcancel : (r^n)⁻¹ * (p.coeff n * r^n) = p.coeff n := by
    field_simp
  rw [hcancel] at hcoeff'
  apply add_left_cancel (a := p.coeff n)
  exact hcoeff'.symm.trans (add_zero (p.coeff n)).symm

private noncomputable def algEquivOfGenerator (v : RatFunc k)
    (hv : Transcendental k v) (hgen : IntermediateField.adjoin k {v} = ⊤) :
    RatFunc k ≃ₐ[k] RatFunc k :=
  ((RatFunc.algEquivOfTranscendental v hv).trans
      (IntermediateField.equivOfEq hgen)).trans
    (IntermediateField.topEquiv : (⊤ : IntermediateField k (RatFunc k)) ≃ₐ[k] RatFunc k)

private lemma algEquivOfGenerator_X (v : RatFunc k)
    (hv : Transcendental k v) (hgen : IntermediateField.adjoin k {v} = ⊤) :
    algEquivOfGenerator v hv hgen (X : RatFunc k) = v := by
  simp [algEquivOfGenerator]

private lemma transcendental_of_adjoin_eq_top (v : RatFunc k)
    (hgen : IntermediateField.adjoin k {v} = ⊤) : Transcendental k v := by
  apply v.transcendental_of_ne_C
  rintro ⟨c, rfl⟩
  have hbot : IntermediateField.adjoin k {(C c : RatFunc k)} = ⊥ :=
    IntermediateField.adjoin_simple_eq_bot_iff.mpr ⟨c, rfl⟩
  have htopbot : (⊤ : IntermediateField k (RatFunc k)) = ⊥ := hgen.symm.trans hbot
  have hx : (X : RatFunc k) ∈ (⊥ : IntermediateField k (RatFunc k)) := by
    rw [← htopbot]
    trivial
  obtain ⟨d, hd⟩ := hx
  have hpoly : (Polynomial.X : k[X]) = Polynomial.C d := by
    apply FaithfulSMul.algebraMap_injective k[X] (RatFunc k)
    simpa using hd.symm
  exact Polynomial.X_ne_C d hpoly

private lemma adjoin_X_add_C_eq_top (b : k) :
    IntermediateField.adjoin k {(X : RatFunc k) + C b} = ⊤ := by
  apply top_unique
  rw [← RatFunc.adjoin_X, IntermediateField.adjoin_simple_le_iff]
  have hv := IntermediateField.subset_adjoin k {(X : RatFunc k) + C b}
    (Set.mem_singleton ((X : RatFunc k) + C b))
  have hb := (IntermediateField.adjoin k {(X : RatFunc k) + C b}).algebraMap_mem b
  simpa [← RatFunc.algebraMap_eq_C] using IntermediateField.sub_mem _ hv hb

private noncomputable def translateAlgEquiv (b : k) : RatFunc k ≃ₐ[k] RatFunc k :=
  algEquivOfGenerator ((X : RatFunc k) + C b)
    (transcendental_of_adjoin_eq_top _ (adjoin_X_add_C_eq_top b))
    (adjoin_X_add_C_eq_top b)

private lemma translateAlgEquiv_X (b : k) :
    translateAlgEquiv b (X : RatFunc k) = X + C b := by
  apply algEquivOfGenerator_X

private lemma X_add_one_ne_zero : (X : RatFunc k) + 1 ≠ 0 := by
  simpa using (algebraMap_ne_zero (Polynomial.X_add_C_ne_zero (1 : k)) :
    algebraMap k[X] (RatFunc k) (Polynomial.X + Polynomial.C 1) ≠ 0)

private lemma adjoin_fractional_eq_top (a b : k) (hab : a ≠ b) :
    IntermediateField.adjoin k {(C a * X + C b) / (X + 1 : RatFunc k)} = ⊤ := by
  let v : RatFunc k := (C a * X + C b) / (X + 1)
  have hden : v - C a ≠ 0 := by
    dsimp [v]
    intro h
    have h' := (div_eq_iff X_add_one_ne_zero).mp (sub_eq_zero.mp h)
    apply hab
    apply (C : k →+* RatFunc k).injective
    have : C b = C a := by linear_combination h'
    exact this.symm
  have hsolve : (C b - v) / (v - C a) = X := by
    apply (div_eq_iff hden).2
    dsimp [v]
    field_simp [X_add_one_ne_zero]
    ring
  apply top_unique
  rw [← RatFunc.adjoin_X, IntermediateField.adjoin_simple_le_iff]
  let E := IntermediateField.adjoin k {v}
  have hv : v ∈ E := IntermediateField.subset_adjoin k {v} (Set.mem_singleton v)
  have hfrac : (C b - v) / (v - C a) ∈ E := by
    apply IntermediateField.div_mem
    · exact IntermediateField.sub_mem _
        (by simp [← RatFunc.algebraMap_eq_C]) hv
    · exact IntermediateField.sub_mem _ hv
        (by simp [← RatFunc.algebraMap_eq_C])
  rw [hsolve] at hfrac
  exact hfrac

private noncomputable def fractionalAlgEquiv (a b : k) (hab : a ≠ b) :
    RatFunc k ≃ₐ[k] RatFunc k :=
  let v : RatFunc k := (C a * X + C b) / (X + 1)
  let hgen := adjoin_fractional_eq_top a b hab
  algEquivOfGenerator v (transcendental_of_adjoin_eq_top v hgen) hgen

private lemma fractionalAlgEquiv_X (a b : k) (hab : a ≠ b) :
    fractionalAlgEquiv a b hab (X : RatFunc k) =
      (C a * X + C b) / (X + 1) := by
  apply algEquivOfGenerator_X

private noncomputable def translateMatrix (b : k) : GL (Fin 2) k :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, b; 0, 1] (by
    simp [Matrix.det_fin_two])

private lemma translateMatrix_mobius (b : k) :
    (C (translateMatrix b 0 0) * X + C (translateMatrix b 0 1)) /
        (C (translateMatrix b 1 0) * X + C (translateMatrix b 1 1)) = X + C b := by
  simp [translateMatrix]

private lemma translateMatrix_infty (b : k) :
    translateMatrix b • (OnePoint.infty : OnePoint k) = OnePoint.infty := by
  simp [OnePoint.smul_infty_eq_ite, translateMatrix]

private lemma translateMatrix_zero (b : k) :
    translateMatrix b • ((0 : k) : OnePoint k) = (b : OnePoint k) := by
  simp [OnePoint.smul_some_eq_ite, translateMatrix]

private noncomputable def fractionalMatrix (a b : k) (hab : a ≠ b) : GL (Fin 2) k :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 1, 1] (by
    simpa [Matrix.det_fin_two] using sub_ne_zero.mpr hab)

private lemma fractionalMatrix_mobius (a b : k) (hab : a ≠ b) :
    (C (fractionalMatrix a b hab 0 0) * X + C (fractionalMatrix a b hab 0 1)) /
        (C (fractionalMatrix a b hab 1 0) * X + C (fractionalMatrix a b hab 1 1)) =
      (C a * X + C b) / (X + 1) := by
  simp [fractionalMatrix]

private lemma fractionalMatrix_infty (a b : k) (hab : a ≠ b) :
    fractionalMatrix a b hab • (OnePoint.infty : OnePoint k) = (a : OnePoint k) := by
  simp [OnePoint.smul_infty_eq_ite, fractionalMatrix]

private lemma fractionalMatrix_zero (a b : k) (hab : a ≠ b) :
    fractionalMatrix a b hab • ((0 : k) : OnePoint k) = (b : OnePoint k) := by
  simp [OnePoint.smul_some_eq_ite, fractionalMatrix]

private lemma projectiveLinearAction_injective (g : GL (Fin 2) k) :
    Function.Injective (projectiveLinearAction g) := by
  intro x y hxy
  have hxy' : g • x = g • y := by
    simpa only [projectiveLinearAction_eq_smul] using hxy
  calc
    x = g⁻¹ • (g • x) := (inv_smul_smul g x).symm
    _ = g⁻¹ • (g • y) := congrArg (fun z => g⁻¹ • z) hxy'
    _ = y := inv_smul_smul g y

private lemma preimage_pair_projectiveLinearAction (g : GL (Fin 2) k)
    (x y : OnePoint k) :
    projectiveLinearAction g ⁻¹'
        {projectiveLinearAction g x, projectiveLinearAction g y} = {x, y} := by
  ext z
  simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (hz | hz)
    · exact Or.inl (projectiveLinearAction_injective g hz)
    · exact Or.inr (projectiveLinearAction_injective g hz)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

private lemma normalize_translate_support (t : RatFunc k) (b : k)
    (hS : t.projectivePoleSupport = {OnePoint.infty, (b : OnePoint k)}) :
    (translateAlgEquiv b t).projectivePoleSupport = zeroInfinity := by
  rw [projectivePoleSupport_algEquiv (translateAlgEquiv b) t (translateMatrix b)]
  · rw [hS]
    have hinfty : projectiveLinearAction (translateMatrix b) OnePoint.infty =
        OnePoint.infty := by
      simpa only [projectiveLinearAction_eq_smul] using translateMatrix_infty b
    have hzero : projectiveLinearAction (translateMatrix b) ((0 : k) : OnePoint k) =
        (b : OnePoint k) := by
      simpa only [projectiveLinearAction_eq_smul] using translateMatrix_zero b
    calc
      projectiveLinearAction (translateMatrix b) ⁻¹' {OnePoint.infty, (b : OnePoint k)} =
          projectiveLinearAction (translateMatrix b) ⁻¹'
            {projectiveLinearAction (translateMatrix b) OnePoint.infty,
              projectiveLinearAction (translateMatrix b) ((0 : k) : OnePoint k)} := by
            rw [hinfty, hzero]
      _ = zeroInfinity := preimage_pair_projectiveLinearAction (translateMatrix b) _ _
  · rw [translateAlgEquiv_X, translateMatrix_mobius]

private lemma normalize_fractional_support (t : RatFunc k) (a b : k) (hab : a ≠ b)
    (hS : t.projectivePoleSupport = {(a : OnePoint k), (b : OnePoint k)}) :
    (fractionalAlgEquiv a b hab t).projectivePoleSupport = zeroInfinity := by
  rw [projectivePoleSupport_algEquiv (fractionalAlgEquiv a b hab) t
    (fractionalMatrix a b hab)]
  · rw [hS]
    have hinfty : projectiveLinearAction (fractionalMatrix a b hab) OnePoint.infty =
        (a : OnePoint k) := by
      simpa only [projectiveLinearAction_eq_smul] using fractionalMatrix_infty a b hab
    have hzero : projectiveLinearAction (fractionalMatrix a b hab)
        ((0 : k) : OnePoint k) = (b : OnePoint k) := by
      simpa only [projectiveLinearAction_eq_smul] using fractionalMatrix_zero a b hab
    calc
      projectiveLinearAction (fractionalMatrix a b hab) ⁻¹'
          {(a : OnePoint k), (b : OnePoint k)} =
          projectiveLinearAction (fractionalMatrix a b hab) ⁻¹'
            {projectiveLinearAction (fractionalMatrix a b hab) OnePoint.infty,
              projectiveLinearAction (fractionalMatrix a b hab) ((0 : k) : OnePoint k)} := by
            rw [hinfty, hzero]
      _ = zeroInfinity := preimage_pair_projectiveLinearAction
        (fractionalMatrix a b hab) _ _
  · rw [fractionalAlgEquiv_X, fractionalMatrix_mobius]

private lemma eq_C_mul_X_pow_of_all_roots_zero [IsAlgClosed k]
    (p : k[X]) (hroot : ∀ a ∈ p.roots, a = 0) :
    p = Polynomial.C p.leadingCoeff * Polynomial.X ^ p.natDegree := by
  have hs : p.Splits := IsAlgClosed.splits p
  have hmap : p.roots.map (fun a => Polynomial.X - Polynomial.C a) =
      p.roots.map (fun _ => Polynomial.X) := by
    refine Multiset.map_congr rfl ?_
    intro a ha
    rw [hroot a ha]
    simp
  calc
    p = Polynomial.C p.leadingCoeff *
        (p.roots.map (fun a => Polynomial.X - Polynomial.C a)).prod := hs.eq_prod_roots
    _ = Polynomial.C p.leadingCoeff *
        (p.roots.map (fun _ => Polynomial.X)).prod := by rw [hmap]
    _ = Polynomial.C p.leadingCoeff * Polynomial.X ^ p.natDegree := by
      rw [Multiset.map_const', Multiset.prod_replicate, hs.natDegree_eq_card_roots]

private lemma zeroInfinity_stabilizer_matrix (g : GL (Fin 2) k)
    (hS : g • (zeroInfinity (k := k)) = zeroInfinity) :
    (g 0 1 = 0 ∧ g 1 0 = 0) ∨ (g 0 0 = 0 ∧ g 1 1 = 0) := by
  have h0mem : g • ((0 : k) : OnePoint k) ∈ zeroInfinity := by
    rw [← hS]
    simp [zeroInfinity]
  have himem : g • (OnePoint.infty : OnePoint k) ∈ zeroInfinity := by
    rw [← hS]
    simp [zeroInfinity]
  simp only [zeroInfinity, Set.mem_insert_iff, Set.mem_singleton_iff] at h0mem himem
  by_cases hc : g 1 0 = 0
  · by_cases hd : g 1 1 = 0
    · exfalso
      apply g.det_ne_zero
      simp [Matrix.det_fin_two, hc, hd]
    · have hb : g 0 1 = 0 := by
        have h := h0mem
        simp [OnePoint.smul_some_eq_ite, hc, hd] at h
        simpa [hc, hd] using h
      exact Or.inl ⟨hb, hc⟩
  · have hd : g 1 1 = 0 := by
      have h := h0mem
      by_cases hd' : g 1 1 = 0
      · exact hd'
      · simp [OnePoint.smul_some_eq_ite, hd'] at h
        have hb : g 0 1 = 0 := by simpa [hd'] using h
        have ha : g 0 0 = 0 := by
          have hi := himem
          simp [OnePoint.smul_infty_eq_ite, hc] at hi
          simpa using hi
        exfalso
        apply g.det_ne_zero
        simp [Matrix.det_fin_two, ha, hb]
    have ha : g 0 0 = 0 := by
      have h := himem
      simp [OnePoint.smul_infty_eq_ite, hc] at h
      simpa using h
    exact Or.inr ⟨ha, hd⟩

private lemma translation_constant_eq_zero_of_support_eq_zeroInfinity [IsAlgClosed k]
    (f : RatFunc k) (hS : f.projectivePoleSupport = zeroInfinity)
    (c : k) (sigma : RatFunc k ≃ₐ[k] RatFunc k)
    (htranslate : sigma f = f + C c) : c = 0 := by
  have hroots : ∀ a ∈ f.denom.roots, a = 0 := by
    intro a ha
    have hmem : (a : OnePoint k) ∈ f.projectivePoleSupport := by
      rw [mem_projectivePoleSupport_coe_iff]
      exact (mem_roots' (p := f.denom)).mp ha |>.2
    rw [hS] at hmem
    simp only [zeroInfinity, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    exact OnePoint.coe_eq_coe.mp (hmem.resolve_left (OnePoint.coe_ne_infty a))
  have hdenom : f.denom = Polynomial.X ^ f.denom.natDegree := by
    have h := eq_C_mul_X_pow_of_all_roots_zero f.denom hroots
    rw [(monic_denom f).leadingCoeff, Polynomial.C_1, one_mul] at h
    exact h
  obtain ⟨g, hg⟩ := algEquiv_X_eq_mobius sigma
  have hcov := projectivePoleSupport_algEquiv sigma f g hg
  rw [htranslate, projectivePoleSupport_add_C, hS] at hcov
  have hstabilizes : g • (zeroInfinity (k := k)) = zeroInfinity := by
    ext z
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    have hz := Set.ext_iff.mp hcov (g⁻¹ • z)
    simp only [Set.mem_preimage] at hz
    simpa [projectiveLinearAction_eq_smul, smul_smul] using hz
  rcases zeroInfinity_stabilizer_matrix g hstabilizes with hdiag | hanti
  · let r := g 0 0 / g 1 1
    have hprod : g 0 0 * g 1 1 ≠ 0 := by
      intro hzero
      apply g.det_ne_zero
      simpa [Matrix.det_fin_two, hdiag.1, hdiag.2] using hzero
    have ha : g 0 0 ≠ 0 := left_ne_zero_of_mul hprod
    have hd : g 1 1 ≠ 0 := right_ne_zero_of_mul hprod
    have hr : r ≠ 0 := div_ne_zero ha hd
    have hCd : C (g 1 1) ≠ (0 : RatFunc k) := by
      simpa using (C : k →+* RatFunc k).injective.ne hd
    have hsigmaX : sigma (X : RatFunc k) = C r * X := by
      rw [hg]
      dsimp [r]
      rw [hdiag.1, hdiag.2]
      simp only [map_zero, zero_mul, add_zero]
      rw [map_div₀]
      field_simp [hCd]
      ring
    apply scale_translation_constant_eq_zero f.num f.denom.natDegree r c hr
    calc
      aeval (C r * X) f.num / (C r * X)^f.denom.natDegree = sigma f := by
        rw [algEquiv_apply_eq_aeval_num_div_denom, hsigmaX, hdenom]
        simp
      _ = f + C c := htranslate
      _ = algebraMap k[X] (RatFunc k) f.num /
          algebraMap k[X] (RatFunc k) (Polynomial.X^f.denom.natDegree) + C c := by
        rw [← hdenom, num_div_denom f]
  · let r := g 0 1 / g 1 0
    have hprod : g 0 1 * g 1 0 ≠ 0 := by
      intro hzero
      apply g.det_ne_zero
      simpa [Matrix.det_fin_two, hanti.1, hanti.2] using (neg_eq_zero.mpr hzero)
    have hb : g 0 1 ≠ 0 := left_ne_zero_of_mul hprod
    have hc : g 1 0 ≠ 0 := right_ne_zero_of_mul hprod
    have hr : r ≠ 0 := div_ne_zero hb hc
    have hCc : C (g 1 0) ≠ (0 : RatFunc k) := by
      simpa using (C : k →+* RatFunc k).injective.ne hc
    have hsigmaX : sigma (X : RatFunc k) = C r / X := by
      rw [hg]
      dsimp [r]
      rw [hanti.1, hanti.2]
      simp only [map_zero, zero_mul, zero_add, add_zero]
      rw [map_div₀]
      field_simp [hCc]
    apply inversion_translation_constant_eq_zero f.num f.denom.natDegree r c hr
    calc
      aeval (C r / X) f.num / (C r / X)^f.denom.natDegree = sigma f := by
        rw [algEquiv_apply_eq_aeval_num_div_denom, hsigmaX, hdenom]
        simp
      _ = f + C c := htranslate
      _ = algebraMap k[X] (RatFunc k) f.num /
          algebraMap k[X] (RatFunc k) (Polynomial.X^f.denom.natDegree) + C c := by
        rw [← hdenom, num_div_denom f]

private lemma finite_affine_translate_parameters_of_support_eq_zeroInfinity [IsAlgClosed k]
    (f : RatFunc k) (hS : f.projectivePoleSupport = zeroInfinity) :
    {c : k | ∃ sigma : RatFunc k ≃ₐ[k] RatFunc k,
      sigma f = f + algebraMap k (RatFunc k) c}.Finite := by
  apply (Set.finite_singleton 0).subset
  rintro c ⟨sigma, hsigma⟩
  have hc : c = 0 := translation_constant_eq_zero_of_support_eq_zeroInfinity
    f hS c sigma (by simpa [← RatFunc.algebraMap_eq_C] using hsigma)
  simp [hc]

/-- A rational function with exactly two projective poles has only finitely
many constant translates in its orbit under `k`-automorphisms of `k(X)`. -/
public theorem finite_affine_translate_parameters_of_projectivePoleSupport_ncard_eq_two
    [IsAlgClosed k] (t : RatFunc k) (htwo : t.projectivePoleSupport.ncard = 2) :
    {c : k | ∃ sigma : RatFunc k ≃ₐ[k] RatFunc k,
      sigma t = t + algebraMap k (RatFunc k) c}.Finite := by
  have transfer (tau : RatFunc k ≃ₐ[k] RatFunc k)
      (hnormal : (tau t).projectivePoleSupport = zeroInfinity) :
      {c : k | ∃ sigma : RatFunc k ≃ₐ[k] RatFunc k,
        sigma t = t + algebraMap k (RatFunc k) c}.Finite := by
    apply (finite_affine_translate_parameters_of_support_eq_zeroInfinity (tau t) hnormal).subset
    rintro c ⟨sigma, hsigma⟩
    let rho : RatFunc k ≃ₐ[k] RatFunc k := tau.symm.trans (sigma.trans tau)
    refine ⟨rho, ?_⟩
    dsimp [rho]
    rw [tau.symm_apply_apply, hsigma, map_add, tau.commutes]
    simp [← RatFunc.algebraMap_eq_C]
  obtain ⟨x, y, hxy, hsupport⟩ := Set.ncard_eq_two.mp htwo
  cases x with
  | infty =>
      cases y with
      | infty => exact (hxy rfl).elim
      | coe b =>
          exact transfer (translateAlgEquiv b) (normalize_translate_support t b hsupport)
  | coe a =>
      cases y with
      | infty =>
          have hsupport' : t.projectivePoleSupport =
              {OnePoint.infty, (a : OnePoint k)} := by
            simpa [Set.pair_comm] using hsupport
          exact transfer (translateAlgEquiv a)
            (normalize_translate_support t a hsupport')
      | coe b =>
          have hab : a ≠ b := by
            intro hab
            apply hxy
            simp [hab]
          exact transfer (fractionalAlgEquiv a b hab)
            (normalize_fractional_support t a b hab hsupport)

end

end RatFunc
