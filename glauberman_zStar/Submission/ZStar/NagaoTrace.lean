import Submission.ZStar.CentralIdempotentSupport
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The odd-order trace argument over a 2-local ring

This file isolates the linear-algebra rigidity used in the elementary
Nagao/projective-character trace calculation.  Two matrices of the same odd
finite order which have the same reduction modulo the maximal ideal of a
local ring with residue characteristic two have the same trace.

The proof is constructive.  The finite sum `intertwinerSum P Q n`
intertwines `P` and `Q`; after reduction it becomes an invertible power of
`P`, so it was already invertible over the local ring.
-/

noncomputable section

open scoped BigOperators
open Module

namespace Submission.ZStar

namespace NagaoTrace

universe u v

attribute [local instance] Fintype.ofFinite

/-- The noncommutative geometric sum used to conjugate two finite-order
elements with the same residue. -/
def intertwinerSum {S : Type*} [Semiring S] (P Q : S) : ℕ → S
  | 0 => 0
  | n + 1 => P ^ n + intertwinerSum P Q n * Q

lemma mul_intertwinerSum_add_pow {S : Type*} [Semiring S]
    (P Q : S) (n : ℕ) :
    P * intertwinerSum P Q n + Q ^ n =
      P ^ n + intertwinerSum P Q n * Q := by
  induction n with
  | zero => simp [intertwinerSum]
  | succ n ih =>
    calc
      P * intertwinerSum P Q (n + 1) + Q ^ (n + 1) =
          P ^ (n + 1) + (P * intertwinerSum P Q n + Q ^ n) * Q := by
            simp only [intertwinerSum, mul_add, pow_succ]
            have hpcomm : P * P ^ n = P ^ n * P := by
              rw [← pow_succ', ← pow_succ]
            rw [hpcomm]
            noncomm_ring
      _ = P ^ (n + 1) +
          (P ^ n + intertwinerSum P Q n * Q) * Q := by rw [ih]
      _ = P ^ (n + 1) + intertwinerSum P Q (n + 1) * Q := by
        rw [intertwinerSum]

lemma map_intertwinerSum {S T : Type*} [Semiring S] [Semiring T]
    (f : S →+* T) (P Q : S) (n : ℕ) :
    f (intertwinerSum P Q n) = intertwinerSum (f P) (f Q) n := by
  induction n with
  | zero => simp [intertwinerSum]
  | succ n ih => simp [intertwinerSum, ih]

lemma intertwinerSum_self_of_char_two {S : Type*} [Semiring S]
    (h2 : (2 : S) = 0) (P : S) {n : ℕ} (hn : Odd n) :
    intertwinerSum P P n = P ^ (n - 1) := by
  have hdouble (a : S) : a + a = 0 := by
    rw [← two_mul, h2, zero_mul]
  have hpair : ∀ k : ℕ,
      intertwinerSum P P (2 * k) = 0 ∧
        intertwinerSum P P (2 * k + 1) = P ^ (2 * k) := by
    intro k
    induction k with
    | zero => simp [intertwinerSum]
    | succ k ih =>
      have heven : intertwinerSum P P (2 * (k + 1)) = 0 := by
        rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
          intertwinerSum, ih.2, ← pow_succ, hdouble]
      refine ⟨heven, ?_⟩
      rw [show 2 * (k + 1) + 1 = (2 * (k + 1)) + 1 by rfl,
        intertwinerSum, heven, zero_mul, add_zero]
  rcases hn with ⟨k, rfl⟩
  simpa using (hpair k).2

/-- Odd-order matrix lifts with the same residue are conjugate enough to have
the same trace.  No completeness, Noetherian, domain, or characteristic-zero
hypothesis is needed. -/
theorem matrix_trace_eq_of_odd_order_of_residue_eq
    {R : Type u} {ι : Type v} [CommRing R] [IsLocalRing R]
    [Fintype ι] [DecidableEq ι]
    (h2 : ¬ IsUnit (2 : R))
    {P Q : Matrix ι ι R} {n : ℕ} (hn : Odd n)
    (hP : P ^ n = 1) (hQ : Q ^ n = 1)
    (hres : P.map (IsLocalRing.residue R) =
      Q.map (IsLocalRing.residue R)) :
    Matrix.trace P = Matrix.trace Q := by
  let S : Matrix ι ι R := intertwinerSum P Q n
  have hn0 : n ≠ 0 := by
    rcases hn with ⟨k, rfl⟩
    omega
  have hinter : P * S = S * Q := by
    have h := mul_intertwinerSum_add_pow P Q n
    dsimp [S]
    rw [hP, hQ] at h
    have h' : (1 : Matrix ι ι R) + P * intertwinerSum P Q n =
        1 + intertwinerSum P Q n * Q := by
      simpa [add_comm] using h
    exact add_left_cancel h'
  have htwo_res : IsLocalRing.residue R (2 : R) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using h2
  let Pbar : Matrix ι ι (IsLocalRing.ResidueField R) :=
    P.map (IsLocalRing.residue R)
  have hPbar_pow : Pbar ^ n = 1 := by
    simpa only [Pbar, RingHom.mapMatrix_apply, Matrix.map_pow,
      map_one] using congrArg
      ((IsLocalRing.residue R).mapMatrix (m := ι)) hP
  have hPbar_unit : IsUnit Pbar :=
    IsUnit.of_pow_eq_one hPbar_pow hn0
  have hSmap : S.map (IsLocalRing.residue R) = Pbar ^ (n - 1) := by
    change (IsLocalRing.residue R).mapMatrix S = _
    rw [show (IsLocalRing.residue R).mapMatrix S =
        intertwinerSum
          ((IsLocalRing.residue R).mapMatrix P)
          ((IsLocalRing.residue R).mapMatrix Q) n by
      simpa [S] using map_intertwinerSum
        ((IsLocalRing.residue R).mapMatrix (m := ι)) P Q n]
    change intertwinerSum Pbar
      (Q.map (IsLocalRing.residue R)) n = Pbar ^ (n - 1)
    rw [← hres]
    apply intertwinerSum_self_of_char_two
    have htwoK : (2 : IsLocalRing.ResidueField R) = 0 := by
      exact (map_ofNat (IsLocalRing.residue R) 2).symm.trans htwo_res
    calc
      (2 : Matrix ι ι (IsLocalRing.ResidueField R)) =
          (2 : IsLocalRing.ResidueField R) •
            (1 : Matrix ι ι (IsLocalRing.ResidueField R)) := by
              ext i j
              simp [Matrix.ofNat_apply, Matrix.one_apply]
      _ = 0 := by rw [htwoK, zero_smul]
    exact hn
  have hSbar_unit : IsUnit (S.map (IsLocalRing.residue R)) := by
    rw [hSmap]
    exact hPbar_unit.pow _
  have hdetS_unit : IsUnit S.det := by
    apply isUnit_of_map_unit (IsLocalRing.residue R)
    rw [(IsLocalRing.residue R).map_det]
    exact (Matrix.isUnit_iff_isUnit_det _).mp hSbar_unit
  have hS_unit : IsUnit S :=
    (Matrix.isUnit_iff_isUnit_det _).mpr hdetS_unit
  let U : (Matrix ι ι R)ˣ := hS_unit.unit
  have hU : (U : Matrix ι ι R) = S := hS_unit.unit_spec
  have hconj :
      (↑U⁻¹ : Matrix ι ι R) * P * (U : Matrix ι ι R) = Q := by
    rw [hU]
    calc
      (↑U⁻¹ : Matrix ι ι R) * P * S =
          (↑U⁻¹ : Matrix ι ι R) * (P * S) := by
            rw [Matrix.mul_assoc]
      _ = (↑U⁻¹ : Matrix ι ι R) * (S * Q) := by rw [hinter]
      _ = (↑U⁻¹ : Matrix ι ι R) * ((U : Matrix ι ι R) * Q) := by rw [hU]
      _ = Q := by rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  calc
    Matrix.trace P =
        Matrix.trace ((↑U⁻¹ : Matrix ι ι R) * P * (U : Matrix ι ι R)) :=
      (Matrix.trace_units_conj' U P).symm
    _ = Matrix.trace Q := by rw [hconj]

/-- The sign character of a two-element group, written without choosing an
explicit equivalence with `C₂`. -/
def cardTwoSign
    {R C : Type*} [CommRing R] [CommGroup C] [DecidableEq C]
    (c : C) (hc : c ≠ 1) (hc2 : c * c = 1)
    (hall : ∀ g : C, g = 1 ∨ g = c) : C →* R where
  toFun g := if g = 1 then 1 else -1
  map_one' := by simp
  map_mul' := by
    intro g h
    rcases hall g with rfl | rfl <;>
      rcases hall h with rfl | rfl <;>
      simp [hc, hc2]

@[simp] lemma cardTwoSign_one
    {R C : Type*} [CommRing R] [CommGroup C] [DecidableEq C]
    (c : C) (hc : c ≠ 1) (hc2 : c * c = 1)
    (hall : ∀ g : C, g = 1 ∨ g = c) :
    cardTwoSign c hc hc2 hall 1 = (1 : R) := by
  simp [cardTwoSign]

lemma cardTwoSign_apply_of_ne_one
    {R C : Type*} [CommRing R] [CommGroup C] [DecidableEq C]
    (c : C) (hc : c ≠ 1) (hc2 : c * c = 1)
    (hall : ∀ g : C, g = 1 ∨ g = c) {g : C} (hg : g ≠ 1) :
    cardTwoSign c hc hc2 hall g = (-1 : R) := by
  simp [cardTwoSign, hg]

/-- Evaluation of a two-element group algebra at the trivial character. -/
def evalPlus
    (R : Type u) (C : Type v) [CommRing R] [CommGroup C] :
    MonoidAlgebra R C →+* R :=
  ((MonoidAlgebra.lift R R C) (1 : C →* R)).toRingHom

/-- Evaluation of a two-element group algebra at its sign character. -/
def evalMinus
    {R : Type u} {C : Type v} [CommRing R] [CommGroup C]
    [DecidableEq C]
    (c : C) (hc : c ≠ 1) (hc2 : c * c = 1)
    (hall : ∀ g : C, g = 1 ∨ g = c) :
    MonoidAlgebra R C →+* R :=
  ((MonoidAlgebra.lift R R C) (cardTwoSign c hc hc2 hall)).toRingHom

@[simp] lemma evalPlus_single
    {R : Type u} {C : Type v} [CommRing R] [CommGroup C]
    (g : C) (r : R) :
    evalPlus R C (MonoidAlgebra.single g r) = r := by
  simp [evalPlus]

@[simp] lemma evalMinus_single
    {R : Type u} {C : Type v} [CommRing R] [CommGroup C]
    [DecidableEq C]
    (c : C) (hc : c ≠ 1) (hc2 : c * c = 1)
    (hall : ∀ g : C, g = 1 ∨ g = c) (g : C) (r : R) :
    evalMinus c hc hc2 hall (MonoidAlgebra.single g r) =
      r * cardTwoSign c hc hc2 hall g := by
  simp [evalMinus]

/-- In residue characteristic two the trivial and sign evaluations of the
order-two group algebra agree. -/
lemma residue_evalPlus_eq_evalMinus
    {R : Type u} {C : Type v} [CommRing R] [IsLocalRing R]
    [CommGroup C] [DecidableEq C]
    (h2 : ¬ IsUnit (2 : R))
    (c : C) (hc : c ≠ 1) (hc2 : c * c = 1)
    (hall : ∀ g : C, g = 1 ∨ g = c)
    (a : MonoidAlgebra R C) :
    IsLocalRing.residue R (evalPlus R C a) =
      IsLocalRing.residue R (evalMinus c hc hc2 hall a) := by
  have htwo_res : IsLocalRing.residue R (2 : R) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using h2
  have htwoK : (2 : IsLocalRing.ResidueField R) = 0 :=
    (map_ofNat (IsLocalRing.residue R) 2).symm.trans htwo_res
  have hneg (x : IsLocalRing.ResidueField R) : -x = x := by
    have hone : (-1 : IsLocalRing.ResidueField R) = 1 := by
      apply neg_eq_iff_add_eq_zero.mpr
      simpa only [one_add_one_eq_two] using htwoK
    rw [← neg_one_mul, hone, one_mul]
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single g r =>
      by_cases hg : g = 1
      · subst g
        simp
      · rw [evalPlus_single, evalMinus_single,
          cardTwoSign_apply_of_ne_one c hc hc2 hall hg,
          mul_neg, mul_one, map_neg, hneg]

/-- Matrix form of the order-two group-algebra trace rigidity: the two
specializations of an odd finite-order matrix have equal trace. -/
theorem matrix_trace_evalPlus_eq_evalMinus_of_odd_order
    {R : Type u} {C : Type v} {ι : Type*}
    [CommRing R] [IsLocalRing R] [CommGroup C]
    [Fintype ι] [DecidableEq ι] [DecidableEq C]
    (h2 : ¬ IsUnit (2 : R))
    (c : C) (hc : c ≠ 1) (hc2 : c * c = 1)
    (hall : ∀ g : C, g = 1 ∨ g = c)
    {F : Matrix ι ι (MonoidAlgebra R C)} {n : ℕ} (hn : Odd n)
    (hF : F ^ n = 1) :
    Matrix.trace (F.map (evalPlus R C)) =
      Matrix.trace (F.map (evalMinus c hc hc2 hall)) := by
  apply matrix_trace_eq_of_odd_order_of_residue_eq h2 hn
  · change (((evalPlus R C).mapMatrix (m := ι)) F) ^ n = 1
    rw [← map_pow, hF, map_one]
  · change (((evalMinus c hc hc2 hall).mapMatrix (m := ι)) F) ^ n = 1
    rw [← map_pow, hF, map_one]
  · ext i j
    exact residue_evalPlus_eq_evalMinus h2 c hc hc2 hall (F i j)

/-- The difference of the two order-two specializations is twice the
coefficient of the nonidentity element. -/
lemma evalPlus_sub_evalMinus_eq_two_mul_coeff
    {R : Type u} {C : Type v} [CommRing R] [CommGroup C]
    [DecidableEq C]
    (c : C) (hc : c ≠ 1) (hc2 : c * c = 1)
    (hall : ∀ g : C, g = 1 ∨ g = c)
    (a : MonoidAlgebra R C) :
    evalPlus R C a - evalMinus c hc hc2 hall a = (2 : R) * a c := by
  induction a using MonoidAlgebra.induction_linear with
  | zero =>
      rw [map_zero, map_zero, sub_self]
      change 0 = (2 : R) * 0
      ring
  | add a b ha hb =>
      rw [map_add, map_add]
      change _ = (2 : R) * (a c + b c)
      linear_combination ha + hb
  | single g r =>
      rcases hall g with rfl | rfl
      · simp [hc]
      · simp [cardTwoSign, hc]
        ring

lemma coeff_shift_of_involution
    {R C : Type*} [CommRing R] [CommGroup C] [DecidableEq C]
    (c : C) (hc2 : c * c = 1) (g : C) (a : MonoidAlgebra R C) :
    (((MonoidAlgebra.of R C c) *
      MonoidAlgebra.single g 1 * a : MonoidAlgebra R C) g) = a c := by
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  rw [show MonoidAlgebra.of R C c = MonoidAlgebra.single c 1 by rfl,
    MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_apply]
  simp [hcinv]

/-- The trace over `R` of multiplication by the involution followed by an
`R[C]`-linear endomorphism is twice the coefficient trace over `R[C]`. -/
theorem trace_lsmul_comp_eq_two_mul_coeff_sum
    {R C M ι : Type*} [CommRing R] [CommGroup C] [Finite C]
    [Fintype ι] [DecidableEq ι] [DecidableEq C]
    [AddCommGroup M] [Module R M] [Module (MonoidAlgebra R C) M]
    [IsScalarTower R (MonoidAlgebra R C) M]
    (bM : Basis ι (MonoidAlgebra R C) M)
    (c : C) (hc2 : c * c = 1) (hC : Nat.card C = 2)
    (f : M →ₗ[MonoidAlgebra R C] M) :
    LinearMap.trace R M
        (((LinearMap.lsmul (MonoidAlgebra R C) M
          (MonoidAlgebra.of R C c)).comp f).restrictScalars R) =
      ∑ i, (2 : R) * (bM.repr (f (bM i)) i) c := by
  classical
  let bR : Basis C R (MonoidAlgebra R C) := Finsupp.basisSingleOne
  rw [LinearMap.trace_eq_matrix_trace R (bR.smulTower' bM), Matrix.trace]
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply,
    Basis.smulTower'_repr, Basis.smulTower'_apply,
    LinearMap.restrictScalars_apply, LinearMap.comp_apply,
    LinearMap.lsmul_apply]
  rw [Fintype.sum_prod_type]
  simp only [map_smul]
  simp only [Finsupp.smul_apply, smul_eq_mul]
  apply Fintype.sum_congr
  intro i
  have hterm (g : C) :
      (bR.repr ((MonoidAlgebra.of R C) c *
        (bR g * (bM.repr (f (bM i))) i))) g =
        (bM.repr (f (bM i)) i) c := by
    change (((MonoidAlgebra.of R C c) *
      (MonoidAlgebra.single g 1 * (bM.repr (f (bM i))) i) :
        MonoidAlgebra R C) g) = (bM.repr (f (bM i)) i) c
    simpa [mul_assoc] using
      coeff_shift_of_involution c hc2 g (bM.repr (f (bM i)) i)
  simp_rw [hterm]
  have hcard : Fintype.card C = 2 := by
    simpa using hC
  simp [hcard, two_mul]

/-- The preceding coefficient formula can be rewritten as the difference of
the two order-two matrix specializations. -/
theorem trace_lsmul_comp_eq_evalPlus_sub_evalMinus
    {R C M ι : Type*} [CommRing R] [CommGroup C] [Finite C]
    [Fintype ι] [DecidableEq ι] [DecidableEq C]
    [AddCommGroup M] [Module R M] [Module (MonoidAlgebra R C) M]
    [IsScalarTower R (MonoidAlgebra R C) M]
    (bM : Basis ι (MonoidAlgebra R C) M)
    (c : C) (hc : c ≠ 1) (hc2 : c * c = 1) (hC : Nat.card C = 2)
    (hall : ∀ g : C, g = 1 ∨ g = c)
    (f : M →ₗ[MonoidAlgebra R C] M) :
    LinearMap.trace R M
        (((LinearMap.lsmul (MonoidAlgebra R C) M
          (MonoidAlgebra.of R C c)).comp f).restrictScalars R) =
      Matrix.trace
          ((LinearMap.toMatrix bM bM f).map (evalPlus R C)) -
        Matrix.trace
          ((LinearMap.toMatrix bM bM f).map
            (evalMinus c hc hc2 hall)) := by
  rw [trace_lsmul_comp_eq_two_mul_coeff_sum bM c hc2 hC f]
  rw [Matrix.trace, Matrix.trace, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Matrix.diag_apply, Matrix.map_apply, LinearMap.toMatrix_apply]
  simpa only [LinearMap.toMatrix_apply] using
    (evalPlus_sub_evalMinus_eq_two_mul_coeff c hc hc2 hall
      ((LinearMap.toMatrix bM bM f) i i)).symm

/-- An odd finite-order `R[C₂]`-linear endomorphism has trace zero after
multiplication by the nonidentity element of `C₂`. -/
theorem trace_lsmul_comp_eq_zero_of_odd_order
    {R C M : Type*} [CommRing R] [IsLocalRing R]
    [CommGroup C] [Finite C]
    [AddCommGroup M] [Module R M] [Module (MonoidAlgebra R C) M]
    [IsScalarTower R (MonoidAlgebra R C) M]
    [Module.Free (MonoidAlgebra R C) M]
    [Module.Finite (MonoidAlgebra R C) M]
    (h2 : ¬ IsUnit (2 : R))
    (c : C) (hc : c ≠ 1) (hc2 : c * c = 1)
    (hC : Nat.card C = 2)
    (f : M →ₗ[MonoidAlgebra R C] M) {n : ℕ} (hn : Odd n)
    (hf : f ^ n = 1) :
    LinearMap.trace R M
        (((LinearMap.lsmul (MonoidAlgebra R C) M
          (MonoidAlgebra.of R C c)).comp f).restrictScalars R) = 0 := by
  classical
  obtain ⟨d, hd, hd_unique⟩ := (Nat.card_eq_two_iff' (1 : C)).mp hC
  have hcd : c = d := hd_unique c hc
  have hall (g : C) : g = 1 ∨ g = c := by
    by_cases hg : g = 1
    · exact Or.inl hg
    · exact Or.inr ((hd_unique g hg).trans hcd.symm)
  let bM := Module.Free.chooseBasis (MonoidAlgebra R C) M
  let F := LinearMap.toMatrix bM bM f
  have hF : F ^ n = 1 := by
    dsimp [F]
    rw [LinearMap.toMatrix_pow, hf, LinearMap.toMatrix_one]
  rw [trace_lsmul_comp_eq_evalPlus_sub_evalMinus
    bM c hc hc2 hC hall f]
  have heq := matrix_trace_evalPlus_eq_evalMinus_of_odd_order
    h2 c hc hc2 hall hn hF
  rw [heq, sub_self]

/-- Projective version of `trace_lsmul_comp_eq_zero_of_odd_order`.  The
order-two group algebra is local, so finite projective modules are free. -/
theorem trace_lsmul_comp_eq_zero_of_projective_odd_order
    {R C M : Type*} [CommRing R] [IsLocalRing R]
    [CommGroup C] [Finite C]
    [AddCommGroup M] [Module R M] [Module (MonoidAlgebra R C) M]
    [IsScalarTower R (MonoidAlgebra R C) M]
    [Module.Projective (MonoidAlgebra R C) M]
    [Module.Finite (MonoidAlgebra R C) M]
    (h2 : ¬ IsUnit (2 : R))
    (c : C) (hc : c ≠ 1) (hc2 : c * c = 1)
    (hC : Nat.card C = 2)
    (f : M →ₗ[MonoidAlgebra R C] M) {n : ℕ} (hn : Odd n)
    (hf : f ^ n = 1) :
    LinearMap.trace R M
        (((LinearMap.lsmul (MonoidAlgebra R C) M
          (MonoidAlgebra.of R C c)).comp f).restrictScalars R) = 0 := by
  letI : IsLocalRing (MonoidAlgebra R C) :=
    CentralIdempotentSupport.isLocalRing_monoidAlgebra_of_card_two h2 hC
  letI : Module.Free (MonoidAlgebra R C) M :=
    Module.free_of_flat_of_isLocalRing
  exact trace_lsmul_comp_eq_zero_of_odd_order
    h2 c hc hc2 hC f hn hf

/-- Representation-theoretic form of the projective odd-order trace theorem.

If the restriction of `rho` along a two-element subgroup `C` is finite
projective over `R[C]`, then every odd-order element centralizing that subgroup
has trace zero on the coset of its nonidentity element. -/
theorem trace_mul_eq_zero_of_projective_restriction_of_odd_order
    {R C G V : Type*} [CommRing R] [IsLocalRing R]
    [CommGroup C] [Finite C] [Group G]
    [AddCommGroup V] [Module R V]
    (rho : Representation R G V) (phi : C →* G)
    [Module.Projective (MonoidAlgebra R C)
      (Representation.asModule (rho.comp phi : Representation R C V))]
    [Module.Finite (MonoidAlgebra R C)
      (Representation.asModule (rho.comp phi : Representation R C V))]
    (h2 : ¬ IsUnit (2 : R))
    (c : C) (hc : c ≠ 1) (hc2 : c * c = 1)
    (hC : Nat.card C = 2)
    (x : G) (hcomm : ∀ g : C, x * phi g = phi g * x)
    {n : ℕ} (hn : Odd n) (hxpow : x ^ n = 1) :
    LinearMap.trace R V (rho (phi c * x)) = 0 := by
  let sigma : Representation R C V := rho.comp phi
  let T : sigma.IntertwiningMap sigma :=
    (rho x).intertwiningMap_of_isIntertwiningMap sigma sigma (by
      intro g v
      change rho x (rho (phi g) v) = rho (phi g) (rho x v)
      change (rho x * rho (phi g)) v = (rho (phi g) * rho x) v
      rw [← map_mul, hcomm, map_mul])
  let f : Module.End (MonoidAlgebra R C) sigma.asModule :=
    Representation.IntertwiningMap.equivAlgEnd sigma T
  have hTcoe (k : ℕ) : (T ^ k).toLinearMap = (rho x) ^ k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ, pow_succ,
        Representation.IntertwiningMap.coe_mul, ih]
      rfl
  have hTpow : T ^ n = 1 := by
    apply Representation.IntertwiningMap.ext
    rw [hTcoe]
    change (rho x) ^ n = 1
    rw [← map_pow, hxpow, map_one]
  have hfpow : f ^ n = 1 := by
    dsimp [f]
    rw [← map_pow, hTpow, map_one]
  have hzero := trace_lsmul_comp_eq_zero_of_projective_odd_order
    (R := R) (C := C) (M := sigma.asModule)
    h2 c hc hc2 hC f hn hfpow
  let L : Module.End R sigma.asModule :=
    (((LinearMap.lsmul (MonoidAlgebra R C) sigma.asModule
      (MonoidAlgebra.of R C c)).comp f).restrictScalars R)
  have hconj : sigma.asModuleEquiv.conj L = rho (phi c * x) := by
    ext v
    simp [L, f, T, sigma,
      Representation.IntertwiningMap.equivAlgEnd,
      Representation.IntertwiningMap.equivLinearMapAsModule,
      Representation.asModuleEquiv,
      LinearEquiv.conj_apply_apply, map_mul]
    rfl
  calc
    LinearMap.trace R V (rho (phi c * x)) =
        LinearMap.trace R V (sigma.asModuleEquiv.conj L) := by rw [hconj]
    _ = LinearMap.trace R sigma.asModule L :=
      LinearMap.trace_conj' L sigma.asModuleEquiv
    _ = 0 := hzero

/-- The same theorem with the cyclic subgroup generated by an involution as
the source of the restriction.  This formulation is convenient in section
arguments: the caller only supplies the projectivity of the restricted module
and commutation with the involution. -/
theorem trace_z_mul_eq_zero_of_projective_zpowers_restriction_of_odd_order
    {R G V : Type*} [CommRing R] [IsLocalRing R]
    [Group G] [AddCommGroup V] [Module R V]
    (rho : Representation R G V) (z : G)
    [Module.Projective (MonoidAlgebra R (Subgroup.zpowers z))
      (Representation.asModule
        (rho.comp (Subgroup.zpowers z).subtype :
          Representation R (Subgroup.zpowers z) V))]
    [Module.Finite (MonoidAlgebra R (Subgroup.zpowers z))
      (Representation.asModule
        (rho.comp (Subgroup.zpowers z).subtype :
          Representation R (Subgroup.zpowers z) V))]
    (h2 : ¬ IsUnit (2 : R))
    (hz : z ≠ 1) (hz2 : z ^ 2 = 1)
    (x : G) (hxz : Commute x z) (hxodd : Odd (orderOf x)) :
    LinearMap.trace R V (rho (z * x)) = 0 := by
  -- A cyclic subgroup carries its canonical commutative-group structure.
  letI : CommGroup (Subgroup.zpowers z) := IsCyclic.commGroup
  let c : Subgroup.zpowers z := ⟨z, Subgroup.mem_zpowers z⟩
  have hc : c ≠ 1 := by
    intro h
    exact hz (congrArg Subtype.val h)
  have hc2 : c * c = 1 := by
    apply Subtype.ext
    simpa [pow_two] using hz2
  have hzOrder : orderOf z = 2 := orderOf_eq_prime hz2 hz
  have hC : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers, hzOrder]
  letI : Finite (Subgroup.zpowers z) :=
    Nat.finite_of_card_ne_zero (by omega)
  have hcomm : ∀ g : Subgroup.zpowers z,
      x * (Subgroup.zpowers z).subtype g =
        (Subgroup.zpowers z).subtype g * x := by
    rw [Subgroup.forall_zpowers]
    intro m
    exact (hxz.zpow_right m).eq
  simpa [c] using
    trace_mul_eq_zero_of_projective_restriction_of_odd_order
      rho (Subgroup.zpowers z).subtype h2 c hc hc2 hC x hcomm hxodd
        (pow_orderOf_eq_one x)

end NagaoTrace

end Submission.ZStar
