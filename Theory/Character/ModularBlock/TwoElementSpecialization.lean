module

public import Theory.Character.ModularBlock.OddOrderMatrixTrace
public import Theory.Character.ModularBlock.GroupAlgebraLocalTrace

/-!
# Two Element Specialization

The trivial and sign evaluations of the group algebra of an order-two
group agree modulo the maximal ideal of a local coefficient ring in which
two is a nonunit. Thus their evaluations of an odd finite-order matrix have
equal trace. A basis calculation identifies the scalar trace of an
endomorphism preceded by the nonidentity group element with the difference
of these two matrix traces.

This translates odd-order matrix rigidity into the projective-character
trace argument. Evaluation homomorphisms and the sign character are exposed
for their intended computational use by the relative-trace extensions.

Ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/NagaoTrace.lean` (revision `c3503435`).
-/

@[expose] public section

noncomputable section

open scoped BigOperators
open Module

namespace ModularBlock.NagaoTrace

universe u v

attribute [local instance] Fintype.ofFinite

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
    evalPlus R C a - evalMinus c hc hc2 hall a = (2 : R) * a.coeff c := by
  induction a using MonoidAlgebra.induction_linear with
  | zero =>
      rw [map_zero, map_zero, sub_self]
      change 0 = (2 : R) * 0
      ring
  | add a b ha hb =>
      rw [map_add, map_add]
      change _ = (2 : R) * (a.coeff c + b.coeff c)
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
      MonoidAlgebra.single g 1 * a : MonoidAlgebra R C).coeff g) = a.coeff c := by
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  rw [show MonoidAlgebra.of R C c = MonoidAlgebra.single c 1 by rfl,
    MonoidAlgebra.single_mul_single, MonoidAlgebra.coeff_single_mul_apply]
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
      ∑ i, (2 : R) * (bM.repr (f (bM i)) i).coeff c := by
  classical
  let bR : Basis C R (MonoidAlgebra R C) := MonoidAlgebra.basis _ _
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
        (bM.repr (f (bM i)) i).coeff c := by
    change (((MonoidAlgebra.of R C c) *
      (MonoidAlgebra.single g 1 * (bM.repr (f (bM i))) i) :
        MonoidAlgebra R C).coeff g) = (bM.repr (f (bM i)) i).coeff c
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

end ModularBlock.NagaoTrace

