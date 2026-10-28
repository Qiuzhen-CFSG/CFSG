module

public import Theory.FieldTheory.RationalFunctionMobius
public import Mathlib.Algebra.Polynomial.Homogenize
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# Projective pole supports of rational functions

For `f : k(X)`, the reduced denominator alone does not record a possible pole
at infinity.  We therefore homogenize `f.denom` to the common projective degree
`max f.num.natDegree f.denom.natDegree` and evaluate this binary form on the
canonical representatives `[1, 0]` and `[a, 1]` of `P^1(k)`.  The resulting
zero set is `RatFunc.projectivePoleSupport`.  The elementary interface below
identifies its finite chart and its point at infinity, proves finiteness and
nonemptiness over an algebraically closed field for nonconstant functions, and
shows that adding a constant preserves the reduced denominator, projective
degree, and support.

The main theorem proves covariance under an automorphism whose image of `X`
is represented by `g : GL (Fin 2) k`.  Both normalized numerator and
denominator are homogenized to the same degree and the two rows of `g` are
substituted into these binary forms.  After dehomogenization this gives a
polynomial numerator-denominator pair for `sigma f`.  Cross multiplication
with the reduced pair of `sigma f`, followed by homogenization, identifies the
two denominator zero sets.  Coprimality of each reduced pair rules out losing
information at a common zero, including at infinity.  The projective action
then gives the inverse orientation
`support (sigma f) = g^-1 • support f` for the pointwise action on sets.

This is the rational-function pole calculation used in the affine-curve step
of Borel, *Linear Algebraic Groups*, Theorem 10.9
(`refs/KGroup/Bor1/Chapter3.tex`).  It is kept at the field-theory layer and
depends only on the Mobius classification in
`Theory.FieldTheory.RationalFunctionMobius`, not on algebraic-group modules.
-/

universe u

open IntermediateField Polynomial
open scoped OnePoint Pointwise

namespace RatFunc

variable {k : Type u} [Field k]

noncomputable section

local instance : DecidableEq k := Classical.decEq k

/-- The common degree used to homogenize a reduced rational function. -/
public noncomputable def projectiveDegree (f : RatFunc k) : ℕ :=
  max f.num.natDegree f.denom.natDegree

/-- The reduced denominator homogenized to the common projective degree. -/
public noncomputable def homogeneousDenominator (f : RatFunc k) :
    MvPolynomial (Fin 2) k :=
  f.denom.homogenize f.projectiveDegree

/-- Evaluation of a binary form on the canonical representatives of `P^1(k)`. -/
public noncomputable def projectiveEval (F : MvPolynomial (Fin 2) k) :
    OnePoint k → k :=
  fun x ↦ x.elim (F.eval ![1, 0]) (fun a ↦ F.eval ![a, 1])

/-- The support of the projective pole divisor, without multiplicities. -/
public noncomputable def projectivePoleSupport (f : RatFunc k) : Set (OnePoint k) :=
  {x | projectiveEval f.homogeneousDenominator x = 0}

/-- The canonical `GL₂(k)` action on the one-point model of `P^1(k)`, packaged
without exposing the decidable-equality parameter used by Mathlib's action. -/
public noncomputable def projectiveLinearAction (g : GL (Fin 2) k)
    (x : OnePoint k) : OnePoint k := by
  letI : DecidableEq k := Classical.decEq k
  exact g • x

/-- With an explicit decidable equality on the field, the packaged projective
action agrees with Mathlib's standard action. -/
public lemma projectiveLinearAction_eq_smul [DecidableEq k]
    (g : GL (Fin 2) k) (x : OnePoint k) :
    projectiveLinearAction g x = g • x := by
  cases x with
  | infty => simp [projectiveLinearAction, OnePoint.smul_infty_eq_ite]
  | coe a => simp [projectiveLinearAction, OnePoint.smul_some_eq_ite]

private lemma eval_homogenize_zero (p : k[X]) (n : ℕ) (a : k) :
    MvPolynomial.eval ![a, 0] (p.homogenize n) = p.coeff n * a ^ n := by
  simp [Polynomial.homogenize, MvPolynomial.eval_monomial]
  induction n with
  | zero => simp
  | succ n =>
      rw [Finset.Nat.sum_antidiagonal_succ']
      simp

/-- Evaluation at the canonical point at infinity reads the top coefficient. -/
public lemma eval_homogenize_one_zero (p : k[X]) (n : ℕ) :
    MvPolynomial.eval ![1, 0] (p.homogenize n) = p.coeff n := by
  simpa using eval_homogenize_zero p n 1

/-- Membership in the affine chart is vanishing of the reduced denominator. -/
public lemma mem_projectivePoleSupport_coe_iff (f : RatFunc k) (a : k) :
    (a : OnePoint k) ∈ f.projectivePoleSupport ↔ f.denom.eval a = 0 := by
  simp [projectivePoleSupport, projectiveEval, homogeneousDenominator, projectiveDegree,
    Polynomial.eval_homogenize (le_max_right f.num.natDegree f.denom.natDegree)]

/-- Infinity is a pole exactly when the denominator has smaller degree than
the common projective degree. -/
public lemma mem_projectivePoleSupport_infty_iff (f : RatFunc k) :
    (OnePoint.infty : OnePoint k) ∈ f.projectivePoleSupport ↔
      f.denom.natDegree < f.projectiveDegree := by
  rw [show (OnePoint.infty : OnePoint k) ∈ f.projectivePoleSupport ↔
      f.denom.coeff f.projectiveDegree = 0 by
    simp [projectivePoleSupport, projectiveEval, homogeneousDenominator,
      eval_homogenize_one_zero]]
  constructor
  · intro hcoeff
    have hle : f.denom.natDegree ≤ f.projectiveDegree :=
      le_max_right f.num.natDegree f.denom.natDegree
    apply lt_of_le_of_ne hle
    intro heq
    have hlc : f.denom.leadingCoeff ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr f.denom_ne_zero
    apply hlc
    rw [← Polynomial.coeff_natDegree, heq, hcoeff]
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt

/-- A rational function has only finitely many projective poles. -/
public lemma projectivePoleSupport_finite (f : RatFunc k) :
    f.projectivePoleSupport.Finite := by
  let Z : Set k := {a | Polynomial.IsRoot f.denom a}
  have hZ : Z.Finite := Polynomial.finite_setOfPred_isRoot f.denom_ne_zero
  have hZ' : ((fun a : k ↦ (a : OnePoint k)) '' Z).Finite := hZ.image _
  apply ((Set.finite_singleton (OnePoint.infty : OnePoint k)).union hZ').subset
  intro x hx
  cases x with
  | infty => exact Set.mem_union_left _ (Set.mem_singleton _)
  | coe a =>
      apply Set.mem_union_right
      refine ⟨a, ?_, rfl⟩
      simpa [Z, Polynomial.IsRoot, mem_projectivePoleSupport_coe_iff] using hx

/-- A nonconstant rational function over an algebraically closed field has a
projective pole. -/
public lemma projectivePoleSupport_nonempty [IsAlgClosed k] {f : RatFunc k}
    (hf : ¬ ∃ c, f = C c) : f.projectivePoleSupport.Nonempty := by
  by_cases hinfty : f.denom.natDegree < f.projectiveDegree
  · exact ⟨OnePoint.infty, mem_projectivePoleSupport_infty_iff f |>.2 hinfty⟩
  · have hdegree : f.projectiveDegree = f.denom.natDegree :=
      (not_lt.mp hinfty).antisymm (le_max_right f.num.natDegree f.denom.natDegree)
    have hpos : 0 < f.denom.natDegree := by
      by_contra h
      have hdenom : f.denom.natDegree = 0 := Nat.eq_zero_of_not_pos h
      have hnum : f.num.natDegree = 0 := by
        have hle := le_max_left f.num.natDegree f.denom.natDegree
        rw [← projectiveDegree, hdegree] at hle
        omega
      exact hf ((eq_C_iff f).2 ⟨hnum, hdenom⟩)
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root f.denom
      (Polynomial.natDegree_pos_iff_degree_pos.mp hpos).ne'
    refine ⟨(a : OnePoint k), (mem_projectivePoleSupport_coe_iff f a).2 ?_⟩
    exact ha

/-- Adding a constant leaves the normalized denominator unchanged. -/
public lemma denom_add_C (f : RatFunc k) (c : k) : (f + C c).denom = f.denom := by
  have hforward : (f + C c).denom ∣ f.denom := by
    simpa using denom_add_dvd f (C c)
  have hbackward : f.denom ∣ (f + C c).denom := by
    have h := denom_add_dvd (f + C c) (C (-c))
    rw [denom_C, mul_one] at h
    simpa using h
  exact Polynomial.eq_of_monic_of_associated (monic_denom (f + C c)) (monic_denom f)
    (associated_of_dvd_dvd hforward hbackward)

private lemma adjoin_add_C (f : RatFunc k) (c : k) :
    IntermediateField.adjoin k {f + C c} = IntermediateField.adjoin k {f} := by
  apply le_antisymm
  · rw [adjoin_simple_le_iff]
    exact (IntermediateField.adjoin k {f}).add_mem
      (subset_adjoin k {f} (Set.mem_singleton f))
      (by simpa using (IntermediateField.adjoin k {f}).algebraMap_mem c)
  · rw [adjoin_simple_le_iff]
    have hm := (IntermediateField.adjoin k {f + C c}).sub_mem
      (subset_adjoin k {f + C c} (Set.mem_singleton _))
      (by simpa using (IntermediateField.adjoin k {f + C c}).algebraMap_mem c)
    rw [add_sub_cancel_right] at hm
    exact hm

/-- Adding a constant leaves the projective degree unchanged. -/
public lemma projectiveDegree_add_C (f : RatFunc k) (c : k) :
    (f + C c).projectiveDegree = f.projectiveDegree := by
  rw [projectiveDegree, projectiveDegree, ← finrank_eq_max_natDegree,
    ← finrank_eq_max_natDegree, adjoin_add_C]

/-- Adding a constant leaves the projective pole support unchanged. -/
public lemma projectivePoleSupport_add_C (f : RatFunc k) (c : k) :
    (f + C c).projectivePoleSupport = f.projectivePoleSupport := by
  simp only [projectivePoleSupport, homogeneousDenominator, denom_add_C,
    projectiveDegree_add_C]

private lemma homogenized_coprime_not_both_zero (p q : k[X]) (n : ℕ)
    (hq : q ≠ 0) (hn : n = max p.natDegree q.natDegree) (v : Fin 2 → k)
    (hv : v ≠ 0) (hcoprime : IsCoprime p q) :
    ¬(MvPolynomial.eval v (p.homogenize n) = 0 ∧
      MvPolynomial.eval v (q.homogenize n) = 0) := by
  intro hzero
  by_cases hv1 : v 1 = 0
  · have hv0 : v 0 ≠ 0 := by
      intro hv0
      apply hv
      funext i
      fin_cases i <;> assumption
    have htop : p.coeff n ≠ 0 ∨ q.coeff n ≠ 0 := by
      by_cases hqn : q.natDegree = n
      · right
        simpa [← hqn] using Polynomial.leadingCoeff_ne_zero.mpr hq
      · left
        have hq_lt : q.natDegree < n := by
          have hq_le : q.natDegree ≤ n := by omega
          omega
        have hpn : p.natDegree = n := by omega
        have hp : p ≠ 0 := by
          intro hp
          subst p
          simp at hpn
          omega
        simpa [← hpn] using Polynomial.leadingCoeff_ne_zero.mpr hp
    have hvect : v = ![v 0, 0] := by
      funext i
      fin_cases i <;> simp [hv1]
    rw [hvect, eval_homogenize_zero, eval_homogenize_zero] at hzero
    rcases htop with hpcoeff | hqcoeff
    · exact (mul_ne_zero hpcoeff (pow_ne_zero _ hv0)) hzero.1
    · exact (mul_ne_zero hqcoeff (pow_ne_zero _ hv0)) hzero.2
  · have hpdegree : p.natDegree ≤ n := by omega
    have hqdegree : q.natDegree ≤ n := by omega
    have hpvalue : p.eval (v 0 / v 1) = 0 := by
      rw [Polynomial.eval_homogenize hpdegree v hv1] at hzero
      exact (mul_eq_zero.mp hzero.1).resolve_right (pow_ne_zero _ hv1)
    have hqvalue : q.eval (v 0 / v 1) = 0 := by
      rw [Polynomial.eval_homogenize hqdegree v hv1] at hzero
      exact (mul_eq_zero.mp hzero.2).resolve_right (pow_ne_zero _ hv1)
    have hcoprime' := hcoprime.map (Polynomial.evalRingHom (v 0 / v 1))
    simp [hpvalue, hqvalue] at hcoprime'

private noncomputable def mobiusLinearForms (g : GL (Fin 2) k) :
    Fin 2 → MvPolynomial (Fin 2) k :=
  fun i ↦ MvPolynomial.C (g i 0) * MvPolynomial.X 0 +
    MvPolynomial.C (g i 1) * MvPolynomial.X 1

private noncomputable def mobiusPolynomial (g : GL (Fin 2) k)
    (p : k[X]) (n : ℕ) : k[X] :=
  MvPolynomial.aeval ![Polynomial.X, 1]
    (MvPolynomial.aeval (mobiusLinearForms g) (p.homogenize n))

private lemma mobiusLinearForms_isHomogeneous (g : GL (Fin 2) k) (i : Fin 2) :
    (mobiusLinearForms g i).IsHomogeneous 1 := by
  simp only [mobiusLinearForms]
  exact (MvPolynomial.isHomogeneous_C_mul_X _ _).add
    (MvPolynomial.isHomogeneous_C_mul_X _ _)

private lemma homogenize_mobiusPolynomial (g : GL (Fin 2) k)
    (p : k[X]) (n : ℕ) :
    (mobiusPolynomial g p n).homogenize n =
      MvPolynomial.aeval (mobiusLinearForms g) (p.homogenize n) := by
  apply Polynomial.homogenize_eq_of_isHomogeneous
  · simpa using (Polynomial.isHomogeneous_homogenize p).aeval
      (mobiusLinearForms g) (mobiusLinearForms_isHomogeneous g)
  · rfl

private lemma natDegree_dehomogenize_le {F : MvPolynomial (Fin 2) k} {n : ℕ}
    (hF : F.IsHomogeneous n) :
    (MvPolynomial.aeval ![(Polynomial.X : k[X]), (1 : k[X])] F).natDegree ≤ n := by
  rw [F.as_sum, map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  rw [MvPolynomial.aeval_monomial]
  calc
    (Polynomial.C (F.coeff d) *
        ∏ i ∈ d.support, (![(Polynomial.X : k[X]), (1 : k[X])] i) ^ d i).natDegree
        ≤ (∏ i ∈ d.support,
          (![(Polynomial.X : k[X]), (1 : k[X])] i) ^ d i).natDegree :=
      Polynomial.natDegree_C_mul_le _ _
    _ ≤ ∑ i ∈ d.support,
        ((![(Polynomial.X : k[X]), (1 : k[X])] i) ^ d i).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ i ∈ d.support, d i := by
      gcongr with i hi
      fin_cases i <;> simp
    _ = n := by
      simpa [Finsupp.weight_apply, Finsupp.sum] using hF (by simpa using hd)

private lemma natDegree_mobiusPolynomial_le (g : GL (Fin 2) k)
    (p : k[X]) (n : ℕ) : (mobiusPolynomial g p n).natDegree ≤ n := by
  apply natDegree_dehomogenize_le
  simpa using (Polynomial.isHomogeneous_homogenize p).aeval
    (mobiusLinearForms g) (mobiusLinearForms_isHomogeneous g)

private lemma mobiusDenominator_ne_zero (g : GL (Fin 2) k) :
    C (g 1 0) * (X : RatFunc k) + C (g 1 1) ≠ 0 := by
  have hpoly : Polynomial.C (g 1 0) * Polynomial.X + Polynomial.C (g 1 1) ≠ 0 := by
    intro h
    have hc : g 1 0 = 0 := by
      have := congrArg (fun p : k[X] ↦ p.coeff 1) h
      simpa using this
    have hd : g 1 1 = 0 := by
      have := congrArg (fun p : k[X] ↦ p.coeff 0) h
      simpa [hc] using this
    apply g.det_ne_zero
    simp [Matrix.det_fin_two, hc, hd]
  simpa using (algebraMap_ne_zero hpoly :
    algebraMap k[X] (RatFunc k)
      (Polynomial.C (g 1 0) * Polynomial.X + Polynomial.C (g 1 1)) ≠ 0)

private lemma algebraMap_mobiusPolynomial (g : GL (Fin 2) k)
    (p : k[X]) (n : ℕ) (hp : p.natDegree ≤ n) :
    algebraMap k[X] (RatFunc k) (mobiusPolynomial g p n) =
      Polynomial.aeval
          ((C (g 0 0) * X + C (g 0 1)) / (C (g 1 0) * X + C (g 1 1))) p *
        (C (g 1 0) * X + C (g 1 1)) ^ n := by
  let A : RatFunc k := C (g 0 0) * X + C (g 0 1)
  let B : RatFunc k := C (g 1 0) * X + C (g 1 1)
  have hB : B ≠ 0 := by
    simpa [B] using mobiusDenominator_ne_zero g
  calc
    algebraMap k[X] (RatFunc k) (mobiusPolynomial g p n) =
        MvPolynomial.aeval ![A, B] (p.homogenize n) := by
      rw [mobiusPolynomial, MvPolynomial.comp_aeval_apply]
      rw [← aeval_X_left_eq_algebraMap, MvPolynomial.comp_aeval_apply]
      congr 1
      apply MvPolynomial.algHom_ext
      intro i
      fin_cases i <;> simp [mobiusLinearForms, A, B]
    _ = Polynomial.aeval (A / B) p * B ^ n := by
      have hdegree : (p.map (algebraMap k (RatFunc k))).natDegree ≤ n :=
        Polynomial.natDegree_map_le.trans hp
      simpa [Polynomial.homogenize_map, MvPolynomial.aeval_def,
        Polynomial.eval_map, Polynomial.aeval_def] using
        (Polynomial.eval_homogenize hdegree ![A, B] hB)
    _ = _ := by rfl

private lemma transcendental_algEquiv_X (sigma : RatFunc k ≃ₐ[k] RatFunc k) :
    Transcendental k (sigma (X : RatFunc k)) := by
  rw [transcendental_iff]
  intro p hp
  apply (transcendental_iff.mp RatFunc.transcendental_X) p
  have hp' := congrArg sigma.symm hp
  rw [map_zero, ← Polynomial.aeval_algHom_apply] at hp'
  simpa using hp'

private lemma mobiusPolynomial_denom_ne_zero
    (sigma : RatFunc k ≃ₐ[k] RatFunc k) (f : RatFunc k) (g : GL (Fin 2) k)
    (hsigma : sigma (X : RatFunc k) =
      (C (g 0 0) * X + C (g 0 1)) / (C (g 1 0) * X + C (g 1 1))) :
    mobiusPolynomial g f.denom f.projectiveDegree ≠ 0 := by
  intro hzero
  have hmap : algebraMap k[X] (RatFunc k)
      (mobiusPolynomial g f.denom f.projectiveDegree) ≠ 0 := by
    rw [algebraMap_mobiusPolynomial g f.denom f.projectiveDegree
      (le_max_right f.num.natDegree f.denom.natDegree), ← hsigma]
    exact mul_ne_zero
      (fun h ↦ f.denom_ne_zero
        ((transcendental_iff.mp (transcendental_algEquiv_X sigma)) f.denom h))
      (pow_ne_zero _ (mobiusDenominator_ne_zero g))
  exact hmap (by rw [hzero, map_zero])

private lemma algEquiv_apply_eq_mobiusPolynomial_div
    (sigma : RatFunc k ≃ₐ[k] RatFunc k) (f : RatFunc k) (g : GL (Fin 2) k)
    (hsigma : sigma (X : RatFunc k) =
      (C (g 0 0) * X + C (g 0 1)) / (C (g 1 0) * X + C (g 1 1))) :
    sigma f =
      algebraMap k[X] (RatFunc k) (mobiusPolynomial g f.num f.projectiveDegree) /
        algebraMap k[X] (RatFunc k) (mobiusPolynomial g f.denom f.projectiveDegree) := by
  rw [algEquiv_apply_eq_aeval_num_div_denom, hsigma,
    algebraMap_mobiusPolynomial g f.num f.projectiveDegree
      (le_max_left f.num.natDegree f.denom.natDegree),
    algebraMap_mobiusPolynomial g f.denom f.projectiveDegree
      (le_max_right f.num.natDegree f.denom.natDegree)]
  symm
  exact mul_div_mul_right _ _ (pow_ne_zero _ (mobiusDenominator_ne_zero g))

private noncomputable def projectiveCoordinates (x : OnePoint k) : Fin 2 → k :=
  x.elim ![1, 0] (fun a ↦ ![a, 1])

private lemma projectiveCoordinates_ne_zero (x : OnePoint k) :
    projectiveCoordinates x ≠ 0 := by
  cases x <;> simp [projectiveCoordinates]

private lemma projectiveEval_eq_eval_coordinates (F : MvPolynomial (Fin 2) k)
    (x : OnePoint k) :
    projectiveEval F x = MvPolynomial.eval (projectiveCoordinates x) F := by
  cases x <;> rfl

private lemma projectiveCoordinates_projectivization (x : OnePoint k) :
    OnePoint.equivProjectivization k x =
      Projectivization.mk k (projectiveCoordinates x) (projectiveCoordinates_ne_zero x) := by
  cases x <;> rfl

private lemma eval_homogenize_eq_zero_iff_projectiveEval_mk (p : k[X]) (n : ℕ)
    (hp : p.natDegree ≤ n) (v : Fin 2 → k) (hv : v ≠ 0) :
    MvPolynomial.eval v (p.homogenize n) = 0 ↔
      projectiveEval (p.homogenize n)
        ((OnePoint.equivProjectivization k).symm (Projectivization.mk k v hv)) = 0 := by
  rw [OnePoint.equivProjectivization_symm_apply_mk]
  by_cases hv1 : v 1 = 0
  · have hv0 : v 0 ≠ 0 := by
      intro hv0
      apply hv
      funext i
      fin_cases i <;> assumption
    have hvect : v = ![v 0, 0] := by
      funext i
      fin_cases i <;> simp [hv1]
    rw [if_pos hv1, hvect, eval_homogenize_zero]
    simp [projectiveEval, eval_homogenize_zero, pow_ne_zero n hv0]
  · rw [if_neg hv1, Polynomial.eval_homogenize hp v hv1]
    simp [projectiveEval, Polynomial.eval_homogenize hp,
      div_eq_mul_inv, mul_comm, pow_ne_zero n hv1]

private lemma eval_mobius_substitution (g : GL (Fin 2) k)
    (F : MvPolynomial (Fin 2) k) (v : Fin 2 → k) :
    MvPolynomial.eval v (MvPolynomial.aeval (mobiusLinearForms g) F) =
      MvPolynomial.eval (g • v) F := by
  change MvPolynomial.aeval v (MvPolynomial.aeval (mobiusLinearForms g) F) =
    MvPolynomial.aeval (g • v) F
  rw [MvPolynomial.aeval_eq_bind₁, MvPolynomial.aeval_bind₁]
  congr 1
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [mobiusLinearForms, Matrix.GeneralLinearGroup.fin_two_smul]

private lemma mobius_homogenized_not_both_zero (f : RatFunc k) (g : GL (Fin 2) k)
    (x : OnePoint k) :
    ¬(MvPolynomial.eval (projectiveCoordinates x)
          ((mobiusPolynomial g f.num f.projectiveDegree).homogenize f.projectiveDegree) = 0 ∧
      MvPolynomial.eval (projectiveCoordinates x)
          ((mobiusPolynomial g f.denom f.projectiveDegree).homogenize f.projectiveDegree) = 0) := by
  rw [homogenize_mobiusPolynomial, homogenize_mobiusPolynomial,
    eval_mobius_substitution, eval_mobius_substitution]
  apply homogenized_coprime_not_both_zero f.num f.denom f.projectiveDegree
    f.denom_ne_zero rfl (g • projectiveCoordinates x)
  · intro hzero
    apply projectiveCoordinates_ne_zero x
    calc
      projectiveCoordinates x = (g⁻¹ : GL (Fin 2) k) • (g • projectiveCoordinates x) :=
        (inv_smul_smul g (projectiveCoordinates x)).symm
      _ = (g⁻¹ : GL (Fin 2) k) • 0 := congrArg _ hzero
      _ = 0 := smul_zero _
  · exact f.isCoprime_num_denom

/-- Projective degree is invariant under rational-function automorphisms. -/
public lemma projectiveDegree_algEquiv (sigma : RatFunc k ≃ₐ[k] RatFunc k)
    (f : RatFunc k) : projectiveDegree (sigma f) = projectiveDegree f := by
  rw [projectiveDegree, projectiveDegree, ← finrank_eq_max_natDegree,
    ← finrank_eq_max_natDegree]
  have hadjoin : IntermediateField.adjoin k {sigma f} =
      (IntermediateField.adjoin k {f}).map sigma.toAlgHom := by
    change IntermediateField.adjoin k {sigma.toAlgHom f} = _
    rw [IntermediateField.adjoin_map, Set.image_singleton]
  rw [hadjoin]
  have htop : (⊤ : IntermediateField k (RatFunc k)).map sigma.toAlgHom = ⊤ := by
    apply top_unique
    intro x hx
    rw [IntermediateField.mem_map]
    exact ⟨sigma.symm x, Set.mem_univ _, sigma.apply_symm_apply x⟩
  calc
    Module.finrank ((IntermediateField.adjoin k {f}).map sigma.toAlgHom) (RatFunc k) =
        ((IntermediateField.adjoin k {f}).map sigma.toAlgHom).relfinrank ⊤ :=
      (IntermediateField.relfinrank_top_right _).symm
    _ = ((IntermediateField.adjoin k {f}).map sigma.toAlgHom).relfinrank
        ((⊤ : IntermediateField k (RatFunc k)).map sigma.toAlgHom) := by rw [htop]
    _ = (IntermediateField.adjoin k {f}).relfinrank ⊤ :=
      IntermediateField.relfinrank_map_map _ _ sigma.toAlgHom
    _ = Module.finrank (IntermediateField.adjoin k {f}) (RatFunc k) :=
      IntermediateField.relfinrank_top_right _

private lemma projectiveDenominator_zero_iff_mobiusDenominator_zero
    (sigma : RatFunc k ≃ₐ[k] RatFunc k) (f : RatFunc k) (g : GL (Fin 2) k)
    (hsigma : sigma (X : RatFunc k) =
      (C (g 0 0) * X + C (g 0 1)) / (C (g 1 0) * X + C (g 1 1)))
    (x : OnePoint k) :
    MvPolynomial.eval (projectiveCoordinates x)
        ((sigma f).denom.homogenize f.projectiveDegree) = 0 ↔
      MvPolynomial.eval (projectiveCoordinates x)
        ((mobiusPolynomial g f.denom f.projectiveDegree).homogenize f.projectiveDegree) = 0 := by
  have hqg : mobiusPolynomial g f.denom f.projectiveDegree ≠ 0 :=
    mobiusPolynomial_denom_ne_zero sigma f g hsigma
  have hratio := algEquiv_apply_eq_mobiusPolynomial_div sigma f g hsigma
  have hcross : (sigma f).num * mobiusPolynomial g f.denom f.projectiveDegree =
      mobiusPolynomial g f.num f.projectiveDegree * (sigma f).denom :=
    (num_mul_eq_mul_denom_iff hqg).2 hratio
  have hsigmaDegree : (sigma f).projectiveDegree = f.projectiveDegree :=
    projectiveDegree_algEquiv sigma f
  have hnumDegree : (sigma f).num.natDegree ≤ f.projectiveDegree := by
    rw [← hsigmaDegree]
    exact le_max_left _ _
  have hdenomDegree : (sigma f).denom.natDegree ≤ f.projectiveDegree := by
    rw [← hsigmaDegree]
    exact le_max_right _ _
  have hpgDegree := natDegree_mobiusPolynomial_le g f.num f.projectiveDegree
  have hqgDegree := natDegree_mobiusPolynomial_le g f.denom f.projectiveDegree
  have hhom := congrArg
    (fun p : k[X] ↦ p.homogenize (f.projectiveDegree + f.projectiveDegree)) hcross
  rw [Polynomial.homogenize_mul _ _ hnumDegree hqgDegree,
    Polynomial.homogenize_mul _ _ hpgDegree hdenomDegree] at hhom
  have heval := congrArg (MvPolynomial.eval (projectiveCoordinates x)) hhom
  simp only [map_mul] at heval
  have hactual :
      ¬(MvPolynomial.eval (projectiveCoordinates x)
          ((sigma f).num.homogenize f.projectiveDegree) = 0 ∧
        MvPolynomial.eval (projectiveCoordinates x)
          ((sigma f).denom.homogenize f.projectiveDegree) = 0) := by
    apply homogenized_coprime_not_both_zero (sigma f).num (sigma f).denom
      f.projectiveDegree (sigma f).denom_ne_zero
    · simpa [projectiveDegree] using hsigmaDegree.symm
    · exact projectiveCoordinates_ne_zero x
    · exact (sigma f).isCoprime_num_denom
  have hmobius := mobius_homogenized_not_both_zero f g x
  constructor
  · intro hdenom
    by_contra hq
    have hnum : MvPolynomial.eval (projectiveCoordinates x)
        ((sigma f).num.homogenize f.projectiveDegree) = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_right hq
      simpa [hdenom] using heval
    exact hactual ⟨hnum, hdenom⟩
  · intro hq
    by_contra hdenom
    have hp : MvPolynomial.eval (projectiveCoordinates x)
        ((mobiusPolynomial g f.num f.projectiveDegree).homogenize f.projectiveDegree) = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_right hdenom
      simpa [hq] using heval.symm
    exact hmobius ⟨hp, hq⟩

private lemma mobiusDenominator_zero_iff_projectiveDenominator_smul
    (f : RatFunc k) (g : GL (Fin 2) k) (x : OnePoint k) :
    MvPolynomial.eval (projectiveCoordinates x)
        ((mobiusPolynomial g f.denom f.projectiveDegree).homogenize f.projectiveDegree) = 0 ↔
      projectiveEval f.homogeneousDenominator (g • x) = 0 := by
  have hgv : g • projectiveCoordinates x ≠ 0 := by
    intro hzero
    apply projectiveCoordinates_ne_zero x
    calc
      projectiveCoordinates x = (g⁻¹ : GL (Fin 2) k) • (g • projectiveCoordinates x) :=
        (inv_smul_smul g (projectiveCoordinates x)).symm
      _ = (g⁻¹ : GL (Fin 2) k) • 0 := congrArg _ hzero
      _ = 0 := smul_zero _
  have hrepr :
      (OnePoint.equivProjectivization k).symm
          (Projectivization.mk k (g • projectiveCoordinates x) hgv) = g • x := by
    apply (OnePoint.equivProjectivization k).injective
    rw [Equiv.apply_symm_apply, OnePoint.equivProjectivization_smul,
      projectiveCoordinates_projectivization, Projectivization.smul_mk]
  rw [homogenize_mobiusPolynomial, eval_mobius_substitution,
    eval_homogenize_eq_zero_iff_projectiveEval_mk f.denom f.projectiveDegree
      (le_max_right f.num.natDegree f.denom.natDegree)
      (g • projectiveCoordinates x) hgv, hrepr]
  rfl

/-- Projective pole support is the preimage under the Mobius matrix describing
an automorphism of `k(X)`.  This is extensionally the pointwise-set formula
`support (sigma f) = g⁻¹ • support f`; the preimage statement avoids exposing
the decidable-equality parameter of Mathlib's `OnePoint` action. -/
public theorem projectivePoleSupport_algEquiv
    (sigma : RatFunc k ≃ₐ[k] RatFunc k) (f : RatFunc k) (g : GL (Fin 2) k)
    (hsigma : sigma (X : RatFunc k) =
      (C (g 0 0) * X + C (g 0 1)) / (C (g 1 0) * X + C (g 1 1))) :
    projectivePoleSupport (sigma f) =
      projectiveLinearAction g ⁻¹' projectivePoleSupport f := by
  apply Set.ext
  intro x
  change projectiveEval (sigma f).homogeneousDenominator x = 0 ↔
    projectiveEval f.homogeneousDenominator (projectiveLinearAction g x) = 0
  change projectiveEval (sigma f).homogeneousDenominator x = 0 ↔
    projectiveEval f.homogeneousDenominator (g • x) = 0
  rw [projectiveEval_eq_eval_coordinates, homogeneousDenominator,
    projectiveDegree_algEquiv sigma f,
    projectiveDenominator_zero_iff_mobiusDenominator_zero sigma f g hsigma x,
    mobiusDenominator_zero_iff_projectiveDenominator_smul]

end

end RatFunc
