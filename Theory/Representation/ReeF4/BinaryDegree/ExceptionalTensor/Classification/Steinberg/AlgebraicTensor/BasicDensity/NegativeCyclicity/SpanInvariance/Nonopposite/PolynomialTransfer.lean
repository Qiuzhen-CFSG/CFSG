module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.SpanInvariance.Triangular

/-!
# From actual root exchanges to representation commutators

Scalar evaluation of polynomials with endomorphism coefficients is a ring
homomorphism because field scalars are central. Dual-coordinate polynomial
uniqueness then compares their coefficients in arbitrary characteristic.
Applying this comparison successively to the two parameters in an actual
root exchange extracts its mixed degree `(1,1)` term. A correction whose
second parameter has degree two contributes zero. The resulting bracket
identity therefore holds on the original representation space.

`ShortRootExchange` specifies the actual A₂/B₂ group identities still needed
for nonopposite roots. The transfer theorems do not assert this group input:
its first correction is a short root with the geometric sum, so a long sum
forces a zero bracket. No adjoint-matrix equality is used as a substitute for
an identity in the arbitrary representation.

Source: Steinberg, *Representations of Algebraic Groups*, Nagoya Math. J.
22 (1963), §§2, 4, 10 and the first part of 11.1(1);
DOI 10.1017/S0027763000011016.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity.SpanInvariance.Nonopposite
noncomputable section
variable {F : Type*} [Field F] [IsAlgClosed F]

/-- Actual characteristic-two collection for a pair with a short second root.
The first correction is short and has root `r+s`; a possible quadratic
correction has root `r+2s`. This is group data, before applying a representation. -/
@[expose] def ShortRootExchange (r s : F4Chevalley.Root) : Prop :=
  (∀ a b : F, Commute (algebraicRootElement r a) (algebraicRootElement s b)) ∨
  ∃ t d : F4Chevalley.Root, ∃ q : F,
    ¬ IsLongRoot t ∧
    typeF4RootPairing.root t = typeF4RootPairing.root r + typeF4RootPairing.root s ∧
    (q = 0 ∨ typeF4RootPairing.root d =
      typeF4RootPairing.root r + (2 : ℕ) • typeF4RootPairing.root s) ∧
    ∀ a b : F,
      algebraicRootElement r a * algebraicRootElement s b =
        algebraicRootElement s b * algebraicRootElement r a *
          algebraicRootElement t (a * b) * algebraicRootElement d (q * a * b ^ 2)

section Polynomial
variable {A : Type*} [Ring A] [Algebra F A]

private def scalarEval (t : F) : Polynomial A →+* A :=
  Polynomial.eval₂RingHom' (RingHom.id A) (algebraMap F A t)
    (fun a => (Algebra.commutes t a).symm)

omit [IsAlgClosed F] in
private lemma scalarEval_eq_sum (q : Polynomial A) (t : F) :
    scalarEval t q = q.sum (fun n a => t ^ n • a) := by
  classical
  change Polynomial.eval₂ (RingHom.id A) (algebraMap F A t) q = _
  rw [Polynomial.eval₂_eq_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [RingHom.id_apply, ← map_pow, Algebra.smul_def]
  exact (Algebra.commutes (t ^ n) (q.coeff n)).symm

omit [IsAlgClosed F] in
private lemma scalarEval_C (t : F) (a : A) : scalarEval t (Polynomial.C a) = a := by
  exact Polynomial.eval₂_C _ _

omit [IsAlgClosed F] in
private lemma scalarEval_monomial (t : F) (n : ℕ) (a : A) :
    scalarEval t (Polynomial.monomial n a) = t ^ n • a := by
  change Polynomial.eval₂ _ _ _ = _
  rw [Polynomial.eval₂_monomial]
  simp only [RingHom.id_apply, ← map_pow, Algebra.smul_def]
  exact (Algebra.commutes (t ^ n) a).symm

private lemma scalarEval_ext (q z : Polynomial A) (h : ∀ t : F, scalarEval t q = scalarEval t z) :
    q = z := by
  classical
  let mapDual (l : Module.Dual F A) (p : Polynomial A) : Polynomial F :=
    p.sum fun n a => Polynomial.monomial n (l a)
  have hc (l : Module.Dual F A) (p : Polynomial A) (n : ℕ) :
      (mapDual l p).coeff n = l (p.coeff n) := by
    by_cases hn : n ∈ p.support
    · simp [mapDual, Polynomial.sum, Polynomial.coeff_monomial, eq_comm, hn]
    · simp [mapDual, Polynomial.sum, Polynomial.coeff_monomial, eq_comm, hn,
        Polynomial.notMem_support_iff.mp hn]
  have he (l : Module.Dual F A) (p : Polynomial A) (t : F) :
      (mapDual l p).eval t = l (scalarEval t p) := by
    rw [scalarEval_eq_sum]
    simp only [mapDual, Polynomial.sum, Polynomial.eval_finsetSum,
      Polynomial.eval_monomial, map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro n hn
    exact mul_comm _ _
  apply Polynomial.ext
  intro n
  apply sub_eq_zero.mp
  rw [← Module.forall_dual_apply_eq_zero_iff F]
  intro l
  have hp : mapDual l q = mapDual l z := by
    apply Polynomial.funext
    intro t
    rw [he, he, h]
  have hh := congrArg (fun p : Polynomial F => p.coeff n) hp
  rw [hc, hc] at hh
  simpa only [map_sub, sub_eq_zero] using hh
end Polynomial

variable {B : AlgebraicFactor F}

private def rootPoly (p : RootExpansion B.action) (r : F4Chevalley.Root) (c : F) (d : ℕ) :
    Polynomial (Module.End F B.Space) :=
  (p.coeff r).sum (fun n a => Polynomial.monomial (d * n) (c ^ n • a))

private lemma rootPoly_eval (p : RootExpansion B.action) (r : F4Chevalley.Root)
    (c t : F) (d : ℕ) :
    scalarEval t (rootPoly p r c d) =
      (B.action.action (algebraicRootElement r (c * t ^ d))).val := by
  classical
  rw [← p.eval_eq]
  simp only [rootPoly, Finsupp.sum, map_sum, scalarEval_monomial, smul_smul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [mul_pow, pow_mul]
  congr 1
  ring

private lemma coeff_zero (p : RootExpansion B.action) (r : F4Chevalley.Root) :
    p.coeff r 0 = 1 := by
  have h := p.eval_eq r 0
  have hz : (p.coeff r).sum (fun n a => (0 : F) ^ n • a) = p.coeff r 0 := by
    rw [Finsupp.sum_eq_single 0]
    · simp
    · intro n _ hn
      simp [zero_pow hn]
    · simp
  rw [hz] at h
  simpa only [ZeroAndMiddle.root_zero, map_one, Units.val_one] using h

private lemma rootPoly_coeff_linear (p : RootExpansion B.action) (r : F4Chevalley.Root)
    (c : F) (n : ℕ) : (rootPoly p r c 1).coeff n = c ^ n • p.coeff r n := by
  classical
  by_cases hn : n ∈ (p.coeff r).support
  · simp [rootPoly, Finsupp.sum, Polynomial.coeff_monomial, eq_comm, hn]
  · simp [rootPoly, Finsupp.sum, Polynomial.coeff_monomial, eq_comm, hn,
      Finsupp.notMem_support_iff.mp hn]

private lemma rootPoly_coeff_quadratic_zero (p : RootExpansion B.action) (r : F4Chevalley.Root)
    (c : F) : (rootPoly p r c 2).coeff 0 = 1 := by
  classical
  simp [rootPoly, Finsupp.sum, Polynomial.coeff_monomial, coeff_zero]

private lemma rootPoly_coeff_quadratic_one (p : RootExpansion B.action) (r : F4Chevalley.Root)
    (c : F) : (rootPoly p r c 2).coeff 1 = 0 := by
  classical
  simp only [rootPoly, Finsupp.sum, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro n hn
  rw [Polynomial.coeff_monomial]
  exact if_neg (by omega)

/-- Extract the mixed degree `(1,1)` from a genuine root exchange. The
quadratic correction contributes no first coefficient in its parameter. -/
theorem coeff_commutator_of_exchange (p : RootExpansion B.action)
    (r s t d : F4Chevalley.Root) (c q : F)
    (h : ∀ a b : F,
      algebraicRootElement r a * algebraicRootElement s b =
        algebraicRootElement s b * algebraicRootElement r a *
          algebraicRootElement t (c * a * b) * algebraicRootElement d (q * a * b ^ 2)) :
    p.coeff r 1 * p.coeff s 1 - p.coeff s 1 * p.coeff r 1 = c • p.coeff t 1 := by
  have hfirst (a : F) :
      (B.action.action (algebraicRootElement r a)).val * p.coeff s 1 =
        (B.action.action (algebraicRootElement r a)).val * ((c * a) • p.coeff t 1) +
          p.coeff s 1 * (B.action.action (algebraicRootElement r a)).val := by
    let R := (B.action.action (algebraicRootElement r a)).val
    have hp : Polynomial.C R * rootPoly p s 1 1 =
        rootPoly p s 1 1 * Polynomial.C R * rootPoly p t (c * a) 1 *
          rootPoly p d (q * a) 2 := by
      apply scalarEval_ext (F := F)
      intro b
      simp only [map_mul, scalarEval_C, rootPoly_eval, one_mul, pow_one]
      have he := congrArg (fun g => (B.action.action g).val) (h a b)
      simpa only [map_mul, Units.val_mul] using he
    have hc := congrArg (fun P : Polynomial (Module.End F B.Space) => P.coeff 1) hp
    simpa only [Polynomial.mul_coeff_one, Polynomial.mul_coeff_zero,
      Polynomial.coeff_C_zero, Polynomial.coeff_C_succ, rootPoly_coeff_linear,
      rootPoly_coeff_quadratic_zero, rootPoly_coeff_quadratic_one,
      pow_zero, pow_one, one_pow, one_smul, coeff_zero, mul_one, one_mul,
      zero_mul, mul_zero, add_zero, zero_add, R] using hc
  have hp : rootPoly p r 1 1 * Polynomial.C (p.coeff s 1) =
      rootPoly p r 1 1 * Polynomial.monomial 1 (c • p.coeff t 1) +
        Polynomial.C (p.coeff s 1) * rootPoly p r 1 1 := by
    apply scalarEval_ext (F := F)
    intro a
    simp only [map_mul, map_add, scalarEval_C, scalarEval_monomial, rootPoly_eval,
      pow_one, one_mul, smul_smul]
    simpa only [mul_comm a c] using hfirst a
  have hc := congrArg (fun P : Polynomial (Module.End F B.Space) => P.coeff 1) hp
  apply sub_eq_iff_eq_add.mpr
  simpa only [Polynomial.coeff_add, Polynomial.mul_coeff_one,
    Polynomial.coeff_C_zero, Polynomial.coeff_C_succ, Polynomial.coeff_monomial,
    rootPoly_coeff_linear, pow_zero, pow_one, one_smul, coeff_zero, mul_one,
    one_mul, zero_mul, mul_zero, add_zero, zero_add, if_true,
    show ¬ (1 : ℕ) = 0 by decide, if_false] using hc

/-- Commuting actual root groups have commuting first-degree coefficients. -/
theorem coeff_commutator_of_commute (p : RootExpansion B.action)
    (r s : F4Chevalley.Root)
    (h : ∀ a b : F, Commute (algebraicRootElement r a) (algebraicRootElement s b)) :
    p.coeff r 1 * p.coeff s 1 - p.coeff s 1 * p.coeff r 1 = 0 := by
  have he := coeff_commutator_of_exchange p r s r r 0 0 (by
    intro a b
    simpa only [zero_mul, ZeroAndMiddle.root_zero, mul_one] using (h a b).eq)
  simpa only [zero_smul] using he

/-- Transfer the short-root part of collection to the actual first coefficients. -/
theorem coeff_commutator_short_or_zero (p : RootExpansion B.action)
    (r s : F4Chevalley.Root) (h : ShortRootExchange (F := F) r s) :
    p.coeff r 1 * p.coeff s 1 - p.coeff s 1 * p.coeff r 1 = 0 ∨
    ∃ t : F4Chevalley.Root, ¬ IsLongRoot t ∧
      typeF4RootPairing.root t = typeF4RootPairing.root r + typeF4RootPairing.root s ∧
      p.coeff r 1 * p.coeff s 1 - p.coeff s 1 * p.coeff r 1 = p.coeff t 1 := by
  rcases h with h | ⟨t, d, q, ht, hsum, _hd, hex⟩
  · exact Or.inl (coeff_commutator_of_commute p r s h)
  · refine Or.inr ⟨t, ht, hsum, ?_⟩
    have he := coeff_commutator_of_exchange p r s t d 1 q (by
      simpa only [one_mul] using hex)
    simpa only [one_smul] using he

/-- If the geometric sum is long, genuine short-root collection forces the
actual representation commutator to vanish. -/
theorem coeff_commutator_long_sum_zero_of_root_exchange (p : RootExpansion B.action)
    (r s t : F4Chevalley.Root) (ht : IsLongRoot t)
    (hsum : typeF4RootPairing.root t = typeF4RootPairing.root r + typeF4RootPairing.root s)
    (h : ShortRootExchange (F := F) r s) :
    p.coeff r 1 * p.coeff s 1 - p.coeff s 1 * p.coeff r 1 = 0 := by
  rcases coeff_commutator_short_or_zero p r s h with hz | ⟨u, hu, hsum', _⟩
  · exact hz
  · exact (hu (typeF4RootPairing.root.injective (hsum.trans hsum'.symm) ▸ ht)).elim

end
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity.SpanInvariance.Nonopposite
