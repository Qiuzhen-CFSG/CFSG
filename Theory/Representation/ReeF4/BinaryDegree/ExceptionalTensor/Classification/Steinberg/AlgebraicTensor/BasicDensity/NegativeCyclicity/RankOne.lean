module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.ZeroAndMiddle.Geometry
public import Mathlib.Algebra.Polynomial.Reverse

/-!
# Local highest strings for negative short-root cyclicity

A highest vector of simple-coroot exponent `n` has a negative simple-root
orbit polynomial of degree at most `n`, whose top coefficient is the actual
Weyl translate. In particular, exponent zero gives fixation and exponent one
identifies the Weyl translate with the first lowering coefficient. Only the
selected positive root group and coroot are constrained.

The proof compares the negative orbit polynomial with the reciprocal positive
orbit polynomial of the Weyl translate using the rank-one Bruhat word. This
localizes the zero-exponent argument in `ZeroAndMiddle.Zero` and extends the
coefficient argument in `EndNode.Multiplicity.RankOneCoefficients`. It makes no
assumption of differential irreducibility.

Source: Steinberg, *Representations of Algebraic Groups*, Nagoya Math. J.
22 (1963), §4, especially 4.3, and the first part of 11.1(1), pp. 52–53;
DOI 10.1017/S0027763000011016.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity
open EndNode.Multiplicity ZeroAndMiddle
noncomputable section
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

omit [IsAlgClosed F] in
private theorem eval_reflect (q : Polynomial F) (N : ℕ) (hN : q.natDegree ≤ N)
    (t : F) (ht : t ≠ 0) :
    (q.reflect N).eval t = t ^ N * q.eval t⁻¹ := by
  let _ : Invertible (t⁻¹) := invertibleOfNonzero (inv_ne_zero ht)
  have h := Polynomial.eval₂_reflect_mul_pow (RingHom.id F) (t⁻¹) N q hN
  have h' : (q.reflect N).eval t * (t⁻¹) ^ N = q.eval t⁻¹ := by
    simpa [invOf_eq_inv] using h
  calc
    (q.reflect N).eval t = ((q.reflect N).eval t * (t⁻¹) ^ N) * t ^ N := by
      rw [mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero N ht), mul_one]
    _ = q.eval t⁻¹ * t ^ N := by rw [h']
    _ = t ^ N * q.eval t⁻¹ := mul_comm _ _

private theorem reciprocal_coeff (p q : Polynomial F) (n k : ℕ) (hk : k ≤ n)
    (h : ∀ t : F, t ≠ 0 → p.eval t = t ^ n * q.eval t⁻¹) :
    p.coeff k = q.coeff (n - k) := by
  let N := max n q.natDegree
  have hn : n ≤ N := le_max_left _ _
  have hq : q.natDegree ≤ N := le_max_right _ _
  have he : Polynomial.X ^ N * p = Polynomial.X ^ n * q.reflect N := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_of_finite_compl
      (by simp : ({t : F | t ≠ 0} : Set F)ᶜ.Finite)).mono
    intro t ht
    simp only [Set.mem_ofPred_eq] at ht ⊢
    rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, h t ht,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, eval_reflect q N hq t ht]
    ring
  have hc := congrArg (fun f : Polynomial F => f.coeff (k + N)) he
  rw [Polynomial.coeff_X_pow_mul, Polynomial.coeff_X_pow_mul', if_pos (by omega),
    Polynomial.coeff_reflect, Polynomial.revAt_le (by omega)] at hc
  have hi : N - (k + N - n) = n - k := by omega
  rwa [hi] at hc

/-- A polynomial reciprocal identity of weight `n` has no terms above `n`. -/
private theorem reciprocal_coeff_eq_zero (p q : Polynomial F) (n k : ℕ) (hk : n < k)
    (h : ∀ t : F, t ≠ 0 → p.eval t = t ^ n * q.eval t⁻¹) :
    p.coeff k = 0 := by
  let N := max n q.natDegree
  have hn : n ≤ N := le_max_left _ _
  have hq : q.natDegree ≤ N := le_max_right _ _
  have he : Polynomial.X ^ N * p = Polynomial.X ^ n * q.reflect N := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_of_finite_compl
      (by simp : ({t : F | t ≠ 0} : Set F)ᶜ.Finite)).mono
    intro t ht
    simp only [Set.mem_ofPred_eq] at ht ⊢
    rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, h t ht,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, eval_reflect q N hq t ht]
    ring
  have hc := congrArg (fun f : Polynomial F => f.coeff (k + N)) he
  rw [Polynomial.coeff_X_pow_mul, Polynomial.coeff_X_pow_mul', if_pos (by omega)] at hc
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt (by simpa [max_eq_left hq] using
      (Polynomial.natDegree_reflect_le (p := q) (N := N)))
      (show N < k + N - n by omega))] at hc
  exact hc

variable [CharP F 2]

private theorem root_mul_self (r : F4Chevalley.Root) (t : F) :
    algebraicRootElement r t * algebraicRootElement r t = 1 := by
  have hi : (algebraicRootElement r t)⁻¹ = algebraicRootElement r t := by
    rw [root_inv, CharTwo.neg_eq]
  calc
    _ = algebraicRootElement r t * (algebraicRootElement r t)⁻¹ := by rw [hi]
    _ = 1 := mul_inv_cancel _

private theorem lower_bruhat (r : F4Chevalley.Root) (t : F) (ht : t ≠ 0) :
    algebraicRootElement (-r) t =
      algebraicRootElement r t⁻¹ *
        (algebraicCorootElement r (Units.mk0 t ht)⁻¹ * algebraicNElement r 1) *
        algebraicRootElement r t⁻¹ := by
  have he : algebraicCorootElement r (Units.mk0 t ht)⁻¹ * algebraicNElement r 1 =
      algebraicNElement r (Units.mk0 t ht)⁻¹ := by
    rw [algebraicCorootElement]
    group
  rw [he]
  have hn : algebraicNElement r (Units.mk0 t ht)⁻¹ =
      algebraicRootElement r t⁻¹ * algebraicRootElement (-r) t *
        algebraicRootElement r t⁻¹ := by
    simp [algebraicNElement, CharTwo.neg_eq]
  rw [hn]
  simp only [← mul_assoc, root_mul_self, one_mul]
  rw [mul_assoc, root_mul_self, mul_one]

private theorem highest_reciprocal (B : AlgebraicFactor F) (i : Fin 4) (n : ℕ)
    (v : B.Space)
    (hupper : ∀ a : F, (B.action.action (algebraicRootElement (typeF4SimpleRootIndex i) a) :
      Module.End F B.Space) v = v)
    (htorus : ∀ t : Fˣ, (B.action.action (algebraicCorootElement (typeF4SimpleRootIndex i) t) :
      Module.End F B.Space) v = (t : F) ^ n • v)
    (l : Module.Dual F B.Space) (s : F) (hs : s ≠ 0) :
    (rootPolynomial B (-typeF4SimpleRootIndex i) l v).eval s =
      s ^ n * (rootPolynomial B (typeF4SimpleRootIndex i) l
        ((B.action.action (algebraicNElement (typeF4SimpleRootIndex i) 1) :
          Module.End F B.Space) v)).eval s⁻¹ := by
  let w := (B.action.action (algebraicNElement (typeF4SimpleRootIndex i) 1) :
    Module.End F B.Space) v
  have hdiag (t : Fˣ) :
      (B.action.action (algebraicCorootElement (typeF4SimpleRootIndex i) t) :
        Module.End F B.Space) w = ((t⁻¹ : Fˣ) : F) ^ n • w := by
    dsimp only [w]
    change ((B.action.action _ * B.action.action _ : LinearMap.GeneralLinearGroup F B.Space) :
      Module.End F B.Space) v = _
    rw [← map_mul, coroot_n_inverse, map_mul]
    change (B.action.action _ : Module.End F B.Space)
      ((B.action.action _ : Module.End F B.Space) v) = _
    rw [htorus, map_smul]
  rw [rootPolynomial_eval, rootPolynomial_eval, lower_bruhat _ s hs, map_mul, map_mul, map_mul]
  change l ((B.action.action _ : Module.End F B.Space)
    ((B.action.action _ : Module.End F B.Space)
      ((B.action.action _ : Module.End F B.Space)
        ((B.action.action _ : Module.End F B.Space) v)))) = _
  rw [hupper]
  change l ((B.action.action _ : Module.End F B.Space)
    ((B.action.action _ : Module.End F B.Space) w)) = _
  rw [hdiag]
  simp only [inv_inv, Units.val_mk0, map_smul, smul_eq_mul]
  rfl


/-- The negative simple root orbit of a highest vector has degree at most its
single corresponding coroot exponent. No conditions on other coroots are used. -/
theorem negative_simple_rootPolynomial_coeff_eq_zero (B : AlgebraicFactor F)
    (i : Fin 4) (n : ℕ) (v : B.Space)
    (hupper : ∀ a : F, (B.action.action (algebraicRootElement (typeF4SimpleRootIndex i) a) :
      Module.End F B.Space) v = v)
    (htorus : ∀ t : Fˣ, (B.action.action (algebraicCorootElement (typeF4SimpleRootIndex i) t) :
      Module.End F B.Space) v = (t : F) ^ n • v)
    (l : Module.Dual F B.Space) (k : ℕ) (hk : n < k) :
    (rootPolynomial B (-typeF4SimpleRootIndex i) l v).coeff k = 0 :=
  reciprocal_coeff_eq_zero _ _ n k hk (highest_reciprocal B i n v hupper htorus l)

/-- The top coefficient is the Weyl translate, in the positive-coroot convention. -/
theorem negative_simple_rootPolynomial_top_coeff (B : AlgebraicFactor F)
    (i : Fin 4) (n : ℕ) (v : B.Space)
    (hupper : ∀ a : F, (B.action.action (algebraicRootElement (typeF4SimpleRootIndex i) a) :
      Module.End F B.Space) v = v)
    (htorus : ∀ t : Fˣ, (B.action.action (algebraicCorootElement (typeF4SimpleRootIndex i) t) :
      Module.End F B.Space) v = (t : F) ^ n • v)
    (l : Module.Dual F B.Space) :
    (rootPolynomial B (-typeF4SimpleRootIndex i) l v).coeff n =
      l ((B.action.action (algebraicNElement (typeF4SimpleRootIndex i) 1) :
        Module.End F B.Space) v) := by
  have h := reciprocal_coeff _ _ n n le_rfl (highest_reciprocal B i n v hupper htorus l)
  simpa only [Nat.sub_self, Polynomial.coeff_zero_eq_eval_zero, rootPolynomial_eval,
    root_zero, map_one, Units.val_one, Module.End.one_apply] using h

/-- Local rank-one fixation when only the selected coroot exponent is zero. -/
theorem negative_simple_fixed_of_zero (B : AlgebraicFactor F) (i : Fin 4) (v : B.Space)
    (hupper : ∀ a : F, (B.action.action (algebraicRootElement (typeF4SimpleRootIndex i) a) :
      Module.End F B.Space) v = v)
    (htorus : ∀ t : Fˣ, (B.action.action (algebraicCorootElement (typeF4SimpleRootIndex i) t) :
      Module.End F B.Space) v = v) (t : F) :
    (B.action.action (algebraicRootElement (-typeF4SimpleRootIndex i) t) :
      Module.End F B.Space) v = v := by
  have ht : ∀ t : Fˣ, (B.action.action (algebraicCorootElement (typeF4SimpleRootIndex i) t) :
      Module.End F B.Space) v = (t : F) ^ 0 • v := by simpa using htorus
  apply (Module.finBasis F B.Space).repr.injective
  ext j
  let l := (Module.finBasis F B.Space).coord j
  change l ((B.action.action (algebraicRootElement (-typeF4SimpleRootIndex i) t) :
    Module.End F B.Space) v) = l v
  have hp : rootPolynomial B (-typeF4SimpleRootIndex i) l v = Polynomial.C (l v) := by
    ext k
    cases k with
    | zero => simp [Polynomial.coeff_zero_eq_eval_zero, rootPolynomial_eval, root_zero]
    | succ k =>
      rw [negative_simple_rootPolynomial_coeff_eq_zero B i 0 v hupper ht l _ (by omega)]
      simp
  rw [← rootPolynomial_eval, hp, Polynomial.eval_C]

/-- At coroot weight zero the simple Weyl representative fixes the highest vector. -/
theorem simple_weyl_fixed_of_zero (B : AlgebraicFactor F) (i : Fin 4) (v : B.Space)
    (hupper : ∀ a : F, (B.action.action (algebraicRootElement (typeF4SimpleRootIndex i) a) :
      Module.End F B.Space) v = v)
    (htorus : ∀ t : Fˣ, (B.action.action (algebraicCorootElement (typeF4SimpleRootIndex i) t) :
      Module.End F B.Space) v = v) :
    (B.action.action (algebraicNElement (typeF4SimpleRootIndex i) 1) :
      Module.End F B.Space) v = v := by
  simp only [algebraicNElement, map_mul, Units.val_mul, Module.End.mul_apply,
    hupper, negative_simple_fixed_of_zero B i v hupper htorus]

/-- At coroot weight one the Weyl translate is exactly the first lowering coefficient. -/
theorem simple_weyl_eq_coeff_one (B : AlgebraicFactor F) (p : RootExpansion B.action)
    (i : Fin 4) (v : B.Space)
    (hupper : ∀ a : F, (B.action.action (algebraicRootElement (typeF4SimpleRootIndex i) a) :
      Module.End F B.Space) v = v)
    (htorus : ∀ t : Fˣ, (B.action.action (algebraicCorootElement (typeF4SimpleRootIndex i) t) :
      Module.End F B.Space) v = (t : F) • v) :
    (B.action.action (algebraicNElement (typeF4SimpleRootIndex i) 1) :
      Module.End F B.Space) v = p.coeff (-typeF4SimpleRootIndex i) 1 v := by
  rw [p.coeff_one_eq_rootOperator]
  apply (Module.finBasis F B.Space).repr.injective
  ext j
  let l := (Module.finBasis F B.Space).coord j
  change l ((B.action.action (algebraicNElement (typeF4SimpleRootIndex i) 1) :
    Module.End F B.Space) v) = l (rootOperator B (-typeF4SimpleRootIndex i) v)
  rw [dual_rootOperator]
  exact (negative_simple_rootPolynomial_top_coeff B i 1 v hupper
    (by simpa only [pow_one] using htorus) l).symm

/-- At coroot weight one the whole negative simple orbit is affine in its first coefficient. -/
theorem negative_simple_action_of_one (B : AlgebraicFactor F) (p : RootExpansion B.action)
    (i : Fin 4) (v : B.Space)
    (hupper : ∀ a : F, (B.action.action (algebraicRootElement (typeF4SimpleRootIndex i) a) :
      Module.End F B.Space) v = v)
    (htorus : ∀ t : Fˣ, (B.action.action (algebraicCorootElement (typeF4SimpleRootIndex i) t) :
      Module.End F B.Space) v = (t : F) • v) (t : F) :
    (B.action.action (algebraicRootElement (-typeF4SimpleRootIndex i) t) :
      Module.End F B.Space) v = v + t • p.coeff (-typeF4SimpleRootIndex i) 1 v := by
  have ht : ∀ t : Fˣ, (B.action.action (algebraicCorootElement (typeF4SimpleRootIndex i) t) :
      Module.End F B.Space) v = (t : F) ^ 1 • v := by simpa only [pow_one] using htorus
  rw [p.coeff_one_eq_rootOperator]
  apply (Module.finBasis F B.Space).repr.injective
  ext j
  let l := (Module.finBasis F B.Space).coord j
  change l ((B.action.action (algebraicRootElement (-typeF4SimpleRootIndex i) t) :
    Module.End F B.Space) v) = l (v + t • rootOperator B (-typeF4SimpleRootIndex i) v)
  let q := rootPolynomial B (-typeF4SimpleRootIndex i) l v
  have hq : q = Polynomial.C (l v) + Polynomial.C (q.coeff 1) * Polynomial.X := by
    ext k
    match k with
    | 0 => simp [q, Polynomial.coeff_zero_eq_eval_zero, rootPolynomial_eval, root_zero]
    | 1 => simp
    | k + 2 =>
      rw [show q.coeff (k + 2) = 0 from
        negative_simple_rootPolynomial_coeff_eq_zero B i 1 v hupper ht l _ (by omega)]
      simp
  rw [← rootPolynomial_eval]
  change q.eval t = _
  rw [hq]
  simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_X, map_add, map_smul, smul_eq_mul, dual_rootOperator]
  exact congrArg (l v + ·) (mul_comm _ _)

end
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity
