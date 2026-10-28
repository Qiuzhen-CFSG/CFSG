module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.EndNode.Multiplicity.WeightShift
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Polynomial.Taylor

/-!
# Highest-string coefficients for the actual F4 root action

For a vector fixed by a positive simple root group and of coroot exponent
`n > 0`, raising after lowering is multiplication by `n`. In particular this
supplies the exponents one and two needed by the short A2 multiplicity proof.

Write `w = n_i(1) v`. With the convention `h_i(t) = n_i(t) n_i(1)⁻¹`, the
checked normalizer relation gives `w` exponent `-n`. The Bruhat word then
relates the scalar orbit polynomials by `p(t) = t^n q(t⁻¹)` off zero.
Polynomial reflection identifies `p_k = q_(n-k)`. The additive root law and
Taylor expansion identify the orbit polynomial for a dual coordinate composed
with the first root operator with the formal derivative of that coordinate's
orbit polynomial. Thus the raising image of `p_1` is `n q_n = n v`.

This coefficient argument works in characteristic two without division by
factorials or a characteristic-zero Lie differential. The Bruhat calculation
adapts the private zero-exponent argument in `ZeroAndMiddle/Zero.lean`.
Source: GLS3, Sections 1.12 and 1.14; the multiplicity application contributes
to the Ree bound used in Aschbacher--Smith, Quasithin, printed p.356/PDF p.367.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.EndNode.Multiplicity
open ZeroAndMiddle
noncomputable section
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private theorem root_add (r : F4Chevalley.Root) (s t : F) :
    algebraicRootElement r (s + t) = algebraicRootElement r s * algebraicRootElement r t := by
  apply carrierMatrix_injective
  simp only [map_mul, carrierMatrix_root, F4Chevalley.rootCurve_add]

private theorem rootPolynomial_dual_operator (B : AlgebraicFactor F)
    (r : F4Chevalley.Root) (l : Module.Dual F B.Space) (v : B.Space) :
    rootPolynomial B r (l.comp (rootOperator B r)) v =
      (rootPolynomial B r l v).derivative := by
  apply Polynomial.funext
  intro t
  have hp : rootPolynomial B r l
      ((B.action.action (algebraicRootElement r t) : Module.End F B.Space) v) =
      Polynomial.taylor t (rootPolynomial B r l v) := by
    apply Polynomial.funext
    intro s
    simp only [Polynomial.taylor_apply, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C, rootPolynomial_eval,
      root_add, map_mul, Units.val_mul, Module.End.mul_apply]
  rw [rootPolynomial_eval, LinearMap.comp_apply, dual_rootOperator, hp,
    Polynomial.taylor_coeff_one]

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

/-- The rank-one highest-string coefficient, for any positive integral exponent. -/
theorem raising_lowering_highest (B : AlgebraicFactor F) (i : Fin 4) (n : ℕ) (hn : 0 < n)
    (v : B.Space)
    (hupper : ∀ a : F, (B.action.action (algebraicRootElement (typeF4SimpleRootIndex i) a) :
      Module.End F B.Space) v = v)
    (htorus : ∀ t : Fˣ, (B.action.action (algebraicCorootElement (typeF4SimpleRootIndex i) t) :
      Module.End F B.Space) v = (t : F) ^ n • v) :
    raising B i (lowering B i v) = (n : F) • v := by
  let w := (B.action.action (algebraicNElement (typeF4SimpleRootIndex i) 1) :
    Module.End F B.Space) v
  have hc (l : Module.Dual F B.Space) (k : ℕ) (hk : k ≤ n) :
      (rootPolynomial B (-typeF4SimpleRootIndex i) l v).coeff k =
      (rootPolynomial B (typeF4SimpleRootIndex i) l w).coeff (n - k) :=
    reciprocal_coeff _ _ n k hk (highest_reciprocal B i n v hupper htorus l)
  apply (Module.finBasis F B.Space).repr.injective
  ext j
  let l := (Module.finBasis F B.Space).coord j
  change l (raising B i (lowering B i v)) = l ((n : F) • v)
  calc
    l (raising B i (lowering B i v)) =
        (rootPolynomial B (-typeF4SimpleRootIndex i) (l.comp (raising B i)) v).coeff 1 :=
      dual_rootOperator B _ (l.comp (raising B i)) v
    _ = (rootPolynomial B (typeF4SimpleRootIndex i) (l.comp (raising B i)) w).coeff (n - 1) :=
      hc _ 1 hn
    _ = (rootPolynomial B (typeF4SimpleRootIndex i) l w).derivative.coeff (n - 1) := by
      rw [raising, rootPolynomial_dual_operator]
    _ = (rootPolynomial B (typeF4SimpleRootIndex i) l w).coeff n * (n : F) := by
      rw [Polynomial.coeff_derivative, Nat.sub_add_cancel hn]
      congr 1
      simpa only [Nat.cast_add, Nat.cast_one] using
        congrArg (fun k : ℕ => (k : F)) (Nat.sub_add_cancel hn : n - 1 + 1 = n)
    _ = l v * (n : F) := by
      have hz := hc l 0 (Nat.zero_le _)
      simp only [Nat.sub_zero, Polynomial.coeff_zero_eq_eval_zero,
        rootPolynomial_eval, root_zero, map_one, Units.val_one, Module.End.one_apply] at hz
      rw [← hz]
    _ = l ((n : F) • v) := by rw [map_smul, smul_eq_mul, mul_comm]

/-- The rank-one coefficient input required by the short A2 multiplicity proof. -/
theorem rankOneHighestCoefficient (B : AlgebraicFactor F) : RankOneHighestCoefficient B := by
  intro i _ n hn v hupper htorus
  exact raising_lowering_highest B i n (by rcases hn with rfl | rfl <;> decide) v hupper htorus

end
end ReeF4.BinaryDegree.ExceptionalTensor.EndNode.Multiplicity
