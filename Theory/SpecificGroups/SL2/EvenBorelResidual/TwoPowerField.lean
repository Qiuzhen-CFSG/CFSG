module

public import Theory.FieldTheory.BinaryTorusInvolution
public import Theory.FieldTheory.FiniteAutomorphismOrder

/-!
# Two-power field actors on binary multiplicative tori

A nonidentity automorphism of a field of order `2^n` whose order is a
power of two has a nonidentity involutory power. Finite-field Frobenius
generation identifies that power with the half-degree Frobenius. If the
original automorphism fixes the actual three-residual of the unit group,
so does this power; the quadratic torus calculation forces `n = 2` or `6`.

In degree six the full field automorphism group has order six, so every
two-power actor has square one. A nonidentity such actor is therefore
the cubic Frobenius, whose displacement image has order nine. This last
conclusion needs no residual-fixation hypothesis.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954 (PDF p.971),
the field arithmetic in alternative (ii) and its outer-actor bound.
These are field conclusions; alignment with an actual matrix actor and
the commutator quotient calculation are separate inputs to that source proof.
-/

namespace FiniteField.BinaryTorusTwoPower

private theorem exists_involutory_power {G : Type*} [Monoid G]
    (a : G) (hne : a ≠ 1) {k : ℕ} (hk : a ^ (2 ^ k) = 1) :
    ∃ j : ℕ, a ^ j ≠ 1 ∧ (a ^ j) ^ 2 = 1 := by
  induction k with
  | zero => simp only [pow_zero, pow_one] at hk; exact (hne hk).elim
  | succ k ih =>
    by_cases h : a ^ (2 ^ k) = 1
    · exact ih h
    · refine ⟨2 ^ k, h, ?_⟩
      rw [← pow_mul, ← pow_succ]
      exact hk

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem exists_half_degree (σ : F ≃+* F) {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hne : σ ≠ 1) (hsq : σ ^ 2 = 1) :
    ∃ m : ℕ, n = 2 * m ∧ ∀ x : F, σ x = x ^ (2 ^ m) := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hdegree : Module.finrank (ZMod 2) F = n := by
    apply Nat.pow_right_injective (by decide : 1 < (2 : ℕ))
    exact (FiniteField.pow_finrank_eq_natCard 2 F).trans hF
  let a : F ≃ₐ[ZMod 2] F := AlgEquiv.ofRingEquiv (f := σ) (by
    intro x
    have hh : σ.toRingHom.comp (algebraMap (ZMod 2) F) = algebraMap (ZMod 2) F :=
      RingHom.ext_zmod _ _
    exact DFunLike.congr_fun hh x)
  obtain ⟨⟨i, hi⟩, he⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod 2) F).surjective a
  change FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F ^ i = a at he
  have ha_apply (x : F) : a x = σ x := rfl
  have hi0 : i ≠ 0 := by
    intro h
    apply hne
    ext x
    have hh := DFunLike.congr_fun he x
    simpa only [h, pow_zero, AlgEquiv.one_apply, RingAut.one_apply, ha_apply] using hh.symm
  have ha : a ^ 2 = 1 := by
    ext x
    exact DFunLike.congr_fun hsq x
  have hd : n ∣ 2 * i := by
    rw [← hdegree, ← FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (ZMod 2) F]
    apply orderOf_dvd_of_pow_eq_one
    rw [mul_comm, pow_mul, he]
    exact ha
  have hn : n = 2 * i := by
    rw [hdegree] at hi
    exact (Nat.eq_of_dvd_of_lt_two_mul (by omega) hd (by omega)).symm
  refine ⟨i, hn, ?_⟩
  intro x
  have hh := DFunLike.congr_fun he x
  simpa only [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate,
    ZMod.card, ha_apply] using hh.symm

omit [Finite F] [CharP F 2] in
private theorem fixed_units_pow (σ : F ≃+* F) {u : Fˣ}
    (hu : Units.map σ.toMonoidHom u = u) (j : ℕ) :
    Units.map (σ ^ j).toMonoidHom u = u := by
  apply Units.ext
  change (σ ^ j) (u : F) = u
  have h : σ (u : F) = u := congrArg Units.val hu
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ', RingAut.mul_apply, ih, h]

omit [CharP F 2] in
private theorem sq_eq_one_of_card_two_pow_six (σ : F ≃+* F)
    (hF : Nat.card F = 2 ^ 6) {k : ℕ} (hpow : σ ^ (2 ^ k) = 1) :
    σ ^ 2 = 1 := by
  have hd6 : orderOf σ ∣ 6 := by
    simpa only [FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two hF] using
      orderOf_dvd_natCard σ
  have hd2 := orderOf_dvd_of_pow_eq_one hpow
  have hc : Nat.Coprime (orderOf σ) 3 :=
    ((by decide : Nat.Coprime 2 3).pow_left k).of_dvd_left hd2
  exact orderOf_dvd_iff_pow_eq_one.mp (hc.dvd_of_dvd_mul_right hd6)

/-- Fixing the three-residual forces the two exceptional field degrees,
without assuming that the original two-power actor is involutory. -/
public theorem degree_eq_two_or_six_of_fixed_residual (σ : F ≃+* F) {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2 ^ n) (hne : σ ≠ 1)
    {k : ℕ} (hpow : σ ^ (2 ^ k) = 1)
    (hfix : ∀ u ∈ pResidual 3 Fˣ, Units.map σ.toMonoidHom u = u) :
    n = 2 ∨ n = 6 := by
  obtain ⟨j, hj, hsq⟩ := exists_involutory_power σ hne hpow
  obtain ⟨m, hnm, hact⟩ := exists_half_degree (σ ^ j) hF hj hsq
  have hm : 0 < m := by
    have := hnm ▸ hn
    omega
  have hcard : Nat.card F = 2 ^ (2 * m) := hF.trans (congrArg (2 ^ ·) hnm)
  have hfixj : ∀ u ∈ pResidual 3 Fˣ,
      Units.map (σ ^ j).toMonoidHom u = u :=
    fun u hu => fixed_units_pow σ (hfix u hu) j
  rcases BinaryTorusInvolution.half_degree_of_fixed_residual
    (σ ^ j) hm hcard hact hfixj with h | h <;> omega

/-- In degree six every nonidentity two-power field actor has displacement
image of order nine, independently of residual fixation. -/
public theorem card_displacement_of_card_two_pow_six (σ : F ≃+* F)
    (hF : Nat.card F = 2 ^ 6) (hne : σ ≠ 1)
    {k : ℕ} (hpow : σ ^ (2 ^ k) = 1) :
    Nat.card (BinaryTorusInvolution.displacement σ).range = 9 := by
  obtain ⟨m, hnm, hact⟩ := exists_half_degree σ hF hne
    (sq_eq_one_of_card_two_pow_six σ hF hpow)
  have hm3 : m = 3 := by omega
  subst m
  exact BinaryTorusInvolution.card_displacement σ (by decide : 0 < 3) hF hact

/-- The degree-six torus displacement is larger than three. -/
public theorem displacement_card_gt_three_of_card_two_pow_six (σ : F ≃+* F)
    (hF : Nat.card F = 2 ^ 6) (hne : σ ≠ 1)
    {k : ℕ} (hpow : σ ^ (2 ^ k) = 1) :
    3 < Nat.card (BinaryTorusInvolution.displacement σ).range := by
  rw [card_displacement_of_card_two_pow_six σ hF hne hpow]
  norm_num

end FiniteField.BinaryTorusTwoPower
