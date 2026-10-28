module

public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.Actions
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# Two-power actors on the symplectic split torus

Let γ act on Fˣ × Fˣ by (x,y) ↦ (y,x²), where |F| = 2^n and n > 1.
Every nonidentity two-power actor in ⟨γ⟩ which fixes the three-residual
forces n = 2 or 6. In either of those degrees its displacement image has
order greater than three.

For odd n, the whole torus has order prime to three. For n = 2m, γ^n is
the coordinatewise half-degree Frobenius. The finite-field power identity
shows its square is one; its displacement order (2^m+1)² shows it is
nonidentity. Uniqueness of the involution in a cyclic group identifies it
with the half-order power of any nonidentity two-power actor. Telescoping
displacements then embeds its image in the original actor's image. Thus
the argument also covers graph actors of order four and higher, and the
field of order four is not a small-displacement exception.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954 (PDF p.971).
These are statements about the actual torus action, for use in the separate
matrix-group commutator and automorphism reductions.
-/

open Subgroup

namespace Theory.SpecificGroups.SymplecticFour.EvenBorelTorus

variable {F : Type*} [Field F]

private theorem field_pow (σ : F ≃+* F) (k : ℕ) :
    fieldTorus (σ ^ k) = fieldTorus σ ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, pow_succ, ← ih]
    ext x <;> rfl

private theorem displacement_pow_le (τ : MulAut (Fˣ × Fˣ)) (k : ℕ) :
    (torusDisplacement (τ ^ k)).range ≤ (torusDisplacement τ).range := by
  rintro _ ⟨x, rfl⟩
  induction k with
  | zero => simp [torusDisplacement]
  | succ k ih =>
    have hmem := (torusDisplacement τ).range.mul_mem
      (show torusDisplacement τ ((τ ^ k) x) ∈ (torusDisplacement τ).range from ⟨_, rfl⟩) ih
    convert hmem using 1
    simp [torusDisplacement, pow_succ', MulAut.mul_apply, mul_assoc]

variable [Finite F] [CharP F 2]

private theorem frobenius_pow_apply (k : ℕ) (x : F) :
    (frobeniusEquiv F 2 ^ k) x = x ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', RingAut.mul_apply, ih]
    change (x ^ (2 ^ k)) ^ 2 = _
    rw [← pow_mul, pow_succ]

private theorem graph_even_pow (k : ℕ) :
    graphTorus (F := F) ^ (2 * k) = fieldTorus (frobeniusEquiv F 2 ^ k) := by
  rw [pow_mul, graphTorus_square, field_pow]

private theorem graph_half_order {m : ℕ} (hm : 0 < m)
    (hF : Nat.card F = 2 ^ (2 * m)) :
    orderOf (graphTorus (F := F) ^ (2 * m)) = 2 := by
  have hs : (graphTorus (F := F) ^ (2 * m)) ^ 2 = 1 := by
    rw [graph_even_pow, ← field_pow, ← pow_mul, Nat.mul_comm m 2]
    have hf : frobeniusEquiv F 2 ^ (2 * m) = 1 := by
      ext x
      rw [frobenius_pow_apply, ← hF]
      let _ := Fintype.ofFinite F
      simpa [Nat.card_eq_fintype_card] using FiniteField.pow_card x
    rw [hf]
    rfl
  apply orderOf_eq_prime hs
  intro he
  have hb := field_displacement_gt_three (frobeniusEquiv F 2 ^ m) hm hF
    (frobenius_pow_apply m)
  rw [← graph_even_pow, he] at hb
  have hbot : (torusDisplacement (1 : MulAut (Fˣ × Fˣ))).range = ⊥ := by
    rw [MonoidHom.range_eq_bot_iff]
    apply MonoidHom.ext
    intro x
    change x * x⁻¹ = 1
    exact mul_inv_cancel x
  rw [hbot, Subgroup.card_bot] at hb
  omega

private theorem field_involution_power {m : ℕ} (hm : 0 < m)
    (hF : Nat.card F = 2 ^ (2 * m))
    (τ : MulAut (Fˣ × Fˣ)) (hτ : τ ∈ zpowers (graphTorus (F := F)))
    (hp : IsPGroup 2 (zpowers τ)) (hne : τ ≠ 1) :
    ∃ k : ℕ, τ ^ k = graphTorus (F := F) ^ (2 * m) := by
  have hd : 2 ∣ orderOf τ := by
    have ht : (⟨τ, mem_zpowers τ⟩ : zpowers τ) ≠ 1 :=
      fun h => hne (congrArg Subtype.val h)
    simpa only [← orderOf_coe] using hp.dvd_orderOf ht
  refine ⟨orderOf τ / 2, ?_⟩
  have ho : orderOf (τ ^ (orderOf τ / 2)) = 2 :=
    orderOf_pow_orderOf_div (orderOf_pos τ).ne' hd
  exact congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two
    (x := (⟨τ ^ (orderOf τ / 2), (zpowers _).pow_mem hτ _⟩ : zpowers (graphTorus (F := F))))
    (y := ⟨graphTorus (F := F) ^ (2 * m), (zpowers _).pow_mem (mem_zpowers _) _⟩)
    (by simpa only [← orderOf_coe] using ho)
    (by simpa only [← orderOf_coe] using graph_half_order hm hF))

/-- A nonidentity two-power actor fixing the three-residual forces degree two or six. -/
public theorem two_power_fixed_residual_degree {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2 ^ n)
    (τ : MulAut (Fˣ × Fˣ)) (hτ : τ ∈ zpowers (graphTorus (F := F)))
    (hp : IsPGroup 2 (zpowers τ)) (hne : τ ≠ 1)
    (hfix : ∀ x ∈ pResidual 3 (Fˣ × Fˣ), τ x = x) : n = 2 ∨ n = 6 := by
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨m, hm⟩ := he
    have hn' : n = 2 * m := by omega
    rw [hn'] at hF ⊢
    have hmpos : 0 < m := by omega
    obtain ⟨k, hk⟩ := field_involution_power hmpos hF τ hτ hp hne
    apply field_fixed_residual_degree (frobeniusEquiv F 2 ^ m) hmpos hF
      (frobenius_pow_apply m)
    intro x hx
    rw [← graph_even_pow, ← hk]
    clear hk
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, hfix x hx]
  · exfalso
    apply hne
    apply MulEquiv.ext
    intro x
    apply hfix x
    apply mem_pResidual_of_orderOf_coprime
    apply Nat.Coprime.of_dvd_right (orderOf_dvd_natCard x)
    rw [Nat.card_prod, Nat.card_units, hF]
    exact (Nat.BinaryTorusParity.coprime_three_sub_one ho).mul_right
      (Nat.BinaryTorusParity.coprime_three_sub_one ho)

private theorem even_displacement_gt_three {m : ℕ} (hm : 0 < m)
    (hF : Nat.card F = 2 ^ (2 * m))
    (τ : MulAut (Fˣ × Fˣ)) (hτ : τ ∈ zpowers (graphTorus (F := F)))
    (hp : IsPGroup 2 (zpowers τ)) (hne : τ ≠ 1) :
    3 < Nat.card (torusDisplacement τ).range := by
  obtain ⟨k, hk⟩ := field_involution_power hm hF τ hτ hp hne
  have hle := card_le_of_le (displacement_pow_le τ k)
  rw [hk, graph_even_pow] at hle
  exact lt_of_lt_of_le
    (field_displacement_gt_three (frobeniusEquiv F 2 ^ m) hm hF
      (frobenius_pow_apply m)) hle

/-- In degrees two and six every nonidentity two-power graph-generated actor
has displacement image larger than three, including actors of order four. -/
public theorem two_power_displacement_gt_three {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (τ : MulAut (Fˣ × Fˣ)) (hτ : τ ∈ zpowers (graphTorus (F := F)))
    (hp : IsPGroup 2 (zpowers τ)) (hne : τ ≠ 1) (hn : n = 2 ∨ n = 6) :
    3 < Nat.card (torusDisplacement τ).range := by
  rcases hn with rfl | rfl
  · exact even_displacement_gt_three (m := 1) (by decide) hF τ hτ hp hne
  · exact even_displacement_gt_three (m := 3) (by decide) hF τ hτ hp hne

end Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
