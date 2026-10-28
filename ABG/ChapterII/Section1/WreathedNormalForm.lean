module
public import ABG.ChapterII.Section1.WreathedPresentation

/-!
# Unique coordinates in a wreathed presentation

For the chosen ABG wreathed presentation, every element has a unique expression
`s^i * t^j * z^b`, with `i,j < 2^n` and `b < 2`. This supplies the coordinate
comparisons used in Chapter II §1 Lemma 2 (article pp.9–10).

Closure induction first gives integer exponents: the commuting generators move
to the left and conjugation by the involution swaps them. The defining power
relations reduce the exponents to the stated bounds. The prescribed cardinality
`2^(2*n+1)` makes the resulting surjection a bijection. In particular, the
modular equality criterion uses the presentation's cardinality hypothesis,
not merely its generator relations.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

private theorem z_inv' : P.z⁻¹ = P.z := by
  apply inv_eq_of_mul_eq_one_left
  simpa [pow_two] using P.z_sq

private theorem swap_s' : SemiconjBy P.z P.s P.t := by
  have h := P.conj_s
  rw [P.z_inv'] at h
  have hh := congrArg (· * P.z) h
  simpa [SemiconjBy, mul_assoc, ← pow_two, P.z_sq] using hh

private theorem swap_t' : SemiconjBy P.z P.t P.s := by
  have h := P.conj_t
  rw [P.z_inv'] at h
  have hh := congrArg (· * P.z) h
  simpa [SemiconjBy, mul_assoc, ← pow_two, P.z_sq] using hh

private theorem integer_normal_form (g : S) :
    ∃ i j k : ℤ, P.s ^ i * P.t ^ j * P.z ^ k = g := by
  have hc : Commute P.s P.t := P.commute
  have hmul (a : S) (ha : a ∈ ({P.s, P.t, P.z} : Set S)) (g : S)
      (hg : ∃ i j k : ℤ, P.s ^ i * P.t ^ j * P.z ^ k = g) :
      ∃ i j k : ℤ, P.s ^ i * P.t ^ j * P.z ^ k = a * g := by
    rcases hg with ⟨i, j, k, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · exact ⟨1 + i, j, k, by simp [zpow_add, mul_assoc]⟩
    · refine ⟨i, 1 + j, k, ?_⟩
      simp only [zpow_add, zpow_one]
      rw [← mul_assoc (P.s ^ i), (hc.zpow_left i).eq]
      simp only [mul_assoc]
    · refine ⟨j, i, 1 + k, ?_⟩
      calc
        _ = P.t ^ i * P.s ^ j * (P.z * P.z ^ k) := by
          rw [(hc.zpow_zpow j i).eq]; simp [zpow_add]
        _ = P.z * (P.s ^ i * P.t ^ j * P.z ^ k) := by
          simp only [← mul_assoc]
          rw [mul_assoc (P.t ^ i) (P.s ^ j) P.z, ← (P.swap_t'.zpow_right j).eq,
            ← mul_assoc, ← (P.swap_s'.zpow_right i).eq]
  have hinv (a : S) (ha : a ∈ ({P.s, P.t, P.z} : Set S)) (g : S)
      (hg : ∃ i j k : ℤ, P.s ^ i * P.t ^ j * P.z ^ k = g) :
      ∃ i j k : ℤ, P.s ^ i * P.t ^ j * P.z ^ k = a⁻¹ * g := by
    rcases hg with ⟨i, j, k, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · exact ⟨-1 + i, j, k, by simp [zpow_add, mul_assoc]⟩
    · refine ⟨i, -1 + j, k, ?_⟩
      simp only [zpow_add, zpow_neg_one]
      rw [← mul_assoc (P.s ^ i), ((hc.zpow_left i).inv_right).eq]
      simp only [mul_assoc]
    · rw [P.z_inv']
      exact hmul P.z (by simp) _ ⟨i, j, k, rfl⟩
  exact Subgroup.closure_induction_left (p := fun g _ =>
    ∃ i j k : ℤ, P.s ^ i * P.t ^ j * P.z ^ k = g)
    ⟨0, 0, 0, by simp⟩ (fun a ha g _ hg => hmul a ha g hg)
    (fun a ha g _ hg => hinv a ha g hg)
    (show g ∈ Subgroup.closure ({P.s, P.t, P.z} : Set S) by rw [P.generate]; trivial)


@[expose] public def normalForm (v : Fin (2 ^ n) × Fin (2 ^ n) × Fin 2) : S :=
  P.s ^ v.1.val * P.t ^ v.2.1.val * P.z ^ v.2.2.val

private theorem bounded_power {a : S} {m : ℕ} (hm : 0 < m) (ha : a ^ m = 1)
    (i : ℤ) : ∃ j : Fin m, a ^ j.val = a ^ i := by
  refine ⟨⟨(i % (m : ℤ)).toNat, ?_⟩, ?_⟩
  · exact Int.toNat_lt (Int.emod_nonneg i (by omega)) |>.mpr (by
      exact_mod_cast Int.emod_lt_of_pos i (by omega : (0 : ℤ) < m))
  · have hi : ((i % (m : ℤ)).toNat : ℤ) = i % (m : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg i (by omega))
    rw [← zpow_natCast, hi, ← zpow_eq_zpow_emod' i ha]

public theorem normal_form_surjective : Function.Surjective P.normalForm := by
  intro g
  rcases P.integer_normal_form g with ⟨i, j, k, h⟩
  rcases bounded_power (by positivity) P.s_pow i with ⟨a, ha⟩
  rcases bounded_power (by positivity) P.t_pow j with ⟨b, hb⟩
  rcases bounded_power (by omega) P.z_sq k with ⟨c, hc⟩
  exact ⟨(a, b, c), by simpa [normalForm, ha, hb, hc] using h⟩

public theorem normal_form_bijective : Function.Bijective P.normalForm := by
  apply (Nat.bijective_iff_surjective_and_card _).mpr
  refine ⟨P.normal_form_surjective, ?_⟩
  simp only [Nat.card_prod, Nat.card_fin, P.card]
  rw [pow_add, Nat.mul_comm 2 n, pow_mul]
  ring

public theorem normal_form_injective : Function.Injective P.normalForm :=
  P.normal_form_bijective.injective

public theorem exists_normal_form (g : S) :
    ∃ i j : Fin (2 ^ n), ∃ b : Fin 2, P.s ^ i.val * P.t ^ j.val * P.z ^ b.val = g := by
  rcases P.normal_form_surjective g with ⟨⟨i, j, b⟩, h⟩
  exact ⟨i, j, b, h⟩


private def residue (m : ℕ) (hm : 0 < m) (i : ℤ) : Fin m :=
  ⟨(i % (m : ℤ)).toNat, Int.toNat_lt (Int.emod_nonneg i (by omega)) |>.mpr (by
    exact_mod_cast Int.emod_lt_of_pos i (by omega : (0 : ℤ) < m))⟩

private theorem residue_val (m : ℕ) (hm : 0 < m) (i : ℤ) :
    ((residue m hm i).val : ℤ) = i % (m : ℤ) :=
  Int.toNat_of_nonneg (Int.emod_nonneg i (by omega))

private theorem residue_power {a : S} {m : ℕ} (hm : 0 < m) (ha : a ^ m = 1)
    (i : ℤ) : a ^ (residue m hm i).val = a ^ i := by
  rw [← zpow_natCast, residue_val, ← zpow_eq_zpow_emod' i ha]

public theorem normal_form_zpow_eq_iff (i j k i' j' k' : ℤ) :
    P.s ^ i * P.t ^ j * P.z ^ k = P.s ^ i' * P.t ^ j' * P.z ^ k' ↔
      i % (2 ^ n : ℕ) = i' % (2 ^ n : ℕ) ∧
      j % (2 ^ n : ℕ) = j' % (2 ^ n : ℕ) ∧ k % 2 = k' % 2 := by
  let a := residue (2 ^ n) (by positivity)
  let b := residue 2 (by omega)
  have hn (i j k : ℤ) : P.normalForm (a i, a j, b k) =
      P.s ^ i * P.t ^ j * P.z ^ k := by
    simp only [normalForm, a, b, residue_power _ P.s_pow,
      residue_power _ P.t_pow, residue_power _ P.z_sq]
  rw [← hn, ← hn, P.normal_form_injective.eq_iff]
  simp only [Prod.mk.injEq, Fin.ext_iff]
  have he (m : ℕ) (hm : 0 < m) (x y : ℤ) :
      (residue m hm x).val = (residue m hm y).val ↔
        x % (m : ℤ) = y % (m : ℤ) := by
    rw [← Nat.cast_inj (R := ℤ), residue_val, residue_val]
  exact and_congr (he _ _ _ _) (and_congr (he _ _ _ _) (he _ _ _ _))

end ABG.Wreathed.Presentation
