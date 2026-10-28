module
public import Theory.SpecificGroups.ExoticTwoGroup.QuarterTurnAction
public import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

/-!
# The split inner extension obstructs a quarter-turn

Commuting involutory lifts of the two inner actions force the commutators of
an inversion obtained by squaring a quarter-turn into the omega four.
The sixteen action words then imply that every square in the four-centralizer
lies in that four. This is the split obstruction of MacWilliams, Trans. AMS
150 (1970), §4 (xx)–(xxii), p.399, without choosing an order-three automorphism.
-/

open C4SquareExtension Subgroup ExoticTwoGroup.ActionModel
namespace ExoticTwoGroup.QuarterTurn

private theorem involution_defect {P : Type*} [Group P]
    (s r t d : P) (hs : s ^ 2 = 1) (hr : r ^ 2 = 1)
    (hd : t * s * t⁻¹ = d * r) : r * d * r⁻¹ = d⁻¹ := by
  have hsq : (d * r) ^ 2 = 1 := by
    rw [← hd]
    calc
      _ = t * s ^ 2 * t⁻¹ := by simp only [pow_two]; group
      _ = 1 := by rw [hs]; group
  apply mul_left_cancel (a := d)
  calc
    d * (r * d * r⁻¹) = (d * r) ^ 2 * (r ^ 2)⁻¹ := by simp only [pow_two]; group
    _ = d * d⁻¹ := by rw [hsq, hr]; simp

/-- In a split inner extension, the square of a quarter-turn commutes with
both inner lifts modulo the square-trivial part of the base. -/
public theorem square_commutators
    {P : Type*} [Group P] (ι : Model →* P) (hi : Function.Injective ι)
    (F : P →* MulAut Model) (hker : F.ker = ι.range)
    (hconj : ∀ s x, s * ι x * s⁻¹ = ι (F s x))
    (g h t : P) (hg : F g = inner₁) (hh : F h = inner₂) (ht : F t = rotation)
    (hg2 : g ^ 2 = 1) (hh2 : h ^ 2 = 1) (hgh : Commute g h) :
    ∃ d e : Model, d ^ 2 = 1 ∧ e ^ 2 = 1 ∧
      t ^ 2 * g * (t ^ 2)⁻¹ * g⁻¹ = ι d ∧
      t ^ 2 * h * (t ^ 2)⁻¹ * h⁻¹ = ι e := by
  have hd : t * g * t⁻¹ * h⁻¹ ∈ ι.range := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
      ht, hg, hh, rotation_inner₁, mul_inv_cancel]
  have he : t * h * t⁻¹ * g⁻¹ ∈ ι.range := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
      ht, hg, hh, rotation_inner₂, mul_inv_cancel]
  obtain ⟨d, hd⟩ := hd
  obtain ⟨e, he⟩ := he
  have htg : t * g * t⁻¹ = ι d * h := (mul_inv_eq_iff_eq_mul.mp hd.symm)
  have hth : t * h * t⁻¹ = ι e * g := (mul_inv_eq_iff_eq_mul.mp he.symm)
  have hd' : inner₂ d = d⁻¹ := hi (by
    rw [← hh, ← hconj, map_inv]
    exact involution_defect g h t (ι d) hg2 hh2 htg)
  have he' : inner₁ e = e⁻¹ := hi (by
    rw [← hg, ← hconj, map_inv]
    exact involution_defect h g t (ι e) hh2 hg2 hth)
  have hcomm : d * inner₂ e = e * inner₁ d := by
    apply hi
    apply mul_right_cancel (b := h * g)
    calc
      ι (d * inner₂ e) * (h * g) = (ι d * h) * (ι e * g) := by
        rw [map_mul, ← hh, ← hconj]; group
      _ = (ι e * g) * (ι d * h) := by
        rw [← htg, ← hth]
        exact (hgh.map (MulAut.conj t).toMonoidHom).eq
      _ = ι (e * inner₁ d) * (h * g) := by
        rw [hgh.symm.eq, map_mul, ← hg, ← hconj]; group
  have hs := split_defect_squares d e hd' he' hcomm
  refine ⟨rotation d * e, rotation e * d, hs.1, hs.2, ?_, ?_⟩
  · calc
      _ = t * (t * g * t⁻¹) * t⁻¹ * g⁻¹ := by simp only [pow_two]; group
      _ = (t * ι d * t⁻¹) * (t * h * t⁻¹) * g⁻¹ := by rw [htg]; group
      _ = ι (rotation d * e) := by rw [hconj, ht, hth, map_mul]; group
  · calc
      _ = t * (t * h * t⁻¹) * t⁻¹ * h⁻¹ := by simp only [pow_two]; group
      _ = (t * ι e * t⁻¹) * (t * g * t⁻¹) * h⁻¹ := by rw [hth]; group
      _ = ι (rotation e * d) := by rw [hconj, ht, htg, map_mul]; group


/-- Squares in the four-centralizer lie in the four in a split quarter-turn
extension. Only the action, its kernel, and the split inner lifts are used. -/
public theorem square_mem_of_fix_squares
    {P : Type*} [Group P] (W : Subgroup P) [W.Normal]
    (ι : Model →* P) (hi : Function.Injective ι)
    (F : P →* MulAut Model) (hker : F.ker = ι.range)
    (hconj : ∀ s x, s * ι x * s⁻¹ = ι (F s x))
    (hW : ∀ d : Model, d ^ 2 = 1 → ι d ∈ W)
    (hA : Nat.card F.range = 16)
    (g h t : P) (hg : F g = inner₁) (hh : F h = inner₂) (ht : F t = rotation)
    (hg2 : g ^ 2 = 1) (hh2 : h ^ 2 = 1) (hgh : Commute g h)
    (x : P) (hxu : F x (u ^ 2) = u ^ 2) (hxv : F x (v ^ 2) = v ^ 2) :
    x ^ 2 ∈ W := by
  let z := t ^ 2
  have hz : F z = inversion := by dsimp [z]; rw [map_pow, ht, rotation_square]
  have hz2 : z ^ 2 ∈ W := by
    have hzk : z ^ 2 ∈ ι.range := by
      rw [← hker, MonoidHom.mem_ker]
      dsimp [z]
      rw [← pow_mul, map_pow, ht]
      exact rotation_four
    obtain ⟨d, hd⟩ := hzk
    have hinv : ι d⁻¹ = ι d := by
      calc
        ι d⁻¹ = ι (F z d) := by
          rw [hz]
          rw [inversion_apply]
        _ = z * ι d * z⁻¹ := (hconj z d).symm
        _ = ι d := by rw [hd]; simp only [pow_two]; group
    have hd2 : d ^ 2 = 1 := by
      calc
        d ^ 2 = d⁻¹ * d := by rw [pow_two, hi hinv]
        _ = 1 := inv_mul_cancel d
    exact hd ▸ hW d hd2
  let q := QuotientGroup.mk' W
  have qsquare {y : P} (hy : y ^ 2 ∈ W) : q y ^ 2 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (N := W) (x := y ^ 2)).mpr hy
  have qcomm {a b : P} (hab : a * b * a⁻¹ * b⁻¹ ∈ W) :
      Commute (q a) (q b) := by
    have he : q (a * b * a⁻¹ * b⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff (N := W) (x := a * b * a⁻¹ * b⁻¹)).mpr hab
    simp only [map_mul, map_inv] at he
    exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_iff_eq_mul.mp he)).trans (by simp)
  have qbase (d : Model) : q (ι d) ^ 2 = 1 := by
    apply qsquare
    rw [← map_pow]
    exact hW (d ^ 2) ((by decide +kernel : ∀ d : Model, (d ^ 2) ^ 2 = 1) d)
  have qcentral (a : P) (ha : F a = inner₁ ∨ F a = inner₂ ∨ F a = inversion)
      (d : Model) : Commute (q a) (q (ι d)) := by
    apply qcomm
    rw [hconj, ← map_inv, ← map_mul]
    apply hW
    rcases ha with ha | ha | ha <;> rw [ha]
    · exact (inner_defect_squares d).1
    · exact (inner_defect_squares d).2
    · rw [inversion_apply]
      exact (by decide : ∀ d : Model, (d⁻¹ * d⁻¹) ^ 2 = 1) d
  obtain ⟨d₁, d₂, hd₁, hd₂, he₁, he₂⟩ :=
    square_commutators ι hi F hker hconj g h t hg hh ht hg2 hh2 hgh
  have hzg : Commute (q z) (q g) := qcomm (he₁.symm ▸ hW d₁ hd₁)
  have hzh : Commute (q z) (q h) := qcomm (he₂.symm ▸ hW d₂ hd₂)
  obtain ⟨i, j, k, he⟩ := exists_even_word F.range hA
    ⟨g, hg⟩ ⟨h, hh⟩ ⟨t, ht⟩ ⟨F x, ⟨x, rfl⟩⟩ hxu hxv
  let w := g ^ i.val * h ^ j.val * z ^ k.val
  have hw : F w = F x := by
    dsimp [w, z]
    rw [map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, hg, hh, ht]
    exact he.symm
  have hxk : x * w⁻¹ ∈ ι.range := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hw, mul_inv_cancel]
  obtain ⟨d, hd⟩ := hxk
  have hx : x = ι d * w := by rw [hd]; group
  have hgq : q g ^ 2 = 1 := by rw [← map_pow, hg2, map_one]
  have hhq : q h ^ 2 = 1 := by rw [← map_pow, hh2, map_one]
  have hzq : q z ^ 2 = 1 := qsquare hz2
  have hp (a : P) (ha : q a ^ 2 = 1) (n : ℕ) : (q a ^ n) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul, ha, one_pow]
  have hwq : q w ^ 2 = 1 := by
    dsimp [w]
    simp only [map_mul, map_pow]
    rw [(((hzg.symm.pow_pow i.val k.val).mul_left
      (hzh.symm.pow_pow j.val k.val))).mul_pow,
      ((hgh.map q).pow_pow i.val j.val).mul_pow,
      hp g hgq, hp h hhq, hp z hzq, one_mul, one_mul]
  have hdc : Commute (q (ι d)) (q w) := by
    dsimp [w]
    simp only [map_mul, map_pow]
    exact (((qcentral g (Or.inl hg) d).symm.pow_right i.val).mul_right
      ((qcentral h (Or.inr (Or.inl hh)) d).symm.pow_right j.val)).mul_right
      ((qcentral z (Or.inr (Or.inr hz)) d).symm.pow_right k.val)
  apply (QuotientGroup.eq_one_iff (N := W) (x := x ^ 2)).mp
  change q (x ^ 2) = 1
  rw [hx, map_pow, map_mul, hdc.mul_pow, qbase, hwq, one_mul]

end ExoticTwoGroup.QuarterTurn
