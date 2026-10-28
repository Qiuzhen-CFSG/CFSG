module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.GeneralizedRows.PowerData
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Roots compatible with the actual power labels

The primitive roots for orders 10 and 15 are chosen with square and cube
respectively equal to the supplied fifth root. Orders 5 and 19 retain the
supplied roots themselves. These choices preserve the fifth-period and
nineteenth-period orientations of the literal table. The class enumeration
and power cycles ensure that no other root enters a given cyclic restriction.
Source: Janko (1966), ordinary-character calculation; Gorenstein §16.6, p.482.
-/

-- Concurrent expansion of the fifteen literal columns exceeded the 8 GiB
-- compiler guard. Sequential elaboration keeps these bounded checks separate.
set_option Elab.async false

public section
namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.CyclicRestrictions

private theorem primitive_mul {a b : ℂ} {m n : ℕ}
    (ha : IsPrimitiveRoot a m) (hb : IsPrimitiveRoot b n) (h : m.Coprime n) :
    IsPrimitiveRoot (a * b) (m * n) := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  rw [(Commute.all a b).orderOf_mul_eq_mul_orderOf_of_coprime (by
    simpa only [ha.eq_orderOf.symm, hb.eq_orderOf.symm] using h)]
  rw [← ha.eq_orderOf, ← hb.eq_orderOf]

private theorem root_ten (z : ℂ) (hz : IsPrimitiveRoot z 5) :
    ∃ w : ℂ, IsPrimitiveRoot w 10 ∧ w ^ 2 = z := by
  refine ⟨(-1) * z ^ 3, ?_, ?_⟩
  · exact primitive_mul (IsPrimitiveRoot.neg_one 0 (by decide))
      (hz.pow_of_coprime 3 (by decide)) (by decide)
  · calc
      ((-1 : ℂ) * z ^ 3) ^ 2 = z ^ 6 := by ring
      _ = z := by rw [pow_eq_pow_mod _ hz.pow_eq_one]; norm_num

private theorem root_fifteen (z : ℂ) (hz : IsPrimitiveRoot z 5) :
    ∃ w : ℂ, IsPrimitiveRoot w 15 ∧ w ^ 3 = z := by
  let u : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)
  have hu : IsPrimitiveRoot u 3 := Complex.isPrimitiveRoot_exp 3 (by decide)
  refine ⟨u * z ^ 2, primitive_mul hu (hz.pow_of_coprime 2 (by decide)) (by decide), ?_⟩
  rw [mul_pow, hu.pow_eq_one, one_mul, ← pow_mul]
  rw [pow_eq_pow_mod _ hz.pow_eq_one]
  norm_num

theorem compatible_root (z5 z19 : ℂ) (h5 : IsPrimitiveRoot z5 5)
    (h19 : IsPrimitiveRoot z19 19) (j : Fin 15) :
    ∃ w : ℂ, IsPrimitiveRoot w (classOrder j) ∧
      (5 ∣ classOrder j → w ^ (classOrder j / 5) = z5) ∧
      (19 ∣ classOrder j → w = z19) := by
  obtain ⟨w10, h10, he10⟩ := root_ten z5 h5
  obtain ⟨w15, h15, he15⟩ := root_fifteen z5 h5
  fin_cases j
  all_goals norm_num only [classOrder, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons]
  all_goals first
    | exact ⟨z5, h5, by norm_num, by norm_num⟩
    | exact ⟨z19, h19, by norm_num, by simp⟩
    | exact ⟨w10, h10, by simpa using he10, by norm_num⟩
    | exact ⟨w15, h15, by simpa using he15, by norm_num⟩
    | (refine ⟨_, Complex.isPrimitiveRoot_exp _ (by decide), ?_, ?_⟩ <;> norm_num)

private theorem value_congr_0 (z5 z19 w5 w19 : ℂ) (i : Fin 15)
    (_h5 : 5 ∣ classOrder 0 → z5 = w5) (_h19 : 19 ∣ classOrder 0 → z19 = w19) :
    ordinaryValue z5 z19 i 0 = ordinaryValue w5 w19 i 0 := by
  fin_cases i <;> simp [ordinaryValue]

private theorem value_congr_1 (z5 z19 w5 w19 : ℂ) (i : Fin 15)
    (_h5 : 5 ∣ classOrder 1 → z5 = w5) (_h19 : 19 ∣ classOrder 1 → z19 = w19) :
    ordinaryValue z5 z19 i 1 = ordinaryValue w5 w19 i 1 := by
  fin_cases i <;> simp [ordinaryValue]

private theorem value_congr_2 (z5 z19 w5 w19 : ℂ) (i : Fin 15)
    (_h5 : 5 ∣ classOrder 2 → z5 = w5) (_h19 : 19 ∣ classOrder 2 → z19 = w19) :
    ordinaryValue z5 z19 i 2 = ordinaryValue w5 w19 i 2 := by
  fin_cases i <;> simp [ordinaryValue]

private theorem value_congr_3 (z5 z19 w5 w19 : ℂ) (i : Fin 15)
    (h5 : 5 ∣ classOrder 3 → z5 = w5) (_h19 : 19 ∣ classOrder 3 → z19 = w19) :
    ordinaryValue z5 z19 i 3 = ordinaryValue w5 w19 i 3 := by
  have he := h5 (by decide)
  subst w5
  fin_cases i <;> simp [ordinaryValue]

private theorem value_congr_4 (z5 z19 w5 w19 : ℂ) (i : Fin 15)
    (h5 : 5 ∣ classOrder 4 → z5 = w5) (_h19 : 19 ∣ classOrder 4 → z19 = w19) :
    ordinaryValue z5 z19 i 4 = ordinaryValue w5 w19 i 4 := by
  have he := h5 (by decide)
  subst w5
  fin_cases i <;> simp [ordinaryValue]

private theorem value_congr_5 (z5 z19 w5 w19 : ℂ) (i : Fin 15)
    (_h5 : 5 ∣ classOrder 5 → z5 = w5) (_h19 : 19 ∣ classOrder 5 → z19 = w19) :
    ordinaryValue z5 z19 i 5 = ordinaryValue w5 w19 i 5 := by
  fin_cases i <;> simp [ordinaryValue]

private theorem value_congr_6 (z5 z19 w5 w19 : ℂ) (i : Fin 15)
    (_h5 : 5 ∣ classOrder 6 → z5 = w5) (_h19 : 19 ∣ classOrder 6 → z19 = w19) :
    ordinaryValue z5 z19 i 6 = ordinaryValue w5 w19 i 6 := by
  fin_cases i <;> simp [ordinaryValue]

private theorem value_congr_7 (z5 z19 w5 w19 : ℂ) (i : Fin 15)
    (h5 : 5 ∣ classOrder 7 → z5 = w5) (_h19 : 19 ∣ classOrder 7 → z19 = w19) :
    ordinaryValue z5 z19 i 7 = ordinaryValue w5 w19 i 7 := by
  have he := h5 (by decide)
  subst w5
  fin_cases i <;> simp [ordinaryValue]

private theorem value_congr_8 (z5 z19 w5 w19 : ℂ) (i : Fin 15)
    (h5 : 5 ∣ classOrder 8 → z5 = w5) (_h19 : 19 ∣ classOrder 8 → z19 = w19) :
    ordinaryValue z5 z19 i 8 = ordinaryValue w5 w19 i 8 := by
  have he := h5 (by decide)
  subst w5
  fin_cases i <;> simp [ordinaryValue]

private theorem value_congr_9 (z5 z19 w5 w19 : ℂ) (i : Fin 15)
    (_h5 : 5 ∣ classOrder 9 → z5 = w5) (_h19 : 19 ∣ classOrder 9 → z19 = w19) :
    ordinaryValue z5 z19 i 9 = ordinaryValue w5 w19 i 9 := by
  fin_cases i <;> simp [ordinaryValue]

private theorem value_congr_10 (z5 z19 w5 w19 : ℂ) (i : Fin 15)
    (h5 : 5 ∣ classOrder 10 → z5 = w5) (_h19 : 19 ∣ classOrder 10 → z19 = w19) :
    ordinaryValue z5 z19 i 10 = ordinaryValue w5 w19 i 10 := by
  have he := h5 (by decide)
  subst w5
  fin_cases i <;> simp [ordinaryValue]

private theorem value_congr_11 (z5 z19 w5 w19 : ℂ) (i : Fin 15)
    (h5 : 5 ∣ classOrder 11 → z5 = w5) (_h19 : 19 ∣ classOrder 11 → z19 = w19) :
    ordinaryValue z5 z19 i 11 = ordinaryValue w5 w19 i 11 := by
  have he := h5 (by decide)
  subst w5
  fin_cases i <;> simp [ordinaryValue]

private theorem value_congr_12 (z5 z19 w5 w19 : ℂ) (i : Fin 15)
    (_h5 : 5 ∣ classOrder 12 → z5 = w5) (h19 : 19 ∣ classOrder 12 → z19 = w19) :
    ordinaryValue z5 z19 i 12 = ordinaryValue w5 w19 i 12 := by
  have he := h19 (by decide)
  subst w19
  fin_cases i <;> simp [ordinaryValue]

private theorem value_congr_13 (z5 z19 w5 w19 : ℂ) (i : Fin 15)
    (_h5 : 5 ∣ classOrder 13 → z5 = w5) (h19 : 19 ∣ classOrder 13 → z19 = w19) :
    ordinaryValue z5 z19 i 13 = ordinaryValue w5 w19 i 13 := by
  have he := h19 (by decide)
  subst w19
  fin_cases i <;> simp [ordinaryValue]

private theorem value_congr_14 (z5 z19 w5 w19 : ℂ) (i : Fin 15)
    (_h5 : 5 ∣ classOrder 14 → z5 = w5) (h19 : 19 ∣ classOrder 14 → z19 = w19) :
    ordinaryValue z5 z19 i 14 = ordinaryValue w5 w19 i 14 := by
  have he := h19 (by decide)
  subst w19
  fin_cases i <;> simp [ordinaryValue]

theorem value_congr (z5 z19 w5 w19 : ℂ) (i j : Fin 15)
    (h5 : 5 ∣ classOrder j → z5 = w5) (h19 : 19 ∣ classOrder j → z19 = w19) :
    ordinaryValue z5 z19 i j = ordinaryValue w5 w19 i j := by
  fin_cases j
  · exact value_congr_0 z5 z19 w5 w19 i h5 h19
  · exact value_congr_1 z5 z19 w5 w19 i h5 h19
  · exact value_congr_2 z5 z19 w5 w19 i h5 h19
  · exact value_congr_3 z5 z19 w5 w19 i h5 h19
  · exact value_congr_4 z5 z19 w5 w19 i h5 h19
  · exact value_congr_5 z5 z19 w5 w19 i h5 h19
  · exact value_congr_6 z5 z19 w5 w19 i h5 h19
  · exact value_congr_7 z5 z19 w5 w19 i h5 h19
  · exact value_congr_8 z5 z19 w5 w19 i h5 h19
  · exact value_congr_9 z5 z19 w5 w19 i h5 h19
  · exact value_congr_10 z5 z19 w5 w19 i h5 h19
  · exact value_congr_11 z5 z19 w5 w19 i h5 h19
  · exact value_congr_12 z5 z19 w5 w19 i h5 h19
  · exact value_congr_13 z5 z19 w5 w19 i h5 h19
  · exact value_congr_14 z5 z19 w5 w19 i h5 h19

theorem power_class_dvd (j : Fin 15) (k : ℕ) :
    classOrder (ordinaryPowerClass j k) ∣ classOrder j := by
  have hm : ordinaryPowerClass j k = ordinaryPowerClass j (k % classOrder j) := by
    simp [ordinaryPowerClass]
  rw [hm]
  have hp : 0 < classOrder j := by fin_cases j <;> decide
  generalize hk : k % classOrder j = m
  have hm : m < classOrder j := hk ▸ Nat.mod_lt k hp
  have hall : ∀ (j : Fin 15) (m : Fin (classOrder j)),
      classOrder (ordinaryPowerClass j m) ∣ classOrder j := by decide +kernel
  exact hall j ⟨m, hm⟩

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.CyclicRestrictions
