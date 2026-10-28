module

public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.Coordinates
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations.LongCommutators.RootCalculus
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations.BlockProduct

/-!
# Eliminating the two middle Ree main coordinates

After the outer coordinates vanish, the positive word is
`x₆ x₄ x₅ y₅ y₇ x₃ y₃` in GLS numbering. Commutation with `x₅(1)`
forces the main parameter of `x₃` to vanish: the exchange of `x₃` and `x₅`
produces `x₄`, while the same-block product contributes only `y₅`.
Commutation with `x₃(1)` then forces the main parameter of `x₅` to vanish;
the extra exchange with `x₆` contributes only `y₅` again. Unique positive
coordinates separate `x₄` from `y₅` in both calculations.

The two exchanges below are proved in the actual split matrix group by the
equal-length root relations. Nonnegative root inner products prove every
commutation used to discard other factors. The central fifth curve is
`centralWord m 4`, with both of its split factors. No exponent or involution
classification premise is used. The outer-coordinate premise is deliberately
retained for the independent outer elimination and the full-center assembly.

Source: GLS3 Table 2.4 and 2.4.5(d), `refs/KGroup/GLS3/chapter2.tex`.
Application: the Ree center calculation used in Aschbacher–Smith 13.6.6,
printed p.927 of `refs/quasithin.pdf`, with the A.2.3–4 model conventions.
-/

public section
noncomputable section

namespace ReeF4.NormalizedRootCentralizers.CenterExponent
open Theory.AlgebraicGroup StandardRootSystem
open Parabolics Parabolics.RadicalCoordinates.FixedCoordinates
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open MatrixRelations.LongCommutators

namespace MiddleElimination

private theorem fieldEnd_half (m : ℕ) (i : Fin 8) :
    rootFieldEnd m (longRoot i) = halfFrobenius m := by
  simp only [rootFieldEnd, if_pos (MatrixRelations.longRoot_isLong i), halfFrobenius]

private theorem main_two (m : ℕ) (t : CoefficientField m) :
    rootWord m 2 t = X m 6 t * X m 7 (halfFrobenius m t) *
      X m 8 (t * halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]; rfl
private theorem main_four (m : ℕ) (t : CoefficientField m) :
    rootWord m 4 t = X m 12 t * X m 13 (halfFrobenius m t) *
      X m 14 (t * halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]; rfl
private theorem main_three (m : ℕ) (t : CoefficientField m) :
    rootWord m 3 t = X m 10 t * X m 11 (halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  change X m 10 t * X m 11 (halfFrobenius m t) * 1 = _
  exact mul_one _
private theorem main_five (m : ℕ) (t : CoefficientField m) :
    rootWord m 5 t = X m 16 t * X m 17 (halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  change X m 16 t * X m 17 (halfFrobenius m t) * 1 = _
  exact mul_one _
private theorem central_two (m : ℕ) (t : CoefficientField m) :
    centralWord m 2 t = X m 9 t * X m 8 (halfFrobenius m t) := by
  simp only [centralWord, fieldEnd_half]; rfl
private theorem central_four (m : ℕ) (t : CoefficientField m) :
    centralWord m 4 t = X m 15 t * X m 14 (halfFrobenius m t) := by
  simp only [centralWord, fieldEnd_half]; rfl
private theorem central_six (m : ℕ) (t : CoefficientField m) :
    centralWord m 6 t = X m 21 t * X m 20 (halfFrobenius m t) := by
  simp only [centralWord, fieldEnd_half]; rfl

private theorem root_zero (m : ℕ) (r : F4Chevalley.Root) :
    rootGeneratorInGroup m r 0 = 1 := Subtype.ext (F4Chevalley.rootCurve_zero r)
private theorem main_zero (m : ℕ) (i : Fin 8) : rootWord m i 0 = 1 := by
  simp [rootWord, root_zero]
private theorem central_zero (m : ℕ) (i : Fin 8) : centralWord m i 0 = 1 := by
  simp [centralWord, root_zero]

private theorem commute_two_three {G : Type*} [Group G] (a b c d e : G)
    (hac : Commute a c) (had : Commute a d) (hae : Commute a e)
    (hbc : Commute b c) (hbd : Commute b d) (hbe : Commute b e) :
    Commute (a * b) (c * d * e) :=
  ((hac.mul_right had).mul_right hae).mul_left ((hbc.mul_right hbd).mul_right hbe)

private theorem commute_two_two {G : Type*} [Group G] (a b c d : G)
    (hac : Commute a c) (had : Commute a d) (hbc : Commute b c) (hbd : Commute b d) :
    Commute (a * b) (c * d) := (hac.mul_right had).mul_left (hbc.mul_right hbd)

private theorem pair_main_commute (m : ℕ) (i : Fin 8) (hi : i = 2 ∨ i = 4)
    (a b : CoefficientField m) : Commute (rootWord m 3 a) (rootWord m i b) := by
  rcases hi with rfl | rfl
  all_goals
    rw [main_three]
    first | rw [main_two] | rw [main_four]
    apply commute_two_three
    all_goals exact xc m _ _ (by norm_num [V, dot, Fin.sum_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three]) _ _

private theorem central_main_commute (m : ℕ) (i j : Fin 8)
    (hi : i = 2 ∨ i = 4 ∨ i = 6) (hj : j = 2 ∨ j = 4)
    (a b : CoefficientField m) : Commute (centralWord m i a) (rootWord m j b) := by
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl
  all_goals
    first | rw [central_two] | rw [central_four] | rw [central_six]
    first | rw [main_two] | rw [main_four]
    apply commute_two_three
    all_goals exact xc m _ _ (by norm_num [V, dot, Fin.sum_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three]) _ _

private theorem five_four_commute (m : ℕ) (a b : CoefficientField m) :
    Commute (rootWord m 5 a) (rootWord m 4 b) := by
  simp only [main_five, main_four]
  apply commute_two_three
  all_goals exact xc m _ _ (by norm_num [V, dot, Fin.sum_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three]) _ _

private theorem pair_central_four_commute (m : ℕ) (a b : CoefficientField m) :
    Commute (rootWord m 3 a) (centralWord m 4 b) := by
  simp only [main_three, central_four]
  apply commute_two_two
  all_goals exact xc m _ _ (by norm_num [V, dot, Fin.sum_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three]) _ _

local macro "geom" : tactic => `(tactic|
  norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three])

private theorem swap_suffix {G : Type*} [Group G] {a b c : G}
    (h : a * b = b * a * c) (d : G) : a * (b * d) = b * (a * (c * d)) := by
  simpa only [mul_assoc] using congrArg (fun z => z * d) h

-- Only the two equal-length exchanges contribute: their corrections are
-- the long and short factors of GLS block 4.
private theorem collect_two_four (m : ℕ) (a s b t : CoefficientField m) :
    X m 6 (a) * X m 7 (s) * X m 8 (a * s) * X m 12 (b) * X m 13 (t) * X m 14 (b * t) =
      X m 12 (b) * X m 13 (t) * X m 14 (b * t) * X m 6 (a) * X m 7 (s) * X m 8 (a * s) * X m 10 (a * b) * X m 11 (s * t) := by
  simp only [mul_assoc]
  rw [(xc m 8 12 (by geom) (a * s) (b)).left_comm]
  rw [(xc m 7 12 (by geom) (s) (b)).left_comm]
  rw [swap_suffix (xs m 6 12 10 (by geom) (by geom) (by ext z; fin_cases z <;> norm_num [V]) (a) (b))]
  rw [(xc m 10 7 (by geom) (a * b) (s)).left_comm]
  rw [(xc m 10 8 (by geom) (a * b) (a * s)).left_comm]
  rw [(xc m 10 13 (by geom) (a * b) (t)).left_comm]
  rw [(xc m 8 13 (by geom) (a * s) (t)).left_comm]
  rw [swap_suffix (xs m 7 13 11 (by geom) (by geom) (by ext z; fin_cases z <;> norm_num [V]) (s) (t))]
  rw [(xc m 6 13 (by geom) (a) (t)).left_comm]
  rw [(xc m 11 8 (by geom) (s * t) (a * s)).left_comm]
  rw [(xc m 11 10 (by geom) (s * t) (a * b)).left_comm]
  rw [(xc m 11 14 (by geom) (s * t) (b * t)).eq]
  rw [(xc m 10 14 (by geom) (a * b) (b * t)).left_comm]
  rw [(xc m 8 14 (by geom) (a * s) (b * t)).left_comm]
  rw [(xc m 7 14 (by geom) (s) (b * t)).left_comm]
  rw [(xc m 6 14 (by geom) (a) (b * t)).left_comm]

-- The sixth-third exchange has the two factors of the central fifth curve.
private theorem collect_five_two (m : ℕ) (a s b t : CoefficientField m) :
    X m 16 (a) * X m 17 (s) * X m 6 (b) * X m 7 (t) * X m 8 (b * t) =
      X m 6 (b) * X m 7 (t) * X m 8 (b * t) * X m 16 (a) * X m 17 (s) * X m 15 (a * b) * X m 14 (s * t) := by
  simp only [mul_assoc]
  rw [(xc m 17 6 (by geom) (s) (b)).left_comm]
  rw [swap_suffix (xs m 16 6 15 (by geom) (by geom) (by ext z; fin_cases z <;> norm_num [V]) (a) (b))]
  rw [(xc m 15 17 (by geom) (a * b) (s)).left_comm]
  rw [(xc m 15 7 (by geom) (a * b) (t)).left_comm]
  rw [swap_suffix (xs m 17 7 14 (by geom) (by geom) (by ext z; fin_cases z <;> norm_num [V]) (s) (t))]
  rw [(xc m 16 7 (by geom) (a) (t)).left_comm]
  rw [(xc m 14 15 (by geom) (s * t) (a * b)).left_comm]
  rw [(xc m 14 8 (by geom) (s * t) (b * t)).eq]
  rw [(xc m 15 8 (by geom) (a * b) (b * t)).left_comm]
  rw [(xc m 17 8 (by geom) (s) (b * t)).left_comm]
  rw [(xc m 16 8 (by geom) (a) (b * t)).left_comm]

private theorem two_four_exchange (m : ℕ) (a b : CoefficientField m) :
    rootWord m 2 a * rootWord m 4 b =
      rootWord m 4 b * rootWord m 2 a * rootWord m 3 (a * b) := by
  rw [main_two, main_four, main_three]
  simpa only [map_mul, mul_assoc] using
    collect_two_four m a (halfFrobenius m a) b (halfFrobenius m b)

private theorem five_two_exchange (m : ℕ) (a b : CoefficientField m) :
    rootWord m 5 a * rootWord m 2 b =
      rootWord m 2 b * rootWord m 5 a * centralWord m 4 (a * b) := by
  rw [main_five, main_two, central_four]
  simpa only [map_mul, mul_assoc] using
    collect_five_two m a (halfFrobenius m a) b (halfFrobenius m b)

private theorem commute_cancel_left {G : Type*} [Group G] {a b z : G}
    (ha : Commute a z) (hab : Commute (a * b) z) : Commute b z := by
  have h := ha.inv_left.mul_left hab
  simpa only [inv_mul_cancel_left] using h

private theorem commute_cancel_right {G : Type*} [Group G] {a b z : G}
    (hb : Commute b z) (hab : Commute (a * b) z) : Commute a z := by
  have h := hab.mul_left hb.inv_left
  simpa only [mul_inv_cancel_right] using h

private theorem positiveWord_reduced (m : ℕ) (p : PositiveParameters m)
    (ho : OuterCoordinatesZero p) :
    positiveWord m p =
      rootWord m 5 (p.pair 2) * rootWord m 3 (p.pair 3) *
      rootWord m 4 (p.main 1) * centralWord m 4 (p.central 1) *
      centralWord m 6 (p.central 2) * rootWord m 2 (p.main 3) *
      centralWord m 2 (p.central 3) := by
  simp [positiveWord, positive_pair_indices, positive_quartet_indices,
    pairCount, quartetCount, List.ofFn_succ, ho.pair_eighth, ho.pair_second, ho.main_first,
    ho.main_seventh, ho.central_first, main_zero, central_zero, mul_assoc]

private def detectionParameters (m : ℕ) (a b : CoefficientField m) : PositiveParameters m :=
  ⟨![0, 0, 0, a], 0, ![0, b, 0, 0]⟩

-- Keep the detecting fourth parameter separate from the central fifth one.
private theorem detection_word (m : ℕ) (a b : CoefficientField m) :
    positiveWord m (detectionParameters m a b) = rootWord m 3 a * centralWord m 4 b := by
  simp [positiveWord, detectionParameters, positive_pair_indices, positive_quartet_indices,
    pairCount, quartetCount, List.ofFn_succ, main_zero, central_zero]

private theorem detect_pair (m : ℕ) (a b c : CoefficientField m)
    (h : rootWord m 3 a * centralWord m 4 b = centralWord m 4 c) : a = 0 := by
  have hp : positiveWord m (detectionParameters m a b) =
      positiveWord m (detectionParameters m 0 c) := by
    simpa only [detection_word, main_zero, one_mul] using h
  exact congrArg (fun p : PositiveParameters m => p.pair 3) (positiveWord_injective m hp)

-- All factors except the two remaining main curves commute with x₅(t).
private theorem inner_commute_four (m : ℕ) (p : PositiveParameters m) (ho : OuterCoordinatesZero p)
    (t : CoefficientField m) (h : Commute (positiveWord m p) (rootWord m 4 t)) :
    Commute (rootWord m 4 (p.main 1) * rootWord m 2 (p.main 3)) (rootWord m 4 t) := by
  have hy (i : Fin 8) (hi : i = 2 ∨ i = 4 ∨ i = 6) (a : CoefficientField m) :=
    central_main_commute m i 4 hi (Or.inr rfl) a t
  rw [positiveWord_reduced m p ho] at h
  have h1 := commute_cancel_right (hy 2 (Or.inl rfl) (p.central 3)) h
  have h2 := commute_cancel_left
    ((five_four_commute m (p.pair 2) t).mul_left
      (pair_main_commute m 4 (Or.inr rfl) (p.pair 3) t))
    (show Commute ((rootWord m 5 (p.pair 2) * rootWord m 3 (p.pair 3)) *
      (rootWord m 4 (p.main 1) * (centralWord m 4 (p.central 1) *
      centralWord m 6 (p.central 2)) * rootWord m 2 (p.main 3))) (rootWord m 4 t) by
      simpa only [mul_assoc] using h1)
  have hc := (central_main_commute m 4 2 (Or.inr (Or.inl rfl)) (Or.inl rfl)
    (p.central 1) (p.main 3)).mul_left
    (central_main_commute m 6 2 (Or.inr (Or.inr rfl)) (Or.inl rfl)
      (p.central 2) (p.main 3))
  rw [mul_assoc, hc.eq, ← mul_assoc] at h2
  exact commute_cancel_right
    ((hy 4 (Or.inr (Or.inl rfl)) (p.central 1)).mul_left
      (hy 6 (Or.inr (Or.inr rfl)) (p.central 2))) h2

-- The x₄ correction detects the third main coordinate; the fifth-block
-- multiplication law contributes only a y₅ parameter.
private theorem main_third_zero (m : ℕ) (p : PositiveParameters m) (ho : OuterCoordinatesZero p)
    (h : Commute (positiveWord m p) (rootWord m 4 1)) : p.main 3 = 0 := by
  have hh := (inner_commute_four m p ho 1 h).eq
  rw [mul_assoc, two_four_exchange] at hh
  simp only [mul_one] at hh
  have he :
      (rootWord m 4 (p.main 1) * rootWord m 4 1) * rootWord m 2 (p.main 3) *
          rootWord m 3 (p.main 3) =
      (rootWord m 4 1 * rootWord m 4 (p.main 1)) * rootWord m 2 (p.main 3) := by
    simpa only [mul_assoc] using hh
  rw [MatrixRelations.rootWord_even_mul m 4 (by decide),
      MatrixRelations.rootWord_even_mul m 4 (by decide), add_comm 1 (p.main 1)] at he
  have he' := mul_left_cancel (show
      rootWord m 4 (p.main 1 + 1) *
        (centralWord m 4 (titsEnd m (p.main 1) * 1) * rootWord m 2 (p.main 3) *
          rootWord m 3 (p.main 3)) =
      rootWord m 4 (p.main 1 + 1) *
        (centralWord m 4 (titsEnd m 1 * p.main 1) * rootWord m 2 (p.main 3)) by
    simpa only [mul_assoc] using he)
  rw [(pair_main_commute m 2 (Or.inl rfl) (p.main 3) (p.main 3)).symm.right_comm] at he'
  have he'' := mul_right_cancel he'
  rw [(pair_central_four_commute m (p.main 3) (titsEnd m (p.main 1) * 1)).symm.eq] at he''
  exact detect_pair m _ _ _ he''

private theorem inner_commute_two (m : ℕ) (p : PositiveParameters m) (ho : OuterCoordinatesZero p)
    (hd : p.main 3 = 0) (t : CoefficientField m)
    (h : Commute (positiveWord m p) (rootWord m 2 t)) :
    Commute (rootWord m 5 (p.pair 2) * rootWord m 4 (p.main 1)) (rootWord m 2 t) := by
  have hy (i : Fin 8) (hi : i = 2 ∨ i = 4 ∨ i = 6) (a : CoefficientField m) :=
    central_main_commute m i 2 hi (Or.inl rfl) a t
  rw [positiveWord_reduced m p ho, hd, main_zero, mul_one] at h
  have h1 := commute_cancel_right (hy 2 (Or.inl rfl) (p.central 3)) h
  have h2 := commute_cancel_right (hy 6 (Or.inr (Or.inr rfl)) (p.central 2)) h1
  have h3 := commute_cancel_right (hy 4 (Or.inr (Or.inl rfl)) (p.central 1)) h2
  rw [mul_assoc, (pair_main_commute m 4 (Or.inr rfl) (p.pair 3) (p.main 1)).eq,
    ← mul_assoc] at h3
  exact commute_cancel_right (pair_main_commute m 2 (Or.inl rfl) (p.pair 3) t) h3

-- After x₃ vanishes, commuting with x₃(1) compares an x₄ parameter with
-- a y₅ parameter. Uniqueness forces the former to be zero.
private theorem main_fifth_zero (m : ℕ) (p : PositiveParameters m) (ho : OuterCoordinatesZero p)
    (hd : p.main 3 = 0)
    (h : Commute (positiveWord m p) (rootWord m 2 1)) : p.main 1 = 0 := by
  have hh := (inner_commute_two m p ho hd 1 h).eq
  have he :
      (rootWord m 2 1 * (rootWord m 5 (p.pair 2) * rootWord m 4 (p.main 1))) *
        rootWord m 3 (p.main 1) =
      (rootWord m 2 1 * (rootWord m 5 (p.pair 2) * rootWord m 4 (p.main 1))) *
        centralWord m 4 (p.pair 2) := by
    calc
      _ = (rootWord m 5 (p.pair 2) * rootWord m 4 (p.main 1)) *
          rootWord m 2 1 * rootWord m 3 (p.main 1) := by rw [hh]
      _ = rootWord m 5 (p.pair 2) *
          (rootWord m 4 (p.main 1) * rootWord m 2 1 * rootWord m 3 (1 * p.main 1)) := by
            simp only [one_mul, mul_assoc]
      _ = rootWord m 5 (p.pair 2) * (rootWord m 2 1 * rootWord m 4 (p.main 1)) := by
        rw [← two_four_exchange]
      _ = (rootWord m 2 1 * rootWord m 5 (p.pair 2) * centralWord m 4 (p.pair 2)) *
          rootWord m 4 (p.main 1) := by
        rw [← mul_assoc, five_two_exchange, mul_one]
      _ = _ := by
        rw [(central_main_commute m 4 4 (Or.inr (Or.inl rfl)) (Or.inr rfl)
          (p.pair 2) (p.main 1)).right_comm]
        simp only [mul_assoc]
  apply detect_pair m (p.main 1) 0 (p.pair 2)
  simpa only [central_zero, mul_one] using mul_left_cancel he

end MiddleElimination

/-- Centrality in all main curves, after outer-coordinate vanishing, kills
precisely the two remaining main coordinates (GLS blocks 5 and 3). This supplies
`hmiddle` in `unipotent_center_sq_of_coordinate_elimination`. -/
theorem middle_coordinates_zero (m : ℕ) (_hm : 0 < m) (p : PositiveParameters m)
    (ho : OuterCoordinatesZero p)
    (hcomm : ∀ i : Fin 8, ∀ t : CoefficientField m,
      Commute (positiveWord m p) (rootWord m i t)) : p.main 1 = 0 ∧ p.main 3 = 0 := by
  have hd := MiddleElimination.main_third_zero m p ho (hcomm 4 1)
  exact ⟨MiddleElimination.main_fifth_zero m p ho hd (hcomm 2 1), hd⟩

end ReeF4.NormalizedRootCentralizers.CenterExponent
