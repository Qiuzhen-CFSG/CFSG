/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Codes/TernaryGolayFullWeight.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Codes.TernaryGolaySupports

/-!
# TernaryGolayFullWeight

The 24 full-weight words give 12 normalized opposite pairs with orthogonal integral signs.
Minimum distance and the weight identity control pairwise distances.

Source: Gerald Höhn, ATLAS, `Atlas/Codes/TernaryGolayFullWeight.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed computational definitions.
-/

@[expose] public section


namespace Atlas.Codes
open scoped BigOperators

/-- The 24 full-weight words, distinct from the 12 coordinate positions. -/
abbrev TernaryFullWords := {w : ternaryGolay // ternaryWeight w.val = 12}

/-- Representatives of opposite full-weight pairs, normalized at coordinate 11. -/
abbrev TernaryFullPairs := {w : ternaryGolay // ternaryWeight w.val = 12 ∧ w.val 11 = 1}

theorem ternaryFullWords_card : Nat.card TernaryFullWords = 24 :=
  ternaryGolay_weight_distribution 12

theorem ternarySupport_full {w : TernaryWord} (hw : ternaryWeight w = 12) :
    ternarySupport w = Finset.univ := by
  apply Finset.eq_univ_of_card
  simpa [ternarySupport_card] using hw

theorem ternaryFull_nonzero {w : TernaryWord} (hw : ternaryWeight w = 12)
    (i : Fin 12) : w i ≠ 0 := by
  have h : i ∈ ternarySupport w := by rw [ternarySupport_full hw]; exact Finset.mem_univ _
  simpa [ternarySupport] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ternaryEncoder_fullPairs_count :
    (Finset.univ.filter (fun p : TernaryParameters =>
      ternaryWeight (ternaryEncoder p) = 12 ∧ ternaryEncoder p 11 = 1)).card = 12 := by
  decide +kernel

theorem ternaryFullPairs_card : Nat.card TernaryFullPairs = 12 := by
  let e : {p : TernaryParameters // ternaryWeight (ternaryEncoder p) = 12 ∧
      ternaryEncoder p 11 = 1} ≃ TernaryFullPairs :=
    Equiv.subtypeEquiv ternaryGolayEquiv.toEquiv (fun _ => Iff.rfl)
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact ternaryEncoder_fullPairs_count

theorem ternaryFull_weight_sum {u v : TernaryWord}
    (hu : ternaryWeight u = 12) (hv : ternaryWeight v = 12) :
    ternaryWeight (u + v) + ternaryWeight (u - v) = 12 := by
  have h := ternaryWeight_add_sub u v
  rw [ternarySupport_full hu, ternarySupport_full hv, Finset.inter_self,
    Finset.card_univ, Fintype.card_fin, hu, hv] at h
  omega

theorem ternaryFull_distance {u v : TernaryWord} (hu : u ∈ ternaryGolay)
    (hv : v ∈ ternaryGolay) (huw : ternaryWeight u = 12)
    (hvw : ternaryWeight v = 12) (hne : u ≠ v) (hneg : u ≠ -v) :
    ternaryWeight (u - v) = 6 ∧ ternaryWeight (u + v) = 6 := by
  have hd := ternaryGolay_minimum (u-v) (ternaryGolay.sub_mem hu hv)
    (sub_ne_zero.mpr hne)
  have ha := ternaryGolay_minimum (u+v) (ternaryGolay.add_mem hu hv)
    (fun h => hneg (eq_neg_of_add_eq_zero_left h))
  have hs := ternaryFull_weight_sum huw hvw
  omega

theorem ternaryFullPairs_distance (u v : TernaryFullPairs) (hne : u ≠ v) :
    ternaryWeight (u.val.val - v.val.val) = 6 ∧
      ternaryWeight (u.val.val + v.val.val) = 6 := by
  apply ternaryFull_distance u.val.prop v.val.prop u.prop.1 v.prop.1
  · exact fun h => hne (Subtype.ext (Subtype.ext h))
  · intro h
    have he := congrFun h 11
    simp only [Pi.neg_apply, u.prop.2, v.prop.2] at he
    exact (by decide : (1 : ZMod 3) ≠ -1) he

def ternaryFullNormalize (w : TernaryFullWords) : TernaryFullPairs :=
  ⟨⟨w.val.val 11 • w.val.val, ternaryGolay.smul_mem _ w.val.prop⟩, by
    have hn := ternaryFull_nonzero w.prop 11
    have he : w.val.val 11 = 1 ∨ w.val.val 11 = -1 := by
      have h : ∀ a : ZMod 3, a ≠ 0 → a = 1 ∨ a = -1 := by decide
      exact h _ hn
    constructor
    · rcases he with he | he
      · simpa [he] using w.prop
      · simpa [he, ternaryWeight_neg] using w.prop
    · change w.val.val 11 * w.val.val 11 = 1
      rcases he with he | he <;> simp [he]⟩

theorem ternaryFullNormalize_rep (w : TernaryFullWords) :
    (ternaryFullNormalize w).val.val = w.val.val ∨
      (ternaryFullNormalize w).val.val = -w.val.val := by
  have h : ∀ a : ZMod 3, a ≠ 0 → a = 1 ∨ a = -1 := by decide
  rcases h _ (ternaryFull_nonzero w.prop 11) with he | he
  · left; change w.val.val 11 • w.val.val = w.val.val; simp [he]
  · right; change w.val.val 11 • w.val.val = -w.val.val; simp [he]

theorem ternaryFullPairs_unique_rep (u v : TernaryFullPairs)
    (h : u.val.val = v.val.val ∨ u.val.val = -v.val.val) : u = v := by
  rcases h with h | h
  · exact Subtype.ext (Subtype.ext h)
  · have he := congrFun h 11
    simp only [Pi.neg_apply, u.prop.2, v.prop.2] at he
    exact False.elim ((by decide : (1 : ZMod 3) ≠ -1) he)

/-- Integral signs of a full-weight word. -/
def ternaryIntegralSigns (w : TernaryWord) : Fin 12 → ℤ :=
  fun i => if w i = 1 then 1 else -1

theorem ternaryFull_sign_dot (u v : TernaryWord)
    (hu : ternaryWeight u = 12) (hv : ternaryWeight v = 12) :
    (∑ i, ternaryIntegralSigns u i * ternaryIntegralSigns v i) +
      2 * (ternaryWeight (u-v) : ℤ) = 12 := by
  have h : ∀ a b : ZMod 3, a ≠ 0 → b ≠ 0 →
      (if a = 1 then 1 else -1 : ℤ) * (if b = 1 then 1 else -1) +
      2 * (if a-b ≠ 0 then 1 else 0 : ℤ) = 1 := by decide
  have he := congrArg (fun f : Fin 12 → ℤ => ∑ i, f i)
    (funext (fun i => h (u i) (v i) (ternaryFull_nonzero hu i)
      (ternaryFull_nonzero hv i)))
  simpa [ternaryIntegralSigns, ternaryWeight, Finset.card_filter,
    Finset.sum_add_distrib, Finset.mul_sum] using he

theorem ternaryFullPairs_orthogonal (u v : TernaryFullPairs) (hne : u ≠ v) :
    ∑ i, ternaryIntegralSigns u.val.val i * ternaryIntegralSigns v.val.val i = 0 := by
  have hd := (ternaryFullPairs_distance u v hne).1
  have h := ternaryFull_sign_dot u.val.val v.val.val u.prop.1 v.prop.1
  rw [hd] at h
  omega

theorem ternaryFull_sign_norm (u : TernaryFullWords) :
    ∑ i, ternaryIntegralSigns u.val.val i * ternaryIntegralSigns u.val.val i = 12 := by
  have h := ternaryFull_sign_dot u.val.val u.val.val u.prop u.prop
  simpa [sub_self, ternaryWeight] using h

end Atlas.Codes
