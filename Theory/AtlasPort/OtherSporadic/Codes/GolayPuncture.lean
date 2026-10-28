/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu23PointStabilizer

/-!
# GolayPuncture

Deleting one coordinate gives a twelve-dimensional binary code with 4096 words and
minimum weight seven. Even parity recovers the deleted bit, proving injectivity, and an
octad through the coordinate attains the minimum.

Source: `Atlas/Codes/GolayPuncture.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
open scoped BigOperators

local instance (a : Omega) : Fintype (Mathieu23Points a) := Fintype.ofFinite _

abbrev PuncturedWord (a : Omega) := Mathieu23Points a → Bit

def puncture (a : Omega) : BinaryWord →ₗ[Bit] PuncturedWord a where
  toFun w x := w x.val
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def puncturedGolay (a : Omega) : Submodule Bit (PuncturedWord a) := golay.map (puncture a)

theorem sum_puncture (a : Omega) (w : BinaryWord) :
    (∑ x, w x) = w a + ∑ x : Mathieu23Points a, w x.val := by
  classical
  have hs : (∑ x : Mathieu23Points a, w x.val) = ∑ x ∈ Finset.univ.erase a, w x := by
    symm
    apply Finset.sum_subtype
    intro x
    simp [SubMulAction.mem_ofStabilizer_iff]
  rw [hs]
  exact (Finset.add_sum_erase _ _ (Finset.mem_univ a)).symm

theorem golay_parity_recovery (a : Omega) (w : golay) :
    w.val a = ∑ x : Mathieu23Points a, w.val x.val := by
  have he : Even (hammingNorm w.val) := even_iff_two_dvd.mpr
    (dvd_trans (by decide : 2 ∣ 4) (golay_doublyEven _ w.prop))
  have h := (even_weight_iff w.val).mp he
  rw [sum_puncture a] at h
  have hb : ∀ x y : Bit, x + y = 0 → x = y := by decide
  exact hb _ _ h

theorem puncture_golay_injective (a : Omega) :
    Function.Injective ((puncture a).comp golay.subtype) := by
  intro u v h
  apply Subtype.ext
  funext x
  by_cases hx : x = a
  · subst x
    rw [golay_parity_recovery a u, golay_parity_recovery a v]
    apply Finset.sum_congr rfl
    intro y _
    exact congrFun h y
  · exact congrFun h ⟨x,hx⟩

def puncturedGolayEquiv (a : Omega) : golay ≃ₗ[Bit] puncturedGolay a :=
  (LinearEquiv.ofInjective ((puncture a).comp golay.subtype) (puncture_golay_injective a)).trans
    (LinearEquiv.ofEq _ _ (by simp [puncturedGolay, LinearMap.range_comp]))

theorem puncturedGolay_finrank (a : Omega) : Module.finrank Bit (puncturedGolay a) = 12 := by
  rw [← (puncturedGolayEquiv a).finrank_eq, golay_finrank]

theorem puncturedGolay_card (a : Omega) : Nat.card (puncturedGolay a) = 4096 := by
  rw [← Nat.card_congr (puncturedGolayEquiv a).toEquiv, golay_card]

theorem puncture_weight (a : Omega) (w : BinaryWord) :
    hammingNorm w = (if w a = 0 then 0 else 1) + hammingNorm (puncture a w) := by
  classical
  simp only [hammingNorm_eq_sum]
  have hs : (∑ x : Mathieu23Points a, if w x.val = 0 then 0 else 1 : ℕ) =
      ∑ x ∈ Finset.univ.erase a, if w x = 0 then 0 else 1 := by
    symm
    apply Finset.sum_subtype
    intro x
    simp [SubMulAction.mem_ofStabilizer_iff]
  change (∑ x : Omega, if w x = 0 then 0 else 1 : ℕ) = _
  change _ = (if w a = 0 then 0 else 1) + ∑ x : Mathieu23Points a, if w x.val = 0 then 0 else 1
  rw [hs]
  exact (Finset.add_sum_erase _ _ (Finset.mem_univ a)).symm

theorem puncturedGolay_minimum (a : Omega) (w : PuncturedWord a)
    (hw : w ∈ puncturedGolay a) (hn : w ≠ 0) : 7 ≤ hammingNorm w := by
  obtain ⟨v,hv,rfl⟩ := hw
  have hvn : v ≠ 0 := by intro h; subst v; exact hn rfl
  have hm := golay_minimum v hv hvn
  have he := puncture_weight a v
  split_ifs at he <;> omega

theorem octad_through_coordinate (a : Omega) : ∃ O ∈ octads, a ∈ O := by
  classical
  obtain ⟨F,hF,hc⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset Omega).erase a) (n := 4)
    (by simp [Omega, HexIndex])
  have ha : a ∉ F := fun h => (Finset.mem_erase.mp (hF h)).1 rfl
  obtain ⟨O,⟨hO,hFO⟩,_⟩ := octad_steiner (insert a F) (by simp [ha,hc])
  exact ⟨O,hO,hFO (Finset.mem_insert_self _ _)⟩

theorem puncturedGolay_minimum_witness (a : Omega) :
    ∃ w ∈ puncturedGolay a, hammingNorm w = 7 := by
  classical
  obtain ⟨O,hO,ha⟩ := octad_through_coordinate a
  obtain ⟨v,hv,rfl⟩ := (octads_mem O).mp hO
  have hva : v.val a ≠ 0 := (Finset.mem_filter.mp ha).2
  refine ⟨puncture a v.val, ⟨v.val,v.prop,rfl⟩,?_⟩
  have he := puncture_weight a v.val
  rw [hv, if_neg hva] at he
  omega

end Atlas.Codes
