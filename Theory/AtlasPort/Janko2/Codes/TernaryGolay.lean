/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Codes/TernaryGolay.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# TernaryGolay

The explicit six-parameter encoder gives the self-dual ternary Golay code
of length twelve. A coordinate calculation proves orthogonality, and kernel
enumeration gives the weight distribution and minimum distance six.

Source: Gerald Höhn, ATLAS, `Atlas/Codes/TernaryGolay.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies.
-/

@[expose] public section

namespace Atlas.Codes
open scoped BigOperators

abbrev TernaryWord := Fin 12 → ZMod 3
abbrev TernaryParameters := Fin 6 → ZMod 3

/-- The six-parameter marking specified in Job 19; parameter 5 is a. -/
def ternaryEncoder : TernaryParameters →ₗ[ZMod 3] TernaryWord where
  toFun p := ![p 0, p 1, p 2, p 3, p 4, -(p 0+p 1+p 2+p 3+p 4),
    p 5+p 4+p 1-p 3-p 2, p 5+p 0+p 2-p 4-p 3,
    p 5+p 1+p 3-p 0-p 4, p 5+p 2+p 4-p 1-p 0,
    p 5+p 3+p 0-p 2-p 1, p 5]
  map_add' := by intros; ext i; fin_cases i <;> simp <;> ring
  map_smul' := by intros; ext i; fin_cases i <;> simp <;> ring

def ternaryGolay : Submodule (ZMod 3) TernaryWord := ternaryEncoder.range

def ternaryDecoder (w : TernaryWord) : TernaryParameters :=
  ![w 0, w 1, w 2, w 3, w 4, w 11]

theorem ternary_decode_encode (p : TernaryParameters) :
    ternaryDecoder (ternaryEncoder p) = p := by
  ext i; fin_cases i <;> rfl

theorem ternaryEncoder_injective : Function.Injective ternaryEncoder :=
  Function.LeftInverse.injective ternary_decode_encode

noncomputable def ternaryGolayEquiv : TernaryParameters ≃ₗ[ZMod 3] ternaryGolay :=
  LinearEquiv.ofInjective ternaryEncoder ternaryEncoder_injective

theorem ternaryGolay_finrank : Module.finrank (ZMod 3) ternaryGolay = 6 := by
  rw [← ternaryGolayEquiv.finrank_eq]
  simp [TernaryParameters]

theorem ternaryGolay_card : Nat.card ternaryGolay = 729 := by
  rw [← Nat.card_congr ternaryGolayEquiv.toEquiv]
  norm_num [TernaryParameters, Nat.card_eq_fintype_card]

theorem ternaryGolay_one : (fun _ => (1 : ZMod 3)) ∈ ternaryGolay := by
  refine ⟨fun _ => 1, ?_⟩
  ext i; fin_cases i <;> norm_num [ternaryEncoder]; decide

def ternaryWeight (w : TernaryWord) : ℕ :=
  (Finset.univ.filter (fun i => w i ≠ 0)).card

def ternaryDot : LinearMap.BilinForm (ZMod 3) TernaryWord :=
  dotProductBilin (ZMod 3) (ZMod 3)

theorem ternaryEncoder_dot (p q : TernaryParameters) :
    ternaryDot (ternaryEncoder p) (ternaryEncoder q) = 0 := by
  simp [ternaryDot, dotProductBilin, dotProduct, Fin.sum_univ_succ, ternaryEncoder]
  ring_nf
  simp [show (6 : ZMod 3) = 0 by decide]

theorem ternaryDot_nondegenerate : ternaryDot.Nondegenerate := by
  have hl : ∀ u : TernaryWord, (∀ v, ternaryDot u v = 0) → u = 0 := by
    intro u hu
    funext i
    simpa [ternaryDot, dotProductBilin, dotProduct, Pi.single_apply, mul_ite] using hu (Pi.single i 1)
  exact ⟨hl, fun u hu => hl u (fun v => by
    simpa [ternaryDot, dotProductBilin, dotProduct, mul_comm] using hu v)⟩

theorem ternaryGolay_selfOrthogonal : ternaryGolay ≤ ternaryDot.orthogonal ternaryGolay := by
  rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
  exact ternaryEncoder_dot q p

theorem ternaryGolay_selfDual : ternaryGolay = ternaryDot.orthogonal ternaryGolay := by
  apply Submodule.eq_of_le_of_finrank_le ternaryGolay_selfOrthogonal
  rw [ternaryDot.finrank_orthogonal ternaryDot_nondegenerate, ternaryGolay_finrank]
  simp [TernaryWord]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ternaryEncoder_weight_distribution :
    ∀ k : Fin 13, (Finset.univ.filter (fun p : TernaryParameters =>
      ternaryWeight (ternaryEncoder p) = k.val)).card =
      ![1,0,0,0,0,0,264,0,0,440,0,0,24] k := by
  decide +kernel


theorem ternaryGolay_weight_distribution (k : Fin 13) :
    Nat.card {w : ternaryGolay // ternaryWeight w.val = k.val} =
      ![1,0,0,0,0,0,264,0,0,440,0,0,24] k := by
  let e : {p : TernaryParameters // ternaryWeight (ternaryEncoder p) = k.val} ≃
      {w : ternaryGolay // ternaryWeight w.val = k.val} :=
    Equiv.subtypeEquiv ternaryGolayEquiv.toEquiv (fun _ => Iff.rfl)
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact ternaryEncoder_weight_distribution k

theorem ternaryWeight_le (w : TernaryWord) : ternaryWeight w ≤ 12 :=
  (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin 12)

theorem ternaryWeight_eq_zero (w : TernaryWord) : ternaryWeight w = 0 ↔ w = 0 := by
  simp [ternaryWeight, Finset.filter_eq_empty_iff, funext_iff]

theorem ternaryGolay_minimum (w : TernaryWord) (hw : w ∈ ternaryGolay)
    (hne : w ≠ 0) : 6 ≤ ternaryWeight w := by
  by_contra h
  have hlt : ternaryWeight w < 6 := by omega
  obtain ⟨p, rfl⟩ := hw
  have hp : p ∈ Finset.univ.filter (fun q : TernaryParameters =>
      ternaryWeight (ternaryEncoder q) = ternaryWeight (ternaryEncoder p)) := by simp
  have hc := Finset.card_pos.mpr ⟨p, hp⟩
  have hd := ternaryEncoder_weight_distribution ⟨ternaryWeight (ternaryEncoder p), by omega⟩
  have hz : ternaryWeight (ternaryEncoder p) ≠ 0 := mt (ternaryWeight_eq_zero _).mp hne
  have hzcount : ∀ k : Fin 13, 0 < k.val → k.val < 6 →
      ![1,0,0,0,0,0,264,0,0,440,0,0,24] k = (0 : ℕ) := by decide
  have he := hzcount ⟨ternaryWeight (ternaryEncoder p), by omega⟩ (Nat.pos_of_ne_zero hz) hlt
  rw [he] at hd
  exact (Nat.ne_of_gt hc) hd

theorem ternaryGolay_minimum_attained : ∃ w : ternaryGolay, ternaryWeight w.val = 6 := by
  have h := ternaryGolay_weight_distribution 6
  have hn : Nonempty {w : ternaryGolay // ternaryWeight w.val = 6} :=
    Nat.card_pos_iff.mp (by simpa using (show 0 < Nat.card {w : ternaryGolay //
      ternaryWeight w.val = (6 : Fin 13).val} by rw [h]; decide)) |>.1
  exact ⟨hn.some.val, hn.some.prop⟩
end Atlas.Codes
