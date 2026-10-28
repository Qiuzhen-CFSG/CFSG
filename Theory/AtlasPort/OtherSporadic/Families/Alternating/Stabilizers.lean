/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Families/Alternating/Stabilizers.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Families.Alternating.Basic
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# Stabilizers

Pointwise stabilizers in alternating groups are alternating groups on the complement.
Extension by the identity and restriction are inverse multiplicative equivalences.

Source: Gerald Höhn, ATLAS, `Atlas/Families/Alternating/Stabilizers.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for downstream calculations in the source API.
-/

@[expose] public section

namespace Atlas.Families.Alternating

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem extension_range (s : Finset α) :
    (alternatingGroup.ofSubtype sᶜ).range =
      fixingSubgroup (alternatingGroup α) (s : Set α) := by
  ext g
  rw [alternatingGroup.mem_range_ofSubtype_iff]
  constructor
  · intro h x
    have hn : x.val ∉ (g.val).support := by
      intro hx
      have := h hx
      simp at this
    exact Equiv.Perm.notMem_support.mp hn
  · intro h x hx
    apply Finset.mem_compl.mpr
    intro hs
    have hf := h ⟨x, hs⟩
    exact (Equiv.Perm.mem_support.mp hx) hf

/-- Intrinsic complement equivalence, inverse to extension by the identity. -/
noncomputable def stabilizerComplementEquiv (s : Finset α) :
    fixingSubgroup (alternatingGroup α) (s : Set α) ≃* alternatingGroup (sᶜ : Finset α) :=
  (MulEquiv.subgroupCongr (extension_range s).symm).trans
    (MonoidHom.ofInjective (alternatingGroup.ofSubtype_injective (s := sᶜ))).symm

theorem stabilizerComplementEquiv_extension (s : Finset α)
    (g : fixingSubgroup (alternatingGroup α) (s : Set α)) :
    alternatingGroup.ofSubtype sᶜ (stabilizerComplementEquiv s g) = g.val := by
  exact MonoidHom.apply_ofInjective_symm (alternatingGroup.ofSubtype_injective (s := sᶜ)) _

theorem stabilizerComplementEquiv_apply (s : Finset α)
    (g : fixingSubgroup (alternatingGroup α) (s : Set α)) (x : (sᶜ : Finset α)) :
    ((stabilizerComplementEquiv s g).val x).val = g.val.val x.val := by
  have h := congrArg (fun k : alternatingGroup α => k.val x.val)
    (stabilizerComplementEquiv_extension s g)
  simpa [alternatingGroup.ofSubtype] using h

def tuplePoints {n k : ℕ} (e : Fin k ↪ Fin n) : Finset (Fin n) := Finset.univ.map e

abbrev PointwiseStabilizer {n k : ℕ} (e : Fin k ↪ Fin n) :=
  fixingSubgroup (Model n) (tuplePoints e : Set (Fin n))

theorem mem_pointwiseStabilizer {n k : ℕ} (e : Fin k ↪ Fin n) (g : Model n) :
    g ∈ PointwiseStabilizer e ↔ ∀ i, g.val (e i) = e i := by
  constructor
  · intro h i
    exact h ⟨e i, by simp [tuplePoints]⟩
  · intro h x
    obtain ⟨i, hi⟩ := (by simpa [tuplePoints] using x.property : ∃ i, e i = x.val)
    change g.val x.val = x.val
    simpa [← hi] using h i

theorem complement_card {n k : ℕ} (e : Fin k ↪ Fin n) :
    Fintype.card (↑((tuplePoints e)ᶜ)) = n - k := by
  rw [Fintype.card_coe, Finset.card_compl]
  simp only [tuplePoints, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- Numerical identification uses a choice of labelling of the complement. -/
noncomputable def stabilizerEquiv {n k : ℕ} (e : Fin k ↪ Fin n) :
    PointwiseStabilizer e ≃* Model (n - k) :=
  (stabilizerComplementEquiv (tuplePoints e)).trans
    (relabel (Fintype.equivFinOfCardEq (complement_card e)))

theorem stabilizer_card {n k : ℕ} (e : Fin k ↪ Fin n) :
    Nat.card (PointwiseStabilizer e) = order (n - k) :=
  (Nat.card_congr (stabilizerEquiv e).toEquiv).trans (card (n - k))

theorem stabilizer_card_factorial {n k : ℕ} (e : Fin k ↪ Fin n) (hk : k + 2 ≤ n) :
    Nat.card (PointwiseStabilizer e) = (n - k).factorial / 2 := by
  rw [stabilizer_card, order, if_neg (by omega)]

theorem stabilizer_card_one {n k : ℕ} (e : Fin k ↪ Fin n) (hk : n - k ≤ 1) :
    Nat.card (PointwiseStabilizer e) = 1 := by
  rw [stabilizer_card, order, if_pos (by omega)]

theorem stabilizer_trivial {n k : ℕ} (e : Fin k ↪ Fin n) (hk : n - k ≤ 1) :
    Subsingleton (PointwiseStabilizer e) := by
  have h := stabilizer_card_one e hk
  exact (Nat.card_eq_one_iff_unique.mp h).1

end Atlas.Families.Alternating
