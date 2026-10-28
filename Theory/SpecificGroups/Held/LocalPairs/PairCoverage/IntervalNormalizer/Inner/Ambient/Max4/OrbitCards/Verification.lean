module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.OrbitCards.Actions
public import Mathlib.Data.Fintype.Card
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Soundness of the max4 orbit certificates

Generator-invariant colors are constant on the generated subgroup's orbits.
A forest whose depth decreases toward the specified roots supplies group
words reaching every vertex of each color. The actual orbits therefore equal
the color fibers. Counting those fibers gives the required orbit sizes.

This checker is specialized to the literal Schreier closures in `Max4.Data`;
it assumes no abstract orbit partition or external group order.
-/

open Subgroup
namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.OrbitCards

private theorem schreierGenerator_closure (j : Fin 7) :
    closure (Set.range (schreierGenerator j)) = candidate j := by
  change closure _ = closure _
  congr 1
  ext g
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨_, _, rfl⟩
  · rintro ⟨e, k, rfl⟩
    cases e
    · refine ⟨⟨k.val, by omega⟩, ?_⟩
      simp [schreierGenerator, show ¬ 4 ≤ k.val by omega, Nat.mod_eq_of_lt k.isLt]
    · refine ⟨⟨4 + k.val, by omega⟩, ?_⟩
      simp [schreierGenerator, Nat.mod_eq_of_lt k.isLt]

private theorem preserves_color {t : ℕ} (j : Fin 7) (color : Fin 2058 → Fin t)
    (hc : ∀ r x, color (schreierGenerator j r • x) = color x)
    (g : candidate j) (x : Fin 2058) : color (g • x) = color x := by
  have hg : g.val ∈ closure (Set.range (schreierGenerator j)) := by
    simpa only [schreierGenerator_closure] using g.property
  have h : ∀ a : He, a ∈ closure (Set.range (schreierGenerator j)) →
      ∀ y, color (a • y) = color y := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem a ha =>
      obtain ⟨r, rfl⟩ := ha
      exact hc r
    | one => intro y; rw [one_smul]
    | mul a b ha hb ha' hb' => intro y; rw [mul_smul, ha', hb']
    | inv a ha ha' =>
      intro y
      simpa only [smul_inv_smul] using (ha' (a⁻¹ • y)).symm
  exact h g.val hg x

private theorem reach {t : ℕ} (j : Fin 7) (color : Fin 2058 → Fin t)
    (rep : Fin t → Fin 2058) (depth : Fin 2058 → ℕ)
    (parent : Fin 2058 → Fin 2058) (step : Fin 2058 → Fin 8)
    (ht : ∀ x, x = rep (color x) ∨ (depth (parent x) < depth x ∧
      color (parent x) = color x ∧ schreierGenerator j (step x) • parent x = x))
    (x : Fin 2058) : ∃ g : candidate j, g • rep (color x) = x := by
  suffices h : ∀ n : ℕ, ∀ y, depth y = n → ∃ g : candidate j, g • rep (color y) = y from
    h (depth x) x rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro y hy
    rcases ht y with he | ⟨hd, hc, hs⟩
    · exact ⟨1, by simpa using he.symm⟩
    · obtain ⟨g, hg⟩ := ih (depth (parent y)) (by omega) (parent y) rfl
      rw [hc] at hg
      exact ⟨⟨schreierGenerator j (step y), schreierGenerator_mem j _⟩ * g,
        by rw [mul_smul, hg]; exact hs⟩

public theorem card_of_forest {t : ℕ} (j : Fin 7) (color : Fin 2058 → Fin t)
    (rep : Fin t → Fin 2058) (depth : Fin 2058 → ℕ)
    (parent : Fin 2058 → Fin 2058) (step : Fin 2058 → Fin 8) (size : Fin t → ℕ)
    (hc : ∀ r x, color (schreierGenerator j r • x) = color x)
    (ht : ∀ x, x = rep (color x) ∨ (depth (parent x) < depth x ∧
      color (parent x) = color x ∧ schreierGenerator j (step x) • parent x = x))
    (hn : ∀ c, (List.finRange 2058).countP (fun x => decide (color x = c)) = size c)
    (hl : ∀ x, orbitSizeLabel j x = size (color x)) (x : Fin 2058) :
    orbitSizeLabel j x = Nat.card (MulAction.orbit (candidate j) x) := by
  have he : MulAction.orbit (candidate j) x = {y | color y = color x} := by
    ext y
    constructor
    · rintro ⟨g, rfl⟩
      exact preserves_color j color hc g x
    · intro hy
      obtain ⟨g, hg⟩ := reach j color rep depth parent step ht x
      obtain ⟨h, hh⟩ := reach j color rep depth parent step ht y
      rw [hy] at hh
      refine ⟨h * g⁻¹, ?_⟩
      change (h * g⁻¹) • x = y
      rw [mul_smul, ← hg, inv_smul_smul, hh]
  rw [he, hl, Nat.card_eq_fintype_card, Fintype.card_subtype,
    ← List.toFinset_finRange 2058, (List.nodup_finRange 2058).card_eq_countP]
  exact (hn (color x)).symm
end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.OrbitCards
