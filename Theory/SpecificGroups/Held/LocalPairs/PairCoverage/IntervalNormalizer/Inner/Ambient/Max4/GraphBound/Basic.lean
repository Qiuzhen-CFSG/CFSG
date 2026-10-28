module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.Data
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.GraphCardBound.Separation
public import Mathlib.GroupTheory.Index

/-!
# Colored refinement and the four-point stabilizer chain

The colors here are the literal tables in `Max4.Data`. Combining them with
adjacencies to fixed vertices, then taking neighbor sums, gives invariant
cells. Orbit–stabilizer and the established four-point graph base multiply
their sizes. An odd symmetry halves the full colored-group bound.

Source context: the concrete ATLAS Held max4 calculation for GLS3 Table 5.3p.
No orbit-size identification or global automorphism-group theorem is used.
-/

namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.GraphBound
open Held.NormalizerGraph Held.NormalizerGraph.CardBound

/-- A kernel-reducible finite traversal with a fixed predicate. -/
@[expose] public def allUpTo (f : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => allUpTo f n && f n

private theorem allUpTo_eq_true (f : ℕ → Bool) (n : ℕ) :
    allUpTo f n = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [allUpTo]
  | succ n ih =>
    simp only [allUpTo, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h, hn⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h i hi
      · exact hn
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h n (Nat.lt_succ_self n)⟩

@[expose] public def vertex (i : ℕ) : Fin 2058 :=
  ⟨i % 2058, Nat.mod_lt _ (by decide)⟩

/-- Linear traversal checks the same finite universal proposition. -/
public theorem checked_forall (P : Fin 2058 → Prop) [DecidablePred P]
    (h : allUpTo (fun i => decide (P (vertex i))) 2058 = true) : ∀ x, P x := by
  intro x
  have hx := of_decide_eq_true ((allUpTo_eq_true _ _).mp h x.val x.isLt)
  simpa only [vertex, Nat.mod_eq_of_lt x.isLt] using hx

/-- Check a block of adjacency rows using two linear traversals. -/
public theorem checked_pairs (P : Fin 2058 → Fin 2058 → Prop)
    [∀ x y, Decidable (P x y)] (lo hi : ℕ)
    (h : allUpTo (fun i =>
      if lo ≤ i ∧ i < hi then
        allUpTo (fun k => decide (P (vertex i) (vertex k))) 2058
      else true) 2058 = true) :
    ∀ x : Fin 2058, lo ≤ x.val → x.val < hi → ∀ y, P x y := by
  intro x hl hu y
  have hx := (allUpTo_eq_true _ _).mp h x.val x.isLt
  rw [if_pos ⟨hl, hu⟩] at hx
  have hy := of_decide_eq_true ((allUpTo_eq_true _ _).mp hx y.val y.isLt)
  simpa only [vertex, Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt] using hy

@[expose] public def ColoredInvariant (j : Fin 7) (n : ℕ) (w : ℕ → ℕ) : Prop :=
  ∀ σ ∈ coloredGraphGroup j, Fixes n σ → ∀ x, w (σ x).val = w x.val

public theorem base_invariant {j : Fin 7} {n : ℕ}
    (bs : List (Fin 2058)) (hb : ∀ b ∈ bs, b.val < n)
    (w decode : ℕ → ℕ)
    (hc : ∀ x : Fin 2058,
      w x.val = decode (orbitSizeLabel j x + 1024 * baseSignature bs x)) :
    ColoredInvariant j n w := by
  intro σ hσ hf x
  rw [hc, hc, hσ.2 x,
    baseSignature_invariant bs σ hσ.1 (fun b h => hf b (hb b h))]

/-- Only the selected old cell needs a neighbor-sum check. -/
public theorem narrow_invariant {j : Fin 7} {n : ℕ} {w v : ℕ → ℕ}
    (hw : ColoredInvariant j n w) (a s : ℕ)
    (hc : ∀ x : Fin 2058,
      v x.val = if w x.val = a ∧ sumBits w (rowMask x) 2058 = s then 1 else 0) :
    ColoredInvariant j n v := by
  intro σ hσ hf x
  rw [hc, hc, hw σ hσ hf x,
    sumBits_invariant w σ hσ.1 (hw σ hσ hf) x]

private abbrev S0 (j : Fin 7) := ↥(coloredGraphGroup j)
private abbrev S1 (j : Fin 7) := ↥(MulAction.stabilizer (S0 j) (0 : Fin 2058))
private abbrev S2 (j : Fin 7) := ↥(MulAction.stabilizer (S1 j) (1 : Fin 2058))
private abbrev S3 (j : Fin 7) := ↥(MulAction.stabilizer (S2 j) (2 : Fin 2058))
private abbrev S4 (j : Fin 7) := ↥(MulAction.stabilizer (S3 j) (3 : Fin 2058))

private theorem fix1 {j : Fin 7} (g : S1 j) : Fixes 1 g.val.val := by
  intro x hx
  have he : x = 0 := Fin.ext (by omega)
  subst x
  exact g.property

private theorem fix2 {j : Fin 7} (g : S2 j) : Fixes 2 g.val.val.val := by
  intro x hx
  by_cases h : x.val < 1
  · exact fix1 g.val x h
  · have he : x = 1 := Fin.ext (by omega)
    subst x
    exact g.property

private theorem fix3 {j : Fin 7} (g : S3 j) : Fixes 3 g.val.val.val.val := by
  intro x hx
  by_cases h : x.val < 2
  · exact fix2 g.val x h
  · have he : x = 2 := Fin.ext (by omega)
    subst x
    exact g.property

private theorem fix4 {j : Fin 7} (g : S4 j) : Fixes 4 g.val.val.val.val.val := by
  intro x hx
  by_cases h : x.val < 3
  · exact fix3 g.val x h
  · have he : x = 3 := Fin.ext (by omega)
    subst x
    exact g.property

public theorem card_le_of_cells (j : Fin 7) (w : Fin 4 → ℕ → ℕ) (c : Fin 4 → ℕ)
    (hw : ∀ n, ColoredInvariant j n.val (w n))
    (hc : ∀ n, Nat.card {x : Fin 2058 // w n x.val = w n n.val} ≤ c n) :
    Nat.card (coloredGraphGroup j) ≤ c 0 * (c 1 * (c 2 * c 3)) := by
  have h4 : Nat.card (S4 j) = 1 := by
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨1, fun g => ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact four_fixed_eq_one _ g.val.val.val.val.property.1 (fix4 g)
  have h3 : Nat.card (S3 j) ≤ c 3 * Nat.card (S4 j) :=
    orbit_upper (3 : Fin 2058) (fun x => w 3 x.val)
      (fun g x => hw 3 _ g.val.val.val.property (fix3 g) x) (hc 3)
  have h2 : Nat.card (S2 j) ≤ c 2 * Nat.card (S3 j) :=
    orbit_upper (2 : Fin 2058) (fun x => w 2 x.val)
      (fun g x => hw 2 _ g.val.val.property (fix2 g) x) (hc 2)
  have h1 : Nat.card (S1 j) ≤ c 1 * Nat.card (S2 j) :=
    orbit_upper (1 : Fin 2058) (fun x => w 1 x.val)
      (fun g x => hw 1 _ g.val.property (fix1 g) x) (hc 1)
  have h0 : Nat.card (S0 j) ≤ c 0 * Nat.card (S1 j) :=
    orbit_upper (0 : Fin 2058) (fun x => w 0 x.val)
      (fun g x => hw 0 _ g.property (by intro x hx; omega) x) (hc 0)
  rw [h4, mul_one] at h3
  exact h0.trans (Nat.mul_le_mul_left _
    (h1.trans (Nat.mul_le_mul_left _ (h2.trans (Nat.mul_le_mul_left _ h3)))))

public theorem even_card_le (j : Fin 7) :
    Nat.card (evenColoredGraphGroup j) ≤ Nat.card (coloredGraphGroup j) :=
  Nat.card_le_card_of_injective
    (Subgroup.inclusion (show evenColoredGraphGroup j ≤ coloredGraphGroup j from inf_le_left))
    (Subgroup.inclusion_injective _)

public theorem even_card_le_of_odd (j : Fin 7)
    (hcard : Nat.card (coloredGraphGroup j) ≤ 2048)
    (σ : Equiv.Perm (Fin 2058)) (hσ : σ ∈ coloredGraphGroup j)
    (hodd : Equiv.Perm.sign σ ≠ 1) : Nat.card (evenColoredGraphGroup j) ≤ 1024 := by
  let E := (evenColoredGraphGroup j).subgroupOf (coloredGraphGroup j)
  have hproper : E ≠ ⊤ := by
    intro he
    have hm : (⟨σ, hσ⟩ : coloredGraphGroup j) ∈ E := he ▸ Subgroup.mem_top _
    exact hodd hm.2
  have hi : 2 ≤ E.index := E.one_lt_index_of_ne_top hproper
  have he : Nat.card E = Nat.card (evenColoredGraphGroup j) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show evenColoredGraphGroup j ≤ coloredGraphGroup j from inf_le_left)).toEquiv
  have hb : Nat.card (evenColoredGraphGroup j) * 2 ≤ Nat.card (coloredGraphGroup j) := by
    rw [← he, ← E.card_mul_index]
    exact Nat.mul_le_mul_left _ hi
  omega

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.GraphBound
