module

public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.Data
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.GraphCardBound.Separation

/-!
# Colored refinement and the four-point stabilizer chain

The colors are the literal table in `InnerNormalizer.Data`. Combining them
with adjacencies to fixed vertices, then taking neighbor sums, gives invariant
cells. Orbit–stabilizer and the established four-point graph base multiply
their sizes. An odd symmetry halves the full colored-group bound.

Source context: the ATLAS Held representative calculation for GLS3 Table 5.3p.
No orbit-size identification or global automorphism-group theorem is used.
-/

namespace Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.GraphBound
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

@[expose] public def ColoredInvariant (n : ℕ) (w : ℕ → ℕ) : Prop :=
  ∀ σ ∈ coloredGraphGroup, Fixes n σ → ∀ x, w (σ x).val = w x.val

public theorem base_invariant {n : ℕ}
    (bs : List (Fin 2058)) (hb : ∀ b ∈ bs, b.val < n)
    (w decode : ℕ → ℕ)
    (hc : ∀ x : Fin 2058,
      w x.val = decode (orbitSizeLabel x + 1024 * baseSignature bs x)) :
    ColoredInvariant n w := by
  intro σ hσ hf x
  rw [hc, hc, hσ.2 x,
    baseSignature_invariant bs σ hσ.1 (fun b h => hf b (hb b h))]

private abbrev S0 := ↥coloredGraphGroup
private abbrev S1 := ↥(MulAction.stabilizer S0 (0 : Fin 2058))
private abbrev S2 := ↥(MulAction.stabilizer S1 (1 : Fin 2058))
private abbrev S3 := ↥(MulAction.stabilizer S2 (2 : Fin 2058))
private abbrev S4 := ↥(MulAction.stabilizer S3 (3 : Fin 2058))

private theorem fix1 (g : S1) : Fixes 1 g.val.val := by
  intro x hx
  have he : x = 0 := Fin.ext (by omega)
  subst x
  exact g.property

private theorem fix2 (g : S2) : Fixes 2 g.val.val.val := by
  intro x hx
  by_cases h : x.val < 1
  · exact fix1 g.val x h
  · have he : x = 1 := Fin.ext (by omega)
    subst x
    exact g.property

private theorem fix3 (g : S3) : Fixes 3 g.val.val.val.val := by
  intro x hx
  by_cases h : x.val < 2
  · exact fix2 g.val x h
  · have he : x = 2 := Fin.ext (by omega)
    subst x
    exact g.property

private theorem fix4 (g : S4) : Fixes 4 g.val.val.val.val.val := by
  intro x hx
  by_cases h : x.val < 3
  · exact fix3 g.val x h
  · have he : x = 3 := Fin.ext (by omega)
    subst x
    exact g.property

public theorem card_le_of_cells (w : Fin 4 → ℕ → ℕ) (c : Fin 4 → ℕ)
    (hw : ∀ n, ColoredInvariant n.val (w n))
    (hc : ∀ n, Nat.card {x : Fin 2058 // w n x.val = w n n.val} ≤ c n) :
    Nat.card coloredGraphGroup ≤ c 0 * (c 1 * (c 2 * c 3)) := by
  have h4 : Nat.card S4 = 1 := by
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨1, fun g => ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact four_fixed_eq_one _ g.val.val.val.val.property.1 (fix4 g)
  have h3 : Nat.card S3 ≤ c 3 * Nat.card S4 :=
    orbit_upper (3 : Fin 2058) (fun x => w 3 x.val)
      (fun g x => hw 3 _ g.val.val.val.property (fix3 g) x) (hc 3)
  have h2 : Nat.card S2 ≤ c 2 * Nat.card S3 :=
    orbit_upper (2 : Fin 2058) (fun x => w 2 x.val)
      (fun g x => hw 2 _ g.val.val.property (fix2 g) x) (hc 2)
  have h1 : Nat.card S1 ≤ c 1 * Nat.card S2 :=
    orbit_upper (1 : Fin 2058) (fun x => w 1 x.val)
      (fun g x => hw 1 _ g.val.property (fix1 g) x) (hc 1)
  have h0 : Nat.card S0 ≤ c 0 * Nat.card S1 :=
    orbit_upper (0 : Fin 2058) (fun x => w 0 x.val)
      (fun g x => hw 0 _ g.property (by intro x hx; omega) x) (hc 0)
  rw [h4, mul_one] at h3
  exact h0.trans (Nat.mul_le_mul_left _
    (h1.trans (Nat.mul_le_mul_left _ (h2.trans (Nat.mul_le_mul_left _ h3)))))

end Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.GraphBound
