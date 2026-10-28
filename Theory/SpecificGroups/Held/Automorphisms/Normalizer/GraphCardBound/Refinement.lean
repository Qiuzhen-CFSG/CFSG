module

public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.GraphData
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.Fintype.Card
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Refinement and orbit bounds for the Held relation

A weight preserved by a graph permutation has a preserved neighbor sum.
Thus any explicitly checked function of the old weight and neighbor sum is
another invariant. Singleton weight classes supply fixed points; their
adjacency signatures can certify that a pointwise stabilizer is trivial.
The final cardinal estimate is the ordinary orbit–stabilizer theorem.

These arguments apply to the full relation-preserving group defined in
`GraphData`; they use neither chosen generators nor orbital identification.
-/

namespace Held.NormalizerGraph.CardBound

public section

open scoped BigOperators

@[expose] def sumBits (w : ℕ → ℕ) (mask : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumBits w mask n + if mask.testBit n then w n else 0

lemma sumBits_eq (w : ℕ → ℕ) (mask n : ℕ) :
    sumBits w mask n = ∑ i ∈ Finset.range n, if mask.testBit i then w i else 0 := by
  induction n with
  | zero => simp [sumBits]
  | succ n ih => simp [sumBits, Finset.sum_range_succ, ih]


lemma sumBits_invariant (w : ℕ → ℕ) (σ : Equiv.Perm (Fin 2058))
    (hσ : σ ∈ preservingGroup) (hw : ∀ x, w (σ x).val = w x.val) (x : Fin 2058) :
    sumBits w (rowMask (σ x)) 2058 = sumBits w (rowMask x) 2058 := by
  rw [sumBits_eq, sumBits_eq]
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  symm
  apply Fintype.sum_equiv σ
  intro y
  have he : (rowMask (σ x)).testBit (σ y).val = (rowMask x).testBit y.val := by
    apply Bool.eq_iff_iff.mpr
    exact hσ x y
  simp only [he, hw]

@[expose] def baseSignature : List (Fin 2058) → Fin 2058 → ℕ
 | [], _ => 0
 | b :: bs, x => 4 * baseSignature bs x + if x = b then 2 else if Adj x b then 1 else 0

lemma baseSignature_invariant (bs : List (Fin 2058)) (σ : Equiv.Perm (Fin 2058))
 (hσ : σ ∈ preservingGroup) (hfix : ∀ b ∈ bs, σ b = b) (x : Fin 2058) :
 baseSignature bs (σ x) = baseSignature bs x := by
 induction bs with
 | nil => rfl
 | cons b bs ih =>
   have hb : σ b = b := hfix b (by simp)
   have he : σ x = b ↔ x = b := by simpa only [hb] using (σ.injective.eq_iff (a := x) (b := b))
   have ha : Adj (σ x) b ↔ Adj x b := by simpa only [hb] using hσ x b
   simp only [baseSignature, ih (fun c hc => hfix c (by simp [hc])), he, ha]

@[expose] def Fixes (n : ℕ) (σ : Equiv.Perm (Fin 2058)) : Prop :=
 ∀ x, x.val < n → σ x = x

@[expose] def Invariant (n : ℕ) (w : ℕ → ℕ) : Prop :=
 ∀ σ ∈ preservingGroup, Fixes n σ → ∀ x, w (σ x).val = w x.val

@[expose] def signature (w : ℕ → ℕ) (x : Fin 2058) : ℕ :=
 w x.val + 2^64 * sumBits w (rowMask x) 2058

lemma signature_invariant {n : ℕ} {w : ℕ → ℕ} (hw : Invariant n w)
 (σ : Equiv.Perm (Fin 2058)) (hσ : σ ∈ preservingGroup) (hf : Fixes n σ)
 (x : Fin 2058) : signature w (σ x) = signature w x := by
 unfold signature
 rw [hw σ hσ hf x, sumBits_invariant w σ hσ (hw σ hσ hf) x]

lemma refined_invariant {n : ℕ} {w v : ℕ → ℕ} (hw : Invariant n w)
 (decode : ℕ → ℕ) (hc : ∀ x : Fin 2058, v x.val = decode (signature w x)) :
 Invariant n v := by
 intro σ hσ hf x
 rw [hc, hc, signature_invariant hw σ hσ hf]

lemma base_invariant {n : ℕ} (bs : List (Fin 2058)) (hb : ∀ b ∈ bs, b.val < n)
 (w decode : ℕ → ℕ) (hc : ∀ x : Fin 2058, w x.val = decode (baseSignature bs x)) :
 Invariant n w := by
 intro σ hσ hf x
 rw [hc, hc, baseSignature_invariant bs σ hσ (fun b h => hf b (hb b h))]

lemma cell_card (w : ℕ → ℕ) (b : Fin 2058) :
 Nat.card {x : Fin 2058 // w x.val = w b.val} =
 (List.finRange 2058).countP (fun x => w x.val == w b.val) := by
 rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
   ← List.toFinset_finRange 2058, (List.nodup_finRange 2058).card_eq_countP]
 rfl

lemma orbit_upper {G X : Type*} [Group G] [MulAction G X] [Finite G] [Finite X]
 (b : X) (w : X → ℕ) (hw : ∀ g : G, ∀ x, w (g • x) = w x) {m : ℕ}
 (hc : Nat.card {x // w x = w b} ≤ m) :
 Nat.card G ≤ m * Nat.card (MulAction.stabilizer G b) := by
 have ho : Nat.card (MulAction.orbit G b) ≤ m := by
   apply (Nat.card_le_card_of_injective
     (fun x : MulAction.orbit G b => (⟨x.val, ?_⟩ : {x // w x = w b}))
     (fun x y h => Subtype.ext (congrArg (fun z : {x // w x = w b} => z.val) h))).trans hc
   obtain ⟨g, hg⟩ := x.property
   rw [← hg, hw]
 have he := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G b)
 rw [Nat.card_prod] at he
 rw [← he]
 exact Nat.mul_le_mul_right _ ho

/-- A separating adjacency certificate kills the entire pointwise stabilizer. -/
lemma fixes_eq_one {w : ℕ → ℕ} (hw : Invariant 4 w)
    (bs : List (Fin 2058))
    (hs : ∀ b ∈ bs, ∀ x : Fin 2058, w x.val = w b.val → x = b)
    (decode : ℕ → ℕ)
    (hc : ∀ x : Fin 2058,
      decode (w x.val + 2^64 * baseSignature bs x) = x.val)
    (σ : Equiv.Perm (Fin 2058)) (hσ : σ ∈ preservingGroup) (hf : Fixes 4 σ) :
    σ = 1 := by
  have hbs : ∀ b ∈ bs, σ b = b := fun b hb => hs b hb (σ b) (hw σ hσ hf b)
  apply Equiv.ext
  intro x
  apply Fin.ext
  change (σ x).val = x.val
  rw [← hc (σ x), ← hc x, hw σ hσ hf x,
    baseSignature_invariant bs σ hσ hbs x]

end

end Held.NormalizerGraph.CardBound
