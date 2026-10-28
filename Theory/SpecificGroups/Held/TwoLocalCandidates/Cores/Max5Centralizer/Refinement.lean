module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Max5Centralizer.Action
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.GraphCardBound.Refinement

/-!
# Color transport for the graph centralizer of Held's max5 core

Commuting graph permutations preserve the equality and adjacency patterns
of the seven actors. A transported color has transported actor colors and
neighbor sums, so checked decoding tables provide successive refinements.
Two different individualized copies can be compared by the same argument:
their color histograms must agree. A discrete transported color forces the
permutation to be the identity.

These are soundness lemmas for finite certificates, independent of any
unproved numerical output. Source: the concrete graph and core action
used for GLS3 Table 5.3p's extraspecial Held centralizer.
-/

namespace Held.TwoLocalCandidates.Cores.Max5Centralizer
open Held.NormalizerGraph

open scoped BigOperators
open Held.NormalizerGraph.CardBound

/-- A color correspondence, also for two differently individualized copies. -/
@[expose] public def Transports (σ : Equiv.Perm (Fin 2058)) (w v : ℕ → ℕ) : Prop :=
  ∀ x : Fin 2058, v (σ x).val = w x.val

@[expose] public def Invariant (w : ℕ → ℕ) : Prop :=
  ∀ σ ∈ graphCentralizer, Transports σ w w

@[expose] public def initialSignature (js : List (Fin 7)) (x : Fin 2058) : ℕ :=
  match js with
  | [] => 0
  | j :: js => 4 * initialSignature js x +
      (if actor j x = x then 2 else 0) + (if Adj x (actor j x) then 1 else 0)

public theorem initialSignature_invariant (σ : Equiv.Perm (Fin 2058))
    (hσ : σ ∈ graphCentralizer) (js : List (Fin 7)) (x : Fin 2058) :
    initialSignature js (σ x) = initialSignature js x := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    have he : actor j (σ x) = σ x ↔ actor j x = x := by
      rw [← actor_commutes σ hσ j, σ.injective.eq_iff]
    have ha : Adj (σ x) (actor j (σ x)) ↔ Adj x (actor j x) := by
      rw [← actor_commutes σ hσ j]
      exact hσ.1 x (actor j x)
    simp only [initialSignature, ih, he, ha]

@[expose] public def actorSignature (w : ℕ → ℕ) (js : List (Fin 7))
    (x : Fin 2058) : ℕ :=
  match js with
  | [] => 0
  | j :: js => w (actor j x).val + 2^32 * actorSignature w js x

public theorem actorSignature_transport (σ : Equiv.Perm (Fin 2058))
    (hσ : σ ∈ graphCentralizer) {w v : ℕ → ℕ} (hw : Transports σ w v)
    (js : List (Fin 7)) (x : Fin 2058) :
    actorSignature v js (σ x) = actorSignature w js x := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    simp only [actorSignature, ← actor_commutes σ hσ j, hw _, ih]

public theorem sumBits_transport (σ : Equiv.Perm (Fin 2058))
    (hσ : σ ∈ preservingGroup) {w v : ℕ → ℕ} (hw : Transports σ w v)
    (x : Fin 2058) :
    sumBits v (rowMask (σ x)) 2058 = sumBits w (rowMask x) 2058 := by
  rw [sumBits_eq, sumBits_eq]
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  symm
  apply Fintype.sum_equiv σ
  intro y
  have he : (rowMask (σ x)).testBit (σ y).val = (rowMask x).testBit y.val := by
    apply Bool.eq_iff_iff.mpr
    exact hσ x y
  simp only [he, hw _]

@[expose] public def signature (w : ℕ → ℕ) (x : Fin 2058) : ℕ :=
  w x.val + 2^32 * actorSignature w (List.finRange 7) x +
    2^256 * sumBits w (rowMask x) 2058

public theorem signature_transport (σ : Equiv.Perm (Fin 2058))
    (hσ : σ ∈ graphCentralizer) {w v : ℕ → ℕ} (hw : Transports σ w v)
    (x : Fin 2058) : signature v (σ x) = signature w x := by
  unfold signature
  rw [hw, actorSignature_transport σ hσ hw, sumBits_transport σ hσ.1 hw]

public theorem decoded_initial (w decode : ℕ → ℕ)
    (hc : ∀ x : Fin 2058, w x.val = decode (initialSignature (List.finRange 7) x)) :
    Invariant w := by
  intro σ hσ x
  rw [hc, hc, initialSignature_invariant σ hσ]

public theorem decoded_transport (σ : Equiv.Perm (Fin 2058))
    (hσ : σ ∈ graphCentralizer) {w v w' v' : ℕ → ℕ} (hw : Transports σ w v)
    (decode : ℕ → ℕ)
    (hc : ∀ x : Fin 2058, w' x.val = decode (signature w x))
    (hd : ∀ x : Fin 2058, v' x.val = decode (signature v x)) :
    Transports σ w' v' := by
  intro x
  rw [hd, hc, signature_transport σ hσ hw]

public theorem decoded_invariant {w v : ℕ → ℕ} (hw : Invariant w)
    (decode : ℕ → ℕ) (hc : ∀ x : Fin 2058, v x.val = decode (signature w x)) :
    Invariant v := fun σ hσ => decoded_transport σ hσ (hw σ hσ) decode hc hc

@[expose] public def markPair (w : ℕ → ℕ) (a b x : Fin 2058) : ℕ :=
  w x.val + (if x = a then 2^32 else 0) + (if x = b then 2^33 else 0)

public theorem markPair_transport (σ : Equiv.Perm (Fin 2058))
    {w v : ℕ → ℕ} (hw : Transports σ w v) (a b x : Fin 2058) :
    markPair v (σ a) (σ b) (σ x) = markPair w a b x := by
  simp only [markPair, hw _, σ.injective.eq_iff]

@[expose] public def colorCount (w : ℕ → ℕ) (c : ℕ) : ℕ :=
  (List.finRange 2058).countP (fun x => w x.val == c)

public theorem colorCount_eq (w : ℕ → ℕ) (c : ℕ) :
    colorCount w c = Nat.card {x : Fin 2058 // w x.val = c} := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    ← List.toFinset_finRange 2058, (List.nodup_finRange 2058).card_eq_countP]
  rfl

public theorem colorCount_transport (σ : Equiv.Perm (Fin 2058))
    {w v : ℕ → ℕ} (hw : Transports σ w v) (c : ℕ) :
    colorCount w c = colorCount v c := by
  rw [colorCount_eq, colorCount_eq]
  apply Nat.card_congr
  exact Equiv.subtypeEquiv σ (fun x => by rw [hw])

public theorem eq_one_of_separating {w : ℕ → ℕ}
    (σ : Equiv.Perm (Fin 2058)) (hw : Transports σ w w)
    (decode : ℕ → ℕ) (hc : ∀ x : Fin 2058, decode (w x.val) = x.val) : σ = 1 := by
  apply Equiv.ext
  intro x
  apply Fin.ext
  change (σ x).val = x.val
  rw [← hc (σ x), hw, hc]

end Held.TwoLocalCandidates.Cores.Max5Centralizer
