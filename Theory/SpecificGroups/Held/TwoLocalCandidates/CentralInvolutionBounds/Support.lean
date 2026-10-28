module
public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Tables2
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.GraphCardBound.Refinement
/-!
# Invariants for graph automorphisms commuting with the max5 involution

A commuting permutation preserves fixed points and adjacency to the involution
image. Fixing a base also fixes its involution image. These signatures and the
existing neighbor-sum invariant yield orbit bounds and detect a trivial final
stabilizer. All statements concern the full preserving group of the exact
published relation. Source lead: GLS3 Table 5.3p.
-/
namespace Held.TwoLocalCandidates.CentralInvolutionBounds
open Cores.Tables2 NormalizerGraph NormalizerGraph.CardBound
public section
@[expose] def graphCentralizer : Subgroup (Equiv.Perm (Fin 2058)) :=
  preservingGroup ⊓ Subgroup.centralizer ({p2} : Set (Equiv.Perm (Fin 2058)))
@[expose] def Invariant (bs : List (Fin 2058)) (w : ℕ → ℕ) : Prop :=
  ∀ σ ∈ graphCentralizer, (∀ b ∈ bs, σ b = b) → ∀ x, w (σ x).val = w x.val
lemma commutes_point (σ : Equiv.Perm (Fin 2058)) (hσ : σ ∈ graphCentralizer)
    (x : Fin 2058) : p2 (σ x) = σ (p2 x) :=
  congrArg (fun p : Equiv.Perm (Fin 2058) => p x)
    (Subgroup.mem_centralizer_singleton_iff.mp hσ.2).symm
@[expose] def initial (bs : List (Fin 2058)) (x : Fin 2058) : ℕ :=
  (if p2 x = x then 2 else if Adj x (p2 x) then 1 else 0) +
    4 * baseSignature (bs ++ bs.map p2) x
lemma initial_invariant (bs : List (Fin 2058))
    (σ : Equiv.Perm (Fin 2058)) (hσ : σ ∈ graphCentralizer)
    (hf : ∀ b ∈ bs, σ b = b) (x : Fin 2058) :
    initial bs (σ x) = initial bs x := by
  have he : p2 (σ x) = σ x ↔ p2 x = x := by
    rw [commutes_point σ hσ]
    exact σ.injective.eq_iff
  have ha : Adj (σ x) (p2 (σ x)) ↔ Adj x (p2 x) := by
    rw [commutes_point σ hσ]
    exact hσ.1 x (p2 x)
  have hbs : ∀ b ∈ bs ++ bs.map p2, σ b = b := by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hf b hb
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
      rw [← commutes_point σ hσ, hf c hc]
  simp only [initial, he, ha, baseSignature_invariant _ σ hσ.1 hbs]
lemma initial_labels_invariant (bs : List (Fin 2058)) (w decode : ℕ → ℕ)
    (hc : ∀ x : Fin 2058, w x.val = decode (initial bs x)) : Invariant bs w := by
  intro σ hσ hf x
  rw [hc, hc, initial_invariant bs σ hσ hf]
@[expose] def signature (w : ℕ → ℕ) (x : Fin 2058) : ℕ :=
  w x.val + 2^16 * w (p2 x).val + 2^32 * sumBits w (rowMask x) 2058
lemma refined_invariant {bs : List (Fin 2058)} {w v : ℕ → ℕ}
    (hw : Invariant bs w) (decode : ℕ → ℕ)
    (hc : ∀ x : Fin 2058, v x.val = decode (signature w x)) : Invariant bs v := by
  intro σ hσ hf x
  rw [hc, hc]
  congr 1
  unfold signature
  rw [hw σ hσ hf x, commutes_point σ hσ, hw σ hσ hf (p2 x),
    sumBits_invariant w σ hσ.1 (hw σ hσ hf) x]
lemma discrete_eq_one {bs : List (Fin 2058)} {w : ℕ → ℕ}
    (hw : Invariant bs w) (decode : ℕ → ℕ)
    (hc : ∀ x : Fin 2058, decode (w x.val) = x.val)
    (σ : Equiv.Perm (Fin 2058)) (hσ : σ ∈ graphCentralizer)
    (hf : ∀ b ∈ bs, σ b = b) : σ = 1 := by
  apply Equiv.ext
  intro x
  apply Fin.ext
  change (σ x).val = x.val
  rw [← hc (σ x), ← hc x, hw σ hσ hf x]
end
end Held.TwoLocalCandidates.CentralInvolutionBounds
