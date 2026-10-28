module
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.Representative
public import Theory.SpecificGroups.Held.Model.FourPointBase
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.GraphBound.GraphTable

/-!
# Graph invariants for the literal Held outer involution

A permutation commuting with the involution preserves adjacency to its image.
Fixing vertices also fixes their involution images. Counts of neighbors in
complete invariant cells then bound the successive point orbits.
Source: GLS3 Table 5.3p and the unchanged ATLAS HeG1-p2058B0 relation.
-/

@[expose] public section
namespace Held.OuterInvolution.FixedStructure.FixedOrderBound
open Held.NormalizerGraph Held.NormalizerGraph.CardBound
open scoped BigOperators

abbrev involution : Equiv.Perm (Fin 2058) := implementer ^ 5

def graphCentralizer : Subgroup (Equiv.Perm (Fin 2058)) :=
  preservingGroup ⊓ Subgroup.centralizer ({involution} : Set (Equiv.Perm (Fin 2058)))

def Invariant (n : ℕ) (w : ℕ → ℕ) : Prop :=
  ∀ σ ∈ graphCentralizer, Fixes n σ → ∀ x, w (σ x).val = w x.val

theorem commutes_point (σ : Equiv.Perm (Fin 2058)) (hσ : σ ∈ graphCentralizer)
    (x : Fin 2058) : involution (σ x) = σ (involution x) :=
  congrArg (fun p : Equiv.Perm (Fin 2058) => p x)
    (Subgroup.mem_centralizer_singleton_iff.mp hσ.2).symm

def initial (bs : List (Fin 2058)) (x : Fin 2058) : ℕ :=
  (if Adj x (involution x) then 1 else 0) +
    4 * baseSignature (bs ++ bs.map involution) x

theorem initial_invariant (bs : List (Fin 2058))
    (σ : Equiv.Perm (Fin 2058)) (hσ : σ ∈ graphCentralizer)
    (hf : ∀ b ∈ bs, σ b = b) (x : Fin 2058) :
    initial bs (σ x) = initial bs x := by
  have ha : Adj (σ x) (involution (σ x)) ↔ Adj x (involution x) := by
    rw [commutes_point σ hσ]
    exact hσ.1 x (involution x)
  have hbs : ∀ b ∈ bs ++ bs.map involution, σ b = b := by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hf b hb
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
      rw [← commutes_point σ hσ, hf c hc]
  simp only [initial, ha, baseSignature_invariant _ σ hσ.1 hbs]

theorem initial_labels_invariant (n : ℕ) (bs : List (Fin 2058))
    (hb : ∀ b ∈ bs, b.val < n) (w : ℕ → ℕ)
    (hc : ∀ x : Fin 2058, w x.val = initial bs x) : Invariant n w := by
  intro σ hσ hf x
  rw [hc, hc, initial_invariant bs σ hσ (fun b h => hf b (hb b h))]

def neighborCount (S : Finset (Fin 2058)) (x : Fin 2058) : ℕ :=
  ∑ y ∈ S, if Adj x y then 1 else 0

theorem neighborCount_invariant {n : ℕ} {w : ℕ → ℕ}
    (hw : Invariant n w) (S : Finset (Fin 2058)) (a : ℕ)
    (hS : ∀ x, x ∈ S ↔ w x.val = a)
    (σ : Equiv.Perm (Fin 2058)) (hσ : σ ∈ graphCentralizer) (hf : Fixes n σ)
    (x : Fin 2058) : neighborCount S (σ x) = neighborCount S x := by
  unfold neighborCount
  symm
  apply Finset.sum_bij (fun y _ => σ y)
  · intro y hy
    apply (hS _).mpr
    rw [hw σ hσ hf]
    exact (hS _).mp hy
  · intro y _ z _ h
    exact σ.injective h
  · intro y hy
    refine ⟨σ.symm y, ?_, σ.apply_symm_apply y⟩
    apply (hS _).mpr
    have he := hw σ hσ hf (σ.symm y)
    rw [σ.apply_symm_apply] at he
    exact he.symm.trans ((hS _).mp hy)
  · intro y _
    simp only [hσ.1 x y]

theorem narrow_function {n : ℕ} {w v : ℕ → ℕ}
    (hw : Invariant n w) (f : Fin 2058 → ℕ)
    (hf : ∀ σ ∈ graphCentralizer, Fixes n σ → ∀ x, f (σ x) = f x)
    (a s : ℕ)
    (hc : ∀ x : Fin 2058,
      v x.val = if w x.val = a ∧ f x = s then 1 else 0) : Invariant n v := by
  intro σ hσ hfix x
  rw [hc, hc, hw σ hσ hfix x, hf σ hσ hfix x]

public theorem sample_spec_of_count (w : ℕ → ℕ) (a : ℕ)
    (S : Finset (Fin 2058)) (hS : ∀ x ∈ S, w x.val = a)
    (hc : (List.finRange 2058).countP (fun x => w x.val == a) ≤ S.card) :
    ∀ x, x ∈ S ↔ w x.val = a := by
  classical
  let C := Finset.univ.filter (fun x : Fin 2058 => w x.val = a)
  have hsub : S ⊆ C := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS x hx⟩
  have hcard : C.card ≤ S.card := by
    simpa only [C, ← List.toFinset_finRange 2058,
      (List.nodup_finRange 2058).card_eq_countP, Bool.beq_eq_decide_eq] using hc
  have he := Finset.eq_of_subset_of_card_le hsub hcard
  intro x
  rw [he]
  simp [C]

end Held.OuterInvolution.FixedStructure.FixedOrderBound
