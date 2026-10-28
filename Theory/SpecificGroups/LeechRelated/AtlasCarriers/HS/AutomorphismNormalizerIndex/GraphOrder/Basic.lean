module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.Graph
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Counting graph automorphisms by invariant colors

A permutation preserving adjacency also preserves the weighted neighbor-color
sum. Individualization restricts to a point stabilizer, and refinement preserves
invariance. Orbit–stabilizer bounds each index by the size of the pivot's color
class; an injective final coloring forces the last stabilizer to be trivial.

These elementary counting tools are used for the explicit HS graph associated
with GLS3, Table 5.3m (printed p.274). The weights need not encode counts
injectively: the finite refinement checks separately prove discrimination.
-/

@[expose] public section

namespace Sporadic.LeechRelated.HS.NormalizerIndex.GraphOrder

/-- The pointwise stabilizer of a list of vertices in the full graph group. -/
def fixing (xs : List (Fin 100)) : Subgroup (Equiv.Perm (Fin 100)) where
  carrier := {g | g ∈ graphGroup ∧ ∀ x ∈ xs, g x = x}
  one_mem' := ⟨graphGroup.one_mem, fun _ _ => rfl⟩
  mul_mem' := by
    rintro g h ⟨hg, hx⟩ ⟨hh, hy⟩
    exact ⟨graphGroup.mul_mem hg hh, fun x hmem => by
      change g (h x) = x
      rw [hy x hmem, hx x hmem]⟩
  inv_mem' := by
    rintro g ⟨hg, hx⟩
    exact ⟨graphGroup.inv_mem hg, fun x hmem => by
      apply g.injective
      simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] using (hx x hmem).symm⟩

theorem mem_fixing (xs : List (Fin 100)) (g : Equiv.Perm (Fin 100)) :
    g ∈ fixing xs ↔ g ∈ graphGroup ∧ ∀ x ∈ xs, g x = x := Iff.rfl

theorem fixing_nil : fixing [] = graphGroup := by
  ext g
  simp only [mem_fixing, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]

def Preserves (xs : List (Fin 100)) (c : Fin 100 → ℕ) : Prop :=
  ∀ g ∈ fixing xs, ∀ x, c (g x) = c x

/-- A weighted encoding of neighbor counts. Its invariance does not require
injectivity of the encoding: discrimination is checked separately. -/
def signature (c : Fin 100 → ℕ) (x : Fin 100) : ℕ :=
  ∑ y : Fin 100, if adjacency x y then 128 ^ c y else 0

theorem signature_invariant (c : Fin 100 → ℕ) (g : Equiv.Perm (Fin 100))
    (hg : g ∈ graphGroup) (hc : ∀ x, c (g x) = c x) (x : Fin 100) :
    signature c (g x) = signature c x := by
  unfold signature
  symm
  apply Fintype.sum_equiv g
  intro y
  simp only [(mem_graphGroup_iff g).mp hg, hc]

theorem preserves_refine {xs : List (Fin 100)} {c d s : Fin 100 → ℕ}
    (hc : Preserves xs c) (hs : ∀ x, signature c x = s x)
    (hd : ∀ x y, c x = c y → s x = s y → d x = d y) : Preserves xs d := by
  intro g hg x
  apply hd (g x) x (hc g hg x)
  rw [← hs, ← hs]
  exact signature_invariant c g hg.1 (hc g hg) x

theorem preserves_individualize {xs : List (Fin 100)} {c d : Fin 100 → ℕ}
    (hc : Preserves xs c) (v : Fin 100)
    (hd : ∀ x y, c x = c y → (x = v ↔ y = v) → d x = d y) :
    Preserves (v :: xs) d := by
  intro g hg x
  have hfix : g v = v := hg.2 v (by simp)
  have hxs : g ∈ fixing xs := ⟨hg.1, fun y hy => hg.2 y (by simp [hy])⟩
  apply hd (g x) x (hc g hxs x)
  exact ⟨fun h => g.injective (h.trans hfix.symm), fun h => h ▸ hfix⟩

def cellSize (c : Fin 100 → ℕ) (v : Fin 100) : ℕ :=
  (Finset.univ.filter (fun x => c x = c v)).card

theorem card_fixing_le {xs : List (Fin 100)} {c : Fin 100 → ℕ}
    (hc : Preserves xs c) (v : Fin 100) :
    Nat.card (fixing xs) ≤ cellSize c v * Nat.card (fixing (v :: xs)) := by
  classical
  let e : MulAction.stabilizer (fixing xs) v ≃ fixing (v :: xs) := {
    toFun := fun g => ⟨g.val.val, g.val.property.1, by
      intro x hx
      rcases List.mem_cons.mp hx with h | h
      · subst x
        exact g.property
      · exact g.val.property.2 x h⟩
    invFun := fun g => ⟨⟨g.val, g.property.1, fun x hx =>
      g.property.2 x (List.mem_cons_of_mem v hx)⟩,
      g.property.2 v (List.mem_cons_self)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have horbit : Nat.card (MulAction.orbit (fixing xs) v) ≤ cellSize c v := by
    let f : MulAction.orbit (fixing xs) v → {x : Fin 100 // c x = c v} := fun x =>
      ⟨x.val, by
        obtain ⟨g, hg⟩ := x.property
        rw [← hg]
        exact hc g.val g.property v⟩
    have h := Nat.card_le_card_of_injective f (by
      intro x y h
      exact Subtype.ext (congrArg (fun z : {x : Fin 100 // c x = c v} => z.val) h))
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, cellSize] using h
  calc
    Nat.card (fixing xs) =
        Nat.card (MulAction.orbit (fixing xs) v) *
          Nat.card (MulAction.stabilizer (fixing xs) v) :=
      (Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (fixing xs) v)).symm.trans
        (Nat.card_prod _ _)
    _ ≤ cellSize c v * Nat.card (fixing (v :: xs)) := by
      rw [Nat.card_congr e]
      exact Nat.mul_le_mul_right _ horbit

theorem card_fixing_eq_one {xs : List (Fin 100)} {c : Fin 100 → ℕ}
    (hc : Preserves xs c) (hinj : Function.Injective c) : Nat.card (fixing xs) = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨1, ?_⟩
  intro g
  apply Subtype.ext
  apply Equiv.ext
  intro x
  exact hinj (hc g.val g.property x)

end Sporadic.LeechRelated.HS.NormalizerIndex.GraphOrder
