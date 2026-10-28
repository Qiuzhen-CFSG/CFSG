module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.Representatives
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.GraphOrder.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Graph bounds for the specified symmetric outer centralizer

We apply individualization and neighbor-color refinement inside the graph
centralizer of `symmetricPermutation`. Its fixed-point coloring is invariant.
The ensuing finite certificate bounds this graph centralizer by 80,640; parity
then bounds its intersection with the actual HS carrier by 40,320.

Source: Aschbacher–Smith 16.1.5(10), printed p.1172; GLS3 Table 5.3m, class 2D.
The graph and its invariance under HS are already kernel certified.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.SymmetricCentralizer.GraphBound

open Sporadic.LeechRelated.HS.NormalizerIndex
open Subgroup

/-- Centralization is imposed in the full graph group, prior to restricting to HS. -/
def graphCentralizer : Subgroup (Equiv.Perm (Fin 100)) :=
  graphGroup ⊓ centralizer ({symmetricPermutation} : Set (Equiv.Perm (Fin 100)))

/-- The pointwise stabilizer of a list of vertices in the full graph group. -/
def fixing (xs : List (Fin 100)) : Subgroup (Equiv.Perm (Fin 100)) where
  carrier := {g | g ∈ graphCentralizer ∧ ∀ x ∈ xs, g x = x}
  one_mem' := ⟨graphCentralizer.one_mem, fun _ _ => rfl⟩
  mul_mem' := by
    rintro g h ⟨hg, hx⟩ ⟨hh, hy⟩
    exact ⟨graphCentralizer.mul_mem hg hh, fun x hmem => by
      change g (h x) = x
      rw [hy x hmem, hx x hmem]⟩
  inv_mem' := by
    rintro g ⟨hg, hx⟩
    exact ⟨graphCentralizer.inv_mem hg, fun x hmem => by
      apply g.injective
      simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] using (hx x hmem).symm⟩

theorem mem_fixing (xs : List (Fin 100)) (g : Equiv.Perm (Fin 100)) :
    g ∈ fixing xs ↔ g ∈ graphCentralizer ∧ ∀ x ∈ xs, g x = x := Iff.rfl

theorem fixing_nil : fixing [] = graphCentralizer := by
  ext g
  simp only [mem_fixing, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]

def Preserves (xs : List (Fin 100)) (c : Fin 100 → ℕ) : Prop :=
  ∀ g ∈ fixing xs, ∀ x, c (g x) = c x

theorem preserves_refine {xs : List (Fin 100)} {c d s : Fin 100 → ℕ}
    (hc : Preserves xs c) (hs : ∀ x, GraphOrder.signature c x = s x)
    (hd : ∀ x y, c x = c y → s x = s y → d x = d y) : Preserves xs d := by
  intro g hg x
  apply hd (g x) x (hc g hg x)
  rw [← hs, ← hs]
  exact GraphOrder.signature_invariant c g hg.1.1 (hc g hg) x

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

/-- Whether a vertex is fixed by the specified outer involution. -/
def initialColor (x : Fin 100) : ℕ := if symmetricPermutation x = x then 1 else 0

theorem initialColor_preserved : Preserves [] initialColor := by
  intro g hg x
  have hcomm : symmetricPermutation * g = g * symmetricPermutation :=
    hg.1.2 symmetricPermutation (Set.mem_singleton _)
  have hval := congrArg (fun p : Equiv.Perm (Fin 100) => p x) hcomm
  change symmetricPermutation (g x) = g (symmetricPermutation x) at hval
  have hfix : symmetricPermutation (g x) = g x ↔ symmetricPermutation x = x := by
    rw [hval]
    exact g.injective.eq_iff
  simp only [initialColor, hfix]

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.SymmetricCentralizer.GraphBound
