module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules.LocalData
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Endpoint highest-vector support in binary SL₄

The four shortest exchange translates of an endpoint highest vector span
an invariant subspace. The inactive-root equations control the exchanges;
the active three-term equation controls one transvection. Conjugation and
transvection generation then give invariance under the whole matrix group.
For an irreducible module this proves dimension at most four.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
G.9.3(11)--(12), printed pp.354,356--357. The elementary root proofs adapt
the binary SL₅ highest-vector development in this repository to rank three.
-/

@[expose] public section

open Representation
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
-- Index the first and last simple roots by zero and one.
private def endpointRoot (e : Fin 2) : Fin 3 := if e = 0 then 0 else 2
private def endpointBase (e : Fin 2) : Fin 4 := if e = 0 then 0 else 3
private def endpointNeighbor (e : Fin 2) : Fin 4 := if e = 0 then 1 else 2
-- Minimal exchange words moving the distinguished endpoint coordinate.
private def endpointWord (e : Fin 2) (k : Fin 4) : List (Fin 3) :=
  if e = 0 then ![[], [0], [1, 0], [2, 1, 0]] k
  else ![[0, 1, 2], [1, 2], [2], []] k
private def wordElement (w : List (Fin 3)) : Group := (w.map simpleSwap).prod
private def endpointRep (e : Fin 2) (k : Fin 4) : Group := wordElement (endpointWord e k)
set_option maxRecDepth 4000
set_option maxHeartbeats 4000000
private theorem endpointRep_base : ∀ e, endpointRep e (endpointBase e) = 1 := by decide
private theorem endpointRep_neighbor : ∀ e,
    endpointRep e (endpointNeighbor e) = simpleSwap (endpointRoot e) := by decide
-- Modulo a single inactive exchange, an adjacent exchange permutes the four words.
private theorem endpoint_swap_action : ∀ (e : Fin 2) (j : Fin 3) (k : Fin 4),
    (∃ l : Fin 4, simpleSwap j * endpointRep e k = endpointRep e l) ∨
    (∃ r : Fin 3, r ≠ endpointRoot e ∧
      simpleSwap j * endpointRep e k = endpointRep e k * simpleSwap r) := by decide
-- Away from the neighboring coordinate, conjugation leaves an upper root.
private theorem endpoint_upper_action : ∀ (e : Fin 2) (k : Fin 4),
    k ≠ endpointNeighbor e → ∃ j : Fin 3,
      simpleUpper (endpointRoot e) * endpointRep e k = endpointRep e k * simpleUpper j := by
  decide
private theorem upper_swap : ∀ i,
    simpleUpper i * simpleSwap i = simpleSwap i * simpleLower i := by decide
-- Each word sends the two coordinates of the active upper root to `a` and `b`.
-- Diagonal entries of the table are unused. The reverse word is the inverse.
private def conjugatorWord (e : Fin 2) (a b : Fin 4) : List (Fin 3) :=
  if e = 0 then
    ![![[], [], [1], [2, 1]],
    ![[0], [], [0, 1], [2, 0, 1]],
    ![[1, 0], [0, 1, 0], [], [1, 2, 0, 1]],
    ![[2, 1, 0], [2, 0, 1, 0], [1, 2, 0, 1, 0], []]] a b
  else
    ![![[], [1, 2, 0, 1], [2, 0, 1], [0, 1]],
    ![[0, 1, 2, 0, 1], [], [2, 1], [1]],
    ![[0, 1, 2, 1], [1, 2, 1], [], []],
    ![[0, 1, 2], [1, 2], [2], []]] a b
private theorem transvection_conjugate : ∀ (e : Fin 2) (a b : Fin 4) (hab : a ≠ b),
    Matrix.SpecialLinearGroup.transvection hab (1 : ZMod 2) =
      wordElement (conjugatorWord e a b) * simpleUpper (endpointRoot e) *
        wordElement (conjugatorWord e a b).reverse := by decide

set_option maxRecDepth 1000
set_option maxHeartbeats 200000

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem endpoint_span_eq_top
    {ρ : Representation (ZMod 2) Group V} [IsIrreducible ρ]
    {v : V} (e : Fin 2) (h : LocalHighestVector ρ {endpointRoot e} v) (hv : v ≠ 0) :
    Submodule.span (ZMod 2) (Set.range (fun k => ρ (endpointRep e k) v)) = ⊤ := by
  let W := Submodule.span (ZMod 2) (Set.range (fun k => ρ (endpointRep e k) v))
  have hmem (k : Fin 4) : ρ (endpointRep e k) v ∈ W :=
    Submodule.subset_span ⟨k, rfl⟩
  have hvW : v ∈ W := by
    simpa only [endpointRep_base, map_one, Module.End.one_apply] using hmem (endpointBase e)
  have hsW : ρ (simpleSwap (endpointRoot e)) v ∈ W := by
    simpa only [endpointRep_neighbor] using hmem (endpointNeighbor e)
  let stable (g : Group) : Prop := ∀ x ∈ W, ρ g x ∈ W
  have extend (g : Group) (hg : ∀ k, ρ g (ρ (endpointRep e k) v) ∈ W) : stable g := by
    intro x hx
    exact (Submodule.span_le.mpr (by
      rintro _ ⟨k, rfl⟩
      exact hg k) : W ≤ W.comap (ρ g)) hx
  have hswap (j : Fin 3) : stable (simpleSwap j) := by
    apply extend
    intro k
    change (ρ (simpleSwap j) * ρ (endpointRep e k)) v ∈ W
    rw [← map_mul]
    rcases endpoint_swap_action e j k with ⟨l, hl⟩ | ⟨r, hr, heq⟩
    · rw [hl]
      exact hmem l
    · rw [heq, map_mul]
      change ρ (endpointRep e k) (ρ (simpleSwap r) v) ∈ W
      rw [h.inactive_fixed r (by simpa using hr)]
      exact hmem k
  have hupper : stable (simpleUpper (endpointRoot e)) := by
    apply extend
    intro k
    by_cases hk : k = endpointNeighbor e
    · subst k
      rw [endpointRep_neighbor]
      change (ρ (simpleUpper (endpointRoot e)) * ρ (simpleSwap (endpointRoot e))) v ∈ W
      rw [← map_mul, upper_swap, map_mul]
      change ρ (simpleSwap (endpointRoot e)) (ρ (simpleLower (endpointRoot e)) v) ∈ W
      apply hswap
      have hr := h.active_relation (endpointRoot e) (Finset.mem_singleton_self _)
      have heq : ρ (simpleLower (endpointRoot e)) v = -(v + ρ (simpleSwap (endpointRoot e)) v) :=
        eq_neg_of_add_eq_zero_right hr
      rw [heq]
      exact W.neg_mem (W.add_mem hvW hsW)
    · obtain ⟨j, hj⟩ := endpoint_upper_action e k hk
      change (ρ (simpleUpper (endpointRoot e)) * ρ (endpointRep e k)) v ∈ W
      rw [← map_mul, hj, map_mul]
      change ρ (endpointRep e k) (ρ (simpleUpper j) v) ∈ W
      have hu : ρ (simpleUpper j) v = v :=
        h.upper_fixed j.castSucc j.succ (by simp)
      rw [hu]
      exact hmem k
  have hone : stable 1 := by intro x hx; simpa using hx
  have hmul (g k : Group) (hg : stable g) (hk : stable k) : stable (g * k) := by
    intro x hx
    rw [map_mul]
    exact hg _ (hk x hx)
  have hword (w : List (Fin 3)) : stable (wordElement w) := by
    induction w with
    | nil => exact hone
    | cons j w ih => exact hmul _ _ (hswap j) ih
  have hall (g : Group) : stable g := by
    apply Matrix.SpecialLinearGroup.diagonal_transvection_induction' stable g
    · intro i j hij c hc
      have hc1 : c = 1 := by
        have : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
        exact this c hc
      subst c
      have hd : Matrix.SpecialLinearGroup.diag2n hij (1 : ZMod 2) hc = 1 := by
        apply Subtype.ext
        simp [Matrix.SpecialLinearGroup.diag2n_coe]
      rw [hd]
      exact hone
    · intro i j hij c
      have hc : c = 0 ∨ c = 1 := by
        have : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
        exact this c
      rcases hc with rfl | rfl
      · simpa only [Matrix.SpecialLinearGroup.transvection_coeff_zero] using hone
      · rw [transvection_conjugate e i j hij]
        exact hmul _ _ (hmul _ _ (hword _) hupper) (hword _)
    · exact hmul
  let S : Subrepresentation ρ :=
    { toSubmodule := W
      apply_mem_toSubmodule := hall }
  have hS : S = ⊤ := (eq_bot_or_eq_top S).resolve_left (by
    intro hS
    have : v ∈ (⊥ : Submodule (ZMod 2) V) := by
      change v ∈ (⊥ : Subrepresentation ρ)
      rw [← hS]
      exact hvW
    exact hv (by simpa using this))
  exact congrArg Subrepresentation.toSubmodule hS

/-- An endpoint singleton highest-vector support forces dimension at most four. -/
theorem LocalHighestVector.finrank_le_four_of_endpoint
    {ρ : Representation (ZMod 2) Group V} [IsIrreducible ρ] {v : V}
    {i : Fin 3} (h : LocalHighestVector ρ {i} v) (hv : v ≠ 0)
    (hi : i = 0 ∨ i = 2) : Module.finrank (ZMod 2) V ≤ 4 := by
  obtain ⟨e, he⟩ : ∃ e : Fin 2, endpointRoot e = i := by
    rcases hi with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  have hs := endpoint_span_eq_top e (he ▸ h) hv
  exact (finrank_le_of_span_eq_top hs).trans (by decide)

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
