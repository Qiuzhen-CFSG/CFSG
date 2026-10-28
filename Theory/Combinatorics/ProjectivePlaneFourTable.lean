module
public import Mathlib.Combinatorics.Configuration
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic.FinCases
/-!
# The forced incidence table of an order-four plane

Four vertical and four horizontal lines, the ideal line, and a diagonal form
an affine grid. Every further line is the graph of a permutation of four
letters with one of three ideal points. A second diagonal forces all 21 lines.
The finite certificates enumerate only the 24 permutations and three ideal
points and are checked by kernel reduction.

This supplies the small-plane uniqueness step in the PSL₃(4) application of
Aschbacher–Smith F.4.8(2), printed p.278, used in F.4.26, printed p.288.
-/

namespace Configuration.Four
@[expose] public section

def line : Fin 21 → Finset (Fin 21) := ![
  {16,17,18,19,20},
  {0,1,2,3,16}, {4,5,6,7,16}, {8,9,10,11,16}, {12,13,14,15,16},
  {0,4,8,12,17}, {1,5,9,13,17}, {2,6,10,14,17}, {3,7,11,15,17},
  {0,5,10,15,18}, {0,6,11,13,19}, {0,7,9,14,20},
  {1,4,11,14,18}, {1,6,8,15,20}, {1,7,10,12,19},
  {2,4,9,15,19}, {2,5,11,12,20}, {2,7,8,13,18},
  {3,4,10,13,20}, {3,5,8,14,19}, {3,6,9,12,18}]

def compatible (s t : Finset (Fin 21)) : Prop := s = t ∨ (s ∩ t).card = 1
instance (s t : Finset (Fin 21)) : Decidable (compatible s t) := inferInstanceAs (Decidable (_ ∨ _))

def firstTen (s : Finset (Fin 21)) : Prop := ∀ j : Fin 10, compatible s (line (j.castLE (by decide)))
instance (s : Finset (Fin 21)) : Decidable (firstTen s) := inferInstanceAs (Decidable (∀ _ : Fin 10, _))

private def cell (i j : Fin 4) : Fin 21 := ⟨4 * i.val + j.val, by omega⟩
private def graph (f : Fin 4 → Fin 4) (k : Fin 3) : Finset (Fin 21) :=
  insert ⟨18 + k.val, by omega⟩ (Finset.univ.image (fun i => cell i (f i)))

private def permutation : Fin 24 → Fin 4 → Fin 4 := ![
  ![0,1,2,3],
  ![0,1,3,2],
  ![0,2,1,3],
  ![0,2,3,1],
  ![0,3,1,2],
  ![0,3,2,1],
  ![1,0,2,3],
  ![1,0,3,2],
  ![1,2,0,3],
  ![1,2,3,0],
  ![1,3,0,2],
  ![1,3,2,0],
  ![2,0,1,3],
  ![2,0,3,1],
  ![2,1,0,3],
  ![2,1,3,0],
  ![2,3,0,1],
  ![2,3,1,0],
  ![3,0,1,2],
  ![3,0,2,1],
  ![3,1,0,2],
  ![3,1,2,0],
  ![3,2,0,1],
  ![3,2,1,0]]

private theorem permutation_exhaustive : ∀ f : Fin 4 → Fin 4,
    Function.Injective f → ∃ i, f = permutation i := by decide +kernel

private theorem classify_graph : ∀ (i : Fin 24) (k : Fin 3),
    firstTen (graph (permutation i) k) → (compatible (graph (permutation i) k) (line 10) ∨
      compatible (graph (permutation i) k) (line 11)) →
      ∃ j, graph (permutation i) k = line j := by
  decide +kernel

private theorem extra_graph : ∀ (i : Fin 24) (k : Fin 3),
    firstTen (graph (permutation i) k) → 0 ∈ graph (permutation i) k →
      19 ∈ graph (permutation i) k →
      graph (permutation i) k = line 10 ∨ graph (permutation i) k = {0,7,9,14,19} := by
  decide +kernel

private theorem cell_horizontal : ∀ i j : Fin 4, cell i j ∈ line ⟨j.val + 5, by omega⟩ := by
  decide +kernel
private theorem cell_injective : ∀ i j k l : Fin 4, cell i j = cell k l → i = k ∧ j = l := by
  decide +kernel

private theorem line_card : ∀ j : Fin 21, (line j).card = 5 := by decide +kernel
private theorem graph_card (f : Fin 4 → Fin 4) (k : Fin 3) : (graph f k).card = 5 := by
  have hi : Function.Injective (fun i => cell i (f i)) :=
    fun i j he => (cell_injective i (f i) j (f j) he).1
  have hn : (⟨18 + k.val, by omega⟩ : Fin 21) ∉ Finset.univ.image (fun i => cell i (f i)) := by
    intro hm
    obtain ⟨i,_,he⟩ := Finset.mem_image.mp hm
    have hv := congrArg Fin.val he
    dsimp [cell] at hv
    omega
  rw [graph, Finset.card_insert_of_notMem hn, Finset.card_image_of_injective _ hi]
  decide
private theorem vertical_cover : ∀ p : Fin 21, p ∈ line 0 ∨
    ∃ j : Fin 4, p ∈ line ⟨j.val + 1, by omega⟩ := by decide +kernel
private theorem horizontal_cover : ∀ p : Fin 21, p ∈ line 0 ∨
    ∃ j : Fin 4, p ∈ line ⟨j.val + 5, by omega⟩ := by decide +kernel
private theorem vertical_ideal : ∀ j : Fin 4, (16 : Fin 21) ∈ line ⟨j.val + 1, by omega⟩ := by
  decide +kernel
private theorem horizontal_ideal : ∀ j : Fin 4, (17 : Fin 21) ∈ line ⟨j.val + 5, by omega⟩ := by
  decide +kernel
private theorem ideal_cases : ∀ p : Fin 21, p ∈ line 0 → p ≠ 16 → p ≠ 17 →
    ∃ k : Fin 3, p = ⟨18 + k.val, by omega⟩ := by decide +kernel
private theorem vertical_cases : ∀ (p : Fin 21) (i : Fin 4),
    p ∈ line ⟨i.val + 1, by omega⟩ → p ≠ 16 → ∃ j, p = cell i j := by decide +kernel

private theorem eq_of_mem_inter {s t : Finset (Fin 21)} (hc : (s ∩ t).card = 1)
    {p q : Fin 21} (hp : p ∈ s) (hpt : p ∈ t) (hq : q ∈ s) (hqt : q ∈ t) : p = q := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
  have hp' : p ∈ ({a} : Finset (Fin 21)) := ha ▸ Finset.mem_inter.mpr ⟨hp,hpt⟩
  have hq' : q ∈ ({a} : Finset (Fin 21)) := ha ▸ Finset.mem_inter.mpr ⟨hq,hqt⟩
  exact (Finset.mem_singleton.mp hp').trans (Finset.mem_singleton.mp hq').symm

/-- The grid forces every non-axis line to be the graph of a four-entry function,
with one of the three remaining points at infinity. -/
private theorem representation (s : Finset (Fin 21)) (hc : s.card = 5) (hs : firstTen s) :
    (∃ j : Fin 9, s = line (j.castLE (by decide))) ∨ ∃ f k, s = graph f k ∧ Function.Injective f := by
  by_cases he : ∃ j : Fin 9, s = line (j.castLE (by decide))
  · exact Or.inl he
  right
  have hi (j : Fin 9) : (s ∩ line (j.castLE (by decide))).card = 1 :=
    (hs (j.castLE (by decide))).resolve_left (fun hj => he ⟨j,hj⟩)
  have hn16 : (16 : Fin 21) ∉ s := by
    intro hm
    have hsub : s ⊆ line 0 := by
      intro p hp
      rcases vertical_cover p with h | ⟨i,h⟩
      · exact h
      · have hpi := eq_of_mem_inter (hi ⟨i.val+1, by omega⟩) hp h hm (vertical_ideal i)
        rw [hpi]
        decide +kernel
    exact he ⟨0, Finset.eq_of_subset_of_card_le hsub (by rw [line_card, hc])⟩
  have hn17 : (17 : Fin 21) ∉ s := by
    intro hm
    have hsub : s ⊆ line 0 := by
      intro p hp
      rcases horizontal_cover p with h | ⟨i,h⟩
      · exact h
      · have hpi := eq_of_mem_inter (hi ⟨i.val+5, by omega⟩) hp h hm (horizontal_ideal i)
        rw [hpi]
        decide +kernel
    exact he ⟨0, Finset.eq_of_subset_of_card_le hsub (by rw [line_card, hc])⟩
  obtain ⟨p,hp⟩ := Finset.card_pos.mp (show 0 < (s ∩ line 0).card by
    have hh : (s ∩ line 0).card = 1 := hi 0
    omega)
  obtain ⟨hp,hpI⟩ := Finset.mem_inter.mp hp
  obtain ⟨k,hk⟩ := ideal_cases p hpI (fun he => hn16 (he ▸ hp)) (fun he => hn17 (he ▸ hp))
  have hrow (i : Fin 4) : ∃ j, cell i j ∈ s := by
    obtain ⟨p,hp⟩ := Finset.card_pos.mp
      (show 0 < (s ∩ line ⟨i.val+1, by omega⟩).card by
        have hh : (s ∩ line ⟨i.val+1, by omega⟩).card = 1 := hi ⟨i.val+1, by omega⟩
        omega)
    obtain ⟨hp,hpv⟩ := Finset.mem_inter.mp hp
    obtain ⟨j,hj⟩ := vertical_cases p i hpv (fun he => hn16 (he ▸ hp))
    exact ⟨j, hj ▸ hp⟩
  choose f hf using hrow
  have hf_inj : Function.Injective f := by
    intro i j hij
    have hci : cell i (f i) ∈ line ⟨(f i).val + 5, by omega⟩ := cell_horizontal i (f i)
    have hcj : cell j (f j) ∈ line ⟨(f i).val + 5, by omega⟩ := hij ▸ cell_horizontal j (f j)
    exact (cell_injective i (f i) j (f j)
      (eq_of_mem_inter (hi ⟨(f i).val+5, by omega⟩) (hf i) hci (hf j) hcj)).1
  refine ⟨f,k, ?_, hf_inj⟩
  apply (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro p hp'
    rcases Finset.mem_insert.mp hp' with he | hm
    · exact he ▸ hk ▸ hp
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hm
      exact hf i
  · rw [hc, graph_card]

/-- Eleven grid lines force all twenty-one rows of the order-four plane. -/
theorem classify (s : Finset (Fin 21)) (hc : s.card = 5)
    (hs : firstTen s) (he : compatible s (line 10) ∨ compatible s (line 11)) : ∃ j, s = line j := by
  rcases representation s hc hs with ⟨j,rfl⟩ | ⟨f,k,rfl,hf⟩
  · exact ⟨j.castLE (by decide), rfl⟩
  · obtain ⟨i,rfl⟩ := permutation_exhaustive f hf
    exact classify_graph i k hs he

private theorem extra_not_axis : ∀ j : Fin 9,
    ¬ ((0 : Fin 21) ∈ line (j.castLE (by decide)) ∧
      (19 : Fin 21) ∈ line (j.castLE (by decide))) := by decide +kernel

/-- The second diagonal has just two possible labelings. -/
theorem extra_cases (s : Finset (Fin 21)) (hc : s.card = 5)
    (hs : firstTen s) (h0 : 0 ∈ s) (h19 : 19 ∈ s) :
    s = line 10 ∨ s = {0,7,9,14,19} := by
  rcases representation s hc hs with ⟨j,rfl⟩ | ⟨f,k,rfl,hf⟩
  · exact (extra_not_axis j ⟨h0,h19⟩).elim
  · obtain ⟨i,rfl⟩ := permutation_exhaustive f hf
    exact extra_graph i k hs h0 h19

theorem line_injective : Function.Injective line := by decide +kernel
end
end Configuration.Four
