module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.ByContra

/-!
# Local geometry of the graph on unordered pairs

Vertices are two-element subsets, adjacent when their intersection has size one.
Choosing one point from each of two disjoint pairs gives a common neighbor.
Common neighbors have two coordinates, one in each pair; changing one coordinate
at a time connects their induced graph. A point from a disjoint pair together
with the intersection point of an adjacent pair gives a triple common neighbor.

These are the diameter, square, and pentagon calculations used in
Aschbacher--Smith, *The Classification of Quasithin Groups*, §5.2, proof of
Theorem 5.2.10, printed p.658 (combined 1 March 2004 manuscript).
The bound on the support of a triangle supplies the remaining elementary input
to the four-transitivity argument there. Cycle closure and group recognition
are separate results; no simple-connectivity claim is made in this module.
-/

@[expose] public section

namespace Theory.Combinatorics.PairGraph

variable {α : Type*} [DecidableEq α]

/-- An unordered pair of distinct points. -/
abbrev Vertex (α : Type*) := {s : Finset α // s.card = 2}

/-- The graph on unordered pairs, also called the triangular graph. -/
def graph (α : Type*) [DecidableEq α] : SimpleGraph (Vertex α) where
  Adj s t := s ≠ t ∧ (s.val ∩ t.val).Nonempty
  symm := ⟨by
    intro s t h
    exact ⟨h.1.symm, by simpa [Finset.inter_comm] using h.2⟩⟩
  loopless := ⟨by intro s h; exact h.1 rfl⟩

/-- The vertex represented by two specified distinct points. -/
def pair (a b : α) (h : a ≠ b) : Vertex α :=
  ⟨{a, b}, Finset.card_pair h⟩

/-- Adjacency agrees with the intersection-cardinality definition. -/
theorem adj_iff_card_inter (s t : Vertex α) :
    (graph α).Adj s t ↔ (s.val ∩ t.val).card = 1 := by
  constructor
  · rintro ⟨hne, hmeet⟩
    have hpos := Finset.card_pos.mpr hmeet
    have hlt : (s.val ∩ t.val).card < 2 := by
      by_contra! h
      have heq : s.val ∩ t.val = s.val :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by simpa [s.property] using h)
      have hsub : s.val ⊆ t.val := by rw [← heq]; exact Finset.inter_subset_right
      exact hne (Subtype.ext (Finset.eq_of_subset_of_card_le hsub (by rw [s.property, t.property])))
    omega
  · intro h
    refine ⟨?_, Finset.card_pos.mp (by omega)⟩
    intro heq
    subst t
    simp [s.property] at h

/-- Distinct nonadjacent vertices are disjoint pairs. -/
theorem disjoint_of_ne_not_adj {s t : Vertex α} (hne : s ≠ t)
    (hn : ¬ (graph α).Adj s t) : Disjoint s.val t.val := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  exact hn ⟨hne, a, Finset.mem_inter.mpr ⟨ha, hb⟩⟩

/-- One point from each disjoint pair gives a common neighbor. -/
theorem pair_common_neighbor {s t : Vertex α} (hd : Disjoint s.val t.val)
    {a b : α} (ha : a ∈ s.val) (hb : b ∈ t.val) :
    ∃ w : Vertex α, w.val = {a, b} ∧ (graph α).Adj s w ∧ (graph α).Adj t w := by
  have hab : a ≠ b := by
    intro h
    exact Finset.disjoint_left.mp hd ha (h ▸ hb)
  refine ⟨pair a b hab, rfl, ?_, ?_⟩
  · refine ⟨?_, a, Finset.mem_inter.mpr ⟨ha, by simp [pair]⟩⟩
    intro h
    have : b ∈ s.val := by rw [h]; simp [pair]
    exact Finset.disjoint_left.mp hd this hb
  · refine ⟨?_, b, Finset.mem_inter.mpr ⟨hb, by simp [pair]⟩⟩
    intro h
    have : a ∈ t.val := by rw [h]; simp [pair]
    exact Finset.disjoint_left.mp hd ha this

/-- Any two vertices are equal, adjacent, or joined by a walk of length two. -/
theorem distance_le_two (s t : Vertex α) :
    s = t ∨ (graph α).Adj s t ∨
      ∃ w, (graph α).Adj s w ∧ (graph α).Adj w t := by
  by_cases heq : s = t
  · exact Or.inl heq
  by_cases hadj : (graph α).Adj s t
  · exact Or.inr (Or.inl hadj)
  have hd := disjoint_of_ne_not_adj heq hadj
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < s.val.card by rw [s.property]; decide)
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (show 0 < t.val.card by rw [t.property]; decide)
  obtain ⟨w, _, hsw, htw⟩ := pair_common_neighbor hd ha hb
  exact Or.inr (Or.inr ⟨w, hsw, htw.symm⟩)

/-- The pair graph is preconnected, including when its vertex set is empty. -/
theorem preconnected : (graph α).Preconnected := by
  intro s t
  rcases distance_le_two s t with rfl | h | ⟨w, hsw, hwt⟩
  · exact SimpleGraph.Reachable.rfl
  · exact h.reachable
  · exact hsw.reachable.trans hwt.reachable

/-- Common neighbors of disjoint pairs choose exactly one point from each. -/
theorem common_neighbor_coordinates {s t u : Vertex α}
    (hd : Disjoint s.val t.val) (hsu : (graph α).Adj s u) (htu : (graph α).Adj t u) :
    ∃ a ∈ s.val, ∃ b ∈ t.val, u.val = {a, b} := by
  obtain ⟨a, hmem⟩ := hsu.2
  obtain ⟨ha, hau⟩ := Finset.mem_inter.mp hmem
  obtain ⟨b, hmem⟩ := htu.2
  obtain ⟨hb, hbu⟩ := Finset.mem_inter.mp hmem
  have hab : a ≠ b := by
    intro h
    exact Finset.disjoint_left.mp hd ha (h ▸ hb)
  refine ⟨a, ha, b, hb, ?_⟩
  exact (Finset.eq_of_subset_of_card_le (show {a, b} ⊆ u.val by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption)
    (by rw [u.property, Finset.card_pair hab])).symm

/-- Change one coordinate at a time inside the common-neighbor graph. -/
theorem common_neighbors_distance_le_two {s t : Vertex α}
    (hd : Disjoint s.val t.val) (u v : Vertex α)
    (hsu : (graph α).Adj s u) (htu : (graph α).Adj t u)
    (hsv : (graph α).Adj s v) (htv : (graph α).Adj t v) :
    ∃ w, (graph α).Adj s w ∧ (graph α).Adj t w ∧
      (u = w ∨ (graph α).Adj u w) ∧ (w = v ∨ (graph α).Adj w v) := by
  obtain ⟨a, ha, b, hb, hu⟩ := common_neighbor_coordinates hd hsu htu
  obtain ⟨c, hc, d, hd', hv⟩ := common_neighbor_coordinates hd hsv htv
  obtain ⟨w, hw, hsw, htw⟩ := pair_common_neighbor hd ha hd'
  refine ⟨w, hsw, htw, ?_, ?_⟩
  · by_cases h : u = w
    · exact Or.inl h
    · exact Or.inr ⟨h, a, by simp [hu, hw]⟩
  · by_cases h : w = v
    · exact Or.inl h
    · exact Or.inr ⟨h, d, by simp [hv, hw]⟩

/-- The common neighbors of disjoint pairs induce a connected graph.
This is the local square calculation in the proof of Theorem 5.2.10. -/
theorem common_neighbors_connected {s t : Vertex α}
    (hd : Disjoint s.val t.val) :
    ((graph α).induce {u | (graph α).Adj s u ∧ (graph α).Adj t u}).Connected := by
  let C := {u | (graph α).Adj s u ∧ (graph α).Adj t u}
  have hex : Nonempty C := by
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < s.val.card by rw [s.property]; decide)
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (show 0 < t.val.card by rw [t.property]; decide)
    obtain ⟨w, _, hsw, htw⟩ := pair_common_neighbor hd ha hb
    exact ⟨⟨w, hsw, htw⟩⟩
  refine { preconnected := ?_, nonempty := hex }
  intro u v
  obtain ⟨w, hsw, htw, huw, hwv⟩ :=
    common_neighbors_distance_le_two hd u.val v.val u.property.1 u.property.2
      v.property.1 v.property.2
  let w' : C := ⟨w, hsw, htw⟩
  have h₁ : ((graph α).induce C).Reachable u w' := by
    rcases huw with heq | hadj
    · have : u = w' := Subtype.ext heq
      rw [this]
    · exact (show ((graph α).induce C).Adj u w' from hadj).reachable
  have h₂ : ((graph α).induce C).Reachable w' v := by
    rcases hwv with heq | hadj
    · have : w' = v := Subtype.ext heq
      rw [this]
    · exact (show ((graph α).induce C).Adj w' v from hadj).reachable
  exact h₁.trans h₂

/-- A pair disjoint from both ends of an edge has a common neighbor with both.
This gives the common neighbor used to contract pentagons in Theorem 5.2.10. -/
theorem triple_common_neighbor {s t u : Vertex α}
    (hst : Disjoint s.val t.val) (hsu : Disjoint s.val u.val)
    (htu : (graph α).Adj t u) :
    ∃ w, (graph α).Adj s w ∧ (graph α).Adj t w ∧ (graph α).Adj u w := by
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < s.val.card by rw [s.property]; decide)
  obtain ⟨b, hmem⟩ := htu.2
  obtain ⟨hbt, hbu⟩ := Finset.mem_inter.mp hmem
  obtain ⟨w, hw, hsw, htw⟩ := pair_common_neighbor hst ha hbt
  obtain ⟨w', hw', _, huw'⟩ := pair_common_neighbor hsu ha hbu
  have heq : w' = w := Subtype.ext (hw'.trans hw.symm)
  exact ⟨w, hsw, htw, heq ▸ huw'⟩

/-- Three vertices forming a two-edge path use at most four underlying points.
In particular every triangle is supported on at most four points. -/
theorem path_support_card_le_four {s t u : Vertex α}
    (hst : (graph α).Adj s t) (htu : (graph α).Adj t u) :
    (s.val ∪ t.val ∪ u.val).card ≤ 4 := by
  have hstc := (adj_iff_card_inter s t).mp hst
  have hfirst := Finset.card_union_add_card_inter s.val t.val
  have hsecond := Finset.card_union_add_card_inter (s.val ∪ t.val) u.val
  have hmeet : ((s.val ∪ t.val) ∩ u.val).Nonempty := by
    obtain ⟨a, hmem⟩ := htu.2
    obtain ⟨hat, hau⟩ := Finset.mem_inter.mp hmem
    exact ⟨a, by simp [hat, hau]⟩
  have hpos := Finset.card_pos.mpr hmeet
  have hs := s.property
  have ht := t.property
  have hu := u.property
  omega

end Theory.Combinatorics.PairGraph
