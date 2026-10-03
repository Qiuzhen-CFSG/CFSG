module
public import Stellmacher.SectionFiveToSeven.Result7_5
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts

/-!
# Normalize critical pairs to the distinguished edge

For the same coset graph and Section Seven hypotheses, any critical pair
can be carried by a graph action to the endpoints of a CriticalPath with
the original distinguished-edge interface. The new path has the same
critical length as the supplied existing path.

Adjacency covariance maps shortest paths, giving distance invariance by
applying the inverse action for the reverse inequality. The new pair has
the same positive minimal critical distance. Edge transitivity carries
the first edge of a shortest path to the supplied distinguished edge,
possibly reversing its orientation. Mapping the path preserves criticality
by covariance of vertex centers and cores. Its initial Sylow containment
and stabilizer identifications come from that distinguished edge in the
appropriate orientation, so the public CriticalPath structure is unchanged.

Source: the repeated shifted critical pairs in Stellmacher (8.2), Journal
of Algebra 190 (1997), pp.37--38, refs/latex/stellmacher-n-group.tex.
This graph transport justifies applying the anchored Section Seven API
to those arbitrary pairs; it does not assert their existence or any new
critical-distance bound.
-/

namespace Stellmacher.SectionsFiveToSeven
open CosetGraphContext
universe u

private theorem distance_act_le
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (Γ : CosetGraphContext G S P1 P2) (g : G) (d e : Γ.Vertex) :
    Γ.distance (Γ.act g d) (Γ.act g e) ≤ Γ.distance d e := by
  obtain ⟨f, h0, hn, hadj⟩ := Γ.distance_path d e
  let f' : Fin (Γ.distance d e + 1) → Γ.Vertex := fun i => Γ.act g (f i)
  have h := Γ.distance_le_of_path (Γ.distance d e) f' (fun i => adjacent_act Γ g (hadj i))
  simpa only [f', h0, hn] using h

private theorem distance_act
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (Γ : CosetGraphContext G S P1 P2) (g : G) (d e : Γ.Vertex) :
    Γ.distance (Γ.act g d) (Γ.act g e) = Γ.distance d e := by
  apply le_antisymm (distance_act_le Γ g d e)
  have h := distance_act_le Γ g⁻¹ (Γ.act g d) (Γ.act g e)
  simpa only [← Γ.act_mul, mul_inv_cancel, Γ.act_one] using h

public theorem exists_criticalPath_of_critical_pair
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (h7 : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) (cp0 : CriticalPath Γ)
    (d e : Γ.Vertex) (hcrit : IsCriticalPair Γ d e) :
    ∃ (g : G) (cp : CriticalPath Γ),
      cp.a = Γ.act g d ∧ cp.a' = Γ.act g e ∧ cp.length = cp0.length := by
  classical
  have hlen : Γ.distance d e = cp0.length := by
    rw [← cp0.endpoint_distance]
    exact hcrit.1.trans cp0.critical.1.symm
  have hpos : 0 < Γ.distance d e := hlen ▸ cp0.length_pos
  obtain ⟨f, h0, hn, hadj⟩ := Γ.distance_path d e
  let l := f ⟨1, by omega⟩
  have hdl : Γ.adjacent d l := by
    have hh := hadj ⟨0, hpos⟩
    change Γ.adjacent (f 0) l at hh
    rwa [h0] at hh
  obtain ⟨g, he⟩ := (lemma_seven_one h7 Γ).edge_not_vertex_transitive.1
    hdl cp0.firstStep_adj
  have hcrit' : IsCriticalPair Γ (Γ.act g d) (Γ.act g e) := by
    refine ⟨?_, ?_⟩
    · rw [distance_act]
      exact hcrit.1
    · change ¬ z Γ (Γ.act g d) ≤ q Γ (Γ.act g e)
      rw [z_act, SevenSix.q_act]
      intro hh
      exact hcrit.2 ((Subgroup.map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp hh)
  have hSP : S ≤ stabilizer Γ (Γ.act g d) ⊓ stabilizer Γ (Γ.act g l) := by
    rcases he with he | he
    · rw [he.1, he.2]
      exact cp0.S_le_edge_stabilizers
    · rw [he.1, he.2, inf_comm]
      exact cp0.S_le_edge_stabilizers
  have hedge :
      (stabilizer Γ (Γ.act g d) = P1 ∧ stabilizer Γ (Γ.act g l) = P2) ∨
      (stabilizer Γ (Γ.act g d) = P2 ∧ stabilizer Γ (Γ.act g l) = P1) := by
    rcases he with he | he
    · rw [he.1, he.2]
      exact cp0.edge_stabilizers_are_P
    · rw [he.1, he.2]
      exact cp0.edge_stabilizers_are_P.elim (fun h => Or.inr ⟨h.2, h.1⟩)
        (fun h => Or.inl ⟨h.2, h.1⟩)
  let cp : CriticalPath Γ :=
    { a := Γ.act g d
      a' := Γ.act g e
      length := Γ.distance d e
      length_pos := hpos
      critical := hcrit'
      firstStep := Γ.act g l
      firstStep_adj := adjacent_act Γ g hdl
      path := fun i => Γ.act g (f i)
      endpoint_distance := distance_act Γ g d e
      path_start := congrArg (Γ.act g) h0
      path_end := congrArg (Γ.act g) hn
      path_first := rfl
      path_adj := fun i => adjacent_act Γ g (hadj i)
      S_le_edge_stabilizers := hSP
      edge_stabilizers_are_P := hedge }
  exact ⟨g, cp, rfl, rfl, hlen⟩

end Stellmacher.SectionsFiveToSeven
