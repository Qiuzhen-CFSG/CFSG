module
public import Stellmacher.SectionFiveToSeven.Result7_5
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts

/-!
# Normalize a critical pair through a prescribed neighbor

Under the genuine Section Seven hypotheses, an adjacent vertex that reduces
the distance to the critical endpoint by one can be retained as the first step
of a normalized critical path. Both endpoints and the supplied neighbor are
transported by the same actor, and the critical length is unchanged.
The strengthened result retains whether the anchored edge has the original
or reversed orientation; the original public theorem remains a wrapper
forgetting that extra conclusion. This evidence lets the central-first-step
case of (8.4) choose the original faithful module after normalization.

Prepend the given edge to a shortest path from the neighbor to the endpoint.
Edge transitivity sends this first edge to the distinguished edge of an
existing critical path, possibly reversing its orientation. Mapping paths
and applying the inverse actor proves the public distance covariance; covariance of
centers and cores preserves criticality. The distinguished edge provides
the required Sylow containment and the two stabilizer identifications.

Source: Stellmacher, Journal of Algebra 190 (1997), (9.9), the application
of (9.8) with interchanged vertices; `refs/latex/stellmacher-n-group.tex`.
The retained orientation is used in (8.4)(7), printed p.39, to transport
source (4) along the reversed conjugate critical path. This transport does
not assert criticality of any new shifted pair or commutation of its centers.
-/

namespace Stellmacher.SectionsFiveToSeven

open CosetGraphContext

universe u

variable {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}

private theorem distance_act_le (Γ : CosetGraphContext G S P1 P2)
    (actor : G) (left right : Γ.Vertex) :
    Γ.distance (Γ.act actor left) (Γ.act actor right) ≤ Γ.distance left right := by
  obtain ⟨path, hstart, hend, hadj⟩ := Γ.distance_path left right
  have hbound := Γ.distance_le_of_path (Γ.distance left right)
    (fun index => Γ.act actor (path index))
    (fun index => adjacent_act Γ actor (hadj index))
  simpa only [hstart, hend] using hbound

public theorem distance_act (Γ : CosetGraphContext G S P1 P2)
    (actor : G) (left right : Γ.Vertex) :
    Γ.distance (Γ.act actor left) (Γ.act actor right) = Γ.distance left right := by
  apply le_antisymm (distance_act_le Γ actor left right)
  have hbound := distance_act_le Γ actor⁻¹ (Γ.act actor left) (Γ.act actor right)
  simpa only [← Γ.act_mul, mul_inv_cancel, Γ.act_one] using hbound

public theorem exists_criticalPath_through_neighbor_with_orientation
    (h7 : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) (cp0 : CriticalPath Γ)
    (left right next : Γ.Vertex) (hcrit : IsCriticalPair Γ left right)
    (hnext : Γ.adjacent left next)
    (hdistance : Γ.distance left right = Γ.distance next right + 1) :
    ∃ (actor : G) (cp : CriticalPath Γ),
      cp.a = Γ.act actor left ∧ cp.a' = Γ.act actor right ∧
        cp.firstStep = Γ.act actor next ∧ cp.length = cp0.length ∧
        ((cp.a = cp0.a ∧ cp.firstStep = cp0.firstStep) ∨
          (cp.a = cp0.firstStep ∧ cp.firstStep = cp0.a)) := by
  classical
  have hlength : Γ.distance next right + 1 = cp0.length := by
    rw [← hdistance, ← cp0.endpoint_distance]
    exact hcrit.1.trans cp0.critical.1.symm
  obtain ⟨tail, hstart, hend, hadj⟩ := Γ.distance_path next right
  let path : Fin (Γ.distance next right + 1 + 1) → Γ.Vertex := Fin.cases left tail
  have hpath_start : path 0 = left := rfl
  have hpath_end : path ⟨Γ.distance next right + 1, by omega⟩ = right := by
    exact hend
  have hpath_first : path ⟨1, by omega⟩ = next := by
    exact hstart
  have hpath_adj : ∀ index : Fin (Γ.distance next right + 1),
      Γ.adjacent (path index.castSucc) (path index.succ) := by
    intro index
    refine Fin.cases ?_ (fun offset => ?_) index
    · change Γ.adjacent left (tail 0)
      rwa [hstart]
    · simpa [path] using hadj offset
  obtain ⟨actor, hedge⟩ := (lemma_seven_one h7 Γ).edge_not_vertex_transitive.1
    hnext cp0.firstStep_adj
  have hcritical : IsCriticalPair Γ (Γ.act actor left) (Γ.act actor right) := by
    refine ⟨?_, ?_⟩
    · rw [distance_act]
      exact hcrit.1
    · change ¬ z Γ (Γ.act actor left) ≤ q Γ (Γ.act actor right)
      rw [z_act, SevenSix.q_act]
      intro hle
      exact hcrit.2
        ((Subgroup.map_le_map_iff_of_injective (MulAut.conj actor⁻¹).injective).mp hle)
  have hSylow : S ≤ stabilizer Γ (Γ.act actor left) ⊓
      stabilizer Γ (Γ.act actor next) := by
    rcases hedge with horiented | hreversed
    · rw [horiented.1, horiented.2]
      exact cp0.S_le_edge_stabilizers
    · rw [hreversed.1, hreversed.2, inf_comm]
      exact cp0.S_le_edge_stabilizers
  have hstabilizers :
      (stabilizer Γ (Γ.act actor left) = P1 ∧
        stabilizer Γ (Γ.act actor next) = P2) ∨
      (stabilizer Γ (Γ.act actor left) = P2 ∧
        stabilizer Γ (Γ.act actor next) = P1) := by
    rcases hedge with horiented | hreversed
    · rw [horiented.1, horiented.2]
      exact cp0.edge_stabilizers_are_P
    · rw [hreversed.1, hreversed.2]
      exact cp0.edge_stabilizers_are_P.elim
        (fun hpair => Or.inr ⟨hpair.2, hpair.1⟩)
        (fun hpair => Or.inl ⟨hpair.2, hpair.1⟩)
  let cp : CriticalPath Γ :=
    { a := Γ.act actor left
      a' := Γ.act actor right
      length := Γ.distance next right + 1
      length_pos := Nat.zero_lt_succ _
      critical := hcritical
      firstStep := Γ.act actor next
      firstStep_adj := adjacent_act Γ actor hnext
      endpoint_distance := (distance_act Γ actor left right).trans hdistance
      path := fun index => Γ.act actor (path index)
      path_start := congrArg (Γ.act actor) hpath_start
      path_end := congrArg (Γ.act actor) hpath_end
      path_first := congrArg (Γ.act actor) hpath_first
      path_adj := fun index => adjacent_act Γ actor (hpath_adj index)
      S_le_edge_stabilizers := hSylow
      edge_stabilizers_are_P := hstabilizers }
  exact ⟨actor, cp, rfl, rfl, rfl, hlength, hedge⟩

public theorem exists_criticalPath_of_critical_pair_through_neighbor
    (h7 : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) (cp0 : CriticalPath Γ)
    (left right next : Γ.Vertex) (hcrit : IsCriticalPair Γ left right)
    (hnext : Γ.adjacent left next)
    (hdistance : Γ.distance left right = Γ.distance next right + 1) :
    ∃ (actor : G) (cp : CriticalPath Γ),
      cp.a = Γ.act actor left ∧ cp.a' = Γ.act actor right ∧
        cp.firstStep = Γ.act actor next ∧ cp.length = cp0.length := by
  obtain ⟨actor,cp,ha,ha',hfirst,hlen,_⟩ :=
    exists_criticalPath_through_neighbor_with_orientation h7 Γ cp0
      left right next hcrit hnext hdistance
  exact ⟨actor,cp,ha,ha',hfirst,hlen⟩

end Stellmacher.SectionsFiveToSeven
