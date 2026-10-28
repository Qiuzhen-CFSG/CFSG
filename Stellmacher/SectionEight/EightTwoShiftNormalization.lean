module
public import Stellmacher.SectionEight.EightTwoShiftedCriticalPair

/-!
# Path-preserving backward normalization for Stellmacher (8.2)

Given backward-center noncontainment, normalize the actual path obtained by
prepending the backward neighbor and removing the terminal vertex. Unlike
normalization through an arbitrary shortest path, the result retains every
vertex of the supplied path. This is needed by both distance branches of
(8.2): a second backward shift must end at the original antepenultimate
vertex, not the penultimate vertex of an unrelated shortest path.

The shifted-pair theorem supplies noncontainment in the penultimate core.
Edge transitivity anchors the new first edge. Covariance preserves core
noncontainment, and critical minimality together with the explicit mapped
path proves its endpoint distance. No local backward-neighbor existence or
noncontainment theorem is assumed implicitly.

Source: Stellmacher (8.2), printed pp.37–38, the two successive backward
critical pairs in `refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionEight
open SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_two_exists_path_preserving_backward_shift
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (h7 : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) (cp : CriticalPath Γ)
    (back : Γ.Vertex) (hback : back ∈ neighborhood Γ cp.a)
    (hout : ¬ z Γ back ≤ stabilizer Γ cp.a') :
    ∃ (actor : G) (shifted : CriticalPath Γ),
      shifted.a = Γ.act actor back ∧
      shifted.a' = Γ.act actor
        (cp.path ⟨cp.length - 1, by have := cp.length_pos; omega⟩) ∧
      shifted.firstStep = Γ.act actor cp.a ∧
      ∃ hlength : shifted.length = cp.length,
        ∀ index : Fin (cp.length + 1), 0 < index.val →
          shifted.path (Fin.cast (congrArg (· + 1) hlength.symm) index) =
            Γ.act actor (cp.path ⟨index.val - 1, by omega⟩) := by
  classical
  have hpos := cp.length_pos
  let last := cp.path ⟨cp.length - 1, by omega⟩
  have hcritical := eight_two_shifted_critical_pair_of_not_le h7 Γ cp back hback hout
  have hadj : Γ.adjacent back cp.a :=
    Γ.adjacent_symm ((SevenSix.mem_neighborhood_iff_adjacent Γ).mp hback)
  obtain ⟨actor, hedge⟩ :=
    (lemma_seven_one h7 Γ).edge_not_vertex_transitive.1 hadj cp.firstStep_adj
  let path : Fin (cp.length + 1) → Γ.Vertex := fun index =>
    if index.val = 0 then back else cp.path ⟨index.val - 1, by omega⟩
  have hpath_start : path 0 = back := by simp [path]
  have hpath_end : path ⟨cp.length, by omega⟩ = last := by
    simp [path, last, Nat.ne_of_gt hpos]
  have hpath_first : path ⟨1, by omega⟩ = cp.a := by
    simpa [path] using cp.path_start
  have hpath_adj : ∀ index : Fin cp.length,
      Γ.adjacent (path index.castSucc) (path index.succ) := by
    intro index
    simp only [path, Fin.val_castSucc, Fin.val_succ]
    by_cases hzero : index.val = 0
    · simpa [hzero, cp.path_start] using hadj
    · have hstep := cp.path_adj ⟨index.val - 1, by omega⟩
      simpa [hzero, Nat.sub_add_cancel (by omega : 1 ≤ index.val)] using hstep
  have hnot : ¬ z Γ (Γ.act actor back) ≤ q Γ (Γ.act actor last) := by
    rw [z_act, SevenSix.q_act]
    intro hle
    exact hcritical.2
      ((Subgroup.map_le_map_iff_of_injective (MulAut.conj actor⁻¹).injective).mp hle)
  have hdistance : Γ.distance (Γ.act actor back) (Γ.act actor last) = cp.length := by
    apply le_antisymm
    · simpa only [hpath_start, hpath_end] using
        Γ.distance_le_of_path cp.length (fun index => Γ.act actor (path index))
          (fun index => adjacent_act Γ actor (hpath_adj index))
    · by_contra hlt
      exact hnot (SevenSix.critical_minimality Γ cp (by omega))
  have hSylow : S ≤ stabilizer Γ (Γ.act actor back) ⊓
      stabilizer Γ (Γ.act actor cp.a) := by
    rcases hedge with horiented | hreversed
    · rw [horiented.1, horiented.2]
      exact cp.S_le_edge_stabilizers
    · rw [hreversed.1, hreversed.2, inf_comm]
      exact cp.S_le_edge_stabilizers
  have hstabilizers :
      (stabilizer Γ (Γ.act actor back) = P1 ∧
        stabilizer Γ (Γ.act actor cp.a) = P2) ∨
      (stabilizer Γ (Γ.act actor back) = P2 ∧
        stabilizer Γ (Γ.act actor cp.a) = P1) := by
    rcases hedge with horiented | hreversed
    · rw [horiented.1, horiented.2]
      exact cp.edge_stabilizers_are_P
    · rw [hreversed.1, hreversed.2]
      exact cp.edge_stabilizers_are_P.elim
        (fun hpair => Or.inr ⟨hpair.2, hpair.1⟩)
        (fun hpair => Or.inl ⟨hpair.2, hpair.1⟩)
  let shifted : CriticalPath Γ :=
    { a := Γ.act actor back
      a' := Γ.act actor last
      length := cp.length
      length_pos := hpos
      critical := ⟨by
        rw [hdistance, ← cp.endpoint_distance]
        exact cp.critical.1, hnot⟩
      firstStep := Γ.act actor cp.a
      firstStep_adj := adjacent_act Γ actor hadj
      endpoint_distance := hdistance
      path := fun index => Γ.act actor (path index)
      path_start := congrArg (Γ.act actor) hpath_start
      path_end := congrArg (Γ.act actor) hpath_end
      path_first := congrArg (Γ.act actor) hpath_first
      path_adj := fun index => adjacent_act Γ actor (hpath_adj index)
      S_le_edge_stabilizers := hSylow
      edge_stabilizers_are_P := hstabilizers }
  refine ⟨actor, shifted, rfl, rfl, rfl, rfl, ?_⟩
  intro index hindex
  change Γ.act actor (path index) = _
  simp only [path, Nat.ne_of_gt hindex, ↓reduceIte]

end Stellmacher.SectionEight
