module

public import Stellmacher.SectionFiveToSeven.PrescribedCriticalPairNormalization

/-!
# Normalize an entire supplied critical path

Under Section Seven's hypotheses, a supplied path of the known critical
length connecting a critical pair can be normalized at its first edge while
retaining every vertex of the sequence. The same group actor moves both
endpoints, the first step, and all later offsets; its critical length is
unchanged. The returned path has the ordinary distinguished-edge Sylow and
stabilizer data.

Edge transitivity supplies the actor. Distance covariance and the equality
of critical distances prove the endpoint metric identity; covariance of
centers and cores preserves criticality. Map the supplied sequence directly
rather than choosing another shortest tail. The anchored edge provides the
Sylow containment and the local group identifications.

This supports the renormalization in Stellmacher (9.10), printed p.57, where
later uses of the same extraction conjugator depend on offsets two and three.
The theorem does not assert criticality of a new pair: that remains input.
-/

namespace Stellmacher.SectionsFiveToSeven

open CosetGraphContext

universe u

public theorem exists_criticalPath_of_supplied_path
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (h7 : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) (original : CriticalPath Γ)
    (left right : Γ.Vertex) (hcritical : IsCriticalPair Γ left right)
    (path : Fin (original.length + 1) → Γ.Vertex)
    (hstart : path 0 = left)
    (hend : path ⟨original.length, Nat.lt_succ_self _⟩ = right)
    (hadj : ∀ index : Fin original.length,
      Γ.adjacent (path index.castSucc) (path index.succ)) :
    ∃ (actor : G) (normalized : CriticalPath Γ)
      (hlength : normalized.length = original.length),
      normalized.a = Γ.act actor left ∧
      normalized.a' = Γ.act actor right ∧
      normalized.firstStep = Γ.act actor (path ⟨1, by have := original.length_pos; omega⟩) ∧
      (∀ index : Fin (original.length + 1),
        normalized.path ⟨index, by rw [hlength]; exact index.isLt⟩ = Γ.act actor (path index)) := by
  let next := path ⟨1, by have := original.length_pos; omega⟩
  have hfirst : Γ.adjacent left next := by
    have h := hadj ⟨0, original.length_pos⟩
    change Γ.adjacent (path 0) next at h
    rwa [hstart] at h
  obtain ⟨actor, hedge⟩ := (lemma_seven_one h7 Γ).edge_not_vertex_transitive.1
    hfirst original.firstStep_adj
  have hdistance : Γ.distance left right = original.length := by
    rw [← original.endpoint_distance]
    exact hcritical.1.trans original.critical.1.symm
  have hcriticalMoved : IsCriticalPair Γ (Γ.act actor left) (Γ.act actor right) := by
    refine ⟨?_, ?_⟩
    · rw [distance_act]
      exact hcritical.1
    · change ¬ z Γ (Γ.act actor left) ≤ q Γ (Γ.act actor right)
      rw [z_act, SevenSix.q_act]
      intro hle
      exact hcritical.2
        ((Subgroup.map_le_map_iff_of_injective (MulAut.conj actor⁻¹).injective).mp hle)
  have hSylow : S ≤ stabilizer Γ (Γ.act actor left) ⊓ stabilizer Γ (Γ.act actor next) := by
    rcases hedge with horiented | hreversed
    · rw [horiented.1, horiented.2]
      exact original.S_le_edge_stabilizers
    · rw [hreversed.1, hreversed.2, inf_comm]
      exact original.S_le_edge_stabilizers
  have hstabilizers :
      (stabilizer Γ (Γ.act actor left) = P1 ∧ stabilizer Γ (Γ.act actor next) = P2) ∨
      (stabilizer Γ (Γ.act actor left) = P2 ∧ stabilizer Γ (Γ.act actor next) = P1) := by
    rcases hedge with horiented | hreversed
    · rw [horiented.1, horiented.2]
      exact original.edge_stabilizers_are_P
    · rw [hreversed.1, hreversed.2]
      exact original.edge_stabilizers_are_P.elim
        (fun hpair => Or.inr ⟨hpair.2, hpair.1⟩)
        (fun hpair => Or.inl ⟨hpair.2, hpair.1⟩)
  let normalized : CriticalPath Γ :=
    { a := Γ.act actor left
      a' := Γ.act actor right
      length := original.length
      length_pos := original.length_pos
      critical := hcriticalMoved
      firstStep := Γ.act actor next
      firstStep_adj := adjacent_act Γ actor hfirst
      endpoint_distance := (distance_act Γ actor left right).trans hdistance
      path := fun index => Γ.act actor (path index)
      path_start := congrArg (Γ.act actor) hstart
      path_end := congrArg (Γ.act actor) hend
      path_first := rfl
      path_adj := fun index => adjacent_act Γ actor (hadj index)
      S_le_edge_stabilizers := hSylow
      edge_stabilizers_are_P := hstabilizers }
  exact ⟨actor, normalized, rfl, rfl, rfl, rfl, fun _ => rfl⟩

end Stellmacher.SectionsFiveToSeven
