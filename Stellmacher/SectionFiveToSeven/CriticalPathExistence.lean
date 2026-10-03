module
public import Stellmacher.SectionFiveToSeven.Result7_5
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts
public import Stellmacher.SectionFiveToSeven.Result7_2

/-!
# Initial normalized critical paths

For a finite group satisfying Section Seven and its coset graph, a critical
path exists without assuming an earlier critical pair or noncommutation.
The nontrivial omega-center of the common Sylow subgroup lies in a vertex
center. Faithfulness implies that this center cannot lie in every vertex
core. Minimize the eligible natural distances; (7.3)(b) excludes zero.
Finally, edge transitivity transports a shortest path to the distinguished
P1/P2 edge, preserving distances and noncontainment by equivariance.

Source: Stellmacher, Journal of Algebra 190 (1997), Section 7, the definition
of critical distance immediately after (7.3), as transcribed in
`refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionsFiveToSeven
open CosetGraphContext
open scoped Pointwise

universe u v

variable {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}

private theorem omegaCenter_ne_bot (hSp : IsPGroup 2 S) (hSne : S ≠ ⊥) :
    omegaOneCenter S ≠ ⊥ := by
  let _ : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).2 hSne
  let _ : Nontrivial (Subgroup.center S) := hSp.center_nontrivial
  have hcenterP := hSp.to_subgroup (Subgroup.center S)
  obtain ⟨power, hpos, hcard⟩ := hcenterP.nontrivial_iff_card.mp inferInstance
  have hdvd : 2 ∣ Nat.card (Subgroup.center S) := by
    rw [hcard]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hpos)
  have hinner := omega₁_map_subtype_ne_bot (G := S) (Subgroup.center S) 2 hdvd
  intro hz
  apply hinner
  apply (Subgroup.map_eq_bot_iff_of_injective
    (H := (omega₁ (G := Subgroup.center S) (p := 2)).map
      (Subgroup.center S).subtype)
    (f := S.subtype) S.subtype_injective).mp
  simpa [omegaOneCenter] using hz

private theorem exists_neighbor (Γ : CosetGraphContext G S P1 P2)
    (d : Γ.Vertex) : ∃ l, Γ.adjacent d l := by
  obtain ⟨g, hd | hd⟩ := Γ.coset₁_surjective d
  all_goals
    have hedge : Γ.adjacent (Γ.coset₁ g) (Γ.coset₂ g) := by
      rw [Γ.adj_cosets]
      apply Set.nonempty_iff_ne_empty.mp
      exact ⟨g, Set.mem_smul_set.mpr ⟨1, P1.one_mem, by simp⟩,
        Set.mem_smul_set.mpr ⟨1, P2.one_mem, by simp⟩⟩
  · exact ⟨Γ.coset₂ g, hd ▸ hedge⟩
  · exact ⟨Γ.coset₁ g, hd ▸ Γ.adjacent_symm hedge⟩

private theorem exists_noncontainment
    (h7 : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) :
    ∃ d e : Γ.Vertex, ¬ Γ.zAt d ≤ Γ.twoCoreAt e := by
  obtain ⟨base, next, _, hbase, _⟩ := (lemma_seven_one h7 Γ).distinguished_edge
  obtain ⟨sylow, hsylow⟩ := h7.P1_mem.1.2.1.2
  have hSp : IsPGroup 2 S := hsylow ▸ sylow.isPGroup'.map P1.subtype
  have hZ : omegaOneCenter S ≤ Γ.zAt base := by
    rw [Γ.zAt_def]
    change omegaOneCenter S ≤ sSup {Z : Subgroup G |
      ∃ T : Sylow 2 (stabilizer Γ base),
        Z = omegaOneCenter ((T : Subgroup (stabilizer Γ base)).map
          (stabilizer Γ base).subtype)}
    rw [hbase]
    exact le_sSup ⟨sylow, congrArg omegaOneCenter hsylow.symm⟩
  by_contra! hall
  have hkernel : omegaOneCenter S ≤ Γ.actionKernel := by
    intro element helement
    rw [Γ.actionKernel_def]
    intro vertex
    have hmem : element ∈ stabilizer Γ vertex := by
      have hcore := hall base vertex (hZ helement)
      rw [Γ.twoCoreAt_def] at hcore
      exact (Subgroup.map_subtype_le _) hcore
    exact (Set.ext_iff.mp (Γ.stabilizer_def vertex) element).mp hmem
  exact omegaCenter_ne_bot hSp h7.S_nontrivial
    (le_bot_iff.mp (hkernel.trans (le_of_eq (lemma_seven_two h7 Γ))))

private theorem distance_act_le (Γ : CosetGraphContext G S P1 P2)
    (g : G) (d e : Γ.Vertex) :
    Γ.distance (Γ.act g d) (Γ.act g e) ≤ Γ.distance d e := by
  obtain ⟨path, hstart, hend, hadj⟩ := Γ.distance_path d e
  have hbound := Γ.distance_le_of_path (Γ.distance d e)
    (fun index => Γ.act g (path index)) (fun index => adjacent_act Γ g (hadj index))
  simpa only [hstart, hend] using hbound

private theorem distance_act (Γ : CosetGraphContext G S P1 P2)
    (g : G) (d e : Γ.Vertex) :
    Γ.distance (Γ.act g d) (Γ.act g e) = Γ.distance d e := by
  apply le_antisymm (distance_act_le Γ g d e)
  have hbound := distance_act_le Γ g⁻¹ (Γ.act g d) (Γ.act g e)
  simpa only [← Γ.act_mul, mul_inv_cancel, Γ.act_one] using hbound

public theorem exists_criticalPath
    (h7 : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) : Nonempty (CriticalPath Γ) := by
  classical
  obtain ⟨witness, endpoint, hnot⟩ := exists_noncontainment h7 Γ
  have hnonempty : {n : ℕ | ∃ d e : Γ.Vertex,
      Γ.distance d e = n ∧ ¬ Γ.zAt d ≤ Γ.twoCoreAt e}.Nonempty :=
    ⟨Γ.distance witness endpoint, witness, endpoint, rfl, hnot⟩
  obtain ⟨d, e, hmin, hcrit⟩ := Nat.sInf_mem hnonempty
  have hpos : 0 < Γ.distance d e := by
    by_contra! hzero
    have heq := (Γ.distance_zero_iff d e).mp (Nat.eq_zero_of_le_zero hzero)
    subst e
    obtain ⟨neighbor, hadj⟩ := exists_neighbor Γ d
    have hcenter := (lemma_seven_three h7 Γ).center_core d neighbor
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hadj)
    apply hcrit
    exact hcenter.trans ((Subgroup.map_mono (Subgroup.map_subtype_le _)).trans
      (Subgroup.map_subtype_le _))
  obtain ⟨path, hstart, hend, hadj⟩ := Γ.distance_path d e
  let first := path ⟨1, by omega⟩
  have hfirst : Γ.adjacent d first := by
    have hedge := hadj ⟨0, hpos⟩
    change Γ.adjacent (path 0) first at hedge
    rwa [hstart] at hedge
  obtain ⟨base, next, hbaseNext, hbase, hnext⟩ :=
    (lemma_seven_one h7 Γ).distinguished_edge
  obtain ⟨g, hedge⟩ := (lemma_seven_one h7 Γ).edge_not_vertex_transitive.1
    hfirst hbaseNext
  have htransport : IsCriticalPair Γ (Γ.act g d) (Γ.act g e) := by
    refine ⟨?_, ?_⟩
    · rw [distance_act]
      exact hmin
    · change ¬ z Γ (Γ.act g d) ≤ q Γ (Γ.act g e)
      rw [z_act, SevenSix.q_act]
      intro hle
      exact hcrit ((Subgroup.map_le_map_iff_of_injective
        (MulAut.conj g⁻¹).injective).mp hle)
  have hstabilizers :
      (stabilizer Γ (Γ.act g d) = P1 ∧ stabilizer Γ (Γ.act g first) = P2) ∨
      (stabilizer Γ (Γ.act g d) = P2 ∧ stabilizer Γ (Γ.act g first) = P1) := by
    rcases hedge with hedge | hedge
    · exact Or.inl ⟨hedge.1 ▸ hbase, hedge.2 ▸ hnext⟩
    · exact Or.inr ⟨hedge.1 ▸ hnext, hedge.2 ▸ hbase⟩
  have hS : S ≤ stabilizer Γ (Γ.act g d) ⊓ stabilizer Γ (Γ.act g first) := by
    rcases hstabilizers with hedge | hedge
    · rw [hedge.1, hedge.2]
      exact le_inf h7.P1_mem.1.2.1.1 h7.P2_mem.1.2.1.1
    · rw [hedge.1, hedge.2]
      exact le_inf h7.P2_mem.1.2.1.1 h7.P1_mem.1.2.1.1
  exact ⟨{
    a := Γ.act g d
    a' := Γ.act g e
    length := Γ.distance d e
    length_pos := hpos
    critical := htransport
    firstStep := Γ.act g first
    firstStep_adj := adjacent_act Γ g hfirst
    endpoint_distance := distance_act Γ g d e
    path := fun index => Γ.act g (path index)
    path_start := congrArg (Γ.act g) hstart
    path_end := congrArg (Γ.act g) hend
    path_first := rfl
    path_adj := fun index => adjacent_act Γ g (hadj index)
    S_le_edge_stabilizers := hS
    edge_stabilizers_are_P := hstabilizers }⟩

end Stellmacher.SectionsFiveToSeven
