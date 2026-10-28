module
public import Stellmacher.SectionNine.GeneratedContext
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts
public import Theory.Frattini.PGroup

/-!
# Inputs for the second extraction in Stellmacher (9.3)

For a commuting critical path of length greater than one, the second path
vertex is adjacent to the first step, and the terminal neighbor-center join
lies in its two-core. That same terminal module is elementary abelian and
has trivial Frattini subgroup.

Prepend a terminal neighbor to the reversed path segment ending at the
second vertex. The reverse-path distance bound is also exported for the
second center-intersection argument, which uses a newly extracted terminal
neighbor. This gives distance at most b-1, so critical minimality puts
each neighboring center in the second vertex's core. Their join remains
there. The endpoint alignment from (7.5), together with neighbor-module
covariance, carries the elementary abelian first-step module to the terminal
module. Elementary abelianness then gives its trivial Frattini subgroup.

These are the adjacency, containment and Frattini inputs of the second
(7.8) extraction before (9.3)(3), journal p.49. Its noncontainment in the
first-step core comes from the separate relation (2). No b=3 assumption is
used. Source: `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

/-- A terminal neighbor followed by the reversed path segment gives the
corresponding upper bound on graph distance. -/
public theorem neighbor_reverse_path_distance_le
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    (l : Gamma.Vertex) (i j : ℕ) (hi : i ≤ j) (hj : j ≤ cp.length)
    (hlj : Gamma.adjacent l
      (cp.path ⟨j, hj.trans_lt (Nat.lt_succ_self _)⟩)) :
    Gamma.distance l
        (cp.path ⟨i, lt_of_le_of_lt hi (hj.trans_lt (Nat.lt_succ_self _))⟩) ≤ j - i + 1 := by
  let f : Fin ((j - i + 1) + 1) → Gamma.Vertex :=
    Fin.cases l (fun k ↦ cp.path ⟨j - k, by omega⟩)
  have hf0 : f 0 = l := by simp [f]
  have hfend : f ⟨j - i + 1, Nat.lt_succ_self _⟩ =
      cp.path ⟨i, lt_of_le_of_lt hi (hj.trans_lt (Nat.lt_succ_self _))⟩ := by
    apply congrArg cp.path
    apply Fin.ext
    simp
    omega
  have hadj : ∀ k : Fin (j - i + 1),
      Gamma.adjacent (f k.castSucc) (f k.succ) := by
    intro k
    refine Fin.cases ?_ (fun m ↦ ?_) k
    · convert hlj using 1 <;> congr 1
    · simp only [f, Fin.castSucc_succ, Fin.cases_succ]
      convert Gamma.adjacent_symm (cp.path_adj ⟨j - m - 1, by omega⟩) using 1
      all_goals congr 1
      all_goals apply Fin.ext
      all_goals simp
      all_goals omega
  simpa [hf0, hfend] using
    Gamma.distance_le_of_path (j - i + 1) f hadj

/-- The terminal neighbor module supplies the containment, elementary
abelian and Frattini inputs at the second vertex for the second (9.3) extraction. -/
public theorem nine_three_second_extraction_inputs
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 1 < ctx.criticalPath.length) :
    let Γ := ctx.Γ
    let cp := ctx.criticalPath
    let l := cp.path ⟨2, by dsimp [cp]; omega⟩
    l ∈ Neighborhood Γ cp.firstStep ∧
      VAt Γ cp.a' ≤ QAt Γ l ∧
      IsElementaryAbelian 2 (VAt Γ cp.a') ∧
      frattiniAmbient (VAt Γ cp.a') = ⊥ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let l := cp.path ⟨2, by dsimp [cp]; omega⟩
  change l ∈ Neighborhood Γ cp.firstStep ∧ _
  have hbLocal : 1 < cp.length := hb
  have hedge : Γ.adjacent cp.firstStep l := by
    have he := cp.path_adj ⟨1, by omega⟩
    simpa [cp.path_first] using he
  have hVle : VAt Γ cp.a' ≤ QAt Γ l := by
    rw [VAt, v, Γ.vAt_def]
    apply sSup_le
    rintro Z ⟨n, hn, rfl⟩
    have hnAdj : Γ.adjacent n cp.a' :=
      Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hn)
    have hd := neighbor_reverse_path_distance_le Γ cp n 2 cp.length
      (by omega) le_rfl (by simpa [cp.path_end] using hnAdj)
    exact critical_minimality Γ cp (lt_of_le_of_lt hd (by omega))
  have hlong := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hb
  have hend : IsElementaryAbelian 2 (VAt Γ cp.a') := by
    obtain ⟨g, _, hg⟩ := lemma_seven_five_endpoint_alignment
      ctx.sectionSeven Γ cp ctx.commutator_eq
    change IsElementaryAbelian 2 (v Γ cp.a')
    rw [← hg, v_act]
    let _ : IsElementaryAbelian 2 (v Γ cp.firstStep) := hlong.1
    exact IsElementaryAbelian.map (MulAut.conj g⁻¹).toMonoidHom
  let _ : IsElementaryAbelian 2 (VAt Γ cp.a') := hend
  let _ : Fact (IsPGroup 2 (VAt Γ cp.a')) :=
    ⟨IsElementaryAbelian.isPGroup 2 (VAt Γ cp.a')⟩
  have hPhi : frattiniAmbient (VAt Γ cp.a') = ⊥ := by
    rw [frattiniAmbient,
      frattini_eq_bot_of_isElementaryAbelian (R := VAt Γ cp.a') (p := 2), Subgroup.map_bot]
  exact ⟨(mem_neighborhood_iff_adjacent Γ).mpr hedge, hVle, hend, hPhi⟩

end Stellmacher.SectionNine
