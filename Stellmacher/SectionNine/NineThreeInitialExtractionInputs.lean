module
public import Stellmacher.SectionNine.GeneratedContext
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Theory.Frattini.PGroup

/-!
# The first critical-path extraction inputs for (9.3)

For a commuting critical path of length greater than one, the neighbor-center
join V at the first step lies in the core at the penultimate vertex. It is
elementary abelian with trivial Frattini subgroup, the two endpoint-side
neighbor-center joins act quadratically on one another, and a prescribed
element of the initial center in V lies outside the terminal core.

Every neighbor of the first step is within distance at most b-1 of the
penultimate vertex. Critical minimality therefore puts each of its centers
in that core, and taking their join gives the actor containment. The last
path edge supplies adjacency, (7.5) supplies elementary abelianness and
quadraticity, and the initial critical pair supplies the prescribed actor.

These are precisely the hypotheses for the first prescribed-actor (7.8)
extraction in the proof of (9.3). Source: Stellmacher, Journal of Algebra
190 (1997), printed p.49 / PDF p.39 of `refs/files/stellmacher-n-group.pdf`.
The argument uses only b>1 and makes no distance-three specialization.
The forward neighbor-path distance bound is public for the later replacement
of the initial vertex by the second extracted neighbor in (9.3).
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

/-- A neighbor prepended to a forward critical-path segment gives its explicit distance bound. -/
public theorem neighbor_path_distance_le
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    (l : Gamma.Vertex) (i j : ℕ) (hi : i ≤ j) (hj : j ≤ cp.length)
    (hli : Gamma.adjacent l
      (cp.path ⟨i, lt_of_le_of_lt hi (hj.trans_lt (Nat.lt_succ_self _))⟩)) :
    Gamma.distance l
        (cp.path ⟨j, hj.trans_lt (Nat.lt_succ_self _)⟩) ≤ j - i + 1 := by
  let f : Fin ((j - i + 1) + 1) → Gamma.Vertex :=
    Fin.cases l (fun k ↦ cp.path ⟨i + k, by omega⟩)
  have hf0 : f 0 = l := by simp [f]
  have hfend : f ⟨j - i + 1, Nat.lt_succ_self _⟩ =
      cp.path ⟨j, hj.trans_lt (Nat.lt_succ_self _)⟩ := by
    apply congrArg cp.path
    apply Fin.ext
    simp
    omega
  have hadj : ∀ k : Fin (j - i + 1),
      Gamma.adjacent (f k.castSucc) (f k.succ) := by
    intro k
    refine Fin.cases ?_ (fun m ↦ ?_) k
    · convert hli using 1 <;> congr 1
    · convert cp.path_adj ⟨i + m, by omega⟩ using 1 <;> congr 1
  simpa [hf0, hfend] using
    Gamma.distance_le_of_path (j - i + 1) f hadj


public theorem nine_three_initial_extraction_inputs
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 1 < ctx.criticalPath.length) :
    let Γ := ctx.Γ
    let cp := ctx.criticalPath
    let l := cp.path ⟨cp.length - 1, by omega⟩
    l ∈ Neighborhood Γ cp.a' ∧
      VAt Γ cp.firstStep ≤ QAt Γ l ∧
      IsElementaryAbelian 2 (VAt Γ cp.firstStep) ∧
      frattiniAmbient (VAt Γ cp.firstStep) = ⊥ ∧
      IsQuadraticOn (VAt Γ cp.firstStep) (VAt Γ cp.a') ∧
      IsQuadraticOn (VAt Γ cp.a') (VAt Γ cp.firstStep) ∧
      ∃ a : G, a ∈ ZAt Γ cp.a ∧ a ∈ VAt Γ cp.firstStep ∧ a ∉ QAt Γ cp.a' := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let l := cp.path ⟨cp.length - 1, by omega⟩
  change l ∈ Neighborhood Γ cp.a' ∧ _
  have hlen : 0 < cp.length := cp.length_pos
  have hbLocal : 1 < cp.length := hb
  have hedge : Γ.adjacent l cp.a' := by
    have he := cp.path_adj ⟨cp.length-1,by omega⟩
    have hs : (⟨cp.length-1,by omega⟩ : Fin cp.length).succ =
        ⟨cp.length,Nat.lt_succ_self _⟩ := by apply Fin.ext; simp; omega
    rw [hs,cp.path_end] at he
    exact he
  have hVle : VAt Γ cp.firstStep ≤ QAt Γ l := by
    rw [VAt,v,Γ.vAt_def]
    apply sSup_le
    rintro Z ⟨n,hn,rfl⟩
    have hnAdj : Γ.adjacent n cp.firstStep :=
      Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hn)
    have hd := neighbor_path_distance_le Γ cp n 1 (cp.length-1)
      (by omega) (by omega) (by simpa [cp.path_first] using hnAdj)
    exact critical_minimality Γ cp (lt_of_le_of_lt hd (by omega))
  have hlong := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hb
  let _ : IsElementaryAbelian 2 (VAt Γ cp.firstStep) := hlong.1
  let _ : Fact (IsPGroup 2 (VAt Γ cp.firstStep)) :=
    ⟨IsElementaryAbelian.isPGroup 2 (VAt Γ cp.firstStep)⟩
  have hPhi : frattiniAmbient (VAt Γ cp.firstStep) = ⊥ := by
    rw [frattiniAmbient,frattini_eq_bot_of_isElementaryAbelian (R := VAt Γ cp.firstStep) (p := 2),Subgroup.map_bot]
  have hnot : ¬ ZAt Γ cp.a ≤ QAt Γ cp.a' := cp.critical.2
  obtain ⟨a,ha,hnotA⟩ := Set.not_subset.mp hnot
  exact ⟨(mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hedge),hVle,
    hlong.1,hPhi,hlong.2.1,hlong.2.2,a,ha,
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1 ha,hnotA⟩

end Stellmacher.SectionNine
