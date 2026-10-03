module
public import Stellmacher.SectionFiveToSeven.CriticalPairNormalization

/-!
# The backward critical-pair shift in Stellmacher (8.2)

Let a critical path have length b and let m neighbor its initial vertex.
If Z_m is not contained in the terminal stabilizer, then m and the
penultimate path vertex form another critical pair of the same distance.
The noncontainment is an explicit hypothesis: its separate proof in (8.2)
uses the local-group argument and (2.5).

By (7.3), the penultimate two-core lies in the terminal stabilizer, so
Z_m is not contained in that core. Prepending m to the original path and
omitting its last edge gives a path of length b. Minimality of the original
critical distance gives the reverse bound. This works also for b = 1,
when the penultimate vertex is the initial vertex. The imported critical-pair
normalization theorem can then carry the new pair to the distinguished edge
without changing the public CriticalPath structure.

Source: Stellmacher (8.2), Journal of Algebra 190 (1997), pp.37–38,
the transition from Z_{a-1} not contained in G_{a'} to the critical pair
(a-1,a'-1), in `refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionEight
open SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_two_shifted_critical_pair_of_not_le
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h7 : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) (cp : CriticalPath Γ)
    (m : Γ.Vertex) (hm : m ∈ neighborhood Γ cp.a)
    (hout : ¬ z Γ m ≤ stabilizer Γ cp.a') :
    IsCriticalPair Γ m (cp.path ⟨cp.length - 1, by have := cp.length_pos; omega⟩) := by
  have hpos := cp.length_pos
  let last := cp.path ⟨cp.length - 1, by omega⟩
  have hlast : cp.a' ∈ neighborhood Γ last := by
    apply (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr
    have hadj := cp.path_adj ⟨cp.length - 1, by omega⟩
    have hi : (⟨cp.length - 1, by omega⟩ : Fin cp.length).succ =
        ⟨cp.length, Nat.lt_succ_self _⟩ := by apply Fin.ext; simp; omega
    rw [hi, cp.path_end] at hadj
    exact hadj
  have hcore : q Γ last ≤ stabilizer Γ cp.a' :=
    ((lemma_seven_three h7 Γ).sylow_and_core last cp.a' hlast
      (Classical.choice (inferInstance : Nonempty
        (Sylow 2 ↥(stabilizer Γ last ⊓ stabilizer Γ cp.a'))))).2.2
  have hnot : ¬ z Γ m ≤ q Γ last := fun hh => hout (hh.trans hcore)
  let path : Fin (cp.length + 1) → Γ.Vertex := fun index =>
    if index.val = 0 then m else cp.path ⟨index.val - 1, by omega⟩
  have hpath : ∀ index : Fin cp.length,
      Γ.adjacent (path index.castSucc) (path index.succ) := by
    intro index
    simp only [path, Fin.val_castSucc, Fin.val_succ]
    by_cases hzero : index.val = 0
    · simpa [hzero, cp.path_start] using
        Γ.adjacent_symm ((SevenSix.mem_neighborhood_iff_adjacent Γ).mp hm)
    · have hadj := cp.path_adj ⟨index.val - 1, by omega⟩
      simpa [hzero, Nat.sub_add_cancel (by omega : 1 ≤ index.val)] using hadj
  have hdist : Γ.distance m last ≤ cp.length := by
    simpa [path, last, Nat.ne_of_gt hpos] using Γ.distance_le_of_path cp.length path hpath
  have heq : Γ.distance m last = cp.length := by
    apply le_antisymm hdist
    by_contra hlt
    exact hnot (SevenSix.critical_minimality Γ cp (by omega))
  refine ⟨?_, hnot⟩
  change Γ.distance m last = _
  rw [heq, ← cp.endpoint_distance]
  exact cp.critical.1

end Stellmacher.SectionEight
