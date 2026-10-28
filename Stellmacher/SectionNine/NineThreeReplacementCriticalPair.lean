module
public import Stellmacher.SectionNine.GeneratedContext
public import Stellmacher.SectionFiveToSeven.Result7_5
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts


/-!
# Replacing the initial vertex of the critical pair

In an actual Section Nine local context with critical length greater than
one, let `n` be a neighbor of the first step whose center is not contained
in the terminal core. Then `n` and the terminal vertex form a critical pair,
their centers commute, and their distance is one more than the distance
from the first step to the terminal vertex.

Prepending one edge to a shortest path bounds a neighboring vertex's
distance by one plus the tail distance. Apply this first to the original
initial vertex: the original critical path gives the opposite bound and
identifies the tail length with `b-1`. Apply it to `n`: noncontainment and
critical minimality force its distance to equal `b`. Finally every neighbor
center lies in the first-step center join, which lies in the terminal
stabilizer by (7.4). The endpoint-center theorem from (7.5) makes the
terminal center central in that stabilizer, proving commutation.

This supplies the replacement critical-pair data behind the normalization
in Stellmacher (9.3), Journal of Algebra 190 (1997), p.49. The result keeps
the original graph and local context, and introduces no new commuting-pair
assumption.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix

private theorem distance_le_succ_of_adjacent
    {G : Type*} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (Γ : CosetGraphContext G S P1 P2) (a b c : Γ.Vertex)
    (hab : Γ.adjacent a b) : Γ.distance a c ≤ Γ.distance b c + 1 := by
  obtain ⟨tail, hstart, hend, hadj⟩ := Γ.distance_path b c
  let path : Fin (Γ.distance b c + 1 + 1) → Γ.Vertex := Fin.cases a tail
  have hpath : ∀ i : Fin (Γ.distance b c + 1),
      Γ.adjacent (path i.castSucc) (path i.succ) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Γ.adjacent a (tail 0)
      rw [hstart]
      exact hab
    · simpa [path] using hadj j
  have hh := Γ.distance_le_of_path (Γ.distance b c + 1) path hpath
  have hpathEnd : path ⟨Γ.distance b c + 1, Nat.lt_succ_self _⟩ = c := by
    change tail ⟨Γ.distance b c, Nat.lt_succ_self _⟩ = c
    exact hend
  simpa only [show path 0 = a from rfl, hpathEnd] using hh

/-- A first-step neighbor whose center escapes the terminal core gives
a commuting replacement critical pair with the same terminal vertex. -/
public theorem nine_three_replacement_initial_critical_pair
    {G : Type*} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionNineLocalContext G S P1 P2)
    (hb : 1 < ctx.criticalPath.length)
    (n : ctx.Γ.Vertex) (hn : n ∈ neighborhood ctx.Γ ctx.criticalPath.firstStep)
    (hnot : ¬ z ctx.Γ n ≤ q ctx.Γ ctx.criticalPath.a') :
    IsCriticalPair ctx.Γ n ctx.criticalPath.a' ∧
      ⁅z ctx.Γ n, z ctx.Γ ctx.criticalPath.a'⁆ = ⊥ ∧
      ctx.Γ.distance n ctx.criticalPath.a' =
        ctx.Γ.distance ctx.criticalPath.firstStep ctx.criticalPath.a' + 1 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  change 1 < cp.length at hb
  change ¬ z Γ n ≤ q Γ cp.a' at hnot
  have htail : Γ.distance cp.firstStep cp.a' ≤ cp.length - 1 := by
    have hh := path_distance_le Γ cp 1 cp.length (Nat.le_of_lt hb) le_rfl
    simpa only [cp.path_first, cp.path_end] using hh
  have hfirst := distance_le_succ_of_adjacent Γ cp.a cp.firstStep cp.a' cp.firstStep_adj
  rw [cp.endpoint_distance] at hfirst
  change cp.length ≤ Γ.distance cp.firstStep cp.a' + 1 at hfirst
  have htailEq : Γ.distance cp.firstStep cp.a' + 1 = cp.length := by omega
  have hupper := distance_le_succ_of_adjacent Γ n cp.firstStep cp.a'
    (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hn))
  have hlower : cp.length ≤ Γ.distance n cp.a' := by
    by_contra hlt
    exact hnot (critical_minimality Γ cp (by omega))
  have hdistance : Γ.distance n cp.a' = cp.length := by omega
  have hcritical : IsCriticalPair Γ n cp.a' := by
    refine ⟨?_, hnot⟩
    rw [hdistance, ← cp.endpoint_distance]
    exact cp.critical.1
  have hnV : z Γ n ≤ v Γ cp.firstStep := by
    rw [v, Γ.vAt_def]
    exact le_sSup ⟨n, hn, rfl⟩
  have hnG : z Γ n ≤ stabilizer Γ cp.a' :=
    hnV.trans (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.2
  have hendC : z Γ cp.a' ≤ Subgroup.centralizer (stabilizer Γ cp.a' : Set G) := by
    rw [lemma_seven_five_endpoint_center ctx.sectionSeven Γ cp ctx.commutator_eq]
    exact (omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _)
  have hcomm : ⁅z Γ n, z Γ cp.a'⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hendC.trans (Subgroup.centralizer_le hnG))
  exact ⟨hcritical, hcomm, hdistance.trans htailEq.symm⟩

end Stellmacher.SectionNine
