module
public import Stellmacher.SectionEight.EightFourFixedClosureControl
/-!
# Fixed-closure control for another critical endpoint

Retain the original initial edge and faithful module in the central-first-step,
nontrivial-closure branch of (8.4). If another endpoint forms a noncommuting
critical pair with the original starting vertex, and the original first step
is one step nearer that endpoint, then the same initial fixed-center normal
closure lies in its core.

Prepend the original edge to a shortest path from its first step to the new
endpoint. This constructs an actual CriticalPath with the very same initial
vertex and first step, so all original Sylow and stabilizer fields apply.
The original faithful quotient witness remains definitionally the correct
one. Apply source (4) to this new context and retain its core containment.

This permits source (4) to be used on the reversed conjugate critical paths
in (8.4)(7), without changing the fixed-center action or assuming its final
normality. Source: Stellmacher, Journal of Algebra 190 (1997), pp.38–39,
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u
public theorem eight_four_closure_le_core_of_critical_endpoint
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (endpoint : ctx.Γ.Vertex)
    (hcritical : IsCriticalPair ctx.Γ ctx.criticalPath.a endpoint)
    (hcomm : ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ endpoint⁆ ≠ ⊥)
    (hnear : ctx.Γ.distance ctx.criticalPath.a endpoint =
      ctx.Γ.distance ctx.criticalPath.firstStep endpoint + 1) :
    (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≤ QAt ctx.Γ endpoint := by
  let Γ := ctx.Γ
  let cp0 := ctx.criticalPath
  obtain ⟨tail,hstart,hend,hadj⟩ := Γ.distance_path cp0.firstStep endpoint
  let path : Fin (Γ.distance cp0.firstStep endpoint + 1 + 1) → Γ.Vertex := Fin.cases cp0.a tail
  have hpath_adj : ∀ i : Fin (Γ.distance cp0.firstStep endpoint + 1),
      Γ.adjacent (path i.castSucc) (path i.succ) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Γ.adjacent cp0.a (tail 0)
      rw [hstart]
      exact cp0.firstStep_adj
    · simpa [path] using hadj j
  let cp : CriticalPath Γ :=
    { a := cp0.a
      a' := endpoint
      length := Γ.distance cp0.firstStep endpoint + 1
      length_pos := Nat.zero_lt_succ _
      critical := hcritical
      firstStep := cp0.firstStep
      firstStep_adj := cp0.firstStep_adj
      endpoint_distance := hnear
      path := path
      path_start := rfl
      path_end := hend
      path_first := hstart
      path_adj := hpath_adj
      S_le_edge_stabilizers := cp0.S_le_edge_stabilizers
      edge_stabilizers_are_P := cp0.edge_stabilizers_are_P }
  let ctx' : SectionEightContext H S0 S P1 P2 :=
    { hypothesisTwo := ctx.hypothesisTwo
      generated := ctx.generated
      Γ := Γ
      criticalPath := cp
      commutator_ne := hcomm }
  exact (eight_four_fixed_closure_control ctx' hcenter w hbranch).1
end Stellmacher.SectionEight
