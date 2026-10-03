module

public import Stellmacher.SectionEight.GeneratedContext
public import Stellmacher.SectionFiveToSeven.Result7_1

/-!
# Propagating the two local models in Stellmacher (8.2)

If the stabilizers on the distinguished critical edge are S4 or C2 times
S4, the same alternative holds at every vertex. The two edge stabilizers
are exactly P1 and P2, possibly in the opposite order. By (7.1), every
vertex stabilizer is conjugate to one of them, and conjugation preserves
the whole-group isomorphism type. The supplemental theorem uses the local
Section Seven data without assuming ambient Hypothesis Two on the generated
group. The legacy theorem is a wrapper through the graph-preserving adapter.

This is the final propagation step of Stellmacher (8.2), Journal of Algebra
190 (1997), pp.37–38, in `refs/latex/stellmacher-n-group.tex`. The two edge
models remain explicit hypotheses: this reduction does not assert the
critical-distance-one theorem or classify a two-core quotient instead of
the whole stabilizer.
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven

universe u v

private theorem isModel_conjugateBy
    {G : Type u} [Group G] {X : Type v} [Group X]
    (A : Subgroup G) (g : G) (hA : IsModel A X) :
    IsModel (conjugateBy A g) X := by
  obtain ⟨equiv⟩ := hA
  exact ⟨((MulAut.conj g).subgroupMap A).symm.trans equiv⟩

public theorem eight_two_models_of_critical_edge_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (ha : IsModel (GAt ctx.Γ ctx.criticalPath.a) S4 ∨
      IsModel (GAt ctx.Γ ctx.criticalPath.a) (C2 × S4))
    (hfirst : IsModel (GAt ctx.Γ ctx.criticalPath.firstStep) S4 ∨
      IsModel (GAt ctx.Γ ctx.criticalPath.firstStep) (C2 × S4)) :
    ∀ d : ctx.Γ.Vertex,
      IsModel (GAt ctx.Γ d) S4 ∨ IsModel (GAt ctx.Γ d) (C2 × S4) := by
  have hbase : (IsModel P1 S4 ∨ IsModel P1 (C2 × S4)) ∧
      (IsModel P2 S4 ∨ IsModel P2 (C2 × S4)) := by
    rcases ctx.criticalPath.edge_stabilizers_are_P with hedge | hedge
    · exact ⟨by simpa [GAt, hedge.1] using ha,
        by simpa [GAt, hedge.2] using hfirst⟩
    · exact ⟨by simpa [GAt, hedge.2] using hfirst,
        by simpa [GAt, hedge.1] using ha⟩
  have h7 := ctx.sectionSeven
  intro d
  obtain ⟨g, hd | hd⟩ := (lemma_seven_one h7 ctx.Γ).vertex_stabilizers_conjugate d
  · change IsModel (ctx.Γ.stabilizer d) S4 ∨
      IsModel (ctx.Γ.stabilizer d) (C2 × S4)
    rw [hd]
    exact hbase.1.imp (isModel_conjugateBy P1 g) (isModel_conjugateBy P1 g)
  · change IsModel (ctx.Γ.stabilizer d) S4 ∨
      IsModel (ctx.Γ.stabilizer d) (C2 × S4)
    rw [hd]
    exact hbase.2.imp (isModel_conjugateBy P2 g) (isModel_conjugateBy P2 g)

public theorem eight_two_models_of_critical_edge
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (ha : IsModel (GAt ctx.Γ ctx.criticalPath.a) S4 ∨
      IsModel (GAt ctx.Γ ctx.criticalPath.a) (C2 × S4))
    (hfirst : IsModel (GAt ctx.Γ ctx.criticalPath.firstStep) S4 ∨
      IsModel (GAt ctx.Γ ctx.criticalPath.firstStep) (C2 × S4)) :
    ∀ d : ctx.Γ.Vertex,
      IsModel (GAt ctx.Γ d) S4 ∨ IsModel (GAt ctx.Γ d) (C2 × S4) :=
  eight_two_models_of_critical_edge_local ctx.toLocalContext ha hfirst

end Stellmacher.SectionEight
