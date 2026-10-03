module
public import Stellmacher.SectionEight.LemmaEightThree
public import Stellmacher.SectionEight.EightFourLocalContext
public import Stellmacher.SectionEight.EightFourFixedClosureControl
public import Stellmacher.SectionFiveToSeven.ResidualTransport

/-!
# Terminal residual-core noncontainment for Stellmacher (8.4)

In the centered-first-step case, the two-core of the terminal vertex's
residual lies outside every neighboring vertex core. This is the transported
(8.3) input in the paragraph between source (5) and (6) of Stellmacher (8.4),
Journal of Algebra 190 (1997), printed p.39,
`refs/files/stellmacher-n-group.pdf`.

The terminal center cannot centralize its stabilizer: (7.4) puts the initial
center there, and the endpoint centers do not commute. Edge transitivity
carries the initial/first-step edge to the terminal/neighbor edge. The swapped
orientation would carry the central first-step center to the terminal center,
contradicting that noncentrality. In the remaining orientation, transport the
existing (8.3) noncontainment by conjugation. Ambient residual and two-core
covariance use the same automorphism, and injectivity reflects the subgroup
inequality. The local context supplies the proved (8.3) callback and the
same Section Seven graph. No fixed-subgroup normality is assumed. The
original canonical theorem is retained as an exact wrapper through
`SectionEightContext.toEightFourContext`, so existing callers keep their
public statements and quotient witnesses.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

/-- At the terminal vertex, the residual two-core lies outside every neighbor core. -/
public theorem eight_four_terminal_core_noncontainment_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : EightFourLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (neighbor : ctx.Γ.Vertex)
    (hadj : ctx.Γ.adjacent ctx.criticalPath.a' neighbor) :
    ¬ twoCoreIn (EAt ctx.Γ ctx.criticalPath.a') ≤ QAt ctx.Γ neighbor := by
  let h := ctx.sectionSeven
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hend : ⁅z Γ cp.a', stabilizer Γ cp.a'⁆ ≠ ⊥ := by
    intro hc
    apply ctx.commutator_ne
    rw [Subgroup.commutator_comm]
    exact bot_unique ((Subgroup.commutator_mono le_rfl
      ((lemma_seven_four h Γ cp).first_containment.1.trans
        (lemma_seven_four h Γ cp).first_containment.2)).trans_eq hc)
  obtain ⟨g, hedge | hedge⟩ :=
    (lemma_seven_one h Γ).edge_not_vertex_transitive.1 cp.firstStep_adj hadj
  · intro hbound
    have he : e Γ (Γ.act g cp.a) = (e Γ cp.a).map (MulAut.conj g⁻¹).toMonoidHom := by
      change Γ.twoResidualAt (Γ.act g cp.a) = (Γ.twoResidualAt cp.a).map _
      rw [Γ.twoResidualAt_def, Γ.twoResidualAt_def]
      change twoResidualIn (stabilizer Γ (Γ.act g cp.a)) =
        (twoResidualIn (stabilizer Γ cp.a)).map (MulAut.conj g⁻¹).toMonoidHom
      rw [stabilizer_act, conjugateBy, twoResidualIn_map_equiv]
    change twoCoreIn (e Γ cp.a') ≤ q Γ neighbor at hbound
    rw [← hedge.1, ← hedge.2, he, SevenSix.twoCoreIn_map_equiv, SevenSix.q_act] at hbound
    exact lemma_eight_three_local ctx hcenter
      ((Subgroup.map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp hbound)
  · have hc : ⁅z Γ cp.firstStep, stabilizer Γ cp.firstStep⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (hcenter.trans (SevenSix.centerAmbient_le_centralizer _))
    have hact : ⁅z Γ (Γ.act g cp.firstStep), stabilizer Γ (Γ.act g cp.firstStep)⁆ = ⊥ := by
      rw [z_act, stabilizer_act, conjugateBy, ← Subgroup.map_commutator, hc, Subgroup.map_bot]
    rw [hedge.2] at hact
    exact False.elim (hend hact)

/-- Canonical-context compatibility wrapper for terminal residual-core noncontainment. -/
public theorem eight_four_terminal_core_noncontainment
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (neighbor : ctx.Γ.Vertex)
    (hadj : ctx.Γ.adjacent ctx.criticalPath.a' neighbor) :
    ¬ twoCoreIn (EAt ctx.Γ ctx.criticalPath.a') ≤ QAt ctx.Γ neighbor :=
  eight_four_terminal_core_noncontainment_local ctx.toEightFourContext hcenter neighbor hadj

end Stellmacher.SectionEight
