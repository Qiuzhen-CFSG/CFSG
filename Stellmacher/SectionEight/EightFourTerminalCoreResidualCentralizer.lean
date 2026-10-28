module
public import Stellmacher.SectionEight.EightFourFixedClosureElementary
public import Stellmacher.SectionEight.EightFourTerminalCore
/-!
# The endpoint core has trivial residual centralizer

For the centered-first-step critical pair in (8.4), the endpoint two-core
has trivial intersection with the centralizer of the endpoint residual.
This supplies the center-free commutator deduction in source (8), printed
p.39 of Stellmacher, Journal of Algebra 190 (1997).

Transport the initial core residual-centralizer theorem along an edge to
the endpoint and its predecessor. The terminal center is noncentral because
it does not commute with the initial center already in its stabilizer.
Consequently the edge transporter cannot reverse the two vertex types:
that would transport the central first-step center to the terminal center.
Core and residual covariance then reflect the trivial centralizer intersection.

The local version uses the literal local graph and the proved initial-core
centralizer theorem. Its canonical statement remains an exact wrapper.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_four_terminal_core_residual_centralizer_trivial_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    QAt ctx.Γ ctx.criticalPath.a' ⊓
      Subgroup.centralizer (EAt ctx.Γ ctx.criticalPath.a' : Set H) = ⊥ := by
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
  have hlen := cp.length_pos
  let neighbor := cp.path ⟨cp.length-1,by omega⟩
  have hadj : Γ.adjacent cp.a' neighbor := by
    have he := cp.path_adj ⟨cp.length-1,by omega⟩
    have hi : (⟨cp.length-1,by omega⟩ : Fin cp.length).succ =
        ⟨cp.length,Nat.lt_succ_self _⟩ := by apply Fin.ext; simp; omega
    rw [hi,cp.path_end] at he
    exact Γ.adjacent_symm he
  obtain ⟨g, hedge | hedge⟩ :=
    (lemma_seven_one h Γ).edge_not_vertex_transitive.1 cp.firstStep_adj hadj
  · have hzero := eight_four_initial_core_residual_centralizer_trivial_local ctx hcenter
    have hq : q Γ cp.a' = (q Γ cp.a).conjBy g⁻¹ := by
      rw [← hedge.1, SevenSix.q_act]; rfl
    have he : e Γ cp.a' = (e Γ cp.a).conjBy g⁻¹ := by
      rw [← hedge.1]
      change Γ.twoResidualAt (Γ.act g cp.a) = (Γ.twoResidualAt cp.a).map (MulAut.conj g⁻¹).toMonoidHom
      rw [Γ.twoResidualAt_def,Γ.twoResidualAt_def]
      change twoResidualIn (stabilizer Γ (Γ.act g cp.a)) = _
      rw [stabilizer_act,conjugateBy,twoResidualIn_map_equiv]
      rfl
    apply le_bot_iff.mp
    intro v hv
    obtain ⟨t,ht,rfl⟩ := (hq ▸ (show v ∈ q Γ cp.a' from hv.1))
    have htE : t ∈ Subgroup.centralizer (e Γ cp.a : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      apply (MulAut.conj g⁻¹).injective
      change (MulAut.conj g⁻¹).toMonoidHom (a*t) =
        (MulAut.conj g⁻¹).toMonoidHom (t*a)
      rw [map_mul,map_mul]
      have haE : (MulAut.conj g⁻¹).toMonoidHom a ∈ e Γ cp.a' :=
        he.symm ▸ Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom ha
      exact Subgroup.mem_centralizer_iff.mp hv.2 _ haE
    have htb : t ∈ (⊥ : Subgroup H) := hzero ▸ (show t ∈ QAt ctx.Γ cp.a ⊓
      Subgroup.centralizer (EAt ctx.Γ cp.a : Set H) from ⟨ht,htE⟩)
    have htone : t = 1 := htb
    simp [htone]
  · have hc : ⁅z Γ cp.firstStep, stabilizer Γ cp.firstStep⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (hcenter.trans (SevenSix.centerAmbient_le_centralizer _))
    have hact : ⁅z Γ (Γ.act g cp.firstStep), stabilizer Γ (Γ.act g cp.firstStep)⁆ = ⊥ := by
      rw [z_act,stabilizer_act,conjugateBy,← Subgroup.map_commutator,hc,Subgroup.map_bot]
    rw [hedge.2] at hact
    exact False.elim (hend hact)

/-- Canonical specialization through the same endpoint and predecessor. -/
public theorem eight_four_terminal_core_residual_centralizer_trivial
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    QAt ctx.Γ ctx.criticalPath.a' ⊓
      Subgroup.centralizer (EAt ctx.Γ ctx.criticalPath.a' : Set H) = ⊥ := by
  exact eight_four_terminal_core_residual_centralizer_trivial_local ctx.toLocalContext hcenter

end Stellmacher.SectionEight
