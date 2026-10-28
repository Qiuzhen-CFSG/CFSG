module
public import Stellmacher.SectionNine.NineThreeNextModuleCentralizerTwo

/-!
# Centralizers of the neighbor-center module along its vertex orbit

In the genuine ambient Section Nine setting, the centralizer of V at any
vertex conjugate to the first step lies in that vertex's two-core. The
proved first-step result uses the ambient characteristic-two hypothesis;
conjugating it retains that hypothesis without constructing a new context.

A multiplicative equivalence transports full centralizers. Combine this
with the graph covariance formulas for the neighbor-center module and the
two-core, and map the first-step containment. This is used at the terminal
vertex in the second fixed-subgroup argument of Stellmacher (9.3), p.49 of
Journal of Algebra 190 (1997), `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem centralizer_map_equiv {G : Type u} [Group G]
    (f : G ≃* G) (K : Subgroup G) :
    (Subgroup.centralizer (K : Set G)).map f.toMonoidHom =
      Subgroup.centralizer (K.map f.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact Subgroup.map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨f.symm x, ?_, f.apply_symm_apply x⟩
    rw [Subgroup.mem_centralizer_iff] at hx
    change ∀ k ∈ K, k * f.symm x = f.symm x * k
    intro k hk
    apply f.injective
    simpa only [map_mul, f.apply_symm_apply] using
      hx (f k) (Subgroup.mem_map_of_mem _ hk)

public theorem nine_three_module_centralizer_core_at_vertex
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (d : ctx.Γ.Vertex)
    (hd : IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep d) :
    Subgroup.centralizer (VAt ctx.Γ d : Set G) ≤ QAt ctx.Γ d := by
  obtain ⟨g,rfl⟩ := hd
  change Subgroup.centralizer (v ctx.Γ (ctx.Γ.act g ctx.criticalPath.firstStep) : Set G) ≤
    q ctx.Γ (ctx.Γ.act g ctx.criticalPath.firstStep)
  rw [v_act,q_act,← centralizer_map_equiv]
  exact Subgroup.map_mono (nine_three_next_module_centralizer_two ctx).2

end Stellmacher.SectionNine
