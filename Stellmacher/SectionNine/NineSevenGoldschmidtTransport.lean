module

public import Stellmacher.SectionNine.NineSevenFourPathLocal
public import Stellmacher.SectionNine.NineSevenLongDistanceSetup

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem nineSeven_first_terminal_modules_noncommuting
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H} {embedding : G →* H}
    {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B) :
    ⁅VAt ctx.Γ ctx.criticalPath.firstStep, VAt ctx.Γ ctx.criticalPath.a'⁆ ≠ ⊥ := by
  intro hcommute
  apply nine_seven_terminal_initial_commutator_ne_bot ctx
  apply le_antisymm _ bot_le
  have hcontain :=
    (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.1
  have hbound := Subgroup.commutator_mono
    (show VAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.a' from le_rfl)
    hcontain
  rw [Subgroup.commutator_comm (VAt ctx.Γ ctx.criticalPath.a')
    (VAt ctx.Γ ctx.criticalPath.firstStep), hcommute] at hbound
  exact hbound

public theorem nineSeven_commuting_four_path_endpoints
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hfirstModel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (hstartModels : ∀ vertex, IsConjugateVertex ctx.Γ ctx.criticalPath.a vertex →
      QuotientIsModel (GAt ctx.Γ vertex) (QAt ctx.Γ vertex) SL2Two)
    (first second : Fin 5 → ctx.Γ.Vertex)
    (hfirst : first 0 = ctx.criticalPath.firstStep)
    (hsecond : second 0 = ctx.criticalPath.firstStep)
    (hfirstadj : ∀ index : Fin 4,
      ctx.Γ.adjacent (first index.castSucc) (first index.succ))
    (hsecondadj : ∀ index : Fin 4,
      ctx.Γ.adjacent (second index.castSucc) (second index.succ))
    (hfirstback : ∀ index : Fin 3,
      first index.castSucc.castSucc ≠ first index.succ.succ)
    (hsecondback : ∀ index : Fin 3,
      second index.castSucc.castSucc ≠ second index.succ.succ)
    (hcommute : ⁅VAt ctx.Γ (first 0), VAt ctx.Γ (first 4)⁆ = ⊥) :
    ⁅VAt ctx.Γ (second 0), VAt ctx.Γ (second 4)⁆ = ⊥ := by
  obtain ⟨actor, hactor⟩ :=
    (nineSeven_cubic_four_path_transitivity_local ctx hfirstModel hstartModels).2
      first second hfirst hsecond hfirstadj hsecondadj hfirstback hsecondback
  have hmap := congrArg
    (fun subgroup : Subgroup G => subgroup.map (MulAut.conj (actor : G)⁻¹).toMonoidHom)
    hcommute
  rw [Subgroup.map_commutator, Subgroup.map_bot] at hmap
  change ⁅(v ctx.Γ (first 0)).map (MulAut.conj (actor : G)⁻¹).toMonoidHom,
    (v ctx.Γ (first 4)).map (MulAut.conj (actor : G)⁻¹).toMonoidHom⁆ = ⊥ at hmap
  rw [← v_act, ← v_act, hactor 0, hactor 4] at hmap
  exact hmap

end Stellmacher.SectionNine
