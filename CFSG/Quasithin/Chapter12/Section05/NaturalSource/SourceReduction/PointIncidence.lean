module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Escaping.Source.Completion
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.SourceReduction.Selection

/-!
# The surviving point incidence in the seven-case reduction

The terminal construction forces G₁ ≤ M for every remaining exterior
marking. Controlled point fusion corrects any conjugator through z into
G₁, and the original TI property inside M then makes its whole conjugate
of V equal V. Apply seven-case selection to obtain either the full original
natural marking or an aligned exterior marking with this unique incidence.

This establishes the uniqueness conclusion used in 12.4.4 from the
completed local and terminal arguments. It does not prove the remaining
point escape: the noncommuting-conjugate and six-space steps of 12.4.4
remain with qt-d-1251-source. Earlier structural/module inputs are only
at the same G,T; their final discharge remains with qt-d-1332-source.
Source: Aschbacher--Smith, 12.4.4 and 12.5.1, printed pp.813,816--822.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}

namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)
  (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
  (structural : Structural1222At KnownSimple.IsKnownSimple T)
include h structural

/-- Fusion and the original TI property give uniqueness through the marked point. -/
theorem conjugate_eq_of_contains_point {g : G}
    (hg : s.marking.z ∈ V.map (MulAut.conj g).toMonoidHom) :
    V.map (MulAut.conj g).toMonoidHom = V := by
  have p := s.pointControl_from_source h structural
  obtain ⟨c,hc⟩ := exists_centralizer_conjugator_of_element_fusion
    (fun x hx => by
      obtain ⟨l,hl,he⟩ := p.fusion x hx
      exact ⟨l,D.normalizes hl,he.symm⟩) hg
  have hcG : (c : G) ∈ s.marking.Gi 1 := p.point_centralizer.symm ▸ c.property
  have hcM := s.point_group_le_M_from_terminal h structural hcG
  rcases ((structural L h).2.2 V D).2.2.1 (c : G) hcM with hbot | he
  · have hz : s.marking.z ∈ V ⊓ V.map (MulAut.conj (c : G)).toMonoidHom :=
      ⟨s.marking.z_mem,hc.symm ▸ hg⟩
    exact (s.marking.z_ne_one (mem_bot.mp (hbot ▸ hz))).elim
  · exact hc.symm.trans he

end SylowExteriorMarking

/-- Apply seven-case selection to the original module. Any remaining exterior
branch has the point containment and unique-conjugate incidence derived above. -/
theorem natural_or_exterior_with_point_incidence
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 5 2) :
    Section09.NaturalModule D 5 ∨
      ∃ s : SylowExteriorMarking D, s.marking.Gi 1 ≤ s.marking.M ∧
        ∀ g : G, s.marking.z ∈ V.map (MulAut.conj g).toMonoidHom →
          V.map (MulAut.conj g).toMonoidHom = V := by
  rcases natural_or_exterior_of_moduleAlternatives D hL (modules L V h D) with hn | ha
  · exact Or.inl hn
  · obtain ⟨a⟩ := ha
    obtain ⟨s,_⟩ := exists_sylow_marking_with_local_source h structural a
    exact Or.inr ⟨s,s.point_group_le_M_from_terminal h structural,
      fun _ hg => s.conjugate_eq_of_contains_point h structural hg⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
