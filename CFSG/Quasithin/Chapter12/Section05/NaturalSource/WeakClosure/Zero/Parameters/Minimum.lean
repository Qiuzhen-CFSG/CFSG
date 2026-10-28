module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Zero.Parameters.Actor
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# The involution minimum for the full exterior automizer

Transport the complete involution calculation through the constructed
equivalence of the full ambient automizer with SL₅(2). Every involution
has fixed codimension three or four, and the first representative attains
three. Taking the actual minimum defining Chapter E's localM gives three,
using precisely the elementary abelian structure of the chosen module.

Source: Aschbacher--Smith, 12.5.5(1) and 12.5.6, printed pp.819--820.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 ChapterE
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)
include s

/-- Both the universal lower bound and its attaining full-automizer witness. -/
theorem full_automizer_involution_codimensions
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    let := D.elementary
    (∀ t : Automizer V, orderOf t = 2 →
      fixedCodim (automizerRepresentation V) (zpowers t) = 3 ∨
        fixedCodim (automizerRepresentation V) (zpowers t) = 4) ∧
      ∃ t : Automizer V, orderOf t = 2 ∧
        fixedCodim (automizerRepresentation V) (zpowers t) = 3 := by
  let := D.elementary
  obtain ⟨e, he⟩ := s.exists_full_automizer_equiv h
  have hc (t : Automizer V) :
      fixedCodim (automizerRepresentation V) (zpowers t) =
        Module.finrank (ZMod 2) (LinearMap.range (SL5ExteriorSquare.displacement (e t))) := by
    rw [fixedCodim_map_equivariant (automizerRepresentation V)
      (SL5TenDimensional.exteriorAction 2) e.toMonoidHom s.marking.linearCoordinates he,
      MonoidHom.map_zpowers, fixedCodim_zpowers_eq_displacement_rank]
    rfl
  constructor
  · intro t ht
    have hg : orderOf (e t) = 2 := (e.orderOf_eq t).trans ht
    have hg2 := (orderOf_eq_prime_iff.mp hg).1
    have hgne := (orderOf_eq_prime_iff.mp hg).2
    have hr := SL5ExteriorSquare.involution_displacement_ranks (e t) hgne
      (by simpa only [pow_two] using hg2)
    rw [hc]
    exact hr.imp And.right And.right
  · refine ⟨e.symm SL5ExteriorSquare.j₁, ?_, ?_⟩
    · rw [e.symm.orderOf_eq]
      exact orderOf_eq_prime (by simpa only [pow_two] using SL5ExteriorSquare.j₁_sq)
        SL5ExteriorSquare.j₁_ne_one
    · rw [hc, e.apply_symm_apply]
      exact SL5ExteriorSquare.finrank_displacement_j₁

/-- The local numerical clause of source 12.5.6 for the entire automizer. -/
theorem localM_eq_three
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    let := D.elementary
    localM V = 3 := by
  let := D.elementary
  obtain ⟨hlower, t, ht, hc⟩ := s.full_automizer_involution_codimensions h
  apply le_antisymm
  · exact (moduleM_le_involution (automizerRepresentation V) ht).trans_eq hc
  · change 3 ≤ sInf _
    apply le_csInf ⟨_, Set.mem_insert _ _⟩
    rintro n (rfl | ⟨x, hx, rfl⟩)
    · have hd := s.marking.linearCoordinates.finrank_eq.trans
        SL5TenDimensional.finrank_exteriorModule_two
      omega
    · rcases hlower x hx with h3 | h4 <;> omega

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
