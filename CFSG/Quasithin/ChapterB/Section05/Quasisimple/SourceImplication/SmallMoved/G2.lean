module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.Representation.G2NaturalOffenders.SmallMoved

/-!
# Excluding the genuine G₂ rows under the original seed-plane bound

The original offender and whole moved-space bound descend to the actual
central quotient of the moved section. The marked actor equivalence then
carries them to the natural G₂ module, where B.4.6(13) produces a short root
moving at least three binary dimensions. Both the defining-field row and
the small marked G₂(2)′ row are covered, without replacing G₂(2) by its derived
group or assuming a split original module.

Source: Aschbacher–Smith 13.7.15(1), printed pp.943–944.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SmallMoved
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

omit [FiniteDimensional (ZMod 2) V] in
/-- The exclusion before any choice of original central extension. -/
theorem not_g2_model_of_plane {A H : Subgroup G}
    (hA : IsOffender ρ A) (hAH : A ≤ H)
    (hd : Module.finrank (ZMod 2) (moved ρ A) ≤ 2)
    (F : BinaryField) (e : ActionEquiv (ρ.comp H.subtype) (binaryG2 F)) : False := by
  have hAr := hA.subgroupOf ρ hAH
  have hAm := hAr.map_equivariant (ρ.comp H.subtype) (binaryG2 F)
    e.groupEquiv.toMonoidHom e.groupEquiv.injective e.linearEquiv e.intertwines
  have he := moved_finrank_equivariant (ρ.comp H.subtype) (binaryG2 F)
    e.groupEquiv.toMonoidHom e.linearEquiv e.intertwines (A.subgroupOf H)
  rw [subspaceCommutator_comp_map, map_subgroupOf_eq_of_le hAH] at he
  have hm := Atlas.G2.NaturalOffenders.natural_offender_moved_gt_two F.card_eq F.degree_pos
    ((A.subgroupOf H).map e.groupEquiv.toMonoidHom) hAm
  exact (not_lt_of_ge (he.symm.le.trans hd)) hm

/-- A natural G₂ model on the actual quotient cannot occur under the plane bound. -/
theorem not_g2_quotient_of_plane {A L H : Subgroup G}
    (hA : IsOffender ρ A) (hAH : A ≤ H)
    (hd : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) ≤ 2)
    (s : MovedSection ρ L) (F : BinaryField)
    (e : ActionEquiv (s.central.quotientRepresentation.comp H.subtype) (binaryG2 F)) : False := by
  let Q := s.central.quotientRepresentation
  have hq := hA.on_subquotient ρ s.space s.central
  have hdq := (moved_finrank_quotient_le s.space.toRepresentation s.central A).trans
    ((moved_finrank_subrepresentation_le ρ s.space A).trans hd)
  have hAr := hq.subgroupOf Q hAH
  have hAm := hAr.map_equivariant (Q.comp H.subtype) (binaryG2 F)
    e.groupEquiv.toMonoidHom e.groupEquiv.injective e.linearEquiv e.intertwines
  have he := moved_finrank_equivariant (Q.comp H.subtype) (binaryG2 F)
    e.groupEquiv.toMonoidHom e.linearEquiv e.intertwines (A.subgroupOf H)
  rw [subspaceCommutator_comp_map, map_subgroupOf_eq_of_le hAH] at he
  have hm := Atlas.G2.NaturalOffenders.natural_offender_moved_gt_two F.card_eq F.degree_pos
    ((A.subgroupOf H).map e.groupEquiv.toMonoidHom) hAm
  exact (not_lt_of_ge (he.symm.le.trans hdq)) hm

/-- The small derived endpoint uses the full marked G₂(2) actor, as in B.4.2. -/
theorem not_g2Two_quotient_of_plane {A L H : Subgroup G}
    (hA : IsOffender ρ A) (hAH : A ≤ H)
    (hd : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) ≤ 2)
    (s : MovedSection ρ L)
    (e : MarkedActionEquiv s.central.quotientRepresentation H L (g2Natural (ZMod 2))
      (commutator (Atlas.G2.Model (ZMod 2)))) : False := by
  exact not_g2_quotient_of_plane ρ hA hAH hd s BinaryField.two e.action
end CFSG.Quasithin.ChapterB.QuasisimpleSource.SmallMoved
