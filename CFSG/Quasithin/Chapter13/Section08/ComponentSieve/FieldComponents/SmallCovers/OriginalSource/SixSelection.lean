module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource.SixModule

/-!
# Original six-cover selection with the native classification discharged

The original cubic operator, centralizer control, small quadratic ratio and
universal irreducible classification now come from SourceContext. The complete
three-way homogeneous F.9.18(4) alternatives still suffice to construct an
invariant hexacode constituent and a literal whole-module or quotient section.
The section includes a faithful H-star actor, its actual K-star image and
intertwining coordinates; its dimension is derived from those coordinates.

The constructed actor controls conjugation on the actual K*/Z(K*), preserving
the source parabolic types. In the reducible source case this conclusion follows
directly from native FF recognition, without the homogeneous alternatives.

These are applications of the newly discharged B.4 inputs, not the complete
six-cover exclusion. qt-d-138-fields-source retains the homogeneous-invariance
argument in the remaining irreducible case, the proper-residual geometry and
the terminal obstruction on the literal V_H/U_H permutation section.
qt-d-1381-source supplies the preceding SourceContext assumptions.
Source: Aschbacher–Smith, 13.8.21(2), printed p.956 (PDF p.973), using
F.9.18(4),(6), B.4.2(8) and B.4.5.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource
open Reduction Reduction.ModuleRecognition SourceCompletion
open LocalGeometry.DynkinExclusion
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
attribute [local instance] Selection.starImage_normal

private theorem component_le (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K) : K ≤ H :=
  (le_sup_left.trans le_sup_left).trans_eq c.component.generated

variable [IsElementaryAbelian 2 (Source.UH H V₃)] [(K.subgroupOf H).Normal]

/-- Only the homogeneous F.9.18(4) alternatives remain for this selection. -/
theorem source_six_cover_model_of_alternatives
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (e : (K ⧸ pCore 2 K) ≃* Components.Models.A6Triple)
    (act : QuotientAction H V₃ V₁)
    (P : Sylow 2 (Source.Hstar H))
    (hP : (P : Subgroup (Source.Hstar H)) = Source.starImage H (T : Subgroup G))
    (src : Recognition.Alternatives act.representation (Source.starImage H K) P
      (star_sylow_generation H K (T : Subgroup G) (source_six_cover_consequences c e).2.1 P hP)) :
    ∃ I : Subrepresentation act.representation,
      IsIrrPlus act.representation (Source.starImage H K) I.toSubmodule ∧
      Nonempty (HexacodeModel (Source.starImage H K) I.toRepresentation) := by
  let : Nontrivial (Additive (Source.Utilde H V₃ V₁)) := source_quotient_nontrivial c
  let eK := (Components.componentStarEquiv H K (component_le c) c.component.component).symm.trans e
  have hc : centralizer (Source.starImage H K : Set (Source.Hstar H)) ≤ Source.starImage H K := by
    rw [←source_six_cover_fitting c e]
    exact centralizer_generalizedFitting_le _
  obtain ⟨z,_,ho,hzc,hp⟩ := source_six_cover_cubic_polynomial c e act
  obtain ⟨I,hI,hm⟩ := Recognition.exists_model act.representation (Source.starImage H K) P
    (star_sylow_generation H K (T : Subgroup G) (source_six_cover_consequences c e).2.1 P hP)
    eK hc z ho hzc hp src
    (Recognition.smallInput_of_irreducibleInputs _ (source_six_cover_irreducibleInputs c e))
    (source_quotient_small_ratio c act)
  exact ⟨I,hI.isIrrPlus,hm⟩

/-- The source cubic action and actual B.4 classification construct the literal
whole-module or quotient hexacode section from the homogeneous alternatives. -/
theorem source_six_cover_section_of_alternatives
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (e : (K ⧸ pCore 2 K) ≃* Components.Models.A6Triple)
    (act : QuotientAction H V₃ V₁)
    (P : Sylow 2 (Source.Hstar H))
    (hP : (P : Subgroup (Source.Hstar H)) = Source.starImage H (T : Subgroup G))
    (src : Recognition.Alternatives act.representation (Source.starImage H K) P
      (star_sylow_generation H K (T : Subgroup G) (source_six_cover_consequences c e).2.1 P hP)) :
    Nonempty (HexacodeSection H K V₃ V₁ act) := by
  let : Nontrivial (Additive (Source.Utilde H V₃ V₁)) := source_quotient_nontrivial c
  let eK := (Components.componentStarEquiv H K (component_le c) c.component.component).symm.trans e
  have hc : centralizer (Source.starImage H K : Set (Source.Hstar H)) ≤ Source.starImage H K := by
    rw [←source_six_cover_fitting c e]
    exact centralizer_generalizedFitting_le _
  have hcenter : Nat.card (center (K ⧸ pCore 2 K)) = 3 :=
    (Nat.card_congr (centerCongr e).toEquiv).trans Hexacode.even_center_card
  have hmove : subspaceCommutator act.representation ⊤ (Source.starImage H K) = ⊤ := by
    apply top_unique
    apply (source_cover_residual_moves_quotient c hcenter act).ge.trans
    apply Submodule.span_mono
    rintro _ ⟨y,hy,v,hv,rfl⟩
    exact ⟨y,(map_mono (subgroupOf_mono H (coverResidualIn_le K))) hy,v,hv,rfl⟩
  obtain ⟨z,_,ho,hzc,hp⟩ := source_six_cover_cubic_polynomial c e act
  obtain ⟨I,hI,⟨m⟩⟩ := source_six_cover_model_of_alternatives c e act P hP src
  obtain ⟨W,hW,hkind,⟨q⟩⟩ := exists_hexacode_quotient act.representation
    (Source.starImage H K) eK (source_six_cover_irreducibleInputs c e) z ho hzc hc hp hmove
    (sectionInputs_of_small_ratio _ _ (source_quotient_small_ratio c act)) I hI m
  exact ⟨{
    denominator := W
    proper := hW
    denominator_kind := hkind
    actor := q.actor
    actor_injective := q.faithful
    component_image := q.component_image
    equivalence := q.coordinates
    intertwines := q.intertwines }⟩

/-- The recognized source section controls the actual action on K*/Z(K*). -/
theorem source_six_cover_natural_of_alternatives
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (e : (K ⧸ pCore 2 K) ≃* Components.Models.A6Triple)
    (act : QuotientAction H V₃ V₁)
    (P : Sylow 2 (Source.Hstar H))
    (hP : (P : Subgroup (Source.Hstar H)) = Source.starImage H (T : Subgroup G))
    (src : Recognition.Alternatives act.representation (Source.starImage H K) P
      (star_sylow_generation H K (T : Subgroup G) (source_six_cover_consequences c e).2.1 P hP))
    (eZ : ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) ≃* AlternatingSix.ShadowLocal.A6)
    (h : Source.Hstar H) :
    sourceAction H K ((le_sup_left.trans le_sup_left).trans_eq c.component.generated)
      c.component.component eZ h ∈
      AlternatingSix.ShadowLocal.natural := by
  obtain ⟨s⟩ := source_six_cover_section_of_alternatives c e act P hP src
  exact sourceAction_natural_of_actor H K (component_le c) c.component.component eZ
    s.actor s.actor_injective s.component_image h

/-- In the reducible source case, native FF recognition already forces natural
central-quotient conjugation, without any homogeneous-invariance assumption. -/
theorem source_six_cover_natural_of_proper_section
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (e : (K ⧸ pCore 2 K) ≃* Components.Models.A6Triple)
    (act : QuotientAction H V₃ V₁)
    (W : Subrepresentation act.representation) (hb : W ≠ ⊥) (ht : W ≠ ⊤)
    (eZ : ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) ≃* AlternatingSix.ShadowLocal.A6)
    (h : Source.Hstar H) :
    sourceAction H K ((le_sup_left.trans le_sup_left).trans_eq c.component.generated)
      c.component.component eZ h ∈
      AlternatingSix.ShadowLocal.natural := by
  obtain ⟨_,⟨m⟩,_⟩ := source_six_cover_proper_sections c e act W hb ht
  exact sourceAction_natural_of_actor H K (component_le c) c.component.component eZ
    m.actor m.faithful m.component_image h

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource
