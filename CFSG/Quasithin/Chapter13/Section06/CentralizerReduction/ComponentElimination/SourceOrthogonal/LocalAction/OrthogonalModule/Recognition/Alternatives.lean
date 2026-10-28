module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.Alternatives.Transport
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.Alternatives.Seed
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.Alternatives.OuterNatural
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.Alternatives.GroupRows
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.Alternatives.NaturalDual
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.SourceAction

/-!
# Selecting the orthogonal module from the full FF alternatives

The complete projective-line-corrected B.5.1 conclusion is obtained on the
actual upper module. Its iterated moved space equals that upper module,
and inclusion induces an equivariant equivalence of their central quotients.
The comparison selects the natural A₈ row and applies the proved extension
to the full plus action and the concrete six-dimensional orthogonal model.

The moving Sylow-fixed seed in Alternatives.Seed supplies a separate
obstruction for the natural-plus-dual comparison. Alternatives.OuterNatural
excludes the natural quotient and all repeated naturals using the actual
outer action. Alternatives.GroupRows excludes the incompatible group rows.
Alternatives.NaturalDual identifies the Sylow-fixed-space centralizer with
the source minimal parabolic using its outer invariance, contradicting the
moving seed. These exclusions exhaust the full list without splitting W_K
or discarding the central kernel of its moved space.

The source application retains the actual A₅ marking, earlier 13.6.2–16
configuration and all three literal conclusions of 13.6.23, including
the prime-to-three residual and the middle-node minimal parabolic. It
constructs the actual Sylow marking and promotes the selected component
action to orthogonal coordinates for the entire plus actor. The universal
corrected B.5.1 implication and component FF witness remain explicit inputs;
their discharge stays with the source-theorem assembly owner.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1,
printed p.99, and the paragraph following 13.6.23, printed p.933/PDF p.950.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.Alternatives
open ComponentSelection
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u
variable {G : Type u} [Group G] [Finite G] (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]

/-- All six B.5.1 clauses are retained, together with the proved identification
of the classified central quotient with the source central quotient. -/
theorem component_classification_with_section_equiv {Ξ : GroupClass.{u}}
    (classification : ProjectiveLine.QuasisimpleClassificationInput.{u,u} Ξ)
    (hY : K ∈ Yz L T z v)
    (hcore : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (e : plusImage K L T z v hL hz K ≃* alternatingGroup (Fin 8))
    (hsource : IsKGroup Ξ (Gv v))
    (s : MovedSection (representation K L T z v hL hz) (plusImage K L T z v hL hz K))
    (hff : IsFFModule (s.space.toRepresentation.comp (plusImage K L T z v hL hz K).subtype)) :
    ∃ c : ProjectiveLine.QuasisimpleSourceConclusion
        (s.space.toRepresentation.comp (plusImage K L T z v hL hz K).subtype) ⊤,
      c.sectionData.space.toSubmodule = ⊤ ∧
        Nonempty (ActionEquiv c.sectionData.action
          (s.action.comp (plusImage K L T z v hL hz K).subtype)) := by
  obtain ⟨c⟩ := component_moved_classification K L T z v hL hz classification hY hcore e hsource s hff
  let : IsQuasisimple (plusImage K L T z v hL hz K) :=
    plusImage_K_quasisimple K L T z v hL hz hY hcore
  exact ⟨c, iterated_space_eq_top _ _ s c.sectionData,
    ⟨iteratedActionEquiv _ _ s c.sectionData⟩⟩

/-- Exhaust the corrected action list using the actual A₈ actor and outer
extension. Only the orthogonal row and the natural-plus-dual row remain.
The latter is kept on the exact upper space required by clause (6). -/
theorem classified_orthogonal_or_naturalDual
    (hY : K ∈ Yz L T z v)
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (e : plusImage K L T z v hL hz K ≃* alternatingGroup (Fin 8))
    (hT : IsPGroup 2 (Tv T v)) (hcore : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (hout : ¬ plusImage K L T z v hL hz (Tv T v) ≤ plusImage K L T z v hL hz K)
    (s : MovedSection (representation K L T z v hL hz) (plusImage K L T z v hL hz K))
    (c : ProjectiveLine.QuasisimpleSourceConclusion
      (s.space.toRepresentation.comp (plusImage K L T z v hL hz K).subtype) ⊤) :
    IsAlternatingNatural (s.action.comp (plusImage K L T z v hL hz K).subtype) 8 ∨
      IsNaturalPlusDual
        (show Representation (ZMod 2)
          (⊤ : Subgroup (plusImage K L T z v hL hz K)) c.sectionData.space.toSubmodule from
          c.sectionData.space.toRepresentation.comp
            (⊤ : Subgroup (plusImage K L T z v hL hz K)).subtype) 4 := by
  let : IsQuasisimple (plusImage K L T z v hL hz K) :=
    plusImage_K_quasisimple K L T z v hL hz hY hcore
  rcases classification_group_rows _ e c.sectionData c.clause_one with
    ha | hl | hd | ⟨r, hr, _, hn⟩
  · exact Or.inl (natural_of_iterated_natural _ _ s c.sectionData 8 ha)
  · exact (classified_not_linearNatural K L T z v hL hz hK hLK e hT hcore hout s hY c hl).elim
  · exact Or.inr hd
  · exact (classified_not_repeatedNatural K L T z v hL hz hK hLK e hT hcore hout s hY c r hr hn).elim

/-- Exhaustive selection on the literal central quotient. The Sylow and
parabolic markings refer to the same SL₄(2) component, and clause (6)
excludes the last upper-space alternative. -/
theorem classified_component_natural
    (hY : K ∈ Yz L T z v)
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (hmove : ¬ Lv L v ≤ centralizer ({z} : Set G))
    (e4 : plusImage K L T z v hL hz K ≃* SL(4, ZMod 2))
    (hT : IsPGroup 2 (Tv T v)) (hcore : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (hout : ¬ plusImage K L T z v hL hz (Tv T v) ≤ plusImage K L T z v hL hz K)
    (s : MovedSection (representation K L T z v hL hz) (plusImage K L T z v hL hz K))
    (R : Sylow 2 (plusImage K L T z v hL hz K))
    (hR : (R : Subgroup (plusImage K L T z v hL hz K)).map
      (plusImage K L T z v hL hz K).subtype = plusImage K L T z v hL hz (Tv T v ⊓ K))
    (b : BinaryLinear.InvariantNodeActions.Basis 3)
    (hP : ((plusImage K L T z v hL hz (sourceParabolic K L T v)).subgroupOf
      (plusImage K L T z v hL hz K)).map
      (e4.trans (BinaryLinear.OuterCyclic.slEquivLinear 4)).toMonoidHom =
        BinaryLinear.InvariantNodeActions.minimalParabolic b (1 : Fin 3))
    (c : ProjectiveLine.QuasisimpleSourceConclusion
      (s.space.toRepresentation.comp (plusImage K L T z v hL hz K).subtype) ⊤) :
    IsAlternatingNatural (s.action.comp (plusImage K L T z v hL hz K).subtype) 8 := by
  let e := e4.trans alternatingEightLinearEquiv.symm
  exact (classified_orthogonal_or_naturalDual K L T z v hL hz hY hK hLK e hT hcore hout s c).resolve_right
     (classified_not_naturalDual K L T z v hL hz hK hLK hmove e4
      hT hcore hout s R hR b hP c)

/-- Apply the universal corrected B.5.1 input and discharge every competing
row. Local-family membership constructs the literal component Sylow; no
Sylow witness, selected row, or recognition record is an extra premise. -/
theorem component_natural_of_ff {Ξ : GroupClass.{u}}
    (classification : ProjectiveLine.QuasisimpleClassificationInput.{u,u} Ξ)
    (hsource : IsKGroup Ξ (Gv v))
    (hY : K ∈ Yz L T z v)
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (hmove : ¬ Lv L v ≤ centralizer ({z} : Set G))
    (e4 : plusImage K L T z v hL hz K ≃* SL(4, ZMod 2))
    (hT : IsPGroup 2 (Tv T v)) (hcore : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (hout : ¬ plusImage K L T z v hL hz (Tv T v) ≤ plusImage K L T z v hL hz K)
    (s : MovedSection (representation K L T z v hL hz) (plusImage K L T z v hL hz K))
    (b : BinaryLinear.InvariantNodeActions.Basis 3)
    (hP : ((plusImage K L T z v hL hz (sourceParabolic K L T v)).subgroupOf
      (plusImage K L T z v hL hz K)).map
      (e4.trans (BinaryLinear.OuterCyclic.slEquivLinear 4)).toMonoidHom =
        BinaryLinear.InvariantNodeActions.minimalParabolic b (1 : Fin 3))
    (hff : IsFFModule (s.space.toRepresentation.comp (plusImage K L T z v hL hz K).subtype)) :
    IsAlternatingNatural (s.action.comp (plusImage K L T z v hL hz K).subtype) 8 := by
  obtain ⟨c⟩ := component_moved_classification K L T z v hL hz classification hY hcore
    (e4.trans alternatingEightLinearEquiv.symm) hsource s hff
  obtain ⟨R, hR⟩ := Selection.ParabolicConstruction.plusSylowIntersection K L T z v hL hz hY.1
  exact classified_component_natural K L T z v hL hz hY hK hLK hmove e4 hT hcore hout
    s R hR b hP c

/-- Apply the full plus-action promotion and actual orthogonal model after
selecting the row on B.5.1's iterated section. Selection remains explicit. -/
theorem orthogonalCoordinates_of_classified_natural
    (hY : K ∈ Yz L T z v)
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (hT : IsPGroup 2 (Tv T v)) (hcore : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (hout : ¬ plusImage K L T z v hL hz (Tv T v) ≤ plusImage K L T z v hL hz K)
    (s : MovedSection (representation K L T z v hL hz) (plusImage K L T z v hL hz K))
    (c : ProjectiveLine.QuasisimpleSourceConclusion
      (s.space.toRepresentation.comp (plusImage K L T z v hL hz K).subtype) ⊤)
    (hnatural : IsAlternatingNatural
      (c.sectionData.action.comp (⊤ : Subgroup (plusImage K L T z v hL hz K)).subtype) 8) :
    ∃ d : NaturalMovedSection K L T z v hL hz,
      Module.finrank (ZMod 2) (d.upper.toSubmodule ⧸ d.central.toSubmodule) = 6 ∧
      ∀ g w, d.orthogonalCoordinates K L T z v hL hz (d.central.quotientRepresentation g w) =
        (Atlas.Order20160A8.DeletedEight.orthogonalHom (d.actor g)).val
          (d.orthogonalCoordinates K L T z v hL hz w) := by
  let : IsQuasisimple (plusImage K L T z v hL hz K) :=
    plusImage_K_quasisimple K L T z v hL hz hY hcore
  exact orthogonalCoordinates_of_component_natural K L T z v hL hz hK hLK hT hcore hout s
    (natural_of_iterated_natural _ _ s c.sectionData 8 hnatural)

section Source
variable {Ξ : GroupClass.{u}} {K L V : Subgroup G} {T : Sylow 2 G} {z v : G}
    (c : SourceAction.Configuration Ξ K L V T z v)
    (classification : ProjectiveLine.QuasisimpleClassificationInput.{u,u} Ξ)
include classification

/-- The source configuration selects the actual A₈ natural central quotient
on the canonical U_K. Its component FF premise is the remaining obligation
of the independent FF preparation owner. -/
theorem source_component_natural
    (hff : let := c.elementary
      IsFFModule ((movedSection K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed
        c.invariant c.lv_le).space.toRepresentation.comp
          (plusImage K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed K).subtype)) :
    let := c.elementary
    IsAlternatingNatural ((movedSection K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed
      c.invariant c.lv_le).action.comp
        (plusImage K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed K).subtype) 8 := by
  let := c.elementary
  exact component_natural_of_ff K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed
    classification (c.standing.qtke.involution_centralizer_sqtk c.v_order).2
    c.selected c.invariant c.lv_le c.seed_moved c.linear_four
    (T.isPGroup'.to_le inf_le_left) c.twoCore c.outside
    (movedSection K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed c.invariant c.lv_le)
    c.basis c.middle_parabolic hff

/-- The selected source component action extends to the full plus actor
and the actual six-dimensional orthogonal model, retaining the entire
fixed kernel. Universal B.5.1 and component FF remain explicit. -/
theorem source_orthogonalCoordinates
    (hff : let := c.elementary
      IsFFModule ((movedSection K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed
        c.invariant c.lv_le).space.toRepresentation.comp
          (plusImage K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed K).subtype)) :
    let := c.elementary
    ∃ d : NaturalMovedSection K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed,
      Module.finrank (ZMod 2) (d.upper.toSubmodule ⧸ d.central.toSubmodule) = 6 ∧
      ∀ g w, d.orthogonalCoordinates K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed
          (d.central.quotientRepresentation g w) =
        (Atlas.Order20160A8.DeletedEight.orthogonalHom (d.actor g)).val
          (d.orthogonalCoordinates K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed w) := by
  let := c.elementary
  exact orthogonalCoordinates_of_component_natural K L (T : Subgroup G) z v
    c.lv_invariant c.seed_fixed c.invariant c.lv_le (T.isPGroup'.to_le inf_le_left)
    c.twoCore c.outside
    (movedSection K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed c.invariant c.lv_le)
    (source_component_natural c classification hff)

end Source

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.Alternatives
