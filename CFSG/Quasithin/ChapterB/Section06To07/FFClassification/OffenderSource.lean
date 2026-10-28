module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Product
public import CFSG.Quasithin.ChapterB.Section06To07.OffenderGeneration
public import Theory.Representation.BinaryOffender.GeneratedCore

/-!
# Original B.5.3 input on the actual offender subgroup

Restrict the faithful binary action to its actual offender subgroup. This
subgroup is normal, so its normal two-core vanishes with the ambient two-core.
All its original best offenders still generate it. Pulling back through the
given SQTK cover supplies the literal cover of the restricted actor.

For a minimal parabolic, the proved offender-generation theorem also supplies
the original residual containment and Sylow supplement. The full earlier
B.5.6 implication can therefore be applied without assuming generation of
the ambient actor or a reduced component list.

Source: Aschbacher–Smith B.5.3, B.5.6 and B.6.9, printed pp.104–105 and 116.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) {K : GroupClass.{u}}

/-- The actual offender action satisfies every original B.5.3 hypothesis. -/
theorem offender_restriction_source_hypothesis
    (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    (hcover : Nonempty (SourceInduction.SQTKQuotient K G)) :
    SourceInduction.FFHypothesis K (ρ.comp (offenderSubgroup ρ).subtype) := by
  let Y := offenderSubgroup ρ
  let : Y.Normal := offenderSubgroup_normal ρ
  obtain ⟨c⟩ := hcover
  refine ⟨inferInstance, hf.comp Y.subtype_injective, ?_,
    offenderSubgroup_restrict_eq_top ρ, ⟨c.subgroup Y⟩⟩
  have hle : (pCore 2 Y).map Y.subtype ≤ pCore 2 G :=
    le_sSup ⟨inferInstance, pCore_isPGroup.map Y.subtype⟩
  apply Subgroup.map_injective Y.subtype_injective
  simpa only [Subgroup.map_bot] using le_bot_iff.mp (hle.trans_eq hcore)

/-- The earlier full B.5.6 classifier applies to the literal original offender action. -/
theorem offender_restriction_classification
    (earlier : SourceInduction.AdequateClassificationInput.{u,v} K)
    (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    (hcover : Nonempty (SourceInduction.SQTKQuotient K G)) :
    SourceInduction.AdequateAlternative (ρ.comp (offenderSubgroup ρ).subtype) :=
  earlier _ _ _ (offender_restriction_source_hypothesis ρ hf hcore hcover)

/-- The B.6.9 input gives both literal B.5.3 preparation and its original Sylow supplement. -/
theorem minimalParabolic_offender_source_hypotheses
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥) (hff : IsFFModule ρ)
    (hcover : Nonempty (SourceInduction.SQTKQuotient K G)) :
    SourceInduction.FFHypothesis K (ρ.comp (offenderSubgroup ρ).subtype) ∧
      pResidual 2 G ≤ offenderSubgroup ρ ∧
      offenderSubgroup ρ ⊔ (T : Subgroup G) = ⊤ :=
  ⟨offender_restriction_source_hypothesis ρ hf hcore hcover,
    offender_generation T hP ρ hff hcore⟩

end CFSG.Quasithin.ChapterB
