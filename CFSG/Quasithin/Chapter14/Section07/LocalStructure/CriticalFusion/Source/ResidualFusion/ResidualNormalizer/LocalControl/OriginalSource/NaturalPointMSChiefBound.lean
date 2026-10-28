module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.LocalControl.OriginalSource.NaturalPointMS
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.LocalControl.OriginalSource.ChiefBound

/-!
# The original 14.7.10 alternative from the natural-point MS theorem

The natural-point theorem supplies the natural or doubled-natural whole
commutator core on the literal Baumann MS pair. The established cubic-movement
chief-count theorem then bounds every complete chief series of the original
point residual by three noncentral two-factors. The characteristic-subgroup
branch gives the alternative Baumann normalizer containment.

This proves the exact Earlier14710 contract without a universal binary MS
classifier premise. Known-simple A/C supplies uniqueness; Structural1222
retains its independent earlier-source producer. The existing classifier-based
APIs remain available. NaturalPointMSDeduction applies this theorem to the
original Rudvalis datum and its final D-model consumer.

Source: Aschbacher--Smith C.1.37, printed pp.141--143; Lemma 14.7.10,
printed p.1045; and its 14.7.67(4) application, printed p.1070.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 ChapterC.NaturalPointControl
namespace ResidualNormalizer.LocalControl.OriginalSource
open NoncentralChiefRefinement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {κ : GroupClass.{u}}

/-- Apply cubic movement to the actual L₁ inclusion into L Baum(R₁).
The natural-point theorem supplies its small commutator core. -/
theorem chief_count_le_of_naturalPointMS (h : HigherRankHypothesis κ T L V 3)
    (structural : Chapter12.Section02.Structural1222 κ)
    (F : InvariantFlag T V 3) :
    letI := seed_normal h structural
    letI := seed_elementary h
    ∀ a : NaturalAction (V.subgroupOf (L ⊔ (T : Subgroup G))),
      ChapterC.BinaryMS.Input κ a.LJ a.BJ →
      ∀ s : ChiefSeries (F.Li L 1), s.head = ⊥ → s.last = ⊤ →
        s.noncentralTwoCount ≤ 3 := by
  let := seed_normal h structural
  let := seed_elementary h
  intro a input s h0 h1
  let : IsElementaryAbelian 2 ((V.subgroupOf (L ⊔ (T : Subgroup G))).subgroupOf a.J) :=
    IsElementaryAbelian.subgroupOf a.module_le_J
  obtain ⟨e,he⟩ := natural_or_double_of_msInput a input
  have hc := NaturalAction.core_card_le_of_models input e he
  have hLiL : F.Li L 1 ≤ L := (F.Li_le L 1).trans inf_le_left
  have hmem (l : F.Li L 1) :
      (⟨l,hLiL.trans le_sup_left l.property⟩ : ↥(L ⊔ (T : Subgroup G))) ∈
        pResidual 2 (L ⊔ (T : Subgroup G) : Subgroup G) := by
    rw [residual_eq h structural]
    exact hLiL l.property
  let f : F.Li L 1 →* a.J := {
    toFun := fun l => ⟨⟨l,hLiL.trans le_sup_left l.property⟩,
      (show pResidual 2 (L ⊔ (T : Subgroup G) : Subgroup G) ≤ a.J
        from le_sup_left) (hmem l)⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y heq
    exact Subtype.ext (congrArg (fun z : a.J => ((z : ↥(L ⊔ (T : Subgroup G))) : G)) heq)
  have hfL : f.range ≤ a.LJ := by
    rintro _ ⟨l,rfl⟩
    exact hmem l
  exact a.inMSGroup.chief_count_le_three input hc f hf hfL
    (pointResidual_quotient_card h F) s h0 h1

/-- The full source alternative, with only the earlier structural and
uniqueness inputs. -/
theorem chief_bound_or_baumann_normalizer_of_naturalPointMS (h : HigherRankHypothesis κ T L V 3)
    (structural : Chapter12.Section02.Structural1222 κ)
    (uniqueness : Uniqueness127 κ)
    (F : InvariantFlag T V 3) :
    (∀ s : ChiefSeries (F.Li L 1), s.head = ⊥ → s.last = ⊤ →
      s.noncentralTwoCount ≤ 3) ∨
    normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G) := by
  let := seed_normal h structural
  let := seed_elementary h
  rcases normalizer_or_msInput h structural uniqueness F with hn | ⟨a,_,⟨hi⟩⟩
  · exact Or.inr hn
  · exact Or.inl (chief_count_le_of_naturalPointMS h structural F a hi)

/-- The exact universal Earlier14710 contract. Known-simple A/C discharge
uniqueness and the natural-point theorem discharges the MS classification.
Structural1222 retains its existing producer. -/
theorem earlier14710_of_naturalPointMS
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) : Earlier14710.{u} := by
  intro G _ _ T L V F _ h _
  apply chief_bound_or_baumann_normalizer_of_naturalPointMS h structural ?_ F
  intro X _ _ hX S B hB
  exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hB

end ResidualNormalizer.LocalControl.OriginalSource
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
