module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.LocalControl.OriginalSource.ClassificationConsequences
public import CFSG.Quasithin.ChapterC.Section01.NaturalPointControl.ChiefBound
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.SourceKnownSimple
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.LocalControl
public import Theory.SpecificGroups.BinaryLinear.DerivedTwoCardinality

/-!
# The original 14.7.10 alternative from binary MS classification

The actual point residual L₁ has two-core quotient of order three. Its
literal inclusion in L Baum(R₁) places all its cubic commutators under the
natural-point chief-count theorem. The original classification alternatives
therefore bound every complete L₁ chief series by three noncentral two-factors.
The characteristic-subgroup branch gives the alternative Baumann normalizer
containment, completing the exact universal Earlier14710 contract.

The independent binary C.1.34 classifier remains explicit, owned by
qt-rank-two-ms93. Structural1222 retains qt-d-1222-source as producer.
Known-simple A/C discharge uniqueness. The actual OriginalInputs and
LocalAlternatives applications are in BaumannDeduction; qt-d-14775-source
retains final Rudvalis assembly and the discharge of its earlier sources.

Source: Aschbacher--Smith C.1.37, printed pp.141--143, and Lemma 14.7.10,
printed p.1045 (PDF p.1062), with the 14.7.67(4) application on p.1070.
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

/-- The original point residual has its literal two-core quotient of order three. -/
theorem pointResidual_quotient_card (h : HigherRankHypothesis κ T L V 3)
    (F : InvariantFlag T V 3) : Nat.card (F.Li L 1 ⧸ pCore 2 (F.Li L 1)) = 3 := by
  let := h.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  obtain ⟨m⟩ := F.naturalSeedMarking_of_ambient (by decide : 3 ≤ 3) L
    h.chosen.normalizes h.naturalMarking
  exact (Nat.card_congr m.quotientEquiv.toEquiv).trans BinaryLinear.SmallParabolicLevi.derived_two_card

/-- Apply cubic movement to the actual L₁ inclusion into L Baum(R₁).
The independent classification supplies its small commutator core. -/
theorem chief_count_le_of_msInput (h : HigherRankHypothesis κ T L V 3)
    (structural : Chapter12.Section02.Structural1222 κ)
    (binary : BinaryMSClassification κ) (F : InvariantFlag T V 3) :
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
  obtain ⟨e,he⟩ := natural_or_double_of_classification binary a input
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

/-- The full source alternative, conditional only on the earlier structural,
uniqueness, and independent binary MS theorems. -/
theorem chief_bound_or_baumann_normalizer (h : HigherRankHypothesis κ T L V 3)
    (structural : Chapter12.Section02.Structural1222 κ)
    (uniqueness : Uniqueness127 κ) (binary : BinaryMSClassification κ)
    (F : InvariantFlag T V 3) :
    (∀ s : ChiefSeries (F.Li L 1), s.head = ⊥ → s.last = ⊤ →
      s.noncentralTwoCount ≤ 3) ∨
    normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G) := by
  let := seed_normal h structural
  let := seed_elementary h
  rcases normalizer_or_msInput h structural uniqueness F with hn | ⟨a,_,⟨hi⟩⟩
  · exact Or.inr hn
  · exact Or.inl (chief_count_le_of_msInput h structural binary F a hi)

/-- The exact universal Earlier14710 contract. Known-simple A/C discharge
uniqueness; qt-rank-two-ms93 retains the classifier and qt-d-1222-source
retains Structural1222 for the final qt-d-14775-source assembly. -/
theorem earlier14710_of_binary
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (binary : BinaryMSClassification KnownSimple.IsKnownSimple.{u}) : Earlier14710.{u} := by
  intro G _ _ T L V F _ h _
  apply chief_bound_or_baumann_normalizer h structural ?_ binary F
  intro X _ _ hX S B hB
  exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hB

end ResidualNormalizer.LocalControl.OriginalSource
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
