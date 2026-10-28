module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ExtraspecialInputs

/-!
# Source actions for every member of the original Y-family

The original counterexample, chosen natural module, flag and center-point
identity construct all of the extraspecial geometry consumed by 14.4.8.
Its application gives the literal full action and both whole parabolics
for every Y-member, before any second member or marked model is selected.

Only the universal earlier component-generation assertion 1.2.1(1) and
faithful classification 14.3.4 remain in addition to the named source setup
predecessors. The former has a proved A/C source route in
ChapterA.Section03.SourceComponents.Generation and
Chapter1.Section02.LocalComponents.Quotients; its specialization is retained
with this source assembly. The faithful-classification producer is
qt-d-1434-source. This theorem supplies no model catalogue or incidence
geometry and does not assert the large-case contradiction.

Source: Aschbacher--Smith, 14.4.8(2), printed p.1009.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.LocalAction LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Apply the extraspecial construction to the literal source 14.4.8 consumer.
In particular I₂T, rather than I₂ alone, is the whole plane parabolic. -/
theorem source_full_actions (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (components : EarlierComponentGeneration G)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∀ X : Subgroup G, X ∈ YFamily F.H T (F.Vi 2) (F.E g) →
      Nonempty (FullMovedSpaceAction T (F.I₂ L) (F.Li L 2) (F.Vi 2) X) ∧
      Quasithin.I5.RankTwoParabolics
        (localJoin (F.Li L 2) X ⊔ (T : Subgroup G) : Subgroup G)
        ((T : Subgroup G).subgroupOf (localJoin (F.Li L 2) X ⊔ (T : Subgroup G)))
        ((F.I₂ L ⊔ (T : Subgroup G)).subgroupOf
          (localJoin (F.Li L 2) X ⊔ (T : Subgroup G)))
        ((X ⊔ (T : Subgroup G)).subgroupOf
          (localJoin (F.Li L 2) X ⊔ (T : Subgroup G))) := by
  let := chosen.elementary
  let := source_intersection_elementary d earlier hq chosen structural alternatives F hne g hg hgH
  obtain ⟨extraspecial, hI⟩ :=
    source_extraspecial_data d earlier hq chosen structural alternatives F hne hZ g hg hgP hgH
  exact (source_lemma_14_4_8 components T (d.qtke.evenCharacteristic T) classification
    (source_natural_action d earlier hq chosen structural) F g hg extraspecial hI).2.2.2

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
