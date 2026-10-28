module

public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.EarlierModules
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockReductionRows
public import CFSG.Quasithin.Chapter13.Section03.SourceClassification.MaximalReduction
public import CFSG.Quasithin.Chapter14.Section03.CaseOneSource.CommutatorInput.At

/-!
# Fixed-space sieve for the original 13.3.2(3) module clause

The guarded seven-row catalogue reduces a chosen module with nonzero fixed
space to four concrete models.  The binary A₈ row is removed internally by
its quotient order, while the L₃ and G₂ rows are discharged by their exact
fixed-space source implications.  The A₆ row is returned with the literal
chosen-module action required by `OriginalFixedModule1332At`.

The two fixed-space implications remain explicit because they use different
source arguments: the L₃ route is the 12.4.2 fusion proof, and the G₂ route is
the independent Weyl-module exclusion.  No later Chapter 13.7 or
Counterexample hypotheses are introduced.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Chapter12.Section02
open Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
open Chapter12.Section04.SmallFusion
open ChapterB.QuasisimpleSource
open Chapter14.Section03.FaithfulSource
open Chapter13.Section03.SourceClassification
open Chapter13.Section03.Noncentrality.SupercriticalSource

universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G}

omit [Finite G] in
/-- Turn the actual `SL₃(2)` quotient marking into the source's `PSL₃(2)`
model.  This is only a model transport; the extension itself is retained by
the fixed-space callback below. -/
private theorem slThree_model
    {K W : Subgroup G} {D : ChosenModule T K W}
    (E : SLThreeExtension D) :
    ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 2 := by
  exact ⟨ZMod 2, inferInstance, inferInstance, by simp,
    ⟨E.quotientEquiv.trans ((BinaryLinear.OuterCyclic.slEquivLinear 3).trans
      (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide)).symm)⟩⟩

/-- The exact fixed-space callbacks consumed by the four-row sieve.  The
L₃ callback is intended to be instantiated with
`slThreeFixedSpace1242_of_source_at`; the G₂ callback is supplied by the
independent Weyl fixed-space exclusion. -/
@[expose] def FixedSpaceRows1332At : Prop :=
  ∀ (K W : Subgroup G),
    Hypothesis1223 KnownSimple.IsKnownSimple T K →
    (D : ChosenModule T K W) →
    W ⊓ centralizer (K : Set G) ≠ ⊥ →
    (∀ (_E : SLThreeExtension D),
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 2 →
      fixedSubgroup K W = ⊥) ∧
    (∀ (_E : ActionEquiv D.quotientAction
        (Atlas.G2.Natural.OrthogonalCover.action (ZMod 2))),
      fixedSubgroup K W = ⊥)

/-- The guarded row reduction proves the original fixed-module clause once
its two genuine fixed-space exclusions are supplied.  The maximal-component
callbacks provide the original 13.1.7/13.3.2 hypotheses for every faithful
component; the module catalogue is used only at the same ambient `G,T`. -/
theorem originalFixedModule1332At_of_fixed_space_rows
    (h1331 : Hypothesis1331 T L)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (quasisimple : ∀ I : Subgroup G, FaithfulMaximalLocal T I →
      IsQuasisimple (I ⧸ pCore 2 I))
    (models : ∀ I : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T I →
      MidSizeModel (Chapter1.XiQuotient I))
    (_structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (fixedRows : FixedSpaceRows1332At (T := T)) :
    OriginalFixedModule1332At T L := by
  intro h K hK W D
  let := D.actionCentralizer_normal
  intro hne
  obtain ⟨hK1223, _⟩ := faithful_hypothesis1223_of_maximal_models
    h1331.hypothesis1311 quasisimple models hK
  have hrows : ModuleAlternatives1222 D := modules K W hK1223 D
  obtain hred := reducibleModels_of_module_alternatives hK1223 D hne hrows
  rcases hred with hL3 | hA6 | hA8 | hG2
  · have hmodel := slThree_model hL3
    exact (hne ((fixedRows K W hK1223 D hne).1 hL3 hmodel)).elim
  · exact ⟨hA6⟩
  · have he := Nat.card_congr hA8.groupEquiv.toEquiv
    rw [nat_card_alternatingGroup, Nat.card_fin] at he
    norm_num [Nat.factorial] at he
    rcases (models K hK1223).card with hcard | hcard | hcard | hcard | hcard <;>
      rw [hcard] at he <;> norm_num at he
  · exact (hne ((fixedRows K W hK1223 D hne).2 hG2)).elim

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
