module

public import CFSG.Quasithin.Chapter13.Section03.SourceClassification.OriginalAlternatingFiveAt
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import Theory.SpecificGroups.BinaryLinear.ActionCardinality
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeNonsplit

/-!
# Automatic A₅ marking from the guarded seven-row module catalogue

The seven-row predicate already contains literal actions.  If the same
component also has an A₅ two-core quotient, cardinality removes every row
except the alternating-five row.  Transport through `coreToFaithfulEquiv`
then gives the exact chosen central quotient and its original action.

This is a narrow adapter for the 13.3.2 consumer; it does not strengthen the
universal module theorem or identify unrelated module rows.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.SourceClassification
open CFSG.Quasithin.Chapter12.Section02
open ChapterB.QuasisimpleSource
open Chapter13.Section03.SourceCompletion
open Chapter13.Section03.Noncentrality.SupercriticalSource

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem central_quotient_natural_of_module_rows
    (D : ChosenModule T L V)
    (rows : ModuleAlternatives1222 D)
    (e₀ : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) :
    letI := D.actionCentralizer_normal
    ∃ (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
      (a : D.chosenCentralQuotient ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5)),
      ∀ l v, a (D.chosenCentralAction l v) =
        Chapter6.Source.a5Module (e (QuotientGroup.mk' (pCore 2 L) l)) (a v) := by
  let := D.elementary
  let H := L ⊔ (T : Subgroup G)
  let : IsElementaryAbelian 2 (ReducedModule H) := reducedModule_elementary H
  let : IsMulCommutative (ReducedModule H) :=
    @IsElementaryAbelian.toIsMulCommutative 2 (ReducedModule H) _
      (reducedModule_elementary H)
  let : CommGroup (ReducedModule H) := IsMulCommutative.instCommGroup
  let := D.actionCentralizer_normal
  let : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hc : Nat.card (L ⧸ pCore 2 L) = 60 := by
    rw [Nat.card_congr e₀.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hfaith : Nat.card (L ⧸ (centralizer (V : Set G)).subgroupOf L) = 60 :=
    (Nat.card_congr (D.coreToFaithfulEquiv e₀.isSimpleGroup).symm.toEquiv).trans hc
  have hlinear (n : ℕ) (hn : n = 3 ∨ n = 4 ∨ n = 5)
      (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : False := by
    have he := (Nat.card_congr e.toEquiv).symm.trans hc
    rw [BinaryLinear.card_SL] at he
    rcases hn with rfl | rfl | rfl <;>
      norm_num [BinaryLinear.order, Fin.prod_univ_succ] at he
  have hfive : Nonempty (ActionEquiv D.faithfulCentralAction
      (alternatingNatural 5)) := by
    cases rows with
    | linear n hn e => exact False.elim (hlinear n hn e.groupEquiv)
    | linearThreeExtension e _ _ => exact False.elim (hlinear 3 (by simp) e)
    | linearFiveExterior e _ _ => exact False.elim (hlinear 5 (by simp) e)
    | alternating n hlo hhi e =>
      have he := (Nat.card_congr e.groupEquiv.toEquiv).symm.trans hfaith
      have hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
      rcases hn with rfl | rfl | rfl | rfl
      · exact ⟨e⟩
      all_goals
        rw [nat_card_alternatingGroup, Nat.card_fin] at he
        norm_num [Nat.factorial] at he
    | alternatingSevenFour e _ =>
      have he := (Nat.card_congr e.toEquiv).symm.trans hfaith
      rw [nat_card_alternatingGroup, Nat.card_fin] at he
      norm_num [Nat.factorial] at he
    | g2 e =>
      have he := (Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc
      rw [Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at he
      norm_num at he
    | tripleSix e _ _ _ =>
      have he := (Nat.card_congr e.toEquiv).symm.trans hc
      rw [Atlas.Codes.hexEven_card] at he
      norm_num at he
  obtain ⟨f⟩ := hfive
  refine ⟨(D.coreToFaithfulEquiv e₀.isSimpleGroup).trans f.groupEquiv,
    f.linearEquiv, ?_⟩
  intro l v
  have hf := f.intertwines
    (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf L) l) v
  change f.linearEquiv (D.chosenCentralAction l v) =
    Chapter6.Source.a5Module
      ((D.coreToFaithfulEquiv e₀.isSimpleGroup).trans f.groupEquiv
        (QuotientGroup.mk' (pCore 2 L) l)) (f.linearEquiv v)
  rw [MulEquiv.trans_apply, D.coreToFaithfulEquiv_mk]
  simpa only [ChosenModule.faithfulCentralAction_mk, Chapter6.Source.a5Module,
    ChapterB.QuasisimpleSource.alternatingNatural] using hf

/-- The guarded 13.3.2 A₅ clause follows directly from the guarded seven-row
catalogue, with no independent naturality callback. -/
theorem originalAlternatingFiveModules1332At_of_module_rows
    (quasisimple : ∀ I : Subgroup G, FaithfulMaximalLocal T I →
      IsQuasisimple (I ⧸ pCore 2 I))
    (models : ∀ I : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T I →
      MidSizeModel (Chapter1.XiQuotient I))
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T) :
    OriginalAlternatingFiveModules1332At T L := by
  apply originalAlternatingFiveModules1332At_of_central_quotient quasisimple models
  intro K hK hfive I D
  obtain ⟨e₀⟩ := hfive
  exact central_quotient_natural_of_module_rows D (modules K I hK D) e₀

end CFSG.Quasithin.Chapter13.Section03.SourceClassification
