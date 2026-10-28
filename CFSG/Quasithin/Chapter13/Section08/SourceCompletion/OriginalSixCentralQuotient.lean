module

public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Definitions
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.SourceSetup
public import Theory.SpecificGroups.BinaryLinear.ActionCardinality
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeNonsplit

/-!
# The original natural A₆ central quotient from the seven module rows

For an ordinary A₆ two-core quotient, the canonical comparison with the
faithful actor preserves its order, 360. The orders of the seven possible
actors leave exactly the natural alternating-six row. Its action equivalence
marks the literal chosen central quotient, using the A₆ marking supplied by
that row. The original marking is used only to determine the actor's order.

Since A₆ is centerless, the same equivalence also intertwines the original
projection through the central core. The chosen module, its fixed-space
quotient, and its action are unchanged.

Source: Aschbacher–Smith, 12.2.2(3), printed p.795, and 13.5.2(3), p.915.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open Chapter12.Section02 ChapterB.QuasisimpleSource
open TransvectionRecognition.Component.ModelExtension

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The seven original module rows give a compatible natural-six marking on
the actual chosen central quotient. The resulting group marking is induced
by the surviving action row, rather than prescribed independently. -/
theorem original_six_central_quotient_natural_of_module_rows
    (D : ChosenModule T L V)
    (rows : ModuleAlternatives1222 D)
    (e₀ : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    ∃ (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
      (a : D.chosenCentralQuotient ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6)),
      ∀ l v, a (D.chosenCentralAction l v) =
        BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
          (e (QuotientGroup.mk' (pCore 2 L) l)) (a v) := by
  let := D.elementary
  let H := L ⊔ (T : Subgroup G)
  let : IsElementaryAbelian 2 (ReducedModule H) := reducedModule_elementary H
  let : IsMulCommutative (ReducedModule H) :=
    @IsElementaryAbelian.toIsMulCommutative 2 (ReducedModule H) _
      (reducedModule_elementary H)
  let : CommGroup (ReducedModule H) := IsMulCommutative.instCommGroup
  let := D.actionCentralizer_normal
  let : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hc : Nat.card (L ⧸ pCore 2 L) = 360 := by
    rw [Nat.card_congr e₀.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hfaith : Nat.card (L ⧸ (centralizer (V : Set G)).subgroupOf L) = 360 :=
    (Nat.card_congr (D.coreToFaithfulEquiv e₀.isSimpleGroup).symm.toEquiv).trans hc
  have hlinear (n : ℕ) (hn : n = 3 ∨ n = 4 ∨ n = 5)
      (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : False := by
    have he := (Nat.card_congr e.toEquiv).symm.trans hc
    rw [BinaryLinear.card_SL] at he
    rcases hn with rfl | rfl | rfl <;>
      norm_num [BinaryLinear.order, Fin.prod_univ_succ] at he
  have hsix : Nonempty (ActionEquiv D.faithfulCentralAction
      (alternatingNatural 6)) := by
    cases rows with
    | linear n hn e => exact False.elim (hlinear n hn e.groupEquiv)
    | linearThreeExtension e _ _ => exact False.elim (hlinear 3 (by simp) e)
    | linearFiveExterior e _ _ => exact False.elim (hlinear 5 (by simp) e)
    | alternating n hlo hhi e =>
      have he := (Nat.card_congr e.groupEquiv.toEquiv).symm.trans hfaith
      have hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
      rcases hn with rfl | rfl | rfl | rfl
      · rw [nat_card_alternatingGroup, Nat.card_fin] at he
        norm_num [Nat.factorial] at he
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
  obtain ⟨f⟩ := hsix
  refine ⟨(D.coreToFaithfulEquiv e₀.isSimpleGroup).trans f.groupEquiv,
    f.linearEquiv, ?_⟩
  intro l v
  have hf := f.intertwines
    (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf L) l) v
  change f.linearEquiv (D.chosenCentralAction l v) =
    BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
      ((D.coreToFaithfulEquiv e₀.isSimpleGroup).trans f.groupEquiv
        (QuotientGroup.mk' (pCore 2 L) l)) (f.linearEquiv v)
  rw [MulEquiv.trans_apply, D.coreToFaithfulEquiv_mk]
  simpa only [ChosenModule.faithfulCentralAction_mk,
    BinaryPermutation.alternatingNaturalRepresentation, alternatingNatural] using hf

omit [Finite G] in
private theorem centralCore_eq_twoCore_of_six
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) : centralCore L = pCore 2 L := by
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    apply card_eq_one.mp
    rw [Nat.card_congr (centerCongr e).toEquiv,
      alternatingGroup.center_eq_bot (by norm_num : 4 ≤ Nat.card (Fin 6)), card_bot]
  change (center (L ⧸ pCore 2 L)).comap (QuotientGroup.mk' (pCore 2 L)) = pCore 2 L
  rw [hz]
  exact QuotientGroup.ker_mk' _

/-- The natural marking from the original module rows uses exactly the
central-core projection required by the natural-six preparation theorem. -/
theorem original_six_central_core_natural_of_module_rows
    (D : ChosenModule T L V)
    (rows : ModuleAlternatives1222 D)
    (e₀ : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    ∃ (e : (L ⧸ centralCore L) ≃* alternatingGroup (Fin 6))
      (a : D.chosenCentralQuotient ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6)),
      ∀ l v, a (D.chosenCentralAction l v) =
        BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
          (e (QuotientGroup.mk' (centralCore L) l)) (a v) := by
  obtain ⟨e, a, ha⟩ := original_six_central_quotient_natural_of_module_rows D rows e₀
  let ec := QuotientGroup.quotientMulEquivOfEq (centralCore_eq_twoCore_of_six e₀)
  exact ⟨ec.trans e, a, ha⟩

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion
