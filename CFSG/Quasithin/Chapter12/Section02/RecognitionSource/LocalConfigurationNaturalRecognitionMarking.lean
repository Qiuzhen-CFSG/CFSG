module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalRecognitionMarkingImage
public import Theory.SpecificGroups.BinaryLinear.ActionCardinality
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder

/-!
# Selecting the marked natural row from the full LT image

Fullness of the component action bounds the order of GL(V) by the orders
of both literal acting quotients. The same bound applies to GL(V/C_V(L)):
a complement embeds this group into GL(V). Each nonnatural row of 12.2.2
has an actor too small for its stated module dimension, so only the natural
SL₃(2), SL₄(2), and SL₅(2) rows survive. This includes exclusion of the
four-dimensional indecomposable SL₃(2) extension without assuming
irreducibility. The surviving ActionEquiv acts through the original L/O₂(L).

Source: Aschbacher–Smith 12.2.2(3a–g) and 12.2.20, printed pp.795,802.
The binary G₂ and hexacode orders reuse the licensed ATLAS ports; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

theorem chosen_GL_card_le_core_quotient_of_join_full
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hf : letI := D.elementary; (chosenJoinLinearAction D hT).range = ⊤) :
    Nat.card (BinaryLinear.GL D.space) ≤ Nat.card (L ⧸ pCore 2 L) :=
  BinaryLinear.card_GL_le_of_full D.quotientAction
    (chosen_quotientLinearAction_surjective_of_join_full h D hT hf)

theorem chosen_GL_card_le_faithful_quotient_of_join_full
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hf : letI := D.elementary; (chosenJoinLinearAction D hT).range = ⊤) :
    letI := D.actionCentralizer_normal
    Nat.card (BinaryLinear.GL D.space) ≤
      Nat.card (L ⧸ (centralizer (V : Set G)).subgroupOf L) := by
  let := D.actionCentralizer_normal
  exact BinaryLinear.card_GL_le_of_full D.faithfulAction
    (chosen_faithfulLinearAction_surjective_of_join_full h D hT hf)

theorem chosen_centralQuotient_GL_card_le (D : ChosenModule T L V) :
    Nat.card (BinaryLinear.GL D.chosenCentralQuotient) ≤ Nat.card (BinaryLinear.GL D.space) :=
  BinaryLinear.card_GL_quotient_le _

private theorem alternating_GL_card_gt {n : ℕ} (hlo : 5 ≤ n) (hhi : n ≤ 8) :
    Nat.card (alternatingGroup (Fin n)) <
      Nat.card (BinaryLinear.GL (BinaryPermutation.natural (Fin n))) := by
  interval_cases n
  · have hd : Module.finrank (ZMod 2) (BinaryPermutation.natural (Fin 5)) = 4 := by
      simpa using BinaryPermutation.finrank_natural_odd (Ω := Fin 5) (by decide)
    rw [BinaryLinear.card_GL_of_finrank hd, nat_card_alternatingGroup]
    norm_num [BinaryLinear.order, Fin.prod_univ_succ, Nat.factorial]
  · have hd : Module.finrank (ZMod 2) (BinaryPermutation.natural (Fin 6)) = 4 := by
      simpa using BinaryPermutation.finrank_natural_even (Ω := Fin 6) (by decide)
    rw [BinaryLinear.card_GL_of_finrank hd, nat_card_alternatingGroup]
    norm_num [BinaryLinear.order, Fin.prod_univ_succ, Nat.factorial]
  · have hd : Module.finrank (ZMod 2) (BinaryPermutation.natural (Fin 7)) = 6 := by
      simpa using BinaryPermutation.finrank_natural_odd (Ω := Fin 7) (by decide)
    rw [BinaryLinear.card_GL_of_finrank hd, nat_card_alternatingGroup]
    norm_num [BinaryLinear.order, Fin.prod_univ_succ, Nat.factorial]
  · have hd : Module.finrank (ZMod 2) (BinaryPermutation.natural (Fin 8)) = 6 := by
      simpa using BinaryPermutation.finrank_natural_even (Ω := Fin 8) (by decide)
    rw [BinaryLinear.card_GL_of_finrank hd, nat_card_alternatingGroup]
    norm_num [BinaryLinear.order, Fin.prod_univ_succ, Nat.factorial]

private theorem GL_card_congr {W X : Type*} [AddCommGroup W] [AddCommGroup X]
    [Module (ZMod 2) W] [Module (ZMod 2) X] (e : W ≃ₗ[ZMod 2] X) :
    Nat.card (BinaryLinear.GL W) = Nat.card (BinaryLinear.GL X) := by
  exact Nat.card_congr ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).symm.trans
    ((LinearMap.GeneralLinearGroup.congrLinearEquiv e).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) X))).toEquiv

theorem chosen_natural_marking_of_join_full
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G))
    (rows : ModuleAlternatives1222 D)
    (hf : letI := D.elementary; (chosenJoinLinearAction D hT).range = ⊤) :
    ∃ d, (3 ≤ d ∧ d ≤ 5) ∧ Nonempty (ActionEquiv D.quotientAction
      (Representation.specialLinearNatural (k := ZMod 2) d)) := by
  have hc := chosen_GL_card_le_core_quotient_of_join_full h D hT hf
  have hcq := (chosen_centralQuotient_GL_card_le D).trans hc
  let := D.actionCentralizer_normal
  have ha := chosen_GL_card_le_faithful_quotient_of_join_full h D hT hf
  have haq := (chosen_centralQuotient_GL_card_le D).trans ha
  cases rows with
  | linear n hn e => exact ⟨n, by omega, ⟨e⟩⟩
  | linearThreeExtension e hd _ =>
    rw [BinaryLinear.card_GL_of_finrank hd, Nat.card_congr e.toEquiv,
      BinaryLinear.card_SL] at hc
    norm_num [BinaryLinear.order, Fin.prod_univ_succ] at hc
  | linearFiveExterior e hd _ =>
    rw [BinaryLinear.card_GL_of_finrank hd, Nat.card_congr e.toEquiv,
      BinaryLinear.card_SL] at hc
    norm_num [BinaryLinear.order, Fin.prod_univ_succ] at hc
  | alternating n hlo hhi e =>
    rw [GL_card_congr e.linearEquiv, Nat.card_congr e.groupEquiv.toEquiv] at haq
    exact (not_le_of_gt (alternating_GL_card_gt hlo hhi) haq).elim
  | alternatingSevenFour e hd =>
    rw [BinaryLinear.card_GL_of_finrank hd, Nat.card_congr e.toEquiv,
      nat_card_alternatingGroup] at ha
    norm_num [BinaryLinear.order, Fin.prod_univ_succ, Nat.factorial] at ha
  | g2 e =>
    have hd : Module.finrank (ZMod 2) D.chosenCentralQuotient = 6 :=
      e.linearEquiv.finrank_eq.trans (Atlas.G2.Natural.finrank_space (ZMod 2))
    rw [BinaryLinear.card_GL_of_finrank hd, Nat.card_congr e.groupEquiv.toEquiv,
      Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hcq
    norm_num [BinaryLinear.order, Fin.prod_univ_succ] at hcq
  | tripleSix e hd _ _ =>
    rw [BinaryLinear.card_GL_of_finrank hd, Nat.card_congr e.toEquiv,
      Atlas.Codes.hexEven_card] at hc
    norm_num [BinaryLinear.order, Fin.prod_univ_succ] at hc

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
