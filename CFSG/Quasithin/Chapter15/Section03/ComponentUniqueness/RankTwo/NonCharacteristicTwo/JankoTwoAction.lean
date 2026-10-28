module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.Definitions
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.JankoTwoModel
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.Terminal
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.JankoTwoAction.Models
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.JankoTwoAction.Placement
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.JankoTwoAction.FixedModel

/-!+# Reduction of the ambient Hall--Janko action calculation

Coprime action proves that the ambient moved subgroup embeds into the actual
component quotient. The earlier radical centrality then bounds its image by
the center of the model's local two-core. A compatible local marking reduces
the two ambient conclusions to a center-order bound and a residual-centralizer
calculation in one fixed subgroup of Aut(J₂).

The conditional reductions are assembled below using the compatible local
marking and the two fixed model calculations. This proves the exact ambient
action conclusions; the surrounding source lemma 15.3.42 still supplies the
separate terminal contradiction.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), final
paragraph of 15.3.42, printed p.1138.
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.JankoTwoAction

variable {G : Type*} [Group G] [Finite G]
variable {I L M Y S V V₁ V₂ Yplus : Subgroup G} [(L.subgroupOf I).Normal]

/-- The two exact ambient conclusions, conditional on the remaining calculations
for their actual transported subgroups. No injectivity premise is assumed. -/
theorem local_action_of_model_bounds
    (d : ComponentSetup I L M Yplus S) (a : ActionSetup M Y S V V₁ V₂ Yplus)
    (j : JankoTwoIdentification I L)
    (hb : Nat.card (center ((modelImage j (Yplus ⊔ S)).pCoreIn 2)) ≤ 4)
    (hc : centralizer (modelImage j Yplus : Set Model) = ⊥) :
    Nat.card (⁅V, Yplus⁆ : Subgroup G) = 4 ∧
      (centralizer (Yplus : Set G)).subgroupOf I ≤
        (centralizer (L : Set G)).subgroupOf I := by
  refine ⟨moved_card_four_of_radical_center_bound d a j hb, ?_⟩
  apply relative_centralizer_le_of_image_centralizer_eq_bot d.component_le
  apply centralizer_eq_bot_of_model _ j.equivalence
  rwa [← modelImage_eq]

/-- A single compatible local marking connects the fixed finite calculations
to the exact ambient source conclusions. Construction of all three premises
remains necessary for final assembly. -/
theorem local_action_of_marking
    (d : ComponentSetup I L M Yplus S) (a : ActionSetup M Y S V V₁ V₂ Yplus)
    (j : JankoTwoIdentification I L) (m : LocalMarking j Yplus S)
    (hb : Nat.card (center (secondNormalizer.pCoreIn 2)) ≤ 4)
    (hc : centralizer (secondResidual : Set Model) = ⊥) :
    Nat.card (⁅V, Yplus⁆ : Subgroup G) = 4 ∧
      (centralizer (Yplus : Set G)).subgroupOf I ≤
        (centralizer (L : Set G)).subgroupOf I := by
  exact local_action_of_model_bounds d a j
    (m.radical_center_card.trans_le hb) (m.centralizer_eq_bot hc)

/-- The completed Aut(J₂) action calculation.  The placement theorem supplies
the one conjugator needed to identify the transported local pair with the
fixed normalizer and residual, while the fixed model calculation supplies the
center bound and the trivial residual centralizer. -/
theorem local_action
    (d : ComponentSetup I L M Yplus S) (a : ActionSetup M Y S V V₁ V₂ Yplus)
    (j : JankoTwoIdentification I L) :
    Nat.card (⁅V, Yplus⁆ : Subgroup G) = 4 ∧
      (centralizer (Yplus : Set G)).subgroupOf I ≤
        (centralizer (L : Set G)).subgroupOf I := by
  obtain ⟨m⟩ := nonempty_localMarking d j
  exact local_action_of_marking d a j m
    FixedModel.radical_center_card_le FixedModel.residual_centralizer_eq_bot

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.JankoTwoAction
