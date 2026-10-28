module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.Inputs
public import Theory.GroupTheory.PResidual.FrattiniControl
public import Theory.Frattini.Intersection

/-!
# The Frattini branch on the actual characteristic replacement

Burnside's basis theorem removes the Frattini factor from the commutator
bound inside the finite replacement group. Commutator idempotence identifies
the entire graph core with the moving part of its central omega layer.
This uses neither a natural subgroup nor a Sylow radical. Identification of
that moving part with the original layer remains a separate source premise.

Source: MS93 (3.6), first paragraph, printed p.870.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo

variable {M : Type*} [Group M] [Finite M]

/-- The finite-group Frattini argument, through the literal amalgam embedding. -/
theorem graph_core_eq_X_commutator_of_frattini (R : Subgroup M)
    (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (hsmall : core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R)) :
    core R (alpha R) = ⁅X R (alpha R), Ltilde R (alpha R)⁆ := by
  have hc : ⁅pCore 2 M, pResidual 2 M⁆ ≤
      (frattini (pCore 2 M)).map (pCore 2 M).subtype ⊔ omegaCenterIn (pCore 2 M) := by
    rw [core_alpha R hp hQR rfl, X, Q_alpha R hp hQR,
      omegaCenter_map _ _ (embedM_injective R),
      frattini_image_map _ _ (embedM_injective R), ← Subgroup.map_sup] at hsmall
    exact (map_le_map_iff_of_injective (embedM_injective R)).mp hsmall
  let : (omegaCenterIn (pCore 2 M)).Normal := by
    let : (omega₁ (center (pCore 2 M)) (p := 2)).Characteristic := omega₁_characteristic _
    infer_instance
  have he := commutator_eq_of_le_frattini_sup_of_isPPerfect
    (pCore 2 M) (pResidual 2 M) (omegaCenterIn (pCore 2 M)) pCore_isPGroup
    (isPPerfect_pResidual 2) (fun x hx => ((mem_omegaCenterIn_iff _ _).mp hx).1) hc
  rw [core_alpha R hp hQR rfl, X, Q_alpha R hp hQR,
    omegaCenter_map _ _ (embedM_injective R), Ltilde_alpha, ← map_commutator]
  exact congrArg (Subgroup.map (embedM R)) he

universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  (h : SmallMSPair κ L R) (d : Replacement L R)

/-- Source (3.2) on the replacement identifies two elementary moving layers.
It does not identify either one with the whole commutator core. -/
structure CentralLayer : Prop where
  X_commutator : ⁅X d.radical (alpha d.radical), Ltilde d.radical (alpha d.radical)⁆ =
    U d.radical (alpha d.radical)
  U_eq_moved : U d.radical (alpha d.radical) = (replacementMoved d).map (embedM d.radical)

include h in
/-- The small branch preserves the whole initial layer, including its fixed line. -/
theorem graph_core_le_of_frattini (hc : CentralLayer d)
    (hsmall : core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)) :
    core d.radical (alpha d.radical) ≤ (replacementMoved d).map (embedM d.radical) := by
  rw [graph_core_eq_X_commutator_of_frattini d.radical
    (replacement_radical_isPGroup h d) (replacement_core_le_radical h d) hsmall,
    hc.X_commutator, hc.U_eq_moved]

include h in
/-- Literal application to the original component commutator, through both maps. -/
theorem exhaustion_of_frattini (hc : CentralLayer d)
    (hsmall : core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)) :
    ⁅pCore 2 (L ⊔ R : Subgroup G), L.subgroupOf (L ⊔ R)⁆ = initialMoved L R :=
  exhaustion_of_graph_core_le h d (graph_core_le_of_frattini h d hc hsmall)

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
