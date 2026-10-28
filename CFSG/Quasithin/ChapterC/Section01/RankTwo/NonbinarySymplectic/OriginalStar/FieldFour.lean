module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.PairedOrbit

/-!
# Field-four recognition for the original nonsylow component

The original characteristic-star construction supplies the short component,
inner action and nonsylow marking needed by the point-parabolic argument.
Its field degree is the original degree, so the resulting restriction applies
to the original component K. The existing whole-core theorem then identifies
K as an Sp4(4) block. No saturation or marked-image assumption on a minimum
replacement is required.

Source: MS93 (3.7), printed pp.872--877, and Aschbacher--Smith C.1.32.
The distance reduction and the original Sylow alternative are separate.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
open DistanceTwoRecognition MSCentralOrbit
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
include h

/-- The field restriction and block recognition concern the original
component and the original field; the source star discharges its local inputs. -/
theorem original_nonsylow_distance_two_field_and_block
    (d : CharacteristicReduction K R) (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h)) :
    n = 2 ∧ Nat.card F = 4 ∧ IsSp4FourBlock K := by
  obtain ⟨_P,Y,_hY,_hn,_hmin,hs,_hquot,_hrest,_hsat,hinner,_hmark,hsyl,gs,hgs⟩ :=
    exists_source_star_intrinsic_distance_two h d g hb
  have hshort := (short_and_natural_of_distance_two h d g hb).1
  have hstarshort : IsShort (K.subgroupOf (K ⊔ (starCentralizer R Y).map R.subtype)) :=
    hshort.of_mulEquiv (subgroupOfEquivOfLe le_sup_left).symm
  have hstar_nsyl : ¬ ∃ S' : Sylow 2 (Sp F), (S' : Subgroup (Sp F)) =
      ((((starCentralizer R Y).map R.subtype).subgroupOf
        (K ⊔ (starCentralizer R Y).map R.subtype)).subgroupOf
          (K.subgroupOf (K ⊔ (starCentralizer R Y).map R.subtype))).map (componentProjection hs) := by
    intro he
    exact hnsyl ((original_sylow_iff_marked_sylow h).mp
      (hsyl.mp ((original_sylow_iff_marked_sylow hs).mpr he)))
  obtain ⟨hn,hF⟩ := original_nonsylow_distance_two_degree_two
    hs hstarshort hinner hstar_nsyl gs hgs
  exact ⟨hn,hF,block_of_degree_two_distance_two h d g hb hn⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
