module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFourComparison

/-!
# Full attachment comparison on the selected original star

Every distance-two critical pair of the selected original nonsylow star
has equal complete fixed attachments. The proof combines both critical
image sizes, applying the original action and discharging shortness and
innerness. The literal quotient marking, original Sylow alternative and
containment of the minimum replacement are preserved.

Source: Meierfrankenfeld--Stellmacher (1993), (3.7)(4), printed p.875.
This finishes the attachment comparison on the original nonsylow star.
Critical-pair selection, minimum marked preservation/saturation, the
original Sylow branch, n = 2 and the full block assembly remain separate
obligations of the distance-two recognition proof.
-/

public noncomputable section
open scoped commutatorElement
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

/-- Equality of the entire fixed attachments for every critical path on the
actual selected original nonsylow star, with no critical-index premise. -/
theorem exists_source_star_fixed_attachments
    (d : CharacteristicReduction K R) (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h)) :
    ∃ P : Sylow 2 (Ltilde R (alpha R)), ∃ Y : Subgroup R,
      Y.map (embedS R) = componentSylowSeed R (alpha R) P ∧
      Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R)) ∧
      d.subgroup ≤ starCentralizer R Y ∧
      (let T := (starCentralizer R Y).map R.subtype
       let M := K ⊔ T
       let S := T.subgroupOf M
       ∃ hs : Input (K.subgroupOf M) S n F, ∃ gs : Geometry S,
         hs.quotientEquiv = (subgroupOfCoreQuotientEquiv le_sup_left).trans h.quotientEquiv ∧
         S = R.subgroupOf M ∧
         (normalizer (S : Set M)).pCoreIn 2 = S ∧
         K.subgroupOf M ⊔ pCore 2 M = ⊤ ∧
         ((T.subgroupOf K).map (componentProjection h)) =
           (R.subgroupOf K).map (componentProjection h) ∧
         ((∃ S' : Sylow 2 M, (S' : Subgroup M) = S) ↔
           ∃ S' : Sylow 2 H, (S' : Subgroup H) = R) ∧
         gs.b S = 2 ∧
         ∀ (a z t : Vertex S) (_path : CriticalPath S gs a z),
           Adjacent S a t → Adjacent S z t →
           U S a ⊓ centralizer (Ltilde S a : Set (FreeAmalgam S)) =
             U S z ⊓ centralizer (Ltilde S z : Set (FreeAmalgam S))) := by
  obtain ⟨P,Y,hY,hn,hmin,hs,hquot,hrest,hsat,hinner,hmark,hsyl,gs,hgs⟩ :=
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
  refine ⟨P,Y,hY,hn,hmin,hs,gs,hquot,hrest,hsat,hinner,hmark,hsyl,hgs,?_⟩
  intro a z t path hat hzt
  exact original_source_four_fixed_attachments hs hstarshort hinner hstar_nsyl
    gs hgs path hat hzt

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
