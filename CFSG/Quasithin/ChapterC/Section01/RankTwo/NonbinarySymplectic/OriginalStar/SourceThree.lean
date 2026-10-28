module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceThreeNoncontained

/-!
# Source (3.7)(3) on the original selected nonsylow star

Apply the complete original critical-core argument to the same star selected
from the supplied characteristic reduction. Its short component, inner
ambient action, original quotient marking and original Sylow alternative
supply every additional local hypothesis. For every field-sized critical
image, the entire core is U D, its central omega subgroup is Z, and both
full-center overlap indices are q. There is no core-containment callback.

This proves the nonsylow branch of source (3.7)(3), printed p.874 of
Meierfrankenfeld--Stellmacher (1993). It does not select a field-sized critical
pair, prove the paired-attachment equality of (4), or complete the original
Sylow branch, minimum marked preservation/saturation, field restriction or
whole-block assembly. Those remain with this source-theorem owner.
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

/-- Source (3.7)(3) on the selected original nonsylow star. Shortness,
innerness and the original marked radical are discharged by the star
construction; only the source's literal field-sized critical image remains
inside the universally quantified conclusion. -/
theorem exists_source_star_source_three
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
           (Q S z).relIndex (Z S a) = 2^n →
           Q S a ≤ Z S a ⊔ Q S z ∧
             Q S a = U S a ⊔ fixedCore S a ∧
             X S a = Z S a ∧
             (Z S z).relIndex (Z S a) = 2^n ∧
             (Z S a).relIndex (Z S z) = 2^n) := by
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
  intro a z t path hat hzt hcritical
  exact original_source_three_of_field_critical hs hstarshort hinner hstar_nsyl
    gs hgs path hat hzt hcritical

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
