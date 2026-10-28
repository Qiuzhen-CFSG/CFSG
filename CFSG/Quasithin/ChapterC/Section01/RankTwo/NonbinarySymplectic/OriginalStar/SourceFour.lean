module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFourEquality

/-!
# Source (3.7)(4) on the original selected nonsylow star

For a field-sized critical image, the two complete component-fixed
attachments agree. The comparison uses individual commutator values on the
full natural cover and the centralizer of the common overlap modulo the
critical displacement. Unequal attachments would force the original
cubic marked radical action to have order at most q squared.

Apply the comparison to the actual star selected from the supplied
characteristic reduction, with shortness, innerness and the original
nonsylow marking discharged. The full-core decomposition and both overlap
indices from (3) are retained in the same consumer conclusion.

Source: Meierfrankenfeld--Stellmacher (1993), (3.7)(4), printed p.875,
case |Z_alpha Q_alpha' / Q_alpha'| = q. The larger critical-image case,
critical-pair selection, minimum marked preservation/saturation, original
Sylow branch, degree-two restriction and block assembly remain open.
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

/-- The original selected-star consumer of source (3.7)(3)--(4) for
field-sized critical images, retaining both complete fixed attachments. -/
theorem exists_source_star_source_four
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
             (Z S a).relIndex (Z S z) = 2^n ∧
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
  intro a z t path hat hzt hcritical
  obtain ⟨hQ,hdecomp,hX,haz,hza⟩ :=
    original_source_three_of_field_critical hs hstarshort hinner hstar_nsyl
      gs hgs path hat hzt hcritical
  exact ⟨hQ,hdecomp,hX,haz,hza,
    original_source_four_of_field_critical hs hstarshort hinner hstar_nsyl
      gs hgs path hat hzt hcritical⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
