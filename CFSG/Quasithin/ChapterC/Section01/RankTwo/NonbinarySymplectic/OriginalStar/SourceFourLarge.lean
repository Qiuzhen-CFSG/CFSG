module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFourEscape

/-!
# Larger-image hyperplanes on the selected original star

Apply the original plane and hyperplane constructions to the actual star
chosen from the supplied characteristic reduction. Shortness and innerness
are discharged, and the original quotient marking, odd-index radical and
Sylow alternative are retained. The common full displacement contains both
complete fixed attachments. Its hyperplane displacement has an order-q
complement to the entire opposite attachment. If the opposite-center
centralizer escapes the endpoint core, its field-sized quotient fills the
hyperplane fixer and its reciprocal movement contains the full attachment.

Source: Meierfrankenfeld--Stellmacher (1993), (3.7)(4), printed p.875,
the opening of the larger-image branch. The subsequent comparison of these
hyperplanes and critical-pair selection remain necessary, as do minimum
marked preservation/saturation, the original Sylow branch, n = 2 and the
full block assembly. No extra source premise is replaced by a callback.
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

/-- The full plane and hyperplane geometry on every large critical path
of the selected original nonsylow star. -/
theorem exists_source_star_large_hyperplane
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
           (2^n)^2 ≤ (Q S z).relIndex (Z S a) →
           (Z S t).relIndex (Z S a)=(2^n)^2 ∧
             (Z S t).relIndex (Z S z)=(2^n)^2 ∧
             Z S a ⊓ Q S z=Z S t ∧ Z S z ⊓ Q S a=Z S t ∧
             (Q S z).relIndex (Z S a)=(2^n)^2 ∧
             (Q S a).relIndex (Z S z)=(2^n)^2 ∧
             ⁅Z S a,Q S t⁆=⁅Z S a,Z S z⁆ ∧
             ⁅Z S z,Q S t⁆=⁅Z S a,Z S z⁆ ∧
             (U S a ⊓ centralizer (Ltilde S a : Set (FreeAmalgam S))) ⊔
               (U S z ⊓ centralizer (Ltilde S z : Set (FreeAmalgam S))) ≤
                 ⁅Z S a,Z S z⁆ ∧
             ∃ P₀ B : Subgroup (FreeAmalgam S),
               let X₀ := Z S z ⊓ centralizer (P₀ : Set (FreeAmalgam S))
               let H₀ := ⁅Z S z,P₀⁆
               let A₀ := U S z ⊓ centralizer (Ltilde S z : Set (FreeAmalgam S))
               let Y₀ := Z S a ⊓ centralizer (X₀ : Set (FreeAmalgam S))
               let A₁ := U S a ⊓ centralizer (Ltilde S a : Set (FreeAmalgam S))
               Q S z ≤ P₀ ∧ P₀ ≤ Q S t ∧ B ≤ Q S t ∧
               P₀=Q S t ⊓ centralizer (X₀ : Set (FreeAmalgam S)) ∧
               X₀.relIndex (Z S z)=2^n ∧
               Z S t ≤ X₀ ∧ ⁅Z S a,Z S z⁆ ≤ X₀ ∧
               (∀ b : FreeAmalgam S, b ∈ B ↔ b ∈ Q S t ∧ ∀ x ∈ X₀, ⁅b,x⁆ ∈ H₀) ∧
               Disjoint ⁅X₀,B⁆ A₀ ∧ Nat.card (⁅X₀,B⁆ : Subgroup (FreeAmalgam S))=2^n ∧
               H₀=⁅X₀,B⁆ ⊔ A₀ ∧ H₀ ≤ ⁅Z S a,Z S z⁆ ∧
               (¬ Y₀ ≤ Q S z →
                 Y₀.relIndex (Z S a)=2^n ∧ (Q S z).relIndex Y₀=2^n ∧
                 P₀=Q S z ⊔ Y₀ ∧ H₀=⁅Z S z,Y₀⁆ ∧
                 A₁ ≤ ⁅X₀,Z S a⁆ ∧ A₁.relIndex ⁅X₀,Z S a⁆=2^n ∧
                 Nat.card (⁅X₀,Z S a⁆ : Subgroup (FreeAmalgam S))=2^n * Nat.card A₁)) := by
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
  obtain ⟨_,_,hai,hzi,haR,hzR,hfixed⟩ :=
    original_source_four_large_paired_geometry hs hstarshort hinner hstar_nsyl
      gs hgs path hat hzt hcritical
  obtain ⟨hak,hzk,haq,hzq⟩ :=
    original_source_four_large_midpoint_kernels hs hstarshort hinner hstar_nsyl
      gs hgs path hat hzt hcritical
  obtain ⟨P₀,B,hQ,hP,hB,hpoint,hi,htX,hcommX,hBmem,hdis,hcard,hprod,hH⟩ :=
    original_source_four_large_hyperplane_attachment hs hstarshort hinner hstar_nsyl
      gs hgs path hat hzt hcritical
  refine ⟨hai,hzi,hak,hzk,haq,hzq,haR,hzR,hfixed,
    P₀,B,hQ,hP,hB,hpoint,hi,htX,hcommX,hBmem,hdis,hcard,hprod,hH,?_⟩
  intro hescape
  obtain ⟨hYi,hYq,hPY,hHY⟩ :=
    original_source_four_large_escaping_hyperplane hs hstarshort hinner hstar_nsyl
      gs hgs path hat hzt hcritical P₀ hP hpoint hi hescape
  obtain ⟨hA,hAi,hAc⟩ :=
    original_source_four_large_escaping_movement hs hstarshort hinner hstar_nsyl
      gs hgs path hat hzt hcritical P₀ hP hpoint hi hescape
  exact ⟨hYi,hYq,hPY,hHY,hA,hAi,hAc⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
