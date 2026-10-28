module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFourFullSaturation

/-!
# Escaping-attachment comparison on the selected original star

The selected source star inherits the complete large-image comparison:
if its attachments differ and the opposite hyperplane centralizer escapes,
both attachments have field order, the movement intersection has field
order, and each nontrivially moving element of the opposite centralizer
has a value outside the reciprocal movement. Shortness and innerness are
discharged here. The original quotient marking, odd-index radical and
Sylow alternative are preserved, without a premise about saturation of
the minimum replacement.

Source: Meierfrankenfeld--Stellmacher (1993), (3.7)(4), printed p.875.
Root-element selection and the remaining attachment comparison still
precede critical-pair selection. Minimum marked preservation/saturation,
the original Sylow branch, n = 2 and the full block assembly remain open.
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

/-- The escaping hyperplane comparison for every large critical path with
unequal attachments on the actual selected original nonsylow star. -/
theorem exists_source_star_large_unequal_value_escape
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
           U S a ⊓ centralizer (Ltilde S a : Set (FreeAmalgam S)) ≠
             U S z ⊓ centralizer (Ltilde S z : Set (FreeAmalgam S)) →
             ∃ P B : Subgroup (FreeAmalgam S),
               let X := Z S z ⊓ centralizer (P : Set (FreeAmalgam S))
               let H₀ := ⁅Z S z,P⁆
               let A₀ := U S z ⊓ centralizer (Ltilde S z : Set (FreeAmalgam S))
               let A₁ := U S a ⊓ centralizer (Ltilde S a : Set (FreeAmalgam S))
               Q S z ≤ P ∧ P ≤ Q S t ∧ B ≤ Q S t ∧
               P=Q S t ⊓ centralizer (X : Set (FreeAmalgam S)) ∧
               X.relIndex (Z S z)=2^n ∧
               Z S t ≤ X ∧ ⁅Z S a,Z S z⁆ ≤ X ∧
               (∀ b : FreeAmalgam S, b ∈ B ↔ b ∈ Q S t ∧ ∀ x ∈ X, ⁅b,x⁆ ∈ H₀) ∧
               Disjoint ⁅X,B⁆ A₀ ∧ Nat.card (⁅X,B⁆ : Subgroup (FreeAmalgam S))=2^n ∧
               H₀=⁅X,B⁆ ⊔ A₀ ∧ H₀ ≤ ⁅Z S a,Z S z⁆ ∧
               (¬ Z S a ⊓ centralizer (X : Set (FreeAmalgam S)) ≤ Q S z →
                 ¬ ⁅X,Z S a⁆ ≤ H₀ ∧
                 Nat.card A₁=2^n ∧ Nat.card A₀=2^n ∧
                 Nat.card (⁅X,Z S a⁆ ⊓ H₀ : Subgroup (FreeAmalgam S))=2^n ∧
                 ∀ y ∈ Z S a ⊓ centralizer (X : Set (FreeAmalgam S)),
                   (∃ b ∈ Z S z, ⁅b,y⁆ ≠ 1) →
                     ∃ b ∈ Z S z, ⁅b,y⁆ ∉ ⁅X,Z S a⁆)) := by
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
  intro a z t path hat hzt hcritical hne
  exact original_source_four_large_unequal_value_escape hs hstarshort hinner hstar_nsyl
    gs hgs path hat hzt hcritical hne

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
