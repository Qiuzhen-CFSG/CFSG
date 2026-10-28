module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.ExceptionalMarking
public import Theory.Representation.AlternatingSevenFiveSeed.Geometry

/-!
# Selecting the original exceptional A₇ five-letter seed

The actual Thompson and Baumann images select a five-letter subgroup through
their common four-group. It generates with the Baumann normalizer image.
Its movement of the fixed plane lifts to movement of the omega center of any
selected two-group with the same image. All maps are the original action map.

Source: Aschbacher–Smith C.1.24, printed p.131, final paragraph.
-/

public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.Alternating.SevenSource
open Representation.AlternatingSevenFiveSeed
local notation "A7" => alternatingGroup (Fin 7)
variable {G : Type*} [Group G] [Finite G]

/-- The source four-space determines an actual A₅ seed and the image of the
normalizer of the unchanged original Baumann group. -/
theorem exceptional_five_quotient_seed
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* A7) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G))
    (hd : Module.finrank (ZMod 2) (Additive U) = 4)
    (T : Sylow 2 G) (hUT : U ≤ T)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ q.ker) :
    ∃ A B : Subgroup A7,
      IsBestOffender (NormalElementaryQuotient.representation U q hq hk) A ∧
      (elementaryAbelianMaxJ (T : Subgroup G)).map q = A ∧
      (ChapterB.baumann (T : Subgroup G)).map q = A ∧
      Nonempty (B ≃* alternatingGroup (Fin 5)) ∧
      (T : Subgroup G).map q ≤ normalizer (B : Set A7) ∧ A ≤ B ∧
      (∃ P : Sylow 2 B, (P : Subgroup B).map B.subtype = A) ∧
      (normalizer (ChapterB.baumann (T : Subgroup G) : Set G)).map q ⊔ B = ⊤ := by
  obtain ⟨A,hAT,hA,hJA,hBA⟩ := exceptional_thompson_baumann_images U q hq hk hd T hUT hJ
  obtain ⟨B,e,hTN,hAB,hP,_,hgen,_⟩ := exists_five_seed
    (NormalElementaryQuotient.representation U q hq hk)
    (NormalElementaryQuotient.representation_injective U q hq hk) hd
    (T.mapSurjective (f := q) hq) A hAT hA
  refine ⟨A,B,hA,hJA,hBA,e,hTN,hAB,hP,?_⟩
  rw [ChapterB.baumann_normalizer_map T q hq,hBA]
  exact hgen

/-- The five-letter seed moves a vector in the original selected omega center.
This is the literal noncentral seed required by C.1.21(4). -/
theorem exceptional_selected_omega_movement
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* A7) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G))
    (hd : Module.finrank (ZMod 2) (Additive U) = 4)
    (T : Sylow 2 G) (A B : Subgroup A7)
    (hA : IsBestOffender (NormalElementaryQuotient.representation U q hq hk) A)
    (e : B ≃* alternatingGroup (Fin 5))
    (hBN : (T : Subgroup G).map q ≤ normalizer (B : Set A7))
    (P Y : Subgroup G) (hUP : U ≤ P) (hP : P.map q = A) (hY : Y.map q = B) :
    ⁅omegaOneCenterAmbient P,Y⁆ ≠ ⊥ := by
  let ρ := NormalElementaryQuotient.representation U q hq hk
  obtain ⟨b,hb,v,hv,hmove⟩ := five_moves_offender_fixedSpace ρ
    (NormalElementaryQuotient.representation_injective U q hq hk) hd
    B e (T.mapSurjective (f := q) hq) hBN A hA
  obtain ⟨y,hy,rfl⟩ : ∃ y ∈ Y, q y = b := (show b ∈ Y.map q by rw [hY]; exact hb)
  have hvP : (v.toMul : G) ∈ centralizer (P : Set G) := by
    apply (NormalElementaryQuotient.mem_fixedSpace_image U q hq hk P v).mp
    rwa [hP]
  have hvZ : (v.toMul : G) ∈ omegaOneCenterAmbient P :=
    (mem_omegaOneCenterAmbient_iff P _).mpr
      ⟨hUP v.toMul.property,elemPow_eq_one_of_isElementaryAbelian _ v.toMul.property,hvP⟩
  intro hbot
  have hc := (commutator_eq_bot_iff_le_centralizer.mp hbot) hvZ y hy
  apply hmove
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [NormalElementaryQuotient.representation_apply, hc,mul_inv_cancel_right]

end CFSG.Quasithin.ChapterC.RankOne.Alternating.SevenSource
