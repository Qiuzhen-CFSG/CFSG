module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.Overlap
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.HallJanko

/-!
# Whole-overlap markings for the Hall--Janko carrier and extension

The first local Borel is the checked subgroup of order 384. Both local
Borels lie in it, because the normalizer of the fixed inner Sylow is exactly
that subgroup. In the extension the local Sylow intersections are the images
of the inner Sylow, so their local normalizers transport through the inclusion.
Adjoining the fixed outer involution gives the whole Borel of order 768.

The constructions require only the first-local order and the explicit
full-normalizer quotient isomorphism. They do not require the second-local
quotient or the first outer-local order. The source assembly owner must still
supply the two premises and the local model calculations.

Source: Aschbacher--Smith F.1.1, F.1.3 and F.1.12(I)(10)--(11), pp.259--263.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterF.GreenBook.HallJanko.SecondParabolic
open Sporadic.LeechRelated.J2
open ExceptionalParabolics Seed PairNormalizer
open ExceptionalParabolics.SecondParabolic
open ExceptionalParabolics.SecondParabolic.Overlap

/-- The first local Borel already contains both local Borel factors. -/
theorem commonBorel_eq (hP : Nat.card p₂ = 1152) : Source.commonBorel L s = B := by
  have h0 : Source.borel (L 0) s = B := by
    rw [Source.borel, s_inf_L, normalizer_s_eq_B hP]
    exact inf_eq_right.mpr B_le_l₁
  have h1 : Source.borel (L 1) s ≤ B := by
    rw [Source.borel, s_inf_L, normalizer_s_eq_B hP]
    exact inf_le_right
  rw [Source.commonBorel, h0, sup_of_le_left h1, sup_of_le_left
    (show s ≤ B from le_sup_left)]

private theorem map_local_normalizer {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) (K T : Subgroup G) :
    K.map f ⊓ Subgroup.normalizer (T.map f : Set H) =
      (K ⊓ Subgroup.normalizer (T : Set G)).map f := by
  rw [← Subgroup.map_comap_eq_self
    (show K.map f ⊓ Subgroup.normalizer (T.map f : Set H) ≤ f.range from
      inf_le_left.trans (K.map_le_range f))]
  rw [Subgroup.comap_inf, Subgroup.comap_normalizer_eq_of_le_range (T.map_le_range f),
    Subgroup.comap_map_eq_self_of_injective hf,
    Subgroup.comap_map_eq_self_of_injective hf]

/-- Each outer local Borel is the image of the corresponding inner local Borel. -/
theorem outer_borel_eq_map (i : Fin 2) :
    Source.borel (outerL i) outerS = (Source.borel (L i) s).map intoExtension := by
  rw [Source.borel, outerS_inf_outerL, Source.borel, s_inf_L]
  exact map_local_normalizer intoExtension intoExtension_injective (L i) s

/-- Both local Borel factors are retained when adjoining the outer Sylow. -/
theorem outer_commonBorel_eq (hP : Nat.card p₂ = 1152) :
    Source.commonBorel outerL outerS = outerB := by
  simp only [Source.commonBorel, outer_borel_eq_map]
  rw [outerS, outerB, ← sup_assoc, ← Subgroup.map_sup, ← Subgroup.map_sup]
  rw [show Source.borel (L 0) s ⊔ Source.borel (L 1) s ⊔ s = B from commonBorel_eq hP]

/-- The fixed inner marking, conditional only on independent local calculations. -/
def marking (h₁ : Nat.card l₁ = 1920)
    (hP : Nonempty ((p₂ ⧸ q₂.subgroupOf p₂) ≃* QuotientModel)) : Marking Carrier where
  L := Seed.L
  S := sylow h₁
  borel_normalizes i := by
    rw [sylow_coe, commonBorel_eq (card_p₂ hP)]
    exact B_normalizes i
  overlap := by
    rw [sylow_coe, commonBorel_eq (card_p₂ hP)]
    change (l₁ ⊔ B) ⊓ (l₂ ⊔ B) = B
    rw [sup_of_le_left B_le_l₁, l₂_sup_B h₁ (card_p₂ hP), l₁_inf_p₂_eq_B (card_p₂ hP)]
  generated := L_generate h₁ (card_p₂ hP)

/-- The fixed marking in the concrete permutation extension. -/
def outerMarking (h₁ : Nat.card l₁ = 1920)
    (hP : Nonempty ((p₂ ⧸ q₂.subgroupOf p₂) ≃* QuotientModel)) : Marking Extension where
  L := Seed.outerL
  S := outerSylow h₁
  borel_normalizes i := by
    rw [outerSylow_coe, outer_commonBorel_eq (card_p₂ hP)]
    exact outerB_normalizes i
  overlap := by
    rw [outerSylow_coe, outer_commonBorel_eq (card_p₂ hP)]
    exact outer_overlap h₁ (card_p₂ hP)
  generated := outerL_generate h₁ (card_p₂ hP)

variable (h₁ : Nat.card l₁ = 1920)
  (hP : Nonempty ((p₂ ⧸ q₂.subgroupOf p₂) ≃* QuotientModel))

@[simp] theorem marking_L : (marking h₁ hP).L = Seed.L := rfl
@[simp] theorem marking_S : ((marking h₁ hP).S : Subgroup Carrier) = s := rfl
@[simp] theorem outerMarking_L : (outerMarking h₁ hP).L = Seed.outerL := rfl
@[simp] theorem outerMarking_S : ((outerMarking h₁ hP).S : Subgroup Extension) = outerS := rfl

@[simp] theorem marking_B : (marking h₁ hP).B = B := commonBorel_eq (card_p₂ hP)
@[simp] theorem outerMarking_B : (outerMarking h₁ hP).B = outerB :=
  outer_commonBorel_eq (card_p₂ hP)

theorem card_marking_B : Nat.card (marking h₁ hP).B = 384 := by
  rw [marking_B, card_B]

theorem card_outerMarking_B : Nat.card (outerMarking h₁ hP).B = 768 := by
  rw [outerMarking_B, card_outerB (card_p₂ hP)]

end CFSG.Quasithin.ChapterF.GreenBook.HallJanko.SecondParabolic
