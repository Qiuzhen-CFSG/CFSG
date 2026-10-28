module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.Cover
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Projection

/-!
# The full central cover before the ambient-image exclusion

Conjugation descends to the canonical six-letter image with the actual
two-core as kernel. The natural quotient and complete component movement
recognize the moved subgroup as the natural module or its augmentation cover
also in the derived-image case. Thus its order is sixteen or thirty-two,
and its component-fixed kernel is central in the entire replacement.

Source: MS93 (3.2)(vi), (3.8), pp.863--864 and877--879; the six-letter
perfect-cover classification of Aschbacher--Smith I.1.5--6, p.408.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Cover
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  (h : SmallMSPair κ L R) (e : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
  (d : Replacement L R)

include hn in
/-- The entire central cover detects precisely the actual replacement two-core. -/
theorem moved_centralizer :
    centralizer (replacementMoved d : Set d.overgroup) = pCore 2 d.overgroup := by
  apply le_antisymm
  · intro g hg
    rw [← replacementAction_kernel h e hz hn d]
    apply LinearMap.ext
    intro v
    obtain ⟨w, hw⟩ := coverProjection_surjective h e hz hn d (Multiplicative.ofAdd v)
    have he := coverProjection_conjugate h e hz hn d g w w (by
      rw [← hg w w.property, mul_inv_cancel_right])
    simp only [hw, toAdd_ofAdd] at he
    exact he.symm
  · intro g hg w hw
    exact ((mem_omegaCenterIn_iff _ w).mp
      (replacementMoved_le_omegaCenter h d hw)).2.1 g hg |>.symm

/-- Conjugation on the whole cover, with its actual image as actor. -/
def action : Representation (ZMod 2) (projection h e hz hn d).range
    (Additive (replacementMoved d)) := by
  let := replacementMoved_normal h d
  exact NormalElementaryQuotient.representation (replacementMoved d)
    (projection h e hz hn d).rangeRestrict
    (projection h e hz hn d).rangeRestrict_surjective
    ((MonoidHom.ker_rangeRestrict _).trans
      ((projection_kernel h e hz hn d).trans (moved_centralizer h e hz hn d).symm))

local notation "p" => SectionFive.coverMap (h := h) (e := e) (hz := hz) (hn := hn) (d := d)
local notation "q" => MonoidHom.rangeRestrict (projection h e hz hn d)

theorem action_conjugate (g : d.overgroup) (v : Additive (replacementMoved d)) :
    ((action h e hz hn d (q g) v).toMul : d.overgroup) =
      g * (v.toMul : d.overgroup) * g⁻¹ := by
  let := replacementMoved_normal h d
  exact NormalElementaryQuotient.representation_apply _ _ _ _ g v

theorem map_equivariant (g : (projection h e hz hn d).range)
    (v : Additive (replacementMoved d)) :
    p (action h e hz hn d g v) =
      BinaryPermutation.naturalRepresentation (Fin 6) g.val (p v) := by
  obtain ⟨x, rfl⟩ := (projection h e hz hn d).rangeRestrict_surjective g
  exact cover_conjugate h e hz hn d x v.toMul
    (action h e hz hn d (q x) v).toMul (action_conjugate h e hz hn d x v)

theorem map_kernel :
    (p).ker = fixedSpace (action h e hz hn d) ((replacementComponent d).map q) := by
  let := replacementMoved_normal h d
  ext v
  change v.toMul ∈ (coverProjection h e hz hn d).ker ↔ _
  rw [coverProjection_kernel]
  exact (NormalElementaryQuotient.mem_fixedSpace_image _ _ _ _ _ v).symm

theorem full_movement :
    subspaceCommutator (action h e hz hn d) ⊤ ((replacementComponent d).map q) = ⊤ := by
  let := replacementMoved_normal h d
  have he : NormalElementaryQuotient.commutatorSpace (replacementMoved d)
      (replacementComponent d) = subspaceCommutator (action h e hz hn d) ⊤
        ((replacementComponent d).map q) :=
    NormalElementaryQuotient.commutatorSpace_eq _ _ _ _ _
  rw [← he, NormalElementaryQuotient.commutatorSpace, replacementMoved_idempotent h d]
  ext v
  simp

/-- Derived image recognizes the entire cover, including its possible fixed line. -/
theorem alternating_model
    (himage : (projection h e hz hn d).range = alternatingGroup (Fin 6)) :
    BinaryPermutation.SixCover.IsNaturalOrCore (action h e hz hn d)
      (projection h e hz hn d).range.subtype := by
  have hK : (replacementComponent d).map q = ⊤ := by
    apply top_unique
    intro g _
    have hg : g.val ∈ (replacementComponent d).map (projection h e hz hn d) := by
      rw [component_image, ← himage]
      exact g.property
    obtain ⟨k, hk, he⟩ := hg
    exact ⟨k, hk, Subtype.ext he⟩
  exact BinaryPermutation.SixCover.naturalOrCore_alternating (action h e hz hn d)
    (MulEquiv.subgroupCongr himage) ((replacementComponent d).map q) hK
    p (map_equivariant h e hz hn d)
    (SectionFive.coverMap_surjective (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
    (map_kernel h e hz hn d).le (full_movement h e hz hn d)

theorem moved_card_of_alternating
    (himage : (projection h e hz hn d).range = alternatingGroup (Fin 6)) :
    Nat.card (replacementMoved d) = 16 ∨ Nat.card (replacementMoved d) = 32 := by
  rcases alternating_model h e hz hn d himage with ⟨E, _⟩ | ⟨E, _⟩
  · left
    change Nat.card (Additive (replacementMoved d)) = 16
    rw [Nat.card_congr E.toEquiv, Module.natCard_eq_pow_finrank (K := ZMod 2),
      BinaryPermutation.finrank_natural_even (Fin 6) (by decide)]
    norm_num
  · right
    change Nat.card (Additive (replacementMoved d)) = 32
    rw [Nat.card_congr E.toEquiv, Module.natCard_eq_pow_finrank (K := ZMod 2),
      BinaryPermutation.finrank_core]
    norm_num

include hn in
/-- The moved order bound does not depend on eliminating the derived image. -/
theorem moved_card :
    Nat.card (replacementMoved d) = 16 ∨ Nat.card (replacementMoved d) = 32 := by
  rcases range_alternatives h e hz hn d with himage | hsur
  · exact moved_card_of_alternating h e hz hn d himage
  · exact SectionFive.moved_card
      (⟨projection h e hz hn d, hsur, projection_action h e hz hn d⟩ :
        FullSymmetricAction h e hz hn d)

/-- The central attachment has order at most two in either ambient-image case. -/
theorem kernel_card :
    Nat.card (coverProjection h e hz hn d).ker = 1 ∨
      Nat.card (coverProjection h e hz hn d).ker = 2 := by
  let f := coverProjection h e hz hn d
  have hr : Nat.card f.range = 16 := by
    rw [MonoidHom.range_eq_top.mpr (coverProjection_surjective h e hz hn d),
      Nat.card_congr (topEquiv).toEquiv]
    change Nat.card (BinaryPermutation.natural (Fin 6)) = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),
      BinaryPermutation.finrank_natural_even (Fin 6) (by decide)]
    norm_num
  have hc := f.ker.card_mul_index
  rw [index_ker, hr] at hc
  have hm := moved_card h e hz hn d
  change Nat.card f.ker = 1 ∨ Nat.card f.ker = 2
  omega

include hn in
/-- The component-fixed part of the cover is central in the whole replacement. -/
theorem moved_fixed_le_center :
    replacementMoved d ⊓ centralizer (replacementComponent d : Set d.overgroup) ≤
      center d.overgroup := by
  let := replacementMoved_normal h d
  let := replacementComponent_normal h d
  let C := replacementMoved d ⊓ centralizer (replacementComponent d : Set d.overgroup)
  have he : (coverProjection h e hz hn d).ker.map (replacementMoved d).subtype = C := by
    rw [coverProjection_kernel, map_comap_eq, range_subtype]
  have hc : Nat.card C = 1 ∨ Nat.card C = 2 := by
    rw [← he, card_map_of_injective (replacementMoved d).subtype_injective]
    exact kernel_card h e hz hn d
  rcases hc with hc | hc
  · exact (Subgroup.card_eq_one.mp hc).le.trans bot_le
  · exact central_of_normal_card_two C hc

theorem kernel_center :
    (coverProjection h e hz hn d).ker =
      (center d.overgroup).comap (replacementMoved d).subtype := by
  rw [coverProjection_kernel]
  ext v
  constructor
  · intro hv
    exact moved_fixed_le_center h e hz hn d ⟨v.property, hv⟩
  · intro hv
    exact (center_le_centralizer (replacementComponent d : Set d.overgroup)) hv

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Cover
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
