module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Geometry.SharpImages.Native
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.Transport
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive

/-!
# Octad placement for large elementary subgroups of native max1

Align the actual Sylow image with the certified star Sylow using a literal
local conjugator. Counting the image and its kernel centralizer forces the
sharp case; the native certificate places that same marked image in the
pointwise kernel of the exceptional octad. No splitting of max1 is assumed.

This supplies the quotient-image step in the global F-occurrence argument
for Kleidman--Wilson (1988), Lemma 1.1.2(ii), p.485.
-/
@[expose] public noncomputable section
namespace Janko4.LocalStructure.LinearFive.Geometry.SharpImages
open Subgroup Cardinality Cardinality.QuotientCount.Image
open SylowCore SylowCore.Transport
open Simplicity.Max1Fusion.QuotientInvolutions
open Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative
attribute [local irreducible] modelGroup matrixA matrixB localKernel max1Subgroup

/-- Counting in the literal local Sylow forces the sharp-image alternative. -/
theorem sylow_large_image_octad (P : Sylow 2 M) (H : Subgroup P)
    [IsElementaryAbelian 2 H] (hne : ¬ H ≤ core P) (hcard : 1024 ≤ Nat.card H)
    (g : M) (hg : P.toSubgroup.map
      ((starProjection matrixA_mul_self matrixB_pow_four).comp (MulAut.conj g).toMonoidHom) =
        sylowCandidate) :
    (H.map (alignedHom P g hg)).map markedSylow ≤ octadPointwiseKernel exceptionalOctad := by
  let f := alignedHom P g hg
  have : IsElementaryAbelian 2 (H.map f) := IsElementaryAbelian.map f
  have hn : H.map f ≠ ⊥ := by
    rw [ne_eq, Subgroup.map_eq_bot_iff, alignedHom_ker]
    exact hne
  apply elementary_large_image_octad (H.map f) hn
  have hc := card_le_image_mul_centralizer (core P) H
  rw [← alignedHom_image_card P g hg H] at hc
  exact hcard.trans (hc.trans
    (Nat.mul_le_mul_left _ (centralizer_card_le_fixedMasks P H g hg)))

private theorem projection_star (g : M) :
    projection g = starGroupEquivM24 (starProjection matrixA_mul_self matrixB_pow_four g) := by
  have he : projection = starGroupEquivM24.toMonoidHom.comp
      (starProjection matrixA_mul_self matrixB_pow_four) := by
    apply MonoidHom.eq_of_eqOn_dense (localXY_generate matrixA_mul_self matrixB_pow_four)
    intro x hx
    rcases (show x = localX matrixA_mul_self matrixB_pow_four ∨
        x = localY matrixA_mul_self matrixB_pow_four from hx) with rfl | rfl
    · change localQuotientEquivM24 matrixA_mul_self matrixB_pow_four
        (QuotientGroup.mk' _ _) = starGroupEquivM24 _
      rw [localQuotientEquivM24_apply, starProjection_x]
      congr 1
      apply Subtype.ext
      exact actionImageEquivStarGroup_x matrixA_mul_self matrixB_pow_four
    · change localQuotientEquivM24 matrixA_mul_self matrixB_pow_four
        (QuotientGroup.mk' _ _) = starGroupEquivM24 _
      rw [localQuotientEquivM24_apply, starProjection_y]
      congr 1
      apply Subtype.ext
      exact actionImageEquivStarGroup_y matrixA_mul_self matrixB_pow_four
  exact DFunLike.congr_fun he g

/-- A large elementary subgroup outside E has an actual local conjugator
putting its genuine Mathieu image in the fixed exceptional octad kernel. -/
theorem local_large_image_octad (H : Subgroup M) [IsElementaryAbelian 2 H]
    (hne : ¬ H ≤ localKernel matrixA_mul_self matrixB_pow_four)
    (hcard : 1024 ≤ Nat.card H) :
    ∃ g : M, (H.map (MulAut.conj g).toMonoidHom).map projection ≤
      octadPointwiseKernel exceptionalOctad := by
  obtain ⟨P,hHP⟩ := (IsElementaryAbelian.isPGroup 2 H).exists_le_sylow
  let : IsElementaryAbelian 2 (H.subgroupOf P.toSubgroup) :=
    IsElementaryAbelian.subgroupOf hHP
  have hc : Nat.card (H.subgroupOf P.toSubgroup) = Nat.card H :=
    Nat.card_congr (subgroupOfEquivOfLe hHP).toEquiv
  have hn : ¬ H.subgroupOf P.toSubgroup ≤ core P := by
    intro h
    apply hne
    intro x hx
    exact h (show (⟨x,hHP hx⟩ : P) ∈ H.subgroupOf P.toSubgroup from hx)
  obtain ⟨g,hg⟩ := exists_alignment P
  have hi := sylow_large_image_octad P (H.subgroupOf P.toSubgroup) hn
    (by simpa only [hc] using hcard) g hg
  refine ⟨g, ?_⟩
  rintro y ⟨z, ⟨x,hx,rfl⟩, rfl⟩
  apply hi
  refine mem_map.mpr ⟨alignedHom P g hg ⟨x,hHP hx⟩,
    mem_map.mpr ⟨⟨x,hHP hx⟩, hx, rfl⟩, ?_⟩
  exact (projection_star ((MulAut.conj g) x)).symm
/-- Counting in the literal local Sylow forces the sharp-image alternative. -/
theorem sylow_large_image_eq_octad (P : Sylow 2 M) (H : Subgroup P)
    [IsElementaryAbelian 2 H] (hne : ¬ H ≤ core P) (hcard : 1024 ≤ Nat.card H)
    (g : M) (hg : P.toSubgroup.map
      ((starProjection matrixA_mul_self matrixB_pow_four).comp (MulAut.conj g).toMonoidHom) =
        sylowCandidate) :
    (H.map (alignedHom P g hg)).map markedSylow = octadPointwiseKernel exceptionalOctad := by
  let f := alignedHom P g hg
  have : IsElementaryAbelian 2 (H.map f) := IsElementaryAbelian.map f
  have hn : H.map f ≠ ⊥ := by
    rw [ne_eq, Subgroup.map_eq_bot_iff, alignedHom_ker]
    exact hne
  apply elementary_large_image_eq_octad (H.map f) hn
  have hc := card_le_image_mul_centralizer (core P) H
  rw [← alignedHom_image_card P g hg H] at hc
  exact hcard.trans (hc.trans
    (Nat.mul_le_mul_left _ (centralizer_card_le_fixedMasks P H g hg)))

/-- A large elementary subgroup outside E has an actual local conjugator
putting its genuine Mathieu image in the fixed exceptional octad kernel. -/
theorem local_large_image_eq_octad (H : Subgroup M) [IsElementaryAbelian 2 H]
    (hne : ¬ H ≤ localKernel matrixA_mul_self matrixB_pow_four)
    (hcard : 1024 ≤ Nat.card H) :
    ∃ g : M, (H.map (MulAut.conj g).toMonoidHom).map projection =
      octadPointwiseKernel exceptionalOctad := by
  obtain ⟨P,hHP⟩ := (IsElementaryAbelian.isPGroup 2 H).exists_le_sylow
  let : IsElementaryAbelian 2 (H.subgroupOf P.toSubgroup) :=
    IsElementaryAbelian.subgroupOf hHP
  have hc : Nat.card (H.subgroupOf P.toSubgroup) = Nat.card H :=
    Nat.card_congr (subgroupOfEquivOfLe hHP).toEquiv
  have hn : ¬ H.subgroupOf P.toSubgroup ≤ core P := by
    intro h
    apply hne
    intro x hx
    exact h (show (⟨x,hHP hx⟩ : P) ∈ H.subgroupOf P.toSubgroup from hx)
  obtain ⟨g,hg⟩ := exists_alignment P
  have hi := sylow_large_image_eq_octad P (H.subgroupOf P.toSubgroup) hn
    (by simpa only [hc] using hcard) g hg
  refine ⟨g, ?_⟩
  have hm : ((H.subgroupOf P.toSubgroup).map (alignedHom P g hg)).map markedSylow =
      (H.map (MulAut.conj g).toMonoidHom).map projection := by
    rw [map_map, map_map]
    have he : markedSylow.comp (alignedHom P g hg) =
        (projection.comp (MulAut.conj g).toMonoidHom).comp P.toSubgroup.subtype := by
      apply MonoidHom.ext
      intro x
      exact (projection_star ((MulAut.conj g) x.val)).symm
    rw [he, ← map_map, map_subgroupOf_eq_of_le hHP]
  exact hm ▸ hi

end Janko4.LocalStructure.LinearFive.Geometry.SharpImages
