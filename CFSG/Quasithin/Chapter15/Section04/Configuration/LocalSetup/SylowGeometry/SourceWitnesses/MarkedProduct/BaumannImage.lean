module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.MarkedProduct.ThompsonImage

/-!
# The original Baumann and Thompson images agree

The source Thompson image has order four. It lies in the Baumann image,
which is a two-subgroup of the plane-preserving orthogonal group of order 36.
That image has order at most four, so the two images coincide. The literal
conjugation action then identifies their fixed subgroups inside the original
moved module; no abstract replacement of either original subgroup is made.

This provides the fixed-subgroup comparison used by the source alpha
decomposition in 15.4.12 and the following 15.4.19 construction.
Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
printed pp.1160--1163.
-/

@[expose] public section
open Subgroup Stellmacher
open OrthogonalFourBinary OrthogonalFourBinary.TerminalLines OrthogonalFourBinary.SylowGeometry
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.MarkedProduct
open FamilySource FamilySource.ModuleStructure
open FamilySource.ModuleStructure.BinaryNormalizer FamilySource.ModuleStructure.BaumannPair

private theorem base_two_subgroup_card_le_four (D : Subgroup OrthogonalFourBinary.IsometryGroup)
    (hD : D ≤ base) (hp : IsPGroup 2 D) : Nat.card D ≤ 4 := by
  have hb : Nat.card base = 36 := by
    rw [Nat.card_congr Concrete.baseEquiv.toEquiv,Nat.card_prod]
    norm_num [Concrete.S3,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hd : Nat.card D ∣ 36 := hb ▸ card_dvd_of_le hD
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hsmall : n ≤ 2 := by
    by_contra! h
    have h8 : 8 ∣ 36 := by
      rw [hn] at hd
      exact (Nat.pow_dvd_pow 2 h).trans hd
    norm_num at h8
  rw [hn]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hsmall

private theorem thompson_le_baumann {G : Type*} [Group G] (R : Subgroup G) :
    elementaryAbelianMaxJ R ≤ ChapterB.baumann R := by
  have hJR : elementaryAbelianMaxJ R ≤ R := sSup_le fun A hA => hA.1
  refine le_inf hJR ?_
  intro j hj z hz
  exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 j hj |>.symm

variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M X : Subgroup G}

/-- The original Thompson group and Baumann group have the same faithful
orthogonal action on the original moved module. -/
theorem SourceAction.thompson_image_eq_baumann_image
    (d : SourceAction T M X) (h : Input K T M X 2) :
    ((elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf M).map d.actor =
      ((ChapterB.baumann (T : Subgroup G)).subgroupOf M).map d.actor := by
  let D := ((ChapterB.baumann (T : Subgroup G)).subgroupOf M).map d.actor
  have hD : D ≤ base := by
    rintro _ ⟨b,hb,rfl⟩
    exact d.baumann_base hb
  have hp : IsPGroup 2 D :=
    (T.isPGroup'.to_le (inf_le_left : ChapterB.baumann (T : Subgroup G) ≤ (T : Subgroup G))).comap_subtype.map d.actor
  apply eq_of_le_of_card_ge
  · exact map_mono (subgroupOf_mono M (thompson_le_baumann (T : Subgroup G)))
  · rw [d.thompson_image_card h]
    exact base_two_subgroup_card_le_four D hD hp

/-- Equality of the actual fixed subgroups, with both actors still in G. -/
theorem SourceAction.baumann_fixed_eq_thompson_fixed
    (d : SourceAction T M X) (h : Input K T M X 2) :
    movedModule (T : Subgroup G) M X ⊓ centralizer (ChapterB.baumann (T : Subgroup G) : Set G) =
      movedModule (T : Subgroup G) M X ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  have him := d.thompson_image_eq_baumann_image h
  have hSM : ChapterB.baumann (T : Subgroup G) ≤ M := inf_le_left.trans h.sylow_le
  apply le_antisymm
  · exact inf_le_inf_left _ (centralizer_le (thompson_le_baumann (T : Subgroup G)))
  · intro w hw
    refine ⟨hw.1, ?_⟩
    intro s hs
    let sm : M := ⟨s,hSM hs⟩
    have hsm : d.actor sm ∈ ((ChapterB.baumann (T : Subgroup G)).subgroupOf M).map d.actor :=
      ⟨sm,hs,rfl⟩
    obtain ⟨j,hj,hactor⟩ := him.symm.le hsm
    have hsAction := d.intertwines sm ⟨w,hw.1⟩
    have hjAction := d.intertwines j ⟨w,hw.1⟩
    have hjfix : (j : G)*w*(j : G)⁻¹=w := mul_inv_eq_iff_eq_mul.mpr (hw.2 j hj)
    have hfix : s*w*s⁻¹=w := by
      change (sm : G)*w*(sm : G)⁻¹=w
      rw [←hsAction,←hactor,hjAction]
      exact hjfix
    exact mul_inv_eq_iff_eq_mul.mp hfix

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.MarkedProduct
