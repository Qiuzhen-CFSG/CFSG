module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPairSolvable.Ambient.Actor
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.ComponentSource.ShortImage
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SameImage
public import CFSG.Quasithin.ChapterB.Section02.FullOffenderMovement
public import Theory.GroupTheory.ReducedNormal.SylowCenterClosure
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
/-!
# The same local cubic block is an ambient block

Let the action on the full Sylow omega-center span have solvable quotient.
Original Thompson movement supplies full best-offender movement on that
literal quotient. Its local cubic seed is subnormal by the preceding actor
lemma. C.1.27 lifts it to an ambient block with the same image, and the
same-image theorem identifies this block with the original subgroup `K`.
No characteristic-normalizer control assumption is used.

The local minimal-parabolic construction is needed upstream to produce
`K`, its movement and module support; those actual inputs suffice here.
Source: Aschbacher--Smith C.1.27, printed pp.132--133.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.Ambient
open ChapterB
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem image_local_subnormal {Q : Type*} [Group Q] (q : G →* Q)
    (K T : Subgroup G) (hs : (K.subgroupOf (K ⊔ T)).IsSubnormal) :
    ((K.map q).subgroupOf (K.map q ⊔ T.map q)).IsSubnormal := by
  let A := K ⊔ T
  have he : (K.subgroupOf A).map (q.subgroupMap A) = (K.map q).subgroupOf (A.map q) := by
    apply map_injective (A.map q).subtype_injective
    have hh : (A.map q).subtype.comp (q.subgroupMap A) = q.comp A.subtype := rfl
    rw [map_map,hh,←map_map,map_subgroupOf_eq_of_le (show K ≤ A from le_sup_left),
      map_subgroupOf_eq_of_le (map_mono (show K ≤ A from le_sup_left))]
  have hh := hs.map (q.subgroupMap_surjective A)
  rw [he] at hh
  change ((K.map q).subgroupOf ((K ⊔ T).map q)).IsSubnormal at hh
  rwa [Subgroup.map_sup] at hh

theorem same_block_of_solvable_omega_action
    (T : Sylow 2 G) (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (H K : Subgroup G) (hTH : (T : Subgroup G) ≤ H) (hKH : K ≤ H)
    (hs : (K.subgroupOf H).IsSubnormal) (ha : IsAlternatingBlock K 3)
    (hJ : K = ⁅K,elementaryAbelianMaxJ (T : Subgroup G)⁆)
    (hU : (blockU K).map K.subtype ≤
      normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hsolv : Group.IsSolvable (G ⧸ centralizer
      (normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G) : Set G))) :
    IsBlock K ∧
      ⁅normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G),K⁆ ≠ ⊥ := by
  let V := normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G)
  let q := QuotientGroup.mk' (centralizer (V : Set G))
  have hv : IsPReduced 2 V := omegaCenter_normalClosure_reduced T hchar
  let : IsElementaryAbelian 2 V := hv.elementary
  let : Group.IsSolvable (G ⧸ centralizer (V : Set G)) := hsolv
  let ρ := NormalElementaryQuotient.representation V q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  have hs' : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal :=
    hs.comap (inclusion (sup_le hKH hTH))
  have hk := ComponentSource.short_image_kind V K ha.2.1 hU
  have hVT : V ≤ (T : Subgroup G) := hv.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T)
  have hm := internal_full_best_movement V q (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) K (T : Subgroup G) T.isPGroup' hVT hs' hk hJ
  obtain ⟨hcard,hsub⟩ := solvable_seed_subnormal ρ
    (NormalElementaryQuotient.representation_injective V q (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _)) hv.quotient_pCore_eq_bot (K.map q) ((T : Subgroup G).map q)
        hk (image_local_subnormal q K _ hs') hm
  obtain ⟨L,hKL,hL,hUL,himage⟩ := source_block_of_quotient_selection T hchar hTH hKH hs
    ha.2.1 hU (K.map q) hsub le_rfl (Or.inr hcard) (Or.inl rfl)
  have heq : K = L := eq_of_same_centralizer_image V H K L hKH
    ((pCore_isPGroup.le_sylow_of_normal T).trans hTH) hs ha.2.1.twoPerfect hKL hL hUL
      (le_centralizer_iff.mp hv.le_centralizer_pCore) himage.symm
  refine ⟨heq.symm ▸ hL,?_⟩
  intro hz
  have hKC : K ≤ centralizer (V : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz)
  have hbot : K.map q = ⊥ := (Subgroup.map_eq_bot_iff _).mpr (by simpa [q] using hKC)
  rw [hbot,card_bot] at hcard
  omega
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.Ambient
