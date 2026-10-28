module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.Replacement
public import Theory.GroupTheory.PRadical.OddIndex

/-!
# Saturation of the original marked star cut

The original star cut contains the full component kernel. Thus preservation
of its marked component image identifies its intersection with K with the
original R intersection K. The product Mstar = K Tstar then identifies
Tstar with R intersect Mstar. Normality of Mstar transfers the original
odd-index radical saturation to this literal star pair.

The marked-image preservation in the first paragraph of MS93 (3.7) remains
explicit. No minimum characteristic replacement or graph-distance transfer
is used. Source: MS93 (3.4), pp.868--869, and (3.7), p.872.
-/

public section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
include h

omit [Finite F] [CharP F 2] in
private theorem star_eq_original_restriction_of_cut
    (Y : Subgroup R)
    (hcut : (K ⊔ (starCentralizer R Y).map R.subtype) ⊓ pCore 2 H ≤
      (starCentralizer R Y).map R.subtype)
    (hmark : (((starCentralizer R Y).map R.subtype).subgroupOf K).map
      (componentProjection h) = (R.subgroupOf K).map (componentProjection h)) :
    let Tstar := (starCentralizer R Y).map R.subtype
    Tstar.subgroupOf (K ⊔ Tstar) = R.subgroupOf (K ⊔ Tstar) := by
  let Tstar := (starCentralizer R Y).map R.subtype
  let := h.component_normal
  have hTR : Tstar ≤ R := map_subtype_le _
  have hkT : (componentProjection h).ker ≤ Tstar.subgroupOf K := by
    rw [componentProjection_kernel]
    intro k hk
    rw [pCore_subnormal_eq_comap 2 (h.component_normal).isSubnormal] at hk
    exact hcut ⟨mem_sup_left k.property,hk⟩
  have hkR : (componentProjection h).ker ≤ R.subgroupOf K :=
    hkT.trans (comap_mono hTR)
  have he : Tstar.subgroupOf K = R.subgroupOf K := by
    have hh := congrArg (fun A => A.comap (componentProjection h)) hmark
    rwa [comap_map_eq_self hkT,comap_map_eq_self hkR] at hh
  apply le_antisymm (comap_mono hTR)
  intro x hx
  change (x : H) ∈ R at hx
  change (x : H) ∈ Tstar
  obtain ⟨k,hk,t,ht,hkt⟩ := mem_sup_of_normal_left.mp x.property
  have hkR' : k ∈ R := by
    have hh : (x : H) * t⁻¹ ∈ R := R.mul_mem hx (R.inv_mem (hTR ht))
    rwa [←hkt,mul_inv_cancel_right] at hh
  have hkT' : k ∈ Tstar := he.ge (show (⟨k,hk⟩ : K) ∈ R.subgroupOf K from hkR')
  rw [←hkt]
  exact Tstar.mul_mem hkT' ht

/-- The original star cut and the marked-image assertion of (3.7) identify
the actual star radical and prove saturation inside its actual overgroup. -/
theorem star_radical_saturated_of_marked_image_eq
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    (P : Sylow 2 (Ltilde R (alpha R))) (Y : Subgroup R)
    (hY : Y.map (embedS R) = componentSylowSeed R (alpha R) P)
    (hn : Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R)))
    (hmark : (((starCentralizer R Y).map R.subtype).subgroupOf K).map
      (componentProjection h) = (R.subgroupOf K).map (componentProjection h)) :
    let Tstar := (starCentralizer R Y).map R.subtype
    let Mstar := K ⊔ Tstar
    Tstar.subgroupOf Mstar = R.subgroupOf Mstar ∧
      (normalizer (Tstar.subgroupOf Mstar : Set Mstar)).pCoreIn 2 =
        Tstar.subgroupOf Mstar := by
  let Tstar := (starCentralizer R Y).map R.subtype
  let Mstar := K ⊔ Tstar
  have hcut := (star_cut_of_span_le h P Y hY
    (h.original_starSpan_le_moving_fixed geometry hb Y P hY hn)).1
  have he := star_eq_original_restriction_of_cut h Y hcut hmark
  refine ⟨he,?_⟩
  let : Mstar.Normal := star_overgroup_normal h Y
  have hR : R.IsPRadical 2 := by
    refine ⟨h.radical_ne_bot,?_⟩
    obtain ⟨A,_,hodd,hcore⟩ := h.radical
    change A.pCoreIn 2 = R at hcore
    rw [←hcore]
    exact pCoreIn_normalizer_eq_of_prime_not_dvd_index A hodd.not_two_dvd_nat
  rw [he]
  exact normal_intersection_relative_core Mstar R hR

/-- The already constructed original source seed feeds the genuine star
saturation consumer. Its only new source premise is marked preservation. -/
theorem exists_source_star_saturation_of_marked_preservation
    (hmark : ∀ (P : Sylow 2 (Ltilde R (alpha R))) (Y : Subgroup R),
      Y.map (embedS R) = componentSylowSeed R (alpha R) P →
      Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R)) →
      (((starCentralizer R Y).map R.subtype).subgroupOf K).map
        (componentProjection h) = (R.subgroupOf K).map (componentProjection h)) :
    ∃ P : Sylow 2 (Ltilde R (alpha R)), ∃ Y : Subgroup R,
      Y.map (embedS R) = componentSylowSeed R (alpha R) P ∧
      Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R)) ∧
      (let Tstar := (starCentralizer R Y).map R.subtype
       let Mstar := K ⊔ Tstar
       Tstar.subgroupOf Mstar = R.subgroupOf Mstar ∧
         (normalizer (Tstar.subgroupOf Mstar : Set Mstar)).pCoreIn 2 =
           Tstar.subgroupOf Mstar) := by
  obtain ⟨geometry,hb,_⟩ := h.positive_even_geometry
  obtain ⟨P,Y,hY,hn,_⟩ := exists_source_star_reduction h
  exact ⟨P,Y,hY,hn,star_radical_saturated_of_marked_image_eq h geometry hb
    P Y hY hn (hmark P Y hY hn)⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
