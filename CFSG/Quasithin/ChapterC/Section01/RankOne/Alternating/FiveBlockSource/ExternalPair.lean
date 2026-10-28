module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.PairTransport
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.EasyCases
public import Stellmacher.BaumannMap
/-!
# The original external two-group and its fixed pair

The Baumann group of the actual Sylow R in H maps onto Baum(T) whenever
Baum(T)≤R≤T in the common ambient group. Transporting the preselected pair
through this literal isomorphism preserves both of its original ambient
subgroups. The canonical C₁(T) remains central in R and lies in the first
member. T is not required to be contained in H.
Source: C.1.21–23, printed pp.127–130.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
open ChapterB GlaubermanNiles
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The intrinsic Baumann Sylow has exactly the original external Baumann image. -/
theorem external_baumann_image (T H : Subgroup G) (R : Sylow 2 H)
    (hBR : baumann T ≤ (R : Subgroup H).map H.subtype)
    (hRT : (R : Subgroup H).map H.subtype ≤ T) :
    (baumann (R : Subgroup H)).map H.subtype = baumann T := by
  calc
    _ = baumann ((R : Subgroup H).map H.subtype) := baumann_map_injective _ H.subtype_injective _
    _ = baumann T := (lemma_B_2_3_4 T _ hBR hRT).symm

/-- The same prescribed pair, now carried by the intrinsic Baumann group.
The two ambient images and the original C₁(T) are retained literally. -/
theorem external_pair_transport (T H : Subgroup G) (R : Sylow 2 H)
    (hBR : baumann T ≤ (R : Subgroup H).map H.subtype)
    (hRT : (R : Subgroup H).map H.subtype ≤ T)
    (D : CharacteristicPair (baumann T)) (hD : D.Universal.{u,u}) :
    ∃ E : CharacteristicPair (baumann (R : Subgroup H)), E.Universal.{u,u} ∧
      (E.first.map (baumann (R : Subgroup H)).subtype).map H.subtype = D.first.map (baumann T).subtype ∧
      (E.second.map (baumann (R : Subgroup H)).subtype).map H.subtype = secondAmbient T D ∧
      (firstAmbient T D).subgroupOf H ≤ (center (R : Subgroup H)).map (R : Subgroup H).subtype ∧
      (firstAmbient T D).subgroupOf H ≤ E.first.map (baumann (R : Subgroup H)).subtype := by
  let B := baumann (R : Subgroup H)
  have hB := external_baumann_image T H R hBR hRT
  let a : B ≃* baumann T := (B.equivMapOfInjective H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr hB)
  let E := transportPair D a.symm
  have hcomp : (H.subtype.comp B.subtype).comp a.symm.toMonoidHom = (baumann T).subtype := by
    ext b
    exact congrArg (fun x : baumann T => (x : G)) (a.apply_symm_apply b)
  have hmap (K : Subgroup (baumann T)) :
      ((K.map a.symm.toMonoidHom).map B.subtype).map H.subtype = K.map (baumann T).subtype := by
    rw [map_map,map_map,hcomp]
  refine ⟨E,transportPair_universal D hD a.symm,hmap D.first,hmap D.second,?_,?_⟩
  · intro c hc
    have hz := firstAmbient_le_omegaCenter T D hc
    have hcR : (c : G) ∈ (R : Subgroup H).map H.subtype := hBR (omegaCenter_le_baumann T hz)
    obtain ⟨r,hr,hrc⟩ := hcR
    have hrc' : r = c := H.subtype_injective hrc
    refine ⟨⟨c,hrc' ▸ hr⟩,mem_center_iff.mpr ?_,rfl⟩
    intro z
    apply Subtype.ext
    apply Subtype.ext
    exact ((mem_omegaOneCenterAmbient_iff T c).mp hz).2.2 z
      (hRT (mem_map_of_mem H.subtype z.property))
  · intro c hc
    have hm := hmap D.first
    have hcD : (c : G) ∈ D.first.map (baumann T).subtype := hc.2
    rw [←hm] at hcD
    obtain ⟨b,hb,hbc⟩ := hcD
    exact H.subtype_injective hbc ▸ hb
end CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
