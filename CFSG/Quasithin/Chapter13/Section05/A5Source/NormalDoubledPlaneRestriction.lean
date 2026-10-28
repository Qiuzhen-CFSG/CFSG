module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalDoubledPlane
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.ExtendedAffinePlaneRestriction

/-!
# Compatible ordinary and doubled source-plane comparisons

The original L has order 960, while its doubled overgroup has order 1,920.
Its image therefore has index two and contains the plane core. The intrinsic
index-two characterization identifies this image with the literal ordinary
plane inside the doubled unitary endpoint. Restricting the same equivalence
retains the inclusion square, the original module and the ordinary overlap.

This supplies the plane half of the compatible ordinary subamalgam needed in
Aschbacher--Smith 13.5.17, printed p.922, under the original normal-branch
hypotheses. No new source or model premise is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
open ChapterF.GreenBook.LieModels.UnitaryFour
open ChapterF.UnitaryTwo
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
  (hU : ¬ IsMulCommutative (Source.UH H V₃))
  (hn : ((residualCentralizer L V₁).subgroupOf H).Normal)
include d hA312 hH hU hn
local notation "M" => (L ⊔ (T : Subgroup G) : Subgroup G)
local notation "P" => planeParabolic 1 (Nat.le_refl 1)
local notation "PE" => Extension.plane 1 (Nat.le_refl 1)
local notation "j" => Extension.binaryPlaneInclusion
local notation "B" => (residualCentralizer L V₁ ⊔ (T : Subgroup G) : Subgroup G)

/-- A full source-plane comparison preserving the module carries the original L
onto the ordinary plane inside the literal extension. -/
theorem source_normal_doubled_plane_ordinary_image
    (E : M ≃* PE)
    (hV : (V.subgroupOf M).map E.toMonoidHom = ExtendedAffinePlane.planeCore) :
    (L.subgroupOf M).map E.toMonoidHom = (j).range := by
  apply ExtendedAffinePlane.eq_ordinary_of_index_two
  · rw [←hV]
    apply map_mono
    exact fun x hx => d.chosen.le_componentCore.trans (pCoreIn_le 2 L) hx
  · refine ((L.subgroupOf M).index_map_equiv E).trans ?_
    have hc : Nat.card (L.subgroupOf M)=960 :=
      (Nat.card_congr (subgroupOfEquivOfLe (H := L) (K := M) le_sup_left).toEquiv).trans
        (normal_local_card d hA312 hH hU hn)
    have hcM : Nat.card M=1920 := (Nat.card_congr E.toEquiv).trans Extension.binary_plane_card
    have hi := (L.subgroupOf M).index_mul_card
    rw [hc,hcM] at hi
    exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 960) (hi.trans (by decide))

/-- One full comparison and its restriction to L retain both plane structures
and commute with the literal ordinary inclusions. -/
theorem source_normal_doubled_plane_pair
    (hdoubled : M ≠ L) :
    ∃ (E : M ≃* PE) (eL : L ≃* P),
      (V.subgroupOf M).map E.toMonoidHom = ExtendedAffinePlane.planeCore ∧
      (V₁.subgroupOf M).map E.toMonoidHom = zpowers ExtendedAffinePlane.longRight ∧
      ((B).subgroupOf M).map E.toMonoidHom =
        (Extension.overlap 1 (Nat.le_refl 1)).subgroupOf PE ∧
      (L.subgroupOf M).map E.toMonoidHom = (j).range ∧
      (V.subgroupOf L).map eL.toMonoidHom = pCore 2 P ∧
      ((B ⊓ L).subgroupOf L).map eL.toMonoidHom =
        (overlap 1 (Nat.le_refl 1)).subgroupOf P ∧
      ∀ l : L, E (inclusion (show L ≤ M from le_sup_left) l) = j (eL l) := by
  obtain ⟨E,hV,hline,hB⟩ := source_normal_doubled_plane_unitary d hA312 hH hU hn hdoubled
  have hL := source_normal_doubled_plane_ordinary_image d hA312 hH hU hn E hV
  let i : L →* M := inclusion le_sup_left
  obtain ⟨eL,hcomp⟩ := MulEquiv.exists_compatible_restriction i (inclusion_injective le_sup_left)
    j Extension.binaryPlaneInclusion_injective E (by
      change (inclusion (show L ≤ M from le_sup_left)).range.map E.toMonoidHom=(j).range
      rw [inclusion_range]
      exact hL)
  have hh : E.toMonoidHom.comp i = (j).comp eL.toMonoidHom := by
    apply MonoidHom.ext
    exact hcomp
  have hVL : V ≤ L := d.chosen.le_componentCore.trans (pCoreIn_le 2 L)
  have hVi : (V.subgroupOf L).map i=V.subgroupOf M := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x.val,hVL hx⟩,hx,rfl⟩
  have hBi : ((B ⊓ L).subgroupOf L).map i=((B).subgroupOf M) ⊓ (L.subgroupOf M) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · rintro ⟨hxB,hxL⟩
      exact ⟨⟨x.val,hxL⟩,⟨hxB,hxL⟩,rfl⟩
  refine ⟨E,eL,hV,hline,hB,hL,?_,?_,hcomp⟩
  · apply map_injective Extension.binaryPlaneInclusion_injective
    calc
      ((V.subgroupOf L).map eL.toMonoidHom).map j =
          ((V.subgroupOf L).map i).map E.toMonoidHom := by rw [map_map,map_map,←hh]
      _ = ExtendedAffinePlane.planeCore := by rw [hVi,hV]
      _ = (pCore 2 P).map j := rfl
  · apply map_injective Extension.binaryPlaneInclusion_injective
    calc
      (((B ⊓ L).subgroupOf L).map eL.toMonoidHom).map j =
          (((B ⊓ L).subgroupOf L).map i).map E.toMonoidHom := by rw [map_map,map_map,←hh]
      _ = ((B).subgroupOf M).map E.toMonoidHom ⊓ (L.subgroupOf M).map E.toMonoidHom := by
        rw [hBi,map_inf _ _ _ E.injective]
      _ = ((Extension.overlap 1 (Nat.le_refl 1)).subgroupOf PE) ⊓ (j).range := by rw [hB,hL]
      _ = ((overlap 1 (Nat.le_refl 1)).subgroupOf P).map j := ExtendedAffinePlane.ordinary_overlap_image.symm
end CFSG.Quasithin.Chapter13.Section05.A5Source
