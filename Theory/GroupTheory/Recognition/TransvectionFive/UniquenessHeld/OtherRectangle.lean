module

public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessHeld.RectangleOverlap
public import Theory.GroupTheory.PCoreLocalSetup

/-! The whole first-rectangle comparison retains the second rectangle too.
Its image is a normal elementary sixty-four in the common normalizer, hence
lies in the marked Sylow and its two-rectangle catalogue. Injectivity excludes
the first rectangle, whose image is already fixed by the kernel marking. -/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessHeld
open UniquenessLinear UniquenessMathieu.SourceNormalizer
variable {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']
  {z : G} {z' : G'} (F : MarkedCentralizer z) (F' : MarkedCentralizer z')

theorem plane_normalizer_equiv_other_rectangle
    (e : sourcePlaneNormalizer F ≃* sourcePlaneNormalizer F')
    (he : ∀ a : F.plane, e (inclusion F.plane.le_normalizer a) =
      inclusion F'.plane.le_normalizer (planeMarkingEquiv F F' a)) :
    (F.threeSpace.subgroupOf (sourcePlaneNormalizer F)).map e.toMonoidHom =
      F'.threeSpace.subgroupOf (sourcePlaneNormalizer F') := by
  let H := sourcePlaneNormalizer F
  let H' := sourcePlaneNormalizer F'
  let I := (sourceThreeSpaceNormalizer F).subgroupOf H
  let I' := (sourceThreeSpaceNormalizer F').subgroupOf H'
  have hI : I.map e.toMonoidHom=I' := plane_normalizer_equiv_rectangle_intersection F F' e he
  have hAH : F.threeSpace≤H := (flag_le_sourceSylow F).2.2.2.trans
    (plane_normalizers_contain_sourceSylow F).1
  have hAH' : F'.threeSpace≤H' := (flag_le_sourceSylow F').2.2.2.trans
    (plane_normalizers_contain_sourceSylow F').1
  let A := F.threeSpace.subgroupOf H
  let B := A.map e.toMonoidHom
  have hAI : A≤I := fun x hx => F.threeSpace.le_normalizer hx
  have hIN : I≤normalizer (A : Set H) := by
    rw [← subgroupOf_normalizer_eq hAH]
  have hBI : B≤I' := (map_mono hAI).trans_eq hI
  have hIN' : I'≤normalizer (B : Set H') := by
    rw [←hI,show B=A.map e.toMonoidHom from rfl,←map_equiv_normalizer_eq]
    exact map_mono hIN
  let := marked_rectangle_elementary F 3
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hAH
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map e.toMonoidHom
  let S : Sylow 2 H' := (sourceSylow F').subtype (plane_normalizers_contain_sourceSylow F').1
  have hSI : (S : Subgroup H')≤I' := by
    rw [Sylow.coe_subtype]
    exact fun x hx => (plane_normalizers_contain_sourceSylow F').2 hx
  have hBS : B≤(S : Subgroup H') := by
    have hh := (le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 B) hBI hIN').trans
      (pCoreIn_le_sylow I' (S.subtype hSI))
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le hSI] at hh
  let C := B.map H'.subtype
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.map H'.subtype
  have hCc : Nat.card C=64 := by
    rw [card_map_of_injective H'.subtype_injective,card_map_of_injective e.injective,
      Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv]
    exact threeSpace_card F
  have hCS : C≤(sourceSylow F' : Subgroup G') := by
    have hh := map_mono (f := H'.subtype) hBS
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le (plane_normalizers_contain_sourceSylow F').1] at hh
  have hfirst : (F.plane.subgroupOf H).map e.toMonoidHom=F'.plane.subgroupOf H' := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      have hh := he ⟨x,hx⟩
      change e x=_ at hh
      change (e x:G')∈F'.plane
      rw [hh]
      exact (planeMarkingEquiv F F' ⟨x,hx⟩).property
    · rw [card_map_of_injective e.injective,
        Nat.card_congr (subgroupOfEquivOfLe F.plane.le_normalizer).toEquiv,
        Nat.card_congr (subgroupOfEquivOfLe F'.plane.le_normalizer).toEquiv,
        plane_card,plane_card]
  rcases rectangleCatalogue F' C hCS inferInstance hCc with hc | hc
  · have hb : B=F'.plane.subgroupOf H' := by
      apply map_injective H'.subtype_injective
      rw [map_subgroupOf_eq_of_le F'.plane.le_normalizer]
      exact hc
    have ha : A=F.plane.subgroupOf H := map_injective e.injective (hb.trans hfirst.symm)
    have hh := congrArg (Subgroup.map H.subtype) ha
    rw [map_subgroupOf_eq_of_le hAH,map_subgroupOf_eq_of_le F.plane.le_normalizer] at hh
    exact (source_plane_ne_threeSpace F hh.symm).elim
  · apply map_injective H'.subtype_injective
    rw [map_subgroupOf_eq_of_le hAH']
    exact hc

end Theory.GroupTheory.TransvectionFive.UniquenessHeld
