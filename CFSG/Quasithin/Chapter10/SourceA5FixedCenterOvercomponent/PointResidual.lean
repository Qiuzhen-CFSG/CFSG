module
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus
public import Theory.GroupTheory.Centralizer
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.FiniteImage
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.PointModel

/-!
# The residual of the literal marked element centralizer

A surjective marked orthogonal action identifies the image of the actual
centralizer C_H(v₂) with the stabilizer of a nonzero second-axis vector.
Surjective transport of prime residuals therefore gives an image of order
three, and the first-axis rotation proves that O²(C_H(v₂)) moves v₁.
Normalization and two-perfectness retain the same ambient subgroup.
Source: Aschbacher–Smith10.2.1, printed p.743.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
open BinaryFourPlus
variable {G : Type*} [Group G] [Finite G]

abbrev pointResidual (H : Subgroup G) (v : G) : Subgroup G :=
  (pResidual 2 (H ⊓ centralizer ({v}:Set G) : Subgroup G)).map
    (H ⊓ centralizer ({v}:Set G)).subtype

omit [Finite G] in
theorem pointResidual_le (H : Subgroup G) (v : G) :
    pointResidual H v ≤ H ⊓ centralizer ({v}:Set G) := map_subtype_le _

omit [Finite G] in
theorem pointResidual_normalized (H : Subgroup G) (v : G) :
    H ⊓ centralizer ({v}:Set G) ≤ normalizer (pointResidual H v:Set G) :=
  (H ⊓ centralizer ({v}:Set G)).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pResidual 2 _))

theorem pointResidual_twoPerfect (H : Subgroup G) (v : G) :
    IsPPerfect 2 (pointResidual H v) := isPPerfect_embedded_pResidual 2 _

theorem pointResidual_image_and_movement
    (H : Subgroup G) (f : H →* Wreath) (hf : Function.Surjective f)
    (v₁ v₂ : G) (a b : Plane) (ha : a≠0) (hb : b≠0)
    (hfix₁ : ∀ h : H, (wreathToIsometry (f h)).val (a,0)=(a,0) ↔
      (h:G)∈centralizer ({v₁}:Set G))
    (hfix₂ : ∀ h : H, (wreathToIsometry (f h)).val (0,b)=(0,b) ↔
      (h:G)∈centralizer ({v₂}:Set G)) :
    Nat.card (((pointResidual H v₂).subgroupOf H).map f)=3 ∧
      ¬ pointResidual H v₂ ≤ centralizer ({v₁}:Set G) := by
  let C := H ⊓ centralizer ({v₂}:Set G)
  let i : C →* H := inclusion (show C≤H from inf_le_left)
  let r : C →* pointStabilizer (0,b) := (f.comp i).codRestrict _
    (fun x => (hfix₂ (i x)).mpr x.property.2)
  have hr : Function.Surjective r := by
    intro g
    obtain ⟨h,hh⟩ := hf g.val
    have hc : h.val∈C := ⟨h.property,(hfix₂ h).mp (hh ▸ g.property)⟩
    exact ⟨⟨h.val,hc⟩,Subtype.ext hh⟩
  have him : ((pointResidual H v₂).subgroupOf H).map f =
      (pResidual 2 (pointStabilizer (0,b))).map (pointStabilizer (0,b)).subtype := by
    have hi : (pointResidual H v₂).subgroupOf H = (pResidual 2 C).map i := by
      apply map_injective H.subtype_injective
      rw [map_subgroupOf_eq_of_le ((pointResidual_le H v₂).trans inf_le_left),map_map]
      rfl
    rw [hi,map_map]
    have he : f.comp i=(pointStabilizer (0,b)).subtype.comp r := rfl
    rw [he,←map_map,map_pResidual_of_surjective 2 r hr]
  refine ⟨?_,?_⟩
  · rw [him,card_map_of_injective (pointStabilizer (0,b)).subtype_injective]
    exact point_stabilizer_residual_card b hb
  · intro hc
    obtain ⟨g,hg,hmove⟩ := exists_odd_point_stabilizer_moving a b ha
    rw [←map_pResidual_of_surjective 2 r hr] at hg
    obtain ⟨x,hx,hxg⟩ := hg
    apply hmove
    have hy : x.val∈pointResidual H v₂ := mem_map_of_mem C.subtype hx
    have hh := (hfix₁ (i x)).mpr (hc hy)
    have he : f (i x)=g.val := congrArg Subtype.val hxg
    rwa [←he]

end CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
