module

public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.M11Exclusion.Inputs
public import Theory.Representation.Mathieu.SmallModules.M11PointGeometry

/-!
# Rank-two actors on the marked M₁₁ point module

Restrict the actor to the given normal component, transport it through the
actual M₁₁ isomorphism, and use the supplied equivalence of representations.
These maps preserve the elementary rank and the literal fixed codimension.
The intrinsic eleven-point calculation therefore discharges the point-geometry
input to the bounded M₁₁ exclusion.

Source: Aschbacher--Smith, K.4, printed p.457 (PDF p.468); the point action and
augmentation conventions are those of B.3.
-/

public section
open Representation.BinaryOffender Subgroup

namespace CFSG.Quasithin.ChapterK.SporadicCatalogue.M11Exclusion
open Representation.MathieuSmall.M12Recognition
universe u v

/-- The exact marked ambient point-module geometry contract. -/
theorem rankTwoPointGeometry : RankTwoPointGeometry.{u,v} := by
  intro G V _ _ _ _ _ ρ L _ e _ hE A hA hr hAL
  obtain ⟨E⟩ := hE
  let B := A.subgroupOf L
  let C := B.map e.toMonoidHom
  let _ : IsElementaryAbelian 2 A := hA.2
  let _ : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hAL
  have hmap : B.map L.subtype = A := map_subgroupOf_eq_of_le hAL
  have hB : IsElementaryTwo B := ⟨fun h => hA.1 (by rw [← hmap, h, Subgroup.map_bot]),
    inferInstance⟩
  have hC : IsElementaryTwo C :=
    ⟨fun h => hB.1 ((map_eq_bot_iff_of_injective B e.injective).mp h),
      IsElementaryAbelian.map e.toMonoidHom⟩
  have hrC : rank C = 2 := by
    rw [rank_map_injective e.toMonoidHom e.injective,
      ← rank_map_injective L.subtype L.subtype_injective B, hmap, hr]
  have hc := Representation.MathieuSmall.M11PointGeometry.point_rankTwo_fixedCodim_ge_five C hC hrC
  have he := fixedCodim_map_equivariant (ρ.comp L.subtype) pointRepresentation
    e.toMonoidHom E.toLinearEquiv
    (fun g v => LinearMap.congr_fun (E.isIntertwining' g) v) B
  have he' : fixedCodim ρ A = fixedCodim pointRepresentation C := by
    unfold fixedCodim at he ⊢
    rw [fixedSpace_comp_map, hmap] at he
    exact he
  rwa [he']
end CFSG.Quasithin.ChapterK.SporadicCatalogue.M11Exclusion
