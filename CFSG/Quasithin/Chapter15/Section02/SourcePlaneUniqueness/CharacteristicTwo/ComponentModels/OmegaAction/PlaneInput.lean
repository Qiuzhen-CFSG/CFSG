module

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.OmegaAction.Reduction

/-!
# The preceding inverting-plane input to the finite Omega calculation

This records the literal 15.2.13(2) marking: the distinguished involution
belongs to the original Sylow action image, moves the whole odd core, and
has fixed plane ZS. It is an earlier-source input, not a stabilizer or
index-six conclusion. Its producers are qt-e-152-plane-geometry and
qt-e-152-small-parabolic.

The original centralizer S = C_T(ZS) maps onto a subgroup containing this
involution. The finite geometry must further identify its full image.
Source: Aschbacher--Smith, printed pp.1112--1113.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.OmegaAction
open ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}

/-- The distinguished involution and its actual fixed plane from 15.2.13(2).
The odd core is O_{2′}, while the later residual is O². -/
structure PlaneInverter (h : ChosenSmallSource T M Mc V) (ZS : Subgroup G) where
  involution : internalActionImage M V h.prepared.normalized
  in_sylow : involution ∈ ((T : Subgroup G).subgroupOf M).map (action h)
  order_two : orderOf involution = 2
  moves_odd_core : ⁅pPrimeCore 2 (internalActionImage M V h.prepared.normalized),
    zpowers involution⁆ = pPrimeCore 2 (internalActionImage M V h.prepared.normalized)
  fixed_plane : ∀ v : V, (v : G) ∈ ZS ↔ involution.val v = v

variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The marked involution belongs to the image of the original plane Sylow. -/
theorem inverter_mem_planeSylow_image (b : PlaneInverter hsource ZS) :
    b.involution ∈ ((planeSylow T ZS).subgroupOf M).map (action hsource) := by
  obtain ⟨t,ht,he⟩ := b.in_sylow
  refine ⟨t,⟨ht,?_⟩,he⟩
  intro z hz
  have hh : (action hsource t).val (⟨z,d.geometry.plane_le hz⟩ : V) =
      ⟨z,d.geometry.plane_le hz⟩ := by
    rw [he]
    exact (b.fixed_plane _).mp hz
  have hc := congrArg Subtype.val hh
  change (t : G) * z * (t : G)⁻¹ = z at hc
  exact (mul_inv_eq_iff_eq_mul.mp hc).symm

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.OmegaAction
