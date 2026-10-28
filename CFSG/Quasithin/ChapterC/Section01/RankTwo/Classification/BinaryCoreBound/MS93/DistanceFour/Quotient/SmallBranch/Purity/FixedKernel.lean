module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Coordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Geometry

/-!
# Fixed lifts and the edge-star centralization step

The full fixed space on core/U lifts into B by its quotient-centralizer
interpretation. Since the core lies in VStar, the starred-intersection identity
then puts each lift in Z. This does not yet say that it lies in U.

A triple commutator into the local center is also contained in V′ = U.
The natural layer has no component-fixed vectors, so that triple commutator
vanishes. Its first commutator therefore lies in B, and membership in the core
and hence VStar puts it in Z. The actual edge and rank-one residual containments
remain explicit in this general deduction.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8)--(4.6.11), pp.905--909.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.SmallBranch
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (d : CoreModule source)

include common radius in
open scoped commutatorElement in
/-- The starred intersection places every lift of a fixed quotient vector in Z. -/
theorem fixed_lift_mem_Z (x : core R (alpha R))
    (hx : (d.projection x).toAdd ∈ fixedSpace d.representation ⊤) :
    (x : FreeAmalgam R) ∈ Z R (alpha R) := by
  apply core_inter_B_le_Z source geometry common radius (alpha R) (beta R)
    rfl (base_adjacent R)
  refine ⟨x.property, ?_⟩
  apply (mem_B_iff R (alpha R) (geometry.Z_normal _)
    (geometry.V_local _ rfl common.large_distance) x).mpr
  refine ⟨radius.core_le_radius _ rfl x.property, ?_⟩
  intro l hl
  rw [Ltilde_alpha] at hl
  obtain ⟨m, _hm, rfl⟩ := hl
  let c : core R (alpha R) := coreAction (R := R) m x * x⁻¹
  have hc : c ∈ d.projection.ker := by
    change d.projection c = 1
    apply Multiplicative.toAdd.injective
    change (d.projection (coreAction (R := R) m x * x⁻¹)).toAdd = 0
    rw [map_mul, map_inv]
    change (d.projection (coreAction (R := R) m x)).toAdd +
      -(d.projection x).toAdd = 0
    have hfix : d.representation (source.projection m) (d.projection x).toAdd =
        (d.projection x).toAdd := hx ⟨source.projection m, mem_top _⟩
    rw [d.action m x _ rfl, hfix, add_neg_cancel]
  rw [d.kernel] at hc
  apply DistanceEight.U_le_Z R (alpha R)
  exact hc

include common radius in
/-- A rank-one triple bound into the local center gives centralization modulo Z.
Its two containment premises must be checked for the actual edge and residual. -/
theorem commutator_le_Z_of_triple
    (E K : Subgroup (FreeAmalgam R))
    (hE : E ≤ V R (alpha R)) (hK : K ≤ Ltilde R (alpha R))
    (ht : ⁅⁅E, K⁆, V R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype) :
    ⁅E, K⁆ ≤ Z R (alpha R) := by
  have hc : ⁅E, K⁆ ≤ core R (alpha R) :=
    commutator_mono (hE.trans (Flags.V_le_Q geometry common.large_distance _ rfl)) hK
  have hV := hc.trans (radius.core_le_radius _ rfl)
  have hu : ⁅⁅E, K⁆, V R (alpha R)⁆ ≤ U R (alpha R) := by
    rw [← radius.radius_derived _ rfl]
    exact commutator_mono hV le_rfl
  have hz : ⁅⁅E, K⁆, V R (alpha R)⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [← Flags.U_fixed_eq_bot common (alpha R) rfl]
    refine le_inf hu (ht.trans ?_)
    rintro x ⟨z, hz, rfl⟩ l hl
    exact congrArg Subtype.val
      ((mem_center_iff.mp hz) ⟨l, (map_subtype_le _) hl⟩)
  apply le_trans ?_ (core_inter_B_le_Z source geometry common radius (alpha R) (beta R)
    rfl (base_adjacent R))
  refine le_inf hc ?_
  rw [radius.B_eq_center _ rfl]
  intro x hx
  refine ⟨⟨x, hV hx⟩, mem_center_iff.mpr ?_, rfl⟩
  intro y
  apply Subtype.ext
  exact (commutator_eq_bot_iff_le_centralizer.mp hz hx y y.property)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.SmallBranch
