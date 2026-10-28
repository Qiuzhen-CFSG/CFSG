module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Setup
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Candidate

/-!
# The supplied starred module and its dimension bound

Restrict the original radius quotient to the image of the actual starred
subgroup. The resulting layer uses exactly the original projection and
SL3(2) action. Thus the earlier starred-intersection theorem gives vanishing
fixed space and, in the large branch, faithfulness on this same subspace.

The identity V_alpha-star intersect B_alpha = Z_alpha injects its relative
quotient into V_alpha/B_alpha. The endpoint calculation's radius bound
therefore gives dimension at most six without invoking an FF-module theorem.
It does not yet identify either of the two natural constituents.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.6.10) and (4.6.12)(5), printed pp.908 and 911.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The literal starred subspace with the restriction of the original action. -/
noncomputable def starRepresentation (d : LayerModule source (V R (alpha R))) :
    Subrepresentation d.representation where
  toSubmodule := d.subspace (VStar R geometry (alpha R) (beta R))
  apply_mem_toSubmodule g v hv := d.subspace_invariant _
    (DistanceEight.V_normalized R _) (Flags.star_normalized geometry _ _) g v hv

/-- Restrict the supplied quotient map, retaining its exact relative kernel. -/
noncomputable def starLayer (d : LayerModule source (V R (alpha R))) :
    LayerModule source (VStar R geometry (alpha R) (beta R)) where
  Space := d.subspace (VStar R geometry (alpha R) (beta R))
  representation := (starRepresentation (geometry := geometry) d).toRepresentation
  projection := {
    toFun := fun x => Multiplicative.ofAdd ⟨(d.projection
      ⟨x, Flags.star_le_radius geometry _ _ x.property⟩).toAdd,
        (d.mem_subspace_iff _ _).mpr ⟨_, x.property, rfl⟩⟩
    map_one' := by
      apply Subtype.ext
      exact d.projection.map_one
    map_mul' := by
      intro x y
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd (d.projection.map_mul
        ⟨x, Flags.star_le_radius geometry _ _ x.property⟩
        ⟨y, Flags.star_le_radius geometry _ _ y.property⟩) }
  onto := by
    intro v
    obtain ⟨x, hx, he⟩ := (d.mem_subspace_iff _ _).mp v.toAdd.property
    refine ⟨⟨x, hx⟩, ?_⟩
    exact Subtype.ext he
  kernel := by
    ext x
    change (⟨(d.projection
      ⟨x, Flags.star_le_radius geometry _ _ x.property⟩).toAdd, _⟩ :
        d.subspace (VStar R geometry (alpha R) (beta R))) = 0 ↔ _
    rw [Subtype.ext_iff]
    change (⟨x, Flags.star_le_radius geometry _ _ x.property⟩ : V R (alpha R)) ∈
      d.projection.ker ↔ _
    rw [d.kernel]
    rfl
  action := by
    intro m x y hy
    apply Subtype.ext
    exact d.action m ⟨x, Flags.star_le_radius geometry _ _ x.property⟩
      ⟨y, Flags.star_le_radius geometry _ _ y.property⟩ hy

/-- The geometric radius bound bounds the actual starred image by six. -/
theorem star_finrank_le_six [Finite M] (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry)
    (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) (s : CriticalSegment geometry) (hest : Estimates d f s) :
    Module.finrank (ZMod 2) (d.subspace (VStar R geometry (alpha R) (beta R))) ≤ 6 := by
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
  let : Finite (V R (alpha R)) := Finite.of_injective
    (inclusion (geometry.V_local (alpha R) rfl common.large_distance))
    (inclusion_injective _)
  have hn : (B R (alpha R) (geometry.Z_normal _)).relIndex (V R (alpha R)) ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  have hle := Subgroup.relIndex_le_of_le_right (H := B R (alpha R) (geometry.Z_normal _))
    (Flags.star_le_radius geometry (alpha R) (beta R)) hn
  rw [← inf_relIndex_left, radius.star_intersection (alpha R) (beta R) rfl
    (base_adjacent R)] at hle
  rw [d.subspace_relIndex _ (Flags.star_le_radius geometry _ _)] at hle
  have hp : 2 ^ Module.finrank (ZMod 2) (d.subspace (VStar R geometry (alpha R) (beta R))) ≤ 2 ^ 6 := hle.trans hest.radius_bound
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hp


/-- All globally fixed vectors vanish in the supplied starred subspace. -/
theorem star_fixed_eq_bot (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (d : LayerModule source (V R (alpha R))) :
    fixedSpace (starRepresentation (geometry := geometry) d).toRepresentation ⊤ = ⊥ :=
  (starLayer d).fixed_eq_bot_of_le_star common radius le_rfl
    (Flags.star_normalized geometry _ _)

/-- The critical midpoint makes the literal starred action faithful. -/
theorem star_faithful [Finite M] (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (hb : geometry.b R = 4)
    (d : LayerModule source (V R (alpha R)))
    (s : CriticalSegment geometry) (hs : ¬ s.SmallIntersection) :
    Function.Injective (starRepresentation (geometry := geometry) d).toRepresentation := by
  apply (starLayer d).faithful_of_le_star common radius le_rfl
    (Flags.star_normalized geometry _ _)
  intro h
  apply large_intersection_not_le_Z radius s hs
  exact ((Z_le_orbitSpan s.middle).trans
    (orbitSpan_le_star geometry radius.toEarlyFacts _ _ (base_adjacent R)
      (midpoint_nu common radius hb s))).trans h

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
