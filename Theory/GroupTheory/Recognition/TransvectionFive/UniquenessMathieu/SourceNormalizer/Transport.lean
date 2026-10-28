module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Rectangles

/-!
# Faithful ambient normalizer quotients for the two marked rectangles

Transport of the explicit rectangle coordinates gives each pulled-back group
order 64. Any element centralizing a rectangle centralizes its marked involution,
so the full-centralizer marking and the model calculation show that both
rectangles are self-centralizing in G. Consequently their normalizer quotients
act faithfully by the literal ambient conjugation maps.

These are the faithful six-dimensional action inputs used in Aschbacher,
*Sporadic Groups* (1994), 39.6 and 40.3–40.4, printed pp.214–219. The quotient
isomorphism types and fusion-control statements are separate source obligations.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
open UniquenessLinear
variable {G : Type*} [Group G] {z : G} (F : MarkedCentralizer z)

/-- The literal plane inherits the model's six binary coordinates. -/
def planeCoordinates : F.plane ≃* Multiplicative (Fin 2 → Fin 3 → ZMod 2) :=
  (F.pullbackEquiv Model.plane Model.plane_le_centralizer).trans modelPlaneCoordinates

/-- The coordinates use the original centralizer marking on every element. -/
theorem planeCoordinates_apply (a : F.plane) (i : Fin 2) (j : Fin 3) :
    (planeCoordinates F a).toAdd i j =
      (F.equiv ⟨a, F.pullback_le Model.plane a.property⟩ : SL)
        (i.castLE (by decide)) (j.natAdd 2) :=
  modelPlaneCoordinates_apply (F.pullbackEquiv Model.plane Model.plane_le_centralizer a) i j

/-- The literal three-space uses the same coordinates after marking interchange. -/
def threeSpaceCoordinates : F.threeSpace ≃* Multiplicative (Fin 2 → Fin 3 → ZMod 2) :=
  (MulEquiv.subgroupCongr (oppositeMarking_plane F).symm).trans
    (planeCoordinates (oppositeMarking F))

theorem plane_card : Nat.card F.plane = 64 := by
  rw [Nat.card_congr (planeCoordinates F).toEquiv]
  change Nat.card (Fin 2 → Fin 3 → ZMod 2) = 64
  simp

theorem threeSpace_card : Nat.card F.threeSpace = 64 := by
  rw [← oppositeMarking_plane F]
  exact plane_card (oppositeMarking F)

/-- Self-centralization holds in the original ambient group, since z belongs
to the rectangle and forces every centralizing element into the marking domain. -/
theorem plane_centralizer_eq : Subgroup.centralizer (F.plane : Set G) = F.plane := by
  have image_mem (a : Model.plane) :
      (F.equiv.symm ⟨a, Model.plane_le_centralizer a.property⟩ : G) ∈ F.plane := by
    apply (F.mem_pullback_iff Model.plane _).mpr
    simpa only [F.equiv.apply_symm_apply] using a.property
  apply le_antisymm
  · intro x hx
    have hxC : x ∈ Subgroup.centralizer ({z} : Set G) :=
      mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp hx z (point_mem_plane F)).symm
    apply (F.mem_pullback_iff Model.plane ⟨x, hxC⟩).mpr
    rw [← model_plane_centralizer_eq]
    apply mem_centralizer_iff.mpr
    intro a ha
    let b := F.equiv.symm ⟨a, Model.plane_le_centralizer ha⟩
    have he : b * ⟨x, hxC⟩ = ⟨x, hxC⟩ * b :=
      Subtype.ext (mem_centralizer_iff.mp hx b (image_mem ⟨a, ha⟩))
    have him := congrArg (fun q => (F.equiv q : SL)) he
    simpa only [map_mul, Subgroup.coe_mul, b, F.equiv.apply_symm_apply] using him
  · let := marked_rectangle_elementary F 2
    intro x hx
    exact mem_centralizer_iff.mpr fun y hy => setLike_mul_comm hy hx

/-- The marking interchange transports self-centralization to A₂. -/
theorem threeSpace_centralizer_eq :
    Subgroup.centralizer (F.threeSpace : Set G) = F.threeSpace := by
  simpa only [oppositeMarking_plane] using plane_centralizer_eq (oppositeMarking F)

abbrev planeNormalizer := normalizer (F.plane : Set G)
abbrev threeSpaceNormalizer := normalizer (F.threeSpace : Set G)
abbrev planeQuotient := planeNormalizer F ⧸ F.plane.subgroupOf (planeNormalizer F)
abbrev threeSpaceQuotient := threeSpaceNormalizer F ⧸ F.threeSpace.subgroupOf (threeSpaceNormalizer F)

/-- The quotient acts on A₁ by the actual ambient conjugation. -/
def planeQuotientAction : planeQuotient F →* MulAut F.plane :=
  QuotientGroup.lift _ F.plane.normalizerMonoidHom (by
    rw [normalizerMonoidHom_ker, plane_centralizer_eq F])

/-- The quotient acts on A₂ by the actual ambient conjugation. -/
def threeSpaceQuotientAction : threeSpaceQuotient F →* MulAut F.threeSpace :=
  QuotientGroup.lift _ F.threeSpace.normalizerMonoidHom (by
    rw [normalizerMonoidHom_ker, threeSpace_centralizer_eq F])

theorem planeQuotientAction_injective : Function.Injective (planeQuotientAction F) := by
  apply (QuotientGroup.injective_lift_iff _ _ _).mpr
  rw [normalizerMonoidHom_ker, plane_centralizer_eq F]

theorem threeSpaceQuotientAction_injective : Function.Injective (threeSpaceQuotientAction F) := by
  apply (QuotientGroup.injective_lift_iff _ _ _).mpr
  rw [normalizerMonoidHom_ker, threeSpace_centralizer_eq F]

theorem planeQuotientAction_mk_apply (g : planeNormalizer F) (a : F.plane) :
    (planeQuotientAction F (QuotientGroup.mk g) a : G) = (g : G) * (a : G) * (g : G)⁻¹ :=
  normalizerMonoidHom_apply_apply_coe F.plane g a

theorem threeSpaceQuotientAction_mk_apply (g : threeSpaceNormalizer F) (a : F.threeSpace) :
    (threeSpaceQuotientAction F (QuotientGroup.mk g) a : G) = (g : G) * (a : G) * (g : G)⁻¹ :=
  normalizerMonoidHom_apply_apply_coe F.threeSpace g a

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
