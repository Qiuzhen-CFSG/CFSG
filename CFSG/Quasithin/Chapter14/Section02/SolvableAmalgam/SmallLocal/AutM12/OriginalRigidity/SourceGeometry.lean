module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.OriginalRigidity.PairTransport
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.Orientation

/-!
# Source geometry of the Aut(M₁₂) movement subgroup

The actual second-parabolic conjugate span identifies the model plane with the
original local module. Its elementary sixteen is the original Thompson subgroup,
and source uniqueness forces its normalizer to preserve that same plane.
These are the literal source inputs for the diagonal-cubic contradiction in
Aschbacher–Smith 14.2.21, printed p.988.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.OriginalRigidity
open SourcePreliminaries Chapter15.Section03
open QuaternionSwapModel.MarkedSylow QuaternionSwapModel.MarkedCubic
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H : Subgroup G} (c : CubicSourceContext T M Mc H)
variable (r : RankTwoAmalgam.Iso
  (RankTwoAmalgam.ofSubgroups H (H ⊓ (sourceResidual M Mc ⊔ (T : Subgroup G)))
    (sourceResidual M Mc ⊔ (T : Subgroup G)) inf_le_left inf_le_right)
  ChapterF.GreenBook.AutMathieuTwelve.autAmalgam)

include c

/-- The split movement mark is the original Sylow central involution. -/
theorem source_movement_mark : QuaternionSwapModel.Z.map (movement r) = centralInvolutions T := by
  rw [movement_mark]
  exact markedCore_image T H c.sylow_le_H c.mark_card r

/-- The marked plane in the actual pair is the original local module. -/
theorem source_movement_plane : localModule T M = markedPlane.map (movement r) := by
  obtain ⟨d⟩ := movement_geometry r
  rw [c.module_span,← source_movement_mark c r]
  exact d.conjugateClosure_eq_plane

/-- The source Thompson subgroup is the same marked elementary sixteen. -/
theorem source_movement_thompson :
    Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) = QuaternionSwapModel.A.map (movement r) := by
  obtain ⟨d⟩ := movement_geometry r
  have he := d.toGeometry.thompson_eq
  rwa [c.intersection] at he

/-- Source uniqueness controls the normalizer of the actual elementary
sixteen, hence forces it to preserve the original plane. -/
theorem source_movement_normalizer_control :
    normalizer (QuaternionSwapModel.A.map (movement r) : Set G) ≤
      normalizer (markedPlane.map (movement r) : Set G) := by
  obtain ⟨d⟩ := movement_geometry r
  let _ : IsElementaryAbelian 2 (QuaternionSwapModel.A.map (movement r)) :=
    (inferInstance : IsElementaryAbelian 2 QuaternionSwapModel.A).map (movement r)
  have hne : QuaternionSwapModel.A.map (movement r) ≠ ⊥ := by
    intro he
    have hc := card_map_of_injective (K := QuaternionSwapModel.A) (movement_injective r)
    rw [QuaternionSwapModel.card_A,he,card_bot] at hc
    norm_num at hc
  rw [← source_movement_plane c r,← c.module_normalizer]
  exact c.normalizer_control _ (IsElementaryAbelian.isPGroup 2 _) hne d.YT_normalizes_A

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.OriginalRigidity
end
