module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ElementaryParabolic.FullCore
public import Theory.GroupTheory.PerfectCentralSupplement

/-!
# Perfectness of the original lifted parabolics

Their projective images are perfect and have odd index. Central Sylow transfer
therefore puts the whole two-kernel into the actual residual, proving that the
full parabolic equals its residual. This is observation (i) in the proof of
Aschbacher--Smith I.2.2, printed p.410.
-/

public section
open Subgroup
namespace Matrix.PSL3Four.ElementaryParabolic
open Matrix.PSL3.LinearThree Matrix.PSL3.RootPlaneGeometry
open Matrix.PSL3.LinearThree.OuterExtensions
variable {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
theorem parabolic_isPerfect (f : E →* PSL) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hk : IsPGroup 2 f.ker) (b : Bool) :
    Group.IsPerfect (liftedParabolic f b) := by
  let N := (liftedResidual f b).map (liftedParabolic f b).subtype
  have hmap : N.map f = parabolic F b := (residual_image f hf b).trans
    (native_parabolic_eq_local b).symm
  have hsup : N ⊔ f.ker = liftedParabolic f b := by
    rw [← Subgroup.comap_map_eq, hmap]
  have hodd : ¬2 ∣ (liftedParabolic f b).index := by
    rw [Subgroup.index_comap_of_surjective _ hf]
    have hu : unipotent F ≤ parabolic F b := by
      rw [native_parabolic_eq_local]
      cases b
      · exact unipotent_le_lineLocal F
      · exact unipotent_le_pointLocal F
    exact fun hh => odd_index_unipotent F (by decide : 0 < 2)
      (by simpa using card_F) (hh.trans (Subgroup.index_dvd_of_le hu))
  have hNP : N = liftedParabolic f b := by
    have hh := sup_central_pSubgroup_eq N f.ker hc hk (hsup.symm ▸ hodd)
    exact hh.symm.trans hsup
  apply Group.IsPerfect.ofSurjective (f := (liftedResidual f b).subtype)
  intro x
  have hx : x.val ∈ N := hNP.symm ▸ x.property
  obtain ⟨y,hy,he⟩ := hx
  exact ⟨⟨y,hy⟩, Subtype.ext he⟩
end Matrix.PSL3Four.ElementaryParabolic
