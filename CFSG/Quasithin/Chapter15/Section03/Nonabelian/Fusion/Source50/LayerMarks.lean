module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Perpendicular
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization.LocalPlanes.Orthogonality

/-!
# Transport the source markings to the common lower-layer coordinates

The determinant-preserving coordinates constructed in source 54 retain
all three original markings: the singular point, its perpendicular, and
the nonsingular definite-plane involution. The determinant equality alone
suffices; no additional choice of model or conjugating automorphism is used.

Source: Aschbacher–Smith, 15.3.60, printed p.1150.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
open Core.Automizers.Models ResidualOrbits.CubicBlocks.Realization
variable {G : Type*} [Group G] [Finite G]
variable (d : CharacteristicTwo.LocalData G) {I P : Subgroup G}
  {hIP : I ≤ normalizer (P : Set G)} {hIV : I ≤ normalizer (d.V : Set G)}
  [(d.V.subgroupOf P).Normal]
  (layers : LayerActions I d.Y P d.V hIP hIV)
  (hdet : ∀ v : d.V, (layers.lowerCoordinates v).toAdd.det =
    FusionCore.orthogonalCoordinateValue (d.action.coordinates v))
include hdet

 theorem lower_marked_singular
    (hf : FusionCore.EarlierFusionInputs d.T d.M d.V d.V₁)
    (z : d.V) (hz : orderOf (z : G) = 2) (hzm : zpowers (z : G) = d.Z) :
    (layers.lowerCoordinates z).toAdd.det = 0 := by
  rw [hdet,← standard_form_eq_coordinateValue]
  exact marked_point_singular d hf z hz hzm

 omit [Finite G] in
theorem lower_polar_eq_standard (z x : d.V) :
    determinantPolar (layers.lowerCoordinates z) (layers.lowerCoordinates x) =
      OrthogonalFourBinary.form.polarBilin
        ((FusionCore.OriginalCoordinates.standardAction d.action).coordinates z).toAdd
        ((FusionCore.OriginalCoordinates.standardAction d.action).coordinates x).toAdd := by
  rw [standard_polar_eq_coordinateValue]
  change (layers.lowerCoordinates z * layers.lowerCoordinates x).toAdd.det -
      (layers.lowerCoordinates z).toAdd.det - (layers.lowerCoordinates x).toAdd.det = _
  rw [← map_mul,hdet,hdet,hdet,map_mul]

 theorem lower_marked_hyperplane
    (h : (localSetup d (centralizerH d.Z)).Hypothesis)
    (hf : ∀ g : G, d.V.map (MulAut.conj g).toMonoidHom ≤ d.M →
      d.V.map (MulAut.conj g).toMonoidHom ≤ centralizer (d.V : Set G))
    (hnon : ¬ IsMulCommutative (localSpan d.V (centralizerH d.Z)))
    (hu : ¬ IsMulCommutative (closureU d.Z d.ZS))
    (z : d.V) (hz : orderOf (z : G) = 2) (hzm : zpowers (z : G) = d.Z) :
    closureU d.Z d.ZS ⊓ d.V = sourceHyperplane layers z := by
  apply le_antisymm
  · rintro x ⟨hx,hxV⟩
    rw [mem_sourceHyperplane layers z ⟨x,hxV⟩,lower_polar_eq_standard d layers hdet]
    exact (intersection_perpendicular d (centralizerH d.Z) h hf hnon hu z hz hzm
      ⟨x,hxV⟩).mp hx
  · intro x hx
    have hxV := sourceHyperplane_le layers z hx
    refine ⟨?_,hxV⟩
    rw [mem_sourceHyperplane layers z ⟨x,hxV⟩,lower_polar_eq_standard d layers hdet] at hx
    exact (intersection_perpendicular d (centralizerH d.Z) h hf hnon hu z hz hzm
      ⟨x,hxV⟩).mpr hx

 omit [Finite G] in
theorem lower_marked_nonsingular (v : d.V) (hv : orderOf (v : G) = 2)
    (hvm : zpowers (v : G) = d.ZS ⊓ d.V₁) :
    (layers.lowerCoordinates v).toAdd.det ≠ 0 := by
  rw [hdet,← standard_form_eq_coordinateValue]
  apply marked_plane_definite d v
  · exact (hvm ▸ mem_zpowers (v : G)).2
  · intro he
    have hg : (v : G) = 1 := congrArg Subtype.val he
    simp [hg] at hv

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
