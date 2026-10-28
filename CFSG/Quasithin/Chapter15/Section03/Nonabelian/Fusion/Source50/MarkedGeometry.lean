module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Perpendicular
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.FixedLine
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Recognition.FusionFields

/-!
# Original orthogonal markings in the recognized natural and dual action

The singular central point and definite-plane involution come from the
original orthogonal action. The commutator hyperplane is its perpendicular,
and the same recognized coordinates put that hyperplane over the two
transvection-center lines. These are the literal markings used by transfer.

Source: Aschbacher–Smith, 15.3.53, 56–58 and 60, printed pp.1146–1150.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
open Core.ResidualGeneration ResidualOrbits
variable {G : Type*} [Group G] [Finite G]

 theorem exists_marked_local_geometry (d : CharacteristicTwo.LocalData G)
    (h : (localSetup d (centralizerH d.Z)).Hypothesis)
    [(d.Z.subgroupOf (closureU d.Z d.ZS)).Normal]
    (hf : FusionCore.EarlierFusionInputs d.T d.M d.V d.V₁)
    (hconj : ∀ g : G, d.V.map (MulAut.conj g).toMonoidHom ≤ d.M →
      d.V.map (MulAut.conj g).toMonoidHom ≤ centralizer (d.V : Set G))
    (hnon : ¬ IsMulCommutative (localSpan d.V (centralizerH d.Z)))
    (hu : ¬ IsMulCommutative (closureU d.Z d.ZS))
    (hcomm : ⁅d.ZS,(d.T : Subgroup G)⁆ ≤ d.Z)
    {t : G} (r : Recognition.FusionRecognition (d.T : Subgroup G) d.Z d.ZS d.V t)
    (z v : G) (hz : orderOf z = 2) (hv : orderOf v = 2)
    (hzm : zpowers z = d.Z) (hvm : zpowers v = d.ZS ⊓ d.V₁) :
    Nonempty (Extraspecial.LocalGeometry r.recognized d.M d.V₁ z v) := by
  obtain ⟨c,hc,f,hf0,hplane⟩ := r.displacement_centers
  have hzV : z ∈ d.V := le_conjugateSpanBy d.Z d.M (hzm ▸ mem_zpowers z)
  refine ⟨{
    orthogonal := FusionCore.OriginalCoordinates.standardAction d.action
    z_order := hz
    z_mark := hzm
    z_mem := hzV
    z_singular := marked_point_singular d hf ⟨z,hzV⟩ hz hzm
    v_order := hv
    v_mark := hvm
    definite_le := d.action.plane_le 1
    definite := marked_plane_definite d
    perpendicular := intersection_perpendicular d (centralizerH d.Z) h hconj hnon hu
      ⟨z,hzV⟩ hz hzm
    fixed_line := quotient_fixed_line_of_commutator hcomm
      ⟨t,r.recognized.t_mem_H⟩ r.recognized.t_mem
    naturalCenter := c
    naturalCenter_ne := hc
    dualCenter := f
    dualCenter_ne := hf0
    plane := ?_ }⟩
  intro x hx
  simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hplane x hx

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
