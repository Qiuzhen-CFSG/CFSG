module
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleSolvableImage
public import Theory.GroupTheory.GeneralizedFitting.TwoCoreImageComparison
public import Theory.GroupTheory.GeneralizedFitting.NormalTwoTower

/-!
# Comparing quasisimple generalized Fitting subgroups through solvable kernels

A solvable normal kernel centralizes the source component and lies in its
center, since the generalized Fitting subgroup contains its centralizer.
The restriction to the component is surjective and induces an isomorphism
of the two central quotients, with the original representative formula.
The generalized Fitting subgroup also pulls back exactly. Consequently a
two-group quotient above the target component identifies the source's
literal two-residual with its component.

The original point-span comparison in Aschbacher--Smith 13.2.12 uses these
maps between the O₃′ quotient and the distinct faithful action quotient
(printed p.882). No isomorphism of the ambient quotients is assumed.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
  [IsQuasisimple (generalizedFitting G)]
  (f : G →* H) (hf : Function.Surjective f) [Group.IsSolvable f.ker]

omit [Finite H] in
/-- A solvable kernel lies in the embedded center of the source component. -/
theorem solvable_kernel_le_fitting_center :
    f.ker ≤ (center (generalizedFitting G)).map (generalizedFitting G).subtype := by
  let L := generalizedFitting G
  have hL : IsComponent G L := ⟨(inferInstance : L.Normal).isSubnormal,inferInstance⟩
  have hc : f.ker ≤ centralizer (L : Set G) :=
    le_centralizer_iff.mp (hL.le_centralizer_of_solvable_normal f.ker)
  intro x hx
  have hxL : x ∈ L := centralizer_generalizedFitting_le G (hc hx)
  refine ⟨⟨x,hxL⟩,?_,rfl⟩
  exact mem_center_iff.mpr (fun y => Subtype.ext (hc hx y y.property))

/-- Restrict the original surjection, using its proved component image. -/
@[expose] noncomputable def solvableImageComponent : generalizedFitting G →* generalizedFitting H :=
  (MulEquiv.subgroupCongr
    (quasisimple_generalizedFitting_image_of_solvable_kernel f hf).1).toMonoidHom.comp
      (f.subgroupMap (generalizedFitting G))

/-- The restriction still surjects onto the full target component. -/
theorem solvableImageComponent_surjective :
    Function.Surjective (solvableImageComponent f hf) :=
  (MulEquiv.subgroupCongr
    (quasisimple_generalizedFitting_image_of_solvable_kernel f hf).1).surjective.comp
      (f.subgroupMap_surjective _)

/-- The restriction is the original map on underlying elements. -/
theorem solvableImageComponent_coe (x : generalizedFitting G) :
    (solvableImageComponent f hf x : H) = f x := rfl

/-- The component central quotients agree through the original map. -/
@[expose] noncomputable def solvableImageComponentCentralEquiv :
    generalizedFitting G ⧸ center (generalizedFitting G) ≃*
      generalizedFitting H ⧸ center (generalizedFitting H) := by
  let := (quasisimple_generalizedFitting_image_of_solvable_kernel f hf).2
  let : IsSimpleGroup (generalizedFitting H ⧸ center (generalizedFitting H)) :=
    IsQuasisimple.simple
  let : Nontrivial (generalizedFitting H) :=
    (QuotientGroup.mk'_surjective (center (generalizedFitting H))).nontrivial
  exact IsQuasisimple.centralQuotientEquiv (solvableImageComponent f hf)
    (solvableImageComponent_surjective f hf)

/-- Compatibility with both literal central quotient projections. -/
theorem solvableImageComponentCentralEquiv_mk (x : generalizedFitting G) :
    solvableImageComponentCentralEquiv f hf (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' _ (solvableImageComponent f hf x) := by rfl

include hf in
/-- The preimage of the target component is exactly the source component. -/
theorem solvableImage_fitting_comap :
    (generalizedFitting H).comap f = generalizedFitting G := by
  rw [←(quasisimple_generalizedFitting_image_of_solvable_kernel f hf).1,
    comap_map_eq_self]
  exact (solvable_kernel_le_fitting_center f).trans (map_subtype_le _)

include f hf in
/-- A two-group quotient above the target component gives the source residual. -/
theorem solvableImage_residual_eq_fitting
    (hquot : IsPGroup 2 (H ⧸ generalizedFitting H)) :
    pResidual 2 G = generalizedFitting G := by
  have hq : IsPGroup 2 (G ⧸ generalizedFitting G) := by
    let q := (QuotientGroup.mk' (generalizedFitting H)).comp f
    have hk : q.ker = generalizedFitting G := by
      rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
      exact solvableImage_fitting_comap f hf
    exact hquot.of_equiv ((QuotientGroup.quotientKerEquivOfSurjective q
      ((QuotientGroup.mk'_surjective _).comp hf)).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hk))
  apply pResidual_eq_of_isPPerfect _ ?_ hq
  intro N hN hNp
  let := hN
  by_contra hn
  let : Nontrivial (generalizedFitting G ⧸ N) := QuotientGroup.nontrivial_iff.mpr hn
  let : Group.IsPerfect (generalizedFitting G ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent (generalizedFitting G ⧸ N) := hNp.isNilpotent
  exact Group.IsPerfect.not_isSolvable (generalizedFitting G ⧸ N) inferInstance
end Theory.GroupTheory
