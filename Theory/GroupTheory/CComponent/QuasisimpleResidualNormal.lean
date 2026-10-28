module
public import Theory.GroupTheory.CComponent.SolvableImageNormality
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.PResidual.NormalSubgroup
/-!
# C-components above a quasisimple two-residual

A solvable-kernel image preserves C-components. Perfectness puts the image
inside the target two-residual, so quasisimplicity forces equality. Its
normality then reflects through the original solvable-kernel map.

Source: Aschbacher–Smith A.3.3, applied to the single source in E.2.3.
-/

public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
/-- A single quasisimple residual forces every original C-component to be normal. -/
theorem IsCComponent.normal_of_solvable_kernel_quasisimple_residual (L : Subgroup G) (hL : L.IsCComponent) (q : G →* H) (hq : Function.Surjective q)
    [Group.IsSolvable q.ker] (hR : IsQuasisimple (pResidual 2 H)) : L.Normal := by
  have hQ := cComponent_map_of_solvable_ker hL q hq
  let := hQ.perfect
  have hp : IsPPerfect 2 (L.map q) := by
    intro N hN hn
    let := hN
    let : Group.IsNilpotent ((L.map q) ⧸ N) := hn.isNilpotent
    apply top_unique
    rw [←solvableResidual_eq_top (G := L.map q)]
    exact solvableResidual_le_of_solvable_quotient N
  have hc : (pResidual 2 H).IsCComponent :=
    (show IsComponent H (pResidual 2 H) from ⟨(inferInstance : (pResidual 2 H).Normal).isSubnormal,hR⟩).isCComponent
  have he := hQ.eq_of_le hc (le_pResidual_of_isPPerfect _ hp)
  exact cComponent_normal_of_solvable_image_normal hL q hq (he ▸ inferInstance)

end Subgroup
