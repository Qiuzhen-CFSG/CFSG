module

public import Theory.Representation.HexacodeAction.Cover
public import Theory.GroupTheory.PerfectCenterFrattini

/-!
# Generation through the full hexacode coordinate quotient

A subgroup inducing the entire symmetric coordinate quotient is the full
hexacode group. Its intersection with the even cover surjects onto A6;
perfectness removes the central cubic supplement there. The remaining
coordinate fibers then lie in the subgroup as well.

This retains the entire cubic kernel. It is the covering-group lift
needed in the two-conjugate generation paragraph after Aschbacher--Smith
12.7.18, printed p.845.
-/

public noncomputable section
open Atlas.Codes Subgroup
namespace Representation.Hexacode

/-- Full symmetric image forces generation of the whole nonsplit cover. -/
theorem subgroup_eq_top_of_coordinate_image (A : Subgroup HexAutomorphisms)
    (hA : A.map hexCoordinateSixHom = ⊤) : A = ⊤ := by
  let B := A.comap hexSign.ker.subtype
  have hB : B.map hexEvenCoordinate = ⊤ := by
    apply top_unique
    intro p _
    have hp : p.val ∈ A.map hexCoordinateSixHom := by rw [hA]; trivial
    obtain ⟨g, hg, hgp⟩ := hp
    have heven : hexSign g = 1 := by
      change Equiv.Perm.sign (hexCoordinateSixHom g) = 1
      rw [hgp]
      exact p.property
    exact ⟨⟨g, heven⟩, hg, Subtype.ext hgp⟩
  have hcover : B ⊔ center HexEvenAutomorphisms = ⊤ := by
    have hh := congrArg (fun C => C.comap hexEvenCoordinate) hB
    simpa only [comap_map_eq, comap_top, even_kernel_eq_center] using hh
  let : Group.IsPerfect HexEvenAutomorphisms := even_isPerfect
  have hBtop : B = ⊤ := eq_top_of_sup_center_eq_top B hcover
  have hscalar : zpowers hexZ ≤ A := by
    apply zpowers_le.mpr
    exact show hexEvenZ ∈ B from hBtop.symm ▸ mem_top _
  apply top_unique
  intro g _
  have hg : hexCoordinateSixHom g ∈ A.map hexCoordinateSixHom := by rw [hA]; trivial
  obtain ⟨x, hx, hxg⟩ := hg
  have hk : g * x⁻¹ ∈ hexCoordinateSixHom.ker := by
    change hexCoordinateSixHom (g * x⁻¹) = 1
    rw [map_mul, map_inv, hxg, mul_inv_cancel]
  rw [hexCoordinateSix_kernel] at hk
  simpa only [inv_mul_cancel_right] using A.mul_mem (hscalar hk) hx

end Representation.Hexacode
