module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.Geometry
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.CentralizerGeometry
public import Theory.SpecificGroups.BinaryLinear.FourCentralizerOvergroups

/-!
# Proper overgroups of the degree-four binary transvection centralizer

Transport a subgroup of the component through its actual PSL₄(2) linear
model. The centralizer is the common stabilizer of the transvection's image
line and fixed hyperplane. The intrinsic binary linear-group calculation
shows that every proper overgroup of this common stabilizer preserves one
of those two subspaces. Transporting back gives exactly the cover required
by `FourIntersection.intersection_eq_of_geometric_inputs`.

Source application: Aschbacher–Smith 2.3.9(7)(g), combined manuscript of
1 March 2004, printed pp.525–526 of `refs/quasithin.pdf`. This module proves
the overgroup cover; the parent owns the intersection and diagram-action
assembly.
-/

public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary.FourIntersection

open Subgroup

variable {G : Type*} [Group G] {L : Subgroup G}

/-- A proper overgroup of the transvection centralizer lies in its image-line
stabilizer or its fixed-hyperplane stabilizer. -/
theorem proper_overgroup_cover (e : L ≃* PSL 4) {t : L}
    (c : TransvectionCoordinates e t) (K : Subgroup L)
    (hC : centralizer ({t} : Set L) ≤ K) (hK : K ≠ ⊤) :
    K ≤ subspaceStabilizer e c.line ∨ K ≤ subspaceStabilizer e c.hyperplane := by
  let E := linearModel e
  let R := K.map E.toMonoidHom
  have hR : R ≠ ⊤ := by
    intro hR
    apply hK
    apply top_unique
    intro x _
    have hx : E x ∈ R := hR ▸ mem_top _
    obtain ⟨y, hy, he⟩ := hx
    exact E.injective he ▸ hy
  have hCR : BinaryLinear.parabolic (Submodule.span (ZMod 2) {c.vector}) ⊓
      BinaryLinear.parabolic c.functional.ker ≤ R := by
    intro g hg
    refine ⟨E.symm g, ?_, E.apply_symm_apply g⟩
    apply hC
    rw [c.centralizer_eq]
    change E (E.symm g) ∈ BinaryLinear.parabolic (Submodule.span (ZMod 2) {c.vector}) ⊓
      BinaryLinear.parabolic c.functional.ker
    simpa only [E.apply_symm_apply] using hg
  rcases BinaryLinear.FourCentralizerOvergroups.flag_overgroup_cover
    c.vector c.functional c.incident R hCR hR with hl | hh
  · left
    intro x hx
    exact hl (show E x ∈ R from ⟨x, hx, rfl⟩)
  · right
    intro x hx
    exact hh (show E x ∈ R from ⟨x, hx, rfl⟩)

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary.FourIntersection

end
