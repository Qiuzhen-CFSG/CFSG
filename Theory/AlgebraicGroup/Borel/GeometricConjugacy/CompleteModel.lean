module

public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.Defs
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.ClosedOrbit
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.MaximalBorel
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagData
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagRepresentation
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagGeometry
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.MinimalOrbit

/-!
# Complete Borel homogeneous-space models

Every algebraic group admitting a Borel has a Borel whose homogeneous space
admits a complete geometric model with a regular action and an equivariant
equivalence on rational points.

Choose a Borel of maximal dimension and realize it as the exact stabilizer of
a full flag in a faithful rational representation. The geometric flag model
has solvable point stabilizers, all of dimension bounded by that Borel. The
selected flag orbit is therefore closed. Its reduced closed subvariety is
complete and its rational points identify equivariantly with the actual
Plücker homogeneous space.

Source: Borel, *Linear Algebraic Groups*, §11.1, the construction before the
fixed-point/conjugacy argument (`refs/KGroup/Bor1/Chapter4.tex`). The source
assumes connectedness. Here the solvable-subgroup bound uses identity
components, and the orbit dimension theorem handles all components and
possibly nonreduced scheme fibres, so no connectedness or separability
assumption is needed.
-/

namespace Theory.AlgebraicGroup.BorelGeometricConjugacy

open Variety.Geometric

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

/-- A maximal-dimensional Borel has a complete geometric homogeneous-space
model, constructed from its own closed flag orbit. -/
public theorem nonempty_completeModel_of_borel_maximal_dimension
    (B : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (hmax : ∀ C : ClosedSubgroup G, IsBorelSubgroup C →
      Variety.dimension C.carrierVariety ≤ Variety.dimension B.carrierVariety) :
    Nonempty (CompleteModel B) := by
  obtain ⟨V, hVadd, hVmodule, hVfinite, ρ, hρrat, hρfaith, F, hF⟩ :=
    exists_faithful_rationalRepresentation_exact_flagStabilizer B hB
  obtain ⟨M⟩ := FlagGeometry.nonempty_flagModel ρ hρrat
  let x := M.pointEquiv.symm F
  have hstab (g : Variety.Point G) :
      M.action.toMulAction.smul g x = x ↔ g ∈ B.toSubgroup := by
    rw [M.smul_eq_iff, Equiv.apply_symm_apply]
    exact hF g
  have hstab_eq : M.action.pointStabilizer x = B := by
    apply SetLike.ext
    intro g
    exact (M.action.mem_pointStabilizer x g).trans (hstab g)
  have hsolv (y : Point M.variety) :
      Group.IsSolvable (Variety.Point (M.action.pointStabilizer y).carrierVariety) := by
    have heq : (M.action.pointStabilizer y).toSubgroup =
        flagStabilizer ρ (M.pointEquiv y) := by
      apply Subgroup.ext
      intro g
      exact (M.action.mem_pointStabilizer y g).trans (M.smul_eq_iff g y)
    have hs : Group.IsSolvable (M.action.pointStabilizer y).toSubgroup := by
      rw [heq]
      exact flagStabilizer_isSolvable ρ hρfaith (M.pointEquiv y)
    let e := Equiv.mulEquiv (M.action.pointStabilizer y).pointEquiv
    let := hs
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have hclosed := M.action.isClosed_orbitMorphismAt_range_of_maximal_stabilizer_dimension x
    (fun y => by
      rw [hstab_eq]
      exact solvable_dimension_le_of_borel_maximal_dimension B hmax
        (M.action.pointStabilizer y) (hsolv y))
  let Z : TopologicalSpace.Closeds M.variety.toScheme :=
    ⟨Set.range (M.action.orbitMorphismAt x).hom, hclosed⟩
  apply nonempty_completeModel_of_closed_orbit_support B M.action x M.complete Z ?_ hstab
  intro y
  change y.1 (IsLocalRing.closedPoint k) ∈ Set.range (M.action.orbitMorphismAt x).hom ↔ _
  rw [← (M.action.orbitMorphismAt x).point_mem_range_iff_closedPoint_mem_range]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨affinePointEquiv G g, ?_⟩
    exact (M.action.orbitMorphismAt_apply x (affinePointEquiv G g)).symm.trans
      ((congrArg (fun p : Point (ofAffine G) => M.action.orbitMorphismAt x p)
        ((affinePointEquiv G).symm_apply_apply g)).trans hg)
  · rintro ⟨g, hg⟩
    exact ⟨(affinePointEquiv G).symm g, (M.action.orbitMorphismAt_apply x g).trans hg⟩

/-- Every algebraic group admitting a Borel has a Borel with a genuine complete
geometric model of its homogeneous space. The ambient group may be disconnected. -/
public theorem exists_borel_completeModel
    (B₀ : ClosedSubgroup G) (hB₀ : IsBorelSubgroup B₀) :
    ∃ B : ClosedSubgroup G, IsBorelSubgroup B ∧ Nonempty (CompleteModel B) := by
  obtain ⟨B, hB, hmax⟩ := exists_borel_of_maximal_dimension B₀ hB₀
  exact ⟨B, hB, nonempty_completeModel_of_borel_maximal_dimension B hB hmax⟩

end Theory.AlgebraicGroup.BorelGeometricConjugacy
