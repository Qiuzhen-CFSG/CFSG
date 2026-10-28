module

public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit.SourceCurves
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# A one-dimensional orbit span is projectively constant

If the actual representation orbit spans one line in any coordinate basis,
all its nonzero vectors define the same original projective point. This is
the final linear-algebra step in excluding equal maximal and minimal weights
for the two distinct fixed points in Borel IV, 13.11(3).
-/

public section
open Theory.AlgebraicGroup.Variety.Geometric
open scoped LinearAlgebra.Projectivization
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Theory.AlgebraicGroup.Bor1.SeparatingBorel
universe u
variable {k E : Type u} [Field k] [IsAlgClosed k]
variable [AddCommGroup E] [Module k E] [FiniteDimensional k E]
variable {G : Variety k} [AlgebraicGroup G]
open ProjectiveLimit

theorem orbit_constant_of_coordinate_span_finrank_one
    (ρ : RationalRepresentation G E)
    (A : MorphicAction G (projectiveSpace k E))
    (b₀ b : Module.Basis (Fin (Module.finrank k E)) k E)
    (he : ∀ g p, projectiveSpacePointEquivOf b₀ (A.toMulAction.smul g p) =
      Projectivization.map (ρ.action g).1 (ρ.action g).toLinearEquiv.injective
        (projectiveSpacePointEquivOf b₀ p))
    (v : E) (hv : v ≠ 0)
    (hline : Module.finrank k (Submodule.span k
      (Set.range fun g : Variety.Point G => b.equivFun ((ρ.action g).1 v))) = 1)
    (g : Variety.Point G) :
    A.toMulAction.smul g
      (projectivePointOfVector (b₀.equivFun v) (b₀.equivFun.map_ne_zero_iff.mpr hv)) =
      projectivePointOfVector (b₀.equivFun v) (b₀.equivFun.map_ne_zero_iff.mpr hv) := by
  let W := Submodule.span k (Set.range fun g : Variety.Point G => b.equivFun ((ρ.action g).1 v))
  have hvW : b.equivFun v ∈ W := by
    apply Submodule.subset_span
    refine ⟨1, ?_⟩
    change b.equivFun ((ρ.action 1).1 v) = b.equivFun v
    rw [map_one]
    rfl
  have hgW : b.equivFun ((ρ.action g).1 v) ∈ W := Submodule.subset_span ⟨g, rfl⟩
  have hW : W = k ∙ b.equivFun v :=
    eq_span_singleton_of_mem_of_finrank_eq_one hline hvW (b.equivFun.map_ne_zero_iff.mpr hv)
  rw [hW] at hgW
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hgW
  rw [action_projective_vector ρ A b₀ he g v hv]
  have ha' : a • v = (ρ.action g).1 v := by
    apply b.equivFun.injective
    simpa only [map_smul] using ha
  apply (projectiveSpacePointEquivOf b₀).injective
  rw [projectiveSpacePointEquivOf_projectivePointOfVector b₀ ((ρ.action g).1 v)
      ((ρ.action g).toLinearEquiv.map_ne_zero_iff.mpr hv),
    projectiveSpacePointEquivOf_projectivePointOfVector b₀ v hv]
  apply (Projectivization.mk_eq_mk_iff' k _ _ _ _).mpr
  exact ⟨a, ha'⟩
end Theory.AlgebraicGroup.Bor1.SeparatingBorel
