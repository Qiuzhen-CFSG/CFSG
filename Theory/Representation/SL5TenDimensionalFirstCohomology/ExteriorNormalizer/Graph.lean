module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.ExteriorNormalizer.Coordinates
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
import Mathlib.Tactic.FinCases

/-!
# Exclusion of the graph automorphism on the exterior modules

On a block of order seven with a two-dimensional identity block, the exterior
square and cube have different traces from their inverse-transpose twists.
Thus no invertible linear map implements the graph automorphism. Simplicity of
the actual projective group also gives faithfulness of both exterior actions.

Source application: Aschbacher--Smith, G.9.3(13), printed pp.354, 356--357.
-/

namespace Representation.SL5TenDimensional.ExteriorNormalizer
open BinaryLinear.OuterCyclic

set_option maxRecDepth 10000

private def witness : Group :=
  ⟨!![0,0,1,0,0; 1,0,1,0,0; 0,1,0,0,0; 0,0,0,1,0; 0,0,0,0,1], by decide +kernel⟩

private def graphWitness : Group :=
  ⟨!![1,0,1,0,0; 1,0,0,0,0; 0,1,0,0,0; 0,0,0,1,0; 0,0,0,0,1], by decide +kernel⟩

private theorem graph_witness : graphSL 5 witness = graphWitness := by
  change (Matrix.SpecialLinearGroup.transpose witness)⁻¹ = graphWitness
  apply inv_eq_of_mul_eq_one_right
  decide +kernel

private theorem trace_graph_ne (a : Fin 2) :
    LinearMap.trace (ZMod 2) (ExteriorModule (degree a))
      (exteriorAction (degree a) (graphSL 5 witness)) ≠
    LinearMap.trace (ZMod 2) (ExteriorModule (degree a))
      (exteriorAction (degree a) witness) := by
  rw [trace_action, trace_action, graph_witness]
  fin_cases a <;> decide +kernel

/-- Both literal exterior representations are faithful. -/
public theorem exteriorAction_injective (a : Fin 2) :
    Function.Injective (exteriorAction (degree a)).asGroupHom := by
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) :=
    Atlas.psl_simple_high_rank 5 (by decide)
  let : IsSimpleGroup Group := projectiveEquiv.isSimpleGroup
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (exteriorAction (degree a)).asGroupHom.ker inferInstance with h | h
  · exact h
  · have hone (g : Group) : exteriorAction (degree a) g = LinearMap.id := by
      have hg : g ∈ (exteriorAction (degree a)).asGroupHom.ker := h ▸ Subgroup.mem_top g
      exact congrArg Units.val hg
    exact False.elim (trace_graph_ne a (by rw [hone, hone]))

/-- No linear change of basis implements inverse transpose on either exterior power. -/
public theorem graph_not_implemented (a : Fin 2)
    (x : (ExteriorModule (degree a) →ₗ[ZMod 2] ExteriorModule (degree a))ˣ)
    (h : ∀ g : Group, x * (exteriorAction (degree a)).asGroupHom g * x⁻¹ =
      (exteriorAction (degree a)).asGroupHom (graphSL 5 g)) : False := by
  have ht := LinearMap.trace_conj' (exteriorAction (degree a) witness)
    (LinearMap.GeneralLinearGroup.toLinearEquiv x)
  apply trace_graph_ne a
  rw [← ht]
  congr 1
  exact (congrArg Units.val (h witness)).symm

end Representation.SL5TenDimensional.ExteriorNormalizer
