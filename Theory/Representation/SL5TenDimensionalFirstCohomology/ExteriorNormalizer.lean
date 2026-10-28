module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.ExteriorNormalizer.Commutant
public import Theory.Representation.SL5TenDimensionalFirstCohomology.ExteriorNormalizer.Graph
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic
import Mathlib.Tactic.Group

/-!
# Self-normalizing exterior images of SL₅(2)

The literal exterior-square and exterior-cube images in GL₁₀(2) are
self-normalizing. A normalizing unit induces an automorphism of SL₅(2), since
both actions are faithful. The actual binary linear-group automorphism theorem
makes this automorphism inner or inverse transpose times inner. The graph case
is excluded by a trace witness; in the inner case the remaining factor belongs
to the trivial centralizer of the exterior image.

This supplies the exterior-image normalizer input for the whole-group
conclusion in Aschbacher--Smith, G.9.3(13), printed pp.354, 356--357.
It uses neither an exhaustion of irreducible representations nor cohomology.
-/

namespace Representation.SL5TenDimensional.ExteriorNormalizer
open BinaryLinear.OuterCyclic

private theorem inner_graph_sl (a : MulAut Group) :
    ∃ g : Group, a = MulAut.conj g ∨ a = graphSL 5 * MulAut.conj g := by
  obtain ⟨g, hg⟩ := inner_graph (Or.inr rfl) (MulAut.congr (slEquivLinear 5) a)
  refine ⟨(slEquivLinear 5).symm g, ?_⟩
  rcases hg with hg | hg
  · left
    apply (MulAut.congr (slEquivLinear 5)).injective
    simpa only [MulAut.congr_conj, MulEquiv.apply_symm_apply] using hg
  · right
    apply (MulAut.congr (slEquivLinear 5)).injective
    simpa only [map_mul, MulAut.congr_conj, MulEquiv.apply_symm_apply, graphLinear] using hg

private theorem normalizer_eq_of_rigidity {U : Type*} [_root_.Group U]
    (f : Group →* U) (hf : Function.Injective f)
    (hcentral : ∀ x : U, (∀ g, x * f g * x⁻¹ = f g) → x = 1)
    (hgraph : ∀ x : U, (∀ g, x * f g * x⁻¹ = f (graphSL 5 g)) → False) :
    Subgroup.normalizer (f.range : Set U) = f.range := by
  apply le_antisymm ?_ f.range.le_normalizer
  intro x hx
  let e := MonoidHom.ofInjective hf
  let a : MulAut Group := MulAut.congr e.symm (f.range.normalizerMonoidHom ⟨x, hx⟩)
  have ha (g : Group) : f (a g) = x * f g * x⁻¹ := by
    change f (e.symm (f.range.normalizerMonoidHom ⟨x, hx⟩ (e g))) = _
    rw [MonoidHom.apply_ofInjective_symm]
    rfl
  obtain ⟨g, hg⟩ := inner_graph_sl a
  have hconj (k : Group) :
      (x * (f g)⁻¹) * f k * (x * (f g)⁻¹)⁻¹ = f (a (g⁻¹ * k * g)) := by
    rw [ha]
    simp only [map_mul, map_inv]
    group
  rcases hg with hg | hg
  · have hc : x * (f g)⁻¹ = 1 := hcentral _ (fun k => by
      rw [hconj, hg]
      simp [MulAut.conj_apply, mul_assoc])
    exact ⟨g, (mul_inv_eq_one.mp hc).symm⟩
  · exact False.elim (hgraph _ (fun k => by
      rw [hconj, hg]
      simp [MulAut.mul_apply, MulAut.conj_apply, mul_assoc]))

private theorem normalizer_degree (a : Fin 2) :
    Subgroup.normalizer ((exteriorAction (degree a)).asGroupHom.range :
      Set (ExteriorModule (degree a) →ₗ[ZMod 2] ExteriorModule (degree a))ˣ) =
      (exteriorAction (degree a)).asGroupHom.range :=
  normalizer_eq_of_rigidity _ (exteriorAction_injective a)
    (centralizing_unit_eq_one a) (graph_not_implemented a)

/-- The second and third exterior images of SL₅(2) are self-normalizing. -/
public theorem normalizer_eq_self (r : ℕ) (hr : r = 2 ∨ r = 3) :
    Subgroup.normalizer ((exteriorAction r).asGroupHom.range :
      Set (ExteriorModule r →ₗ[ZMod 2] ExteriorModule r)ˣ) =
      (exteriorAction r).asGroupHom.range := by
  rcases hr with rfl | rfl
  · exact normalizer_degree 0
  · exact normalizer_degree 1

/-- The literal exterior-square image is self-normalizing in GL₁₀(2). -/
public theorem normalizer_two :
    Subgroup.normalizer ((exteriorAction 2).asGroupHom.range :
      Set (ExteriorModule 2 →ₗ[ZMod 2] ExteriorModule 2)ˣ) =
      (exteriorAction 2).asGroupHom.range :=
  normalizer_eq_self 2 (Or.inl rfl)

/-- The literal exterior-cube image is self-normalizing in GL₁₀(2). -/
public theorem normalizer_three :
    Subgroup.normalizer ((exteriorAction 3).asGroupHom.range :
      Set (ExteriorModule 3 →ₗ[ZMod 2] ExteriorModule 3)ˣ) =
      (exteriorAction 3).asGroupHom.range :=
  normalizer_eq_self 3 (Or.inr rfl)

end Representation.SL5TenDimensional.ExteriorNormalizer
