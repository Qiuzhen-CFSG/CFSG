module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.Quotient.B4Extraction.SplitModels.Models
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.Quotient.B4Extraction.IndexTwo
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.RadicalOrientation.Duality
public import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# Graph twists exchange the marked constituents

For two summands exchanged by a swapper, its inverse identifies the right
summand with the left action twisted by conjugation with the inverse swapper.
An explicit graph-times-inner identity for that conjugation then exchanges
the natural and contragredient models, with the same specified GL₄(2) marking.
We remove the inner conjugation and use the coordinate dot-product equivalence;
the reverse orientation also uses that inverse transpose has square one.

This is the constituent transport used in the split branch of Aschbacher–Smith
13.8.25, printed pp.959–960, after the B.4.2(9–10) and B.4.5 alternatives on
pp.86–87 (combined manuscript of 1 March 2004). The graph-action identity and
the classification of the left constituent remain explicit premises here.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalQuotient.B4Extraction.SplitModels
open Representation FourStructure.ChiefFactors BinaryLinear.OuterCyclic
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  {ρ : Representation (ZMod 2) H U} {K : Subgroup H}

private theorem inverse_mem (d : RestrictionSplit ρ K) (v : d.right.toSubmodule) :
    ρ d.swapper⁻¹ v ∈ d.left.toSubmodule := by
  have hv : (v : U) ∈ d.left.toSubmodule.map (ρ d.swapper) := by
    rw [d.map_left]
    exact v.property
  obtain ⟨w, hw, he⟩ := hv
  rw [← he]
  simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply]
  exact hw

private noncomputable def inverseSwapper (d : RestrictionSplit ρ K) :
    d.right.toSubmodule ≃ₗ[ZMod 2] d.left.toSubmodule where
  toFun v := ⟨ρ d.swapper⁻¹ v, inverse_mem d v⟩
  invFun v := ⟨ρ d.swapper v, d.apply_swapper_mem_right v⟩
  left_inv v := by
    apply Subtype.ext
    simp [← Module.End.mul_apply, ← map_mul]
  right_inv v := by
    apply Subtype.ext
    simp [← Module.End.mul_apply, ← map_mul]
  map_add' v w := by apply Subtype.ext; exact map_add _ _ _
  map_smul' a v := by apply Subtype.ext; exact map_smul _ _ _

variable [K.Normal]

private theorem inverseSwapper_intertwines (d : RestrictionSplit ρ K)
    (k : K) (v : d.right.toSubmodule) :
    inverseSwapper d (d.right.toRepresentation k v) =
      d.left.toRepresentation ((MulAut.conjNormal : H →* MulAut K) d.swapper⁻¹ k)
        (inverseSwapper d v) := by
  apply Subtype.ext
  change ρ d.swapper⁻¹ (ρ (k : H) v) =
    ρ (((MulAut.conjNormal : H →* MulAut K) d.swapper⁻¹ k) : H)
      (ρ d.swapper⁻¹ v)
  rw [MulAut.conjNormal_apply]
  simp only [← Module.End.mul_apply, ← map_mul, inv_inv, mul_assoc, mul_inv_cancel,
    mul_one]

private theorem marked_conjugation (d : RestrictionSplit ρ K)
    (eK : K ≃* BinaryLinear.GL FourSpace) (g : BinaryLinear.GL FourSpace)
    (hgraph : MulAut.congr eK ((MulAut.conjNormal : H →* MulAut K) d.swapper⁻¹) =
      graphLinear 4 * MulAut.conj g) (k : K) :
    eK ((MulAut.conjNormal : H →* MulAut K) d.swapper⁻¹ k) =
      graphLinear 4 (g * eK k * g⁻¹) := by
  have h := congrArg (fun a : MulAut (BinaryLinear.GL FourSpace) => a (eK k)) hgraph
  simpa [MulAut.congr_apply, MulAut.conj_apply] using h

private theorem pairing_graph (k : BinaryLinear.GL FourSpace) (v : FourSpace) :
    dotProductEquiv (ZMod 2) (Fin 4) (graphLinear 4 k v) =
      (dotProductEquiv (ZMod 2) (Fin 4) v).comp k.symm.toLinearMap := by
  apply LinearMap.ext
  intro x
  change dotProduct (graphLinear 4 k v) x = dotProduct v (k.symm x)
  simpa only [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] using
    graphLinear_dotProduct k v (k⁻¹ x)

private theorem graph_graph (k : BinaryLinear.GL FourSpace) :
    graphLinear 4 (graphLinear 4 k) = k := by
  have h := congrArg (fun a : MulAut (BinaryLinear.GL FourSpace) => a k)
    (graphLinear_sq 4)
  simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using h

private theorem pairing_symm_graph (k : BinaryLinear.GL FourSpace)
    (f : Module.Dual (ZMod 2) FourSpace) :
    (dotProductEquiv (ZMod 2) (Fin 4)).symm
      (f.comp (graphLinear 4 k).symm.toLinearMap) =
        k ((dotProductEquiv (ZMod 2) (Fin 4)).symm f) := by
  obtain ⟨v, rfl⟩ := (dotProductEquiv (ZMod 2) (Fin 4)).surjective f
  rw [← pairing_graph, graph_graph]
  simp only [LinearEquiv.symm_apply_apply]

/-- A natural left constituent becomes contragredient on the right under the
specified graph action, without changing the actor marking. -/
theorem dual_right_of_natural_left (d : RestrictionSplit ρ K)
    (eK : K ≃* BinaryLinear.GL FourSpace) (g : BinaryLinear.GL FourSpace)
    (hgraph : MulAut.congr eK ((MulAut.conjNormal : H →* MulAut K) d.swapper⁻¹) =
      graphLinear 4 * MulAut.conj g)
    (hL : IsNatural d.left.toRepresentation eK) : IsDual d.right.toRepresentation eK := by
  obtain ⟨eL, hL⟩ := hL
  let e := ((inverseSwapper d).trans eL).trans
    ((graphLinear 4 g).symm.trans (dotProductEquiv (ZMod 2) (Fin 4)))
  refine ⟨e, fun k v => ?_⟩
  simp only [e, LinearEquiv.trans_apply]
  rw [inverseSwapper_intertwines, hL, marked_conjugation d eK g hgraph]
  simp only [map_mul, map_inv, LinearEquiv.mul_apply, LinearEquiv.coe_inv,
    LinearEquiv.symm_apply_apply]
  rw [pairing_graph]
  change _ = (dotProductEquiv (ZMod 2) (Fin 4)
    ((graphLinear 4 g).symm (eL (inverseSwapper d v)))).comp (eK k⁻¹).toLinearMap
  rw [map_inv]
  rfl

/-- A contragredient left constituent becomes natural on the right under the
same graph action and actor marking. -/
theorem natural_right_of_dual_left (d : RestrictionSplit ρ K)
    (eK : K ≃* BinaryLinear.GL FourSpace) (g : BinaryLinear.GL FourSpace)
    (hgraph : MulAut.congr eK ((MulAut.conjNormal : H →* MulAut K) d.swapper⁻¹) =
      graphLinear 4 * MulAut.conj g)
    (hL : IsDual d.left.toRepresentation eK) : IsNatural d.right.toRepresentation eK := by
  obtain ⟨eL, hL⟩ := hL
  let e := ((inverseSwapper d).trans eL).trans
    ((dotProductEquiv (ZMod 2) (Fin 4)).symm.trans g.symm)
  refine ⟨e, fun k v => ?_⟩
  simp only [e, LinearEquiv.trans_apply]
  rw [inverseSwapper_intertwines, hL]
  change g.symm ((dotProductEquiv (ZMod 2) (Fin 4)).symm
    ((eL (inverseSwapper d v)).comp
      (eK ((MulAut.conjNormal : H →* MulAut K) d.swapper⁻¹ k)⁻¹).toLinearMap)) = _
  rw [map_inv, marked_conjugation d eK g hgraph]
  change g.symm ((dotProductEquiv (ZMod 2) (Fin 4)).symm
    ((eL (inverseSwapper d v)).comp
      (graphLinear 4 (g * eK k * g⁻¹)).symm.toLinearMap)) = _
  rw [pairing_symm_graph]
  simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]

/-- The two exchanged constituents have opposite marked models, conditional
on the explicit graph-action identity and the model of the left constituent. -/
theorem oppositeModels_of_graph (d : RestrictionSplit ρ K)
    (eK : K ≃* BinaryLinear.GL FourSpace) (g : BinaryLinear.GL FourSpace)
    (hgraph : MulAut.congr eK ((MulAut.conjNormal : H →* MulAut K) d.swapper⁻¹) =
      graphLinear 4 * MulAut.conj g)
    (hL : IsNaturalOrDual d.left.toRepresentation eK) : OppositeModels d eK := by
  rcases hL with hL | hL
  · exact Or.inl ⟨hL, dual_right_of_natural_left d eK g hgraph hL⟩
  · exact Or.inr ⟨hL, natural_right_of_dual_left d eK g hgraph hL⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalQuotient.B4Extraction.SplitModels
