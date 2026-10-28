module
public import Theory.Representation.SL3FourNaturalDual.QuadraticActors

/-!
# The rank bound supplied by natural-plus-dual coordinates

A quadratic subgroup of SL₃(4) is carried to a root plane. Its binary
parameter subspace lies in F₄², so its rank is at most four. The faithful
normalizer reduction places every elementary quadratic actor of ratio at
most two in the component. Combining these facts removes the separate
rank bound from the existing critical-shape classification.

Source: Aschbacher–Smith, 13.8.20, printed p.955.
-/

public section
open Subgroup Representation

namespace Representation.SL3FourNaturalDual.QuadraticActors
open BinaryOffender LinearClassification

/-- The root-plane parameter space bounds every internal quadratic actor by four. -/
theorem quadratic_rank_le_four (A : Subgroup SL) (hA : A ≠ ⊥)
    (hq : IsQuadratic representation A) : rank A ≤ 4 := by
  obtain ⟨f,_,D,_,hD⟩ := exists_rootPlane_coordinates A hA hq
  have hr : rank A = Module.finrank (ZMod 2) D := by
    rw [←rank_map_injective f.toMonoidHom f.injective A,hD,planeActor_rank]
  rw [hr]
  simpa only [Module.finrank_prod,finrank_field] using D.finrank_le

/-- The rank-four bound follows from the faithful natural-plus-dual action;
no independent rank premise is needed for the critical-shape classification. -/
theorem criticalShapes_of_equivariant_unbounded
    {J U : Type*} [Group J] [Finite J] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) J U) (hρ : Function.Injective ρ)
    (K : Subgroup J) [K.Normal] (eK : K ≃* SL) (E : U ≃ₗ[ZMod 2] V)
    (hE : ∀ (k : K) u, E (ρ k u) = representation (eK k) (E u))
    (A : Subgroup J) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hsmall : fixedCodim ρ A ≤ 2 * rank A) : CriticalShapes ρ A := by
  have hAK := NormalizerReduction.actor_le_of_equivariant ρ hρ K eK E hE A hA hq hsmall
  apply criticalShapes_of_equivariant ρ hρ K eK E hE A hA hq hsmall
  rw [←modelActor_rank K eK A hAK]
  exact quadratic_rank_le_four _ (modelActor_elementary K eK A hAK hA).1
    (modelActor_quadratic ρ K eK E hE A hq)
end Representation.SL3FourNaturalDual.QuadraticActors
