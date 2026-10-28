module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Duality.Core
public import Theory.Representation.Quotient

/-!
# Marked coordinates for ten-dimensional binary SL₅ modules

The dimension-only irreducible classification gives the exterior square or
cube for the prescribed actor marking. Complementary wedges identify the
cube with the square after inverse transpose. Thus the resulting square
coordinates use either the original marking or its specified graph twist.
No arbitrary replacement of the actor is made.

Source: Aschbacher--Smith I.1.6(7), printed p.408, as used in 15.1.28,
printed p.1103.
-/

public section
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional

/-- Recognition with the original actor marking retained up to inverse transpose. -/
theorem square_coordinates_of_finrank_ten
    {H W : Type*} [_root_.Group H] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) [IsIrreducible ρ]
    (mark : H ≃* Group) (hdim : Module.finrank (ZMod 2) W = 10) :
    ∃ (actor : H ≃* Group) (coordinates : W ≃ₗ[ZMod 2] ExteriorModule 2),
      (actor = mark ∨ actor = mark.trans Duality.graph) ∧
      ∀ g v, coordinates (ρ g v) = exteriorAction 2 (actor g) (coordinates v) := by
  let σ := ρ.comp mark.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff mark.symm.toMonoidHom mark.symm.surjective ρ).mpr
      inferInstance
  rcases Classification.identification_of_finrank_ten σ hdim with hs | hc
  · obtain ⟨e⟩ := hs
    refine ⟨mark, e.toLinearEquiv, Or.inl rfl, ?_⟩
    intro g v
    have h := LinearMap.congr_fun (e.isIntertwining' (mark g)) v
    change e (ρ (mark.symm (mark g)) v) = exteriorAction 2 (mark g) (e v) at h
    simpa only [mark.symm_apply_apply, Representation.Equiv.toLinearEquiv_apply,
      Representation.Equiv.coe_toIntertwiningMap] using h
  · obtain ⟨e⟩ := hc
    refine ⟨mark.trans Duality.graph, e.toLinearEquiv.trans Duality.hodge,
      Or.inr rfl, ?_⟩
    intro g v
    have h := LinearMap.congr_fun (e.isIntertwining' (mark g)) v
    have he : e (ρ g v) = exteriorAction 3 (mark g) (e v) := by
      change e (ρ (mark.symm (mark g)) v) = exteriorAction 3 (mark g) (e v) at h
      simpa only [mark.symm_apply_apply] using h
    change Duality.hodge (e (ρ g v)) =
      exteriorAction 2 (Duality.graph (mark g)) (Duality.hodge (e v))
    rw [he, Duality.hodge_action]

end Representation.SL5ExteriorSquare
