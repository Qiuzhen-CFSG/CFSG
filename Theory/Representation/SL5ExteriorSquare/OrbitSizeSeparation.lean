module
public import Theory.Representation.OrbitSizeSeparation
public import Theory.Representation.Quotient
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Orbits.VectorNormalForm
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Duality.Core
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification
public import Mathlib.FieldTheory.Finiteness

/-!
# Orbit separation in the binary rank-ten special linear modules

Every nonzero exterior-square vector is decomposable or nondecomposable.
These two orbits have different sizes because the vector space has even
cardinality. Hodge duality transports separation to the exterior cube,
and the existing irreducible-module classification covers every marked
rank-ten action.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the irreducible
case in 12.2.16, printed pp.799–800. The concrete exterior actions and their
classification are reused with their existing source attribution.
-/

public noncomputable section
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional

theorem square_orbitCardSeparates : OrbitCardSeparates (exteriorAction 2) := by
  let : Finite (ExteriorModule 2) := Finite.of_injective coordinates coordinates.injective
  apply OrbitCardSeparates.of_two_nonzero_orbits (exteriorAction 2) _
    decomposable nondecomposable decomposable_ne_zero nondecomposable_ne_zero
    exterior_orbits_exhaustive
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),
    finrank_exteriorModule_two,Nat.card_zmod]
  decide

theorem cube_orbitCardSeparates : OrbitCardSeparates (exteriorAction 3) :=
  square_orbitCardSeparates.of_intertwining Duality.graph.toMonoidHom
    Duality.graph.surjective Duality.hodge Duality.hodge_action

theorem irreducible_ten_orbitCardSeparates
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) Group W) [IsIrreducible ρ]
    (hd : Module.finrank (ZMod 2) W = 10) : OrbitCardSeparates ρ := by
  rcases Classification.identification_of_finrank_ten ρ hd with hs | hc
  · obtain ⟨e⟩ := hs
    exact square_orbitCardSeparates.of_intertwining (MonoidHom.id Group)
      Function.surjective_id e.toLinearEquiv
      (fun g w => LinearMap.congr_fun (e.isIntertwining' g) w)
  · obtain ⟨e⟩ := hc
    exact cube_orbitCardSeparates.of_intertwining (MonoidHom.id Group)
      Function.surjective_id e.toLinearEquiv
      (fun g w => LinearMap.congr_fun (e.isIntertwining' g) w)

theorem marked_irreducible_ten_orbitCardSeparates
    {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) (e : A ≃* Group)
    [IsIrreducible ρ] (hd : Module.finrank (ZMod 2) W = 10) :
    OrbitCardSeparates ρ := by
  let σ := ρ.comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr inferInstance
  apply (irreducible_ten_orbitCardSeparates σ hd).of_intertwining e.toMonoidHom e.surjective
    (LinearEquiv.refl _ _)
  intro g v
  change ρ g v = ρ (e.symm (e g)) v
  rw [e.symm_apply_apply]

end Representation.SL5ExteriorSquare
