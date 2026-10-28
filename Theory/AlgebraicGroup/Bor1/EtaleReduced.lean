module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Unramified.Field

universe u

namespace Theory.AlgebraicGroup.Bor1

open CategoryTheory CategoryTheory.Limits CommRingCat
open AlgebraicGeometry
open scoped TensorProduct

set_option linter.style.haveILetI false in
/-- The spectrum map of an etale algebra is geometrically reduced. -/
public theorem etaleSpecMap_geometricallyReduced
    {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.Etale R S] :
    GeometricallyReduced
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  rw [geometricallyReduced_iff,
    geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K _ _
  apply ObjectProperty.prop_of_iso (AlgebraicGeometry.IsReduced ·)
    (pullbackSpecIso R S K).symm
  rw [affine_isReduced_iff]
  have h : IsReduced (K ⊗[R] S) := by
    haveI : Algebra.Etale K (K ⊗[R] S) := inferInstance
    exact Algebra.FormallyUnramified.isReduced_of_field K _
  letI := h
  exact isReduced_of_injective (Algebra.TensorProduct.comm R S K)
    (Algebra.TensorProduct.comm R S K).injective

set_option linter.style.haveILetI false in
/-- An etale algebra over a reduced Noetherian ring is reduced. -/
public theorem isReduced_of_etale_of_isNoetherian
    {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.Etale R S] [IsNoetherianRing R] [IsReduced R] :
    IsReduced S := by
  let f : Spec (.of S) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R S))
  letI : GeometricallyReduced f := by
    exact etaleSpecMap_geometricallyReduced
  letI : Flat f := by
    rw [Flat.SpecMap_iff]
    exact (RingHom.Etale.iff_flat_and_formallyUnramified.mp
      (show (algebraMap R S).Etale from by
        simpa [RingHom.etale_algebraMap])).1
  have hsred : AlgebraicGeometry.IsReduced (Spec (.of S)) :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian f
  exact (affine_isReduced_iff (.of S)).mp hsred

end Theory.AlgebraicGroup.Bor1
