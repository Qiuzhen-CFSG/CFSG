module

public import Mathlib.RingTheory.Smooth.Basic

universe u

open scoped TensorProduct

namespace Theory.AlgebraicGroup.Bor1

/-- For a formally smooth augmented algebra, the augmentation cotangent
space is the fiber of its module of Kahler differentials. -/
@[expose] public noncomputable def augmentedCotangentKaehlerEquiv
    {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    (e : A →ₐ[k] k) (he : Function.Surjective e)
    [Algebra.FormallySmooth k A] :
    letI : Algebra A k := e.toRingHom.toAlgebra
    (RingHom.ker e).Cotangent ≃ₗ[k] k ⊗[A] Ω[A⁄k] := by
  letI : Algebra A k := e.toRingHom.toAlgebra
  haveI : IsScalarTower k A k :=
    IsScalarTower.of_algebraMap_eq fun x => (e.commutes x).symm
  let l := (KaehlerDifferential.kerCotangentToTensor k A k).restrictScalars k
  have hinj : Function.Injective l := by
    exact (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff he).mpr
      inferInstance
  have hsurj : Function.Surjective l := by
    intro z
    have hz : KaehlerDifferential.mapBaseChange k A k z = 0 :=
      Subsingleton.elim _ _
    obtain ⟨x, hx⟩ :=
      (KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange
        k A k he z).mp hz
    exact ⟨x, hx⟩
  exact LinearEquiv.ofBijective l ⟨hinj, hsurj⟩

end Theory.AlgebraicGroup.Bor1
