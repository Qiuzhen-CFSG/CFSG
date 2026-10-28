module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Smooth.Flat
public import Theory.AlgebraicGroup.Bor1.GlobalSmoothness

universe u

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]

/-- A point-surjective morphism of algebraic groups with surjective identity
differential induces a faithfully flat pullback on coordinate rings. -/
public theorem pullbackRingHom_faithfullyFlat_of_surjective_of_tangent_surjective
    (f : AlgebraicGroup.Morphism G Q)
    (hsurj : Function.Surjective f.onPoints)
    (hdf : Function.Surjective (identityTangentMorphismLinearMap f)) :
    f.toVariety.pullbackRingHom.FaithfullyFlat := by
  let F := f.toVariety.pullbackRingHom
  have hsmooth : F.Smooth :=
    pullbackRingHom_smooth_of_tangent_surjective f hdf
  have hflat : F.Flat := hsmooth.flat
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
  refine ⟨hflat, ?_⟩
  intro p
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p.asIdeal p.2.ne_top
  obtain ⟨y, hy⟩ := Q.exists_pointPrime_eq_of_isMaximal m hm
  obtain ⟨x, hx⟩ := hsurj y
  let P := G.pointPrime x
  have hcomap : PrimeSpectrum.comap F P = Q.pointPrime y := by
    calc
      PrimeSpectrum.comap F P = Q.pointPrime (f.onPoints x) :=
        (f.toVariety.pointPrime_image x).symm
      _ = Q.pointPrime y := congrArg (Q.pointPrime ·) hx
  have hpmy : p ≤ Q.pointPrime y := by
    rw [← PrimeSpectrum.asIdeal_le_asIdeal, hy]
    exact hpm
  have hspec : p ⤳ PrimeSpectrum.comap F P := by
    rw [hcomap]
    exact (PrimeSpectrum.le_iff_specializes p (Q.pointPrime y)).mp hpmy
  obtain ⟨P', -, hP'⟩ := hflat.generalizingMap_comap hspec
  exact ⟨P', hP'⟩

end Theory.AlgebraicGroup.Bor1
