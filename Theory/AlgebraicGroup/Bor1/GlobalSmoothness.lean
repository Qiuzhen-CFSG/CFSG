module

public import Theory.AlgebraicGroup.Bor1.SmoothAtTranslation

universe u

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]

set_option linter.style.haveILetI false in
/-- A morphism of algebraic groups whose identity differential is surjective
is smooth. -/
public theorem pullbackRingHom_smooth_of_tangent_surjective
    (f : AlgebraicGroup.Morphism G Q)
    (hdf : Function.Surjective (identityTangentMorphismLinearMap f)) :
    f.toVariety.pullbackRingHom.Smooth := by
  let A := Variety.PolynomialFunction Q
  let B := Variety.PolynomialFunction G
  let F := f.toVariety.pullbackRingHom
  letI : Algebra A B := F.toAlgebra
  have hfp : F.FinitePresentation :=
    f.toVariety.pullbackRingHom_finitePresentation
  letI : Algebra.FinitePresentation A B := hfp
  rw [RingHom.smooth_def]
  constructor
  · change Algebra.FormallySmooth A B
    rw [← Algebra.smoothLocus_eq_univ_iff]
    apply Set.eq_univ_of_forall
    intro p
    obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p.asIdeal p.2.ne_top
    obtain ⟨x, hx⟩ := G.exists_pointPrime_eq_of_isMaximal m hm
    have hxSmooth : G.pointPrime x ∈ Algebra.smoothLocus A B :=
      point_isSmoothAt_of_tangent_surjective f hdf x
    have hpmx : p ≤ G.pointPrime x := by
      rw [← PrimeSpectrum.asIdeal_le_asIdeal, hx]
      exact hpm
    have hspec : p ⤳ G.pointPrime x :=
      (PrimeSpectrum.le_iff_specializes p (G.pointPrime x)).mp hpmx
    exact hspec.mem_open Algebra.isOpen_smoothLocus hxSmooth
  · exact f.toVariety.pullbackRingHom_finitePresentation

end Theory.AlgebraicGroup.Bor1
