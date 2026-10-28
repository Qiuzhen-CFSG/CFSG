module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Theory.AlgebraicGroup.Bor1.PointDerivationCotangent

universe u

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k]
variable {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]

/-- Pullback on the cotangent spaces at the identity induced by an
algebraic-group morphism. -/
@[expose] public noncomputable def identityCotangentMorphismLinearMap
    (f : AlgebraicGroup.Morphism G Q) :
    (Q.pointPrime 1).asIdeal.Cotangent →ₗ[k]
      (G.pointPrime 1).asIdeal.Cotangent := by
  have hcomp : (Q.pointPrime 1).asIdeal ≤
      (G.pointPrime 1).asIdeal.comap f.toVariety.pullbackAlgHom := by
    have hpoint := f.toVariety.pointPrime_image (1 : Variety.Point G)
    rw [f.map_one] at hpoint
    intro a ha
    change f.toVariety.pullbackRingHom a ∈ (G.pointPrime 1).asIdeal
    rw [← Ideal.mem_comap, ← PrimeSpectrum.comap_asIdeal, ← hpoint]
    exact ha
  exact Ideal.mapCotangent (Q.pointPrime 1).asIdeal
    (G.pointPrime 1).asIdeal f.toVariety.pullbackAlgHom hcomp

/-- The identity tangent map is dual to pullback on identity cotangent
spaces. -/
public theorem identityPointDerivationEquivCotangentDual_naturality
    (f : AlgebraicGroup.Morphism G Q) (D : IdentityPointDerivation G) :
    identityPointDerivationEquivCotangentDual Q
        (identityTangentMorphismLinearMap f D) =
      (identityPointDerivationEquivCotangentDual G D).comp
        (identityCotangentMorphismLinearMap f) := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := (Q.pointPrime 1).asIdeal.toCotangent_surjective z
  rfl

/-- A surjective identity differential induces an injective pullback on the
identity cotangent spaces. -/
public theorem identityCotangentMorphismLinearMap_injective_of_tangent_surjective
    (f : AlgebraicGroup.Morphism G Q)
    (hdf : Function.Surjective (identityTangentMorphismLinearMap f)) :
    Function.Injective (identityCotangentMorphismLinearMap f) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm
  intro z hz
  rw [Submodule.mem_bot]
  apply (Module.forall_dual_apply_eq_zero_iff k z).mp
  intro l
  let DQ := (identityPointDerivationEquivCotangentDual Q).symm l
  obtain ⟨DG, hDG⟩ := hdf DQ
  have hnat := identityPointDerivationEquivCotangentDual_naturality f DG
  rw [hDG, LinearEquiv.apply_symm_apply] at hnat
  rw [hnat, LinearMap.comp_apply, hz, map_zero]
  exact bot_le

end Theory.AlgebraicGroup.Bor1
