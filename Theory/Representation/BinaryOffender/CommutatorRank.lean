module

public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Theory.Representation.BinaryNormalizerRank
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Displacement of a commutator

Fixed codimension for a cyclic actor is the rank of its displacement operator.
Subadditivity of displacement, together with invariance under conjugacy and
inversion, bounds the displacement of [a,b] by twice that of a. Transposition
also identifies the displacement ranks of a representation and its dual.

This supplies the linear inequality used in the paired-module calculation of
Aschbacher–Smith 13.8.21(1), printed p.956, combined manuscript of 1 March 2004.
The inequality itself applies to every finite-dimensional binary representation.
-/

public section

open Representation
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The fixed space of a cyclic subgroup is the fixed space of its generator. -/
theorem mem_fixedSpace_zpowers_iff (ρ : Representation (ZMod 2) G V) (a : G) (v : V) :
    v ∈ fixedSpace ρ (Subgroup.zpowers a) ↔ ρ a v = v := by
  apply Representation.mem_invariants_iff_of_forall_mem_zpowers
    (ρ.comp (Subgroup.zpowers a).subtype) ⟨a, Subgroup.mem_zpowers a⟩
  intro x
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp x.property
  exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext hn⟩

variable [FiniteDimensional (ZMod 2) V]
/-- Rank-nullity identifies fixed codimension with the rank of the displacement. -/
theorem fixedCodim_zpowers_eq_displacement_rank
    (ρ : Representation (ZMod 2) G V) (a : G) :
    fixedCodim ρ (Subgroup.zpowers a) =
      Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) := by
  have hk : (ρ a - LinearMap.id).ker = fixedSpace ρ (Subgroup.zpowers a) := by
    ext v
    rw [mem_fixedSpace_zpowers_iff]
    exact sub_eq_zero
  have hn := (ρ a - LinearMap.id).finrank_range_add_finrank_ker
  have hc := fixedCodim_add_finrank ρ (Subgroup.zpowers a)
  rw [hk] at hn
  omega

/-- A commutator has displacement at most twice that of its first entry. -/
theorem fixedCodim_commutator_le_twice (ρ : Representation (ZMod 2) G V) (a b : G) :
    fixedCodim ρ (Subgroup.zpowers (a * b * a⁻¹ * b⁻¹)) ≤
      2 * fixedCodim ρ (Subgroup.zpowers a) := by
  let τ : G →* (V ≃ₗ[ZMod 2] V) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp ρ.asGroupHom
  have hr := BinaryNormalizerRank.rank_mul_le (τ a) (τ b * (τ a)⁻¹ * (τ b)⁻¹)
  rw [BinaryNormalizerRank.rank_conj, BinaryNormalizerRank.rank_inv] at hr
  rw [fixedCodim_zpowers_eq_displacement_rank, fixedCodim_zpowers_eq_displacement_rank]
  change Module.finrank (ZMod 2) (LinearMap.range
    (BinaryNormalizerRank.displacement (τ (a * b * a⁻¹ * b⁻¹)))) ≤
      2 * Module.finrank (ZMod 2) (LinearMap.range (BinaryNormalizerRank.displacement (τ a)))
  have he : τ a * (τ b * (τ a)⁻¹ * (τ b)⁻¹) = τ (a * b * a⁻¹ * b⁻¹) := by
    simp only [map_mul, map_inv, mul_assoc]
  rw [he] at hr
  simpa only [two_mul] using hr

omit [FiniteDimensional (ZMod 2) V] in
/-- A generator and its inverse have the same fixed codimension. -/
theorem fixedCodim_zpowers_inv (ρ : Representation (ZMod 2) G V) (a : G) :
    fixedCodim ρ (Subgroup.zpowers a⁻¹) = fixedCodim ρ (Subgroup.zpowers a) := by
  rw [Subgroup.zpowers_inv]

/-- Contragredience preserves the displacement of an individual actor. -/
theorem fixedCodim_zpowers_dual (ρ : Representation (ZMod 2) G V) (a : G) :
    fixedCodim ρ.dual (Subgroup.zpowers a) = fixedCodim ρ (Subgroup.zpowers a) := by
  rw [fixedCodim_zpowers_eq_displacement_rank]
  have he : ρ.dual a - LinearMap.id = (ρ a⁻¹ - LinearMap.id).dualMap := by
    ext f v
    change f (ρ a⁻¹ v) - f v = f (ρ a⁻¹ v - v)
    exact (map_sub f _ _).symm
  rw [he, LinearMap.finrank_range_dualMap_eq_finrank_range,
    ← fixedCodim_zpowers_eq_displacement_rank, fixedCodim_zpowers_inv]

/-- Conjugate actors have the same fixed codimension. -/
theorem fixedCodim_zpowers_conj (ρ : Representation (ZMod 2) G V) (a c : G) :
    fixedCodim ρ (Subgroup.zpowers (c * a * c⁻¹)) = fixedCodim ρ (Subgroup.zpowers a) := by
  have he := (MulAut.conj c).toMonoidHom.map_zpowers a
  change (Subgroup.zpowers a).map (MulAut.conj c).toMonoidHom =
    Subgroup.zpowers (c * a * c⁻¹) at he
  rw [← he, fixedCodim_map_conj]
end Representation.BinaryOffender
