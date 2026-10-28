module

public import Theory.Representation.BinaryNormalizerRank
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Fixed codimension of an actor inverting an odd-order element

The commutator of `t` with an element `x` that it inverts is `x⁻²`.
For odd-order `x` this generates the same cyclic subgroup as `x`.
Subadditivity and conjugacy invariance of displacement therefore give
`codim C_V(x) ≤ 2 * codim C_V(t)`, over any field.

This is the linear step in Guralnick--Malle, *Classification of 2F-modules,
II*, Lemma 8.8, internal p.57. The application to the literal exceptional
Ree factors is in the parent module; involution coverage and the odd-element
calculations are separate mathematical inputs there.
-/

public section

namespace ReeF4.FixedSpaceEstimate.BasicInvolutions

open Representation Subgroup

variable {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]

/-- The generator, rather than a choice of cyclic-group coordinates, determines
the invariant subspace. -/
theorem cyclic_invariants_eq_ker (ρ : Representation F G V) (x : G) :
    invariants (ρ.comp (zpowers x).subtype) = LinearMap.ker (ρ x - 1) := by
  ext v
  rw [Representation.mem_invariants_iff_of_forall_mem_zpowers
    (ρ.comp (zpowers x).subtype) ⟨x, mem_zpowers x⟩ (by
      intro y
      obtain ⟨n, hn⟩ := mem_zpowers_iff.mp y.property
      exact mem_zpowers_iff.mpr ⟨n, Subtype.ext hn⟩)]
  exact sub_eq_zero.symm

/-- The literal quotient by cyclic invariants has the displacement rank. -/
theorem cyclic_fixedCodim_eq_rank (ρ : Representation F G V) (x : G) :
    Module.finrank F (V ⧸ invariants (ρ.comp (zpowers x).subtype)) =
      Module.finrank F (LinearMap.range (ρ x - 1)) := by
  rw [cyclic_invariants_eq_ker]
  exact (ρ x - 1).quotKerEquivRange.finrank_eq

/-- Conjugation preserves the codimension of the literal cyclic fixed space. -/
theorem cyclic_fixedCodim_conj (ρ : Representation F G V) (c x : G) :
    Module.finrank F (V ⧸ invariants (ρ.comp (zpowers (c * x * c⁻¹)).subtype)) =
      Module.finrank F (V ⧸ invariants (ρ.comp (zpowers x).subtype)) := by
  let τ : G →* (V ≃ₗ[F] V) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F V).toMonoidHom.comp ρ.asGroupHom
  rw [cyclic_fixedCodim_eq_rank, cyclic_fixedCodim_eq_rank]
  change Module.finrank F (LinearMap.range
    (Representation.BinaryNormalizerRank.displacement (τ (c * x * c⁻¹)))) =
      Module.finrank F (LinearMap.range
        (Representation.BinaryNormalizerRank.displacement (τ x)))
  rw [map_mul, map_mul, map_inv, Representation.BinaryNormalizerRank.rank_conj]

variable [FiniteDimensional F V]

/-- The displacement of a commutator is at most twice that of its first entry. -/
theorem cyclic_fixedCodim_commutator_le (ρ : Representation F G V) (t x : G) :
    Module.finrank F (V ⧸ invariants (ρ.comp (zpowers (t * x * t⁻¹ * x⁻¹)).subtype)) ≤
      2 * Module.finrank F (V ⧸ invariants (ρ.comp (zpowers t).subtype)) := by
  let τ : G →* (V ≃ₗ[F] V) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F V).toMonoidHom.comp ρ.asGroupHom
  have hr := Representation.BinaryNormalizerRank.rank_mul_le
    (τ t) (τ x * (τ t)⁻¹ * (τ x)⁻¹)
  rw [Representation.BinaryNormalizerRank.rank_conj,
    Representation.BinaryNormalizerRank.rank_inv] at hr
  rw [cyclic_fixedCodim_eq_rank, cyclic_fixedCodim_eq_rank]
  change Module.finrank F (LinearMap.range
    (Representation.BinaryNormalizerRank.displacement (τ (t * x * t⁻¹ * x⁻¹)))) ≤
      2 * Module.finrank F (LinearMap.range
        (Representation.BinaryNormalizerRank.displacement (τ t)))
  have he : τ t * (τ x * (τ t)⁻¹ * (τ x)⁻¹) = τ (t * x * t⁻¹ * x⁻¹) := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    group
  rw [he] at hr
  simpa only [two_mul] using hr

/-- Inverting an odd-order element costs at least half its displacement.
No involution or characteristic assumption is needed for this inequality. -/
theorem cyclic_fixedCodim_le_twice_of_inverts (ρ : Representation F G V)
    (t x : G) (hodd : Odd (orderOf x)) (hinv : t * x * t⁻¹ = x⁻¹) :
    Module.finrank F (V ⧸ invariants (ρ.comp (zpowers x).subtype)) ≤
      2 * Module.finrank F (V ⧸ invariants (ρ.comp (zpowers t).subtype)) := by
  have hsquare : zpowers (x ^ 2) = zpowers x := by
    apply le_antisymm
    · exact zpowers_le.mpr (pow_mem (mem_zpowers x) 2)
    · exact zpowers_le.mpr (mem_zpowers_pow_iff.mpr hodd.coprime_two_left)
  have he : zpowers (t * x * t⁻¹ * x⁻¹) = zpowers x := by
    rw [hinv, ← pow_two, inv_pow, zpowers_inv, hsquare]
  have h := cyclic_fixedCodim_commutator_le ρ t x
  rw [he] at h
  exact h

end ReeF4.FixedSpaceEstimate.BasicInvolutions
