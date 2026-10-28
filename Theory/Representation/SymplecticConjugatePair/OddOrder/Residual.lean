module

public import Theory.GroupTheory.PResidual.Defs
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Odd-prime actors in pointwise fixers

Cauchy's theorem detects an odd-prime actor whenever a finite group's
actual two-residual is nontrivial. Otherwise all prime divisors of the
order are two, so the group is a two-group and its two-residual is trivial.
A subspace fixed by that actor lies in its fixed space; rank-nullity then
transfers the actor's codimension bound to the subspace.

Source: the reduction implicit in the definition of β on printed p.377
and its use in H.7 on p.389, Aschbacher–Smith, 1 March 2004 manuscript.
-/

@[expose] public section

open Representation Representation.BinaryOffender
namespace SymplecticConjugatePair.OddOrder

/-- A nontrivial two-residual in a finite group forces an odd-prime-order element. -/
theorem exists_odd_prime_actor {G : Type*} [Group G] [Finite G]
    (h : pResidual 2 G ≠ ⊥) :
    ∃ (p : ℕ) (x : G), p.Prime ∧ Odd p ∧ orderOf x = p := by
  by_contra! hn
  have hp : IsPGroup 2 G := by
    apply IsPGroup.of_card_dvd_pow (n := Nat.card G)
    apply (Nat.dvd_pow_self_iff (Nat.card_pos.ne') (by decide : 2 ≠ 0)).mpr
    intro p hp
    obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
    by_cases he : p = 2
    · simp [he, Nat.prime_two]
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p (hp := ⟨hpp⟩) hpd
    exact False.elim (hn p x hpp (hpp.odd_of_ne_two he) hx)
  apply h
  apply le_antisymm _ bot_le
  exact sInf_le ⟨inferInstance, hp.of_surjective (QuotientGroup.mk' ⊥) (QuotientGroup.mk'_surjective ⊥)⟩

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The subgroup fixing every vector of the given binary subspace. -/
def pointwiseFixer (ρ : Representation (ZMod 2) G V)
    (U : Submodule (ZMod 2) V) : Subgroup G where
  carrier := {x | ∀ v ∈ U, ρ x v = v}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy v hv
    simp only [map_mul, Module.End.mul_apply, hy v hv, hx v hv]
  inv_mem' := by
    intro x hx v hv
    have he := congrArg (ρ x⁻¹) (hx v hv)
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using he.symm

/-- Odd-prime actor bounds imply the bound for every subspace whose pointwise
fixer has nontrivial two-residual. Properness is unnecessary for this implication. -/
theorem codim_bound_of_odd_prime_actors [Finite G] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (b : ℕ)
    (hb : ∀ (p : ℕ) (x : G), p.Prime → Odd p → orderOf x = p →
      b ≤ fixedCodim ρ (Subgroup.zpowers x))
    (U : Submodule (ZMod 2) V) (hU : pResidual 2 (pointwiseFixer ρ U) ≠ ⊥) :
    b ≤ Module.finrank (ZMod 2) (V ⧸ U) := by
  obtain ⟨p, x, hp, ho, hx⟩ := exists_odd_prime_actor hU
  have hx' : orderOf (x : G) = p := by rwa [Subgroup.orderOf_coe]
  have hle : U ≤ fixedSpace ρ (Subgroup.zpowers (x : G)) := by
    intro v hv
    rw [mem_fixedSpace_zpowers_iff]
    exact x.property v hv
  have hm := Submodule.finrank_mono hle
  have hq := U.finrank_quotient_add_finrank
  have hc := fixedCodim_add_finrank ρ (Subgroup.zpowers (x : G))
  have hb' := hb p x hp ho hx'
  omega

end SymplecticConjugatePair.OddOrder
