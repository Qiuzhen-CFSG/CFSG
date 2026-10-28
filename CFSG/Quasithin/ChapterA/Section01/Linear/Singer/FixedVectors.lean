module

public import CFSG.Quasithin.ChapterA.Section01.Linear.Singer.Defs
public import Theory.Representation.PrimeFixedPointCentralization.Subgroup
public import Theory.Representation.PrimeFixedPointCentralization.Branches
public import Theory.Representation.PrimeFixedPointCentralization.FixedVectors

/-!
# The faithful-action adapter for A.1.12's fixed-vector input

Oddness makes every normal two-subgroup trivial and makes each prime-order
actor odd. For the remaining distinct odd primes, the actual inclusion of Y
in the linear automorphism group is faithful. The semidirect-product fixed
vector theorem then implies relative centralization inside Y.

The first adapter retains its explicit representation-theoretic premise.
The final theorem discharges it with the assembled minimal-action structure,
abelian and extraspecial calculations, and faithful irreducible reduction,
obtaining `PrimeFixedPointCentralization Y` from oddness alone.

Source: Aschbacher–Smith A.1.12, printed p.22, invoking Aschbacher,
*Finite Group Theory*, second edition, 36.2, printed p.194.
-/

universe u
namespace CFSG.Quasithin.ChapterA.Singer

open Representation.PrimeFixedPointCentralization

/-- Assemble relative centralization from the full prime-action fixed-vector
input. Faithfulness is derived from the actual linear subgroup, and the
normal two-subgroup case is discharged using oddness. -/
public theorem primeFixedPointCentralization_of_prime_action_fixed_vectors
    {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (Y : Subgroup (V ≃ₗ[ZMod 2] V)) (hodd : Odd (Nat.card Y))
    (hfixed : ∀ q r : ℕ, q.Prime → Odd q → r.Prime → Odd r → q ≠ r →
      PrimeActionFixedVectorStatement.{u} q r) :
    PrimeFixedPointCentralization Y := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun g : V ≃ₗ[ZMod 2] V => (g : V → V)) DFunLike.coe_injective
  intro q r hq hr hqr N hnorm hN x hx hfree a
  let : Fact q.Prime := ⟨hq⟩
  let : Fact r.Prime := ⟨hr⟩
  let : N.Normal := hnorm
  by_cases hq2 : q = 2
  · have hNodd := hodd.of_dvd_nat N.card_subgroup_dvd_card
    have hcard : Nat.card N = 1 := hN.card_eq_or_dvd.resolve_right (by
      simpa only [hq2] using hNodd.not_two_dvd_nat)
    have hbot : N = ⊥ := (Subgroup.eq_bot_iff_card (H := N)).mpr hcard
    have ha : (a : Y) = 1 := by simpa [hbot] using a.property
    simp [ha]
  · have hrodd : Odd r := hodd.of_dvd_nat (hx ▸ orderOf_dvd_natCard x)
    let ρ : Representation (ZMod 2) Y V :=
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom
        (R := ZMod 2) (M := V)).comp Y.subtype
    have hfaith : Function.Injective ρ := by
      intro y z heq
      apply Subtype.ext
      apply LinearEquiv.toLinearMap_injective
      exact heq
    exact commute_of_prime_action_fixed_vectors hqr
      (hfixed q r hq (hq.odd_of_ne_two hq2) hr hrodd hqr)
      ρ hfaith N hN x hx hfree a

/-- In an odd-order binary linear group, a prime-order element fixing only
zero centralizes every normal subgroup of a distinct prime-power order. -/
public theorem primeFixedPointCentralization_of_odd
    {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (Y : Subgroup (V ≃ₗ[ZMod 2] V)) (hodd : Odd (Nat.card Y)) :
    PrimeFixedPointCentralization Y := by
  apply primeFixedPointCentralization_of_prime_action_fixed_vectors Y hodd
  intro q r hq hqodd hr hrodd hqr
  let : Fact q.Prime := ⟨hq⟩
  let : Fact r.Prime := ⟨hr⟩
  exact prime_action_fixed_vectors hqodd hrodd hqr

end CFSG.Quasithin.ChapterA.Singer
