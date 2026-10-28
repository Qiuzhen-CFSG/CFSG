module

public import Theory.SpecificGroups.Janko1.Model
public import Theory.GroupTheory.PerfectCentralCoverOddPart
public import Theory.GroupTheory.PerfectCentralCoverCentralQuotient

/-!
# Odd central-cover exclusion for the actual J₁ model

The certified J₁ order has squarefree odd part. Its odd Sylow subgroups
are therefore cyclic, so transfer excludes every odd prime from a perfect
central kernel. A trivial two-core excludes the remaining prime. The source
corollary retains the literal projection from the central quotient.

Source: Aschbacher–Smith I.1.2 and A.2.19, printed pp.407 and 40–41.
-/

namespace Janko1.OddCover
open Subgroup PerfectCentralCovering

private theorem square_not_dvd (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ^ 2 ∣ Nat.card Model := by
  rw [card_model]
  intro hd
  have hpd : p ∣ 175560 := (show p ∣ p ^ 2 by
    simpa only [pow_one] using pow_dvd_pow p (by decide : 1 ≤ 2)).trans hd
  change p ∣ 2 * 2 * 2 * 3 * 5 * 7 * 11 * 19 at hpd
  simp only [hp.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hp Nat.prime_two,
    Nat.prime_dvd_prime_iff_eq hp Nat.prime_three,
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 11),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 19)] at hpd
  have h : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 19 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl <;> norm_num at hd

/-- The original central projection is injective when the two-core is trivial. -/
public theorem projection_injective {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]
    (hcore : pCore 2 L = ⊥) (e : L ⧸ center L ≃* Model) :
    Function.Injective (e.toMonoidHom.comp (QuotientGroup.mk' (center L))) :=
  (centralQuotientCover e).injective_of_squarefree_odd_part_of_pCore_eq_bot
    hcore square_not_dvd

/-- Source application identifying the kernel as the actual center. -/
public theorem center_eq_bot {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]
    (hcore : pCore 2 L = ⊥) (e : L ⧸ center L ≃* Model) : center L = ⊥ := by
  have hk := (MonoidHom.ker_eq_bot_iff _).mpr (projection_injective hcore e)
  rwa [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk'] at hk

end Janko1.OddCover
