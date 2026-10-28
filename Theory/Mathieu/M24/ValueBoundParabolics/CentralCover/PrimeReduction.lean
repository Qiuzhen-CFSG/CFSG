module

public import Theory.GroupTheory.PerfectCentralCover
public import Theory.GroupTheory.Covering
public import Theory.PGroupCore
public import Theory.Mathieu.M24.Properties.Order

/-!
# Reduction of the M₂₄ central-cover problem to the prime three

The order of M₂₄ has no repeated prime factor except two and three. Thus
its other Sylow subgroups are cyclic, and Sylow transfer excludes those
primes from the kernel of any finite perfect central cover. Triviality of
the two-core separately excludes two from the center. Only the prime three
remains in a quasisimple group whose actual central quotient is M₂₄.

The final theorem here explicitly retains the remaining three-divisibility
premise. It does not assert the M₂₄ multiplier calculation.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.4.3(2), printed pp.241--242, and I.1.1--I.1.4, printed pp.407--408.
-/

public section

open Subgroup Theory.GroupTheory PerfectCentralCovering
namespace Sporadic.Mathieu.M24ValueBoundParabolics

variable {X : Type*} [Group X] [Finite X] [IsQuasisimple X]

/-- The perfect central cover obtained from the given central-quotient isomorphism. -/
@[expose] noncomputable def centralQuotientCover (e : X ⧸ center X ≃* M24) : Cover X M24 where
  toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (center X))
  surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
  isPerfect := inferInstance
  ker_le_center := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']

omit [Finite X] in
/-- The kernel is exactly the center of the original group. -/
theorem centralQuotientCover_ker (e : X ⧸ center X ≃* M24) :
    (centralQuotientCover e).toMonoidHom.ker = center X := by
  exact (MonoidHom.ker_comp_of_injective _ _ e.injective).trans (QuotientGroup.ker_mk' _)

/-- Away from two and three, every Sylow subgroup of M₂₄ is cyclic. -/
theorem isCyclic_sylow_of_ne_two_of_ne_three {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (P : Sylow p M24) : IsCyclic P := by
  have hp : p.Prime := Fact.out
  have hsq : ¬ p ^ 2 ∣ Nat.card M24 := by
    intro h
    have hd : p ∣ Nat.card M24 := (dvd_pow_self p (by omega : 2 ≠ 0)).trans h
    rcases (m24_prime_dvd_order_iff p).mp hd with h2 | h3 | rfl | rfl | rfl | rfl
    · exact hp2 h2
    · exact hp3 h3
    all_goals rw [m24_order] at h; norm_num at h
  apply isCyclic_of_card_dvd_prime (p := p)
  rw [P.card_eq_multiplicity]
  have hn : (Nat.card M24).factorization p ≤ 1 := by
    by_contra hn
    exact hsq ((hp.pow_dvd_iff_le_factorization (Nat.card_pos.ne')).mpr (by omega))
  simpa only [pow_one] using (pow_dvd_pow p hn)

/-- Cyclic Sylow transfer excludes every center prime other than two and three. -/
theorem not_dvd_center_of_ne_two_of_ne_three
    (e : X ⧸ center X ≃* M24) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) : ¬ p ∣ Nat.card (center X) := by
  rw [← centralQuotientCover_ker e]
  exact (centralQuotientCover e).not_dvd_card_multiplier_of_isCyclic_sylow
    (isCyclic_sylow_of_ne_two_of_ne_three hp2 hp3)

omit [IsQuasisimple X] in
/-- A central involution would generate a nontrivial normal two-subgroup. -/
theorem not_two_dvd_center_of_twoCore_eq_bot (hcore : pCore 2 X = ⊥) :
    ¬ 2 ∣ Nat.card (center X) := by
  intro h
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h
  let Z : Subgroup X := zpowers (z : X)
  have hc : Nat.card Z = 2 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz]
  have hZc : Z ≤ center X := (zpowers_le).mpr z.property
  have hZnormal : Z.Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hxcenter := hZc hx
    have hcomm := mem_center_iff.mp hxcenter g
    simpa only [hcomm, mul_inv_cancel_right] using hx
  have hZp : IsPGroup 2 Z := IsPGroup.of_card (n := 1) (by simpa using hc)
  have hle : Z ≤ pCore 2 X := le_sSup ⟨hZnormal, hZp⟩
  have hbot : Z = ⊥ := le_bot_iff.mp (hcore ▸ hle)
  rw [hbot] at hc
  simp at hc

/-- Conditional assembly: after excluding three, triviality of the two-core
forces the whole center to be trivial. -/
theorem center_eq_bot_of_twoCore_eq_bot_of_three_not_dvd
    (hcore : pCore 2 X = ⊥) (e : X ⧸ center X ≃* M24)
    (hthree : ¬ 3 ∣ Nat.card (center X)) : center X = ⊥ := by
  apply Subgroup.eq_bot_of_card_eq
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro p hp
  let : Fact p.Prime := ⟨hp⟩
  by_cases hp2 : p = 2
  · subst p
    exact not_two_dvd_center_of_twoCore_eq_bot hcore
  by_cases hp3 : p = 3
  · subst p
    exact hthree
  exact not_dvd_center_of_ne_two_of_ne_three e hp2 hp3
end Sporadic.Mathieu.M24ValueBoundParabolics

end
