module

public import Theory.Mathieu.M12.Properties.Order
public import Theory.GroupTheory.PerfectCentralCover
public import Theory.GroupTheory.Covering
public import Theory.PGroupCore

/-!
# Prime reduction for central covers of M₁₂

The Sylow subgroups of M₁₂ at primes other than two and three are cyclic:
its order is 2⁶ · 3³ · 5 · 11. Transfer therefore excludes these primes
from the kernel of every finite perfect central cover. Triviality of O₂
also excludes two from the center, leaving a three-group center.

This proves the prime reduction needed for Aschbacher–Smith E.4.3(1),
printed pp.241–242 (PDF pp.252–253). The remaining three-primary exclusion
is separate. The multiplier value two in GLS3 §6.1, sporadic multiplier
table, is not assumed here.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Sporadic.Mathieu.M12SmallPair.ValueBoundParabolics.CentralCovers

theorem sylow_isCyclic_of_ne_two_three {p : ℕ} [Fact p.Prime]
    (h2 : p ≠ 2) (h3 : p ≠ 3) (P : Sylow p M12) : IsCyclic P := by
  by_cases hp : p ∣ Nat.card M12
  · rcases (m12_prime_dvd_order_iff p).mp hp with rfl | rfl | rfl | rfl
    · exact (h2 rfl).elim
    · exact (h3 rfl).elim
    · apply isCyclic_of_card_dvd_prime (p := 5)
      rw [P.card_eq_multiplicity, m12_order]
      decide +kernel
    · apply isCyclic_of_card_dvd_prime (p := 11)
      rw [P.card_eq_multiplicity, m12_order]
      decide +kernel
  · apply isCyclic_of_card_dvd_prime (p := p)
    rw [P.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd hp]
    simp

theorem not_dvd_kernel_card_of_ne_two_three
    {Q : Type*} [Group Q] [Finite Q] [Group.IsPerfect Q]
    (f : Q →* M12) (hf : Function.Surjective f) (hZ : f.ker ≤ center Q)
    {p : ℕ} [Fact p.Prime] (h2 : p ≠ 2) (h3 : p ≠ 3) :
    ¬ p ∣ Nat.card f.ker :=
  PerfectCentralCovering.not_dvd_card_kernel_of_isCyclic_sylow
    f hf hZ (sylow_isCyclic_of_ne_two_three h2 h3)

theorem two_not_dvd_center_card {Q : Type*} [Group Q] [Finite Q]
    (hcore : pCore 2 Q = ⊥) : ¬ 2 ∣ Nat.card (center Q) := by
  let P : Sylow 2 (center Q) := default
  have hl := P.map_le_pCore (inferInstance : (center Q).Normal) inferInstance 2
  have hP : (P : Subgroup (center Q)) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hx' : (x : Q) ∈ (P : Subgroup (center Q)).map (center Q).subtype :=
      ⟨x, hx, rfl⟩
    have hone : (x : Q) = 1 := by simpa only [hcore, mem_bot] using hl hx'
    exact mem_bot.mpr (Subtype.ext hone)
  have hi := P.not_dvd_index
  simpa only [hP, index_bot] using hi

theorem prime_dvd_center_card_eq_three
    {Q : Type*} [Group Q] [Finite Q] [Group.IsPerfect Q]
    (hcore : pCore 2 Q = ⊥) (e : (Q ⧸ center Q) ≃* M12)
    {p : ℕ} [Fact p.Prime] (hp : p ∣ Nat.card (center Q)) : p = 3 := by
  let f : Q →* M12 := e.toMonoidHom.comp (QuotientGroup.mk' (center Q))
  have hk : f.ker = center Q := by
    ext x
    change e (QuotientGroup.mk' (center Q) x) = 1 ↔ x ∈ center Q
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  by_contra h3
  have h2 : p ≠ 2 := by rintro rfl; exact two_not_dvd_center_card hcore hp
  apply not_dvd_kernel_card_of_ne_two_three f
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hk.le h2 h3
  rwa [hk]

theorem center_isThreeGroup
    {Q : Type*} [Group Q] [Finite Q] [Group.IsPerfect Q]
    (hcore : pCore 2 Q = ⊥) (e : (Q ⧸ center Q) ≃* M12) :
    IsPGroup 3 (center Q) := by
  rw [isPGroup_iff_primeFactors_card_subset (by decide : 3 ≠ 0)]
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  let _ : Fact p.Prime := ⟨hprime⟩
  have he := prime_dvd_center_card_eq_three hcore e (Nat.dvd_of_mem_primeFactors hp)
  rw [he]
  exact Nat.mem_primeFactors.mpr ⟨Nat.prime_three, dvd_rfl, by decide⟩

theorem center_eq_bot_of_three_not_dvd
    {Q : Type*} [Group Q] [Finite Q] [Group.IsPerfect Q]
    (hcore : pCore 2 Q = ⊥) (e : (Q ⧸ center Q) ≃* M12)
    (h3 : ¬ 3 ∣ Nat.card (center Q)) : center Q = ⊥ := by
  apply Subgroup.card_eq_one.mp
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro p hp hd
  let _ : Fact p.Prime := ⟨hp⟩
  exact h3 (prime_dvd_center_card_eq_three hcore e hd ▸ hd)

end Sporadic.Mathieu.M12SmallPair.ValueBoundParabolics.CentralCovers
