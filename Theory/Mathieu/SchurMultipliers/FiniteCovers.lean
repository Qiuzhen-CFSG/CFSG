module

public import Theory.GroupTheory.PerfectCentralCoverSylowNine
public import Theory.GroupTheory.PerfectCentralCoverSemidihedral
public import Theory.Mathieu.M11.Properties.Order
public import Theory.Mathieu.M11.Properties.Sylow3
public import Theory.Mathieu.M11.Properties.SylowTwo
public import Theory.Mathieu.M12.ValueBoundParabolics.CentralCovers.PrimeReduction
public import Theory.Mathieu.M23.Properties.Order
public import Theory.Mathieu.M24.ValueBoundParabolics.CentralCover.PrimeReduction
public import Theory.Mathieu.M24.ValueBoundParabolics.CentralCover.ThreeModel
public import Theory.Mathieu.M24.ValueBoundParabolics.CentralCover.ThreeTransfer
public import Theory.Mathieu.SchurMultipliers.ThreePrimary

/-!
# Finite perfect central covers of the Mathieu groups

This file records the finite-cover restrictions that are available directly
from the certified Mathieu models.  They are stated for the `Cover` interface,
so they apply to every finite perfect central cover of the displayed model.
The M₁₁ kernel is trivial: partial inversion excludes three and its
semidihedral Sylow subgroup excludes two. The M₁₂ and M₂₄ kernels are
two-groups. Their exact values and the M₂₃ value need further calculations;
no table entry is used here.

The cyclic-Sylow steps are the transfer input in Aschbacher--Smith I.1.2 and
E.4.3(1)--(2), printed pp.407--408 and pp.241--242.  The order-nine step for
M₁₁ and M₂₃ is the corresponding Sylow-nine bound.
-/

open Subgroup
open Theory.GroupTheory
open PerfectCentralCovering

namespace Sporadic.Mathieu

namespace SchurMultipliers

variable {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]

private theorem m11_isCyclic_sylow_of_ne_two_three {p : ℕ} [Fact p.Prime]
    (h2 : p ≠ 2) (h3 : p ≠ 3) (P : Sylow p M11) : IsCyclic P := by
  by_cases hp : p ∣ Nat.card M11
  · rcases (m11_prime_dvd_order_iff p).mp hp with rfl | rfl | rfl | rfl
    · exact (h2 rfl).elim
    · exact (h3 rfl).elim
    · apply isCyclic_of_card_dvd_prime (p := 5)
      rw [P.card_eq_multiplicity, m11_order]
      decide +kernel
    · apply isCyclic_of_card_dvd_prime (p := 11)
      rw [P.card_eq_multiplicity, m11_order]
      decide +kernel
  · apply isCyclic_of_card_dvd_prime (p := p)
    rw [P.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd hp]
    simp

private theorem m23_isCyclic_sylow_of_ne_two_of_ne_three {p : ℕ} [Fact p.Prime]
    (h2 : p ≠ 2) (h3 : p ≠ 3) (P : Sylow p M23) : IsCyclic P := by
  by_cases hp : p ∣ Nat.card M23
  · rcases (m23_prime_dvd_order_iff p).mp hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (h2 rfl).elim
    · exact (h3 rfl).elim
    · apply isCyclic_of_card_dvd_prime (p := 5)
      rw [P.card_eq_multiplicity, m23_order]
      decide +kernel
    · apply isCyclic_of_card_dvd_prime (p := 7)
      rw [P.card_eq_multiplicity, m23_order]
      decide +kernel
    · apply isCyclic_of_card_dvd_prime (p := 11)
      rw [P.card_eq_multiplicity, m23_order]
      decide +kernel
    · apply isCyclic_of_card_dvd_prime (p := 23)
      rw [P.card_eq_multiplicity, m23_order]
      decide +kernel
  · apply isCyclic_of_card_dvd_prime (p := p)
    rw [P.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd hp]
    simp

/-- M₁₂ central covers have no kernel prime other than two or three. -/
public theorem m12_cover_kernel_prime_restriction
    (f : Cover E M12) {p : ℕ} [Fact p.Prime]
    (h2 : p ≠ 2) (h3 : p ≠ 3) : ¬ p ∣ Nat.card f.toMonoidHom.ker := by
  exact M12SmallPair.ValueBoundParabolics.CentralCovers.not_dvd_kernel_card_of_ne_two_three
    f.toMonoidHom f.surjective f.ker_le_center h2 h3

/-- M₁₁ central covers have no kernel prime other than two or three. -/
public theorem m11_cover_kernel_prime_restriction
    (f : Cover E M11) {p : ℕ} [Fact p.Prime]
    (h2 : p ≠ 2) (h3 : p ≠ 3) : ¬ p ∣ Nat.card f.toMonoidHom.ker := by
  exact PerfectCentralCovering.not_dvd_card_kernel_of_isCyclic_sylow
    f.toMonoidHom f.surjective f.ker_le_center
    (m11_isCyclic_sylow_of_ne_two_three h2 h3)

/-- M₂₃ central covers have no kernel prime other than two or three. -/
public theorem m23_cover_kernel_prime_restriction
    (f : Cover E M23) {p : ℕ} [Fact p.Prime]
    (h2 : p ≠ 2) (h3 : p ≠ 3) : ¬ p ∣ Nat.card f.toMonoidHom.ker := by
  exact PerfectCentralCovering.not_dvd_card_kernel_of_isCyclic_sylow
    f.toMonoidHom f.surjective f.ker_le_center
    (m23_isCyclic_sylow_of_ne_two_of_ne_three h2 h3)

/-- M₂₄ central covers have no kernel prime other than two or three. -/
public theorem m24_cover_kernel_prime_restriction
    (f : Cover E M24) {p : ℕ} [Fact p.Prime]
    (h2 : p ≠ 2) (h3 : p ≠ 3) : ¬ p ∣ Nat.card f.toMonoidHom.ker := by
  exact PerfectCentralCovering.not_dvd_card_kernel_of_isCyclic_sylow
    f.toMonoidHom f.surjective f.ker_le_center
    (M24ValueBoundParabolics.isCyclic_sylow_of_ne_two_of_ne_three h2 h3)

/-- The M₁₁ Sylow-nine bound controls the three-part of every central cover. -/
public theorem m11_cover_kernel_not_nine
    (f : Cover E M11) : ¬ 9 ∣ Nat.card f.toMonoidHom.ker := by
  let _ := ‹Group.IsPerfect E›
  exact f.not_nine_dvd_card_kernel_of_sylow_nine m11Sylow3
    (by rw [m11Sylow3_coe, m11Sylow3Subgroup_card])

private theorem m23_sylow_three_card (P : Sylow 3 M23) : Nat.card P = 9 := by
  have hzero : padicValNat 3 1133440 = 0 :=
    padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr (by norm_num)))
  rw [P.card_eq_multiplicity, m23_order,
    Nat.factorization_def 10200960 Nat.prime_three,
    show (10200960 : Nat) = 3 ^ 2 * 1133440 by norm_num,
    padicValNat_base_pow_mul (by norm_num) (by norm_num) 2, hzero]
  norm_num

/-- The M₂₃ Sylow-nine bound controls the three-part of every central cover. -/
public theorem m23_cover_kernel_not_nine
    (f : Cover E M23) : ¬ 9 ∣ Nat.card f.toMonoidHom.ker := by
  let _ := ‹Group.IsPerfect E›
  exact f.not_nine_dvd_card_kernel_of_sylow_nine (Classical.choice inferInstance)
    (m23_sylow_three_card (Classical.choice inferInstance))

/-- The actual M₂₄ inverted-Heisenberg Sylow excludes three from every cover. -/
public theorem m24_cover_kernel_not_three
    (f : Cover E M24) : ¬ 3 ∣ Nat.card f.toMonoidHom.ker := by
  let _ := ‹Group.IsPerfect E›
  exact PerfectCentralCovering.not_three_dvd_kernel_of_invertedHeisenbergSylow f
    M24ValueBoundParabolics.invertedHeisenbergSylowThree

/-- Every odd prime is excluded from the kernel of a perfect M₁₂ cover. -/
public theorem m12_cover_kernel_not_odd
    (f : Cover E M12) {p : ℕ} [Fact p.Prime] (h2 : p ≠ 2) :
    ¬ p ∣ Nat.card f.toMonoidHom.ker := by
  by_cases h3 : p = 3
  · subst p
    exact m12_cover_kernel_not_three f
  · exact m12_cover_kernel_prime_restriction f h2 h3

/-- Every odd prime is excluded from the kernel of a perfect M₂₄ cover. -/
public theorem m24_cover_kernel_not_odd
    (f : Cover E M24) {p : ℕ} [Fact p.Prime] (h2 : p ≠ 2) :
    ¬ p ∣ Nat.card f.toMonoidHom.ker := by
  by_cases h3 : p = 3
  · subst p
    exact m24_cover_kernel_not_three f
  · exact m24_cover_kernel_prime_restriction f h2 h3

private theorem isTwoGroup_of_no_odd_prime {K : Type*} [Group K] [Finite K]
    (h : ∀ p, p.Prime → p ≠ 2 → ¬ p ∣ Nat.card K) : IsPGroup 2 K := by
  rw [isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)]
  intro p hp
  have heq : p = 2 := by
    by_contra hne
    exact h p (Nat.prime_of_mem_primeFactors hp) hne (Nat.dvd_of_mem_primeFactors hp)
  simp [heq, Nat.prime_two]

/-- The kernel of any finite perfect central cover of M₁₂ is a two-group. -/
public theorem m12_cover_kernel_isTwoGroup (f : Cover E M12) :
    IsPGroup 2 f.toMonoidHom.ker := by
  apply isTwoGroup_of_no_odd_prime
  intro p hp h2
  let _ : Fact p.Prime := ⟨hp⟩
  exact m12_cover_kernel_not_odd f h2

/-- The kernel of any finite perfect central cover of M₂₄ is a two-group. -/
public theorem m24_cover_kernel_isTwoGroup (f : Cover E M24) :
    IsPGroup 2 f.toMonoidHom.ker := by
  apply isTwoGroup_of_no_odd_prime
  intro p hp h2
  let _ : Fact p.Prime := ⟨hp⟩
  exact m24_cover_kernel_not_odd f h2

/-- The actual semidihedral Sylow subgroup excludes two from an M₁₁ cover. -/
public theorem m11_cover_kernel_not_two (f : Cover E M11) :
    ¬ 2 ∣ Nat.card f.toMonoidHom.ker := by
  obtain ⟨Q, a, b, ha, hb, hba, hgen⟩ := m11_exists_semidihedral_sylow
  exact PerfectCentralCovering.not_two_dvd_card_kernel_of_semidihedral_sylow
    f.toMonoidHom f.surjective f.ker_le_center Q a b ha
    (by simpa only [hb] using pow_orderOf_eq_one b) hba hgen

/-- Every finite perfect central cover of the concrete M₁₁ is injective. -/
public theorem m11_cover_kernel_eq_bot (f : Cover E M11) :
    f.toMonoidHom.ker = ⊥ := by
  apply Subgroup.card_eq_one.mp
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro p hp hd
  let _ : Fact p.Prime := ⟨hp⟩
  by_cases h2 : p = 2
  · subst p
    exact m11_cover_kernel_not_two f hd
  by_cases h3 : p = 3
  · subst p
    exact m11_cover_kernel_not_three f hd
  exact m11_cover_kernel_prime_restriction f h2 h3 hd

end SchurMultipliers

end Sporadic.Mathieu
