module

public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.GroupTheory.PerfectCentralCoverOddPart
public import Theory.GroupTheory.PerfectCentralCoverOddSupport

/-!
# Odd central kernels over PSL₄(3)

The actual projective group over any three-element field has order
2⁷ · 3⁶ · 5 · 13. Every other odd prime has cyclic Sylow subgroups, so
central transfer excludes it from a finite perfect covering kernel.
An odd kernel and trivial three-core then make the given cover injective.
This needs neither a universal-cover calculation nor a chosen field model.

Source: Aschbacher–Smith A.2.17, printed p.39, degree-four linear branch;
the cyclic-Sylow transfer statement is I.1.2, printed p.407.
-/

public section

open PerfectCentralCovering
open scoped MatrixGroups

namespace Matrix.PSL4.OddCentralKernels

variable {F : Type*} [Field F] [Finite F]

/-- The actual quotient order, uniformly over all fields of order three. -/
theorem card_projective_three (hF : Nat.card F = 3) :
    Nat.card PSL(4, F) = 6065280 := by
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
  rw [hF] at h
  norm_num [Fin.prod_univ_succ] at h
  omega

private theorem square_not_dvd_order {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hr3 : r ≠ 3) : ¬ r ^ 2 ∣ 6065280 := by
  intro hd
  have hrd : r ∣ 2 ^ 7 * (3 ^ 6 * (5 * 13)) := by
    norm_num
    exact (dvd_pow_self r (by decide : 2 ≠ 0)).trans hd
  rcases hr.dvd_mul.mp hrd with h | h
  · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
      (hr.dvd_of_dvd_pow h))
  rcases hr.dvd_mul.mp h with h | h
  · exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp
      (hr.dvd_of_dvd_pow h))
  rcases hr.dvd_mul.mp h with h | h
  · have he : r = 5 := (Nat.prime_dvd_prime_iff_eq hr (by decide)).mp h
    subst r
    norm_num at hd
  · have he : r = 13 := (Nat.prime_dvd_prime_iff_eq hr (by decide)).mp h
    subst r
    norm_num at hd

/-- Only two and three can divide any perfect central kernel over PSL₄(3). -/
theorem prime_dvd_kernel_eq_two_or_three (hF : Nat.card F = 3)
    {E : Type*} [Group E] [Finite E] (f : Cover E PSL(4, F))
    {r : ℕ} (hr : r.Prime) (hd : r ∣ Nat.card f.toMonoidHom.ker) :
    r = 2 ∨ r = 3 := by
  by_cases hr2 : r = 2
  · exact Or.inl hr2
  by_cases hr3 : r = 3
  · exact Or.inr hr3
  let : Fact r.Prime := ⟨hr⟩
  exact (f.not_dvd_card_kernel_of_square_not_dvd
    (by rw [card_projective_three hF]; exact square_not_dvd_order hr hr2 hr3) hd).elim

/-- The source's oddness and trivial defining core make this actual map injective. -/
theorem ker_eq_bot_of_odd_of_threeCore_eq_bot (hF : Nat.card F = 3)
    {E : Type*} [Group E] [Finite E] (f : Cover E PSL(4, F))
    (hodd : Odd (Nat.card f.toMonoidHom.ker)) (hcore : pCore 3 E = ⊥) :
    f.toMonoidHom.ker = ⊥ :=
  f.ker_eq_bot_of_odd_of_pCore_eq_bot hodd hcore
    (fun _ hr hd => prime_dvd_kernel_eq_two_or_three hF f hr hd)

end Matrix.PSL4.OddCentralKernels
