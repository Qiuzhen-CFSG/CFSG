module
public import Theory.GroupTheory.Fitting.Centralizer
public import Theory.GroupTheory.Fitting.PrimeSubgroups

/-!
# Prime support detected by prime-core automorphisms

In a finite solvable group, a prime-order element centralizing every prime
core lies in the Fitting subgroup. Its cyclic subgroup then lies in the
corresponding prime core. Thus a prime absent from its own core and from
the automorphism groups of all prime cores is absent from the group order.

This is the Fitting self-centralization argument used in Aschbacher--Smith,
14.6.14, printed p.1032. It requires no rank or small-prime assumptions.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- Prime-core automorphism orders detect every prime outside the corresponding core. -/
theorem not_dvd_card_of_solvable_core_automorphisms
    (hs : Group.IsSolvable G) {r : ℕ} (hr : r.Prime)
    (hcore : pCore r G = ⊥)
    (ha : ∀ q : ℕ, q.Prime → ¬ r ∣ Nat.card (MulAut (pCore q G))) :
    ¬ r ∣ Nat.card G := by
  intro hd
  let : Fact r.Prime := ⟨hr⟩
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' r hd
  have hp : IsPGroup r (zpowers x) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers,hx,pow_one])
  have hcent : zpowers x ≤ centralizer (fittingSubgroup G : Set G) := by
    apply subgroup_le_centralizer_fitting_of_le_centralizer_pCores
    intro q
    let Q := pCore q.val.val G
    let f : G →* MulAut Q := MulAut.conjNormal
    have he : f x = 1 := by
      apply orderOf_eq_one_iff.mp
      apply Nat.eq_one_of_dvd_coprimes
        ((hr.coprime_iff_not_dvd).mpr (ha q.val.val (Nat.prime_of_mem_primeFactors q.val.property)))
      · exact hx ▸ orderOf_map_dvd f x
      · exact orderOf_dvd_natCard _
    apply zpowers_le.mpr
    intro y hy
    have hh := congrArg (fun a : MulAut Q => (a ⟨y,hy⟩ : G)) he
    change x*y*x⁻¹ = y at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hle := Theory.GroupTheory.IsPGroup.le_pCore_of_le_fitting hp
    (hcent.trans (centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hs))
  have hx1 : x = 1 := by
    have hh := hle (mem_zpowers x)
    simpa only [hcore,mem_bot] using hh
  exact hr.ne_one (by simpa only [hx1,orderOf_one] using hx.symm)
end Theory.GroupTheory
