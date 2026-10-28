module

public import Theory.SpecificGroups.ClassicalOrthogonal.EvenCoverKernels.Plus.RootLifts
public import Theory.GroupTheory.PerfectCentralCoverPrimeReduction
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple

/-!
# Odd-prime reduction for higher split orthogonal covering kernels

A prime dividing a finite perfect central kernel survives in a quotient cover
whose kernel has that prime order. Excluding odd prime-order kernels therefore
makes the original kernel a two-group, including that of the constructed
universal cover. Rank four and the rank-raising implication can be supplied
independently; induction then gives the entire higher split range.

The rank-four exclusion and the rank-raising implication remain explicit
mathematical inputs. This module does not prove either multiplier calculation.
In GLS3 Section 6.1, Tables 6.1.2–6.1.3 and Theorem 6.1.4, the characteristic-two
D-series has trivial canonical part and D₄(2) has exceptional elementary
divisors 2,2. Odd-primary exclusion is sufficient and preserves that exception.
The actual B.1.13 consumers are in `EvenCoverLifting.Orthogonal.HigherPlus`.
-/

@[expose] public section
namespace ClassicalOrthogonal.EvenCoverKernels.Plus
open PerfectCentralCovering
universe u

/-- Exclusion of odd prime-order kernels for finite perfect central covers of
the concrete split model. No independent model simplicity is requested. -/
def OddPrimeKernelExclusion (r : ℕ) (F : Type u) [Field F] : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 →
    ∀ (E : Type u) [Group E] [Finite E] (c : Cover E (POmegaPlus r F)),
      Nat.card c.toMonoidHom.ker ≠ p

variable {r : ℕ} {F : Type u} [Field F] [Finite F]

omit [Finite F] in
/-- A concrete extension of the normalized Siegel lifts discharges the
prime-order obstruction. The actual map, rather than an abstract family tag,
is the remaining presentation or geometry input. -/
theorem oddPrimeKernelExclusion_of_siegelLift_extensions [CharP F 2]
    (hext : ∀ (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
      (E : Type u) [Group E] [Finite E] (c : Cover E (POmegaPlus r F))
      (hc : Nat.card c.toMonoidHom.ker = p),
        ∃ s : POmegaPlus r F →* E, ∀ u v hu hv,
          s (siegelGenerator u v hu hv) =
            siegelLift c (hc.symm ▸ hp.odd_of_ne_two hp2) u v hu hv) :
    OddPrimeKernelExclusion r F := by
  intro p hp hp2 E _ _ c hc
  obtain ⟨s, hs⟩ := hext p hp hp2 E c hc
  have hi := injective_of_siegelLift_extension c _ s hs
  have hker := c.toMonoidHom.ker_eq_bot_iff.mpr hi
  have hone : Nat.card c.toMonoidHom.ker = 1 := by rw [hker]; simp
  exact hp.ne_one (hc.symm.trans hone)

/-- A prime-order quotient detects any odd prime in an arbitrary finite cover. -/
theorem not_dvd_kernel_of_oddPrimeKernelExclusion
    (h : OddPrimeKernelExclusion r F) {E : Type u} [Group E] [Finite E]
    (c : Cover E (POmegaPlus r F)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card c.toMonoidHom.ker := by
  let : Fact p.Prime := ⟨hp⟩
  exact c.not_dvd_card_kernel_of_no_prime_kernel (h p hp hp2)

/-- The exclusion controls the entire kernel, with no restriction on its
rank or exponent and without eliminating a possible two-primary part. -/
theorem kernel_isTwoGroup_of_oddPrimeKernelExclusion
    (h : OddPrimeKernelExclusion r F) {E : Type u} [Group E] [Finite E]
    (c : Cover E (POmegaPlus r F)) : IsPGroup 2 c.toMonoidHom.ker := by
  apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
  intro p hp
  obtain ⟨hprime, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
  have heq : p = 2 := by
    by_contra hne
    exact not_dvd_kernel_of_oddPrimeKernelExclusion h c hprime hne hdvd
  subst p
  exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_rfl, by decide⟩

/-- Apply the prime-order exclusion to the actual universal perfect cover. -/
theorem universal_kernel_isTwoGroup_of_oddPrimeKernelExclusion
    [Theory.GroupTheory.IsQuasisimple (POmegaPlus r F)]
    (h : OddPrimeKernelExclusion r F) :
    IsPGroup 2 (universalProjection (POmegaPlus r F)).ker :=
  kernel_isTwoGroup_of_oddPrimeKernelExclusion h (universalCover (POmegaPlus r F))

omit [Finite F] in
/-- Rank four and the genuine rank-raising implication cover all ranks at
least four. The latter can be proved independently with its lower-rank
exclusion explicit, so it has no scheduling dependency on the base case. -/
theorem oddPrimeKernelExclusion_of_rank_induction
    (hfour : OddPrimeKernelExclusion 4 F)
    (hstep : ∀ n, 4 ≤ n → OddPrimeKernelExclusion n F →
      OddPrimeKernelExclusion (n + 1) F)
    (hr : 4 ≤ r) : OddPrimeKernelExclusion r F := by
  induction r, hr using Nat.le_induction with
  | base => exact hfour
  | succ n hn ih => exact hstep n hn ih

/-- The conditional final kernel assembly uses inherited quasisimplicity only
for the target universal cover, never for a separately certified smaller model. -/
theorem universal_kernel_isTwoGroup_of_rank_induction
    [Theory.GroupTheory.IsQuasisimple (POmegaPlus r F)]
    (hr : 4 ≤ r) (hfour : OddPrimeKernelExclusion 4 F)
    (hstep : ∀ n, 4 ≤ n → OddPrimeKernelExclusion n F →
      OddPrimeKernelExclusion (n + 1) F) :
    IsPGroup 2 (universalProjection (POmegaPlus r F)).ker :=
  universal_kernel_isTwoGroup_of_oddPrimeKernelExclusion
    (oddPrimeKernelExclusion_of_rank_induction hfour hstep hr)

end ClassicalOrthogonal.EvenCoverKernels.Plus
