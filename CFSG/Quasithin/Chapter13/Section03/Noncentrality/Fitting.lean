module

public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.Components
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.Nine

/-!
# Deductions for Fitting centralization in 13.3.14(d)

The completed deductions are the literal residual-preimage transport and
movement test, the Ξ-minus prime restriction, the extraspecial rank
contradiction and E₉ isomorphism, and the entire component construction
conditional on Fitting centralization and the earlier orbit bound.

The prime-core formula reduces Fitting centralization to the odd cores.
The supercritical Ξ construction and the embedding/ratio exclusion remain
open. In particular this module does not assert reduction (d) or assume
its conclusion as a source theorem. Final assembly must discharge the
Ξ-minus and Fitting premises using the actual flag, Sylow, quotient-list,
and earlier universal source implications.
Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 13.3.14(d) and the following paragraph, printed p.892, PDF p.909.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
variable {G : Type*} [Group G] [Finite G]

/-- The two-core of the star quotient is trivial, so the odd cores suffice for (d). -/
theorem centralizes_fitting_of_odd_cores (H : Subgroup G) (A : Subgroup (Star H))
    (hodd : ∀ p : ℕ, p.Prime → Odd p →
      A ≤ centralizer (pCore p (Star H) : Set (Star H))) :
    A ≤ centralizer (fittingSubgroup (Star H) : Set (Star H)) := by
  apply le_centralizer_iff.mpr
  rw [fitting_eq_sup_pCore]
  apply iSup_le
  intro p
  have hp := Nat.prime_of_mem_primeFactors p.val.property
  by_cases h2 : p.val.val = 2
  · rw [h2, pCore_quotient_pCore_eq_bot]
    exact bot_le
  · exact le_centralizer_iff.mp (hodd p.val.val hp (hp.odd_of_ne_two h2))

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
