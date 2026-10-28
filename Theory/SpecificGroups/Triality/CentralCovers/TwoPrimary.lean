module

public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.RootRelations

/-!
# The two-primary calculation for genuine binary triality

The finite central-extension problem is reduced to compatible lifts of the six
positive folded roots. `RootRelations` proves that additive root sections whose
commutators have strictly higher root height split the literal positive subgroup.
Its odd index and central transfer exclude two from the canonical covering kernel.

The two independent inputs here are the lifted relations for q = 2 and for q ≥ 4.
Both remain explicit: the source multiplier theorem is not asserted without them.
In particular the smallest genuine triality group is retained. The separate
odd-part calculation and the final whole-kernel assembly belong to
`CentralCovers.PrimaryAssembly`.

Sources: Aschbacher–Smith A.2.4 and I.1.3, printed pp.33 and 407 (PDF pp.44
and 418), and GLS3 §6.1, Theorem 6.1.4 and Tables 6.1.2–3. The local root
markings are those of GLS3 §2.4 and the genuine `StandardModel` construction.
-/

public section

namespace Triality.Standard.CentralCovers.TwoPrimary

open PerfectCentralCovering

/-- Assemble the two parameter ranges on the literal canonical projection.
The independent inputs are compatible root lifts, not multiplier conclusions. -/
theorem universal_not_two_dvd_kernel_of_root_calculations
    (hsmall : ∃ L : RootSections 1 (by decide)
      (universalProjection (BinaryCarrier 1 (by decide))), L.HigherCommutators)
    (hlarge : ∀ (n : ℕ) (hn : 0 < n), 2 ≤ n →
      ∃ L : RootSections n hn (universalProjection (BinaryCarrier n hn)),
        L.HigherCommutators)
    (n : ℕ) (hn : 0 < n) :
    ¬ 2 ∣ Nat.card (universalProjection (BinaryCarrier n hn)).ker := by
  by_cases hlarge_n : 2 ≤ n
  · obtain ⟨L, hL⟩ := hlarge n hn hlarge_n
    exact universal_not_two_dvd_kernel_of_higherCommutators n hn L hL
  · have hn1 : n = 1 := by omega
    subst n
    obtain ⟨L, hL⟩ := hsmall
    exact universal_not_two_dvd_kernel_of_higherCommutators 1 hn L hL

end Triality.Standard.CentralCovers.TwoPrimary
