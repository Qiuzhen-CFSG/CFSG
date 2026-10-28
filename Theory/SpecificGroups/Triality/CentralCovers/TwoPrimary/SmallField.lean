module

public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.RootRelations
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.HighestLift
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.Pairs
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.PairCalculations
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.Commuting
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.Normalization

/-!
# Root lifts for the genuine group ³D₄(2)

`SmallField.universalRootSections` constructs all six additive root sections
in the actual finite canonical universal cover. Short roots use the splitting
of the genuine PSL₂(8) Levi. A comparison of short and long commutators proves
an involutory highest-root lift; the actual binary fixed field and folded Weyl
words give all long roots.

Exact commutation of the ten noninteracting pairs and a central normalization
of the five other pairs now give one common system satisfying
`HigherCommutators`. The normalization retains the prescribed projections and
additivity over GF(8) for short roots and the actual fixed GF(2) for long roots.
Collection then splits the literal positive subgroup, and its odd index gives
the two-primary exclusion on the canonical kernel. Both conclusions below
are unconditional. `PairCalculations` preserves the earlier conditional APIs.

Sources: Aschbacher–Smith A.2.4 and I.1.3 (PDF pp.44 and 418), GLS3 §2.4
and §6.1, Theorem 6.1.4 and Tables 6.1.2–3.
-/

public section
namespace Triality.Standard.CentralCovers.TwoPrimary
open PerfectCentralCovering

/-- The six prescribed additive root lifts in the genuine canonical cover of
³D₄(2) admit a common normalization satisfying all higher-root exchanges. -/
theorem smallField_exists_higherCommutators :
    ∃ L : RootSections 1 (by decide)
      (universalProjection (BinaryCarrier 1 (by decide))), L.HigherCommutators :=
  smallField_higherCommutators_of_adjustment
    (SmallField.exists_normalizingAdjustment SmallField.universal_commutingPairs)

/-- Two does not divide the literal canonical covering kernel of ³D₄(2).
All root-lifting, commutation and normalization premises are discharged. -/
theorem smallField_universal_not_two_dvd_kernel :
    ¬ 2 ∣ Nat.card (universalProjection (BinaryCarrier 1 (by decide))).ker := by
  obtain ⟨L, hL⟩ := smallField_exists_higherCommutators
  exact universal_not_two_dvd_kernel_of_higherCommutators 1 (by decide) L hL

end Triality.Standard.CentralCovers.TwoPrimary
