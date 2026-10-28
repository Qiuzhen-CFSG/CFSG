module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.Max1AmalgamRigidity.Core
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.Max1RelativeRigidity.PairOrbit
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex

/-!
# Odd index of the actual max1 overlap in the full marked centralizer

The intrinsic pair centralizer has index 1771 in M. Its ambient image H
therefore has index 1771 times the odd ambient index of M. Since H ≤ C,
the index [C:D] divides [Model:H], and is odd.
No bound or formula for the order of C is needed.

The marked carriers and the identity H = M ∩ C are those of `Core`.
Source context: GLS3 Table 5.3i and the actual kernel-pair orbit proved
in `Max1RelativeRigidity.PairOrbit`.
-/

public section
open Subgroup
namespace Janko4.Max1AmalgamRigidity

theorem D_index_odd : ¬ 2 ∣ D.index := by
  have hH : ¬ 2 ∣ H.index := by
    rw [index_map_subtype, Max1RelativeRigidity.pair_centralizer_index]
    intro hd
    rcases (Nat.prime_two.dvd_mul.mp hd) with hd | hd
    · norm_num at hd
    · exact OuterReduction.max1_odd_index_unconditional hd
  intro hd
  exact hH (hd.trans (relIndex_dvd_index_of_le H_le_C))

end Janko4.Max1AmalgamRigidity
