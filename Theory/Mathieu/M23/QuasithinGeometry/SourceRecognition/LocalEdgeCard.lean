module
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.ConcreteLocal
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.KernelNormalizer
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The order of the local pointwise edge fixer

The literal four-set kernel is UB. Its elementary kernel has order sixteen
and its specified cubic complement has order three; their orders are coprime
and the cubic normalizes the kernel. This gives the order 48 used in the
source edge-fixer rigidity argument of Aschbacher--Smith 5.2.10, p.657.
-/
public noncomputable section
open Subgroup
namespace Sporadic.Mathieu.M23Geometry

theorem fourTwoPairStabilizer_card : Nat.card fourTwoPairStabilizer = 48 := by
  have hU : Nat.card heptadKernelAmbient = 16 :=
    (card_map_of_injective heptadStabilizer.subtype_injective).trans heptadKernel_card
  have hB : heptadThreeSubgroup ≤ fourTwoPairStabilizer :=
    heptadSectionThreeSubgroup_le_twoPair AlternatingSection.s AlternatingSection.heptadAction_s
  have hn : heptadThreeSubgroup ≤ normalizer (heptadKernelAmbient : Set M23) := by
    rw [heptadKernelAmbient_normalizer]
    exact hB.trans (inf_le_left.trans fourPairStabilizer_le_heptad)
  have hd : Disjoint heptadKernelAmbient heptadThreeSubgroup :=
    disjoint_of_coprime_natCard (by rw [hU,heptadThreeSubgroup_card]; decide)
  rw [fourTwoPairStabilizer_eq_binary_three,
    card_sup_eq_mul_of_normalizes_of_disjoint _ _ hn hd,hU,heptadThreeSubgroup_card]

end Sporadic.Mathieu.M23Geometry
