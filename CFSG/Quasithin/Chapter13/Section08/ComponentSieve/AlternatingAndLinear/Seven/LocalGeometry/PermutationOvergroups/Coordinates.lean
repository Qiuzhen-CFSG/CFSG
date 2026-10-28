module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.Partitions
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic

/-!
# Compatible Sylow coordinates for the seven-point calculation

The intersection of the four-plus-three and three-pair stabilizers is the
standard Sylow two-subgroup of S₇. Its even part gives the standard Sylow
subgroup of A₇. All groups are the actual permutation subgroups in the source
coordinates. The cardinalities below use kernel-checked finite enumeration.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.24, printed pp.958–959 (1 March 2004 manuscript).
-/

@[expose] public section
open Equiv Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.LocalGeometry.PermutationOvergroups

instance (g : S7) : Decidable (g ∈ pairStabilizer) :=
  inferInstanceAs (Decidable (∀ i j, pairBlock (g i) = pairBlock (g j) ↔
    pairBlock i = pairBlock j))

theorem mem_fourThree_coord (g : S7) :
    g ∈ fourThreeStabilizer ↔ ∀ i : Fin 7, i.val < 4 → (g i).val < 4 := by
  rw [mem_fourThreeStabilizer_iff, fourBlock_eq]
  rfl

instance (g : S7) : Decidable (g ∈ fourThreeStabilizer) :=
  decidable_of_iff (∀ i : Fin 7, i.val < 4 → (g i).val < 4) (mem_fourThree_coord g).symm

/-- The common Sylow two-subgroup in the source coordinates. -/
def standardTwo : Subgroup S7 := fourThreeStabilizer ⊓ pairStabilizer
instance (g : S7) : Decidable (g ∈ standardTwo) :=
  inferInstanceAs (Decidable (g ∈ fourThreeStabilizer ∧ g ∈ pairStabilizer))

section Cardinalities
local instance : Fintype S7 := fintypePerm
set_option maxRecDepth 100000

theorem pairStabilizer_card : Nat.card pairStabilizer = 48 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem standardTwo_card : Nat.card standardTwo = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

end Cardinalities

/-- In particular the pair stabilizer cannot contain a subgroup of order
  divisible by nine. -/
theorem nine_not_dvd_pairStabilizer_card : ¬ 9 ∣ Nat.card pairStabilizer := by
  rw [pairStabilizer_card]
  decide

/-- The standard two-subgroup restricted to an intermediate permutation group. -/
def standardTwoIn (B : Subgroup S7) : Subgroup B := standardTwo.comap B.subtype

/-- The alternating restriction, with its literal seven-point embedding. -/
abbrev standardEvenTwo := standardTwoIn (alternatingGroup (Fin 7))

instance (g : S7) : Decidable (g ∈ alternatingGroup (Fin 7)) :=
  inferInstanceAs (Decidable (g.sign = 1))

instance (g : alternatingGroup (Fin 7)) : Decidable (g ∈ standardEvenTwo) :=
  inferInstanceAs (Decidable (g.val ∈ standardTwo))

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.LocalGeometry.PermutationOvergroups
