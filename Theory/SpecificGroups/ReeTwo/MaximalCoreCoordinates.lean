module

public import Theory.SpecificGroups.ReeTwo.MaximalCharacters

/-!
# A four-element quotient of the four core-character kernels

On each maximal-character kernel with core coefficient one, parity and
the root-3 character give a surjection onto a group of order four. Correcting
roots 1 and 3 by a power of root 4 gives explicit lifts of its two basis
elements. The kernel of this quotient has order 512.

This module only constructs the quotient. Containment of its kernel in the
Frattini subgroup, and the intrinsic eighth-power test, are separate facts
needed to control automorphisms.

Source: the root coordinates and characters verified from Shinoda (1975),
(2.3), pp. 81–83, in `Core`, `RootAction`, and `MaximalCharacters`.
-/

namespace ReeTwo.SylowModel

/-- The order-2048 kernels with nonzero core-character coefficient. -/
public abbrev maximalCore (a b : ZMod 2) := (maximalCharacter a b 1).ker

/-- Parity and the root-3 coordinate on a core-character kernel. -/
@[expose] public def maximalCoreQuotient (a b : ZMod 2) :
    maximalCore a b →* FiveFour.Cyclic 2 × FiveFour.Cyclic 2 :=
  (character.prod rootThreeCharacter).comp (maximalCore a b).subtype

/-- Correcting the two roots by root 4 puts them in the required kernel. -/
public theorem maximalCore_corrected_roots_mem : ∀ a b : ZMod 2,
    rootOne * root 1 ^ a.val ∈ maximalCore a b ∧
    root 0 * root 1 ^ b.val ∈ maximalCore a b := by decide +kernel

/-- A lift of parity one and root-3 coordinate zero. -/
@[expose] public def maximalCoreFirst (a b : ZMod 2) : maximalCore a b :=
  ⟨rootOne * root 1 ^ a.val, (maximalCore_corrected_roots_mem a b).1⟩

/-- A lift of parity zero and root-3 coordinate one. -/
@[expose] public def maximalCoreSecond (a b : ZMod 2) : maximalCore a b :=
  ⟨root 0 * root 1 ^ b.val, (maximalCore_corrected_roots_mem a b).2⟩

@[simp] public theorem maximalCoreQuotient_first (a b : ZMod 2) :
    maximalCoreQuotient a b (maximalCoreFirst a b) = (FiveFour.generator 2, 1) := by
  exact (by decide +kernel : ∀ a b : ZMod 2,
    maximalCoreQuotient a b (maximalCoreFirst a b) = (FiveFour.generator 2, 1)) a b

@[simp] public theorem maximalCoreQuotient_second (a b : ZMod 2) :
    maximalCoreQuotient a b (maximalCoreSecond a b) = (1, FiveFour.generator 2) := by
  exact (by decide +kernel : ∀ a b : ZMod 2,
    maximalCoreQuotient a b (maximalCoreSecond a b) = (1, FiveFour.generator 2)) a b

/-- The two binary coordinates remain independent on all four kernels. -/
public theorem maximalCoreQuotient_surjective (a b : ZMod 2) :
    Function.Surjective (maximalCoreQuotient a b) := by
  rintro ⟨u, v⟩
  refine ⟨maximalCoreFirst a b ^ u.toAdd.val * maximalCoreSecond a b ^ v.toAdd.val, ?_⟩
  rw [map_mul, map_pow, map_pow, maximalCoreQuotient_first, maximalCoreQuotient_second]
  exact (by decide +kernel : ∀ u v : FiveFour.Cyclic 2,
    (FiveFour.generator 2, (1 : FiveFour.Cyclic 2)) ^ u.toAdd.val *
      ((1 : FiveFour.Cyclic 2), FiveFour.generator 2) ^ v.toAdd.val = (u, v)) u v

/-- All four core-character kernels are finite two-groups. -/
public theorem maximalCore_isPGroup (a b : ZMod 2) : IsPGroup 2 (maximalCore a b) :=
  IsPGroup.of_card (n := 11)
    (maximalCharacter_ker_card a b 1 (Or.inr (Or.inr (by decide))))

/-- The common coordinate quotient has four elements. -/
public theorem maximalCoreQuotient_card :
    Nat.card (FiveFour.Cyclic 2 × FiveFour.Cyclic 2) = 4 := by
  change Nat.card (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) = 4
  rw [Nat.card_prod]
  change Nat.card (ZMod 2) * Nat.card (ZMod 2) = 4
  simp

/-- The coordinate quotient has kernel of order 512. -/
public theorem maximalCoreQuotient_ker_card (a b : ZMod 2) :
    Nat.card (maximalCoreQuotient a b).ker = 512 := by
  have hindex : (maximalCoreQuotient a b).ker.index = 4 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (maximalCoreQuotient_surjective a b)]
    exact (Nat.card_congr Subgroup.topEquiv.toEquiv).trans maximalCoreQuotient_card
  have h := (maximalCoreQuotient a b).ker.index_mul_card
  rw [hindex, maximalCharacter_ker_card a b 1 (Or.inr (Or.inr (by decide)))] at h
  omega

end ReeTwo.SylowModel
