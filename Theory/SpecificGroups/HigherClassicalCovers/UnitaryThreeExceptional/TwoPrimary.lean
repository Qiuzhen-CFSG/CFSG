module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.TwoPrimary.OddIndex
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.TwoPrimary.BinaryModel
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.TwoPrimary.DerivedBound
public import Theory.GroupTheory.PerfectCentralCoverLocalDerivedBound

/-!
# The two-primary upper bound for perfect central covers of PSU₄(3)

The full centralizer of the standard projective involution has odd index.
In a cover with two-group kernel, central transfer therefore puts the
entire kernel in the derived subgroup of its preimage. The generic primary
quotient construction extends the resulting bound to arbitrary finite
perfect central covers, including those with odd kernel factors.

The two determinant-one unitary coordinate blocks give a binary-tetrahedral
pair with normal image of index four and diagonal kernel of order two.
The derived-kernel calculation for this actual pair bounds the local
intersection by four, without assuming that the local extension is perfect.
Consequently eight divides no finite perfect central covering kernel.

Source: the two-primary part of Aschbacher--Smith I.1.4(5), printed p.408 of
`refs/quasithin.pdf`, and GLS3 §6.1, Tables 6.1.2--6.1.3. The complete
exceptional multiplier assembly remains in `UnitaryThreeExceptional`.
-/

public section
open Subgroup PerfectCentralCovering
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.TwoPrimary
universe u

/-- The exact local-to-global consumer of the centralizer derived-kernel
calculation. Odd factors in the original covering kernel are allowed. -/
theorem not_eight_dvd_kernel_of_centralizer_bound
    {E : Type u} [Group E] [Finite E] (f : Cover E (Carrier 4))
    (hlocal : ∀ {D : Type u} [Group D] [Finite D] (g : D →* standardCentralizer),
      Function.Surjective g → g.ker ≤ center D → IsPGroup 2 g.ker →
        Nat.card (g.ker ⊓ _root_.commutator D : Subgroup D) ≤ 4) :
    ¬ 8 ∣ Nat.card f.toMonoidHom.ker := by
  apply f.not_primePower_dvd_kernel_of_local_derived_bound
    (p := 2) (n := 3) standardCentralizer standardCentralizer_not_two_dvd_index
  intro D _ _ g hg hc hp hd
  have hle := hlocal g hg hc hp
  have hge := Nat.le_of_dvd (Nat.card_pos (α :=
    (g.ker ⊓ _root_.commutator D : Subgroup D))) hd
  omega

/-- The kernel of every finite perfect central cover of the actual PSU₄(3)
model has two-part at most four. Odd kernel factors are allowed. This
discharges `h2` in the exceptional universal-cover assembly. -/
theorem not_eight_dvd_kernel
    {E : Type u} [Group E] [Finite E] (f : Cover E (Carrier 4)) :
    ¬ 8 ∣ Nat.card f.toMonoidHom.ker := by
  apply not_eight_dvd_kernel_of_centralizer_bound f
  intro D _ _ g hg hc hk
  exact standardCentralizer_card_ker_inf_commutator_le_four
    BinaryModel.pair BinaryModel.pair_range_normal BinaryModel.pair_kernel_card
    BinaryModel.pair_range_index g hg hc hk

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.TwoPrimary
