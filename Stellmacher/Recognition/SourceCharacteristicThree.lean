module
public import ABG.ChapterII.Section3.SolvableCharacteristicPower
public import ABG.ChapterII.Section3.CharacteristicPower
public import ABG.ChapterII.Section2.SimpleQD
public import Theory.GroupTheory.NonsolvableTwoLocal

/-!
# Actual source characteristic three in the semidihedral N2 branch

A finite simple N2 group with quasi-dihedral Sylow two-subgroups has ABG
source characteristic power three. This provides the actual characteristic
SL2 datum of its involution centralizers before any appeal to the First Main
Theorem or the final GL2/GU2 centralizer parameters.

The full QD fusion theorem places a simple semidihedral group in the QD
class, whose source characteristic power exists. Its chosen involution
centralizer is solvable: a nonsolvable such centralizer would give a
nonsolvable two-local normalizer, contradicting N2. The source solvability
lemma then forces its actual field order to equal three.

Source: ABG II.3 Definition 2 and the preceding existence argument,
article p23, and the N2 condition in Stellmacher's introduction. The result
uses no ABG main-theorem placeholder and no characteristic-parameter
existence assumption.
-/

namespace Stellmacher.Recognition
universe u

public theorem sourceCharacteristicPower_three_of_simple_nTwo
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hS : ABG.HasQuasiDihedralSylowTwoSubgroups G) (hN : IsNTwoGroup G) :
    ABG.HasSourceCharacteristicPower G 3 := by
  obtain ⟨q, hq, _⟩ := ABG.exists_sourceCharacteristicPower (ABG.isQDGroup_of_simple hS)
  obtain ⟨x, hx, hCx⟩ := hq
  have hsolvable : Group.IsSolvable (Subgroup.centralizer ({x} : Set G)) := by
    by_contra hnot
    obtain ⟨U, hU, hUnot⟩ :=
      Theory.GroupTheory.exists_nonsolvable_twoLocal_of_involution_centralizer hx hnot
    exact hUnot (hN U hU)
  let := hsolvable
  have heq := hCx.eq_three_of_isSolvable
  exact ⟨x, hx, heq ▸ hCx⟩

end Stellmacher.Recognition
