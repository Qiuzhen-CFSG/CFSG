module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Geometry.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Geometry.SplitMonomial
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Geometry.OddTorus

/-!
# Residue-class assembly for inner-centralizer generation

For p congruent to one modulo four, a solvable full-Sylow overgroup supplies
a mixing matrix. For p congruent to three modulo four, an odd subgroup
normalized by the full Sylow centralizer of the original inner four-group
supplies such a matrix in its commutator with that actor. The centralizer
and either witness generate the literal graph extension by the root
calculation in the imported modules.

The final theorem discharges both constructions for every odd prime p > 3.
It proves the published generation predicate without any additional local
geometry or strongly-quasithin premise. The separate centralizer-structure
input and final family escape remain with their assembly owner.

Source: Aschbacher--Smith E.1.14(7), printed p.214, and its reference to
Aschbacher (1982), Lemma 4.11.
-/

public section
open Subgroup
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge

open InnerGenerationGeometry

variable (F : Type*) [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]

/-- Conditional assembly of the two concrete matrix-witness constructions.
Neither construction is inferred merely from the residue-class hypothesis. -/
theorem innerCentralizerGeneration_of_residue_mixing {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p)
    (hsplit : p % 4 = 1 → SolvableMixing F)
    (hnonsplit : p % 4 = 3 → FourGroupOddMixing F) :
    InnerCentralizerGeneration F := by
  have hmod : p % 4 = 1 ∨ p % 4 = 3 := by
    obtain ⟨k, hk⟩ := ho
    omega
  rcases hmod with h | h
  · exact innerCentralizerGeneration_of_solvable_mixing F (hsplit h)
  · exact innerCentralizerGeneration_of_four_group_odd_mixing F hp ho hF (hnonsplit h)

/-- The involution centralizer and the published local subgroup controls
generate the actual odd-prime PSL₃ graph extension. Both residue-class
witness constructions are discharged, retaining the original actor family
and the full ambient Sylow subgroup. -/
theorem innerCentralizerGeneration {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hbig : 3 < p) (hF : Nat.card F = p) :
    InnerCentralizerGeneration F := by
  apply innerCentralizerGeneration_of_residue_mixing F hp ho hF
  · intro hmod
    exact solvableMixing_of_card_mod_four_eq_one F (by simpa only [hF] using hmod)
  · intro hmod
    exact fourGroupOddMixing_of_card_mod_four_eq_three F hp hbig hF hmod

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge
