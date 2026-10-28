module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.FourActors.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.FourActors.Geometry.Transfer
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Geometry.SplitMonomial
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Geometry.OddTorus
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.FourActors.Geometry.ConjugateFusion

/-!
# Residue-class assembly for positioned outer four-group generation

For primes congruent to one modulo four, a solvable overgroup of the full
ambient Sylow containing a mixing matrix suffices. For primes congruent to
three modulo four, two conjugates of the original actor transfer the odd
commutator controls to an inner four-group, where the existing odd-torus
mixing construction applies.

The final theorem discharges all three concrete inputs for every odd prime
p > 3. It proves `FourActorCentralizerGeneration` for the literal graph
extension, retaining the original family and the full ambient Sylow subgroup.
No additional geometry or strongly-quasithin premise is needed. The local
E-member construction and final family-escape assembly remain separate.

Source: Aschbacher--Smith E.1.14(7), printed p.214, and the reference there to
Aschbacher (1982), Lemma 4.11; the controls come from E.1.1--5, pp.209--210.
-/

public section
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies
open InnerGenerationGeometry
variable (F : Type*) [Field F] [Finite F]

/-- Conditional assembly retaining both existing matrix-witness producers
and the independent outer-actor conjugacy calculation. -/
theorem fourActorCentralizerGeneration_of_residue_geometry {p : ℕ}
    (ho : Odd p) (hsplit : p % 4 = 1 → SolvableMixing F)
    (hnonsplit : p % 4 = 3 → FourGroupOddMixing F)
    (hfusion : p % 4 = 3 → OuterFourConjugateFusion F) :
    FourActorCentralizerGeneration F := by
  have hmod : p % 4 = 1 ∨ p % 4 = 3 := by obtain ⟨k, hk⟩ := ho; omega
  rcases hmod with h | h
  · exact fourActorCentralizerGeneration_of_solvable_mixing F (hsplit h)
  · exact fourActorCentralizerGeneration_of_conjugate_fusion F (hnonsplit h) (hfusion h)

/-- The inner involution centralizer and the published local subgroup controls
generate the actual odd-prime PSL₃ graph extension. Solvable full-Sylow mixing
handles the split residue class; conjugates of the original outer actor transfer
its odd-commutator controls to the proved inner four-group mixing construction
in the other class. No additional local geometry premise remains. -/
theorem fourActorCentralizerGeneration [IsSimpleGroup PSL(3,F)] {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hbig : 3 < p) (hF : Nat.card F = p) :
    FourActorCentralizerGeneration F := by
  apply fourActorCentralizerGeneration_of_residue_geometry F ho
  · intro hmod
    exact solvableMixing_of_card_mod_four_eq_one F (by simpa only [hF] using hmod)
  · intro hmod
    exact fourGroupOddMixing_of_card_mod_four_eq_three F hp hbig hF hmod
  · intro _
    exact outerFourConjugateFusion_of_odd_card F ho hF

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies
