module
public import Theory.SpecificGroups.Symplectic.TwoRankLower
public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.F4
public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.E7
public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.E8
public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.TwistedE6
/-!
# Elementary eights in the characteristic-two exceptional carriers

The checked root words already give injective homomorphisms from the literal
Sp6(2), not merely abstract sections. Its elementary eight therefore embeds
in each actual exceptional central quotient. This extracts the ordinary
two-rank consequence without any assumption on quotient quasithinness.
Source: GLS3 §2.6 and Aschbacher--Smith A.2.12, printed p.36.
-/

public noncomputable section
namespace Theory.SpecificGroups.LieType.TwoRank
open SourceLevi SymplecticSix
open SymplecticSix.UniversalDoubleCover
open Theory.GroupTheory
open Theory.AlgebraicGroup.StandardRootSystem
local instance : Fintype typeE7Roots := Fintype.ofFinite _
local instance : Fintype typeE8Roots := Fintype.ofFinite _

/-- The actual binary symplectic presentation forces ordinary two-rank at least three. -/
theorem three_le_of_sp6_relators {H : Type*} [Group H] [Finite H]
    (A B : H) (rel : ∀ i : Fin 7, KernelPresentation.word A B i = 1)
    (hA : A ≠ 1) : 3 ≤ primeRank 2 H := by
  have hs : 3 ≤ primeRank 2 (Sp (ZMod 2)) := by
    rw [primeRank_equiv 2 (EvenProjective.equiv (F := ZMod 2))]
    exact Symplectic.TwoRank.three_le (ZMod 2) (by decide : 2 ≤ 3)
  exact hs.trans (primeRank_le_of_injective 2 (Sp6Presentation.hom A B rel)
    (Sp6Presentation.hom_injective A B rel hA))

variable (F : Type*) [Field F] [Finite F] [CharP F 2]

/-- The literal split F4 carrier contains an elementary eight. -/
theorem f4_three_le : 3 ≤ primeRank 2 (ExceptionalSplit.F4 F) := by
  apply three_le_of_sp6_relators (F4.modelA F) (F4.modelB F)
  · intro i
    change KernelPresentation.word
      (ExceptionalSplit.projection _ _ F (F4.a F))
      (ExceptionalSplit.projection _ _ F (F4.b F)) i = 1
    rw [← KernelPresentation.map_word, F4.relators, map_one]
  · exact F4.modelA_ne_one F

/-- The literal split E6 carrier contains an elementary eight. -/
theorem e6_three_le : 3 ≤ primeRank 2 (ExceptionalSplit.E6 F) := by
  apply three_le_of_sp6_relators (E6.modelA F) (E6.modelB F)
  · intro i
    change KernelPresentation.word
      (ExceptionalSplit.projection _ _ F (E6.a F))
      (ExceptionalSplit.projection _ _ F (E6.b F)) i = 1
    rw [← KernelPresentation.map_word, E6.relators, map_one]
  · exact E6.modelA_ne_one F

/-- The literal split E7 carrier contains an elementary eight. -/
theorem e7_three_le : 3 ≤ primeRank 2 (ExceptionalSplit.E7 F) := by
  apply three_le_of_sp6_relators (E7.modelA F) (E7.modelB F)
  · intro i
    change KernelPresentation.word
      (ExceptionalSplit.projection _ _ F (E7.a F))
      (ExceptionalSplit.projection _ _ F (E7.b F)) i = 1
    rw [← KernelPresentation.map_word, E7.relators, map_one]
  · exact E7.modelA_ne_one F

/-- The literal split E8 carrier contains an elementary eight. -/
theorem e8_three_le : 3 ≤ primeRank 2 (ExceptionalSplit.E8 F) := by
  apply three_le_of_sp6_relators (E8.modelA F) (E8.modelB F)
  · intro i
    change KernelPresentation.word
      (ExceptionalSplit.projection _ _ F (E8.a F))
      (ExceptionalSplit.projection _ _ F (E8.b F)) i = 1
    rw [← KernelPresentation.map_word, E8.relators, map_one]
  · exact E8.modelA_ne_one F

/-- The literal graph-field fixed model also contains the same elementary eight. -/
theorem twisted_e6_three_le (m : ℕ) :
    3 ≤ primeRank 2 (_root_.TwistedE6.Model 2 m) := by
  apply three_le_of_sp6_relators (Twisted.modelA m) (Twisted.modelB m)
  · intro i
    change KernelPresentation.word (_root_.TwistedE6.toModel 2 m (Twisted.a m))
      (_root_.TwistedE6.toModel 2 m (Twisted.b m)) i = 1
    rw [← KernelPresentation.map_word, Twisted.relators, map_one]
  · exact Twisted.modelA_ne_one m

end Theory.SpecificGroups.LieType.TwoRank
