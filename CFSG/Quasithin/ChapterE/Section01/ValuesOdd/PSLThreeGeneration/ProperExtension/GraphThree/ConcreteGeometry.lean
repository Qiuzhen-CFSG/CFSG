module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.Placement
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.InnerActors
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.OuterActors

/-!
# Concrete graph-centralizer placement for PSL₃(3)

The local witnesses are conjugates of the actual graph-involution centralizer.
Their S₃ quotients, two-group kernels and order-48 calculations are proved in
`GraphLocalQuotients`. Thus an intersection of order sixteen establishes the
literal Sylow clause, and escape from the intrinsic two-core establishes
nontriviality of the actor's quotient image.

The inner and outer actor calculations construct these placements for every
elementary actor of rank greater than one. Splitting on containment in the
inner subgroup exhausts the actors. The final theorem supplies both branches
to the conditional assembly and establishes `LocalGeometryAt` for the literal
graph extension over ZMod 3, with no remaining geometric premises. This
discharges the concrete placement input to the rank-one E-generation proof.

Source: Aschbacher–Smith E.1.2, E.1.5 and E.1.14(7), printed pp.209–210,
214; Asc82a, Lemma 4.11.
-/

public section
open Subgroup Theory.GroupTheory
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
open Matrix.PSL3Three.GraphLocalQuotients

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree
namespace ConcreteGeometry

/-- Conditional final assembly: the two independent actor branches must each
construct their concrete centralizer placement. -/
theorem exists_localGeometry_of_inner_outer
    (hinner : ∀ (T : Sylow 2 G) (A : Subgroup G),
      IsElementaryAbelian 2 A → A ≤ (T : Subgroup G) → 1 < Group.rank A →
      A ≤ innerPart (ZMod 3) → CentralizerPlacement T A)
    (houter : ∀ (T : Sylow 2 G) (A : Subgroup G),
      IsElementaryAbelian 2 A → A ≤ (T : Subgroup G) → 1 < Group.rank A →
      ¬ A ≤ innerPart (ZMod 3) → CentralizerPlacement T A) :
    ∃ T : Sylow 2 G, LocalGeometryAt T := by
  classical
  let T : Sylow 2 G := default
  refine ⟨T, localGeometryAt_of_centralizerPlacements T ?_⟩
  intro A hA hAT hrank
  by_cases hAI : A ≤ innerPart (ZMod 3)
  · exact hinner T A hA hAT hrank hAI
  · exact houter T A hA hAT hrank hAI

end ConcreteGeometry

/-- The literal PSL₃(3) graph extension has the local geometry required for
rank-one E-generation. Both actor branches and all quotient and Sylow
obligations are discharged by the concrete graph-centralizer calculations. -/
theorem exists_localGeometry_zmod_three :
    ∃ T : Sylow 2 (Matrix.PSL3.OddPrimeGraphExtension.graphExtension (ZMod 3)),
      LocalGeometryAt T :=
  ConcreteGeometry.exists_localGeometry_of_inner_outer
    ConcreteGeometry.centralizerPlacement_of_inner
    ConcreteGeometry.centralizerPlacement_of_outer

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree
