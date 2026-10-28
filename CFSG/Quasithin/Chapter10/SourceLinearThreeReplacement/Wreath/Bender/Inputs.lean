module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.Branches
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Contracts

/-!
# Independent source inputs for the Bender branch

The Borel input places the actual component join in H-star. The recognition
input is the linear-three case of 10.2.3, with its Hall-faithfulness premise
explicit so that the two source arguments can be proved independently.
It includes the placement of the literal two-residual X needed by 10.3.3.
These propositions are outstanding obligations, not source theorems.

Source: Aschbacher--Smith, 10.2.3(2--3) and 10.3.3, pp.744--745,756.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Bender
open Chapter3.Section02
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G]

/-- Faithfulness for all the actual odd Hall actors of H intersect M. -/
def HallFaithful {T : Sylow 2 G} {L : Subgroup G}
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (H : Subgroup G) : Prop :=
  ∀ B : Subgroup H, B ≤ D.maximalLocal.subgroupOf H →
    IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H)) →
    IsMulCommutative B →
    (B.map H.subtype : Set G) * (T : Set G) =
      (T : Set G) * (B.map H.subtype : Set G) →
    B.map H.subtype ⊓ Chapter4.sectionCentralizer (localOrbit T L) = ⊥

/-- The Borel argument must produce minimality in the original subgroup lattice. -/
def BorelHStarAt (T : Sylow 2 G) : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D) (d : CentralizerData T D s) (I : Subgroup G),
    I ∈ Chapter1.cComponentsIn (centralizer ({d.first * d.second} : Set G)) →
    ¬ I ≤ D.maximalLocal → ClassificationModels.IsBenderModel (I ⧸ pCore 2 I) →
    I ⊔ (T : Subgroup G) ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal

/-- Source 10.2.3(3), specialized to its actual centralizer consumer.
The quotient, the seed and the Hall action all retain their original carriers.
The seed nontriviality is part of the parabolic calculation, not an assumption. -/
def HStarRecognitionAt (T : Sylow 2 G) : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D) (d : CentralizerData T D s) (H : Subgroup G),
    H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal →
    H ≤ centralizer ({d.first * d.second} : Set G) → HallFaithful D H →
    Nonempty ((H ⧸ pCore 2 H) ≃* Theory.SpecificGroups.SymmetricFive.WreathComponents.W) ∧
    centralizerSeed T L (d.first * d.second) ≤ H ∧
    centralizerSeed T L (d.first * d.second) ≠ ⊥

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Bender
