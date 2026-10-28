module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.Contracts
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.Setup
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.LocalAction
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.Models
public import CFSG.KnownSimple.CarrierCatalogue

/-!
# The two remaining model inspections in E.6.23

The quotient recognition retains the full ambient configuration, its common
Sylow and all five alternatives of earlier E.6.8. In particular it is not a
claim about arbitrary A₆ components of involution centralizers. Theorem C
supplies the complete central-quotient catalogue as an explicit input.

The independent binary calculation may assume that quotient identification.
It must remove the central two-cover and prove outerness for the actual
order-two subgroup of Aut(Y), whose fixed subgroup contains the embedded A₆
component. These are outstanding proof contracts. Neither is an established
source theorem or an extra earlier-source premise to the completed result.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.254
(PDF p.265), the further-enlargement paragraph of E.6.23. The retained
earlier statements are Theorem C (p.33), E.6.8 (pp.247–248), E.6.18 (p.252)
and E.6.21 (p.253).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification
open ComponentBalance
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Exactly the permitted earlier E.6.8, E.6.18 and E.6.21 statements.
The Q in every E.6.8 action clause is the original C_T(V). -/
structure EarlierResults (T : Sylow 2 G) (M V : Subgroup G) : Prop where
  component_alternatives : ∀ B ∈ obstructionFamily M V, ∀ Y : Subgroup G,
    CentralizerComponent B Y → ¬ Y ≤ M ∧
      Components.ComponentAlternatives M V B (sylowCentralizer (T : Subgroup G) V) Y
  seven_excluded : SevenExcluded M V
  odd_core_free : OddCoreFree V

/-- Screen the complete Theorem C catalogue using the full source action data.
Only a central-quotient identification is requested here; the binary cover
and outer-action calculation is a separate, independent obligation. -/
def QuotientRecognition (T : Sylow 2 G) (M V : Subgroup G)
    [IsElementaryAbelian 2 V] : Prop :=
  HypothesisE61 KnownSimple.IsKnownSimple T M V → HypothesisE615 V →
    EarlierResults T M V →
    ∀ U A L X : Subgroup G, ∀ g : G, EscapeConfiguration M V U A L X g →
      intersection A U g ≠ ⊥ → ∀ Y : Subgroup G, NormalComponentExtension U A X g Y →
        ChapterA.Section02.IsTheoremCModel (Y ⧸ center Y) →
          ClassicalGroup.IsPSL (Y ⧸ center Y) 4 2 ∨
            ClassicalGroup.IsPSL (Y ⧸ center Y) 5 2

/-- The binary-model calculation, conditional on the quotient identification.
An actual A₆ component of the literal fixed subgroup is retained. In particular,
a central quotient or an abstract automorphism-family label cannot discharge it. -/
def BinaryCoverAnalysis : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] [IsQuasisimple D],
    IsStronglyQuasithin D → IsPGroup 2 (center D) →
    (ClassicalGroup.IsPSL (D ⧸ center D) 4 2 ∨
      ClassicalGroup.IsPSL (D ⧸ center D) 5 2) →
    ∀ R : Subgroup (MulAut D), Nat.card R = 2 → ∀ S : Subgroup D,
      S ≤ FixedPoints.subgroup R D →
      IsComponent (FixedPoints.subgroup R D) (S.subgroupOf (FixedPoints.subgroup R D)) →
      Chapter1.Section02.LocalModels.IsAlternating S 6 →
        center D = ⊥ ∧ ¬ R ≤ (MulAut.conj : D →* MulAut D).range

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification
