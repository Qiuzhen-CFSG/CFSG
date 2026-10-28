module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.Contracts

/-!
# Concrete inputs for the HS modular saturation argument

Nine pairwise inequivalent simple actions suffice if the actual HS carrier
has at most nine odd-order conjugacy classes. The proposed family consists
of the trivial action, one action of degree twenty, and seven larger actions.
These predicates request actual representations and their irreducibility;
they do not assert existence or completeness of a character table.

The degree-twenty model is already the subject of the independent
`SourceDegree.TraceField.ElevenFixedFree` model construction. The two other
inputs are a group conjugacy calculation and construction of the larger
simple actions. All three may use the simplicity inherited by the consumer.

Source: Guralnick--Malle, *Classification of 2F-modules I*, Proposition 5.1,
author-preprint p.16; Hiss--Malle, corrected Table 2. Candidate dimensions
come from the HS characteristic-two entry in GAP CTblLib 1.3.11,
`ctbspora.tbl`, and the ATLAS of Finite Group Representations HS page.
Their validity and the required carrier comparisons remain proof obligations.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FixedSpace

universe v

/-- An upper bound on actual odd-order conjugacy classes, not on proposed
representatives without a coverage proof. -/
def OddClassBound : Prop :=
  IsSimpleGroup KnownSimple.SporadicName.hs.Carrier →
    Nat.card (ConjClasses.mk ''
      {g : KnownSimple.SporadicName.hs.Carrier | ¬ 2 ∣ orderOf g}) ≤ 9

/-- A single genuine simple degree-twenty model, with the original group
marking, over each algebraically closed characteristic-two field. No
recognition assertion about arbitrary degree-twenty actions is included. -/
def TwentyModelExists : Prop :=
  IsSimpleGroup KnownSimple.SporadicName.hs.Carrier →
  ∀ (F : Type v) [Field F] [IsAlgClosed F] [CharP F 2],
    ∃ ρ : Representation F KnownSimple.SporadicName.hs.Carrier (Fin 20 → F),
      ρ.IsIrreducible

/-- Candidate dimensions above the source degree window. -/
def largeDegree : Fin 7 → ℕ := ![56, 132, 518, 896, 896, 1000, 1408]

/-- Seven actual simple actions, pairwise inequivalent after scalar extension.
In particular the two actions of degree 896 must be distinguished. -/
def LargeModelsExist : Prop :=
  IsSimpleGroup KnownSimple.SporadicName.hs.Carrier →
  ∀ (F : Type v) [Field F] [IsAlgClosed F] [CharP F 2],
    ∃ ρ : ∀ i, Representation F KnownSimple.SporadicName.hs.Carrier
      (Fin (largeDegree i) → F),
      (∀ i, (ρ i).IsIrreducible) ∧
        Pairwise fun i j => IsEmpty ((ρ i).Equiv (ρ j))

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FixedSpace
