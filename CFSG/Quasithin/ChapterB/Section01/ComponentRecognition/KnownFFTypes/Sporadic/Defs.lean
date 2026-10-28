module

public import Theory.Representation.BinaryOffender.NormalizerExtension
public import Theory.GroupTheory.Covering
public import CFSG.KnownSimple.CarrierCatalogue

/-!
# Contracts for the sporadic representation exclusions

Each contract concerns the literal full linear normalizer of a faithful,
irreducible binary action of a finite quasisimple group, with its central
quotient identified with one of the twenty-six actual catalogue carriers.
These contracts are not asserted to hold in this module. Their proofs are
independent inputs to the sporadic branch of Aschbacher–Smith B.1.13,
printed pp.73–74, citing Guralnick–Malle, *Classification of 2F-modules, II*,
Table 2 (DOI 10.1515/9783110198126.117).
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open Subgroup Theory.GroupTheory Representation.BinaryOffender
universe u v

/-- The remaining representation exclusion for a single actual sporadic carrier.
Finiteness and quasisimplicity are inherited from the source actor; no independent
order or simplicity certification of the carrier is required. -/
def FaithfulExclusion (name : KnownSimple.SporadicName) : Prop :=
  ∀ {L : Type u} {W : Type v} [Group L] [Finite L] [IsQuasisimple L]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) L W),
    Function.Injective σ → σ.IsIrreducible →
    Nonempty (L ⧸ center L ≃* name.Carrier) →
    ¬ IsFFModule (normalizerRepresentation σ)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
