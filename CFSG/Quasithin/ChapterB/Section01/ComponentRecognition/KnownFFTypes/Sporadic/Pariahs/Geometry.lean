module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Defs
public import Theory.Representation.BinaryOffender.ThreeConjugateNormalizer
public import Theory.GroupTheory.ThreeConjugateAutomorphisms

/-!
# Remaining normalizer geometry for the pariah exclusion route

These are explicit unproved contracts for the group-theoretic input to the
three-conjugate route. They concern generation of the actual linear component
image and a bound on the automorphism two-rank of its specified central quotient.
They do not assert an FF exclusion, a character table, or a description of the
normalizer's generalized Fitting subgroup.

The assembly in `Pariahs.lean` combines producers of these contracts with the
independently proved prime-degree bounds. Until all producers exist, the six
source exclusions remain unfinished. Source: Aschbacher–Smith B.1.13, printed
pp.73–74, citing Guralnick–Malle, Classification of 2F-modules II, Table 2.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Pariahs
open Subgroup Theory.GroupTheory Representation.BinaryOffender
universe u v

/-- Model facts before central-cover lifting. Finiteness, simplicity and
perfectness are inherited from the source central quotient. These facts do not
require independently certifying the order or simplicity of the carrier. -/
def SimpleGeometry (name : KnownSimple.SporadicName) (r : ℕ) : Prop :=
  ∀ [Finite name.Carrier] [IsSimpleGroup name.Carrier] [Group.IsPerfect name.Carrier],
    ThreeConjugateAutomorphisms name.Carrier ∧ primeRank 2 (MulAut name.Carrier) ≤ r

/-- Intrinsic rank and three-conjugate generation obligations for every faithful
irreducible central cover, with the actual image inside the full normalizer. -/
def Geometry (name : KnownSimple.SporadicName) (r : ℕ) : Prop :=
  ∀ {L : Type u} {W : Type v} [Group L] [Finite L] [IsQuasisimple L]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) L W),
    Function.Injective σ → σ.IsIrreducible →
    Nonempty (L ⧸ center L ≃* name.Carrier) →
    NormalizerThreeConjugates σ ∧ primeRank 2 (MulAut name.Carrier) ≤ r

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Pariahs
