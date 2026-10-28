module

public import Theory.AtlasPort.LinearGroups.G2.Basic
public import Theory.GroupTheory.Covering
public import Theory.PGroupCore
public import Theory.Representation.BinaryOffender.NormalizerExtension
public import Theory.Representation.AbsolutelyIrreducible
public import Theory.PrimeRank

/-!
# Independent model inputs for odd-field G₂ FF exclusion

These propositions specify the remaining model mathematics, not assumed
classification theorems. The assembly in `OddCharacteristic` requires proofs
of all four. Rank and conjugate generation are group-theoretic inputs; the
large-field degree bound and the exceptional ternary displacement bound
are independent representation-theoretic inputs.

The numerical margins are deliberately coarse: degree at least 33 exceeds
eight times automorphism two-rank four. The ternary branch instead retains
every binary irreducible module and every involution of its full normalizer,
including outer involutions and all possible central covers.

Sources: Aschbacher–Smith B.1.13, printed pp.73–74; Guralnick–Malle,
Classification of 2F-modules I, (2.6) and Proposition 4.6, pp.4 and 14–15.
The eight-conjugate input is a proposed sufficient model bound to be proved;
it is not asserted by citing that proposition.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.G2Odd
universe u v w

/-- Automorphism rank, for the actual split-octonion carrier in every odd field. -/
def AutomorphismRankBound : Prop :=
  ∀ (F : Type v) [Field F] [Finite F], 2 < Nat.card F → ringChar F ≠ 2 →
    primeRank 2 (MulAut (Atlas.G2.Model F)) ≤ 4

/-- The degree bound is imposed only on absolutely irreducible actions over
their finite characteristic-two field, not on the original binary action. -/
def LargeFieldDegreeBound : Prop :=
  ∀ (R : Type u) [Group R] [Finite R] [IsQuasisimple R]
    (F : Type v) [Field F] [Finite F], 3 < Nat.card F → ringChar F ≠ 2 →
    (R ⧸ center R ≃* Atlas.G2.Model F) → pCore 2 R = ⊥ →
    ∀ (K : Type w) [Field K] [Finite K] [CharP K 2]
      (U : Type w) [AddCommGroup U] [Module K U] [FiniteDimensional K U]
      (τ : Representation K R U), Function.Injective τ →
        τ.IsAbsolutelyIrreducible → 33 ≤ Module.finrank K U

/-- Eight conjugates in the full binary normalizer generate a subgroup
containing the component image. No innerness of the original involution is assumed. -/
def LargeFieldConjugateBound : Prop :=
  ∀ (R : Type u) [Group R] [Finite R] [IsQuasisimple R]
    (F : Type v) [Field F] [Finite F], 3 < Nat.card F → ringChar F ≠ 2 →
    (R ⧸ center R ≃* Atlas.G2.Model F) → pCore 2 R = ⊥ →
    ∀ (W : Type w) [AddCommGroup W] [Module (ZMod 2) W]
      [FiniteDimensional (ZMod 2) W] (σ : Representation (ZMod 2) R W),
      Function.Injective σ → σ.IsIrreducible →
      ∀ t : linearNormalizer σ, t ≠ 1 → t ^ 2 = 1 →
        ∃ g : Fin 8 → linearNormalizer σ,
          (actionImage σ).subgroupOf (linearNormalizer σ) ≤
            closure (Set.range fun i => g i * t * (g i)⁻¹)

/-- The small field needs the displacement bound also for outer involutions.
This includes the fourteen-dimensional binary module singled out in the source. -/
def TernaryDisplacementBound : Prop :=
  ∀ (R : Type u) [Group R] [Finite R] [IsQuasisimple R]
    (F : Type v) [Field F] [Finite F], Nat.card F = 3 → ringChar F ≠ 2 →
    (R ⧸ center R ≃* Atlas.G2.Model F) → pCore 2 R = ⊥ →
    ∀ (W : Type w) [AddCommGroup W] [Module (ZMod 2) W]
      [FiniteDimensional (ZMod 2) W] (σ : Representation (ZMod 2) R W),
      Function.Injective σ → σ.IsIrreducible →
      ∀ t : linearNormalizer σ, t ≠ 1 → t ^ 2 = 1 →
        4 < fixedCodim (normalizerRepresentation σ) (zpowers t)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.G2Odd
