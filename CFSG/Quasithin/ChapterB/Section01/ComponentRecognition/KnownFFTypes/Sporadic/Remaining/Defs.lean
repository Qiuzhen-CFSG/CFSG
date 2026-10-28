module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Defs
public import Theory.Representation.BinaryOffender.NormalizerConjugateBound

/-!
# Quantitative inputs for the remaining sporadic exclusions

These are proof contracts, not assertions of any model fact. A rank bound is
required only in the presence of a finite quasisimple source cover and its
actual quotient equivalence. Displacement, degree and generation statements
quantify over every faithful irreducible binary action of every such cover.
Generation takes place in the literal full linear normalizer.

`Remaining.lean` proves the exclusion from rank and displacement bounds, and
also supplies the degree-and-conjugates route to displacement bounds. The
model producers must prove the quantitative inputs before the eight exclusions
can be assembled. In particular a degree bound only for the simple group does
not discharge the degree contract for all its central covers.

Source: Aschbacher–Smith, B.1.13, printed pp.73–74 / PDF pp.84–85, citing
Guralnick–Malle, *Classification of 2F-modules, II*, Table 2,
DOI 10.1515/9783110198126.117.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Remaining
open Subgroup Theory.GroupTheory Representation.BinaryOffender
universe u v

/-- The required automorphism two-rank bound, using only inherited source hypotheses. -/
def RankBound (name : KnownSimple.SporadicName) (r : ℕ) : Prop :=
  ∀ {L : Type u} [Group L] [Finite L] [IsQuasisimple L],
    Nonempty (L ⧸ center L ≃* name.Carrier) →
      primeRank 2 (MulAut name.Carrier) ≤ r

/-- Every nonidentity involution in the full normalizer moves more than `r` dimensions. -/
def DisplacementBound (name : KnownSimple.SporadicName) (r : ℕ) : Prop :=
  ∀ {L : Type u} {W : Type v} [Group L] [Finite L] [IsQuasisimple L]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) L W),
    Function.Injective σ → σ.IsIrreducible →
    Nonempty (L ⧸ center L ≃* name.Carrier) →
    ∀ t : linearNormalizer σ, t ≠ 1 → t ^ 2 = 1 →
      r < fixedCodim (normalizerRepresentation σ) (zpowers t)

/-- A lower degree bound for every faithful irreducible binary central-cover action. -/
def DegreeBound (name : KnownSimple.SporadicName) (d : ℕ) : Prop :=
  ∀ {L : Type u} {W : Type v} [Group L] [Finite L] [IsQuasisimple L]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) L W),
    Function.Injective σ → σ.IsIrreducible →
    Nonempty (L ⧸ center L ≃* name.Carrier) → d ≤ Module.finrank (ZMod 2) W

/-- Each involution has `k` conjugates generating a subgroup containing the actual actor. -/
def ConjugateGenerationBound (name : KnownSimple.SporadicName) (k : ℕ) : Prop :=
  ∀ {L : Type u} {W : Type v} [Group L] [Finite L] [IsQuasisimple L]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) L W),
    Function.Injective σ → σ.IsIrreducible →
    Nonempty (L ⧸ center L ≃* name.Carrier) →
    ∀ t : linearNormalizer σ, t ≠ 1 → t ^ 2 = 1 →
      ∃ g : Fin k → linearNormalizer σ,
        normalizerActor σ ≤ ⨆ i, (zpowers t).map (MulAut.conj (g i)).toMonoidHom

/-- A common, proved rank bound and strict displacement bound suffice for one named carrier. -/
def InvolutionBounds (name : KnownSimple.SporadicName) : Prop :=
  ∃ r, RankBound.{u} name r ∧ DisplacementBound.{u,v} name r

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Remaining
