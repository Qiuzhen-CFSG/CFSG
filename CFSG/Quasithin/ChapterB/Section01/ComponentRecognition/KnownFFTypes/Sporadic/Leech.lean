module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Defs
public import Theory.Representation.BinaryOffender.NormalizerConjugateDimension

/-!+# Degree reduction for the Leech-related sporadic exclusions

The full normalizer of a faithful irreducible binary action has a
small-displacement involution if it is an FF-module. A bound on the number
of conjugates needed to generate the action image therefore bounds the
degree. The automorphism rank is transported through the actual central
quotient, so this reduction includes all finite quasisimple central covers.

This module connects that argument to the literal `FaithfulExclusion`
contract. The required conjugate-generation, rank and bounded-degree
representation results remain explicit. No exclusion for J₂, HS, McL,
Suz, Co₁, Co₂ or Co₃ is asserted here without those premises.

Source target: Aschbacher–Smith B.1.13, printed pp.73–74 / PDF pp.84–85,
citing Guralnick–Malle, *Classification of 2F-modules, II*, Table 2,
DOI 10.1515/9783110198126.117. The carrier is always the exact catalogue
carrier; this argument supplies no comparison with alternate lattice models.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech
open Subgroup Theory.GroupTheory Representation.BinaryOffender
universe u v

/-- The representation exclusion restricted to degrees at most `d`.
Its proof, and the bounds reducing the full problem to this range, are
independent mathematical obligations. -/
@[expose] def BoundedDegreeExclusion (name : KnownSimple.SporadicName) (d : ℕ) : Prop :=
  ∀ {L : Type u} {W : Type v} [Group L] [Finite L] [IsQuasisimple L]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) L W),
    Function.Injective σ → σ.IsIrreducible →
    Nonempty (L ⧸ center L ≃* name.Carrier) →
    Module.finrank (ZMod 2) W ≤ d →
    ¬ IsFFModule (normalizerRepresentation σ)

/-- Apply the conjugate-dimension estimate to the exact source representation
and its actual catalogue identification. -/
theorem ff_degree_bound (name : KnownSimple.SporadicName)
    {L : Type u} {W : Type v} [Group L] [Finite L] [IsQuasisimple L]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) L W) (hf : Function.Injective σ)
    (hi : σ.IsIrreducible) (he : Nonempty (L ⧸ center L ≃* name.Carrier))
    {n r : ℕ} (hgen : NormalizerConjugateGenerationBound σ n)
    (hr : primeRank 2 (MulAut name.Carrier) ≤ r)
    (hff : IsFFModule (normalizerRepresentation σ)) :
    Module.finrank (ZMod 2) W ≤ n * r :=
  finrank_le_of_ff_normalizer_central_quotient σ hf hi he.some hgen hr hff

/-- A bounded-degree exclusion suffices once genuine uniform generation and
rank bounds have been proved. All three premises still require discharge. -/
theorem faithfulExclusion_of_bounded_degree (name : KnownSimple.SporadicName)
    (n r : ℕ) (hr : primeRank 2 (MulAut name.Carrier) ≤ r)
    (hgen : ∀ {L : Type u} {W : Type v} [Group L] [Finite L] [IsQuasisimple L]
      [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
      (σ : Representation (ZMod 2) L W),
      Function.Injective σ → σ.IsIrreducible →
      Nonempty (L ⧸ center L ≃* name.Carrier) →
      NormalizerConjugateGenerationBound σ n)
    (hsmall : BoundedDegreeExclusion.{u,v} name (n * r)) :
    FaithfulExclusion.{u,v} name := by
  intro L W _ _ _ _ _ _ σ hf hi he hff
  exact hsmall σ hf hi he
    (ff_degree_bound name σ hf hi he (hgen σ hf hi he) hr hff) hff

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech
