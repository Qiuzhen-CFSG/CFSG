module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.HigherRecognition.EvenTwisted.Absolute

/-!
# Reduction of the characteristic-two twisted exceptional FF exclusions

The literal central quotient belongs to twisted E6, genuine triality, or
the Ree F4 family with its original positive parameter restriction. Each
family's absolute fixed-space bound is applied through the actual Schur-field
action, preserving central covers and outer actions in the ambient group.

The three family bounds below remain explicit inputs. This is not yet the
unconditional FF exclusion for a finite group with quasisimple generalized
Fitting subgroup. That theorem requires constructing all three inputs from
the native group hypotheses, not importing the restricted Chapter G setup.

Source: Guralnick–Malle II, Lemmas 8.6, 8.8, 8.10 and p.64;
see `Source.md` and `EvenTwisted/Source.md` for the source conventions.
-/

public section

open Subgroup Representation Representation.BinaryOffender

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted

universe u v

variable {H : Type u} [Group H] {V : Type v} [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (N : Subgroup H) (ρ : Representation (ZMod 2) H V) [ρ.IsIrreducible]
  [IsIrreducible (ρ.comp N.subtype)]

/-- Conditional final case assembly, using the exact quotient in all three
branches. The native family estimates have not been discharged here. -/
theorem not_ff_of_absolute_family_bounds (hρ : Function.Injective ρ)
    (hQ : IsEvenTwistedQuotient (N ⧸ center N))
    (hE6 : ∀ q : ℕ, Even q → ExceptionalGroup.IsTwistedE6 (N ⧸ center N) q →
      AbsoluteGap.{u, v} H N)
    (hD4 : ∀ q : ℕ, Even q → Triality.Standard.IsTrialityGroupAt q (N ⧸ center N) →
      AbsoluteGap.{u, v} H N)
    (hF4 : ReeF4.IsReeF4Model (N ⧸ center N) → AbsoluteGap.{u, v} H N) :
    ¬ IsFFModule ρ := by
  apply not_ff_of_absoluteGap N ρ hρ
  rcases hQ with ⟨q, heven, hmodel⟩ | ⟨q, heven, hmodel⟩ | hmodel
  · exact hE6 q heven hmodel
  · exact hD4 q heven hmodel
  · exact hF4 hmodel

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted
