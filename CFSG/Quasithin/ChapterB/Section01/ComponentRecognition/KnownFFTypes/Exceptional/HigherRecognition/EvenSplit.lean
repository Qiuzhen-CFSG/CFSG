module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.HigherRecognition.Models
public import Theory.Representation.BinaryOffender.EndFieldTransfer
public import Theory.GroupTheory.GeneralizedFitting.Defs

/-!
# Scalar reduction for the split even-field exceptional FF exclusions

The native binary hypotheses supply an absolutely irreducible representation
over the actual Schur field, with the same group, normal quasisimple component,
central quotient and offender. Its restriction to the component remains
irreducible. The finite-field witnesses in the catalogue force q = 2^a with
a positive, retaining the field of order two.

This is the scalar reduction for the source argument, not the representation
exclusion itself. The remaining F₄/E₆, E₇ and E₈ branches must establish the
strict F-module fixed-space inequalities, including outer actors and covers.
In particular the 26-dimensional F₄ modules cannot be excluded as 2F-modules.

Source: Guralnick–Malle, *Classification of 2F-modules, II*, Theorem 8.1,
Lemmas 8.8, 8.10 and 9.1, and the proof of Theorem 9.5 on internal pp.62–64.
See `Source.md` for the retained author text and the concrete carrier convention.
-/

public section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MonoidAlgebra

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenSplit

/-- Every admitted even split-field parameter is a positive power of two.
The literal four carrier equivalences are retained. -/
theorem quotient_two_power {Q : Type*} [Group Q] (hQ : IsEvenSplitQuotient Q) :
    ∃ a : ℕ, 0 < a ∧
      (ExceptionalGroup.IsF4 Q (2 ^ a) ∨ ExceptionalGroup.IsE6 Q (2 ^ a) ∨
        ExceptionalGroup.IsE7 Q (2 ^ a) ∨ ExceptionalGroup.IsE8 Q (2 ^ a)) := by
  obtain ⟨q, heven, hmodel⟩ := hQ
  have hpower : IsPrimePow q := by
    rcases hmodel with h | h | h | h <;> exact h.parameter_isPrimePow
  obtain ⟨p, a, hp, ha, hpa⟩ := (isPrimePow_nat_iff q).mp hpower
  have hp2 : p = 2 := hp.even_iff.mp <| even_iff_two_dvd.mpr <|
    Nat.prime_two.dvd_of_dvd_pow (hpa ▸ even_iff_two_dvd.mp heven)
  subst p
  exact ⟨a, ha, hpa ▸ hmodel⟩

variable {H W : Type*} [Group H] [Finite H]
  (N : Subgroup H) [N.Normal] [IsQuasisimple N]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  (ρ : Representation (ZMod 2) H W) [IsIrreducible ρ]
  [IsIrreducible (ρ.comp N.subtype)]

/-- The precise source input obtained from a native split exceptional binary
FF-action. Normality is inside H, and the quotient is exactly N/Z(N).
Absolute irreducibility is asserted only on H, as required by §8. -/
theorem exists_absolute_offender (hf : Function.Injective ρ)
    (hfit : generalizedFitting H = N) (hQ : IsEvenSplitQuotient (N ⧸ center N))
    (hff : IsFFModule ρ) :
    N.Normal ∧ IsQuasisimple N ∧ generalizedFitting H = N ∧
      CharP (Module.End (ZMod 2)[H] ρ.asModule) 2 ∧
      FiniteDimensional (Module.End (ZMod 2)[H] ρ.asModule) ρ.asModule ∧
      Function.Injective ρ.endFieldRep ∧ IsAbsolutelyIrreducible ρ.endFieldRep ∧
      IsIrreducible (ρ.endFieldRep.comp N.subtype) ∧
      ∃ (a : ℕ) (A : Subgroup H), 0 < a ∧
        (ExceptionalGroup.IsF4 (N ⧸ center N) (2 ^ a) ∨
          ExceptionalGroup.IsE6 (N ⧸ center N) (2 ^ a) ∨
          ExceptionalGroup.IsE7 (N ⧸ center N) (2 ^ a) ∨
          ExceptionalGroup.IsE8 (N ⧸ center N) (2 ^ a)) ∧
        IsElementaryTwo A ∧ Nat.card ρ.asModule ≤
          Nat.card A * Nat.card (invariants (ρ.endFieldRep.comp A.subtype)) := by
  obtain ⟨a, ha, hmodel⟩ := quotient_two_power hQ
  obtain ⟨A, hA, hcard⟩ := EndFieldTransfer.exists_endField_offender ρ hff
  exact ⟨inferInstance, inferInstance, hfit, EndFieldTransfer.charTwo ρ,
    EndFieldTransfer.finiteDimensional ρ, EndFieldTransfer.faithful ρ hf,
    endFieldRep_isAbsolutelyIrreducible ρ, EndFieldTransfer.restrict_irreducible ρ N,
    a, A, ha, hmodel, hA, hcard⟩

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenSplit
