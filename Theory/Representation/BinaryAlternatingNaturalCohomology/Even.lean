module

public import Theory.Representation.BinaryAlternatingNaturalCohomology.Even.Displacement
public import Theory.Representation.BinaryAlternatingNaturalCohomology.Even.Normalized
public import Theory.Representation.BinaryAlternatingNaturalCohomology.Even.Restriction
public import Theory.Representation.FirstCohomologyCyclic

/-!
# Even-degree alternating natural-module cohomology

The natural modules of A₆ and A₈ have first cohomology of dimension one over
`ZMod 2`. Here the natural module is the image of the augmentation kernel in
the full permutation module modulo constants, as in §B.3.

The coordinate displacement supplies a nonzero class. For the upper bound,
subtract a principal cocycle to vanish on a point stabilizer, then identify the
normalized cocycle as a scalar multiple of the coordinate cocycle. The final
theorems discharge both steps using the restriction and normalized-cocycle
calculations.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma I.1.6(1), printed p.408 (Exercise 6.3 of
Aschbacher, *Finite Group Theory*, 1986); §B.3, printed p.83.
-/

@[expose] public section

open Representation Representation.OneCohomology

namespace BinaryPermutation

/-- Point-stabilizer normalization and the normalized cocycle calculation give
the exact dimension, with nonprincipality discharged by the augmentation test. -/
theorem alternatingNatural_finrank_H1_eq_one_of_normalization
    (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (hcard : 3 ≤ Nat.card Ω) (heven : Even (Fintype.card Ω)) (b : Ω)
    (hnormalize : ∀ f : cocycles (alternatingNaturalRepresentation Ω),
      ∃ v : natural Ω, ∀ g : alternatingGroup Ω, g.val b = b →
        f.val g = alternatingNaturalRepresentation Ω g v - v)
    (hnormalized : ∀ f : cocycles (alternatingNaturalRepresentation Ω),
      (∀ g : alternatingGroup Ω, g.val b = b → f.val g = 0) →
        ∃ a : ZMod 2, f = a • naturalCoordinateCocycle Ω b) :
    Module.finrank (ZMod 2) (H1 (alternatingNaturalRepresentation Ω)) = 1 := by
  apply finrank_H1_of_cyclicNormalForm _ (naturalCoordinateCocycle Ω b)
    (naturalCoordinateCocycle_not_principal Ω hcard heven b)
  intro f
  obtain ⟨v, hv⟩ := hnormalize f
  obtain ⟨a, ha⟩ := hnormalized
    (f - principal (alternatingNaturalRepresentation Ω) v) (by
      intro g hg
      change f.val g - (alternatingNaturalRepresentation Ω g v - v) = 0
      rw [hv g hg, sub_self])
  refine ⟨a, v, ?_⟩
  exact (sub_eq_iff_eq_add (a := f)
    (b := principal (alternatingNaturalRepresentation Ω) v)
    (c := a • naturalCoordinateCocycle Ω b)).mp ha

/-- The even-degree cohomology dimensions in Aschbacher–Smith I.1.6(1). -/
theorem alternatingNatural_finrank_H1_eq_one (n : ℕ) (hn : n = 6 ∨ n = 8) :
    Module.finrank (ZMod 2) (H1 (alternatingNaturalRepresentation (Fin n))) = 1 := by
  let b : Fin n := ⟨0, by omega⟩
  refine alternatingNatural_finrank_H1_eq_one_of_normalization (Fin n) ?_ ?_ b
    (alternatingNatural_normalize_pointStabilizer n hn b)
    (alternatingNatural_normalized_eq_coordinate n hn b)
  · simpa only [Nat.card_fin] using (show 3 ≤ n by omega)
  · rcases hn with rfl | rfl <;> decide

/-- The degree-six dimension-one assertion of Aschbacher–Smith I.1.6(1). -/
theorem alternatingSix_natural_finrank_H1 :
    Module.finrank (ZMod 2) (H1 (alternatingNaturalRepresentation (Fin 6))) = 1 :=
  alternatingNatural_finrank_H1_eq_one 6 (Or.inl rfl)

/-- The degree-eight dimension-one assertion of Aschbacher–Smith I.1.6(1). -/
theorem alternatingEight_natural_finrank_H1 :
    Module.finrank (ZMod 2) (H1 (alternatingNaturalRepresentation (Fin 8))) = 1 :=
  alternatingNatural_finrank_H1_eq_one 8 (Or.inr rfl)

/-- The degree-six nonvanishing assertion. -/
theorem alternatingSix_natural_finrank_H1_pos :
    0 < Module.finrank (ZMod 2) (H1 (alternatingNaturalRepresentation (Fin 6))) := by
  apply alternatingNatural_finrank_H1_pos_of_even
  · simp
  · decide

/-- The degree-eight nonvanishing assertion. -/
theorem alternatingEight_natural_finrank_H1_pos :
    0 < Module.finrank (ZMod 2) (H1 (alternatingNaturalRepresentation (Fin 8))) := by
  apply alternatingNatural_finrank_H1_pos_of_even
  · simp
  · decide

end BinaryPermutation
