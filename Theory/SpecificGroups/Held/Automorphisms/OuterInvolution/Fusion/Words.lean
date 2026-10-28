module

public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.Noninner
public import Theory.SpecificGroups.Held.LocalPairs.Transport
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.Words

/-!
# Words for outer Held involution fusion

Conjugate the published outer representative by `(a*b⁻¹)^4`. The resulting
involution is intended to normalize the existing four-generator Sylow subgroup;
that assertion is checked separately. Multiplying it on the left by the
published 1024 binary words gives the exact coset to be inspected.

These definitions use actual elements of the full permutation normalizer.
They assert neither coset exhaustion nor fusion. Source: GLS3 Table 5.3p
and its pp.260–261 interpretation; the fixed ATLAS permutation model.
-/

@[expose] public section
namespace Held.OuterInvolution.Fusion
open LocalPairs
open TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration

/-- A short conjugator in the literal Held carrier. -/
def shift : He := (a * b⁻¹) ^ 4

/-- The outer involution used with the existing inner Sylow representative. -/
def outer : PermutationNormalizer := MulAut.conj (innerEmbedding shift) representative

/-- The specified outer coset of the published binary words. -/
def oddWord (n : Fin 1024) : PermutationNormalizer :=
  innerEmbedding (normalForm n).val * outer

theorem outer_sq : outer ^ 2 = 1 := by
  rw [outer, ← map_pow, representative_sq, map_one]

end Held.OuterInvolution.Fusion
