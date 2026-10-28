module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.RootUniqueness.TangentSpan.DimensionBound.DenseParameters.Words
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RationalDescent.BruhatParameters.RestrictedCells

/-!
# Fixed ordered root products covering the literal F4 carrier

The algebraic-field Bruhat prerequisite exposes its `U N U` factorization
before passage to opposite-unipotent cells. Its positive subgroup and middle
normalizer subgroup already use the literal words of `DenseParameters.Words`.
Exact left root transport supplies the local negative-simple exchange; the
proved root generation then gives this factorization for every carrier point.
Collecting both positive factors in the genuine `positiveOrdering` gives two
fixed products of exactly 24 roots, with the same middle normalizer word.
All nonzero-parameter rank-one contributions remain in that middle factor.

This is the unrestricted existence consequence of GLS3 1.11.5 needed by the
parameter-cell density argument, using the rank-one convention of 1.12.1.
The root collection is also the ordered-unipotent parametrization underlying
Steinberg, Theorem 7. Sources: `refs/KGroup/GLS3/Chapter1.tex`, §§1.11–1.12,
and `refs/KGroup/GLS3/Chapter2St1.tex`, Theorem 7, pp. 64–67.
-/

public section

namespace Theory.AlgebraicGroup.F4Chevalley.DenseParameters

open CarrierBruhat

universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]

/-- Two fixed 24-root products and a literal normalizer word cover every
point of the algebraic F4 carrier, given exact left root transport. In
particular this applies over the algebraic closure of a finite field of
characteristic two. Both products use the same genuine positive-root ordering. -/
theorem exists_ordered_normal_forms_of_transport
    (htransport : ∀ n ∈ normalizerWords (k := k), Nonempty (RootTransport n)) :
    ∃ p q : Fin 24 → Root, ∀ g : Variety.Point (Carrier (k := k)),
      ∃ (a b : Fin 24 → k) (n : Variety.Point (Carrier (k := k))),
        n ∈ normalizerWords (k := k) ∧ g = rootProduct p a * n * rootProduct q b := by
  let p : Fin 24 → Root := fun i => (positiveOrdering i).val
  refine ⟨p, p, ?_⟩
  intro g
  obtain ⟨u, hu, n, hn, v, hv, hg⟩ :=
    exists_unrestricted_factors_of_negativeSimpleExchange
      (negativeSimpleExchange_of_partition positiveRootPartition htransport) g
  obtain ⟨a, ha⟩ := orderedPositiveCoverage positiveOrdering u hu
  obtain ⟨b, hb⟩ := orderedPositiveCoverage positiveOrdering v hv
  exact ⟨a, b, n, hn, by rw [← ha, ← hb]; exact hg⟩

end Theory.AlgebraicGroup.F4Chevalley.DenseParameters
