module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.Reduction
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.Endpoint
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.Higher

/-!
# The SL₅ graph-actor displacement estimate

Every elementary actor meeting the graph coset has rank at most four.
A standard graph involution, conjugate to one of its elements, has fixed
codimension at most that of the original actor. Thus nine moved dimensions
for that involution imply the strict common-fixed-space inequality for A.
The local support splits into the endpoint pair and its complement.

The endpoint root certificate supplies nine independent moved vectors directly.
For every higher support, the local dimension certificates and generation by
three graph conjugates give the same displacement bound. Their assembly proves
`graph_estimate` under faithful irreducibility, with no inner-estimate premise.
It retains the literal `GraphEstimate` contract, including the full actor and
its common fixed space, without any degree or absolute-irreducibility assumption.

Source: Guralnick–Malle, Classification of 2F-modules II, author manuscript,
Proposition 4.8(3A–3B), pp.27–28; Aschbacher–Smith K.3.2, printed pp.454–455.
-/

public section
open Subgroup Representation Representation.BinaryOffender

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (σ : Representation (ZMod 2) SL5TenDimensional.Group V)
variable [FiniteDimensional (ZMod 2) V]

/-- The rank-four reduction applies a standard involution bound to the original full actor. -/
theorem graph_estimate_of_standard_displacement (hf : Function.Injective σ)
    (hi : IsIrreducible σ)
    (hmove : ∀ (J : Finset (Fin 4)) (v : V), v ≠ 0 →
      SL5TenDimensional.Classification.LocalHighestVector σ J v → 2 ≤ J.card →
      ∀ t : linearNormalizer σ, IsStandardGraph σ t →
        9 ≤ fixedCodim (normalizerRepresentation σ) (zpowers t)) : GraphEstimate σ := by
  intro J v hv hJ hcard A hA _ hout _
  have hr := outer_rank_le_four σ hf hi A hA hout
  obtain ⟨t, ht, hcodim⟩ := exists_standard_graph_with_codim_le σ hf hi A hA hout
  have hm := hmove J v hv hJ hcard t ht
  omega

/-- Conditional assembly of the endpoint and higher-support estimates. -/
theorem graph_estimate_of_endpoint_and_higher (hf : Function.Injective σ)
    (hi : IsIrreducible σ) (hend : EndpointDisplacement σ)
    (hhigher : HigherDisplacement σ) : GraphEstimate σ := by
  apply graph_estimate_of_standard_displacement σ hf hi
  intro J v hv hJ hcard t ht
  by_cases h : J = {0, 3}
  · subst J
    exact hend v hv hJ t ht
  · exact hhigher J v hv hJ hcard h t ht

/-- Every elementary graph actor satisfies the strict multiple-support displacement
bound on the original faithful irreducible binary module. -/
theorem graph_estimate (hf : Function.Injective σ)
    (hi : IsIrreducible σ) : GraphEstimate σ := by
  exact graph_estimate_of_endpoint_and_higher σ hf hi
    (endpoint_displacement σ) (higher_displacement σ hf hi)

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph
