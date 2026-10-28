module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.Contracts
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.Endpoint.Realization
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.Endpoint.AdjointCentralizer

/-!
# The binary SL₅ endpoint-pair estimate

A nonzero local highest vector with support `{0,3}` constructs an actual
equivariant identification with the trace-zero matrix representation.
`Realization` proves this identification from the local relations and
irreducibility, without a dimension cutoff or a module catalogue.

The common-centralizer estimate in `AdjointCentralizer` bounds the fixed
codimension for every nontrivial elementary subgroup of rank at most six.
Both adjoint constructions use the same trace kernel and the same matrix
conjugation action, so this estimate discharges the concrete model premise
of `endpoint_estimate_of_adjoint`. The subgroup and its marking are unchanged
under the resulting fixed-space transport.

This supplies the endpoint premise of `inner_estimate_of_end_node_and_endpoint`
in `Inner`; the independent end-node sieve handles the other ten supports.

Source: Guralnick–Malle, *Classification of 2F-modules, II*, author manuscript,
Lemma 4.5 step 2, pp.23–24, and Proposition 4.7, pp.25–26;
Aschbacher–Smith K.3.2, printed pp.454–455.
-/

public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.Endpoint

open Representation Representation.BinaryOffender

/-- The endpoint-pair common-fixed-space estimate for every faithful irreducible
finite-dimensional binary SL₅ representation. Recognition and the concrete
adjoint estimate are both discharged; no model hypothesis remains. -/
theorem endpoint_estimate {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V)
    (_hfaith : Function.Injective σ) (hirred : IsIrreducible σ) :
    EndpointEstimate σ := by
  let := hirred
  apply endpoint_estimate_of_adjoint
  intro B hB hc hr
  exact Adjoint.strict_fixedCodim_of_cubic B hB hc hr

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.Endpoint
