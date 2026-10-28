module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J2.Placement.Coverage.Transversal
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J2.Placement.CoverageReduction

/-!
# Coverage by the 72 fixed J₂ double cosets

The 128 checked subgroup words give `128 ≤ Nat.card Seed.s`. The 4,725
checked distinct cosets have representatives `a * representative i`, with
`a ∈ Seed.s` and `i : Fin 72`. The existing normal-form upper bound
`Nat.card Carrier ≤ 604800` therefore forces these cosets to exhaust the
actual degree-100 carrier. This proves the double-coset cover with all
witness premises discharged.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511/PDF p.528,
and GLS3 Table 5.3g. Witness provenance and the checked counting argument
are described in `Coverage/source/README.md`.
-/

public section
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J2Placement

/-- The 72 fixed words cover the actual carrier by double cosets of `Seed.s`. -/
theorem covers : Covers :=
  covers_of_transversal CoverageCertificate.card_seed_lower
    CoverageCertificate.transversal CoverageCertificate.transversal_factor
    CoverageCertificate.transversal_cosets_injective

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J2Placement
