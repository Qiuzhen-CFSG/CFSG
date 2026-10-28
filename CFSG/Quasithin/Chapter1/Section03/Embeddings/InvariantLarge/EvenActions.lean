module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Kernel
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.FieldPowers
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.G2
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.G2.Source.Coverage
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Linear.SourceConvention
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.RankOne
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Ree.Coverage
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Triality

/-!
# Characteristic-two Cartan actions for invariant Ξ embeddings

This development supplies the nonsymplectic action steps from the full raw
A.3.15(5) configuration, with actual model equivalences and the literal
normalizer action on B/Φ(B):

* `RankOne.isCyclic_of_generalizedFitting` proves cyclicity for PSL₂, PSU₃
  and Suzuki directly from the ambient permutability hypotheses.
* `G2.Source.frattini_power_of_source`, `Triality.frattini_power_of_source`
  and `Ree.Source.frattini_power_of_source` prove the power-orbit conclusion.
* `Linear.frattini_of_source_configuration` constructs one square-one
  automorphism giving the two power orbits in type A₂. Its raw input permits
  automorphism-conjugates of field actions, as required by GLS3's convention.

The concrete torus computations, inner-action kernels, source alignment and
automorphism coverage are discharged. Triality uses the genuine cubic-field
fixed-group central quotient; its coefficient action retains the order-three
contribution and is distinct from the source field subgroup. The unitary
rank-one model retains matrix-field order (2ⁿ)², and the Ree branch keeps
m ≥ 1 separate from the Tits endpoint.

These are the action deductions from the supplied raw case. The parent owns
the existence of that case, cover transport, irreducibility contradictions
and the symplectic alternative in the final embedding classification.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, Proposition 1.3.4,
printed p.511 (PDF p.528), using Lemma A.3.15(5), printed pp.50–51 (PDF pp.61–62).
-/
