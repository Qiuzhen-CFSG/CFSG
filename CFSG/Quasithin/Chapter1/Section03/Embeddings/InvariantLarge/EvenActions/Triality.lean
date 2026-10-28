module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Triality.Transport
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Triality.SourceAction

/-!
# Genuine triality Cartan power actions

The coroot words have explicit diagonal coordinates on the full D₄ Geck
lattice. Cubic coefficient automorphisms act by uniform powers on their
subgroup, including after elementary restriction and central quotient.
The concrete Borel geometry and the raw source field/Cartan configuration
give a common Sylow/Cartan alignment. The inner factor centralizes B and
the actual N_S(B) action on B/Φ(B) preserves every cyclic subgroup.

`EvenActions.Triality.frattini_power_of_source` completes this action step
from the full raw A.3.15(5) triality configuration and ambient SQTK input.
It discharges geometry, alignment and automorphism coverage, using the
source component's nonabelian simplicity. The existing conditional APIs
remain available. Construction of the raw A.3.15 case itself belongs to
the earlier source theorem.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, Notation A.2.5,
printed p.33, Lemma A.3.15(5), pp.50–51, and Proposition 1.3.4, p.511.
-/
