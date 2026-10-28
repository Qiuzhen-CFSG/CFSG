module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.Covers

/-!
# The four remaining sporadic actions in the invariant-three sieve

The last paragraph of Aschbacher–Smith's proof of Proposition 1.3.4,
printed p.511 (PDF p.528 of `refs/quasithin.pdf`), requires local action
calculations for M₂₃, M₂₄, J₂ and J₄. Its local quotients are GL₂(4),
S₃ × L₃(2), Z₂/(S₃ × Z₃) and S₅ × L₃(2), respectively. Extension
notation does not assert splitting, and the J₂ assertion includes outer
automorphisms of the fixed ATLAS permutation carrier.

`SporadicActions.Transport` proves transport of the actual pair automizer
and invariant subgroups of the Frattini quotient. `SporadicActions.Covers`
removes central two-kernels using a universal earlier multiplier bound,
then transfers a proved fixed-carrier calculation to the source pair.

The four `CarrierPairExclusion` computations remain to be proved and
assembled here. The present exports are conditional reductions, not the
source's four exclusions. The parent retains the irreducibility contradiction.
-/
