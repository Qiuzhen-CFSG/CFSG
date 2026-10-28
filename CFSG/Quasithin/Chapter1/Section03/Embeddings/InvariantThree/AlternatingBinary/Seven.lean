module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.AlternatingBinary.Basic
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.AlternatingBinary.Seven.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.AlternatingBinary.Seven.PermutationAction

/-!
# The A₇ Sylow-pair exclusion

`alternating_seven` proves reducibility for the Sylow pair in every finite
central cover of A₇. A central intersection visible modulo Φ(R) already
gives an invariant subgroup. Otherwise the image of R in A₇ has order nine,
and its product with the Sylow two-subgroup has a unique four-point orbit.
The kernel of R's image on that orbit has order three and is preserved by
every permutation normalizing the pair.

The central-cover reduction pulls this line back to a proper nonzero subgroup
of R/Φ(R). It transports the actual extending automorphisms through the central
quotient and Aut(A₇) = S₇, so the invariant subgroup is preserved by the entire
pair automizer. No multiplier or additional action hypothesis is required.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Proposition 1.3.4, printed p.511 (PDF p.528).
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.AlternatingBinary
universe u
variable {Q : Type u} [Group Q] [Finite Q]

/-- The Sylow-pair action is reducible for every finite central cover of A₇. -/
theorem alternating_seven {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    (e : Q ⧸ center Q ≃* alternatingGroup (Fin 7)) : PairReducible (S : Subgroup Q) R :=
  alternating_seven_of_permutationLine seven_permutationLine h e

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.AlternatingBinary
