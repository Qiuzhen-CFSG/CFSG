module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.Local
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.ParameterObstruction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.Sylow
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.OuterParameters
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.Classification

/-!
# Swapped-component embedding with the sufficient Sylow hypothesis

The local module constructs a moving element of N_T(P), proves that its
induced automizer has nontrivial Frattini subgroup, and identifies an abelian
complement with E_(p²). The parameter module proves that a group of order 504
cannot satisfy the stated swapped-model alternatives.

The separately named `SwappedSylowInput` adds the genuine Sylow hypothesis
needed for the sufficient local variant. Its transport module restricts the
Sylow subgroup to the relatively normal orbit and both two-core quotients,
embeds the odd complement, and proves solvability of the local product.
Quotient Borel normalization then lifts to the original Sylow intersection.
The outer-parameter module proves that binary PSL₂ outer order divides its
defining degree and that the concrete Suzuki outer group has odd order.

`SwappedSylow.embedding_of_A_3_7_A_3_8` assembles the complete sufficient
local variant of Proposition 1.3.4(1): the actual conjugate direct product,
the plane isomorphism, and both exact PSL₂ alternatives. The Borel/Cartan
and outer-action proofs exclude Suzuki and J₁ and force even binary degree.
Only the exact universal earlier A.3.7/A.3.8 implications remain explicit,
for the Chapter 1 assembly owner to supply.

`SwappedInput.embedding_of_sylow_of_A_3_7_A_3_8` takes the additional Sylow
hypothesis separately. The original intrinsic input and obstruction results
are preserved; the unrestricted classification is not asserted.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, printed pp.509–510 and 1052.
-/
