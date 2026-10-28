module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Statements
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.Obstruction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.LocalPair

/-!
# The invariant-three embedding sieve

The model sieve in Aschbacher–Smith, Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`), needs the genuine Sylow hypothesis.
The version with an arbitrary two-group T is false.

`XiEmbedding.InvariantThree.Obstruction.counterexample` gives H = L = A₆,
X = P = E₉, and T = C₄. It proves the SQTK, `LocalInput`, relative
normality, C-component, quasisimplicity, normalization, containment, and
commutator hypotheses, and negates the entire requested conclusion.
The actual normalizer action on P/Φ(P) is irreducible and PT = TP.

The separately named `pairInput_of_sylow` prepares the corrected sufficient
variant with `IsSylowIn 2 T H`. It restricts Sylow membership to the relatively
normal component, transports it and PT = TP through O₂(L), and retains the
actual complement and Frattini actions. `not_pairReducible` turns a proved
model-local action obstruction into a contradiction, and
`automizer_cyclic_of_pairAutomizer` transfers the symplectic cyclicity output.

The complete Theorem C family computations and final assembly are still
required. Their surviving alternatives must include the linear and symplectic
possibilities as well as M₁₁, L₄(2), and L₅(2). The original `LocalInput` and
its checked obstruction are unchanged; no classification is asserted here.
-/
