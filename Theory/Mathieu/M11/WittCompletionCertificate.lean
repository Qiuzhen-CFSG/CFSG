module

public import Theory.Mathieu.M11.WittCompletion.Tree

/-!
# All completions of the normalized small Witt seed

The four blocks through the normalized triple have exactly 48 completions, all
isomorphic to the explicit Witt `S(4,5,11)` model. For the required uniqueness
statement, the certificate exhausts all possible completions by forced unique
extensions and branching on a four-subset. Its 85 nodes and 48 explicit leaf
relabelings are checked by the kernel, using the general Steiner-system rules.

Reference: Hall, *The Theory of Groups*, Theorem 5.8.1, the combinatorial
Witt-design uniqueness route to Mathieu recognition. The certificate and its
untrusted, reproducible generator live in `WittCompletion/`.
-/

namespace Sporadic.Mathieu
open Theory.GroupTheory
open scoped Pointwise

/-- Every Steiner system containing the normalized four-block seed is isomorphic
to the repository's explicit Witt design. -/
public theorem m11_completion_equiv (D : SteinerSystem (Fin 11) 4 5)
    (hseed : m11CompletionSeed ⊆ D.blocks) :
    ∃ e : Equiv.Perm (Fin 11),
      e • (D.blocks : Set (Finset (Fin 11))) =
        (m11WittDesign.blocks : Set (Finset (Fin 11))) :=
  WittCompletion.completion D hseed

end Sporadic.Mathieu
