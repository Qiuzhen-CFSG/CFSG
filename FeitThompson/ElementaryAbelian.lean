module

public import Theory.ElementaryAbelian.Basic
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.ElementaryAbelian.Join

/-!
# Elementary abelian `p`-groups (compatibility shim)

The canonical definition of elementary abelian `p`-groups lives in
`Theory.ElementaryAbelian` (split across `Basic`, `VectorSpace`, and `Join`).

This module is a temporary compatibility shim kept so that existing consumers
which still `import FeitThompson.ElementaryAbelian` continue to transitively
receive the `Theory.ElementaryAbelian` declarations under their old module
path.  Consumers that use the unqualified name `IsElementaryAbelian` should
add `open Theory.ElementaryAbelian` in their own module.

Long term (issue #25, Phase 1) the goal is to migrate consumers directly to
`Theory.ElementaryAbelian` and delete this shim.
-/
