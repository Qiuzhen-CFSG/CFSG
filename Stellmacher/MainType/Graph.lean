module

public import Stellmacher.ExceptionalType

/-!
# Embedded graph data for the remaining local types

The source defines its local types using a pair inside the finite ambient
group, whose intersection is an ambient Sylow subgroup and whose generated
subgroup has trivial two-core. Its coset graph may belong to the generated
subgroup rather than the whole ambient group. This record supplies that
finite graph group, its injective ambient map, the graph and critical path,
and the actual ambient Sylow witness. Each specialized local type states the
intersection and join-core equations at its own pair of vertices: a/a+1 in
(8.6), a/a' in (9.1), and a+2/a+1 in (10.1).

The native S parameter is not identified with those possibly shifted edges.
Specialized records therefore state cardinal bounds for the ambient Sylow
or supply the explicit equality of its cardinal with that of the native S.
No global local-solvability hypothesis or named-group recognition datum is
part of this interface. Source: Stellmacher, Journal of Algebra 190 (1997),
the type definitions on printed pp.45,48,65.
-/

universe u

namespace Stellmacher

open SectionsFiveToSeven

/-- A finite coset-graph group embedded into the actual ambient finite group.
The specialized type supplies its particular Sylow pair and local equations. -/
public structure EmbeddedLocalTypeGraph
    (H : Type u) [Group H] [Finite H] where
  K : Type u
  [groupK : Group K]
  [finiteK : Finite K]
  embedding : K →* H
  embedding_injective : Function.Injective embedding
  sylowIntersection : Sylow 2 H
  S : Subgroup K
  P1 : Subgroup K
  P2 : Subgroup K
  Γ : CosetGraphContext.{u, u} K S P1 P2
  criticalPath : CriticalPath Γ

end Stellmacher
