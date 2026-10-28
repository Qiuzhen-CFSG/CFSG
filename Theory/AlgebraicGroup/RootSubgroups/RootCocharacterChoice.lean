module

public import Theory.AlgebraicGroup.RootSubgroups.Cocharacter

universe u

/-!
# Cartan-normalized root cocharacter choices

GLS3, Theorem 1.9.5(d), chooses for each root `beta` a cocharacter whose
evaluation under every root character `alpha` is the Laurent power with
Cartan exponent `D.pairing alpha beta`.  The predicate below isolates exactly
that source assertion.  A realized datum's stored cocharacter is one such
choice, by its realization equations.

These root-character equations do not determine the cocharacter on an ambient
central torus: multiplying by a central cocharacter preserves them.  Consumers
which need a cocharacter in the derived group must therefore existentially
choose a Cartan-normalized cocharacter with that geometric property, rather
than claim it for the arbitrary cocharacter stored in `RootGroupData`.
-/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- A cocharacter satisfying the Cartan equations against every realized root
weight.  This is the cocharacter clause of GLS3, Theorem 1.9.5(d). -/
@[expose]
public def RootGroupData.IsCartanRootCocharacter
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (beta : D.Root)
    (h : ClosedSubgroupTorusCocharacter T) : Prop :=
  forall alpha, WeightCocharacterEquation T (D.rootWeight alpha) h
    (D.pairing alpha beta)

/-- The cocharacter stored by a realization satisfies all root-weight Cartan
equations.  No uniqueness among ambient cocharacters is asserted. -/
public theorem RootGroupData.IsRealization.rootCocharacter_isCartan
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (hD : D.IsRealization) (beta : D.Root) :
    D.IsCartanRootCocharacter beta (D.rootCocharacter beta) := by
  intro alpha
  exact hD.rootWeight_rootCocharacter alpha beta

end Theory.AlgebraicGroup
