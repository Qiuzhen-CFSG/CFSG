module

public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.SourceSetup
public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.Commutator

/-!
This module proves that the next layer in the relative-root filtration attached
to a representation source is normal in the current layer.  The source's
root-system realization identifies the abstract base support with the simple
roots of its root-group datum; after this identification, the result is the
generic normality theorem for consecutive positive relative-root layers.  This
is the filtration normality used in the GLS3 relative-root quotient construction.
-/

set_option warningAsError false

universe u v w

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public theorem sourceRelativeRootLayer_next_normal
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    ((sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
      (S.height + 1)).subgroupOf
    (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
          S.height)).Normal := by
  let _ := Fintype.ofFinite S.D.Root
  have hbase : S.base.support = S.D.simple.toFinite.toFinset := by
    ext α
    simp only [Set.Finite.mem_toFinset]
    exact (S.rootSystemRealization.2.2.2.1 α).symm
  have hnormal := relativeRootSeries_next_layer_normal S.D S.C S.pairing
    (Equiv.refl S.D.Root) S.base S.coeff S.simpleRootExpansion
    S.chevalleySystem S.J S.height S.height_pos
  rw [hbase] at hnormal
  exact hnormal

attribute [instance] sourceRelativeRootLayer_next_normal

end Theory.AlgebraicGroup
