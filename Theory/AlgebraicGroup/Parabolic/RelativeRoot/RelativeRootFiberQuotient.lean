module

public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.sourceRelativeRootLayer_next_normal
public import Theory.AlgebraicGroup.Representations.Algebraic.RelativeRoot

/-!
# Relative-root fiber quotients

This module supplies the root elements used to model a selected relative-root
fiber in the adjacent source-layer quotient.  A root in the selected fiber has
relative height exactly `S.height`, hence its root subgroup occurs among the
generators of that layer.  The Chevalley-system range identity places every
parameterized root element in the layer, and the quotient subgroup is the
closure of their adjacent-layer classes.

These declarations form the lower quotient API used by the canonical source
coordinate model and by `RelativeRootFiberModule`.  Their construction follows
the source order preceding GLS3, Theorem 1.14.7 and uses no representation,
regularity, or numbered-theorem conclusion.
-/

set_option warningAsError false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem sourceRelativeRootLayer_root_mem
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (γ : S.D.Root)
    (hγ : γ ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root) (t : k) :
    S.C.x γ t ∈ sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
    S.coeff S.J S.height := by
  rw [sourceRelativeRootLayer, RelativeRootSeries, RootSubgroupGenerated]
  apply Subgroup.subset_closure
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  refine ⟨γ, ?_, ?_⟩
  · have himage : (Equiv.refl S.D.Root : S.D.Root → S.D.Root) '' S.J = S.J := by
      ext α
      simp
    rw [himage]
    exact hγ.2.ge
  · rw [← (S.chevalleySystem.1 γ).2]
    exact ⟨t, rfl⟩

@[expose, reducible]
public noncomputable def relativeRootLayerQuotient
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :=
  sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J S.height ⧸
    (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J
      (S.height + 1)).subgroupOf
      (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset S.coeff S.J S.height)

@[instance_reducible]
public noncomputable instance relativeRootLayerQuotientGroup
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
  Group (relativeRootLayerQuotient S) := by
  unfold relativeRootLayerQuotient
  let := sourceRelativeRootLayer_next_normal S
  infer_instance

public noncomputable def relativeRootLayerElement
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (γ : S.D.Root)
    (hγ : γ ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root) (t : k) :
    sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
      S.coeff S.J S.height :=
  ⟨S.C.x γ t, sourceRelativeRootLayer_root_mem S γ hγ t⟩

/-- A root-layer element has the corresponding Chevalley root element as its
ambient point. -/
public theorem relativeRootLayerElement_coe
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (γ : S.D.Root)
    (hγ : γ ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root) (t : k) :
    (relativeRootLayerElement S γ hγ t : Variety.Point K) = S.C.x γ t := by
  rfl

public noncomputable def relativeRootFiberQuotientSubgroup
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    [Group (relativeRootLayerQuotient S)] :
    Subgroup (relativeRootLayerQuotient S) :=
  let := sourceRelativeRootLayer_next_normal S
  Subgroup.closure (Set.range fun z :
      {γ : S.D.Root // γ ∈ relativeRootFiberAtHeight
        S.D S.coeff S.J S.height S.root} × k =>
      QuotientGroup.mk' _
      (relativeRootLayerElement S z.1.1 z.1.2 z.2))

/-- The fiber quotient subgroup is the subgroup closure of its root-layer
generators. -/
public theorem relativeRootFiberQuotientSubgroup_spec
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    letI := relativeRootLayerQuotientGroup S
    relativeRootFiberQuotientSubgroup S = Subgroup.closure
      (Set.range fun z :
        {γ : S.D.Root // γ ∈ relativeRootFiberAtHeight
          S.D S.coeff S.J S.height S.root} × k =>
        QuotientGroup.mk' _ (relativeRootLayerElement S z.1.1 z.1.2 z.2)) := by
  letI := relativeRootLayerQuotientGroup S
  rfl

public noncomputable def relativeRootFiberQuotientGenerator
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (z : {γ : S.D.Root // γ ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root} × k) :
    relativeRootFiberQuotientSubgroup S :=
  ⟨QuotientGroup.mk' _ (relativeRootLayerElement S z.1.1 z.1.2 z.2),
    Subgroup.subset_closure ⟨z, rfl⟩⟩

/-- The underlying quotient point of a fiber generator is the corresponding
root-layer quotient class. -/
public theorem relativeRootFiberQuotientGenerator_coe
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (z : {γ : S.D.Root // γ ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root} × k) :
    letI := relativeRootLayerQuotientGroup S
    (relativeRootFiberQuotientGenerator S z : relativeRootLayerQuotient S) =
      QuotientGroup.mk' _ (relativeRootLayerElement S z.1.1 z.1.2 z.2) := by
  letI := relativeRootLayerQuotientGroup S
  rfl

end Theory.AlgebraicGroup
