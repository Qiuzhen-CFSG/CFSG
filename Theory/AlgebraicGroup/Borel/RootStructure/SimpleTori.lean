module

public import Theory.AlgebraicGroup.Borel.RootStructure.theorem_1_12_6

/-!
Canonical simple-root torus factors for the Borel structure theorem.

For a fundamental root `alpha`, the source defines `T_alpha` as the intersection
inside the chosen torus of the centralizers of all other fundamental root
subgroups.  Arbitrary intersections of Zariski-closed sets make this a closed
subgroup without additional structure hypotheses.  `SimpleRootTorusPackage`
collects the remaining conclusions of GLS3, Theorem 1.12.7(e): the common
centralizer, one-dimensional quotient, product decomposition, and directness
for an adjoint group.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- The source-defined factor `T_alpha`: elements of `T` centralizing every
fundamental root subgroup except the one indexed by `alpha`. -/
public noncomputable def fundamentalRootTorus
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (positiveRoots : Set D.Root)
    (alpha : FundamentalRoot D positiveRoots) : ClosedSubgroup K :=
  ClosedSubgroup.ofSubgroup
    (T.toSubgroup ⊓
      ⨅ beta : {beta : FundamentalRoot D positiveRoots // beta ≠ alpha},
        Subgroup.centralizer
          ((D.rootSubgroup beta.1.1).toSubgroup : Set (Variety.Point K))) (by
      have hclosed : IsZariskiClosed K
        ((T.toSubgroup : Set (Variety.Point K)) ∩
          ⋂ beta : {beta : FundamentalRoot D positiveRoots // beta ≠ alpha},
            (Subgroup.centralizer
              ((D.rootSubgroup beta.1.1).toSubgroup : Set (Variety.Point K)) :
                Set (Variety.Point K))) := by
        apply isZariskiClosed_inter T.isZariskiClosed
        apply isZariskiClosed_iInter
        intro beta
        exact (D.rootSubgroup beta.1.1).centralizer_isZariskiClosed
      simpa only [Subgroup.coe_inf, Subgroup.coe_iInf] using hclosed)

/-- Membership in the canonical simple-root torus factor. -/
public lemma mem_fundamentalRootTorus_iff
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (positiveRoots : Set D.Root)
    (alpha : FundamentalRoot D positiveRoots) (t : Variety.Point K) :
    t ∈ fundamentalRootTorus D positiveRoots alpha ↔
      t ∈ T ∧
        ∀ beta : FundamentalRoot D positiveRoots, beta ≠ alpha →
          t ∈ Subgroup.centralizer
            ((D.rootSubgroup beta.1).toSubgroup : Set (Variety.Point K)) := by
  change t ∈
      T.toSubgroup ⊓
        ⨅ beta : {beta : FundamentalRoot D positiveRoots // beta ≠ alpha},
          Subgroup.centralizer
            ((D.rootSubgroup beta.1.1).toSubgroup : Set (Variety.Point K)) ↔ _
  simp only [Subgroup.mem_inf, Subgroup.mem_iInf]
  constructor
  · rintro ⟨ht, hcentral⟩
    refine ⟨ht, fun beta hbeta => hcentral ⟨beta, hbeta⟩⟩
  · rintro ⟨ht, hcentral⟩
    exact ⟨ht, fun beta => hcentral beta.1 beta.2⟩

/-- The canonical family of source-defined simple-root torus factors. -/
public noncomputable def canonicalSimpleRootTorusFamily
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (positiveRoots : Set D.Root) :
    SimpleRootTorusFamily D positiveRoots where
  carrier := fundamentalRootTorus D positiveRoots
  mem_iff := mem_fundamentalRootTorus_iff D positiveRoots

/-- The torus elements centralizing every fundamental root subgroup. -/
public noncomputable def fundamentalRootCentralKernel
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (positiveRoots : Set D.Root) :
    Subgroup (Variety.Point K) :=
  T.toSubgroup ⊓
    ⨅ beta : FundamentalRoot D positiveRoots,
      Subgroup.centralizer
        ((D.rootSubgroup beta.1).toSubgroup : Set (Variety.Point K))

/-- Restoring the omitted root centralizer in `T_alpha` gives the common
fundamental-root kernel. -/
public lemma fundamentalRootTorus_inf_centralizer
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (positiveRoots : Set D.Root)
    (alpha : FundamentalRoot D positiveRoots) :
    (fundamentalRootTorus D positiveRoots alpha).toSubgroup ⊓
        Subgroup.centralizer
          ((D.rootSubgroup alpha.1).toSubgroup : Set (Variety.Point K)) =
      fundamentalRootCentralKernel D positiveRoots := by
  ext t
  change
    (t ∈ T.toSubgroup ⊓
          ⨅ beta : {beta : FundamentalRoot D positiveRoots // beta ≠ alpha},
            Subgroup.centralizer
              ((D.rootSubgroup beta.1.1).toSubgroup : Set (Variety.Point K)) ∧
      t ∈ Subgroup.centralizer
        ((D.rootSubgroup alpha.1).toSubgroup : Set (Variety.Point K))) ↔
    t ∈ T.toSubgroup ⊓
      ⨅ beta : FundamentalRoot D positiveRoots,
        Subgroup.centralizer
          ((D.rootSubgroup beta.1).toSubgroup : Set (Variety.Point K))
  simp only [Subgroup.mem_inf, Subgroup.mem_iInf]
  constructor
  · rintro ⟨⟨ht, hother⟩, halpha⟩
    refine ⟨ht, fun beta => ?_⟩
    by_cases hbeta : beta = alpha
    · simpa [hbeta] using halpha
    · exact hother ⟨beta, hbeta⟩
  · rintro ⟨ht, hall⟩
    exact ⟨⟨ht, fun beta => hall beta.1⟩, hall alpha⟩

/-- The reusable form of the five torus conclusions in GLS3,
Theorem 1.12.7(e). -/
public structure SimpleRootTorusPackage
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (D : RootGroupData K T) (positiveRoots : Set D.Root) where
  simple_tori : SimpleRootTorusFamily D positiveRoots
  simple_tori_centralizer : ∀ alpha,
    (simple_tori.carrier alpha).toSubgroup ⊓
        Subgroup.centralizer
          ((D.rootSubgroup alpha.1).toSubgroup : Set (Variety.Point K)) =
      Subgroup.center (Variety.Point K)
  simple_tori_quotient : ∀ alpha,
    IsOneDimensionalTorusModuloAmbientCenter (simple_tori.carrier alpha)
  torus_product : ∀ order, EnumeratesType order → ∀ t, t ∈ T →
    ∃ factors : Fin order.length → Variety.Point K,
      (∀ i, factors i ∈ simple_tori.carrier (order.get i)) ∧
        orderedSubgroupFactorProduct simple_tori order factors = t
  adjoint_torus_direct : IsAdjointVersion K →
    ∀ order, EnumeratesType order → ∀ t, t ∈ T →
      ∃! factors : Fin order.length → Variety.Point K,
        (∀ i, factors i ∈ simple_tori.carrier (order.get i)) ∧
          orderedSubgroupFactorProduct simple_tori order factors = t

end Theory.AlgebraicGroup
