module

public import Theory.AlgebraicGroup.ClosedSubgroup.Closure
public import Theory.AlgebraicGroup.RootSubgroups.GeneratedSubgroup

universe u

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k]

/-- The root-generated Levi factor attached to a chosen Levi root set.  This
is an abstract subgroup of rational points; its Zariski closure is supplied
separately when an algebraic subgroup is needed. -/
@[expose]
public noncomputable def standardLeviRootFactor
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (sigmaJ : Set D.Root) :
    Subgroup (Variety.Point K) :=
  RootSubgroupGenerated D (sigmaJ ∪ D.neg '' sigmaJ)

/-- The root-generated unipotent factor attached to the positive roots outside
the Levi subsystem. -/
@[expose]
public noncomputable def standardUnipotentRootFactor
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (positiveRoots sigmaJ : Set D.Root) :
    Subgroup (Variety.Point K) :=
  RootSubgroupGenerated D (positiveRoots \ sigmaJ)

/-- The abstract root-generated standard parabolic factor. -/
@[expose]
public noncomputable def standardParabolicRootFactor
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (positiveRoots sigmaJ : Set D.Root) :
  Subgroup (Variety.Point K) :=
  RootSubgroupGenerated D (positiveRoots ∪ sigmaJ ∪ D.neg '' sigmaJ)

/-- A canonical closed algebraic subgroup containing the abstract standard
parabolic root factor.  No parabolicity assertion is built into this
definition: that is the separate geometric theorem still missing upstream. -/
@[expose]
public noncomputable def standardParabolicClosure
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (positiveRoots sigmaJ : Set D.Root) :
    ClosedSubgroup K :=
  subgroupZariskiClosure K (standardParabolicRootFactor D positiveRoots sigmaJ)

public lemma standardUnipotentRootFactor_le_standardParabolicRootFactor
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (positiveRoots sigmaJ : Set D.Root) :
    standardUnipotentRootFactor D positiveRoots sigmaJ ≤
      standardParabolicRootFactor D positiveRoots sigmaJ := by
  apply RootSubgroupGenerated_mono D
  intro α hα
  exact Or.inl (Or.inl hα.1)

public lemma standardLeviRootFactor_le_standardParabolicRootFactor
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (positiveRoots sigmaJ : Set D.Root) :
    standardLeviRootFactor D sigmaJ ≤
      standardParabolicRootFactor D positiveRoots sigmaJ := by
  apply RootSubgroupGenerated_mono D
  intro α hα
  rcases hα with hα | hα
  · exact Or.inl (Or.inr hα)
  · exact Or.inr hα

public lemma standardParabolicRootFactor_le_standardParabolicClosure
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (positiveRoots sigmaJ : Set D.Root) :
  standardParabolicRootFactor D positiveRoots sigmaJ ≤
      (standardParabolicClosure D positiveRoots sigmaJ).toSubgroup := by
  intro x hx
  change x ∈ closure
    (standardParabolicRootFactor D positiveRoots sigmaJ : Set (Variety.Point K))
  exact subset_closure hx

public lemma standardUnipotentRootFactor_le_standardParabolicClosure
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (positiveRoots sigmaJ : Set D.Root) :
    standardUnipotentRootFactor D positiveRoots sigmaJ ≤
      (standardParabolicClosure D positiveRoots sigmaJ).toSubgroup := by
  exact (standardUnipotentRootFactor_le_standardParabolicRootFactor D
    positiveRoots sigmaJ).trans
    (standardParabolicRootFactor_le_standardParabolicClosure D positiveRoots sigmaJ)

public lemma standardLeviRootFactor_le_standardParabolicClosure
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (positiveRoots sigmaJ : Set D.Root) :
    standardLeviRootFactor D sigmaJ ≤
      (standardParabolicClosure D positiveRoots sigmaJ).toSubgroup := by
  exact (standardLeviRootFactor_le_standardParabolicRootFactor D
    positiveRoots sigmaJ).trans
    (standardParabolicRootFactor_le_standardParabolicClosure D positiveRoots sigmaJ)

end

end Theory.AlgebraicGroup
