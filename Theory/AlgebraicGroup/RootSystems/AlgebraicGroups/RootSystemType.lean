module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.ChevalleyVersions
public import Theory.AlgebraicGroup.RootSystems.Dynkin

/-!
This module provides the reusable root-system-type contract for an algebraic
group.  `HasRootSystemType` is the source-faithful existential packaging of a
maximal torus, its realized root-group datum, and a based root pairing with a
specified Dynkin type.  The conversion theorems below package and unpack the
same data as a `RootSystemModel`; the existentially stored algebraic and
root-system instances are passed through unchanged.  This is the model API
used by the later GLS3 Section 1.10 constructions, and is independent of the
numbered isogeny and version-classification theorems.  The contract follows
the maximal-torus/root-data setup of GLS3, Definitions 1.9.1--1.9.5; the
conversion itself is only structure projection and reconstruction.
-/

universe u v w

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A group has the indicated root-system type when one of its maximal tori
and realized root data identify with a based root pairing of that type. -/
public def HasRootSystemType
    (G : Variety k) [AlgebraicGroup G]
    (classification : RootClassification) : Prop :=
  ∃ T : ClosedSubgroup G, IsMaximalTorus T ∧
  ∃ D : RootGroupData G T, D.IsRealization ∧
  ∃ ι M N : Type u,
  ∃ _ : Finite ι,
  ∃ _ : AddCommGroup M,
  ∃ _ : Module ℝ M,
  ∃ _ : AddCommGroup N,
  ∃ _ : Module ℝ N,
  ∃ P : RootPairing ι ℝ M N,
  ∃ _ : P.IsRootSystem,
  ∃ _ : P.IsCrystallographic,
  ∃ _ : P.IsReduced,
  ∃ base : P.Base,
  ∃ e : D.Root ≃ ι,
    IsActualBasedRootPairing D P base e ∧
      HasDynkinType P classification

/-- The existential form used by the model conversion API.  It intentionally
repeats the instance binders from `HasRootSystemType`: those binders are data
in the proposition and must not be reconstructed from global search. -/
public abbrev RootSystemModelWitness
    (G : Variety k) [AlgebraicGroup G]
    (classification : RootClassification) : Prop :=
  ∃ ι M N : Type u,
  ∃ _ : Finite ι,
  ∃ _ : AddCommGroup M,
  ∃ _ : Module ℝ M,
  ∃ _ : AddCommGroup N,
  ∃ _ : Module ℝ N,
  ∃ P : RootPairing ι ℝ M N,
  ∃ _ : P.IsRootSystem,
  ∃ _ : P.IsCrystallographic,
  ∃ _ : P.IsReduced,
  ∃ _model : RootSystemModel P G,
    HasDynkinType P classification

omit [IsAlgClosed k] in
/-- Construct a root-system-type witness from a stored root-system model. -/
public theorem hasRootSystemType_of_rootSystemModel
    {G : Variety k} [AlgebraicGroup G]
    (classification : RootClassification)
    {ι M N : Type u} [Finite ι]
    [AddCommGroup M] [Module ℝ M]
    [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (model : RootSystemModel P G)
    (hType : HasDynkinType P classification) :
    HasRootSystemType G classification := by
  exact ⟨model.torus, model.maximalTorus, model.rootData, model.realization,
    ι, M, N, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, P, inferInstance, inferInstance,
    inferInstance, model.base, model.rootEquiv, model.actual, hType⟩

omit [IsAlgClosed k] in
/-- A short namespace-qualified spelling is convenient at construction sites. -/
public theorem HasRootSystemType.of_rootSystemModel
    {G : Variety k} [AlgebraicGroup G]
    (classification : RootClassification)
    {ι M N : Type u} [Finite ι]
    [AddCommGroup M] [Module ℝ M]
    [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (model : RootSystemModel P G)
    (hType : HasDynkinType P classification) :
    HasRootSystemType G classification :=
  hasRootSystemType_of_rootSystemModel classification P model hType

omit [IsAlgClosed k] in
public theorem hasRootSystemType_of_model
    {G : Variety k} [AlgebraicGroup G]
    {classification : RootClassification}
    {ι M N : Type u} [Finite ι]
    [AddCommGroup M] [Module ℝ M]
    [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (model : RootSystemModel P G)
    (hType : HasDynkinType P classification) :
    HasRootSystemType G classification :=
  hasRootSystemType_of_rootSystemModel classification P model hType

omit [IsAlgClosed k] in
public theorem HasRootSystemType.of_model
    {G : Variety k} [AlgebraicGroup G]
    {classification : RootClassification}
    {ι M N : Type u} [Finite ι]
    [AddCommGroup M] [Module ℝ M]
    [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (model : RootSystemModel P G)
    (hType : HasDynkinType P classification) :
    HasRootSystemType G classification :=
  hasRootSystemType_of_rootSystemModel classification P model hType

omit [IsAlgClosed k] in
/-- Unpack a root-system-type witness into the same data with a
`RootSystemModel` carrying the original maximal torus and realization. -/
public theorem HasRootSystemType.exists_rootSystemModel
    {G : Variety k} [AlgebraicGroup G]
    (classification : RootClassification)
    (h : HasRootSystemType G classification) :
    RootSystemModelWitness G classification := by
  rcases h with ⟨T, hT, D, hD, ι, M, N, hι, hM, hmodM, hN, hmodN, P,
    hroot, hcrys, hred, base, e, hactual, hType⟩
  let model : RootSystemModel P G :=
    { torus := T
      maximalTorus := hT
      rootData := D
      realization := hD
      base := base
      rootEquiv := e
      actual := hactual }
  exact ⟨ι, M, N, hι, hM, hmodM, hN, hmodN, P, hroot, hcrys, hred,
    model, hType⟩

omit [IsAlgClosed k] in
public theorem HasRootSystemType.to_rootSystemModel
    {G : Variety k} [AlgebraicGroup G]
    (classification : RootClassification)
    (h : HasRootSystemType G classification) :
    RootSystemModelWitness G classification :=
  HasRootSystemType.exists_rootSystemModel classification h

omit [IsAlgClosed k] in
public theorem HasRootSystemType.exists_model
    {G : Variety k} [AlgebraicGroup G]
    {classification : RootClassification}
    (h : HasRootSystemType G classification) :
    RootSystemModelWitness G classification :=
  HasRootSystemType.exists_rootSystemModel classification h

omit [IsAlgClosed k] in
/-- The model witness and the original root-system-type contract are
interchangeable. -/
public theorem hasRootSystemType_iff_rootSystemModelWitness
    {G : Variety k} [AlgebraicGroup G]
    (classification : RootClassification) :
    HasRootSystemType G classification ↔ RootSystemModelWitness G classification := by
  constructor
  · exact HasRootSystemType.exists_rootSystemModel classification
  · intro h
    rcases h with ⟨ι, M, N, hι, hM, hmodM, hN, hmodN, P,
      hroot, hcrys, hred, model, hType⟩
    exact ⟨model.torus, model.maximalTorus, model.rootData,
      model.realization, ι, M, N, hι, hM, hmodM, hN, hmodN, P,
      hroot, hcrys, hred, model.base, model.rootEquiv,
      model.actual, hType⟩

omit [IsAlgClosed k] in
public theorem hasRootSystemType_iff_exists_rootSystemModel
    {G : Variety k} [AlgebraicGroup G]
    (classification : RootClassification) :
    HasRootSystemType G classification ↔
      (∃ ι M N : Type u,
        ∃ _ : Finite ι,
        ∃ _ : AddCommGroup M,
        ∃ _ : Module ℝ M,
        ∃ _ : AddCommGroup N,
        ∃ _ : Module ℝ N,
        ∃ P : RootPairing ι ℝ M N,
        ∃ _ : P.IsRootSystem,
        ∃ _ : P.IsCrystallographic,
        ∃ _ : P.IsReduced,
        ∃ _model : RootSystemModel P G,
          HasDynkinType P classification) :=
  hasRootSystemType_iff_rootSystemModelWitness classification

omit [IsAlgClosed k] in
public theorem HasRootSystemType.iff_exists_model
    {G : Variety k} [AlgebraicGroup G]
    (classification : RootClassification) :
    HasRootSystemType G classification ↔ RootSystemModelWitness G classification :=
  hasRootSystemType_iff_rootSystemModelWitness classification

end Theory.AlgebraicGroup
