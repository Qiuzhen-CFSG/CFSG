module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.ChevalleyVersions
public import Theory.AlgebraicGroup.RootData.Chevalley
public import Theory.AlgebraicGroup.Morphism.Reconstruction

universe u

set_option linter.style.haveILetI false

/-!
This module is the lower-layer realization endpoint for an integral map of
root data.  A root-pairing map by itself is discrete data: it does not provide
a point-group homomorphism, nor does it prove that the corresponding map of
coordinate rings descends from a presentation.  The structure below records
exactly those two geometric certificates together with the Chevalley
generator transport and the integral root-index transport.  The reconstruction
lemma then turns the certificate into a regular algebraic-group morphism.

The resulting morphism is an isogeny whenever the supplied point map is
surjective with finite kernel.  Generator agreement gives uniqueness by the
presentation certificate, hence applies unchanged to connected and derived
semisimple carriers.  No universal-version predicate is strengthened here;
the construction is independent of the unresolved numbered realization
theorems.
-/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/--
Certificate data for realizing an integral root-datum map by a regular group
morphism.

`latticeMap` is normally instantiated over `ℤ`; its `indexEquiv` records the
root transport on the chosen root-pairing models.  The two coordinate fields
are the descent datum needed by `Morphism.exists_of_pointHom_of_polynomialFunctionAlgHom`.
The final field is the presentation-side uniqueness statement: the chosen
Chevalley root generators determine a point-group homomorphism.
-/
public structure RootDatumMorphismRealizationData
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    {TG : ClosedSubgroup G} {TH : ClosedSubgroup H}
    {DG : RootGroupData G TG} {DH : RootGroupData H TH}
    (CG : ChevalleyData G DG) (CH : ChevalleyData H DH)
    {ι ι' R X Y X' Y' : Type*} [Finite ι] [Finite ι'] [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [AddCommGroup X'] [Module R X'] [AddCommGroup Y'] [Module R Y']
    (P : RootPairing ι R X Y) (Q : RootPairing ι' R X' Y') where
  /-- Integral character/cocharacter lattice map and its root-index map. -/
  latticeMap : RootPairing.Hom P Q
  sourceRootIndex : DG.Root ≃ ι
  targetRootIndex : DH.Root ≃ ι'
  rootIndex : DG.Root ≃ DH.Root
  /-- The chosen actual-root transport is the lattice-map index transport. -/
  rootIndex_index : ∀ α,
    targetRootIndex (rootIndex α) = latticeMap.indexEquiv (sourceRootIndex α)
  /-- Reflection/Weyl transport on the chosen Chevalley roots. -/
  reflection_transport : ∀ α β,
    rootIndex (DG.reflect α β) = DH.reflect (rootIndex α) (rootIndex β)
  /-- The lattice-map index equivalence intertwines the Weyl reflections. -/
  weyl_transport : ∀ i j,
    latticeMap.indexEquiv (P.reflectionPerm i j) =
      Q.reflectionPerm (latticeMap.indexEquiv i) (latticeMap.indexEquiv j)
  /-- Simple roots remain integral root generators under the chosen transport. -/
  simple_root_transport : ∀ α, α ∈ DG.simple → rootIndex α ∈ DH.simple
  simple_root_transport_iff : ∀ α,
    α ∈ DG.simple ↔ rootIndex α ∈ DH.simple
  /-- Explicit positive-integral root multiple witness.  In the exact
  `RootPairing.Hom` presentation this witness is necessarily `1`; retaining
  it in the certificate makes the source's integral-root hypothesis visible
  to callers which use a rescaled target pairing. -/
  positive_root_multiple : ∀ α, ∃ n : ℕ, 0 < n ∧
    latticeMap.weightMap (P.root (sourceRootIndex α)) =
      (n : R) • Q.root (targetRootIndex (rootIndex α))
  /-- Point-group map supplied by the Chevalley presentation. -/
  pointHom : Variety.Point G →* Variety.Point H
  /-- Pullback on polynomial functions supplied by coordinate descent. -/
  coordinatePullback : Variety.PolynomialFunction H →ₐ[k]
    Variety.PolynomialFunction G
  /-- The pullback evaluates through the supplied point map. -/
  coordinate_spec : ∀ a y, coordinatePullback a y = a (pointHom y)
  /-- Reparametrization of each root-generator curve. -/
  rootParameterMap : DG.Root → k → k
  /-- Transport of every chosen root generator.  In characteristic zero this
  is usually a scalar reparametrization; in positive characteristic it may be
  the additive Frobenius polynomial forced by the positive root multiple. -/
  rootGenerator_transport : ∀ α t,
    pointHom (CG.x α t) = CH.x (rootIndex α) (rootParameterMap α t)
  /-- The parameter reparametrization is additive, as required by the root
  subgroup presentation. -/
  rootParameterMap_add : ∀ α t u,
    rootParameterMap α (t + u) = rootParameterMap α t + rootParameterMap α u
  /-- The point map is onto and has finite kernel. -/
  point_surjective : Function.Surjective pointHom
  kernel_finite : Finite pointHom.ker
  /-- Chevalley generators determine a point-group homomorphism uniquely. -/
  generator_determines : ∀ ψ₁ ψ₂ : Variety.Point G →* Variety.Point H,
    (∀ α t, ψ₁ (CG.x α t) = ψ₂ (CG.x α t)) → ψ₁ = ψ₂

/-- Exact root preservation yields the positive-integral root transport used in
the isogeny direction: the multiplier is `1`.  More general positive
integral multipliers are represented by choosing the correspondingly rescaled
target root pairing before forming `latticeMap`.
-/
public theorem RootDatumMorphismRealizationData.positiveIntegral_root_transport
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    {TG : ClosedSubgroup G} {TH : ClosedSubgroup H}
    {DG : RootGroupData G TG} {DH : RootGroupData H TH}
    {CG : ChevalleyData G DG} {CH : ChevalleyData H DH}
    {ι ι' R X Y X' Y' : Type*} [Finite ι] [Finite ι'] [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [AddCommGroup X'] [Module R X'] [AddCommGroup Y'] [Module R Y']
    {P : RootPairing ι R X Y} {Q : RootPairing ι' R X' Y'}
    (C : RootDatumMorphismRealizationData CG CH P Q) (α : DG.Root) :
    ∃ n : ℕ, 0 < n ∧
      C.latticeMap.weightMap (P.root (C.sourceRootIndex α)) =
        (n : R) • Q.root (C.targetRootIndex (C.rootIndex α)) := by
  exact C.positive_root_multiple α

namespace RootDatumMorphismRealizationData

variable {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
variable {TG : ClosedSubgroup G} {TH : ClosedSubgroup H}
variable {DG : RootGroupData G TG} {DH : RootGroupData H TH}
variable {CG : ChevalleyData G DG} {CH : ChevalleyData H DH}
variable {ι ι' R X Y X' Y' : Type*} [Finite ι] [Finite ι'] [CommRing R]
variable [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
variable [AddCommGroup X'] [Module R X'] [AddCommGroup Y'] [Module R Y']
variable {P : RootPairing ι R X Y} {Q : RootPairing ι' R X' Y'}

/-- Construct the regular algebraic-group morphism represented by a
root-datum realization certificate. -/
public theorem exists_morphism
    (C : RootDatumMorphismRealizationData CG CH P Q) :
    ∃ φ : AlgebraicGroup.Morphism G H, φ.onPoints = C.pointHom := by
  exact Morphism.exists_of_pointHom_of_polynomialFunctionAlgHom C.pointHom
    C.coordinatePullback C.coordinate_spec

/-- The morphism produced by a realization certificate is an isogeny. -/
public theorem exists_isogeny
    (C : RootDatumMorphismRealizationData CG CH P Q) :
    ∃ φ : AlgebraicGroup.Morphism G H,
      φ.onPoints = C.pointHom ∧ IsIsogeny φ := by
  obtain ⟨φ, hφ⟩ := C.exists_morphism
  refine ⟨φ, hφ, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [hφ] using C.point_surjective
  · simpa [AlgebraicGroup.Morphism.kernel, hφ] using C.kernel_finite

/-- The regular morphism transports the chosen Chevalley root generators. -/
public theorem exists_morphism_rootGenerator_transport
    (C : RootDatumMorphismRealizationData CG CH P Q) :
    ∃ φ : AlgebraicGroup.Morphism G H,
      φ.onPoints = C.pointHom ∧
        (∀ α t, φ.onPoints (CG.x α t) =
          CH.x (C.rootIndex α) (C.rootParameterMap α t)) := by
  obtain ⟨φ, hφ⟩ := C.exists_morphism
  refine ⟨φ, hφ, ?_⟩
  intro α t
  rw [hφ]
  exact C.rootGenerator_transport α t

/-- Uniqueness of a regular morphism from its values on Chevalley generators.

The statement is deliberately phrased without an additional connectedness
hypothesis: callers may apply it to connected or derived semisimple carriers,
while the actual uniqueness input is the presentation certificate.
-/
public theorem unique_of_generator_agreement
    (C : RootDatumMorphismRealizationData CG CH P Q)
    {φ ψ : AlgebraicGroup.Morphism G H}
    (hgen : ∀ α t, φ.onPoints (CG.x α t) = ψ.onPoints (CG.x α t)) :
    φ = ψ := by
  have hpoint : φ.onPoints = ψ.onPoints :=
    C.generator_determines φ.onPoints ψ.onPoints hgen
  apply AlgebraicGroup.Morphism.ext φ ψ
  funext x
  exact congrArg (fun f : Variety.Point G →* Variety.Point H => f x) hpoint

/-- The same uniqueness statement, named for its usual connected-carrier use. -/
public theorem unique_on_connected_of_generator_agreement
    (C : RootDatumMorphismRealizationData CG CH P Q)
    {φ ψ : AlgebraicGroup.Morphism G H}
    (_hconnected : IsConnected (Set.univ : Set (Variety.Point G)))
    (hgen : ∀ α t, φ.onPoints (CG.x α t) = ψ.onPoints (CG.x α t)) :
    φ = ψ := by
  exact C.unique_of_generator_agreement hgen

/-- The same uniqueness statement, named for its derived-carrier use.  A
derived semisimple carrier supplies the displayed generator certificate. -/
public theorem unique_on_derived_of_generator_agreement
    (C : RootDatumMorphismRealizationData CG CH P Q)
    {φ ψ : AlgebraicGroup.Morphism G H}
    (hgen : ∀ α t, φ.onPoints (CG.x α t) = ψ.onPoints (CG.x α t)) :
    φ = ψ := by
  exact C.unique_of_generator_agreement hgen

/-- Canonical interface name used by the root-system isogeny-lift layer. -/
public theorem rootDatumMorphism_of_realizationData
    (C : RootDatumMorphismRealizationData CG CH P Q) :
    ∃ φ : AlgebraicGroup.Morphism G H,
      φ.onPoints = C.pointHom ∧ IsIsogeny φ ∧
        (∀ α t, φ.onPoints (CG.x α t) =
          CH.x (C.rootIndex α) (C.rootParameterMap α t)) := by
  obtain ⟨φ, hpoint, hiso⟩ := C.exists_isogeny
  refine ⟨φ, hpoint, hiso, ?_⟩
  intro α t
  rw [hpoint]
  exact C.rootGenerator_transport α t

end RootDatumMorphismRealizationData

/-! Direct carrier aliases for callers which already hold
`RootSystemModel`s rather than `SemisimpleVersion`s. -/

public abbrev RootSystemModelMorphismRealizationData
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    {ι ι' E E' F F' : Type u} [Finite ι] [Finite ι']
    [AddCommGroup E] [Module ℝ E] [AddCommGroup E'] [Module ℝ E']
    [AddCommGroup F] [Module ℝ F] [AddCommGroup F'] [Module ℝ F']
    (P : RootPairing ι ℝ E E') [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (Q : RootPairing ι' ℝ F F') [Q.IsRootSystem]
    [Q.IsCrystallographic] [Q.IsReduced]
    (source : RootSystemModel P G)
    (target : RootSystemModel Q H)
    (sourceChevalley : ChevalleyData G source.rootData)
    (targetChevalley : ChevalleyData H target.rootData) :=
  RootDatumMorphismRealizationData sourceChevalley targetChevalley P Q

namespace RootSystemModel

variable {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
variable {ι ι' E E' F F' : Type u} [Finite ι] [Finite ι']
variable [AddCommGroup E] [Module ℝ E] [AddCommGroup E'] [Module ℝ E']
variable [AddCommGroup F] [Module ℝ F] [AddCommGroup F'] [Module ℝ F']
variable {P : RootPairing ι ℝ E E'} [P.IsRootSystem]
variable [P.IsCrystallographic] [P.IsReduced]
variable {Q : RootPairing ι' ℝ F F'} [Q.IsRootSystem]
variable [Q.IsCrystallographic] [Q.IsReduced]

public theorem rootDatumMorphism_of_realizationData
    (source : RootSystemModel P G) (target : RootSystemModel Q H)
    (sourceChevalley : ChevalleyData G source.rootData)
    (targetChevalley : ChevalleyData H target.rootData)
    (C : RootSystemModelMorphismRealizationData P Q source target
      sourceChevalley targetChevalley) :
    ∃ φ : AlgebraicGroup.Morphism G H,
      φ.onPoints = C.pointHom ∧ IsIsogeny φ ∧
        (∀ α t,
          φ.onPoints (sourceChevalley.x α t) =
            targetChevalley.x (C.rootIndex α) (C.rootParameterMap α t)) := by
  exact RootDatumMorphismRealizationData.rootDatumMorphism_of_realizationData C

end RootSystemModel

/-! A carrier-level alias for the semisimple-version layer.  The explicit
`letI` binders preserve the algebraic-group instances stored in each version. -/

public abbrev SemisimpleRootDatumMorphismRealizationData
    {ι ι' E E' F F' : Type u} [Finite ι] [Finite ι']
    [AddCommGroup E] [Module ℝ E] [AddCommGroup E'] [Module ℝ E']
    [AddCommGroup F] [Module ℝ F] [AddCommGroup F'] [Module ℝ F']
    (P : RootPairing ι ℝ E E') [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (Q : RootPairing ι' ℝ F F') [Q.IsRootSystem]
    [Q.IsCrystallographic] [Q.IsReduced]
    (source : SemisimpleVersion (k := k) P)
    (target : SemisimpleVersion (k := k) Q)
    (sourceChevalley :
      letI := source.group
      ChevalleyData source.carrier source.rootModel.rootData)
    (targetChevalley :
      letI := target.group
      ChevalleyData target.carrier target.rootModel.rootData) :=
  letI := source.group
  letI := target.group
  RootDatumMorphismRealizationData sourceChevalley targetChevalley P Q

namespace SemisimpleVersion

variable {ι ι' E E' F F' : Type u} [Finite ι] [Finite ι']
variable [AddCommGroup E] [Module ℝ E] [AddCommGroup E'] [Module ℝ E']
variable [AddCommGroup F] [Module ℝ F] [AddCommGroup F'] [Module ℝ F']
variable {P : RootPairing ι ℝ E E'} [P.IsRootSystem]
variable [P.IsCrystallographic] [P.IsReduced]
variable {Q : RootPairing ι' ℝ F F'} [Q.IsRootSystem]
variable [Q.IsCrystallographic] [Q.IsReduced]
variable {source : SemisimpleVersion (k := k) P}
variable {target : SemisimpleVersion (k := k) Q}

public theorem rootDatumMorphism_of_realizationData
    (sourceChevalley :
      letI := source.group
      ChevalleyData source.carrier source.rootModel.rootData)
    (targetChevalley :
      letI := target.group
      ChevalleyData target.carrier target.rootModel.rootData)
    (C : SemisimpleRootDatumMorphismRealizationData P Q source target
      sourceChevalley targetChevalley) :
    letI := source.group
    letI := target.group
    ∃ φ : AlgebraicGroup.Morphism source.carrier target.carrier,
      φ.onPoints = C.pointHom ∧ IsIsogeny φ ∧
        (∀ α t,
          φ.onPoints (sourceChevalley.x α t) =
            targetChevalley.x (C.rootIndex α) (C.rootParameterMap α t)) := by
  letI := source.group
  letI := target.group
  exact RootDatumMorphismRealizationData.rootDatumMorphism_of_realizationData C

end SemisimpleVersion

end Theory.AlgebraicGroup
