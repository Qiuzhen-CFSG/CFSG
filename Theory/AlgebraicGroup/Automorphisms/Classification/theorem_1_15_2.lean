module

public import Theory.AlgebraicGroup.Automorphisms.Classification.GraphAutomorphismCore

/-!
This module isolates GLS3 `theorem_1_15_2` as a proof target and retains the
following Steinberg automorphism interfaces.  Its graph-automorphism input API
lives in `GraphAutomorphismCore`, so the target declaration can be checked and
proved without exposing unrelated source text.
-/

set_option warningAsError false

universe u v w

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]


public theorem theorem_1_15_2
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (hK : IsSemisimpleAlgebraicGroup K)
    (D : RootGroupData K T) (C : ChevalleyData K D)
    (setup : GraphChevalleyRootSystem D C) :
    Nonempty (GraphAutomorphismClassification hK D C setup) := by sorry

public structure SteinbergChevalleyRootSystem
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D) where
  isMaximalTorus : IsMaximalTorus T
  realizesRootGroups : D.IsRealization
  ι : Type u
  E : Type u
  E' : Type u
  [finiteRoot : Finite ι]
  [addCommGroupWeight : AddCommGroup E]
  [weightSpace : Module ℝ E]
  [addCommGroupCoweight : AddCommGroup E']
  [coweightSpace : Module ℝ E']
  pairing : RootPairing ι ℝ E E'
  [isRootSystem : pairing.IsRootSystem]
  [isCrystallographic : pairing.IsCrystallographic]
  [isReduced : pairing.IsReduced]
  rootEquiv : D.Root ≃ ι
  base : pairing.Base
  realizesRoots : IsRootSystemRealization D pairing rootEquiv base
  isChevalleySystem : IsChevalleySystem D C pairing rootEquiv base
  rootGeneration : HasChevalleyRootGeneration D C

attribute [instance]
  SteinbergChevalleyRootSystem.finiteRoot
  SteinbergChevalleyRootSystem.addCommGroupWeight
  SteinbergChevalleyRootSystem.weightSpace
  SteinbergChevalleyRootSystem.addCommGroupCoweight
  SteinbergChevalleyRootSystem.coweightSpace
  SteinbergChevalleyRootSystem.isRootSystem
  SteinbergChevalleyRootSystem.isCrystallographic
  SteinbergChevalleyRootSystem.isReduced

public structure FrobeniusAutomorphismFamily
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D) where
  scalarSystem : FrobeniusScalarSystem (k := k) (ringChar k)
  automorphism : ℤ → Aut K
  formula : ∀ a α t,
    automorphism a (C.x α t) = C.x α (scalarSystem.scalar a t)
  map_zero : automorphism 0 = 1
  map_add : ∀ a b, automorphism (a + b) = automorphism a * automorphism b

public def HasAlgebraicEndomorphismRealization
    {K : Variety k} [AlgebraicGroup K] (σ : Aut K) : Prop :=
  ∃ f : AlgebraicEndomorphism K, IsAlgebraicRealization σ f

public def IsAnglePreservingLengthChangingRootBijection
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (ρ : Equiv.Perm D.Root) : Prop :=
  (∀ α, α ∈ D.simple ↔ ρ α ∈ D.simple) ∧
  (∀ α, α ∈ D.positive ↔ ρ α ∈ D.positive) ∧
  (∀ α, IsLongRoot D α ↔ IsShortRoot D (ρ α)) ∧
  (∀ α, IsShortRoot D α ↔ IsLongRoot D (ρ α)) ∧
  ∀ α β,
    D.pairing (ρ α) (ρ β) * D.pairing (ρ β) (ρ α) =
      D.pairing α β * D.pairing β α

public def IsExceptionalGraphFieldFormula
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    (family : FrobeniusAutomorphismFamily D C)
    (ρ : Equiv.Perm D.Root) (ψ : Aut K) : Prop :=
  (∀ α, IsLongRoot D α → ∀ t,
      ψ (C.x α t) = C.x (ρ α) t) ∧
  ∀ α, IsShortRoot D α → ∀ t,
      ψ (C.x α t) = C.x (ρ α) (family.scalarSystem.scalar 1 t)

public def RootGroupData.HasDynkinClassificationForSteinberg
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (classification : RootClassification) : Prop :=
  Nonempty
    {e : D.simple ≃ Fin classification.rank //
      ∀ i j, D.pairing i.1 j.1 =
        dynkinCartanEntry classification (e i) (e j)}

end Theory.AlgebraicGroup
