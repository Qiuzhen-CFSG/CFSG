module

public import Theory.AlgebraicGroup.Borel.RootStructure.theorem_1_11_3

/-!
This module isolates `theorem_1_11_4` from `Theory.AlgebraicGroup.Borel.RootStructure`.
It retains the declarations following that unresolved result up to the next
unresolved result, preserving the source order and public API of the GLS3
algebraic-group development.
-/

set_option warningAsError false

universe u v w

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem theorem_1_11_4
    {K : Variety k} [AlgebraicGroup K]
    (hK : IsReductiveAlgebraicGroup K)
    (B₀ B₁ U₀ U₁ : ClosedSubgroup K)
    (hB₀ : IsBorelSubgroup B₀) (hB₁ : IsBorelSubgroup B₁)
    (hU₀ : IsUnipotentRadicalOf B₀ U₀)
    (hU₁ : IsUnipotentRadicalOf B₁ U₁) :
    IsUnipotentRadicalOf (B₀.inter B₁) (U₀.inter U₁) ∧
    Nonempty (BorelIntersectionDecomposition B₀ B₁ U₀ U₁) ∧
    (∀ (I : BorelIntersectionDecomposition B₀ B₁ U₀ U₁)
      (D : RootGroupData K I.torus), D.IsRealization →
      ∀ positive₀ positive₁ : Set D.Root,
        IsPositiveSystem D positive₀ → IsPositiveSystem D positive₁ →
        U₀.toSubgroup = RootSubgroupGenerated D positive₀ →
        U₁.toSubgroup = RootSubgroupGenerated D positive₁ →
        (U₀.inter U₁).toSubgroup =
          RootSubgroupGenerated D (positive₀ ∩ positive₁)) ∧
    (∃ B₁' : {B : ClosedSubgroup K // IsBorelSubgroup B},
      IsMaximalTorus (B₀.inter B₁'.1)) := by sorry

public def BruhatRootSet
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (positiveRoots : Set D.Root)
    {ι X Y : Type u} [Finite ι] [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing ι ℤ X Y) (e : D.Root ≃ ι)
    (w : P.weylGroup) : Set D.Root :=
  {α | α ∈ positiveRoots ∧
      e.symm (P.weylGroupToPerm w (e α)) ∉ positiveRoots}

public noncomputable def normalizerWeylClass
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    {ι X Y : Type u} [Finite ι] [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing ι ℤ X Y)
    (weylMap : T.normalizer.toSubgroup →* P.weylGroup)
    (n : T.normalizer.toSubgroup) : P.weylGroup :=
  weylMap n

public def MapsBaseToNegative
    {ι X Y : Type u} [Finite ι] [AddCommGroup X] [AddCommGroup Y]
    {P : RootPairing ι ℤ X Y} (base : P.Base) (w₀ : P.weylGroup) : Prop :=
  P.weylGroupToPerm w₀ '' (base.support : Set ι) =
    (fun i => P.reflectionPerm i i) '' (base.support : Set ι)

public structure BruhatNormalForm
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (positiveRoots : Set D.Root)
    (Uplus : ClosedSubgroup K)
    {ι X Y : Type u} [Finite ι] [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing ι ℤ X Y) (e : D.Root ≃ ι)
    (weylMap : T.normalizer.toSubgroup →* P.weylGroup) where
  u : Variety.Point K
  u_mem : u ∈ Uplus.toSubgroup
  n : T.normalizer.toSubgroup
  v : Variety.Point K
  v_mem : v ∈ RootSubgroupGenerated D
    (BruhatRootSet D positiveRoots P e
        (normalizerWeylClass T P weylMap n))

@[expose]
public noncomputable def sourceFundamentalCorootWord
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (C : ChevalleyData K D)
    {ι R M N : Type*} [Finite ι] [Field R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} (base : P.Base) (e : D.Root ≃ ι)
    (parameters : base.support → kˣ) : Variety.Point K :=
  (base.support.attach.toList.map fun i : base.support =>
    C.h (e.symm i) (parameters i)).prod

public theorem sourceFundamentalCorootWord_eq
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (C : ChevalleyData K D)
    {ι R M N : Type*} [Finite ι] [Field R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} (base : P.Base) (e : D.Root ≃ ι)
    (parameters : base.support → kˣ) :
    sourceFundamentalCorootWord C base e parameters =
      (base.support.attach.toList.map fun i : base.support =>
        C.h (e.symm i) (parameters i)).prod := rfl

public structure SourceReflectionRelations
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D) where
  sign : D.Root → D.Root → kˣ
  sign_is_unit_sign : ∀ α β, sign α β = 1 ∨ sign α β = -1
  conjugates_root_elements :
    ∀ α β t, (C.n β 1)⁻¹ * C.x α t * C.n β 1 =
      C.x (D.reflect β α) ((sign α β : k) * t)
  conjugates_coroots :
    ∀ α β t, (C.n β 1)⁻¹ * C.h α t * C.n β 1 =
      C.h (D.reflect β α) t
  conjugates_normalizer_words :
    ∀ α β t, (C.n β 1)⁻¹ * C.n α t * C.n β 1 =
      C.n (D.reflect β α) (sign α β * t)

public structure SourceChevalleyRelations
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base) : Prop where
  parametrizes_root_subgroups :
    ∀ α, Function.Injective (C.x α) ∧ Set.range (C.x α) = D.rootSubgroup α
  normalizer_word :
    ∀ α t, C.n α t =
      C.x α t * C.x (D.neg α) (-((t : k)⁻¹)) * C.x α t
  coroot_word :
    ∀ α t, C.h α t = (C.n α 1)⁻¹ * C.n α t
  torus_generated_by_coroots :
    T.toSubgroup = Subgroup.closure {g | ∃ α t, g = C.h α t}
  root_addition :
    ∀ α t u, C.x α t * C.x α u = C.x α (t + u)
  commutator_formula :
    ∀ α β, AreLinearlyIndependentRoots D P e α β →
      ∃ order : List (ChevalleyCommutatorTerm D.Root),
      ∃ coefficient : ChevalleyCommutatorTerm D.Root → k,
        order.Nodup ∧
        order.Pairwise (fun q r => q.i + q.j ≤ r.i + r.j) ∧
        (∀ q, q ∈ order ↔
          IsValidChevalleyCommutatorTerm D P e α β q) ∧
        (∀ q ∈ order,
          HasExpectedChevalleyCoefficient D P e α β q (coefficient q)) ∧
        ∀ t u,
          (C.x α t)⁻¹ * (C.x β u)⁻¹ * C.x α t * C.x β u =
            (order.map fun q =>
              C.x q.root (coefficient q * t ^ q.i * u ^ q.j)).prod
  coroots_commute :
    ∀ α β t u, C.h α t * C.h β u = C.h β u * C.h α t
  coroot_multiplication :
    ∀ α t u, C.h α t * C.h α u = C.h α (t * u)
  coroot_expansion :
    ∃ coefficient : D.Root → base.support → ℤ,
      (∀ α, P.coroot (e α) =
        ∑ i, coefficient α i • P.coroot i) ∧
      ∀ α t, C.h α t =
        sourceFundamentalCorootWord C base e (fun i => t ^ coefficient α i)
  universal_coroot_independence :
    IsUniversalVersion K →
      ∀ parameters : base.support → kˣ,
        sourceFundamentalCorootWord C base e parameters = 1 ↔
          ∀ i, parameters i = 1
  adjoint_coroot_relations :
    IsAdjointVersion K →
      ∀ parameters : base.support → kˣ,
        sourceFundamentalCorootWord C base e parameters = 1 ↔
          ∀ j,
            (base.support.attach.toList.map fun i : base.support =>
              parameters i ^ D.pairing (e.symm j) (e.symm i)).prod = 1
  general_coroot_relations :
    ∃ weights : base.support → TorusWeight T,
      Set.range D.rootWeight ⊆ Subgroup.closure (Set.range weights) ∧
      ∀ parameters : base.support → kˣ,
        sourceFundamentalCorootWord C base e parameters = 1 ↔
          ∀ j,
            (base.support.attach.toList.map fun i : base.support =>
              parameters i ^ D.weightPairing (weights j) (e.symm i)).prod = 1
  torus_conjugates_root_elements :
    ∀ α β t u, (C.h β u)⁻¹ * C.x α t * C.h β u =
      C.x α ((u : k) ^ D.pairing α β * t)
  reflection_relations : Nonempty (SourceReflectionRelations D C)
  normalizer_square :
    ∀ α, C.n α 1 * C.n α 1 = C.h α (-1)

end Theory.AlgebraicGroup
