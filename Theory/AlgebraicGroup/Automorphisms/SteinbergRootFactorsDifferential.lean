module

public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.RingTheory.Nilpotent.Basic
public import Theory.AlgebraicGroup.Bor1.Differential
public import Theory.AlgebraicGroup.Borel.Defs
public import Theory.AlgebraicGroup.RootSubgroups.Defs
public import Theory.AlgebraicGroup.Morphism.Basic
public import Theory.AlgebraicGroup.Semisimple.Defs
public import Theory.AlgebraicGroup.Tori.Basic

/-!
# Steinberg root factors and the identity differential

This module isolates the differential step in GLS3, Chapter 2, [St2, 10.5].
The geometric root-space construction supplies a spanning family consisting of
the toral tangent directions and the positive and negative root directions.
When the corresponding coordinate factors are `X ^ (p ^ m)` with `m > 0`,
their derivatives at the identity vanish.  The transport equations in
`SteinbergRootTangentData` then force the identity differential to vanish on
that spanning family, hence everywhere.  The same result is applied to a
positive iterate and the differential-of-iterate formula gives nilpotence of
the original differential.

The decomposition and transport equations are explicit hypotheses here: the
surjective semisimple-group argument constructing them belongs to the
surrounding Steinberg fixed-point development.  No tangent-space decomposition
is currently exported by the root-subgroup modules, so this interface keeps
that geometric input separate from the formal linear-algebra bridge.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-! A positive root is represented by its root label together with membership
in the chosen positive system. -/

public abbrev PositiveRootIndex {K : Variety k} [AlgebraicGroup K]
    {T : ClosedSubgroup K} (D : RootGroupData K T) :=
  {α : D.Root // α ∈ D.positive}

omit [IsAlgClosed k] in
private lemma derivative_eval_zero_X_pow {n : ℕ} (hn : 1 < n) :
    (Polynomial.derivative (Polynomial.X ^ n : Polynomial k)).eval 0 = 0 := by
  rw [Polynomial.derivative_X_pow]
  simp [show n - 1 ≠ 0 by omega]

omit [IsAlgClosed k] in
private lemma one_lt_prime_pow (p m : ℕ) [Fact p.Prime] (hm : 0 < m) :
    1 < p ^ m := by
  exact Nat.one_lt_pow (Nat.ne_of_gt hm) (Fact.out : Nat.Prime p).one_lt

/-!
The tangent decomposition used by the Steinberg bridge.  `toralTangent` is a
chosen spanning family for the tangent space of the invariant torus,
`positiveTangent` and `negativeTangent` are the two signed root families, and
the transport equations express the differential on each family as the
derivative at the identity of its Frobenius factor.
-/

public structure SteinbergRootTangentData
    {K : Variety k} [AlgebraicGroup K]
    (B T : ClosedSubgroup K) (D : RootGroupData K T)
    (τ : Morphism K K) (ιT : Type*) (p m : ℕ) where
  semisimple : IsSemisimpleAlgebraicGroup K
  borel : IsBorelSubgroup B
  maximalTorus : IsMaximalTorus T
  torus_le_borel : T ≤ B
  surjective : Function.Surjective τ.onPoints
  torus_preserved :
    τ.onPoints '' (T : Set (Variety.Point K)) = (T : Set (Variety.Point K))
  toralTangent : ιT → Bor1.IdentityPointDerivation K
  positiveTangent : PositiveRootIndex D → Bor1.IdentityPointDerivation K
  negativeTangent : PositiveRootIndex D → Bor1.IdentityPointDerivation K
  toralFactor : ιT → Polynomial k
  positiveFactor : PositiveRootIndex D → Polynomial k
  negativeFactor : PositiveRootIndex D → Polynomial k
  span_top :
    Submodule.span k
        (Set.range toralTangent ∪
          Set.range positiveTangent ∪ Set.range negativeTangent) = ⊤
  toralFactor_eq : ∀ i, toralFactor i = Polynomial.X ^ (p ^ m)
  positiveFactor_eq : ∀ α, positiveFactor α = Polynomial.X ^ (p ^ m)
  negativeFactor_eq : ∀ α, negativeFactor α = Polynomial.X ^ (p ^ m)
  toral_transport : ∀ i,
    Bor1.identityTangentMorphismLinearMap τ (toralTangent i) =
      (toralFactor i).derivative.eval 0 • toralTangent i
  positive_transport : ∀ α,
    Bor1.identityTangentMorphismLinearMap τ (positiveTangent α) =
      (positiveFactor α).derivative.eval 0 • positiveTangent α
  negative_transport : ∀ α,
    Bor1.identityTangentMorphismLinearMap τ (negativeTangent α) =
      (negativeFactor α).derivative.eval 0 • negativeTangent α

omit [IsAlgClosed k] in
private theorem differential_mem_ker_of_toral
    {K : Variety k} [AlgebraicGroup K]
    {B T : ClosedSubgroup K} {D : RootGroupData K T}
    {τ : Morphism K K} {ιT : Type*} {p m : ℕ}
    (h : SteinbergRootTangentData B T D τ ιT p m)
    (hn : 1 < p ^ m) (i : ιT) :
    h.toralTangent i ∈
      LinearMap.ker (Bor1.identityTangentMorphismLinearMap τ) := by
  rw [LinearMap.mem_ker]
  rw [h.toral_transport i, h.toralFactor_eq i,
    derivative_eval_zero_X_pow hn, zero_smul]

omit [IsAlgClosed k] in
private theorem differential_mem_ker_of_positive
    {K : Variety k} [AlgebraicGroup K]
    {B T : ClosedSubgroup K} {D : RootGroupData K T}
    {τ : Morphism K K} {ιT : Type*} {p m : ℕ}
    (h : SteinbergRootTangentData B T D τ ιT p m)
    (hn : 1 < p ^ m) (α : PositiveRootIndex D) :
    h.positiveTangent α ∈
      LinearMap.ker (Bor1.identityTangentMorphismLinearMap τ) := by
  rw [LinearMap.mem_ker]
  rw [h.positive_transport α, h.positiveFactor_eq α,
    derivative_eval_zero_X_pow hn, zero_smul]

omit [IsAlgClosed k] in
private theorem differential_mem_ker_of_negative
    {K : Variety k} [AlgebraicGroup K]
    {B T : ClosedSubgroup K} {D : RootGroupData K T}
    {τ : Morphism K K} {ιT : Type*} {p m : ℕ}
    (h : SteinbergRootTangentData B T D τ ιT p m)
    (hn : 1 < p ^ m) (α : PositiveRootIndex D) :
    h.negativeTangent α ∈
      LinearMap.ker (Bor1.identityTangentMorphismLinearMap τ) := by
  rw [LinearMap.mem_ker]
  rw [h.negative_transport α, h.negativeFactor_eq α,
    derivative_eval_zero_X_pow hn, zero_smul]

/-! The root-factor equations kill the full identity differential. -/

omit [IsAlgClosed k] in
public theorem Bor1.identityTangentMorphismLinearMap_eq_zero_of_steinbergRootTangentData
    {K : Variety k} [AlgebraicGroup K]
    {B T : ClosedSubgroup K} {D : RootGroupData K T}
    {τ : Morphism K K} {ιT : Type*} {p m : ℕ}
    (h : SteinbergRootTangentData B T D τ ιT p m)
    (hn : 1 < p ^ m) :
    Bor1.identityTangentMorphismLinearMap τ = 0 := by
  apply LinearMap.ker_eq_top.mp
  apply top_unique
  rw [← h.span_top]
  apply Submodule.span_le.2
  intro v hv
  rcases hv with hv | hv
  · rcases hv with hv | hv
    · obtain ⟨i, rfl⟩ := hv
      exact differential_mem_ker_of_toral h hn i
    · obtain ⟨α, rfl⟩ := hv
      exact differential_mem_ker_of_positive h hn α
  · obtain ⟨α, rfl⟩ := hv
    exact differential_mem_ker_of_negative h hn α

omit [IsAlgClosed k] in
public theorem Bor1.identityTangentMorphismLinearMap_eq_zero_of_prime_frobenius_factors
    {K : Variety k} [AlgebraicGroup K]
    {B T : ClosedSubgroup K} {D : RootGroupData K T}
    {τ : Morphism K K} {ιT : Type*} {p m : ℕ}
    [Fact p.Prime] [CharP k p] (hm : 0 < m)
    (h : SteinbergRootTangentData B T D τ ιT p m) :
    Bor1.identityTangentMorphismLinearMap τ = 0 := by
  exact Bor1.identityTangentMorphismLinearMap_eq_zero_of_steinbergRootTangentData h
    (one_lt_prime_pow p m hm)

/-! Algebraic-group iterates are defined recursively so their differentials
can be compared directly with powers in `Module.End`. -/

public def Morphism.iterate {K : Variety k} [AlgebraicGroup K]
    (f : Morphism K K) : ℕ → Morphism K K
  | 0 => Morphism.id K
  | n + 1 => (Morphism.iterate f n).comp f

public theorem Bor1.identityTangentMorphismLinearMap_iterate
    {K : Variety k} [AlgebraicGroup K]
    (f : Morphism K K) (n : ℕ) :
    Bor1.identityTangentMorphismLinearMap (Morphism.iterate f n) =
      (Bor1.identityTangentMorphismLinearMap f) ^ n := by
  induction n with
  | zero =>
      rw [Morphism.iterate, Bor1.identityTangentMorphismLinearMap_id]
      exact Module.End.one_eq_id.symm
  | succ n ih =>
      rw [Morphism.iterate, Bor1.identityTangentMorphismLinearMap_comp, ih,
        pow_succ]
      apply LinearMap.ext
      intro x
      rw [LinearMap.comp_apply, Module.End.mul_apply]

/-! A zero differential on an iterate is exactly nilpotence of the original
differential. -/

public theorem isNilpotent_identityTangentMorphismLinearMap_of_iterate_eq_zero
    {K : Variety k} [AlgebraicGroup K]
    (f : Morphism K K) (n : ℕ)
    (hzero : Bor1.identityTangentMorphismLinearMap (Morphism.iterate f n) = 0) :
    IsNilpotent (Bor1.identityTangentMorphismLinearMap f) := by
  refine ⟨n, ?_⟩
  rw [← Bor1.identityTangentMorphismLinearMap_iterate f n]
  exact hzero

public theorem isNilpotent_identityTangentMorphismLinearMap_of_steinbergRootTangentData
    {K : Variety k} [AlgebraicGroup K]
    {B T : ClosedSubgroup K} {D : RootGroupData K T}
    {f : Morphism K K} {ιT : Type*} {p m n : ℕ}
    (h : SteinbergRootTangentData B T D (Morphism.iterate f n) ιT p m)
    (hn : 1 < p ^ m) :
    IsNilpotent (Bor1.identityTangentMorphismLinearMap f) := by
  apply isNilpotent_identityTangentMorphismLinearMap_of_iterate_eq_zero f n
  exact Bor1.identityTangentMorphismLinearMap_eq_zero_of_steinbergRootTangentData h hn

public theorem isNilpotent_identityTangentMorphismLinearMap_of_prime_frobenius_factors
    {K : Variety k} [AlgebraicGroup K]
    {B T : ClosedSubgroup K} {D : RootGroupData K T}
    {f : Morphism K K} {ιT : Type*} {p m n : ℕ}
    [Fact p.Prime] [CharP k p] (hm : 0 < m)
    (h : SteinbergRootTangentData B T D (Morphism.iterate f n) ιT p m) :
    IsNilpotent (Bor1.identityTangentMorphismLinearMap f) := by
  apply isNilpotent_identityTangentMorphismLinearMap_of_iterate_eq_zero f n
  exact Bor1.identityTangentMorphismLinearMap_eq_zero_of_prime_frobenius_factors hm h

end Theory.AlgebraicGroup
