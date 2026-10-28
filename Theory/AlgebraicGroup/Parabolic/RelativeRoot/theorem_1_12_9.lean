module

public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.CentralSeriesCore

/-!
This module contains the height-filtration statement of GLS3 Theorem 1.12.9
and the standard parabolic and Levi candidates used in Section 1.13.  The
candidates are Zariski closures of the torus together with their prescribed
root factors.  Their public specification theorems express those generators as
subgroup joins using `Subgroup.sup_eq_closure`; in particular, the
specifications are definitional and require no ambient root-generation theorem.
The normalizer-part and aligned-Borel specifications also export their exact
defining formulas without exposing implementation bodies.  These API lemmas
are proved by reflexivity and do not depend on the height-filtration theorem.
-/

set_option warningAsError false

universe u v w

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]


public theorem theorem_1_12_9
    {K : Variety k} [AlgebraicGroup K]
    (hK : IsSimpleAlgebraicGroup K)
    (T : ClosedSubgroup K) (D : RootGroupData K T)
    (positiveRoots : Set D.Root) (B U : ClosedSubgroup K)
    (_S : RootHeightBorelSetup T D positiveRoots B U) :
    (∀ i, 0 < i →
      IsZariskiClosed K (rootHeightSubgroup D i : Set (Variety.Point K))) ∧
    (∀ i, 0 < i → rootHeightSubgroup D i ≤ U.toSubgroup) ∧
    (∀ i, 0 < i →
      ((rootHeightSubgroup D i).subgroupOf U.toSubgroup).Normal) ∧
    rootHeightSubgroup D 1 = U.toSubgroup ∧
    (∀ i, 0 < i → rootHeightSubgroup D (i + 1) ≤ rootHeightSubgroup D i) ∧
    (∀ i, 0 < i →
      ⁅rootHeightSubgroup D i, U.toSubgroup⁆ ≤
        rootHeightSubgroup D (i + 1)) ∧
    (∀ {ii R M N : Type*} [Finite ii] [Field R] [CharZero R]
      [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
      (P : RootPairing ii R M N) [P.IsRootSystem]
      [P.IsCrystallographic] [P.IsReduced]
      (e : D.Root ≃ ii) (base : P.Base)
      (_hActual : IsRootSystemRealization D P e base)
      (_hPositive : ∀ α, α ∈ positiveRoots ↔ base.IsPos (e α))
      (classification : RootClassification)
      (_hType : HasDynkinType P classification)
      (_hNonsingular : ¬ IsUSingular classification (ringChar k)),
      ∀ i, rootHeightSubgroup D (i + 1) = ambientLowerCentralSeries U i) ∧
    (∀ {ii R M N : Type*} [Finite ii] [Field R] [CharZero R]
      [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
      (P : RootPairing ii R M N) [P.IsRootSystem]
      [P.IsCrystallographic] [P.IsReduced]
      (e : D.Root ≃ ii) (base : P.Base)
      (_hActual : IsRootSystemRealization D P e base)
      (_hPositive : ∀ α, α ∈ positiveRoots ↔ base.IsPos (e α))
      (classification : RootClassification)
      (_hType : HasDynkinType P classification)
      (_hNonsingular : ¬ IsUSingular classification (ringChar k))
      (lowestRoot : D.Root) (_hLowest : IsLowestRoot D positiveRoots lowestRoot)
      (c : ℕ) (_hc : (c : ℤ) = D.height (D.neg lowestRoot)),
      ∀ i, i ≤ c →
        ambientUpperCentralSeries U i = rootHeightSubgroup D (c + 1 - i)) ∧
    (∀ lowestRoot, IsLowestRoot D positiveRoots lowestRoot →
      (D.rootSubgroup (D.neg lowestRoot)).toSubgroup ≤ ambientCenter U) ∧
    (∀ lowestRoot, IsLowestRoot D positiveRoots lowestRoot →
      ∃ c : ℕ, (c : ℤ) = D.height (D.neg lowestRoot) ∧
        Group.nilpotencyClass U.toSubgroup ≤ c) ∧
    (∀ {ii R M N : Type*} [Finite ii] [Field R] [CharZero R]
      [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
      (P : RootPairing ii R M N) [P.IsRootSystem]
      [P.IsCrystallographic] [P.IsReduced]
      (e : D.Root ≃ ii) (base : P.Base)
      (_hActual : IsRootSystemRealization D P e base)
      (_hPositive : ∀ α, α ∈ positiveRoots ↔ base.IsPos (e α))
      (classification : RootClassification)
      (_hType : HasDynkinType P classification)
      (_hNonsingular : ¬ IsUSingular classification (ringChar k))
      (lowestRoot : D.Root) (_hLowest : IsLowestRoot D positiveRoots lowestRoot),
      ambientCenter U = (D.rootSubgroup (D.neg lowestRoot)).toSubgroup) ∧
    (∀ {ii R M N : Type*} [Finite ii] [Field R] [CharZero R]
      [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
      (P : RootPairing ii R M N) [P.IsRootSystem]
      [P.IsCrystallographic] [P.IsReduced]
      (e : D.Root ≃ ii) (base : P.Base)
      (_hActual : IsRootSystemRealization D P e base)
      (_hPositive : ∀ α, α ∈ positiveRoots ↔ base.IsPos (e α))
      (classification : RootClassification)
      (_hType : HasDynkinType P classification)
      (_hNonsingular : ¬ IsUSingular classification (ringChar k))
      (lowestRoot : D.Root) (_hLowest : IsLowestRoot D positiveRoots lowestRoot)
      (c : ℕ) (_hc : (c : ℤ) = D.height (D.neg lowestRoot)),
      Group.nilpotencyClass U.toSubgroup = c) := by sorry

public noncomputable def parabolicCandidate
    {K : Variety k} [AlgebraicGroup K]
    (T : ClosedSubgroup K) (D : RootGroupData K T)
    (positiveRoots J : Set D.Root) : ClosedSubgroup K :=
  subgroupZariskiClosure K
    (Subgroup.closure
      ((T : Set (Variety.Point K)) ∪
        standardParabolicRootFactor D positiveRoots (RootSubsystemSpan D J)))

omit [IsAlgClosed k] in
/-- The standard parabolic candidate is unconditionally the Zariski closure of
the join of its torus and parabolic root factor. -/
public theorem parabolicCandidate_spec
    {K : Variety k} [AlgebraicGroup K]
    (T : ClosedSubgroup K) (D : RootGroupData K T)
    (positiveRoots J : Set D.Root) :
    parabolicCandidate T D positiveRoots J =
      subgroupZariskiClosure K
        (T.toSubgroup ⊔
          standardParabolicRootFactor D positiveRoots
            (RootSubsystemSpan D J)) := by
  rw [parabolicCandidate, Subgroup.sup_eq_closure]
  rfl

public noncomputable def leviCandidate
    {K : Variety k} [AlgebraicGroup K]
    (T : ClosedSubgroup K) (D : RootGroupData K T)
    (J : Set D.Root) : ClosedSubgroup K :=
  subgroupZariskiClosure K
    (Subgroup.closure
      ((T : Set (Variety.Point K)) ∪
        standardLeviRootFactor D (RootSubsystemSpan D J)))

omit [IsAlgClosed k] in
/-- The standard Levi candidate is unconditionally the Zariski closure of the
join of its torus and Levi root factor. -/
public theorem leviCandidate_spec
    {K : Variety k} [AlgebraicGroup K]
    (T : ClosedSubgroup K) (D : RootGroupData K T)
    (J : Set D.Root) :
    leviCandidate T D J =
      subgroupZariskiClosure K
        (T.toSubgroup ⊔
          standardLeviRootFactor D (RootSubsystemSpan D J)) := by
  rw [leviCandidate, Subgroup.sup_eq_closure]
  rfl

public noncomputable def parabolicNormalizerPart
    {K : Variety k} [AlgebraicGroup K]
    (T : ClosedSubgroup K) (D : RootGroupData K T)
    (J : Set D.Root) : ClosedSubgroup K :=
  T.normalizer.inter (leviCandidate T D J)

public theorem parabolicNormalizerPart_spec
    {K : Variety k} [AlgebraicGroup K]
    (T : ClosedSubgroup K) (D : RootGroupData K T)
    (roots : Set D.Root) :
    parabolicNormalizerPart T D roots =
      T.normalizer.inter (leviCandidate T D roots) := by
  rfl

public def IsAlignedStandardBorelSetup
    {K : Variety k} [AlgebraicGroup K]
    (T B : ClosedSubgroup K) (D : RootGroupData K T)
    (positiveRoots : Set D.Root) : Prop :=
  IsStandardBorelSetup T B D positiveRoots ∧
    B = subgroupZariskiClosure K
      (Subgroup.closure
        ((T : Set (Variety.Point K)) ∪
          standardUnipotentRootFactor D positiveRoots ∅))

public theorem isAlignedStandardBorelSetup_spec
    {K : Variety k} [AlgebraicGroup K]
    (T B : ClosedSubgroup K) (D : RootGroupData K T)
    (positiveRoots : Set D.Root) :
    IsAlignedStandardBorelSetup T B D positiveRoots ↔
      IsStandardBorelSetup T B D positiveRoots ∧
        B = subgroupZariskiClosure K
          (Subgroup.closure
            ((T : Set (Variety.Point K)) ∪
              standardUnipotentRootFactor D positiveRoots ∅)) := by
  rfl

end Theory.AlgebraicGroup
