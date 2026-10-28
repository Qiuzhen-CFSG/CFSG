module

public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.theorem_1_13_2
public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.LayerQuotientModel

/-!
This module isolates `theorem_1_13_3` from `Theory.AlgebraicGroup.Parabolic.RelativeRoot`.
It retains the declarations following that unresolved result up to the next
unresolved result, preserving the source order and public API of the GLS3
algebraic-group development.

The source theorem indexes standard parabolics by the fundamental roots of the
chosen positive system.  `D.simple`, however, is the simple-root set attached
to `D.positive`; `IsStandardBorelSetup` certifies that `positiveRoots` is a
positive system but does not align it with `D.positive`.  The explicit equality
below records that alignment.

The root-addition completeness clause is now part of `IsStandardBorelSetup`.
The base realization predicate constrains successful values of `D.add`, but does
not say that every sum of actual roots is represented.  Completeness makes the
stored decomposition test exhaustive, while the explicit actual based pairing
below identifies `D.simple` with a genuine finite reduced crystallographic
root-system base.  These are structural inputs used by standard positive-root
collection and do not assume any conclusion of the Levi decomposition.  The
imported lower-level setup also stores exact root-addition realizations for its
integral and rational models and derives the same completeness fact from the
integral actual-root identification. The adjacent-layer quotient model is
maintained in a clean lower module and re-exported here for compatibility.
-/

set_option warningAsError false

universe u v w

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem theorem_1_13_3
    {K : Variety k} [AlgebraicGroup K]
    (hK : IsReductiveAlgebraicGroup K)
    (T B : ClosedSubgroup K) (D : RootGroupData K T)
    {ι : Type v} {E E' : Type w} [Finite ι]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup E'] [Module ℝ E']
    (P : RootPairing ι ℝ E E') [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (rootEquiv : D.Root ≃ ι)
    (actualRootPairing : IsActualBasedRootPairing D P base rootEquiv)
    (positiveRoots : Set D.Root)
    (hSetup : IsStandardBorelSetup T B D positiveRoots)
    (positiveRoots_actual : positiveRoots = D.positive) :
    (∀ J : Set D.Root, J ⊆ D.simple →
      (∀ x : Variety.Point K,
        x ∈ parabolicCandidate T D positiveRoots J ↔
          ∃ u l : Variety.Point K,
            u ∈ unipotentCandidate T D positiveRoots J ∧
              l ∈ leviCandidate T D J ∧ x = u * l) ∧
      IsUnipotentRadicalOf
        (parabolicCandidate T D positiveRoots J)
        (unipotentCandidate T D positiveRoots J) ∧
      (unipotentCandidate T D positiveRoots J).toSubgroup ⊓
          (leviCandidate T D J).toSubgroup = ⊥ ∧
      IsReductiveAlgebraicGroup (leviCandidate T D J).carrierVariety ∧
      IsTorusMaximalIn T (leviCandidate T D J) ∧
      HasRootSubsystem (leviCandidate T D J) D (RootSubsystemSpan D J) ∧
      (IsUniversalVersion K →
        IsUniversalVersion
          (derivedCandidate (leviCandidate T D J)).carrierVariety)) ∧
    (∀ J : Set D.Root, J ⊆ D.simple →
      ∀ p, p ∈ parabolicCandidate T D positiveRoots J →
        ∀ u, u ∈ unipotentCandidate T D positiveRoots J →
          p * u * p⁻¹ ∈ unipotentCandidate T D positiveRoots J) ∧
    (∀ J : Set D.Root, J ⊆ D.simple →
      (mCandidate T D J).toSubgroup =
        (derivedCandidate (leviCandidate T D J)).toSubgroup) ∧
    (∀ J : Set D.Root, J ⊂ D.simple →
      (leviCandidate T D J).inter
          (unipotentCandidate T D positiveRoots J).centralizer =
        (ClosedSubgroup.top (G := K)).centralizer) ∧
    (∀ J : Set D.Root, J ⊆ D.simple →
      (ClosedSubgroup.top (G := K)).centralizer ≤ T) := by sorry

public def ambientCenterInLeviCenter
    {K : Variety k} [AlgebraicGroup K] (L : ClosedSubgroup K) :
    Subgroup (Subgroup.center L.toSubgroup) :=
  (Subgroup.center (Variety.Point K)).comap
    (L.toSubgroup.subtype.comp (Subgroup.center L.toSubgroup).subtype)

public structure LeviCenterQuotientTorusModel
    {K : Variety k} [AlgebraicGroup K]
    (L : ClosedSubgroup K) (dimension : ℕ) where
  quotient : Variety k
  [quotientAlgebraicGroup : AlgebraicGroup quotient]
  [ambientCenterNormal : (ambientCenterInLeviCenter L).Normal]
  pointIso :
    Subgroup.center L.toSubgroup ⧸ ambientCenterInLeviCenter L ≃*
      Variety.Point quotient
  isTorus : IsTorus quotient
  dimension_eq : Variety.dimension quotient = dimension

end Theory.AlgebraicGroup
