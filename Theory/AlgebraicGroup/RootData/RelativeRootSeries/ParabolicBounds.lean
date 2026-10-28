module

public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.Nilpotency
public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.ParabolicSetup
public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.StandardParabolic

universe u

set_option linter.style.haveILetI false

/-!
The initial layer, termination, commutator, and nilpotency bounds for a
standard-parabolic relative-root filtration.
-/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- The unipotent radical of a standard parabolic is its first relative-root
layer. -/
public lemma standardParabolicUnipotentRadical_eq_firstRelativeRootLayer
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) :
    S.U.toSubgroup = S.layer 1 := by
  letI := Fintype.ofFinite S.D.Root
  letI := Fintype.ofFinite S.ι
  rw [StandardParabolicRelativeRootSetup.layer, S.baseSupport_eq]
  exact (relativeRootSeries_one_eq_standardUnipotentRadical
    S.T S.B S.D S.integralPairing S.integralBase S.rootEquiv
    S.weightEquiv S.positiveRoots S.J S.sigmaJ S.U S.coeff
    S.actualRootDatum S.integralSimpleRootExpansion S.standardParabolic
    S.unipotentRootGeneration).symm

/-- No relative-root layer remains above the maximal relative height. -/
public lemma standardParabolicRelativeRootLayer_terminal
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) :
    S.layer (S.maxRelativeHeight + 1) = ⊥ := by
  letI := Fintype.ofFinite S.D.Root
  letI := Fintype.ofFinite S.ι
  apply relativeRootSeries_eq_bot_of_height_lt
  intro α
  have hα := S.relativeHeight_le α
  omega

/-- Commuting a positive relative-root layer with the unipotent radical moves
one step down the filtration. -/
public lemma standardParabolicRelativeRootLayer_commutator_le_next
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i) :
    ⁅S.layer i, S.U.toSubgroup⁆ ≤ S.layer (i + 1) := by
  letI := Fintype.ofFinite S.D.Root
  letI := Fintype.ofFinite S.ι
  rw [standardParabolicUnipotentRadical_eq_firstRelativeRootLayer S]
  exact relativeRootSeries_commutator_series_le S.D S.C
    S.rationalPairing S.rootEquiv S.rationalBase S.coeff
    S.rationalSimpleRootExpansion S.chevalleySystem S.J i hi

/-- The maximal relative height bounds the nilpotency class of the standard
parabolic unipotent radical. -/
public lemma standardParabolicUnipotentRadical_nilpotencyClass_le
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) :
    Group.nilpotencyClass S.U.toSubgroup ≤ S.maxRelativeHeight := by
  exact relativeRootSeries_nilpotencyClass_le_of_terminal S.D
    S.rationalPairing S.rationalBase S.rootEquiv S.coeff
    S.rationalSimpleRootExpansion S.J S.U.toSubgroup
    (standardParabolicUnipotentRadical_eq_firstRelativeRootLayer S).symm
    S.C S.chevalleySystem S.maxRelativeHeight
    (standardParabolicRelativeRootLayer_terminal S)

end Theory.AlgebraicGroup
