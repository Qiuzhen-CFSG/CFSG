module

public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.Setup
public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.nonsingular_coefficient
public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.Commutator
public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.ParabolicBounds

universe u

set_option linter.style.haveILetI false

open scoped commutatorElement

/-!
Exact commutator layers for a parabolic relative-root filtration.  The
root-theoretic core is the arbitrary-`J` reverse inclusion in
`RelativeRootSeries.Commutator`: a root of height at least two splits into a
height-one and a complementary root, whose `(1,1)` Chevalley term has
nonzero coefficient under the nonsingularity hypothesis.  The standard
parabolic first-layer and terminal-layer identities then turn the finite
descending induction into the setup-level equality
`⁅S.layer i, S.U.toSubgroup⁆ = S.layer (i + 1)`.

This is the relative-root form of GLS3, Chapter 1, Lemma 1.13.6, retaining
arbitrary standard-parabolic `J` rather than specializing to the empty set.
-/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

private def ParabolicRelativeRootSetup.toStandardForExactCommutator
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) :
    StandardParabolicRelativeRootSetup K where
  T := S.T
  B := S.B
  U := S.U
  D := S.D
  C := S.C
  finiteActualRoot := S.finiteActualRoot
  ι := S.ι
  X := S.X
  Y := S.Y
  finiteRoot := S.finiteRoot
  addCommGroupX := S.addCommGroupX
  addCommGroupY := S.addCommGroupY
  integralPairing := S.pairing
  integralRootSystem := S.isRootSystem
  integralCrystallographic := S.isCrystallographic
  integralReduced := S.isReduced
  integralBase := S.base
  rootEquiv := S.rootEquiv
  weightEquiv := S.weightEquiv
  positiveRoots := S.positiveRoots
  J := S.J
  sigmaJ := S.sigmaJ
  coeff := S.coeff
  integralRootAdditionRealization := S.integralRootAdditionRealization
  actualRootDatum := S.actualRootDatum
  integralSimpleRootExpansion := S.simpleRootExpansion
  standardParabolic := S.standardParabolic
  unipotentRootGeneration := S.unipotentRootGeneration
  XQ := S.XQ
  YQ := S.YQ
  addCommGroupXQ := S.addCommGroupXQ
  moduleXQ := S.moduleXQ
  addCommGroupYQ := S.addCommGroupYQ
  moduleYQ := S.moduleYQ
  rationalPairing := S.rootPairing
  rationalRootSystem := S.rootPairingIsRootSystem
  rationalCrystallographic := S.rootPairingIsCrystallographic
  rationalReduced := S.rootPairingIsReduced
  rationalBase := S.rootBase
  baseSupport_eq := S.rootBase_support
  rationalRootRealization := S.rootSystemRealization
  rationalRootAdditionRealization := S.rationalRootAdditionRealization
  rationalSimpleRootExpansion := S.rootSimpleRootExpansion
  chevalleySystem := S.chevalleySystem
  maxRelativeHeight := S.maxRelativeHeight
  relativeHeight_le := S.relativeHeight_le

omit [IsAlgClosed k] in
private lemma layer_toStandardForExactCommutator
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) (i : ℕ) :
    S.toStandardForExactCommutator.layer i = S.layer i := by
  rw [StandardParabolicRelativeRootSetup.layer,
    ParabolicRelativeRootSetup.layer]
  change RelativeRootSeries S.D S.rootEquiv S.rootBase.support S.coeff S.J i =
    RelativeRootSeries S.D S.rootEquiv S.base.support S.coeff S.J i
  rw [S.rootBase_support]

public theorem ParabolicRelativeRootSetup.exact_commutator_layers
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K)
    (classification : RootClassification)
    (hType : HasDynkinType S.rootPairing classification)
    (hNonsingular : ¬ IsUSingular classification (ringChar k)) :
    ∀ i, 0 < i → i ≤ S.maxRelativeHeight →
      ⁅S.layer i, S.U.toSubgroup⁆ = S.layer (i + 1) := by
  letI := Fintype.ofFinite S.D.Root
  letI := Fintype.ofFinite S.ι
  letI : IsAddTorsionFree S.XQ := IsAddTorsionFree.of_module_rat S.XQ
  let S' := S.toStandardForExactCommutator
  have hCoeff11 : ∀ {α β : S.D.Root} {q : ChevalleyCommutatorTerm S.D.Root},
      AreLinearlyIndependentRoots S.D S.rootPairing S.rootEquiv α β →
      IsValidChevalleyCommutatorTerm S.D S.rootPairing S.rootEquiv α β q →
      q.i = 1 → q.j = 1 →
      ∀ c : k,
        HasExpectedChevalleyCoefficient S.D S.rootPairing S.rootEquiv α β q c →
          c ≠ 0 := by
    intro α β q hLI hqvalid hqi hqj c hc
    exact (S.expectedChevalleyCoefficient_ne_zero classification hType hNonsingular hc)
  have hJ : S.rootEquiv '' S.J ⊆ S.rootBase.support := by
    rintro _ ⟨α, hαJ, rfl⟩
    exact (S.rootSystemRealization.2.2.2.1 α).1
      (S.standardParabolic.2.1 hαJ)
  have hExact := relativeRootSeries_eq_commutator_of_one_one_nonzero_of_subset
    S.D S.C S.rootPairing S.rootEquiv S.rootBase S.coeff
      S.rootSimpleRootExpansion S.chevalleySystem S.J hJ hCoeff11
      S.maxRelativeHeight (standardParabolicRelativeRootLayer_terminal S')
  intro i hi hle
  rw [← layer_toStandardForExactCommutator S i,
    ← layer_toStandardForExactCommutator S (i + 1)]
  have hU : S'.U.toSubgroup = S.U.toSubgroup := rfl
  rw [← hU, standardParabolicUnipotentRadical_eq_firstRelativeRootLayer S']
  exact hExact i hi hle

end Theory.AlgebraicGroup
