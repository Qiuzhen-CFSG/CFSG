module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.RankOneTorus
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.OrthogonalPinning
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.CoefficientApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialityPresentation.SignedSubgroup

/-!
# Constructed signed roots on the literal triality quotient

Two source SL₂ maps and their geometric orthogonality construct all negative
roots, the full signed Weyl action, and the rank-one torus words on X/Q.D.
Combine their positive orbit maps with the existing coefficient calculation
and canonical positive-root placements to construct the actual positive and
signed presentation data. The signed subgroup is exactly split.U joined
with the two literal rank-one Weyl images.

The positive evaluation retains the original S image and Q.q for the
original numerator, or the supplied marked amalgam for a geometric numerator.
Weyl words lift through the same Q.endpointEquiv maps for either orientation;
all field transports use the original cubic marking and its fixed-field
restriction.

The inputs remain intermediate source obligations: construct the compatible
rank-one maps, their geometric normalization and braid, the coefficient-stage
equations and canonical placements from 6E(b). Cross-torus commutation, mixed
torus characters and full signed generation in the ambient quotient are also
still required. This module does not claim the completed 6E(b) reconstruction.
Source: Fong--Seitz II §7 and §9B; DGS Theorem D, printed p.224.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
open Triality.Standard Triality.Standard.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.PinnedApplication
variable {F Y : Type*} [Field F] [CharP F 2] [Group Y] {σ : F ≃+* F}

def rawRoots (p : RankOnePair σ Y) : RawRoots σ Y := ⟨p.shortOrbit, p.longOrbit⟩

section Quotient
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  {n : ℕ} {hn : 0 < n}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (p : RankOnePair σ (X ⧸ Q.D)) (e : ScalarMarking (binaryParameters n hn) σ)
  (orientation : Bool) (hm : rotationOrder Q = 6)
  (placement : ∀ A, A ∈ orderedRoots Q split orientation 6 ↔ ∃ i, (rawRoots p).ranges i = A)
  [Finite F] (c : (rawRoots p).CoefficientStage e)

abbrev positiveData : TrialityPresentation.PositiveRootData Q split n hn σ :=
  positiveRootData Q split (rawRoots p) e orientation hm placement c

/-- The negative maps and their actions are constructed from the source rank-one
maps; the positive coefficient stage remains an independent source obligation. -/
def signedData : TrialityPresentation.SignedRootData
    (positiveData Q split p e orientation hm placement c) where
  negativeShort i := p.dihedral.W.toMonoidHom.comp (p.markedShort i)
  negativeLong i := p.dihedral.W.toMonoidHom.comp (p.longOrbit i)
  actions := p.actions e

@[simp] theorem signedData_roots :
    (signedData Q split p e orientation hm placement c).roots = p.signedRoots e := rfl

include hm placement c in
/-- The literal signed subgroup is U together with the two same-source Weyl images. -/
theorem signedClosure_eq_unipotent_sup_weyl :
    (p.signedRoots e).signedClosure = split.U ⊔
      Subgroup.closure {p.shortMap (Theory.PSL2.SemilinearCoverage.weyl F),
        p.longMap (Theory.PSL2.SemilinearCoverage.weyl _)} := by
  have h := (signedData Q split p e orientation hm placement c).signedClosure_eq_sourceUnipotent_sup_simpleWords
  rw [signedData_roots, p.nA_one, p.nB_one] at h
  exact h

include split hm placement c in
/-- Positive equations and the derived signed words discharge the finite Weyl contract. -/
theorem weylRelations : (p.signedRoots e).WeylRelations :=
  p.weylRelations e (positiveData Q split p e orientation hm placement c).root_relations

/-- The geometric/original marking retains the literal original S image. -/
theorem nativeHom_range_marked {G : Type*} [Group G]
    {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (marking : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam) (h : HypothesisF11 L S) :
    (positiveData Q split p e orientation hm placement c).nativeHom.range =
      (MarkedLocal.sylowMap Q marking h).range :=
  (positiveData Q split p e orientation hm placement c).nativeHom_range_marked marking h

/-- The constructed signed short coroot keeps the same source diagonal. -/
theorem short_coroot_parameter (t : Fˣ) :
    (signedData Q split p e orientation hm placement c).roots.hA
      (Units.map e.extension.toMonoidHom t) =
        p.shortMap (Theory.PSL2.SemilinearCoverage.tor t) := p.hA_parameter e t

/-- The long coroot uses the restriction of the same field marking. -/
theorem long_coroot_parameter (t : (ScalarMarking.SourceFixed (σ := σ))ˣ) :
    (signedData Q split p e orientation hm placement c).roots.hB
      (Units.map e.fixed.toMonoidHom t) =
        p.longMap (Theory.PSL2.SemilinearCoverage.tor t) := p.hB_parameter e t

end Quotient

section GeometricPinning
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  {n : ℕ} {hn : 0 < n} [Finite F]
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (g : GeometricPair σ (X ⧸ Q.D)) (e : ScalarMarking (binaryParameters n hn) σ)
  (orientation : Bool) (hm : rotationOrder Q = 6)
  (placement : ∀ A, A ∈ orderedRoots Q split orientation 6 ↔
    ∃ i, (rawRoots g.toRankOnePair).ranges i = A)
  (c : (rawRoots g.toRankOnePair).CoefficientStage e)

/-- On the literal quotient, geometric normalization and positive source
commutation now suffice to construct the signed presentation data. -/
def geometricSignedData : TrialityPresentation.SignedRootData
    (positiveData Q split g.toRankOnePair e orientation hm placement c) :=
  signedData Q split g.toRankOnePair e orientation hm placement c

end GeometricPinning

section Endpoints
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  {n : ℕ} {hn : 0 < n}
  (Q : MarkedQuotient P) (p : RankOnePair σ (X ⧸ Q.D))
  (e : ScalarMarking (binaryParameters n hn) σ)

private theorem endpoint_lift (i : Fin 2) (y : X ⧸ Q.D)
    (hy : y ∈ Q.tits.standardParabolic {Q.simple i}) :
    ∃ x : P i, Q.q x = y ∧ (Q.endpointEquiv i x : X ⧸ Q.D) = y := by
  let z : Q.tits.standardParabolic {Q.simple i} := ⟨y,hy⟩
  let x := (Q.endpointEquiv i).symm z
  have hx : (Q.endpointEquiv i x : X ⧸ Q.D) = y :=
    congrArg Subtype.val ((Q.endpointEquiv i).apply_symm_apply z)
  exact ⟨x, by simpa only [MarkedQuotient.endpointEquiv_apply] using hx, hx⟩

/-- The defined short Weyl word lifts through the original endpoint map,
for either orientation of the source pair. -/
theorem short_word_endpoint (i : Fin 2)
    (h : p.shortMap.range ≤ Q.tits.standardParabolic {Q.simple i}) :
    ∃ x : P i, Q.q x = (p.signedRoots e).nA 1 ∧
      (Q.endpointEquiv i x : X ⧸ Q.D) = (p.signedRoots e).nA 1 := by
  apply endpoint_lift Q i
  rw [p.nA_one]
  exact h ⟨_,rfl⟩

/-- The long word retains the other original endpoint under the same quotient. -/
theorem long_word_endpoint (i : Fin 2)
    (h : p.longMap.range ≤ Q.tits.standardParabolic {Q.simple i}) :
    ∃ x : P i, Q.q x = (p.signedRoots e).nB 1 ∧
      (Q.endpointEquiv i x : X ⧸ Q.D) = (p.signedRoots e).nB 1 := by
  apply endpoint_lift Q i
  rw [p.nB_one]
  exact h ⟨_,rfl⟩

end Endpoints

/-- The generated numerator uses the unchanged source quotient map. -/
theorem nativeHom_range_original [Finite F]
    {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    {n : ℕ} {hn : 0 < n}
    (p : RankOnePair σ ((generated L S) ⧸ Q.D)) (e : ScalarMarking (binaryParameters n hn) σ)
    (orientation : Bool) (hm : rotationOrder Q = 6)
    (placement : ∀ A, A ∈ orderedRoots Q split orientation 6 ↔ ∃ i, (rawRoots p).ranges i = A)
    (c : (rawRoots p).CoefficientStage e) :
    (positiveData Q split p e orientation hm placement c).nativeHom.range =
      (S.subgroupOf (generated L S)).map Q.q :=
  TrialityPresentation.nativeHom_range_original h Q split
    (positiveData Q split p e orientation hm placement c)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.PinnedApplication
