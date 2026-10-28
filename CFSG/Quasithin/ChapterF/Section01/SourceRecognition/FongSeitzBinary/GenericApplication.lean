module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuotientReduction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionUnitaryPlane

/-!
# The marked quotient reduction on the selected generic factor

Apply the quotient reduction to the original pair ![L,R] and
S = O₂(N_G(L) ∩ H), using the existing preparation theorem to discharge
every F.1.1 premise. The resulting local lift has exactly the
`sourceParabolicAmalgam` type consumed by the Chapter12 generic recognition
core, including the whole overlap and both endpoint maps.

The source apartment/quotient and split data remain explicit earlier inputs
from qt-dgs85-apartment-exchange. A marked quotient comparison is transported
here, not asserted: exhaustive Fong–Seitz recognition and its minimality
reduction remain with this family. The generic-global and DGS assembly owners
retain preparation, exceptional branches and all final premise discharge.
No exceptional parabolic equivalence is upgraded to amalgam isomorphism.

Source: DGS Theorem D, printed p.224; Aschbacher–Smith F.1.9–12 and 5.2.6,
printed pp.261–264 and 650–651, with the original Chapter12 use on p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
open Chapter6.Source.RankOneGeneric

variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}

/-- The selected-factor preparation supplies the faithful original source
hypotheses; no quotient-faithfulness or ambient-center premise is added. -/
theorem prepared_quotient_reduction
    (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H)
    (Q : SourceQuotient ![L,R] (Global.sourceS L H)) (split : SplitData Q.tits) :
    Q.tits.B.normalCore = ⊥ ∧
      pCore 2 ((generated ![L,R] (Global.sourceS L H)) ⧸ Q.D) = ⊥ ∧
      center ((generated ![L,R] (Global.sourceS L H)) ⧸ Q.D) = ⊥ := by
  have hr := quotient_reduction (d.hypothesisF11 h hTH) Q split
  exact ⟨hr.1, hr.2.1, hr.2.2.1⟩

omit [Finite G] in
/-- The literal original Chapter12 amalgam maps to the two marked quotient
parabolics by an isomorphism respecting both endpoint inclusions. -/
def selectedFactorMarkedIso (Q : SourceQuotient ![L,R] (Global.sourceS L H)) :
    RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H))
      Q.standardAmalgam := originalMarkedIso Q

omit [Finite G] in
/-- A regular-branch quotient comparison lifts to the exact selected-factor
amalgam required by the existing generic recognition consumer. -/
def selectedFactorComparison
    (Q : SourceQuotient ![L,R] (Global.sourceS L H))
    {X C Y : Type*} [Group X] [Group C] [Group Y]
    {β : RankTwoAmalgam X C Y} (e : RankTwoAmalgam.Iso Q.standardAmalgam β) :
    RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) β :=
  originalComparison Q e

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
