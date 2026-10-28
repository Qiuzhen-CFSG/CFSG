module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.SixHAssembly
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalSixHAssembly
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.PolygonParameters.Octagon

/-!
# Octagon-specialized (6H) source constructors

The finite octagon square theorem supplies the odd linear degree needed by
the existing source `(6H)` assembly.  These wrappers retain the established
interfaces and all literal endpoint and whole-Borel markings while removing
only that separately discharged arithmetic premise.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open MarkedLocal

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 8) (n : ℕ) (hn : 0 < n) (m : ℕ)
  (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
  (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q 1).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set _))

/-- Source `(6H)` data with oddness discharged by the finite octagon. -/
def sourceReeSixHData_of_octagon
    (hcore : Q.tits.B.normalCore = ⊥)
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤
      pCore 2 (Endpoint Q 1)) :
    ReeSixHData Q split n m := by
  let hnOdd : Odd n := linear_degree_odd_of_octagon Q split hm 0 1 (by decide)
    n hn m ν T hC μ hB
  exact sourceReeSixHData Q split n hnOdd m ν T hC μ hB hm hcore hc

variable {G : Type*} [Group G]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Original marked `(6H)` data with oddness discharged by the finite octagon. -/
def originalSourceReeSixHData_of_octagon
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
        inf_le_left inf_le_right) Q.standardAmalgam)
    (h : HypothesisF11 L S) (split : SplitData Q.tits)
    (hm : rotationOrder Q = 8) (n : ℕ) (hn : 0 < n) (m : ℕ)
    (μ₀ : (parabolic L S 0 ⧸ originalPanelKernel (L := L) (S := S) 0) ≃*
      PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hB₀ : (originalFaithfulBorel (L := L) (S := S) 0).map μ₀.toMonoidHom =
      normalizer (T : Set _))
    (μ₁ : (parabolic L S 1 ⧸ originalPanelKernel (L := L) (S := S) 1) ≃*
      SuzukiMatrixGroup m)
    (hB₁ : (originalFaithfulBorel (L := L) (S := S) 1).map μ₁.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m))) :
    ReeSixHData Q split n m := by
  let ν₀ := faithfulModelMarking Q e h 0 μ₀
  let ν₁ := faithfulModelMarking Q e h 1 μ₁
  let hC₀ := faithfulModelMarking_borel Q e h 0 μ₀ (normalizer (T : Set _)) hB₀
  let hC₁ := faithfulModelMarking_borel Q e h 1 μ₁
    (normalizer (SuzukiRootSubgroup m : Set _)) hB₁
  let hnOdd : Odd n := linear_degree_odd_of_octagon Q split hm 0 1 (by decide)
    n hn m ν₀ T hC₀ ν₁ hC₁
  exact originalSourceReeSixHData Q e h split hm n hnOdd m μ₀ T hB₀ μ₁ hB₁

variable (Q : SourceQuotient L S)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 8) (n : ℕ) (hn : 0 < n) (m : ℕ)
  (μ₀ : (parabolic L S 0 ⧸ originalPanelKernel (L := L) (S := S) 0) ≃*
    PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hB₀ : (originalFaithfulBorel (L := L) (S := S) 0).map μ₀.toMonoidHom =
    normalizer (T : Set _))
  (μ₁ : (parabolic L S 1 ⧸ originalPanelKernel (L := L) (S := S) 1) ≃*
    SuzukiMatrixGroup m)
  (hB₁ : (originalFaithfulBorel (L := L) (S := S) 1).map μ₁.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

/-- The same octagon-specialized data on the literal original quotient. -/
def quotientSourceReeSixHData_of_octagon :
    ReeSixHData Q split n m :=
  originalSourceReeSixHData_of_octagon Q (originalMarkedIso Q) h split hm n hn m
    μ₀ T hB₀ μ₁ hB₁

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
