module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalSixHAssembly
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.OriginalV1Basis

/-!
# Applying the constructed (6H) data to the actual Section 10 basis

The independently proved Section 10 natural-basis theorems now apply to
the original source without a ReeSixHData argument: OriginalSixHAssembly
constructs it from the same natural panel markings and F.1.1. Both endpoint
inclusion squares and literal Q.q right-conjugation are preserved. This
removes the structural input to the completed (10.6) consumer; multiplicative
field synchronization and later mixed equations remain with Section 10.
Source: Fong--Seitz II (1974), (10.6), printed pp.222--223.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open MarkedLocal

variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 8) (n : ℕ) (hn : Odd n) (m : ℕ)
  (μ₀ : (parabolic L S 0 ⧸ originalPanelKernel (L := L) (S := S) 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hB₀ : (originalFaithfulBorel (L := L) (S := S) 0).map μ₀.toMonoidHom = normalizer (T : Set _))
  (μ₁ : (parabolic L S 1 ⧸ originalPanelKernel (L := L) (S := S) 1) ≃* SuzukiMatrixGroup m)
  (hB₁ : (originalFaithfulBorel (L := L) (S := S) 1).map μ₁.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

open CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
local instance sourceV1BasisBinaryAlgebra : Algebra (ZMod 2) (ReeF4.CoefficientField m) := ZMod.algebra _ 2

/-- The printed basis has both original endpoint squares, with (6H) constructed here. -/
theorem original_source_V1_basis_endpoints (j : Fin 2) :
    let c := originalSourceReeSixHData Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁
    ∀ i : Fin 2, ∃ hi : ((originalV1BasisPoint Q e split c j).val.val : G) ∈ parabolic L S i,
      endpointMap Q e i ⟨(originalV1BasisPoint Q e split c j).val.val,hi⟩ =
        (V1BasisPoint Q split c j : X ⧸ Q.D) ∧
      originalV1BasisCoordinates Q e split c
        (Additive.ofMul (QuotientGroup.mk (originalV1BasisPoint Q e split c j))) =
        ![![0,1],![1,0]] j :=
  originalV1BasisPoint_endpoints Q e split
    (originalSourceReeSixHData Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁) h j

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open MarkedLocal

variable {G : Type*} [Group G]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 8) (n : ℕ) (hn : Odd n) (m : ℕ)
  (μ₀ : (parabolic L S 0 ⧸ originalPanelKernel (L := L) (S := S) 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hB₀ : (originalFaithfulBorel (L := L) (S := S) 0).map μ₀.toMonoidHom = normalizer (T : Set _))
  (μ₁ : (parabolic L S 1 ⧸ originalPanelKernel (L := L) (S := S) 1) ≃* SuzukiMatrixGroup m)
  (hB₁ : (originalFaithfulBorel (L := L) (S := S) 1).map μ₁.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

open CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
local instance sourceV1BasisQuotientBinaryAlgebra : Algebra (ZMod 2) (ReeF4.CoefficientField m) := ZMod.algebra _ 2

/-- Literal Q.q conjugation in the natural basis, without an assumed (6H) bundle. -/
theorem original_source_V1_basis_right_quotient
    (g v : generated L S) (hg : Q.q g ∈ rankOne Q split 0)
    (hv : Q.q v ∈ simpleRemainder Q split 0) :
    let c := quotientSourceReeSixHData Q h split hm n hn m μ₀ T hB₀ μ₁ hB₁
    ∃ w : simpleRemainder Q split 0,
      (w : (generated L S) ⧸ Q.D) = Q.q (g⁻¹*v*g) ∧
      V1BasisCoordinates Q split c (Additive.ofMul (QuotientGroup.mk w)) =
        Representation.SL2.BinarySmall.natural
          ((linearPinning Q split c).symm (⟨Q.q g,hg⟩ : rankOne Q split 0)⁻¹)
          (V1BasisCoordinates Q split c (Additive.ofMul (QuotientGroup.mk (⟨Q.q v,hv⟩ :
            simpleRemainder Q split 0)))) :=
  V1BasisCoordinates_right_quotient Q split
    (quotientSourceReeSixHData Q h split hm n hn m μ₀ T hB₀ μ₁ hB₁) g v hg hv

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
