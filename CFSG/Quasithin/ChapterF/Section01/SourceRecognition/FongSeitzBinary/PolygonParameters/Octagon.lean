module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.PolygonParameters.OctagonDegrees
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalCommonField

/-!
# Octagon parameter constraints on the original Ree source

The actual marked linear and Suzuki roots have orders 2^n and
(2^(2m+1))^2. The finite octagon square theorem therefore supplies the
oddness previously required by the common-field argument. The existing
perpendicular-root actions then identify n with 2m+1. Two Suzuki panels
are excluded by the same square theorem, including the parameter zero.

The original application retains both endpoint markings and the whole
Borel normalizers. Field-family selection, split structure, reflections
and later mixed root equations remain with their source producers.

Source: Fong--Seitz I (1J), (6H)(a), printed pp.6 and 51.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}

/-- The two actual panel markings supply the odd linear degree in (6H)(a). -/
theorem linear_degree_odd_of_octagon
    (Q : MarkedQuotient P) (split : SplitData Q.tits) (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) (n : ℕ) (hn : 0 < n) (m : ℕ)
    (μ₀ : (Endpoint Q i ⧸ panelKernel Q i) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hB₀ : (quotientBorel Q i).map μ₀.toMonoidHom = normalizer (T : Set _))
    (μ₁ : (Endpoint Q j ⧸ panelKernel Q j) ≃* SuzukiMatrixGroup m)
    (hB₁ : (quotientBorel Q j).map μ₁.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m))) : Odd n := by
  apply octagon_linear_degree_odd Q split hm i j hij (k := 2 * m + 1)
  · simpa only [HexagonStructure.rootAt_one] using
      linear_rootAt_card Q split i n μ₀ T hB₀ hn 1
  · rw [Nat.card_congr (suzukiRootEquiv Q split j m μ₁ hB₁).toEquiv,matrixRoot_card]

/-- The common-field equality with its oddness premise discharged by finite geometry. -/
theorem ree_common_field_exponent_of_octagon
    (Q : MarkedQuotient P) (split : SplitData Q.tits) (hm : rotationOrder Q = 8)
    (n : ℕ) (hn : 0 < n) (m : ℕ)
    (μ₀ : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hB₀ : (quotientBorel Q 0).map μ₀.toMonoidHom = normalizer (T : Set _))
    (μ₁ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
    (hB₁ : (quotientBorel Q 1).map μ₁.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
    (s : ∀ i, RootReflection Q split i) (hcore : Q.tits.B.normalCore = ⊥) :
    n = 2 * m + 1 :=
  ree_common_field_exponent Q split hm n
    (linear_degree_odd_of_octagon Q split hm 0 1 (by decide) n hn m μ₀ T hB₀ μ₁ hB₁)
    m μ₀ T hB₀ μ₁ hB₁ s hcore

/-- Two naturally marked Suzuki panels cannot occur in a finite octagon. -/
theorem two_suzuki_panels_excluded_of_octagon
    (Q : MarkedQuotient P) (split : SplitData Q.tits) (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) (m n : ℕ)
    (μ₀ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
    (hB₀ : (quotientBorel Q i).map μ₀.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
    (μ₁ : (Endpoint Q j ⧸ panelKernel Q j) ≃* SuzukiMatrixGroup n)
    (hB₁ : (quotientBorel Q j).map μ₁.toMonoidHom =
      normalizer (SuzukiRootSubgroup n : Set (SuzukiMatrixGroup n))) : False := by
  apply octagon_two_square_binary_roots_excluded Q split hm i j hij
    (a := 2 * m + 1) (b := 2 * n + 1)
  · rw [Nat.card_congr (suzukiRootEquiv Q split i m μ₀ hB₀).toEquiv,matrixRoot_card]
  · rw [Nat.card_congr (suzukiRootEquiv Q split j n μ₁ hB₁).toEquiv,matrixRoot_card]

open MarkedLocal
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Literal original-source application: both full Borel markings are retained,
and no odd-degree or square-profile premise is required. -/
theorem original_ree_common_field_exponent_of_octagon
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam)
    (h : HypothesisF11 L S) (split : SplitData Q.tits)
    (hm : rotationOrder Q = 8) (n : ℕ) (hn : 0 < n) (m : ℕ)
    (μ₀ : (parabolic L S 0 ⧸ originalPanelKernel (L := L) (S := S) 0) ≃*
      PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hB₀ : (originalFaithfulBorel (L := L) (S := S) 0).map μ₀.toMonoidHom =
      normalizer (T : Set _))
    (μ₁ : (parabolic L S 1 ⧸ originalPanelKernel (L := L) (S := S) 1) ≃* SuzukiMatrixGroup m)
    (hB₁ : (originalFaithfulBorel (L := L) (S := S) 1).map μ₁.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
    (s : ∀ i, RootReflection Q split i) : n = 2 * m + 1 :=
  ree_common_field_exponent_of_octagon Q split hm n hn m
    (faithfulModelMarking Q e h 0 μ₀) T (faithfulModelMarking_borel Q e h 0 μ₀ _ hB₀)
    (faithfulModelMarking Q e h 1 μ₁) (faithfulModelMarking_borel Q e h 1 μ₁ _ hB₁) s
    (LinearThreePresentation.borel_core_eq_bot Q e h)

/-- The original two-Suzuki alternative is excluded with both endpoint and
whole-Borel markings retained, including parameter zero and either orientation. -/
theorem original_two_suzuki_panels_excluded_of_octagon
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam)
    (h : HypothesisF11 L S) (split : SplitData Q.tits) (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) (m n : ℕ)
    (μ₀ : (parabolic L S i ⧸ originalPanelKernel (L := L) (S := S) i) ≃*
      SuzukiMatrixGroup m)
    (hB₀ : (originalFaithfulBorel (L := L) (S := S) i).map μ₀.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
    (μ₁ : (parabolic L S j ⧸ originalPanelKernel (L := L) (S := S) j) ≃*
      SuzukiMatrixGroup n)
    (hB₁ : (originalFaithfulBorel (L := L) (S := S) j).map μ₁.toMonoidHom =
      normalizer (SuzukiRootSubgroup n : Set (SuzukiMatrixGroup n))) : False :=
  two_suzuki_panels_excluded_of_octagon Q split hm i j hij m n
    (faithfulModelMarking Q e h i μ₀) (faithfulModelMarking_borel Q e h i μ₀ _ hB₀)
    (faithfulModelMarking Q e h j μ₁) (faithfulModelMarking_borel Q e h j μ₁ _ hB₁)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
