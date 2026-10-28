module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalCommonField
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.SixH

/-!
# Original-carrier application of the initial Ree Cartan clauses

This leaf keeps the literal original marked quotient and its full Borel map.
It applies the common-field Cartan equivalence together with the actual joint
simple-root separation and rank-one centralization clauses.  The output is a
partial Cartan package, not the full (6H) theorem. The remaining commutator,
Frattini, center and Section 10 construction stay with this theorem-family
owner; no Section 10 relation or full-model comparison is assumed here.
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
  (s : ∀ i, RootReflection Q split i)

include e h hm hn μ₀ hB₀ μ₁ hB₁ s in
theorem original_ree_sixH_package :
    n = 2*m+1 ∧
    Nat.card (originalCartan Q e h) = (2^(2*m+1)-1)^2 ∧
    (((Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) ⊓
      centralizer (simpleRoot Q split 0 : Set (X ⧸ Q.D))) ⊓
      centralizer (simpleRoot Q split 1 : Set (X ⧸ Q.D)) = ⊥) ∧
    (∀ i : Fin 2,
      ((Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) ⊓
        embeddedPanelKernel Q i) ≤
        centralizer (rankOneRootGroup Q split i : Set (X ⧸ Q.D))) := by
  have hcore : Q.tits.B.normalCore = ⊥ :=
    LinearThreePresentation.borel_core_eq_bot Q e h
  refine ⟨original_ree_common_field_exponent Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁ s,
    original_ree_cartan_card Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁ s, ?_, ?_⟩
  · exact sixH_joint_simpleRoot_centralizer_eq_bot Q split s hcore
  · intro i
    exact sixH_panelKernel_centralizes_rankOne Q split i

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
