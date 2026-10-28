module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SuzukiLocalIdentification
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.GenericRootCoordinates

/-!
# Suzuki local recognition in the selected Chapter 12 pair

Apply the original-factor recognition to the actual second endpoint of
![L,R]. Its canonical root-generated group is R/O₂(R), its full panel
kernel is trivial on that subgroup, and its panel degree cannot be nine.
The same equivalence identifies the full local permutation group after
the separate (2B) containment is supplied. In particular no independently
chosen Suzuki tag or local-permutation isomorphism is an input.

The original preparation supplies F.1.1. Perfectness and the Suzuki
quotient belong to the selected second-factor branch; the marked finite
quotient and split datum retain the apartment/exchange producer. Nonlinear
(2B), the nonperfect branches and exhaustive marked assembly remain with
source recognition, and the original Chapter 12 owner retains their final
discharge. Source: Fong--Seitz I (2A), (5C), pp.7--8,25--26; AS 12.2.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
open Chapter6.Source.RankOneGeneric
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  {P : Fin 2 → Subgroup X}

/-- The actual selected Suzuki factor gives its original root identification,
trivial root-action kernel and exclusion of the degree-nine local action.
Only the extension to the full local image still requires source (2B). -/
theorem prepared_suzuki_local_identification
    (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    {m : ℕ} (μ : (R ⧸ pCore 2 R) ≃* SuzukiMatrixGroup m)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    ∃ a : MarkedLocal.originalRankOne Q e split 1 ≃* R ⧸ pCore 2 R,
      (MarkedLocal.originalPanelKernel (L := ![L,R]) (S := Global.sourceS L H) 1).subgroupOf
        (MarkedLocal.originalRankOne Q e split 1) = ⊥ ∧
      Nat.card (Panel Q 1) ≠ 9 ∧
      ∀ _ : simpleRemainder Q split 1 ≤ localKernel Q 1,
        ∃ b : localGroup Q split 1 ≃* R ⧸ pCore 2 R,
          ∀ r, a r = b (MarkedLocal.originalRootProjection Q e split 1 r) := by
  let hf := d.hypothesisF11 h hTH
  obtain ⟨T₁,hT₁⟩ := hf.sylow 1
  refine ⟨(MarkedLocal.originalSuzukiRankOneEquiv Q e hf split 1 hp T₁ hT₁ μ).trans μ.symm,
    MarkedLocal.suzuki_original_root_kernel_trivial Q e hf split 1 hp T₁ hT₁ μ,
    MarkedLocal.suzuki_panel_card_ne_nine Q e hf split 1 T₁ hT₁ μ, ?_⟩
  intro hV
  refine ⟨(MarkedLocal.suzukiLocalEquiv Q e hf split 1 hp T₁ hT₁ μ hV).trans μ.symm, ?_⟩
  intro r
  exact congrArg μ.symm
    (MarkedLocal.originalSuzukiRankOneEquiv_projection Q e hf split 1 hp T₁ hT₁ μ hV r)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The literal Chapter 12 selected Suzuki branch uses the same quotient,
full Borel marking and second original endpoint, with its root kernel discharged. -/
theorem rankOne_global_suzuki_local_identification
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (hp : Group.IsPerfect R) {m : ℕ}
    (μ : (R ⧸ pCore 2 R) ≃* SuzukiMatrixGroup m)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    ∃ a : MarkedLocal.originalRankOne Q e split 1 ≃* R ⧸ pCore 2 R,
      (MarkedLocal.originalPanelKernel (L := ![L,R]) (S := Global.sourceS L H) 1).subgroupOf
        (MarkedLocal.originalRankOne Q e split 1) = ⊥ ∧
      Nat.card (Panel Q 1) ≠ 9 ∧
      ∀ _ : simpleRemainder Q split 1 ≤ localKernel Q 1,
        ∃ b : localGroup Q split 1 ≃* R ⧸ pCore 2 R,
          ∀ r, a r = b (MarkedLocal.originalRootProjection Q e split 1 r) :=
  prepared_suzuki_local_identification d
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH hp μ Q e split

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
