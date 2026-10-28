module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SuzukiAllLocalIdentification
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.GenericRootCoordinates

/-!
# All Suzuki parameters on the literal Chapter 12 pair

The original factor R need not be perfect. Its actual Suzuki quotient,
including Sz(2), supplies (2B), the original parabolic two-core, the
canonical root-group comparison and the faithful local action comparison.
The whole original cover retains both its factor representative equation
and its root/local projection square. No small group is replaced by its
derived subgroup. Both endpoint maps and the full common Borel are the
same independently supplied marking throughout.

This discharges the Suzuki local-model and cover premises of the generic
Chapter 12 recognition family. The finite quotient, split datum and marked
amalgam remain genuine apartment/exchange inputs. Neither this selected
Suzuki branch nor these local equivalences establish a global Lie row.
Source: Fong--Seitz I (2B), (5B)--(5C), pp.7--9,25--26;
AS F.1.1--3 and 12.2.2. Final source assembly retains exhaustive row selection.
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

/-- The actual selected Suzuki endpoint, with perfectness and positivity removed. -/
theorem prepared_suzuki_all_local_identification
    (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H)
    {m : ℕ} (μ : (R ⧸ pCore 2 R) ≃* SuzukiMatrixGroup m)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    simpleRemainder Q split 1 ≤ localKernel Q 1 ∧
      (simpleRemainder Q split 1).comap (MarkedLocal.endpointMap Q e 1) =
        pCore 2 (parabolic ![L,R] (Global.sourceS L H) 1) ∧
      ∃ a : MarkedLocal.originalRankOne Q e split 1 ≃* R ⧸ pCore 2 R,
        (MarkedLocal.originalPanelKernel (L := ![L,R]) (S := Global.sourceS L H) 1).subgroupOf
          (MarkedLocal.originalRankOne Q e split 1) = ⊥ ∧
        Nat.card (Panel Q 1) ≠ 9 ∧
        ∃ b : localGroup Q split 1 ≃* R ⧸ pCore 2 R,
          ∀ r, a r = b (MarkedLocal.originalRootProjection Q e split 1 r) := by
  let hf := d.hypothesisF11 h hTH
  obtain ⟨T₁,hT₁⟩ := hf.sylow 1
  refine ⟨MarkedLocal.suzuki_remainder_le_kernel_all Q e hf split 1 T₁ hT₁ μ,
    MarkedLocal.suzuki_remainder_comap_all Q e hf split 1 T₁ hT₁ μ,
    (MarkedLocal.originalSuzukiAllRankOneEquiv Q e hf split 1 T₁ hT₁ μ).trans μ.symm,
    MarkedLocal.suzuki_all_original_root_kernel_trivial Q e hf split 1 T₁ hT₁ μ,
    MarkedLocal.suzuki_panel_card_ne_nine Q e hf split 1 T₁ hT₁ μ,
    (MarkedLocal.suzukiAllLocalEquiv Q e hf split 1 T₁ hT₁ μ).trans μ.symm, ?_⟩
  intro r
  exact congrArg μ.symm (MarkedLocal.originalSuzukiAllRankOneEquiv_projection Q e hf split 1 T₁ hT₁ μ r)

/-- The whole original cover and both representative squares for the selected factor. -/
theorem prepared_suzuki_all_original_cover
    (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H)
    {m : ℕ} (μ : (R ⧸ pCore 2 R) ≃* SuzukiMatrixGroup m)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    let hf := d.hypothesisF11 h hTH
    letI := MarkedLocal.originalRadicalInClosure_normal Q e hf split 1
    ∃ c : (MarkedLocal.originalLocalClosure Q e split 1 ⧸
        MarkedLocal.originalRadicalInClosure Q e split 1) ≃* SuzukiMatrixGroup m,
      ∃ a : MarkedLocal.originalRankOne Q e split 1 ≃* SuzukiMatrixGroup m,
        ∃ b : localGroup Q split 1 ≃* SuzukiMatrixGroup m,
          (∀ l : R, c (QuotientGroup.mk' _ (MarkedLocal.originalFactorIntoClosure Q e hf split 1 l)) =
            μ (QuotientGroup.mk' (pCore 2 R) l)) ∧
          ∀ r, c (QuotientGroup.mk' _ (inclusion
              (MarkedLocal.originalRankOne_le_localClosure Q e split 1) r)) = a r ∧
            a r = b (MarkedLocal.originalRootProjection Q e split 1 r) := by
  let hf := d.hypothesisF11 h hTH
  let := MarkedLocal.originalRadicalInClosure_normal Q e hf split 1
  obtain ⟨T₁,hT₁⟩ := hf.sylow 1
  refine ⟨MarkedLocal.originalSuzukiAllCoverEquiv Q e hf split 1 T₁ hT₁ μ,
    MarkedLocal.originalSuzukiAllRankOneEquiv Q e hf split 1 T₁ hT₁ μ,
    MarkedLocal.suzukiAllLocalEquiv Q e hf split 1 T₁ hT₁ μ,
    MarkedLocal.originalSuzukiAllCoverEquiv_mk_factor Q e hf split 1 T₁ hT₁ μ, ?_⟩
  intro r
  exact ⟨MarkedLocal.originalSuzukiAllCoverEquiv_mk_root Q e hf split 1 T₁ hT₁ μ r,
    MarkedLocal.originalSuzukiAllRankOneEquiv_projection Q e hf split 1 T₁ hT₁ μ r⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The literal Chapter 12 local comparison for every original Suzuki parameter. -/
theorem rankOne_global_suzuki_all_local_identification
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    {m : ℕ} (μ : (R ⧸ pCore 2 R) ≃* SuzukiMatrixGroup m)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    simpleRemainder Q split 1 ≤ localKernel Q 1 ∧
      (simpleRemainder Q split 1).comap (MarkedLocal.endpointMap Q e 1) =
        pCore 2 (parabolic ![L,R] (Global.sourceS L H) 1) ∧
      ∃ a : MarkedLocal.originalRankOne Q e split 1 ≃* R ⧸ pCore 2 R,
        (MarkedLocal.originalPanelKernel (L := ![L,R]) (S := Global.sourceS L H) 1).subgroupOf
          (MarkedLocal.originalRankOne Q e split 1) = ⊥ ∧
        Nat.card (Panel Q 1) ≠ 9 ∧
        ∃ b : localGroup Q split 1 ≃* R ⧸ pCore 2 R,
          ∀ r, a r = b (MarkedLocal.originalRootProjection Q e split 1 r) :=
  prepared_suzuki_all_local_identification d
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH μ Q e split

/-- The literal Chapter 12 cover comparison, preserving the original quotient maps. -/
theorem rankOne_global_suzuki_all_original_cover
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    {m : ℕ} (μ : (R ⧸ pCore 2 R) ≃* SuzukiMatrixGroup m)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    let hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
    letI := MarkedLocal.originalRadicalInClosure_normal Q e hf split 1
    ∃ c : (MarkedLocal.originalLocalClosure Q e split 1 ⧸
        MarkedLocal.originalRadicalInClosure Q e split 1) ≃* SuzukiMatrixGroup m,
      ∃ a : MarkedLocal.originalRankOne Q e split 1 ≃* SuzukiMatrixGroup m,
        ∃ b : localGroup Q split 1 ≃* SuzukiMatrixGroup m,
          (∀ l : R, c (QuotientGroup.mk' _ (MarkedLocal.originalFactorIntoClosure Q e hf split 1 l)) =
            μ (QuotientGroup.mk' (pCore 2 R) l)) ∧
          ∀ r, c (QuotientGroup.mk' _ (inclusion
              (MarkedLocal.originalRankOne_le_localClosure Q e split 1) r)) = a r ∧
            a r = b (MarkedLocal.originalRootProjection Q e split 1 r) :=
  prepared_suzuki_all_original_cover d
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH μ Q e split

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
