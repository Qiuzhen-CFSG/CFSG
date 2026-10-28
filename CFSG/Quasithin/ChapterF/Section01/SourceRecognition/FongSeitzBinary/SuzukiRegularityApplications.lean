module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SuzukiLocal
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SuzukiIdentificationApplications

/-!
# The regular Suzuki local comparison on the Chapter 12 pair

The original selected perfect factor R supplies its actual Suzuki
quotient. The proved nonlinear (2B) theorem now discharges the only kernel
containment premise of the previous local comparison. Its root-generated
group and full local permutation image identify compatibly with R/O₂(R),
and the canonical remainder pulls back to the original endpoint two-core.
The root-kernel and degree-nine exclusions are reused with their original
markings; no independent local Suzuki tag is assumed.

The same preparation, finite marked quotient, full Borel and split datum
are retained in the literal Chapter 12 application. The earlier geometric
inputs belong to qt-dgs85-apartment-exchange. The assembly owners retain
full endpoint/model selection and all other source branches.
Source: Fong--Seitz I (2B), (5C), pp.7--9,25--26; AS 12.2.2 and F.1.1.
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

/-- Discharge (2B) at the actual selected Suzuki endpoint, with no new
kernel-containment or local-model premise. -/
theorem prepared_suzuki_regular_local_identification
    (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
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
  have hV := MarkedLocal.suzuki_remainder_le_kernel_of_perfect Q e hf split 1 T₁ hT₁ hp μ
  obtain ⟨a,hker,hdeg,hlocal⟩ := prepared_suzuki_local_identification d h hTH hp μ Q e split
  exact ⟨hV,MarkedLocal.remainder_comap_of_containment Q e split 1 hV,
    a,hker,hdeg,hlocal hV⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The literal Chapter 12 Suzuki branch supplies the canonical remainder,
original two-core and compatible local identifications on the same marking. -/
theorem rankOne_global_suzuki_regular_local_identification
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
    simpleRemainder Q split 1 ≤ localKernel Q 1 ∧
      (simpleRemainder Q split 1).comap (MarkedLocal.endpointMap Q e 1) =
        pCore 2 (parabolic ![L,R] (Global.sourceS L H) 1) ∧
      ∃ a : MarkedLocal.originalRankOne Q e split 1 ≃* R ⧸ pCore 2 R,
        (MarkedLocal.originalPanelKernel (L := ![L,R]) (S := Global.sourceS L H) 1).subgroupOf
          (MarkedLocal.originalRankOne Q e split 1) = ⊥ ∧
        Nat.card (Panel Q 1) ≠ 9 ∧
        ∃ b : localGroup Q split 1 ≃* R ⧸ pCore 2 R,
          ∀ r, a r = b (MarkedLocal.originalRootProjection Q e split 1 r) :=
  prepared_suzuki_regular_local_identification d
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH hp μ Q e split

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
