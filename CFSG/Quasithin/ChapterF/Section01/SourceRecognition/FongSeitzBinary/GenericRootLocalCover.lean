module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RootLocalCover
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.GenericSylowGeneratedReduction

/-!
# The smaller local cover for the actual Chapter12 pair

For the original selected pair ![L,R], the canonical root-generated
subgroup meets the full panel kernel only in the Cartan, and meets its
two-radical trivially. With the earlier (2B) root-remainder containment,
it maps onto the actual local permutation group with central odd stem
kernel. The original chosen module, full KnownSimple hypothesis, both
endpoint markings and the entire Borel are retained.

Source: Fong--Seitz I (5C), pp.25--26, in the DGS Theorem D reduction.
The independent apartment/exchange input supplies the marked quotient
and split datum. The containment from (2B) and rank-one catalogue still
belong to source recognition; the seven full marked comparisons are not
consequences of this intermediate theorem alone.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
open Chapter6.Source.RankOneGeneric
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  {P : Fin 2 → Subgroup X}

theorem prepared_original_root_kernel
    (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (i : Fin 2) :
    MarkedLocal.originalRankOne Q e split i ⊓
        MarkedLocal.originalPanelKernel (L := ![L,R]) (S := Global.sourceS L H) i ≤
      (Q.tits.B ⊓ Q.tits.N).comap (MarkedLocal.endpointMap Q e i) :=
  MarkedLocal.originalRankOne_inf_kernel_le_cartan Q e (d.hypothesisF11 h hTH) split i

namespace Prepared
variable (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
  (split : SplitData Q.tits) (i : Fin 2)
  (hV : simpleRemainder Q split i ≤ localKernel Q i)

/-- The actual smaller group is the original whole-root cover, with no extra quotient. -/
def originalRootCover :
    letI := MarkedLocal.originalRadicalInClosure_normal Q e (d.hypothesisF11 h hTH) split i
    MarkedLocal.originalRankOne Q e split i ≃*
      MarkedLocal.originalLocalClosure Q e split i ⧸ MarkedLocal.originalRadicalInClosure Q e split i :=
  MarkedLocal.originalRootCoverEquiv Q e (d.hypothesisF11 h hTH) split i hV

end Prepared
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The literal Chapter12 application of the unconditional (5C)(a) kernel bound. -/
theorem rankOne_global_original_root_kernel
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (i : Fin 2) :
    MarkedLocal.originalRankOne Q e split i ⊓
        MarkedLocal.originalPanelKernel (L := ![L,R]) (S := Global.sourceS L H) i ≤
      (Q.tits.B ⊓ Q.tits.N).comap (MarkedLocal.endpointMap Q e i) :=
  prepared_original_root_kernel d
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH Q e split i

/-- The regular local-section premise gives the smaller cover at either selected endpoint. -/
theorem rankOne_global_original_root_cover
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    (MarkedLocal.originalRootProjection Q e split i).ker =
      (MarkedLocal.originalPanelKernel (L := ![L,R]) (S := Global.sourceS L H) i).subgroupOf
        (MarkedLocal.originalRankOne Q e split i) ∧
      Function.Surjective (MarkedLocal.originalRootProjection Q e split i) ∧
      (MarkedLocal.originalRootProjection Q e split i).ker ≤
        center (MarkedLocal.originalRankOne Q e split i) ∧
      Nat.Coprime 2 (Nat.card (MarkedLocal.originalRootProjection Q e split i).ker) ∧
      (MarkedLocal.originalRootProjection Q e split i).ker ≤
        _root_.commutator (MarkedLocal.originalRankOne Q e split i) :=
  ⟨MarkedLocal.originalRootProjection_ker Q e
    (d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH) split i,
    MarkedLocal.original_root_central_odd_cover Q e split i hV⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
