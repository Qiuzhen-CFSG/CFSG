module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SylowGeneratedReduction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# The selected generic pair with no second-factor perfectness premise

The preparation supplies F.1.1 for the literal pair ![L,R] and
S = O₂(N_G(L) intersect H). Its first factor is perfect by local-family
membership. The source Sylow-generation argument therefore proves a
simple perfect two-residual in the same finite marked quotient, even
when the selected R is not assumed perfect. Its actual Weyl roots
generate the entire quotient in all cases.

The Chapter12 applications preserve the original chosen module,
KnownSimple hypothesis, full overlap and both marked endpoint maps.
The quotient and splitness still come from the independent apartment
and exchange construction. These statements discharge normal generation,
residual perfectness and the single-component reduction, not the seven
marked Lie comparisons or the whole-quotient nonperfect cases.

Source: Fong–Seitz I, Theorem A and (1A), pp.1–3; DGS Theorem D, p.224;
Aschbacher–Smith 5.2.6, pp.650–651, and Chapter12, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootGeneration
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
open Chapter6.Source.RankOneGeneric
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  {P : Fin 2 → Subgroup X}

/-- The source normal closure and canonical root span are the whole selected quotient. -/
theorem prepared_marked_normal_generation_of_source
    (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    split.unipotentClosure = ⊤ ∧ weylRootSpan Q split = ⊤ :=
  ⟨MarkedLocal.unipotentClosure_eq_top_of_source Q e (d.hypothesisF11 h hTH) split,
    MarkedLocal.weylRootSpan_eq_top_of_source Q e (d.hypothesisF11 h hTH) split⟩

/-- The selected factor need not be perfect for the quotient's residual to be simple. -/
theorem prepared_marked_simple_residual_of_source
    (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    Group.IsPerfect (pResidual 2 (X ⧸ Q.D)) ∧
      IsSimpleGroup (pResidual 2 (X ⧸ Q.D)) ∧
      pResidual 2 (X ⧸ Q.D) = solvableResidual (X ⧸ Q.D) :=
  ⟨MarkedLocal.twoResidual_isPerfect_of_source Q e (d.hypothesisF11 h hTH) split,
    MarkedLocal.twoResidual_isSimple_of_perfect_factor Q e (d.hypothesisF11 h hTH) split 0
      (Chapter1.mem_L_isPerfect h.local_mem.1.1),
    MarkedLocal.twoResidual_eq_solvableResidual_of_source Q e (d.hypothesisF11 h hTH) split⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- Normal generation for the literal Chapter12 pair, with no additional local perfectness. -/
theorem rankOne_global_marked_normal_generation_of_source
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    split.unipotentClosure = ⊤ ∧ weylRootSpan Q split = ⊤ :=
  prepared_marked_normal_generation_of_source d
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH Q e split

/-- The exact Chapter12 consumer has a simple perfect residual without perfectness of R. -/
theorem rankOne_global_marked_simple_residual_of_source
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    Group.IsPerfect (pResidual 2 (X ⧸ Q.D)) ∧
      IsSimpleGroup (pResidual 2 (X ⧸ Q.D)) ∧
      pResidual 2 (X ⧸ Q.D) = solvableResidual (X ⧸ Q.D) :=
  prepared_marked_simple_residual_of_source d
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH Q e split

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
