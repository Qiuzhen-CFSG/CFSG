module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SimpleSocle
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.GenericMinimalNormal
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# A simple socle for the literal generic selected-factor consumer

The original preparation constructs F.1.1 for ![L,R] and
S = O₂(N_G(L) ∩ H). Local-family membership supplies perfectness of L;
the existing comparison premise supplies perfectness of R. Applying the
new source reduction proves that the same finite marked quotient has
simple two-residual. The Chapter12 application obtains the generic input
from the original chosen-module hypotheses and retains the selected R.

This discharges the number-of-simple-components step, including local
normal generation and solvability of proper normal local subgroups.
It does not identify a Lie row. All seven marked model comparisons,
the remaining full Fong–Seitz reduction, and the binary/nonperfect branches
remain obligations of this recognition family. The earlier geometric
quotient, Cartan/root and splitness premises retain their apartment/exchange
producer; qt-dgs85-source-assembly and the original generic-global owner
retain their final discharge. The explicit SourceQuotient here is a quotient
of the actual generated carrier, not an assertion of descent from the
universal geometric quotient. The Theory reduction also applies directly
to a finite universal quotient once its local premises are transported.

Source: DGS, Groups and Graphs, Part II, pp.80–81 and Theorem D on p.224;
Aschbacher–Smith 5.2.6, pp.650–651, and its Chapter12 application, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}

/-- The selected perfect-factor branch has a simple two-residual. -/
theorem prepared_quotient_twoResidual_isSimple
    (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hR : Group.IsPerfect R)
    (Q : SourceQuotient ![L,R] (Global.sourceS L H)) (split : SplitData Q.tits) :
    IsSimpleGroup (pResidual 2 ((generated ![L,R] (Global.sourceS L H)) ⧸ Q.D)) := by
  apply quotient_twoResidual_isSimple (d.hypothesisF11 h hTH) _ Q split
  intro i
  fin_cases i
  · exact Chapter1.mem_L_isPerfect h.local_mem.1.1
  · exact hR

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} (D : ChosenModule T L V)
include D

/-- Apply the simple-socle reduction to the original Chapter12 comparison
consumer, retaining its selected R, perfectness premise and marked quotient. -/
theorem rankOne_global_quotient_twoResidual_isSimple
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (hR : Group.IsPerfect R)
    (Q : SourceQuotient ![L,R] (Global.sourceS L H)) (split : SplitData Q.tits) :
    IsSimpleGroup (pResidual 2 ((generated ![L,R] (Global.sourceS L H)) ⧸ Q.D)) :=
  prepared_quotient_twoResidual_isSimple d
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH hR Q split

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
