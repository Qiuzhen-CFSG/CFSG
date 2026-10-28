module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.CartanTransport
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# Simple-root containment for the selected generic source pair

The original generic input already identifies the first local quotient
with PSL₂(2ⁿ), with n > 1, and local-family membership proves that factor
perfect. The Cartan transport therefore places the first canonical simple
root in its actual marked factor image. When the selected second factor
is also perfect, the established two-residual formula puts this same root
in O² of the finite marked quotient.

The Chapter12 application uses the literal chosen-module input, retains
the full KnownSimple scope and selected pair, and accepts both endpoint
squares and the entire overlap through the supplied amalgam isomorphism.
The quotient carrier may be the universal apartment quotient; no descent
to the original generated group is required. This removes the first-root
containment premise only. Earlier apartment and splitness inputs retain
their existing producers. The remaining root-generation reduction, seven
marked Lie comparisons and nonperfect branches remain with this recognition
family; the original source and generic-global owners retain final assembly.

Source: DGS, Groups and Graphs, Part II, pp.80–81 and Theorem D, p.224;
Aschbacher–Smith 5.2.6, pp.650–651, with the Chapter12 application, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
open Chapter6.Source.RankOneGeneric
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  {P : Fin 2 → Subgroup X}

/-- The selected pair's first root lies in the marked original L image.
All local-model and fixed-pair premises come from the actual generic input. -/
theorem prepared_marked_quotient_first_root_le_factor
    (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    simpleRoot Q split 0 ≤ (MarkedLocal.factorMap Q e 0).range := by
  apply MarkedLocal.simpleRoot_le_factor_linear Q e (d.hypothesisF11 h hTH) split 0
    (Chapter1.mem_L_isPerfect h.local_mem.1.1) n
    (by have hn := h.exponent; omega)
  exact h.linear

/-- The actual selected-perfect-factor consumer places its first simple root
in the same quotient's two-residual. No whole-quotient recognition is assumed. -/
theorem prepared_marked_quotient_first_root_le_twoResidual
    (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hR : Group.IsPerfect R) (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    simpleRoot Q split 0 ≤ pResidual 2 (X ⧸ Q.D) := by
  have hp : ∀ i : Fin 2, Group.IsPerfect (![L,R] i) := by
    intro i
    fin_cases i
    · exact Chapter1.mem_L_isPerfect h.local_mem.1.1
    · exact hR
  rw [(MarkedLocal.perfect_residual Q e (d.hypothesisF11 h hTH) hp split).1]
  exact (prepared_marked_quotient_first_root_le_factor d h hTH Q e split).trans le_sup_left

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The Chapter12 chosen-module application retains the full KnownSimple input
and the literal selected pair, including both marked endpoint maps and overlap. -/
theorem rankOne_global_marked_quotient_first_root_le_twoResidual
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (hR : Group.IsPerfect R) (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    simpleRoot Q split 0 ≤ pResidual 2 (X ⧸ Q.D) :=
  prepared_marked_quotient_first_root_le_twoResidual d
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH hR Q e split

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
