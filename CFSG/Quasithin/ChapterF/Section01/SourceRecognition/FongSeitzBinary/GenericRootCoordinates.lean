module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearRootCoordinates
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.PerfectQuotient
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# Uniform roots and their first field on the selected generic pair

The genuine generic input and selected-perfect-factor premise make both
original factors perfect. The uniform Cartan argument places both canonical
simple roots in O² of the same independently marked finite quotient. The
original first-factor PSL₂(2ⁿ) witness gives exact additive coordinates on
its first root over a field of order 2ⁿ, including the literal Chapter12
chosen-module application with full KnownSimple scope.

The final simplicity application retains the independent ordered-root
premise from qt-dgs85-split-root-coordinates. Apartment and splitness data
remain with qt-dgs85-apartment-exchange. The source assembly and original
generic-global owner retain their final discharge, while this recognition
family still owns root-field compatibility, seven marked Lie comparisons
and nonperfect branches. No model catalogue tag supplies those conclusions.

Source: DGS, Groups and Graphs, Part II, pp.80–81 and Theorem D, p.224;
Aschbacher–Smith 5.2.6, pp.650–651, and Chapter12, p.795.
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

private theorem prepared_perfect_pair (h : Input κ T L W n) (hR : Group.IsPerfect R) :
    ∀ i : Fin 2, Group.IsPerfect (![L,R] i) := by
  intro i
  fin_cases i
  · exact Chapter1.mem_L_isPerfect h.local_mem.1.1
  · exact hR

/-- Both canonical roots lie in the same quotient's two-residual. -/
theorem prepared_marked_quotient_roots_le_twoResidual
    (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hR : Group.IsPerfect R) (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (i : Fin 2) :
    simpleRoot Q split i ≤ pResidual 2 (X ⧸ Q.D) :=
  MarkedLocal.simpleRoot_le_twoResidual Q e (d.hypothesisF11 h hTH)
    (prepared_perfect_pair h hR) split i

/-- The original first-factor field parametrizes the actual first simple root. -/
theorem prepared_marked_quotient_first_root_coordinates
    (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    Nat.card (simpleRoot Q split 0) = 2^n ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
        Nat.card F = 2^n ∧ Nonempty (simpleRoot Q split 0 ≃* Multiplicative F) :=
  MarkedLocal.exists_linear_root_coordinates Q e (d.hypothesisF11 h hTH) split 0
    (Chapter1.mem_L_isPerfect h.local_mem.1.1) h.linear

/-- The selected-perfect-factor quotient is simple once the independently
constructed actual Weyl roots generate U. -/
theorem prepared_marked_quotient_isSimple_of_weyl_roots
    (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hR : Group.IsPerfect R) (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits)
    (hroots : split.U ≤ ⨆ (i : Fin 2) (n : Q.tits.N),
      rightConjugate (simpleRoot Q split i) (n : X ⧸ Q.D)) :
    IsSimpleGroup (X ⧸ Q.D) :=
  MarkedLocal.isSimple_of_weyl_roots Q e (d.hypothesisF11 h hTH)
    (prepared_perfect_pair h hR) split hroots

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The literal Chapter12 pair, with every rank-one constructor covered at the second endpoint. -/
theorem rankOne_global_marked_quotient_roots_le_twoResidual
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (hR : Group.IsPerfect R) (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (i : Fin 2) :
    simpleRoot Q split i ≤ pResidual 2 (X ⧸ Q.D) :=
  prepared_marked_quotient_roots_le_twoResidual d
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH hR Q e split i

/-- Exact local field size and additive coordinates on Chapter12's first source root. -/
theorem rankOne_global_marked_quotient_first_root_coordinates
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    Nat.card (simpleRoot Q split 0) = 2^n ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
        Nat.card F = 2^n ∧ Nonempty (simpleRoot Q split 0 ≃* Multiplicative F) :=
  prepared_marked_quotient_first_root_coordinates d
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH Q e split

/-- The actual Chapter12 whole-quotient application, conditional only on
the earlier marked split quotient and the independent ordered-root generation. -/
theorem rankOne_global_marked_quotient_isSimple_of_weyl_roots
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (hR : Group.IsPerfect R) (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits)
    (hroots : split.U ≤ ⨆ (i : Fin 2) (n : Q.tits.N),
      rightConjugate (simpleRoot Q split i) (n : X ⧸ Q.D)) :
    IsSimpleGroup (X ⧸ Q.D) :=
  prepared_marked_quotient_isSimple_of_weyl_roots d
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH hR Q e split hroots

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
