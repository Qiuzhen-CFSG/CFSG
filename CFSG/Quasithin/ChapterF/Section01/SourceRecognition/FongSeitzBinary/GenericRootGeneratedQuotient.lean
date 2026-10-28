module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OddLinearRootCoordinates
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# Whole-quotient simplicity for the literal selected-perfect generic pair

The genuine generic input makes its first factor perfect, and the selected
second factor retains its original perfectness premise. Apply the now
unconditional ordered-root reduction to the independently marked split
quotient. This removes the extra generation premise from the earlier
Chapter12 simple-socle/whole-quotient application, preserving the complete
KnownSimple scope and the same chosen module and endpoint maps. In the
actual odd-Weyl branch the original first-factor field also parametrizes
all canonical roots by conjugation, and these maps generate the quotient.

The earlier geometric/split quotient and eventual seven-row comparison
still require their source proofs; simplicity alone is not recognition.
Source: DGS, Groups and Graphs, pp.80–81 and Theorem D, p.224;
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

/-- The same whole marked generic quotient is perfect. -/
theorem prepared_marked_quotient_isPerfect
    (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hR : Group.IsPerfect R) (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    Group.IsPerfect (X ⧸ Q.D) :=
  MarkedLocal.quotient_isPerfect Q e (d.hypothesisF11 h hTH)
    (prepared_perfect_pair h hR) split

/-- The same whole marked generic quotient is simple. -/
theorem prepared_marked_quotient_isSimple
    (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hR : Group.IsPerfect R) (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    IsSimpleGroup (X ⧸ Q.D) :=
  MarkedLocal.quotient_isSimple Q e (d.hypothesisF11 h hTH)
    (prepared_perfect_pair h hR) split

/-- The original first local field parametrizes all Weyl roots on the actual odd branch. -/
theorem prepared_marked_quotient_odd_root_parameters
    (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hR : Group.IsPerfect R) (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : Odd (rotationOrder Q)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = 2^n ∧
      ∃ x : (Fin 2 × Weyl Q) → Multiplicative K →* X ⧸ Q.D,
        (∀ j, (x j).range = rightConjugate (simpleRoot Q split j.1)
          (representative j.2 : X ⧸ Q.D)) ∧
        (∀ j, Function.Injective (x j)) ∧
        closure {g | ∃ j a, g = x j a} = ⊤ :=
  MarkedLocal.exists_odd_linear_root_parameters Q e (d.hypothesisF11 h hTH) split hm
    (prepared_perfect_pair h hR) h.linear

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The literal Chapter12 whole-quotient conclusion, with ordered-root generation discharged. -/
theorem rankOne_global_marked_quotient_isPerfect
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (hR : Group.IsPerfect R) (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    Group.IsPerfect (X ⧸ Q.D) :=
  prepared_marked_quotient_isPerfect d
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH hR Q e split

/-- The literal Chapter12 whole-quotient conclusion, with ordered-root generation discharged. -/
theorem rankOne_global_marked_quotient_isSimple
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (hR : Group.IsPerfect R) (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    IsSimpleGroup (X ⧸ Q.D) :=
  prepared_marked_quotient_isSimple d
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH hR Q e split

/-- The Chapter12 first-field parameter is retained on every constructed Weyl root. -/
theorem rankOne_global_marked_quotient_odd_root_parameters
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (hR : Group.IsPerfect R) (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : Odd (rotationOrder Q)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = 2^n ∧
      ∃ x : (Fin 2 × Weyl Q) → Multiplicative K →* X ⧸ Q.D,
        (∀ j, (x j).range = rightConjugate (simpleRoot Q split j.1)
          (representative j.2 : X ⧸ Q.D)) ∧
        (∀ j, Function.Injective (x j)) ∧
        closure {g | ∃ j a, g = x j a} = ⊤ :=
  prepared_marked_quotient_odd_root_parameters d
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH hR Q e split hm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
