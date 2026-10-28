module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OddSinglePerfectFactor
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# The selected generic pair on an odd Weyl branch

Apply the one-perfect-endpoint reduction to the literal pair ![L,R]. The
original generic input already makes L perfect. If the actual Weyl rotation
is odd, the whole marked quotient is perfect and simple; the original PSL₂
field gives generating additive coordinates for all canonical Weyl roots.
No perfectness of the selected second factor R is assumed. The Chapter12
applications preserve KnownSimple, the chosen module, full Borel and both
endpoint maps. The quotient, splitness and oddness remain explicit inputs,
with the first two supplied by the apartment/exchange producer and oddness
retained for source row selection. No mixed root relations are asserted.

Source: Fong–Seitz I (1A), p.3; DGS, Groups and Graphs, pp.80–81 and
Theorem D, p.224; Aschbacher–Smith 5.2.6 and Chapter12, p.795.
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

/-- The selected source quotient is perfect on the actual odd branch without
assuming perfectness of its second local factor. -/
theorem prepared_marked_quotient_isPerfect_of_source_odd
    (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : Odd (rotationOrder Q)) :
    Group.IsPerfect (X ⧸ Q.D) :=
  MarkedLocal.quotient_isPerfect_of_perfect_first_factor_of_odd Q e
    (d.hypothesisF11 h hTH) split (Chapter1.mem_L_isPerfect h.local_mem.1.1) hm

/-- The same selected odd-branch quotient is simple without second-factor
perfectness. -/
theorem prepared_marked_quotient_isSimple_of_source_odd
    (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : Odd (rotationOrder Q)) :
    IsSimpleGroup (X ⧸ Q.D) :=
  MarkedLocal.quotient_isSimple_of_perfect_first_factor_of_odd Q e
    (d.hypothesisF11 h hTH) split (Chapter1.mem_L_isPerfect h.local_mem.1.1) hm

/-- Single-field generating root parameters for the same literal selected
odd source quotient, with its original first-factor model. -/
theorem prepared_marked_quotient_odd_root_parameters_of_source
    (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (Q : MarkedQuotient P)
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
  MarkedLocal.exists_odd_linear_root_parameters_of_source Q e
    (d.hypothesisF11 h hTH) split (Chapter1.mem_L_isPerfect h.local_mem.1.1) hm h.linear

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The literal Chapter12 odd-branch quotient is perfect with no additional
perfectness assumption on R. -/
theorem rankOne_global_marked_quotient_isPerfect_of_source_odd
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : Odd (rotationOrder Q)) :
    Group.IsPerfect (X ⧸ Q.D) :=
  prepared_marked_quotient_isPerfect_of_source_odd d
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH Q e split hm

/-- The literal Chapter12 odd-branch quotient is simple with no additional
perfectness assumption on R. -/
theorem rankOne_global_marked_quotient_isSimple_of_source_odd
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : Odd (rotationOrder Q)) :
    IsSimpleGroup (X ⧸ Q.D) :=
  prepared_marked_quotient_isSimple_of_source_odd d
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH Q e split hm

/-- The exact Chapter12 consumer receives generating first-field parameters
on the literal quotient's actual Weyl roots, even when R is not perfect. -/
theorem rankOne_global_marked_quotient_odd_root_parameters_of_source
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
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
  prepared_marked_quotient_odd_root_parameters_of_source d
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH Q e split hm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
