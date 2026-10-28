module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.TrialityReducedComparison
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.TrialityAllDegrees
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalOriginalTrialityExtension

/-!
# Original and Chapter 12 applications of reduced Triality recognition

Unequal original PSL2 factors on the actual marked reduced hexagon produce
the native reduced comparison. At the selected-perfect-factor consumer,
the binary central endpoint is excluded by its solvability. Native restoration
then identifies the original field degree and forces the selected left endpoint
to be central. The output retains the same original S and selected R, both
endpoint maps, the whole Borel, and the original right-core equality.

The original KnownSimple/proper-K and perfect-R hypotheses are those of the
existing restoration consumer. Nonperfect binary input remains admitted by the
reduced comparison in the parent module; it is not excluded here without those
consumer hypotheses.

Source: DGS (1985), (15.2), pp.226--228; AS F.1.12, pp.263--264,
and the Chapter 12 chosen-module application, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.TrialityReducedComparison
open FongSeitzBinary OriginalExtension SuzukiContainment
open Chapter6.Source.RankOneGeneric
variable {G X : Type*} [Group G] [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (hrot : rotationOrder Q = 6)
section Original
variable [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {K W H A B R : Subgroup G} {n : ℕ}
  (d : Global.Preparation T K H A B R)
  (input : Input κ T K W n) (hTH : (T : Subgroup G) ≤ H)
  (hp : Group.IsPerfect R)
  (e₀ : Iso (reducedAmalgam ![K,R] (Global.sourceS K H)) Q.standardAmalgam)

include Q split hrot d input hTH hp e₀ in
/-- Restore the original selected pair from the constructed reduced comparison.
The degree-one exclusion uses the actual selected-perfect-factor hypotheses. -/
theorem original_recognition
    (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hsmall : ClassicalGroup.IsPSL ((![K,R] i) ⧸ pCore 2 (![K,R] i)) 2 (2^a))
    (hlarge : ClassicalGroup.IsPSL ((![K,R] j) ⧸ pCore 2 (![K,R] j)) 2 (2^b)) :
    b = 3*a ∧ a = n ∧ j = 1 ∧
      (R ⊔ Global.sourceS K H).pCoreIn 2 = R.pCoreIn 2 ∧
      Global.sourceS K H ≤ R ∧
      Nonempty (Iso (Global.sourceParabolicAmalgam ![K,R] (Global.sourceS K H))
        (Global.OriginalTriality.orientedAmalgam a ha .central)) ∧
      Global.ConcreteAmalgamComparison
        (Global.sourceParabolicAmalgam ![K,R] (Global.sourceS K H)) := by
  obtain ⟨hc,⟨e⟩⟩ := reduced_comparison_of_factor_types
    (d.hypothesisF11 input hTH) Q e₀ split hrot i j hij ha hab hsmall hlarge
  have hm2 := triality_reduced_parameter d input hTH hp a ha (nativeOrientation j) e
  obtain ⟨cmp,hd,hi⟩ := triality_original_comparison_of_reduced_iso
    d input hTH a ha hm2 (nativeOrientation j) e hp
  have hj : j = 1 := by
    fin_cases j
    · simp [TrialityNative.side] at hi
    · rfl
  obtain ⟨hcore,hcontain⟩ := triality_original_core_and_containment_of_reduced_iso
    d input hTH a ha hm2 (nativeOrientation j) e hp
  rw [hi] at cmp
  exact ⟨hc,hd,hj,hcore,hcontain,cmp,
    triality_concreteComparison_of_reduced_iso d input hTH a ha hm2 (nativeOrientation j) e hp⟩

include Q split hrot d input hTH hp e₀ in
/-- The chosen left factor forces the smaller field and central orientation;
the original opposite linear degree is therefore exactly its triple. -/
theorem original_selected_unequal
    {r : ℕ} (hr : 0 < r) (hne : r ≠ n)
    (hR : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^r)) :
    r = 3*n ∧
      (R ⊔ Global.sourceS K H).pCoreIn 2 = R.pCoreIn 2 ∧
      Global.sourceS K H ≤ R ∧
      Nonempty (Iso (Global.sourceParabolicAmalgam ![K,R] (Global.sourceS K H))
        (Global.OriginalTriality.orientedAmalgam n (Nat.zero_lt_of_lt input.exponent) .central)) ∧
      Global.ConcreteAmalgamComparison
        (Global.sourceParabolicAmalgam ![K,R] (Global.sourceS K H)) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨_,_,hj,_⟩ := original_recognition Q split hrot d input hTH hp e₀
      1 0 (by decide) hr hlt hR input.linear
    exact False.elim ((show (0 : Fin 2) ≠ 1 by decide) hj)
  · obtain ⟨hc,_,_,hcore,hcontain,cmp,hcatalogue⟩ :=
      original_recognition Q split hrot d input hTH hp e₀
        0 1 (by decide) (Nat.zero_lt_of_lt input.exponent) hgt input.linear hR
    exact ⟨hc,hcore,hcontain,cmp,hcatalogue⟩

end Original
end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.TrialityReducedComparison

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Chapter6.Source.RankOneGeneric
open ChapterF.Source.DGS85.OriginalExtension
open ChapterF.Source.DGS85.Assembly.TrialityReducedComparison
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D in
/-- Unequal original linear factors on the marked reduced hexagon give the
original triality row, its forced cubic degree and the original core and Sylow
containment. The full KnownSimple/proper-K preparation is unchanged. -/
theorem rankOne_reduced_unequal_linear_triality
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
    (Q : MarkedQuotient P)
    (mark : Iso (reducedAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (hrot : rotationOrder Q = 6)
    {r : ℕ} (hr : 0 < r) (hne : r ≠ n)
    (hR : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^r)) :
    r = 3*n ∧
      (R ⊔ Global.sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧
      Global.sourceS L H ≤ R ∧
      Nonempty (Iso (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H))
        (Global.OriginalTriality.orientedAmalgam n (Nat.zero_lt_of_lt hn) .central)) ∧
      Global.ConcreteAmalgamComparison
        (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) :=
  original_selected_unequal Q split hrot d
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp mark hr hne hR
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
