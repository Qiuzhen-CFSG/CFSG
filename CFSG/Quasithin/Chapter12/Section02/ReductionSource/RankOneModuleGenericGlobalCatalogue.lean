module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.Catalogue
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalLinearRecognition
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalSymplecticExtensionOrder.Order
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalG2Recognition
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalTrialityRecognition
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalReeCompletion.Recognition
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitarySource.Recognition
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFiveSource.Completion

/-!
# Complete conditional catalogue assembly for the original Chapter 12 exit

Every prepared concrete comparison now gives the strict GlobalExit: all
seven Lie families, the U₄ graph extension, and the nonmaximal linear M₂₃
branch use their proved ambient recognizers. The U₅(4) branch uses the actual
source completion theorem, with no additional recognition or order premise.

The universal original or reduced marked alternatives first give comparisons
for EVERY selected perfect R. The core bound and diagram exclusion then
construct preparation at the whole residual, to which the same comparison
and ambient recognition apply. The full original Borel and both endpoint
squares survive every regular row; exceptional parabolic and binary type
clauses are excluded using their actual weaker information.

Exhaustive DGS selection and original uniqueness remain explicit source
inputs. This module does not claim unconditional 5.2.3. Their producers are
qt-dgs85-source-assembly and qt-d-1222-rankone-global-uniqueness; final
unconditional assembly remains with the generic-global owner.
Source: Aschbacher--Smith F.1.12, pp.263--264, 5.2.6--10, pp.650--653,
5.3.1--7, pp.658--661, and Chapter 12, p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
include D h hmany hn hpsl hH

/-- Every actual whole-residual catalogue comparison yields the strict
rank-two or actual Mathieu output, with no ambient-recognition callback. -/
theorem rankOne_globalExit_of_prepared_comparison
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (hc : Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))) :
    RankOneModule.GlobalExit G := by
  cases hc with
  | linear F m hm hF he =>
    exact D.rankOne_globalExit_of_linear_amalgam h hmany hn hpsl hH d hp F hm hF he
  | symplectic F m hm hF he =>
    exact D.rankOne_globalExit_of_symplectic_comparison h hmany hn hpsl hH d hp F hm hF he
  | g2 F he =>
    exact D.rankOne_globalExit_of_g2_comparison h hmany hn hpsl hH d hp F he
  | triality m hm he =>
    exact D.rankOne_globalExit_of_triality_comparison h hmany hn hpsl hH d hp m hm he
  | ree m he =>
    exact D.rankOne_globalExit_of_ree_comparison h hmany hn hpsl hH d hp m he
  | unitary m hm he =>
    exact D.rankOne_globalExit_of_unitaryFour h hmany hn hpsl hH d hp m hm (Or.inl he)
  | unitaryExtension m hm he =>
    exact D.rankOne_globalExit_of_unitaryFour h hmany hn hpsl hH d hp m hm (Or.inr he)
  | unitaryFive M he =>
    exact D.rankOne_globalExit_of_unitaryFive_source h hmany hn hpsl hH d hp M he
  | exceptional c he =>
    have hn := d.not_exceptional_parabolic_models
      (D.rankOne_generic_input_of_many h hmany hn hpsl) hp c
    exact (he.elim hn.1 hn.2).elim

/-- The original broad markings are restricted on the SAME arbitrary
selected perfect R, before any whole-residual selection. -/
theorem rankOne_global_comparison_of_original_alternatives
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
    (ha : Global.OriginalExtension.Alternatives L R (Global.sourceS L H)) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) :=
  d.concreteComparison_of_original_alternatives
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp ha

/-- Restore the reduced source alternatives for the same selected perfect R,
including the full original overlap and the possible U₄ graph extension. -/
theorem rankOne_global_comparison_of_reduced_alternatives
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
    (ha : Global.OriginalExtension.ReducedAlternatives L R (Global.sourceS L H)) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) :=
  d.concreteComparison_of_reduced_alternatives
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp ha

variable
  (hpar : 1 < ChapterE.generationParameter H)
  (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
  (hN : localBorel T L ≤ normalizer (residual H : Set G))
  (hunique : ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X →
    X = normalizer (L : Set G))
include hpar hthree hN hunique

/-- Whole-residual preparation from the broad original alternatives. The
universal premise is used at the arbitrary factor selected by the source. -/
theorem rankOne_global_residual_preparation_of_original_alternatives
    (ha : ∀ A B R : Subgroup G, Global.Preparation T L H A B R →
      Group.IsPerfect R → Global.OriginalExtension.Alternatives L R (Global.sourceS L H)) :
    ∃ A B : Subgroup G, Global.Preparation T L H A B (residual H) ∧
      Group.IsPerfect (residual H) := by
  apply D.rankOne_global_residual_preparation_of_concrete_comparisons
    h hmany hn hpsl hH hpar hthree hN hunique
  intro A B R d hp
  exact D.rankOne_global_comparison_of_original_alternatives h hmany hn hpsl hH d hp (ha A B R d hp)

/-- The same universal consumer accepts actual reduced DGS rows; it assumes
neither R = O²(H) nor a pre-existing original concrete comparison. -/
theorem rankOne_global_residual_preparation_of_reduced_alternatives
    (ha : ∀ A B R : Subgroup G, Global.Preparation T L H A B R →
      Group.IsPerfect R → Global.OriginalExtension.ReducedAlternatives L R (Global.sourceS L H)) :
    ∃ A B : Subgroup G, Global.Preparation T L H A B (residual H) ∧
      Group.IsPerfect (residual H) := by
  apply D.rankOne_global_residual_preparation_of_concrete_comparisons
    h hmany hn hpsl hH hpar hthree hN hunique
  intro A B R d hp
  exact D.rankOne_global_comparison_of_reduced_alternatives h hmany hn hpsl hH d hp (ha A B R d hp)

/-- Broad original marked exhaustion and original uniqueness suffice for
the full strict GlobalExit. All comparison and prepared-recognition premises
are discharged internally, including U₅ and the nonmaximal linear branch. -/
theorem rankOne_globalExit_of_original_alternatives
    (ha : ∀ A B R : Subgroup G, Global.Preparation T L H A B R →
      Group.IsPerfect R → Global.OriginalExtension.Alternatives L R (Global.sourceS L H)) :
    RankOneModule.GlobalExit G := by
  obtain ⟨A,B,d,hp⟩ := D.rankOne_global_residual_preparation_of_original_alternatives
    h hmany hn hpsl hH hpar hthree hN hunique ha
  exact D.rankOne_globalExit_of_prepared_comparison h hmany hn hpsl hH d hp
    (D.rankOne_global_comparison_of_original_alternatives h hmany hn hpsl hH d hp
      (ha A B (residual H) d hp))

/-- The literal reduced DGS alternatives also give the original strict
GlobalExit after whole-Borel restoration. Exhaustiveness and uniqueness
remain the genuine independent source inputs. -/
theorem rankOne_globalExit_of_reduced_alternatives
    (ha : ∀ A B R : Subgroup G, Global.Preparation T L H A B R →
      Group.IsPerfect R → Global.OriginalExtension.ReducedAlternatives L R (Global.sourceS L H)) :
    RankOneModule.GlobalExit G := by
  obtain ⟨A,B,d,hp⟩ := D.rankOne_global_residual_preparation_of_reduced_alternatives
    h hmany hn hpsl hH hpar hthree hN hunique ha
  exact D.rankOne_globalExit_of_prepared_comparison h hmany hn hpsl hH d hp
    (D.rankOne_global_comparison_of_reduced_alternatives h hmany hn hpsl hH d hp
      (ha A B (residual H) d hp))
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
