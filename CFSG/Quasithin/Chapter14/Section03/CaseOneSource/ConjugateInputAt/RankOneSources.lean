module

public import CFSG.Quasithin.Chapter14.Section03.CaseOneSource.ConjugateInputAt
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.LocalParameterRankOneSources

/-!
# The original rank-one source implications in the guarded conjugator application

Use the actual Hypothesis1311 at the original G,T to discharge A₇ exclusion,
then apply the two earlier rank-one sources to each local residual via its
literal K/O₂(K) quotient. The Counterexample application supplies the ambient
guard itself. The chosen V and both 12.4.1 guards are unchanged.

The generic and small source implications remain with their existing producers,
qt-d-1222-rankone-generic and qt-d-1222-rankone-recognition. Their final discharge
remains with qt-d-1241-l3-conjugate; no unconditional source theorem is asserted.
Source: Aschbacher–Smith, 12.3.2, 12.4.1 and the original 14.3 counterexample,
printed pp.807,812,990–992.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.CaseOneSource
open Chapter12.Section02 Chapter12.Section04.SmallFusion ChapterE
open Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
open Chapter13.Section01 Chapter13.Section03.SourceClassification
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

variable
    (generic : ∀ (K W : Subgroup G),
      Hypothesis1223 KnownSimple.IsKnownSimple T K → ChosenModule T K W →
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      ∀ n : ℕ, 1 < n → ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n) →
      RankOneModule.GenericExit T K)
    (small : ∀ (K W : Subgroup G),
      Hypothesis1223 KnownSimple.IsKnownSimple T K → ChosenModule T K W →
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      ∀ n : ℕ, 1 < n → ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n) →
      RankOneModule.SmallExit T K)

include generic small

/-- The original ambient guard eliminates A₇; the literal rank-one source
contracts supply the residual exits without a separate local callback. -/
theorem noncommutingConjugate_of_guarded_rankOne_sources
    (h13 : Hypothesis1311 T)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hZ : centralizer (sylowCenterSeed T : Set G) ≤ normalizer (L : Set G)) :
    letI := D.elementary
    1 < globalS V →
    ∃ g : G, ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≤ V ⊓ V.map (MulAut.conj g).toMonoidHom :=
  noncommutingConjugate_of_rankOne_sources_at generic small h D structural modules hmany hZ
    (fun _ hY => alternatingSeven_excluded_of_source_inputs_at h13 hY hmany structural modules)

/-- The actual counterexample supplies Hypothesis1311 at the same G,T,
and the source implication constructs a conjugate of its original chosen V. -/
theorem noncommutingConjugate_of_counterexample_rankOne_sources
    (d : Counterexample T L) (hmax : FaithfulMaximalLocal T L)
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hZ : centralizer (sylowCenterSeed T : Set G) ≤ normalizer (L : Set G)) :
    letI := D.elementary
    1 < globalS V →
    ∃ g : G, ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≤ V ⊓ V.map (MulAut.conj g).toMonoidHom := by
  have h13 := FaithfulSource.Counterexample.hypothesis1311 d
  exact noncommutingConjugate_of_guarded_rankOne_sources generic small h13
    (h13.hypothesis1223 hmax hq) D structural modules hmany hZ

end CFSG.Quasithin.Chapter14.Section03.CaseOneSource
