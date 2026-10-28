module
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.LocalParameterSourceExits
public import CFSG.Quasithin.Chapter13.Section03.SourceClassification.AlternatingSevenInputAt
public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource.Hypothesis1311

/-!
# The guarded original conjugator in the Chapter14 counterexample

The accepted same-G,T A₇ theorem uses Hypothesis1311 and the earlier local
12.2.2 inputs. It removes the proper A₇ overcomponent from the local
12.3.2 classification. The checked whole-layer restriction and parameter
argument then construct the original ambient conjugator, preserving both
Omega-center and globalS guards and the literal conjugation map.

The original Counterexample supplies Hypothesis1311; no universal A₇
exclusion is inferred. Only the generic and small 6.2.20 source exits remain
with qt-d-1222-rankone-module. Final discharge of those exits stays with
qt-d-1241-l3-conjugate; qt-d-1242-l3-commutator-source owns the subsequent
symmetric-plane and fixed-involution fusion assembly. No fixed-space
vanishing or naturality is assumed here.
Source: Aschbacher–Smith, 12.3.2 and 12.4.1, printed pp.807,812,
and the original 14.3 counterexample, printed pp.990–992.
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
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}

/-- The actual ambient 13.1.1 guard discharges the A₇ alternative in 12.3.2.
The H-star witness itself supplies the multiple-overgroup hypothesis. -/
theorem local_classification_of_guarded_source_exits
    (h13 : Hypothesis1311 T)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hZ : centralizer (sylowCenterSeed T : Set G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (exits : Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) →
      Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T (localResidual H) ∧
        RankOneModule.SmallExit T (localResidual H)) :
    Group.IsSolvable H ∨
      (Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5)) ∧
        FaithfulMaximalLocal T (localResidual H) ∧
        Chapter6.Source.IsOneOrTwoA5Modules (localResidual H)
          ⁅conjugateSpanBy (sylowCenterSeed T) (localResidual H),localResidual H⁆) := by
  apply local_classification_of_source_exits_at h structural modules hZ hH _ exits
  intro Y hY
  exact alternatingSeven_excluded_of_source_inputs_at h13 hY
    (local_hstar_many h structural hH) structural modules

/-- The guarded source application has no A₇-exclusion or moved-module callback.
The residual source exits remain with the existing 6.2.20 producer. -/
theorem noncommutingConjugate_of_guarded_source_exits
    (h13 : Hypothesis1311 T)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hZ : centralizer (sylowCenterSeed T : Set G) ≤ normalizer (L : Set G))
    (exits : ∀ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) →
      Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T (localResidual H) ∧
        RankOneModule.SmallExit T (localResidual H)) :
    letI := D.elementary
    1 < globalS V →
    ∃ g : G, ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ ∧
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≤ V ⊓ V.map (MulAut.conj g).toMonoidHom :=
  noncommutingConjugate_of_source_exits_at h D structural modules hmany hZ
    (fun _ hY => alternatingSeven_excluded_of_source_inputs_at h13 hY hmany structural modules) exits

/-- The original Counterexample supplies both ambient source hypotheses for
its actual chosen module, retaining the guards used before the fusion argument. -/
theorem noncommutingConjugate_of_counterexample_source_exits
    (d : Counterexample T L) (hmax : FaithfulMaximalLocal T L)
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hZ : centralizer (sylowCenterSeed T : Set G) ≤ normalizer (L : Set G))
    (exits : ∀ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) →
      Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T (localResidual H) ∧
        RankOneModule.SmallExit T (localResidual H)) :
    letI := D.elementary
    1 < globalS V →
    ∃ g : G, ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ ∧
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≤ V ⊓ V.map (MulAut.conj g).toMonoidHom :=
  noncommutingConjugate_of_guarded_source_exits (FaithfulSource.Counterexample.hypothesis1311 d)
    ((FaithfulSource.Counterexample.hypothesis1311 d).hypothesis1223 hmax hq) D structural modules hmany hZ exits
end CFSG.Quasithin.Chapter14.Section03.CaseOneSource
