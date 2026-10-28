module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.NonBender.Preparation
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Assembly
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Inputs

/-!
# Reusing the earlier seed and closure calculations in the centralizer

The earlier normal-intermediate-subgroup calculation shows that a strict
seed closure cannot lie in M: otherwise the centralizer normalizes X and
its closure equals X. The actual parabolic seed supplies the Xi input in
the involution centralizer. The common wreath-action sieve then gives the
component models and the exact orbit equality. Containment of that component
in M would put its whole T-orbit in M, contradicting the proved escape.

This discharges `StrictClosureAt` conditionally on three existing earlier
source obligations, with no later S₅-wreath-recognition premise. Their
original producers retain responsibility for proving them.
Source: Aschbacher--Smith 10.1.3, 10.2.4 and 10.3.3, pp.742,747,756.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.NonBender
open Chapter3.Section02
open Overgroups.Closure Geometry.CoreReduced
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreeSurvivor T D}

/-- Restriction to the earlier diagonal configuration uses only original
fields of the supplied centralizer data. -/
theorem centralizer_configuration
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (d : CentralizerData T D s) : Configuration s d.first d.second :=
  ⟨hmany, d.fixed_part, d.moved_ti, d.first_mem, d.second_mem,
    d.first_ne, d.second_ne, d.first_fixed, d.second_fixed, d.central, d.order⟩

/-- Relative normality of K_z inside G_z and the earlier seed calculation
force every strict closure to escape the original maximal local subgroup. -/
theorem span_escapes_of_seedAnalysis (hlocal : SeedAnalysisAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (d : CentralizerData T D s)
    (hstrict : centralizerSeed T L (d.first * d.second) <
      componentSpan T L (d.first * d.second)) :
    ¬ componentSpan T L (d.first * d.second) ≤ D.maximalLocal := by
  intro hKM
  have ha := hlocal L D s d.first d.second (centralizer_configuration hmany d)
  have hn := ha.normal_in_kernel (componentSpan T L (d.first * d.second))
    (le_inf (componentSpan_le_centralizer _) hKM)
    (le_normalizer_conjugateSpanBy _ _) (le_conjugateSpanBy _ _)
  exact hstrict.not_ge (conjugateSpanBy_le le_rfl hn)

/-- The genuine centralizer closure conclusion from the existing independent
seed, invariant-sieve and local-normality sources. -/
theorem strictClosure_of_earlier_sources (hseed : ParabolicSeedAt T)
    (hsieve : InvariantWreathSieveAt T) (hlocal : SeedAnalysisAt T) :
    StrictClosureAt T := by
  intro hmany L D s d hstrict
  obtain ⟨r⟩ := hseed hmany L D s d
  have hXC : centralizerSeed T L (d.first * d.second) ⊔ (T : Subgroup G) ≤
      centralizer ({d.first * d.second} : Set G) :=
    sup_le ((map_subtype_le _).trans inf_le_right) d.sylow_le_centralizer
  obtain ⟨P, hP⟩ := r.localInput hXC
  rcases normalClosure_models_of_sieve hsieve hP
      (D.simpleQTKE.involution_centralizer_sqtk d.order) r.seed_wreath with
    he | ⟨I, hI, hqs, horbit, hm⟩
  · exact (hstrict.ne he.symm).elim
  · have hout : ¬ I ≤ D.maximalLocal := by
      intro hIM
      apply span_escapes_of_seedAnalysis hlocal hmany d hstrict
      rw [componentSpan, horbit]
      exact iSup_conjugates_le_of_le_normalizer I (T : Subgroup G) D.maximalLocal hIM
        ((le_normalizer_componentOrbit L (T : Subgroup G)).trans D.maximalLocal.le_normalizer)
    exact ⟨I, hI, hout, hqs, horbit.symm, hm⟩

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.NonBender
