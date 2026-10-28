module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.NonBender.Preparation
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.NonBender.Models
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.NonBender.Closure
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.NonBender.SolvableCover
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.Assembly

/-!
# Assembly of the non-Bender source obligations

An escaping component exists in the actual centralizer. If the seed equals
its normal closure, the normal-seed input makes that component Bender,
contrary to the branch hypothesis. The strict-closure input then identifies
an escaping component and its original orbit. The proved small-model sieve
and the model-family input supply the required parabolics. Positivity and
attainment give their exact numeric parameters on the same carriers.

All three earlier inputs remain explicit here. This is a conditional assembly,
not a completed proof of 10.3.3. The last theorem connects it to the existing
wreath-recognition consumer while retaining the independent Bender branch.

Source: Aschbacher--Smith 10.3.3, printed p.756, using 10.2.4, p.747.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.NonBender
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- Escape turns the normal-seed Bender conclusion into the strict inequality
needed by the independent closure theorem. -/
theorem seed_strict_of_normalSeedBender (hnormal : NormalSeedBenderAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D) (d : CentralizerData T D s)
    (hnone : ∀ I ∈ Chapter1.cComponentsIn (centralizer ({d.first * d.second} : Set G)),
      ¬ I ≤ D.maximalLocal → ¬ ClassificationModels.IsBenderModel (I ⧸ pCore 2 I)) :
    centralizerSeed T L (d.first * d.second) < componentSpan T L (d.first * d.second) := by
  apply lt_of_le_of_ne (le_conjugateSpanBy _ _)
  intro he
  obtain ⟨I, hI, hout⟩ := d.exists_escaping_component
  exact hnone I hI hout (hnormal hmany L D s d he I hI hout)

/-- Conditional assembly with the exact output and original Sylow embeddings
of `NonBenderGenerationAt`; the three source premises are not discharged. -/
theorem nonBenderGeneration_of_source_inputs
    (hnormal : NormalSeedBenderAt T) (hclosure : StrictClosureAt T)
    (hmodels : ModelFamiliesAt T) : NonBenderGenerationAt T := by
  intro hmany L D s d hnone
  have hstrict := seed_strict_of_normalSeedBender hnormal hmany D s d hnone
  obtain ⟨I, hI, hout, hqs, horbit, hm⟩ := hclosure hmany L D s d hstrict
  have hremaining := remainingModel_of_not_bender hqs hm (hnone I hI hout)
  obtain ⟨Δ, hΔ, hgen⟩ := hmodels hmany L D s d I hI hout hqs horbit hremaining
  exact ⟨I, hI, hout, Δ, family_parameters_one d le_sup_right Δ hΔ, hgen⟩

/-- Actual recognition consumer; the Bender source remains independent of
the three non-Bender obligations. -/
theorem wreathRecognition_of_nonBender_source_inputs (hB : BenderRecognitionAt T)
    (hnormal : NormalSeedBenderAt T) (hclosure : StrictClosureAt T)
    (hmodels : ModelFamiliesAt T) : WreathRecognitionAt T :=
  wreathRecognition_of_branches hB
    (nonBenderGeneration_of_source_inputs hnormal hclosure hmodels)

/-- Final non-Bender assembly reuses the existing producers for the earlier
parabolic seed, invariant wreath sieve and local seed analysis. Only the
normal-seed exclusion and model-family construction are new obligations. -/
theorem nonBenderGeneration_of_earlier_sources
    (hnormal : NormalSeedBenderAt T)
    (hseed : Overgroups.Closure.ParabolicSeedAt T)
    (hsieve : Overgroups.Closure.InvariantWreathSieveAt T)
    (hlocal : Geometry.CoreReduced.SeedAnalysisAt T)
    (hmodels : ModelFamiliesAt T) : NonBenderGenerationAt T :=
  nonBenderGeneration_of_source_inputs hnormal
    (strictClosure_of_earlier_sources hseed hsieve hlocal) hmodels

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.NonBender
