module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.NonBender.Assembly
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.NonBender.SeedNormality
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Invariant.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Moved
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Held
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Generation

/-!+# Source assembly through generation of the actual orbit join

The non-Bender model rows give E-generation at one for the literal join
of the escaping component with the original full Sylow subgroup. The
binary-linear and Held rows use the completed invariant-component proofs;
the odd-prime row retains only the independent moved-component obligation.
All quotient transports use the actual two-cores and subgroup inclusions.

The earlier overgroup bound then puts this join in M, contradicting escape.
Thus the non-Bender hypothesis is impossible, and in particular implies
the exact specified-family contract. This route does not require a separate
classification of all minimal parabolics. The normal-seed exclusion and
the earlier parabolic seed and moved-prime inputs remain explicit. The
last two theorems also instantiate the completed invariant wreath sieve;
the needed local normality is derived from the parabolic seed itself.

Source: Aschbacher--Smith 10.3.3, printed p.756, using 10.2.4, p.747,
and the E-generation results of Appendix E. The corrected Held row is retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.NonBender
open Chapter3.Section02 Overgroups.ModelGeneration
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreeSurvivor T D}

/-- Model generation on the literal centralizer component--Sylow join.
Only the moved odd-prime row is still an explicit model premise. -/
theorem orbit_join_isEGenerated_of_remaining
    (hmoved : MovedOddPrimeGeneration.{u}) (d : CentralizerData T D s)
    {I : Subgroup G}
    (hI : I ∈ Chapter1.cComponentsIn (centralizer ({d.first * d.second} : Set G)))
    (hq : IsQuasisimple (I ⧸ pCore 2 I)) (hm : RemainingModel T I) :
    ChapterE.IsEGenerated 1
      (componentOrbit I (T : Subgroup G) ⊔ (T : Subgroup G) : Subgroup G) := by
  have hY := orbit_join_sqtk d hI
  rw [componentOrbit_sup] at hY ⊢
  let Y := I ⊔ (T : Subgroup G)
  have hYC : Y ≤ centralizer ({d.first * d.second} : Set G) :=
    sup_le hI.1 d.sylow_le_centralizer
  let K := I.subgroupOf Y
  let S := T.subtype (show (T : Subgroup G) ≤ Y from le_sup_right)
  have hK : K.IsCComponent := hI.2.subgroupOf_of_le le_sup_left hYC
  let a := subgroupOfEquivOfLe (show I ≤ Y from le_sup_left)
  let b := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hqK : IsQuasisimple (K ⧸ pCore 2 K) := by
    let := hq
    exact IsQuasisimple.of_mulEquiv b.symm
  have hKS : K ⊔ (S : Subgroup Y) = ⊤ := by
    change I.subgroupOf Y ⊔ (T : Subgroup G).subgroupOf Y = ⊤
    rw [← subgroupOf_sup (show I ≤ Y from le_sup_left)
      (show (T : Subgroup G) ≤ Y from le_sup_right)]
    exact subgroupOf_self Y
  rcases hm with ⟨p, hp, ho, hlarge, hm⟩ | ⟨hn, k, hk, hm, _⟩ | ⟨hn, ⟨e⟩⟩
  · exact oddPrimeOrbitGeneration_of_moved hmoved Y hY S K hK hqK hKS
      p hp ho hlarge (hm.of_mulEquiv b)
  · let hnK : K.Normal :=
      normal_subgroupOf_of_le_normalizer (sup_le I.le_normalizer hn)
    exact isEGenerated_of_normal_binary_component hY S K hK hKS hk (hm.of_mulEquiv b)
  · have hnK : K.Normal :=
      normal_subgroupOf_of_le_normalizer (sup_le I.le_normalizer hn)
    exact invariantHeldGeneration Y hY S K hK hnK hqK hKS ⟨b.trans e⟩

/-- Under the earlier source inputs the no-Bender hypothesis is impossible:
the generated join lies in M and still contains the escaping component. -/
theorem false_of_no_escaping_bender
    (hnormal : NormalSeedBenderAt T) (hclosure : StrictClosureAt T)
    (hmoved : MovedOddPrimeGeneration.{u})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D) (d : CentralizerData T D s)
    (hnone : ∀ I ∈ Chapter1.cComponentsIn (centralizer ({d.first * d.second} : Set G)),
      ¬ I ≤ D.maximalLocal → ¬ ClassificationModels.IsBenderModel (I ⧸ pCore 2 I)) :
    False := by
  have hstrict := seed_strict_of_normalSeedBender hnormal hmany D s d hnone
  obtain ⟨I, hI, hout, hqs, _, hm⟩ := hclosure hmany L D s d hstrict
  have hremaining := remainingModel_of_not_bender hqs hm (hnone I hI hout)
  have hgen := orbit_join_isEGenerated_of_remaining hmoved d hI hqs hremaining
  have hYM := Overgroups.le_maximal_of_eGenerated_one s d le_sup_right hgen
  exact hout ((le_componentOrbit I (T : Subgroup G)).trans (le_sup_left.trans hYM))

/-- Exact original non-Bender contract, conditional on independent earlier
source inputs. No separate model-family premise is needed. -/
theorem nonBenderGeneration_of_moved
    (hnormal : NormalSeedBenderAt T)
    (hseed : Overgroups.Closure.ParabolicSeedAt T)
    (hsieve : Overgroups.Closure.InvariantWreathSieveAt T)
    (hlocal : Geometry.CoreReduced.SeedAnalysisAt T)
    (hmoved : MovedOddPrimeGeneration.{u}) : NonBenderGenerationAt T := by
  intro hmany L D s d hnone
  exact (false_of_no_escaping_bender hnormal
    (strictClosure_of_earlier_sources hseed hsieve hlocal) hmoved hmany D s d hnone).elim

/-- The actual recognition consumer retains its independent Bender branch
and discharges the non-Bender branch by the preceding contradiction. -/
theorem wreathRecognition_of_moved (hB : BenderRecognitionAt T)
    (hnormal : NormalSeedBenderAt T)
    (hseed : Overgroups.Closure.ParabolicSeedAt T)
    (hsieve : Overgroups.Closure.InvariantWreathSieveAt T)
    (hlocal : Geometry.CoreReduced.SeedAnalysisAt T)
    (hmoved : MovedOddPrimeGeneration.{u}) : WreathRecognitionAt T :=
  wreathRecognition_of_branches hB
    (nonBenderGeneration_of_moved hnormal hseed hsieve hlocal hmoved)

/-- Exact non-Bender contract from the three outstanding source branches
and the shared parabolic seed. The normality needed for escape is derived
from that seed, so no full geometry or SeedAnalysis input remains. -/
theorem nonBenderGeneration_of_parabolicSeed
    (hnormal : NormalSeedBenderAt T)
    (hseed : Overgroups.Closure.ParabolicSeedAt T)
    (hsieve : Overgroups.Closure.InvariantWreathSieveAt T)
    (hmoved : MovedOddPrimeGeneration.{u}) : NonBenderGenerationAt T := by
  intro hmany L D s d hnone
  exact (false_of_no_escaping_bender hnormal
    (strictClosure_of_seed_and_sieve hseed hsieve) hmoved hmany D s d hnone).elim

/-- Actual recognition consumer for the route independent of geometry. -/
theorem wreathRecognition_of_parabolicSeed (hB : BenderRecognitionAt T)
    (hnormal : NormalSeedBenderAt T)
    (hseed : Overgroups.Closure.ParabolicSeedAt T)
    (hsieve : Overgroups.Closure.InvariantWreathSieveAt T)
    (hmoved : MovedOddPrimeGeneration.{u}) : WreathRecognitionAt T :=
  wreathRecognition_of_branches hB
    (nonBenderGeneration_of_parabolicSeed hnormal hseed hsieve hmoved)

/-- Final conditional source assembly, with the invariant sieve proved
and no geometry or separate model-family input. The three premises are
the genuinely outstanding normal-seed, parabolic-seed and moved-prime proofs. -/
theorem nonBenderGeneration_of_remaining
    (hnormal : NormalSeedBenderAt T)
    (hseed : Overgroups.Closure.ParabolicSeedAt T)
    (hmoved : MovedOddPrimeGeneration.{u}) : NonBenderGenerationAt T :=
  nonBenderGeneration_of_parabolicSeed hnormal hseed
    (Overgroups.Closure.invariantWreathSieve T) hmoved

/-- Actual wreath-recognition consumer after discharging the shared sieve. -/
theorem wreathRecognition_of_remaining (hB : BenderRecognitionAt T)
    (hnormal : NormalSeedBenderAt T)
    (hseed : Overgroups.Closure.ParabolicSeedAt T)
    (hmoved : MovedOddPrimeGeneration.{u}) : WreathRecognitionAt T :=
  wreathRecognition_of_branches hB (nonBenderGeneration_of_remaining hnormal hseed hmoved)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.NonBender
