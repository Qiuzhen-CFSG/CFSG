module

public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FFReduction.Complete
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalCentralization

/-!
# The FF source argument at the original Cartan consumers

The FF reduction now supplies its full original configuration, including both
Thompson equalities and movement of the original residual. The earlier Baumann
normalizer theorem is also proved. The final applications remove both inputs
from the actual centralization and relocation consumers; the
subsequent A₇ exclusion, module recognition and component sieve retain their
separate source owners.

Source: Aschbacher--Smith, 5.1.13, printed pp.637--638.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original component centralizes omega once the independent A₇
contradiction is available. The FF configuration is constructed here. -/
theorem localCartan_centralizes_of_baumann_and_a7
    (hbaum : RankOneBaumannNormalizerControl G) (ha7 : LocalCartanA7Exclusion G)
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) : X ≤ omegaCentralizer T :=
  localCartan_centralizes_of_ff_and_a7 (localCartan_ffReduction_source hbaum)
    ha7 h hH hgen c hY d

/-- The literal centralization contract, with the FF source premise discharged. -/
theorem localCartanCentralization_of_baumann_and_source_steps
    (hbaum : RankOneBaumannNormalizerControl G) (ha7 : LocalCartanA7Exclusion G)
    (hm : LocalCartanModuleRecognition G) :
    LocalCartanCentralization KnownSimple.IsKnownSimple G :=
  localCartanCentralization_of_source_steps (localCartan_ffReduction_source hbaum) ha7 hm

/-- The actual relocation contract uses the same component sieve and marks. -/
theorem sourceLocalCartanEscape_of_baumann_and_source_steps
    (hbaum : RankOneBaumannNormalizerControl G)
    (hsieve : LocalCartanSieve KnownSimple.IsKnownSimple G)
    (ha7 : LocalCartanA7Exclusion G) (hm : LocalCartanModuleRecognition G) :
    SourceLocalCartanEscape KnownSimple.IsKnownSimple G :=
  sourceLocalCartanEscape_of_local_source_steps hsieve
    (localCartan_ffReduction_source hbaum) ha7 hm

/-- The original component centralizes omega using the proved FF reduction
and the independently owned A₇ exclusion. -/
theorem localCartan_centralizes_of_a7
    (ha7 : LocalCartanA7Exclusion G)
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) : X ≤ omegaCentralizer T :=
  localCartan_centralizes_of_ff_and_a7 localCartan_ffReduction ha7 h hH hgen c hY d

/-- The original centralization contract after discharging the complete FF
construction, including its Baumann input. -/
theorem localCartanCentralization_of_a7_and_recognition
    (ha7 : LocalCartanA7Exclusion G) (hm : LocalCartanModuleRecognition G) :
    LocalCartanCentralization KnownSimple.IsKnownSimple G :=
  localCartanCentralization_of_source_steps localCartan_ffReduction ha7 hm

/-- The literal relocation consumer retains only its separately owned sieve,
A₇ exclusion and module-recognition inputs. -/
theorem sourceLocalCartanEscape_of_sieve_a7_and_recognition
    (hsieve : LocalCartanSieve KnownSimple.IsKnownSimple G)
    (ha7 : LocalCartanA7Exclusion G) (hm : LocalCartanModuleRecognition G) :
    SourceLocalCartanEscape KnownSimple.IsKnownSimple G :=
  sourceLocalCartanEscape_of_local_source_steps hsieve localCartan_ffReduction ha7 hm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
