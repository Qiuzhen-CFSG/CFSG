module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.GeneratorLiftCertificate.Words
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.GeneratorLiftCertificate.WordTable
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.GeneratorLiftCertificate.CandidateTable

/-!
# Interpreting the candidate table in the actual Fi23 carrier

The numerical certificates evaluate the literal twelve-letter word and its
seventh power. The only remaining inputs here identify the packed source maps
with the two original ATLAS generators. Their producer is the separately owned
`Fi23InFi24Prime.Comparison.SourceActions` development.

This identifies the exact centralizer candidate used in GLS3 Table 5.3u; no
order, simplicity, fixed-point coverage, or centralizer structure is assumed.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.GeneratorLiftCertificate
open Fi24Prime.Fi23Lift.Certificate (sourceA sourceB)

theorem wordMap_eq_inclusion_word
    (ha : ∀ x, generatorA x = sourceA x)
    (hb : ∀ x, generatorB x = sourceB x) (x : Fin 31671) :
    wordMap x = inclusion word x := by
  rw [wordMap_eq_evalWord]
  simp only [evalWord, ← ha, ← hb, word, map_mul, pow_succ,
    pow_zero, Equiv.Perm.mul_apply]
  rfl

theorem candidateMap_eq_inclusion_candidate
    (ha : ∀ x, generatorA x = sourceA x)
    (hb : ∀ x, generatorB x = sourceB x) (x : Fin 31671) :
    candidateMap x = inclusion candidate x := by
  have hw : wordMap = (inclusion word : Fin 31671 → Fin 31671) :=
    funext (wordMap_eq_inclusion_word ha hb)
  rw [(candidate_checks x).1, hw]
  simp only [candidate, map_pow, Equiv.Perm.coe_pow]

end Sporadic.Fischer.Fi23.CentralizerSection.GeneratorLiftCertificate
