module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.FixedPointSetup
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Generators
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Exhaustion.Evaluation
public import Theory.GroupAction.SchreierCentralizerCertificate

/-!
# Assembly of Fi23 centralizer exhaustion

For the shared 31671 representative words, the two families of forward
Schreier edges must belong to the eight-generator witness group. If the eight
witnesses commute with the candidate and only the base representative does
so, every centralizing element belongs to the witness group by word induction.
This proves an upper containment without assuming that the concrete ATLAS
action is a conjugation action or that a centralizer element fixes letter 15181.

This module retains the unfinished finite certificates explicitly. The final
unconditional `centralizer_le_witnessGroup` still requires their discharge.
Source: GLS3 Table 5.3u, its conjugation description near line 754, and the
Fischer paragraph near line 1042 in `refs/KGroup/GLS3/Chapter5(sec3-).tex`.
-/

public section
namespace Sporadic.Fischer.Fi23.CentralizerSection
open ImageContainmentCertificate ImageContainmentCertificate.Exhaustion

/-- Extend eight commutation checks to their actual permutation closure. -/
theorem witnessGroup_le_candidate_centralizer
    (hcomm : ∀ j, witnessGenerator j * inclusion candidate =
      inclusion candidate * witnessGenerator j) :
    witnessGroup ≤ Subgroup.centralizer {inclusion candidate} := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm j)

/-- Actual centralizer application of forward Schreier edges and a separated
identity representative. All remaining premises are finite concrete checks. -/
theorem centralizer_le_witnessGroup_of_edges_and_separation
    (hedge : ∀ (b : Bool) (x : Fin 31671), inclusion (edge b x) ∈ witnessGroup)
    (hcomm : ∀ j, witnessGenerator j * inclusion candidate =
      inclusion candidate * witnessGenerator j)
    (hsep : ∀ x, representative x * candidate = candidate * representative x → x = base) :
    ∀ g : numerator, inclusion g.val ∈ witnessGroup := by
  intro g
  apply Theory.GroupAction.SchreierActionCertificate.mem_of_centralizing_of_schreier
    (MonoidHom.id _) {generatorA, generatorB} witnessGroup
    (fun x => inclusion (representative x)) base (inclusion candidate)
  · rw [representative_base, map_one]
  · intro s hs x
    rcases Set.mem_insert_iff.mp hs with rfl | hs
    · simpa only [edge, map_mul, map_inv, inclusion_letter_false, MonoidHom.id_apply]
        using hedge false x
    · have hs' : s = generatorB := Set.mem_singleton_iff.mp hs
      subst s
      simpa only [edge, map_mul, map_inv, inclusion_letter_true, MonoidHom.id_apply]
        using hedge true x
  · exact witnessGroup_le_candidate_centralizer hcomm
  · intro x hx
    have he : representative x * candidate = candidate * representative x := by
      apply inclusion_injective
      simpa only [map_mul] using Subgroup.mem_centralizer_singleton_iff.mp hx
    rw [hsep x he, representative_base, map_one]
  · exact g.val.property
  · apply Subgroup.mem_centralizer_singleton_iff.mpr
    simpa only [map_mul] using
      congrArg inclusion (Subgroup.mem_centralizer_singleton_iff.mp g.property)

open Fi24Prime.Fi23Lift.Certificate

/-- The numerical separation certificate, exact source-map agreements, and
the two independent witness certificates discharge the concrete coverage. -/
theorem centralizer_le_witnessGroup_of_packed_certificates
    (hA : ∀ x, generatorA x = sourceA x) (hB : ∀ x, generatorB x = sourceB x)
    (hcheck : checkPow separationCheck 0 15 = true)
    (hedge : ∀ (b : Bool) (x : Fin 31671), inclusion (edge b x) ∈ witnessGroup)
    (hcomm : ∀ j, witnessGenerator j * inclusion candidate =
      inclusion candidate * witnessGenerator j) :
    ∀ g : numerator, inclusion g.val ∈ witnessGroup :=
  centralizer_le_witnessGroup_of_edges_and_separation hedge hcomm
    (representative_separated_of_check hA hB hcheck)

end Sporadic.Fischer.Fi23.CentralizerSection
