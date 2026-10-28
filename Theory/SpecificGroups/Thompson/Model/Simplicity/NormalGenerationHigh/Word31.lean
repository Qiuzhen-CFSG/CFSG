module

public import Theory.SpecificGroups.Thompson.Model.Simplicity.PrimeRepresentatives
public import Theory.SpecificGroups.Thompson.Model.Simplicity.NormalGenerationHigh.Word31Certificate.Checked
public import Theory.SpecificGroups.Thompson.Model.Simplicity.NormalGenerationHigh.Word31Certificate.Shape

import Mathlib.Tactic.IntervalCases

/-!
# The checked collapse of the Thompson 31A–B word quotient

The generated coset-word trace proves `a = 1` from the relations `a² = 1`,
`b³ = 1`, `(ab)¹⁹ = 1`, and the proposed 31A–B word equal to one. Here the
literal relators are matched to images of the actual matrix generators under
an arbitrary homomorphism. No group presentation identification is needed.

Source: https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Th/ ; the producer and
its reproducible kernel checks are described in `source/README.md`.
-/

namespace Thompson.Simplicity
open Subgroup.CosetWordCertificate Word31Certificate

private theorem literal_relations {G : Type*} [Group G] (f : Model →* G)
    (hab19 : (generatorA * generatorB)^19 = 1)
    (hw : f (word "abababababababbabbabababababbababababababababb") = 1) :
    ∀ r, eval ![f generatorA, f generatorB] (relatorWords r) = 1 := by
  intro r
  unfold relatorWords
  split
  · rename_i hr
    interval_cases r
    · simpa [relatorFin, eval_cons, pow_two] using congrArg f generatorA_sq
    · simpa [relatorFin, eval_cons, pow_succ, mul_assoc] using congrArg f generatorB_cube
    · simpa [relatorFin, eval_cons, pow_succ, mul_assoc] using congrArg f hab19
    · simpa [relatorFin, eval_cons, word] using hw
  · exact eval_nil _

/-- Killing the proposed 31A–B word kills the involution generator, assuming
only the standard product relation in addition to the certified generator orders. -/
public theorem generatorA_eq_one_of_word31 {G : Type*} [Group G] (f : Model →* G)
    (hab19 : (generatorA * generatorB)^19 = 1)
    (hw : f (word "abababababababbabbabababababbababababababababb") = 1) :
    f generatorA = 1 := by
  let g : Fin 2 → G := ![f generatorA, f generatorB]
  have hv : Valid context (⊥ : Subgroup G) g (definitions.repr g) := by
    apply definitions.valid relatorWords (fun _ => false)
    · intro a ha
      simp at ha
    · exact literal_relations f hab19 hw
  have hh := all_hold hv 16035 (by decide)
  rw [output_shape] at hh
  obtain ⟨h, hh⟩ := hh
  have he : (h : G) = 1 := h.property
  simpa [Holds, definitions.repr_zero, he, g] using hh

end Thompson.Simplicity
