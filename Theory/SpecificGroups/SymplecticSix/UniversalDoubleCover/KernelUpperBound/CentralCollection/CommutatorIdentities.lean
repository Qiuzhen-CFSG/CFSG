module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.CentralCollection.Basic
public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.CentralCollection.CommutatorIdentities.Relators
public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.CentralCollection.CommutatorIdentities.Certificate.Output

/-!
# The three central commutator defects coincide

Act on the literal free central extension by conjugation and central
translations. Four short words stabilize the first generator. A kernel-checked
coset certificate puts the translations by c₄c₆ and c₅c₆ in that stabilizer.
A translation fixing any group element is trivial; since c₆ is an involution,
this gives c₄ = c₆ and c₅ = c₆ without any finiteness or multiplier hypothesis.

`CommutatorIdentities/Collection.lean` supplies both identities to the existing
collection consumer; its two power premises remain with the outer assembly.
Source: Wilson–Nickerson–Bray, ATLAS S62G1-P1.M. See the certificate's
`CommutatorIdentities/source/README.md` for conventions and reproduction.
-/

public section
namespace Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.CentralCollection
open Subgroup.CosetWordCertificate
open CommutatorIdentities

private theorem eq_of_translation_stabilizes (i : Fin 7)
    (h : translation (centralRelator i) * translation (centralRelator 6) ∈ stabilizer) :
    centralRelator i = centralRelator 6 := by
  change (centralRelator i : Central) * ((centralRelator 6 : Central) * a) = a at h
  have he : centralRelator i * centralRelator 6 = 1 := by
    apply Subtype.ext
    apply mul_right_cancel (b := a)
    simpa only [Subgroup.coe_mul, OneMemClass.coe_one, one_mul, mul_assoc] using h
  calc
    centralRelator i = (centralRelator i * centralRelator 6) * centralRelator 6 := by
      rw [mul_assoc, ← pow_two, centralRelator_six_sq, mul_one]
    _ = centralRelator 6 := by rw [he, one_mul]

/-- The fourth commutator defect equals the distinguished sixth defect. -/
theorem centralRelator_four_eq_six : centralRelator 4 = centralRelator 6 := by
  apply eq_of_translation_stabilizes 4
  obtain ⟨h, hh⟩ := CommutatorIdentities.Certificate.four_six certificate_valid
  have he : traceGenerator 2 * traceGenerator 4 = (h : Ambient) := by
    simpa only [Definitions.repr_zero, one_mul, mul_one, eval_cons, eval_nil, if_true] using hh
  change traceGenerator 2 * traceGenerator 4 ∈ stabilizer
  rw [he]
  exact h.property

/-- The cubic commutator defect equals the distinguished sixth defect. -/
theorem centralRelator_five_eq_six : centralRelator 5 = centralRelator 6 := by
  apply eq_of_translation_stabilizes 5
  obtain ⟨h, hh⟩ := CommutatorIdentities.Certificate.five_six certificate_valid
  have he : traceGenerator 3 * traceGenerator 4 = (h : Ambient) := by
    simpa only [Definitions.repr_zero, one_mul, mul_one, eval_cons, eval_nil, if_true] using hh
  change traceGenerator 3 * traceGenerator 4 ∈ stabilizer
  rw [he]
  exact h.property

end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.CentralCollection
