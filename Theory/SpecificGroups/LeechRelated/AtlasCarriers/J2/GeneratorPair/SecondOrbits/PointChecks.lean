module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.SecondOrbits.NormalForms
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.SecondOrbits.OrbitRepresentatives

/-!
# Soundness of pointwise rejection witnesses

A witness either exhibits a moved point for one of the first three word
identities, or identifies the permutation with a supplied partner. This avoids
checking full permutations for most rejected cases. The code is total: its
point and partner fields are reduced into range, so no unchecked bounds enter
the proof. The finite exhaustive certificate remains a separate obligation.

Source: the ATLAS `J2G1-p100B0` word tests used for GLS3, Table 5.3g.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.GeneratorPair.SecondOrbitCertificate

/-- Point field of a rejection witness. -/
def witnessPoint (code : Nat) : Fin 100 :=
  ⟨(code / 4) % 100, Nat.mod_lt _ (by decide)⟩

/-- Conjugator field of an acceptance witness. -/
def witnessConjugator (code : Nat) : Fin 240 :=
  ⟨(code / 8) % 240, Nat.mod_lt _ (by decide)⟩

/-- Orbit field of an acceptance witness. -/
def witnessInverse (code : Nat) : Bool := (code / 4) % 2 == 1

/-- Tags 0, 1, 2 reject by a moved point; tag 3 supplies an exact partner. -/
def WitnessValid (y : Equiv.Perm (Fin 100)) (code : Nat) : Prop :=
  match code % 4 with
  | 0 => (y ^ 3) (witnessPoint code) ≠ witnessPoint code
  | 1 => ((tableA * y) ^ 7) (witnessPoint code) ≠ witnessPoint code
  | 2 => ((tableA * y * tableA * y⁻¹) ^ 12) (witnessPoint code) ≠ witnessPoint code
  | _ => y = partnerTable (witnessConjugator code) (witnessInverse code)

instance (y : Equiv.Perm (Fin 100)) (code : Nat) : Decidable (WitnessValid y code) := by
  unfold WitnessValid
  split <;> infer_instance

/-- A valid witness classifies any permutation satisfying the word tests. -/
theorem partner_of_witnessValid {y : Equiv.Perm (Fin 100)} {code : Nat}
    (h : AmbientProfile y) (valid : WitnessValid y code) :
    ∃ j : Fin 240, ∃ inverse : Bool, y = partnerTable j inverse := by
  unfold WitnessValid at valid
  split at valid
  · exact (valid (by rw [h.1]; rfl)).elim
  · exact (valid (by rw [h.2.1]; rfl)).elim
  · exact (valid (by rw [h.2.2.1]; rfl)).elim
  · exact ⟨witnessConjugator code, witnessInverse code, valid⟩

/-- An exhaustive family of valid witnesses supplies the finite orbit check. -/
theorem classify_of_witnesses (code : Index → Nat)
    (valid : ∀ i, WitnessValid (normalForm i) (code i))
    (i : Index) (h : AmbientProfile (normalForm i)) :
    ∃ j : Fin 240, ∃ inverse : Bool, normalForm i = partnerTable j inverse :=
  partner_of_witnessValid h (valid i)

end Sporadic.LeechRelated.J2.GeneratorPair.SecondOrbitCertificate
