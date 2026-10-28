module

public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.Conjugacy.WordValues.NumericalCertificate.Batches

/-!
# Assembly of the recovered-word numerical certificate

The numerical work consists of four independent batches of equations for one
family of candidate matrices and the identification of its two outputs.
This assembly lemma constructs exactly the witness required by the symbolic
certificate soundness theorem. It assumes no presentation relation or group
identification. Source: Breuer–Magaard–Wilson (2019), Table 1 and §3.4;
see `../source/README.md`.
-/

public section
namespace BabyMonster.OrderLowerBound

/-- Final assembly interface for the independently checked numerical batches. -/
theorem recovered_program_certificate_of_batches
    (v : Fin 242 → AtlasMatrix)
    (h0 : RecoveredWordProgram.Numerical.Batch0 v)
    (h1 : RecoveredWordProgram.Numerical.Batch1 v)
    (h2 : RecoveredWordProgram.Numerical.Batch2 v)
    (h3 : RecoveredWordProgram.Numerical.Batch3 v)
    (hA : v 232 = conjugacyA) (hB : v 241 = conjugacyB) :
    ∃ w : Fin 242 → AtlasMatrix,
      RecoveredWordProgram.Certificate w ∧ w 232 = conjugacyA ∧ w 241 = conjugacyB :=
  ⟨v, RecoveredWordProgram.Numerical.certificate_of_batches h0 h1 h2 h3, hA, hB⟩

end BabyMonster.OrderLowerBound
