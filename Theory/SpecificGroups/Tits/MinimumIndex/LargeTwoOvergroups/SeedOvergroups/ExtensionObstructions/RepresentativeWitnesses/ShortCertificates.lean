module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.Cases
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.Certificates
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.Contracts
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.OrderChecks
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.RecoveryChecks
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.Samples

/-!
# Assembly of short representative certificates

Certified arithmetic reduces recovery to normal-form index equations. The
shared catalogue separates the order calculation from the literal seed
membership and recovery calculation. Both finite certificate families are
proved, so `shortWitnesses` supplies an actual representative witness for
every original short case, with no extra membership, recovery or order premise.

Source: Parrott (1972), section 5, p.683; `ShortCertificates/source/README.md`.
-/

public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates

/-- Final assembly of the two independently checkable finite families. -/
theorem shortWitnesses_of_shortCertificates
    (hr : ShortCertificates.RecoveryCertificates)
    (ho : ShortCertificates.OrderCertificates) :
    ∀ (i : Fin 122) (a b : Fin 32) (c : Fin 15), witnessCase i a b c = .short →
      RepresentativeWitness i a b ⟨c.val + 3, by omega⟩ := by
  intro i a b c hc
  obtain ⟨q, n, h⟩ := hr i a b c hc
  exact ShortCertificates.representativeWitness_of_certificate i a b c q n h
    (ho n c h.2.1)

/-- Every original short case has an actual representative witness, with all
seed membership, recovery and order-thirteen premises discharged. -/
theorem shortWitnesses :
    ∀ (i : Fin 122) (a b : Fin 32) (c : Fin 15), witnessCase i a b c = .short →
      RepresentativeWitness i a b ⟨c.val + 3, by omega⟩ :=
  shortWitnesses_of_shortCertificates ShortCertificates.recoveryCertificates
    ShortCertificates.orderCertificates

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates
