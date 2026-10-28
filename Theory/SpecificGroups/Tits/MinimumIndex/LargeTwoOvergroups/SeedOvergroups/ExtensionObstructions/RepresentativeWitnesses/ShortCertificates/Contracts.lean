module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.Catalogue
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.NormalForms

/-!
# Independent checks needed for the short representative branch

Recovery certificates construct a literal seed member and its numeric
multiplication equation. Order certificates concern only the 5,122 shared
short elements listed in the catalogue. The actual representative witness
below follows from these separate facts and the certified normal-form
multiplication. Neither interface assumes the desired extension witness.

Source: Parrott (1972), section 5, p.683; the parent `source/README.md`.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ShortCertificates

/-- The actual seed member, catalogue entry and exact left-product equation. -/
def RecoveryCertificate (i : Fin 122) (a b : Fin 32) (c : Fin 15)
    (q n : Fin 2048) : Prop :=
  atlas1600SylowTwoNormalForm q ∈ seed i ∧ inCatalogue n c = true ∧
    normalMul q (transversalPattern (seedTransversalPattern i) a) =
      normalMul (transversalPattern (seedTransversalPattern i) b) n

/-- Recovery is independent of the orders of the catalogue elements. -/
def RecoveryCertificates : Prop :=
  ∀ (i : Fin 122) (a b : Fin 32) (c : Fin 15), witnessCase i a b c = .short →
    ∃ q n : Fin 2048, RecoveryCertificate i a b c q n

/-- Only the 5,122 positive catalogue entries need an order proof. -/
def OrderCertificates : Prop :=
  ∀ (n : Fin 2048) (c : Fin 15), inCatalogue n c = true →
    orderOf (shortElement n (shortIndex c)) = 13

/-- A certificate supplies an actual order-thirteen element in this extension. -/
theorem representativeWitness_of_certificate
    (i : Fin 122) (a b : Fin 32) (c : Fin 15) (q n : Fin 2048)
    (h : RecoveryCertificate i a b c q n)
    (ho : orderOf (shortElement n (shortIndex c)) = 13) :
    RepresentativeWitness i a b (shortIndex c) :=
  representativeWitness_of_shortRecovery i a b (shortIndex c) n
    ⟨atlas1600SylowTwoNormalForm q, h.1⟩ (recovery_of_normalMul i a b q n h.2.2) ho

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ShortCertificates
