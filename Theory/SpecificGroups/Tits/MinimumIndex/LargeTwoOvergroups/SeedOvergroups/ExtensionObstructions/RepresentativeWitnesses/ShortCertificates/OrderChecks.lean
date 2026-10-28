module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.Contracts
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.OrderChecks.Row00
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.OrderChecks.Row01
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.OrderChecks.Row02
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.OrderChecks.Row03
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.OrderChecks.Row04
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.OrderChecks.Row05
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.OrderChecks.Row06
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.OrderChecks.Row07
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.OrderChecks.Row08
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.OrderChecks.Row09
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.OrderChecks.Row10
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.OrderChecks.Row11
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.OrderChecks.Row12
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.OrderChecks.Row13
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.OrderChecks.Row14

/-!
# The complete short-element order-thirteen catalogue

All 5,122 positive entries of the fifteen original catalogue masks have order
thirteen. Each row is certified in bounded kernel checks of the forward maps
on the three-point base, then transported to the literal Atlas group element.
The index remains `c.val + 3`, and all products retain the Lean left action.

The final application supplies the order premise of the existing representative
witness construction. Its independent seed membership and recovery equation
remain explicit; the outer short-witness assembly owns their discharge.

Source: Parrott (1972), section 5, p.683; the parent source READMEs and
`OrderChecks/source/README.md` for reproduction and measured checking costs.
-/

public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ShortCertificates

/-- Every positive entry in the published catalogue has actual order thirteen. -/
theorem orderCertificates : OrderCertificates := by
  intro n c hc
  apply OrderChecks.entryTest_sound n c _ hc
  fin_cases c
  · exact OrderChecks.row00 n
  · exact OrderChecks.row01 n
  · exact OrderChecks.row02 n
  · exact OrderChecks.row03 n
  · exact OrderChecks.row04 n
  · exact OrderChecks.row05 n
  · exact OrderChecks.row06 n
  · exact OrderChecks.row07 n
  · exact OrderChecks.row08 n
  · exact OrderChecks.row09 n
  · exact OrderChecks.row10 n
  · exact OrderChecks.row11 n
  · exact OrderChecks.row12 n
  · exact OrderChecks.row13 n
  · exact OrderChecks.row14 n

/-- Discharge the source order premise for an actual recovered seed multiple.
The independent recovery producer must still supply `h`. -/
theorem representativeWitness_of_recoveryCertificate
    (i : Fin 122) (a b : Fin 32) (c : Fin 15) (q n : Fin 2048)
    (h : RecoveryCertificate i a b c q n) :
    RepresentativeWitness i a b (shortIndex c) :=
  representativeWitness_of_certificate i a b c q n h (orderCertificates n c h.2.1)

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ShortCertificates
