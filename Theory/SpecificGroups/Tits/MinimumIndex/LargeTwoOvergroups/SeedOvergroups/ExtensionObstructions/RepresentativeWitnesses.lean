module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.Contracts
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.Cases
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.Pilot
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.PlacementCertificates
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ProductCertificates

/-!
# Assembly of the remaining finite seed-extension witnesses

The explicit finite selector separates short order-thirteen witnesses, literal
place membership, and longer order-thirteen products. Its three cases are
exhaustive by construction. The three certified families discharge every seed
membership, recovery, place containment and order premise, giving the
unconditional `representativeWitnesses` for all fifteen remaining double-coset
families. No Sylow factorization or seed-catalogue exhaustiveness is assumed.

Source: Parrott (1972), section 5, p.683, and the literal contracts in
`ExtensionObstructions.Contracts`. See `RepresentativeWitnesses/source/README.md`
for the reproducible witness data and measured proof costs.
-/

public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions
open RepresentativeCertificates

/-- Assemble three proofs about a finite computational partition. None of the
three premises is discharged by the selector definition itself. -/
theorem representativeWitnesses_of_cases
    (hs : ∀ (i : Fin 122) (a b : Fin 32) (c : Fin 15),
      witnessCase i a b c = .short → RepresentativeWitness i a b ⟨c.val + 3, by omega⟩)
    (hp : ∀ (i : Fin 122) (a b : Fin 32) (c : Fin 15),
      witnessCase i a b c = .place → RepresentativeWitness i a b ⟨c.val + 3, by omega⟩)
    (hm : ∀ (i : Fin 122) (a b : Fin 32) (c : Fin 15),
      witnessCase i a b c = .product → RepresentativeWitness i a b ⟨c.val + 3, by omega⟩)
    (i : Fin 122) (a b : Fin 32) (c : Fin 15) :
    RepresentativeWitness i a b ⟨c.val + 3, by omega⟩ := by
  cases h : witnessCase i a b c with
  | short => exact hs i a b c h
  | place => exact hp i a b c h
  | product => exact hm i a b c h

/-- Every representative in the fifteen remaining double-coset families has
an actual listed-place or single-extension witness, with no extra premises. -/
theorem representativeWitnesses :
    ∀ (i : Fin 122) (a b : Fin 32) (c : Fin 15),
      RepresentativeWitness i a b ⟨c.val + 3, by omega⟩ :=
  representativeWitnesses_of_cases shortWitnesses placementWitnesses productWitnesses

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions
