module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Places
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.Reduction
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses

/-!
# The Tits seed extension obstruction

The certified Sylow factorizations refine the eighteen ambient double cosets
to seed double cosets. Multiplication on either side by seed elements preserves
the literal extension. The identity and both parabolic reflection families
lie in listed places; the remaining families have certified place or extension
witnesses. Excluding every listed place therefore gives the required index or
order obstruction by Lagrange's theorem.

Both finite certificate premises are discharged in `singleExtension_obstruction`.
No geometry certificate, seed order or seed-catalogue exhaustiveness is assumed.
Source: Parrott (1972), section 5, p.683; `ExtensionObstructions/source/README.md`.
-/

namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups
open ExtensionObstructions

/-- The exact obstruction required by seed-overgroup placement, reduced to two
independent finite certificates. -/
public theorem singleExtension_obstruction_of_finite_certificates
    (hf : SylowFactorizations)
    (hw : ∀ (i : Fin 122) (a b : Fin 32) (c : Fin 15),
      RepresentativeWitness i a b ⟨c.val + 3, by omega⟩)
    (i : Fin 122) (x : Atlas1600Group) (hx : ∀ j ∈ placeIds i, x ∉ place j) :
    ¬ 2 ∣ (singleExtension i x).index ∨
      25 ∣ Nat.card (singleExtension i x) ∨ 13 ∣ Nat.card (singleExtension i x) :=
  obstruction_of_certificates hf hw i x hx

/-- Adjoining an element outside every listed place gives an extension of odd
index or of order divisible by 25 or 13. Both finite certificate families are
supplied, so the literal seed and element require no extra hypotheses. -/
public theorem singleExtension_obstruction
    (i : Fin 122) (x : Atlas1600Group) (hx : ∀ j ∈ placeIds i, x ∉ place j) :
    ¬ 2 ∣ (singleExtension i x).index ∨
      25 ∣ Nat.card (singleExtension i x) ∨ 13 ∣ Nat.card (singleExtension i x) :=
  singleExtension_obstruction_of_finite_certificates sylowFactorizations
    representativeWitnesses i x hx

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups
