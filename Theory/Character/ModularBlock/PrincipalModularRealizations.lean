module

public import Theory.Character.ModularBlock.OrdinaryCyclotomicModels
public import Theory.Character.ModularBlock.PrincipalIntegralReduction

/-!
# Modular realizations of ordinary principal-block characters

Every ordinary character in the prescribed principal congruence block is
realized on odd-order elements by the genuine Brauer character of a module
in the principal block over the prescribed splitting residue field.

Choose the integral model over the localization at the prescribed cyclotomic
prime supplied by `OrdinaryCyclotomicModels`. Reduce its matrices to the
splitting residue field. The integral selector identity places the reduction
in the principal block, and preservation of the lifted eigenvalue multiset
identifies its Brauer values with the ordinary character on odd-order elements.
This is ordinary lattice reduction as in Serre, *Linear Representations of
Finite Groups*, Chapter 15.
-/

public section
noncomputable section

namespace ModularBlock.Cartan

open PrincipalBlockConstruction BrauerCoefficientExtension

variable {G : Type*} [Group G] [Finite G]

/-- Reduction at the prescribed prime realizes every ordinary block character
as a genuine principal-block Brauer character on odd-order elements. -/
theorem exists_modular_realization (d : PrincipalCongruenceBlockData G)
    (i : d.I) (hi : i ∈ d.block) :
    ∃ (m : ℕ) (ρ : Representation (splittingField d) G (Fin m → splittingField d)),
      InPrincipalBlock d ρ ∧ ∀ g : G, Odd (orderOf g) →
        d.chi i (ConjClasses.mk g) = BrauerCharacter.value d ρ g := by
  obtain ⟨m, σ, hχ⟩ := OrdinaryCyclotomicModels.exists_integral_model d i
  refine ⟨m, Representation.mapCoefficients (localizedReduction d) σ,
    inPrincipalBlock_mapCoefficients d σ i hi hχ, ?_⟩
  intro g hg
  rw [hχ]
  exact BrauerCharacter.character_eq_value_mapCoefficients d σ g hg

end ModularBlock.Cartan
