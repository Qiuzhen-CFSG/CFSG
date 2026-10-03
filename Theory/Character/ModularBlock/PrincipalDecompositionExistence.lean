module

public import Theory.Character.ModularBlock.PrincipalBrauerMultiplicities
public import Theory.Character.ModularBlock.PrincipalModularRealizations

/-!
# Assembly of principal decomposition data from modular realizations

For a prescribed principal Brauer family, integral character restrictions are
equivalent to decomposition data retaining exactly that family. More
substantively, it suffices to realize each ordinary block character on
odd-order elements as the genuine Brauer value of a finite-dimensional
principal-block module. The composition-factor theorem then supplies the
nonnegative integral coefficients.

This is the final assembly step for the definition in `Cartan.lean`, as used
for the decomposition and Cartan matrices in Fong, *Some Sylow subgroups of
order 32*, J. Algebra 6 (1967), p. 71. Existence of these modular realizations
follows from ordinary integral lattice reduction in
`PrincipalModularRealizations`. Consequently every prescribed principal Brauer
family admits decomposition data.
-/

public section
noncomputable section

namespace ModularBlock.Cartan

open PrincipalBlockConstruction BrauerCoefficientExtension

variable {G : Type*} [Group G] [Finite G]
variable {d : PrincipalCongruenceBlockData G} {n : ℕ}

/-- Assemble the rows, using zero outside the block where no row is specified. -/
theorem exists_decompositionData_of_restrictions (b : PrincipalBrauerFamily d n)
    (h : ∀ i ∈ d.block, ∃ c : Fin n → ℕ, ∀ g : G, Odd (orderOf g) →
      d.chi i (ConjClasses.mk g) =
        ∑ j, (c j : ℂ) * BrauerCharacter.value d (b.rep j) g) :
    ∃ a : PrincipalDecompositionData d n, a.family = b := by
  classical
  let c : d.I → Fin n → ℕ := fun i =>
    if hi : i ∈ d.block then (h i hi).choose else fun _ => 0
  refine ⟨{ family := b, decomposition := c, restriction := ?_ }, rfl⟩
  intro i hi g hg
  simpa only [c, dif_pos hi] using (h i hi).choose_spec g hg

/-- The rowwise integral restriction statement is exactly the existence requirement. -/
theorem exists_decompositionData_iff_restrictions (b : PrincipalBrauerFamily d n) :
    (∃ a : PrincipalDecompositionData d n, a.family = b) ↔
      ∀ i ∈ d.block, ∃ c : Fin n → ℕ, ∀ g : G, Odd (orderOf g) →
        d.chi i (ConjClasses.mk g) =
          ∑ j, (c j : ℂ) * BrauerCharacter.value d (b.rep j) g := by
  constructor
  · rintro ⟨a, ha⟩ i hi
    refine ⟨a.decomposition i, ?_⟩
    rw [← ha]
    exact a.restriction i hi
  · exact exists_decompositionData_of_restrictions b

/-- Actual modular realizations suffice; composition factors supply integral rows. -/
theorem exists_decompositionData_of_modular_realizations (b : PrincipalBrauerFamily d n)
    (h : ∀ i ∈ d.block, ∃ (m : ℕ)
      (ρ : Representation (splittingField d) G (Fin m → splittingField d)),
      InPrincipalBlock d ρ ∧ ∀ g : G, Odd (orderOf g) →
        d.chi i (ConjClasses.mk g) = BrauerCharacter.value d ρ g) :
    ∃ a : PrincipalDecompositionData d n, a.family = b := by
  apply exists_decompositionData_of_restrictions b
  intro i hi
  obtain ⟨m, ρ, hblock, hvalue⟩ := h i hi
  obtain ⟨c, hc⟩ := b.exists_multiplicities ρ hblock
  exact ⟨c, fun g hg => (hvalue g hg).trans (hc g)⟩

/-- Every prescribed principal Brauer family admits genuine decomposition data. -/
theorem exists_decompositionData (b : PrincipalBrauerFamily d n) :
    ∃ a : PrincipalDecompositionData d n, a.family = b :=
  exists_decompositionData_of_modular_realizations b (exists_modular_realization d)

end ModularBlock.Cartan
