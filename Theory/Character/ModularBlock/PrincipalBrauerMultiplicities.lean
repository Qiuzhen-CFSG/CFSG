module

public import Theory.Character.ModularBlock.PrincipalSubquotients
public import Theory.Character.ModularBlock.BrauerCharacterAdditivity
public import Theory.Representation.SubrepresentationLattice

/-!
# Nonnegative integral multiplicities of principal-block modules

Every finite-dimensional module on which the actual principal selector acts
as the identity has a Brauer value which is a nonnegative integral combination
of the values of a prescribed complete principal Brauer family.

Choose a simple submodule and induct on the dimension of the quotient. Both
remain in the block. Additivity of lifted eigenvalues adds the multiplicities;
coordinate completeness identifies the simple submodule with a family member.
This is the composition-factor argument for modular characters, implemented
without choosing a composition series or assuming semisimplicity.

The ordinary lattice-reduction step is separate: this theorem starts with an
actual representation over the prescribed splitting residue field.
-/

public section
noncomputable section
namespace ModularBlock.Cartan.PrincipalBrauerFamily
open PrincipalBlockConstruction BrauerCoefficientExtension
variable {G : Type*} [Group G] [Finite G]
variable {d : PrincipalCongruenceBlockData G} {n : ℕ}
variable (b : PrincipalBrauerFamily d n)

/-- Multiplicities of actual simple block modules in any finite-dimensional block module. -/
theorem exists_multiplicities
    {V : Type*} [AddCommGroup V] [Module (splittingField d) V]
    [FiniteDimensional (splittingField d) V]
    (ρ : Representation (splittingField d) G V) (hblock : InPrincipalBlock d ρ) :
    ∃ c : Fin n → ℕ, ∀ g : G,
      BrauerCharacter.value d ρ g =
        ∑ j, (c j : ℂ) * BrauerCharacter.value d (b.rep j) g := by
  classical
  generalize hdim : Module.finrank (splittingField d) V = m
  induction m using Nat.strong_induction_on generalizing V with
  | h m ih =>
    cases subsingleton_or_nontrivial V with
    | inl hV =>
      let := hV
      exact ⟨fun _ => 0, fun g => by simp [BrauerCharacter.value_eq_zero_of_subsingleton]⟩
    | inr hV =>
      let := hV
      obtain ⟨S, hS⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional ρ
      obtain ⟨cS, hcS⟩ := b.exists_multiplicities_of_irreducible S.toRepresentation hS
        (inPrincipalBlock_subrepresentation S hblock)
      let Q := V ⧸ S.toSubmodule
      let τ := ρ.quotient S.toSubmodule S.apply_mem_toSubmodule
      have hSpos : 0 < Module.finrank (splittingField d) S.toSubmodule := by
        let := hS
        let := Subrepresentation.irreducible_module_nontrivial S.toRepresentation
        exact Module.finrank_pos
      have hQlt : Module.finrank (splittingField d) Q < m := by
        have hsum := S.toSubmodule.finrank_quotient_add_finrank
        change Module.finrank (splittingField d) Q +
          Module.finrank (splittingField d) S.toSubmodule =
          Module.finrank (splittingField d) V at hsum
        omega
      obtain ⟨cQ, hcQ⟩ := ih _ hQlt τ (inPrincipalBlock_quotient S hblock) rfl
      refine ⟨fun j => cS j + cQ j, ?_⟩
      intro g
      rw [BrauerCharacter.value_subquotient d ρ S g, hcS g, hcQ g]
      simp only [Nat.cast_add, add_mul, Finset.sum_add_distrib]

end ModularBlock.Cartan.PrincipalBrauerFamily
