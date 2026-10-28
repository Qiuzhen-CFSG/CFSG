module

public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.Quotient

/-!
# Irreducible descent through a p-group kernel

A surjective group map with p-group kernel carries every irreducible
characteristic-p representation of its source to a representation of its
target on the same vector space. The normal-p-subgroup fixed-vector theorem
kills the kernel; quotient descent preserves irreducibility and the exact
action of every lifted element.

This is the modular fixed-vector argument used in Aschbacher--Smith,
13.8.33, when recognizing a simple quotient under the actual barred actor.
-/

public section
namespace Representation

/-- Descend a simple modular representation without changing its vector space. -/
theorem exists_irreducible_descent_of_pGroup_kernel
    {F B Q X : Type*} [Field F] [Group B] [Finite B] [Group Q]
    {p : ℕ} [Fact p.Prime] [CharP F p]
    [AddCommGroup X] [Module F X] [FiniteDimensional F X]
    (σ : Representation F B X) [IsIrreducible σ]
    (π : B →* Q) (hπ : Function.Surjective π) (hker : IsPGroup p π.ker) :
    ∃ τ : Representation F Q X,
      (∀ g, τ (π g) = σ g) ∧ IsIrreducible τ := by
  have hk : π.ker ≤ σ.ker := normal_p_subgroup_le_ker σ π.ker hker
  let e := QuotientGroup.quotientKerEquivOfSurjective π hπ
  let τ : Representation F Q X := (quotientOfLEKer σ π.ker hk).comp e.symm.toMonoidHom
  have hτ (g : B) : τ (π g) = σ g := by
    change quotientOfLEKer σ π.ker hk (e.symm (e (QuotientGroup.mk' π.ker g))) = σ g
    rw [e.symm_apply_apply]
    rfl
  have he : τ.comp π = σ := MonoidHom.ext hτ
  exact ⟨τ,hτ,(irreducible_comp_surjective_iff π hπ τ).mp (he.symm ▸ inferInstance)⟩

end Representation
