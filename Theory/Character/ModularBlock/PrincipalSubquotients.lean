module

public import Theory.Character.ModularBlock.Cartan

/-!
# Principal-block subquotients

The actual principal selector acts as the identity on subrepresentations,
quotients, and equivalent representations whenever it does on the original
module. Intertwining maps are group-algebra linear, so injectivity or
surjectivity transports this identity.

A finite basis also extends coordinate completeness of a principal Brauer
family to arbitrary finite-dimensional spaces. A simple module consequently
has a single multiplicity in the family. These are the selector and simple
factor steps of ordinary-to-modular decomposition, using the definitions of
`Cartan.lean`; no semisimplicity is required.
-/

public section

noncomputable section
namespace ModularBlock.Cartan
open PrincipalBlockConstruction BrauerCoefficientExtension
variable {G : Type*} [Group G] [Finite G]
variable {d : PrincipalCongruenceBlockData G}
variable {V W : Type*} [AddCommGroup V] [Module (splittingField d) V]
  [AddCommGroup W] [Module (splittingField d) W]
variable {ρ : Representation (splittingField d) G V}
  {σ : Representation (splittingField d) G W}

/-- An equivariant injection into a block module detects the selector identity. -/
theorem inPrincipalBlock_of_injective_intertwiner
    (f : ρ.IntertwiningMap σ) (hf : Function.Injective f)
    (hσ : InPrincipalBlock d σ) : InPrincipalBlock d ρ := by
  apply LinearMap.ext
  intro v
  apply hf
  have h := (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ f).map_smul
    (splittingSelector d) v
  change f (ρ.asAlgebraHom (splittingSelector d) v) =
    σ.asAlgebraHom (splittingSelector d) (f v) at h
  change σ.asAlgebraHom (splittingSelector d) = 1 at hσ
  simpa only [hσ, Module.End.one_apply] using h

/-- An equivariant quotient inherits the selector identity. -/
theorem inPrincipalBlock_of_surjective_intertwiner
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f)
    (hρ : InPrincipalBlock d ρ) : InPrincipalBlock d σ := by
  apply LinearMap.ext
  intro w
  obtain ⟨v, rfl⟩ := hf w
  have h := (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ f).map_smul
    (splittingSelector d) v
  change f (ρ.asAlgebraHom (splittingSelector d) v) =
    σ.asAlgebraHom (splittingSelector d) (f v) at h
  change ρ.asAlgebraHom (splittingSelector d) = 1 at hρ
  simpa only [hρ, Module.End.one_apply] using h.symm

/-- Every invariant subspace of a principal-block module belongs to that block. -/
theorem inPrincipalBlock_subrepresentation (S : Subrepresentation ρ)
    (hρ : InPrincipalBlock d ρ) : InPrincipalBlock d S.toRepresentation := by
  let f : S.toRepresentation.IntertwiningMap ρ :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  exact inPrincipalBlock_of_injective_intertwiner f Subtype.val_injective hρ

/-- Quotienting by an invariant subspace preserves principal-block membership. -/
theorem inPrincipalBlock_quotient (S : Subrepresentation ρ)
    (hρ : InPrincipalBlock d ρ) :
    InPrincipalBlock d (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) := by
  let f : ρ.IntertwiningMap (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) :=
    { toLinearMap := S.toSubmodule.mkQ
      isIntertwining' := fun _ => rfl }
  exact inPrincipalBlock_of_surjective_intertwiner f S.toSubmodule.mkQ_surjective hρ

/-- Principal-block membership is invariant under representation equivalence. -/
theorem inPrincipalBlock_equiv (e : ρ.Equiv σ) :
    InPrincipalBlock d ρ ↔ InPrincipalBlock d σ :=
  ⟨inPrincipalBlock_of_surjective_intertwiner e.toIntertwiningMap e.toLinearEquiv.surjective,
    inPrincipalBlock_of_injective_intertwiner e.toIntertwiningMap e.toLinearEquiv.injective⟩

end ModularBlock.Cartan

namespace ModularBlock.Cartan.PrincipalBrauerFamily
open PrincipalBlockConstruction BrauerCoefficientExtension
variable {G : Type*} [Group G] [Finite G]
variable {d : PrincipalCongruenceBlockData G} {n : ℕ}
variable (b : PrincipalBrauerFamily d n)

/-- Coordinate completeness covers finite-dimensional representations in any universe. -/
theorem complete_finiteDimensional
    {V : Type*} [AddCommGroup V] [Module (splittingField d) V]
    [FiniteDimensional (splittingField d) V]
    (ρ : Representation (splittingField d) G V)
    (hρ : Representation.IsIrreducible ρ) (hblock : InPrincipalBlock d ρ) :
    ∃ j, Nonempty (ρ.Equiv (b.rep j)) := by
  classical
  let K := splittingField d
  let basisEquiv := (Module.finBasis K V).equivFun
  let σ : Representation K G (Fin (Module.finrank K V) → K) :=
    (basisEquiv.conjAlgEquiv K).toAlgHom.toMonoidHom.comp ρ
  let e : ρ.Equiv σ := .mk basisEquiv (by
    intro g
    ext v
    simp [σ, LinearEquiv.conjAlgEquiv_apply])
  have hσ : Representation.IsIrreducible σ := by
    let := hρ
    rw [Representation.irreducible_iff_isSimpleModule_asModule]
    let E : σ.asModule ≃ₗ[MonoidAlgebra K G] ρ.asModule :=
      LinearEquiv.ofBijective
        (Representation.IntertwiningMap.equivLinearMapAsModule σ ρ
          e.symm.toIntertwiningMap) e.symm.toLinearEquiv.bijective
    exact E.isSimpleModule_iff.mpr inferInstance
  obtain ⟨j, ⟨f⟩⟩ := b.complete _ σ hσ ((inPrincipalBlock_equiv e).mp hblock)
  exact ⟨j, ⟨e.trans f⟩⟩

/-- A simple block module has a single multiplicity in a complete Brauer family. -/
theorem exists_multiplicities_of_irreducible
    {V : Type*} [AddCommGroup V] [Module (splittingField d) V]
    [FiniteDimensional (splittingField d) V]
    (ρ : Representation (splittingField d) G V)
    (hρ : Representation.IsIrreducible ρ) (hblock : InPrincipalBlock d ρ) :
    ∃ c : Fin n → ℕ, ∀ g : G,
      BrauerCharacter.value d ρ g =
        ∑ j, (c j : ℂ) * BrauerCharacter.value d (b.rep j) g := by
  classical
  obtain ⟨j, ⟨e⟩⟩ := b.complete_finiteDimensional ρ hρ hblock
  refine ⟨fun k => if k = j then 1 else 0, ?_⟩
  intro g
  simpa using BrauerCharacter.value_equiv d e g

end ModularBlock.Cartan.PrincipalBrauerFamily
