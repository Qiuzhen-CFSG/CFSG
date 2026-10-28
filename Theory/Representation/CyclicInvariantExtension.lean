module

public import Theory.Representation.CyclicQuotientExtension
public import Theory.Representation.CharacterEquivalence
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Extending a cyclic-invariant character to a semidirect product

An irreducible complex representation whose character is invariant under a
finite cyclic action extends to the semidirect product on the original space.
Identify the base group with the kernel of the projection onto the complement;
character invariance gives the conjugate equivalences required by cyclic
quotient extension. An irreducible restriction makes the extension irreducible.

This is the extension-existence step used in Lyons, *A Characterization of the
Group U₃(4)* (1972), Lemma 4, p. 381.
-/

public section

open Representation

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Representation

/-- Irreducibility of a pullback implies irreducibility of the representation. -/
theorem isIrreducible_of_comp {F G H W : Type*} [Field F] [Monoid G] [Monoid H]
    [AddCommGroup W] [Module F W] (σ : Representation F G W) (f : H →* G)
    [IsIrreducible (σ.comp f)] : IsIrreducible σ := by
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial (σ.comp f)
  rw [IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun S => ?_⟩
  let T : Subrepresentation (σ.comp f) :=
    ⟨S.toSubmodule, fun h _ hv => S.apply_mem_toSubmodule (f h) hv⟩
  rcases eq_bot_or_eq_top T with h | h
  · left
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun U : Subrepresentation (σ.comp f) => U.toSubmodule) h
  · right
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun U : Subrepresentation (σ.comp f) => U.toSubmodule) h

variable {K C V : Type*} [Group K] [Finite K] [Group C] [Finite C] [IsCyclic C]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

private def baseKernelEquiv (α : C →* MulAut K) :
    K ≃* (SemidirectProduct.rightHom (φ := α)).ker where
  toFun k := ⟨SemidirectProduct.inl k, by simp⟩
  invFun x := x.1.left
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    ext
    · rfl
    · exact x.2.symm
  map_mul' _ _ := by apply Subtype.ext; exact map_mul _ _ _

omit [Finite K] [Finite C] [IsCyclic C] in
private theorem conjugate_inl (α : C →* MulAut K) (g : K ⋊[α] C) (k : K) :
    g * SemidirectProduct.inl k * g⁻¹ =
      SemidirectProduct.inl (g.left * α g.right k * g.left⁻¹) := by
  rcases g with ⟨a, b⟩
  ext <;> simp [mul_assoc]

/-- An invariant irreducible character extends through a finite cyclic action,
on the original vector space, and the extension is irreducible. -/
theorem exists_cyclic_semidirect_extension (α : C →* MulAut K)
    (ρ : Representation ℂ K V) [IsIrreducible ρ]
    (hinv : ∀ t s, ρ.character (α t s) = ρ.character s) :
    ∃ σ : Representation ℂ (K ⋊[α] C) V,
      IsIrreducible σ ∧ σ.comp SemidirectProduct.inl = ρ := by
  classical
  let G := K ⋊[α] C
  let N : Subgroup G := (SemidirectProduct.rightHom (φ := α)).ker
  let e : K ≃* N := baseKernelEquiv α
  let τ : Representation ℂ N V := ρ.comp e.symm.toMonoidHom
  let : IsIrreducible τ :=
    (RepEquiv.irreducible_iff_group_iso (ρ := τ) (σ := ρ) e.symm
      (fun _ _ => rfl)).2 inferInstance
  let : Finite G := Finite.of_equiv (K × C) (SemidirectProduct.equivProd (φ := α)).symm
  let eqQ : (G ⧸ N) ≃* C := QuotientGroup.quotientKerEquivOfSurjective
    (SemidirectProduct.rightHom (φ := α)) SemidirectProduct.rightHom_surjective
  have hcyc : IsCyclic (G ⧸ N) :=
    isCyclic_of_surjective eqQ.symm.toMonoidHom eqQ.symm.surjective
  have E : ∀ g : G, τ ≃ₗ conjugateRep τ g := by
    intro g
    apply RepEquiv.ofRepresentationEquiv
    apply Classical.choice
    apply equiv_of_character_eq
    ext n
    obtain ⟨k, rfl⟩ := e.surjective n
    have hc : (⟨g * (e k).val * g⁻¹,
        Subgroup.Normal.conj_mem (inferInstance : N.Normal) (e k) (e k).2 g⟩ : N) =
        e (g.left * α g.right k * g.left⁻¹) := by
      apply Subtype.ext
      change g * SemidirectProduct.inl k * g⁻¹ =
        SemidirectProduct.inl (g.left * α g.right k * g.left⁻¹)
      exact conjugate_inl α g k

    change ρ.character k = LinearMap.trace ℂ V ((conjugateRep τ g) (e k))
    rw [conjugateRep_apply, hc]
    change ρ.character k = ρ.character (g.left * α g.right k * g.left⁻¹)
    rw [char_conj, hinv]
  obtain ⟨σ, hσ⟩ := proposition_2_2_b (W := V) N hcyc τ E
  have hres : σ.comp SemidirectProduct.inl = ρ := by
    ext k v
    exact congrArg (fun r : Representation ℂ N V => r (e k) v) hσ
  let : IsIrreducible (σ.comp SemidirectProduct.inl) := hres.symm ▸ inferInstance
  exact ⟨σ, isIrreducible_of_comp σ SemidirectProduct.inl, hres⟩

end Representation
