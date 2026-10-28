module

public import Theory.Representation.BinaryPermutationNaturalStructure
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Equivariant quotients of a binary augmentation core

Alternating-invariant subspaces of the full permutation module are zero,
constants, the augmentation core, or the whole module. Thus a nonzero
quotient of the core is the core itself or its natural quotient. The two
linear equivalences below retain the supplied full symmetric actor marking.
This is the uniform form of the eight-letter calculation used in Chapter 13.

Source: Aschbacher–Smith, B.3.1, printed p.83, and G.6.4, pp.345–346.
-/

public section
namespace BinaryPermutation
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]

private theorem core_kernel_alternatives {n : ℕ} (hn : 5 ≤ n) (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* Equiv.Perm (Fin n)) (f : core (Fin n) →ₗ[ZMod 2] U)
    (heq : ∀ g v, f (coreRepresentation (Fin n) (eH g) v) = ρ g (f v))
    (hne : f ≠ 0) :
    f.ker = ⊥ ∨ f.ker = (coreToNatural (Fin n)).ker := by
  let P := f.ker.map (core (Fin n)).subtype
  have hP : ∀ g : alternatingGroup (Fin n), ∀ v ∈ P,
      representation (Fin n) g.val v ∈ P := by
    rintro g v ⟨u, hu, rfl⟩
    refine ⟨coreRepresentation (Fin n) g.val u, ?_, rfl⟩
    change f (coreRepresentation (Fin n) g.val u) = 0
    rw [← eH.apply_symm_apply g.val, heq]
    rw [show f u = 0 from hu, map_zero]
  have hproper : ¬ core (Fin n) ≤ P := by
    intro h
    apply hne
    ext v
    obtain ⟨w, hw, hwv⟩ := h v.property
    have he : w = v := Subtype.ext hwv
    subst w
    exact hw
  rcases invariant_submodule_classification (by simpa using hn : 5 ≤ Fintype.card (Fin n)) P hP with
      hz | hc | ht | ht
  · left
    apply le_antisymm _ bot_le
    intro v hv
    have hv' : v.val ∈ P := ⟨v, hv, rfl⟩
    rw [hz] at hv'
    exact Subtype.ext hv'
  · right
    ext v
    have hv : v ∈ f.ker ↔ v.val ∈ P := by
      constructor
      · exact fun h => ⟨v, h, rfl⟩
      · rintro ⟨w, hw, he⟩
        exact (Subtype.ext he : w = v) ▸ hw
    rw [hv, hc]
    change v.val ∈ constants (Fin n) ↔ coreToNatural (Fin n) v = 0
    rw [← Subtype.val_inj]
    exact (Submodule.Quotient.mk_eq_zero (constants (Fin n))).symm
  · exact (hproper ht.ge).elim
  · exact (hproper (by rw [ht]; exact le_top)).elim

/-- Every nonzero equivariant quotient of the eight-point augmentation core
is the core itself or its natural quotient. -/
theorem natural_or_core_of_core_surjection {n : ℕ} (hn : 5 ≤ n) (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* Equiv.Perm (Fin n)) (f : core (Fin n) →ₗ[ZMod 2] U)
    (heq : ∀ g v, f (coreRepresentation (Fin n) (eH g) v) = ρ g (f v))
    (hf : Function.Surjective f) (hne : f ≠ 0) :
    (∃ E : U ≃ₗ[ZMod 2] natural (Fin n),
      ∀ g u, E (ρ g u) = naturalRepresentation (Fin n) (eH g) (E u)) ∨
    (∃ E : U ≃ₗ[ZMod 2] core (Fin n),
      ∀ g u, E (ρ g u) = coreRepresentation (Fin n) (eH g) (E u)) := by
  rcases core_kernel_alternatives hn ρ eH f heq hne with hk | hk
  · let e : core (Fin n) ≃ₗ[ZMod 2] U :=
      LinearEquiv.ofBijective f ⟨LinearMap.ker_eq_bot.mp hk, hf⟩
    refine Or.inr ⟨e.symm, ?_⟩
    intro g u
    apply e.injective
    simp only [e.apply_symm_apply]
    exact (congrArg (ρ g) (e.apply_symm_apply u)).symm.trans (heq g (e.symm u)).symm
  · let q := coreToNatural (Fin n)
    let eqn := q.quotKerEquivOfSurjective coreToNatural_surjective
    let e : U ≃ₗ[ZMod 2] natural (Fin n) :=
      (f.quotKerEquivOfSurjective hf).symm.trans
        ((Submodule.quotEquivOfEq _ _ hk).trans eqn)
    have he (v : core (Fin n)) : e (f v) = q v := by
      simp only [e, LinearEquiv.trans_apply, LinearMap.quotKerEquivOfSurjective_symm_apply,
        Submodule.quotEquivOfEq_mk, eqn, LinearMap.quotKerEquivOfSurjective_apply_mk]
    refine Or.inl ⟨e, ?_⟩
    intro g u
    obtain ⟨v, rfl⟩ := hf u
    rw [← heq, he, he]
    exact coreToNatural_equivariant _ _


end BinaryPermutation
