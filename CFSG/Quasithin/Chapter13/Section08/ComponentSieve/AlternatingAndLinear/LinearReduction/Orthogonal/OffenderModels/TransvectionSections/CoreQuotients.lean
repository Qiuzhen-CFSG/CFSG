module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.Defs
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Recognizing equivariant quotients of the augmentation core

An equivariant quotient of the eight-point binary augmentation module has
kernel zero, the constant line, or the whole core, by the actual alternating
invariant-subspace classification. A nonzero quotient is therefore the core
or the natural six-dimensional module. The proof constructs equivariant
linear equivalences, including in the quotient-by-constants case.

Applying this to a map with image [E,K] constructs that literal commutator
subrepresentation and retains its inclusion into E. Construction of such a
map from a transvection remains a separate obligation; no map is inferred
merely from the dimension or the name of the group.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.3.1, printed p.83, and the module recognition in 13.8.25,
printed p.960 (PDF p.977).
-/

public section
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.TransvectionSections
open BinaryPermutation Representation.BinaryOffender
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]

private theorem core_kernel_alternatives (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* Perm) (f : core (Fin 8) →ₗ[ZMod 2] U)
    (heq : ∀ g v, f (coreRepresentation (Fin 8) (eH g) v) = ρ g (f v))
    (hne : f ≠ 0) :
    f.ker = ⊥ ∨ f.ker = (coreToNatural (Fin 8)).ker := by
  let P := f.ker.map (core (Fin 8)).subtype
  have hP : ∀ g : alternatingGroup (Fin 8), ∀ v ∈ P,
      representation (Fin 8) g.val v ∈ P := by
    rintro g v ⟨u, hu, rfl⟩
    refine ⟨coreRepresentation (Fin 8) g.val u, ?_, rfl⟩
    change f (coreRepresentation (Fin 8) g.val u) = 0
    rw [← eH.apply_symm_apply g.val, heq]
    rw [show f u = 0 from hu, map_zero]
  have hproper : ¬ core (Fin 8) ≤ P := by
    intro h
    apply hne
    ext v
    obtain ⟨w, hw, hwv⟩ := h v.property
    have he : w = v := Subtype.ext hwv
    subst w
    exact hw
  rcases invariant_submodule_classification (by decide : 5 ≤ Fintype.card (Fin 8)) P hP with
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
    change v.val ∈ constants (Fin 8) ↔ coreToNatural (Fin 8) v = 0
    rw [← Subtype.val_inj]
    exact (Submodule.Quotient.mk_eq_zero (constants (Fin 8))).symm
  · exact (hproper ht.ge).elim
  · exact (hproper (by rw [ht]; exact le_top)).elim

/-- Every nonzero equivariant quotient of the eight-point augmentation core
is the core itself or its natural quotient. -/
theorem naturalOrCover_of_core_surjection (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* Perm) (f : core (Fin 8) →ₗ[ZMod 2] U)
    (heq : ∀ g v, f (coreRepresentation (Fin 8) (eH g) v) = ρ g (f v))
    (hf : Function.Surjective f) (hne : f ≠ 0) : IsEightNaturalOrCover ρ eH := by
  rcases core_kernel_alternatives ρ eH f heq hne with hk | hk
  · let e : core (Fin 8) ≃ₗ[ZMod 2] U :=
      LinearEquiv.ofBijective f ⟨LinearMap.ker_eq_bot.mp hk, hf⟩
    refine Or.inr ⟨e.symm, ?_⟩
    intro g u
    apply e.injective
    simp only [e.apply_symm_apply]
    exact (congrArg (ρ g) (e.apply_symm_apply u)).symm.trans (heq g (e.symm u)).symm
  · let q := coreToNatural (Fin 8)
    let eqn := q.quotKerEquivOfSurjective coreToNatural_surjective
    let e : U ≃ₗ[ZMod 2] natural (Fin 8) :=
      (f.quotKerEquivOfSurjective hf).symm.trans
        ((Submodule.quotEquivOfEq _ _ hk).trans eqn)
    have he (v : core (Fin 8)) : e (f v) = q v := by
      simp only [e, LinearEquiv.trans_apply, LinearMap.quotKerEquivOfSurjective_symm_apply,
        Submodule.quotEquivOfEq_mk, eqn, LinearMap.quotKerEquivOfSurjective_apply_mk]
    refine Or.inl ⟨e, ?_⟩
    intro g u
    obtain ⟨v, rfl⟩ := hf u
    rw [← heq, he, he]
    exact coreToNatural_equivariant _ _

/-- A core map whose image is the literal commutator constructs its
subrepresentation and equivariant natural-or-cover identification. -/
theorem commutator_model_of_core_map (ρ : Representation (ZMod 2) H U)
    (K : Subgroup H) (eH : H ≃* Perm) (f : core (Fin 8) →ₗ[ZMod 2] U)
    (heq : ∀ g v, f (coreRepresentation (Fin 8) (eH g) v) = ρ g (f v))
    (hrange : LinearMap.range f = subspaceCommutator ρ ⊤ K)
    (hK : ∃ k ∈ K, ∃ u : U, ρ k u ≠ u) :
    IsCommutatorNaturalOrCover ρ K eH := by
  let J : Subrepresentation ρ := {
    toSubmodule := LinearMap.range f
    apply_mem_toSubmodule := by
      rintro g u ⟨v, rfl⟩
      exact ⟨coreRepresentation (Fin 8) (eH g) v, heq g v⟩ }
  have hf : f.rangeRestrict ≠ 0 := by
    intro hz
    obtain ⟨k, hk, u, hu⟩ := hK
    have hm : ρ k u - u ∈ LinearMap.range f := by
      rw [hrange]
      exact Submodule.subset_span ⟨k, hk, u, Submodule.mem_top, rfl⟩
    obtain ⟨v, hv⟩ := hm
    have he := congrArg (fun j : LinearMap.range f => (j : U)) (LinearMap.congr_fun hz v)
    change f v = 0 at he
    exact hu (sub_eq_zero.mp (hv.symm.trans he))
  exact ⟨J, hrange, naturalOrCover_of_core_surjection J.toRepresentation eH f.rangeRestrict
    (fun g v => Subtype.ext (heq g v)) f.surjective_rangeRestrict hf⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.TransvectionSections
