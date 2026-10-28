module

public import Theory.Representation.SixLetterRadicalDisplacement.PermutationQuotients.QuadraticKernels
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Faithfulness of noncentral syntheme quotients

A nontrivial normal subgroup of S₆ contains A₆, hence contains the even
radical D₀. If such a subgroup were the actor kernel on a noncentral
syntheme quotient, D₀ would act trivially, and therefore quadratically,
contrary to the finite invariant-kernel calculation. For A₆ the kernel is
trivial or the whole group by simplicity; the latter possibility similarly
contradicts the intrinsic alternating-radical obstruction.

The resulting injectivity statements require only a surjective equivariant
map from the actual marked fifteen-point module and a noncentrality witness.
The actor-isomorphism versions retain the same quotient and linear action.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma 13.8.34, printed p.968 (PDF p.985), the faithful-action step in the
rank-one argument. Noncentrality is the conclusion of 13.8.4(5), using
13.7.7; source marking and specialization belong to the source assembly.
-/

public section

open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Representation.BinaryOffender
namespace Representation.SixLetterRadicalDisplacement.PermutationQuotients

private theorem quadratic_of_le_ker {G Q : Type*} [Group G]
    [AddCommGroup Q] [Module (ZMod 2) Q]
    (σ : Representation (ZMod 2) G Q) (E : Subgroup G) (hE : E ≤ σ.asGroupHom.ker) :
    IsQuadratic σ E := by
  intro a ha b _ v
  have h : σ a = 1 := congrArg Units.val (show σ.asGroupHom a = 1 from hE ha)
  rw [h, Module.End.one_apply]

/-- Every noncentral equivariant quotient of the marked syntheme module is faithful for S₆. -/
theorem faithful_of_noncentral_quotient {Q : Type*} [AddCommGroup Q] [Module (ZMod 2) Q]
    (σ : Representation (ZMod 2) S Q) (f : P →ₗ[ZMod 2] Q)
    (hf : Function.Surjective f) (heq : ∀ g v, f (rho g v) = σ g (f v))
    (hnc : ∃ g v, σ g v ≠ v) : Function.Injective σ := by
  have hk : σ.asGroupHom.ker = ⊥ := by
    by_contra hne
    have hA : alternatingGroup (Fin 6) ≤ σ.asGroupHom.ker :=
      Equiv.Perm.alternatingGroup_le_of_normal (by simp)
        ((Subgroup.nontrivial_iff_ne_bot _).mpr hne)
    exact not_quadratic_D0 σ f hf heq hnc
      (quadratic_of_le_ker σ D0 (inf_le_right.trans hA))
  intro x y hxy
  exact (σ.asGroupHom.ker_eq_bot_iff.mp hk) (Units.ext hxy)

/-- The same faithfulness conclusion for the intrinsic A₆ action and an A₆-equivariant quotient. -/
theorem alternating_faithful_of_noncentral_quotient {Q : Type*}
    [AddCommGroup Q] [Module (ZMod 2) Q]
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 6)) Q) (f : P →ₗ[ZMod 2] Q)
    (hf : Function.Surjective f) (heq : ∀ g v, f (rhoA g v) = σ g (f v))
    (hnc : ∃ g v, σ g v ≠ v) : Function.Injective σ := by
  have hk : σ.asGroupHom.ker = ⊥ := by
    rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (by simp : 5 ≤ Nat.card (Fin 6))
        (N := σ.asGroupHom.ker) with hbot | htop
    · exact hbot
    · exact False.elim (not_quadratic_alternatingRadical σ f hf heq hnc
        (quadratic_of_le_ker σ alternatingRadical (by rw [htop]; exact le_top)))
  intro x y hxy
  exact (σ.asGroupHom.ker_eq_bot_iff.mp hk) (Units.ext hxy)

/-- Faithfulness transported through a chosen isomorphism of the actor with S₆. -/
theorem actor_faithful_of_noncentral_quotient {G Q : Type*} [Group G]
    [AddCommGroup Q] [Module (ZMod 2) Q]
    (e : G ≃* S) (σ : Representation (ZMod 2) G Q) (f : P →ₗ[ZMod 2] Q)
    (hf : Function.Surjective f) (heq : ∀ g v, f (rho (e g) v) = σ g (f v))
    (hnc : ∃ g v, σ g v ≠ v) : Function.Injective σ := by
  let τ := σ.comp e.symm.toMonoidHom
  have hτeq : ∀ g v, f (rho g v) = τ g (f v) := by
    intro g v
    simpa [τ] using heq (e.symm g) v
  have hτnc : ∃ g v, τ g v ≠ v := by
    obtain ⟨g, v, h⟩ := hnc
    exact ⟨e g, v, by simpa [τ] using h⟩
  have hτ := faithful_of_noncentral_quotient τ f hf hτeq hτnc
  intro a b hab
  apply e.injective
  apply hτ
  simpa [τ] using hab

/-- Faithfulness transported through a chosen isomorphism of the actor with A₆. -/
theorem alternating_actor_faithful_of_noncentral_quotient {G Q : Type*} [Group G]
    [AddCommGroup Q] [Module (ZMod 2) Q]
    (e : G ≃* alternatingGroup (Fin 6)) (σ : Representation (ZMod 2) G Q)
    (f : P →ₗ[ZMod 2] Q) (hf : Function.Surjective f)
    (heq : ∀ g v, f (rhoA (e g) v) = σ g (f v))
    (hnc : ∃ g v, σ g v ≠ v) : Function.Injective σ := by
  let τ := σ.comp e.symm.toMonoidHom
  have hτeq : ∀ g v, f (rhoA g v) = τ g (f v) := by
    intro g v
    simpa [τ] using heq (e.symm g) v
  have hτnc : ∃ g v, τ g v ≠ v := by
    obtain ⟨g, v, h⟩ := hnc
    exact ⟨e g, v, by simpa [τ] using h⟩
  have hτ := alternating_faithful_of_noncentral_quotient τ f hf hτeq hτnc
  intro a b hab
  apply e.injective
  apply hτ
  simpa [τ] using hab

end Representation.SixLetterRadicalDisplacement.PermutationQuotients
