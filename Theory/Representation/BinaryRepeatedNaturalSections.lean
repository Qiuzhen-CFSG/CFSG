module
public import Theory.Representation.PSL3Two.SurjectiveCoordinates
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.Irreducibility
public import Theory.Representation.Quotient
public import Theory.Representation.BinaryPermutationNaturalDuality

/-!
# Repeated natural sections and self-dual permutation covers

For a non-self-dual simple representation, every intertwiner to its dual
vanishes. Pulling back a self-duality along a surjective cover gives such
an intertwiner from the upper module to the dual of its lower section.
It kills both the lower section and the cover kernel, so exactness forces
it to factor through the repeated upper section. This contradicts its
surjectivity. No semisimplicity of the extension is assumed.

The binary SL₃(2) application uses the same surjective actor map on both
natural sections and the invariant dot product on the literal deleted
permutation module on seven letters. It supplies the marked restriction
obstruction in Aschbacher--Smith 12.2.25, printed p.805, independently of
how the smaller actor embeds in the alternating group.
-/

public noncomputable section
open Representation
namespace Representation
variable {k A V M N : Type*} [Field k] [Group A]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- A repeated non-self-dual simple section cannot cover a self-dual module
nontrivially on its lower section. The kernel allowance retains a fixed radical. -/
theorem no_self_dual_cover_of_repeated_sections
    (ρ : Representation k A V) [ρ.IsIrreducible]
    (σ : Representation k A M) (τ : Representation k A N)
    (hdual : ¬ Nonempty (ρ.Equiv ρ.dual))
    (i : ρ.IntertwiningMap σ) (p : σ.IntertwiningMap ρ)
    (hp : Function.Surjective p)
    (f : σ.IntertwiningMap τ) (hf : Function.Surjective f)
    (hker : p.toLinearMap.ker ≤ i.toLinearMap.range ⊔ f.toLinearMap.ker)
    (hfi : f.comp i ≠ 0) (e : τ.Equiv τ.dual) : False := by
  have hz (a : ρ.IntertwiningMap ρ.dual) : a = 0 := by
    rcases IsIrreducible.injective_or_eq_zero a with ha | ha
    · have hs : Function.Surjective a :=
        (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp ha
      exact (hdual ⟨a.ofBijective ⟨ha,hs⟩⟩).elim
    · exact ha
  have hfi_inj : Function.Injective (f.comp i) :=
    (IsIrreducible.injective_or_eq_zero (f.comp i)).resolve_right hfi
  let j : σ.IntertwiningMap ρ.dual := {
    toLinearMap := (f.comp i).toLinearMap.dualMap.comp (e.toLinearMap.comp f.toLinearMap)
    isIntertwining' := by
      intro a
      ext m v
      change e (f (σ a m)) (f (i v)) = e (f m) (f (i (ρ a⁻¹ v)))
      rw [f.isIntertwining]
      have he := LinearMap.congr_fun (e.isIntertwining' a) (f m)
      change e (τ a (f m)) = τ.dual a (e (f m)) at he
      rw [he]
      change e (f m) (τ a⁻¹ (f (i v))) = _
      rw [← f.isIntertwining, ← i.isIntertwining] }
  have hj : Function.Surjective j :=
    (LinearMap.dualMap_surjective_of_injective hfi_inj).comp (e.surjective.comp hf)
  have hji := hz (j.comp i)
  have hk : p.toLinearMap.ker ≤ j.toLinearMap.ker := by
    apply hker.trans
    apply sup_le
    · rintro x ⟨v,rfl⟩
      exact congrArg (fun t : ρ.IntertwiningMap ρ.dual => t v) hji
    · intro x hx
      change f x = 0 at hx
      change (f.comp i).toLinearMap.dualMap (e (f x)) = 0
      rw [hx,map_zero,map_zero]
  let b : V →ₗ[k] Module.Dual k V :=
    (p.toLinearMap.ker.liftQ j.toLinearMap hk).comp
      (p.toLinearMap.quotKerEquivOfSurjective hp).symm.toLinearMap
  have hb (m : M) : b (p m) = j m := by
    change p.toLinearMap.ker.liftQ j.toLinearMap hk
      ((p.toLinearMap.quotKerEquivOfSurjective hp).symm (p.toLinearMap m)) = _
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
    rfl
  let b' : ρ.IntertwiningMap ρ.dual := {
    toLinearMap := b
    isIntertwining' := by
      intro a
      apply LinearMap.ext
      intro v
      obtain ⟨m,rfl⟩ := hp v
      change b (ρ a (p m)) = ρ.dual a (b (p m))
      rw [← p.isIntertwining,hb,hb,j.isIntertwining] }
  have hzero : ∀ m : M, j m = 0 := by
    intro m
    rw [← hb]
    exact congrArg (fun t : ρ.IntertwiningMap ρ.dual => t (p m)) (hz b')
  have hsub : Subsingleton (Module.Dual k V) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨x,rfl⟩ := hj a
    obtain ⟨y,rfl⟩ := hj b
    rw [hzero,hzero]
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨a,b,hab⟩ := exists_pair_ne (Module.Dual k V)
  exact hab (hsub.elim a b)
end Representation

namespace BinaryLinearThree
open Representation
variable {A M : Type*} [_root_.Group A] [AddCommGroup M] [Module (ZMod 2) M]

/-- Literal binary permutation actions cannot have the same marked natural
three-space below and above, even allowing a radical killed by the cover. -/
theorem no_permutation_cover_of_repeated_natural_sections
    (q : A →* Group) (hq : Function.Surjective q)
    (σ : Representation (ZMod 2) A M) (a : A →* Equiv.Perm (Fin 7))
    (i : Representation.IntertwiningMap (W.comp q) σ) (p : σ.IntertwiningMap (W.comp q))
    (hp : Function.Surjective p)
    (f : σ.IntertwiningMap ((BinaryPermutation.naturalRepresentation (Fin 7)).comp a))
    (hf : Function.Surjective f)
    (hker : p.toLinearMap.ker ≤ i.toLinearMap.range ⊔ f.toLinearMap.ker)
    (hfi : f.comp i ≠ 0) : False := by
  let : IsIrreducible (W.comp q) :=
    (irreducible_comp_surjective_iff q hq W).mpr IrreducibleCatalogue.natural_irreducible
  have hdual : ¬ Nonempty (Representation.Equiv (W.comp q) (Representation.dual (W.comp q))) := by
    exact (NaturalCover.mk q hq (LinearEquiv.refl _ _) (fun _ _ => rfl)).not_self_dual
  let τ : Representation (ZMod 2) A (BinaryPermutation.natural (Fin 7)) :=
    (BinaryPermutation.naturalRepresentation (Fin 7)).comp a
  let e : τ.Equiv τ.dual := {
    toLinearEquiv := BinaryPermutation.naturalDualEquiv (Fin 7)
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro v
      simpa only [LinearMap.comp_apply, τ, Representation.dual_apply,
        MonoidHom.comp_apply, map_inv, LinearEquiv.coe_coe] using
          BinaryPermutation.naturalDualEquiv_equivariant (Fin 7) (a g) v }
  exact no_self_dual_cover_of_repeated_sections (W.comp q) σ τ hdual i p hp f hf hker hfi e
end BinaryLinearThree
