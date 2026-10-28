module

public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.ActionIdentification.Generation

/-!
# Invariance under the two actual derived-group generators

On a finite module, injectivity makes a generator's restriction to a stable
subspace surjective. Thus inverse generators also preserve the subspace.
Free-group induction and the checked surjectivity of the actual generator
homomorphism establish invariance for the entire derived group.
Source application: Aschbacher–Smith G.7.2(3), printed pp.347–348.
-/

public section

namespace G2DerivedPermutationFiltration.CycleModelLink
open VertexCoordinates

theorem invariant_of_generators {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] (ρ : Representation (ZMod 2) Group V) (S : Submodule (ZMod 2) V)
    (h : ∀ (j : Fin 2) v, v ∈ S → ρ (groupGenerator j) v ∈ S) :
    ∀ g v, v ∈ S → ρ g v ∈ S := by
  intro g
  obtain ⟨w, rfl⟩ := groupHom_surjective g
  induction w using FreeGroup.induction_on with
  | C1 => intro v hv; simpa only [map_one, Module.End.one_apply] using hv
  | of j => exact h j
  | inv_of j ih =>
    let f : S → S := fun v => ⟨ρ (groupHom (FreeGroup.of j)) v.val, ih v.val v.property⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      exact (Representation.apply_bijective ρ (groupHom (FreeGroup.of j))).1
        (congrArg Subtype.val hxy)
    intro v hv
    obtain ⟨u, hu⟩ := Finite.surjective_of_injective hf ⟨v, hv⟩
    have hu' : ρ (groupHom (FreeGroup.of j)) u.val = v := congrArg Subtype.val hu
    rw [map_inv, ← hu', Representation.inv_self_apply]
    exact u.property
  | mul a b ha hb =>
    intro v hv
    simpa only [map_mul, Module.End.mul_apply] using ha _ (hb v hv)

end G2DerivedPermutationFiltration.CycleModelLink
