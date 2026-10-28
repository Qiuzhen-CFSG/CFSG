module

public import Theory.Representation.BinaryPermutation.SevenPointChiefFactor
public import Mathlib.Algebra.Module.ZMod

/-!
# Irreducibility of the five-letter core as a group

An equivariant group identification with the binary five-letter core transfers
its irreducibility to invariant subgroups. Over the prime field every additive
subgroup is a submodule. The actor is allowed to cover A₅ surjectively.

Source: Aschbacher–Smith, B.3.1; used for the moved section in 14.4.9.
-/

public section
namespace BinaryPermutation

/-- The five-letter core has no proper nontrivial invariant subgroup. -/
theorem fiveCore_invariant_subgroup
    (F : Subgroup (Multiplicative (core (Fin 5))))
    (hF : ∀ g : alternatingGroup (Fin 5), ∀ v ∈ F,
      Multiplicative.ofAdd (coreRepresentation (Fin 5) g.val v.toAdd) ∈ F) :
    F = ⊥ ∨ F = ⊤ := by
  let e : Subgroup (Multiplicative (core (Fin 5))) ≃o
      Submodule (ZMod 2) (core (Fin 5)) :=
    AddSubgroup.toSubgroup.symm.trans (AddSubgroup.toZModSubmodule 2)
  have h := SevenPointChiefFactor.fiveCore_simple (e F) hF
  rcases h with h | h
  · left
    exact e.injective (h.trans e.map_bot.symm)
  · right
    exact e.injective (h.trans e.map_top.symm)

/-- An actual equivariant identification with the core transfers irreducibility. -/
theorem invariant_subgroup_of_fiveCore
    {K Q : Type*} [Group K] [Group Q]
    (M : Subgroup Q) (ρ : K →* MulAut Q)
    (hM : ∀ k : K, ∀ v ∈ M, ρ k v ∈ M)
    (π : K →* alternatingGroup (Fin 5)) (hπ : Function.Surjective π)
    (e : M ≃* Multiplicative (core (Fin 5)))
    (he : ∀ (k : K) (v : M),
      e ⟨ρ k v, hM k v v.property⟩ =
        Multiplicative.ofAdd (coreRepresentation (Fin 5) (π k).val (e v).toAdd))
    (F : Subgroup Q) (hFM : F ≤ M)
    (hF : ∀ k : K, ∀ v ∈ F, ρ k v ∈ F) : F = ⊥ ∨ F = M := by
  let E := (F.subgroupOf M).map e.toMonoidHom
  have hE : ∀ g : alternatingGroup (Fin 5), ∀ v ∈ E,
      Multiplicative.ofAdd (coreRepresentation (Fin 5) g.val v.toAdd) ∈ E := by
    intro g v hv
    obtain ⟨k, rfl⟩ := hπ g
    obtain ⟨u, hu, rfl⟩ := hv
    change Multiplicative.ofAdd (coreRepresentation (Fin 5) (π k).val (e u).toAdd) ∈ E
    rw [← he]
    exact Subgroup.mem_map_of_mem _ (hF k u hu)
  rcases fiveCore_invariant_subgroup E hE with h | h
  · left
    apply le_antisymm _ bot_le
    intro v hv
    have hvE : e ⟨v,hFM hv⟩ ∈ E := Subgroup.mem_map_of_mem _ hv
    rw [h] at hvE
    have hv1 : (⟨v,hFM hv⟩ : M) = 1 := e.injective
      ((Subgroup.mem_bot.mp hvE).trans e.map_one.symm)
    exact congrArg Subtype.val hv1
  · right
    apply le_antisymm hFM
    intro v hv
    have hvE : e ⟨v,hv⟩ ∈ E := h ▸ Subgroup.mem_top _
    obtain ⟨u, hu, huv⟩ := hvE
    have huv' := congrArg Subtype.val (e.injective huv)
    change (u : Q) = v at huv'
    change (u : Q) ∈ F at hu
    exact huv' ▸ hu
end BinaryPermutation
