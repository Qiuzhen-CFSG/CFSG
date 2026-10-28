module

public import Theory.Alternating.theorem_5_2_1_2
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Recognition from a noncollapsed type-A chain

In degree at least five, elements satisfying the adjacent-transposition
relations generate a symmetric group as soon as the product of the first
two generators is nonidentity. The type-A presentation supplies a map from
the symmetric group. A nontrivial kernel would contain the alternating group
and kill that product. The resulting isomorphism records every generator,
which matters in degree six because abstract isomorphisms can exchange the
two classes of odd involutions.

This is the presentation step used in Aschbacher, “A 2-local characterization
of M12”, Illinois J. Math. 47 (2003), Lemma 4.6. The presentation itself is
proved in `Theory.Alternating.theorem_5_2_1_2`.
-/

namespace Theory.GroupTheory.SymmetricCoxeterRecognition

open Subgroup GLS3.Chapter5.SchurPresentation

variable {G : Type*} [Group G] (n : ℕ)
variable (f : Fin (n + 4) → G) (hf : CoxeterMatrix.IsLiftable (CoxeterMatrix.A (n + 4)) f)

private noncomputable def presentationEquiv : TypeACoxeterGroup n ≃* Equiv.Perm (Fin (n + 5)) :=
  MulEquiv.ofBijective (typeACoxeterPermutationProjection n)
    ⟨typeACoxeterPermutationProjection_injective n,
      typeACoxeterPermutationProjection_surjective n⟩

/-- The representation specified by the type-A relations. -/
public noncomputable def lift : Equiv.Perm (Fin (n + 5)) →* G :=
  ((CoxeterMatrix.A (n + 4)).toCoxeterSystem.lift ⟨f, hf⟩).comp
    (presentationEquiv n).symm.toMonoidHom

public theorem lift_adjacent (i : Fin (n + 4)) :
    lift n f hf (adjacentSwap n i) = f i := by
  rw [← typeACoxeterPermutationProjection_simple n i]
  change (CoxeterMatrix.A (n + 4)).toCoxeterSystem.lift ⟨f, hf⟩
    ((presentationEquiv n).symm
      (presentationEquiv n ((CoxeterMatrix.A (n + 4)).simple i))) = _
  rw [MulEquiv.symm_apply_apply]
  exact (CoxeterMatrix.A (n + 4)).toCoxeterSystem.lift_apply_simple hf i

/-- One surviving adjacent product rules out all nontrivial kernels. -/
public theorem lift_injective (hne : f 0 * f 1 ≠ 1) : Function.Injective (lift n f hf) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  by_contra hk
  have hn : Nontrivial (lift n f hf).ker := (Subgroup.nontrivial_iff_ne_bot _).mpr hk
  have hA := Equiv.Perm.alternatingGroup_le_of_normal
    (by simp : 5 ≤ Nat.card (Fin (n + 5))) hn
  have hm : adjacentSwap n 0 * adjacentSwap n 1 ∈ alternatingGroup (Fin (n + 5)) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    have hs (i : Fin (n + 4)) : Equiv.Perm.sign (adjacentSwap n i) = -1 := by
      apply Equiv.Perm.sign_swap
      intro he
      have hh := congrArg Fin.val he
      change i.val = i.val + 1 at hh
      omega
    rw [map_mul, hs, hs]
    norm_num
  have hz := hA hm
  change lift n f hf (adjacentSwap n 0 * adjacentSwap n 1) = 1 at hz
  rw [map_mul, lift_adjacent, lift_adjacent] at hz
  exact hne hz

public theorem lift_range : (lift n f hf).range = closure (Set.range f) := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    obtain ⟨w, rfl⟩ := (presentationEquiv n).surjective p
    change (CoxeterMatrix.A (n + 4)).toCoxeterSystem.lift ⟨f, hf⟩
      ((presentationEquiv n).symm (presentationEquiv n w)) ∈ _
    rw [MulEquiv.symm_apply_apply]
    apply (CoxeterMatrix.A (n + 4)).toCoxeterSystem.simple_induction w
    · intro i
      rw [CoxeterSystem.lift_apply_simple]
      exact subset_closure ⟨i, rfl⟩
    · simp only [map_one]
      exact one_mem _
    · intro v w hv hw
      simpa only [map_mul] using mul_mem hv hw
  · apply (closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨adjacentSwap n i, lift_adjacent n f hf i⟩

include hf in
/-- The generated subgroup is the symmetric group, with all simple
reflections identified with the specified adjacent transpositions. -/
public theorem exists_marked_equiv (hne : f 0 * f 1 ≠ 1) :
    ∃ e : closure (Set.range f) ≃* Equiv.Perm (Fin (n + 5)),
      ∀ i, e ⟨f i, subset_closure ⟨i, rfl⟩⟩ = adjacentSwap n i := by
  let e₀ : Equiv.Perm (Fin (n + 5)) ≃* (lift n f hf).range :=
    MulEquiv.ofBijective (lift n f hf).rangeRestrict
      ⟨fun _ _ he => lift_injective n f hf hne (congrArg Subtype.val he),
        (lift n f hf).rangeRestrict_surjective⟩
  let e := e₀.trans (MulEquiv.subgroupCongr (lift_range n f hf))
  refine ⟨e.symm, fun i => ?_⟩
  apply e.injective
  rw [e.apply_symm_apply]
  apply Subtype.ext
  exact (lift_adjacent n f hf i).symm

end Theory.GroupTheory.SymmetricCoxeterRecognition
