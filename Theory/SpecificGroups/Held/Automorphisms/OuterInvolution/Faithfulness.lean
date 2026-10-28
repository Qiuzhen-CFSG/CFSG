module

public import Theory.SpecificGroups.Held.Model.Transitivity
public import Theory.SpecificGroups.Held.Automorphisms.Reduction
/-!
# Faithfulness of the Held permutation-normalizer action

The permutation `a*b` has exactly one fixed point, namely letter 293.
A permutation commuting with Held must fix that point. Transitivity then
forces it to fix every point. Thus the permutation centralizer is trivial,
and the full normalizer acts faithfully by automorphisms of Held.

In particular, the implementing permutation and its induced automorphism
have the same order. This justifies passing from involutory actions to
involutory permutations without adding a hypothesis.
Source: the concrete ATLAS `HeG1-p2058B0` tables and their transitivity tree.
-/

public section
namespace Held.OuterInvolution
open Subgroup
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem ab_fixed_iff : ∀ x : Fin 2058, (atlasA * atlasB) x = x ↔ x = 293 := by
  decide +kernel

theorem permutation_centralizer_eq_bot :
    centralizer (permutationGroup : Set (Equiv.Perm (Fin 2058))) = ⊥ := by
  apply eq_bot_iff.mpr
  intro c hc
  rw [mem_bot]
  have commute (g : He) : representation g * c = c * representation g :=
    mem_centralizer_iff.mp hc _ g.property
  have h293 : c 293 = 293 := by
    apply (ab_fixed_iff _).mp
    have h := congrArg (fun p : Equiv.Perm (Fin 2058) => p 293) (commute (a * b))
    change (atlasA * atlasB) (c 293) = c ((atlasA * atlasB) 293) at h
    rw [(ab_fixed_iff 293).mpr rfl] at h
    exact h
  apply Equiv.ext
  intro x
  change c x = x
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq He (293 : Fin 2058) x
  change representation g 293 = x at hg
  have h := congrArg (fun p : Equiv.Perm (Fin 2058) => p 293) (commute g)
  change representation g (c 293) = c (representation g 293) at h
  simpa only [h293, hg] using h.symm

theorem normalizer_action_injective :
    Function.Injective permutationGroup.normalizerMonoidHom := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [normalizerMonoidHom_ker, permutation_centralizer_eq_bot]
  apply eq_bot_iff.mpr
  intro n hn
  rw [mem_bot]
  apply Subtype.ext
  exact hn

theorem normalizer_action_order
    (n : normalizer (permutationGroup : Set (Equiv.Perm (Fin 2058)))) :
    orderOf (permutationGroup.normalizerMonoidHom n) = orderOf n :=
  orderOf_injective _ normalizer_action_injective n
theorem normalizer_action_inner_iff
    (n : normalizer (permutationGroup : Set (Equiv.Perm (Fin 2058)))) :
    (∃ g : He, MulAut.conj g = permutationGroup.normalizerMonoidHom n) ↔
      (n : Equiv.Perm (Fin 2058)) ∈ permutationGroup := by
  constructor
  · rintro ⟨g, hg⟩
    let m : normalizer (permutationGroup : Set (Equiv.Perm (Fin 2058))) :=
      ⟨representation g, permutationGroup.le_normalizer g.property⟩
    have hm : permutationGroup.normalizerMonoidHom m = MulAut.conj g := by
      ext x
      rfl
    have he : m = n := normalizer_action_injective (hm.trans hg)
    exact he ▸ g.property
  · intro hn
    refine ⟨⟨n, hn⟩, ?_⟩
    ext x
    rfl
end Held.OuterInvolution
