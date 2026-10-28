module
public import Theory.GroupTheory.PerfectMinimalSimpleTwoNormalizer
/-!
# Large perfect automorphism groups cannot normalize a two-group

A perfect automorphism subgroup of a finite centerless simple group, with
solvable outer group, embeds in the inner group. If its order is at least
the order of the original group, that embedding is surjective. A normalized
two-subgroup would then lie in the two-core of an automorphism overgroup,
which is trivial.

This is the equal-order component obstruction used in the unitary
specialization of Aschbacher–Smith C.4.5–8, printed pp.152–154.
-/

public section
open Subgroup Theory.GroupTheory
namespace MulAut
variable {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q] [Group.IsPerfect Q]

theorem perfect_normalizer_two_eq_bot_of_card_le
    (hz : center Q = ⊥)
    [Group.IsSolvable (Outer Q)]
    (A U : Subgroup (MulAut Q)) [Group.IsPerfect A]
    (hcard : Nat.card Q ≤ Nat.card A) (hU : IsPGroup 2 U)
    (hAU : A ≤ normalizer (U : Set (MulAut Q))) : U = ⊥ := by
  obtain ⟨f,hf,hconj⟩ := perfect_subgroup_exists_inner_lift A hz
  have hs : Function.Surjective f := (hf.bijective_of_nat_card_le hcard).2
  have hi : ∀ x : Q, conj x ∈ A := by
    intro x
    obtain ⟨a,ha⟩ := hs x
    rw [←ha,hconj]
    exact a.property
  have hcore : pCore 2 Q = ⊥ := by
    rcases (inferInstance : (pCore 2 Q).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · have hp : IsPGroup 2 Q := IsPGroup.of_equiv
        (pCore_isPGroup (p := 2) (G := Q)) ((MulEquiv.subgroupCongr ht).trans topEquiv)
      let := hp.isNilpotent
      exact (Group.IsPerfect.not_isSolvable Q inferInstance).elim
  let J := A ⊔ U
  have hj : pCore 2 J = ⊥ := automorphism_core_eq_bot 2
    (conj_injective_of_center_eq_bot hz) hcore J (fun x => mem_sup_left (hi x))
  have hu : U ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes hU le_sup_right
    (sup_le hAU U.le_normalizer)
  unfold Subgroup.pCoreIn at hu
  rw [hj,Subgroup.map_bot] at hu
  exact bot_unique hu
end MulAut
