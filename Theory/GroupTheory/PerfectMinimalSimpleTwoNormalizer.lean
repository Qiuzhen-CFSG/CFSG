module
public import Theory.GroupTheory.PerfectAutomorphismStabilizer
public import Theory.GroupTheory.PCoreLocalSetup
/-!
# Perfect normalizers over minimal simple groups

If every proper subgroup of a centerless simple group is soluble, a
nontrivial perfect automorphism subgroup is the full inner group, provided
the outer group is soluble. It cannot normalize a nontrivial two-subgroup:
that two-subgroup would lie in the two-core of an automorphism overgroup.

This retains outer radical actions in the rank-one A5 case of
Aschbacher–Smith C.4.5–6, printed p.152.
-/

public section
open Subgroup Theory.GroupTheory
namespace MulAut
variable {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q] [Group.IsPerfect Q]

theorem perfect_minimal_simple_normalizer_two_eq_bot
    (hz : center Q = ⊥)
    (hproper : ∀ B : Subgroup Q, B ≠ ⊤ → Group.IsSolvable B)
    [Group.IsSolvable (Outer Q)]
    (A U : Subgroup (MulAut Q)) [Group.IsPerfect A]
    (hne : A ≠ ⊥) (hU : IsPGroup 2 U)
    (hAU : A ≤ normalizer (U : Set (MulAut Q))) : U = ⊥ := by
  obtain ⟨f,hf,hconj⟩ := perfect_subgroup_exists_inner_lift A hz
  have hr : f.range = ⊤ := by
    by_contra hr
    let : Group.IsSolvable f.range := hproper f.range hr
    let : Group.IsSolvable A := Group.isSolvable_of_isSolvable_injective
      (f := f.rangeRestrict) (by intro x y hxy; exact hf (congrArg Subtype.val hxy))
    let : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isSolvable A inferInstance
  have hi : ∀ x : Q, conj x ∈ A := by
    intro x
    obtain ⟨a,ha⟩ := (show x ∈ f.range from hr ▸ mem_top x)
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
