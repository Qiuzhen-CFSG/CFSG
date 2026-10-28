module
public import Theory.SpecificGroups.SymmetricFive.AutomorphismRank
public import Theory.GroupTheory.SolvableRadical
public import Theory.GroupTheory.LocalNormalizerUniqueness
public section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.FivePointSylowParabolic

theorem radical_eq_bot_of_alternating_le (M : Subgroup (Equiv.Perm (Fin 5)))
    (hA : alternatingGroup (Fin 5) ≤ M) : solvableRadical M = ⊥ := by
  let : M.Normal := Subgroup.Normal.of_commutator_le _ (alternatingGroup.commutator_perm_le.trans hA)
  let R := (solvableRadical M).map M.subtype
  have hn : R.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    exact (show (⊤ : Subgroup (Equiv.Perm (Fin 5))) ≤ normalizer (M : Set _) by
      rw [normalizer_eq_top]).trans
      (normalizer_le_normalizer_characteristic_image M (solvableRadical M))
  have hr : R = ⊥ := by
    by_contra hne
    let := hn
    have hAR : alternatingGroup (Fin 5) ≤ R :=
      Equiv.Perm.alternatingGroup_le_of_normal (by simp) ((nontrivial_iff_ne_bot R).mpr hne)
    let : Group.IsSolvable R :=
      Group.isSolvable_of_surjective (f := M.subtype.subgroupMap (solvableRadical M))
        (M.subtype.subgroupMap_surjective _)
    let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5))
      (Group.isSolvable_of_isSolvable_injective (inclusion_injective hAR))
  exact ((solvableRadical M).map_eq_bot_iff_of_injective M.subtype_injective).mp hr

theorem solvable_normal_le_ker {E : Type*} [Group E] [Finite E]
    (f : E →* Equiv.Perm (Fin 5)) (hA : alternatingGroup (Fin 5) ≤ f.range)
    (N : Subgroup E) [N.Normal] [Group.IsSolvable N] : N ≤ f.ker := by
  let g := f.rangeRestrict
  have hn : (N.map g).Normal := Subgroup.Normal.map inferInstance g f.rangeRestrict_surjective
  have hs : Group.IsSolvable (N.map g) := Group.isSolvable_of_surjective
    (f := g.subgroupMap N) (g.subgroupMap_surjective N)
  have hle := le_solvableRadical (N.map g) hn hs
  rw [radical_eq_bot_of_alternating_le f.range hA] at hle
  intro n hn
  have he : g n = 1 := hle (mem_map_of_mem g hn)
  exact congrArg Subtype.val he
end Theory.SpecificGroups.FivePointSylowParabolic
