module
public import Theory.SpecificGroups.SymmetricEight.PairFourGroupObstruction
public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.TreeWreathModel
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupTheory.SylowNormalizerOvergroup
/-!
# A large normal elementary subgroup of every S₈ Sylow subgroup

The elementary base fixes each of four pairs individually. It is normalized
by the pair stabilizer and lies in the binary-tree Sylow by Sylow maximality.
Eight distinct pair-flip words give the strict lower bound needed to separate
this Sylow group from the Hall–Janko Sylow. Sylow conjugacy transports the
literal base to every Sylow subgroup of S₈.

Source: Aschbacher–Smith A.3.12, pp.47–48, used in 15.3.32(3), p.1133;
the existing binary-tree model and pair stabilizer retain their source references.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SymmetricEight
open A6ShadowTwoLocals PairFourGroupObstruction
private theorem pairBase_elementary : IsElementaryAbelian 2 pairBase := by
  have hsq (g : pairBase) : g ^ 2 = 1 := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    change g.val (g.val i) = i
    have h1 := g.property i
    have h2 := (g.property (g.val i)).trans h1
    change (g.val i).val / 2 = i.val / 2 at h1
    change (g.val (g.val i)).val / 2 = i.val / 2 at h2
    by_cases h : g.val i = i
    · rw [h,h]
    by_contra hh
    have he : g.val (g.val i) = g.val i := by
      apply Fin.ext
      have hn : (g.val i).val ≠ i.val := fun he => h (Fin.ext he)
      have hhn : (g.val (g.val i)).val ≠ i.val := fun he => hh (Fin.ext he)
      omega
    exact h (g.val.injective he)
  exact {
    toIsMulCommutative := ⟨⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun g => orderOf_dvd_of_pow_eq_one (hsq g)) a b).eq⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsq }

private theorem pairBase_card_ge_eight : 8 ≤ Nat.card pairBase := by
  have hm : ∀ i : Fin 8, treeWord ⟨i.val, by omega⟩ ∈ pairBase := by
    change ∀ i : Fin 8, ∀ j : Fin 8, (treeWord ⟨i.val, by omega⟩ j).val / 2 = j.val / 2
    decide +kernel
  let f : Fin 8 → pairBase := fun i => ⟨treeWord ⟨i.val, by omega⟩, hm i⟩
  have hf : Function.Injective f := by
    intro i j he
    have hh := treeWord_injective (congrArg Subtype.val he)
    exact Fin.ext (congrArg (fun x : Fin 128 => x.val) hh)
  simpa using Nat.card_le_card_of_injective f hf

/-- Every S₈ Sylow has a normal elementary subgroup of order greater than four. -/
theorem exists_large_normal_elementary (P : Sylow 2 (Equiv.Perm (Fin 8))) :
    ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 4 < Nat.card E := by
  have hn : treeGroup ≤ normalizer (pairBase : Set S8) :=
    (treeGroup_le_flagStabilizer.trans inf_le_left).trans pairBase_normalizes
  have hle : pairBase ≤ treeGroup := pairBase_isPGroup.le_sylow_of_normalized treeSylow hn
  let E := pairBase.subgroupOf treeGroup
  let : E.Normal := normal_subgroupOf_of_le_normalizer hn
  let : IsElementaryAbelian 2 pairBase := pairBase_elementary
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hle
  let e : treeGroup ≃* P := treeSylow.equiv P
  refine ⟨E.map e.toMonoidHom, (inferInstance : E.Normal).map e.toMonoidHom e.surjective,
    IsElementaryAbelian.map _, ?_⟩
  rw [card_map_of_injective e.injective,Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]
  exact (by decide : 4 < 8).trans_le pairBase_card_ge_eight
end Theory.SpecificGroups.SymmetricEight
