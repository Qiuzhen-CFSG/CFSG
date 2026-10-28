module
public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.TreeWreathModel
public import Theory.ElementaryAbelian.Injective
public import Mathlib.GroupTheory.SpecificGroups.Alternating


/-!
# Normal elementary subgroups with odd permutations in an S₈ Sylow

Conjugation by the single tree word 108 detects every odd involution outside
the four-pair base. Inside the base, four conjugates under regular block
permutations give sixteen distinct binary products. The certificates check
128 tree words and sixteen base words; they do not enumerate subgroups.
Sylow conjugacy transfers the resulting order bound to every Sylow of S₈.

This is the exceptional local calculation used with the original small-actor
hypothesis in Aschbacher--Smith G.10.15(3), printed p.363, and 14.3.12, p.993.
-/

public noncomputable section
namespace Theory.SpecificGroups.SymmetricEight.NormalElementaryOdd
open Subgroup Equiv.Perm
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals

private def conjugator : S8 := treeWord 108
private def orbitConjugator : Fin 4 → S8 := ![1,treeWord 48,treeWord 64,treeWord 112]
private def orbitProduct (x : S8) (i : Fin 16) : S8 :=
  (if i.val % 2 = 1 then (MulAut.conj (orbitConjugator 0)) x else 1) *
  (if i.val / 2 % 2 = 1 then (MulAut.conj (orbitConjugator 1)) x else 1) *
  (if i.val / 4 % 2 = 1 then (MulAut.conj (orbitConjugator 2)) x else 1) *
  (if i.val / 8 % 2 = 1 then (MulAut.conj (orbitConjugator 3)) x else 1)

private theorem odd_involution_commuting_conjugate_base : ∀ i : Fin 128,
    (treeWord i).sign ≠ 1 → treeWord i ^ 2 = 1 →
    treeWord i * (MulAut.conj conjugator) (treeWord i) =
      (MulAut.conj conjugator) (treeWord i) * treeWord i → i.val < 16 := by
  decide +kernel


private theorem orbitProduct_base_injective : ∀ i : Fin 16,
    (treeWord ⟨i.val, by omega⟩).sign ≠ 1 →
      Function.Injective (orbitProduct (treeWord ⟨i.val, by omega⟩)) := by
  decide +kernel

private theorem orbitConjugator_mem (j : Fin 4) : orbitConjugator j ∈ treeGroup := by
  fin_cases j
  · exact treeGroup.one_mem
  · exact treeWord_mem 48
  · exact treeWord_mem 64
  · exact treeWord_mem 112

open scoped IsMulCommutative

/-- A normal elementary subgroup of the tree Sylow containing an odd element
has at least sixteen elements. -/
theorem tree_normal_elementary_card (A : Subgroup S8) [IsElementaryAbelian 2 A]
    (hle : A ≤ treeGroup) (hn : treeGroup ≤ normalizer (A : Set S8))
    (x : A) (ho : (x : S8).sign ≠ 1) : 16 ≤ Nat.card A := by
  obtain ⟨i,hi⟩ := (mem_treeGroup (x : S8)).mp (hle x.property)
  have hc : conjugator * (x : S8) * conjugator⁻¹ ∈ A :=
    (hn (treeWord_mem 108) _).mp x.property
  have hcomm : (x : S8) * (MulAut.conj conjugator) x =
      (MulAut.conj conjugator) x * x :=
    congrArg Subtype.val (mul_comm x (⟨_,hc⟩ : A))
  have hx2 : (x : S8) ^ 2 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : S8) x.property
  have hil : i.val < 16 := odd_involution_commuting_conjugate_base i
    (hi.symm ▸ ho) (hi.symm ▸ hx2) (hi.symm ▸ hcomm)
  have hm (j : Fin 16) : orbitProduct x j ∈ A := by
    unfold orbitProduct
    repeat apply A.mul_mem
    all_goals split_ifs <;> first
      | exact (hn (orbitConjugator_mem _) _).mp x.property
      | exact A.one_mem
  let f : Fin 16 → A := fun j => ⟨orbitProduct x j,hm j⟩
  have hf : Function.Injective f := by
    intro j k he
    have hprod : orbitProduct x j = orbitProduct x k := congrArg Subtype.val he
    rw [← hi] at hprod
    exact orbitProduct_base_injective ⟨i.val,hil⟩ (hi.symm ▸ ho) hprod
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf

/-- The same bound in an arbitrary Sylow subgroup, with its literal normalizer. -/
theorem sylow_normal_elementary_card (P : Sylow 2 S8)
    (A : Subgroup S8) [IsElementaryAbelian 2 A]
    (hle : A ≤ (P : Subgroup S8)) (hn : (P : Subgroup S8) ≤ normalizer (A : Set S8))
    (x : A) (ho : (x : S8).sign ≠ 1) : 16 ≤ Nat.card A := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq S8 P treeSylow
  let c := MulAut.conj g
  have hP : (P : Subgroup S8).map c.toMonoidHom = treeGroup := by
    change ((g • P : Sylow 2 S8) : Subgroup S8) = treeGroup
    rw [hg,treeSylow_coe]
  let A' := A.map c.toMonoidHom
  let : IsElementaryAbelian 2 A' := IsElementaryAbelian.map c.toMonoidHom
  have hle' : A' ≤ treeGroup := by rw [← hP]; exact Subgroup.map_mono hle
  have hn' : treeGroup ≤ normalizer (A' : Set S8) := by
    rw [← hP]
    exact (Subgroup.map_mono hn).trans (Subgroup.le_normalizer_map c.toMonoidHom)
  let x' : A' := ⟨c x, mem_map.mpr ⟨x,x.property,rfl⟩⟩
  have ho' : (x' : S8).sign ≠ 1 := by
    change (g * (x : S8) * g⁻¹).sign ≠ 1
    rw [map_mul,map_mul,map_inv,mul_comm g.sign (x : S8).sign,
      mul_assoc,mul_inv_cancel,mul_one]
    exact ho
  have hh := tree_normal_elementary_card A' hle' hn' x' ho'
  change 16 ≤ Nat.card (A.map c.toMonoidHom) at hh
  rw [card_map_of_injective c.injective] at hh
  exact hh


end Theory.SpecificGroups.SymmetricEight.NormalElementaryOdd
