module

public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.Basic

/-!
# A common Sylow subgroup of the two block stabilizers

The seven interchanges in the binary tree on eight letters have 128 normal
forms. Right multiplication by any generator stays in these normal forms;
the inverse permutation recovers the seven binary coordinates. This proves
both generation and the order without enumerating S₈. Each generator preserves
the pair partition and the four-point partition. Adjoining the central C₂
therefore gives a common Sylow subgroup of the two lifted stabilizers.

The normal-form argument is adapted from this repository's
`CFSG/Quasithin/ChapterB/Section03/Offenders/Eight/Sylow.lean`, with only its
intrinsic permutation mathematics retained, so there is no upward import.
Source: Aschbacher–Smith, Proposition B.3.2, printed pp.83–84; the present
application is Lemma 2.5.26, printed p.569.
-/

@[expose] public section
namespace Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
open Subgroup

/-- The seven involutions interchanging children of a binary tree. -/
def treeGenerator : Fin 7 → S8 :=
  ![Equiv.swap 0 1, Equiv.swap 2 3, Equiv.swap 4 5, Equiv.swap 6 7,
    Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.swap 4 6 * Equiv.swap 5 7,
    Equiv.swap 0 4 * Equiv.swap 1 5 * Equiv.swap 2 6 * Equiv.swap 3 7]

/-- The binary normal forms, with lower tree levels written first. -/
def treeWord (i : Fin 128) : S8 :=
  (if i.val % 2 = 1 then treeGenerator 0 else 1) *
  (if i.val / 2 % 2 = 1 then treeGenerator 1 else 1) *
  (if i.val / 4 % 2 = 1 then treeGenerator 2 else 1) *
  (if i.val / 8 % 2 = 1 then treeGenerator 3 else 1) *
  (if i.val / 16 % 2 = 1 then treeGenerator 4 else 1) *
  (if i.val / 32 % 2 = 1 then treeGenerator 5 else 1) *
  (if i.val / 64 % 2 = 1 then treeGenerator 6 else 1)

private def treeWordIndex (g : S8) : ℕ :=
  (g⁻¹ 0).val % 2 + 2 * ((g⁻¹ 2).val % 2) +
    4 * ((g⁻¹ 4).val % 2) + 8 * ((g⁻¹ 6).val % 2) +
    16 * ((g⁻¹ 0).val / 2 % 2) + 32 * ((g⁻¹ 4).val / 2 % 2) +
    64 * ((g⁻¹ 0).val / 4)

set_option maxRecDepth 10000 in
private theorem treeWordIndex_word : ∀ i, treeWordIndex (treeWord i) = i.val := by
  decide +kernel

private def treeNext (i : Fin 128) (j : Fin 7) : Fin 128 :=
  ⟨treeWordIndex (treeWord i * treeGenerator j) % 128, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem treeWord_step : ∀ i j, treeWord i * treeGenerator j = treeWord (treeNext i j) := by
  decide +kernel

private theorem treeGenerator_inv : ∀ j, (treeGenerator j)⁻¹ = treeGenerator j := by
  decide +kernel

def treeGroup : Subgroup S8 := Subgroup.closure (Set.range treeGenerator)

theorem treeGenerator_mem (i : Fin 7) : treeGenerator i ∈ treeGroup :=
  Subgroup.subset_closure ⟨i, rfl⟩

theorem treeWord_mem (i : Fin 128) : treeWord i ∈ treeGroup := by
  unfold treeWord
  repeat apply treeGroup.mul_mem
  all_goals split_ifs <;> first | exact treeGenerator_mem _ | exact treeGroup.one_mem

theorem mem_treeGroup (g : S8) : g ∈ treeGroup ↔ ∃ i, treeWord i = g := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction_right with
    | one => exact ⟨0, rfl⟩
    | mul_right x hx y hy ih =>
      obtain ⟨i, rfl⟩ := ih
      obtain ⟨j, rfl⟩ := hy
      exact ⟨treeNext i j, (treeWord_step i j).symm⟩
    | mul_inv_cancel x hx y hy ih =>
      obtain ⟨i, rfl⟩ := ih
      obtain ⟨j, rfl⟩ := hy
      rw [treeGenerator_inv]
      exact ⟨treeNext i j, (treeWord_step i j).symm⟩
  · rintro ⟨i, rfl⟩
    exact treeWord_mem i

theorem treeWord_injective : Function.Injective treeWord := by
  intro i j h
  apply Fin.ext
  simpa only [treeWordIndex_word] using congrArg treeWordIndex h

theorem card_treeGroup : Nat.card treeGroup = 128 := by
  have e : treeGroup ≃ Set.range treeWord :=
    Equiv.setCongr (by ext g; exact mem_treeGroup g)
  rw [Nat.card_congr e, ← Nat.card_congr (Equiv.ofInjective treeWord treeWord_injective)]
  simp

theorem treeGroup_le_flagStabilizer : treeGroup ≤ flagStabilizer := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  exact (by decide +kernel : ∀ i, treeGenerator i ∈ flagStabilizer) i

/-- The full common Sylow subgroup in C₂ × S₈. -/
def standardTwoGroup : Subgroup X := (⊤ : Subgroup C2).prod treeGroup

theorem card_standardTwoGroup : Nat.card standardTwoGroup = 256 := by
  change Nat.card ((⊤ : Subgroup C2).prod treeGroup) = 256
  rw [Nat.card_congr ((⊤ : Subgroup C2).prodEquiv treeGroup).toEquiv,
    Nat.card_prod, Subgroup.card_top, card_treeGroup]
  norm_num [C2, Nat.card_eq_fintype_card]

noncomputable def standardSylow : Sylow 2 X :=
  Sylow.ofCard standardTwoGroup (by
    rw [card_standardTwoGroup,
      ← (Sylow.card_eq_multiplicity (Sylow.nonempty.some : Sylow 2 X)), card_sylow])

@[simp] theorem standardSylow_coe : (standardSylow : Subgroup X) = standardTwoGroup := rfl

theorem standardSylow_le_pairOvergroup : (standardSylow : Subgroup X) ≤ pairOvergroup :=
  Subgroup.prod_mono le_rfl (treeGroup_le_flagStabilizer.trans inf_le_left)

theorem standardSylow_le_fourOvergroup : (standardSylow : Subgroup X) ≤ fourOvergroup :=
  Subgroup.prod_mono le_rfl (treeGroup_le_flagStabilizer.trans inf_le_right)

end Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
