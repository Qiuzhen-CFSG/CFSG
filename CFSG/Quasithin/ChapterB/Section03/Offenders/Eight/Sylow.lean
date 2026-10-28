module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Defs
public import CFSG.Quasithin.ChapterB.Section03.Offenders.FixedTests
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Canonical.Representatives
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Conjugacy
public import Mathlib.GroupTheory.Sylow
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# A canonical Sylow two-subgroup in degree eight

The seven swaps of the binary tree on eight letters generate a group of order
128. Its normal forms consist of four independent pair swaps, two swaps of
pairs inside the four-point blocks, and an interchange of those blocks. Kernel
checked generator transitions prove that these are all the elements. Their
order and the odd index 315 establish the Sylow property.

A transposition outside the four canonical pairs has an order-three product
with one of the canonical swaps. Thus every transposition in a two-subgroup
containing `D` already lies in `D`. This proves the containment needed for
case (a) and uniqueness of a conjugate of `D` inside such a two-subgroup.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Proposition B.3.2(4)–(6), printed pp. 83–84.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterB.Offenders.Eight

open Representation.BinaryOffender

def secondBlockSwap : Perm := Equiv.swap 4 6 * Equiv.swap 5 7
def halfSwap : Perm := Equiv.swap 0 4 * Equiv.swap 1 5 * Equiv.swap 2 6 * Equiv.swap 3 7
def sylowGenerators : Fin 7 → Perm :=
  ![pairSwap 8 0, pairSwap 8 1, pairSwap 8 2, pairSwap 8 3,
    kleinSecond 8 (by decide), secondBlockSwap, halfSwap]
def sylowWord (i : Fin 128) : Perm :=
  dWords ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩ *
    (if i.val / 16 % 2 = 1 then kleinSecond 8 (by decide) else 1) *
    (if i.val / 32 % 2 = 1 then secondBlockSwap else 1) *
    (if i.val / 64 % 2 = 1 then halfSwap else 1)
private def sylowWordIndex (g : Perm) : ℕ :=
  (g⁻¹ 0).val % 2 + 2 * ((g⁻¹ 2).val % 2) +
    4 * ((g⁻¹ 4).val % 2) + 8 * ((g⁻¹ 6).val % 2) +
    16 * ((g⁻¹ 0).val / 2 % 2) + 32 * ((g⁻¹ 4).val / 2 % 2) +
    64 * ((g⁻¹ 0).val / 4)

set_option maxRecDepth 10000 in
private theorem sylowWordIndex_word : ∀ i, sylowWordIndex (sylowWord i) = i.val := by decide +kernel

private def sylowNext (i : Fin 128) (j : Fin 7) : Fin 128 :=
  ⟨sylowWordIndex (sylowWord i * sylowGenerators j) % 128, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem sylowWord_step : ∀ i j, sylowWord i * sylowGenerators j = sylowWord (sylowNext i j) := by decide +kernel

private theorem sylowGenerators_inv : ∀ j, (sylowGenerators j)⁻¹ = sylowGenerators j := by decide +kernel

def canonicalTwoSubgroup : Subgroup Perm := Subgroup.closure (Set.range sylowGenerators)

theorem sylowWord_mem (i : Fin 128) : sylowWord i ∈ canonicalTwoSubgroup := by
  have hgen (j : Fin 7) : sylowGenerators j ∈ canonicalTwoSubgroup := Subgroup.subset_closure ⟨j, rfl⟩
  have hD : D 8 ≤ canonicalTwoSubgroup := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, _, rfl⟩
    fin_cases j
    all_goals first | exact hgen 0 | exact hgen 1 | exact hgen 2 | exact hgen 3
  unfold sylowWord
  apply canonicalTwoSubgroup.mul_mem
  · apply canonicalTwoSubgroup.mul_mem
    · apply canonicalTwoSubgroup.mul_mem
      · exact hD ((mem_disjointTranspositions_iff 4 _).mpr
          ⟨⟨i.val % 16, Nat.mod_lt _ (by decide)⟩, rfl⟩)
      · split_ifs
        · exact hgen 4
        · exact canonicalTwoSubgroup.one_mem
    · split_ifs
      · exact hgen 5
      · exact canonicalTwoSubgroup.one_mem
  · split_ifs
    · exact hgen 6
    · exact canonicalTwoSubgroup.one_mem

theorem mem_canonicalTwoSubgroup (g : Perm) : g ∈ canonicalTwoSubgroup ↔ ∃ i, sylowWord i = g := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction_right with
    | one => exact ⟨0, rfl⟩
    | mul_right x hx y hy ih =>
      obtain ⟨i, rfl⟩ := ih
      obtain ⟨j, rfl⟩ := hy
      exact ⟨sylowNext i j, (sylowWord_step i j).symm⟩
    | mul_inv_cancel x hx y hy ih =>
      obtain ⟨i, rfl⟩ := ih
      obtain ⟨j, rfl⟩ := hy
      rw [sylowGenerators_inv]
      exact ⟨sylowNext i j, (sylowWord_step i j).symm⟩
  · rintro ⟨i, rfl⟩
    exact sylowWord_mem i

theorem sylowWord_injective : Function.Injective sylowWord := by
  intro i j h
  apply Fin.ext
  simpa only [sylowWordIndex_word] using congrArg sylowWordIndex h

theorem card_canonicalTwoSubgroup : Nat.card canonicalTwoSubgroup = 128 := by
  have e : canonicalTwoSubgroup ≃ Set.range sylowWord := Equiv.setCongr (by ext g; exact mem_canonicalTwoSubgroup g)
  rw [Nat.card_congr e, ← Nat.card_congr (Equiv.ofInjective sylowWord sylowWord_injective)]
  simp

def canonicalSylow : Sylow 2 Perm :=
  (IsPGroup.of_card (show Nat.card canonicalTwoSubgroup = 2 ^ 7 from card_canonicalTwoSubgroup)).toSylow (by
    have hi := canonicalTwoSubgroup.card_mul_index
    have hc : Nat.card Perm = 40320 := by
      simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    rw [card_canonicalTwoSubgroup, hc] at hi
    have hindex : canonicalTwoSubgroup.index = 315 := by omega
    rw [hindex]
    decide)

/-- The concrete Sylow has the explicitly generated subgroup as its carrier. -/
theorem canonicalSylow_coe : (canonicalSylow : Subgroup Perm) = canonicalTwoSubgroup := rfl

theorem sylowGenerators_mem (i : Fin 7) : sylowGenerators i ∈ canonicalSylow :=
  Subgroup.subset_closure ⟨i, rfl⟩

theorem D_le_canonicalSylow : D 8 ≤ canonicalSylow := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, _, rfl⟩
  fin_cases i
  all_goals first
    | exact sylowGenerators_mem 0
    | exact sylowGenerators_mem 1
    | exact sylowGenerators_mem 2
    | exact sylowGenerators_mem 3

theorem disjointTranspositions_le_canonicalSylow (m : ℕ) :
    disjointTranspositions 8 m ≤ canonicalSylow :=
  (disjointTranspositions_le_D 8 m).trans D_le_canonicalSylow

theorem exceptional_le_canonicalSylow : exceptional 8 (by decide) ≤ canonicalSylow := by
  apply (Subgroup.closure_le _).mpr
  rintro g (hg | ⟨i, _, rfl⟩)
  · rcases hg with rfl | hg
    · exact canonicalSylow.mul_mem (sylowGenerators_mem 0) (sylowGenerators_mem 1)
    · rw [Set.mem_singleton_iff] at hg
      subst g
      exact sylowGenerators_mem 4
  · exact D_le_canonicalSylow (pairSwap_mem i i.isLt)

theorem evenPart_le_canonicalSylow : evenPart 8 ≤ canonicalSylow :=
  inf_le_left.trans D_le_canonicalSylow

theorem hyperplane_le_canonicalSylow {H : Subgroup Perm} (hH : H ⋖ D 8) :
    H ≤ canonicalSylow := hH.le.trans D_le_canonicalSylow

private theorem swap_obstruction : ∀ a b : Fin 8, a ≠ b →
    (∃ i : Fin 4, Equiv.swap a b = pairSwap 8 i) ∨
    ∃ i : Fin 4, (Equiv.swap a b * pairSwap 8 i) ^ 3 = 1 ∧
      Equiv.swap a b * pairSwap 8 i ≠ 1 := by decide +kernel

/-- Every transposition in a two-subgroup containing `D` is a canonical pair swap. -/
theorem isSwap_mem_D_of_isPGroup {P : Subgroup Perm} (hP : IsPGroup 2 P)
    (hD : D 8 ≤ P) {s : Perm} (hs : s.IsSwap) (hsP : s ∈ P) : s ∈ D 8 := by
  rcases hs with ⟨a, b, hab, rfl⟩
  rcases swap_obstruction a b hab with ⟨i, hi⟩ | ⟨i, hc, hne⟩
  · rw [hi]
    exact pairSwap_mem (n := 8) (m := 4) i i.isLt
  · have hmem := P.mul_mem hsP (hD (pairSwap_mem (n := 8) (m := 4) i i.isLt))
    have heq : (⟨Equiv.swap a b * pairSwap 8 i, hmem⟩ : P) = 1 := by
      have hx : (⟨Equiv.swap a b * pairSwap 8 i, hmem⟩ : P) ^ 3 = 1 := Subtype.ext hc
      apply (hP.powEquiv (by decide : Nat.Coprime 2 3)).injective
      simpa only [IsPGroup.powEquiv_apply, one_pow] using hx
    exact False.elim (hne (congrArg Subtype.val heq))

private theorem conj_pairSwap_isSwap (g : Perm) (i : Fin 4) :
    ((MulAut.conj g) (pairSwap 8 i)).IsSwap := by
  let a : Fin 8 := ⟨2 * i.val, by omega⟩
  let b : Fin 8 := ⟨2 * i.val + 1, by omega⟩
  refine ⟨g a, g b, ?_, ?_⟩
  · apply g.injective.ne
    intro h
    have := congrArg Fin.val h
    dsimp [a, b] at this
    omega
  · change g * Equiv.swap a b * g⁻¹ = Equiv.swap (g a) (g b)
    exact Equiv.symm_trans_swap_trans a b g

/-- The case-(a) containment holds in every two-subgroup containing `D`. -/
theorem caseAFamily_le_D_of_isPGroup {P : Subgroup Perm} (hP : IsPGroup 2 P)
    (hD : D 8 ≤ P) {A : Subgroup Perm} (hA : CaseAFamily 8 A) (hAP : A ≤ P) :
    A ≤ D 8 := by
  rcases hA with ⟨m, _, _, g, rfl⟩
  apply Subgroup.map_le_iff_le_comap.mpr
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, hi, rfl⟩
  apply isSwap_mem_D_of_isPGroup hP hD (conj_pairSwap_isSwap g i)
  exact hAP (Subgroup.mem_map.mpr ⟨pairSwap 8 i, pairSwap_mem i hi, rfl⟩)

/-- Two conjugates of the full pair-swap group cannot share a two-overgroup. -/
theorem conjugate_D_eq_of_le_isPGroup {P A : Subgroup Perm} (hP : IsPGroup 2 P)
    (hD : D 8 ≤ P) (hA : IsConjugateTo A (D 8)) (hAP : A ≤ P) : A = D 8 := by
  have hle := caseAFamily_le_D_of_isPGroup hP hD ⟨4, by decide, by decide, hA⟩ hAP
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [(hA.isElementaryTwo isElementaryTwo_D8).card_eq_two_pow_rank,
    hA.rank_eq, rank_D]
  exact (card_disjointTranspositions 4).le

end CFSG.Quasithin.ChapterB.Offenders.Eight
