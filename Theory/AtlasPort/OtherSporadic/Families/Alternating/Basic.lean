/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Families/Alternating/Basic.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
public import Theory.AtlasPort.OtherSporadic.Families.Cyclic.Construction

/-!
# Basic

Alternating groups are given concrete carriers with orders, actions, and simplicity facts.
The proofs specialize Mathlib results and handle the small degrees separately.

Source: Gerald Höhn, ATLAS, `Atlas/Families/Alternating/Basic.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for downstream calculations in the source API.
-/

@[expose] public section

namespace Atlas.Families.Alternating

abbrev Model (n : ℕ) := ↥(alternatingGroup (Fin n))
def IsAdmissible (n : ℕ) : Prop := 5 ≤ n
def order (n : ℕ) : ℕ := if n < 2 then 1 else n.factorial / 2

theorem finite (n : ℕ) : Finite (Model n) := inferInstance

theorem normal (n : ℕ) : (alternatingGroup (Fin n)).Normal := inferInstance

theorem index (n : ℕ) (hn : 2 ≤ n) : (alternatingGroup (Fin n)).index = 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  exact alternatingGroup.index_eq_two

theorem card_mul_two (n : ℕ) (hn : 2 ≤ n) : 2 * Nat.card (Model n) = n.factorial := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  simpa only [Nat.card_perm, Nat.card_fin] using two_mul_nat_card_alternatingGroup (α := Fin n)

theorem card_factorial (n : ℕ) (hn : 2 ≤ n) : Nat.card (Model n) = n.factorial / 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  simpa only [Nat.card_fin] using nat_card_alternatingGroup (α := Fin n)

theorem factorial_divisible (n : ℕ) (hn : 2 ≤ n) : 2 ∣ n.factorial :=
  ⟨Nat.card (Model n), (card_mul_two n hn).symm⟩

theorem trivial_small (n : ℕ) (hn : n ≤ 2) : alternatingGroup (Fin n) = ⊥ :=
  alternatingGroup.eq_bot_of_card_le_two (by simpa)

theorem card (n : ℕ) : Nat.card (Model n) = order n := by
  by_cases hn : n < 2
  · have h := trivial_small n (by omega)
    simp [Model, h, order, hn]
  · simpa [order, hn] using card_factorial n (by omega)

theorem isSimpleGroup (n : ℕ) (hn : IsAdmissible n) : IsSimpleGroup (Model n) :=
  alternatingGroup.isSimpleGroup (by simpa [IsAdmissible] using hn)

theorem exists_mul_ne_mul (n : ℕ) (hn : 4 ≤ n) :
    ∃ a b : Model n, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hc : IsMulCommutative (Model n) := ⟨⟨h⟩⟩
  have := alternatingGroup.isMulCommutative_iff_card_le_three.mp hc
  simp only [Nat.card_fin] at this
  omega

theorem cyclic_three : IsCyclic (Model 3) :=
  alternatingGroup.isCyclic_of_card_le_three (by simp)

theorem simple_three : IsSimpleGroup (Model 3) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply isSimpleGroup_of_prime_card (p := 3)
  rw [card_factorial _ (by decide)]; norm_num [Nat.factorial]

noncomputable def threeEquivCyclic : Model 3 ≃* Cyclic.Model 3 := by
  have e := (zmodCyclicMulEquiv cyclic_three).symm
  have h : Nat.card (Model 3) = 3 := by rw [card_factorial _ (by decide)]; norm_num [Nat.factorial]
  exact e.trans (by rw [h])

theorem not_simple_four : ¬ IsSimpleGroup (Model 4) := by
  intro hs
  let := hs
  have hn := alternatingGroup.normal_kleinFour (α := Fin 4) (by simp)
  have hc := alternatingGroup.kleinFour_card_of_card_eq_four (α := Fin 4) (by simp)
  rcases hn.eq_bot_or_eq_top with h | h
  · simp [h] at hc
  · have h4 : Nat.card (Model 4) = 12 := by
      rw [card_factorial _ (by decide)]
      norm_num [Nat.factorial]
    have hc' : Nat.card (Model 4) = 4 := by simpa only [h, Subgroup.card_top] using hc
    omega

theorem not_simple_small (n : ℕ) (hn : n ≤ 2) : ¬ IsSimpleGroup (Model n) := by
  intro hs
  have hc : Nat.card (Model n) = 1 := by simp [Model, trivial_small n hn]
  have : Nontrivial (Model n) := hs.toNontrivial
  have := Fintype.one_lt_card (α := Model n)
  rw [Nat.card_eq_fintype_card] at hc
  omega

theorem isSimpleGroup_iff (n : ℕ) : IsSimpleGroup (Model n) ↔ n = 3 ∨ 5 ≤ n := by
  constructor
  · intro h
    by_cases h5 : 5 ≤ n
    · exact Or.inr h5
    by_cases h3 : n = 3
    · exact Or.inl h3
    by_cases h4 : n = 4
    · subst n; exact False.elim (not_simple_four h)
    exact False.elim (not_simple_small n (by omega) h)
  · rintro (rfl | h)
    · exact simple_three
    · exact isSimpleGroup n h

theorem nonabelian_simple_iff (n : ℕ) :
    (IsSimpleGroup (Model n) ∧ ∃ a b : Model n, a * b ≠ b * a) ↔ 5 ≤ n := by
  constructor
  · rintro ⟨hs, a, b, hab⟩
    rcases (isSimpleGroup_iff n).mp hs with rfl | h
    · have hc := alternatingGroup.isMulCommutative_of_card_le_three (α := Fin 3) (by simp)
      exact False.elim (hab (hc.is_comm.comm a b))
    · exact h
  · intro h
    exact ⟨isSimpleGroup n h, exists_mul_ne_mul n (by omega)⟩

theorem faithful (n : ℕ) : FaithfulSMul (Model n) (Fin n) := inferInstance

theorem action_apply (n : ℕ) (g : Model n) (x : Fin n) : g • x = g.val x := rfl

theorem generation (n : ℕ) :
    Subgroup.closure {g : Equiv.Perm (Fin n) | g.IsThreeCycle} = alternatingGroup (Fin n) :=
  Equiv.Perm.closure_three_cycles_eq_alternating

noncomputable def relabel {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) : alternatingGroup α ≃* alternatingGroup β :=
  Equiv.altCongrHom e

theorem relabel_apply {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (g : alternatingGroup α) (x : β) :
    (relabel e g).val x = e (g.val (e.symm x)) := rfl

end Atlas.Families.Alternating
