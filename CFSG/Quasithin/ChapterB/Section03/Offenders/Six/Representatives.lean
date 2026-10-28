module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Defs
public import CFSG.Quasithin.ChapterB.Section03.Offenders.FixedTests
import Mathlib.Tactic.FinCases

/-!
# Concrete degree-six offender representatives

These are the actual permutation subgroups used in B.3.2 and B.3.4. Small
multiplication tables certify their orders and elementary abelian structure;
the tables are connected to the defining subgroup closures. In particular,
no exhaustive subgroup list is assumed here.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, printed pp. 83–85.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterB.Offenders.Six

open Representation.BinaryOffender

abbrev Perm := Equiv.Perm (Fin 6)

/-- The final transposition subgroup, denoted `A₁⁰` in B.3.4. -/
def last : Subgroup Perm := Subgroup.closure {pairSwap 6 2}

/-- A copy of `A₂` containing the final transposition. -/
def tailTwo : Subgroup Perm := Subgroup.closure {pairSwap 6 1, pairSwap 6 2}

/-- The mixed hyperplane of `D`, denoted `A⁺` in B.3.4. -/
def plus : Subgroup Perm := Subgroup.closure {kleinFirst 6 (by decide), pairSwap 6 2}

/-- A double-transposition cyclic subgroup, used to exclude nonoffenders. -/
def double : Subgroup Perm := Subgroup.closure {kleinFirst 6 (by decide)}

/-- A triple-transposition cyclic subgroup, used to exclude nonoffenders. -/
def triple : Subgroup Perm :=
  Subgroup.closure {kleinFirst 6 (by decide) * pairSwap 6 2}

/-- The regular Klein four group on the first four coordinates. -/
def klein : Subgroup Perm :=
  Subgroup.closure {kleinFirst 6 (by decide), kleinSecond 6 (by decide)}

/-- A Klein four group with orbits of lengths four and two. -/
def twisted : Subgroup Perm :=
  Subgroup.closure {kleinFirst 6 (by decide), kleinSecond 6 (by decide) * pairSwap 6 2}

/-- The canonical Sylow candidate. Its Sylow property is proved separately. -/
def sylowCarrier : Subgroup Perm := D 6 ⊔ exceptional 6 (by decide)

/-- Ordered products of three independent commuting involutions. -/
def cubeWords (a b c : Perm) : Fin 8 → Perm := ![1, a, b, a*b, c, a*c, b*c, a*b*c]

/-- An enumeration of `D`. -/
def dWords : Fin 8 → Perm := cubeWords (pairSwap 6 0) (pairSwap 6 1) (pairSwap 6 2)

/-- An enumeration of the exceptional rank-three group. -/
def exceptionalWords : Fin 8 → Perm :=
  cubeWords (kleinFirst 6 (by decide)) (kleinSecond 6 (by decide)) (pairSwap 6 2)

/-- The first `2^m` entries enumerate `A_m`. -/
def initialWords (m : Fin 4) : Fin (2 ^ m.val) → Perm := fun i =>
  dWords ⟨i.val, lt_of_lt_of_le i.isLt (by have := m.isLt; interval_cases m.val <;> decide)⟩

private def tableSubgroup {k : ℕ} (f : Fin k → Perm)
    (hone : ∃ i, f i = 1)
    (hmul : ∀ i j, ∃ l, f i * f j = f l)
    (hinv : ∀ i, ∃ j, (f i)⁻¹ = f j) : Subgroup Perm where
  carrier := Set.range f
  one_mem' := hone
  mul_mem' := by
    rintro a b ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨l, hl⟩ := hmul i j
    exact ⟨l, hl.symm⟩
  inv_mem' := by
    rintro a ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hinv i
    exact ⟨j, hj.symm⟩

private theorem card_tableSubgroup {k : ℕ} (f : Fin k → Perm)
    (hone hmul hinv) (hf : Function.Injective f) :
    Nat.card (tableSubgroup f hone hmul hinv) = k := by
  exact (Nat.card_congr (Equiv.ofInjective f hf)).symm.trans (by simp)

private theorem elementary_tableSubgroup {k : ℕ} (f : Fin k → Perm)
    (hone hmul hinv) (hcomm : ∀ i j, f i * f j = f j * f i)
    (hsq : ∀ i, f i ^ 2 = 1) :
    IsElementaryAbelian 2 (tableSubgroup f hone hmul hinv) := by
  refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
  · rintro ⟨a, i, rfl⟩ ⟨b, j, rfl⟩
    exact Subtype.ext (hcomm i j)
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    rintro ⟨a, i, rfl⟩
    exact Subtype.ext (hsq i)

private def initialTable (m : Fin 4) : Subgroup Perm := tableSubgroup (initialWords m)
  (by fin_cases m <;> exact ⟨0, rfl⟩)
  (by revert m; decide)
  (by revert m; decide)

private theorem initialTable_eq (m : Fin 4) :
    initialTable m = disjointTranspositions 6 m.val := by
  apply le_antisymm
  · rintro g ⟨i, rfl⟩
    have h0 (h : 0 < m.val) := pairSwap_mem (n := 6) (m := m.val) 0 h
    have h1 (h : 1 < m.val) := pairSwap_mem (n := 6) (m := m.val) 1 h
    have h2 (h : 2 < m.val) := pairSwap_mem (n := 6) (m := m.val) 2 h
    fin_cases m <;> fin_cases i <;>
      dsimp only [initialWords, dWords, cubeWords] <;>
      first | exact Subgroup.one_mem _ | exact h0 (by decide) |
        exact h1 (by decide) | exact h2 (by decide) |
        exact Subgroup.mul_mem _ (h0 (by decide)) (h1 (by decide)) |
        exact Subgroup.mul_mem _ (h0 (by decide)) (h2 (by decide)) |
        exact Subgroup.mul_mem _ (h1 (by decide)) (h2 (by decide)) |
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (h0 (by decide)) (h1 (by decide)))
          (h2 (by decide))
  · apply (Subgroup.closure_le _).2
    rintro g ⟨i, hi, rfl⟩
    fin_cases m <;> fin_cases i <;> dsimp at hi <;> try omega
    all_goals first | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨4, rfl⟩

/-- The full table of each initial disjoint-transposition subgroup. -/
theorem mem_disjointTranspositions_iff (m : Fin 4) (g : Perm) :
    g ∈ disjointTranspositions 6 m.val ↔ ∃ i, initialWords m i = g := by
  rw [← initialTable_eq]
  rfl

/-- The exact orders of `A_m`, including the trivial initial segment. -/
theorem card_disjointTranspositions (m : Fin 4) :
    Nat.card (disjointTranspositions 6 m.val) = 2 ^ m.val := by
  rw [← initialTable_eq]
  apply card_tableSubgroup
  revert m
  decide

/-- The disjoint-transposition rank calculation in B.3.2(1). -/
theorem rank_disjointTranspositions (m : Fin 4) :
    rank (disjointTranspositions 6 m.val) = m.val := by
  rw [rank, card_disjointTranspositions, Nat.log_pow (by decide : 1 < 2)]

theorem elementary_disjointTranspositions (m : Fin 4) :
    IsElementaryAbelian 2 (disjointTranspositions 6 m.val) := by
  rw [← initialTable_eq]
  apply elementary_tableSubgroup
  · revert m; decide
  · revert m; decide

theorem isElementaryTwo_disjointTranspositions (m : Fin 4) (hm : 0 < m.val) :
    IsElementaryTwo (disjointTranspositions 6 m.val) := by
  refine ⟨?_, elementary_disjointTranspositions m⟩
  intro h
  have hc := card_disjointTranspositions m
  rw [h, Subgroup.card_bot] at hc
  have hr := rank_disjointTranspositions m
  rw [h, Representation.BinaryOffender.rank_bot] at hr
  omega

private def exceptionalTable : Subgroup Perm := tableSubgroup exceptionalWords
  ⟨0, rfl⟩ (by decide) (by decide)

private theorem exceptionalTable_eq : exceptionalTable = exceptional 6 (by decide) := by
  have h0 : kleinFirst 6 (by decide) ∈ exceptional 6 (by decide) :=
    Subgroup.subset_closure (Or.inl (Or.inl rfl))
  have h1 : kleinSecond 6 (by decide) ∈ exceptional 6 (by decide) :=
    Subgroup.subset_closure (Or.inl (Or.inr (Set.mem_singleton _)))
  have h2 : pairSwap 6 2 ∈ exceptional 6 (by decide) :=
    Subgroup.subset_closure (Or.inr ⟨2, le_rfl, rfl⟩)
  apply le_antisymm
  · rintro g ⟨i, rfl⟩
    fin_cases i <;> dsimp only [exceptionalWords, cubeWords]
    · exact Subgroup.one_mem _
    · exact h0
    · exact h1
    · exact Subgroup.mul_mem _ h0 h1
    · exact h2
    · exact Subgroup.mul_mem _ h0 h2
    · exact Subgroup.mul_mem _ h1 h2
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h0 h1) h2
  · apply (Subgroup.closure_le _).2
    rintro g (hg | ⟨i, hi, rfl⟩)
    · rcases hg with rfl | hg
      · exact ⟨1, rfl⟩
      · rw [Set.mem_singleton_iff] at hg
        subst g
        exact ⟨2, rfl⟩
    · fin_cases i <;> dsimp at hi <;> first | omega | exact ⟨4, rfl⟩

theorem mem_exceptional_iff (g : Perm) :
    g ∈ exceptional 6 (by decide) ↔ ∃ i, exceptionalWords i = g := by
  rw [← exceptionalTable_eq]
  rfl

theorem card_exceptional : Nat.card (exceptional 6 (by decide)) = 8 := by
  rw [← exceptionalTable_eq]
  exact card_tableSubgroup _ _ _ _ (by decide)

theorem rank_exceptional : rank (exceptional 6 (by decide)) = 3 := by
  rw [rank, card_exceptional]
  decide

theorem isElementaryTwo_exceptional : IsElementaryTwo (exceptional 6 (by decide)) := by
  refine ⟨?_, ?_⟩
  · intro h
    have hc := card_exceptional
    rw [h, Subgroup.card_bot] at hc
    contradiction
  · rw [← exceptionalTable_eq]
    exact elementary_tableSubgroup _ _ _ _ (by decide) (by decide)

theorem last_le_tailTwo : last ≤ tailTwo := by
  apply Subgroup.closure_mono
  intro g hg
  exact Or.inr hg

theorem last_le_plus : last ≤ plus := by
  apply Subgroup.closure_mono
  intro g hg
  exact Or.inr hg

private theorem kleinFirst_mem_D : kleinFirst 6 (by decide) ∈ D 6 := by
  exact Subgroup.mul_mem _ (pairSwap_mem (n := 6) 0 (by decide))
    (pairSwap_mem (n := 6) 1 (by decide))

theorem plus_le_D : plus ≤ D 6 := by
  apply (Subgroup.closure_le _).2
  rintro g (rfl | hg)
  · exact kleinFirst_mem_D
  · rw [Set.mem_singleton_iff] at hg
    subst g
    exact pairSwap_mem (n := 6) 2 (by decide)

theorem tailTwo_le_D : tailTwo ≤ D 6 := by
  apply (Subgroup.closure_le _).2
  rintro g (rfl | hg)
  · exact pairSwap_mem (n := 6) 1 (by decide)
  · rw [Set.mem_singleton_iff] at hg
    subst g
    exact pairSwap_mem (n := 6) 2 (by decide)

theorem plus_le_exceptional : plus ≤ exceptional 6 (by decide) := by
  apply (Subgroup.closure_le _).2
  rintro g (rfl | hg)
  · exact Subgroup.subset_closure (Or.inl (Or.inl rfl))
  · rw [Set.mem_singleton_iff] at hg
    subst g
    exact Subgroup.subset_closure (Or.inr ⟨2, le_rfl, rfl⟩)

theorem last_le_exceptional : last ≤ exceptional 6 (by decide) :=
  last_le_plus.trans plus_le_exceptional

theorem klein_le_exceptional : klein ≤ exceptional 6 (by decide) :=
  Subgroup.closure_mono Set.subset_union_left

theorem twisted_le_exceptional : twisted ≤ exceptional 6 (by decide) := by
  apply (Subgroup.closure_le _).2
  rintro g (rfl | hg)
  · exact Subgroup.subset_closure (Or.inl (Or.inl rfl))
  · rw [Set.mem_singleton_iff] at hg
    subst g
    exact Subgroup.mul_mem _
      (Subgroup.subset_closure (Or.inl (Or.inr (Set.mem_singleton _))))
      (Subgroup.subset_closure (Or.inr ⟨2, le_rfl, rfl⟩))

theorem D_le_sylowCarrier : D 6 ≤ sylowCarrier := le_sup_left

theorem exceptional_le_sylowCarrier : exceptional 6 (by decide) ≤ sylowCarrier := le_sup_right

end CFSG.Quasithin.ChapterB.Offenders.Six
