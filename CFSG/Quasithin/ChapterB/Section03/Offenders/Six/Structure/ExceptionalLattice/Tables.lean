module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Defs
public import CFSG.Quasithin.ChapterB.Section03.Offenders.FixedTests
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Representatives
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Structure.Basic
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Structure.Reduction
import Mathlib.Tactic.FinCases

/-!
# The exceptional order-eight subgroup lattice

The certified word coordinates `1,a,b,ab,c,ac,bc,abc` identify subgroups with
multiplicatively closed subsets of eight indices. Exhaustion of these subsets
proves that the seven lines, seven planes, and whole group listed here are all
the nontrivial subgroups. The table rows are distinct, with their exact orders,
and the planes are connected to their two explicit generators.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, Proposition B.3.2 and Lemma B.3.4, printed pp. 83–85.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.Offenders.Six
open Representation.BinaryOffender

/-- The zero subgroup, seven lines, seven planes, and the whole exceptional group,
in coordinates `1,a,b,ab,c,ac,bc,abc`. -/
def exceptionalIndices (r : Fin 16) : Finset (Fin 8) :=
  ![{0}, {0,1}, {0,2}, {0,3}, {0,4}, {0,5}, {0,6}, {0,7},
    {0,1,2,3}, {0,1,4,5}, {0,2,4,6}, {0,3,4,7},
    {0,1,6,7}, {0,2,5,7}, {0,3,5,6}, Finset.univ] r

private def exMul (i j : Fin 8) : Fin 8 :=
  ![![0,1,2,3,4,5,6,7], ![1,0,3,2,5,4,7,6],
    ![2,3,0,1,6,7,4,5], ![3,2,1,0,7,6,5,4],
    ![4,5,6,7,0,1,2,3], ![5,4,7,6,1,0,3,2],
    ![6,7,4,5,2,3,0,1], ![7,6,5,4,3,2,1,0]] i j

private theorem exMul_spec (i j : Fin 8) :
    exceptionalWords (exMul i j) = exceptionalWords i * exceptionalWords j := by
  revert i j; decide

/-- The subgroup associated to each row of the explicit exceptional lattice. -/
def exceptionalSubgroup (r : Fin 16) : Subgroup Perm where
  carrier := {g | ∃ i ∈ exceptionalIndices r, exceptionalWords i = g}
  one_mem' := ⟨0, by revert r; decide, rfl⟩
  mul_mem' := by
    rintro x y ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
    exact ⟨exMul i j, (by decide : ∀ r i j, i ∈ exceptionalIndices r →
      j ∈ exceptionalIndices r → exMul i j ∈ exceptionalIndices r) r i j hi hj,
      exMul_spec i j⟩
  inv_mem' := by
    rintro x ⟨i, hi, rfl⟩
    exact ⟨i, hi, (by decide : ∀ i, exceptionalWords i = (exceptionalWords i)⁻¹) i⟩

theorem mem_exceptionalSubgroup_iff (r : Fin 16) (g : Perm) :
    g ∈ exceptionalSubgroup r ↔ ∃ i ∈ exceptionalIndices r, exceptionalWords i = g := Iff.rfl

theorem exceptionalSubgroup_le (r : Fin 16) :
    exceptionalSubgroup r ≤ exceptional 6 (by decide) := by
  rintro g ⟨i, _, rfl⟩
  exact (mem_exceptional_iff _).2 ⟨i, rfl⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem index_classification (s : Finset (Fin 8))
    (h0 : 0 ∈ s) (hm : ∀ i ∈ s, ∀ j ∈ s, exMul i j ∈ s) :
    ∃ r, s = exceptionalIndices r := by
  revert s
  decide

theorem subgroup_le_exceptional_iff (A : Subgroup Perm) :
    A ≤ exceptional 6 (by decide) ↔ ∃ r, A = exceptionalSubgroup r := by
  classical
  refine ⟨fun hA => ?_, ?_⟩
  · let s := Finset.univ.filter (fun i => exceptionalWords i ∈ A)
    have h0 : 0 ∈ s := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, A.one_mem⟩
    have hm : ∀ i ∈ s, ∀ j ∈ s, exMul i j ∈ s := by
      intro i hi j hj
      simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and, exMul_spec] using
        A.mul_mem (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
    obtain ⟨r, hr⟩ := index_classification s h0 hm
    refine ⟨r, ?_⟩
    ext g
    constructor
    · intro hg
      obtain ⟨i, rfl⟩ := (mem_exceptional_iff _).1 (hA hg)
      exact ⟨i, hr ▸ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩), rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact (Finset.mem_filter.mp (hr ▸ hi : i ∈ s)).2
  · rintro ⟨r, rfl⟩
    exact exceptionalSubgroup_le r


private theorem exceptionalSubgroup_eq_table {k : ℕ} (r : Fin 16)
    (B : Subgroup Perm) (f : Fin k → Perm)
    (hB : ∀ g, g ∈ B ↔ ∃ j, f j = g)
    (hf : ∀ i ∈ exceptionalIndices r, ∃ j, f j = exceptionalWords i)
    (hb : ∀ j, ∃ i ∈ exceptionalIndices r, exceptionalWords i = f j) :
    exceptionalSubgroup r = B := by
  ext g
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact (hB _).2 (hf i hi)
  · intro hg
    obtain ⟨j, rfl⟩ := (hB _).1 hg
    exact hb j

@[simp] theorem exceptionalSubgroup_zero : exceptionalSubgroup 0 = ⊥ := by
  ext g
  simp [mem_exceptionalSubgroup_iff, exceptionalIndices, exceptionalWords, cubeWords, eq_comm]

@[simp] theorem exceptionalSubgroup_double : exceptionalSubgroup 1 = double := by
  exact exceptionalSubgroup_eq_table 1 _ (lineWords 1) mem_double_iff (by decide) (by decide)

@[simp] theorem exceptionalSubgroup_last : exceptionalSubgroup 4 = last := by
  exact exceptionalSubgroup_eq_table 4 _ (lineWords 0) mem_last_iff (by decide) (by decide)

@[simp] theorem exceptionalSubgroup_triple : exceptionalSubgroup 5 = triple := by
  exact exceptionalSubgroup_eq_table 5 _ (lineWords 2) mem_triple_iff (by decide) (by decide)

@[simp] theorem exceptionalSubgroup_klein : exceptionalSubgroup 8 = klein := by
  exact exceptionalSubgroup_eq_table 8 _ (planeWords 1) mem_klein_iff (by decide) (by decide)

@[simp] theorem exceptionalSubgroup_plus : exceptionalSubgroup 9 = plus := by
  exact exceptionalSubgroup_eq_table 9 _ (planeWords 0) mem_plus_iff (by decide) (by decide)

@[simp] theorem exceptionalSubgroup_twisted : exceptionalSubgroup 12 = twisted := by
  exact exceptionalSubgroup_eq_table 12 _ (planeWords 2) mem_twisted_iff (by decide) (by decide)

@[simp] theorem exceptionalSubgroup_exceptional : exceptionalSubgroup 15 = exceptional 6 (by decide) := by
  exact exceptionalSubgroup_eq_table 15 _ (exceptionalWords) mem_exceptional_iff (by decide) (by decide)


theorem exceptionalSubgroup_line (i : Fin 7) :
    exceptionalSubgroup ⟨i.val + 1, Nat.lt_of_lt_of_le (Nat.add_lt_add_right i.isLt 1) (of_decide_eq_true rfl)⟩ =
      Subgroup.closure {exceptionalWords ⟨i.val + 1, Nat.lt_of_lt_of_le (Nat.add_lt_add_right i.isLt 1) (of_decide_eq_true rfl)⟩} := by
  let j : Fin 8 := ⟨i.val + 1, Nat.lt_of_lt_of_le (Nat.add_lt_add_right i.isLt 1) (of_decide_eq_true rfl)⟩
  apply le_antisymm
  · rintro g ⟨k, hk, rfl⟩
    have hk' : k = 0 ∨ k = j :=
      (by decide : ∀ i : Fin 7, ∀ k ∈ exceptionalIndices ⟨i.val + 1, Nat.lt_of_lt_of_le (Nat.add_lt_add_right i.isLt 1) (of_decide_eq_true rfl)⟩,
        k = 0 ∨ k = (⟨i.val + 1, Nat.lt_of_lt_of_le (Nat.add_lt_add_right i.isLt 1) (of_decide_eq_true rfl)⟩ : Fin 8)) i k hk
    rcases hk' with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure rfl
  · apply (Subgroup.closure_le _).2
    rintro g rfl
    exact ⟨j, (by decide : ∀ i : Fin 7,
      (⟨i.val + 1, Nat.lt_of_lt_of_le (Nat.add_lt_add_right i.isLt 1) (of_decide_eq_true rfl)⟩ : Fin 8) ∈ exceptionalIndices ⟨i.val + 1, Nat.lt_of_lt_of_le (Nat.add_lt_add_right i.isLt 1) (of_decide_eq_true rfl)⟩) i, rfl⟩

/-- Generating pairs for the seven planes, in lattice-table order. -/
def exceptionalPlaneIndices (r : Fin 7) : Fin 8 × Fin 8 :=
  ![(1,2),(1,4),(2,4),(3,4),(1,6),(2,5),(3,5)] r

theorem exceptionalSubgroup_plane (r : Fin 7) :
    exceptionalSubgroup ⟨r.val + 8, Nat.lt_of_lt_of_le (Nat.add_lt_add_right r.isLt 8) (of_decide_eq_true rfl)⟩ =
      Subgroup.closure {exceptionalWords (exceptionalPlaneIndices r).1,
        exceptionalWords (exceptionalPlaneIndices r).2} := by
  let x := exceptionalWords (exceptionalPlaneIndices r).1
  let y := exceptionalWords (exceptionalPlaneIndices r).2
  have hx : x ∈ Subgroup.closure {x,y} := Subgroup.subset_closure (Or.inl rfl)
  have hy : y ∈ Subgroup.closure {x,y} := Subgroup.subset_closure (Or.inr rfl)
  apply le_antisymm
  · rintro g ⟨i, hi, rfl⟩
    have ht : exceptionalWords i = 1 ∨ exceptionalWords i = x ∨
        exceptionalWords i = y ∨ exceptionalWords i = x*y :=
      (by decide : ∀ r : Fin 7, ∀ i ∈ exceptionalIndices ⟨r.val + 8, Nat.lt_of_lt_of_le (Nat.add_lt_add_right r.isLt 8) (of_decide_eq_true rfl)⟩,
        exceptionalWords i = 1 ∨
        exceptionalWords i = exceptionalWords (exceptionalPlaneIndices r).1 ∨
        exceptionalWords i = exceptionalWords (exceptionalPlaneIndices r).2 ∨
        exceptionalWords i = exceptionalWords (exceptionalPlaneIndices r).1 *
          exceptionalWords (exceptionalPlaneIndices r).2) r i hi
    rcases ht with h | h | h | h <;> rw [h]
    · exact Subgroup.one_mem _
    · exact hx
    · exact hy
    · exact Subgroup.mul_mem _ hx hy
  · apply (Subgroup.closure_le _).2
    rintro g (rfl | hg)
    · exact ⟨_, (by decide : ∀ r : Fin 7,
        (exceptionalPlaneIndices r).1 ∈ exceptionalIndices ⟨r.val + 8, Nat.lt_of_lt_of_le (Nat.add_lt_add_right r.isLt 8) (of_decide_eq_true rfl)⟩) r, rfl⟩
    · rw [Set.mem_singleton_iff] at hg
      subst g
      exact ⟨_, (by decide : ∀ r : Fin 7,
        (exceptionalPlaneIndices r).2 ∈ exceptionalIndices ⟨r.val + 8, Nat.lt_of_lt_of_le (Nat.add_lt_add_right r.isLt 8) (of_decide_eq_true rfl)⟩) r, rfl⟩

/-- The mixed plane generated by `b` and `c`. -/
def mixedSecond : Subgroup Perm :=
  Subgroup.closure {kleinSecond 6 (by decide), pairSwap 6 2}

/-- The mixed plane generated by `ab` and `c`. -/
def mixedThird : Subgroup Perm :=
  Subgroup.closure {kleinFirst 6 (by decide) * kleinSecond 6 (by decide), pairSwap 6 2}

@[simp] theorem exceptionalSubgroup_mixedSecond : exceptionalSubgroup 10 = mixedSecond :=
  exceptionalSubgroup_plane 2

@[simp] theorem exceptionalSubgroup_mixedThird : exceptionalSubgroup 11 = mixedThird :=
  exceptionalSubgroup_plane 3

private theorem exceptionalWords_injective : Function.Injective exceptionalWords := by decide

theorem exceptionalWord_mem_iff (r : Fin 16) (i : Fin 8) :
    exceptionalWords i ∈ exceptionalSubgroup r ↔ i ∈ exceptionalIndices r := by
  constructor
  · rintro ⟨j, hj, hji⟩
    exact exceptionalWords_injective hji ▸ hj
  · intro hi
    exact ⟨i, hi, rfl⟩

theorem exceptionalSubgroup_injective : Function.Injective exceptionalSubgroup := by
  intro r s h
  have hi : exceptionalIndices r = exceptionalIndices s := by
    ext i
    rw [← exceptionalWord_mem_iff, ← exceptionalWord_mem_iff, h]
  exact (by decide : Function.Injective exceptionalIndices) hi

theorem card_exceptionalSubgroup (r : Fin 16) :
    Nat.card (exceptionalSubgroup r) = (exceptionalIndices r).card := by
  let f : {i // i ∈ exceptionalIndices r} → exceptionalSubgroup r :=
    fun i => ⟨exceptionalWords i, (exceptionalWord_mem_iff r i).2 i.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      exact Subtype.ext (exceptionalWords_injective (congrArg Subtype.val h))
    · rintro ⟨g, i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  simp

/-- The fifteen distinct nontrivial subgroups: rows 1–7 are lines, rows 8–14
are planes, and row 15 is the whole group. -/
theorem nontrivial_subgroup_le_exceptional_iff (A : Subgroup Perm) :
    (A ≤ exceptional 6 (by decide) ∧ A ≠ ⊥) ↔
      ∃ r : Fin 15, A = exceptionalSubgroup ⟨r.val + 1, by omega⟩ := by
  constructor
  · rintro ⟨hA, hne⟩
    obtain ⟨r, rfl⟩ := (subgroup_le_exceptional_iff A).1 hA
    have hr : r ≠ 0 := by rintro rfl; exact hne exceptionalSubgroup_zero
    refine ⟨⟨r.val - 1, by omega⟩, ?_⟩
    congr 1
    apply Fin.ext
    change r.val = r.val - 1 + 1
    have := r.isLt
    omega
  · rintro ⟨r, rfl⟩
    refine ⟨exceptionalSubgroup_le _, ?_⟩
    intro h
    rw [← exceptionalSubgroup_zero] at h
    have hi := congrArg Fin.val (exceptionalSubgroup_injective h)
    simp only [Fin.val_zero] at hi
    omega

end CFSG.Quasithin.ChapterB.Offenders.Six
