module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Defs
public import CFSG.Quasithin.ChapterB.Section03.Offenders.FixedTests
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Representatives
public import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic.FinCases
/-!
# Orders and Sylow reduction for the degree-six representatives

Finite element tables certify the cyclic and rank-two representatives and the
order-sixteen Sylow candidate. Every involution of the latter lies in `D` or
in the exceptional group, so every elementary abelian subgroup lies in one of
these two order-eight groups. These certificates prepare the exhaustive
subgroup and hyperplane classifications.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, Proposition B.3.2 and Lemma B.3.4, printed pp. 83–85.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.Offenders.Six
open Representation.BinaryOffender

private def wordSubgroup {k : ℕ} (f : Fin k → Perm)
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

private theorem card_wordSubgroup {k : ℕ} (f : Fin k → Perm)
    (hone hmul hinv) (hf : Function.Injective f) :
    Nat.card (wordSubgroup f hone hmul hinv) = k :=
  (Nat.card_congr (Equiv.ofInjective f hf)).symm.trans (by simp)

private theorem elementary_wordSubgroup {k : ℕ} (f : Fin k → Perm)
    (hone hmul hinv) (hcomm : ∀ i j, f i * f j = f j * f i)
    (hsq : ∀ i, f i ^ 2 = 1) :
    IsElementaryAbelian 2 (wordSubgroup f hone hmul hinv) := by
  refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
  · rintro ⟨a, i, rfl⟩ ⟨b, j, rfl⟩
    exact Subtype.ext (hcomm i j)
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    rintro ⟨a, i, rfl⟩
    exact Subtype.ext (hsq i)

/-- Generators for the three cyclic representatives. -/
def lineGenerator (r : Fin 3) : Perm :=
  ![pairSwap 6 2, kleinFirst 6 (by decide),
    kleinFirst 6 (by decide) * pairSwap 6 2] r

/-- Tables for `last`, `double`, and `triple`, in that order. -/
def lineWords (r : Fin 3) : Fin 2 → Perm := ![1, lineGenerator r]

private def lineTable (r : Fin 3) : Subgroup Perm := wordSubgroup (lineWords r)
  ⟨0, rfl⟩ (by revert r; decide) (by revert r; decide)

private theorem lineTable_eq (r : Fin 3) :
    lineTable r = Subgroup.closure {lineGenerator r} := by
  apply le_antisymm
  · rintro g ⟨i, rfl⟩
    fin_cases i
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure rfl
  · apply (Subgroup.closure_le _).2
    rintro g rfl
    exact ⟨1, rfl⟩

private theorem card_line (r : Fin 3) :
    Nat.card (Subgroup.closure {lineGenerator r}) = 2 := by
  rw [← lineTable_eq]
  apply card_wordSubgroup
  revert r
  decide

private theorem elementary_line (r : Fin 3) :
    IsElementaryTwo (Subgroup.closure {lineGenerator r}) := by
  refine ⟨?_, ?_⟩
  · intro h
    have hc := card_line r
    rw [h, Subgroup.card_bot] at hc
    contradiction
  · rw [← lineTable_eq]
    apply elementary_wordSubgroup
    · revert r; decide
    · revert r; decide

/-- Generating pairs for the five rank-two representatives. -/
def planeGenerators (r : Fin 5) : Perm × Perm :=
  ![(kleinFirst 6 (by decide), pairSwap 6 2),
    (kleinFirst 6 (by decide), kleinSecond 6 (by decide)),
    (kleinFirst 6 (by decide), kleinSecond 6 (by decide) * pairSwap 6 2),
    (pairSwap 6 1, pairSwap 6 2),
    (kleinFirst 6 (by decide), pairSwap 6 0 * pairSwap 6 2)] r

/-- Tables for `plus`, `klein`, `twisted`, `tailTwo`, and `evenPart 6`. -/
def planeWords (r : Fin 5) : Fin 4 → Perm :=
  ![1, (planeGenerators r).1, (planeGenerators r).2,
    (planeGenerators r).1 * (planeGenerators r).2]

private def planeTable (r : Fin 5) : Subgroup Perm := wordSubgroup (planeWords r)
  ⟨0, rfl⟩ (by revert r; decide) (by revert r; decide)

private theorem planeTable_eq (r : Fin 5) :
    planeTable r = Subgroup.closure {(planeGenerators r).1, (planeGenerators r).2} := by
  apply le_antisymm
  · rintro g ⟨i, rfl⟩
    have h0 : (planeGenerators r).1 ∈
        Subgroup.closure {(planeGenerators r).1, (planeGenerators r).2} :=
      Subgroup.subset_closure (Or.inl rfl)
    have h1 : (planeGenerators r).2 ∈
        Subgroup.closure {(planeGenerators r).1, (planeGenerators r).2} :=
      Subgroup.subset_closure (Or.inr rfl)
    fin_cases i
    · exact Subgroup.one_mem _
    · exact h0
    · exact h1
    · exact Subgroup.mul_mem _ h0 h1
  · apply (Subgroup.closure_le _).2
    rintro g (rfl | hg)
    · exact ⟨1, rfl⟩
    · rw [Set.mem_singleton_iff] at hg
      subst g
      exact ⟨2, rfl⟩

private theorem card_plane (r : Fin 5) : Nat.card (planeTable r) = 4 := by
  apply card_wordSubgroup
  revert r
  decide

private theorem elementary_plane (r : Fin 5) : IsElementaryTwo (planeTable r) := by
  refine ⟨?_, ?_⟩
  · intro h
    have hc := card_plane r
    rw [h, Subgroup.card_bot] at hc
    contradiction
  · apply elementary_wordSubgroup
    · revert r; decide
    · revert r; decide

private theorem evenPart_table : evenPart 6 = planeTable 4 := by
  apply le_antisymm
  · intro g hg
    obtain ⟨i, rfl⟩ := (mem_disjointTranspositions_iff (3 : Fin 4) g).1 hg.1
    have he : (initialWords 3 i) ∈ alternatingGroup (Fin 6) := hg.2
    fin_cases i
    · exact ⟨0, rfl⟩
    · exact False.elim ((by simp [Equiv.Perm.mem_alternatingGroup, initialWords, dWords, cubeWords, pairSwap] : initialWords 3 1 ∉ alternatingGroup (Fin 6)) he)
    · exact False.elim ((by simp [Equiv.Perm.mem_alternatingGroup, initialWords, dWords, cubeWords, pairSwap] : initialWords 3 2 ∉ alternatingGroup (Fin 6)) he)
    · exact ⟨1, rfl⟩
    · exact False.elim ((by simp [Equiv.Perm.mem_alternatingGroup, initialWords, dWords, cubeWords, pairSwap] : initialWords 3 4 ∉ alternatingGroup (Fin 6)) he)
    · exact ⟨2, rfl⟩
    · exact ⟨3, by decide⟩
    · exact False.elim ((by simp [Equiv.Perm.mem_alternatingGroup, initialWords, dWords, cubeWords, pairSwap] : initialWords 3 7 ∉ alternatingGroup (Fin 6)) he)
  · rintro g ⟨i, rfl⟩
    refine ⟨?_, ?_⟩
    · apply (mem_disjointTranspositions_iff (3 : Fin 4) _).2
      revert i
      decide
    · fin_cases i <;>
        simp [Equiv.Perm.mem_alternatingGroup, planeWords, planeGenerators, kleinFirst, pairSwap]


/-- The complete element table of `last`. -/
theorem mem_last_iff (g : Perm) :
    g ∈ last ↔ ∃ i, lineWords 0 i = g := by
  change g ∈ Subgroup.closure {lineGenerator 0} ↔ _
  rw [← lineTable_eq]
  rfl

theorem card_last : Nat.card last = 2 := card_line 0

theorem rank_last : rank last = 1 := by
  rw [rank, card_last]
  decide

theorem isElementaryTwo_last : IsElementaryTwo last := elementary_line 0

/-- The complete element table of `double`. -/
theorem mem_double_iff (g : Perm) :
    g ∈ double ↔ ∃ i, lineWords 1 i = g := by
  change g ∈ Subgroup.closure {lineGenerator 1} ↔ _
  rw [← lineTable_eq]
  rfl

theorem card_double : Nat.card double = 2 := card_line 1

theorem rank_double : rank double = 1 := by
  rw [rank, card_double]
  decide

theorem isElementaryTwo_double : IsElementaryTwo double := elementary_line 1

/-- The complete element table of `triple`. -/
theorem mem_triple_iff (g : Perm) :
    g ∈ triple ↔ ∃ i, lineWords 2 i = g := by
  change g ∈ Subgroup.closure {lineGenerator 2} ↔ _
  rw [← lineTable_eq]
  rfl

theorem card_triple : Nat.card triple = 2 := card_line 2

theorem rank_triple : rank triple = 1 := by
  rw [rank, card_triple]
  decide

theorem isElementaryTwo_triple : IsElementaryTwo triple := elementary_line 2

/-- The complete element table of `plus`. -/
theorem mem_plus_iff (g : Perm) :
    g ∈ plus ↔ ∃ i, planeWords 0 i = g := by
  change g ∈ Subgroup.closure {(planeGenerators 0).1, (planeGenerators 0).2} ↔ _
  rw [← planeTable_eq]
  rfl

theorem card_plus : Nat.card plus = 4 := by
  change Nat.card (Subgroup.closure {(planeGenerators 0).1, (planeGenerators 0).2}) = 4
  rw [← planeTable_eq]
  exact card_plane 0

theorem rank_plus : rank plus = 2 := by
  rw [rank, card_plus]
  decide

theorem isElementaryTwo_plus : IsElementaryTwo plus := by
  change IsElementaryTwo (Subgroup.closure {(planeGenerators 0).1, (planeGenerators 0).2})
  rw [← planeTable_eq]
  exact elementary_plane 0

/-- The complete element table of `klein`. -/
theorem mem_klein_iff (g : Perm) :
    g ∈ klein ↔ ∃ i, planeWords 1 i = g := by
  change g ∈ Subgroup.closure {(planeGenerators 1).1, (planeGenerators 1).2} ↔ _
  rw [← planeTable_eq]
  rfl

theorem card_klein : Nat.card klein = 4 := by
  change Nat.card (Subgroup.closure {(planeGenerators 1).1, (planeGenerators 1).2}) = 4
  rw [← planeTable_eq]
  exact card_plane 1

theorem rank_klein : rank klein = 2 := by
  rw [rank, card_klein]
  decide

theorem isElementaryTwo_klein : IsElementaryTwo klein := by
  change IsElementaryTwo (Subgroup.closure {(planeGenerators 1).1, (planeGenerators 1).2})
  rw [← planeTable_eq]
  exact elementary_plane 1

/-- The complete element table of `twisted`. -/
theorem mem_twisted_iff (g : Perm) :
    g ∈ twisted ↔ ∃ i, planeWords 2 i = g := by
  change g ∈ Subgroup.closure {(planeGenerators 2).1, (planeGenerators 2).2} ↔ _
  rw [← planeTable_eq]
  rfl

theorem card_twisted : Nat.card twisted = 4 := by
  change Nat.card (Subgroup.closure {(planeGenerators 2).1, (planeGenerators 2).2}) = 4
  rw [← planeTable_eq]
  exact card_plane 2

theorem rank_twisted : rank twisted = 2 := by
  rw [rank, card_twisted]
  decide

theorem isElementaryTwo_twisted : IsElementaryTwo twisted := by
  change IsElementaryTwo (Subgroup.closure {(planeGenerators 2).1, (planeGenerators 2).2})
  rw [← planeTable_eq]
  exact elementary_plane 2

/-- The complete element table of `tailTwo`. -/
theorem mem_tailTwo_iff (g : Perm) :
    g ∈ tailTwo ↔ ∃ i, planeWords 3 i = g := by
  change g ∈ Subgroup.closure {(planeGenerators 3).1, (planeGenerators 3).2} ↔ _
  rw [← planeTable_eq]
  rfl

theorem card_tailTwo : Nat.card tailTwo = 4 := by
  change Nat.card (Subgroup.closure {(planeGenerators 3).1, (planeGenerators 3).2}) = 4
  rw [← planeTable_eq]
  exact card_plane 3

theorem rank_tailTwo : rank tailTwo = 2 := by
  rw [rank, card_tailTwo]
  decide

theorem isElementaryTwo_tailTwo : IsElementaryTwo tailTwo := by
  change IsElementaryTwo (Subgroup.closure {(planeGenerators 3).1, (planeGenerators 3).2})
  rw [← planeTable_eq]
  exact elementary_plane 3

/-- The complete element table of `evenPart`. -/
theorem mem_evenPart_iff (g : Perm) :
    g ∈ (evenPart 6) ↔ ∃ i, planeWords 4 i = g := by
  rw [evenPart_table]
  rfl

theorem card_evenPart : Nat.card (evenPart 6) = 4 := by
  rw [evenPart_table]
  exact card_plane 4

theorem rank_evenPart : rank (evenPart 6) = 2 := by
  rw [rank, card_evenPart]
  decide

theorem isElementaryTwo_evenPart : IsElementaryTwo (evenPart 6) := by
  rw [evenPart_table]
  exact elementary_plane 4

/-- Sixteen normal forms for the canonical Sylow subgroup. -/
def sylowWords (i : Fin 16) : Perm :=
  if h : i.val < 8 then dWords ⟨i.val, h⟩
  else dWords ⟨i.val - 8, by omega⟩ * kleinSecond 6 (by decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private def sylowTable : Subgroup Perm := wordSubgroup sylowWords
  ⟨0, rfl⟩ (by decide) (by decide)

private theorem dWords_mem_D (i : Fin 8) : dWords i ∈ D 6 :=
  (mem_disjointTranspositions_iff (3 : Fin 4) _).2 ⟨i, rfl⟩

private theorem sylowTable_eq : sylowTable = sylowCarrier := by
  apply le_antisymm
  · rintro g ⟨i, rfl⟩
    unfold sylowWords
    split
    · exact D_le_sylowCarrier (dWords_mem_D _)
    · exact Subgroup.mul_mem _ (D_le_sylowCarrier (dWords_mem_D _))
        (exceptional_le_sylowCarrier
          (Subgroup.subset_closure (Or.inl (Or.inr (Set.mem_singleton _)))))
  · apply sup_le
    · intro g hg
      obtain ⟨i, rfl⟩ := (mem_disjointTranspositions_iff (3 : Fin 4) g).1 hg
      have hi : i.val < 8 := i.isLt
      refine ⟨⟨i.val, by omega⟩, ?_⟩
      simp [sylowWords, hi, initialWords]
    · apply (Subgroup.closure_le _).2
      rintro g (hg | ⟨i, hi, rfl⟩)
      · rcases hg with rfl | hg
        · exact ⟨3, rfl⟩
        · rw [Set.mem_singleton_iff] at hg
          subst g
          exact ⟨8, by simp [sylowWords, dWords, cubeWords]⟩
      · fin_cases i <;> dsimp at hi <;> first | omega | exact ⟨4, rfl⟩

theorem mem_sylowCarrier_iff (g : Perm) :
    g ∈ sylowCarrier ↔ ∃ i, sylowWords i = g := by
  rw [← sylowTable_eq]
  rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem card_sylowCarrier : Nat.card sylowCarrier = 16 := by
  rw [← sylowTable_eq]
  exact card_wordSubgroup _ _ _ _ (by decide)

/-- The canonical candidate is an actual Sylow subgroup of the symmetric group. -/
def sylow : Sylow 2 Perm :=
  (IsPGroup.of_card (show Nat.card sylowCarrier = 2 ^ 4 from card_sylowCarrier)).toSylow (by
    have hc := sylowCarrier.card_mul_index
    rw [card_sylowCarrier, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at hc
    norm_num [Nat.factorial] at hc
    omega)

@[simp] theorem sylow_coe : (sylow : Subgroup Perm) = sylowCarrier := rfl

end CFSG.Quasithin.ChapterB.Offenders.Six
