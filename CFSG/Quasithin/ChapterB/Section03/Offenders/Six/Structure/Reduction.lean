module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Defs
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Conjugacy
public import CFSG.Quasithin.ChapterB.Section03.Offenders.FixedTests
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Representatives
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Structure.Basic
/-!
# Reduction to the two elementary abelian groups of order eight

Sylow conjugacy moves an elementary abelian subgroup into the certified
order-sixteen subgroup. Its elements lie in the union of `D` and the exceptional
group. The subgroup-union lemma therefore places the entire subgroup in one of
these two groups. We also record the conjugacy transport API and the explicit
conjugacies for the final one and two transpositions.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, Proposition B.3.2 and Lemma B.3.4, printed pp. 83–85.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.Offenders
open Representation.BinaryOffender

/-- Symmetry of the chosen orientation of subgroup conjugacy. -/
theorem IsConjugateTo.symm {n : ℕ} {A B : Subgroup (Equiv.Perm (Fin n))}
    (h : IsConjugateTo A B) : IsConjugateTo B A := by
  obtain ⟨g, rfl⟩ := h
  refine ⟨g⁻¹, ?_⟩
  rw [Subgroup.map_map]
  have he : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id _ := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [he, Subgroup.map_id]

/-- Composition of subgroup conjugacies. -/
theorem IsConjugateTo.trans {n : ℕ} {A B C : Subgroup (Equiv.Perm (Fin n))}
    (hAB : IsConjugateTo A B) (hBC : IsConjugateTo B C) : IsConjugateTo A C := by
  obtain ⟨g, rfl⟩ := hAB
  obtain ⟨h, rfl⟩ := hBC
  refine ⟨g * h, ?_⟩
  rw [Subgroup.map_map]
  congr 1

/-- Conjugate subgroups have the same order. -/
theorem IsConjugateTo.card_eq {n : ℕ} {A B : Subgroup (Equiv.Perm (Fin n))}
    (h : IsConjugateTo A B) : Nat.card A = Nat.card B := by
  obtain ⟨g, rfl⟩ := h
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

/-- Containment in the alternating group is invariant under subgroup conjugacy. -/
theorem IsConjugateTo.le_alternating_iff {n : ℕ} {A B : Subgroup (Equiv.Perm (Fin n))}
    (h : IsConjugateTo A B) : A ≤ alternatingGroup (Fin n) ↔
      B ≤ alternatingGroup (Fin n) := by
  have forward {A B : Subgroup (Equiv.Perm (Fin n))}
      (h : IsConjugateTo A B) (hB : B ≤ alternatingGroup (Fin n)) :
      A ≤ alternatingGroup (Fin n) := by
    obtain ⟨g, rfl⟩ := h
    rintro x ⟨b, hb, rfl⟩
    exact Subgroup.Normal.conj_mem inferInstance b (hB hb) g
  exact ⟨forward h.symm, forward h⟩

namespace Six

/-- Every element of order at most two lies in one of the two rank-three groups. -/
theorem involution_mem_D_or_exceptional {g : Perm}
    (hg : g ∈ sylowCarrier) (hsq : g ^ 2 = 1) :
    g ∈ D 6 ∨ g ∈ exceptional 6 (by decide) := by
  obtain ⟨i, rfl⟩ := (mem_sylowCarrier_iff g).1 hg
  have ht : ∀ i : Fin 16, sylowWords i ^ 2 = 1 →
      (∃ j, dWords j = sylowWords i) ∨ (∃ j, exceptionalWords j = sylowWords i) := by
    decide
  rcases ht i hsq with h | h
  · exact Or.inl ((mem_disjointTranspositions_iff (3 : Fin 4) _).2 h)
  · exact Or.inr ((mem_exceptional_iff _).2 h)

/-- Elementary abelian subgroups of the Sylow candidate lie in one of its two
maximal elementary abelian subgroups. -/
theorem elementary_le_D_or_exceptional {A : Subgroup Perm}
    (hA : IsElementaryTwo A) (hAT : A ≤ sylowCarrier) :
    A ≤ D 6 ∨ A ≤ exceptional 6 (by decide) := by
  let _ : IsElementaryAbelian 2 A := hA.2
  apply SubgroupClass.subset_union.mp
  intro a ha
  exact involution_mem_D_or_exceptional (hAT ha)
    (elemPow_eq_one_of_isElementaryAbelian a ha)

/-- Sylow conjugacy moves every elementary abelian subgroup into the canonical
order-sixteen subgroup. -/
theorem exists_conjugate_le_sylowCarrier {A : Subgroup Perm} (hA : IsElementaryTwo A) :
    ∃ B : Subgroup Perm, IsElementaryTwo B ∧ B ≤ sylowCarrier ∧ IsConjugateTo A B := by
  let _ : IsElementaryAbelian 2 A := hA.2
  obtain ⟨Q, hAQ⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Perm Q sylow
  let B := A.map (MulAut.conj g).toMonoidHom
  refine ⟨B, ⟨?_, IsElementaryAbelian.map _⟩, ?_, g⁻¹, ?_⟩
  · intro hB
    apply hA.1
    exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).1 hB
  · rintro x ⟨a, ha, rfl⟩
    change (MulAut.conj g) a ∈ (sylow : Subgroup Perm)
    rw [← hg]
    exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom (hAQ ha)
  · dsimp only [B]
    rw [Subgroup.map_map]
    have he : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id Perm := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [he, Subgroup.map_id]

/-- The global classification reduces to the subgroup lattices of two groups
of order eight. -/
theorem exists_conjugate_le_D_or_exceptional {A : Subgroup Perm} (hA : IsElementaryTwo A) :
    ∃ B : Subgroup Perm, IsElementaryTwo B ∧
      (B ≤ D 6 ∨ B ≤ exceptional 6 (by decide)) ∧ IsConjugateTo A B := by
  obtain ⟨B, hB, hBT, hAB⟩ := exists_conjugate_le_sylowCarrier hA
  exact ⟨B, hB, elementary_le_D_or_exceptional hB hBT, hAB⟩

/-- The final transposition is conjugate to the first one. -/
theorem last_conjugate : IsConjugateTo last (disjointTranspositions 6 1) := by
  let g : Perm := Equiv.swap 0 4 * Equiv.swap 1 5
  have hc : ∀ i : Fin 2,
      (MulAut.conj g) (initialWords 1 i) = lineWords 0 i := by decide
  refine ⟨g, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨i, rfl⟩ := (mem_last_iff x).1 hx
    exact Subgroup.mem_map.mpr ⟨initialWords 1 i,
      (mem_disjointTranspositions_iff (1 : Fin 4) _).2 ⟨i, rfl⟩, hc i⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨i, rfl⟩ := (mem_disjointTranspositions_iff (1 : Fin 4) y).1 hy
    exact (mem_last_iff _).2 ⟨i, (hc i).symm⟩

/-- The last two transpositions form a conjugate of the initial rank-two group. -/
theorem tailTwo_conjugate : IsConjugateTo tailTwo (disjointTranspositions 6 2) := by
  let g : Perm := Equiv.swap 0 4 * Equiv.swap 1 5
  have hf : ∀ i : Fin 4, ∃ j : Fin 4,
      (MulAut.conj g) (initialWords 2 j) = planeWords 3 i := by decide
  have hb : ∀ j : Fin 4, ∃ i : Fin 4,
      planeWords 3 i = (MulAut.conj g) (initialWords 2 j) := by decide
  refine ⟨g, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨i, rfl⟩ := (mem_tailTwo_iff x).1 hx
    obtain ⟨j, hj⟩ := hf i
    exact Subgroup.mem_map.mpr ⟨initialWords 2 j,
      (mem_disjointTranspositions_iff (2 : Fin 4) _).2 ⟨j, rfl⟩, hj⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨j, rfl⟩ := (mem_disjointTranspositions_iff (2 : Fin 4) y).1 hy
    exact (mem_tailTwo_iff _).2 (hb j)

end Six
end CFSG.Quasithin.ChapterB.Offenders
