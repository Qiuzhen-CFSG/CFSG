module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Coordinates
public import CFSG.Quasithin.ChapterB.Section03.Offenders.SourceSylow

/-!
# Simultaneous marking of the degree-five Sylow action

The centralizer of the two disjoint transpositions is their four-group D.
Every Sylow two-subgroup containing D also contains the even exchange
(02)(13). Indeed, the odd-degree transposition calculation forces its
conjugations to permute the two pair swaps, placing it in the explicit
Sylow subgroup from B.3.2. All finite certificates are kernel checked.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.3.2,
printed pp.83–84, and C.5.6, printed pp.157–158.
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Action
open Subgroup CFSG.Quasithin.ChapterB.Offenders

private def words : Fin 4 → Perm :=
  ![1, transposition 0, transposition 1, transposition 0 * transposition 1]

private theorem words_mem (i : Fin 4) : words i ∈ ChapterB.Offenders.D 5 := by
  have h0 := pairSwap_mem (n := 5) (m := 2) 0 (by decide)
  have h1 := pairSwap_mem (n := 5) (m := 2) 1 (by decide)
  fin_cases i
  · exact one_mem _
  · exact h0
  · exact h1
  · exact mul_mem h0 h1

/-- The marked commuting-transposition actor is self-centralizing in S₅. -/
theorem centralizer_D_le : centralizer (ChapterB.Offenders.D 5 : Set Perm) ≤ ChapterB.Offenders.D 5 := by
  intro g hg
  have h0 := mem_centralizer_iff.mp hg (transposition 0) (words_mem 1)
  have h1 := mem_centralizer_iff.mp hg (transposition 1) (words_mem 2)
  have h : ∀ g : Perm, transposition 0 * g = g * transposition 0 →
      transposition 1 * g = g * transposition 1 → ∃ i, words i = g := by
    decide +kernel
  obtain ⟨i, rfl⟩ := h g h0 h1
  exact words_mem i

private theorem swap_mem_D_iff (g : Perm) (hg : g.IsSwap) :
    g ∈ ChapterB.Offenders.D 5 ↔ g = transposition 0 ∨ g = transposition 1 := by
  constructor
  · intro hD
    let := Odd.elementary_disjointTranspositions (n := 5) (m := 2) (Or.inl rfl) (by decide)
    have hc : ChapterB.Offenders.D 5 ≤ centralizer (ChapterB.Offenders.D 5 : Set Perm) :=
      le_centralizer_iff_isMulCommutative.mpr inferInstance
    have h0 := mem_centralizer_iff.mp (hc hD) (transposition 0) (words_mem 1)
    have h1 := mem_centralizer_iff.mp (hc hD) (transposition 1) (words_mem 2)
    have h : ∀ a b : Fin 5, a ≠ b →
        transposition 0 * Equiv.swap a b = Equiv.swap a b * transposition 0 →
        transposition 1 * Equiv.swap a b = Equiv.swap a b * transposition 1 →
        Equiv.swap a b = transposition 0 ∨ Equiv.swap a b = transposition 1 := by
      decide +kernel
    obtain ⟨a, b, hab, rfl⟩ := hg
    exact h a b hab h0 h1
  · rintro (rfl | rfl)
    · exact words_mem 1
    · exact words_mem 2

/-- The same marking of D puts the even exchange in every containing Sylow group. -/
theorem exchange_mem_sylow (P : Sylow 2 Perm) (hD : ChapterB.Offenders.D 5 ≤ P) : exchange ∈ P := by
  obtain ⟨T, hT⟩ := Odd.exists_sylow_containing_D_exceptional (n := 5) (Or.inl rfl)
  have he : exchange ∈ (T : Subgroup Perm) := by
    rw [hT]
    exact mem_sup_right (subset_closure (Or.inl (Or.inr (Set.mem_singleton _))))
  have hPT : (P : Subgroup Perm) ≤ T := by
    intro g hg
    have hs (i : Fin 2) : ((MulAut.conj g) (transposition i)).IsSwap := by
      fin_cases i
      · exact ⟨g 0, g 1, g.injective.ne (by decide),
          Equiv.symm_trans_swap_trans 0 1 g⟩
      · exact ⟨g 2, g 3, g.injective.ne (by decide),
          Equiv.symm_trans_swap_trans 2 3 g⟩
    have hi (i : Fin 2) := (swap_mem_D_iff _ (hs i)).mp
      (Odd.isSwap_mem_D_of_isPGroup (Or.inl rfl) P.isPGroup' hD (hs i)
        (P.mul_mem (P.mul_mem hg (hD (pairSwap_mem (n := 5) (m := 2) i i.isLt))) (P.inv_mem hg)))
    have h : ∀ g : Perm,
        (∀ i : Fin 2, (MulAut.conj g) (transposition i) = transposition 0 ∨
          (MulAut.conj g) (transposition i) = transposition 1) →
        ∃ i : Fin 4, g = words i ∨ g = words i * exchange := by decide +kernel
    obtain ⟨i, rfl | rfl⟩ := h g hi
    · exact hT ▸ mem_sup_left (words_mem i)
    · exact T.mul_mem (hT ▸ mem_sup_left (words_mem i)) he
  have hEq : (P : Subgroup Perm) = T := (P.is_maximal' T.isPGroup' hPT).symm
  change exchange ∈ (P : Subgroup Perm)
  rw [hEq]
  exact he

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Action

end
