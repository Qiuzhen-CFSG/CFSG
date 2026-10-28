module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Defs
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Odd.Representatives
public import Mathlib.GroupTheory.Sylow

/-!
# Sylow containment in odd degree

In degrees five and seven, every transposition in a 2-subgroup containing `D`
is a canonical pair swap. Indeed, any other transposition overlaps a canonical
pair in exactly one point, and their product is a nonidentity element whose cube
is one. A small kernel-checked certificate verifies this alternative on the
five- and seven-point sets; the coprime power map excludes it in a 2-group.

Conjugating the generators of `A_m` gives transpositions, so every member of
`CaseAFamily` inside such a 2-subgroup lies in `D`. The checked order formula
for `D` then supplies a Sylow 2-subgroup containing it.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, Proposition B.3.2(4), printed pp. 83–84.
-/

public section

namespace CFSG.Quasithin.ChapterB.Offenders.Odd

private theorem swap_obstruction {n : ℕ} (hn : n = 5 ∨ n = 7) :
    ∀ a b : Fin n, a ≠ b →
      (∃ i : Fin (n / 2), Equiv.swap a b = pairSwap n i) ∨
      ∃ i : Fin (n / 2), (Equiv.swap a b * pairSwap n i) ^ 3 = 1 ∧
        Equiv.swap a b * pairSwap n i ≠ 1 := by
  rcases hn with rfl | rfl <;> decide


private theorem cube_eq_one {G : Type*} [Group G] (hG : IsPGroup 2 G)
    (x : G) (hx : x ^ 3 = 1) : x = 1 := by
  apply (hG.powEquiv (by decide : Nat.Coprime 2 3)).injective
  simpa only [IsPGroup.powEquiv_apply, one_pow] using hx

/-- A transposition in a 2-subgroup containing `D` already belongs to `D`. -/
theorem isSwap_mem_D_of_isPGroup {n : ℕ} (hn : n = 5 ∨ n = 7)
    {P : Subgroup (Equiv.Perm (Fin n))} (hP : IsPGroup 2 P) (hD : D n ≤ P)
    {s : Equiv.Perm (Fin n)} (hs : s.IsSwap) (hsP : s ∈ P) : s ∈ D n := by
  rcases hs with ⟨a, b, hab, rfl⟩
  rcases swap_obstruction hn a b hab with ⟨i, hi⟩ | ⟨i, hc, hne⟩
  · rw [hi]
    exact pairSwap_mem i i.isLt
  · have hmem := P.mul_mem hsP (hD (pairSwap_mem i i.isLt))
    have heq := cube_eq_one hP (⟨_, hmem⟩ : P) (Subtype.ext hc)
    exact False.elim (hne (congrArg Subtype.val heq))

private theorem conj_pairSwap_isSwap {n : ℕ} (g : Equiv.Perm (Fin n))
    (i : Fin (n / 2)) : ((MulAut.conj g) (pairSwap n i)).IsSwap := by
  let a : Fin n := ⟨2 * i.val, by omega⟩
  let b : Fin n := ⟨2 * i.val + 1, by omega⟩
  refine ⟨g a, g b, ?_, ?_⟩
  · apply g.injective.ne
    intro h
    have := congrArg Fin.val h
    dsimp [a, b] at this
    omega
  · change g * Equiv.swap a b * g⁻¹ = Equiv.swap (g a) (g b)
    exact Equiv.symm_trans_swap_trans a b g

/-- Containment of case (a) holds in every 2-subgroup containing `D`. -/
theorem caseAFamily_le_D_of_isPGroup {n : ℕ} (hn : n = 5 ∨ n = 7)
    {P : Subgroup (Equiv.Perm (Fin n))} (hP : IsPGroup 2 P) (hD : D n ≤ P)
    {A : Subgroup (Equiv.Perm (Fin n))} (hA : CaseAFamily n A) (hAP : A ≤ P) :
    A ≤ D n := by
  rcases hA with ⟨m, _, _, g, rfl⟩
  apply Subgroup.map_le_iff_le_comap.mpr
  apply (Subgroup.closure_le _).mpr
  rintro s ⟨i, hi, rfl⟩
  apply isSwap_mem_D_of_isPGroup hn hP hD (conj_pairSwap_isSwap g i)
  apply hAP
  exact Subgroup.mem_map.mpr ⟨pairSwap n i, pairSwap_mem i hi, rfl⟩

/-- Every Sylow 2-subgroup containing `D` has the required case (a) containment. -/
theorem caseAFamily_le_D_of_le_sylow {n : ℕ} (hn : n = 5 ∨ n = 7)
    (T : Sylow 2 (Equiv.Perm (Fin n))) (hD : D n ≤ T)
    {A : Subgroup (Equiv.Perm (Fin n))} (hA : CaseAFamily n A) (hAT : A ≤ T) :
    A ≤ D n :=
  caseAFamily_le_D_of_isPGroup hn T.isPGroup' hD hA hAT

/-- The Sylow subgroup required for B.3.2(4) in degrees five and seven. -/
theorem exists_sylow_containing_D {n : ℕ} (hn : n = 5 ∨ n = 7) :
    ∃ T : Sylow 2 (Equiv.Perm (Fin n)), D n ≤ T ∧
      ∀ A, CaseAFamily n A → A ≤ T → A ≤ D n := by
  obtain ⟨T, hT⟩ := (IsPGroup.of_card
    (card_disjointTranspositions hn (le_refl (n / 2)))).exists_le_sylow
  exact ⟨T, hT, fun _ hA hAT => caseAFamily_le_D_of_le_sylow hn T hT hA hAT⟩

end CFSG.Quasithin.ChapterB.Offenders.Odd
