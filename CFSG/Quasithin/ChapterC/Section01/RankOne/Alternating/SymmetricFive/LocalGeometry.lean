module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Geometry
public import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic
/-!
# The local S₄ subgroup in the natural S₅ branch

A two-group containing the transposition four-group fixes its unique common
fixed letter. The resulting point stabilizer is maximal of index five. A
three-cycle in its alternating subgroup joins the four-group to a conjugate
generating the whole point stabilizer. A bounded word certificate verifies
this last assertion in the actual five-letter permutation group.

Source: Aschbacher–Smith, C.1.24 and 3.1.7, printed pp.130–131 and 575–576.
-/

public section
namespace CFSG.Quasithin.ChapterC.SymmetricFive
open ChapterB.Offenders BinaryPermutation Subgroup Equiv MulAction

def pointFour : Subgroup Sym := stabilizer Sym (4 : Fin 5)

/-- Membership in the original marked point stabilizer. -/
theorem mem_pointFour_iff (g : Sym) : g ∈ pointFour ↔ g 4 = 4 := Iff.rfl

theorem pointFour_index : pointFour.index = 5 := by
  rw [pointFour, index_stabilizer, orbit_eq_univ]
  simp

theorem pointFour_coatom : IsCoatom pointFour := by
  refine ⟨fun ht => by simpa [ht] using pointFour_index, fun B hB => ?_⟩
  have hm := relIndex_mul_index hB.le
  rw [pointFour_index] at hm
  have hp : (pointFour.relIndex B * B.index).Prime := hm.symm ▸ (by decide : Nat.Prime 5)
  rcases Nat.prime_mul_iff.mp hp with ⟨_, hB'⟩ | ⟨_, hrel⟩
  · exact index_eq_one.mp hB'
  · exact (hB.not_ge (relIndex_eq_one.mp hrel)).elim

theorem two_group_le_pointFour {P : Subgroup Sym} (hP : IsPGroup 2 P) (hD : D 5 ≤ P) :
    P ≤ pointFour := by
  obtain ⟨i, hi⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card (Fin 5) (by norm_num)
  have ha : swap (0 : Fin 5) 1 i = i := hi ⟨_, hD (pairSwap_mem 0 (by decide))⟩
  have hb : swap (2 : Fin 5) 3 i = i := hi ⟨_, hD (pairSwap_mem 1 (by decide))⟩
  have hc : ∀ i : Fin 5, swap (0 : Fin 5) 1 i = i → swap (2 : Fin 5) 3 i = i → i = 4 := by decide
  have he := hc i ha hb
  subst i
  intro g hg
  exact hi ⟨g, hg⟩

def localCubic : Sym := swap 0 1 * swap 1 2

theorem localCubic_even : localCubic ∈ alternatingGroup (Fin 5) := by
  rw [Perm.mem_alternatingGroup]
  decide +kernel

theorem localCubic_mem_pointFour : localCubic ∈ pointFour := by
  change localCubic 4 = 4
  decide +kernel

private def fourWords : Fin 4 → Sym := ![1, pairSwap 5 0, pairSwap 5 1, pairSwap 5 0 * pairSwap 5 1]
private theorem fourWords_mem (i : Fin 4) : fourWords i ∈ D 5 := by
  fin_cases i
  · exact one_mem _
  · exact pairSwap_mem 0 (by decide)
  · exact pairSwap_mem 1 (by decide)
  · exact mul_mem (pairSwap_mem 0 (by decide)) (pairSwap_mem 1 (by decide))

theorem local_two_four_groups_generate :
    D 5 ⊔ (D 5).map (MulAut.conj localCubic).toMonoidHom = pointFour := by
  have hD : D 5 ≤ pointFour := by
    apply (closure_le _).mpr
    rintro g ⟨i, _, rfl⟩
    fin_cases i <;> change pairSwap 5 _ 4 = 4 <;> decide
  apply le_antisymm
  · apply sup_le hD
    rintro g ⟨x, hx, rfl⟩
    exact pointFour.mul_mem (pointFour.mul_mem localCubic_mem_pointFour (hD hx))
      (pointFour.inv_mem localCubic_mem_pointFour)
  · have hc : ∀ g : Sym, g 4 = 4 → ∃ i j k : Fin 4,
        fourWords i * (MulAut.conj localCubic) (fourWords j) * fourWords k = g := by
      decide +kernel
    intro g hg
    obtain ⟨i, j, k, rfl⟩ := hc g hg
    exact mul_mem (mul_mem (mem_sup_left (fourWords_mem i))
      (mem_sup_right (mem_map_of_mem _ (fourWords_mem j)))) (mem_sup_left (fourWords_mem k))

theorem pointFour_card : Nat.card pointFour = 24 := by
  have h := pointFour.index_mul_card
  rw [pointFour_index] at h
  have hc : Nat.card Sym = 120 := by
    norm_num [Sym, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  rw [hc] at h
  omega

theorem two_group_le_conjugate_pointFour {P : Subgroup Sym} (hP : IsPGroup 2 P)
    (a : Sym) (hD : (D 5).map (MulAut.conj a).toMonoidHom ≤ P) :
    P ≤ pointFour.map (MulAut.conj a).toMonoidHom := by
  have hcancel (B : Subgroup Sym) :
      (B.map (MulAut.conj a).toMonoidHom).map (MulAut.conj a⁻¹).toMonoidHom = B := by
    rw [map_map]
    have hi : (MulAut.conj a⁻¹).toMonoidHom.comp (MulAut.conj a).toMonoidHom = MonoidHom.id _ := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hi, map_id]
  have hD' : D 5 ≤ P.map (MulAut.conj a⁻¹).toMonoidHom := by
    simpa only [hcancel] using map_mono (f := (MulAut.conj a⁻¹).toMonoidHom) hD
  have hb := two_group_le_pointFour (hP.map _) hD'
  intro x hx
  refine ⟨a⁻¹ * x * a, hb (mem_map_of_mem _ hx), ?_⟩
  simp [MulAut.conj_apply, mul_assoc]

theorem local_two_conjugate_four_groups_generate (a : Sym) :
    (D 5).map (MulAut.conj a).toMonoidHom ⊔
      ((D 5).map (MulAut.conj a).toMonoidHom).map
        (MulAut.conj (a * localCubic * a⁻¹)).toMonoidHom =
          pointFour.map (MulAut.conj a).toMonoidHom := by
  have hc : ((D 5).map (MulAut.conj a).toMonoidHom).map
      (MulAut.conj (a * localCubic * a⁻¹)).toMonoidHom =
      ((D 5).map (MulAut.conj localCubic).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
    rw [map_map, map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [hc, ← Subgroup.map_sup, local_two_four_groups_generate]

end CFSG.Quasithin.ChapterC.SymmetricFive
