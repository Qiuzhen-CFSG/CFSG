module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.ActionTransport
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Odd.FullClassification
public import Theory.Representation.BinaryPermutation.OddOffenderTransport
public import Theory.Representation.AlternatingSevenConjugatePair.ElementaryGeometry

/-!
# The lower ratio bound for the natural A₇ module

B.3's equality cases in the permutation-module rank bound contain a
transposition, and therefore cannot lie in A₇. Every elementary actor
in A₇ has rank at most two. Its strictly larger integral fixed codimension
thus gives ratio at least 3/2, even without a cubicity assumption.
Both infima satisfy this lower bound, and actual intertwining coordinates
transport it to the source action with G = L.

This is the lower half of the A₇ row in Table B.4.5, as invoked in
Aschbacher–Smith, K.1, printed p.452. Attainment still requires a separate
quadratic actor calculation.
-/

public section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open scoped ENNReal

namespace CFSG.Quasithin.ChapterK.Alternating
open ChapterB.QuasisimpleSource ChapterB.Offenders

private theorem caseA_not_le_alternating {A : Subgroup (Equiv.Perm (Fin 7))}
    (hA : CaseAFamily 7 A) : ¬ A ≤ alternatingGroup (Fin 7) := by
  obtain ⟨m, hm0, _, g, rfl⟩ := hA
  intro h
  have hs : pairSwap 7 0 ∈ disjointTranspositions 7 m := pairSwap_mem 0 hm0
  have he := h (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hs)
  have hsign : Equiv.Perm.sign (pairSwap 7 0) = -1 := by decide
  have he' : Equiv.Perm.sign ((MulAut.conj g) (pairSwap 7 0)) = 1 := he
  simp only [MulAut.conj_apply, map_mul, map_inv, hsign] at he'
  have he'' : (-1 : Units ℤ) = 1 := by
    calc
      -1 = Equiv.Perm.sign g * -1 * (Equiv.Perm.sign g)⁻¹ := by
        rw [mul_comm (Equiv.Perm.sign g), mul_assoc, mul_inv_cancel, mul_one]
      _ = 1 := he'
  norm_num at he''

private theorem rank_lt_fixedCodim {A : Subgroup (Equiv.Perm (Fin 7))}
    (hA : IsElementaryTwo A) (hAlt : A ≤ alternatingGroup (Fin 7)) :
    rank A < fixedCodim (naturalRepresentation (Fin 7)) A := by
  rw [fixedCodim_natural_eq_full_odd (Fin 7) (by decide)]
  have hle := ChapterB.Offenders.Odd.rank_le_fixedCodim_full_of_elementary
    (Or.inr rfl) A hA
  by_contra hn
  have he : fixedCodim (representation (Fin 7)) A = rank A :=
    le_antisymm (Nat.le_of_not_gt hn) hle
  exact caseA_not_le_alternating
    (ChapterB.Offenders.Odd.caseAFamily_of_elementary_and_fixedCodim_full_eq_rank
      (Or.inr rfl) hA he) hAlt

/-- Every nontrivial elementary actor has ratio at least 3/2 on the natural A₇ module. -/
theorem sevenNatural_actionRatio_lower (A : Subgroup (alternatingGroup (Fin 7)))
    (hA : IsElementaryTwo A) : 3 / 2 ≤ actionRatio (alternatingNatural 7) A := by
  let f := (alternatingGroup (Fin 7)).subtype
  let B := A.map f
  let : IsElementaryAbelian 2 A := hA.2
  have hB : IsElementaryTwo B := by
    refine ⟨?_, IsElementaryAbelian.map f⟩
    intro hbot
    apply hA.1
    apply Subgroup.map_injective (f := f) Subtype.val_injective
    simpa only [Subgroup.map_bot] using hbot
  have hle : B ≤ alternatingGroup (Fin 7) := Subgroup.map_subtype_le A
  have hr := AlternatingSevenConjugatePair.ElementaryGeometry.rank_le_two_of_le_alternating
    B hB hle
  have hstrict := rank_lt_fixedCodim hB hle
  have hrank : rank B = rank A := rank_map_injective f Subtype.val_injective A
  have hcodim : fixedCodim (alternatingNatural 7) A =
      fixedCodim (naturalRepresentation (Fin 7)) B := by
    unfold fixedCodim
    rw [alternatingNatural, fixedSpace_comp_map]
  rw [hrank] at hr hstrict
  rw [← hcodim] at hstrict
  have hp := hA.rank_pos
  have hcases : rank A = 1 ∨ rank A = 2 := by omega
  rcases hcases with h | h
  · have hc : (2 : ℝ≥0∞) ≤ fixedCodim (alternatingNatural 7) A := by
      exact_mod_cast (show 2 ≤ fixedCodim (alternatingNatural 7) A by omega)
    rw [actionRatio, h, Nat.cast_one, div_one]
    have hn : (3 : ℝ≥0∞) / 2 ≤ 2 := by
      rw [ENNReal.div_le_iff (by norm_num) (by simp)]
      norm_num
    exact hn.trans hc
  · have hc : (3 : ℝ≥0∞) ≤ fixedCodim (alternatingNatural 7) A := by
      exact_mod_cast (show 3 ≤ fixedCodim (alternatingNatural 7) A by omega)
    rw [actionRatio, h]
    exact ENNReal.div_le_div_right hc 2

/-- The cubic lower bound does not assume that cubic actors are quadratic. -/
theorem sevenNatural_cubicRatio_lower : 3 / 2 ≤ cubicRatio (alternatingNatural 7) := by
  apply le_iInf
  intro A
  apply le_iInf
  intro hA
  exact sevenNatural_actionRatio_lower A hA.1

/-- The same lower bound applies to the smaller quadratic indexing family. -/
theorem sevenNatural_quadraticRatio_lower : 3 / 2 ≤ quadraticRatio (alternatingNatural 7) :=
  sevenNatural_cubicRatio_lower.trans (cubicRatio_le_quadraticRatio _)

/-- The lower half of the source A₇ row for the original full-component action. -/
theorem sevenNatural_source_lower {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    {L : Subgroup G} (hL : L = ⊤)
    (e : ActionEquiv (ρ.comp L.subtype) (alternatingNatural 7)) :
    3 / 2 ≤ cubicRatio ρ ∧ 3 / 2 ≤ quadraticRatio ρ := by
  rw [cubicRatio_eq (wholeAction hL e), quadraticRatio_eq (wholeAction hL e)]
  exact ⟨sevenNatural_cubicRatio_lower, sevenNatural_quadraticRatio_lower⟩

end CFSG.Quasithin.ChapterK.Alternating
