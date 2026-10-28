module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Exhaustion
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Canonical.Hyperplanes.Forms
public import Theory.SpecificGroups.SymmetricEight.FourBlockCoreAction

/-!
# No orthogonal offenders in the actual four-block two-core

The complete degree-eight classification leaves the disjoint-swap,
exceptional, even-hyperplane and regular-eight families. The first two
contain odd permutations; an even hyperplane has two four-point supports
whose union has size six, impossible in the two block Klein groups.
The remaining hyperplanes contain odd permutations, and the regular
family cannot preserve the two four-point blocks.

Thus every nontrivial elementary subgroup of the literal V₄ × V₄
fails the offender inequality on the six-dimensional natural module.
The small finite check examines only pairs among its sixteen elements.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.3.2,
printed pp.83–85, applied after 13.6.23 on printed p.933.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.OrthogonalOffenders
open Subgroup Equiv Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.Offenders
open Theory.SpecificGroups.SymmetricEight.FourBlockCoreAction

private theorem klein_even : kleinGroup ≤ alternatingGroup (Fin 8) := by
  have ht : ∀ a b : Fin 4, Perm.sign (kleinPerm a b) = 1 := by decide
  rintro g ⟨a, b, rfl⟩
  exact ht a b

private theorem even_of_conjugate_le {A B : Subgroup (Perm (Fin 8))}
    (hA : A ≤ kleinGroup) (hc : IsConjugateTo A B) : B ≤ alternatingGroup (Fin 8) := by
  obtain ⟨g, rfl⟩ := hc
  intro b hb
  have hs := klein_even (hA (mem_map_of_mem (MulAut.conj g).toMonoidHom hb))
  change Perm.sign (g * b * g⁻¹) = 1 at hs
  change Perm.sign b = 1
  have he : Perm.sign (g * b * g⁻¹) = Perm.sign b := by
    rw [map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]
  exact he ▸ hs

private theorem not_caseA {A : Subgroup (Perm (Fin 8))} (hA : A ≤ kleinGroup) :
    ¬ CaseAFamily 8 A := by
  rintro ⟨m, hm, _, hc⟩
  have hs := even_of_conjugate_le hA hc (pairSwap_mem (n := 8) (m := m) 0 hm)
  exact (by decide : Perm.sign (pairSwap 8 0) ≠ 1) hs

private theorem not_exceptional {A : Subgroup (Perm (Fin 8))} (hA : A ≤ kleinGroup) :
    ¬ IsConjugateTo A (exceptional 8 (by decide)) := by
  intro hc
  have hm : pairSwap 8 2 ∈ exceptional 8 (by decide) :=
    subset_closure (Or.inr ⟨2, by decide, rfl⟩)
  exact (by decide : Perm.sign (pairSwap 8 2) ≠ 1)
    (even_of_conjugate_le hA hc hm)

private theorem klein_support_union {a b : Perm (Fin 8)} (ha : a ∈ kleinGroup)
    (hb : b ∈ kleinGroup) (hca : a.support.card = 4) (hcb : b.support.card = 4) :
    (a.support ∪ b.support).card ≠ 6 := by
  have ht : ∀ i j k l : Fin 4,
      (kleinPerm i j).support.card = 4 → (kleinPerm k l).support.card = 4 →
      ((kleinPerm i j).support ∪ (kleinPerm k l).support).card ≠ 6 := by decide
  obtain ⟨i, j, rfl⟩ := ha
  obtain ⟨k, l, rfl⟩ := hb
  exact ht i j k l hca hcb

private theorem not_evenPart {A : Subgroup (Perm (Fin 8))} (hA : A ≤ kleinGroup) :
    ¬ IsConjugateTo A (evenPart 8) := by
  rintro ⟨g, rfl⟩
  let a := pairSwap 8 0 * pairSwap 8 1
  let b := pairSwap 8 0 * pairSwap 8 2
  have ha : a ∈ evenPart 8 :=
    ⟨mul_mem (pairSwap_mem 0 (by decide)) (pairSwap_mem 1 (by decide)), show Perm.sign a = 1 from by decide⟩
  have hb : b ∈ evenPart 8 :=
    ⟨mul_mem (pairSwap_mem 0 (by decide)) (pairSwap_mem 2 (by decide)), show Perm.sign b = 1 from by decide⟩
  have hca : (g * a * g⁻¹).support.card = 4 := by
    rw [Perm.card_support_conj]
    decide
  have hcb : (g * b * g⁻¹).support.card = 4 := by
    rw [Perm.card_support_conj]
    decide
  have h := klein_support_union
    (hA (mem_map_of_mem (MulAut.conj g).toMonoidHom ha))
    (hA (mem_map_of_mem (MulAut.conj g).toMonoidHom hb)) hca hcb
  apply h
  change ((g * a * g⁻¹).support ∪ (g * b * g⁻¹).support).card = 6
  rw [Perm.support_conj, Perm.support_conj, ← Finset.map_union, Finset.card_map]
  decide

private theorem not_hyperplane {A : Subgroup (Perm (Fin 8))} (hA : A ≤ kleinGroup) :
    ¬ HyperplaneFamily 8 A := by
  rintro ⟨B, hB, hne, hc⟩
  have hBe : B ≤ evenPart 8 := le_inf hB.le (even_of_conjugate_le hA hc)
  have hed : evenPart 8 ≠ D 8 := by
    intro he
    have hh : pairSwap 8 0 ∈ evenPart 8 := he ▸ pairSwap_mem 0 (by decide)
    exact (by decide : Perm.sign (pairSwap 8 0) ≠ 1) hh.2
  exact hne ((hB.eq_or_eq hBe inf_le_left).resolve_right hed).symm

private theorem not_regular {A : Subgroup (Perm (Fin 8))} (hA : A ≤ kleinGroup) :
    ¬ IsRegularEight A := by
  intro h
  obtain ⟨a, ha, _⟩ := h.2.2.2 0 4
  obtain ⟨i, j, hij⟩ := hA a.property
  have ht : ∀ i j : Fin 4, (kleinPerm i j 0).val < 4 := by decide
  have hh := ht i j
  rw [← hij, ha] at hh
  omega

/-- The actual four-block two-core contains no nontrivial binary offender
on the six-dimensional natural module. -/
theorem not_isOffender_natural {A : Subgroup (Perm (Fin 8))} (hA : A ≤ kleinGroup) :
    ¬ IsOffender (naturalRepresentation (Fin 8)) A := by
  intro h
  rcases EightExhaustion.caseBFamily_or_isRegularEight_of_isOffender_natural h with
    (h | h | h | h) | h
  · exact not_caseA hA h
  · exact not_exceptional hA h
  · exact not_evenPart hA h
  · exact not_hyperplane hA h
  · exact not_regular hA h

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.OrthogonalOffenders
