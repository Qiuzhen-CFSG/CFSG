module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.OuterActors.ActorCertificates.CoverageTable

/-!
# Exhaustion of outer elementary actors

An outer involution and the rank hypothesis supply an outer four-group.
The finite coverage table either contains the whole actor already, or a
third generator produces one of the two maximal elementary eight-groups.
The conclusion identifies every element of the original subgroup.

Source: Aschbacher–Smith E.1.14(7), printed p.214; Asc82a Lemma 4.11.
-/

public section
set_option maxRecDepth 10000
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.OuterActors.ActorCertificates

open Subgroup Matrix.PSL3Three.GraphLocalQuotients
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure

private theorem exists_second (A : Subgroup G) (hr : 1 < Group.rank A) (a : A) :
    ∃ b : A, b ≠ 1 ∧ b ≠ a := by
  classical
  by_contra h
  push Not at h
  have hc : Subgroup.closure (({a} : Finset A) : Set A) = ⊤ := by
    apply top_unique
    intro b _
    by_cases hb : b = 1
    · rw [hb]
      exact Subgroup.one_mem _
    · rw [h b hb]
      exact Subgroup.subset_closure (by simp)
  have hh := Group.rank_le hc
  simp only [Finset.card_singleton] at hh
  omega

/-- All whole outer elementary actors of rank at least two occur in the table.
The proof grows a four-group by at most one extra generator. -/
theorem actor_complete (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAS : A ≤ standardSubgroup) (hr : 1 < Group.rank A)
    (hout : ¬ A ≤ innerPart (ZMod 3)) :
    ∃ n : Fin 15, ∀ i, element i ∈ A ↔ i ∈ actor n := by
  classical
  let := hA
  have hsquare (i : Index) (hi : element i ∈ A) : involutive i :=
    (element_sq_eq_one_iff i).mp (elemPow_eq_one_of_isElementaryAbelian _ hi)
  have hcomm (i j : Index) (hi : element i ∈ A) (hj : element j ∈ A) :
      commutes i j :=
    (element_commute_iff i j).mp (show Commute (element i) (element j) from
      congrArg Subtype.val (mul_comm' (⟨element i,hi⟩ : A) ⟨element j,hj⟩))
  obtain ⟨a, ha, haout⟩ : ∃ a, a ∈ A ∧ a ∉ innerPart (ZMod 3) := by
    by_contra h
    apply hout
    intro a ha
    by_contra hn
    exact h ⟨a, ha, hn⟩
  obtain ⟨i, rfl⟩ := hAS ha
  have hi : i.2 = true := by
    have hh := (element_mem_inner_iff i).not.mp haout
    cases hi : i.2 <;> simp_all
  obtain ⟨b, hb1, hba⟩ := exists_second A hr ⟨element i,ha⟩
  obtain ⟨j, hj⟩ := hAS b.property
  have hjA : element j ∈ A := hj.symm ▸ b.property
  have hj0 : j ≠ (0,false) := by
    intro hh
    apply hb1
    apply Subtype.ext
    rw [← hj, hh, element_one]
    rfl
  have hji : j ≠ i := by
    intro hh
    apply hba
    apply Subtype.ext
    exact hj.symm.trans (congrArg element hh)
  obtain ⟨n, hn, hnrow⟩ := four_table i j hi (hsquare i ha) (hsquare j hjA)
    (hcomm i j ha hjA) hj0 hji
  have hrow : ∀ l ∈ actor n, element l ∈ A := by
    intro l hl
    rw [hnrow] at hl
    simp only [four, Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · rw [element_one]; exact A.one_mem
    · exact ha
    · exact hjA
    · rw [element_mul]; exact A.mul_mem ha hjA
  by_cases hsub : ∀ l, element l ∈ A → l ∈ actor n
  · exact ⟨n, fun l => ⟨hsub l, hrow l⟩⟩
  push Not at hsub
  obtain ⟨k, hkA, hkn⟩ := hsub
  obtain ⟨m, _, hmrow, hmax⟩ := eight_table n k hn (hsquare k hkA) hkn
    (fun l hl => hcomm k l hkA (hrow l hl))
  have hrowm : ∀ l ∈ actor m, element l ∈ A := by
    intro l hl
    rw [hmrow] at hl
    rcases Finset.mem_union.mp hl with hl | hl
    · exact hrow l hl
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hl
      rw [element_mul]
      exact A.mul_mem hkA (hrow x hx)
  refine ⟨m, fun l => ⟨fun hl => ?_, hrowm l⟩⟩
  exact hmax l (hsquare l hl) (fun x hx => hcomm l x hl (hrowm x hx))

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.OuterActors.ActorCertificates
