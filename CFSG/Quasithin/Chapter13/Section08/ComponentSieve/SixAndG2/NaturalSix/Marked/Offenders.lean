module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Marked.Outer
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Rigidity

/-!
# The distinguished transvection cube and its opposite action

The within-pair cube of the canonical flag is the exact subgroup `D 6` in
the degree-six offender classification. Rigidity identifies each elementary
actor fixing a hyperplane with a transposition group; the Sylow classification
then puts it in D. Conversely the three generating transpositions fix
hyperplanes. Thus their generated subgroup is precisely D, of rank three.
Its outer image is the exceptional cube, and the explicit second displacement
in `Outer` excludes quadraticity on the opposite natural action.

Source: Aschbacher–Smith B.3.4(2)(i) and the strong-offender contradiction
in 13.8.26, printed pp.84–85 and 962. No assertion about arbitrary rank-three
subgroups is made.
-/

@[expose] public section

open BinaryPermutation Representation.BinaryOffender
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Marked

open CFSG.Quasithin.ChapterB.Offenders
open CFSG.Quasithin.ChapterB.Offenders.Six

/-- The canonical flag cube is literally the cube in the offender classification. -/
theorem flags_D_eq : BinaryFlags.D = CFSG.Quasithin.ChapterB.Offenders.D 6 := by
  unfold BinaryFlags.D CFSG.Quasithin.ChapterB.Offenders.D disjointTranspositions
  congr 1
  ext g
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by decide, rfl⟩
    · exact ⟨1, by decide, rfl⟩
    · exact ⟨2, by decide, rfl⟩
  · rintro ⟨i, _, rfl⟩
    fin_cases i <;> simp [pairSwap, swap01, swap23, swap45]

theorem D_rank : rank BinaryFlags.D = 3 := by
  rw [flags_D_eq]
  exact rank_disjointTranspositions 3

theorem D_card : Nat.card BinaryFlags.D = 8 := by
  rw [flags_D_eq]
  exact card_disjointTranspositions 3

theorem D_elementary : IsElementaryTwo BinaryFlags.D := by
  rw [flags_D_eq]
  exact isElementaryTwo_disjointTranspositions 3 (by decide)

theorem D_le_sylow : BinaryFlags.D ≤ sylowCarrier := by
  rw [flags_D_eq]
  exact D_le_sylowCarrier

theorem strong_iff (A : Subgroup Symmetric) :
    IsStrongOffender symmetricAction A ↔ IsConjugateTo A BinaryFlags.D := by
  rw [flags_D_eq]
  exact isStrongOffender_natural_iff A

theorem strong_best_in_sylow_iff (A : Subgroup Symmetric) :
    (IsBestOffender symmetricAction A ∧ IsStrongOffender symmetricAction A ∧
      A ≤ sylowCarrier) ↔ A = BinaryFlags.D := by
  rw [flags_D_eq]
  exact strong_best_natural_le_sylowCarrier_iff A

theorem strong_in_sylow_eq_D {A : Subgroup Symmetric}
    (hs : IsStrongOffender symmetricAction A) (hT : A ≤ sylowCarrier) :
    A = BinaryFlags.D := by
  rw [flags_D_eq]
  exact eq_D_of_le_sylowCarrier_of_conjugate hT ((isStrongOffender_natural_iff A).mp hs)

theorem strong_in_sylow_not_quadratic {A : Subgroup Symmetric}
    (hs : IsStrongOffender symmetricAction A) (hT : A ≤ sylowCarrier) :
    ¬ IsQuadratic oppositeAction A := by
  rw [strong_in_sylow_eq_D hs hT]
  exact D_not_quadratic

/-- In characteristic two these are exactly the nontrivial elementary actors
fixing a hyperplane; `transvectionGroup_card` verifies that each is an involution
subgroup, so its nonidentity element is a natural transvection. -/
def transvectionGroups : Set (Subgroup Symmetric) :=
  {A | IsElementaryTwo A ∧ fixedCodim symmetricAction A = 1}

theorem transvectionGroup_card {A : Subgroup Symmetric} (hA : A ∈ transvectionGroups) :
    Nat.card A = 2 := by
  obtain ⟨g, rfl⟩ := natural_small_codim_conjugate hA.1 hA.2.le
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact card_disjointTranspositions 1

def transvectionSubgroup : Subgroup Symmetric := generatedBy transvectionGroups sylowCarrier

private theorem A1_closure : disjointTranspositions 6 1 = Subgroup.closure {swap01} := by
  unfold disjointTranspositions
  congr 1
  ext g
  constructor
  · rintro ⟨i, hi, rfl⟩
    fin_cases i <;> simp_all [pairSwap, swap01]
  · rintro rfl
    exact ⟨0, by decide, rfl⟩

private def pairConjugator : Fin 3 → Symmetric :=
  ![1, Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.swap 0 4 * Equiv.swap 1 5]

private theorem pairGroup_conjugate (i : Fin 3) :
    IsConjugateTo (Subgroup.closure {pairSwap 6 i}) (disjointTranspositions 6 1) := by
  refine ⟨pairConjugator i, ?_⟩
  rw [A1_closure, MonoidHom.map_closure, Set.image_singleton]
  congr 2
  fin_cases i <;> decide

private theorem pairGroup_mem (i : Fin 3) : Subgroup.closure {pairSwap 6 i} ∈ transvectionGroups := by
  constructor
  · exact (pairGroup_conjugate i).isElementaryTwo
      (isElementaryTwo_disjointTranspositions 1 (by decide))
  · obtain ⟨g, he⟩ := pairGroup_conjugate i
    rw [he, fixedCodim_map_conj]
    exact fixedCodim_A1.2.2.2

theorem transvectionSubgroup_eq_D : transvectionSubgroup = BinaryFlags.D := by
  rw [flags_D_eq]
  apply le_antisymm
  · refine iSup_le fun A => iSup_le fun h => ?_
    obtain ⟨g, hg⟩ := natural_small_codim_conjugate h.1.1 h.1.2.le
    exact caseAFamily_le_D_of_le_sylowCarrier ⟨1, by decide, by decide, g, hg⟩ h.2
  · rw [CFSG.Quasithin.ChapterB.Offenders.D, disjointTranspositions, Subgroup.closure_le]
    rintro g ⟨i, _, rfl⟩
    have hT : Subgroup.closure {pairSwap 6 i} ≤ sylowCarrier := by
      rw [Subgroup.closure_le, Set.singleton_subset_iff]
      exact D_le_sylowCarrier (pairSwap_mem i i.isLt)
    have hle : Subgroup.closure {pairSwap 6 i} ≤ transvectionSubgroup :=
      le_iSup_of_le (Subgroup.closure {pairSwap 6 i})
        (le_iSup_of_le ⟨pairGroup_mem i, hT⟩ le_rfl)
    exact hle (Subgroup.subset_closure rfl)

theorem transvectionSubgroup_rank : rank transvectionSubgroup = 3 := by
  rw [transvectionSubgroup_eq_D]
  exact D_rank

theorem transvectionSubgroup_not_quadratic : ¬ IsQuadratic oppositeAction transvectionSubgroup := by
  rw [transvectionSubgroup_eq_D]
  exact D_not_quadratic

/-- The outer image of the transvection cube is the actual exceptional cube,
with its regular Klein four on the first four letters and its last pair swap. -/
theorem outer_D : BinaryFlags.D.map outer.toMonoidHom = exceptional 6 (by decide) := by
  apply Subgroup.eq_of_le_of_card_ge
  · rw [Subgroup.map_le_iff_le_comap, BinaryFlags.D, Subgroup.closure_le]
    rintro g (rfl | rfl | rfl)
    all_goals change outer _ ∈ exceptional 6 (by decide)
    · rw [outer_swap01]
      exact (mem_exceptional_iff _).mpr ⟨6, by decide⟩
    · rw [outer_swap23]
      exact (mem_exceptional_iff _).mpr ⟨7, by decide⟩
    · rw [outer_swap45]
      exact (mem_exceptional_iff _).mpr ⟨5, by decide⟩
  · rw [Subgroup.card_map_of_injective outer.injective, D_card, card_exceptional]

theorem outer_D0 : BinaryFlags.D0.map outer.toMonoidHom =
    exceptional 6 (by decide) ⊓ alternatingGroup (Fin 6) := by
  rw [BinaryFlags.D0, Subgroup.map_inf _ _ _ outer.injective, outer_D, outer_alternating]

theorem sylow_le_H2 : sylowCarrier ≤ H2 := by
  intro g hg
  obtain ⟨i, rfl⟩ := (mem_sylowCarrier_iff g).mp hg
  clear hg
  revert i
  decide +kernel

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Marked
