module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.CoreGeometry

/-!
# The S6 point-core offender family

The point radical is the exceptional elementary subgroup in B.3.4. Its five
best offenders are the point transposition, three mixed planes, and the full
radical. None is strong. Equal-weight subgroups lying in even conjugates of
one mixed plane generate each offender. Two explicit even conjugates of that
plane generate S6, and each has fixed codimension two on the natural module.

These are the finite group and module calculations used by the full-radical
B.2.19 branch of C.1.37, printed pp.142--143.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.Model
open Subgroup BinaryPermutation Representation.BinaryOffender
open ChapterB.Offenders ChapterB.Offenders.Six
abbrev S := Equiv.Perm (Fin 6)
noncomputable abbrev rho := naturalRepresentation (Fin 6)
abbrev E := exceptional 6 (by decide)

theorem pointCore_eq_exceptional :
    Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore = E := by
  rw [Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore_eq_closure]
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro x (rfl | rfl | rfl)
    · exact last_le_exceptional (subset_closure rfl)
    · exact plus_le_exceptional (subset_closure (Or.inl rfl))
    · exact klein_le_exceptional (subset_closure (Or.inr rfl))
  · apply (closure_le _).mpr
    rintro x ((rfl | rfl) | ⟨i,hi,rfl⟩)
    · exact subset_closure (Or.inr (Or.inl rfl))
    · exact subset_closure (Or.inr (Or.inr rfl))
    · have hi2 : i = 2 := by apply Fin.ext; have := i.isLt; dsimp at *; omega
      subst i
      exact subset_closure (Or.inl rfl)

theorem no_strong {A : Subgroup S} (hA : A ≤ E) : ¬ IsStrongOffender rho A := by
  rw [isStrongOffender_natural_iff]
  exact exceptional_not_conjugate_D hA

theorem rank_le_fixedCodim {A : Subgroup S} (hA : A ≤ E) (he : IsElementaryTwo A) :
    rank A ≤ fixedCodim rho A := by
  exact Nat.le_of_not_gt (fun h => no_strong hA ⟨he,h⟩)

theorem best_iff {A : Subgroup S} (hA : A ≤ E) :
    IsBestOffender rho A ↔ A = last ∨ A = plus ∨ A = mixedSecond ∨
      A = mixedThird ∨ A = E := by
  rw [isBestOffender_natural_iff]
  exact caseBFamily_le_exceptional_iff hA

theorem best_contains_swap {A : Subgroup S} (hA : A ≤ E)
    (hb : IsBestOffender rho A) : pairSwap 6 2 ∈ A := by
  apply (exceptional_last_mem_iff hA).mpr
  exact (best_iff hA).mp hb

theorem best_weight {A : Subgroup S} (hA : A ≤ E)
    (hb : IsBestOffender rho A) : weight rho A = 4 := by
  have ho : IsOffender rho A := (isOffender_natural_iff A).mpr
    ((isBestOffender_natural_iff A).mp hb)
  have he : fixedCodim rho A = rank A := le_antisymm ho.2 (rank_le_fixedCodim hA ho.1)
  have hd := fixedCodim_add_finrank rho A
  rw [he, finrank_natural_even (Fin 6) (by decide)] at hd
  exact hd

def conjugator : S := Equiv.swap 1 2 * Equiv.swap 3 4

theorem conjugator_even : conjugator ∈ alternatingGroup (Fin 6) := by
  change Equiv.Perm.sign conjugator = 1
  decide

def secondPlane : Subgroup S := plus.map (MulAut.conj conjugator).toMonoidHom

private def generators : Fin 4 → S :=
  ![kleinFirst 6 (by decide), pairSwap 6 2,
    (MulAut.conj conjugator) (kleinFirst 6 (by decide)),
    (MulAut.conj conjugator) (pairSwap 6 2)]

private def adjacentWord : Fin 5 → List (Fin 4) :=
  ![[0,3,0,3,0,3], [0,1,2,0,2,0,1,3], [3,0,3,0,3], [1,3,1], [1]]

private theorem adjacentWord_value (i : Fin 5) :
    ((adjacentWord i).map generators).prod = Equiv.swap i.castSucc i.succ := by
  revert i
  decide +kernel

theorem planes_generate : plus ⊔ secondPlane = ⊤ := by
  let N := plus ⊔ secondPlane
  have hg (i : Fin 4) : generators i ∈ N := by
    fin_cases i
    · exact mem_sup_left (subset_closure (Or.inl rfl))
    · exact mem_sup_left (subset_closure (Or.inr rfl))
    · exact mem_sup_right (mem_map_of_mem _ (subset_closure (Or.inl rfl)))
    · exact mem_sup_right (mem_map_of_mem _ (subset_closure (Or.inr rfl)))
  apply top_unique
  rw [← Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ 5)]
  apply (closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  change Equiv.swap i.castSucc i.succ ∈ N
  rw [← adjacentWord_value i]
  apply N.list_prod_mem
  intro x hx
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx
  exact hg j


def planeConjugator (i : Fin 3) : S :=
  ![1, Equiv.swap 1 2 * Equiv.swap 4 5, Equiv.swap 1 3 * Equiv.swap 4 5] i

def corePlane (i : Fin 3) : Subgroup S := ![plus,mixedSecond,mixedThird] i

theorem planeConjugator_even (i : Fin 3) : planeConjugator i ∈ alternatingGroup (Fin 6) := by
  change Equiv.Perm.sign (planeConjugator i) = 1
  revert i
  decide

theorem corePlane_conjugate (i : Fin 3) :
    plus.map (MulAut.conj (planeConjugator i)).toMonoidHom = corePlane i := by
  fin_cases i
  · change plus.map (MonoidHom.id S) = plus
    exact map_id plus
  · rw [plus,MonoidHom.map_closure]
    simp only [Set.image_insert_eq,Set.image_singleton]
    change closure { (MulAut.conj (planeConjugator 1)) (kleinFirst 6 (by decide)),
      (MulAut.conj (planeConjugator 1)) (pairSwap 6 2) } = mixedSecond
    have h1 : (MulAut.conj (planeConjugator 1)) (kleinFirst 6 (by decide)) =
        kleinSecond 6 (by decide) := by decide
    have h2 : (MulAut.conj (planeConjugator 1)) (pairSwap 6 2) = pairSwap 6 2 := by decide
    rw [h1,h2]
    rfl
  · rw [plus,MonoidHom.map_closure]
    simp only [Set.image_insert_eq,Set.image_singleton]
    change closure { (MulAut.conj (planeConjugator 2)) (kleinFirst 6 (by decide)),
      (MulAut.conj (planeConjugator 2)) (pairSwap 6 2) } = mixedThird
    have h1 : (MulAut.conj (planeConjugator 2)) (kleinFirst 6 (by decide)) =
        kleinFirst 6 (by decide) * kleinSecond 6 (by decide) := by decide
    have h2 : (MulAut.conj (planeConjugator 2)) (pairSwap 6 2) = pairSwap 6 2 := by decide
    rw [h1,h2]
    rfl

theorem corePlane_le (i : Fin 3) : corePlane i ≤ E := by
  fin_cases i
  · exact plus_le_exceptional
  · exact mixedSecond_le_exceptional
  · exact mixedThird_le_exceptional

theorem corePlane_best (i : Fin 3) : IsBestOffender rho (corePlane i) := by
  apply (best_iff (corePlane_le i)).mpr
  fin_cases i <;> simp [corePlane]

theorem corePlane_codim (i : Fin 3) : fixedCodim rho (corePlane i) = 2 := by
  rw [← corePlane_conjugate,fixedCodim_map_conj]
  exact fixedCodim_plus.2.2.2

theorem corePlanes_generate : plus ⊔ mixedSecond = E := by
  apply le_antisymm (sup_le plus_le_exceptional mixedSecond_le_exceptional)
  apply (closure_le _).mpr
  rintro x ((rfl | rfl) | ⟨i,hi,rfl⟩)
  · exact mem_sup_left (subset_closure (Or.inl rfl))
  · exact mem_sup_right (subset_closure (Or.inl rfl))
  · have hi2 : i = 2 := by apply Fin.ext; have := i.isLt; dsimp at *; omega
    subst i
    exact mem_sup_left (subset_closure (Or.inr rfl))

theorem best_small_cover {A : Subgroup S} (hA : A ≤ E)
    (hb : IsBestOffender rho A) (hne : A ≠ E) :
    ∃ g ∈ alternatingGroup (Fin 6), A ≤ plus.map (MulAut.conj g).toMonoidHom := by
  rcases (best_iff hA).mp hb with rfl | rfl | rfl | rfl | he
  · exact ⟨1,one_mem _,by change last ≤ plus.map (MonoidHom.id S);rw [map_id];exact last_le_plus⟩
  · exact ⟨1,one_mem _,by change plus ≤ plus.map (MonoidHom.id S);rw [map_id]⟩
  · exact ⟨planeConjugator 1,planeConjugator_even 1,by rw [corePlane_conjugate];exact le_rfl⟩
  · exact ⟨planeConjugator 2,planeConjugator_even 2,by rw [corePlane_conjugate];exact le_rfl⟩
  · exact (hne he).elim

theorem equal_weight_cover {A : Subgroup S} (hA : A ≤ E) (hb : IsBestOffender rho A) :
    ∃ F : Set (Subgroup S), sSup F = A ∧ ∀ B ∈ F,
      IsElementaryTwo B ∧ EqualWeightLE rho B A ∧
      ∃ g ∈ alternatingGroup (Fin 6), B ≤ plus.map (MulAut.conj g).toMonoidHom := by
  by_cases he : A = E
  · subst A
    refine ⟨{plus,mixedSecond},?_,?_⟩
    · simpa using corePlanes_generate
    · intro B hB
      rcases hB with rfl | rfl
      · have hbest := corePlane_best 0
        refine ⟨hbest.1,⟨plus_le_exceptional,?_⟩,1,one_mem _,?_⟩
        exact (best_weight plus_le_exceptional hbest).trans (best_weight le_rfl hb).symm
        change plus ≤ plus.map (MonoidHom.id S)
        rw [map_id]
      · have hbest := corePlane_best 1
        refine ⟨hbest.1,⟨mixedSecond_le_exceptional,?_⟩,
          planeConjugator 1,planeConjugator_even 1,?_⟩
        · exact (best_weight mixedSecond_le_exceptional hbest).trans (best_weight le_rfl hb).symm
        · rw [corePlane_conjugate];exact le_rfl
  · refine ⟨{A},by simp,?_⟩
    intro B hB
    obtain rfl : B=A := Set.mem_singleton_iff.mp hB
    exact ⟨hb.1,⟨le_rfl,rfl⟩,best_small_cover hA hb he⟩

theorem exists_plane_equalWeight {A : Subgroup S} (hA : A ≤ E)
    (hb : IsBestOffender rho A) (hne : ¬ A ≤ last) :
    ∃ i : Fin 3, EqualWeightLE rho (corePlane i) A := by
  rcases (best_iff hA).mp hb with he | he | he | he | he
  · exact (hne (he.le)).elim
  · exact ⟨0,he ▸ ⟨le_rfl,rfl⟩⟩
  · exact ⟨1,he ▸ ⟨le_rfl,rfl⟩⟩
  · exact ⟨2,he ▸ ⟨le_rfl,rfl⟩⟩
  · subst A
    exact ⟨0,plus_le_exceptional,
      (best_weight plus_le_exceptional (corePlane_best 0)).trans (best_weight le_rfl hb).symm⟩

noncomputable def root (i : Fin 2) : Subgroup S := if i=0 then plus else secondPlane

theorem root_generation : (⨆ i : Fin 2, root i) = ⊤ := by
  apply top_unique
  rw [← planes_generate]
  exact sup_le (le_iSup root 0) (le_iSup root 1)

theorem root_codim (i : Fin 2) : fixedCodim rho (root i) = 2 := by
  fin_cases i
  · exact fixedCodim_plus.2.2.2
  · change fixedCodim rho (plus.map (MulAut.conj conjugator).toMonoidHom) = 2
    rw [fixedCodim_map_conj]
    exact fixedCodim_plus.2.2.2

end CFSG.Quasithin.ChapterC.NaturalSixControl.Model
