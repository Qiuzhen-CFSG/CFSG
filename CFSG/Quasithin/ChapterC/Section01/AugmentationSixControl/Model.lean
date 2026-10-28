module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.SixCorePoint
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.Model
public import Theory.Representation.BinaryPermutation.CoreFixedLine

/-!
# Mixed-plane geometry on the augmentation core

The point radical's offenders admit equal-weight covers by two even-conjugate
mixed planes. Each plane has fixed codimension two, and A₆ has fixed
codimension four. These are calculations on the five-dimensional core;
they do not assume a splitting of its constant line or a two-group kernel.

Extracted from AugmentationSixControl.Baumann for its ordinary and full-kernel
Sylow-preimage applications. Source: Aschbacher--Smith B.3.4(2), pp.84--85,
and C.1.37, pp.142--143.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterC.AugmentationSixControl
open Subgroup Representation.BinaryOffender
open ChapterB.Offenders ChapterB.Offenders.Six
namespace Model
open BinaryPermutation
abbrev S := Equiv.Perm (Fin 6)
abbrev E := exceptional 6 (by decide)
abbrev rho := coreRepresentation (Fin 6)
abbrev secondPlane := NaturalSixControl.Model.secondPlane
abbrev conjugator := NaturalSixControl.Model.conjugator
abbrev planeConjugator := NaturalSixControl.Model.planeConjugator
abbrev corePlane := NaturalSixControl.Model.corePlane
abbrev root := NaturalSixControl.Model.root

abbrev pointCore_eq_exceptional := NaturalSixControl.Model.pointCore_eq_exceptional
abbrev conjugator_even := NaturalSixControl.Model.conjugator_even
abbrev planeConjugator_even := NaturalSixControl.Model.planeConjugator_even
theorem corePlane_conjugate (i : Fin 3) :
    plus.map (MulAut.conj (planeConjugator i)).toMonoidHom = corePlane i :=
  NaturalSixControl.Model.corePlane_conjugate i
abbrev corePlane_le := NaturalSixControl.Model.corePlane_le
abbrev root_generation := NaturalSixControl.Model.root_generation

theorem no_strong {A : Subgroup S} (hA : A ≤ E) : ¬ IsStrongOffender rho A := by
  rw [isStrongOffender_core_iff]
  exact exceptional_not_conjugate_D hA

theorem rank_le_fixedCodim {A : Subgroup S} (hA : A ≤ E) (he : IsElementaryTwo A) :
    rank A ≤ fixedCodim rho A := Nat.le_of_not_gt (fun h => no_strong hA ⟨he,h⟩)

theorem best_iff {A : Subgroup S} (hA : A ≤ E) :
    IsBestOffender rho A ↔ A = last ∨ A = plus ∨ A = mixedSecond ∨
      A = mixedThird ∨ A = E := by
  rw [isBestOffender_core_iff]
  exact caseBFamily_le_exceptional_iff hA

theorem best_weight {A : Subgroup S} (hA : A ≤ E)
    (hb : IsBestOffender rho A) : weight rho A = 5 := by
  have ho := hb.isOffender rho
  have he : fixedCodim rho A = rank A := le_antisymm ho.2 (rank_le_fixedCodim hA ho.1)
  have hd := fixedCodim_add_finrank rho A
  rw [he,finrank_core] at hd
  exact hd

theorem corePlane_best (i : Fin 3) : IsBestOffender rho (corePlane i) := by
  apply (best_iff (corePlane_le i)).mpr
  fin_cases i <;> simp [NaturalSixControl.Model.corePlane]

theorem root_codim (i : Fin 2) : fixedCodim rho (root i) = 2 := by
  fin_cases i
  · exact fixedCodim_plus.2.2.1
  · change fixedCodim rho (plus.map (MulAut.conj conjugator).toMonoidHom) = 2
    rw [fixedCodim_map_conj]
    exact fixedCodim_plus.2.2.1

theorem alternating_codim : fixedCodim rho (alternatingGroup (Fin 6)) = 4 := by
  have hf : fixedSpace rho (alternatingGroup (Fin 6)) = coreConstants := by
    ext v
    exact core_fixed_iff_constant (by simp) v
  have hd := fixedCodim_add_finrank rho (alternatingGroup (Fin 6))
  have he : Module.finrank (ZMod 2) (coreConstants (Ω := Fin 6)) = 1 := by
    change Module.finrank (ZMod 2) ((constants (Fin 6)).comap (core (Fin 6)).subtype) = 1
    rw [(Submodule.comapSubtypeEquivOfLe
      ((constants_le_core_iff (Fin 6)).mpr (by decide))).finrank_eq,finrank_constants]
  rw [hf,he,finrank_core] at hd
  change fixedCodim rho (alternatingGroup (Fin 6)) + 1 = 5 at hd
  omega
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
    · simpa using NaturalSixControl.Model.corePlanes_generate
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


end Model

end CFSG.Quasithin.ChapterC.AugmentationSixControl
