module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Odd
public import Theory.Representation.BinaryOffender.FixedCodimTransport
import Mathlib.Tactic

/-!
# The stable transposition family for the seven-letter core

Every nonempty stable family contains a transposition subgroup, by descending
with equal weight from a classified offender. Conjugation supplies every
transposition. Inside a Sylow containing the three standard disjoint swaps,
the family therefore generates exactly their eight-group.

Source: Aschbacher–Smith, B.3.2(4) and the S₇ case of C.1.24, printed pp.84 and 131.
-/

public section

open Subgroup Equiv Equiv.Perm
open CFSG.Quasithin.ChapterB.Offenders Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.RankOne.Alternating.SevenSource
private theorem first_eq_zpowers : disjointTranspositions 7 1 = zpowers (swap (0 : Fin 7) 1) := by
  rw [disjointTranspositions, zpowers_eq_closure]
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have he : i = 0 := Fin.ext (by change i.val = 0; omega)
    rw [he]
    rfl
  · rintro rfl
    exact ⟨0, by decide, rfl⟩

private theorem offender_weight (A : Subgroup (Perm (Fin 7)))
    (hA : IsBestOffender (BinaryPermutation.coreRepresentation (Fin 7)) A) :
    weight (BinaryPermutation.coreRepresentation (Fin 7)) A = Module.finrank (ZMod 2) (BinaryPermutation.core (Fin 7)) := by
  have hd := fixedCodim_add_finrank (BinaryPermutation.coreRepresentation (Fin 7)) A
  have hl := (hA.isOffender (BinaryPermutation.coreRepresentation (Fin 7))).2
  have hu : rank A ≤ fixedCodim (BinaryPermutation.coreRepresentation (Fin 7)) A := by
    by_contra! h
    exact Odd.not_isStrongOffender_core (Or.inr rfl) A ⟨hA.1, h⟩
  unfold weight
  omega

/-- Stability and the absence of strong offenders close this family downward
among the actual natural-module offenders. -/
theorem stable_downward {P : Set (Subgroup (Perm (Fin 7)))}
    (hP : IsStable (BinaryPermutation.coreRepresentation (Fin 7)) P) {A B : Subgroup (Perm (Fin 7))}
    (hA : A ∈ P) (hB : IsBestOffender (BinaryPermutation.coreRepresentation (Fin 7)) B) (hBA : B ≤ A) : B ∈ P := by
  apply hP.2.2.2 A hA B hB.1
  exact ⟨hBA, (offender_weight B hB).trans (offender_weight A (hP.2.1 A hA)).symm⟩

/-- Every transposition subgroup belongs to every nonempty stable family. -/
theorem transposition_mem_stable {P : Set (Subgroup (Perm (Fin 7)))}
    (hP : IsStable (BinaryPermutation.coreRepresentation (Fin 7)) P) (a b : Fin 7) (hab : a ≠ b) :
    zpowers (swap a b) ∈ P := by
  obtain ⟨A, hA⟩ := hP.1
  obtain ⟨m, hm, hm7, g, hg⟩ :=
    (Odd.isBestOffender_core_iff_caseAFamily (Or.inr rfl) A).mp (hP.2.1 A hA)
  have hsmall : (disjointTranspositions 7 1).map (MulAut.conj g).toMonoidHom ∈ P := by
    apply stable_downward hP hA
      ((Odd.isBestOffender_disjointTranspositions (n := 7) (m := 1) (Or.inr rfl) (by decide) (by decide)).2.1.map_conj
        (BinaryPermutation.coreRepresentation (Fin 7)) g)
    rw [hg]
    exact map_mono (disjointTranspositions_mono hm)
  have hfirst := hP.2.2.1 _ hsmall g⁻¹
  rw [show ((disjointTranspositions 7 1).map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj g⁻¹).toMonoidHom = disjointTranspositions 7 1 from by
    rw [Subgroup.map_map]
    have hc : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id _ := by ext x; simp [MulAut.conj_apply, mul_assoc]
    rw [hc, Subgroup.map_id]] at hfirst
  rw [first_eq_zpowers] at hfirst
  obtain ⟨h, hh⟩ := isConj_iff.mp (isConj_swap (by decide : (0 : Fin 7) ≠ 1) hab)
  have hlast := hP.2.2.1 _ hfirst h
  rw [MonoidHom.map_zpowers] at hlast
  exact (show (MulAut.conj h) (swap 0 1) = swap a b from hh) ▸ hlast

/-- In the canonical Sylow coordinates the family generates D. -/
theorem stable_generatedBy_eq_D {P : Set (Subgroup (Perm (Fin 7)))}
    (hP : IsStable (BinaryPermutation.coreRepresentation (Fin 7)) P) (R : Subgroup (Perm (Fin 7)))
    (hR : IsPGroup 2 R) (hD : D 7 ≤ R) :
    generatedBy P R = D 7 := by
  apply le_antisymm
  · apply iSup_le
    intro A
    apply iSup_le
    rintro ⟨hA, hAR⟩
    exact Odd.caseAFamily_le_D_of_isPGroup (Or.inr rfl) hR hD
      ((Odd.isBestOffender_core_iff_caseAFamily (Or.inr rfl) A).mp (hP.2.1 A hA)) hAR
  · rw [D, disjointTranspositions, closure_le]
    rintro t ⟨i, hi, rfl⟩
    let a : Fin 7 := ⟨2 * i.val, by omega⟩
    let b : Fin 7 := ⟨2 * i.val + 1, by omega⟩
    have hab : a ≠ b := by intro h; have := congrArg Fin.val h; dsimp [a, b] at this; omega
    have ht : pairSwap 7 i ∈ R := hD (pairSwap_mem i hi)
    have hmem : zpowers (pairSwap 7 i) ∈ P := transposition_mem_stable hP a b hab
    have hle : zpowers (pairSwap 7 i) ≤ generatedBy P R :=
      le_iSup_of_le (zpowers (pairSwap 7 i))
        (le_iSup_of_le ⟨hmem, zpowers_le.mpr ht⟩ le_rfl)
    exact hle (mem_zpowers _)


/-- Conjugating the ambient Sylow conjugates its generated stable-family subgroup. -/
theorem generatedBy_conj {P : Set (Subgroup (Perm (Fin 7)))}
    (hP : IsStable (BinaryPermutation.coreRepresentation (Fin 7)) P) (R : Subgroup (Perm (Fin 7))) (g : Perm (Fin 7)) :
    (generatedBy P R).map (MulAut.conj g).toMonoidHom =
      generatedBy P (R.map (MulAut.conj g).toMonoidHom) := by
  apply le_antisymm
  · rw [map_le_iff_le_comap]
    apply iSup_le
    intro A
    apply iSup_le
    rintro ⟨hA, hAR⟩
    apply map_le_iff_le_comap.mp
    exact le_iSup_of_le _ (le_iSup_of_le ⟨hP.2.2.1 A hA g, map_mono hAR⟩ le_rfl)
  · apply iSup_le
    intro A
    apply iSup_le
    rintro ⟨hA, hAR⟩
    have hback := hP.2.2.1 A hA g⁻¹
    have hle : A.map (MulAut.conj g⁻¹).toMonoidHom ≤ R := by
      have hm := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hAR
      have hc : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
          MonoidHom.id _ := by ext x; simp [MulAut.conj_apply, mul_assoc]
      simpa only [Subgroup.map_map, hc, Subgroup.map_id] using hm
    have hi : A.map (MulAut.conj g⁻¹).toMonoidHom ≤ generatedBy P R :=
      le_iSup_of_le _ (le_iSup_of_le ⟨hback, hle⟩ le_rfl)
    have hm := map_mono (f := (MulAut.conj g).toMonoidHom) hi
    have hc : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
        MonoidHom.id _ := by ext x; simp [MulAut.conj_apply, mul_assoc]
    simpa only [Subgroup.map_map, hc, Subgroup.map_id] using hm

/-- Every Sylow marking is simultaneously conjugate to the three chosen swaps. -/
theorem exists_generatedBy_marking {P : Set (Subgroup (Perm (Fin 7)))}
    (hP : IsStable (BinaryPermutation.coreRepresentation (Fin 7)) P) (R : Sylow 2 (Perm (Fin 7))) :
    ∃ g : Perm (Fin 7),
      (generatedBy P (R : Subgroup _)).map (MulAut.conj g).toMonoidHom = D 7 := by
  obtain ⟨Q, hDQ, _⟩ := Odd.exists_sylow_containing_D (Or.inr rfl : 7 = 5 ∨ 7 = 7)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 7)) R Q
  refine ⟨g, ?_⟩
  rw [generatedBy_conj hP]
  have he : (R : Subgroup _).map (MulAut.conj g).toMonoidHom = Q := by
    rw [← hg]
    rfl
  rw [he]
  exact stable_generatedBy_eq_D hP Q Q.isPGroup' hDQ

end CFSG.Quasithin.ChapterC.RankOne.Alternating.SevenSource
